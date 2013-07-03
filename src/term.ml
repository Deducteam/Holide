(** This module implements the terms of HOL and their translation to Dedukti.
    The translation of the datatypes uses sharing, which is handled by smart
    constructors. *)

type var = string * Type.hol_type

type cst = string

type term =
  | Var of var
  | Cst of cst * Type.hol_type
  | Lam of var * term
  | App of term * term

(** Type alias to satisfy the OrderedType interface used by sets and maps. *)
type t = term

(** Type schemes of the declared constants. *)
(* Cannot use the smart constructors because the output environment has not
    been setup yet. *)
let csts = ref [
    "=", Type.App("->", [Type.Var("A"); Type.App("->", [Type.Var("A"); Type.App("bool", [])])]);
    "select", Type.App("->", [Type.App("->", [Type.Var("A"); Type.App("bool", [])]); Type.Var("A")]);
  ]

let is_declared c = List.mem_assoc c !csts

(** Compute the type of [a], assuming it is well typed. *)
let rec type_of a =
  match a with
  | Var((x, a)) -> a
  | Cst(c, a) -> a
  | Lam((x, a), b) -> Type.arr a (type_of b)
  | App(t, u) -> let a, b = Type.get_arr (type_of t) in b

let rec free_type_vars ftv a =
  match a with
  | Var((x, a)) -> Type.free_vars ftv a
  | Cst(c, a) -> Type.free_vars ftv a
  | Lam((x, a), t) -> free_type_vars (Type.free_vars ftv a) t
  | App(t, u) -> free_type_vars (free_type_vars ftv t) u

let free_vars fv a =
  let rec free_vars bound fv a =
    match a with
    | Var(x) -> if List.mem x bound || List.mem x fv then fv else x :: fv
    | Cst(c, a) -> fv
    | Lam(x, t) -> free_vars (x :: bound) fv t
    | App(t, u) -> free_vars bound (free_vars bound fv t) u
  in free_vars [] fv a

(** Type to represent the index of bound and free variables. *)
type index =
  | Bound of int
  | Free of var

(** Return the index of the variable [x] in the binding context. *)
let index context x =
  let rec index i context =
    match context with
    | [] -> Free(x)
    | y :: context ->
      if x = y then Bound(i)
      else index (i + 1) context
  in index 0 context

(** Alpha-equivalence-aware total ordering function. *)
let compare t u =
  (* Lexicographical ordering *)
  let lex f a b g c d = let cmp = f a b in if cmp <> 0 then cmp else g c d in
  let rec compare bindings_t bindings_u t u =
    match t, u with
    | Var(x), Var(y) -> Pervasives.compare (index bindings_t x) (index bindings_u y)
    | Cst(c, a), Cst(d, b) -> lex Pervasives.compare c d Pervasives.compare a b
    | Lam((x, a), t), Lam((y, b), u) -> lex Pervasives.compare a b (compare ((x, a) :: bindings_t) ((y, b) :: bindings_u)) t u
    | App(t1, t2), App(u1, u2) -> lex (compare bindings_t bindings_u) t1 u1 (compare bindings_t bindings_u) t2 u2
    | _ -> Pervasives.compare t u
  in compare [] [] t u

let alpha_equiv t u =
  compare t u = 0

(** Translation *)

module TermSharing = Sharing.Make(
  struct
    type t = term
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let translate_id id = Name.id "term" id

exception UnboundVariable

let translate_var context (x, a) =
  (* Different variables can have the same name but different types, so we
     suffix the level of the variable avoid clashes. If the variable is not
     bound by the context, it should be eliminated. *)
  match index context (x, a) with
  | Bound(i) -> Name.id x (List.length context - i)
  | Free(_) -> raise UnboundVariable

let translate_cst c =
  match c with
  | "=" -> Name.hol "eq"
  | "select" -> Name.hol "select"
  | _ -> Name.escape c

(** Translate the HOL type [a] as a Dedukti type. *)
let translate_type a =
  Dedukti.app (Dedukti.var (Name.hol "term")) (Type.translate_type a)

(** Translate the list of term variables [x1, a1; ...; xn, an]
    into the Dedukti terms [x1 : ||a1||; ...; xn : ||an||] *)
let rec translate_vars context vars =
  match vars with
  | [] -> []
  | (x, a) :: vars ->
    let x' = translate_var ((x, a) :: context) (x, a) in
    let a' = translate_type a in
    let vars' = translate_vars ((x, a) :: context) vars in
    (x', a') :: vars'

(* Sometimes the variable is not bound by the context, so we should be
   eliminate it by replacing it with a witness for the type. *)
let translate_var_term context (x, a) =
  try Dedukti.var (translate_var context (x, a))
  with UnboundVariable ->
    Output.print_verbose "Eliminating unbound free variable\n";
    Dedukti.app (Dedukti.var (Name.hol "witness")) (Type.translate_type (a))

(** Translate the HOL term [t] as a Dedukti term. *)
let rec translate_term context t =
  try
    let id = TermSharing.find t in
    let ftv = free_type_vars [] t in
    let fv = free_vars [] t in
    let id' = Dedukti.var (translate_id id) in
    let ftv' = List.map (fun x -> Dedukti.var (Type.translate_var x)) (List.rev ftv) in
    let fv' = List.map (translate_var_term context) (List.rev fv) in
    Dedukti.apps (Dedukti.apps id' ftv') fv'
  with Not_found ->
    match t with
    | Var(x) ->
      translate_var_term context x
    | Cst(c, a) ->
      let b = List.assoc c !csts in
      let ftv = Type.free_vars [] b in
      let theta = Type.match_type [] a b in
      let c' = Dedukti.var (translate_cst c) in
      let theta' = List.map (fun x -> Type.translate_type (List.assoc x theta)) ftv in
      Dedukti.apps c' theta'
    | Lam((x, a), t) ->
      let x' = translate_var ((x, a) :: context) (x, a) in
      let a' = translate_type a in
      let t' = translate_term ((x, a) :: context) t in
      Dedukti.lam (x', a') t'
    | App(t, u) ->
      let t' = translate_term context t in
      let u' = translate_term context u in 
      Dedukti.app t' u'

(** Declare the term [c : a]. *)
let declare_cst c a =
  Output.print_verbose "Declaring constant %s\n%!" c;
  let ftv = Type.free_vars [] a in
  let c' = translate_cst c in  
  let ftv' = Type.translate_vars (List.rev ftv) in
  let a' = Dedukti.pies ftv' (translate_type a) in
  Output.print_declaration c' a';
  csts := (c, a) :: !csts

(** Define the term [id := t]. *)
let define_term t =
  let _ = if not (TermSharing.mem t) then (
      let a = type_of t in
      let ftv = free_type_vars [] t in
      let fv = free_vars [] t in  
      let ftv' = Type.translate_vars (List.rev ftv) in
      let fv' = translate_vars [] (List.rev fv) in
      let a' = Dedukti.pies ftv' (Dedukti.pies fv' (translate_type a)) in
      let t' = Dedukti.lams ftv' (Dedukti.lams fv' (translate_term fv t)) in
      let id = TermSharing.add t in
      let id' = translate_id id in
      Output.print_definition false id' a' t';)
  in t

(** Smart constructors *)

let var x = Var(x)

let cst c a =
  (* Check first if the constant is declared. *)
  if not (is_declared c) then (
    Output.print_verbose "Warning: using undeclared constant %s\n%!" c;
    (* Cannot assume the time of [c] is [a], as it can be more general. *)
    declare_cst c (Type.var "A"));
  define_term (Cst(c, a))

let lam x t = define_term (Lam(x, t))

let app t u = define_term (App(t, u))

let eq t u =
  let a = type_of t in
  app (app (cst "=" (Type.arr a (Type.arr a (Type.bool ())))) t) u

let select p =
  let a, b = Type.get_arr (type_of p) in
  app (cst "select" (Type.arr (Type.arr a b) (Type.bool ()))) p

let get_eq t =
  match t with
  | App(App(Cst("=", _), t), u) -> (t, u)
  | _ -> failwith "Not an equality"

let get_select t =
  match t with
  | App(Cst("select", _), p) -> p
  | _ -> failwith "Not a select operation"

(** Substitutions *)

let rec type_subst theta t =
  match t with
  | Var((x, a)) -> var (x, (Type.subst theta a))
  | Cst(c, a) -> cst c (Type.subst theta a)
  | Lam((x, a), t) -> lam (x, (Type.subst theta a)) (type_subst theta t)
  | App(t, u) -> app (type_subst theta t) (type_subst theta u)

(** Return a variant of the variable [x] of type [a] which does not appear in
    the list of variables [avoid]. *)
let variant (x, a) avoid =
  let rec variant n =
    let y = Printf.sprintf "%s_%d" x n in
    if List.mem (y, a) avoid then variant (n + 1) else (y, a) in
  if List.mem (x, a) avoid then variant 1 else (x, a)

(** Capture-avoiding term substitution. The substitution must be given as
    a list of the form [(x1, a1), u1; ...; (xn, an), un]. *)
let subst sigma t =
  let fv = List.fold_left free_vars (free_vars [] t) (snd (List.split sigma)) in
  let rec subst fv sigma t =
    match t with
    | Var(x) ->
      begin try List.assoc x sigma
        with Not_found -> t end
    | Cst(_) -> t
    | Lam(x, t) ->
      let x' = variant x fv in
      let sigma' = (x, var x') :: sigma in
      let fv' = x' :: fv in
      lam x' (subst fv' sigma' t)
    | App(t, u) -> app (subst fv sigma t) (subst fv sigma u)
  in subst fv sigma t

