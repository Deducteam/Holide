(** This module implements the terms of HOL and their translation to Dedukti.
    The translation of the datatypes uses sharing, which is handled by smart
    constructors. *)

type var = string

type cst = string

type term =
| Var of var * Type.hol_type
| Cst of cst * Type.hol_type
| Lam of var * Type.hol_type * term
| App of term * term

(** Type schemes of the declared constants. *)
(* Cannot use the smart constructors because the output environment has not
    been setup yet. *)
let csts = ref [
  "=", Type.App("->", [Type.Var("A"); Type.App("->", [Type.Var("A"); Type.App("bool", [])])]);
  "select", Type.App("->", [Type.App("->", [Type.Var("A"); Type.App("bool", [])]); Type.Var("A")]);
  ]

let is_declared c = List.mem_assoc c !csts

(** Computes the type of [a], assuming it is well typed. *)
let rec type_of a =
  match a with
  | Var(x, a) -> a
  | Cst(c, a) -> a
  | Lam(x, a, b) -> Type.arr a (type_of b)
  | App(t, u) -> let a, b = Type.get_arr (type_of t) in b

(** Free variables *)

let rec free_type_vars ftv a =
  match a with
  | Var(x, a) -> Type.free_vars ftv a
  | Cst(c, a) -> Type.free_vars ftv a
  | Lam(x, a, t) -> free_type_vars (Type.free_vars ftv a) t
  | App(t, u) -> free_type_vars (free_type_vars ftv t) u

let free_vars fv a =
  let rec free_vars bound fv a =
    match a with
    | Var(x, a) -> if List.mem (x, a) bound || List.mem (x, a) fv then fv else (x, a) :: fv
    | Cst(c, a) -> fv
    | Lam(x, a, t) -> free_vars ((x, a) :: bound) fv t
    | App(t, u) -> free_vars bound (free_vars bound fv t) u
  in free_vars [] fv a

type index =
| Bound of int
| Free of var * Type.hol_type

let index context (x, a) =
  let rec index i context =
    match context with
    | [] -> Free(x, a)
    | (y, b) :: context ->
        if (x, a) = (y, b) then Bound(i)
        else index (i + 1) context
  in index 0 context

let alpha_equiv t u =
  let rec alpha_equiv bindings_t bindings_u t u =
    match t, u with
    | Var(x, a), Var(y, b) -> a = b && (index bindings_t (x, a) = index bindings_u (y, b))
    | Cst(c, a), Cst(d, b) -> a = b && c = d
    | Lam(x, a, t), Lam(y, b, u) -> a = b && (alpha_equiv ((x, a) :: bindings_t) ((y, b) :: bindings_u) t u)
    | App(t1, t2), App(u1, u2) -> (alpha_equiv bindings_t bindings_u t1 u1) && (alpha_equiv bindings_t bindings_u t2 u2)
    | _ -> false
  in alpha_equiv [] [] t u

(** Translation *)

module TermSharing = Sharing.Make(
  struct
    type t = term
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let translate_id id = Name.id "term" id

let translate_var (x, a) =
  (* Different variables can have the same name but different types, so we
     suffix the hash of the type to avoid clashes. Use hashparam to avoid
     collisions (which would otherwise happen often). *)
  let hash = Hashtbl.hash_param 1000000 1000000 a mod 256 in
  Printf.sprintf "%s_%02X" (Name.escape x) hash

let translate_cst c =
  match c with
  | "=" -> Name.hol "eq"
  | "select" -> Name.hol "select"
  | _ -> Name.escape c

(** Translate the HOL type [a] as a Dedukti type. *)
let translate_type a =
  Dedukti.app (Dedukti.var (Name.hol "term")) (Type.translate_type a)

(** Translate the HOL term [t] as a Dedukti term. *)
let rec translate_term t =
  try
    let id = TermSharing.find t in
    let ftv = free_type_vars [] t in
    let fv = free_vars [] t in
    let id' = Dedukti.var (translate_id id) in
    let ftv' = List.map Dedukti.var (List.map Type.translate_var ftv) in
    let fv' = List.map Dedukti.var (List.map translate_var fv) in
    Dedukti.apps (Dedukti.apps id' ftv') fv'
  with Not_found ->
    match t with
    | Var(x, a) ->
        Dedukti.var (translate_var (x, a))
    | Cst(c, a) ->
        let b = List.assoc c !csts in
        let ftv = Type.free_vars [] b in
        let theta = Type.match_type [] a b in
        let c' = Dedukti.var (translate_cst c) in
        let theta' = List.map (fun x -> Type.translate_type (List.assoc x theta)) ftv in
        Dedukti.apps c' theta'
    | Lam(x, a, t) ->
        let x' = translate_var (x, a) in
        let a' = translate_type a in
        let t' = translate_term t in
        Dedukti.lam (x', a') t'
    | App(t, u) ->
        let t' = translate_term t in
        let u' = translate_term u in
        Dedukti.app t' u'

(** Translate the list of term variables [x1, a1; ...; xn, an]
    into the dedukti context [x1 : ||a1||; ...; xn : ||an||] *)
let translate_vars_context vars =
  List.map (fun (x, a) -> (translate_var (x, a), translate_type a)) vars

(** Declare the term [c : a]. *)
let declare_cst c a =
  Output.print_verbose "Declaring constant %s\n%!" c;
  let ftv = Type.free_vars [] a in
  let c' = translate_cst c in  
  let ftv' = Type.translate_vars_context ftv in
  let a' = Dedukti.pies ftv' (translate_type a) in
  Output.print_declaration c' a';
  csts := (c, a) :: !csts

(** Define the term [id := t]. *)
let define_term t =
  let _ = if not (TermSharing.mem t) then (
    let a = type_of t in
    let ftv = free_type_vars [] t in
    let fv = free_vars [] t in  
    let ftv' = Type.translate_vars_context ftv in
    let fv' = translate_vars_context fv in
    let a' = Dedukti.pies ftv' (Dedukti.pies fv' (translate_type a)) in
    let t' = Dedukti.lams ftv' (Dedukti.lams fv' (translate_term t)) in
    let id = TermSharing.add t in
    let id' = translate_id id in
    Output.print_definition false id' a' t';)
  in t

(** Smart constructors *)

let var x a = Var(x, a)

let cst c a =
  (* Check first if the constant is declared. *)
  if not (is_declared c) then (
    Output.print_verbose "Warning: using undeclared constant %s\n%!" c;
    (* Cannot assume the time of [c] is [a], as it can be more general. *)
    declare_cst c (Type.var "A"));
   define_term (Cst(c, a))

let lam x a t = define_term (Lam(x, a, t))

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
  | Var(x, a) -> var x (Type.subst theta a)
  | Cst(c, a) -> cst c (Type.subst theta a)
  | Lam(x, a, t) -> lam x (Type.subst theta a) (type_subst theta t)
  | App(t, u) -> app (type_subst theta t) (type_subst theta u)

(** Return a variant of the variable [x] of type [a] which does not appear in
    the list of variables [avoid]. *)
let rec variant (x, a) avoid =
  if not (List.mem (x, a) avoid) then x else variant (x ^ "_", a) avoid

(** Capture-avoiding term substitution. The substitution must be given as
    a list of the form [(x1, a1), u1; ...; (xn, an), un]. *)
let subst sigma t =
  let fv = List.fold_left free_vars (free_vars [] t) (snd (List.split sigma)) in
  let rec subst fv sigma t =
    match t with
    | Var(x, a) ->
        begin try List.assoc (x, a) sigma
        with Not_found -> t end
    | Cst(_) -> t
    | Lam(x, a, t) ->
        let x' = variant (x, a) fv in
        let sigma' = ((x, a), var x' a) :: sigma in
        let fv' = (x', a) :: fv in
        lam x' a (subst fv' sigma' t)
    | App(t, u) -> app (subst fv sigma t) (subst fv sigma u)
  in subst fv sigma t

