(** HOL terms and their translation to Dedukti. *)

(** Debugging *)

let declared = ref []

let in_type_op = ref ([] : string list)

(** Term variables are annotated by their type, as different variables can have
    the same name but different type. *)
type var = string * Type.hol_type

(** Term constants *)
type cst = string

(** Terms *)
type term =
  | Var of var
  | Cst of cst * Type.hol_type
  | Lam of var * term
  | App of term * term

let dummy_term = Var ("dummy",Type.dummy_type)

let is_var = function
  | Var _ -> true
  | _ -> false

(** Type alias to satisfy the OrderedType interface used by sets and maps *)
type t = term

let tyvar x = Type.Var(x)
let tybool = Type.App("bool", [])
let tyarrow a b = Type.App("->", [a; b])

let rec sprint_term () t =
  match t with
  | Var (x, _) ->
    Printf.sprintf "%s" x
  | Cst (c, _) ->
    Printf.sprintf "%s" c
  | Lam ((x, _), t) ->
    Printf.sprintf "\\lambda %s. %a" x sprint_term t
  | App (t, u) ->
    Printf.sprintf "(%a %a)" sprint_term t sprint_term u

let sprint_list_term lt =
	let rec sprint_list_term_rec = function
	 [] 		-> ""
	| t::ltq	-> String.concat "" [(sprint_term () t);"\n";(sprint_list_term_rec ltq)]
	in
	String.concat "" ["[";sprint_list_term_rec lt;"]"]

(** Type schemes of the declared constants *)

let base_csts = [
    "=", Type.App("->", [Type.Var("A"); Type.App("->", [Type.Var("A"); Type.App("bool", [])])]);
    "select", Type.App("->", [Type.App("->", [Type.Var("A"); Type.App("bool", [])]); Type.Var("A")]);
  ]

let csts = ref base_csts

let is_declared c = List.mem_assoc c !csts

(** Compute the type of [a], assuming it is well typed. *)
let rec type_of t =
  match t with
  | Var((x, a)) -> a
  | Cst(c, a) -> a
  | Lam((x, a), b) -> Type.arr a (type_of b)
  | App(t, u) -> let a, b = Type.get_arr (type_of t) in b

(** Compute the free type variables in [t] using [ftv] as an accumulator. *)
let rec free_type_vars ftv t =
  match t with
  | Var((x, a)) -> Type.free_vars ftv a
  | Cst(c, a) -> Type.free_vars ftv a
  | Lam((x, a), t) -> free_type_vars (Type.free_vars ftv a) t
  | App(t, u) -> free_type_vars (free_type_vars ftv t) u

(** Compute the free term variables in [t] using [fv] as an accumulator. *)
let free_vars fv t =
  let rec free_vars bound fv t =
    match t with
    | Var(x) -> if List.mem x bound || List.mem x fv then fv else x :: fv
    | Cst(c, a) -> fv
    | Lam(x, t) -> free_vars (x :: bound) fv t
    | App(t, u) -> free_vars bound (free_vars bound fv t) u
  in free_vars [] fv t

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

(** Alpha-equivalence-aware total ordering function *)
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

(** Interpretation of special constants **)
let base_interpretation = [
  ("Data.Bool./\\",(Type.App ("->",[Type.App ("bool",[]);Type.App ("->",[Type.App ("bool",[]);Type.App ("bool",[])])]),Name.hole "and_cp"));
  ("Data.Bool.\\/",(Type.App ("->",[Type.App ("bool",[]);Type.App ("->",[Type.App ("bool",[]);Type.App ("bool",[])])]),Name.hole "or_cp"));
  ("Data.Bool.==>",(Type.App ("->",[Type.App ("bool",[]);Type.App ("->",[Type.App ("bool",[]);Type.App ("bool",[])])]),Name.hole "imp_cp"));
  ("Data.Bool.T",(Type.App ("bool",[]),Name.hole "true_cp"));
  ("Data.Bool.F",(Type.App ("bool",[]),Name.hole "false_cp"));
  ("Data.Bool.~",(Type.App ("->",[Type.App ("bool",[]);Type.App ("bool",[])]),Name.hole "not_cp"));
  ("Data.Bool.!",(Type.App ("->",[Type.App ("->",[Type.Var "A";Type.App ("bool",[])]);Type.App ("bool",[])]),Name.hole "forall_cp"));
  ("Data.Bool.?",(Type.App ("->",[Type.App ("->",[Type.Var "A";Type.App ("bool",[])]);Type.App ("bool",[])]),Name.hole "exists_cp"))
  ]

let interpretation = ref base_interpretation

let () =
  List.iter (fun (c, (a, c')) -> csts := (c, a) :: !csts) !interpretation

let connectives = ref ["Data.Bool./\\";"Data.Bool.\\/";"Data.Bool.==>";"Data.Bool.T";"Data.Bool.~";"Data.Bool.!";"Data.Bool.?"]

(** Keep track of constants' definition *)

let defined_csts = Database.unmarshal_h "csts.holide"

let add_cst (c:cst) (a:Type.hol_type) =
	Hashtbl.add defined_csts c (a,Name.escape (Input.get_module_name()));
	try
		let prov_cst = Name.escape (Input.get_module_name()) in
		let already_used = Hashtbl.find_all Type.unresolved_deps c in
		let resolve_dep mod_name = Hashtbl.add Type.deps mod_name prov_cst in
		let () = List.iter resolve_dep already_used in
		let () = List.iter (fun x -> Hashtbl.remove Type.unresolved_deps c) already_used in
		()
	with Not_found -> ()

let add_dep_cst (cst:string) =
	let mod_name = Name.escape (Input.get_module_name()) in
	try
		let prov_cst = snd (Hashtbl.find defined_csts cst) in
		let deps_mod_name = Hashtbl.find_all Type.deps mod_name in
		if not (List.mem prov_cst deps_mod_name) then
			Hashtbl.add Type.deps mod_name prov_cst
		else ()
	with Not_found -> Hashtbl.add Type.unresolved_deps cst mod_name

(** Sharing of terms *)

module TermSharing = Sharing.Make(
  struct
    type t = term
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let translate_id id = Name.id "term" id

exception UnboundVariable

(** Translate the name of the variable [x] of type [a] according to its
    position in the binding context. Different variables can have the same name
    but different types, so we suffix the level of the variable avoid clashes.
    Raise [UnboundVariable] if the variable is not in [context]. *)
let translate_var context (x, a) =
  match index context (x, a) with
  | Bound(i) -> Name.id x (List.length context - i)
  | Free(_) -> raise UnboundVariable

let translate_cst c =
  match c with
  | "=" -> Name.hole "eq"
  | "select" -> Name.hole "select"
  | _ ->
    begin
      try snd (List.assoc c !interpretation) with
      | Not_found -> Name.escape c
    end

(** Translate the HOL type [a] as a Dedukti type. *)
(*let translate_type a =
  Dedukti.app (Dedukti.var (Name.hol "term")) (Type.translate_type a)*)

(** Translate the HOL type [a] as a Dedukti type with substitution. *)
let translate_type theta a =
  Dedukti.app (Dedukti.var (Name.hole "term")) (Type.translate_type theta a)

(** Translate the HOL type [a] as a Dedukti type. *)
let translate_type_total a =
  Dedukti.app (Dedukti.var (Name.hole "term")) (Type.translate_type_total a)

(** Translate the list of term variables [x1, a1; ...; xn, an]
    into the Dedukti terms [x1 : ||a1||; ...; xn : ||an||] and add them to
    the context. *)
let rec translate_vars context vars =
  let context = List.rev_append vars context in
  let vars' = List.map (fun (x, a) -> (translate_var context (x, a), translate_type [] a)) vars in
  (vars', context)

(** Translate the list of term variables [x1, a1; ...; xn, an]
    into the Dedukti terms [x1 : ||a1||; ...; xn : ||an||] and add them to
    the context, without sharing. *)
let rec translate_vars_total context vars =
  let context = List.rev_append vars context in
  let vars' = List.map (fun (x, a) -> (translate_var context (x, a), translate_type_total a)) vars in
  (vars', context)

(** Translate the variable [x] of type [a] as a Dedukti term. Sometimes the
    variable is not bound by the context, in which case we should eliminate it
    by replacing it with a witness for the type [a]. *)
(*let translate_var_term context (x, a) =
  try Dedukti.var (translate_var context (x, a))
  with UnboundVariable ->
    Dedukti.app (Dedukti.var (Name.hol "witness")) (Type.translate_type (a))*)

(** Same with a substitution. *)
let translate_var_term context (x, a) theta =
  try Dedukti.var (translate_var context (x, a))
  with UnboundVariable ->
    Dedukti.app (Dedukti.var (Name.hole "witness")) (Type.translate_type theta a)

let mk_lam a a' b x t =
  let lam = Dedukti.lam (x, a') t in
  match !Options.language with
  | Options.No | Options.Dk -> lam
  | Options.Coq | Options.Twelf -> Dedukti.apps (Dedukti.var (Name.hol "lam")) [a; b; lam]

let get_lam p =
  match p with
  Lam (x,bod) -> (x,bod)
  | _ -> failwith "Not a lambda-abstraction"


let mk_app a b t u =
  match !Options.language with
  | Options.No | Options.Dk -> Dedukti.app t u
  | Options.Coq | Options.Twelf -> Dedukti.apps (Dedukti.var (Name.hol "app")) [a; b; t; u]

let get_app p =
  match p with
  App (t,u) -> (t,u)
  | _ -> failwith "Not an application"

(** Translate the HOL term [t] as a Dedukti term. *)
(*
let translate_term_bool t_o_t tr_t needs_gilbert =
  let gilbert_t = Dedukti.var (Name.hol "gilbert_t") in
  let gilbert = Dedukti.app gilbert_t t_o_t in
  if needs_gilbert then Dedukti.app gilbert tr_t
  else tr_t

let rec term_is_con = function
  | Var _ -> false
  | Cst _ -> true
  | t -> term_is_con_rec t

and term_is_con_rec = function
  | App (t,u) -> term_is_con_rec t
  | Cst (c,a) when List.mem c !connectives -> true
  | _ -> false*)

(** Translate the HOL term [t] as a Dedukti term with an additional substitution. *)
let rec translate_term context theta t =
  (*let t_o_t = type_of t in
  let t_o_t_d = Type.translate_type theta t_o_t in
  let is_bool = t_o_t = tybool in
  let is_abs_type = Type.is_var t_o_t in
  let needs_gilbert = (is_abs_type || (is_bool && not (term_is_con t))) in*)
  try
    let id = TermSharing.find t in
    let ftv = free_type_vars [] t in
    let fv = free_vars [] t in
    let id' = Dedukti.var (translate_id id) in
    let ftv' = List.map (fun x -> if List.mem x theta then Dedukti.var (Name.hole "bool") else Dedukti.var (Type.translate_var x)) ftv in
    let fv' = List.map (fun x -> translate_var_term context x theta) fv in
    Dedukti.apps (Dedukti.apps id' ftv') fv'
  with Not_found ->
    match t with
    | Var(x) ->
      (*translate_term_bool t_o_t_d*) (translate_var_term context x theta) (*needs_gilbert*)
    | Cst(c, a) ->
      let b = List.assoc c !csts in
      let ftv = Type.free_vars [] b in
      let theta' = Type.match_type [] a b in
      let c' = Dedukti.var (translate_cst c) in
      let theta'' = List.map (fun x -> Type.translate_type theta (List.assoc x theta')) ftv in
      let tr_t = Dedukti.apps c' theta'' in
      (*translate_term_bool t_o_t_d*) tr_t (*needs_gilbert*)
    | Lam((x, a), t) ->
      let b = type_of t in
      let a' = Type.translate_type theta a in
      let b' = Type.translate_type theta b in
      let x' = translate_var ((x, a) :: context) (x, a) in
      let t' = translate_term ((x, a) :: context) theta t in
      let tr_t = mk_lam a' (translate_type theta a) b' x' t' in
      (*translate_term_bool t_o_t_d*) tr_t (*needs_gilbert*)
    | App(t, u) ->
      let a, b = Type.get_arr (type_of t) in
      let a' = Type.translate_type theta a in
      let b' = Type.translate_type theta b in
      let t' = translate_term context theta t in
      let u' = translate_term context theta u in
      let tr_t = mk_app a' b' t' u' in
      (*translate_term_bool t_o_t_d*) tr_t (*needs_gilbert*)

(** Translate the HOL term [t] as a Dedukti term, without using the sharing. *)
let rec translate_term_total context t =
  (*let t_o_t = type_of t in
  let t_o_t_d = Type.translate_type_total t_o_t in
  let is_bool = t_o_t = tybool in
  let is_abs_type = Type.is_var t_o_t in
  let needs_gilbert = (is_abs_type || (is_bool && not (term_is_con t))) in*)
  match t with
    | Var(x) ->
      (*translate_term_bool t_o_t_d*) (translate_var_term context x []) (*needs_gilbert*)
    | Cst(c, a) ->
      let b = List.assoc c !csts in
      let ftv = Type.free_vars [] b in
      let theta = Type.match_type [] a b in
      let c' = Dedukti.var (translate_cst c) in
      let theta' = List.map (fun x -> Type.translate_type_total (List.assoc x theta)) ftv in
      let tr_t = Dedukti.apps c' theta' in
       (*translate_term_bool t_o_t_d*) tr_t (*needs_gilbert*)
    | Lam((x, a), t) ->
      let b = type_of t in
      let a' = Type.translate_type_total a in
      let b' = Type.translate_type_total b in
      let x' = translate_var ((x, a) :: context) (x, a) in
      let t' = translate_term_total ((x, a) :: context) t in
      let tr_t = mk_lam a' (translate_type_total a) b' x' t' in
      (*translate_term_bool t_o_t_d*) tr_t (*needs_gilbert*)
    | App(t, u) ->
      let a, b = Type.get_arr (type_of t) in
      let a' = Type.translate_type_total a in
      let b' = Type.translate_type_total b in
      let t' = translate_term_total context t in
      let u' = translate_term_total context u in
      let tr_t = mk_app a' b' t' u' in
      (*translate_term_bool t_o_t_d*) tr_t (*needs_gilbert*)

(** Import the constant c. *)
let import_cst c =
  let c_type,c_module = Hashtbl.find defined_csts c in
  Output.print_verbose "Importing constant %s\n%!" c;
  if !Options.language <> Options.No then (
	let c_name = String.concat "." [c_module;Name.escape c] in
	let c' = translate_cst c in
	let c_def = Dedukti.Var c_name in
	Output.print_comment (Printf.sprintf "Constant %s" c);
	Output.print_dependancy c' c_def);
  csts := (c, c_type) :: !csts

(** Declare the constant [c : a]. *)
let declare_cst ?(intyop=false) c a =
  let () = if (not intyop) then add_dep_cst c in
  if ((Hashtbl.mem defined_csts c) &&
	(snd (Hashtbl.find defined_csts c) <> Name.escape (Input.get_module_name())))
	then import_cst c
  else
  (Output.print_verbose "Warning: using constant %s, undeclared in this module\n%!" c;
  Output.print_verbose "Declaring constant %s\n%!" c;
  if !Options.language <> Options.No then (
	let ftv = Type.free_vars [] a in
	let () = declared := (c,Name.escape (Input.get_module_name()))::!declared in
	let c' = translate_cst c in
	let ftv' = Type.translate_vars ftv in
	if (not intyop) then begin
	let a' = Dedukti.pies ftv' (translate_type [] a) in
	Output.print_comment (Printf.sprintf "Constant %s" c);
	Output.print_declaration c' a' end
	else begin
	let a' = Dedukti.pies ftv' (translate_type_total a) in
	Output.print_comment (Printf.sprintf "Constant %s" c);
	Output.print_declaration c' a' end);
  csts := (c, a) :: !csts)


(** Define the constant [c : a := t]. *)
let define_cst c a t =
  Output.print_verbose "Defining constant %s\n%!" c;
  if !Options.language <> Options.No then (
    let ftv = Type.free_vars [] a in
    let c' = translate_cst c in
    let ftv' = Type.translate_vars ftv in
    let a' = Dedukti.pies ftv' (translate_type_total a) in
    let t' = Dedukti.lams ftv' (translate_term_total [] t) in
    Output.print_comment (Printf.sprintf "Constant %s" c);
    Output.print_definition c' a' t');
  csts := (c, a) :: !csts


(** Define the term [id := t]. *)
let define_term ?(local=false) t =
  if !Options.language <> Options.No && not (TermSharing.mem t) then (
      let a = type_of t in
      let ftv = free_type_vars [] t in
      let fv = free_vars [] t in
      let ftv' = Type.translate_vars ftv in
      let fv', context = translate_vars [] fv in
      let a' = Dedukti.pies ftv' (Dedukti.pies fv' (translate_type [] a)) in
      let t' = Dedukti.lams ftv' (Dedukti.lams fv' (translate_term context [] t)) in
      let id = TermSharing.add t in
      let id' = translate_id id in
      Output.print_definition ~untyped:true ~local:local id' a' t');
  t

(** Smart constructors *)

let var x = Var(x)

let cst c a =
  (* Check first if the constant is declared. *)
  if (not (is_declared c))  then (
    (* Cannot assume the time of [c] is [a], as it can be more general. *)
    if c = "=" then failwith "Equality should be declared";
    if c = "select" then failwith "Selection should be declared";
    declare_cst c (Type.var "A"));
  (Cst(c, a))

let lam x t = (Lam(x, t))

let app t u = (App(t, u))

let eq t u =
  let a = type_of t in
  app (app (cst "=" (Type.arr a (Type.arr a (Type.bool ())))) t) u

let select p =
  let a, b = Type.get_arr (type_of p) in
  app (cst "select" (Type.arr (Type.arr a b) (Type.bool ()))) p

let mk_bin_op op t1 t2 =
  app (app (cst op (Type.arr (Type.bool()) (Type.arr (Type.bool()) (Type.bool ())))) t1) t2

let mk_op op t =
  app (cst op (Type.arr (Type.bool()) (Type.bool ()))) t

let mk_bind op p =
  app (cst op (Type.arr (type_of p) (Type.bool ()))) p

let get_eq t =
  match t with
  | App(App(Cst("=", _), t), u) -> (t, u)
  | _ -> failwith "Not an equality"

let get_select t =
  match t with
  | App(Cst("select", _), p) -> p
  | _ -> failwith "Not a select operation"

let get_bin_op op t =
  match t with
  | App(App(Cst(cop, _), t), u) when cop = op -> (t, u)
  | _ -> failwith "Not an application of given binary operator"

let get_un_op op t =
  match t with
  | App(Cst(cop, _), p) when cop = op -> p
  | _ -> failwith "Not an application of given unary operator"


(* We define the following functions after the translation as we might want to
   use sharing or smart constructors. *)

(** Type substitution *)
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

(** Capture-avoiding term substitution *)
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
    | App(t, u) -> app (subst fv sigma t) (subst fv sigma u) in
  subst fv sigma t

let betar p s =
	match p with
	Lam (v,b) -> subst [(v,s)] b
	| _ -> failwith "Only applications of abstractions can be reduced"

