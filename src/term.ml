open Type

(* Synstax of HOL terms *)

type var = string * htype

type term =
| Var of var
| Cst of string * htype list (* Constant terms carry the type parameters for their type scheme. *)
| Lam of var * term
| App of term * term

(* The type of a declared constant is parametrized by the set of type variables
   it contains. *)
let cst_type_schemes =
  ref [
    "eq", (["A"], ty_arr (TyVar("A")) (ty_arr (TyVar("A")) ty_bool));
    "select", (["A"], ty_arr (ty_arr (TyVar("A")) ty_bool) (TyVar("A")));]

(* Return the type of the constant c with type parameters ty_args. *)
let type_of_cst c ty_args =
  let ty_vars, a = List.assoc c !cst_type_schemes in
  let theta = List.combine ty_vars ty_args in
  type_inst theta a

(* Computes the type of a term, assuming it is well-typed. *)
let rec type_of t =
  match t with
  | Var(_, a) -> a
  | Cst(c, args) -> type_of_cst c args
  | Lam((_, a), t1) -> ty_arr a (type_of t1)
  | App(t1, t2) -> let a, b = get_arr (type_of t1) in b

(* Compute the free variables in the term t and adds them to the accumulator fv.
   This function is tail-recursive. *)
let free_vars t fv =
  let rec fv_rec t bound fv =
    match t with
    | Var(x) -> if List.mem x bound || List.mem x fv then fv else x :: fv
    | Cst(_) -> fv
    | Lam(x, t1) -> fv_rec t1 (x :: bound) fv
    | App(t1, t2) -> fv_rec t2 bound (fv_rec t1 bound fv)
  in
  fv_rec t [] fv

(* Compute the free type variables in the term t and adds them to the
   accumulator ftv. This function is tail-recursive. *)
let rec free_tvars t ftv =
  match t with
  | Var(idx, a) -> free_type_vars a ftv
  | Cst(c, args) -> List.fold_left (fun ftv a -> free_type_vars a ftv) ftv args
  | Lam((idx, a), t1) -> free_tvars t1 (free_type_vars a ftv)
  | App(t1, t2) -> free_tvars t1 (free_tvars t2 ftv)

(* Return a variant of the variable x which does not appear in the list of
   variables avoid. *)
let rec variant x avoid =
  if not (List.mem x avoid) then x else
  let (idx, a) = x in variant (idx ^ "'", a) avoid

(* Capture-avoiding parallel substitution. Returns the result of applying the
   parallel substitution s to the term t. The parallel substitution must be
   given as a list of the form [x1, u1; ...; xn, un]. *)
let subst s t =
  let fv = List.fold_left (fun fv (x, u) -> free_vars u fv) [] s in
  let rec subst_rec s t fv =
    match t with
    | Var(y) ->
        begin try List.assoc y s
        with Not_found -> t end
    | Cst(_) -> t
    | Lam(y, t1) ->
        let y' = variant y fv in
        let s' = (y, Var(y')) :: s in
        let fv' = y' :: fv in
        Lam(y', subst_rec s' t1 fv')
    | App(t1, t2) -> App(subst_rec s t1 fv, subst_rec s t2 fv)
  in
  subst_rec s t fv

(* Applies the type substitution theta to the term t.
   See also: Type.type_inst. *)
let rec type_subst theta t =
  match t with
  | Var(idx, a) -> Var(idx, type_inst theta a)
  | Cst(c, args) -> Cst(c, List.map (type_inst theta) args)
  | Lam((idx, a), u) -> Lam((idx, type_inst theta a), type_subst theta u)
  | App(t1, t2) -> App(type_subst theta t1, type_subst theta t2)

(* Returns true when t1 and t2 are alpha equivalent. This is not very well
   written and may be improved. *)
let alpha_equiv t1 t2 =
  let fv = free_vars t1 (free_vars t2 []) in
  let rename x map =
    try List.assoc x map
    with _ -> x
  in
  let rec alpha_equiv_rec t1 t2 map1 map2 fv =
    match t1, t2 with
    | Var(x), Var(y) ->
        let x' = rename x map1 in
        let y' = rename y map2 in
        x' = y'
    | Cst(c1, theta1), Cst(c2, theta2) -> c1 = c2
    | Lam(x1, u1), Lam(x2, u2) ->
        let (_, a) = x1 in
        let (_, b) = x2 in
        if a <> b then false else
        let x = variant x1 fv in
        let map1 = (x1, x) :: map1 in
        let map2 = (x2, x) :: map2 in
        alpha_equiv_rec u1 u2 map1 map2 (x :: fv)
    | App(t1, u1), App(t2, u2) ->
        alpha_equiv_rec t1 t2 map1 map2 fv &
        alpha_equiv_rec u1 u2 map1 map2 fv
    | _ -> false
  in alpha_equiv_rec t1 t2 [] [] fv

(* Define a new constant c equal to t. SIDE-EFFECT: modifies cst_type_schemes
   and outputs the constant declaration. *)
let define_new_constant c t =
  let a = type_of t in
  let ftv = free_type_vars a [] in
  (* Note: The term t must not have any free term variables. *)
  assert (free_vars t [] = []);
  (* Note: Every type variable that appears in the type of a subterm of t must
     also appear in the type of t. *)
  assert (List.for_all (fun x -> List.mem x ftv) (free_tvars t []));
  if List.mem_assoc c !cst_type_schemes then failwith (Printf.sprintf "constant %s already defined" c) else
  cst_type_schemes := (c, (ftv, a)) :: !cst_type_schemes;
  ftv, a

let define_new_typeop opname absname repname type_vars p t =
  if List.mem_assoc opname !type_arities then failwith (Printf.sprintf "type %s already defined" opname) else
  type_arities := (opname, List.length type_vars) :: !type_arities;
  let type_args = List.map (fun x -> TyVar(x)) type_vars in
  let xtype = type_of t in
  let ytype = TyApp(opname, type_args) in
  cst_type_schemes := (repname, (type_vars, ty_arr ytype xtype)) :: (absname, (type_vars, ty_arr xtype ytype)) :: !cst_type_schemes;
  ytype, Cst(absname, type_args), Cst(repname, type_args)

(* Match the type scheme of the constant c with the type a, generating a
   type substitution for the type variables. *)
let match_constant_type c a =
  let (ty_vars, b) =
    try List.assoc c !cst_type_schemes
    with Not_found -> failwith (Printf.sprintf "constant %s not declared" c) in
  let rec match_type a b theta =
    match a, b with
    | a, TyVar(x) ->
        begin try if List.assoc x theta = a then theta else failwith "type match: inconsistent instantiation"
        with Not_found -> (x, a) :: theta end
    | TyApp(opa, argsa), TyApp(opb, argsb) ->
        if opa <> opb then failwith (Printf.sprintf "type match: type operators %s and %s do not agree" opa opb)else
        List.fold_left2 (fun theta a b -> match_type a b theta) theta argsa argsb
    | _ -> failwith "type match: not an instance" in
  let theta = match_type a b [] in
  List.map (fun x -> List.assoc x theta) ty_vars
  
(* Shortcuts *)

let eq t1 t2 =
  let a = type_of t1 in
  assert (a = type_of t2);
  App(App(Cst("eq", [a]), t1), t2)

let get_eq t =
  match t with
  | App(App(Cst("eq", _), t1), t2) -> t1, t2
  | _ -> failwith "not an equality"

