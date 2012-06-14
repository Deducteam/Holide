(* Syntax of HOL types *)

type htype =
| TyVar of string
| TyApp of string * htype list

let type_arities =
  ref ["arr",  2; "bool", 0; "ind", 0]

(* Return all the type variables in the type a. Type variables are reported
   only once in the order that they appear in. *)
let rec free_type_vars a ftv =
  match a with
  | TyVar(x) -> if List.mem x ftv then ftv else x :: ftv
  | TyApp(tyop, args) -> List.fold_right (fun a ftv -> free_type_vars a ftv) args ftv

(* Apply the (parallel) type substitution theta to the type a. The substitution
   must be given as a list of the form [x1, a1; ...; xn, an]. *)
let rec type_inst theta a =
  match a with
  | TyVar(x) -> begin try List.assoc x theta with Not_found -> a end
  | TyApp(tyop, args) -> TyApp(tyop, List.map (type_inst theta) args)

let ty_app op args =
  let arity =
    try List.assoc op !type_arities
    with Not_found -> failwith (Printf.sprintf "type %s not declared" op) in
  if List.length args != arity then failwith "invalid number of type arguments" else
  TyApp(op, args)

(* Shortcuts *)

let ty_bool = TyApp("bool", [])

let ty_arr a b = TyApp("arr", [a; b])

let is_bool b =
  match b with
  | TyApp("bool", []) -> true
  | _ -> false

let get_arr ab =
  match ab with
  | TyApp("arr", [a; b]) -> a, b
  | _ -> failwith "not an arrow type"
