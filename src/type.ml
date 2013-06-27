(** HOL Types *)

type var = string

type op = string

type hol_type =
| Var of var
| App of op * hol_type list

module TypeSharing = Sharing.Make(
  struct
    type t = hol_type
    let equal = (=)
    let hash = Hashtbl.hash
  end)

(** Arities of the declared type operators. *)
let ops = ref [
  "bool", 0;
  "ind", 0;
  "->", 2;
  ]

let is_declared op = List.mem_assoc op !ops

(** Free variables *)

let rec free_vars xs a =
  match a with
  | Var(x) -> if List.mem x xs then xs else x :: xs
  | App(op, args) -> List.fold_left free_vars xs args

(** Translation *)

let translate_type_id id = Name.id "type" id

let translate_var x = Name.escape x

let translate_op op =
  match op with
  | "bool" -> Name.hol "bool"
  | "ind" -> Name.hol "ind"
  | "->" -> Name.hol "arr"
  | _ -> Name.escape op

(** Translate a HOL kind as a Dedukti type. *)
let translate_kind arity =
  let k = Dedukti.var (Name.hol "type") in
  Dedukti.arrs (Array.to_list (Array.make arity k)) k

(** Translate a HOL type as a Dedukti term. *)
let rec translate_type a =
  try
    let id = TypeSharing.find a in
    let xs = free_vars [] a in
    let id' = Dedukti.var (translate_type_id id) in
    let xs' = List.map Dedukti.var (List.map translate_var xs) in
    Dedukti.apps id' xs'
  with Not_found ->
    match a with
    | Var(x) ->
        Dedukti.var (translate_var x)
    | App(op, args) ->
        let op' = Dedukti.var (translate_op op) in
        let args' = List.map translate_type args in
        Dedukti.apps op' args'

let declare_op op arity =
  Output.print_verbose "Declaring type operator %s\n" op;
  let op' = translate_op op in
  let arity' = translate_kind arity in
  Output.print_declaration op' arity';
  ops := (op, arity) :: !ops

let define_type id a =
  let id' = translate_type_id id in
  let xs = free_vars [] a in
  let xs' = List.map (fun x -> (translate_var x, translate_kind 0)) xs in
  let arity' = translate_kind (List.length xs) in
  let a' = Dedukti.lams xs' (translate_type a) in
  Output.print_definition false id' arity' a'

(** Smart constructors *)

(* We don't need sharing for variables. *)
let var x = Var(x)

let app op args =
  (* Check first if the type operator is declared. *)
  if not (is_declared op) then (
    Output.print_verbose "Warning: using undeclared type operator %s\n" op;
    declare_op op (List.length args));
  TypeSharing.add define_type (App(op, args))

(* Use unit to avoid evaluation while the environment is not set up yet. *)
let bool () = app "bool" []

let ind () = app "ind" []

let arr a b = app "->" [a; b]

(** Substitutions *)

let rec type_subst theta a =
  match a with
  | Var(x) -> if List.mem_assoc x theta then List.assoc x theta else a
  | App(op, args) -> app op (List.map (type_subst theta) args)

(** Match the type [a] against [b], generating a type substitution for the type
    variables in [b]. *)
let rec match_type theta a b =
  match a, b with
  | a, Var(x) -> (
      try
        if List.assoc x theta = a then theta
        else failwith "type match: inconsistent instantiation"
      with Not_found -> (x, a) :: theta)
  | App(op_a, args_a), App(op_b, args_b) ->
      if op_a <> op_b
      then failwith (Printf.sprintf "type match: type operators %s and %s do not agree" op_a op_b)
      else List.fold_left2 match_type theta args_a args_b
  | _ -> failwith "type match: not an instance"

