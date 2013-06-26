(** HOL Types *)

type type_var = string

type type_op = string

type hol_type =
| TypeVar of type_var
| TypeApp of type_op * hol_type list

module TypeSharing = Sharing.Make(
  struct
    type t = hol_type
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let type_ops = ref ["bool", 0; "->", 2]

let is_declared c = List.mem_assoc c !type_ops

let rec free_type_vars xs a =
  match a with
  | TypeVar(x) -> if List.mem x xs then xs else x :: xs
  | TypeApp(c, args) -> List.fold_left free_type_vars xs args

(** Translation *)

let translate_type_id id = Printf.sprintf "type_%d" id

let translate_type_var x = Name.escape x

let translate_type_op c =
  match c with
  | "bool" -> Name.hol "bool"
  | "->" -> Name.hol "arr"
  | _ -> Name.escape c

let declare_type_op c arity =
  Output.print_verbose "Declaring type operator %s\n" c;
  let hol_type = Dedukti.var (Name.hol "type") in
  let c' = translate_type_op c in
  let arity' = Dedukti.arrs (Array.to_list (Array.make arity hol_type)) hol_type in
  Output.print_declaration c' arity';
  type_ops := (c, arity) :: !type_ops

let rec translate_type a =
  try
    let id = TypeSharing.find a in
    let id' = translate_type_id id in
    let xs = free_type_vars [] a in
    let xs' = List.map translate_type_var xs in
    Dedukti.apps (Dedukti.var id') (List.map Dedukti.var xs')
  with Not_found ->
    match a with
    | TypeVar(x) ->
        let x' = translate_type_var x in
        Dedukti.var x'
    | TypeApp(c, args) ->
        let c' = translate_type_op c in
        let args' = List.map translate_type args in
        Dedukti.apps (Dedukti.var c') args'

let define_type id a =
  let hol_type = Dedukti.var (Name.hol "type") in
  let id' = translate_type_id id in
  let xs = free_type_vars [] a in
  let xs' = List.map (fun x -> (translate_type_var x, hol_type)) xs in
  let arity' = Dedukti.pies xs' hol_type in
  let a' = Dedukti.lams xs' (translate_type a) in
  Output.print_definition false id' arity' a'

(** Smart constructors *)

let type_var x = TypeVar(x) (* We don't need sharing for variables. *)

let type_app c args =
  (* Check first if the type operator is declared. *)
  if not (is_declared c) then (
    Output.print_verbose "Warning: using undeclared type operator %s\n" c;
    declare_type_op c (List.length args));
  TypeSharing.add define_type (TypeApp(c, args))

