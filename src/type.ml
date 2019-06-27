(** HOL types and their translation to Dedukti *)

(** Type variables *)
type var = string

(** Type operators *)
type op = string

(** Types *)
type hol_type =
  | Var of var
  | App of op * hol_type list

let dummy_type = Var "dummy"

(** Printing types *)

let rec sprint_type () t =
  match t with
  | Var x ->
    Printf.sprintf "%s" x
  | App (top, l) ->
    Printf.sprintf "(%s %s)" top (sprint_list_type l)
  and sprint_list_type_rec = function
	 [] 		-> ""
	| t::ltq	-> String.concat "" [(sprint_type () t);"\n";(sprint_list_type_rec ltq)]
  and sprint_list_type lt = String.concat "" ["[";sprint_list_type_rec lt;"]"]

(** Arities of the declared type operators *)

let base_ops = [
    "bool", 0;
    "ind", 0;
    "->", 2;
  ]

let ops = ref base_ops

let reset_ops = ops := base_ops

let is_declared op = List.mem_assoc op !ops

(** Keep track of constants' definition *)

let defined_typeops = Hashtbl.create 100

let deps = Hashtbl.create 4000

let unresolved_deps = Hashtbl.create 1000

let add_typeop (tyop:string) (arity:int) =
	Hashtbl.add defined_typeops tyop (arity,Name.escape (Input.get_module_name()));
	try
		let prov_op = Name.escape (Input.get_module_name()) in
		let already_used = Hashtbl.find_all unresolved_deps tyop in
		let resolve_dep mod_name = Hashtbl.add deps mod_name prov_op in
		let () = List.iter resolve_dep already_used in
		let () = List.iter (fun x -> Hashtbl.remove unresolved_deps tyop) already_used in
		()
	with Not_found -> ()

let add_dep_op  (op:string) =
	let mod_name = Name.escape (Input.get_module_name()) in
	try
		let prov_op = snd (Hashtbl.find defined_typeops op) in
		let deps_mod_name = Hashtbl.find_all deps mod_name in
		if not (List.mem prov_op deps_mod_name) then
			Hashtbl.add deps mod_name prov_op
		else ()
	with Not_found -> Hashtbl.add unresolved_deps op mod_name

(** Compute the free type variables in [a] using [fv] as an accumulator. *)
let rec free_vars fv a =
  match a with
  | Var(x) -> if List.mem x fv then fv else x :: fv
  | App(op, args) -> List.fold_left free_vars fv args

(** Translation *)

module TypeSharing = Sharing.Make(
  struct
    type t = hol_type
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let translate_type_id id = Name.id "type" id

let translate_var x = Name.escape x

let translate_op op =
  match op with
  | "bool" -> Name.hol "bool"
  | "ind" -> Name.hol "ind"
  | "->" -> Name.hol "arr"
  | _ -> Name.escape op

let translate_htype () =
  match !Options.language with
  | Options.No
  | Options.Dk
  | Options.Coq -> Dedukti.var (Name.hol "type")
  | Options.Twelf -> Dedukti.var (Name.hol "htype")

(** Translate a HOL kind as a Dedukti type. *)
let translate_kind arity =
  let k = translate_htype () in
  Dedukti.arrs (Array.to_list (Array.make arity k)) k

(** Translate a HOL type as a Dedukti term. *)
let rec translate_type a =
  try
    let id = TypeSharing.find a in
    let fv = free_vars [] a in
    let id' = Dedukti.var (translate_type_id id) in
    let fv' = List.map Dedukti.var (List.map translate_var fv) in
    Dedukti.apps id' fv'
  with Not_found ->
    match a with
    | Var(x) ->
      Dedukti.var (translate_var x)
    | App(op, args) ->
      let op' = Dedukti.var (translate_op op) in
      let args' = List.map translate_type args in
      Dedukti.apps op' args'

(** Translate a HOL type as a Dedukti term with a substitution. *)
let rec translate_type_ws theta a  =
  try
    let id = TypeSharing.find a in
    let fv = free_vars [] a in
    let id' = Dedukti.var (translate_type_id id) in
    let fv' = List.map Dedukti.var (List.map (fun x -> if List.mem x theta then "hol.bool" else translate_var x) fv) in
    Dedukti.apps id' fv'
  with Not_found ->
    match a with
    | Var(x) ->
	  if List.mem x theta then Dedukti.var "hol.bool" else
      Dedukti.var (translate_var x)
    | App(op, args) ->
      let op' = Dedukti.var (translate_op op) in
      let args' = List.map (translate_type_ws theta) args  in
      Dedukti.apps op' args'

(** Translate a HOL type as a Dedukti term, without using the sharing. *)
let rec translate_type_total a =
  match a with
    | Var(x) ->
      Dedukti.var (translate_var x)
    | App(op, args) ->
      let op' = Dedukti.var (translate_op op) in
      let args' = List.map translate_type_total args in
      Dedukti.apps op' args'

(** Translate the list of type variables [x1; ...; xn]
    into the Dedukti terms [x1 : type; ...; xn : type] *)
let translate_vars vars =
  List.map (fun x -> (translate_var x, translate_kind 0)) vars

(** Declare the Dedukti term [op : |arity|]. *)
let import_op op =
  let op_arity,op_module = Hashtbl.find defined_typeops op in
  Output.print_verbose "Importing type operator %s\n%!" op;
  if !Options.language <> Options.No then (
	let op_name = String.concat "." [op_module;Name.escape op] in
	let op' = translate_op op in
	let op_def = Dedukti.Var op_name in
	Output.print_comment (Printf.sprintf "Type operator %s" op);
	Output.print_dependancy op' op_def);
  ops := (op, op_arity) :: !ops

(** Declare the Dedukti term [op : |arity|]. *)
let declare_op op arity =
  Output.print_verbose "Warning: using undeclared type operator %s\n%!" op;
  let () = add_dep_op op in
  if (Hashtbl.mem defined_typeops op) then import_op op
  else
  (Output.print_verbose "Declaring type operator %s\n%!" op;
  if !Options.language <> Options.No then
    let op' = translate_op op in
    let arity' = translate_kind arity in
    Output.print_declaration op' arity');
  ops := (op, arity) :: !ops

(** Define the Dedukti term [op : |arity|]. 
	Same as a declaration, but no import possible. *)
let define_op op arity =
  Output.print_verbose "Defining type operator %s\n%!" op;
  if !Options.language <> Options.No then
    let op' = translate_op op in
    let arity' = translate_kind arity in
    Output.print_declaration op' arity';
  ops := (op, arity) :: !ops

(** Define the Dedukti term [id := |a|]. *)
let define_type ?(local=false) a =
  if !Options.language <> Options.No && not (TypeSharing.mem a) then (
      let fv = free_vars [] a in
      let fv' = translate_vars fv in
      let arity' = translate_kind (List.length fv) in
      let a' = Dedukti.lams fv' (translate_type a) in
      let id = (TypeSharing.add a) in
      let id' = translate_type_id id in
      Output.print_definition ~untyped:true ~local:local id' arity' a');
  a

(** Smart constructors *)

let var x = Var(x)

let app op args =
  (* Check first if the type operator is declared. *)
  if not (is_declared op) then (
    declare_op op (List.length args));
  (App(op, args))

(* Use unit to avoid evaluation. *)
let bool () = app "bool" []

let ind () = app "ind" []

let arr a b = app "->" [a; b]

let get_arr a =
  match a with
  | App("->", [a; b]) -> (a, b)
  | _ -> failwith ("Not an arrow type")

(* We define the following functions after the translation as we might want to
   use sharing or smart constructors. *)

(** Type substitution *)
let rec subst theta a =
  match a with
  | Var(x) -> if List.mem_assoc x theta then List.assoc x theta else a
  | App(op, args) -> app op (List.map (subst theta) args)

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

