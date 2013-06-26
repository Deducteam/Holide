(** This module implements the OpenTheory article virtual machine.
    The description of the machine can be found at:
    http://www.gilith.com/research/opentheory/article.html
    This code is inspired by the import code of HOL Light:
    http://src.gilith.com/hol-light.html *)


(** The objects and stack of the virtual machine. *)
type stack_object =
| Name of string
| Num of int
| List of stack_object list
| TypeOp of string
| Type
| Const of string
| Var of string
| Term
| Thm

type stack = stack_object list

(** The dictionary that holds intermediate objects. *)
let dict = Hashtbl.create 10007

let dict_add k obj =
  Hashtbl.add dict k obj

let dict_find k =
  Hashtbl.find dict k

(** Extract a number from the cmd string. *)
let process_num stack cmd =
  let i = int_of_string cmd in
  Num(i) :: stack

(** Extract a name from the cmd string. *)
let process_name stack cmd =
  (* Regular expressions taken from the OpenTheory standard. *)
  let component_str = Printf.sprintf "\\([^.\"\\]\\|[\\][.\"\\]\\)*" in
  let namespace_str = Printf.sprintf "\\(%s[\\.]\\)*" component_str in
  let name_str = Printf.sprintf "\"\\(%s%s\\)\"" namespace_str component_str in
  (* Compile the regular expression and try to match the whole string. *)
  let name_regexp = Str.regexp name_str in
  if not (Str.string_match name_regexp cmd 0) ||
    Str.match_end () != String.length cmd
    then failwith (Printf.sprintf "Invalid name %s" cmd);
  (* Extract the unquoted string. *)
  let name = Str.matched_group 1 cmd in
  (* Unescape the backslash-escaped characters. *)
  let name = Str.global_replace (Str.regexp "[\\]\\(.\\)") "\\1" name in
  (* Escape the non-alphanumerical characters. *)
  let name = Name.escape name in
  Output.print_verbose "Processing name %s as \"%s\".\n" cmd name;
  Name(name) :: stack

(** Process the command given the current stack and return the new stack. *)
let process_command cmd stack =
  if String.length cmd = 0 then stack else
  let c = String.get cmd 0 in
  if c = '#' then stack else (* Ignore comments *)
  if c = '\"' then process_name stack cmd else
  if Name.is_numerical c then process_num stack cmd else
  match cmd, stack with
  | "absTerm", Term :: Var(x) :: stack -> Term :: stack
  | "absThm", Thm :: Var(x) :: stack -> Thm :: stack
  | "appTerm", Term :: Term :: stack -> Term :: stack
  | "appThm", Thm :: Thm :: stack -> Thm :: stack
  | "assume", Term :: stack -> Thm :: stack
  | "axiom", Term :: List(gamma) :: stack ->
      let extract_term obj =
        match obj with
        | Term -> ()
        | _ -> failwith "not a term object" in
      let _ = List.map extract_term gamma in
      Thm :: stack
  | "betaConv", Term :: stack -> Thm :: stack
  | "cons", List(tail) :: head :: stack -> List(head :: tail) :: stack
  | "const", Name(name) :: stack -> Const(name) :: stack
  | "constTerm", Type :: Const(c) :: stack -> Term :: stack
  | "deductAntisym", Thm :: Thm :: stack -> Thm :: stack
  | "def", Num(k) :: obj :: stack ->
      dict_add k obj;
      obj :: stack
  | "defineConst", Term :: Name(n) :: stack -> Thm :: Const(n) :: stack
  | "defineTypeOp", Thm :: List(type_vars) :: Name(rep_name) :: Name(abs_name) :: Name(op_name) :: stack ->
      let extract_name obj =
        match obj with
        | Name(n) -> n
        | _ -> failwith "not a name object" in
      let _ = List.map extract_name type_vars in
      Thm :: Thm :: Const(rep_name) :: Const(abs_name) :: TypeOp(op_name) :: stack
  | "eqMp", Thm :: Thm :: stack -> Thm :: stack
  | "nil", stack -> List([]) :: stack
  | "opType", List(args) :: TypeOp(type_op) :: stack -> Type :: stack
  | "pop", _ :: stack -> stack
  | "ref", Num(k) :: stack -> dict_find k :: stack
  | "refl", Term :: stack -> Thm :: stack
  | "remove", Num(k) :: stack ->
      let obj = dict_find k in
      Hashtbl.remove dict k;
      obj :: stack
  | "subst", Thm :: List([List(theta); List(sigma)]) :: stack ->
      let extract_type_subst obj =
        match obj with
        | List([Name(a); Type]) -> a
        | _ -> failwith "not a type substitution" in
      let extract_term_subst obj =
        match obj with
        | List([Var(x); Term]) -> x
        | _ -> failwith "not a term substitution" in
      let _ = List.map extract_type_subst theta in
      let _ = List.map extract_term_subst sigma in
      Thm :: stack
  | "thm", Term :: List(qs) :: Thm :: stack -> stack
  | "typeOp", Name(type_op) :: stack -> TypeOp(type_op) :: stack
  | "var", Type :: Name(x) :: stack -> Var(x) :: stack
  | "varTerm", Var(x) :: stack -> Term :: stack
  | "varType", Name(a) :: stack -> Type :: stack
  | _ -> failwith "invalid command/state"

(** Read and process the article file. *)
let translate_file () =
  (* Preamble *)
  Output.print_comment "This file was generated by Holide.";
  Output.print_command "NAME" [Input.get_module_name ()];
  Output.print_command "IMPORT" ["hol"];
  (* Main section *)
  let rec process_commands stack =
    let cmd = Input.read_line () in
    let stack = process_command cmd stack in
    process_commands stack in
  try process_commands []
  with End_of_file -> ()

