(** This module implements the OpenTheory article virtual machine.
    The description of the machine can be found at:
    http://www.gilith.com/research/opentheory/article.html
    This code is inspired by the import code of HOL Light:
    http://src.gilith.com/hol-light.html *)

type thm = Thm.thm

(** The objects and stack of the virtual machine. *)
type stack_object =
| Name of string
| Num of int
| List of stack_object list
| TypeOp of string
| Type of Type.hol_type
| Const of string
| Var of string * Type.hol_type
| Term of Term.term
| Thm of Thm.thm

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
  if not (Str.string_match (Str.regexp name_str) cmd 0) ||
    Str.match_end () != String.length cmd
    then failwith (Printf.sprintf "Invalid name %s" cmd);
  (* Extract the unquoted string. *)
  let name = Str.matched_group 1 cmd in
  (* Unescape the backslash-escaped characters. *)
  let name = Str.global_replace (Str.regexp "[\\]\\(.\\)") "\\1" name in
(*  Output.print_verbose "Processing name %s as \"%s\".\n" cmd name;*)
  Name(name) :: stack

(** Process the command given the current stack and return the new stack. *)
let process_command cmd stack =
  if String.length cmd = 0 then stack else
  let c = String.get cmd 0 in
  if c = '#' then stack else (* Ignore comments *)
  if c = '\"' then process_name stack cmd else
  if Name.is_numerical c then process_num stack cmd else
(*  let _ = Output.print_verbose "Processing %s\n%!" cmd in*)
(*  let _ = Output.print_comment cmd in*)
  match cmd, stack with
  | "absTerm", Term(t) :: Var(x, a) :: stack -> Term(Term.lam x a t) :: stack
  | "absThm", Thm(thm_tu) :: Var(x, a) :: stack -> Thm(Thm.abs_thm x a thm_tu) :: stack
  | "appTerm", Term(u) :: Term(t) :: stack -> Term(Term.app t u) :: stack
  | "appThm", Thm(thm_tu) :: Thm(thm_fg) :: stack -> Thm(Thm.app_thm thm_fg thm_tu) :: stack
  | "assume", Term(p) :: stack -> Thm(Thm.assume p) :: stack
  | "axiom", Term(p) :: List(gamma) :: stack ->
      let extract_term obj =
        match obj with
        | Term(t) -> t
        | _ -> failwith "not a term object" in
      let gamma = List.map extract_term gamma in
      Thm(Thm.axiom gamma p) :: stack
  | "betaConv", Term(Term.App(Term.Lam(x, a, t), u)) :: stack -> Thm(Thm.beta_conv x a t u) :: stack
  | "cons", List(tail) :: head :: stack -> List(head :: tail) :: stack
  | "const", Name(name) :: stack -> Const(name) :: stack
  | "constTerm", Type(a) :: Const(c) :: stack -> Term(Term.cst c a) :: stack
  | "deductAntisym", Thm(thm_q) :: Thm(thm_p) :: stack -> Thm(Thm.deduct_anti_sym thm_p thm_q) :: stack
  | "def", Num(k) :: obj :: stack ->
      dict_add k obj;
      obj :: stack
  | "defineConst", Term(t) :: Name(n) :: stack -> Thm(Thm.define_const n t) :: Const(n) :: stack
(*  | "defineTypeOp", Thm :: List(type_vars) :: Name(rep_name) :: Name(abs_name) :: Name(op_name) :: stack ->*)
(*      let extract_name obj =*)
(*        match obj with*)
(*        | Name(n) -> n*)
(*        | _ -> failwith "not a name object" in*)
(*      let _ = List.map extract_name type_vars in*)
(*      Thm :: Thm :: Const(rep_name) :: Const(abs_name) :: TypeOp(op_name) :: stack*)
  | "eqMp", Thm(thm_p) :: Thm(thm_pq) :: stack -> Thm(Thm.eq_mp thm_p thm_pq) :: stack
  | "nil", stack -> List([]) :: stack
  | "opType", List(args) :: TypeOp(type_op) :: stack ->
      let extract_type obj =
        match obj with
        | Type(a) -> a
        | _ -> failwith "not a type object" in
      let args = List.map extract_type args in
      Type(Type.app type_op args) :: stack
  | "pop", _ :: stack -> stack
  | "ref", Num(k) :: stack -> dict_find k :: stack
  | "refl", Term(t) :: stack -> Thm(Thm.refl t) :: stack
  | "remove", Num(k) :: stack ->
      let obj = dict_find k in
      Hashtbl.remove dict k;
      obj :: stack
  | "subst", Thm(thm) :: List([List(theta); List(sigma)]) :: stack ->
      let extract_type_subst obj =
        match obj with
        | List([Name(x); Type(a)]) -> (x, a)
        | _ -> failwith "not a type substitution" in
      let extract_term_subst obj =
        match obj with
        | List([Var(x, a); Term(t)]) -> ((x, a), t)
        | _ -> failwith "not a term substitution" in
      let theta = List.map extract_type_subst theta in
      let sigma = List.map extract_term_subst sigma in
      Thm(Thm.subst sigma (Thm.type_subst theta thm)) :: stack
  | "thm", Term(p) :: List(qs) :: Thm(thm) :: stack ->
      let extract_term obj =
        match obj with
        | Term(t) -> t
        | _ -> failwith "not a term" in
      let _ = List.map extract_term qs in
      let _ = Thm.thm thm in
      stack
  | "typeOp", Name(op) :: stack -> TypeOp(op) :: stack
  | "var", Type(a) :: Name(x) :: stack -> Var(x, a) :: stack
  | "varTerm", Var(x, a) :: stack -> Term(Term.var x a) :: stack
  | "varType", Name(x) :: stack -> Type(Type.var x) :: stack
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

