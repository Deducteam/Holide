open Printf
open Type
open Term
open Proof
open Thm

type stack_object =
  | OName of string
  | ONum of int
  | OList of stack_object list
  | OTypeOp of string
  | OType of htype
  | OConst of string
  | OVar of var
  | OTerm of term
  | OThm of thm

type stack = stack_object list

let dict = Hashtbl.create 10007

(* Use the opentheory dictionary compression. Will create intermediary steps
   named dict_<number> for every entry in the opentheory dictionary. *)
let use_dict = ref false

(* Fully factorize proof into elementary steps. Will create intermediary steps
   named step_<number> for every application of a deduction rule. *)
let use_step = ref false

let create_step name thm =
  let Thm(gamma, p, proof) = thm in
  print_thm name thm;
  let proof = open_abstract gamma p (PVar(name)) in
  Thm(gamma, p, proof)

let step cmd thm =
  if not !use_step then thm else
  begin Output.output_comment cmd;
  create_step (Name.fresh_step ()) thm end

let dict_add k obj =
  let value =
    if not !use_dict then obj else
    match obj with
    | OThm(thm) ->
        let name = Name.export_dict k in
        OThm(create_step name thm)
    | _ -> obj in
  Hashtbl.add dict k value

let dict_find k = Hashtbl.find dict k

(* Crude printing of the stack, for debugging. *)
let print_stack stack =
  let rec print_stack stack =
    match stack with
    | [] -> ()
    | head :: tail -> print_object head; eprintf "\n"; print_stack tail
  and print_object obj =
    match obj with
    | OName(n) -> eprintf "OName(\"%s\")" n
    | ONum(i) -> eprintf "ONum(%d)" i
    | OList(objs) -> eprintf "OList(["; print_object_list objs; eprintf "])"
    | OTypeOp(tyop) -> eprintf "OTypeOp(%s)" tyop
    | OType(_) -> eprintf "OType"
    | OConst(c) -> eprintf "OConst(%s)" c
    | OVar(x, _) -> eprintf "OVar(%s, _)" x
    | OTerm(_) -> eprintf "OTerm"
    | OThm(_) -> eprintf "OThm"
  and print_object_list objs = 
    match objs with
    | [] -> ()
    | [head] -> print_object head
    | head :: tail -> print_object head; eprintf "; "; print_object_list tail in
  eprintf "Stack:\n";
  print_stack stack

let is_digit c =
  match c with
  | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
  | _ -> false

let process_num stack cmd =
  ONum(int_of_string cmd) :: stack

(* Escape non-alphanumerical characters. *)
let escape name =
  let hex = "0123456789abcdef" in
  let s = String.create 256 in
  let j = ref 0 in
  for i = 0 to String.length name - 1 do
    let c = name.[i] in
    let code = Char.code c in
    if c = '_' then (s.[!j] <- '_'; s.[!j + 1] <- '_'; j := !j + 2) else
    if (Char.code '0' <= code && code <= Char.code '9') ||
        (Char.code 'a' <= code && code <= Char.code 'z') ||
        (Char.code 'A' <= code && code <= Char.code 'Z')
      then (s.[!j] <- c; j := !j + 1) else
    (s.[!j] <- '_'; s.[!j + 1] <- hex.[code / 16]; s.[!j + 2] <- hex.[code mod 16]; j := !j + 3) done;
  String.sub s 0 !j

(* Extract the name from the cmd string. *)
let process_name stack cmd =
  let components = Str.split (Str.regexp "[\".]") cmd in
  let s, sl =
    match List.rev components with
    | s :: sl -> s, sl
    | _ -> failwith "invalid name" in
  let sl = List.rev sl in
  let name = match sl, s with
    | [], "bool" -> "bool"
    | [], "ind" -> "ind"
    | [], "->" -> "arr"
    | [], "=" -> "eq"
    | [], "select" -> "select"
    | ["Data"; "Bool"], "T" -> "top"
    | ["Data"; "Bool"], "F" -> "bot"
    | ["Data"; "Bool"], "~" -> "not"
    | ["Data"; "Bool"], "/\\\\" -> "and"
    | ["Data"; "Bool"], "\\\\/" -> "or"
    | ["Data"; "Bool"], "==>" -> "imp"
    | ["Data"; "Bool"], "<=>" -> "iff"
    | ["Data"; "Bool"], "!" -> "forall"
    | ["Data"; "Bool"], "?" -> "exists"
    | ["Data"; "Bool"], "?!" -> "exists_unique"
    | _ :: _, _ -> (escape (List.nth sl (List.length sl - 1))) ^ "_" ^ (escape s)
    | _ -> escape s in
  OName(name) :: stack

let process_command stack cmd =
  let c = String.get cmd 0 in
  if c = '#' then stack else
  if c = '\"' then process_name stack cmd else
  if is_digit c then process_num stack cmd else
  match cmd, stack with
  | "absTerm", OTerm(t) :: OVar(x) :: stack -> OTerm(Lam(x, t)) :: stack
  | "absThm", OThm(thmtu) :: OVar(x) :: stack -> OThm(step cmd (absThm x thmtu)) :: stack
  | "appTerm", OTerm(u) :: OTerm(t) :: stack -> OTerm(App(t, u)) :: stack
  | "appThm", OThm(thmtu) :: OThm(thmfg) :: stack -> OThm(step cmd (appThm thmfg thmtu)) :: stack
  | "assume", OTerm(p) :: stack -> OThm(step cmd (assume p)) :: stack
  | "axiom", OTerm(p) :: OList(qs) :: stack ->
      let extract_term obj =
        match obj with
        | OTerm(q) -> q
        | _ -> failwith "not a term object" in
      OThm(step cmd (axiom (List.map extract_term qs) p)) :: stack
  | "betaConv", OTerm(xtu) :: stack -> OThm(step cmd (betaConv xtu)) :: stack
  | "cons", OList(tail) :: head :: stack -> OList(head :: tail) :: stack
  | "const", OName(name) :: stack -> OConst(name) :: stack
  | "constTerm", OType(ty) :: OConst(c) :: stack ->
      let ty_args = match_constant_type c ty in
      OTerm(Cst(c, ty_args)) :: stack
  | "deductAntisym", OThm(thmq) :: OThm(thmp) :: stack -> OThm(step cmd (deductAntiSym thmp thmq)) :: stack
  | "def", ONum(k) :: obj :: stack ->
      dict_add k obj;
      obj :: stack
  | "defineConst", OTerm(t) :: OName(n) :: stack ->
      eprintf "Defining constant %s..." n; prerr_newline ();
      let thm = defineConst n t in
      OThm(step cmd thm) :: OConst(n) :: stack
  | "defineTypeOp", OThm(thmpt) :: OList(type_vars) :: OName(repname) :: OName(absname) :: OName(opname) :: stack ->
      eprintf "Defining type %s..." opname; prerr_newline ();
      let extract_name obj =
        match obj with
        | OName(n) -> n
        | _ -> failwith "not a name object" in
      let thmrepabs, thmabsrep = defineTypeOp opname absname repname (List.map extract_name type_vars) thmpt in
      OThm(step cmd thmrepabs) :: OThm(step cmd thmabsrep) :: OConst(repname) :: OConst(absname) :: OTypeOp(opname) :: stack
  | "eqMp", OThm(thmp) :: OThm(thmpq) :: stack -> OThm(step cmd (eqMp thmpq thmp)) :: stack
  | "nil", stack -> OList([]) :: stack
  | "opType", OList(args) :: OTypeOp(tyop) :: stack ->
      let extract_type obj = 
        match obj with
        | OType(ty) -> ty
        | _ -> failwith "not a type object" in
      OType(TyApp(tyop, List.map extract_type args)) :: stack
  | "pop", _ :: stack -> stack
  | "ref", ONum(k) :: stack -> dict_find k :: stack
  | "refl", OTerm(t) :: stack -> OThm(step cmd (refl t)) :: stack
  | "remove", ONum(k) :: stack ->
      let obj = dict_find k in
      Hashtbl.remove dict k;
      obj :: stack
  | "subst", OThm(thm) :: OList([OList(theta); OList(sigma)]) :: stack ->
      let extract_type_subst obj =
        match obj with
        | OList([OName(a); OType(ty)]) -> (a, ty)
        | _ -> failwith "not a type substitution" in
      let extract_term_subst obj =
        match obj with
        | OList([OVar(x); OTerm(t)]) -> (x, t)
        | _ -> failwith "not a term substitution" in
      let theta = List.map extract_type_subst theta in
      let sigma = List.map extract_term_subst sigma in
      OThm(step cmd (substThm theta sigma thm)) :: stack
  | "thm", OTerm(p) :: OList(qs) :: OThm(thm) :: stack ->
      print_thm (Name.fresh_thm ()) thm;
      stack
  | "typeOp", OName(tyop) :: stack -> OTypeOp(tyop) :: stack
  | "var", OType(ty) :: OName(x) :: stack -> OVar((x, ty)) :: stack
  | "varTerm", OVar(x) :: stack -> OTerm(Var(x)) :: stack
  | "varType", OName(a) :: stack -> OType(TyVar(a)) :: stack
  | _ -> failwith "invalid command/state"

let read_article filename =
  let file = open_in filename in
  let rec loop line_number stack =
    let cmd = input_line file in
    let state =
      if line_number mod 10000 = 0 then (eprintf "Processing line %d...\n" line_number; flush_all ()) else ();
      try process_command stack cmd
      with
      | e ->
          flush_all ();
          print_newline ();
          print_stack stack;
          eprintf "In article %s, at line %d: %s\n" filename line_number cmd;
          raise e in
    loop (line_number + 1) state in
  try loop 1 [] with End_of_file -> ();
  close_in file


