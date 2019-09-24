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
  | TypeOp of Type.op
  | Type of Type.hol_type
  | Const of Term.cst
  | Var of Term.var
  | Term of Term.term
  | Thm of Thm.thm

type stack = stack_object list

(** The dictionary that holds intermediate objects. *)
let dict = Hashtbl.create 10007

let dict_add k obj =
  let obj =
    match obj with
    | Type(a) -> Type(Type.define_type ~local:true a)
    | Term(t) -> Term(Term.define_term ~local:true t)
    | Thm(thm) -> Thm(Thm.define_thm "dict" ~untyped:true ~local:true thm)
    | _ -> obj in
  Hashtbl.add dict k obj

let dict_find k =
  Hashtbl.find dict k

(** Extract a number from the cmd string. *)
let process_num stack cmd =
  let i = int_of_string cmd in
  Num(i)::stack

(** Extract a name from the cmd string. *)
let process_name stack cmd =
  (* Regular expressions taken from the OpenTheory standard. *)
  let component_str = Printf.sprintf "\\([^.\"\\]\\|[\\][.\"\\]\\)*" in
  let namespace_str = Printf.sprintf "\\(%s[\\.]\\)*" component_str in
  let name_str = Printf.sprintf "\"\\(%s%s\\)\"" namespace_str component_str in
  (* Compile the regular expression and try to match the whole string. *)
  if not (Str.string_match (Str.regexp name_str) cmd 0) ||
     Str.match_end () <> String.length cmd
  then failwith (Printf.sprintf "Invalid name %s" cmd);
  (* Extract the unquoted string. *)
  let name = Str.matched_group 1 cmd in
  (* Unescape the backslash-escaped characters. *)
  let name = Str.global_replace (Str.regexp "[\\]\\(.\\)") "\\1" name in
  (*  Output.print_verbose "Processing name %s as \"%s\".\n" cmd name;*)
  Name(name)::stack

(** Process the command given the current stack and return the new stack. *)
let process_command cmd stack =
  if String.length cmd = 0 then stack else
    let c = String.get cmd 0 in
    if c = '#' then stack else (* Ignore comments *)
    if c = '\"' then process_name stack cmd else
    if Name.is_numerical c then process_num stack cmd else
(*      let () = Output.print_verbose "Processing %s\n%!" cmd in*)
      match cmd, stack with
      | "absTerm", Term(t) :: Var(x) :: stack -> Term(Term.lam x t) :: stack
      | "absThm", Thm(thm_tu) :: Var(x) :: stack -> Thm(Thm.abs_thm x thm_tu) :: stack
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
      | "namedAxiom", Name(name) :: Term(p) :: List(gamma) :: stack ->
        let extract_term obj =
          match obj with
          | Term(t) -> t
          | _ -> failwith "not a term object" in
        let gamma = List.map extract_term gamma in
        let () = Thm.add_dep_ax name in
        Thm(Thm.named_axiom gamma p name) :: stack
      | "betaConv", Term(Term.App(Term.Lam(x, t), u)) :: stack -> Thm(Thm.define_thm "dictBeta" ~untyped:true ~local:true (Thm.beta_conv x t u)) :: stack
      | "cons", List(tail) :: head :: stack -> List(head :: tail) :: stack
      | "const", Name(name) :: stack -> Const(name) :: stack
      | "constTerm", Type(a) :: Const(c) :: stack -> Term(Term.cst c a) :: stack
      | "deductAntisym", Thm(thm_q) :: Thm(thm_p) :: stack -> Thm(Thm.deduct_anti_sym thm_p thm_q) :: stack
      | "def", Num(k) :: obj :: stack ->
        dict_add k obj;
        obj :: stack
      | "defineConst", Term(t) :: Name(n) :: stack ->
		Term.add_cst n (Term.type_of t);
		Thm(Thm.define_const n t) :: Const(n) :: stack
      | "defineTypeOp", Thm(pt) :: List(tvars) :: Name(rep) :: Name(abs) :: Name(op) :: stack ->
        let extract_name obj =
          match obj with
          | Name(n) -> n
          | _ -> failwith "not a name object" in
        let tvars = List.map extract_name tvars in
        let abs_rep, rep_abs = Thm.define_type_op op abs rep tvars pt in
        Type.add_typeop op (List.length tvars);
        Thm(rep_abs) :: Thm(abs_rep) :: Const(rep) :: Const(abs) :: TypeOp(op) :: stack
      | "eqMp", Thm(thm_p) :: Thm(thm_pq) :: stack -> Thm(Thm.define_thm "dictEqMp" ~untyped:true ~local:true (Thm.eq_mp thm_pq thm_p)) :: stack
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
      | "refl", Term(t) :: stack -> Thm(Thm.define_thm "dictRefl" ~untyped:true ~local:true (Thm.refl t)) :: stack
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
        Thm(Thm.define_thm "dictSubst" ~untyped:true ~local:true (Thm.subst theta sigma thm)) :: stack
      | "thm", Term(p) :: List(qs) :: Thm(thm) :: stack ->
        let extract_term obj =
          match obj with
          | Term(t) -> t
          | _ -> failwith "not a term" in
        let qs = List.map extract_term qs in
        let _ = Thm.thm qs p thm in
        stack
      | "namedThm", Name(n) :: Term(p) :: List(qs) :: Thm(thm) :: stack ->
        let extract_term obj =
          match obj with
          | Term(t) -> t
          | _ -> failwith "not a term" in
        let qs = List.map extract_term qs in
        let _ = Thm.namedthm qs p thm n in
        let () = Thm.add_thm n in
        Printf.printf "Defining theorem %s\n" n;
        stack
      | "typeOp", Name(op) :: stack -> TypeOp(op) :: stack
      | "var", Type(a) :: Name(x) :: stack -> Var((x, a)) :: stack
      | "varTerm", Var(x) :: stack -> Term(Term.var x) :: stack
      | "varType", Name(x) :: stack -> Type(Type.var x) :: stack

      (* Version 6 features captured here *)
      | "pragma", _ :: stack -> stack (*simply ignore it*)
      | "hdTl" , List(hd :: tail) ::stack -> List(tail):: hd :: stack
      | "proveHyp", Thm (thm_q) :: Thm (thm_p) :: stack -> Thm(Thm.define_thm "dictPH" ~untyped:true ~local:true (Thm.proveHyp thm_q thm_p)) :: stack
      | "sym", Thm (thm1) :: stack -> Thm (Thm.sym thm1) :: stack
      | "trans", Thm (thm_t2't3) :: Thm(thm_t1t2) :: stack -> Thm (Thm.define_thm "dictTRANS" ~untyped:true ~local:true (Thm.trans thm_t1t2 thm_t2't3)) :: stack
      | "version" , _ :: stack -> stack (*ignore the version thing*)
      (* | "defineConst", Term(t) :: Name(n) :: stack -> Thm(Thm.define_const n t) :: Const(n) :: stack *)
      | "defineConstList", Thm(thm) :: List(nv_List) :: stack ->
        (* let () = Printf.printf "defineConstList Used here \n" in  *)
        let rm_List x = match x with List([Name(n); Var(x,a)]) -> (n, (x,a)) in
        let nv_list = List.map rm_List nv_List in
        let const_list x  = match x with List([Name(n); Var(x,a)]) -> Const(n) in
        let c_list = List.map const_list nv_List in
        Thm (Thm.define_const_list thm nv_list) :: List(c_list) :: stack
      
      (* ND rules *)
      | "truth", _ -> Thm (Thm.truth_thm) :: stack
      | "conj",Thm(thm1)::Thm(thm2)::stack ->  Thm(Thm.conj thm1 thm2) :: stack
      | "conjunct1",Thm(thm) :: stack -> Thm(Thm.define_thm "dictConj1" ~untyped:true ~local:true (Thm.conjunct1 thm)) :: stack
      | "conjunct2",Thm(thm) :: stack -> Thm(Thm.define_thm "dictConj2" ~untyped:true ~local:true (Thm.conjunct2 thm)) :: stack
      | "contr", Term(tm) :: Thm(thm) :: stack ->
		Thm(Thm.contr tm thm) :: stack
      | "disch", Term(tm) :: Thm(thm) :: stack ->
		Thm(Thm.disch thm tm) :: stack
      | "mp", Thm(thm1) :: Thm(thm2) :: stack ->
		Thm(Thm.define_thm "dictMp" ~untyped:true ~local:true (Thm.mp thm1 thm2)) :: stack
      | "disjcases",Thm(thm2)::Thm(thm1)::Thm(thm)::stack -> Thm(Thm.define_thm "dictDisj" ~untyped:true ~local:true (Thm.disjcases thm thm1 thm2)) :: stack
      | "disj1",Term(tm) :: Thm(thm) :: stack -> Thm(Thm.disj1 thm tm) :: stack
      | "disj2",Term(tm) :: Thm(thm) :: stack -> Thm(Thm.disj2 thm tm) :: stack
      | "gen",Term(tm) :: Thm(thm) :: stack -> Thm(Thm.define_thm "dictGen" ~untyped:true ~local:true (Thm.gen tm thm)) :: stack
      | "spec",Thm(thm) :: Term(tm) :: stack -> Thm(Thm.define_thm "dictSpec" ~untyped:true ~local:true (Thm.spec tm thm)) :: stack
      | "exists",Thm(thm) :: Term(y) :: Term(etm) :: stack -> Thm(Thm.define_thm "dictExists" ~untyped:true ~local:true (Thm.exists etm y thm)) :: stack
      | "choose",Thm(thm2) :: Thm(thm1) :: Term(v) :: stack -> Thm(Thm.define_thm "dictChoose" ~untyped:true ~local:true (Thm.choose v thm1 thm2)) :: stack
      
      | c, _ -> failwith (Printf.sprintf "invalid command/state: %s" c)



(** Read and process the article file. *)

let rec require_deps = function
	  []		-> Output.print_command "REQUIRE" ["hol"] true
	| dep::qdep	-> if dep <> ((Name.escape (Output.low_dash (Input.get_module_name ()))))
		then Output.print_command "REQUIRE" [dep] false; require_deps qdep

let process_file () =
  (* Preamble *)
  if !Options.language <> Options.No then (
    Output.print_comment "This file was generated by Holide.";
    match !Options.language with
    | Options.No
    | Options.Twelf -> ()
    | Options.Dk -> ()
    | Options.Coq ->
       Output.print_command "Require Import" ["hol"] true);
  (* Main section *)
  require_deps (Sort.dependencies (Name.escape (Output.low_dash (Input.get_module_name ()))));
  let rec process_commands stack =
    let cmd = Input.read_line () in
    let stack = process_command cmd stack in
    process_commands stack in
  try process_commands []
  with End_of_file ->
    let () = Input.close () in
	let () = Term.csts := Term.base_csts in
	let () = Type.ops := Type.base_ops in
	let () = Term.interpretation := Term.base_interpretation in
	let () = List.iter (fun (c, (a, c')) -> Term.csts := (c, a) :: !Term.csts) !Term.interpretation in
	let () = Thm.thm_names := [] in
	let () = Hashtbl.clear dict in
	let () = Thm.ThmSharing.clear (Thm.dummy_th,false) in
	let () = Term.TermSharing.clear Term.dummy_term in
	let () = Type.TypeSharing.clear Type.dummy_type in
	close_out !Options.output_channel



(** Read and build a database for theorems and axioms of given files *)

(** List of processed articles *)

let articles = ref []

let add_article name = let () = articles := (!articles)@[name] in ()

let process_names_file () =
  let rec process_commands stack =
    let cmd = Input.read_line () in
    let stack = process_command cmd stack in
    process_commands stack in
  try process_commands []
  with End_of_file ->
    let () = Input.close () in
	let () = Term.csts := Term.base_csts in
	let () = Type.ops := Type.base_ops in
	let () = Term.interpretation := Term.base_interpretation in
	let () = List.iter (fun (c, (a, c')) -> Term.csts := (c, a) :: !Term.csts) !Term.interpretation in
	let () = Thm.thm_names := [] in
	let () = Hashtbl.clear dict in
	let () = Thm.ThmSharing.clear (Thm.dummy_th,false) in
	let () = Term.TermSharing.clear Term.dummy_term in
	let () = Type.TypeSharing.clear Type.dummy_type in
	add_article (!Input.input_file)


