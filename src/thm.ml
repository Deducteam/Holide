
open Type
open Term
open Proof
open Output

(* A theorem consists of a hypothesis context, a statement, and a proof term
   showing that the statement is correct. *)

type context = term list

type thm =
  | Thm of context * term * pterm

let rec context_union gamma delta =
  match delta with
  | [] -> gamma
  | h :: t ->
      let union = context_union t gamma in
      if List.exists (alpha_equiv h) union then union else h :: union

let rec context_remove gamma p =
  List.filter (fun q -> not (alpha_equiv p q)) gamma

(* Deduction rules *)

let absThm x thmtu =
  let Thm(gamma, tu, htu) = thmtu in
  let t, u = try get_eq tu with Failure s -> failwith ("absThm" ^ s) in
  let _, a = x in
  let a' = export_raw_type a in
  let a'' = export_type a in
  let b' = export_raw_type (type_of t) in
  let lt' = export_term (Lam(x, t)) in
  let lu' = export_term (Lam(x, u)) in
  Thm(gamma, eq (Lam(x, t)) (Lam(x, u)),
    PApp(PApp(PApp(PApp(PApp(PVar("hol.FUN_EXT"), a'), b'), lt'), lu'), PLam(Name.export_var x, a'', htu)))

let appThm thmfg thmtu =
  let Thm(gamma, fg, hfg) = thmfg in
  let Thm(delta, tu, htu) = thmtu in
  let f, g = try get_eq fg with Failure s -> failwith ("appThm: " ^ s) in
  let t, u = try get_eq tu with Failure s -> failwith ("appThm: " ^ s) in
  let a, b = try get_arr (type_of f) with Failure s -> failwith ("appThm: " ^ s) in
  let a', b' = export_raw_type a, export_raw_type b in
  let f', g' = export_term f, export_term g in
  let t', u' = export_term t, export_term u in
  assert (a = type_of t);
  Thm(context_union gamma delta, eq (App(f, t)) (App(g, u)),
    PApp(PApp(PApp(PApp(PApp(PApp(PApp(PApp(PVar("hol.APP_THM"), a'), b'), f'), g'), t'), u'), hfg), htu))

let assume p =
  assert (is_bool (type_of p));
  Thm([p], p,
    PHyp(p))

let betaConv xtu =
  let x, t, u =
    match xtu with
    | App(Lam(x, t), u) -> x, t, u
    | _ -> failwith "betaConv: not a redex" in
  let a' = export_raw_type (type_of t) in
  let xtu = App(Lam(x, t), u) in
  let xtu' = export_term xtu in
  Thm([], eq xtu (subst [x, u] t),
    PApp(PApp(PVar("hol.REFL"), a'), xtu'))

let deductAntiSym thmp thmq =
  let Thm(gamma, p, hp) = thmp in
  let Thm(delta, q, hq) = thmq in
  let gamma' = context_remove gamma q in
  let delta' = context_remove delta p in
  let p' = export_term p in
  let q' = export_term q in
  let hp' = abstract_hyp q hp in
  let hq' = abstract_hyp p hq in
  Thm(context_union gamma' delta', eq p q,
    PApp(PApp(PApp(PApp(PVar("hol.PROP_EXT"), p'), q'), hp'), hq'))

let refl t =
  let a' = export_raw_type (type_of t) in
  let t' = export_term t in
  Thm([], eq t t,
    PApp(PApp(PVar("hol.REFL"), a'), t'))

(* The type variables are instantiated first, followed by the term variables. *)
let substThm theta sigma thmp =
  let Thm(gamma, p, hp) = thmp in
  let s t = subst sigma (type_subst theta t) in
  let hp' = export_subst theta sigma gamma p hp in
  Thm(List.map s gamma, s p, hp')

(* Instantiates the free variables that are in fv to
   eliminate them. In the rule eqMp, some free variables can appear in the
   premises but not in the conclusion, so wee need to eliminate them. *)
let elim_free_vars fv t =
  let inst_var t x =
    let _, a = x in
    PApp(abstract_var x t, PApp(PVar("witness"), export_raw_type a)) in
  List.fold_left inst_var t fv

let eqMp thmpq thmr =
  let Thm(gamma, pq, hpq) = thmpq in
  let Thm(delta, r, hp) = thmr in
  let p, q = try get_eq pq with Failure s -> failwith ("eqMp: " ^ s) in
  if not (alpha_equiv p r) then failwith "eqMp: terms do not agree" else
  let p' = export_term p in
  let q' = export_term q in
  let gamma_delta = context_union gamma delta in
  (* Eliminate free variables that appear in p but not in gamma, delta or q. *)
  let vars, _ = all_free_vars gamma_delta q in
  let fv = List.filter (fun x -> not (List.mem x vars)) (free_vars p []) in 
  let p' = elim_free_vars fv p' in
  let hp = elim_free_vars fv hp in
  let hpq = elim_free_vars fv hpq in
  Thm(context_union gamma delta, q,
    PApp(PApp(PApp(PApp(PVar("hol.EQ_MP"), p'), q'), hpq), hp))

let defineConst cname t =
  let ty_vars, a = define_new_constant cname t in
  let a' = List.fold_right gen_tvar ty_vars (export_type a) in
  let args = List.map (fun x -> TyVar(x)) ty_vars in
  let c = Cst(cname, args) in
  (* Short-circuit the definitions. *)
  let def, proof =
    match cname with
    | "imp" ->
        (PVar("hol.imp"), PVar("hol.EQUIV_IMP_HIMP"))
    | "forall" ->
        (PVar("hol.forall"), PApp(PVar("hol.EQUIV_FORALL_HFORALL"), PVar(Name.export_tyvar "A")))
    | "top" ->
        (PVar("hol.top"), PVar("hol.EQUIV_TOP_HTOP"))
    | "and" ->
        (PVar("hol.and"), PVar("hol.EQUIV_AND_HAND"))
    | _ ->
        let a' = export_raw_type a in
        let c' = export_term (c) in
        let t' = List.fold_right abstract_tvar ty_vars (export_term t) in
        (t', PApp(PApp(PVar("hol.REFL"), a'), c')) in
  output_definition (Name.export_cst cname) a' def;
  Thm([], eq c t, proof)

let defineTypeOp opname absname repname type_vars thmpt =
  let Thm(gamma, pt, hpt) = thmpt in
  (* Gamma must be empty. *)
  assert (gamma = []);
  let p, t =
    match pt with
    | App(p, t) -> p, t
    | _ -> failwith ("not an application") in
  let xtype = type_of t in
  let ytype, abs, rep = define_new_typeop opname absname repname type_vars p t in
  let x = Var("r", xtype) in
  let y = Var("a", ytype) in
  let kind = List.fold_right gen_tvar type_vars (PVar("hol.type")) in
  let xtype' = export_raw_type xtype in
  let ytype' = export_raw_type ytype in
  let x' = export_term x in
  let y' = export_term y in
  let p' = export_term p in
  let t' = export_term t in
  let fv = free_vars t [] in
  let t' = elim_free_vars fv t' in
  let hpt = elim_free_vars fv hpt in
  let typedef = List.fold_right abstract_tvar type_vars (PApp(PApp(PApp(PVar("hol.typedef"), xtype'), p'), t')) in
  output_definition (Name.export_tyop opname) kind typedef;
  let type_abs' = List.fold_right gen_tvar type_vars (export_type (ty_arr xtype ytype)) in
  let def_abs' = List.fold_right abstract_tvar type_vars (PApp(PApp(PApp(PVar("hol.abs"), xtype'), p'), t')) in
  output_definition (Name.export_cst absname) type_abs' def_abs';
  let type_rep' = List.fold_right gen_tvar type_vars (export_type (ty_arr ytype xtype)) in
  let def_rep' = List.fold_right abstract_tvar type_vars (PApp(PApp(PApp(PVar("hol.rep"), xtype'), p'), t')) in
  output_definition (Name.export_cst repname) type_rep' def_rep';
  (Thm([], eq (App(p, x)) (eq (App(rep, App(abs, x))) x),
    PApp(PApp(PApp(PApp(PApp(PVar("hol.REP_ABS"), xtype'), p'), t'), hpt), x')),
  Thm([], eq (App(abs, App(rep, y))) y,
    PApp(PApp(PVar("hol.REFL"), ytype'), y')))

let axiom gamma p =
  Printf.eprintf "Assuming axiom..."; prerr_newline ();
  let statement = close_gen gamma p (export_prop p) in
  let name = Name.fresh_axm () in
  output_declaration name statement;
  Thm(gamma, p, open_abstract gamma p (PVar(name)))

(* Abstract over the free hypotheses, the free variables, and the free type
   variables in the theorem to obtain a well-typed "standalone" proof term. *)
let print_thm name theorem =
  let Thm(gamma, p, proof) = theorem in
  let statement = close_gen gamma p (export_prop p) in
  let proof = close_abstract gamma p proof in
  output_definition name statement proof

