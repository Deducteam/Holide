(** HOL Theorems *)

module TermSet =
struct

  include Set.Make(Term)
  
  let map f gamma =
    fold (fun p gamma -> add (f p) gamma) gamma empty
  
  let of_list gamma =
    List.fold_left (fun gamma p -> add p gamma) empty gamma

end

type axm = TermSet.t * Term.term

type thm = TermSet.t * Term.term * proof

and proof =
  | Axiom of axm
  | Refl of Term.term
  | AbsThm of Term.var * thm
  | AppThm of thm * thm
  | Assume of Term.term
  | DeductAntiSym of thm * thm
  | EqMp of thm * thm
  | BetaConv of Term.var * Term.term
  | TypeSubst of (Type.var * Type.hol_type) list * thm
  | TermSubst of (Term.var * Term.term) list * thm
  | DefineConst of Term.cst * Term.term

module ThmSharing = Sharing.Make(
  struct
    type t = thm
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let check_prop p =
  if Term.type_of p <> Type.bool () then failwith "Axiom term must have type bool"

let free_type_vars (gamma, p, _) =
  List.fold_left Term.free_type_vars [] (p :: TermSet.elements gamma)

let free_vars (gamma, p, _) =
  List.fold_left Term.free_vars [] (p :: TermSet.elements gamma)

(** Translation *)

let translate_id id = Name.id "thm" id

let translate_hyp p =
  let hash = Hashtbl.hash_param 1000000 1000000 p in
  Name.id "hyp" hash

(** Translate a HOL proposition as a Dedukti type. *)
let translate_prop p =
  Dedukti.app (Dedukti.var (Name.hol "proof")) (Term.translate_term p)

(** Translate the HOL theorem [thm] as a Dedukti term. *)
let rec translate_thm ((gamma, p, proof) as thm) =
  try
    let id = ThmSharing.find thm in
    let ftv = free_type_vars thm in
    let fv = free_vars thm in
    let id' = Dedukti.var (translate_id id) in
    let ftv' = List.map Dedukti.var (List.map Type.translate_var ftv) in
    let fv' = List.map Dedukti.var (List.map Term.translate_var fv) in
    let gammas' = List.map Dedukti.var (List.map translate_hyp (TermSet.elements gamma)) in
    Dedukti.apps (Dedukti.apps (Dedukti.apps id' ftv') fv') gammas'
  with Not_found ->
    match proof with

    | Axiom(gamma, p) -> failwith "Axiom"

    | Refl(t) ->
      let a = Term.type_of t in
      let refl' = Dedukti.var (Name.hol "REFL") in
      let a' = Type.translate_type a in
      let t' = Term.translate_term t in
      Dedukti.apps refl' [a'; t']

    | AbsThm((x, a), ((_, tu, _) as thm_tu)) ->
      let t, u = Term.get_eq tu in
      let b = Term.type_of t in
      let abs_thm' = Dedukti.var (Name.hol "ABS_THM") in
      let a' = Type.translate_type a in
      let b' = Type.translate_type b in
      let x' = Term.translate_var (x, a) in
      let t' = Term.translate_term (Term.lam (x, a) t) in
      let u' = Term.translate_term (Term.lam (x, a) u) in
      let thm_tu' = Dedukti.lam (x', Term.translate_type a) (translate_thm thm_tu) in
      Dedukti.apps abs_thm' [a'; b'; t'; u'; thm_tu']

    | AppThm(((_, fg, _) as thm_fg), ((_, tu, _) as thm_tu)) ->
      let f, g = Term.get_eq fg in
      let t, u = Term.get_eq tu in
      let a, b = Type.get_arr (Term.type_of f) in
      let app_thm' = Dedukti.var (Name.hol "APP_THM") in
      let a' = Type.translate_type a in
      let b' = Type.translate_type b in
      let f' = Term.translate_term f in
      let g' = Term.translate_term g in
      let t' = Term.translate_term t in
      let u' = Term.translate_term u in
      let thm_fg' = translate_thm thm_fg in
      let thm_tu' = translate_thm thm_tu in
      Dedukti.apps app_thm' [a'; b'; f'; g'; t'; u'; thm_fg'; thm_tu']

    | Assume(p) ->
      Dedukti.var (translate_hyp p)

    | DeductAntiSym(((_, p, _) as thm_p), ((_, q, _) as thm_q)) ->
      let prop_ext' = Dedukti.var (Name.hol "PROP_EXT") in
      let p' = Term.translate_term p in
      let q' = Term.translate_term q in
      let thm_p' = Dedukti.lam (translate_hyp q, translate_prop q) (translate_thm thm_p) in
      let thm_q' = Dedukti.lam (translate_hyp p, translate_prop p) (translate_thm thm_q) in
      Dedukti.apps prop_ext' [p'; q'; thm_p'; thm_q']

    | _ -> failwith "Not implemented"

(** Translate the set of hypotheses {p1; ...; pn}
    into the dedukti context [x1 : ||p1||; ...; xn : ||pn||] *)
let translate_hyps_context hyps =
  List.map (fun p -> (translate_hyp p, translate_prop p)) (TermSet.elements hyps)

(** Declare the axiom [gamma |- p] **)
let declare_axiom (gamma, p) =
  let thm = (gamma, p, Axiom(gamma, p)) in
  let _ = if not (ThmSharing.mem thm) then (
      let ftv = List.fold_left Term.free_type_vars [] (p :: (TermSet.elements gamma)) in
      let fv = List.fold_left Term.free_vars [] (p :: (TermSet.elements gamma)) in
      let ftv' = Type.translate_vars_context ftv in
      let fv' = Term.translate_vars_context fv in
      let gamma' = translate_hyps_context gamma in
      let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop p))) in
      let id = ThmSharing.add (gamma, p, Axiom(gamma, p)) in
      let id' = translate_id id in
      Output.print_declaration id' p');
  in thm

(** Define the theorem [id := thm] *)
let define_thm comment ((gamma, p, _) as thm) =
  let _ = if not (ThmSharing.mem thm) then (
      let ftv = free_type_vars thm in
      let fv = free_vars thm in
      let ftv' = Type.translate_vars_context ftv in
      let fv' = Term.translate_vars_context fv in
      let gamma' = translate_hyps_context gamma in
      let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop p))) in
      let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm thm))) in
      let id = ThmSharing.add thm in
      let id' = translate_id id in
      Output.print_comment comment;
      Output.print_definition true id' p' thm')
  in thm

(** Smart constructors *)

let axiom gamma p =
  List.iter check_prop (p :: gamma);
  declare_axiom (TermSet.of_list gamma, p)

let refl t =
  define_thm "refl" (TermSet.empty, Term.eq t t, Refl(t))

let abs_thm x ((gamma, tu, _) as thm_tu) =
  let t, u = Term.get_eq tu in
  define_thm "absThm" (gamma, Term.eq (Term.lam x t) (Term.lam x u), AbsThm(x, thm_tu))

let app_thm ((gamma, fg, _) as thm_fg) ((delta, tu, _) as thm_tu) =
  let f, g = Term.get_eq fg in
  let t, u = Term.get_eq tu in
  define_thm  "appThm" (TermSet.union gamma delta, Term.eq (Term.app f t) (Term.app g u), AppThm(thm_fg, thm_tu))

(* TODO *)

let assume p =
  check_prop p;
  (TermSet.singleton p, p, Assume(p))

let deduct_anti_sym ((gamma, p, _) as thm_p) ((delta, q, _) as thm_q) =
  let gamma_delta = TermSet.union (TermSet.remove q gamma) (TermSet.remove p delta) in
  let pq = Term.eq p q in
  define_thm "deductAntiSym" (gamma_delta, pq, DeductAntiSym(thm_p, thm_q))

let eq_mp (gamma, p, _) (delta, pq, _) =
  let p', q = Term.get_eq pq in
  if Term.compare p p' <> 0 then failwith "eq_mp : terms must be alpha-equivalent";
  declare_axiom (TermSet.union gamma delta, q)

let beta_conv x t u =
  declare_axiom (TermSet.empty, Term.eq (Term.app (Term.lam x t) u) (Term.subst [x, u] t))

let type_subst theta (gamma, p, _) =
  declare_axiom (TermSet.map (Term.type_subst theta) gamma, Term.type_subst theta p)

let term_subst sigma (gamma, p, _) =
  declare_axiom (TermSet.map (Term.subst sigma) gamma, Term.subst sigma p)

let define_const c t =
  if Term.free_vars [] t <> [] then failwith "constant definition contains free variables";
  let a = Term.type_of t in
  Term.declare_cst c a;
  declare_axiom (TermSet.empty, Term.eq (Term.cst c a) t)

let define_type_op op abs rep _ =
  failwith "Not implemented"

let thm gamma p ((delta, q, _) as thm) =
  if Term.compare p q <> 0 then failwith "theorem conclusion must be alpha-equivalent";
  if not (TermSet.subset delta (TermSet.of_list gamma)) then failwith "theorem hypotheses must be alpha-equivalent";
  define_thm "thm" thm

