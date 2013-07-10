(** HOL theorems and their translation to Dedukti *)

(* Hypotheses are represented as a set of terms. *)
module TermSet =
struct

  include Set.Make(Term)
  
  let map f gamma =
    fold (fun p gamma -> add (f p) gamma) gamma empty
  
  let of_list gamma =
    List.fold_left (fun gamma p -> add p gamma) empty gamma

end

(** Axioms consist of a set of hypotheses and a conclusion. *)
type axm = TermSet.t * Term.term

(** Theorems consist a set of hypotheses and a conclusion, together with a
    proof that the conclusion follows from the hypotheses. *)
type thm = TermSet.t * Term.term * proof

and proof =
  | Axiom of axm
  | Refl of Term.term
  | AbsThm of Term.var * thm
  | AppThm of thm * thm
  | Assume of Term.term
  | DeductAntiSym of thm * thm
  | EqMp of thm * thm
  | BetaConv of Term.var * Term.term * Term.term
  | Subst of (Type.var * Type.hol_type) list * (Term.var * Term.term) list * thm
  | DefineConst of Term.cst * Term.term

(** Check the the term [p] has a [bool] type. *)
let check_prop p =
  if Term.type_of p <> Type.bool () then failwith "Axiom term must have type bool"

(** Compute the free type variables using [ftv] as an accumulator. *)
let free_type_vars (gamma, p, _) =
  List.fold_left Term.free_type_vars [] (p :: TermSet.elements gamma)

(** Compute the free term variables in [t] using [fv] as an accumulator. *)
let free_vars (gamma, p, _) =
  List.fold_left Term.free_vars [] (p :: TermSet.elements gamma)

(** Translation *)

module ThmSharing = Sharing.Make(
  struct
    type t = thm
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let translate_id id = Name.id "thm" id

let translate_hyp context p =
  let rec index i context =
    match context with
    | [] -> failwith "Unbound hypotheses"
    | q :: context ->
      if Term.alpha_equiv p q then i
      else index (i + 1) context
  in Name.id "hyp" (List.length context - (index 0 context))

(** Translate a HOL proposition as a Dedukti type. *)
let translate_prop term_context p =
  Dedukti.app (Dedukti.var (Name.hol "proof")) (Term.translate_term term_context p)

(** Translate the list of hypotheses [p1; ...; pn]
    into the Dedukti terms [x1 : ||p1||; ...; xn : ||pn||] and add them to
    the context *)
let rec translate_hyps term_context context hyps =
  let context = List.rev_append hyps context in
  let hyps' = List.map (fun p -> (translate_hyp context p, translate_prop term_context p)) hyps in
  (hyps', context)

(** Translate the HOL theorem [thm] as a Dedukti term. *)
let rec translate_thm term_context context ((gamma, p, proof) as thm) =
  try
    let id = ThmSharing.find thm in
    let ftv = free_type_vars thm in
    let fv = free_vars thm in
    let id' = Dedukti.var (translate_id id) in
    let ftv' = List.map (fun x -> Dedukti.var (Type.translate_var x)) ftv in
    let fv' = List.map (fun x -> Term.translate_var_term term_context x) fv in
    let gammas' = List.map (fun p -> Dedukti.var (translate_hyp context p)) (TermSet.elements gamma) in
    Dedukti.apps (Dedukti.apps (Dedukti.apps id' ftv') fv') gammas'
  with Not_found ->
    match proof with

    | Axiom(gamma, p) -> failwith "Axiom"

    | Refl(t) ->
      let a = Term.type_of t in
      let refl' = Dedukti.var (Name.hol "REFL") in
      let a' = Type.translate_type a in
      let t' = Term.translate_term term_context t in
      Dedukti.apps refl' [a'; t']

    | AbsThm((x, a), ((_, tu, _) as thm_tu)) ->
      let t, u = Term.get_eq tu in
      let b = Term.type_of t in
      let abs_thm' = Dedukti.var (Name.hol "ABS_THM") in
      let a' = Type.translate_type a in
      let b' = Type.translate_type b in
      let x' = Term.translate_var ((x, a) :: term_context) (x, a) in
      let t' = Dedukti.lam (x', Term.translate_type a) (Term.translate_term ((x, a) :: term_context) t) in
      let u' = Dedukti.lam (x', Term.translate_type a) (Term.translate_term ((x, a) :: term_context) u) in
      let thm_tu' = Dedukti.lam (x', Term.translate_type a) (translate_thm ((x, a) :: term_context) context thm_tu) in
      Dedukti.apps abs_thm' [a'; b'; t'; u'; thm_tu']

    | AppThm(((_, fg, _) as thm_fg), ((_, tu, _) as thm_tu)) ->
      let f, g = Term.get_eq fg in
      let t, u = Term.get_eq tu in
      let a, b = Type.get_arr (Term.type_of f) in
      let app_thm' = Dedukti.var (Name.hol "APP_THM") in
      let a' = Type.translate_type a in
      let b' = Type.translate_type b in
      let f' = Term.translate_term term_context f in
      let g' = Term.translate_term term_context g in
      let t' = Term.translate_term term_context t in
      let u' = Term.translate_term term_context u in
      let thm_fg' = translate_thm term_context context thm_fg in
      let thm_tu' = translate_thm term_context context thm_tu in
      Dedukti.apps app_thm' [a'; b'; f'; g'; t'; u'; thm_fg'; thm_tu']

    | Assume(p) ->
      Dedukti.var (translate_hyp context p)

    | DeductAntiSym(((_, p, _) as thm_p), ((_, q, _) as thm_q)) ->
      let prop_ext' = Dedukti.var (Name.hol "PROP_EXT") in
      let p' = Term.translate_term term_context p in
      let q' = Term.translate_term term_context q in
      let hp' = translate_hyp (p :: context) p in
      let hq' = translate_hyp (q :: context) q in
      let thm_p' = Dedukti.lam (hq', translate_prop term_context q) (translate_thm term_context (q :: context) thm_p) in
      let thm_q' = Dedukti.lam (hp', translate_prop term_context p) (translate_thm term_context (p :: context) thm_q) in
      Dedukti.apps prop_ext' [p'; q'; thm_p'; thm_q']
    
    | EqMp(((_, pq, _) as thm_pq), ((_, p, _) as thm_p)) ->
      let _, q = Term.get_eq pq in
      let eq_mp' = Dedukti.var (Name.hol "EQ_MP") in
      let p' = Term.translate_term term_context p in
      let q' = Term.translate_term term_context q in
      let thm_p' = translate_thm term_context context thm_p in
      let thm_pq' = translate_thm term_context context thm_pq in
      Dedukti.apps eq_mp' [p'; q'; thm_pq'; thm_p']
    
    | BetaConv((x, a), t, u) ->
      let b = Term.type_of t in
      let beta_conv' = Dedukti.var (Name.hol "BETA_CONV") in
      let a' = Type.translate_type a in
      let b' = Type.translate_type b in
      let x' = Term.translate_var ((x, a) :: term_context) (x, a) in
      let xt' = Dedukti.lam (x', Term.translate_type a) (Term.translate_term ((x, a) :: term_context) t) in
      let u' = Term.translate_term term_context u in
      Dedukti.apps beta_conv' [a'; b'; xt'; u']

    | Subst(theta, sigma, ((gamma, p, _) as thm_p)) ->
      (* First abstract the proof of p *)
      let ftv = free_type_vars thm_p in
      let fv = free_vars thm_p in
      let ftv' = Type.translate_vars ftv in
      let fv', term_context2 = Term.translate_vars [] fv in
      let gamma', context2 = translate_hyps term_context2 [] (TermSet.elements gamma) in
      let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm term_context2 context2 thm_p))) in
      (* Then apply to instantiate *)
      let type_subst a = Type.subst theta a in
      let term_subst t = Term.subst sigma (Term.type_subst theta t) in
      let ftv' = List.map (fun x -> Type.translate_type (type_subst (Type.var x))) ftv in
      let fv' = List.map (fun x -> Term.translate_term term_context (term_subst (Term.var x))) fv in
      let gamma' = List.map (fun p -> Dedukti.var (translate_hyp context p)) (List.map term_subst (TermSet.elements gamma)) in
      Dedukti.apps (Dedukti.apps (Dedukti.apps thm' ftv') fv') gamma'

    | _ -> failwith "Not implemented"

(** Declare the axiom [gamma |- p] **)
let declare_axiom comment (gamma, p) =
  let thm = (gamma, p, Axiom(gamma, p)) in
  if not !Output.just_check && not (ThmSharing.mem thm) then (
      let ftv = List.fold_left Term.free_type_vars [] (p :: (TermSet.elements gamma)) in
      let fv = List.fold_left Term.free_vars [] (p :: (TermSet.elements gamma)) in
      let ftv' = Type.translate_vars ftv in
      let fv', term_context = Term.translate_vars [] fv in
      let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
      let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
      let id = ThmSharing.add (gamma, p, Axiom(gamma, p)) in
      let id' = translate_id id in
      Output.print_comment comment;
      Output.print_declaration id' p');
  thm

(** Define the theorem [id := thm] *)
let define_thm comment ?(untyped=false) ((gamma, p, _) as thm) =
  if not !Output.just_check && not (ThmSharing.mem thm) then (
      let ftv = free_type_vars thm in
      let fv = free_vars thm in
      let ftv' = Type.translate_vars ftv in
      let fv', term_context = Term.translate_vars [] fv in
      let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
      let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
      let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm term_context context thm))) in
      let id = ThmSharing.add thm in
      let id' = translate_id id in
      Output.print_comment comment;
      Output.print_definition ~opaque:true ~untyped:untyped id' p' thm');
  thm

(** Smart constructors *)

let axiom gamma p =
  List.iter check_prop (p :: gamma);
  declare_axiom "axiom" (TermSet.of_list gamma, p)

let refl t =
  (TermSet.empty, Term.eq t t, Refl(t))

let abs_thm x ((gamma, tu, _) as thm_tu) =
  let t, u = Term.get_eq tu in
  (gamma, Term.eq (Term.lam x t) (Term.lam x u), AbsThm(x, thm_tu))

let app_thm ((gamma, fg, _) as thm_fg) ((delta, tu, _) as thm_tu) =
  let f, g = Term.get_eq fg in
  let t, u = Term.get_eq tu in
  (TermSet.union gamma delta, Term.eq (Term.app f t) (Term.app g u), AppThm(thm_fg, thm_tu))

let assume p =
  check_prop p;
  (TermSet.singleton p, p, Assume(p))

let deduct_anti_sym ((gamma, p, _) as thm_p) ((delta, q, _) as thm_q) =
  let gamma_delta = TermSet.union (TermSet.remove q gamma) (TermSet.remove p delta) in
  let pq = Term.eq p q in
  (gamma_delta, pq, DeductAntiSym(thm_p, thm_q))

let eq_mp ((gamma, pq, _) as thm_pq) ((delta, p, _) as thm_p) =
  let p', q = Term.get_eq pq in
  if Term.compare p p' <> 0 then failwith "eq_mp : terms must be alpha-equivalent";
  (TermSet.union gamma delta, q, EqMp(thm_pq, thm_p))

let beta_conv x t u =
  (TermSet.empty, Term.eq (Term.app (Term.lam x t) u) (Term.subst [x, u] t), BetaConv(x, t, u))

let subst theta sigma ((gamma, p, _) as thm_p) =
  let s t = Term.subst sigma (Term.type_subst theta t) in
  (TermSet.map s gamma, s p, Subst(theta, sigma, thm_p))

let define_const c t =
  if Term.free_vars [] t <> [] then failwith "constant definition contains free variables";
  let a = Term.type_of t in
  Term.declare_cst c a;
  declare_axiom "defineConst" (TermSet.empty, Term.eq (Term.cst c a) t)

let define_type_op op abs rep tvars (gamma, pt, _) =
  if not (TermSet.is_empty gamma) then failwith "type definition contains hypotheses";
  match pt with
  | Term.App(p, t) ->
    let a = Term.type_of t in
    let ftv = Term.free_type_vars [] p in
    if List.sort compare ftv <> List.sort compare tvars then failwith "type variables in type definition do not agree";
    Type.declare_op op (List.length tvars);
    let b = Type.app op (List.map Type.var tvars) in
    Term.declare_cst abs (Type.arr a b);
    Term.declare_cst rep (Type.arr b a);
    let abs = Term.cst abs (Type.arr a b) in
    let rep = Term.cst rep (Type.arr b a) in
    let var_a = Term.var ("a", b) in
    let var_r = Term.var ("r", a) in
    (declare_axiom "defineTypeOp" (TermSet.empty, Term.eq (Term.app abs (Term.app rep var_a)) var_a),
     declare_axiom "defineTypeOp" (TermSet.empty, Term.eq (Term.app p var_r) (Term.eq (Term.app rep (Term.app abs var_r)) var_r)))
  | _ -> failwith "ill-formed type definition"

let thm gamma p ((delta, q, _) as thm) =
  if Term.compare p q <> 0 then failwith "theorem conclusion must be alpha-equivalent";
  if not (TermSet.subset delta (TermSet.of_list gamma)) then failwith "theorem hypotheses must be alpha-equivalent";
  define_thm "thm" thm

