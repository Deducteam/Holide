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
  | ProveHyp of thm * thm (*version 6*)
  | Sym of thm
  | Trans of thm * thm

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

    | Trans (((_, t1t2, _) as thm1), ((_, t2t3, _) as thm2)) ->
      let t1, t2 = Term.get_eq t1t2 in
      let t2',t3 = Term.get_eq t2t3 in
      let a = Term.type_of t1 in
      let a' = Type.translate_type a in
      if Term.compare t2 t2' <> 0 then failwith "failed at Trans" else
      let trans' = Dedukti.var (Name.hol "TRANS") in
      let t1' = Term.translate_term term_context t1 in
      let t2' = Term.translate_term term_context t2 in
      let t3' = Term.translate_term term_context t3 in
      let thm1' = translate_thm term_context context thm1 in
      let thm2' = translate_thm term_context context thm2 in
      Dedukti.apps trans' [a'; t1'; t2'; t3'; thm1'; thm2']

    | Sym ((_, p, _) as thm_p) ->
      let l, r = Term.get_eq p in
      let l' = Term.translate_term term_context l in
      let r' = Term.translate_term term_context r in
      let a = Term.type_of l in
      let b = Term.type_of r in
      if a <> b then failwith "SYM: failed at Sym because they are not of the same type" else
      (* let a' = Term.translate_type a in _------- dobule bar *)
      let a' = Type.translate_type a in (*this should be a Type.translate_type not Term.translate*)
      let thm_p' = translate_thm term_context context thm_p in
      let sym' = Dedukti.var (Name.hol "SYM") in
      Dedukti.apps sym' [a'; l'; r'; thm_p']

    | ProveHyp (((_, q, _) as thm_q), ((_, p, _) as thm_p)) -> (*t1= psi; t2 = phy*)
      (* let () = Printf.printf "\n\n Let me print a line to see what it is \n\n\n" in  *)
      let ph' = Dedukti.var (Name.hol "PROVE_HYP") in
      let q' = Term.translate_term term_context q in
      let p' = Term.translate_term term_context p in
      (* let hu' = translate_hyp (t1 :: context) t1 in  *)
      let a' = translate_prop term_context p in (*should be p*)
      let x' = translate_hyp (p :: context) p in (* x is $h_{t1}$ here*)
      let thm_p' = (translate_thm term_context context thm_p) in
      let thm_q' = (translate_thm term_context (p :: context) thm_q) in (*add the t1 back to A2*)
      let thm_q'' = Dedukti.lam (x', a') thm_q' in
      Dedukti.apps ph' [p'; q'; thm_p'; thm_q'']

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
  if !Options.language <> Options.No && not (ThmSharing.mem thm) then (
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
  if !Options.language <> Options.No && not (ThmSharing.mem thm) then (
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

(* version 6*)

let sym ((delta, t, _) as thm1) =
  let p, q = Term.get_eq t in
  (delta, Term.eq q p, Sym thm1)

let proveHyp ((delta, psi, _) as thm_q) ((gamma, phy, _) as thm_p) =
  let asl = TermSet.union gamma (TermSet.remove phy delta) in (*and deduce psi*)
  (asl, psi, ProveHyp (thm_q,thm_p))

let trans  ((delta, t12, _) as thm1) ((gamma, t23, _) as thm2) =
  let t1, t2 = Term.get_eq t12 in
  let t2', t3 = Term.get_eq t23 in
  if Term.compare t2 t2' <> 0 then failwith "trans: terms must be alpha-equivalent" ;
  let t = Term.eq t1 t3 in
  ((TermSet.union delta gamma), t, Trans (thm1,thm2))

let beta_conv x t u =
  (TermSet.empty, Term.eq (Term.app (Term.lam x t) u) (Term.subst [x, u] t), BetaConv(x, t, u))

let subst theta sigma ((gamma, p, _) as thm_p) =
  let s t = Term.subst sigma (Term.type_subst theta t) in
  (TermSet.map s gamma, s p, Subst(theta, sigma, thm_p))

let define_const c t =
  if Term.free_vars [] t <> [] then failwith "constant definition contains free variables";
  let a = Term.type_of t in
  if List.mem_assoc c Term.interpretation then
    (TermSet.empty, Term.eq (Term.cst c a) t, Refl (Term.cst c a))
  else
    let () = Term.define_cst c a t in
    (TermSet.empty, Term.eq (Term.cst c a) t, Refl (Term.cst c a))

let define_const_list ((delta, psi, _) as thm1) (nv_list :  (Term.cst * Term.var) list) = (* *)
  if TermSet.cardinal delta <> List.length nv_list then failwith "define_const_list: length not equal"
  else 
         (* the following declare constants *)
    let findfilter v setele = (*find out the t in the set of element (v,t)*)
      let (v',t) = Term.get_eq setele in 
      if Term.compare (Term.Var(v)) v' == 0 then true else false 
    in  
    let f (nv :  (Term.cst * Term.var)) =
      let (n, v) = nv in 
      let sg = TermSet.filter (findfilter v) delta in 
      if TermSet.cardinal sg == 1 then (*this size should be one!!!*)
      let e = TermSet.min_elt sg in  
      let (v', t) = Term.get_eq e in 
      (*do I actually need this????*)
      let () = Printf.printf "defineConstList defined_here \n"  in 
      let x = define_const n t in 
        ()
      in 
    List.map f (nv_list :  (Term.cst * Term.var) list); (*declare constants ??*)

    let g  (nv :  (Term.cst * Term.var)) =
      let (n, v') = nv in 
      let sg = TermSet.filter (findfilter v') delta in 
      (* if TermSet.cardinal sg == 0 then *)
      let e = TermSet.min_elt sg in  
      let (v, t) = Term.get_eq e  in 
      let a = Term.type_of t in 
      let c = Term.cst n a in 
      (v', c) in 

    let sigma = List.map g nv_list in 
    let s = Term.subst sigma in 
    (* subst [] sigma thm1 *)
    (* define an axiom ??? *)
    (* let k = DefineConstList(thm1, nv_list) in  *)
    (* (TermSet.empty, s psi, k) *)
    declare_axiom "defineConstList" (TermSet.empty, s psi)


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
    let va = ("a", b) in 
    let var_a = Term.var va in
    let vr = ("r", a) in 
    let var_r = Term.var vr in

    let lamvaa = Term.lam va var_a in 
    let term_lama = Term.lam va (Term.app abs (Term.app rep var_a)) in 
    let eq1 = Term.eq term_lama lamvaa in 

    let term_pr = (Term.app p var_r) in 
    let term_lamr1 = Term.lam vr term_pr in 
    let term_rep = Term.eq (Term.app rep (Term.app abs var_r)) var_r in
    let term_lamr2 = Term.lam vr term_rep in 
    let eq2 = Term.eq term_lamr2 term_lamr1 in 
    (* (declare_axiom "defineTypeOp" (TermSet.empty, Term.eq (Term.app abs (Term.app rep var_a)) var_a), *)
    (* declare_axiom "defineTypeOp" (TermSet.empty, Term.eq (Term.app p var_r) (Term.eq (Term.app rep (Term.app abs var_r)) var_r))) *)
    (* (λr. rep (abs r) = r) = λr. φ r  *)
    (declare_axiom "defineTypeOp" (TermSet.empty, eq1),
     declare_axiom "defineTypeOp" (TermSet.empty, eq2)) 
  | _ -> failwith "ill-formed type definition"

let rec sprint_thm () (gamma, p, _) =
  (* WARNING: printing of context not yet implemented *)
  Printf.sprintf "|- %a" Term.sprint_term p

let thm gamma p ((delta, q, _) as thm) =
  if Term.compare p q <> 0 then failwith "theorem conclusion must be alpha-equivalent";
  if not (TermSet.subset delta (TermSet.of_list gamma)) then failwith "theorem hypotheses must be alpha-equivalent";
  Output.print_comment (Printf.sprintf "Theorem: %a" sprint_thm thm);
  define_thm "thm" thm

