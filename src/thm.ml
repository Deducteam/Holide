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

(** Names are registered in a separate list *)

let thm_names = ref []

let rec search_name id = function
	| []			-> failwith "Name not declared\n"
	| (id',name)::q	-> if id=id' then name else search_name id q


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
  | Mp of thm * thm (*ND rules*)
  | Disch of thm * Term.term
  | Conj of thm * thm
  | Conjunct1 of thm
  | Conjunct2 of thm
  | Spec of Term.term * thm
  | Gen of thm * Term.term
  | Disj1 of thm * Term.term
  | Disj2 of thm * Term.term
  | Noti of thm
  | Note of thm
  | Contr of thm * Term.term
  | Disjcases of thm * thm * thm
  | Choose of Term.term * thm * thm
  | Exists of Term.term * Term.term * thm
  | Truth

let dummy_th = (TermSet.empty,Term.dummy_term,Truth)

(** Check the the term [p] has a [bool] type. *)
let check_prop p =
  if Term.type_of p <> Type.bool () then failwith "Axiom term must have type bool"

(** Compute the free type variables using [ftv] as an accumulator. *)
let free_type_vars (gamma, p, _) =
  List.fold_left Term.free_type_vars [] (p :: TermSet.elements gamma)

(** Compute the free term variables in [t] using [fv] as an accumulator. *)
let free_vars (gamma, p, _) =
  List.fold_left Term.free_vars [] (p :: TermSet.elements gamma)

(** Dummy substitution for useless free vars *)

let rec cwd l = function
 | []		-> []
 | hd::q	-> if List.mem hd l then cwd l q else hd::(cwd l q)

(** Adding theorems to the database *)

let outputs = Hashtbl.create 1000

let add_thm (thm:string) = Hashtbl.add outputs thm (Name.escape (Input.get_module_name()))

let add_dep_ax (ax:string) =
	try
		let prov_ax = Hashtbl.find outputs ax in
		let mod_name = Name.escape (Input.get_module_name()) in
		let deps_mod_name = Hashtbl.find_all Type.deps mod_name in
		if not (List.mem prov_ax deps_mod_name) then
			Hashtbl.add Type.deps mod_name prov_ax
		else ()
	with Not_found -> ()


(** Translation *)

module ThmSharing = Sharing.Make(
  struct
    type t = thm * bool
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

(** Translate a HOL proposition as a Dedukti type with a subs. *)
let translate_prop_ws term_context p theta =
  Dedukti.app (Dedukti.var (Name.hol "proof")) (Term.translate_term_ws term_context p theta)

(** Translate the list of hypotheses [p1; ...; pn]
    into the Dedukti terms [x1 : ||p1||; ...; xn : ||pn||] and add them to
    the context *)
let rec translate_hyps term_context context hyps =
  let context = List.rev_append hyps context in
  let hyps' = List.map (fun p -> (translate_hyp context p, translate_prop term_context p)) hyps in
  (hyps', context)

(** Translate the HOL theorem [thm] as a Dedukti term. *)
let rec translate_thm term_context context ((gamma, p, proof) as thm) theta =
  try
	let id = ThmSharing.find (thm,true) in
    let ftv = free_type_vars thm in
    let fv = free_vars thm in
    let id' = Dedukti.var (search_name id (!thm_names)) in
    let ftv' = List.map (fun x -> if List.mem x theta then Dedukti.var "hol.bool" else Dedukti.var (Type.translate_var x)) ftv in
    let fv' = List.map (fun x -> Term.translate_var_term_ws term_context x theta) fv in
    let gammas' = List.map (fun p -> Dedukti.var (translate_hyp context p)) (TermSet.elements gamma) in
    Dedukti.apps (Dedukti.apps (Dedukti.apps id' ftv') fv') gammas'
  with Not_found ->
  try
	let id = ThmSharing.find (thm,false) in
    let ftv = free_type_vars thm in
    let fv = free_vars thm in
    let id' = Dedukti.var (translate_id id) in
    let ftv' = List.map (fun x -> if List.mem x theta then Dedukti.var "hol.bool" else Dedukti.var (Type.translate_var x)) ftv in
    let fv' = List.map (fun x -> Term.translate_var_term_ws term_context x theta) fv in
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
      let thm_tu' = Dedukti.lam (x', Term.translate_type a) (translate_thm ((x, a) :: term_context) context thm_tu theta) in
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
      let thm_fg' = translate_thm term_context context thm_fg theta in
      let thm_tu' = translate_thm term_context context thm_tu theta in
      Dedukti.apps app_thm' [a'; b'; f'; g'; t'; u'; thm_fg'; thm_tu']

    | Assume(p) ->
      Dedukti.var (translate_hyp context p)

    | DeductAntiSym(((_, p, _) as thm_p), ((_, q, _) as thm_q)) ->
      let prop_ext' = Dedukti.var (Name.hol "PROP_EXT") in
      let p' = Term.translate_term term_context p in
      let q' = Term.translate_term term_context q in
      let hp' = translate_hyp (p :: context) p in
      let hq' = translate_hyp (q :: context) q in
      let thm_p' = Dedukti.lam (hq', translate_prop term_context q) (translate_thm term_context (q :: context) thm_p theta) in
      let thm_q' = Dedukti.lam (hp', translate_prop term_context p) (translate_thm term_context (p :: context) thm_q theta) in
      Dedukti.apps prop_ext' [p'; q'; thm_p'; thm_q']

    | EqMp(((_, pq, _) as thm_pq), ((_, p, _) as thm_p)) ->
      let _, q = Term.get_eq pq in
      let eq_mp' = Dedukti.var (Name.hol "EQ_MP") in
      let p' = Term.translate_term term_context p in
      let q' = Term.translate_term term_context q in
      let thm_p' = translate_thm term_context context thm_p theta in
      let thm_pq' = translate_thm term_context context thm_pq theta in
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
      let thm1' = translate_thm term_context context thm1 theta in
      let thm2' = translate_thm term_context context thm2 theta in
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
      let thm_p' = translate_thm term_context context thm_p theta in
      let sym' = Dedukti.var (Name.hol "SYM") in
      Dedukti.apps sym' [a'; l'; r'; thm_p']

    | ProveHyp (((_, q, _) as thm_q), ((_, p, _) as thm_p)) -> (*t1= psi; t2 = phy*)
      (* let () = Printf.printf "\n\n Let me print a line to see what it is \n\n\n" in  *)
      let ph' = Dedukti.var (Name.hol "PROVE_HYP") in
      let q' = Term.translate_term_ws term_context q theta in
      let p' = Term.translate_term_ws term_context p theta in
      (* let hu' = translate_hyp (t1 :: context) t1 in  *)
      let a' = translate_prop_ws term_context p theta in (*should be p*)
      let x' = translate_hyp (p :: context) p in (* x is $h_{t1}$ here*)
      let thm_p' = (translate_thm term_context context thm_p theta) in
      let thm_q' = (translate_thm term_context (p :: context) thm_q theta) in (*add the t1 back to A2*)
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

    | Subst(theta', sigma, ((gamma, p, _) as thm_p)) ->
      (* First abstract the proof of p *)
      let ftv = free_type_vars thm_p in
      let fv = free_vars thm_p in
      let ftv' = Type.translate_vars ftv in
      let fv', term_context2 = Term.translate_vars [] fv in
      let gamma', context2 = translate_hyps term_context2 [] (TermSet.elements gamma) in
      let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm term_context2 context2 thm_p theta))) in
      (* Then apply to instantiate *)
      let type_subst a = Type.subst theta' a in
      let term_subst t = Term.subst sigma (Term.type_subst theta' t) in
      let ftv' = List.map (fun x -> Type.translate_type (type_subst (Type.var x))) ftv in
      let fv' = List.map (fun x -> Term.translate_term term_context (term_subst (Term.var x))) fv in
      let gamma' = List.map (fun p -> Dedukti.var (translate_hyp context p)) (List.map term_subst (TermSet.elements gamma)) in
      Dedukti.apps (Dedukti.apps (Dedukti.apps thm' ftv') fv') gamma'
    
    | Truth -> Dedukti.var (Name.hol "true_i")
	
	| Mp (((_,p1,_) as th1),((_,p2,_) as th2)) ->
      let t1, t2 = Term.get_bin_op "Data.Bool.==>" p1 in
      if Term.compare t1 p2 <> 0 then failwith "failed at MP" else
      let mp' = Dedukti.var (Name.hol "imp_e") in
      let t1' = Term.translate_term_ws term_context t1 theta in
      let t2' = Term.translate_term_ws term_context t2 theta in
      let th1' = translate_thm term_context context th1 theta in
      let th2' = translate_thm term_context context th2 theta in
      Dedukti.apps mp' [t1'; t2'; th1'; th2']
		
	| Disch ((_,p,_) as th,tm) ->
      let disch' = Dedukti.var (Name.hol "imp_i") in
      let p' = Term.translate_term term_context p in
      let tm' = Term.translate_term term_context tm in
      let htm' = translate_hyp (tm :: context) tm in
      let th' = Dedukti.lam (htm', translate_prop term_context tm) (translate_thm term_context (tm :: context) th theta) in
      Dedukti.apps disch' [tm'; p'; th']
		
	| Conj ( ((_,t1,_) as th1) , ((_,t2,_) as th2) ) -> 
      let conj' = Dedukti.var (Name.hol "and_i") in
      let t1' = Term.translate_term term_context t1 in
      let t2' = Term.translate_term term_context t2 in
      let th1' = translate_thm term_context context th1 theta in
      let th2' = translate_thm term_context context th2 theta in
      Dedukti.apps conj' [t1'; t2'; th1'; th2']
		
	| Conjunct1 ((_,t,_) as th) ->
      let t1, t2 = Term.get_bin_op "Data.Bool./\\" t in
      let conj1' = Dedukti.var (Name.hol "and_el") in
      let t1' = Term.translate_term_ws term_context t1 theta in
      let t2' = Term.translate_term_ws term_context t2 theta in
      let th' = translate_thm term_context context th theta in
      Dedukti.apps conj1' [t1'; t2'; th']

	| Conjunct2 ((_,t,_) as th)  ->
      let t1, t2 = Term.get_bin_op "Data.Bool./\\" t in
      let conj2' = Dedukti.var (Name.hol "and_er") in
      let t1' = Term.translate_term_ws term_context t1 theta in
      let t2' = Term.translate_term_ws term_context t2 theta in
      let th' = translate_thm term_context context th theta in
      Dedukti.apps conj2' [t1'; t2'; th']
      
	| Contr (th,tm) ->
	  let contr' = Dedukti.var (Name.hol "false_e") in
      let tm' = Term.translate_term term_context tm in
      let th' = translate_thm term_context context th theta in
      Dedukti.apps contr' [tm' ; th']
    
	| Disj1 (((_,a,_) as th),b) ->
	  let disj1' = Dedukti.var (Name.hol "or_il") in
      let th' = translate_thm term_context context th theta in
      let b' = Term.translate_term term_context b in
      let a' = Term.translate_term term_context a in
	  Dedukti.apps disj1' [a' ; b' ; th']
	  
	| Disj2 (((_,b,_) as th),a) ->
	  let disj2' = Dedukti.var (Name.hol "or_ir") in
      let th' = translate_thm term_context context th theta in
      let b' = Term.translate_term term_context b in
      let a' = Term.translate_term term_context a in
	  Dedukti.apps disj2' [a' ; b' ; th']
	  
	| Disjcases (((_,ab,_) as th),((_,c1,_) as th1) , ((_,c2,_) as th2) ) ->
      if Term.compare c1 c2 <> 0 then failwith "failed at DISJCASES" else
	  let disjcases' = Dedukti.var (Name.hol "or_e") in
	  let a, b = Term.get_bin_op "Data.Bool.\\/" ab in
      let a' = Term.translate_term term_context a in
      let b' = Term.translate_term term_context b in
      let c' = Term.translate_term term_context c1 in
      let th' = translate_thm term_context context th theta in
      let ha' = translate_hyp (a :: context) a in
      let th1' = Dedukti.lam (ha', translate_prop term_context a) (translate_thm term_context (a :: context) th1 theta) in
      let hb' = translate_hyp (b :: context) b in
      let th2' = Dedukti.lam (hb', translate_prop term_context b) (translate_thm term_context (b :: context) th2 theta) in
	  Dedukti.apps disjcases' [a' ; b' ; c' ; th' ; th1' ; th2']
	  
	| Gen (((_,t,_) as th),x) ->
	  begin
	  match x with
	  Term.Var (xn,xty) ->
		  let gen' = Dedukti.var (Name.hol "forall_i") in
		  let xty' = Term.translate_type xty in
		  let xty'' = Type.translate_type xty in
		  let x' = Term.translate_var ((xn, xty) :: term_context) (xn, xty) in
		  let t' = Dedukti.lam (x', xty') (Term.translate_term ((xn, xty) :: term_context) t) in
		  let th' = Dedukti.lam (x', xty') (translate_thm ((xn, xty) :: term_context) context th theta) in
		  Dedukti.apps gen' [xty'' ; t' ; th']
	  | _ -> failwith "Cannot generalize without a variable"
	  end
		

	| Spec (s,((_,t,_) as th)) ->
	  let spec' = Dedukti.var (Name.hol "fa_e") in
	  let p = Term.get_un_op "Data.Bool.!" t in
	  let a,_ = Type.get_arr (Term.type_of p) in
	  let a' = Type.translate_type_ws theta a in
      let s' = Term.translate_term_ws term_context s theta in
      let p' = Term.translate_term_ws term_context p theta in
      let th' = translate_thm term_context context th theta in
	  Dedukti.apps spec' [a' ; s' ; p' ; th']
	  
	| Exists (etm,s,((_,t,_) as th)) ->
	  let exists' = Dedukti.var (Name.hol "exists_i") in
	  let p = Term.get_un_op "Data.Bool.?" etm in
	  let a,_ = Type.get_arr (Term.type_of p) in
	  let a' = Type.translate_type a in
      let s' = Term.translate_term term_context s in
      let p' = Term.translate_term term_context p in
      let th' = translate_thm term_context context th theta in
	  Dedukti.apps exists' [a' ; s' ; p' ; th']


	| Choose (v,((gamma1,t1,_) as th1),((gamma2,t2,_) as th2)) ->
	begin
	  match v with
	  Term.Var vv ->
	  begin
	  let choose' = Dedukti.var (Name.hol "ex_e") in
	  let p = Term.get_un_op "Data.Bool.?" t1 in
	  let (xp,a),bodp = Term.get_lam p in
	  let pat = Term.subst [((xp,a),v)] bodp in
	  let a' = Term.translate_type a in
	  let a'' = Type.translate_type a in
      let t2' = Term.translate_term term_context t2 in
      let p' = Term.translate_term term_context p in
      let th1' = translate_thm term_context context th1 theta in      
      let hp' = translate_hyp (pat :: context) pat in
	  let xp' = Term.translate_var ((xp, a) :: term_context) (xp, a) in
	  let v' = Term.translate_var (vv :: term_context) vv in
      let th2' = Dedukti.lam (v',a') (Dedukti.lam (hp', translate_prop (vv :: term_context) pat) (translate_thm (vv :: term_context) (pat :: context) th2 theta)) in
	  Dedukti.apps choose' [a'' ; t2' ; p' ; th1' ; th2']
	  end
	  | _ -> failwith "CHOOSE"
	end

    | _ -> failwith "Not implemented"

(** Declare the axiom [gamma |- p] **)
let declare_axiom comment (gamma, p) =
  let thm = (gamma, p, Axiom(gamma, p)) in
  if !Options.language <> Options.No && not (ThmSharing.mem (thm,true))
	&& not (ThmSharing.mem (thm,false))then (
      let ftv = List.fold_left Term.free_type_vars [] (p :: (TermSet.elements gamma)) in
      let fv = List.fold_left Term.free_vars [] (p :: (TermSet.elements gamma)) in
      let ftv' = Type.translate_vars ftv in
      let fv', term_context = Term.translate_vars [] fv in
      let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
      let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
      let id = ThmSharing.add ((gamma, p, Axiom(gamma, p)),false) in
      let id' = translate_id id in
      Output.print_comment comment;
      Output.print_declaration id' p');
  thm


(** Declare the axiom [gamma |- p] **)
let declare_namedaxiom comment (gamma, p) (name:string) =
  let thm = (gamma, p, Axiom(gamma, p)) in
  if !Options.language <> Options.No && not (ThmSharing.mem (thm,true))
	&& not (ThmSharing.mem (thm,false))then (
      if not (Hashtbl.mem outputs name) then (
      let ftv = List.fold_left Term.free_type_vars [] (p :: (TermSet.elements gamma)) in
      let fv = List.fold_left Term.free_vars [] (p :: (TermSet.elements gamma)) in
      let ftv' = Type.translate_vars ftv in
      let fv', term_context = Term.translate_vars [] fv in
      let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
      let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
      let id = ThmSharing.add (thm,true) in
      let () = (thm_names := (id,name)::(!thm_names)) in
      Output.print_comment comment;
      Output.print_declaration name p')
      else (
	  let module_name = Hashtbl.find outputs name in
	  let axiom_name = String.concat "." [module_name;name] in
	  let p' = Dedukti.var axiom_name in
      let id = ThmSharing.add (thm,true) in
      let () = (thm_names := (id,name)::(!thm_names)) in
      Output.print_comment comment;
      Output.print_dependancy name p'));
  thm


(** Define the theorem [id := thm] *)
let define_thm comment ?(untyped=false) ((gamma, p, pi) as thm) =
  if !Options.language <> Options.No && not (ThmSharing.mem (thm,true))
	&& not (ThmSharing.mem (thm,false)) then
	  (match pi with
	  | ProveHyp (thm1,thm2) | Mp (thm1,thm2) ->
		  let ftv = free_type_vars thm in
		  let fv = free_vars thm in
		  let theta = cwd (free_type_vars thm) (free_type_vars thm1) in
		  let ftv' = Type.translate_vars ftv in
		  let fv', term_context = Term.translate_vars [] fv in
		  let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
		  let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
		  let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm term_context context thm theta))) in
		  let id = ThmSharing.add (thm,false) in
		  let id' = translate_id id in
		  Output.print_comment comment;
		  Output.print_definition ~opaque:true ~untyped:untyped id' p' thm';
	  | Conjunct1 thm1 | Conjunct2 thm1 | Spec (_,thm1) ->
		  let ftv = free_type_vars thm in
		  let fv = free_vars thm in
		  let theta = cwd (free_type_vars thm) (free_type_vars thm1) in
		  let ftv' = Type.translate_vars ftv in
		  let fv', term_context = Term.translate_vars [] fv in
		  let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
		  let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
		  let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm term_context context thm theta))) in
		  let id = ThmSharing.add (thm,false) in
		  let id' = translate_id id in
		  Output.print_comment comment;
		  Output.print_definition ~opaque:true ~untyped:untyped id' p' thm';
	  | _ ->
		  let ftv = free_type_vars thm in
		  let fv = free_vars thm in
		  let ftv' = Type.translate_vars ftv in
		  let fv', term_context = Term.translate_vars [] fv in
		  let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
		  let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
		  let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm term_context context thm []))) in
		  let id = ThmSharing.add (thm,false) in
		  let id' = translate_id id in
		  Output.print_comment comment;
		  Output.print_definition ~opaque:true ~untyped:untyped id' p' thm');
	thm

let define_namedthm comment ?(untyped=false) ((gamma, p, _) as thm) (name:string) =
  if !Options.language <> Options.No && not (ThmSharing.mem (thm,true)) then (
      let ftv = free_type_vars thm in
      let fv = free_vars thm in
      let ftv' = Type.translate_vars ftv in
      let fv', term_context = Term.translate_vars [] fv in
      let gamma', context = translate_hyps term_context [] (TermSet.elements gamma) in
      let p' = Dedukti.pies ftv' (Dedukti.pies fv' (Dedukti.pies gamma' (translate_prop term_context p))) in
      let thm' = Dedukti.lams ftv' (Dedukti.lams fv' (Dedukti.lams gamma' (translate_thm term_context context thm []))) in
      let id = ThmSharing.add (thm,true) in
      let () = (thm_names := (id,name)::(!thm_names)) in
      Output.print_comment comment;
      Output.print_definition ~opaque:true ~untyped:untyped name p' thm');
  thm

(** Smart constructors *)

let axiom gamma p =
  List.iter check_prop (p :: gamma);
  declare_axiom "axiom" (TermSet.of_list gamma, p)
  
let named_axiom gamma p name =
  List.iter check_prop (p :: gamma);
  declare_namedaxiom "axiom" (TermSet.of_list gamma, p) name

let refl t =
  (TermSet.empty, Term.eq t t, Refl(t))

let abs_thm x ((gamma, tu, _) as thm_tu) =
  let t, u = Term.get_eq tu in
  (gamma, Term.eq (Term.lam x t) (Term.lam x u), AbsThm(x, thm_tu))

let truth_thm =
	(TermSet.empty,Term.Cst("Data.Bool.T",Type.App ("bool",[])),Truth)

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
  if Term.compare p p' <> 0 then
	begin
	Printf.printf "%s\n" (Term.sprint_term () p);
	Printf.printf "%s\n" (Term.sprint_term () q);
	failwith "eq_mp : terms must be alpha-equivalent";
	end;
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
  if List.mem_assoc c !Term.interpretation then
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
      (*do I actually need this????
      let () = Printf.printf "defineConstList defined_here \n"  in*) 
      let x = define_const n t in 
      Term.add_cst n (Term.type_of t)
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


(* ND rules *)

let conj ((gamma,t1,_) as th1) ((delta,t2,_) as th2) =
	(TermSet.union gamma delta,Term.mk_bin_op "Data.Bool./\\" t1 t2,Conj (th1,th2))
		
let conjunct1 ((gamma,t,_) as th) =
    let t1, t2 = Term.get_bin_op "Data.Bool./\\" t in
    (gamma,t1,Conjunct1(th))

let conjunct2 ((gamma,t,_) as th) =
    let t1, t2 = Term.get_bin_op "Data.Bool./\\" t in
    (gamma,t2,Conjunct2(th))

let contr tm ((gamma,t,_) as th) =
	if Term.compare t (Term.Cst("Data.Bool.F",Type.App ("bool",[]))) <> 0
	then failwith "Contradiction proof needs falsity"
	else (gamma,tm,Contr(th,tm))

let note ((gamma,t,_) as th) =
	let t' = Term.get_un_op "Data.Bool.~" t in
	(gamma,Term.mk_bin_op "Data.Bool.==>" t' (Term.Cst("Data.Bool.F",Type.App ("bool",[]))),Note(th))

let noti ((gamma,t,_) as th) =
	let t1,t2 = Term.get_bin_op "Data.Bool.==>" t in
	if Term.compare t2 (Term.Cst("Data.Bool.F",Type.App ("bool",[]))) <> 0
	then failwith "No negation to introduce in Noti"
	else (gamma,Term.mk_op "Data.Bool.~" t1,Noti(th))

let disch ((gamma,t,_) as th) tm =
	(TermSet.remove tm gamma,Term.mk_bin_op "Data.Bool.==>" tm t,Disch(th,tm))

let mp ((gamma,t1,_) as th1) ((delta,t2,_) as th2) =
	let p,q = Term.get_bin_op "Data.Bool.==>" t1 in
	if Term.compare p t2 <> 0
	then failwith "MP : terms must be alpha-equivalent"
	else (TermSet.union gamma delta,q,Mp(th1,th2))

let disjcases ((gamma,t,_) as th) ((delta1,t1,_) as th1) ((delta2,t2,_) as th2) =
    let ta, tb = Term.get_bin_op "Data.Bool.\\/" t in
    if Term.compare t1 t2 <> 0
    then failwith "Disjunction of cases : terms must be alpha-equivalent"
    else
    (TermSet.union (TermSet.union gamma (TermSet.remove tb delta2)) (TermSet.remove ta delta1),
    t1,Disjcases(th,th1,th2))
		
let disj1 ((gamma,a,_) as th) b =
	(gamma,Term.mk_bin_op "Data.Bool.\\/" a b,Disj1(th,b))

let disj2 ((gamma,b,_) as th) a =
	(gamma,Term.mk_bin_op "Data.Bool.\\/" a b,Disj2(th,a))

let gen x ((gamma,t,_) as th) =
	match x with
	Term.Var v ->
		let p = Term.lam v t in
		(gamma,Term.mk_bind "Data.Bool.!" p,Gen(th,x))
	| _ -> failwith "Cannot generalize without a variable"

let spec s ((gamma,t,_) as th) =
	let p = Term.get_un_op "Data.Bool.!" t in
	(gamma,Term.betar p s,Spec(s,th))

let exists etm y ((gamma,t,_) as th) =
	(gamma,etm,Exists(etm,y,th))

let choose v ((delta1,t1,_) as th1) ((delta2,t2,_) as th2) =
	let p = Term.get_un_op "Data.Bool.?" t1 in
	let x,bod = Term.get_lam p in
	(TermSet.union delta1 (TermSet.remove (Term.subst [(x,v)] bod) delta2),
	t2,Choose(v,th1,th2))


let define_type_op op abs rep tvars (gamma, pt, _) =
  if not (TermSet.is_empty gamma) then failwith "type definition contains hypotheses";
  match pt with
  | Term.App(p, t) ->
    let a = Term.type_of t in
    let ftv = Term.free_type_vars [] p in
    if List.sort compare ftv <> List.sort compare tvars then failwith "type variables in type definition do not agree";
    Type.define_op op (List.length tvars);
    let b = Type.app op (List.map Type.var tvars) in
    let () = Term.in_type_op := abs::!Term.in_type_op in
    let () = Term.in_type_op := rep::!Term.in_type_op in
    Term.declare_cst abs (Type.arr a b);
    Term.declare_cst rep (Type.arr b a);
    Term.add_cst abs (Type.arr a b);
    Term.add_cst rep (Type.arr b a);
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

let namedthm gamma p ((delta, q, _) as thm) name =
  if Term.compare p q <> 0 then failwith "theorem conclusion must be alpha-equivalent";
  if not (TermSet.subset delta (TermSet.of_list gamma)) then failwith "theorem hypotheses must be alpha-equivalent";
  Output.print_comment (Printf.sprintf "Theorem %s: %a" name sprint_thm thm);
  define_namedthm "thm" thm name

