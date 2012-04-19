open Format
open Type
open Term

(* Proof terms are tems of the λΠ-calculus. *)

type pterm =
  | PVar of string
  | PLam of string * pterm * pterm
  | PPi  of string * pterm * pterm
  | PArr of pterm * pterm
  | PApp of pterm * pterm
  | PHyp of Term.term (* Placeholder for a hypothesis variable *)

(* Translate HOL types into pterms. *)

let rec export_raw_type a =
  match a with
  | TyVar(id) -> PVar(Name.export_tyvar id)
  | TyApp(op, ty_args) ->
      let op = Name.export_tyop op in
      List.fold_left (fun a b -> PApp(a, export_raw_type b)) (PVar(op)) ty_args

let export_type a =
  PApp(PVar("term"), export_raw_type a)

(* Translate HOL terms into pterms. *)

let rec export_term t =
  match t with
  | Var(x) -> PVar(Name.export_var x)
  | Cst((c, ty_args)) ->
      let c = Name.export_cst(c) in
      List.fold_left (fun t a -> PApp(t, export_raw_type a)) (PVar(c)) ty_args
  | Lam(x, u) ->
      let (_, a) = x in
      PLam(Name.export_var x, export_type a, export_term u)
  | App(t1, t2) ->
      PApp(export_term t1, export_term t2)

let export_prop p =
  PApp(PVar("eps"), export_term p)

(* Operations for abstracting over variables. Useful for generalizing theorems. *)

let abstract_tvar t a =
  PLam(Name.export_tyvar a, PVar("type"), t)

let abstract_var t x =
  let (_, a) = x in
  PLam(Name.export_var x, export_type a, t)

let abstract_hyp t p =
  let idh = Name.fresh_hyp () in
  let rec abstract_hyp t =
    match t with
    | PVar(_) -> t
    | PLam(x, a, t1) -> PLam(x, a, abstract_hyp t1)
    | PPi (_) -> t
    | PArr(_) -> t
    | PApp(t1, t2) -> PApp(abstract_hyp t1, abstract_hyp t2)
    | PHyp(q) -> if alpha_equiv p q then PVar(idh) else t in
  PLam(idh, export_prop p, abstract_hyp t)

let gen_tvar t a =
  PPi(Name.export_tyvar a, PVar("type"), t)

let gen_var t x =
  let (_, a) = x in
  PPi(Name.export_var x, export_type a, t)

let gen_hyp t p =
  PArr(export_prop p, t)

let all_free_vars gamma p =
  let fv = List.fold_left (fun fv q -> free_vars q fv) (free_vars p []) gamma in
  let ftv = List.fold_left(fun ftv q -> free_tvars q ftv) (free_tvars p []) gamma in
  fv, ftv

let close_gen gamma p t =
  let fv, ftv = all_free_vars gamma p in
  let t = List.fold_left gen_hyp t gamma in
  let t = List.fold_left gen_var t fv in
  let t = List.fold_left gen_tvar t ftv in
  t

let close_abstract gamma p t =
  let fv, ftv = all_free_vars gamma p in
  let t = List.fold_left abstract_hyp t gamma in
  let t = List.fold_left abstract_var t fv in
  let t = List.fold_left abstract_tvar t ftv in
  t

(* Operations for specializing theorems. *)

let apply_tvar t a =
  PApp(t, PVar(Name.export_tyvar a))

let apply_var t x =
  PApp(t, PVar(Name.export_var x))

let apply_hyp t p =
  PApp(t, PHyp(p))

(* Inverse of the close_abstract operation *)
let open_abstract gamma p t =
  let fv, ftv = all_free_vars gamma p in
  let t = List.fold_left apply_tvar t (List.rev ftv) in
  let t = List.fold_left apply_var t (List.rev fv) in
  let t = List.fold_left apply_hyp t (List.rev gamma) in
  t

(* Translate substitutions *)

(* Applies the function s to the hypothesis variables in t. We need this
   because substitutions also modify hypotheses. Free variables in hypotheses
   cannot be bound by a lambda, so this is safe. *)
let rec subst_in_hyp s t =
  match t with
  | PVar(_) -> t
  | PLam(x, a, u) -> PLam(x, a, subst_in_hyp s u)
  | PPi (_) -> t
  | PArr(_) -> t
  | PApp(t1, t2) -> PApp(subst_in_hyp s t1, subst_in_hyp s t2)
  | PHyp(p) -> PHyp(s p)

let export_subst sigma t =
  let t = subst_in_hyp (subst sigma) t in
  let vars, terms = List.split sigma in
  let apply_term t u = PApp(t, export_term u) in
  List.fold_left apply_term (List.fold_left abstract_var t vars) (List.rev terms)

let export_type_subst theta t =
  let t = subst_in_hyp (type_subst theta) t in
  let tvars, types = List.split theta in
  let apply_type t a = PApp(t, export_raw_type a) in
  List.fold_left apply_type (List.fold_left abstract_tvar t tvars) (List.rev types)

(* Pretty printing *)

let fprintf_pterm ppf t =
  let rec print_pterm ppf t =
    match t with
    | PVar(x) -> fprintf ppf "%s" x
    | PLam(x, a, t1) -> fprintf ppf "@[%s :@<2> %a =>@ %a@]" x print_pterm a print_pterm t1
    | PPi (x, a, b) -> fprintf ppf "@[%s :@<2> %a ->@ %a" x print_pterm a print_pterm b
    | PArr(a, b) -> fprintf ppf "@[%a ->@ %a@]" print_left_arr a print_pterm b
    | PApp(t1, t2) -> fprintf ppf "@[<2>%a@ %a@]" print_left_app t1 print_right_app t2
    | PHyp(p) ->
        fprintf str_formatter "%a" print_pterm (export_term p); (* There cannot be a free hypothesis in (export_term p), so this won't loop. *)
        failwith (sprintf "free hypotheses remaining: %s" (flush_str_formatter ()))
  and print_left_arr ppf t =
    match t with
    | PArr(_) -> fprintf ppf "@[(%a)@]" print_pterm t
    | _ -> fprintf ppf "%a" print_pterm t
  and print_left_app ppf t =
    match t with
    | PLam(_) | PPi(_) -> fprintf ppf "@[(%a)@]" print_pterm t
    | _ -> fprintf ppf "%a" print_pterm t
  and print_right_app ppf t =
    match t with
    | PLam(_) | PApp(_) -> fprintf ppf "@[(%a)@]" print_pterm t
    | _ -> fprintf ppf "%a" print_pterm t in
  print_pterm ppf t

