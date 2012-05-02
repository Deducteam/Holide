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
  | PHLam of Term.term * pterm (* Abstraction for hypothesis variables *)

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
  PHLam(p, t)

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

let export_subst theta sigma gamma p t =
  let s t = subst sigma (type_subst theta t) in
  let fv, ftv = all_free_vars gamma p in
  let t = close_abstract gamma p t in
  let t = List.fold_left (fun t a -> PApp(t, export_raw_type (type_inst theta (TyVar(a))))) t (List.rev ftv) in
  let t = List.fold_left (fun t x -> PApp(t, export_term (s (Var(x))))) t (List.rev fv) in
  let t = List.fold_left apply_hyp t (List.rev (List.map s gamma)) in
  t

(* Pretty printing *)

(* Convert hypothesis variables to lambda abstractions. *)
let convert_hyp t p =
  let idh = Name.fresh_hyp () in
  let rec convert_hyp t =
    match t with
    | PVar(_) -> t
    | PLam(x, a, t1) -> PLam(x, a, convert_hyp t1)
    | PPi (_) -> t
    | PArr(_) -> t
    | PApp(t1, t2) -> PApp(convert_hyp t1, convert_hyp t2)
    | PHyp(q) -> if alpha_equiv p q then PVar(idh) else t
    | PHLam(q, t1) -> if alpha_equiv p q then t else PHLam(q, convert_hyp t1) in
  PLam(idh, export_prop p, convert_hyp t)

let fprintf_pterm ppf t =
  let rec print_pterm ppf t =
    match t with
    | PVar(x) -> fprintf ppf "%s" x
    | PLam(x, a, t1) -> fprintf ppf "%s : %a => %a" x print_pterm a print_pterm t1
    | PPi (x, a, b) -> fprintf ppf "%s : %a -> %a" x print_pterm a print_pterm b
    | PArr(a, b) -> fprintf ppf "%a -> %a" print_left_arr a print_pterm b
    | PApp(t1, t2) -> fprintf ppf "%a %a" print_left_app t1 print_right_app t2
    | PHyp(p) ->
        fprintf str_formatter "%a" print_pterm (export_term p); (* There cannot be a free hypothesis in (export_term p), so this won't loop. *)
        failwith (sprintf "free hypothesis remaining: %s" (flush_str_formatter ()))
    | PHLam(p, t1) -> print_pterm ppf (convert_hyp t1 p)
  and print_left_arr ppf t =
    match t with
    | PArr(_) -> fprintf ppf "(%a)" print_pterm t
    | _ -> fprintf ppf "%a" print_pterm t
  and print_left_app ppf t =
    match t with
    | PLam(_) | PPi(_) | PHLam(_) -> fprintf ppf "(%a)" print_pterm t
    | _ -> fprintf ppf "%a" print_pterm t
  and print_right_app ppf t =
    match t with
    | PLam(_) | PPi(_) | PHLam(_) | PApp(_) -> fprintf ppf "(%a)" print_pterm t
    | _ -> fprintf ppf "%a" print_pterm t in
  print_pterm ppf t

