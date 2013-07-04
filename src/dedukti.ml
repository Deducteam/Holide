(** Dedukti terms and pretty-printing functions *)

(** Grammar of the Dedukti terms *)

type var = string

type term =
  | Type
  | Var of var
  | Pie of var * term * term
  | Lam of var * term * term
  | App of term * term

let var x = Var(x)

let arr a b = Pie("", a, b)

let pie (x, a) b = Pie(x, a, b)

let lam (x, a) b = Lam(x, a, b)

let app a b = App(a, b)

let arrs args b = List.fold_right arr args b

let pies args b = List.fold_right pie args b

let lams args b = List.fold_right lam args b

let apps a args = List.fold_left app a args

(** Pretty-print the term using the minimal number of parentheses. *)
let rec print_term out term =
  match term with
  | Pie("", a, b) ->
    Printf.fprintf out "%a -> %a" print_applicative a print_term b
  | Pie(x, a, b) ->
    Printf.fprintf out "{%s : %a} %a" x print_applicative a print_term b
  | Lam(x, a, b) ->
    Printf.fprintf out "[%s : %a] %a" x print_applicative a print_term b
  | _ ->
    Printf.fprintf out "%a" print_applicative term

and print_applicative out term =
  match term with
  | App(a, b) ->
    Printf.fprintf out "%a %a" print_applicative a print_atomic b
  | _ ->
    Printf.fprintf out "%a" print_atomic term

and print_atomic out term =
  match term with
  | Type ->
    Printf.fprintf out "type"
  | Var(x) ->
    Printf.fprintf out "%s" x
  | _ ->
    Printf.fprintf out "(%a)" print_term term

