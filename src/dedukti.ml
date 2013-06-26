(** Dedukti terms and pretty-printing functions. *)

(** Grammar of the Dedukti terms. *)
type term =
| Type
| Var of string
| Pie of string * term * term
| Lam of string * term * term
| App of term * term

(** Pretty-print the term using the minimal number of parentheses. *)
let rec print_term out term =
  match term with
  | Pie("", a, b) ->
      Printf.fprintf out "%a -> %a" print_applicative a print_term b
  | Pie(x, a, b) ->
      Printf.fprintf out "%s : %a -> %a" x print_applicative a print_term b
  | Lam(x, a, b) ->
      Printf.fprintf out "%s : %a => %a" x print_applicative a print_term b
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
      Printf.fprintf out "Type"
  | Var(x) ->
      Printf.fprintf out "%s" x
  | _ ->
      Printf.fprintf out "(%a)" print_term term
