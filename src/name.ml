(** Name generation and handling. *)

let is_alpha c =
  (Char.code 'a' <= Char.code c && Char.code c <= Char.code 'z') ||
  (Char.code 'A' <= Char.code c && Char.code c <= Char.code 'Z')

let is_numerical c =
  Char.code '0' <= Char.code c && Char.code c <= Char.code '9'

let is_alpha_numerical c =
  is_alpha c || is_numerical c

(** Escape non-alphanumerical characters using underscores and hexadecimal
    values to be compatible with Dedukti. *)
let escape name =
  (* Use Printf.sprintf for efficiency. *)
  let escape_char () c =
    if is_alpha_numerical c
    then Printf.sprintf "%c" c
    else if c = '_'
    then Printf.sprintf "__"
    else Printf.sprintf "_%2X" (Char.code c) in
  let rec escape i () name =
    if i = String.length name
    then Printf.sprintf ""
    else Printf.sprintf "%a%a" escape_char name.[i] (escape (i + 1)) name in
  escape 0 () name

let hol name = Printf.sprintf "hol.%s" name

