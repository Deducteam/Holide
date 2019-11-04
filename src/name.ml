(** Name generation and handling. *)

let is_alpha c =
  match c with
  | 'a' .. 'z'
  | 'A' .. 'Z' -> true
  | _ -> false

let is_numerical c =
  match c with
  | '0' .. '9' -> true
  | _ -> false

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
    else Printf.sprintf "_%02X" (Char.code c) in
  let rec escape i () name =
    if i = String.length name
    then Printf.sprintf ""
    else Printf.sprintf "%a%a" escape_char name.[i] (escape (i + 1)) name in
  escape 0 () name

let module_name modname name =
  match !Options.language with
  | Options.No | Options.Twelf ->
     Printf.sprintf "%s" name
  | Options.Dk | Options.Coq ->
     Printf.sprintf "%s.%s" modname name

let ne name = module_name "ne" name

let hol name = module_name "hol" name

let hole name = module_name "hole" name

let id prefix id = Printf.sprintf "%s_%d" (escape prefix) id

