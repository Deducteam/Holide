(** Output file and printing functions. *)

let output_file = ref ""

let output_channel = ref stdout

(* Output language option *)
type language = No | Dk
let language = ref Dk

(** Quiet mode option. *)
let quiet = ref false

(** Untyped definitions option. *)
let untyped_def = ref false

(** Set the output to [filename]. *)
let set_output filename =
  output_file := filename;
  output_channel := open_out filename

(* Set the output language to [lang] *)
let set_language lang =
  language := (
    match lang with
    | "none" | "None" -> No
    | "dedukti" | "Dedukti" | "dk" | "Dk" -> Dk
    | _ -> failwith ("unknown output_language: \"" ^ lang ^ "\"")
  )

(* Get the file extension corresponding to an output language *)
let extension = function
  | Dk -> ".dk"
  | No -> assert false

(** Printf-like function for printing information. *)
let print_verbose fmt =
  if !quiet then Printf.ifprintf stdout fmt else Printf.fprintf stdout fmt

let print_comment comment =
  Printf.fprintf !output_channel "\n(; %s ;)\n" comment

(** Print the command (e.g. ["NAME"], ["IMPORT"]) followed by its arguments. *)
let print_command command args =
  Printf.fprintf !output_channel "\n#%s" command;
  List.iter (Printf.fprintf !output_channel " %s") args;
  Printf.fprintf !output_channel ".\n"

(** Print the declaration [x : a]. *)
let print_declaration x a =
  Printf.fprintf !output_channel "\n%s : %a.\n" x Dedukti.print_term a

(** Print the definition [x : a := b] or [x := b].
    If [opaque] is set to [true], the definition will be opaque.
    If [untyped] is set to true, the definition will be untyped. *)
let print_definition ?(opaque=false) ?(untyped=false) x a b =
  if !untyped_def && untyped
  then (
    if opaque
    then Printf.fprintf !output_channel "\n{%s} :=\n  %a.\n" x Dedukti.print_term b
    else Printf.fprintf !output_channel "\ndef %s :=\n  %a.\n" x Dedukti.print_term b)
  else (
    if opaque
    then Printf.fprintf !output_channel "\n{%s} : %a :=\n  %a.\n" x Dedukti.print_term a Dedukti.print_term b
    else Printf.fprintf !output_channel "\ndef %s : %a :=\n  %a.\n" x Dedukti.print_term a Dedukti.print_term b)
    
