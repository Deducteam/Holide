(** Output file and printing functions. *)

let output_file = ref ""

let output_channel = ref stdout

(** Quiet mode option. *)
let quiet = ref false

(** Set the output to [filename]. *)
let set_output filename =
  output_file := filename;
  output_channel := open_out filename

(** Printf-like function for printing information. *)
let print_verbose fmt =
  if !quiet then Printf.ifprintf stdout fmt else Printf.fprintf stdout fmt

let print_comment comment =
  Printf.fprintf !output_channel "\n(; %s ;)\n" comment

(** Print the command (e.g. ["NAME"], ["IMPORT"]) followed by its arguments. *)
let print_command command args =
  Printf.fprintf !output_channel "\n#%s" command;
  List.iter (Printf.fprintf !output_channel " %s") args;
  Printf.fprintf !output_channel "\n"

(** Print the declaration ["x : a"]. *)
let print_declaration x a =
  Printf.fprintf !output_channel "\n%s : %a.\n" x Dedukti.print_term a

(** Print the definition ["x : a := b"].
    If [opaque] is set to [true], the definition will be opaque. *)
let print_definition opaque x a b =
  if opaque
  then Printf.fprintf !output_channel "\n{%s} : %a :=\n  %a.\n" x Dedukti.print_term a Dedukti.print_term b
  else Printf.fprintf !output_channel "\n%s : %a :=\n  %a.\n" x Dedukti.print_term a Dedukti.print_term b

