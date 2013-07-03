(** Input file and reading functions. *)

let input_file = ref ""

let input_channel = ref stdin

(** Set the input to [filename]. *)
let set_input filename =
  input_file := filename;
  input_channel := open_in filename

(** Get the name of the module from the name of the file. *)
let get_module_name () =
  Filename.chop_extension (Filename.basename !input_file)

(** Read one line from the input. *)
let read_line () = input_line !input_channel

