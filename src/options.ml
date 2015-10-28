(** Output file and printing functions. *)

let output_file = ref ""

let output_channel = ref stdout

(* Output language option *)
type language = No | Dk | Coq | Twelf
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
    | "coq" | "Coq" -> Coq
    | "twelf" | "Twelf" -> Twelf
    | _ -> failwith ("unknown output_language: \"" ^ lang ^ "\"")
  )
