
(** Get the file extension corresponding to an output language *)
let extension = function
  | Options.Dk -> ".dk"
  | Options.Coq -> ".v"
  | Options.Twelf -> ".elf"
  | Options.No -> assert false

(** Replace - characters with _ for filenames *)

let low_dash s = String.map (fun x -> if x = '-' then '_' else x) s

(** Printf-like function for printing information. *)
let print_verbose fmt =
  if !Options.quiet then Printf.ifprintf stdout fmt else Printf.fprintf stdout fmt

let print_comment comment = match !Options.language with
  | Options.No    -> ()
  | Options.Dk    -> Printf.fprintf !Options.output_channel "\n(; %s ;)\n" comment
  | Options.Coq   -> Printf.fprintf !Options.output_channel "\n(* %s *)\n" comment
  | Options.Twelf -> Printf.fprintf !Options.output_channel "\n%% %s %%\n" comment

(** Print the command (e.g. ["NAME"], ["IMPORT"]) followed by its arguments. *)
let print_command command args b =
  Printf.fprintf !Options.output_channel "\n";
  if !Options.language = Options.Dk then
  Printf.fprintf !Options.output_channel "#";
  Printf.fprintf !Options.output_channel "%s" command;
  List.iter (Printf.fprintf !Options.output_channel " %s") args;
  Printf.fprintf !Options.output_channel ".";
  if b then Printf.fprintf !Options.output_channel "\n"

(** Print the declaration [x : a]. *)
let print_declaration ?(local=false) x a =
  Printf.fprintf !Options.output_channel "\n";
  if !Options.language = Options.Coq then Printf.fprintf !Options.output_channel "Parameter ";
  Printf.fprintf !Options.output_channel "%s : %a.\n" x Dedukti.print_term a

(** Print the definition [x : a := b] or [x := b].
    If [opaque] is set to [true], the definition will be opaque.
    If [untyped] is set to true, the definition will be untyped. *)
let print_definition ?(opaque=false) ?(untyped=false) ?(local=false) x a b =
  let untyped = !Options.untyped_def && untyped in
  let chan = !Options.output_channel in
  match !Options.language with
  | Options.No -> ()
  | Options.Dk ->
     Printf.fprintf chan "\n";
     if local then Printf.fprintf chan "local ";
     if opaque
     then Printf.fprintf chan "thm %s" x
     else Printf.fprintf chan "def %s" x;
     if not untyped
     then Printf.fprintf chan " : %a" Dedukti.print_term a;
     Printf.fprintf chan " :=\n  %a.\n" Dedukti.print_term b;
  | Options.Coq ->
     Printf.fprintf chan "\nDefinition %s" x;
     if not untyped
     then Printf.fprintf chan " : %a" Dedukti.print_term a;
     Printf.fprintf chan " :=\n  %a.\n" Dedukti.print_term b;
  | Options.Twelf ->
     if untyped then
       Printf.fprintf chan "\n%%abbrev\n%s =\n  %a.\n" x Dedukti.print_term b
     else if opaque then
       Printf.fprintf chan "\n%s : %a.\n%%abbrev\n_ : %a =\n  %a.\n"
         x Dedukti.print_term a Dedukti.print_term a Dedukti.print_term b
     else
       Printf.fprintf chan "\n%%abbrev\n%s : %a =\n  %a.\n" x Dedukti.print_term a Dedukti.print_term b

(** Print the definition [x := b]. *)
let print_dependancy x b =
  let chan = !Options.output_channel in
  match !Options.language with
  | Options.No -> ()
  | Options.Dk ->
     Printf.fprintf chan "\n";
     Printf.fprintf chan "def %s" x;
     Printf.fprintf chan " :=\n  %a.\n" Dedukti.print_term b;
  | Options.Coq ->
     Printf.fprintf chan "\nDefinition %s" x;
     Printf.fprintf chan " :=\n  %a.\n" Dedukti.print_term b;
  | Options.Twelf ->
     Printf.fprintf chan "\n%%abbrev\n%s =\n  %a.\n" x Dedukti.print_term b
