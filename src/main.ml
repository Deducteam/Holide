let filename = 
  ref None

let set_filename name =
  filename := Some(name)

let options = Arg.align [
  "--dict", Arg.Set(Machine.use_dict), " Use opentheory dictionary compression";
  "--mangle", Arg.Set(Name.mangle_names), " Activate name mangling for variable names";
  "--old-def", Arg.Clear(Output.new_def_syntax), " Do not use the new definition syntax";
  "-o", Arg.String(Output.set_out_channel), "<file> Set output filename";
  "--no-steps", Arg.Clear(Machine.use_step), " Do not output intermediary derivation steps"]

let usage =
  Printf.sprintf "Usage: %s <options> <file>\n" Sys.argv.(0)

let () =
  Arg.parse options set_filename usage;
  match !filename with
  | None ->
      Arg.usage options usage;
      exit 1
  | Some filename ->
      Output.output_preamble ();
      Machine.read_article filename

