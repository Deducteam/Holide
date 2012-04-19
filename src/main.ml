let filename = 
  ref None

let set_filename name =
  filename := Some(name)

let options = Arg.align [
  "-d", Arg.Set(Machine.use_dict), " Use opentheory dictionary compression";
  "-m", Arg.Set(Name.mangle_names), " Activate name mangling for variable names";
  "-o", Arg.String(Output.set_out_channel), "<file> Set output filename";
  "-s", Arg.Set(Machine.use_step), " Output intermediary derivation steps"]

let usage =
  Printf.sprintf "Usage: %s <options> <file>" Sys.argv.(0)

let () =
  Arg.parse options set_filename usage;
  match !filename with
  | None ->
      Arg.usage options usage;
      exit 1
  | Some filename ->
      Output.output_preamble ();
      Machine.read_article filename

