let version = "0.2.1"

let show_version () =
  Printf.printf "Holide HOL to Dedukti translator, version %s\n" version;
  exit 0

let options = Arg.align [
    "--output-language", Arg.String(Output.set_language), "<language> Set output language. Valid values are: None, Dedukti. Default: Dedukti";
    "--just-check", Arg.Unit(fun () -> Output.set_language "None"), " Just check, do not translate (Same as --output-language None)";
    "-o", Arg.String(Output.set_output), "<file> Set output filename";
    "--quiet", Arg.Set(Output.quiet), " Suppress all information";
    "--untyped-def", Arg.Set(Output.untyped_def), " Use untyped declarations";
    "--version", Arg.Unit(show_version), " Print version and exit";
  ]

let usage =
  Printf.sprintf "Usage: %s <options> <file>\n" Sys.argv.(0)

let fail () =
  Arg.usage options usage;
  exit 1

let () =
  Arg.parse options Input.set_input usage;
  if !Input.input_file = ""
  then fail ();
  if !Output.output_file = "" && !Output.language <> Output.No
  then Output.set_output (Filename.chop_extension !Input.input_file ^ Output.extension !Output.language);
  Article.process_file ()

