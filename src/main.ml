let version = "0.2.1"

let show_version () =
  Printf.printf "Holide HOL to Dedukti translator, version %s\n" version;
  exit 0

let options = Arg.align [
    "--output-language", Arg.String(Options.set_language), "<language> Set output language. Valid values are: None, Dedukti, Coq. Default: Dedukti";
    "--just-check", Arg.Unit(fun () -> Options.set_language "None"), " Just check, do not translate (Same as --output-language None)";
    "-o", Arg.String(Options.set_output), "<file> Set output filename";
    "--quiet", Arg.Set(Options.quiet), " Suppress all information";
    "--untyped-def", Arg.Set(Options.untyped_def), " Use untyped declarations";
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
  if !Options.output_file = "" && !Options.language <> Options.No
  then Options.set_output (Filename.chop_extension !Input.input_file ^ Output.extension !Options.language);
  Article.process_file ()

