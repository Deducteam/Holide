let version = "0.2.2"

let show_version () =
  Printf.printf "Holide HOL to Dedukti translator, version %s\n" version;
  exit 0

let options = Arg.align [
    "--output-language", Arg.String(Options.set_language), "<language> Set output language. Valid values are: None, Dedukti, Coq, and Twelf. Default: Dedukti";
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

let process_names file =
	Input.set_input file;
	if !Input.input_file = ""
	then fail ();
	Printf.printf "+------------------------------------------------+\n Adding %s\ to database\n+------------------------------------------------+\n" file;
	if (*!Options.output_file = "" &&*) !Options.language <> Options.No
	then Options.set_output (Name.escape (Input.get_module_name()) ^ Output.extension !Options.language);
	Article.process_names_file ()


let process file =
	Input.set_input file;
	if !Input.input_file = ""
	then fail ();
	Printf.printf "+------------------------------------------------+\n Processing %s\n+------------------------------------------------+\n" file;
	if (*!Options.output_file = "" &&*) !Options.language <> Options.No
	then Options.set_output (Name.escape (Input.get_module_name()) ^ Output.extension !Options.language);
	Article.process_file ()

let remove_file file =
	Input.set_input file;
	let to_remove = (Name.escape (Input.get_module_name())) ^ (Output.extension !Options.language) in
	Sys.remove to_remove

let () =
  Arg.parse options process_names usage;
  let () = Term.declared := [] in
  let () = Term.in_type_op := [] in
  let () = List.iter remove_file (!Article.articles) in
  let modules = List.map (fun x -> Name.escape (Output.low_dash (Filename.chop_extension (Filename.basename x)))) !Article.articles  in
  let () = (Sort.fill_dep modules) in
  let () = List.iter process (!Article.articles) in
  let () = Printf.printf "\n\nTopological order (%n):\n" (Sort.number_dep()) in
  let () = Sort.ordereddep (fun file -> Printf.printf " %s.dk " file) Sort.dep in
  Printf.printf "\n\n"
