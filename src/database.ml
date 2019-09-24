(** Creating and using the database of articles inputs and outputs *)

(** Building the database incrementally *)

(* See if the database exists *)

let file_exists = Sys.file_exists

let rec find_database () =
  if file_exists "database.holide"
    then open_in "database.holide"
  else failwith "Database not found"

(* Construct the database *)

let marshal defined_typeops defined_csts outputs =
  try
    let file = "database.holide" in
    let oc = open_out file in
    Marshal.to_channel oc defined_typeops [];
    Marshal.to_channel oc defined_csts [];
    Marshal.to_channel oc outputs [];
    close_out oc; true
  with _ -> false

(* Import from database *)

let unmarshal () =
  try
    let chan = find_database () in
    let tdops		= Marshal.from_channel chan in
    let tdcsts		= Marshal.from_channel chan in
    let toutputs	= Marshal.from_channel chan in
    close_in chan; Some (tdops,tdcsts,toutputs)
  with
  | _ -> None
