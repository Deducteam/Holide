(** Creating and using the database of articles inputs and outputs *)

(** Building the database incrementally *)

(* See if the database exists *)

let file_exists = Sys.file_exists

let rec find_database database =
  if file_exists database
    then open_in database
  else failwith "Database not found"

(* Construct the database *)

let marshal content file =
  try
    let oc = open_out file in
    Marshal.to_channel oc content [];
    close_out oc; true
  with _ -> false

(* Import from database *)

let unmarshal_h database =
  try
    let chan = find_database database in
    let content   = Marshal.from_channel chan in
    close_in chan; content
  with
  | _ -> Hashtbl.create 100

let unmarshal_l database =
  try
    let chan = find_database database in
    let content   = Marshal.from_channel chan in
    close_in chan; content
  with
  | _ -> []
