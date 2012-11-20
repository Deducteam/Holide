open Format
open Proof

let new_def_syntax = ref true

let out_channel = ref stdout

let out_formatter = ref std_formatter

let set_out_channel filename =
  out_channel := open_out filename;
  out_formatter := formatter_of_out_channel !out_channel;
  pp_set_margin !out_formatter 1000000000

let output_raw format = fprintf !out_formatter format

let output_comment comment = fprintf !out_formatter "(; %s ;)@." comment

let output_definition name ty body =
  if !new_def_syntax
  then
    fprintf !out_formatter "%s: %a := %a@." name fprintf_pterm ty fprintf_pterm body
  else (
    fprintf !out_formatter "%s: %a.@." name fprintf_pterm ty;
    fprintf !out_formatter "[] %s --> %a.@.@." name fprintf_pterm body)

let output_opaque_definition name ty body =
  if !new_def_syntax
  then
    fprintf !out_formatter "{%s}: %a := %a@." name fprintf_pterm ty fprintf_pterm body
  else (
    fprintf !out_formatter "%s: %a.@." name fprintf_pterm ty;
    fprintf !out_formatter "[] %s --> %a.@.@." name fprintf_pterm body)

let output_declaration name ty =
  fprintf !out_formatter "%s: %a.@.@." name fprintf_pterm ty

let output_preamble () = fprintf !out_formatter "
(;--------------------------- BEGIN HOL SIGNATURE ----------------------------;)
type : Type.
[] type --> hol.type.
bool : type.
[] bool --> hol.bool.
ind : type.
[] ind --> hol.ind.
arr : type -> type -> type.
[] arr --> hol.arr.

term : type -> Type.
[] term --> hol.term.
eq : a : type -> term (arr a (arr a bool)).
[] eq --> hol.eq.
select : a : type -> term (arr (arr a bool) a).
[] select --> hol.select.
witness : a : type -> term a.
[] witness --> hol.witness.

proof : term bool -> Type.
[] proof --> hol.proof.
(;---------------------------- END HOL SIGNATURE -----------------------------;)
@."

