open Format
open Proof

let out_channel = ref stdout

let out_formatter = ref std_formatter

let set_out_channel filename =
  out_channel := open_out filename;
  out_formatter := formatter_of_out_channel !out_channel;
  pp_set_margin !out_formatter 1000000000

let output_comment comment = fprintf !out_formatter "(; %s ;)@." comment

let output_preamble () = fprintf !out_formatter "
;---------------------------- BEGIN HOL SIGNATURE -----------------------------;
type : Type.
[] type --> hol.type.
bool : type.
[] bool --> hol.bool.
arr  : type -> type -> type.
[] arr --> hol.arr.

term : type -> Type.
[] term --> hol.term.
eq : a : type -> term (arr a (arr a bool)).
[] eq --> hol.eq.
select : a : type -> term (arr (arr a bool) a).
[] select --> hol.select.

eps : term bool -> Type.
[] eps --> hol.eps.
FUN_EXT : a : type -> b : type -> p : term (arr a b) -> q : term (arr a b) -> (x : term a -> eps (eq b (p x) (q x))) -> eps (eq (arr a b) p q).
[] FUN_EXT --> hol.FUN_EXT.
PROP_EXT : p : term bool -> q : term bool -> (eps q -> eps p) -> (eps p -> eps q) -> eps (eq bool p q).
[] PROP_EXT --> hol.PROP_EXT.
;----------------------------- END HOL SIGNATURE ------------------------------;
@."

let output_definition name ty body =
  fprintf !out_formatter "@[<2>%s:@ %a.@]@." name fprintf_pterm ty;
  fprintf !out_formatter "@[<2>[] %s -->@ %a.@]@.@." name fprintf_pterm body

let output_declaration name ty =
  fprintf !out_formatter "@[<2>%s:@ %a.@]@." name fprintf_pterm ty
