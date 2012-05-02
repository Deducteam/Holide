open Format
open Proof

let out_channel = ref stdout

let out_formatter = ref std_formatter

let set_out_channel filename =
  out_channel := open_out filename;
  out_formatter := formatter_of_out_channel !out_channel;
  pp_set_margin !out_formatter 1000000000

let output_comment comment = fprintf !out_formatter "(; %s ;)@." comment

let output_definition name ty body =
  fprintf !out_formatter "%s: %a.@." name fprintf_pterm ty;
  fprintf !out_formatter "[] %s --> %a.@.@." name fprintf_pterm body

let output_declaration name ty =
  fprintf !out_formatter "%s: %a.@.@." name fprintf_pterm ty

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
witness : a : type -> term a.
[] witness --> hol.witness.
imp : term (arr bool (arr bool bool)).
[] imp --> hol.imp.
forall : a : type -> term (arr (arr a bool) bool).
[] forall --> hol.forall.
himp : term (arr bool (arr bool bool)).
[] himp --> hol.himp.
hforall : a : type -> term (arr (arr a bool) bool).
[] hforall --> hol.hforall.

eps : term bool -> Type.
[] eps --> hol.eps.
FUN_EXT : a : type -> b : type -> p : term (arr a b) -> q : term (arr a b) -> (x : term a -> eps (eq b (p x) (q x))) -> eps (eq (arr a b) p q).
[] FUN_EXT --> hol.FUN_EXT.
PROP_EXT : p : term bool -> q : term bool -> (eps q -> eps p) -> (eps p -> eps q) -> eps (eq bool p q).
[] PROP_EXT --> hol.PROP_EXT.
REFL : a : type -> t : term a -> eps (eq a t t).
[] REFL --> hol.REFL.
EQ_MP : p : term bool -> q : term bool -> eps (eq bool p q) -> eps p -> eps q.
[] EQ_MP --> hol.EQ_MP.
APP_THM : a : type -> b : type -> f : term (arr a b) -> g : term (arr a b) -> t : term a -> u : term a -> eps (eq (arr a b) f g) -> eps (eq a t u) -> eps (eq b (f t) (g u)).
[] APP_THM --> hol.APP_THM.
EQUIV_IMP_HIMP : eps (eq (arr bool (arr bool bool)) imp himp).
[] EQUIV_IMP_HIMP --> hol.EQUIV_IMP_HIMP.
EQUIV_FORALL_HFORALL : a : type -> eps (eq (arr (arr a bool) bool) (forall a) (hforall a)).
[] EQUIV_FORALL_HFORALL --> hol.EQUIV_FORALL_HFORALL.
;----------------------------- END HOL SIGNATURE ------------------------------;
@."

