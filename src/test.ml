open Type
open Term
open Proof
open Thm
open Output

let _ = output_preamble ()

let x = ("x", TyVar("A"))

let y = ("y", TyVar("A"))

let z = ("z", ty_bool)

(* Rule refl *)

let test_refl = refl (Var(x))

let _ = print_thm "test_refl" test_refl

(* Rule absThm *)

let test_absThm = absThm x test_refl

let _ = print_thm "test_absThm" test_absThm

(* Rules appThm *)

let test_appThm = appThm (refl (Lam(x, Var(x)))) (refl (Var(y)))

let _ = print_thm "test_appThm" test_appThm

(* Rule assume *)

let test_assume = assume (Var(z))

let _ = print_thm "test_assume" test_assume

(* Rule betaConv *)

let test_betaConv = betaConv (App(Lam(x, Var(x)), Var(y)))

let _ = print_thm "test_betaConv" test_betaConv

(* Rule eqMp *)

let test_eqMp = eqMp (refl (Var(z))) (assume (Var(z)))

let _ = print_thm "test_eqMp" test_eqMp

(* Rule instThm *)

let test_inst = instThm ["A", ty_bool] [("y", ty_bool), Var(z)] test_betaConv

let _ = print_thm "test_inst" test_inst

(* Rules deductAntiSym *)

let test_deductAntiSym = deductAntiSym test_assume test_assume

let _ = print_thm "test_deductAntiSym" test_deductAntiSym

(* The following tests deductAntiSym with alpha conversion. The resulting
   context should be empty. *)

let f = Lam(x, Var(x))

let g = Lam(y, Var(y))

let thmf = assume (eq f f)

let thmg = refl g

let test_deduct_alpha = deductAntiSym thmf thmg

let _ = print_thm "test_deduct_alpha" test_deduct_alpha

(* Test defineConst *)

let test_defineConst = defineConst "c" (Lam(x, Var(x)))

let _ = print_thm "test_DefineConst" test_defineConst

