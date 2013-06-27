(** HOL Theorems *)

type thm = Term.term list * Term.term * proof

and proof =
| Refl of Term.term
| AbsThm of Term.var * Type.hol_type * thm
| AppThm of thm * thm
| Assume of Term.term
| DeductAntiSym of thm * thm
| EqMp of thm * thm
| BetaConv of Term.var * Type.hol_type * Term.term
| Subst of ((Term.var * Type.hol_type) * Term.term) list * thm
| TypeSubst of (Type.var * Type.hol_type) list * thm
| DefineConst of Term.cst * Term.term

module ThmSharing = Sharing.Make(
  struct
    type t = thm
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let free_type_vars ((hyps, p, _) as thm) =
  List.fold_left Term.free_type_vars [] (p :: hyps)

let free_vars ((hyps, p, _) as thm) =
  List.fold_left Term.free_vars [] (p :: hyps)

