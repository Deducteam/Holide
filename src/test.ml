
let _ =
  Printf.printf "Testing...\n"

let a = Type.app "pair" [Type.var "A"; Type.app "list" [Type.var "B"]]

let x = ("x", a)

let y = ("y", a)

let z = ("z", a)

let t1 = Term.lam x (Term.lam x (Term.var x))

let t2 = Term.lam x (Term.lam y (Term.var x))

let t3 = Term.lam y (Term.lam x (Term.var y))

let t4 = Term.lam x (Term.subst [z, (Term.var x)] (Term.lam x (Term.var z)))

let () =
  assert (Term.compare t1 t2 <> 0);
  assert (Term.compare t1 t3 <> 0);
  assert (Term.compare t2 t3 = 0);
  assert (Term.compare t2 t3 = 0);
  Printf.printf "%a\n" Dedukti.print_term (Term.translate_term [] t4)
