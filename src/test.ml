let a = Type.type_app "pair" [Type.type_var "A"; Type.type_app "list" [Type.type_var "B"]]

let a' = Type.translate_type a

let _ =
  Printf.printf "Testing...\n";
  Printf.printf "%a\n" Dedukti.print_term a'

