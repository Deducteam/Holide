OBJS=name.cmo type.cmo term.cmo proof.cmo output.cmo thm.cmo machine.cmo main.cmo

holide: $(OBJS)
	ocamlc -o holide $(OBJS)

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi

.ml.cmo:
	ocamlc -c $<

.mli.cmi:
	ocamlc -c $<

# Clean up
clean:
	rm -f holide
	rm -f *.cmi *.cmo

# Dependencies
depend:
	ocamldep *.mli *.ml > .depend

include .depend
