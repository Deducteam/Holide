EXECUTABLE = holide
MODULES    = name type term proof output thm machine main
LIBRARIES  = str

OCAMLC   = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep

BFLAGS =
OFLAGS =

$(EXECUTABLE): $(MODULES:%=%.cmx)
	$(OCAMLOPT) $(OFLAGS) -o $(EXECUTABLE) $(LIBRARIES:%=%.cmxa) $(MODULES:%=%.cmx)

$(EXECUTABLE).byte: $(MODULES:%=%.cmo)
	$(OCAMLC) $(BFLAGS) -o $(EXECUTABLE).byte $(LIBRARIES:%=%.cma) $(MODULES:%=%.cmo)

%.cmo: %.ml
	$(OCAMLC) $(BFLAGS) -c $*.ml
%.cmi: %.mli
	$(OCAMLC) $(BFLAGS) -c $*.mli
%.cmx: %.ml
	$(OCAMLOPT) $(OFLAGS) -c $*.ml

# Dependencies
.depend:
	ocamldep *.ml *.mli > .depend

# Statistics
stat: clean
	wc -l *.ml

# Clean up
clean:
	rm -f $(EXECUTABLE) $(EXECUTABLE).byte
	rm -f *.cmi *.cmo *.cmx *.o

include .depend
