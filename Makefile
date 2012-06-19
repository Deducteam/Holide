EXECUTABLE = holide
MODULES    = name type term proof output thm machine main
LIBRARIES  = str

# Tools
OCAMLC   = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep

# Options
BFLAGS =
OFLAGS =

$(EXECUTABLE): $(MODULES:%=src/%.cmx)
	$(OCAMLOPT) $(OFLAGS) -o $(EXECUTABLE) $(LIBRARIES:%=%.cmxa) $(MODULES:%=src/%.cmx)

$(EXECUTABLE).byte: $(MODULES:%=src/%.cmo)
	$(OCAMLC) $(BFLAGS) -o $(EXECUTABLE).byte $(LIBRARIES:%=%.cma) $(MODULES:%=src/%.cmo)

%.cmo: %.ml
	$(OCAMLC) $(BFLAGS) -I src -c $*.ml
%.cmi: %.mli
	$(OCAMLC) $(BFLAGS) -I src -c $*.mli
%.cmx: %.ml
	$(OCAMLOPT) $(OFLAGS) -I src -c $*.ml

# Dependencies
.depend:
	ocamldep -I src src/*.ml src/*.mli > .depend

# Statistics
stat: clean
	wc -l src/*.ml

# Clean up
clean:
	rm -f $(EXECUTABLE) $(EXECUTABLE).byte
	rm -f src/*.cm[iox] src/*.o

include .depend
