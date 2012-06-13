EXECUTABLE = holide
MODULES    = name type term proof output thm machine main

OCAMLC    = ocamlc
OCAMLOPT  = ocamlopt
OCAMLDEP  = ocamldep

BFLAGS =
OFLAGS =

$(EXECUTABLE): $(MODULES:%=%.cmx)
	$(OCAMLOPT) $(OFLAGS) -o $(EXECUTABLE) $(MODULES:%=%.cmx)

byte: $(MODULES:%=%.cmo)
	$(OCAMLC) $(BFLAGS) -o $(EXECUTABLE) $(MODULES:%=%.cmo)

opt: $(MODULES:%=%.cmx)
	$(OCAMLOPT) $(OFLAGS) -o $(EXECUTABLE) $(MODULES:%=%.cmx)

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
	wc -l *.ml parser.mly lexer.mll

# Clean up
clean:
	rm -f $(EXECUTABLE)
	rm -f *.cmi *.cmo *.cmx *.o

include .depend
