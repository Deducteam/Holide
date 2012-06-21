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

# Exporting opentheory packages (needs opentheory)
PACKAGES = \
  axiom-extensionality axiom-choice axiom-infinity \
  unit-def unit-thm \
  bool-def bool-int bool-ext bool-class \
  pair-def pair-thm \
  function-def function-thm \
  natural-def natural-thm natural-numeral natural-dest \
  natural-order-def natural-order-thm \
  natural-order-min-max-def natural-order-min-max-thm \
  natural-add-def natural-add-thm \
  natural-mult-def natural-mult-thm \
  natural-sub-def natural-sub-thm \
  natural-distance-def natural-distance-thm \
  natural-exp-def natural-exp-thm \
  natural-div-def natural-div-thm \
  natural-factorial-def natural-factorial-thm \
#  natural-funpow-def natural-funpow-thm # Does not exist! :S

OPENTHEORY = opentheory

# Prevent stupid make from deleting intermediary files.
.SECONDARY: 

packages: $(PACKAGES:%=dedukti/atomic/%.dk)

dedukti/atomic/%.dk: $(EXECUTABLE) opentheory/atomic/%.art
	./$(EXECUTABLE) --steps opentheory/atomic/$*.art -o dedukti/atomic/$*.dk 

opentheory/atomic/%.art:
	$(OPENTHEORY) info --article $* > opentheory/atomic/$*.art

include .depend
