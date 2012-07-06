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
.depend: $(MODULES:%=src/%.ml)
	ocamldep -I src src/*.ml src/*.mli > .depend

# Statistics
stat: clean
	wc -l src/*.ml

# Clean up
clean:
	rm -f $(EXECUTABLE) $(EXECUTABLE).byte
	rm -f src/*.cm[iox] src/*.o

# OpenTheory standard packages (optional)
# (needs the opentheory tool if you don't have the article files)
OPENTHEORY = opentheory

PACKAGES = \
  unit \
  bool \
  pair \
  function \
  natural \
  set \
  list \
  option \
  real \
  relation \
  sum
  
ATOMIC = \
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
  set-def set-thm \
  set-finite-def set-finite-thm \
  set-fold-def set-fold-thm \
  set-size-def set-size-thm \
  list-def list-thm \
  list-dest-def list-dest-thm \
  list-length-def list-length-thm \
  list-set-def list-set-thm \
  list-append-def list-append-thm \
  list-map-def list-map-thm \
  list-filter-def list-filter-thm \
  list-reverse-def list-reverse-thm \
  list-fold-def list-fold-thm \
  list-last-def list-last-thm \
  list-nth-def list-nth-thm \
  list-interval-def list-interval-thm \
  list-nub-def list-nub-thm \
  list-replicate-def list-replicate-thm \
  list-take-drop-def list-take-drop-thm \
  list-zip-def list-zip-thm \
  option-def option-thm \
  option-dest-def option-dest-thm \
  real-def real-thm \
  relation-def relation-thm \
  relation-well-founded-def relation-well-founded-thm \
  relation-natural-def relation-natural-thm \
  sum-def \
#  natural-funpow-def natural-funpow-thm Does not exist! :S

# Prevent stupid make from deleting intermediary files.
.SECONDARY: 

base: dedukti/base.dk

packages: $(PACKAGES:%=dedukti/%.dk)

atomic: $(ATOMIC:%=dedukti/atomic/%.dk)

dedukti/%.dk: $(EXECUTABLE) opentheory/%.art
	./$(EXECUTABLE) --steps opentheory/$*.art -o dedukti/$*.dk 

dedukti/atomic/%.dk: $(EXECUTABLE) opentheory/atomic/%.art
	./$(EXECUTABLE) --steps opentheory/atomic/$*.art -o dedukti/atomic/$*.dk 

opentheory/%.art:
	$(OPENTHEORY) info --article $* > opentheory/$*.art

opentheory/atomic/%.art:
	$(OPENTHEORY) info --article $* > opentheory/atomic/$*.art

include .depend