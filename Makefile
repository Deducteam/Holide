SHELL      = bash
OCAMLBUILD = ocamlbuild

OPTIONS    = -classic-display -build-dir build
INCLUDES   = src
LIBS       = str

.PHONY: native byte test clean stat

native:
	$(OCAMLBUILD) $(OPTIONS) -libs $(LIBS) -Is $(INCLUDES) main.native
	ln -sf build/src/main.native holide

byte:
	$(OCAMLBUILD) $(OPTIONS) -libs $(LIBS) -Is $(INCLUDES) main.byte
	ln -sf build/src/main.byte holide

test: native
#	$(OCAMLBUILD) $(OPTIONS) -libs $(LIBS) -Is $(INCLUDES) test.byte --
	holide opentheory/atomic/natural-exp-thm.art -o dedukti/atomic/natural-exp-thm.dk
	cd dedukti && camelide atomic/natural-exp-thm.dk

clean:
	$(OCAMLBUILD) $(OPTIONS) -clean
	rm -rf holide

stat:
	wc -l src/*.ml*

# OpenTheory standard packages (optional)
# (needs the opentheory tool if you don't have the article files)

OPENTHEORY = opentheory
HOLIDE = holide

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

opentheory: $(PACKAGES:%=opentheory/%.art)

opentheory_atomic: $(ATOMIC:%=opentheory/atomic/%.art)

dedukti: $(PACKAGES:%=dedukti/%.dk)

dedukti_atomic: $(ATOMIC:%=dedukti/atomic/%.dk)

dedukti/atomic/%.dk: holide opentheory/atomic/%.art holide
	$(HOLIDE) opentheory/atomic/$*.art -o dedukti/atomic/$*.dk 

dedukti/%.dk: holide opentheory/%.art holide
	$(HOLIDE) opentheory/$*.art -o dedukti/$*.dk 

opentheory/atomic/%.art:
	$(OPENTHEORY) install $*
	$(OPENTHEORY) info --article $* > opentheory/atomic/$*.art

opentheory/%.art:
	$(OPENTHEORY) install $*
	$(OPENTHEORY) info --article $* > opentheory/$*.art

