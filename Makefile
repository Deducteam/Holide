#############
# Utilities #
#############

SHELL      = bash
OCAMLBUILD = ocamlbuild
DEDUKTI    = dkcheck    # (optional)
COQC       = coqc       # (optional)
OPENTHEORY = opentheory # (optional)

#################
# Configuration #
#################

OPTIONS     = -classic-display
LIBS        = str

# Do not include slash at the end because ocamlbuild does not support it
SOURCE_DIR  = src
BUILD_DIR   = build

INSTALL_DIR = /usr/local/bin/

# Components of the HOL theory
THEORY = hol

# Components of the OpenTheory standard library
# (needs the opentheory package manager if you don't have the article files)
STDLIB =\
  unit\
  bool\
  pair\
  function\
  natural\
  set\
  list\
  option\
  real\
  relation\
  sum

#######################
# Derived definitions #
#######################

THEORY_DK  = $(THEORY:%=dedukti/%.dk)
THEORY_DKO = $(THEORY:%=dedukti/%.dko)
THEORY_V   = $(THEORY:%=coq/%.v)
THEORY_VO  = $(THEORY:%=coq/%.vo)

STDLIB_ART = $(STDLIB:%=opentheory/%.art)
STDLIB_DK  = $(STDLIB:%=dedukti/%.dk)
STDLIB_DKO = $(STDLIB:%=dedukti/%.dko)
STDLIB_V   = $(STDLIB:%=coq/%.v)
STDLIB_VO  = $(STDLIB:%=coq/%.vo)

BUILD = $(OCAMLBUILD) \
  $(OPTIONS) -libs $(LIBS) -I $(SOURCE_DIR) -build-dir $(BUILD_DIR)

################
# Main targets #
################

holide:
	$(BUILD) main.native
	ln -sf build/src/main.native holide

install: holide
	install holide $(INSTALL_DIR)

uninstall:
	rm $(INSTALL_DIR)holide

# Only works if you have the opentheory package manager
get-stdlib: $(STDLIB_ART)

translate-stdlib: $(STDLIB_DK) $(STDLIB_V)

compile-theory: $(THEORY_DKO) $(THEORY_VO)

compile-stdlib: $(STDLIB_DKO) $(STDLIB_VO)

all: holide get-stdlib translate-stdlib compile-theory compile-stdlib

test: test-all

clean: clean-holide clean-theory-dko clean-theory-vo\
	clean-stdlib-dko clean-stdlib-vo\
	clean-stdlib-dk clean-stdlib-v

#################
# Dirty details #
#################

clean-holide:
	$(BUILD) -clean
	rm -rf holide

clean-stdlib-dk:
	rm -f $(STDLIB_DK)

clean-stdlib-v:
	rm -f $(STDLIB_V)

clean-theory-dko:
	rm -f $(THEORY_DKO)

clean-theory-vo:
	rm -f $(THEORY_VO)

clean-stdlib-dko:
	rm -f $(STDLIB_DKO)

clean-stdlib-vo:
	rm -f $(STDLIB_VO)

test-all:
	$(MAKE) clean
	time $(MAKE) all

test-translate-stdlib:
	$(MAKE) clean-stdlib-dk
	$(MAKE) clean-stdlib-v
	$(MAKE) holide
	time $(MAKE) translate-stdlib

test-compile-stdlib:
	$(MAKE) clean-stdlib-dko
	$(MAKE) clean-stdlib-vo
	$(MAKE) holide translate-stdlib compile-theory
	time $(MAKE) compile-stdlib

# Only works if you have the opentheory package manager
$(STDLIB_ART): opentheory/%.art:
	$(OPENTHEORY) install $*
	$(OPENTHEORY) info --article -o $@ $*

$(STDLIB_DK): dedukti/%.dk: opentheory/%.art
	./holide $< -o $@

$(STDLIB_V): coq/%.v: opentheory/%.art
	./holide $< --output-language Coq -o $@

$(THEORY_DKO): dedukti/%.dko: dedukti/%.dk
	cd $(dir $<) && $(DEDUKTI) -e $(notdir $<)

$(THEORY_VO): coq/%.vo: coq/%.v
	cd $(dir $<) && $(COQC) $(notdir $<)

$(STDLIB_DKO): dedukti/%.dko: dedukti/%.dk $(THEORY_DKO)
	cd $(dir $<) && $(DEDUKTI) -e $(notdir $<)

$(STDLIB_VO): coq/%.vo: coq/%.v $(THEORY_VO)
	cd $(dir $<) && $(COQC) $(notdir $<)

.PHONY: \
	holide get-stdlib translate-stdlib compile-theory compile-stdlib \
  clean clean-holide clean-stdlib-dk clean-theory-dko clean-stdlib-dko \
  clean-stdlib-v clean-theory-vo clean-stdlib-vo \
  test test-all test-translate-stdlib test-compile-stdlib

# Prevent make from deleting intermediary files.
.SECONDARY:

