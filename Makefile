#############
# Utilities #
#############

SHELL      = bash
OCAMLBUILD = ocamlbuild
DEDUKTI    = dkcheck    # (optional)
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

STDLIB_ART = $(STDLIB:%=opentheory/%.art)
STDLIB_DK  = $(STDLIB:%=dedukti/%.dk)
STDLIB_DKO = $(STDLIB:%=dedukti/%.dko)

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

translate-stdlib: $(STDLIB_DK)

compile-theory: $(THEORY_DKO)

compile-stdlib: $(STDLIB_DKO)

all: holide get-stdlib translate-stdlib compile-theory compile-stdlib

test: test-all

clean: clean-holide clean-theory-dko clean-stdlib-dko clean-stdlib-dk

#################
# Dirty details #
#################

clean-holide:
	$(BUILD) -clean
	rm -rf holide

clean-stdlib-dk:
	rm -f $(STDLIB_DK)

clean-theory-dko:
	rm -f $(THEORY_DKO)

clean-stdlib-dko:
	rm -f $(STDLIB_DKO)

test-all:
	$(MAKE) clean
	time $(MAKE) all

test-translate-stdlib:
	$(MAKE) clean-stdlib-dk
	$(MAKE) holide
	time $(MAKE) translate-stdlib

test-compile-stdlib:
	$(MAKE) clean-stdlib-dko
	$(MAKE) holide translate-stdlib compile-theory
	time $(MAKE) compile-stdlib

# Only works if you have the opentheory package manager
$(STDLIB_ART): opentheory/%.art:
	$(OPENTHEORY) install $*
	$(OPENTHEORY) info --article -o $@ $*

$(STDLIB_DK): dedukti/%.dk: opentheory/%.art
	./holide $< -o $@

$(THEORY_DKO): dedukti/%.dko: dedukti/%.dk
	cd $(dir $<) && $(DEDUKTI) -e $(notdir $<)

$(STDLIB_DKO): dedukti/%.dko: dedukti/%.dk $(THEORY_DKO)
	cd $(dir $<) && $(DEDUKTI) -e $(notdir $<)

.PHONY: \
	holide get-stdlib translate-stdlib compile-theory compile-stdlib \
  clean clean-holide clean-stdlib-dk clean-theory-dko clean-stdlib-dko \
  test test-all test-translate-stdlib test-compile-stdlib

# Prevent make from deleting intermediary files.
.SECONDARY:

