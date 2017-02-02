#############
# Utilities #
#############

SHELL      = bash
OCAMLBUILD = ocamlbuild
DEDUKTI    = dkcheck    # (optional)
COQC       = coqc       # (optional)
TWELF      = ./twelf-check
OPENTHEORY = opentheory # (optional)

#################
# Configuration #
#################

OPTIONS     = -classic-display
LIBS        = str

# Do not include slash at the end because ocamlbuild does not support it
SOURCE_DIR  = src
BUILD_DIR   = build

INSTALL_DIR = /usr/local/bin
LIBINSTALL_DIR = /usr/local/lib

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
THEORY_ELF = $(THEORY:%=twelf/%.elf)
THEORY_ELC = $(THEORY:%=twelf/%.elc)

STDLIB_ART = $(STDLIB:%=opentheory/%.art)
STDLIB_DK  = $(STDLIB:%=dedukti/%.dk)
STDLIB_DKO = $(STDLIB:%=dedukti/%.dko)
STDLIB_V   = $(STDLIB:%=coq/%.v)
STDLIB_VO  = $(STDLIB:%=coq/%.vo)
STDLIB_ELF = $(STDLIB:%=twelf/%.elf)
STDLIB_ELC = $(STDLIB:%=twelf/%.elc)

BUILD = $(OCAMLBUILD) \
  $(OPTIONS) -libs $(LIBS) -I $(SOURCE_DIR) -build-dir $(BUILD_DIR)

################
# Main targets #
################

default: holide $(THEORY_DKO)

holide:
	$(BUILD) main.native
	ln -sf build/src/main.native holide

install: holide $(THEORY_DKO)
	install holide $(INSTALL_DIR)
	install $(THEORY_DKO) $(LIBINSTALL_DIR)

uninstall:
	rm -f $(INSTALL_DIR)/holide
	rm -f $(LIBINSTALL_DIR)/$(THEORY_DKO)

# Only works if you have the opentheory package manager
get-stdlib: $(STDLIB_ART)

translate-stdlib: $(STDLIB_DK) $(STDLIB_V) $(STDLIB_ELF)

compile-theory: $(THEORY_DKO) $(THEORY_VO) $(THEORY_ELC)

compile-stdlib: $(STDLIB_DKO) $(STDLIB_VO) $(STDLIB_ELC)

all: holide get-stdlib translate-stdlib compile-theory compile-stdlib

test: test-all

clean: clean-holide clean-theory-dko clean-theory-elc clean-theory-vo\
	clean-stdlib-dko clean-stdlib-elc clean-stdlib-vo\
	clean-stdlib-dk clean-stdlib-elf clean-stdlib-v

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

clean-stdlib-elf:
	rm -f $(STDLIB_ELF)

clean-theory-dko:
	rm -f $(THEORY_DKO)

clean-theory-vo:
	rm -f $(THEORY_VO)

clean-theory-elc:
	rm -f $(THEORY_ELC)

clean-stdlib-dko:
	rm -f $(STDLIB_DKO)

clean-stdlib-vo:
	rm -f $(STDLIB_VO)

clean-stdlib-elc:
	rm -f $(STDLIB_ELC)

test-all:
	$(MAKE) clean
	time $(MAKE) all

test-translate-stdlib:
	$(MAKE) clean-stdlib-dk
	$(MAKE) clean-stdlib-v
	$(MAKE) clean-stdlib-elf
	$(MAKE) holide
	time $(MAKE) translate-stdlib

test-compile-stdlib:
	$(MAKE) clean-stdlib-dko
	$(MAKE) clean-stdlib-vo
	$(MAKE) clean-stdlib-elc
	$(MAKE) holide translate-stdlib compile-theory
	time $(MAKE) compile-stdlib

# Only works if you have the opentheory package manager
$(STDLIB_ART): opentheory/%.art: opentheory
	$(OPENTHEORY) install $*
	$(OPENTHEORY) info --article -o $@ $*

opentheory:
	mkdir -p opentheory

$(STDLIB_DK): dedukti/%.dk: opentheory/%.art
	./holide $< -o $@

$(STDLIB_V): coq/%.v: opentheory/%.art
	./holide $< --output-language Coq -o $@

$(STDLIB_ELF): twelf/%.elf: opentheory/%.art
	./holide $< --output-language Twelf -o $@

$(THEORY_DKO): dedukti/%.dko: dedukti/%.dk
	cd $(dir $<) && $(DEDUKTI) -e $(notdir $<)

$(THEORY_VO): coq/%.vo: coq/%.v
	cd $(dir $<) && $(COQC) $(notdir $<)

$(THEORY_ELC): twelf/%.elc: twelf/%.elf
	cd $(dir $<) && $(TWELF) $(notdir $<)

$(STDLIB_DKO): dedukti/%.dko: dedukti/%.dk $(THEORY_DKO)
	cd $(dir $<) && $(DEDUKTI) -e $(notdir $<)

$(STDLIB_VO): coq/%.vo: coq/%.v $(THEORY_VO)
	cd $(dir $<) && $(COQC) $(notdir $<)

$(STDLIB_ELC): twelf/%.elc: twelf/%.elf $(THEORY_ELF)
	cd $(dir $<) && $(TWELF) $(notdir $(THEORY_ELF)) $(notdir $<)

.PHONY: \
	holide get-stdlib translate-stdlib compile-theory compile-stdlib \
  clean clean-holide clean-stdlib-dk clean-theory-dko clean-stdlib-dko \
  clean-stdlib-v clean-theory-vo clean-stdlib-vo \
  clean-stdlib-elf clean-theory-elc clean-stdlib-elc \
  test test-all test-translate-stdlib test-compile-stdlib

# Prevent make from deleting intermediary files.
.SECONDARY:

