SHELL      = bash
OCAMLBUILD = ocamlbuild
OPENTHEORY = opentheory

OPTIONS    = -classic-display
BUILD_DIR  = build
INCLUDES   = src
LIBS       = str

# OpenTheory standard library
# (needs the opentheory tool if you don't have the article files)
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

BUILD = $(OCAMLBUILD) \
  $(OPTIONS) -build-dir $(BUILD_DIR) -libs $(LIBS) -Is $(INCLUDES)

holide:
	$(BUILD) main.native
	ln -sf build/src/main.native holide

test: holide twelf/unit.elf
	$(BUILD) test.native --
	cd twelf && ./twelf-check hol.elf unit.elf

stdlib: $(STDLIB:%=twelf/%.elf)

clean:
	$(BUILD) -clean
	rm -rf holide
	rm -f $(STDLIB:%=twelf/%.elf)

stat:
	wc -l src/*.ml*

twelf/%.elf: holide opentheory/%.art
	./holide opentheory/$*.art -o twelf/$*.elf

opentheory/%.art:
	$(OPENTHEORY) install $*
	$(OPENTHEORY) info --article -o opentheory/$*.art $*

.PHONY : holide test stdlib clean stat

# Prevent make from deleting intermediary files.
.SECONDARY:

