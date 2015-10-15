all: clean build

OCAMLBUILD = ocamlbuild
OCAMLC = metaocamlc
TARGET = hlist.byte lr_parser.byte
TAGS = annot,bin_annot
PKGS = genlet

build:
	$(OCAMLBUILD) -tag $(TAGS) -pkgs $(PKGS) -ocamlc $(OCAMLC) $(TARGET)

test:
	$(OCAMLBUILD) -tag $(TAGS) -pkgs $(PKGS) -ocamlc $(OCAMLC) $(TESTTARGET)

clean:
	rm -rf *.cmi *.cmo *.out *.byte _build

.PHONY: byte clean test
