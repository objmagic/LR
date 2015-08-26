all: clean build

OCAMLBUILD = ocamlbuild
OCAMLC = metaocamlc
TARGET = lr_parser.byte
TAGS = annot,bin_annot
PKGS = genlet

build:
	$(OCAMLBUILD) -tag $(TAGS) -pkgs $(PKGS) -ocamlc $(OCAMLC) $(TARGET)

test:
	$(OCAMLBUILD) -tag $(TAGS) -pkgs $(PKGS) -ocamlc $(OCAMLC) $(TESTTARGET)

clean:
	ocamlbuild -ocamlc $(METAOCAMLC) -clean
	rm -rf *.cmi *.cmo *.out *.byte _build

.PHONY: byte clean test
