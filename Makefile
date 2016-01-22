all: clean build

OCAMLBUILD = ocamlbuild
OCAMLC = ocamlc
TARGET = hmap.byte lr_parser.byte
TAGS = annot,bin_annot

build:
	$(OCAMLBUILD) -tag $(TAGS) -ocamlc $(OCAMLC) $(TARGET)

test:
	$(OCAMLBUILD) -tag $(TAGS) -ocamlc $(OCAMLC) $(TESTTARGET)

clean:
	rm -rf *.cmi *.cmo *.out *.byte _build

.PHONY: byte clean test
