VFILES:=$(shell grep "^[^#].*.v" _CoqProject)

core: core.make
	make -f core.make

clean: core.make
	make -f core.make clean
	rm -r _build

core.make: _CoqProject
	coq_makefile -f _CoqProject -o core.make

edsger: parser
	cd Edsger && dune build edsger.bc

edsger.exe: parser
	cd Edsger && dune build edsger.exe

parser: Edsger/config.h Edsger/parser.mly Edsger/make_parser.sh
	cd Edsger && ./make_parser.sh

minicc:
	cd minic && dune build minicc.bc

minicc.exe:
	cd minic && dune build minicc.exe

.PHONY: clean core edsger edsger.exe parser

coqdoc: core
	mkdir -p docs/coqdoc	
	rm -f docs/coqdoc/*.html
	coqdoc -R . DeepSpec $(VFILES) --toc -d docs/coqdoc --toc-depth 2 --html --interpolate --no-lib-name
	cp docs/coqdoc/custom-coqdoc.css docs/coqdoc/coqdoc.css

coqdoc-latex: core
	mkdir -p docs/coqdoc-latex	
	rm -f docs/coqdoc-latex/*.tex
	coqdoc -R . DeepSpec $(VFILES) --latex -d docs/coqdoc-latex --interpolate --no-lib-name --no-glob --short --body-only