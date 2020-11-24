all: alethe doc

doc: doc/manual.pdf

doc/manual.pdf: doc/manual.tex
	cd doc && latexmk -pdflatex -silent manual

alethe: src/*.hs
	stack build
	cp "$$(stack path --local-install-root)/bin/alethe" ./alethe

.PHONY: all doc