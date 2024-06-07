MAIN := paper
RULES := dcoi-rules

LATEX_FLAGS := -jobname=$(MAIN) -shell-escape
LATEX := pdflatex $(LATEX_FLAGS)
LATEXRUN := ./latexrun --latex-args "$(LATEX_FLAGS)"
BIBTEX := bibtex
OTT := ott -tex_wrap false -tex_show_meta false -picky_multiple_parses false -merge true

-include overrides.mk

MAKEDEPS  := Makefile
OTTDEPS := ../old.ott Auxiliary.ott
LATEXDEPS := weirich.bib refs.bib
MOREDEPS := ACM-Reference-Format.bst acmart.cls listproc.sty ottalt.sty draft.sty
GENERATED := $(MAIN).pdf $(MAIN)-output.tex $(RULES).tex

all : $(MAIN).pdf

spec.tex: ../old.ott Auxiliary.ott dcoi-rules.tex
	$(OTT) -tex_filter spec.mng spec.tex

spec.pdf: spec.tex
	$(LATEX) spec.tex
	$(LATEX) spec.tex
	$(LATEX) spec.tex

$(MAIN)-output.tex: $(MAKEDEPS) $(OTTDEPS) $(MAIN).tex $(RULES).tex
	$(OTT) -tex_filter $(MAIN).tex $(MAIN)-output.tex $(OTTDEPS)
	perl -i -ne 'print unless m/^%/' $(MAIN)-output.tex

.PHONY: FORCE
$(MAIN).pdf : FORCE $(MAKEDEPS) $(MAIN)-output.tex
	$(LATEXRUN) $(MAIN)-output.tex

$(RULES).tex : $(MAKEDEPS) $(OTTDEPS)
	$(OTT) -o $(RULES).tex $(OTTDEPS)

source.zip : $(MAKEDEPS) $(MAIN)-output.tex $(LATEXDEPS) $(MOREDEPS)
	rm -rf source source.zip
	mkdir source
	cp $(MAKEDEPS) $(MAIN)-output.tex $(LATEXDEPS) $(MOREDEPS) latex.out/$(MAIN).bbl $(RULES).tex source/
	zip -r source source

.PHONY: clean
clean:
	$(LATEXRUN) --clean-all
	rm -if $(GENERATED)
