MAIN := paper
RULES := dcoi-rules

LATEX := pdflatex -jobname=$(MAIN) -shell-escape
BIBTEX := bibtex
OTT := ott -tex_wrap false -tex_show_meta false -picky_multiple_parses false -merge true

-include overrides.mk

MAKEDEPS  := Makefile
OTTDEPS := ../dcoi.ott Auxiliary.ott
LATEXDEPS := weirich.bib refs.bib
ACMDEPS := ACM-Reference-Format.bst acmart.cls
STYDEPS := listproc.sty ottalt.sty draft.sty
GENERATED := $(MAIN).pdf $(MAIN).bbl $(MAIN)-output.tex $(RULES).tex

all : $(MAIN).pdf

spec.tex: ../dcoi.ott Auxiliary.ott dcoi-rules.tex
	$(OTT) -tex_filter spec.mng spec.tex

spec.pdf: spec.tex
	$(LATEX) spec.tex
	$(LATEX) spec.tex
	$(LATEX) spec.tex

$(MAIN)-output.tex: $(MAKEDEPS) $(OTTDEPS) $(MAIN).tex $(RULES).tex
	$(OTT) -tex_filter $(MAIN).tex $(MAIN)-output.tex $(OTTDEPS)
	perl -i -ne 'print unless m/^%/' $(MAIN)-output.tex

$(MAIN).pdf : $(MAKEDEPS) $(MAIN)-output.tex $(LATEXDEPS) $(ACMDEPS) $(STYDEPS)
	$(LATEX) $(MAIN)-output.tex
	$(BIBTEX) $(MAIN)
	$(LATEX) $(MAIN)-output.tex
	$(LATEX) $(MAIN)-output.tex

$(RULES).tex : $(MAKEDEPS) $(OTTDEPS)
	$(OTT) -o $(RULES).tex $(OTTDEPS)

source.zip : $(MAKEDEPS) $(MAIN)-output.tex $(LATEXDEPS) $(ACMDEPS)
	rm -rf source source.zip
	mkdir source
	cp $(MAKEDEPS) $(MAIN)-output.tex $(LATEXDEPS) $(ACMDEPS) $(MAIN).bbl $(RULES).tex $(STYDEPS) source/
	zip -r source source

.PHONY: clean
clean:
	rm -if *.log *.aux *.out *~ *.bbl *.blg *.cut *.fdb_latexmk *.fls *.tex.tmp *.synctex.gz $(GENERATED)
