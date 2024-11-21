MAIN := paper
RULES := dcoi-rules
DIFF := diff

LATEX_FLAGS := -jobname=$(MAIN) -shell-escape
LATEX := pdflatex $(LATEX_FLAGS)
LATEXRUN := ./latexrun --latex-args "$(LATEX_FLAGS)"
LATEXDIFF := latexdiff
BIBTEX := bibtex
OTT := ott -tex_wrap false -tex_show_meta false -picky_multiple_parses false -merge true

-include overrides.mk

MAKEDEPS  := Makefile
OTTDEPS := dcoi.ott aux.ott
LATEXDEPS := refs.bib
MOREDEPS := ACM-Reference-Format.bst acmart.cls listproc.sty ottalt.sty draft.sty
GENERATED := $(MAIN).pdf $(MAIN)-output.tex $(RULES).tex

all : $(MAIN).pdf

$(MAIN)-output.tex: $(MAKEDEPS) $(OTTDEPS) $(MAIN).tex $(RULES).tex
	$(OTT) -tex_filter $(MAIN).tex $(MAIN)-output.tex $(OTTDEPS)
	perl -i -ne 'print unless m/^%/' $(MAIN)-output.tex

.PHONY: FORCE
$(MAIN).pdf : FORCE $(MAKEDEPS) $(MAIN)-output.tex
	$(LATEXRUN) $(MAIN)-output.tex

$(DIFF).pdf : $(MAKEDEPS) $(OTTDEPS) $(RULES).tex
	$(LATEXDIFF) old.tex $(MAIN).tex > $(DIFF).tex
	$(OTT) -tex_filter $(DIFF).tex $(DIFF)-output.tex $(OTTDEPS)
	$(LATEXRUN) -o $(DIFF).pdf $(DIFF)-output.tex
	rm $(DIFF)-output.tex

$(RULES).tex : $(MAKEDEPS) $(OTTDEPS)
	$(OTT) -o $(RULES).tex $(OTTDEPS)

source.zip : paper-output.tex Makefile refs.bib ACM-Reference-Format.bst acmart.cls
	rm -rf source source.zip
	mkdir source
	cp acmart.cls  listproc.sty  ottalt.sty   draft.sty dcoi-rules.tex  paper-output.tex  refs.bib ACM-Reference-Format.bst source/
	cp latex.out/paper.bbl source/paper-out.bbl
	cp Makefile.export source/Makefile
	zip -r source source

.PHONY: clean
clean:
	$(LATEXRUN) --clean-all
	rm -if $(GENERATED)
