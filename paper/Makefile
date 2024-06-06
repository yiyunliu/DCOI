PDFLATEX = pdflatex -shell-escape
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta false -picky_multiple_parses false -merge true -i ../dcoi.ott -i Auxiliary.ott


MAIN = paper

-include overrides.mk

MAKEDEPS  = Makefile
LATEXDEPS = weirich.bib refs.bib
GENERATED = paper.pdf paper.mng dcoi-rules.tex

all : paper-output.pdf

spec.tex: ../dcoi.ott Auxiliary.ott dcoi-rules.tex
	$(OTT) $(OTT_FLAGS) -tex_filter spec.mng spec.tex

spec.pdf: spec.tex
	$(PDFLATEX) spec.tex
	$(PDFLATEX) spec.tex
	$(PDFLATEX) spec.tex

paper-output.tex: ../dcoi.ott Auxiliary.ott paper.tex Makefile dcoi-rules.tex
	$(OTT) $(OTT_FLAGS) -tex_filter paper.tex paper-output.tex
	perl -i -ne 'print unless m/^%/' paper-output.tex

paper-output.pdf : $(MAIN)-output.tex $(MAKEDEPS) $(LATEXDEPS)
	$(PDFLATEX) $(MAIN)-output.tex
	$(BIBTEX) $(MAIN)-output
	$(PDFLATEX) $(MAIN)-output.tex
	$(PDFLATEX) $(MAIN)-output.tex

dcoi-rules.tex : ../dcoi.ott Auxiliary.ott Makefile
	$(OTT) $(OTT_FLAGS) -o dcoi-rules.tex

source.zip : paper-output.tex Makefile weirich.bib refs.bib ACM-Reference-Format.bst acmart.cls
	rm -rf source source.zip
	mkdir source
	cp acmart.cls  listproc.sty  paper-output.bbl  ottalt.sty  students.bib  draft.sty dcoi-rules.tex  paper-output.tex  refs.bib ACM-Reference-Format.bst  weirich.bib source/
	cp Makefile.export source/Makefile
	zip -r source source

.POHNY: clean
clean:
	rm -if *.log *.aux *.out *~ *.bbl *.blg *.fdb_latexmk *.fls *.tex.tmp *.synctex.gz *.pdf dcoi-rules.tex
