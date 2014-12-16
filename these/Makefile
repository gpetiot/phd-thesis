
BIB=biblio.bib
SCHEMES=SANTE_slicing.tex SANTE_slicing_advanced.tex

all: these.pdf

these.dvi: these.tex $(BIB) $(SCHEMES) existant.tex memory_model.tex stady.tex
	latex $^
	bibtex these
	latex $^
	latex $^

these.pdf: these.dvi
	dvipdf these.dvi

clean:
	rm *.toc *.aux *.log *.bbl *.blg *.dvi *.nav *.out *.snm *.lof
