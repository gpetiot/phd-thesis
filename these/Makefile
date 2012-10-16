
BIB=biblio.bib
SCHEMES=

all: these.pdf

these.dvi: these.tex $(BIB) $(SCHEMES) existant.tex
	latex $^
	bibtex these
	latex $^
	latex $^

these.pdf: these.dvi
	dvipdf these.dvi

clean:
	rm *.toc *.aux *.log *.bbl *.blg *.dvi *.nav *.out *.snm *.lof
