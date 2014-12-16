
BIB=biblio.bib
SCHEMES=SANTE_slicing.tex SANTE_slicing_advanced.tex

all: main.pdf

main.dvi: main.tex $(BIB) $(SCHEMES) existant.tex memory_model.tex stady.tex
	latex $^
	bibtex main
	latex $^
	latex $^

main.pdf: main.dvi
	dvipdf main.dvi

clean:
	rm *.toc *.aux *.log *.bbl *.blg *.dvi *.nav *.out *.snm *.lof
