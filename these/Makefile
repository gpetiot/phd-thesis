
BIB=biblio.bib
SCHEMES=fig_SANTE_slicing.tex fig_SANTE_slicing_advanced.tex fig_frama_c.tex

all: main.pdf

main.dvi: main.tex $(BIB) $(SCHEMES) style_listings.tex
	latex $^
	bibtex main
	latex $^
	latex $^

main.pdf: main.dvi
	dvipdf main.dvi

clean:
	rm *.toc *.aux *.log *.bbl *.blg *.dvi *.nav *.out *.snm *.lof
