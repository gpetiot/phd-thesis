MLPOST_EXEC :=$(shell which mlpost)
MLPOST ?= $(MLPOST_EXEC)
BIB=biblio.bib
MLFIG=frama_c_architecture.ml
FIG=fig_SANTE_slicing.tex fig_SANTE_slicing_advanced.tex $(MLFIG:.ml=.mps) tikz_mem_annots.tex

all: main.pdf

main.dvi: main.tex $(BIB) $(FIG) style_listings.tex table_eacsl_experiments.tex commands.tex existant.tex mem_annots.c
	latex $^
	bibtex main
	latex $^
	latex $^

main.pdf: main.dvi
	dvipdf main.dvi


.SUFFIXES: .fig .pdf .eps .mll .ml .mps

#MLPOST is a conditional variable.
ifneq ($(MLPOST),)
.ml.mps:
	$(MLPOST) -pdf $<
	$(RM) $(<:.ml=.cm*)

else
	$(info Warning: Mlpost is not installed so we use the one versionned.)
endif


clean:
	rm *.toc *.aux *.log *.bbl *.blg *.dvi *.nav *.out *.snm *.lof
