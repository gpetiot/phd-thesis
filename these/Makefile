MLPOST_EXEC :=$(shell which mlpost)
MLPOST ?= $(MLPOST_EXEC)
BIB=biblio.bib
MLFIG=frama_c_architecture.ml
FIG=figures/fig_SANTE_slicing.tex figures/fig_SANTE_slicing_advanced.tex $(MLFIG:.ml=.mps) figures/fig_mem_annots.tex figures/fig_add_patricia_trie.tex figures/fig_rem_patricia_trie.tex
LISTINGS=listings/mem_annots.c listings/common_prefix_mask.c listings/swap.c

all: main.pdf

main.dvi: main.tex $(BIB) $(FIG) $(LISTINGS) style_listings.tex table_eacsl_experiments.tex commands.tex existant.tex motiv_contrib.tex traduction.tex preuve.tex runtime.tex stady.tex scenarios.tex ce.tex eacsl.tex header.tex
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

run_eacsl2c_on_mem_annots: listings/mem_annots.c
	frama-c $< -e-acsl -then-on e-acsl -print -ocode out.c && gcc out.c `frama-c -print-share-path`/e-acsl/e_acsl.c `frama-c -print-share-path`/e-acsl/memory_model/e_acsl_mmodel.c `frama-c -print-share-path`/e-acsl/memory_model/e_acsl_bittree.c && ./a.out
