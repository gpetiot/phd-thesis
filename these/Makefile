MLPOST_EXEC :=$(shell which mlpost)
MLPOST ?= $(MLPOST_EXEC)
BIB=biblio.bib
MLFIG=frama_c_architecture.ml
FIG=$(MLFIG:.ml=.mps) figures/fig_mem_annots.tex figures/fig_add_patricia_trie.tex figures/fig_rem_patricia_trie.tex figures/fig_grammar.tex
LISTINGS=listings/mem_annots.c listings/common_prefix_mask.c listings/swap.c listings/naive_false_positive.c listings/naive_false_negative.c listings/is_present_normalized.c listings/is_present_instrumented.c
CHAPTERS_TEX=$(wildcard chapter_*.tex)
CHAPTERS_PDF=$(CHAPTERS_TEX:.tex=.pdf)

all: main.pdf $(CHAPTERS_PDF)

main.pdf: main.tex $(BIB) $(FIG) $(LISTINGS) style_listings.tex table_eacsl_experiments.tex commands.tex $(CHAPTERS_TEX) header.tex
	pdflatex $<
	bibtex main
	pdflatex $<
	pdflatex $<

$(CHAPTERS_PDF): %.pdf: %.tex chapter.tex header.tex $(BIB) $(FIG) $(LISTINGS) style_listings.tex commands.tex
	pdflatex -jobname="$(patsubst %.tex,%,$<)" "\def\chaptertoinclude{$(patsubst %.tex,%,$<)}\input{chapter}"
	bibtex $(patsubst %.tex,%,$<)
	pdflatex -jobname="$(patsubst %.tex,%,$<)" "\def\chaptertoinclude{$(patsubst %.tex,%,$<)}\input{chapter}"
	pdflatex -jobname="$(patsubst %.tex,%,$<)" "\def\chaptertoinclude{$(patsubst %.tex,%,$<)}\input{chapter}"

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
