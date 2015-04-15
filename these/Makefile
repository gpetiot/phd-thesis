MLPOST_EXEC :=$(shell which mlpost)
MLPOST ?= $(MLPOST_EXEC)
BIB=biblio.bib
MLFIG=frama_c_architecture.ml
FIG=$(MLFIG:.ml=.mps) \
	figures/fig_mem_annots.tex \
	figures/fig_add_patricia_trie.tex \
	figures/fig_rem_patricia_trie.tex \
	figures/fig_grammar.tex \
	figures/fig_rules.tex \
	figures/user_f.png \
	figures/user_m.png
LISTINGS=listings/mem_annots.c \
	listings/common_prefix_mask.c \
	listings/swap.c \
	listings/naive_false_positive.c \
	listings/naive_false_negative.c \
	listings/is_present_normalized.c \
	listings/is_present_instrumented.c
CHAPTERS_TEX=$(wildcard chapter_*.tex)
CHAPTERS_PDF=$(CHAPTERS_TEX:.tex=.pdf)

all_DEPS=chapter.tex header.tex $(BIB) style_listings.tex commands.tex
chapter_ce_DEPS=
chapter_motiv_contrib_DEPS=figures/user_f.png figures/user_m.png
chapter_scenarios_DEPS=
chapter_eacsl_DEPS=figures/fig_add_patricia_trie.tex \
		figures/fig_rem_patricia_trie.tex
chapter_preuve_DEPS=
chapter_stady_DEPS=
chapter_existant_DEPS=listings/swap.c
chapter_runtime_DEPS=figures/fig_mem_annots.tex \
		listings/mem_annots.c \
		listings/common_prefix_mask.c
chapter_traduction_DEPS=figures/fig_grammar.tex \
			figures/fig_rules.tex \
			listings/naive_false_positive.c \
			listings/naive_false_negative.c \
			listings/is_present_normalized.c \
			listings/is_present_instrumented.c

all: main.pdf $(CHAPTERS_PDF)

main.pdf: main.tex $(BIB) $(FIG) $(LISTINGS) style_listings.tex \
		table_eacsl_experiments.tex \
		commands.tex \
		$(CHAPTERS_TEX) \
		header.tex
	pdflatex $<
	bibtex main
	pdflatex $<
	pdflatex $<

compile_chapter= \
	pdflatex -jobname="$(1)" "\def\chaptertoinclude{$(1)}\input{chapter}" \
	bibtex $(1) \
	pdflatex -jobname="$(1)" "\def\chaptertoinclude{$(1)}\input{chapter}" \
	pdflatex -jobname="$(1)" "\def\chaptertoinclude{$(1)}\input{chapter}"

.SECONDEXPANSION:
chapter_%.pdf: chapter_%.tex $(all_DEPS) $${chapter_%_DEPS}
	$(call compile_chapter,$(patsubst %.tex,%,$<))

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
	frama-c $< -e-acsl -then-on e-acsl -print -ocode out.c && \
	gcc out.c `frama-c -print-share-path`/e-acsl/e_acsl.c \
	`frama-c -print-share-path`/e-acsl/memory_model/e_acsl_mmodel.c \
	`frama-c -print-share-path`/e-acsl/memory_model/e_acsl_bittree.c && \
	./a.out
