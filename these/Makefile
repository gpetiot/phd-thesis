MLPOST_EXEC :=$(shell which mlpost)
MLPOST ?= $(MLPOST_EXEC)
BIB=biblio.bib
MLFIG=frama_c_architecture.ml
FIG=$(MLFIG:.ml=.mps) \
	figures/fig_mem_annots.tex \
	figures/fig_add_patricia_trie.tex \
	figures/fig_rem_patricia_trie.tex \
	figures/fig_grammar.tex \
	figures/fig_grammar_exp_term.tex \
	figures/fig_grammar_pred.tex \
	figures/fig_rules_annot.tex \
	figures/fig_rules_loop_annot.tex \
	figures/fig_rules_const_id.tex \
	figures/fig_rules_coerce.tex \
	figures/fig_rules_op.tex \
	figures/fig_rules_builtin.tex \
	figures/fig_rules_pred.tex \
	figures/fig_rules_valid.tex \
	figures/fig_rules_quantif.tex \
	figures/user_f.png \
	figures/user_m.png \
	figures/fig_code_gen.tex \
	figures/fig_code_ins.tex \
	figures/fig_proof_loop_contract.tex \
	figures/fig_proof_fct_contract_call.tex \
	figures/fig_proof_fct_contract_main.tex \
	figures/fig_semantics.tex \
	figures/fig_semantics_exp_term.tex \
	figures/fig_semantics_pred.tex \
	figures/fig_semantics_fct.tex \
	figures/mmodel_architecture.pdf \
	figures/stady_architecture.pdf
LISTINGS=listings/mem_annots.c \
	listings/mem_annots_instru.c \
	listings/common_prefix_mask.c \
	listings/swap.c \
	listings/naive_false_positive.c \
	listings/naive_false_negative.c \
	listings/is_present_normalized.c \
	listings/is_present_instrumented.c \
	listings/ex1.c \
	listings/ex2.c \
	listings/rgf_0.c \
	listings/deleteSubstrTrous.c \
	listings/findSubstr.c
CHAPTERS_TEX=$(wildcard chapter_*.tex)
CHAPTERS_PDF=$(CHAPTERS_TEX:.tex=.pdf)

all_DEPS=chapter.tex header.tex $(BIB) style_listings.tex commands.tex
chapter_swd_DEPS=listings/ex1.c \
		listings/ex2.c \
		listings/rgf_0.c
chapter_motiv_contrib_DEPS=figures/user_f.png \
			figures/user_m.png
chapter_ncd_DEPS=listings/deleteSubstrTrous.c \
		listings/findSubstr.c
chapter_method_DEPS=table_rgf.pdf
chapter_eacsl_DEPS=figures/mmodel_architecture.pdf
chapter_stady_DEPS=full_exp_latex_IEEE.csv figures/stady_architecture.pdf
chapter_existant_DEPS=listings/swap.c
chapter_runtime_DEPS=figures/fig_mem_annots.tex \
		listings/mem_annots.c \
		listings/mem_annots_instru.c \
		listings/common_prefix_mask.c \
		figures/fig_add_patricia_trie.tex \
		figures/fig_rem_patricia_trie.tex
chapter_lang_DEPS=figures/fig_grammar.tex \
		figures/fig_grammar_exp_term.tex \
		figures/fig_grammar_pred.tex \
		figures/fig_semantics.tex \
		figures/fig_semantics_exp_term.tex \
		figures/fig_semantics_pred.tex \
		figures/fig_semantics_fct.tex \
		listings/is_present_normalized.c
chapter_instrumentation_DEPS=figures/fig_rules_annot.tex \
			figures/fig_rules_loop_annot.tex \
			figures/fig_rules_const_id.tex \
			figures/fig_rules_coerce.tex \
			figures/fig_rules_op.tex \
			figures/fig_rules_builtin.tex \
			figures/fig_rules_pred.tex \
			figures/fig_rules_valid.tex \
			figures/fig_rules_quantif.tex \
			listings/naive_false_positive.c \
			listings/naive_false_negative.c \
			listings/is_present_instrumented.c \
			figures/fig_code_gen.tex \
			figures/fig_code_ins.tex \
			figures/fig_proof_loop_contract.tex \
			figures/fig_proof_fct_contract_call.tex \
			figures/fig_proof_fct_contract_main.tex

all: main.pdf $(CHAPTERS_PDF) abstract.pdf

abstract.pdf: abstract.tex
	pdflatex $<

main.pdf: main.tex $(BIB) $(FIG) $(LISTINGS) style_listings.tex \
		table_eacsl_experiments.tex \
		commands.tex \
		$(CHAPTERS_TEX) \
		table_rgf.pdf \
		full_exp_latex_IEEE.csv \
		header.tex
	pdflatex $<
	bibtex main
	pdflatex $<
	pdflatex $<

table_rgf.pdf: table_rgf.tex
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
