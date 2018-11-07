THESIS=thesis
AGDA=agda-2.6.0

all: latex/$(THESIS).pdf

AGDA_FILES:=\
  shared/Data/Var.lagda \
  shared/Data/Environment.lagda \
  type-scope-semantics/StateOfTheArt/McBride05.lagda \
  type-scope-semantics/Syntax/Type.lagda \
  type-scope-semantics/Syntax/Calculus.lagda \
  type-scope-semantics/Semantics/Specification.lagda

AGDA_OUTPUT:=$(patsubst %.lagda,latex-agda-output/%.tex,$(AGDA_FILES))
AGDA_OUTPUT_PROCESSED:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

.SECONDARY: $(AGDA_OUTPUT)

THESIS_DEPENDENCIES:=\
  latex/$(THESIS).tex \
  latex/agda.sty \
  latex/unicode.tex \
  latex/commands.tex \
  latex/main.bib \
  latex/indexed-combinators.tex \
  latex/type-scope-semantics.tex \
  latex/a-universe.tex \
  $(AGDA_OUTPUT_PROCESSED)

latex/main.bib: main.bib
	@mkdir -p $(dir $@)
	cp $< $@

latex/unicode.tex: unicode.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/agda.sty: $(AGDA_OUTPUT)
	@mkdir -p $(dir $@)
	cp latex-agda-output/shared/agda.sty $@

latex/commands.tex: commands.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(THESIS).pdf: $(THESIS_DEPENDENCIES)
	cd latex; latexmk -pdf -bibtex $(THESIS).tex

latex/$(THESIS).tex: $(THESIS).tex
	mkdir -p $(dir $@)
	cp $< $@

latex/indexed-combinators.tex: indexed-combinators.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/type-scope-semantics.tex: type-scope-semantics.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/a-universe.tex: a-universe.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/%.tex: latex-agda-output/%.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex-agda-output/shared/%.tex: shared/%.lagda
	@mkdir -p $(dir $@)
	${AGDA} --latex $< \
	        --latex-dir=latex-agda-output/shared/ \
		> $(basename $@).log

latex-agda-output/type-scope-semantics/%.tex: type-scope-semantics/%.lagda
	@mkdir -p $(dir $@)
	${AGDA} --latex $< \
	        --latex-dir=latex-agda-output/type-scope-semantics/ \
		> $(basename $@).log

clean:
	rm -rf latex/

fullclean: clean
	rm -rf latex-agda-output/
