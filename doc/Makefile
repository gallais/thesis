THESIS=thesis
STRATH=strath
SLIDES=slides

AGDA?=agda-2.6.4

all: slides

strath: latex/$(STRATH).pdf
thesis: latex/$(THESIS).pdf
slides: latex/$(SLIDES).pdf

AGDA_FILES:=\
  shared/Stdlib.lagda \
  shared/Data/Var.lagda \
  shared/Data/Var/Varlike.lagda \
  shared/Data/Environment.lagda \
  shared/Data/Environment/Sized.lagda \
  shared/Data/Relation.lagda \
  shared/Data/Relation/Sized.lagda \
  shared/Relation/Binary/PropositionalEquality/Extra.lagda \
  introduction.agda/introduction.lagda \
  type-scope-semantics.agda/StateOfTheArt/McBride05/Base.lagda \
  type-scope-semantics.agda/StateOfTheArt/McBride05/Kit.lagda \
  type-scope-semantics.agda/Syntax/Type.lagda \
  type-scope-semantics.agda/Syntax/Calculus.lagda \
  type-scope-semantics.agda/Syntax/Normal.lagda \
  type-scope-semantics.agda/Syntax/WeakHead.lagda \
  type-scope-semantics.agda/Syntax/MoggiML/Type.lagda \
  type-scope-semantics.agda/Syntax/MoggiML/Calculus.lagda \
  type-scope-semantics.agda/Syntax/MoggiML/CPS.lagda \
  type-scope-semantics.agda/Semantics/Specification.lagda \
  type-scope-semantics.agda/Semantics/Syntactic/Specification.lagda \
  type-scope-semantics.agda/Semantics/Syntactic/Instances.lagda \
  type-scope-semantics.agda/Semantics/Printing.lagda \
  type-scope-semantics.agda/Semantics/NormalisationByEvaluation/Specification.lagda \
  type-scope-semantics.agda/Semantics/NormalisationByEvaluation/BetaIotaXiEta.lagda \
  type-scope-semantics.agda/Semantics/NormalisationByEvaluation/BetaIotaXi.lagda \
  type-scope-semantics.agda/Semantics/NormalisationByEvaluation/BetaIota.lagda \
  type-scope-semantics.agda/Semantics/CPS/CBN.lagda \
  type-scope-semantics.agda/Semantics/CPS/CBV.lagda \
  type-scope-semantics.agda/Properties/Simulation/Specification.lagda \
  type-scope-semantics.agda/Properties/Simulation/Instances.lagda \
  type-scope-semantics.agda/Properties/Fusion/Specification.lagda \
  type-scope-semantics.agda/Properties/Fusion/Syntactic/Specification.lagda \
  type-scope-semantics.agda/Properties/Fusion/Syntactic/Instances.lagda \
  type-scope-semantics.agda/Properties/Fusion/Instances.lagda \
  generic-syntax.agda/Motivation/Problem/Naive.lagda \
  generic-syntax.agda/Generic/Data.lagda \
  generic-syntax.agda/Generic/Syntax.lagda \
  generic-syntax.agda/Generic/Syntax/Bidirectional.lagda \
  generic-syntax.agda/Generic/Syntax/Extended.lagda \
  generic-syntax.agda/Generic/Syntax/LetBinder.lagda \
  generic-syntax.agda/Generic/Syntax/LetCounter.lagda \
  generic-syntax.agda/Generic/Examples/STLC.lagda \
  generic-syntax.agda/Generic/Examples/UntypedLC.lagda \
  generic-syntax.agda/Generic/Semantics.lagda \
  generic-syntax.agda/Generic/Semantics/Syntactic.lagda \
  generic-syntax.agda/Generic/Semantics/Elaboration/LetBinder.lagda \
  generic-syntax.agda/Generic/Semantics/Elaboration/LetCounter.lagda \
  generic-syntax.agda/Generic/Semantics/TypeChecking.lagda \
  generic-syntax.agda/Generic/Semantics/Elaboration/Typed.lagda \
  generic-syntax.agda/Generic/Scopecheck.lagda \
  generic-syntax.agda/Generic/Relator.lagda \
  generic-syntax.agda/Generic/Identity.lagda \
  generic-syntax.agda/Generic/Simulation.lagda \
  generic-syntax.agda/Generic/Simulation/Syntactic.lagda \
  generic-syntax.agda/Generic/Fusion.lagda \
  generic-syntax.agda/Generic/Fusion/Syntactic.lagda \
  generic-syntax.agda/Generic/Fusion/Specialised/Propositional.lagda \
  generic-syntax.agda/Generic/Fusion/Syntactic.lagda \
  generic-syntax.agda/Generic/Examples/ElaborationLet.lagda \
  generic-syntax.agda/Generic/Semantics/NbyE.lagda \
  generic-syntax.agda/Generic/Semantics/Printing.lagda \
  generic-syntax.agda/Generic/Examples/NbyE.lagda \
  generic-syntax.agda/Generic/Examples/TypeChecking.lagda \
  generic-syntax.agda/Generic/Examples/Elaboration.lagda \
  generic-syntax.agda/Generic/Examples/Printing.lagda \
  generic-syntax.agda/Generic/Equality.lagda \

AGDA_OUTPUT:=$(patsubst %.lagda,latex-agda-output/%.tex,$(AGDA_FILES))
AGDA_OUTPUT_PROCESSED:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

.SECONDARY: $(AGDA_OUTPUT)

THESIS_DEPENDENCIES:=\
  latex/$(THESIS).tex \
  latex/convention.tex \
  latex/agda.sty \
  latex/unicode.tex \
  latex/commands.tex \
  latex/robust-catch.tex \
  latex/main.bib \
  latex/cover.tex \
  latex/introduction.tex/intro.tex \
  latex/introduction.tex/agda.tex \
  latex/introduction.tex/type-theory.tex \
  latex/introduction.tex/category.tex \
  latex/type-scope-semantics.tex/syntax.tex \
  latex/type-scope-semantics.tex/refactoring.tex \
  latex/type-scope-semantics.tex/normalization.tex \
  latex/type-scope-semantics.tex/normalization/betaiotaxieta.tex \
  latex/type-scope-semantics.tex/normalization/betaiotaxi.tex \
  latex/type-scope-semantics.tex/normalization/betaiota.tex \
  latex/type-scope-semantics.tex/cps-translation.tex \
  latex/type-scope-semantics.tex/program-conclusion.tex \
  latex/type-scope-semantics.tex/simulation.tex \
  latex/type-scope-semantics.tex/fusion.tex \
  latex/type-scope-semantics.tex/proof-conclusion.tex \
  latex/generic-syntax.tex/data.tex \
  latex/generic-syntax.tex/syntax.tex \
  latex/generic-syntax.tex/a-universe.tex \
  latex/generic-syntax.tex/safe-programs.tex \
  latex/generic-syntax.tex/catalogue/desugaring.tex \
  latex/generic-syntax.tex/catalogue/inlining.tex \
  latex/generic-syntax.tex/catalogue/normalising.tex \
  latex/generic-syntax.tex/catalogue/printing.tex \
  latex/generic-syntax.tex/catalogue/typechecking.tex \
  latex/generic-syntax.tex/catalogue/elaborating.tex \
  latex/generic-syntax.tex/catalogue/scopechecking.tex \
  latex/generic-syntax.tex/catalogue/equality.tex \
  latex/generic-syntax.tex/compiling.tex \
  latex/generic-syntax.tex/other-programs.tex \
  latex/generic-syntax.tex/proofs.tex \
  latex/generic-syntax.tex/proofs/simulation.tex \
  latex/generic-syntax.tex/proofs/fusion.tex \
  latex/conclusion.tex \
  $(AGDA_OUTPUT_PROCESSED)

STRATH_DEPENDENCIES:=\
  latex/$(STRATH).tex \
  latex/titlingpage.tex \
  latex/strath_coat.png \
  $(THESIS_DEPENDENCIES)

SLIDES_DEPENDENCIES:=\
  latex/$(SLIDES).tex \
  $(THESIS_DEPENDENCIES)

latex/main.bib: main.bib
	@mkdir -p $(dir $@)
	cp $< $@

latex/conclusion.tex: conclusion.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/unicode.tex: unicode.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/agda.sty: agda.sty
	@mkdir -p $(dir $@)
	cp $< $@

latex/commands.tex: commands.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/robust-catch.tex: robust-catch.tex
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(SLIDES).pdf: $(SLIDES_DEPENDENCIES)
	cd latex; latexmk -pdf -bibtex $(SLIDES).tex

latex/$(THESIS).pdf: $(THESIS_DEPENDENCIES)
	cd latex; latexmk -pdf -bibtex $(THESIS).tex

latex/$(STRATH).pdf: $(STRATH_DEPENDENCIES)
	cd latex; latexmk -pdf -bibtex $(STRATH).tex

latex/$(THESIS).tex: $(THESIS).tex
	mkdir -p $(dir $@)
	cp $< $@

latex/$(STRATH).tex: $(STRATH).tex
	mkdir -p $(dir $@)
	cp $< $@

latex/$(SLIDES).tex: $(SLIDES).tex
	mkdir -p $(dir $@)
	cp $< $@

latex/cover.tex: cover.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/strath_coat.png: strath_coat.png
	mkdir -p $(dir $@)
	cp $< $@

latex/titlingpage.tex: titlingpage.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/convention.tex: convention.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/introduction.tex/%.tex: introduction.tex/%.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/type-scope-semantics.tex/%.tex: type-scope-semantics.tex/%.tex
	mkdir -p $(dir $@)
	cp $< $@

latex/generic-syntax.tex/%.tex: generic-syntax.tex/%.tex
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

latex-agda-output/introduction.agda/%.tex: introduction.agda/%.lagda
	@mkdir -p $(dir $@)
	${AGDA} --latex $< \
	        --latex-dir=latex-agda-output/introduction.agda/ \
		> $(basename $@).log

latex-agda-output/type-scope-semantics.agda/%.tex: type-scope-semantics.agda/%.lagda
	@mkdir -p $(dir $@)
	${AGDA} --latex $< \
	        --latex-dir=latex-agda-output/type-scope-semantics.agda/ \
		> $(basename $@).log

latex-agda-output/generic-syntax.agda/%.tex: generic-syntax.agda/%.lagda
	@mkdir -p $(dir $@)
	${AGDA} --latex $< \
	        --latex-dir=latex-agda-output/generic-syntax.agda/ \
		> $(basename $@).log

clean:
	rm -rf latex/

fullclean: clean
	rm -rf latex-agda-output/
