THESIS=thesis
AGDA=agda-2.6.0

all: latex/$(THESIS).pdf

AGDA_FILES:=\
  shared/Stdlib.lagda \
  shared/Data/Var.lagda \
  shared/Data/Var/Varlike.lagda \
  shared/Data/Environment.lagda \
  shared/Data/Relation.lagda \
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
  type-scope-semantics.agda/Semantics/NormalisationByEvaluation/BetaIotaXiEta.lagda \
  type-scope-semantics.agda/Semantics/NormalisationByEvaluation/BetaIotaXi.lagda \
  type-scope-semantics.agda/Semantics/NormalisationByEvaluation/BetaIota.lagda \
  type-scope-semantics.agda/Semantics/CPS/CBN.lagda \
  type-scope-semantics.agda/Semantics/CPS/CBV.lagda \
  type-scope-semantics.agda/Properties/Simulation/Specification.lagda \
  type-scope-semantics.agda/Properties/Simulation/Instances.lagda \
  type-scope-semantics.agda/Properties/Fusion/Specification.lagda \
  type-scope-semantics.agda/Properties/Fusion/Syntactic/Specification.lagda \
  generic-syntax.agda/Generic/Data.lagda \
  generic-syntax.agda/Generic/Syntax.lagda \
  generic-syntax.agda/Generic/Examples/STLC.lagda \
  generic-syntax.agda/Generic/Examples/UntypedLC.lagda \
  generic-syntax.agda/Generic/Semantics.lagda \
  generic-syntax.agda/Generic/Semantics/Syntactic.lagda \
  generic-syntax.agda/Generic/Zip.lagda \
  generic-syntax.agda/Generic/Identity.lagda \
  generic-syntax.agda/Generic/Simulation.lagda \
  generic-syntax.agda/Generic/Simulation/Syntactic.lagda \
  generic-syntax.agda/Generic/Fusion.lagda \
  generic-syntax.agda/Generic/Fusion/Syntactic.lagda \
  generic-syntax.agda/Generic/Fusion/Specialised/Propositional.lagda \
  generic-syntax.agda/Generic/Fusion/Syntactic.lagda \
  generic-syntax.agda/Generic/Examples/ElaborationLet.lagda \

AGDA_OUTPUT:=$(patsubst %.lagda,latex-agda-output/%.tex,$(AGDA_FILES))
AGDA_OUTPUT_PROCESSED:=$(patsubst %.lagda,latex/%.tex,$(AGDA_FILES))

.SECONDARY: $(AGDA_OUTPUT)

THESIS_DEPENDENCIES:=\
  latex/$(THESIS).tex \
  latex/agda.sty \
  latex/unicode.tex \
  latex/commands.tex \
  latex/main.bib \
  latex/introduction-agda.tex \
  latex/type-scope-semantics.tex/refactoring.tex \
  latex/type-scope-semantics.tex/normalization.tex \
  latex/type-scope-semantics.tex/cps-translation.tex \
  latex/type-scope-semantics.tex/program-conclusion.tex \
  latex/type-scope-semantics.tex/simulation.tex \
  latex/type-scope-semantics.tex/fusion.tex \
  latex/type-scope-semantics.tex/proof-conclusion.tex \
  latex/generic-syntax.tex/data.tex \
  latex/generic-syntax.tex/syntax.tex \
  latex/generic-syntax.tex/a-universe.tex \
  latex/generic-syntax.tex/safe-programs.tex \
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

latex/introduction-agda.tex: introduction-agda.tex
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
