CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  lib GeneralLogic MinimumLogic PropositionalLogic ModalLogic SeparationLogic \
  QuantifierLogic Extensions HoareLogic LogicGenerator

COQ_FLAG = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))
DEP_FLAG = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))

lib_FILES = \
  Coqlib.v Ensembles_ext.v EnsemblesProperties.v Relation_ext.v Equivalence_ext.v List_Func_ext.v \
  Bijection.v Countable.v NatChoice.v StrongInduction.v \
  Bisimulation.v RelationPairs_ext.v \
  register_typeclass.v SublistT.v \
  Stream/SigStream.v Stream/StreamFunctions.v Stream/StreamSplit.v 

GeneralLogic_ProofTheory_FILES = \
  BasicSequentCalculus.v TheoryOfSequentCalculus.v

GeneralLogic_Semantics_FILES = \
  Kripke.v

GeneralLogic_Complete_FILES = \
  ContextProperty_Trivial.v ContextProperty_Kripke.v ContextProperty.v \
  Canonical_Kripke.v \
  Lindenbaum.v Lindenbaum_Kripke.v \
  Complete_Kripke.v 

GeneralLogic_ShallowEmbedded_FILES = \
  PredicateAsLang.v MonoPredicateAsLang.v

GeneralLogic_FILES = \
  Base.v HenkinCompleteness.v \
  KripkeModel.v \
  $(GeneralLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(GeneralLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(GeneralLogic_Complete_FILES:%.v=Complete/%.v) \
  $(GeneralLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

MinimumLogic_ProofTheory_FILES = \
  Minimum.v ProofTheoryPatterns.v \
  RewriteClass.v TheoryOfSequentCalculus.v ExtensionTactic.v

MinimumLogic_Semantics_FILES = \
  Kripke.v Trivial.v SemanticEquiv.v

MinimumLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

MinimumLogic_Complete_FILES = \
  ContextProperty_Kripke.v Lindenbaum_Kripke.v Truth_Kripke.v

MinimumLogic_ShallowEmbedded_FILES = \

MinimumLogic_DeepEmbedded_FILES = \
  MinimumLanguage.v KripkeSemantics.v MinimumLogic.v \
  Complete_Kripke.v Soundness.v

MinimumLogic_FILES = \
  Syntax.v \
  $(MinimumLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(MinimumLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(MinimumLogic_Sound_FILES:%.v=Sound/%.v) \
  $(MinimumLogic_Complete_FILES:%.v=Complete/%.v) \
  $(MinimumLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v)

PropositionalLogic_ProofTheory_FILES = \
  Intuitionistic.v DeMorgan.v \
  GodelDummett.v Classical.v \
  RewriteClass.v ProofTheoryPatterns.v

PropositionalLogic_Semantics_FILES = \
  Kripke.v Trivial.v

PropositionalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

PropositionalLogic_Complete_FILES = \
  ContextProperty_Kripke.v \
  Lindenbaum_Kripke.v Canonical_Kripke.v Truth_Kripke.v \
  ContextProperty_Trivial.v \
  Lindenbaum_Trivial.v Truth_Trivial.v Complete_Trivial.v

PropositionalLogic_DeepEmbedded_FILES = \
  PropositionalLanguage.v ProofTheories.v \
  KripkeSemantics.v TrivialSemantics.v \
  Soundness.v Complete_Kripke.v Complete_Classical_Trivial.v \
  Deep.v Solver.v

PropositionalLogic_ShallowEmbedded_FILES = \
  PredicatePropositionalLogic.v \
  MonoPredicatePropositionalLogic.v

PropositionalLogic_FILES = \
  Syntax.v\
  $(PropositionalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(PropositionalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(PropositionalLogic_Sound_FILES:%.v=Sound/%.v) \
  $(PropositionalLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(PropositionalLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v) \
  $(PropositionalLogic_Complete_FILES:%.v=Complete/%.v)

ModalLogic_ProofTheory_FILES = \
  ModalLogic.v RewriteClass.v \
  ClassicalDerivedRules.v IntuitionisticDerivedRules.v

ModalLogic_Model_FILES = \
  KripkeModel.v OrderedKripkeModel.v

ModalLogic_Semantics_FILES = \
  Kripke.v Flat.v

ModalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Flat.v

ModalLogic_ShallowEmbedded_FILES = \
  PredicateModalLogic.v \
  MonoPredicateModalLogic.v

ModalLogic_FILES = \
  Syntax.v \
  $(ModalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(ModalLogic_Model_FILES:%.v=Model/%.v) \
  $(ModalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(ModalLogic_Sound_FILES:%.v=Sound/%.v) \
  $(ModalLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

QuantifierLogic_ProofTheory_FILES = \
  QuantifierLogic.v

QuantifierLogic_DeepEmbedded_FILES = \
  FirstOrderLanguage.v FirstOrderLogic.v

QuantifierLogic_ShallowEmbedded_FILES = \
  PredicateAsBLang.v PredicateQuantifierLogic.v

QuantifierLogic_FILES = \
  Syntax.v \
  $(QuantifierLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(QuantifierLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(QuantifierLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

SeparationLogic_ProofTheory_FILES = \
  SeparationLogic.v SeparationLogicExtension.v \
  RewriteClass.v DerivedRules.v IterSepcon.v WandFrame.v

SeparationLogic_Model_FILES = \
  SeparationAlgebra.v OrderedSA.v \
  UpwardsClosure.v DownwardsClosure.v \
  OSAGenerators.v OSAExamples.v

SeparationLogic_Semantics_FILES = \
  WeakSemantics.v StrongSemantics.v \
  UpwardsSemantics.v DownwardsSemantics.v FlatSemantics.v \
  DownUpSemantics_Fail.v \
  Down2Flat.v Up2Flat.v \
  SemanticsExtension.v

SeparationLogic_Sound_FILES = \
  Sound_Downwards.v Sound_Upwards.v Sound_Flat.v \
  Sound_DownUp_Fail.v

SeparationLogic_Complete_FILES = \
  ContextProperty_Flat.v \
  Lindenbaum_Flat.v Truth_Flat.v Canonical_Flat.v

SeparationLogic_DeepEmbedded_FILES = \
  SeparationLanguage.v SeparationEmpLanguage.v \
  Parameter.v \
  ParametricSeparationLogic.v SeparationLogicsInLiteratures.v \
  FlatSemantics.v ParametricCompleteness.v

SeparationLogic_ShallowEmbedded_FILES = \
  PredicateSeparationLogic.v MonoPredicateSeparationLogic.v

SeparationLogic_FILES = \
  Syntax.v \
  $(SeparationLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(SeparationLogic_Model_FILES:%.v=Model/%.v) \
  $(SeparationLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(SeparationLogic_Sound_FILES:%.v=Sound/%.v) \
  $(SeparationLogic_Complete_FILES:%.v=Complete/%.v) \
  $(SeparationLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(SeparationLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

Extensions_ProofTheory_FILES = \
  Stable.v ModalSeparation.v Corable.v CoreTransit.v

Extensions_Semantics_FILES = \
  SemanticStable.v ModalSeparation.v

Extensions_Sound_FILES = \
  StableSound.v

Extensions_ShallowEmbedded_FILES = \
  MonoPredicateStable.v

Extensions_FILES = \
  Syntax_CoreTransit.v \
  $(Extensions_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(Extensions_Semantics_FILES:%.v=Semantics/%.v) \
  $(Extensions_Sound_FILES:%.v=Sound/%.v) \
  $(Extensions_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v)

HoareLogic_FILES = \
  ImperativeLanguage.v ProgramState.v Trace.v \
  SimpleSmallStepSemantics.v SmallStepSemantics.v \
  BigStepSemantics.v ConcurrentSemantics_Angelic.v \
  TraceSemantics.v \
  OperationalSemanticsGenerator.v \
  HoareLogic.v GuardedHoareLogic.v \
  HoareTriple_BigStepSemantics.v GuardedHoareTriple_Angelic.v GuardedHoareTriple_TraceSemantics.v \
  Sound_Basic.v Sound_Imp.v Sound_Frame.v \
  Sound_Resource_Angelic.v Sound_Resource_TraceSemantics.v

LogicGenerator_FILES = \
  ConfigLang.v ConfigDenot.v ConfigCompute.v Utils.v #Generate.v 

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  $(GeneralLogic_FILES:%.v=GeneralLogic/%.v) \
  $(MinimumLogic_FILES:%.v=MinimumLogic/%.v) \
  $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.v) \
  $(ModalLogic_FILES:%.v=ModalLogic/%.v) \
  $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.v) \
  $(SeparationLogic_FILES:%.v=SeparationLogic/%.v) \
  $(Extensions_FILES:%.v=Extensions/%.v) \
  $(HoareLogic_FILES:%.v=HoareLogic/%.v) \
  $(LogicGenerator_FILES:%.v=LogicGenerator/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

lib: \
  .depend $(lib_FILES:%.v=lib/%.vo)

GeneralLogic: \
  .depend $(GeneralLogic_FILES:%.v=GeneralLogic/%.vo)

MinimumLogic: \
  .depend $(MinimumLogic_FILES:%.v=MinimumLogic/%.vo)

PropositionalLogic: \
  .depend $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.vo)

ModalLogic: \
  .depend $(ModalLogic_FILES:%.v=ModalLogic/%.vo)

QuantifierLogic: \
  .depend $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.vo)

SeparationLogic: \
  .depend $(SeparationLogic_FILES:%.v=SeparationLogic/%.vo)

all: \
  $(FILES:%.v=%.vo)

lgen_demo_1:
	./logic_gen.sh LogicGenerator/demo/configuration_1.v LogicGenerator/demo/interface_1.v
	@echo COQC LogicGenerator/demo/interface_1.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_1.v
	@echo COQC LogicGenerator/demo/implementation_1.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_1.v

lgen_demo_2:
	./logic_gen.sh LogicGenerator/demo/configuration_2.v LogicGenerator/demo/interface_2.v
	@echo COQC LogicGenerator/demo/interface_2.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_2.v
	@echo COQC LogicGenerator/demo/implementation_2a.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_2a.v
	@echo COQC LogicGenerator/demo/implementation_2b.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_2b.v

lgen_demo_3:
	./logic_gen.sh LogicGenerator/demo/configuration_3.v LogicGenerator/demo/interface_3.v
	@echo COQC LogicGenerator/demo/interface_3.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/interface_3.v
	@echo COQC LogicGenerator/demo/implementation_3.v
	@$(COQC) $(COQ_FLAG) LogicGenerator/demo/implementation_3.v

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob */*/*.vo */*/*.glob

.DEFAULT_GOAL := all

include .depend

