CURRENT_DIR=./
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  lib GeneralLogic MinimunLogic PropositionalLogic ModalLogic SeparationLogic \
  QuantifierLogic Extensions HoareLogic

INCLUDE_DEMO = $(foreach d, $(DIRS), -R $(CURRENT_DIR)/$(d) Logic.$(d))
COQ_FLAG = $(INCLUDE_DEMO)
DEP_DEMO = -R $(CURRENT_DIR) Logic
DEP_FLAG = $(DEP_DEMO) 

lib_FILES = \
  Coqlib.v Ensembles_ext.v Relation_ext.v Equivalence_ext.v List_Func_ext.v \
  Bijection.v Countable.v NatChoice.v StrongInduction.v \
  SublistT.v \
  Stream/SigStream.v Stream/StreamFunctions.v Stream/StreamSplit.v 

GeneralLogic_ShallowEmbedded_FILES = \
  PredicateAsLang.v MonoPredicateAsLang.v

GeneralLogic_FILES = \
  Base.v HenkinCompleteness.v \
  KripkeModel.v \
  $(GeneralLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v) 

MinimunLogic_ProofTheory_FILES = \
  Normal.v Minimun.v Adjoint.v AdjointLemmas.v \
  RewriteClass.v ContextProperty.v

MinimunLogic_FILES = \
  Syntax.v $(MinimunLogic_ProofTheory_FILES:%.v=ProofTheory/%.v)

PropositionalLogic_ProofTheory_FILES = \
  Intuitionistic.v DeMorgan.v \
  GodelDummett.v Classical.v \
  RewriteClass.v

PropositionalLogic_Semantics_FILES = \
  Kripke.v Trivial.v SemanticEquiv.v

PropositionalLogic_Sound_FILES = \
  Sound_Kripke.v Sound_Classical_Trivial.v

PropositionalLogic_DeepEmbedded_FILES = \
  PropositionalLanguage.v \
  IntuitionisticLogic.v DeMorganLogic.v \
  GodelDummettLogic.v ClassicalLogic.v \
  KripkeSemantics.v TrivialSemantics.v \
  Soundness.v

PropositionalLogic_ShallowEmbedded_FILES = \
  PredicatePropositionalLogic.v \
  MonoPredicatePropositionalLogic.v

PropositionalLogic_Complete_FILES = \
  Complete_Classical_Trivial.v \
  Complete_Kripke.v

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

ModalLogic_FILES = \
  Syntax.v \
  $(ModalLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(ModalLogic_Model_FILES:%.v=Model/%.v) \
  $(ModalLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(ModalLogic_Sound_FILES:%.v=Sound/%.v)

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
  RewriteClass.v DerivedRules.v IterSepcon.v 

SeparationLogic_Model_FILES = \
  SeparationAlgebra.v OrderedSA.v \
  UpwardsClosure.v DownwardsClosure.v \
  OSAGenerators.v OSAExamples.v

SeparationLogic_Semantics_FILES = \
  WeakSemantics.v StrongSemantics.v \
  WeakSemanticsMono.v StrongSemanticsMono.v \
  UpwardsSemantics.v DownwardsSemantics.v FlatSemantics.v \
  DownUpSemantics_Fail.v \
  Down2Flat.v Up2Flat.v \
  SemanticsExtension.v

SeparationLogic_Sound_FILES = \
  Sound_Downwards.v Sound_Upwards.v Sound_Flat.v \
  Sound_DownUp_Fail.v

SeparationLogic_DeepEmbedded_FILES = \
  SeparationLanguage.v SeparationEmpLanguage.v \
  Parameter.v \
  ParametricSeparationLogic.v SeparationLogicsInLiteratures.v \
  FlatSemantics.v

SeparationLogic_ShallowEmbedded_FILES = \
  PredicateSeparationLogic.v MonoPredicateSeparationLogic.v

SeparationLogic_FILES = \
  Syntax.v \
  $(SeparationLogic_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(SeparationLogic_Model_FILES:%.v=Model/%.v) \
  $(SeparationLogic_Semantics_FILES:%.v=Semantics/%.v) \
  $(SeparationLogic_Sound_FILES:%.v=Sound/%.v) \
  $(SeparationLogic_DeepEmbedded_FILES:%.v=DeepEmbedded/%.v) \
  $(SeparationLogic_ShallowEmbedded_FILES:%.v=ShallowEmbedded/%.v) \
  Complete_Flat.v

Extentions_ProofTheory_FILES = \
  Stable.v ModalSeparation.v Corable.v CoreTransit.v

Extentions_Semantics_FILES = \
  SemanticStable.v ModalSeparation.v

Extentions_Sound_FILES = \
  StableSound.v

Extentions_FILES = \
  Syntax_CoreTransit.v \
  $(Extentions_ProofTheory_FILES:%.v=ProofTheory/%.v) \
  $(Extentions_Semantics_FILES:%.v=Semantics/%.v) \
  $(Extentions_Sound_FILES:%.v=Sound/%.v)

HoareLogic_FILES = \
  ImperativeLanguage.v ProgramState.v Trace.v \
  SimpleSmallStepSemantics.v SmallStepSemantics.v \
  BigStepSemantics.v ConcurrentSemantics.v LocalTraceSemantics.v \
  OperationalSemanticsGenerator.v \
  HoareLogic_Sequential.v HoareLogic_Concurrent.v \
  Sound_Basic.v Sound_Imp.v Sound_Frame.v \
  Sound_ResourceBrookes.v

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  $(GeneralLogic_FILES:%.v=GeneralLogic/%.v) \
  $(MinimunLogic_FILES:%.v=MinimunLogic/%.v) \
  $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.v) \
  $(ModalLogic_FILES:%.v=ModalLogic/%.v) \
  $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.v) \
  $(SeparationLogic_FILES:%.v=SeparationLogic/%.v) \
  $(Extentions_FILES:%.v=Extensions/%.v) \
  IRIS/Sound.v \
  $(HoareLogic_FILES:%.v=HoareLogic/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

lib: \
  .depend $(lib_FILES:%.v=lib/%.vo)

GeneralLogic: \
  .depend $(GeneralLogic_FILES:%.v=GeneralLogic/%.vo)

MinimunLogic: \
  .depend $(MinimunLogic_FILES:%.v=MinimunLogic/%.vo)

PropositionalLogic: \
  .depend $(PropositionalLogic_FILES:%.v=PropositionalLogic/%.vo)

ModalLogic: \
  .depend $(ModalLogic_FILES:%.v=ModalLogic/%.vo)

QuantifierLogic: \
  .depend $(QuantifierLogic_FILES:%.v=QuantifierLogic/%.vo)

SeparationLogic: \
  .depend $(SeparationLogic_FILES:%.v=SeparationLogic/%.vo)

all: \
  $(FILES:%.v=%.vo) \

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob */*/*.vo */*/*.glob

.DEFAULT_GOAL := all

include .depend


#COQC = coqc
# 
#%.vo: %.v
# 	@echo COQC $*.v
# 	@$(COQC) -q -R "." -as Logic $*.v
# 
#all: 
#     
#     SeparationLogic/Syntax.vo SeparationLogic/SeparationLogic.vo \
#     SeparationLogic/QinxiangSantiagoSemantics.vo
