Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.Corable.

Require Logic.LogicGenerator.ConfigLang.
Require Import Logic.LogicGenerator.Utils. 

Module D.
Import ConfigLang.
Import ListNotations.

Definition types: list type :=
  [ expr
  ; context
  ].

Definition connectives: list connective :=
  [ impp
  ; andp
  ; orp
  ; falsep
  ; truep
  ; iffp
  ; negp
  ; coq_prop
  ; sepcon
  ; wand
  ; emp
  ; multi_imp
  ; iter_andp
  ; iter_sepcon
  ; empty_context
  ].

Definition judgements: list judgement :=
  [ provable
  ; derivable
  ; derivable1
  ; logic_equiv
  ; corable
  ].

Definition how_types: list how_type :=
  [ FROM_ensemble_expr_TO_context
  ].

Definition how_connectives: list how_connective :=
  [ FROM_andp_impp_TO_iffp
  ; FROM_falsep_impp_TO_negp
  ; FROM_falsep_impp_TO_truep
  ; FROM_impp_TO_multi_imp
  ; FROM_andp_TO_iter_andp
  ; FROM_sepcon_TO_iter_sepcon
  ; FROM_empty_set_TO_empty_context
  ].

Definition how_judgements: list how_judgement :=
  [ FROM_provable_TO_derivable
  ; FROM_derivable_TO_provable
  ].

Definition type_classes :=
  [ Language
  ].

Definition connective_classes :=
  [ MinimumLanguage
  ; AndLanguage
  ; OrLanguage
  ; FalseLanguage
  ; TrueLanguage
  ; IffLanguage
  ; NegLanguage
  ; CoqPropLanguage
  ; SepconLanguage
  ; WandLanguage
  ; EmpLanguage
  ; IterAndLanguage
  ; IterSepconLanguage
  ].

Definition judgement_classes :=
  [ Provable
  ; Derivable
  ; Derivable1
  ; LogicEquiv
  ; Corable
  ].

Definition rule_classes :=
  [ provability_OF_impp
  ; provability_OF_andp
  ; provability_OF_orp
  ; provability_OF_falsep
  ; provability_OF_truep
  ; provability_OF_iffp
  ; provability_OF_negp
  ; provability_OF_iter_andp
  ; provability_OF_de_morgan
  ; provability_OF_godel_dummett
  ; provability_OF_classical_logic
  ; provability_OF_coq_prop
  ; provability_OF_sepcon_rule
  ; provability_OF_wand_rule
  ; provability_OF_emp_rule
  ; provability_OF_iter_sepcon
  ; provability_OF_sepcon_orp_rule
  ; provability_OF_sepcon_falsep_rule
  ; provability_OF_sepcon_coq_prop
  ; provability_OF_sepcon_rule_AS_weak
  ; provability_OF_sepcon_rule_AS_weak_iffp
  ; provability_OF_sepcon_rule_AS_mono
  ; provability_OF_emp_rule_AS_iffp
  ; provability_OF_garbage_collected_sl
  ; derivitive_OF_basic_setting
  ; derivitive_OF_finite_derivation
  ; derivitive_OF_impp
  ; derivitive_OF_andp
  ; derivitive_OF_orp
  ; derivitive_OF_falsep
  ; derivitive_OF_truep
  ; derivitive_OF_iffp
  ; derivitive_OF_negp
(*  ; derivitive_OF_de_morgan *)
(*  ; derivitive_OF_godel_dummett *)
  ; derivitive_OF_classical_logic
  ; corability_OF_basic_setting
  ; corability_OF_coq_prop
  ; GEN_iter_andp_FROM_fold_left_andp
  ; GEN_iter_andp_FROM_fold_right_andp
  ; GEN_iter_sepcon_FROM_fold_left_sepcon
  ; GEN_iter_sepcon_FROM_fold_right_sepcon
  ; GEN_derivable_FROM_provable
  ; GEN_provable_FROM_derivable
  ].

Definition classes :=
  ltac:(let l := eval compute in
         (map TC type_classes ++
          map CC connective_classes ++
          map JC judgement_classes ++
          map RC rule_classes) in
        exact l).

Definition refl_classes :=
  [ RC GEN_iffp_FROM_andp_impp
  ; RC GEN_truep_FROM_falsep_impp
  ; RC GEN_negpp_FROM_falsep_impp
  ; RC GEN_iter_andp_FROM_fold_left_andp
  ; RC GEN_iter_sepcon_FROM_fold_left_sepcon
  ; RC GEN_derivable_FROM_provable
  ; RC GEN_provable_FROM_derivable
  ].

End D.

Definition Build_Language := Build_Language.
Definition Build_MinimumLanguage := Build_MinimumLanguage.
Definition Build_AndLanguage := Build_AndLanguage.
Definition Build_OrLanguage := Build_OrLanguage.
Definition Build_FalseLanguage := Build_FalseLanguage.
Definition Build_TrueLanguage := Build_TrueLanguage.
Definition Build_IffLanguage := Build_IffLanguage.
Definition Build_NegLanguage := Build_NegLanguage.
Definition Build_IterAndLanguage := Build_IterAndLanguage.
Definition Build_CoqPropLanguage := Build_CoqPropLanguage.
Definition Build_SepconLanguage := Build_SepconLanguage.
Definition Build_WandLanguage := Build_WandLanguage.
Definition Build_EmpLanguage := Build_EmpLanguage.
Definition Build_IterSepconLanguage := Build_IterSepconLanguage.
Definition Build_Provable := Build_Provable.
Definition Build_Derivable := Build_Derivable.
Definition Build_Derivable1 := Build_Derivable1.
Definition Build_LogicEquiv := Build_LogicEquiv.
Definition Build_Corable := Build_Corable.
Definition Build_IterAndDefinition_left := Build_IterAndDefinition_left.
Definition Build_IterAndDefinition_right := Build_IterAndDefinition_right.
Definition Build_IterSepconDefinition_left := Build_IterSepconDefinition_left.
Definition Build_IterSepconDefinition_right := Build_IterSepconDefinition_right.
Definition Build_NormalAxiomatization := Build_NormalAxiomatization.
Definition Build_NormalSequentCalculus := Build_NormalSequentCalculus.
Definition Build_MinimumAxiomatization := Build_MinimumAxiomatization.
Definition Build_AndAxiomatization := Build_AndAxiomatization.
Definition Build_OrAxiomatization := Build_OrAxiomatization.
Definition Build_FalseAxiomatization := Build_FalseAxiomatization.
Definition Build_TrueAxiomatization := Build_TrueAxiomatization.
Definition Build_IffAxiomatization := Build_IffAxiomatization.
Definition Build_IntuitionisticNegAxiomatization := Build_IntuitionisticNegAxiomatization.
Definition Build_IterAndAxiomatization_left := Build_IterAndAxiomatization_left.
Definition Build_DeMorganAxiomatization := Build_DeMorganAxiomatization.
Definition Build_ClassicalAxiomatization := Build_ClassicalAxiomatization.
Definition Build_CoqPropAxiomatization := Build_CoqPropAxiomatization.
Definition Build_SepconAxiomatization := Build_SepconAxiomatization.
Definition Build_WandAxiomatization := Build_WandAxiomatization.
Definition Build_EmpAxiomatization := Build_EmpAxiomatization.
Definition Build_IterSepconAxiomatization_left := Build_IterSepconAxiomatization_left.
Definition Build_SepconOrAxiomatization := Build_SepconOrAxiomatization.
Definition Build_SepconFalseAxiomatization := Build_SepconFalseAxiomatization.
Definition Build_SepconCoqPropAxiomatization := Build_SepconCoqPropAxiomatization.
Definition Build_SepconAxiomatization_weak := Build_SepconAxiomatization_weak.
Definition Build_SepconAxiomatization_weak_iffp := Build_SepconAxiomatization_weak_iffp.
Definition Build_SepconMonoAxiomatization := Build_SepconMonoAxiomatization.
Definition Build_EmpAxiomatization_iffp := Build_EmpAxiomatization_iffp.
Definition Build_GarbageCollectSeparationLogic := Build_GarbageCollectSeparationLogic.
Definition Build_BasicSequentCalculus := Build_BasicSequentCalculus.
Definition Build_FiniteWitnessedSequentCalculus := Build_FiniteWitnessedSequentCalculus.
Definition Build_MinimumSequentCalculus := Build_MinimumSequentCalculus.
Definition Build_AndSequentCalculus := Build_AndSequentCalculus.
Definition Build_OrSequentCalculus := Build_OrSequentCalculus.
Definition Build_FalseSequentCalculus := Build_FalseSequentCalculus.
Definition Build_TrueSequentCalculus := Build_TrueSequentCalculus.
Definition Build_IffSequentCalculus := Build_IffSequentCalculus.
Definition Build_IntuitionisticNegSequentCalculus := Build_IntuitionisticNegSequentCalculus.
Definition Build_ClassicalSequentCalculus := Build_ClassicalSequentCalculus.
Definition Build_Corable_withAxiomatization := Build_Corable_withAxiomatization.
Definition Build_CoqPropCorable := Build_CoqPropCorable.

Module S.
Import NameListNotations.
Section S.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {truepL: TrueLanguage L}
        {iffpL: IffLanguage L}
        {negpL: NegLanguage L}
        {iter_andp_L : IterAndLanguage L}
        {coq_prop_L : CoqPropLanguage L}
        {sepconL : SepconLanguage L}
        {wandL : WandLanguage L}
        {empL: EmpLanguage L}
        {iter_sepcon_L : IterSepconLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {Cor: Corable L}
        {iffpDef: IffDefinition_And_Imp L}
        {truepDef: TrueDefinition_False_Imp L}
        {negpDef: NegDefinition_False_Imp L}
        {iter_andp_DL: IterAndDefinition_left L}
        {iter_andp_DR: IterAndDefinition_right L}
        {iter_sepcon_DL: IterSepconDefinition_left L}
        {iter_sepcon_DR: IterSepconDefinition_right L}
        {AX: NormalAxiomatization L GammaP GammaD}
        {SC : NormalSequentCalculus L GammaP GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iter_andp_AXL: IterAndAxiomatization_left L GammaP}
        {cpAX: ClassicalAxiomatization L GammaP}
        {dmpAX: DeMorganAxiomatization L GammaP}
        {gdpAX: GodelDummettAxiomatization L GammaP}
        {coq_prop_AX: CoqPropAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}
        {wandAX: WandAxiomatization L GammaP}
        {empAX: EmpAxiomatization L GammaP}
        {iter_sepcon_AXL: IterSepconAxiomatization_left L GammaP}
        {sepcon_orp_AX: SepconOrAxiomatization L GammaP}
        {sepcon_falsep_AX: SepconFalseAxiomatization L GammaP}
        {sepcon_coq_prop_AX: SepconCoqPropAxiomatization L GammaP}
        {sepconAX_weak: SepconAxiomatization_weak L GammaP}
        {sepconAX_weak_iffp: SepconAxiomatization_weak_iffp L GammaP}
        {sepcon_mono_AX: SepconMonoAxiomatization L GammaP}
        {empAX_iffp: EmpAxiomatization_iffp L GammaP}
        {extsAX: ExtSeparationLogic L GammaP}
        {nsesAX: NonsplitEmpSeparationLogic L GammaP}
        {desAX: DupEmpSeparationLogic L GammaP}
        {mfsAX: MallocFreeSeparationLogic L GammaP}
        {gcsAX: GarbageCollectSeparationLogic L GammaP}
        {bSC : BasicSequentCalculus L GammaD}
        {fwSC : FiniteWitnessedSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC : AndSequentCalculus L GammaD}
        {orpSC : OrSequentCalculus L GammaD}
        {falsepSC : FalseSequentCalculus L GammaD}
        {truepSC : TrueSequentCalculus L GammaD}
        {iffpSC : IffSequentCalculus L GammaD}
        {inegpSC : IntuitionisticNegSequentCalculus L GammaD}
        {cpSC : ClassicalSequentCalculus L GammaD}
        {CorAX: Corable_withAxiomatization L GammaP Cor}
        {coq_prop_Cor: CoqPropCorable L Cor}
        .

Definition types: list Name :=
  [ expr
  ; context
  ].

Definition connectives: list Name :=
  [ impp
  ; andp
  ; orp
  ; falsep
  ; truep
  ; iffp
  ; negp
  ; coq_prop
  ; sepcon
  ; wand
  ; emp
  ; multi_imp
  ; iter_andp
  ; iter_sepcon
  ; empty_context
  ].

Definition judgements: list Name :=
  [ provable
  ; derivable
  ; derivable1
  ; logic_equiv
  ; corable
  ].

Definition how_types: list Name :=
  [ (context, expr -> Prop)
  ].

Definition how_connectives: list Name :=
  [ (iffp, fun x y => andp (impp x y) (impp y x))
  ; (negp, fun x => impp x falsep)
  ; (truep, impp falsep falsep)
  ; (multi_imp, fun xs y => fold_right impp y xs)
  ; (iter_andp, fun xs => fold_left andp xs truep)
  ; (iter_sepcon, fun xs => fold_left sepcon xs emp)
  ; (empty_context, Empty_set expr)
  ].

Definition how_judgements: list Name :=
  [ (derivable, fun Phi x => exists xs, Forall Phi xs /\ provable (multi_imp xs x))
  ; (provable, fun x => derivable empty_context x)
  ].

Definition type_instances_build :=
  [ (L, Build_Language expr)
  ].

Definition connective_instances_build :=
  [ (minL, Build_MinimumLanguage L impp)
  ; (andpL, Build_AndLanguage L andp)
  ; (orpL, Build_OrLanguage L orp)
  ; (falsepL, Build_FalseLanguage L falsep)
  ; (truepL, Build_TrueLanguage L truep)
  ; (iffpL, Build_IffLanguage L iffp)
  ; (negpL, Build_NegLanguage L negp)
  ; (iter_andp_L, Build_IterAndLanguage L iter_andp)
  ; (coq_prop_L, Build_CoqPropLanguage L coq_prop)
  ; (sepconL, Build_SepconLanguage L sepcon)
  ; (wandL, Build_WandLanguage L wand)
  ; (empL, Build_EmpLanguage L emp)
  ; (iter_sepcon_L, Build_IterSepconLanguage L iter_sepcon)
  ].

Definition judgement_instances_build :=
  [ (GammaP, Build_Provable _ provable)
  ; (GammaD, Build_Derivable _ derivable)
  ; (GammaD1, Build_Derivable1 _ derivable1)
  ; (GammaE, Build_LogicEquiv _ logic_equiv)
  ; (Cor, Build_Corable _ corable)
  ].

Definition rule_instances_build :=
  [ (minAX, Build_MinimumAxiomatization L minL GammaP modus_ponens axiom1 axiom2)
  ; (andpAX, Build_AndAxiomatization L minL andpL GammaP andp_intros andp_elim1 andp_elim2)
  ; (orpAX, Build_OrAxiomatization L minL orpL GammaP orp_intros1 orp_intros2 orp_elim)
  ; (falsepAX, Build_FalseAxiomatization L minL falsepL GammaP falsep_elim)
  ; (truepAX, Build_TrueAxiomatization L minL truepL GammaP truep_intros)
  ; (iffpAX, Build_IffAxiomatization L minL iffpL GammaP iffp_intros iffp_elim1 iffp_elim2)
  ; (inegpAX, Build_IntuitionisticNegAxiomatization L minL falsepL negpL GammaP negp_unfold negp_fold)
  ; (iter_andp_AXL, Build_IterAndAxiomatization_left L truepL andpL iffpL iter_andp_L GammaP iter_andp_spec_left)
  ; (dmpAX, Build_DeMorganAxiomatization L minL orpL falsepL negpL GammaP weak_excluded_middle)
  ; (gdpAX, Build_GodelDummettAxiomatization L minL orpL GammaP impp_choice)
  ; (cpAX, Build_ClassicalAxiomatization L minL GammaP peirce_law)
  ; (coq_prop_AX, Build_CoqPropAxiomatization L minL coq_prop_L GammaP coq_prop_intros coq_prop_elim coq_prop_impp)
  ; (sepconAX, Build_SepconAxiomatization L minL sepconL GammaP sepcon_comm_impp sepcon_assoc1 sepcon_mono)
  ; (wandAX, Build_WandAxiomatization L minL sepconL wandL GammaP wand_sepcon_adjoint)
  ; (empAX, Build_EmpAxiomatization L minL sepconL empL GammaP sepcon_emp1 sepcon_emp2)
  ; (iter_sepcon_AXL, Build_IterSepconAxiomatization_left L minL sepconL empL iter_sepcon_L GammaP iter_sepcon_spec_left1 iter_sepcon_spec_left2)
  ; (sepcon_orp_AX, Build_SepconOrAxiomatization L minL orpL sepconL GammaP orp_sepcon_left)
  ; (sepcon_falsep_AX, Build_SepconFalseAxiomatization L minL falsepL sepconL GammaP falsep_sepcon_left)
  ; (sepcon_coq_prop_AX, Build_SepconCoqPropAxiomatization L minL andpL iffpL coq_prop_L sepconL GammaP prop_andp_sepcon1)
  ; (sepconAX_weak, Build_SepconAxiomatization_weak L minL sepconL GammaP sepcon_comm_impp sepcon_assoc1)
  ; (sepconAX_weak_iffp, Build_SepconAxiomatization_weak_iffp L iffpL sepconL GammaP sepcon_comm sepcon_assoc)
  ; (sepcon_mono_AX, Build_SepconMonoAxiomatization L minL sepconL GammaP sepcon_mono)
  ; (empAX_iffp, Build_EmpAxiomatization_iffp L iffpL sepconL empL GammaP sepcon_emp)
  ; (gcsAX, Build_GarbageCollectSeparationLogic L minL sepconL GammaP sepcon_elim1)
  ; (bSC, Build_BasicSequentCalculus L GammaD deduction_weaken derivable_assum deduction_subst)
  ; (fwSC, Build_FiniteWitnessedSequentCalculus L GammaD derivable_finite_witnessed)
  ; (minSC, Build_MinimumSequentCalculus L minL GammaD deduction_modus_ponens deduction_impp_intros) 
  ; (andpSC, Build_AndSequentCalculus L andpL GammaD deduction_andp_intros deduction_andp_elim1 deduction_andp_elim2)
  ; (orpSC, Build_OrSequentCalculus L orpL GammaD deduction_orp_intros1 deduction_orp_intros2 deduction_orp_elim)
  ; (falsepSC, Build_FalseSequentCalculus L falsepL GammaD deduction_falsep_elim)
  ; (truepSC, Build_TrueSequentCalculus L truepL GammaD deduction_truep_intros)
  ; (iffpSC, Build_IffSequentCalculus L iffpL GammaD deduction_iffp_intros deduction_iffp_elim1 deduction_iffp_elim2)
  ; (inegpSC, Build_IntuitionisticNegSequentCalculus L falsepL negpL GammaD deduction_negp_unfold deduction_negp_fold)
  ; (cpSC, Build_ClassicalSequentCalculus L orpL negpL GammaD derivable_excluded_middle)
  ; (CorAX, Build_Corable_withAxiomatization L andpL iffpL sepconL GammaP Cor corable_preserved' corable_andp_sepcon1)
  ; (coq_prop_Cor, Build_CoqPropCorable L coq_prop_L Cor corable_coq_prop)
  ; (iter_andp_DL, Build_IterAndDefinition_left L andpL truepL iter_andp_L iter_andp_def_l)
  ; (iter_andp_DR, Build_IterAndDefinition_right L andpL truepL iter_andp_L iter_andp_def_r)
  ; (iter_sepcon_DL, Build_IterSepconDefinition_left L sepconL empL iter_sepcon_L iter_sepcon_def_l)
  ; (iter_sepcon_DR, Build_IterSepconDefinition_right L sepconL empL iter_sepcon_L iter_sepcon_def_r)
  ; (AX, Build_NormalAxiomatization L minL GammaP GammaD derivable_provable)
  ; (SC, Build_NormalSequentCalculus L GammaP GammaD provable_derivable)
  ].

Definition instances_build :=
  ltac:(let instances_build :=
          eval cbv [type_instances_build
                    connective_instances_build
                    judgement_instances_build
                    rule_instances_build
                    app] in
        (type_instances_build ++
         connective_instances_build ++
         judgement_instances_build ++
         rule_instances_build) in
        exact instances_build).

Definition refl_instances :=
  [ (iffpDef, AndImp2Iff_Normal)
  ; (truepDef, FalseImp2True_Normal)
  ; (negpDef, FalseImp2Neg_Normal)
  ; (iter_andp_DL, FoldLeftAnd2IterAnd_Normal)
  ; (iter_sepcon_DL, FoldLeftSepcon2IterSepcon_Normal)
  ; (AX, Provable2Derivable_Normal)
  ; (SC, Derivable2Provable_Normal)
  ].

Definition instance_transitions :=
  [ (iter_andp_AXL, IterAndFromDefToAX_L2L)
  ; (iter_sepcon_AXL, IterSepconFromDefToAX_L2L)
  ; (SC, Axiomatization2SequentCalculus_SC)
  ; (bSC, Axiomatization2SequentCalculus_bSC)
  ; (fwSC, Axiomatization2SequentCalculus_fwSC)
  ; (minSC, Axiomatization2SequentCalculus_minSC)
  ; (andpSC, Axiomatization2SequentCalculus_andpSC)
  ; (orpSC, Axiomatization2SequentCalculus_orpSC)
  ; (falsepSC, Axiomatization2SequentCalculus_falsepSC)
  ; (truepSC, Axiomatization2SequentCalculus_truepSC)
  ; (iffpSC, Axiomatization2SequentCalculus_iffpSC)
  ; (inegpSC, Axiomatization2SequentCalculus_inegpSC)
  ; (AX, SequentCalculus2Axiomatization_AX)
  ; (minAX, SequentCalculus2Axiomatization_minAX)
  ; (andpAX, SequentCalculus2Axiomatization_andpAX)
  ; (orpAX, SequentCalculus2Axiomatization_orpAX)
  ; (falsepAX, SequentCalculus2Axiomatization_falsepAX)
  ; (truepAX, SequentCalculus2Axiomatization_truepAX)
  ; (iffpAX, SequentCalculus2Axiomatization_iffpAX)
  ; (inegpAX, SequentCalculus2Axiomatization_inegpAX)
  ; (sepconAX, SepconAxiomatizationWeak2SepconAxiomatization)
  ; (sepconAX_weak, SepconAxiomatizationWeakIff2SepconAxiomatizationWeak)
  ; (sepcon_mono_AX, Adj2SepconMono)
  ; (sepcon_orp_AX, Adj2SepconOr)
  ; (sepcon_falsep_AX, Adj2SepconFalse)
  ; (empAX, EmpAxiomatizationIff2EmpAxiomatization)
  ; (sepcon_coq_prop_AX, CoqPropCorable2SepconCoqPropAX)
  ; (sepcon_coq_prop_AX, Adj2SepconCoqProp)
  ].

Definition type_instances: list Name :=
  map_fst type_instances_build.

Definition connective_instances :=
  map_fst connective_instances_build.

Definition judgement_instances :=
  map_fst judgement_instances_build.

Definition rule_instances :=
  map_fst rule_instances_build.

Definition instances :=
  ltac:(let instances :=
          eval cbv [type_instances
                    connective_instances
                    judgement_instances
                    rule_instances
                    app] in
        (type_instances ++
         connective_instances ++
         judgement_instances ++
         rule_instances) in
        exact instances).

Definition type_dependency_via_ins :=
  noninstance_arg_lists
    (type_instances_build, map_snd type_instances_build).

Definition connective_dependency_via_ins :=
  noninstance_arg_lists
    (connective_instances_build, map_snd connective_instances_build).

Definition judgement_dependency_via_ins :=
  noninstance_arg_lists
    (judgement_instances_build, map_snd judgement_instances_build).

Definition primary_rule_dependency_via_ins :=
  noninstance_arg_lists
    (rule_instances_build, map_snd rule_instances_build).

Definition instance_dependency_via_transition :=
  instance_arg_lists
    (instance_transitions, map_snd instance_transitions).

Definition D_type_dependency_via_ins :=
  (map_with_hint (type_instances_build, D.type_classes)
                 (map_fst type_dependency_via_ins),
   map_with_hint (types, D.types)
                 (map_snd type_dependency_via_ins)).

Definition D_connective_dependency_via_ins :=
  (map_with_hint (connective_instances_build, D.connective_classes)
                 (map_fst connective_dependency_via_ins),
   map_with_hint (connectives, D.connectives)
                 (map_snd connective_dependency_via_ins)).

Definition D_judgement_dependency_via_ins :=
  (map_with_hint (judgement_instances_build, D.judgement_classes)
                 (map_fst judgement_dependency_via_ins),
   map_with_hint (judgements, D.judgements)
                 (map_snd judgement_dependency_via_ins)).

Definition D_instance_transitions: list ConfigLang.how_instance :=
  nat_ident_list instance_transitions.

Definition D_instance_transition_results :=
  map_with_hint (instances, D.classes) (map_fst instance_transitions).

Definition D_instance_dependency_via_transition :=
  (map_with_hint (instance_transitions, D_instance_transitions)
                 (map_fst instance_dependency_via_transition),
   map_with_hint (instances, D.classes)
                 (map_snd instance_dependency_via_transition)).

Definition primary_rules_with_dup: list Name :=
  map_snd primary_rule_dependency_via_ins.

Definition derived_rules :=
  [ provable_impp_refl
  ; provable_impp_arg_switch
  ; provable_impp_trans
  ; provable_multi_imp_shrink
  ; provable_multi_imp_arg_switch1
  ; provable_multi_imp_arg_switch2
  ; provable_add_multi_imp_left_head
  ; provable_add_multi_imp_left_tail
  ; provable_multi_imp_modus_ponens
  ; provable_multi_imp_weaken
  ; provable_impp_refl_instance
  ; deduction_impp_elim
  ; deduction_theorem
  ; deduction_theorem_multi_imp
  ; derivable_impp_refl
  ; deduction_left_impp_intros
  ; derivable_modus_ponens
  ; deduction_impp_trans
  ; deduction_impp_arg_switch
  ; provable_proper_impp
  ; impp_proper_impp
  ; derivable_proper_impp

  ; demorgan_orp_negp
  ; demorgan_negp_orp
  ; provable_truep
  ; andp_comm
  ; andp_assoc
  ; orp_comm
  ; orp_assoc
  ; andp_dup
  ; orp_dup
  ; impp_curry
  ; impp_uncurry
  ; double_negp_elim
  ; double_negp
  ; contrapositiveNN
  ; contrapositiveNP
  ; impp2orp
  ; solve_weak_classic
  ; solve_classic
  ; andp_proper_impp
  ; orp_proper_impp
  ; negp_proper_impp
  ; provable_iffp_equiv
  ; provable_proper_iffp
  ; impp_proper_iffp
  ; andp_proper_iffp
  ; orp_proper_iffp
  ; iffp_proper_iffp
  ; negp_proper_iffp
  ; derivable_proper_iffp
  ; iter_andp_spec_right
  ; iter_andp_unfold_left_assoc
  ; iter_andp_unfold_right_assoc

  ; coq_prop_truep
  ; coq_prop_andp
  ; andp_coq_prop
  ; coq_prop_andp_impp
  ; andp_coq_prop_impp
  ; impp_coq_prop
  ; coq_prop_and
  ; coq_prop_or
  ; coq_prop_impl

  ; sepcon_orp_distr_l
  ; falsep_sepcon
  ; provable_wand_sepcon_modus_ponens1
  ; wand_andp
  ; sepcon_orp_distr_r
  ; sepcon_falsep
  ; provable_wand_sepcon_modus_ponens2
  ; wand_mono
  ; orp_wand
  ; prop_sepcon_andp2
  ; prop_sepcon_andp1
  ; prop_andp_sepcon2
  ; sepcon_iter_sepcon
  ; iter_sepcon_unfold_right_assoc
  ; iter_sepcon_unfold_left_assoc
  ; corable_sepcon_andp2
  ; corable_sepcon_andp1
  ; corable_andp_sepcon2
  ].

Ltac filter_instance_rec l res :=
  match l with
  | nil => res
  | cons (BuildName ?x) ?l0 =>
      let tac1 TT := filter_instance_rec l0 (cons (BuildName x) res) in
      let tac2 TT := filter_instance_rec l0 res in
      if_instance x tac1 tac2
  end.

Notation "'filter_instance' l" :=
  (ltac:(let l' := eval hnf in l in
         let res := filter_instance_rec l' (@nil Name) in
         exact res))
  (only parsing, at level 99).

Definition derived_rules_as_instance :=
  filter_instance derived_rules.

Definition D_primary_rules_with_dup: list nat :=
  nodup_nat_ident_list primary_rules_with_dup.

Definition D_primary_rules: list nat :=
  ltac:(
    let l := eval compute in 
      (ConfigLang.NatList.shrink D_primary_rules_with_dup)
    in
    exact l).

Definition primary_rules :=
  map_with_hint (D_primary_rules_with_dup, primary_rules_with_dup) D_primary_rules.

Definition D_derived_rules :=
  nat_ident_list derived_rules.

Definition D_derived_rules_as_instance :=
  map_with_hint (derived_rules, D_derived_rules) derived_rules_as_instance.

Definition D_primary_rule_dependency_via_ins :=
  (map_with_hint (rule_instances_build, D.rule_classes)
                 (map_fst primary_rule_dependency_via_ins),
   map_with_hint (primary_rules, D_primary_rules)
                 (map_snd primary_rule_dependency_via_ins)).  

(* TODO: delete it *)
Definition primary_rules_dependency_via_ins :=
  instance_arg_lists
    (primary_rules, primary_rules).

Definition derived_rules_dependency_via_ins :=
  instance_arg_lists
    (derived_rules, derived_rules).

(* TODO: delete it *)
Definition D_primary_rules_dependency_via_ins :=
  (map_with_hint (primary_rules, D_primary_rules)
                 (map_fst primary_rules_dependency_via_ins),
   map_with_hint (instances, D.classes)
                 (map_snd primary_rules_dependency_via_ins)).

Definition D_derived_rules_dependency_via_ins :=
  (map_with_hint (derived_rules, D_derived_rules)
                 (map_fst derived_rules_dependency_via_ins),
   map_with_hint (instances, D.classes)
                 (map_snd derived_rules_dependency_via_ins)).

End S.
End S.


