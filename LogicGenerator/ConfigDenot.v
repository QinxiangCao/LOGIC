Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.Join2Sepcon.
Require Import Logic.SeparationLogic.ShallowEmbedded.Model2CoqPropEmp.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.

Require Logic.LogicGenerator.ConfigLang.
Require Import Logic.LogicGenerator.Utils. 

Module D.
Import ConfigLang.
Import ListNotations.

(* Locate Model.
Locate Language. *)
(* Locate type.
Check model. *)

Definition types: list type :=
  [ model  
  ; expr
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
  ; join
  ; is_unit
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
  ; FROM_model_TO_expr
  ].

Definition how_connectives: list how_connective :=
  [ FROM_andp_impp_TO_iffp
  ; FROM_falsep_impp_TO_negp
  ; FROM_falsep_impp_TO_truep
  ; FROM_impp_negp_TO_orp
  ; FROM_negp_falsep_TO_truep
  ; FROM_negp_truep_TO_falsep
  ; FROM_impp_TO_multi_imp
  ; FROM_andp_TO_iter_andp
  ; FROM_sepcon_TO_iter_sepcon
  ; FROM_empty_set_TO_empty_context
  ; FROM_join_TO_sepcon
  ; FROM_model_TO_impp
  ; FROM_model_TO_andp
  ; FROM_model_TO_orp
  ; FROM_model_TO_coq_prop
  ; FROM_unit_TO_emp
  ; FROM_model_TO_truep
  ].

Definition how_judgements: list how_judgement :=
  [ FROM_provable_TO_derivable
  ; FROM_derivable_TO_provable
  ; FROM_provable_TO_derivable1
  ; FROM_provable_TO_logic_equiv
  ; FROM_derivable1_TO_logic_equiv
  ; FROM_model_TO_provable
  ].

Definition type_classes :=
  [ Language
  ; Model
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
  ; Join
  ; Unit
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
  ; provability_OF_classical_logic_peirce
  ; provability_OF_classical_logic_by_contra
  ; provability_OF_classical_logic_double_negp
  ; provability_OF_classical_logic_canalysis
  ; provability_OF_classical_logic_EM
  ; provability_OF_classical_logic_impp_orp
  ; provability_OF_coq_prop
  ; provability_OF_coq_prop_impp
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
  ; derivitive1_OF_basic_setting
  ; derivitive1_OF_impp_andp_adjoint
  ; derivitive1_OF_andp
  ; derivitive1_OF_orp
  ; derivitive1_OF_falsep
  ; derivitive1_OF_truep
  ; derivitive1_OF_iffp
  ; derivitive1_OF_negp
  ; derivitive1_OF_impp_negp
  ; derivitive1_OF_sepcon
  ; derivitive1_OF_wand
  ; derivitive1_OF_emp
  ; derivitive1_OF_sepcon_orp_rule
  ; derivitive1_OF_sepcon_falsep_rule
  ; equivalence_OF_basic_setting
  ; equivalence_OF_impp
  ; corability_OF_basic_setting
  ; corability_OF_coq_prop
  ; GEN_iffp_FROM_andp_impp
  ; GEN_truep_FROM_falsep_impp
  ; GEN_negp_FROM_falsep_impp
  ; GEN_orp_FROM_impp_negp
  ; GEN_truep_FROM_impp_self
  ; GEN_truep_FROM_negp_falsep
  ; GEN_falsep_FROM_negp_truep
  ; GEN_iter_andp_FROM_fold_left_andp
  ; GEN_iter_andp_FROM_fold_right_andp
  ; GEN_iter_sepcon_FROM_fold_left_sepcon
  ; GEN_iter_sepcon_FROM_fold_right_sepcon
  ; GEN_derivable_FROM_provable
  ; GEN_provable_FROM_derivable
  ; GEN_derivable1_FROM_provable
  ; GEN_logic_equiv_FROM_provable
  ; GEN_logic_equiv_FROM_derivable1
  ; GEN_sepcon_FROM_join
  ; join_is_SA
  ; GEN_emp_FROM_unit
  (* ; provability_OF_sepcon_rule *)
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
  ; RC GEN_negp_FROM_falsep_impp
  ; RC GEN_orp_FROM_impp_negp
  ; RC GEN_truep_FROM_negp_falsep
  ; RC GEN_falsep_FROM_negp_truep
  ; RC GEN_iter_andp_FROM_fold_left_andp
  ; RC GEN_iter_sepcon_FROM_fold_left_sepcon
  ; RC GEN_derivable_FROM_provable
  ; RC GEN_provable_FROM_derivable
  ; RC GEN_derivable1_FROM_provable
  ; RC GEN_logic_equiv_FROM_provable
  ; RC GEN_logic_equiv_FROM_derivable1
  ; RC GEN_sepcon_FROM_join
  ; RC GEN_impp_FROM_model
  ; RC GEN_provable_FROM_model
  ; RC GEN_andp_FROM_model
  ; RC GEN_orp_FROM_model
  ; RC GEN_coq_prop_FROM_model
  ; RC GEN_emp_FROM_unit
  ; RC GEN_truep_FROM_model
  ].

End D.

(* Class JoinLanguage (L: Language): Type := {
  join: prog_state -> prog_state -> prog_state -> Prop
}. *)

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
Definition Build_IffDefinition_And_Imp := Build_IffDefinition_And_Imp.
Definition Build_TrueDefinition_False_Imp := Build_TrueDefinition_False_Imp.
Definition Build_NegDefinition_False_Imp := Build_NegDefinition_False_Imp.
Definition Build_OrDefinition_Imp_Neg := Build_OrDefinition_Imp_Neg.
Definition Build_TrueDefinition_Imp_Self := Build_TrueDefinition_Imp_Self.
Definition Build_TrueDefinition_Neg_False := Build_TrueDefinition_Neg_False.
Definition Build_FalseDefinition_Neg_True := Build_FalseDefinition_Neg_True.
Definition Build_IterAndDefinition_left := Build_IterAndDefinition_left.
Definition Build_IterAndDefinition_right := Build_IterAndDefinition_right.
Definition Build_IterSepconDefinition_left := Build_IterSepconDefinition_left.
Definition Build_IterSepconDefinition_right := Build_IterSepconDefinition_right.
Definition Build_DerivableProvable := Build_DerivableProvable.
Definition Build_ProvableDerivable := Build_ProvableDerivable.
Definition Build_Derivable1Provable := Build_Derivable1Provable.
Definition Build_EquivProvable := Build_EquivProvable.
Definition Build_EquivDerivable1 := Build_EquivDerivable1.
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
Definition Build_PeirceLaw := Build_PeirceLaw.
Definition Build_ByContradiction := Build_ByContradiction.
Definition Build_DoubleNegElimination := Build_DoubleNegElimination.
Definition Build_ClassicAnalysis := Build_ClassicAnalysis.
Definition Build_ExcludedMiddle := Build_ExcludedMiddle.
Definition Build_ImplyToOr := Build_ImplyToOr.
Definition Build_CoqPropAxiomatization := Build_CoqPropAxiomatization.
Definition Build_CoqPropImpAxiomatization := Build_CoqPropImpAxiomatization.
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
Definition Build_BasicDeduction := Build_BasicDeduction.
Definition Build_AndDeduction := Build_AndDeduction.
Definition Build_ImpAndAdjointDeduction := Build_ImpAndAdjointDeduction.
Definition Build_OrDeduction := Build_OrDeduction.
Definition Build_FalseDeduction := Build_FalseDeduction.
Definition Build_TrueDeduction := Build_TrueDeduction.
Definition Build_IffDeduction := Build_IffDeduction.
Definition Build_IntuitionisticNegDeduction := Build_IntuitionisticNegDeduction.
Definition Build_ImpNegDeduction := Build_ImpNegDeduction.
Definition Build_SepconDeduction := Build_SepconDeduction.
Definition Build_WandDeduction := Build_WandDeduction.
Definition Build_EmpDeduction := Build_EmpDeduction.
Definition Build_SepconOrDeduction := Build_SepconOrDeduction.
Definition Build_SepconFalseDeduction := Build_SepconFalseDeduction.
Definition Build_BasicLogicEquiv := Build_BasicLogicEquiv.
Definition Build_ImpLogicEquiv := Build_ImpLogicEquiv.
Definition Build_Corable_withAxiomatization := Build_Corable_withAxiomatization.
Definition Build_CoqPropCorable := Build_CoqPropCorable.
Definition Build_Model := Build_Model.
Definition Build_SeparationAlgebra := Build_SeparationAlgebra.

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
        {orpDef_impp_negp: OrDefinition_Imp_Neg L}
        {truepDef_impp_self: TrueDefinition_Imp_Self L}
        {truepDef_negp_falsep: TrueDefinition_Neg_False L}
        {falsepDef_negp_truep: FalseDefinition_Neg_True L}
        {iter_andp_DL: IterAndDefinition_left L}
        {iter_andp_DR: IterAndDefinition_right L}
        {iter_sepcon_DL: IterSepconDefinition_left L}
        {iter_sepcon_DR: IterSepconDefinition_right L}
        {GammaDP: DerivableProvable L GammaP GammaD}
        {GammaPD : ProvableDerivable L GammaP GammaD}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {GammaEP: EquivProvable L GammaP GammaE}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
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
        {plAX: PeirceLaw L GammaP}
        {bcAX: ByContradiction L GammaP}
        {double_negp_elim_AX: DoubleNegElimination L GammaP}
        {caAX: ClassicAnalysis L GammaP}
        {emAX: ExcludedMiddle L GammaP}
        {impp2orpAX: ImplyToOr L GammaP}
        {coq_prop_AX: CoqPropAxiomatization L GammaP}
        {coq_prop_impp_AX: CoqPropImpAxiomatization L GammaP}
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
        {bD : BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD : AndDeduction L GammaD1}
        {orpD : OrDeduction L GammaD1}
        {falsepD : FalseDeduction L GammaD1}
        {truepD : TrueDeduction L GammaD1}
        {iffpD : IffDeduction L GammaD1}
        {inegpD : IntuitionisticNegDeduction L GammaD1}
        {impp_negp_D: ImpNegDeduction L GammaD1}
        {sepconD : SepconDeduction L GammaD1}
        {wandD : WandDeduction L GammaD1}
        {empD : EmpDeduction L GammaD1}
        {sepcon_orp_D : SepconOrDeduction L GammaD1}
        {sepcon_falsep_D : SepconFalseDeduction L GammaD1}
        {bE: BasicLogicEquiv L GammaE}
        {imppE: ImpLogicEquiv L GammaE}
        {CorAX: Corable_withAxiomatization L GammaP Cor}
        {coq_prop_Cor: CoqPropCorable L Cor}
        
        (* new *)
        {M : Model}
        {J : Join model}
        {U : Unit model}
        {sepconDef_join : SepconDefinition_Join Join2Sepcon}
        {J_SA : @SeparationAlgebra model J}
        {minL_modelL : MinimumLanguage Model_L}
        {andpL_modelL : AndLanguage Model_L}
        {orpL_modelL: OrLanguage Model_L}
        {coq_prop_modelL : CoqPropLanguage Model_L}
        {sepconL_modelL: SepconLanguage Model_L}
        {GammaP_modelL : Provable Model_L}
        {truepL_modelL : TrueLanguage Model_L}
        {sepconAX_modelL : SepconAxiomatization Model_L GammaP_modelL}
        {empL_modelL : EmpLanguage Model_L}
        {imppDef_model : ImppDefinition_Model minL_modelL}
        {provableDef_model: ProvableDefinition_Model GammaP_modelL}
        {andpDef_model : AndpDefinition_Model andpL_modelL}
        {orpDef_model : OrpDefinition_Model orpL_modelL}
        {coqpropDef_model : CoqPropDefinition_Model coq_prop_modelL}
        {truepDef_model : TrueDefinition_Model truepL_modelL}
        {empDef_unit : EmpDefinition_Unit Unit2Emp}
        .

Definition types: list Name :=
  [ model
  ; expr
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
  ; join
  ; is_unit
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
  ; (expr, model -> Prop)
  ].

Definition how_connectives: list Name :=
  [ (iffp, fun x y => andp (impp x y) (impp y x))
  ; (negp, fun x => impp x falsep)
  ; (truep, impp falsep falsep)
  ; (orp, fun x y => impp (negp x) y)
  ; (truep, negp falsep)
  ; (falsep, negp truep)
  ; (multi_imp, fun xs y => fold_right impp y xs)
  ; (iter_andp, fun xs => fold_left andp xs truep)
  ; (iter_sepcon, fun xs => fold_left sepcon xs emp)
  ; (empty_context, Empty_set expr)
  ; (sepcon, fun x y => fun m => exists m1 m2, join m1 m2 m /\ x m1 /\ y m2)
  ; (impp, fun (x y : model -> Prop) (m : model) => (x m -> y m))
  ; (andp, fun (x y : model -> Prop) (m : model) => (x m /\ y m))
  ; (orp, fun (x y : model -> Prop) (m : model) => (x m \/ y m))
  ; (coq_prop, fun (P : Prop) (m : model) => P)
  ; (emp, fun (m : model) => is_unit m)
  ; (truep, fun (m : model) => True)
  ].

Definition how_judgements: list Name :=
  [ (derivable, fun Phi x => exists xs, Forall Phi xs /\ provable (multi_imp xs x))
  ; (provable, fun x => derivable empty_context x)
  ; (derivable1, fun x y => provable (impp x y))
  ; (logic_equiv, fun x y => provable (impp x y) /\ provable (impp y x))
  ; (logic_equiv, fun x y => derivable1 x y /\ derivable1 y x)
  ; (provable, fun x : (model -> Prop) => forall m, x m)
  ].

Definition type_instances_build :=
  [ (L, Build_Language expr)
  ; (M, Build_Model model)
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
  ; (J, join)
  ; (U, is_unit)
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
  ; (truepAX, Build_TrueAxiomatization L truepL GammaP truep_intros)
  ; (iffpAX, Build_IffAxiomatization L minL iffpL GammaP iffp_intros iffp_elim1 iffp_elim2)
  ; (inegpAX, Build_IntuitionisticNegAxiomatization L minL negpL GammaP contrapositivePP contradiction_elim1 double_negp_intros)
  ; (iter_andp_AXL, Build_IterAndAxiomatization_left L truepL andpL iffpL iter_andp_L GammaP iter_andp_spec_left)
  ; (dmpAX, Build_DeMorganAxiomatization L minL orpL falsepL negpL GammaP weak_excluded_middle)
  ; (gdpAX, Build_GodelDummettAxiomatization L minL orpL GammaP impp_choice)
  ; (cpAX, Build_ClassicalAxiomatization L minL GammaP peirce_law)
  ; (plAX, Build_PeirceLaw L minL GammaP peirce_law)
  ; (bcAX, Build_ByContradiction L minL negpL GammaP by_contradiction)
  ; (double_negp_elim_AX, Build_DoubleNegElimination L minL negpL GammaP double_negp_elim)
  ; (caAX, Build_ClassicAnalysis L minL negpL GammaP classic_analysis)
  ; (emAX, Build_ExcludedMiddle L orpL negpL GammaP excluded_middle)
  ; (impp2orpAX, Build_ImplyToOr L minL orpL negpL GammaP impp2orp1)
  ; (coq_prop_AX, Build_CoqPropAxiomatization L minL coq_prop_L GammaP coq_prop_intros coq_prop_elim)
  ; (coq_prop_impp_AX, Build_CoqPropImpAxiomatization L minL coq_prop_L GammaP coq_prop_impp)
  ; (sepconAX, Build_SepconAxiomatization L minL sepconL GammaP sepcon_comm_impp sepcon_assoc1 sepcon_mono)
  ; (wandAX, Build_WandAxiomatization L minL sepconL wandL GammaP wand_sepcon_adjoint)
  ; (empAX, Build_EmpAxiomatization L minL sepconL empL GammaP sepcon_emp1 sepcon_emp2)
  ; (iter_sepcon_AXL, Build_IterSepconAxiomatization_left L minL sepconL empL iter_sepcon_L GammaP iter_sepcon_spec_left1 iter_sepcon_spec_left2)
  ; (sepcon_orp_AX, Build_SepconOrAxiomatization L minL orpL sepconL GammaP orp_sepcon_impp)
  ; (sepcon_falsep_AX, Build_SepconFalseAxiomatization L minL falsepL sepconL GammaP falsep_sepcon_impp)
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
  ; (inegpSC, Build_IntuitionisticNegSequentCalculus L negpL GammaD deduction_contrapositivePP deduction_contradiction_elim deduction_double_negp_intros)
  ; (cpSC, Build_ClassicalSequentCalculus L orpL negpL GammaD derivable_excluded_middle)
  ; (bD, Build_BasicDeduction L GammaD1 derivable1_refl derivable1_trans)
  ; (adjD, Build_ImpAndAdjointDeduction L minL andpL GammaD1 derivable1_impp_andp_adjoint)
  ; (andpD, Build_AndDeduction L andpL GammaD1 derivable1_andp_intros derivable1_andp_elim1 derivable1_andp_elim2)
  ; (orpD, Build_OrDeduction L orpL GammaD1 derivable1_orp_intros1 derivable1_orp_intros2 derivable1_orp_elim)
  ; (falsepD, Build_FalseDeduction L falsepL GammaD1 derivable1_falsep_elim)
  ; (truepD, Build_TrueDeduction L truepL GammaD1 derivable1_truep_intros)
  ; (iffpD, Build_IffDeduction L minL iffpL GammaD1 derivable1_iffp_intros derivable1_iffp_elim1 derivable1_iffp_elim2)
  ; (inegpD, Build_IntuitionisticNegDeduction L negpL GammaD1 derivable1_contrapositivePP' derivable1_contradiction_elim derivable1_double_negp_intros)
  ; (impp_negp_D, Build_ImpNegDeduction L minL negpL GammaD1 derivable1_contrapositivePP derivable1_contradiction_elim')
  ; (sepconD, Build_SepconDeduction L sepconL GammaD1 derivable1_sepcon_comm derivable1_sepcon_assoc1 derivable1_sepcon_mono)
  ; (wandD, Build_WandDeduction L sepconL wandL GammaD1 derivable1_wand_sepcon_adjoint)
  ; (empD, Build_EmpDeduction L sepconL empL GammaD1 sepcon_emp_left sepcon_emp_right)
  ; (sepcon_orp_D, Build_SepconOrDeduction L orpL sepconL GammaD1 orp_sepcon_left)
  ; (sepcon_falsep_D, Build_SepconFalseDeduction L falsepL sepconL GammaD1 falsep_sepcon_left)
  ; (bE, Build_BasicLogicEquiv L GammaE logic_equiv_refl logic_equiv_symm logic_equiv_trans)
  ; (imppE, Build_ImpLogicEquiv L minL GammaE logic_equiv_impp)
  ; (CorAX, Build_Corable_withAxiomatization L andpL iffpL sepconL GammaP Cor corable_preserved' corable_andp_sepcon1)
  ; (coq_prop_Cor, Build_CoqPropCorable L coq_prop_L Cor corable_coq_prop)
  ; (iffpDef, Build_IffDefinition_And_Imp L minL andpL iffpL andp_impp2iffp)
  ; (truepDef, Build_TrueDefinition_False_Imp L minL falsepL truepL falsep_impp2truep)
  ; (negpDef, Build_NegDefinition_False_Imp L minL falsepL negpL falsep_impp2negp)
  ; (orpDef_impp_negp, Build_OrDefinition_Imp_Neg L minL negpL orpL impp_negp2orp)
  ; (truepDef_impp_self, Build_TrueDefinition_Imp_Self L minL truepL impp_self2truep)
  ; (truepDef_negp_falsep, Build_TrueDefinition_Neg_False L falsepL negpL truepL negp_falsep2truep)
  ; (falsepDef_negp_truep, Build_FalseDefinition_Neg_True L truepL negpL falsepL negp_truep2falsep)
  ; (iter_andp_DL, Build_IterAndDefinition_left L andpL truepL iter_andp_L iter_andp_def_l)
  ; (iter_andp_DR, Build_IterAndDefinition_right L andpL truepL iter_andp_L iter_andp_def_r)
  ; (iter_sepcon_DL, Build_IterSepconDefinition_left L sepconL empL iter_sepcon_L iter_sepcon_def_l)
  ; (iter_sepcon_DR, Build_IterSepconDefinition_right L sepconL empL iter_sepcon_L iter_sepcon_def_r)
  ; (GammaDP, Build_DerivableProvable L minL GammaP GammaD derivable_provable)
  ; (GammaPD, Build_ProvableDerivable L GammaP GammaD provable_derivable)
  ; (GammaD1P, Build_Derivable1Provable L minL GammaP GammaD1 derivable1_provable)
  ; (GammaEP, Build_EquivProvable L minL GammaP GammaE logic_equiv_provable)
  ; (GammaED1, Build_EquivDerivable1 L GammaD1 GammaE logic_equiv_derivable1)
  ; (sepconDef_join, SepconDefinition_Join Join2Sepcon )
  ; (J_SA, Build_SeparationAlgebra model J join_comm join_assoc)
  ; (empDef_unit, Unit2Emp_Normal)
  (* ; (sepconAX_modelL, Build_SepconAxiomatization Model_L minL_modelL sepconL_modelL GammaP_modelL sepcon_comm_impp sepcon_assoc1 sepcon_mono) *)
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
  ; (orpDef_impp_negp, ImpNeg2Or_Normal)
  ; (truepDef_negp_falsep, NegFalse2True_Normal)
  ; (falsepDef_negp_truep, NegTrue2False_Normal)
  ; (iter_andp_DL, FoldLeftAnd2IterAnd_Normal)
  ; (iter_sepcon_DL, FoldLeftSepcon2IterSepcon_Normal)
  ; (GammaDP, Provable2Derivable_Normal)
  ; (GammaPD, Derivable2Provable_Normal)
  ; (GammaD1P, Provable2Derivable1_Normal)
  ; (GammaEP, Provable2Equiv_Normal)
  ; (GammaED1, Derivable12Equiv_Normal)
  ; (sepconDef_join, Join2Sepcon_Normal)
  ; (imppDef_model, Model2Impp_Normal) 
  ; (provableDef_model, Model2Provable_Normal)    (*TODO*)
  ; (andpDef_model, Model2Andp_Normal)
  ; (orpDef_model, Model2Orp_Normal)
  ; (coqpropDef_model, Model2CoqProp_Normal)
  ; (empDef_unit, Unit2Emp_Normal)
  ; (truepDef_model, Model2Truep_Normal)
  ].
 
(* Check AndImp2Iff_Normal. (* : IffDefinition_And_Imp L *)
Check Join2Sepcon_Normal. : SepconDefinition_Join *)

Definition instance_transitions :=
  [ (iffpAX, IffFromDefToAX_And_Imp)
  ; (truepAX, TrueFromDefToAX_False_Imp)
  ; (inegpAX, NegFromDefToAX_False_Imp)
  ; (orpAX, OrFromDefToAX_Imp_Neg)
  ; (truepAX, TrueFromDefToAX_Imp_Self)
  ; (truepAX, TrueFromDefToAX_Neg_False)
  ; (falsepAX, FalseFromDefToAX_Neg_True)
  ; (iter_andp_AXL, IterAndFromDefToAX_L2L)
  ; (iter_sepcon_AXL, IterSepconFromDefToAX_L2L)
  ; (GammaPD, Axiomatization2SequentCalculus_GammaPD)
  ; (bSC, Axiomatization2SequentCalculus_bSC)
  ; (fwSC, Axiomatization2SequentCalculus_fwSC)
  ; (minSC, Axiomatization2SequentCalculus_minSC)
  ; (andpSC, Axiomatization2SequentCalculus_andpSC)
  ; (orpSC, Axiomatization2SequentCalculus_orpSC)
  ; (falsepSC, Axiomatization2SequentCalculus_falsepSC)
  ; (truepSC, Axiomatization2SequentCalculus_truepSC)
  ; (iffpSC, Axiomatization2SequentCalculus_iffpSC)
  ; (inegpSC, Axiomatization2SequentCalculus_inegpSC)
  ; (cpSC, Axiomatization2SequentCalculus_cpSC)
  ; (GammaDP, SequentCalculus2Axiomatization_GammaDP)
  ; (minAX, SequentCalculus2Axiomatization_minAX)
  ; (andpAX, SequentCalculus2Axiomatization_andpAX)
  ; (orpAX, SequentCalculus2Axiomatization_orpAX)
  ; (falsepAX, SequentCalculus2Axiomatization_falsepAX)
  ; (truepAX, SequentCalculus2Axiomatization_truepAX)
  ; (iffpAX, SequentCalculus2Axiomatization_iffpAX)
  ; (inegpAX, SequentCalculus2Axiomatization_inegpAX)
  ; (cpAX, Peirce2cpAX)
  ; (bcAX, Peirce2ByContradiction)
  ; (double_negp_elim_AX, ByContradiction2DoubleNegElimination)
  ; (caAX, DoubleNegElimination2ClassicAnalysis)
  ; (plAX, ClassicAnalysis2PeirceLaw)
  ; (impp2orpAX, ClassicAnalysis2ImplyToOr)
  ; (emAX, ImplyToOr2ExcludedMiddle)
  ; (caAX, ExcludedMiddle2ClassicAnalysis)
  ; (inegpAX, ByContradiction2IntuitionisticNegAxiomatization)
  ; (sepconAX, SepconAxiomatizationWeak2SepconAxiomatization)
  ; (sepconAX_weak, SepconAxiomatizationWeakIff2SepconAxiomatizationWeak)
  ; (sepcon_mono_AX, Adj2SepconMono)
  ; (sepcon_orp_AX, Adj2SepconOr)
  ; (sepcon_falsep_AX, Adj2SepconFalse)
  ; (empAX, EmpAxiomatizationIff2EmpAxiomatization)
  ; (sepcon_coq_prop_AX, CoqPropCorable2SepconCoqPropAX)
  ; (sepcon_coq_prop_AX, Adj2SepconCoqProp)
  ; (bD, Axiomatization2Deduction_bD)
  ; (sepconD, Axiomatization2Deduction_sepconD)
  ; (wandD, Axiomatization2Deduction_wandD)
  ; (empD, Axiomatization2Deduction_empD)
  ; (bE, Axiomatization2Equiv_bE)
  ; (GammaED1, Axiomatization2Deduction_GammaED1)
  ; (imppE, Axiomatization2LogicEquiv_imppE)
  (* ; (sepconAX_modelL, SeparationAlgebra2SepconAxiomatization)  *)
  ; (sepconAX, SeparationAlgebra2SepconAxiomatization)
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

(* try write a subst *)

Definition subst_table := 
  [ (Model_L, L)
  ; (minL_modelL, minL)
  ; (sepconL_modelL, sepconL)
  ; (GammaP_modelL, GammaP)
  ; (sepconAX_modelL, sepconAX)
  ].

Ltac subst_name_tac1 x l :=
  match l with 
  | nil => constr:(x) 
  | cons (BuildName (pair x ?b)) ?l' => constr:(b)
  | cons (BuildName (pair _ ?b)) ?l' => subst_name_tac1 x l' 
  end.

Ltac subst_name_tac lx l :=
  match lx with 
  | @nil ?T => constr:(@nil T)
  | cons ?x ?lx' => let aa := subst_name_tac1 x l in 
                    let bb := subst_name_tac lx' l in constr:(cons aa bb)
  end.

Notation " 'subst_name' '(' lx ',' l ')' " :=
  ltac: ( let lx' := eval hnf in lx in 
          let l'  := eval hnf in l in 
          let res := subst_name_tac lx' l' in
          exact res )
          (only parsing, at level 99).

Ltac instance_trans_subst_tac x l :=
  match type of x with 
  | ?t0 ?x0 => let x0' := subst_name_tac1 x0 l in
               let t0' := instance_trans_subst_tac t0 l in  
               constr:(t0' x0')
  | ?t0 => t0
  end.


(* Definition d := cons Model_L nil.
Definition b : @list Language.
  let x := (subst_name_tac1 Model_L (cons (BuildName (pair Model_L L)) nil)) in pose x.
  let x := (subst_name_tac (cons Model_L nil) (cons (BuildName (pair Model_L L)) nil)) in pose x.
  let x := (subst_name_tac1 Model_L [ (Model_L, L)
  ; (minL_modelL, minL)
  ; (sepconL_modelL, sepconL)
  ; (GammaP_modelL, GammaP)
  ; (sepconAX_modelL, sepconAX)
  ]) in pose x.
  let x := (subst_name_tac (cons Model_L nil) [ (Model_L, L)
  ; (minL_modelL, minL)
  ; (sepconL_modelL, sepconL)
  ; (GammaP_modelL, GammaP)
  ; (sepconAX_modelL, sepconAX)
  ]) in pose x.

  let x := eval hnf in d in pose x.
  let x := eval hnf in subst_table in pose x.
  pose (subst_name (d, subst_table)).

  exact nil.
Defined. *)

Ltac dependency_subst_tac1 x l :=
  match x with 
  | (?x1, ?x2, ?x3) =>  let x3' := subst_name_tac1 x3 l in 
                        constr:((x1, x2, x3'))
  end.

Ltac dependency_subst_tac lx l :=
  match lx with 
  | @nil ?T => constr:(@nil T)
  | (BuildName ?x) :: ?lx' => 
      let x' := dependency_subst_tac1 x l in 
      let lx'' := dependency_subst_tac lx' l in 
                  constr:(BuildName x' :: lx'')
  end.

Notation " 'dependency_subst' '(' lx ',' l ')' " :=
  ltac: ( let x := eval hnf in lx in
          let y := eval hnf in l in 
          let z := dependency_subst_tac x y in 
          exact z ) (only parsing, at level 99).

Goal  False  .
  let x := eval hnf in subst_table in
    let y := dependency_subst_tac1 (sepconAX_modelL, SeparationAlgebra2SepconAxiomatization, M) x in
      pose y.
Abort.

(* Ltac build_name_tac1 a :=
  match a with 
  | (?x, ?y) => let x' := constr:(BuildName x) in
                let y' := constr:(BuildName y) in 
                exact (x', y')
  end.

Ltac build_name_tac l :=
  match l with 
  | nil => let res := constr:(@nil Name) in 
           exact res
  | cons ?x ?l' => let x' := build_name_tac1 x in 
                   let l'' := build_name_tac l' in 
                   let res := constr:(cons x' l'') in 
                   exact res
  end.

Definition subst_table_name : @list (Name * Name).

let x := build_name_tac1 (Model_L, L) in pose x.

let x := build_name_tac [ (Model_L, L)
; (minL_modelL, minL)
; (sepconL_modelL, sepconL)
; (GammaP_modelL, GammaP)
; (sepconAX_modelL, sepconAX)
] in exact x. *)

Definition type_dependency_via_ins :=
  noninstance_arg_lists
    (type_instances_build, map_snd type_instances_build).

Definition connective_dependency_via_ins :=
  cons (BuildName (U, is_unit, is_unit))
  (cons (BuildName (J, join, join))
  (noninstance_arg_lists
    (connective_instances_build, map_snd connective_instances_build))).

Definition judgement_dependency_via_ins :=
  noninstance_arg_lists
    (judgement_instances_build, map_snd judgement_instances_build).

(* Definition primary_rule_dependency_via_ins :=
  noninstance_arg_lists
    (rule_instances_build, map_snd rule_instances_build).

Definition instance_dependency_via_transition :=
  instance_arg_lists
    (instance_transitions, map_snd instance_transitions). *)

(* Definition ll1 := (noninstance_arg_lists (rule_instances_build, map_snd rule_instances_build)).

Definition ll2 := dependency_subst (
  (noninstance_arg_lists (rule_instances_build, map_snd rule_instances_build)), subst_table). *)

  (* Ltac dependency_subst_tac1 x l :=
    match x with 
    | (?x1, ?x2, ?x3) =>  let x3' := subst_name_tac1 x3 l in 
                          constr:((x1, x2, x3'))
    end.
  
  Ltac dependency_subst_tac lx l :=
    match lx with 
    | @nil ?T => constr:(@nil T)
    | (BuildName ?x) :: ?lx' => 
        let x' := dependency_subst_tac1 x l in 
        let lx'' := dependency_subst_tac lx' l in 
                    constr:(BuildName x' :: lx'')
    end. *)

(* Ltac list_minus_tac l1 l2 :=
  match l1 with 
  | cons ?a ?l1' => match (eval compute in (In a l2)) with 
    | True => let l' := list_minus_tac l1' l2 in constr:(cons a l')
    | False => let l' := list_minus_tac l1' l2 in l' 
  end 
  | nil => constr:(nil)
  end.

Goal False.
pose list_minus_tac ll1 ll2 as x. *)


(* Fixpoint listminus {A : Type} (l1 l2 : list A) : (list A) :=
  match l1 with 
  | a :: l1' => match (In a l2) with 
    | True => a :: (listminus l1' l2)
    | False => (listminus l1' l2)
  end
  | nil => nil 
  end. *)

(* Compute listminus [1 ; 2]  [1].
Compute In 2 (@cons nat 1 nil).
Compute listminus [1;2] [1]. *)

(* Ltac printbothlist l1 l2 :=
  match l1 with 
  | ?x :: ?l1' => match l2 with 
    | ?y :: ?l2' => idtac x y; printbothlist l1' l2' 
    | nil => idtac x "over"; printbothlist l1' nil 
  end
  | nil => match l2 with 
    | ?y :: ?l2' => idtac "over" y; printbothlist nil l2'
    | nil => idtac 
  end end. *)




Definition primary_rule_dependency_via_ins :=
  dependency_subst (
    (noninstance_arg_lists (rule_instances_build, map_snd rule_instances_build)), subst_table).

Definition instance_dependency_via_transition :=
  dependency_subst (
    (instance_arg_lists (instance_transitions, map_snd instance_transitions)), subst_table).

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

(* Goal True.
  pose (map_fst instance_dependency_via_transition).
  let x := eval hnf in instance_transitions in pose x.
  reflexivity. Qed. *)

Definition D_instance_dependency_via_transition :=
  (map_with_hint (instance_transitions, D_instance_transitions)
                 (map_fst instance_dependency_via_transition),
   map_with_hint (instances, D.classes)
                 (map_snd instance_dependency_via_transition)).

Definition primary_rules_with_dup: list Name :=
  map_snd primary_rule_dependency_via_ins.

Definition derived_rules :=
  [ (* provable * impp *)
    provable_impp_refl
  ; provable_impp_refl'
  ; provable_impp_arg_switch
  ; provable_impp_trans
    (* provable * multi_imp *)
  ; provable_multi_imp_shrink
  ; provable_multi_imp_arg_switch1
  ; provable_multi_imp_arg_switch2
  ; provable_add_multi_imp_left_head
  ; provable_add_multi_imp_left_tail
  ; provable_multi_imp_modus_ponens
  ; provable_multi_imp_weaken
  ; provable_impp_refl_instance
    (* derivable * impp *)
  ; deduction_impp_elim
  ; deduction_theorem
  ; deduction_theorem_multi_imp
  ; derivable_impp_refl
  ; deduction_left_impp_intros
  ; derivable_modus_ponens
  ; deduction_impp_trans
  ; deduction_impp_arg_switch
    (* rewrite classes OF impp *)
  ; provable_proper_impp
  ; impp_proper_impp
  ; derivable_proper_impp

  ; negp_fold_unfold
  ; deduction_negp_fold
  ; deduction_negp_unfold

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
  ; solve_impp_trans
  ; solve_andp_intros
  ; solve_andp_elim1
  ; solve_andp_elim2
  ; negp_fold
  ; negp_unfold
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
  ; cancel_ready
  ; cancel_one_succeed
  ; cancel_one_giveup
  ; cancel_rev
  ; cancel_finish
  ; iter_sepcon_unfold_right_assoc
  ; iter_sepcon_unfold_left_assoc
  ; corable_sepcon_andp2
  ; corable_sepcon_andp1
  ; corable_andp_sepcon2
  ; sepcon_proper_impp
  ; wand_proper_impp
  ; sepcon_proper_iffp
  ; wand_proper_iffp

  ; expr_deep
  ; impp_deep
  ; sepcon_deep
  ; emp_deep
  ; varp_deep
  ; var_pos
  ; sepcon_pos
  ; cancel_mark
  ; cancel_different
  ; cancel_same
  ; restore
  ; cancel_sound

  ; impp_proper_equiv
  ; sepcon_proper_logic_equiv
  ; provable_proper_equiv
  ; logic_equiv_refl_instance
  ; logic_equiv_symm_instance
  ; logic_equiv_trans_instance

  ; sepcon_comm_logic_equiv
  ; sepcon_assoc_logic_equiv
  ; sepcon_emp_logic_equiv

(*
  ; derivable1_sepcon_assoc2
  ; orp_sepcon_right
  ; falsep_sepcon_right
(*  ; sepcon_comm_equiv
  ; sepcon_orp_distr_r_equiv
  ; sepcon_orp_distr_l_equiv
  ; falsep_sepcon_equiv
  ; sepcon_falsep_equiv*)
  ; derivable1_wand_sepcon_modus_ponens1
  ; derivable1_wand_sepcon_modus_ponens2
  ; derivable1_wand_mono
(*  ; wand_andp_equiv
  ; orp_wand_equiv*)
*)
  ].

(* Check @sepcon_assoc_logic_equiv.
Check @sepcon_comm_logic_equiv.

(GammaD1 : Derivable1 L),
       BasicDeduction L GammaD1 ->
       SepconDeduction L GammaD1 ->
       forall GammaE : LogicEquiv L,
       EquivDerivable1 L GammaD1 GammaE *)

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
                 
Ltac pr_subst_tac1 x l :=
  match x with 
  | (?x1, ?x2) => let x2' := subst_name_tac1 x2 l in
                            constr:((x1, x2'))
  end.

Ltac pr_subst_tac lx l :=
  match lx with 
  | @nil ?T => constr:(@nil T)
  | (BuildName ?x) :: ?lx' =>   
      let x' := pr_subst_tac1 x l in 
      let lx'' := pr_subst_tac lx' l in 
            constr:(BuildName x' :: lx'')
  end.

Notation " 'pr_subst' '(' lx ',' l ')' " :=
  ltac:( let x := eval hnf in lx in 
         let y := eval hnf in l in 
         let z := pr_subst_tac x y in 
         exact z) (only parsing, at level 99).

(* TODO: delete it *)
(* Definition primary_rules_dependency_via_ins :=
  instance_arg_lists
    (primary_rules, primary_rules). *)

Definition primary_rules_dependency_via_ins :=
  pr_subst ((instance_arg_lists (primary_rules, primary_rules)), subst_table).

Definition derived_rules_dependency_via_ins :=
  instance_arg_lists
    (derived_rules, derived_rules).

(* Definition dr := [sepcon_comm 
; sepcon_assoc1 
; sepcon_mono].

Compute instance_arg_lists (dr, dr). *)

(* Compute ( primary_rule_dependency_via_ins).

Compute map_with_hint (instances, D.classes)
(map_snd primary_rules_dependency_via_ins). *)

(* TODO: delete it *)
Definition D_primary_rules_dependency_via_ins :=
  (map_with_hint (primary_rules, D_primary_rules)
                 (map_fst primary_rules_dependency_via_ins),
   map_with_hint (instances, D.classes)
                 (map_snd primary_rules_dependency_via_ins)).

(* second entry - not fully computed *)

Definition D_derived_rules_dependency_via_ins :=
  (map_with_hint (derived_rules, D_derived_rules)
                 (map_fst derived_rules_dependency_via_ins),
   map_with_hint (instances, D.classes)
                 (map_snd derived_rules_dependency_via_ins)).

End S.
End S.
