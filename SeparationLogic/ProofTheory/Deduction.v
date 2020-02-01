Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section SLFromDeduction2SLFromAxiomatization1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {sepconL: SepconLanguage L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma SepconDeduction2SepconAxiomatization_sepconAX
      {sepconD: SepconDeduction L GammaD1}:
  SepconAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply derivable1_sepcon_comm.
  -intros. apply derivable1_provable. apply derivable1_sepcon_assoc1.
  -intros. apply derivable1_provable. apply derivable1_provable in H.
   apply derivable1_provable in H0. apply derivable1_sepcon_mono;auto.
   Qed.

Context {orpL: OrLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {falsepL: FalseLanguage L}.

Lemma Deduction2Axiomatization_sepcon_orp_AX
      {sepcon_orp_D: SepconOrDeduction L GammaD1}:
  SepconOrAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply orp_sepcon_left.
  Qed.

Lemma Deduction2Axiomatization_sepcon_falsep_AX
      {sepcon_falsep_D: SepconFalseDeduction L GammaD1}:
  SepconFalseAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply falsep_sepcon_left.
  Qed.

Lemma Deduction2Axiomatization_esGamma
      {esD: ExtSeparationLogicDeduction L GammaD1}:
  ExtSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_sepcon_ext.
  Qed.

Lemma Deduction2Axiomatization_gcsAX
      {gcs: GarbageCollectSeparationLogicDeduction L GammaD1}:
  GarbageCollectSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_sepcon_elim1.
  Qed.

End SLFromDeduction2SLFromAxiomatization1.

Instance reg_Deduction2Axiomatization_sepcon_orpAX:
  RegisterClass D12P_reg (fun sepcon_orp_AX:unit => @Deduction2Axiomatization_sepcon_orp_AX) 10.
Qed.

Instance reg_Deduction2Axiomatization_sepcon_falsep_AX:
  RegisterClass D12P_reg (fun sepcon_false_AX:unit => @Deduction2Axiomatization_sepcon_falsep_AX) 11.
Qed.

Instance reg_Deduction2Axiomatization_gcsAX:
  RegisterClass D12P_reg (fun gcsGamma:unit => @Deduction2Axiomatization_gcsAX) 12.
Qed.

(*Rules from SeparationLogic*)

Section SLFromDeduction2SLFromAxiomatization2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma Deduction2Axiomatization_empAX
      {empD: EmpDeduction L GammaD1}:
  EmpAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply sepcon_emp_left.
  -intros. apply derivable1_provable. apply sepcon_emp_right.
  Qed.

Section SLFromDeduction2SLFromAxiomatization3.

Context {orpL: OrLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {falsepL: FalseLanguage L}.

Lemma Deduction2Axiomatization_desGamma
      {desD: DupEmpSeparationLogicDeduction L GammaD1}:
  DupEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_emp_dup.
  Qed.

Lemma Deduction2Axiomatization_nssGamma
      {nssD: NonsplitEmpSeparationLogicDeduction L GammaD1}:
  NonsplitEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_emp_sepcon_truep_elim.
  Qed.

End SLFromDeduction2SLFromAxiomatization3.

End SLFromDeduction2SLFromAxiomatization2.

Instance reg_Deduction2Axiomatization_nssGamma:
  RegisterClass D12P_reg (fun nssGamma:unit => @Deduction2Axiomatization_nssGamma) 13.
Qed.

Instance reg_Deduction2Axiomatization_empAX:
  RegisterClass D12P_reg (fun empAx:unit => @Deduction2Axiomatization_empAX) 14.
Qed.

Section SLFromDeduction2SLFromAxiomatization4.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma WandDeduction2WandAxiomatization_wandAX
      {wandD: WandDeduction L GammaD1}:
  WandAxiomatization L GammaP.
Proof.
  constructor.
  split.
  -intros. apply derivable1_provable. apply derivable1_provable in H.
   apply derivable1_wand_sepcon_adjoint;auto.
  - intros. apply derivable1_provable. apply derivable1_provable in H.
   apply derivable1_wand_sepcon_adjoint;auto.
   Qed.

End SLFromDeduction2SLFromAxiomatization4.

Instance reg_WandDeduction1WandAxiomatization:
  RegisterClass D12P_reg (fun wandAX: unit => @WandDeduction2WandAxiomatization_wandAX) 15.
Qed.

Instance reg_SepconDeduction2SepconAxiomatization:
  RegisterClass D12P_reg (fun SAx:unit => @SepconDeduction2SepconAxiomatization_sepconAX) 16.
Qed.

Section FromAxiomatizationToDeduction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma Axiomatization2Deduction_sepconD
      {sepconAX: SepconAxiomatization L GammaP}:
  SepconDeduction L GammaD1.
Proof.
  intros.
  constructor; intros.
  + rewrite derivable1_provable.
    apply sepcon_comm_impp.
  + rewrite derivable1_provable.
    apply sepcon_assoc1.
  + rewrite derivable1_provable in H, H0 |- *.
    apply sepcon_mono; auto.
Qed.

End FromAxiomatizationToDeduction.

(*Rules from TheoryOfSeparationAxioms*)

Class SepconMonoDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __sepcon_mono: forall x1 x2 y1 y2 : expr, x1 |-- x2 -> y1 |-- y2 -> x1 * y1 |-- x2 * y2
}.

Class SepconDeduction_weak
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __sepcon_comm_impp: forall x y, x * y |-- y * x;
  __sepcon_assoc1: forall x y z, x * (y * z) |-- (x * y) * z;
}.

Class SepconLogicEquiv_weak_iffp
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaE: LogicEquiv L) := {
  __sepcon_comm: forall x y, x * y --||-- y * x;
  __sepcon_assoc: forall x y z, x * (y * z) --||-- (x * y) * z;
}.

Class EmpLogicEquiv_iffp
        (L: Language)
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaE: LogicEquiv L) := {
  __sepcon_emp: forall x, x * emp --||-- x
}.

Lemma SepconDeductionWeak2SepconDeduction
      {L: Language}
      {minL: MinimumLanguage L}
      {sepconL: SepconLanguage L}
      {GammaD1: Derivable1 L}
      {sepconAX: SepconDeduction_weak L GammaD1}
      {sepcon_mono_AX: SepconMonoDeduction L GammaD1}:
  SepconDeduction L GammaD1.
Proof.
  constructor.
  - apply __sepcon_comm_impp.
  - apply __sepcon_assoc1.
  - apply __sepcon_mono.
Qed.

Section SepconDeduction_weak2SepconAxiomatization_weak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {sepconDw: SepconDeduction_weak L GammaD1}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma SepconDeduction_weak2SepconAxiomatization_weak: SepconAxiomatization_weak L GammaP.
Proof.
  constructor.
  -intros.
   apply derivable1_provable.
   apply __sepcon_comm_impp.
  -intros.
   apply derivable1_provable.
   apply __sepcon_assoc1.
   Qed.

End SepconDeduction_weak2SepconAxiomatization_weak.

Instance reg_SepconDeduction_weak2SepconAxiomatization_weak:
  RegisterClass D12P_reg (fun sepconAX:unit => @SepconDeduction_weak2SepconAxiomatization_weak) 17.
Qed.

Section SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaPD1: ProvableDerivable1 L GammaP GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
  SepconAxiomatization_weak_iffp L GammaP.
Proof.
  pose proof Deduction2Axiomatization_minAX as minAX.
  pose proof Deduction2Axiomatization_iffpAX as iffpAX.
  constructor.
  - intros.
    pose proof __sepcon_comm x y.
    apply logic_equiv_derivable1 in H; destruct H.
    rewrite derivable1_provable in H, H0.
    apply solve_iffp_intros; auto.
  - intros.
    pose proof __sepcon_assoc x y z.
    apply logic_equiv_derivable1 in H; destruct H.
    rewrite derivable1_provable in H, H0.
    apply solve_iffp_intros; auto.
Qed.

End SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

Instance reg_SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
  RegisterClass D12P_reg (fun sepcon_weak_iffp:unit => @SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp) 18.
Qed.

Section EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaPD1: ProvableDerivable1 L GammaP GammaD1}
        {empE: EmpLogicEquiv_iffp L GammaE}
        {iffpD: IffDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
EmpAxiomatization_iffp L GammaP.
Proof.
  pose proof Deduction2Axiomatization_minAX as minAX.
  pose proof Deduction2Axiomatization_iffpAX as iffpAX.
  constructor.
  intros.
  pose proof __sepcon_emp x.
  apply logic_equiv_derivable1 in H; destruct H.
  rewrite derivable1_provable in H, H0.
  apply solve_iffp_intros; auto.
Qed.

End EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

Instance reg_EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
  RegisterClass D12P_reg (fun empAX_iffp:unit => @EmpLogicEquiv_iffp2EmpAxiomatization_iffp) 19.
Qed.

Section FromSepconDeductionWeakToSepcon.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {sepconD: SepconDeduction_weak L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma Adj2SepconMono: SepconMonoDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconMono.
  constructor.
  intros.
  rewrite derivable1_provable in H0, H1 |- *.
  apply TheoryOfSeparationAxioms.__sepcon_mono;auto.
  Qed.

End FromSepconDeductionWeakToSepcon.

Section FromSepconWeakIffToSepconDeductionWeak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma SepconLogicEquivWeakIff2SepconDeductionWeak:
  SepconDeduction_weak L GammaD1.
Proof.
  AddAxiomatization.
  pose proof SepconAxiomatizationWeakIff2SepconAxiomatizationWeak.
  constructor.
  -intros.
   apply derivable1_provable;apply TheoryOfSeparationAxioms.__sepcon_comm_impp.
  -intros.
   apply derivable1_provable;apply TheoryOfSeparationAxioms.__sepcon_assoc1.
   Qed.

End FromSepconWeakIffToSepconDeductionWeak.

Section FromAdjToSepconOrDeductionPropositionalCombination.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma Adj2SepconOrD {orpL: OrLanguage L} {orpD: OrDeduction L GammaD1}: SepconOrDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconOr.
  constructor.
  intros.
  apply derivable1_provable.
  apply orp_sepcon_impp.
Qed.

Lemma Adj2SepconFalse {falsepL: FalseLanguage L} {falsepD: FalseDeduction L GammaD1}: SepconFalseDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconFalse.
  constructor.
  intros.
  apply derivable1_provable.
  apply falsep_sepcon_impp.
Qed.

End FromAdjToSepconOrDeductionPropositionalCombination.

Section FromEmpEIffToEmpD.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {empD: EmpLogicEquiv_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma EmpLogicEquivIff2EmpDeduction:
  EmpDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof EmpAxiomatizationIff2EmpAxiomatization.
  constructor.
  + intros.
    apply derivable1_provable. apply SeparationLogic.sepcon_emp1.
  + intros.
    apply derivable1_provable. apply SeparationLogic.sepcon_emp2.
Qed.

End FromEmpEIffToEmpD.


