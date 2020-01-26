Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
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
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import Derivable1.
Local Open Scope Derivable1.

Class CoqPropDeduction
      (L: Language)
      {truepL: TrueLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (GammaD1: Derivable1 L): Prop := {
  coq_prop_right: forall (P: Prop) x, P -> x |-- !! P;
  coq_prop_left: forall (P: Prop) x, (P -> TT |-- x) -> !! P |-- x;
}.

Class CoqPropImpDeduction
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (GammaD1: Derivable1 L): Prop := {
  derivable1_coq_prop_impp: forall (P Q: Prop), (!! P --> !! Q) |-- !! (P -> Q);
}.

Section CoqPropDeduction2CoqPropAxiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {coq_prop_D: CoqPropDeduction L GammaD1}
        {minAX: MinimumAxiomatization L GammaP}
        {bD: BasicDeduction L GammaD1}
        {truepD: TrueDeduction L GammaD1}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {GammaPD1: ProvableDerivable1 L GammaP GammaD1}.

Lemma Deduction2Axiomatization_coq_prop_AX:
  CoqPropAxiomatization L GammaP.
Proof.  
  constructor.
  + intros.
    rewrite provable_derivable1_true. apply coq_prop_right. auto.
  + intros.
    apply derivable1_provable.
    rewrite provable_derivable1_true in H.
    apply coq_prop_left.
    auto.
Qed.

Lemma Deduction2Axiomatization_coq_prop_impp_AX
      {coq_prop_impp_D: CoqPropImpDeduction L GammaD1}:
  CoqPropImpAxiomatization L GammaP.
Proof.
  constructor.
  intros.
  apply derivable1_provable. apply derivable1_coq_prop_impp.
Qed.

End CoqPropDeduction2CoqPropAxiomatization.

Instance reg_Deduction2Axiomatization_coq_prop_AX:
  RegisterClass D1ToP_reg (fun coq_prop_AX:unit => @Deduction2Axiomatization_coq_prop_AX) 8.
Qed.

Instance reg_Deduction2Axiomatization_coq_prop_impp_AX:
  RegisterClass D1ToP_reg (fun coq_prop_impp_AX:unit => @Deduction2Axiomatization_coq_prop_impp_AX) 9.
Qed.

Section DeductionRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {orpD: OrDeduction L GammaD1}
        {falsepD: FalseDeduction L GammaD1}
        {inegpD: IntuitionisticNegDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {truepD: TrueDeduction L GammaD1}
        {coq_prop_D: CoqPropDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma coq_prop_andp_left: 
forall (P: Prop) Q R, (P -> Q |-- R) -> !! P && Q |-- R.
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_andp_impp P Q R.
  rewrite derivable1_provable in H |- *.
  auto.
  Qed.

Lemma andp_coq_prop_left: 
forall (P: Prop) Q R, (P -> Q |-- R) -> Q && !! P |-- R.
Proof.
  AddAxiomatization.
  intros.
  pose proof andp_coq_prop_impp P Q R.
  rewrite derivable1_provable in H |- *.
  auto.
  Qed.

Section LogicEquiv.

Context {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma coq_prop_truep_equiv: forall (P: Prop), P -> !! P --||-- truep.
Proof.
  AddAxiomatization.
  intros.
  apply logic_equiv_derivable1.
  pose proof coq_prop_truep P.
  pose proof iffp_elim1 (!! P) TT.
  pose proof iffp_elim2 (!! P) TT.
  split.
  -apply derivable1_provable.
   eapply modus_ponens;[apply H1|].
   apply H0;auto.
  -apply derivable1_provable.
   eapply modus_ponens;[apply H2|].
   apply H0;auto.
   Qed.

Lemma coq_prop_andp_equiv: forall (P: Prop) Q, P -> !! P && Q --||-- Q.
Proof.
  AddAxiomatization.
  intros.
  apply logic_equiv_derivable1.
  split.
  -apply derivable1_andp_elim2.
  -pose proof ProofRules.coq_prop_intros P.
   apply H0 in H.
   apply derivable1_provable.
   pose proof andp_intros (!! P) Q.
   pose proof modus_ponens _ _ H1 H.
   auto.
   Qed.

Lemma andp_coq_prop_equiv: forall (P: Prop) Q, P -> Q && !! P --||-- Q.
Proof.
  AddAxiomatization.
  intros.
  apply logic_equiv_derivable1.
  split.
  -apply derivable1_andp_elim1.
  -pose proof ProofRules.coq_prop_intros P.
   apply H0 in H.
   apply derivable1_provable.
   pose proof andp_intros Q (!! P).
   apply derivable1_provable in H1.
   apply deduction_exchange in H1.
   apply derivable1_provable in H1.
   pose proof modus_ponens _ _ H1 H.
   auto.
   Qed.

Lemma coq_prop_and_equiv: forall P Q: Prop, !! (P /\ Q) --||-- !! P && !! Q.
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_and P Q.
  apply logic_equiv_derivable1.
  split.
  -apply derivable1_provable.
   pose proof iffp_elim1 (!! (P /\ Q)) (!! P && !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
  -apply derivable1_provable.
   pose proof iffp_elim2 (!! (P /\ Q)) (!! P && !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
   Qed.

Lemma coq_prop_or_equiv: forall P Q: Prop, !! (P \/ Q) --||-- !! P || !! Q.
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_or P Q.
  apply logic_equiv_derivable1.
  split.
  -apply derivable1_provable.
   pose proof iffp_elim1 (!! (P \/ Q)) (!! P || !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
  -apply derivable1_provable.
   pose proof iffp_elim2 (!! (P \/ Q)) (!! P || !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
   Qed.

Lemma coq_prop_impl_equiv {coq_prop_impp_D: CoqPropImpDeduction L GammaD1}:
  forall P Q: Prop, !! (P -> Q) --||-- (!! P --> !! Q).
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_impl P Q.
  apply logic_equiv_derivable1.
  split.
  -apply derivable1_provable.
   pose proof iffp_elim1 (!! (P -> Q)) (!! P --> !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
  -apply derivable1_provable.
   pose proof iffp_elim2 (!! (P -> Q)) (!! P --> !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
   Qed.

End LogicEquiv.

End DeductionRules.
