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
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (GammaD1: Derivable1 L): Prop := {
  coq_prop_intros: forall P: Prop, P -> (!! P --> !! P)|-- !! P;
  coq_prop_elim: forall (P: Prop) x, (P -> (x --> x) |-- x) -> (!! P |-- x);
  coq_prop_impp: forall (P Q: Prop), (!! P --> !! Q) |-- !! (P -> Q);
}.

Section CoqPropDeduction2CoqPropAxiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {coq_prop_D: CoqPropDeduction L GammaD1}
        {minD: MinimumDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}
        {P2D: Provable_Derivable1 L GammaP GammaD1}.

Lemma CoqPropDeduction2CoqPropAxiomatization_coq_prop_AX:
CoqPropAxiomatization L GammaP.
Proof.
  constructor.
  -intros.
   apply provable_derivable1. apply coq_prop_intros. auto.
  -intros.
   pose proof PD2ND.
   apply derivable1_provable.
   rewrite <- provable_derivable1 in H.
   apply coq_prop_elim;auto.
  -intros.
   pose proof PD2ND.
   apply derivable1_provable. apply coq_prop_impp.
  Qed.

End CoqPropDeduction2CoqPropAxiomatization.

Instance reg_CoqPropDeduction2CoqPropAxiomatization_coq_prop_AX:
  RegisterClass D1ToP_reg (fun coq_prop_AX:unit => @CoqPropDeduction2CoqPropAxiomatization_coq_prop_AX) 8.
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
        {andpD: AndpDeduction L GammaD1}
        {adjD: ImppAndpAdjoint L GammaD1}
        {orpD: OrpDeduction L GammaD1}
        {falsepD: FalsepDeduction L GammaD1}
        {inegpD: NegpDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {truepD: TruepDeduction L GammaD1}
        {coq_prop_D: CoqPropDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma coq_prop_andp_impp: 
forall (P: Prop) Q R, (P -> Q |-- R) -> !! P && Q |-- R.
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_andp_impp P Q R.
  rewrite derivable1_provable in H |- *.
  auto.
  Qed.

Lemma andp_coq_prop_impp: 
forall (P: Prop) Q R, (P -> Q |-- R) -> Q && !! P |-- R.
Proof.
  AddAxiomatization.
  intros.
  pose proof andp_coq_prop_impp P Q R.
  rewrite derivable1_provable in H |- *.
  auto.
  Qed.

Lemma impp_coq_prop: forall (P: Prop) Q, P -> Q |-- !! P.
Proof.
  AddAxiomatization.
  intros.
  pose proof impp_coq_prop P Q.
  rewrite derivable1_provable.
  auto.
  Qed.

Section LogicEquiv.

Context {GammaE: LogicEquiv L}
        {NE2: NormalEquiv2 L GammaD1 GammaE}.

Lemma coq_prop_truep: forall (P: Prop), P -> !! P --||-- truep.
Proof.
  AddAxiomatization.
  intros.
  apply equiv_derivable1.
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

Lemma coq_prop_andp: forall (P: Prop) Q, P -> !! P && Q --||-- Q.
Proof.
  AddAxiomatization.
  intros.
  apply equiv_derivable1.
  split.
  -apply derivable1_andp_elim2.
  -pose proof ProofRules.coq_prop_intros P.
   apply H0 in H.
   apply derivable1_provable.
   pose proof andp_intros (!! P) Q.
   pose proof modus_ponens _ _ H1 H.
   auto.
   Qed.

Lemma andp_coq_prop: forall (P: Prop) Q, P -> Q && !! P --||-- Q.
Proof.
  AddAxiomatization.
  intros.
  apply equiv_derivable1.
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

Lemma coq_prop_and: forall P Q: Prop, !! (P /\ Q) --||-- !! P && !! Q.
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_and P Q.
  apply equiv_derivable1.
  split.
  -apply derivable1_provable.
   pose proof iffp_elim1 (!! (P /\ Q)) (!! P && !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
  -apply derivable1_provable.
   pose proof iffp_elim2 (!! (P /\ Q)) (!! P && !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
   Qed.

Lemma coq_prop_or: forall P Q: Prop, !! (P \/ Q) --||-- !! P || !! Q.
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_or P Q.
  apply equiv_derivable1.
  split.
  -apply derivable1_provable.
   pose proof iffp_elim1 (!! (P \/ Q)) (!! P || !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
  -apply derivable1_provable.
   pose proof iffp_elim2 (!! (P \/ Q)) (!! P || !! Q).
   pose proof modus_ponens _ _ H0 H;auto.
   Qed.

Lemma coq_prop_impl: forall P Q: Prop, !! (P -> Q) --||-- (!! P --> !! Q).
Proof.
  AddAxiomatization.
  intros.
  pose proof coq_prop_impl P Q.
  apply equiv_derivable1.
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
