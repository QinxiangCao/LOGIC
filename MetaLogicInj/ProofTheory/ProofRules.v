Require Import Logic.lib.register_typeclass.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MetaLogicInj.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.

Class CoqPropAxiomatization
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (Gamma: Provable L): Prop := {
  coq_prop_intros: forall P: Prop, P -> |-- !! P;
  coq_prop_elim: forall (P: Prop) x, (P -> |-- x) -> |-- !! P --> x;
}.

Class CoqPropImpAxiomatization
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (Gamma: Provable L): Prop := {
  coq_prop_impp: forall (P Q: Prop), |-- (!! P --> !! Q) --> !! (P -> Q);
}.

Class CoqPropSequentCalculus
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (Gamma: Derivable L): Prop := {
  derivable_coq_prop_intros: forall (P: Prop) Phi, P -> Phi |--- !! P;
  derivable_coq_prop_elim: forall (P: Prop) Phi x, (P -> Phi |--- x) -> Phi;; !! P |--- x;
  derivable_coq_prop_impp_left: forall (P Q: Prop) Phi, Phi;; !! P --> !! Q |--- !! (P -> Q)
}.

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

Section DerivedRulesFromAxiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {coq_prop_AX: CoqPropAxiomatization L Gamma}.

Lemma coq_prop_truep: forall (P: Prop), P -> |-- !! P <--> truep.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply coq_prop_elim.
    intros.
    apply provable_truep.
  + apply aux_minimun_rule00.
    apply coq_prop_intros.
    auto.
Qed.

Lemma coq_prop_andp: forall (P: Prop) Q, P -> |-- !! P && Q <--> Q.
Proof.
  intros.
  rewrite coq_prop_truep by auto.
  rewrite truep_andp.
  apply provable_iffp_refl.
Qed.

Lemma andp_coq_prop: forall (P: Prop) Q, P -> |-- Q && !! P <--> Q.
Proof.
  intros.
  rewrite coq_prop_truep by auto.
  rewrite andp_truep.
  apply provable_iffp_refl.
Qed.

Lemma coq_prop_andp_impp: forall (P: Prop) Q R, (P -> |-- Q --> R) -> |-- !! P && Q --> R.
Proof.
  intros.
  rewrite <- impp_curry.
  apply coq_prop_elim.
  auto.
Qed.

Lemma andp_coq_prop_impp: forall (P: Prop) Q R, (P -> |-- Q --> R) -> |-- Q && !! P --> R.
Proof.
  intros.
  rewrite andp_comm.
  rewrite <- impp_curry.
  apply coq_prop_elim.
  auto.
Qed.

Lemma impp_coq_prop: forall (P: Prop) Q, P -> |-- Q --> !! P.
Proof.
  intros.
  apply aux_minimun_rule00.
  apply coq_prop_intros.
  auto.
Qed.

Lemma coq_prop_and: forall P Q: Prop, |-- !! (P /\ Q) <--> !! P && !! Q.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply coq_prop_elim.
    intros [? ?].
    apply solve_andp_intros; apply coq_prop_intros; auto.
  + rewrite <- impp_curry.
    apply coq_prop_elim; intros.
    apply coq_prop_elim; intros.
    apply coq_prop_intros; auto.
Qed.

Lemma coq_prop_or: forall P Q: Prop, |-- !! (P \/ Q) <--> !! P || !! Q.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply coq_prop_elim.
    intros [? | ?].
    - apply solve_orp_intros1.
      apply coq_prop_intros; auto.
    - apply solve_orp_intros2.
      apply coq_prop_intros; auto.
  + apply solve_orp_impp.
    - apply coq_prop_elim; intros.
      apply coq_prop_intros; auto.
    - apply coq_prop_elim; intros.
      apply coq_prop_intros; auto.
Qed.

Lemma coq_prop_impl {coq_prop_impp_AX: CoqPropImpAxiomatization L Gamma}:
  forall P Q: Prop, |-- !! (P -> Q) <--> (!! P --> !! Q).
Proof.
  intros.
  apply solve_iffp_intros.
  + apply coq_prop_elim; intros.
    apply coq_prop_elim; intros.
    apply coq_prop_intros; auto.
  + apply coq_prop_impp.
Qed.

End DerivedRulesFromAxiomatization.

Section Deduction2Axiomatization.

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

End Deduction2Axiomatization.

Instance reg_Deduction2Axiomatization_coq_prop_AX:
  RegisterClass D12P_reg (fun coq_prop_AX:unit => @Deduction2Axiomatization_coq_prop_AX) 8.
Qed.

Instance reg_Deduction2Axiomatization_coq_prop_impp_AX:
  RegisterClass D12P_reg (fun coq_prop_impp_AX:unit => @Deduction2Axiomatization_coq_prop_impp_AX) 9.
Qed.

Section DeductionRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {orpD: OrDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {truepD: TrueDeduction L GammaD1}
        {coq_prop_D: CoqPropDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma coq_prop_andp_left: 
forall (P: Prop) Q R, (P -> Q |-- R) -> !! P && Q |-- R.
Proof.
  intros.
  apply derivable1_impp_andp_adjoint.
  apply coq_prop_left.
  intros.
  apply derivable1_impp_andp_adjoint.
  rewrite <- H by auto.
  apply derivable1_andp_elim2.
Qed.

Lemma andp_coq_prop_left: 
forall (P: Prop) Q R, (P -> Q |-- R) -> Q && !! P |-- R.
Proof.
  intros.
  rewrite derivable1_andp_comm.
  apply coq_prop_andp_left.
  auto.
Qed.

Section LogicEquiv.

Context {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma coq_prop_truep_equiv: forall (P: Prop), P -> !! P --||-- truep.
Proof.
  intros.
  apply logic_equiv_derivable1; split.
  + apply derivable1_truep_intros.
  + apply coq_prop_right; auto.
Qed.

Lemma coq_prop_andp_equiv: forall (P: Prop) Q, P -> !! P && Q --||-- Q.
Proof.
  intros.
  apply logic_equiv_derivable1; split.
  + apply derivable1_andp_elim2.
  + apply derivable1_andp_intros.
    - apply coq_prop_right; auto.
    - reflexivity.
Qed.

Lemma andp_coq_prop_equiv: forall (P: Prop) Q, P -> Q && !! P --||-- Q.
Proof.
  intros.
  apply logic_equiv_derivable1; split.
  + apply derivable1_andp_elim1.
  + apply derivable1_andp_intros.
    - reflexivity.
    - apply coq_prop_right; auto.
Qed.

Lemma coq_prop_and_equiv: forall P Q: Prop, !! (P /\ Q) --||-- !! P && !! Q.
Proof.
  intros.
  apply logic_equiv_derivable1; split.
  + apply derivable1_andp_intros.
    - apply coq_prop_left; intros.
      apply coq_prop_right; tauto.
    - apply coq_prop_left; intros.
      apply coq_prop_right; tauto.
 + apply derivable1_impp_andp_adjoint.
   apply coq_prop_left; intros.
   apply derivable1_impp_andp_adjoint.
   rewrite derivable1_andp_comm.
   apply derivable1_impp_andp_adjoint.
   apply coq_prop_left; intros.
   apply derivable1_impp_andp_adjoint.
   apply coq_prop_right.
   auto.
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
