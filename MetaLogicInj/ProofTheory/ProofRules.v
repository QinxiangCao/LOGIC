Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
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
  coq_prop_impp: forall (P Q: Prop), |-- (!! P --> !! Q) --> !! (P -> Q);
}.

Class CoqPropSequentCalculus
      (L: Language)
      {minL: MinimumLanguage L}
      {coq_prop_L: CoqPropLanguage L}
      (Gamma: Derivable L): Prop := {
  derivable_coq_prop_intros: forall (P: Prop) Phi, P -> Phi |-- !! P;
  derivable_coq_prop_elim: forall (P: Prop) Phi x, (P -> Phi |-- x) -> Phi;; !! P |-- x;
  derivable_coq_prop_impp_left: forall (P Q: Prop) Phi, Phi;; !! P --> !! Q |-- !! (P -> Q)
}.

Section DerivedRules.

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

Lemma coq_prop_impl: forall P Q: Prop, |-- !! (P -> Q) <--> (!! P --> !! Q).
Proof.
  intros.
  apply solve_iffp_intros.
  + apply coq_prop_elim; intros.
    apply coq_prop_elim; intros.
    apply coq_prop_intros; auto.
  + apply coq_prop_impp.
Qed.

End DerivedRules.
