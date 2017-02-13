Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Section IntuitionisticDerivedRules.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {KmGamma: SystemK L Gamma}.

Lemma boxp_andp: forall x y, |-- boxp (x && y) <--> (boxp x && boxp y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem;
    apply deduction_andp_intros.
    - rewrite <- (andp_elim1 x y) at 2.
      apply derivable_assum1.
    - rewrite <- (andp_elim2 x y) at 2.
      apply derivable_assum1.
  + rewrite <- deduction_theorem.
    pose proof derivable_assum1 empty_context (boxp x && boxp y).
    pose proof deduction_andp_elim1 _ _ _ H.
    pose proof deduction_andp_elim2 _ _ _ H.
    eapply deduction_modus_ponens; [exact H1 |].
    apply deduction_axiom_K.
    eapply deduction_modus_ponens; [exact H0 |].
    apply deduction_axiom_K.
    apply deduction_weaken0.
    apply rule_N.
    apply andp_intros.
Qed.

Lemma orp_boxp: forall x y, |-- boxp x || boxp y --> boxp (x || y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_orp_elim.
  + apply deduction_axiom_K.
    rewrite <- provable_derivable.
    apply rule_N.
    apply orp_intros1.
  + apply deduction_axiom_K.
    rewrite <- provable_derivable.
    apply rule_N.
    apply orp_intros2.
Qed.

Lemma boxp_TT: |-- boxp TT.
Proof.
  apply rule_N.
  apply provable_impp_refl.
Qed.

Lemma not_diamondp_FF: |-- ~~ diamondp FF.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_double_negp_intros.
  rewrite <- provable_derivable.
  apply rule_N.
  apply provable_impp_refl.
Qed.

Lemma impp_diamondp: forall x y, |-- boxp (x --> y) --> (diamondp x --> diamondp y).
Proof.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_contrapositivePP.
  apply deduction_axiom_K.
  rewrite <- contrapositivePP.
  apply derivable_assum1.
Qed.

Lemma derivable_impp_diamondp: forall Phi x y, Phi |-- boxp (x --> y) --> (diamondp x --> diamondp y).
Proof.
  intros.
  apply deduction_weaken0.
  apply impp_diamondp.
Qed.

Lemma deduction_impp_diamondp: forall Phi x y,
  Phi |-- boxp (x --> y) ->
  Phi |-- (diamondp x --> diamondp y).
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_impp_diamondp.
Qed.

Lemma diamondp_andp: forall x y, |-- diamondp (x && y) --> (diamondp x && diamondp y).
Proof.
  intros.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros.
  + rewrite -> deduction_theorem.
    apply deduction_impp_diamondp.
    rewrite <- provable_derivable.
    apply rule_N.
    apply andp_elim1.
  + rewrite -> deduction_theorem.
    apply deduction_impp_diamondp.
    rewrite <- provable_derivable.
    apply rule_N.
    apply andp_elim2.
Qed.

Lemma orp_diamondp: forall x y, |-- diamondp x || diamondp y --> diamondp (x || y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_orp_elim.
  + apply deduction_impp_diamondp.
    rewrite <- provable_derivable.
    apply rule_N.
    apply orp_intros1.
  + apply deduction_impp_diamondp.
    rewrite <- provable_derivable.
    apply rule_N.
    apply orp_intros2.
Qed.

Lemma P_diamondp_P {TmGamma: SystemT L Gamma}: forall x, |-- x --> diamondp x.
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_contrapositivePN.
  apply derivable_axiom_T.
Qed.

End IntuitionisticDerivedRules.