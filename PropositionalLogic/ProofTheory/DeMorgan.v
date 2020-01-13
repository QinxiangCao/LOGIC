Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class DeMorganPropositionalAxiomatization (L: Language) {minL: MinimumLanguage L} {orpL: OrpLanguage L} {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {orpGamma: OrpAxiomatization L Gamma} {falsepGamma: FalsepAxiomatization L Gamma} {inegpGamma: IntuitionisticNegpAxiomatization L Gamma} := {
  weak_excluded_middle: forall x, |-- ~~ x || ~~ ~~ x
}.

Section DeMorgan.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndpLanguage L}
        {orpL: OrpLanguage L}
        {falsepL: FalsepLanguage L}
        {negpL: NegpLanguage L}
        {iffpL: IffpLanguage L}
        {truepL: TruepLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpGamma: AndpAxiomatization L Gamma}
        {orpGamma: OrpAxiomatization L Gamma}
        {falsepGamma: FalsepAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegpAxiomatization L Gamma}
        {iffpGamma: IffpAxiomatization L Gamma}
        {truepGamma: TruepAxiomatization L Gamma}
        {dmpAX: DeMorganPropositionalAxiomatization L Gamma}.

Lemma demorgan_negp_andp: forall (x y: expr),
  |-- ~~ (x && y) <--> (~~ x || ~~ y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply (deduction_modus_ponens _ (~~ x || ~~ ~~ x)); [apply deduction_weaken0, weak_excluded_middle |].
    apply deduction_orp_elim'.
    - apply deduction_weaken0.
      apply orp_intros1.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros2.
      pose proof negp_fold y. rewrite <- H.
      rewrite <- deduction_theorem.
      apply  (deduction_modus_ponens _ (x --> FF)).
      * rewrite <- deduction_theorem.
        apply (deduction_modus_ponens _ (x && y)).
        { apply deduction_andp_intros; [| apply deduction_weaken1]; apply derivable_assum1. }
        { pose proof negp_unfold (x && y). rewrite <- H0. solve_assum. }
      * pose proof negp_fold x. rewrite H0.
        pose proof negp_unfold (~~x). rewrite <- H1.
        solve_assum.
  + rewrite deduction_theorem.
    rewrite <- provable_derivable.
    apply demorgan_orp_negp.
Qed.

End DeMorgan.
