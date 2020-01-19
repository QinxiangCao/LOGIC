Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class ExcludedMiddle (L: Language) {orpL: OrLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __excluded_middle: forall x, |-- x || ~~ x
}.

Class ClassicAnalysis (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __classic_analysis: forall x y, |-- (x --> y) --> (~~ x --> y) --> y
}.

Class ImplyToOr (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} {iffpL: IffLanguage L} (Gamma: Provable L) := {
  __impp2orp1: forall x y, |-- (x --> y) --> (~~ x || y)
}.

Class PeirceLaw (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) := {
  __peirce_law: forall x y, |-- ((x --> y) --> x) --> x
}.

Class ByContradiction (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __by_contradiction: forall x y, |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x
}.

Class DoubleNegativeElimination (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  __double_negp_elim: forall x, |-- ~~ (~~ x) --> x
}.

Section ExcludedMiddle2ClassicAnalysis.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {emAX: ExcludedMiddle L Gamma}.

Lemma ExcludedMiddle2ClassicAnalysis: ClassicAnalysis L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  rewrite <- deduction_theorem.
  apply deduction_subst1 with (x || ~~ x).
  + do 2 apply deduction_weaken1.
    rewrite <- provable_derivable.
    apply __excluded_middle.
  + apply deduction_orp_elim; rewrite deduction_theorem; solve_assum.
Qed.

End ExcludedMiddle2ClassicAnalysis.

Section ClassicAnalysis2ImplyToOr.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpGamma: AndAxiomatization L Gamma}
        {orpGamma: OrAxiomatization L Gamma}
        {falsepGamma: FalseAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegAxiomatization L Gamma}
        {iffpGamma: IffAxiomatization L Gamma}
        {cAX: ClassicAnalysis L Gamma}.

Lemma ClassicAnalysis2ExcludedMiddle: ExcludedMiddle L Gamma.
Proof.
  constructor.
  intros.
  pose proof __classic_analysis x (x || ~~ x).
  pose proof modus_ponens _ _ H (orp_intros1 _ _).
  pose proof modus_ponens _ _ H0 (orp_intros2 _ _).
  auto.
Qed.

Lemma ClassicAnalysis2ImplyToOr: ImplyToOr L Gamma.
Proof.
  pose proof ClassicAnalysis2ExcludedMiddle as EM.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply (deduction_modus_ponens _ (x || ~~ x)).
  + pose proof __excluded_middle x.
    pose proof solve_impp_elim_left (x-->y) _ H.
    rewrite provable_derivable in H0.
    rewrite <- deduction_theorem in H0. apply H0.
  + apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros2.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros1.
      apply derivable_assum1.
Qed.

End ClassicAnalysis2ImplyToOr.

Section ImplyToOr2PeirceLaw.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpGamma: AndAxiomatization L Gamma}
        {orpGamma: OrAxiomatization L Gamma}
        {falsepGamma: FalseAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegAxiomatization L Gamma}
        {iffpGamma: IffAxiomatization L Gamma}
        {truepGamma: TrueAxiomatization L Gamma}
        {itoAX: ImplyToOr L Gamma}.

Lemma ImplyToOr2ExcludedMiddle: ExcludedMiddle L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  pose proof __impp2orp1 x x.
  rewrite orp_comm in H.
  rewrite <- H.
  rewrite provable_derivable. rewrite <- deduction_theorem.
  solve_assum.
Qed.

Lemma ImplyToOr2PeirceLaw: PeirceLaw L Gamma.
Proof.
  pose proof ImplyToOr2ExcludedMiddle as EM.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite (__impp2orp1 (x --> y) x).
  rewrite provable_derivable.
  apply deduction_orp_elim'.
  + apply (deduction_modus_ponens _ (x || ~~ x)); [rewrite <- provable_derivable; apply __excluded_middle |].
    apply deduction_orp_elim'.
    - rewrite <- !deduction_theorem. solve_assum.
    - rewrite <- provable_derivable.
      rewrite <- (falsep_elim x) at 3.
      rewrite <- (negp_unfold (~~ (x --> y))).
      rewrite <- double_negp_intros.
      rewrite <- (falsep_elim y).
      apply negp_unfold.
  + rewrite <- deduction_theorem. solve_assum.
Qed.

End ImplyToOr2PeirceLaw.

Section PeirceLaw2ByContradiction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {plAX: PeirceLaw L Gamma}.

Lemma Peirce2ByContradiction: ByContradiction L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  pose proof __peirce_law x FF.
  rewrite <- (falsep_elim x) in H at 2.
  rewrite -> (negp_fold x) in H.
  pose proof negp_unfold y.
  rewrite (provable_impp_arg_switch (~~y) y FF) in H0.
  rewrite <- H at 3.
  rewrite H0 at 1.
  apply axiom2.
Qed.

End PeirceLaw2ByContradiction.

Section ByContradiction2DoubleNegativeElimination.

Context {L: Language}
        {minL: MinimumLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {inegpGamma: IntuitionisticNegAxiomatization L Gamma}
        {bcAX: ByContradiction L Gamma}.

Lemma ByContradiction2DoubleNegativeElimination:
  DoubleNegativeElimination L Gamma.
Proof.
  constructor.
  intros.
  pose proof __by_contradiction x (~~ (~~ x)).
  pose proof double_negp_intros (~~ x).
  pose proof axiom1 (~~ (~~ x)) (~~ x).
  rewrite <- H1 in H.
  rewrite -> (provable_impp_arg_switch (~~ (~~ x)) (~~ x --> ~~ (~~ (~~ x))) x) in H.
  rewrite H in H0. apply H0.
Qed.

End ByContradiction2DoubleNegativeElimination.

Section DoubleNegativeElimination2ExcludedMiddle.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {dneAX: DoubleNegativeElimination L Gamma}.

Lemma DoubleNegativeElimination2ExcludedMiddle: ExcludedMiddle L Gamma.
Proof.
  AddSequentCalculus.
  constructor.
  intros.
  pose proof negp_unfold x.
  rewrite (provable_impp_arg_switch (~~ x) x FF) in H.
  rewrite <- (__double_negp_elim x) in H at 1.
  rewrite <- (__double_negp_elim (x || ~~ x)).
  rewrite <- (negp_fold (~~ (x || ~~ x))).

  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  eapply deduction_modus_ponens with (~~ x).
  {
    rewrite deduction_theorem, <- provable_derivable.
    eapply modus_ponens; [apply contrapositivePP |].
    apply orp_intros1.
  }
  eapply deduction_modus_ponens with (~~ (~~ x)).
  {
    rewrite deduction_theorem, <- provable_derivable.
    eapply modus_ponens; [apply contrapositivePP |].
    apply orp_intros2.
  }
  rewrite deduction_theorem.
  rewrite <- provable_derivable.
  apply aux_minimun_rule00.
  auto.
Qed.

End DoubleNegativeElimination2ExcludedMiddle.

