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

Class ExcludedMiddle (L: Language) {minL: MinimumLanguage L} {orpL: OrpLanguage L} {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {orpGamma: OrpAxiomatization L Gamma} {falsepGamma: FalsepAxiomatization L Gamma} {inegpGamma: IntuitionisticNegpAxiomatization L Gamma} := {
  excluded_middle: forall x, |-- x || ~~ x
}.

Section ExcludedMiddle2ImplyToOr.

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
        {emAX: ExcludedMiddle L Gamma}.

Lemma impp2orp': forall (x y: expr),
  |-- (x --> y) <--> (~~ x || y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply (deduction_modus_ponens _ (x || ~~ x)).
    - pose proof excluded_middle x.
      pose proof solve_impp_elim_left (x-->y) _ H.
      rewrite provable_derivable in H0.
      rewrite <- deduction_theorem in H0. apply H0.
    - apply deduction_orp_elim'.
      * rewrite <- deduction_theorem.
        apply deduction_orp_intros2.
        rewrite -> deduction_theorem.
        apply derivable_assum1.
      * rewrite <- deduction_theorem.
        apply deduction_orp_intros1.
        apply derivable_assum1.
  + rewrite deduction_theorem. apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      rewrite <- deduction_theorem.
      apply deduction_falsep_elim.
      rewrite -> deduction_theorem.
      pose proof negp_fold_unfold x. rewrite <- H.
      apply derivable_assum1.
    - apply derivable_axiom1.
Qed.

End ExcludedMiddle2ImplyToOr.

Class ImplyToOr (L: Language) {minL: MinimumLanguage L} {orpL: OrpLanguage L} {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} {iffpL: IffpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {orpGamma: OrpAxiomatization L Gamma} {falsepGamma: FalsepAxiomatization L Gamma} {inegpGamma: IntuitionisticNegpAxiomatization L Gamma} {iffpGamma: IffpAxiomatization L Gamma} := {
  impp2orp: forall x y, |-- (x --> y) <--> (~~ x || y)
}.

Section ImplyToOr2DoubleNegativeElimination.

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
        {impp2orpAX: ImplyToOr L Gamma}.

Lemma double_negp_elim': forall (x: expr),
  |-- ~~ (~~ x) --> x.
Proof.
  AddSequentCalculus.
  intros.
  pose proof negp_fold_unfold x.
  pose proof negp_fold_unfold (~~x).

Admitted.

End ImplyToOr2DoubleNegativeElimination.

Class DoubleNegativeElimination (L: Language) {minL: MinimumLanguage L} {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {falsepGamma: FalsepAxiomatization L Gamma} {inegpGamma: IntuitionisticNegpAxiomatization L Gamma} := {
  double_negp_elim: forall x, |-- ~~ (~~ x) --> x
}.

Class PeirceLaw (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  peirce_law: forall x y, |-- ((x --> y) --> x) --> x
}.

Class ByContradiction (L: Language) {minL: MinimumLanguage L} {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {falsepGamma: FalsepAxiomatization L Gamma} {inegpGamma: IntuitionisticNegpAxiomatization L Gamma} := {
  by_contradiction: forall x y, |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x
}.



Class ClassicalPropositionalSequentCalculus (L: Language) {minL: MinimumLanguage L} {orpL: OrpLanguage L} {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} (Gamma: Derivable L) {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {orpSC: OrpSequentCalculus L Gamma} {falsepSC: FalsepSequentCalculus L Gamma} {inegpSC: IntuitionisticNegpSequentCalculus L Gamma} := {
  derivable_excluded_middle: forall Phi x, Phi |-- x || ~~ x
}.

Section Axiomatization2SequentCalculus.

(*Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimumAxiomatization L GammaP}
        {ipAX: IntuitionisticPropositionalLogic L GammaP}
        {cpAX: ClassicalPropositionalLogic L GammaP}
        {SC: NormalSequentCalculus L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD}.

Lemma Axiomatization2SequentCalculus_cpSC:
  ClassicalPropositionalSequentCalculus L GammaD.
Proof.
  intros.
  constructor.
  intros.
  apply deduction_weaken0.
  apply excluded_middle.
Qed.*)

End Axiomatization2SequentCalculus.

Instance reg_Axiomatization2SequentCalculus_cpSC:
  RegisterClass P2D_reg (fun cpSC: unit => @Axiomatization2SequentCalculus_cpSC) 5.
Qed.

Section SequentCalculus2Axiomatization.

(*Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {SC: NormalSequentCalculus L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD}
        {cpSC: ClassicalPropositionalSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {ipAX: IntuitionisticPropositionalLogic L GammaP}.

Lemma SequentCalculus2Axiomatization_cpAX: ClassicalPropositionalLogic L GammaP.
Proof.
  intros.
  constructor.
  intros.
  rewrite provable_derivable.
  apply derivable_excluded_middle.
Qed.*)

End SequentCalculus2Axiomatization.

Instance reg_SequentCalculus2Axiomatization_cpAX:
  RegisterClass D2P_reg (fun cpAX: unit => @SequentCalculus2Axiomatization_cpAX) 3.
Qed.

Section DerivableRulesFromAxiomatization1.

(*Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {cpAX: ClassicalPropositionalLogic L Gamma}.

Lemma double_negp_elim: forall (x: expr),
  |-- ~~ (~~ x) --> x.
Proof.
  AddSequentCalculus.
  intros.
  unfold negp.
  pose proof orp_elim x (x --> FF) (((x --> FF) --> FF) --> x).
  pose proof axiom1 x ((x --> FF) --> FF).
  pose proof modus_ponens _ _ H H0.
  clear H H0.

  pose proof derivable_contradiction_elim empty_context (x --> FF) x.
  rewrite <- provable_derivable in H.
  pose proof modus_ponens _ _ H1 H.
  clear H H1.

  pose proof excluded_middle x.
  pose proof modus_ponens _ _ H0 H.
  auto.
Qed.

Lemma double_negp: forall (x: expr),
  |-- ~~ (~~ x) <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros;
  rewrite <- provable_derivable.
  + apply double_negp_elim.
  + apply double_negp_intros.
Qed.

Instance Classical2GodelDummett: GodelDummettPropositionalLogic L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  set (Phi := empty_context).
  clearbody Phi.
  pose proof excluded_middle x.
  apply deduction_weaken0 with (Phi0 := Phi) in H.
  eapply deduction_modus_ponens; [exact H |].
  apply deduction_orp_elim'.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros2.
    rewrite deduction_theorem.
    apply derivable_axiom1.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros1.
    rewrite deduction_theorem.
    apply deduction_impp_arg_switch.
    apply derivable_contradiction_elim.
Qed.

Lemma contrapositiveNN: forall (x y: expr),
  |-- (~~ y --> ~~ x) --> (x --> y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite <- (double_negp_elim y) at 2.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_contrapositivePN.
  solve_assum.
Qed.

Lemma contrapositiveNP: forall (x y: expr),
  |-- (~~ y --> x) --> (~~ x --> y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite <- (contrapositiveNN (~~ x) y).
  rewrite <- (double_negp_intros x).
  apply provable_impp_refl.
Qed.*)

End DerivableRulesFromAxiomatization1.

Section DerivableRulesFromSequentCalculus.

(*Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}.

Lemma deduction_contrapositiveNN: forall Phi (x y: expr),
  Phi |-- ~~ y --> ~~ x ->
  Phi |-- x --> y.
Proof.
  AddAxiomatization.
  intros.
  rewrite <- contrapositiveNN.
  auto.
Qed.

Lemma deduction_contrapositiveNP: forall Phi (x y: expr),
  Phi |-- ~~ y --> x ->
  Phi |-- ~~ x --> y.
Proof.
  AddAxiomatization.
  intros.
  rewrite <- contrapositiveNP.
  auto.
Qed.*)

End DerivableRulesFromSequentCalculus.

Section DerivableRulesFromAxiomatization2.

(*Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {cpAX: ClassicalPropositionalLogic L Gamma}.

Lemma impp2orp: forall (x y: expr),
  |-- (x --> y) <--> (~~ x || y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply (deduction_modus_ponens _ (x || ~~ x)); [apply derivable_excluded_middle |].
    apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros2.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply deduction_orp_intros1.
      apply derivable_assum1.
  + apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      rewrite <- deduction_theorem.
      apply deduction_falsep_elim.
      rewrite -> deduction_theorem.
      apply derivable_assum1.
    - apply derivable_axiom1.
Qed.*)

End DerivableRulesFromAxiomatization2.

