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

Class ExcludedMiddle (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {orpGamma: OrAxiomatization L Gamma} {falsepGamma: FalseAxiomatization L Gamma} {inegpGamma: IntuitionisticNegAxiomatization L Gamma} := {
  excluded_middle: forall x, |-- x || ~~ x
}.

Class ImplyToOr (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} {iffpL: IffLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {orpGamma: OrAxiomatization L Gamma} {falsepGamma: FalseAxiomatization L Gamma} {inegpGamma: IntuitionisticNegAxiomatization L Gamma} {iffpGamma: IffAxiomatization L Gamma} := {
  impp2orp: forall x y, |-- (x --> y) <--> (~~ x || y)
}.

Class PeirceLaw (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  peirce_law: forall x y, |-- ((x --> y) --> x) --> x
}.

Class ByContradiction (L: Language) {minL: MinimumLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {falsepGamma: FalseAxiomatization L Gamma} {inegpGamma: IntuitionisticNegAxiomatization L Gamma} := {
  by_contradiction: forall x y, |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x
}.

Class DoubleNegativeElimination (L: Language) {minL: MinimumLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} {falsepGamma: FalseAxiomatization L Gamma} {inegpGamma: IntuitionisticNegAxiomatization L Gamma} := {
  double_negp_elim: forall x, |-- ~~ (~~ x) --> x
}.

Class ClassicalPropositionalSequentCalculus (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} (Gamma: Derivable L) {bSC: BasicSequentCalculus L Gamma} {minSC: MinimumSequentCalculus L Gamma} {orpSC: OrSequentCalculus L Gamma} {falsepSC: FalseSequentCalculus L Gamma} {inegpSC: IntuitionisticNegSequentCalculus L Gamma} := {
  derivable_excluded_middle: forall Phi x, Phi |-- x || ~~ x
}.

Section ExcludedMiddle2ImplyToOr.

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
        {emAX: ExcludedMiddle L Gamma}.

Lemma EM2ImplyToOr: ImplyToOr L Gamma.
Proof.
  constructor.
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

Lemma ImplyToOr2EM: ExcludedMiddle L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  pose proof impp2orp x x.
  rewrite orp_comm in H.
  rewrite <- H.
  rewrite provable_derivable. rewrite <- deduction_theorem.
  solve_assum.
Qed.

Lemma ImplyToOr2PeirceLaw: PeirceLaw L Gamma.
Proof.
  pose proof ImplyToOr2EM as EM.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite (impp2orp (x --> y) x).
  rewrite provable_derivable.
  apply deduction_orp_elim'.
  + apply (deduction_modus_ponens _ (x || ~~ x)); [rewrite <- provable_derivable; apply excluded_middle |].
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
        {plAX: PeirceLaw L Gamma}.

Lemma Peirce2ByContradiction: ByContradiction L Gamma.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  pose proof peirce_law x FF.
  rewrite <- (falsep_elim x) in H at 2.
  rewrite -> (negp_fold x) in H.
  pose proof negp_unfold y.
  rewrite (provable_impp_arg_switch (~~y) y FF) in H0.
  rewrite (impp_curry_uncurry y (~~y) FF) in H0.
  pose proof impp_andp (~~ x) y (~~ y).
  rewrite H0 in H1.
  rewrite H in H1.
  apply H1.
Qed.

End PeirceLaw2ByContradiction.

Section ByContradiction2DoubleNegativeElimination.

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
        {bcAX: ByContradiction L Gamma}.

Lemma ByContradiction2DoubleNegativeElimination:
  DoubleNegativeElimination L Gamma.
Proof.
  constructor.
  intros.
  pose proof by_contradiction x (~~ (~~ x)).
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
        {dneAX: DoubleNegativeElimination L Gamma}.

Lemma DoubleNegativeElimination2ExcludedMiddle: ExcludedMiddle L Gamma.
Proof.
  constructor.
  intros.
  pose proof negp_unfold x.
  rewrite (provable_impp_arg_switch (~~ x) x FF) in H.
  rewrite (impp_curry_uncurry x (~~ x) FF) in H.
  rewrite <- (double_negp_elim x) in H at 1.
  rewrite <- (demorgan_negp_orp (~~ x) x) in H.
  rewrite (negp_fold (~~ (~~ x || x))) in H.
  rewrite (double_negp_elim (~~ x || x)) in H.
  rewrite orp_comm. apply H.
Qed.

End DoubleNegativeElimination2ExcludedMiddle.

Section Axiomatization2SequentCalculus.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {emAX: ExcludedMiddle L GammaP}
        {SC: NormalSequentCalculus L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}.

Lemma Axiomatization2SequentCalculus_cpSC:
  ClassicalPropositionalSequentCalculus L GammaD.
Proof.
  intros.
  constructor.
  intros.
  apply deduction_weaken0.
  apply excluded_middle.
Qed.

End Axiomatization2SequentCalculus.

Instance reg_Axiomatization2SequentCalculus_cpSC:
  RegisterClass P2D_reg (fun cpSC: unit => @Axiomatization2SequentCalculus_cpSC) 10.
Qed.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {SC: NormalSequentCalculus L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}
        {cpSC: ClassicalPropositionalSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}.

Lemma SequentCalculus2Axiomatization_emAX: ExcludedMiddle L GammaP.
Proof.
  intros.
  constructor.
  intros.
  rewrite provable_derivable.
  apply derivable_excluded_middle.
Qed.

End SequentCalculus2Axiomatization.

Instance reg_SequentCalculus2Axiomatization_cpAX:
  RegisterClass D2P_reg (fun cpAX: unit => @SequentCalculus2Axiomatization_emAX) 8.
Qed.

Section DerivableRulesFromAxiomatization1.

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
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {emAX: ExcludedMiddle L Gamma}.

Lemma double_negp: forall (x: expr),
  |-- ~~ (~~ x) <--> x.
Proof.
  pose proof EM2ImplyToOr.
  pose proof ImplyToOr2PeirceLaw.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegativeElimination.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + apply double_negp_elim.
  + apply double_negp_intros.
Qed.

Instance Classical2GodelDummett: GodelDummettPropositionalAxiomatization L Gamma.
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
  pose proof EM2ImplyToOr.
  pose proof ImplyToOr2PeirceLaw.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegativeElimination.
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
Qed.

End DerivableRulesFromAxiomatization1.

Section DerivableRulesFromSequentCalculus.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {andpSC: AndSequentCalculus L Gamma}
        {orpSC: OrSequentCalculus L Gamma}
        {falsepSC: FalseSequentCalculus L Gamma}
        {inegpSC: IntuitionisticNegSequentCalculus L Gamma}
        {iffpSC: IffSequentCalculus L Gamma}
        {truepSC: TrueSequentCalculus L Gamma}
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
Qed.

End DerivableRulesFromSequentCalculus.

Section DerivableRulesFromAxiomatization2.

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
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {emAX: ExcludedMiddle L Gamma}.

Lemma solve_classic: forall x y: expr,
  |-- x --> y ->
  |-- ~~ x --> y ->
  |-- y.
Proof.
  intros.
  eapply modus_ponens; [| apply (excluded_middle x)].
  apply solve_orp_impp; auto.
Qed.

End DerivableRulesFromAxiomatization2.

