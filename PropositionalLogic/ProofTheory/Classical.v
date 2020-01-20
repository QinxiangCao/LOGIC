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
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class ClassicalAxiomatization (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) := {
  peirce_law: forall x y, |-- ((x --> y) --> x) --> x
}.

Class ClassicalSequentCalculus (L: Language) {orpL: OrLanguage L} {negpL: NegLanguage L} (Gamma: Derivable L) := {
  derivable_excluded_middle: forall Phi x, Phi |-- x || ~~ x
}.

Class ClassicalDeduction (L:Language) {orpL: OrLanguage L} {negp:NegLanguage L} (GammaD1:Derivable1 L) := {
  deduction_excluded_middle: forall x y,derivable1 x (y || ~~y)
}.

Class ClassicalPropositionalLogicEquiv (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {negpL: NegLanguage L}  (GammaE:LogicEquiv L) := {
  equiv_excluded_middle:forall x, x --||-- ~~(~~x);
  equiv_DeMorgen:forall x y, ~~(x && y) --||-- (~~x) && (~~y)
}.

Section DerivableRulesFromAxiomatization0.

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
        {cpAX: ClassicalAxiomatization L Gamma}.

Lemma by_contradiction: forall x y, |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  apply __by_contradiction.
Qed.

Lemma double_negp_elim: forall x, |-- ~~ (~~ x) --> x.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegativeElimination.
  apply __double_negp_elim.
Qed.

Lemma excluded_middle: forall x, |-- x || ~~ x.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegativeElimination.
  pose proof DoubleNegativeElimination2ExcludedMiddle.
  apply __excluded_middle.
Qed.

Lemma classic_analysis: forall x y, |-- (x --> y) --> (~~ x --> y) --> y.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegativeElimination.
  pose proof DoubleNegativeElimination2ExcludedMiddle.
  pose proof ExcludedMiddle2ClassicAnalysis.
  apply __classic_analysis.
Qed.

Lemma impp2orp1: forall x y, |-- (x --> y) --> (~~ x || y).
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegativeElimination.
  pose proof DoubleNegativeElimination2ExcludedMiddle.
  pose proof ExcludedMiddle2ClassicAnalysis.
  pose proof ClassicAnalysis2ImplyToOr.
  apply __impp2orp1.
Qed.

Lemma impp2orp: forall x y, |-- (x --> y) <--> (~~ x || y).
Proof.
  intros.
  apply solve_iffp_intros.
  + apply impp2orp1.
  + apply impp2orp2.
Qed.

End DerivableRulesFromAxiomatization0.

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
        {cpAX: ClassicalAxiomatization L GammaP}
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
  ClassicalSequentCalculus L GammaD.
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
        {cpSC: ClassicalSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}.

Lemma SequentCalculus2Axiomatization_cpAX: ClassicalAxiomatization L GammaP.
Proof.
  intros.
  constructor.
  assert (forall x, |-- x || ~~ x). {
    intros.
    rewrite provable_derivable.
    apply derivable_excluded_middle.
  }
  pose proof Build_ExcludedMiddle _ _ _ _ H.
  pose proof ExcludedMiddle2ClassicAnalysis.
  pose proof ClassicAnalysis2ImplyToOr.
  pose proof ImplyToOr2PeirceLaw.
  apply __peirce_law.
Qed.

End SequentCalculus2Axiomatization.

Instance reg_SequentCalculus2Axiomatization_cpAX:
  RegisterClass D2P_reg (fun cpAX: unit => @SequentCalculus2Axiomatization_cpAX) 8.
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
        {cpAX: ClassicalAxiomatization L Gamma}.

Lemma double_negp: forall (x: expr),
  |-- ~~ (~~ x) <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + apply double_negp_elim.
  + apply double_negp_intros.
Qed.

Instance Classical2GodelDummett: GodelDummettAxiomatization L Gamma.
Proof.
  constructor.
  clear - orpAX inegpAX cpAX minAX falsepAX.
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
        {cpSC: ClassicalSequentCalculus L Gamma}.

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
        {cpAX: ClassicalAxiomatization L Gamma}.

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

