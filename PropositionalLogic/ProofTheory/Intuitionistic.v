Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class AndpAxiomatization (L: Language) {minL: MinimumLanguage L} {andpL: AndpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  andp_intros: forall x y, |-- x --> y --> x && y;
  andp_elim1: forall x y, |-- x && y --> x;
  andp_elim2: forall x y, |-- x && y --> y
}.

Class OrpAxiomatization (L: Language) {minL: MinimumLanguage L} {orpL: OrpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  orp_intros1: forall x y, |-- x --> x || y;
  orp_intros2: forall x y, |-- y --> x || y;
  orp_elim: forall x y z, |-- (x --> z) --> (y --> z) --> (x || y --> z)
}.

Class FalsepAxiomatization (L: Language) {minL: MinimumLanguage L} {falsepL: FalsepLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  falsep_elim: forall x, |-- FF --> x
}.

Class IntuitionisticNegpAxiomatization (L: Language) {minL: MinimumLanguage L} {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  negp_unfold: forall x, |-- (~~x) --> (x --> FF);
  negp_fold: forall x, |-- (x --> FF) --> (~~x)
}.

Class IffpAxiomatization (L: Language) {minL: MinimumLanguage L} {iffpL: IffpLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  iffp_intros: forall x y, |-- (x --> y) --> (y --> x) --> (x <--> y);
  iffp_elim1: forall x y, |-- (x <--> y) --> (x --> y);
  iffp_elim2: forall x y, |-- (x <--> y) --> (y --> x)
}.

Class TruepAxiomatization (L: Language) {minL: MinimumLanguage L} {truepL: TruepLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  truep_intros: |-- TT
}.

Class AndpSequentCalculus (L: Language) {andpL: AndpLanguage L} (Gamma: Derivable L) := {
  deduction_andp_intros: forall Phi x y, Phi |-- x -> Phi |-- y -> Phi |-- x && y;
  deduction_andp_elim1: forall Phi x y, Phi |-- x && y -> Phi |-- x;
  deduction_andp_elim2: forall Phi x y, Phi |-- x && y -> Phi |-- y
}.

Class OrpSequentCalculus (L: Language) {orpL: OrpLanguage L} (Gamma: Derivable L) := {
  deduction_orp_intros1: forall Phi x y, Phi |-- x -> Phi |-- x || y;
  deduction_orp_intros2: forall Phi x y, Phi |-- y -> Phi |-- x || y;
  deduction_orp_elim: forall Phi x y z, Phi;; x |-- z -> Phi ;; y |-- z -> Phi;; x || y |-- z
}.

Class FalsepSequentCalculus (L: Language) {falsepL: FalsepLanguage L} (Gamma: Derivable L) := {
  deduction_falsep_elim: forall Phi x, Phi |-- FF -> Phi |-- x
}.

Class IntuitionisticNegpSequentCalculus (L: Language) {falsepL: FalsepLanguage L} {negpL: NegpLanguage L} (Gamma: Derivable L) := {
  deduction_negp_unfold: forall Phi x, Phi |-- (~~x) -> Phi ;; x |-- FF;
  deduction_negp_fold: forall Phi x, Phi ;; x |-- FF -> Phi |-- (~~x)
}.

Class IffpSequentCalculus (L: Language) {iffpL: IffpLanguage L} (Gamma: Derivable L) := {
  deduction_iffp_intros: forall Phi x y, Phi ;; x |-- y -> Phi ;; y |-- x -> Phi |-- (x <--> y);
  deduction_iffp_elim1: forall Phi x y, Phi |-- (x <--> y) -> Phi ;; x |-- y;
  deduction_iffp_elim2: forall Phi x y, Phi |-- (x <--> y) -> Phi ;; y |-- x
}.

Class TruepSequentCalculus (L: Language) {truepL: TruepLanguage L} (Gamma: Derivable L) := {
  deduction_truep_intros: forall Phi, Phi |-- TT
}.

Section DerivableRulesFromSequentCalculus1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndpLanguage L}
        {orpL: OrpLanguage L}
        {falsepL: FalsepLanguage L}
        {negpL: NegpLanguage L}
        {iffpL: IffpLanguage L}
        {truepL: TruepLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {andpSC: AndpSequentCalculus L Gamma}
        {orpSC: OrpSequentCalculus L Gamma}
        {falsepSC: FalsepSequentCalculus L Gamma}
        {inegpSC: IntuitionisticNegpSequentCalculus L Gamma}
        {iffpSC: IffpSequentCalculus L Gamma}
        {truepSC: TruepSequentCalculus L Gamma}.

Lemma derivable_andp_intros: forall (Phi: context) (x y: expr),
  Phi |-- x --> y --> x && y.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_andp_intros; solve_assum.
Qed.

Lemma derivable_andp_elim1: forall (Phi: context) (x y: expr),
  Phi |-- x && y --> x.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_elim1 with y; solve_assum.
Qed.

Lemma derivable_andp_elim2: forall (Phi: context) (x y: expr),
  Phi |-- x && y --> y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_elim2 with x; solve_assum.
Qed.

Lemma derivable_orp_intros1: forall (Phi: context) (x y: expr),
  Phi |-- x --> x || y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_orp_intros1; solve_assum.
Qed.

Lemma derivable_orp_intros2: forall (Phi: context) (x y: expr),
  Phi |-- y --> x || y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_orp_intros2; solve_assum.
Qed.

Lemma derivable_orp_elim: forall (Phi: context) (x y z: expr),
  Phi |-- (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_orp_elim.
  + rewrite deduction_theorem; solve_assum.
  + rewrite deduction_theorem; solve_assum.
Qed.

Lemma derivable_falsep_elim: forall (Phi: context) (x: expr),
  Phi |-- FF --> x.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_falsep_elim; solve_assum.
Qed.

Lemma derivable_negp_unfold: forall (Phi: context) (x: expr),
  Phi |-- (~~x) --> x --> FF.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_negp_unfold; solve_assum.
Qed.

Lemma derivable_negp_fold: forall (Phi: context) (x: expr),
  Phi |-- (x --> FF) --> (~~ x).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_negp_fold.
  apply deduction_modus_ponens with x; solve_assum.
Qed.

Lemma derivable_iffp_intros: forall (Phi: context) (x y: expr),
  Phi |-- (x --> y) --> (y --> x) --> (x <--> y).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_iffp_intros.
  +rewrite deduction_theorem; solve_assum.
  +rewrite deduction_theorem; solve_assum.
Qed.

Lemma derivable_iffp_elim1: forall (Phi: context) (x y: expr),
  Phi |-- (x <--> y) --> (x --> y).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_iffp_elim1; solve_assum.
Qed.

Lemma derivable_iffp_elim2: forall (Phi: context) (x y: expr),
  Phi |-- (x <--> y) --> (y --> x).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_iffp_elim2; solve_assum.
Qed.

Lemma derivable_truep_intros: forall (Phi: context),
  Phi |-- TT.
Proof.
  intros.
  apply deduction_truep_intros; solve_assum.
Qed.

Lemma deduction_orp_elim': forall (Phi: context) (x y z: expr),
  Phi |-- x --> z ->
  Phi |-- y --> z ->
  Phi |-- x || y --> z.
Proof.
  intros.
  rewrite <- deduction_theorem in H, H0 |- *.
  apply deduction_orp_elim; auto.
Qed.

Lemma derivable_double_negp_intros: forall (Phi: context) (x: expr),
  Phi |-- x --> ~~ ~~ x.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  pose proof deduction_negp_fold (Phi;;x) (~~x).
  apply H.
  pose proof deduction_negp_unfold (Phi;;~~x) x.
  pose proof derivable_impp_refl Phi (~~x).
  rewrite <- !deduction_theorem in H1.
  pose proof deduction_impp_arg_switch Phi (~~ x) x FF.
  rewrite <- !deduction_theorem in H2.
  apply H2.
  apply H0.
  apply H1.
Qed.

Lemma deduction_double_negp_intros: forall (Phi: context) (x: expr),
  Phi |-- x ->
  Phi |-- ~~ ~~ x.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_double_negp_intros.
Qed.

Lemma derivable_contradiction_elim: forall (Phi: context) (x y: expr),
  Phi |-- x --> ~~ x --> y.
Proof.
  intros.
  pose proof derivable_double_negp_intros Phi x.
  pose proof derivable_falsep_elim Phi y.
  rewrite <- !deduction_theorem in H.
  rewrite <- !deduction_theorem.
  pose proof deduction_negp_unfold (Phi;;x) (~~x).
  apply H1 in H.
  apply (deduction_weaken1 _ x) in H0.
  apply (deduction_weaken1 _ (~~ x)) in H0.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_contradiction_elim: forall (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- ~~ x ->
  Phi |-- y.
Proof.
  intros.
  pose proof derivable_contradiction_elim Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H1.
  pose proof deduction_modus_ponens _ _ _ H0 H2.
  auto.
Qed.

Lemma derivable_iffp_refl: forall (Phi: context) (x: expr),
  Phi |-- x <--> x.
Proof.
  intros.
  pose proof deduction_iffp_intros Phi x x.
  pose proof derivable_impp_refl Phi x.
  rewrite <- !deduction_theorem in H0.
  apply H.
  apply H0. apply H0.
Qed.

End DerivableRulesFromSequentCalculus1.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndpLanguage L}
        {orpL: OrpLanguage L}
        {falsepL: FalsepLanguage L}
        {negpL: NegpLanguage L}
        {iffpL: IffpLanguage L}
        {truepL: TruepLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {SC: NormalSequentCalculus L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndpSequentCalculus L GammaD}
        {orpSC: OrpSequentCalculus L GammaD}
        {falsepSC: FalsepSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegpSequentCalculus L GammaD}
        {iffpSC: IffpSequentCalculus L GammaD}
        {truepSC: TruepSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma SequentCalculus2Axiomatization_andpAX: AndpAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_andp_intros.
  + apply derivable_andp_elim1.
  + apply derivable_andp_elim2.
Qed.

Lemma SequentCalculus2Axiomatization_orpAX: OrpAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_orp_intros1.
  + apply derivable_orp_intros2.
  + apply derivable_orp_elim.
Qed.

Lemma SequentCalculus2Axiomatization_falsepAX: FalsepAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  apply derivable_falsep_elim.
Qed.

Lemma SequentCalculus2Axiomatization_inegpAX: IntuitionisticNegpAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_negp_unfold.
  + apply derivable_negp_fold.
Qed.

Lemma SequentCalculus2Axiomatization_iffpAX: IffpAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_iffp_intros.
  + apply derivable_iffp_elim1.
  + apply derivable_iffp_elim2.
Qed.

Lemma SequentCalculus2Axiomatization_truepAX: TruepAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  apply derivable_truep_intros.
Qed.

End SequentCalculus2Axiomatization.

Instance reg_SequentCalculus2Axiomatization_andpAX:
  RegisterClass D2P_reg (fun andpAX: unit => @SequentCalculus2Axiomatization_andpAX) 2.
Qed.

Instance reg_SequentCalculus2Axiomatization_orpAX:
  RegisterClass D2P_reg (fun orpAX: unit => @SequentCalculus2Axiomatization_orpAX) 3.
Qed.

Instance reg_SequentCalculus2Axiomatization_falsepAX:
  RegisterClass D2P_reg (fun falsepAX: unit => @SequentCalculus2Axiomatization_falsepAX) 4.
Qed.

Instance reg_SequentCalculus2Axiomatization_inegpAX:
  RegisterClass D2P_reg (fun inegpAX: unit => @SequentCalculus2Axiomatization_inegpAX) 5.
Qed.

Instance reg_SequentCalculus2Axiomatization_iffpAX:
  RegisterClass D2P_reg (fun iffpAX: unit => @SequentCalculus2Axiomatization_iffpAX) 6.
Qed.

Instance reg_SequentCalculus2Axiomatization_truepAX:
  RegisterClass D2P_reg (fun truepAX: unit => @SequentCalculus2Axiomatization_truepAX) 7.
Qed.

Section Axiomatization2SequentCalculus.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndpLanguage L}
        {orpL: OrpLanguage L}
        {falsepL: FalsepLanguage L}
        {negpL: NegpLanguage L}
        {iffpL: IffpLanguage L}
        {truepL: TruepLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {AX: NormalAxiomatization L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpGamma: AndpAxiomatization L GammaP}
        {orpGamma: OrpAxiomatization L GammaP}
        {falsepGamma: FalsepAxiomatization L GammaP}
        {inegpGamma: IntuitionisticNegpAxiomatization L GammaP}
        {iffpGamma: IffpAxiomatization L GammaP}
        {truepGamma: TruepAxiomatization L GammaP}.

Lemma Axiomatization2SequentCalculus_andpSC:
  AndpSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_SC.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  + apply deduction_modus_ponens with y; auto.
    apply deduction_modus_ponens with x; auto.
    apply deduction_weaken0.
    apply andp_intros.
  + apply deduction_modus_ponens with (x && y); auto.
    apply deduction_weaken0.
    apply andp_elim1.
  + apply deduction_modus_ponens with (x && y); auto.
    apply deduction_weaken0.
    apply andp_elim2.
Qed.

Lemma Axiomatization2SequentCalculus_orpSC:
  OrpSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_SC.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  + apply deduction_modus_ponens with x; auto.
    apply deduction_weaken0.
    apply orp_intros1.
  + apply deduction_modus_ponens with y; auto.
    apply deduction_weaken0.
    apply orp_intros2.
  + rewrite deduction_theorem in H2, H3 |- *.
    apply deduction_modus_ponens with (y --> z); auto.
    apply deduction_modus_ponens with (x --> z); auto.
    apply deduction_weaken0.
    apply orp_elim.
Qed.

Lemma Axiomatization2SequentCalculus_falsepSC:
  FalsepSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_SC.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  apply deduction_modus_ponens with FF; auto.
  apply deduction_weaken0.
  apply falsep_elim.
Qed.

Lemma Axiomatization2SequentCalculus_inegpSC:
  IntuitionisticNegpSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_SC.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  + rewrite deduction_theorem.
    apply deduction_modus_ponens with (~~ x); auto.
    apply deduction_weaken0.
    apply negp_unfold.
  + rewrite deduction_theorem in H2.
    apply deduction_modus_ponens with (x --> FF); auto.
    apply deduction_weaken0.
    apply negp_fold.
Qed.

Lemma Axiomatization2SequentCalculus_iffpSC:
  IffpSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_SC.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  + rewrite deduction_theorem in H2, H3.
    apply deduction_modus_ponens with (y --> x); auto.
    apply deduction_modus_ponens with (x --> y); auto.
    apply deduction_weaken0.
    apply iffp_intros.
  + rewrite deduction_theorem.
    apply deduction_modus_ponens with (x <--> y); auto.
    apply deduction_weaken0.
    apply iffp_elim1.
  + rewrite deduction_theorem.
    apply deduction_modus_ponens with (x <--> y); auto.
    apply deduction_weaken0.
    apply iffp_elim2.
Qed.

Lemma Axiomatization2SequentCalculus_truepSC:
  TruepSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_SC.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  apply deduction_weaken0.
  apply truep_intros.
Qed.

End Axiomatization2SequentCalculus.

Instance reg_Axiomatization2SequentCalculus_andpSC:
  RegisterClass P2D_reg (fun andpSC: unit => @Axiomatization2SequentCalculus_andpSC) 4.
Qed.

Instance reg_Axiomatization2SequentCalculus_orpSC:
  RegisterClass P2D_reg (fun orpSC: unit => @Axiomatization2SequentCalculus_orpSC) 5.
Qed.

Instance reg_Axiomatization2SequentCalculus_falsepSC:
  RegisterClass P2D_reg (fun falsepSC: unit => @Axiomatization2SequentCalculus_falsepSC) 6.
Qed.

Instance reg_Axiomatization2SequentCalculus_inegpSC:
  RegisterClass P2D_reg (fun inegpSC: unit => @Axiomatization2SequentCalculus_inegpSC) 7.
Qed.

Instance reg_Axiomatization2SequentCalculus_iffpSC:
  RegisterClass P2D_reg (fun iffpSC: unit => @Axiomatization2SequentCalculus_iffpSC) 8.
Qed.

Instance reg_Axiomatization2SequentCalculus_truepSC:
  RegisterClass P2D_reg (fun truepSC: unit => @Axiomatization2SequentCalculus_truepSC) 9.
Qed.
(**)

Section DerivableRulesFromAxiomatization1.

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
        {truepGamma: TruepAxiomatization L Gamma}.

Lemma solve_andp_intros: forall x y: expr,
  |-- x -> |-- y -> |-- x && y.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H, H0 |- *.
  pose proof deduction_andp_intros.
  apply deduction_andp_intros; auto.
Qed.

Lemma solve_andp_elim1: forall x y: expr,
  |-- x && y -> |-- x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H |- *.
  eapply deduction_andp_elim1; eauto.
Qed.

Lemma solve_andp_elim2: forall x y: expr,
  |-- x && y -> |-- y.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H |- *.
  eapply deduction_andp_elim2; eauto.
Qed.

Lemma solve_iffp_intros: forall x y: expr,
  |-- x --> y ->
  |-- y --> x ->
  |-- x <--> y.
Proof.
  intros.
  pose proof iffp_intros x y.
  pose proof modus_ponens _ _ H1 H.
  pose proof modus_ponens _ _ H2 H0.
  auto.
Qed.

Lemma solve_impp_elim_left: forall x y: expr,
  |-- y -> |-- x --> y.
Proof.
  intros.
  eapply modus_ponens.
  + apply axiom1.
  + auto.
Qed.

Lemma solve_orp_impp: forall x y z: expr,
  |-- x --> z -> |-- y --> z -> |-- x || y --> z.
Proof.
  intros.
  eapply modus_ponens; [| exact H0].
  eapply modus_ponens; [| exact H].
  apply orp_elim.
Qed.

Lemma solve_orp_intros1: forall x y: expr,
  |-- x -> |-- x || y.
Proof.
  intros.
  eapply modus_ponens; [| exact H].
  apply orp_intros1.
Qed.

Lemma solve_orp_intros2: forall x y: expr,
  |-- y -> |-- x || y.
Proof.
  intros.
  eapply modus_ponens; [| exact H].
  apply orp_intros2.
Qed.

Lemma solve_impp_andp: forall x y z: expr,
  |-- x --> y -> |-- x --> z -> |-- x --> y && z.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H, H0 |- *.
  rewrite <- deduction_theorem in H, H0 |- *.
  apply deduction_andp_intros; auto.
Qed.

Lemma double_negp_intros: forall (x: expr),
  |-- x --> ~~ ~~ x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply derivable_double_negp_intros.
Qed.

Lemma provable_iffp_refl: forall (x: expr),
  |-- x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply derivable_iffp_refl.
Qed.

Lemma contrapositivePP: forall (x y: expr),
  |-- (y --> x) --> ~~ x --> ~~ y.
Proof.
  intros.
  eapply modus_ponens; [apply provable_impp_arg_switch |].
  pose proof negp_unfold x. rewrite H.
  pose proof negp_fold y. rewrite <- H0.
  apply aux_minimun_theorem00.
Qed.

Lemma contrapositivePN: forall (x y: expr),
  |-- (y --> ~~ x) --> (x --> ~~ y).
Proof.
  intros.
  pose proof negp_unfold x. rewrite H.
  pose proof negp_fold y. rewrite <- H0.
  apply provable_impp_arg_switch.
Qed.

End DerivableRulesFromAxiomatization1.

Section DerivableRulesFromSequentCalculus2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndpLanguage L}
        {orpL: OrpLanguage L}
        {falsepL: FalsepLanguage L}
        {negpL: NegpLanguage L}
        {iffpL: IffpLanguage L}
        {truepL: TruepLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {andpSC: AndpSequentCalculus L Gamma}
        {orpSC: OrpSequentCalculus L Gamma}
        {falsepSC: FalsepSequentCalculus L Gamma}
        {inegpSC: IntuitionisticNegpSequentCalculus L Gamma}
        {iffpSC: IffpSequentCalculus L Gamma}
        {truepSC: TruepSequentCalculus L Gamma}.

Lemma deduction_contrapositivePP: forall Phi (x y: expr),
  Phi |-- y --> x ->
  Phi |-- ~~ x --> ~~ y.
Proof.
  AddAxiomatization.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply deduction_weaken0.
  apply contrapositivePP.
Qed.

Lemma deduction_contrapositivePN: forall Phi (x y: expr),
  Phi |-- y --> ~~ x ->
  Phi |-- x --> ~~ y.
Proof.
  AddAxiomatization.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply deduction_weaken0.
  apply contrapositivePN.
Qed.

End DerivableRulesFromSequentCalculus2.

Section DerivableRulesFromAxiomatization2.

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
        {truepGamma: TruepAxiomatization L Gamma}.

Lemma demorgan_orp_negp: forall (x y: expr),
  |-- ~~ x || ~~ y --> ~~ (x && y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  pose proof negp_fold (x && y).
  rewrite <- H.
  rewrite <- !deduction_theorem.
  apply (deduction_modus_ponens _ (~~ x || ~~ y)).
  + apply deduction_weaken1.
    apply derivable_assum1.
  + apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ x).
      *apply deduction_weaken1.
       eapply deduction_andp_elim1.
       apply derivable_assum1.
      *pose proof negp_unfold x.
       rewrite <- H0.
       apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ y).
      *apply deduction_weaken1.
       eapply deduction_andp_elim2.
       apply derivable_assum1.
      *pose proof negp_unfold y.
       rewrite <- H0.
       apply derivable_assum1.
Qed.

Lemma demorgan_negp_orp: forall (x y: expr),
  |-- ~~ (x || y) <--> (~~ x && ~~ y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_andp_intros. 
    - rewrite deduction_theorem.
      apply deduction_contrapositivePP.
      rewrite <- provable_derivable.
      apply orp_intros1.
    - rewrite deduction_theorem.
      apply deduction_contrapositivePP.
      rewrite <- provable_derivable.
      apply orp_intros2.
  +pose proof negp_fold (x || y). rewrite <- H.
   apply deduction_orp_elim'.
    - pose proof negp_unfold x. rewrite <- H0.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - pose proof negp_unfold y. rewrite <- H0.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma provable_truep: |-- TT.
Proof.
  apply truep_intros.
Qed.

Lemma andp_comm: forall (x y: expr),
  |-- x && y <--> y && x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_andp_intros.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
  + apply deduction_andp_intros.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
Qed.

Lemma andp_assoc: forall (x y z: expr),
  |-- x && y && z <--> x && (y && z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_andp_intros; [| apply deduction_andp_intros].
    - eapply deduction_andp_elim1.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
  + apply deduction_andp_intros; [apply deduction_andp_intros |].
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma orp_comm_impp: forall (x y: expr),
  |-- x || y --> y || x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_orp_elim.
  + apply deduction_orp_intros2.
    apply derivable_assum1.
  + apply deduction_orp_intros1.
    apply derivable_assum1.
Qed.

Lemma orp_comm: forall (x y: expr),
  |-- x || y <--> y || x.
Proof.
  intros.
  apply solve_iffp_intros;
  apply orp_comm_impp.
Qed.

Lemma orp_assoc: forall (x y z: expr),
  |-- x || y || z <--> x || (y || z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_orp_elim; [apply deduction_orp_elim |].
    - apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply deduction_orp_intros2.
      apply derivable_assum1.
  + apply deduction_orp_elim; [| apply deduction_orp_elim].
    - apply deduction_orp_intros1.
      apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros1.
      apply deduction_orp_intros2.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply derivable_assum1.
Qed.

Lemma andp_truep: forall (x: expr),
  |-- x && TT <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem.
  + apply derivable_andp_elim1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - apply derivable_assum1.
    - apply derivable_truep_intros.
Qed.

Lemma truep_andp: forall (x: expr),
  |-- TT && x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem.
  + apply derivable_andp_elim2.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - apply derivable_truep_intros.
    - apply derivable_assum1.
Qed.

Lemma falsep_orp: forall (x: expr),
  |-- FF || x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_orp_elim; rewrite deduction_theorem.
    - apply derivable_falsep_elim.
    - apply derivable_impp_refl.
  + rewrite deduction_theorem. apply derivable_orp_intros2.
Qed.

Lemma orp_falsep: forall (x: expr),
  |-- x || FF <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_orp_elim; rewrite deduction_theorem.
    - apply derivable_impp_refl.
    - apply derivable_falsep_elim.
  + rewrite deduction_theorem. apply derivable_orp_intros1.
Qed.

Lemma truep_impp: forall (x: expr),
  |-- (TT --> x) <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_modus_ponens with TT.
    - apply deduction_weaken0.
      apply provable_truep.
    - solve_assum.
  + rewrite deduction_theorem.
    apply derivable_axiom1.
Qed.

Lemma andp_dup: forall (x: expr),
  |-- x && x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem.
  + apply derivable_andp_elim1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros; apply derivable_assum1.
Qed.

Lemma orp_dup: forall (x: expr),
  |-- x || x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros.
  + apply deduction_orp_elim; apply derivable_assum1.
  + rewrite deduction_theorem. apply derivable_orp_intros1.
Qed.

Lemma impp_curry: forall (x y z: expr),
  |-- (x --> y --> z) --> (x && y --> z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with y.
  + apply deduction_andp_elim2 with x.
    solve_assum.
  + apply deduction_modus_ponens with x.
    - apply deduction_andp_elim1 with y.
      solve_assum.
    - solve_assum.
Qed.

Lemma impp_uncurry: forall (x y z: expr),
  |-- (x && y --> z) --> (x --> y --> z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with (x && y).
  + apply deduction_andp_intros;
    solve_assum.
  + solve_assum.
Qed.

Lemma impp_curry_uncurry: forall (x y z: expr),
  |-- (x --> y --> z) <--> (x && y --> z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + apply impp_curry.
  + apply impp_uncurry.
Qed.

Lemma negp_fold_unfold: forall (x: expr),
  |-- (~~x) <--> (x --> FF).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + apply negp_unfold.
  + apply negp_fold.
Qed.

Lemma iffp_fold_unfold: forall (x y: expr),
  |-- (x <--> y) <--> (x --> y) && (y --> x).
Proof.
AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + pose proof iffp_elim1 x y. pose proof iffp_elim2 x y.
    apply (solve_impp_andp _ _ _ H H0).
  + pose proof iffp_intros x y.
    pose proof impp_curry (x --> y) (y --> x) (x <--> y). rewrite H0 in H.
    apply H.
Qed.

End DerivableRulesFromAxiomatization2.


