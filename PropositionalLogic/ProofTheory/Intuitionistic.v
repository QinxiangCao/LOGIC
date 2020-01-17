Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class AndAxiomatization (L: Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} (Gamma: Provable L) := {
  andp_intros: forall x y, |-- x --> y --> x && y;
  andp_elim1: forall x y, |-- x && y --> x;
  andp_elim2: forall x y, |-- x && y --> y
}.

Class OrAxiomatization (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} (Gamma: Provable L) := {
  orp_intros1: forall x y, |-- x --> x || y;
  orp_intros2: forall x y, |-- y --> x || y;
  orp_elim: forall x y z, |-- (x --> z) --> (y --> z) --> (x || y --> z)
}.

Class FalseAxiomatization (L: Language) {minL: MinimumLanguage L} {falsepL: FalseLanguage L} (Gamma: Provable L) := {
  falsep_elim: forall x, |-- FF --> x
}.

Class IntuitionisticNegAxiomatization (L: Language) {minL: MinimumLanguage L} {falsepL: FalseLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  negp_unfold: forall x, |-- (~~x) --> (x --> FF);
  negp_fold: forall x, |-- (x --> FF) --> (~~x)
}.

Class IffAxiomatization (L: Language) {minL: MinimumLanguage L} {iffpL: IffLanguage L} (Gamma: Provable L) := {
  iffp_intros: forall x y, |-- (x --> y) --> (y --> x) --> (x <--> y);
  iffp_elim1: forall x y, |-- (x <--> y) --> (x --> y);
  iffp_elim2: forall x y, |-- (x <--> y) --> (y --> x)
}.

Class TrueAxiomatization (L: Language) {minL: MinimumLanguage L} {truepL: TrueLanguage L} (Gamma: Provable L) := {
  truep_intros: |-- TT
}.

Class AndSequentCalculus (L: Language) {andpL: AndLanguage L} (Gamma: Derivable L) := {
  deduction_andp_intros: forall Phi x y, Phi |-- x -> Phi |-- y -> Phi |-- x && y;
  deduction_andp_elim1: forall Phi x y, Phi |-- x && y -> Phi |-- x;
  deduction_andp_elim2: forall Phi x y, Phi |-- x && y -> Phi |-- y
}.

Class OrSequentCalculus (L: Language) {orpL: OrLanguage L} (Gamma: Derivable L) := {
  deduction_orp_intros1: forall Phi x y, Phi |-- x -> Phi |-- x || y;
  deduction_orp_intros2: forall Phi x y, Phi |-- y -> Phi |-- x || y;
  deduction_orp_elim: forall Phi x y z, Phi;; x |-- z -> Phi ;; y |-- z -> Phi;; x || y |-- z
}.

Class FalseSequentCalculus (L: Language) {falsepL: FalseLanguage L} (Gamma: Derivable L) := {
  deduction_falsep_elim: forall Phi x, Phi |-- FF -> Phi |-- x
}.


Class IntuitionisticNegSequentCalculus (L: Language) {falsepL: FalseLanguage L} {negpL: NegLanguage L} (Gamma: Derivable L) := {
  deduction_negp_unfold: forall Phi x, Phi |-- (~~x) -> Phi ;; x |-- FF;
  deduction_negp_fold: forall Phi x, Phi ;; x |-- FF -> Phi |-- (~~x)
}.

Class IffSequentCalculus (L: Language) {iffpL: IffLanguage L} (Gamma: Derivable L) := {
  deduction_iffp_intros: forall Phi x y, Phi ;; x |-- y -> Phi ;; y |-- x -> Phi |-- (x <--> y);
  deduction_iffp_elim1: forall Phi x y, Phi |-- (x <--> y) -> Phi ;; x |-- y;
  deduction_iffp_elim2: forall Phi x y, Phi |-- (x <--> y) -> Phi ;; y |-- x
}.

Class TrueSequentCalculus (L: Language) {truepL: TrueLanguage L} (Gamma: Derivable L) := {
  deduction_truep_intros: forall Phi, Phi |-- TT
}.

Class IterAndAxiomatization_left
      (L: Language)
      {truepL: TrueLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {iter_andp_L: IterAndLanguage L}
      (Gamma: Provable L) := {
      iter_andp_spec_left: forall (xs: list expr),
    |-- iter_andp xs <--> fold_left andp xs TT
}.

Class AndpDeduction (L: Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} (GammaD1: Derivable1 L) {minD:MinimumDeduction L GammaD1}:= {
  derivable1_andp_intros:forall x y z,derivable1 x y -> derivable1 x z -> derivable1 x (y && z);
  derivable1_andp_elim1:forall x y,derivable1 (x && y) x;
  derivable1_andp_elim2:forall x y,derivable1 (x && y) y
}.

Class ImppAndpAdjoint (L: Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} (GammaD1: Derivable1 L) {minD:MinimumDeduction L GammaD1}:= {
  derivable1_impp_andp_adjoint: forall x y z, derivable1 x (y-->z) <-> derivable1 (x && y) z
}.

Class OrpDeduction (L: Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} (GammaD1: Derivable1 L) {minD:MinimumDeduction L GammaD1}:= {
  derivable1_orp_intros1:forall x y,derivable1 x (x || y);
  derivable1_orp_intros2:forall x y,derivable1 y (x || y);
  derivable1_orp_elim:forall x y z,derivable1 x z -> derivable1 y z -> derivable1 (x || y) z
}.

Class FalsepDeduction (L: Language) {minL: MinimumLanguage L} {falsepL: FalseLanguage L} (GammaD1: Derivable1 L) {minD:MinimumDeduction L GammaD1}:= {
  derivable1_falsep_elim: forall x, derivable1 FF x
}.

Class NegpDeduction (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} {falsepL: FalseLanguage L} (GammaD1: Derivable1 L) {minD:MinimumDeduction L GammaD1}:= {
  derivable1_negp_unfold: forall x, derivable1 (~~x) (x --> FF);
  derivable1_negp_fold: forall x, derivable1 (x --> FF) (~~x)
}.

Class TruepDeduction (L: Language) {minL: MinimumLanguage L} {truepL: TrueLanguage L} (GammaD1: Derivable1 L) {minD:MinimumDeduction L GammaD1}:= {
  derivable1_truep_intros: forall x, derivable1 x TT
}.

Class IffDeduction (L: Language) {minL: MinimumLanguage L} {iffpL: IffLanguage L} (GammaD1: Derivable1 L) {minD:MinimumDeduction L GammaD1}:= {
  derivable1_iffp_intros: forall x y, derivable1 (x --> y) ((y --> x) --> (x <--> y));
  derivable1_iffp_elim1: forall x y, derivable1 (x <--> y) (x --> y);
  derivable1_iffp_elim2: forall x y, derivable1 (x <--> y) (y --> x)
}.

Class EquivAndp (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_andp_congr:forall x1 x2 y1 y2,x1 --||-- x2 -> y1 --||-- y2 -> 
  (x1 && y1) --||-- (x2 && y2);
  equiv_andp_comm:forall x y,x && y --||-- y && x;
  equiv_andp_assoc:forall x y z,x && y && z --||-- x && (y && z)
}.

Class EquivOrp (L:Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_orp_congr:forall x1 x2 y1 y2,  x1 --||-- x2 -> y1 --||-- y2 ->
  (x1 || y1) --||-- (x2 || y2);
  equiv_orp_comm:forall x y,x || y --||-- y || x;
  equiv_orp_assoc:forall x y z, x || y || z --||-- x || (y || z)
}.

Class EquivDistr (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {orpL: OrLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_andp_distr:forall x y z,x && (y || z) --||-- (x && y) || (x && z);
  equiv_orp_distr:forall x y z,x || (y && z) --||-- (x || y) && (x || z)
}.

Class EquivDeMorgen (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {orpL: OrLanguage L} {negp: NegLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_DeMorgen: forall x y,~~ (x || y) --||-- (~~ x) && (~~y)
}.

Class EquivFalsepAndp (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {falsepL: FalseLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_false_andp:forall x,x && FF --||-- FF
}.

Class EquivFalsepOrp (L:Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {falsepL: FalseLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_falsep_orp:forall x,x || FF --||-- x
}.

Class EquiveTruepAndp (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {truepL: TrueLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_truep_andp:forall x, x && TT --||-- x
}.

Class EquiveTruepOrp (L:Language) {minL: MinimumLanguage L} {orpL: OrLanguage L} {truepL: TrueLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_truep_orp:forall x, x || TT --||-- TT
}.

Class EquivIffp (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {iffpL: IffLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_iffp_intros: forall x y, (x --> y) && (y --> x) --||-- (x <--> y);
}.

Class EquivNegp (L:Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (GammaE:LogicEquiv L) {minE:MinimumEquiv L GammaE}:= {
  equiv_negp_intros:forall x y, x --||-- y -> ~~ x --||-- ~~ y
}.

Section DerivableRulesFromSequentCalculus1.

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
        {truepSC: TrueSequentCalculus L Gamma}.

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

Lemma deduction_negp_fold_unfold: forall (Phi: context) (x: expr),
  Phi |-- (~~ x) <-> Phi;;x |-- FF.
Proof.
  intros.
  split.
  apply deduction_negp_unfold.
  apply deduction_negp_fold.
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
        {minAX: MinimumAxiomatization L GammaP}.

Lemma SequentCalculus2Axiomatization_andpAX: AndAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_andp_intros.
  + apply derivable_andp_elim1.
  + apply derivable_andp_elim2.
Qed.

Lemma SequentCalculus2Axiomatization_orpAX: OrAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_orp_intros1.
  + apply derivable_orp_intros2.
  + apply derivable_orp_elim.
Qed.

Lemma SequentCalculus2Axiomatization_falsepAX: FalseAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  apply derivable_falsep_elim.
Qed.

Lemma SequentCalculus2Axiomatization_inegpAX: IntuitionisticNegAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_negp_unfold.
  + apply derivable_negp_fold.
Qed.

Lemma SequentCalculus2Axiomatization_iffpAX: IffAxiomatization L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_iffp_intros.
  + apply derivable_iffp_elim1.
  + apply derivable_iffp_elim2.
Qed.

Lemma SequentCalculus2Axiomatization_truepAX: TrueAxiomatization L GammaP.
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
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {AX: NormalAxiomatization L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}.

Lemma Axiomatization2SequentCalculus_andpSC:
  AndSequentCalculus L GammaD.
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
  OrSequentCalculus L GammaD.
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
  FalseSequentCalculus L GammaD.
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
  IntuitionisticNegSequentCalculus L GammaD.
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
  IffSequentCalculus L GammaD.
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
  TrueSequentCalculus L GammaD.
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
        {truepAX: TrueAxiomatization L Gamma}.

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

Lemma solve_iffp_elim1: forall x y: expr,
  |-- x <--> y ->
  |-- x --> y.
Proof.
  intros.
  pose proof iffp_elim1 x y.
  eapply modus_ponens; eauto.
Qed.

Lemma solve_iffp_elim2: forall x y: expr,
  |-- x <--> y ->
  |-- y --> x.
Proof.
  intros.
  pose proof iffp_elim2 x y.
  eapply modus_ponens; eauto.
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
  clear - minAX andpAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H, H0 |- *.
  rewrite <- deduction_theorem in H, H0 |- *.
  apply deduction_andp_intros; auto.
Qed.

Lemma impp_andp: forall (x y z: expr),
  |-- (x --> y) --> (x --> z) --> (x --> y && z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable. rewrite <- !deduction_theorem.
  apply deduction_andp_intros; rewrite deduction_theorem; solve_assum.
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
  intros.
  apply solve_iffp_intros;
  apply provable_impp_refl.
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
        {truepSC: TrueSequentCalculus L Gamma}.

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
        {truepAX: TrueAxiomatization L Gamma}.

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

Lemma andp_comm_impp: forall (x y: expr),
  |-- x && y --> y && x.
Proof.
  clear - minAX andpAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros.
  + eapply deduction_andp_elim2.
    apply derivable_assum1.
  + eapply deduction_andp_elim1.
    apply derivable_assum1.
Qed.

Lemma andp_comm: forall (x y: expr),
  |-- x && y <--> y && x.
Proof.
  intros.
  apply solve_iffp_intros;
  apply andp_comm_impp.
Qed.

Lemma andp_assoc_impp1: forall (x y z: expr),
  |-- x && y && z --> x && (y && z).
Proof.
  clear - minAX andpAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros; [| apply deduction_andp_intros].
  + eapply deduction_andp_elim1.
    eapply deduction_andp_elim1.
    apply derivable_assum1.
  + eapply deduction_andp_elim2.
    eapply deduction_andp_elim1.
    apply derivable_assum1.
  + eapply deduction_andp_elim2.
    apply derivable_assum1.
Qed.

Lemma andp_assoc_impp2: forall (x y z: expr),
  |-- x && (y && z) --> x && y && z.
Proof.
  clear - minAX andpAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros; [apply deduction_andp_intros |].
  + eapply deduction_andp_elim1.
    apply derivable_assum1.
  + eapply deduction_andp_elim1.
    eapply deduction_andp_elim2.
    apply derivable_assum1.
  + eapply deduction_andp_elim2.
    eapply deduction_andp_elim2.
    apply derivable_assum1.
Qed.

Lemma andp_assoc: forall (x y z: expr),
  |-- x && y && z <--> x && (y && z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + apply andp_assoc_impp1.
  + apply andp_assoc_impp2.
Qed.

Lemma orp_comm_impp: forall (x y: expr),
  |-- x || y --> y || x.
Proof.
  clear - minAX orpAX.
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

Lemma andp_truep1: forall (x: expr),
  |-- x && TT --> x.
Proof.
  intros.
  apply andp_elim1.
Qed.

Lemma andp_truep2: forall (x: expr),
  |-- x --> x && TT.
Proof.
  clear - minAX andpAX truepAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros.
  + apply derivable_assum1.
  + apply derivable_truep_intros.
Qed.

Lemma andp_truep: forall (x: expr),
  |-- x && TT <--> x.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply andp_truep1.
  + apply andp_truep2.
Qed.

Lemma truep_andp1: forall (x: expr),
  |-- TT && x --> x.
Proof.
  intros.
  apply andp_elim2.
Qed.

Lemma truep_andp2: forall (x: expr),
  |-- x --> TT && x.
Proof.
  clear - minAX andpAX truepAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_andp_intros.
  + apply derivable_truep_intros.
  + apply derivable_assum1.
Qed.

Lemma truep_andp: forall (x: expr),
  |-- TT && x <--> x.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply truep_andp1.
  + apply truep_andp2.
Qed.

Lemma falsep_orp_impp1: forall (x: expr),
  |-- FF || x --> x.
Proof.
  clear - minAX falsepAX orpAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable. rewrite <- deduction_theorem.
  apply deduction_orp_elim; rewrite deduction_theorem.
  + apply derivable_falsep_elim.
  + apply derivable_impp_refl.
Qed.

Lemma falsep_orp_impp2: forall (x: expr),
  |-- x --> FF || x.
Proof.
  clear - minAX falsepAX orpAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable. rewrite <- deduction_theorem.
  rewrite deduction_theorem. apply derivable_orp_intros2.
Qed.

Lemma falsep_orp: forall (x: expr),
  |-- FF || x <--> x.
Proof.
  clear - minAX falsepAX orpAX iffpAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + apply falsep_orp_impp1.
  + apply falsep_orp_impp2.
Qed.

Lemma orp_falsep: forall (x: expr),
  |-- x || FF <--> x.
Proof.
  clear - minAX falsepAX orpAX iffpAX.
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
  clear - minAX andpAX.
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
  clear - minAX andpAX.
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
  intros.
  apply solve_iffp_intros.
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

Section DerivableRulesFromLogicEquiv.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {iffpL: IffLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {NE:NormalEquiv L GammaP GammaE}
        {minAX: MinimumAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}.

Lemma equiv_iffp : forall x y,
  x --||-- y <-> |-- x <--> y.
Proof.
  intros.
  split.
  -intros. apply equiv_provable in H. destruct H.
   pose proof iffp_intros x y.
   pose proof modus_ponens _ _ H1 H.
   pose proof modus_ponens _ _ H2 H0.
   auto.
  -intros.
   apply equiv_provable.
   split.
     *pose proof iffp_elim1 x y.
      pose proof modus_ponens _ _ H0 H;auto.
     *pose proof iffp_elim2 x y.
      pose proof modus_ponens _ _ H0 H;auto.
  Qed.

End DerivableRulesFromLogicEquiv.

Lemma derivable1_distr
       {L: Language}
       {minL: MinimumLanguage L}
       {andpL: AndLanguage L}
       {orpL: OrLanguage L}
       {GammaD1: Derivable1 L}
       {minD: MinimumDeduction L GammaD1}
       {andpD: AndpDeduction L GammaD1}
       {orpD: OrpDeduction L GammaD1}
       {adjD:ImppAndpAdjoint L GammaD1}
       {BD: BasicDeduction L GammaD1}
      :forall P x y z,
  derivable1 (P && (x || y)) z <-> derivable1 ((P && x) || (P && y)) z.
Proof.
   split.
   -intros.
    apply derivable1_orp_elim.
     *apply derivable1_impp_andp_adjoint in H.
      pose proof derivable1_andp_elim1 P x.
      pose proof derivable1_andp_elim2 P x.
      pose proof derivable1_orp_intros1 x y.
      pose proof deduction1_trans _ _ _ H1 H2;clear H1 H2.
      pose proof deduction1_trans _ _ _ H0 H;clear H0 H.
      AddAxiomatization.
      rewrite derivable1_provable in H3, H1 |- *.
      pose proof axiom2 (P && x) (x || y) z.
      pose proof modus_ponens _ _ H H1.
      pose proof modus_ponens _ _ H0 H3;auto.
     *apply derivable1_impp_andp_adjoint in H.
      pose proof derivable1_andp_elim1 P y.
      pose proof derivable1_andp_elim2 P y.
      pose proof derivable1_orp_intros2 x y.
      pose proof deduction1_trans _ _ _ H1 H2;clear H1 H2.
      pose proof deduction1_trans _ _ _ H0 H;clear H0 H.
      AddAxiomatization.
      rewrite derivable1_provable in H3, H1 |- *.
      pose proof axiom2 (P && y) (x || y) z.
      pose proof modus_ponens _ _ H H1.
      pose proof modus_ponens _ _ H0 H3;auto.
   -intros.
    apply derivable1_impp_andp_adjoint.
    pose proof derivable1_orp_intros1 (P && x) (P && y).
    pose proof derivable1_orp_intros2 (P && x) (P && y).
    pose proof deduction1_trans _ _ _ H0 H.
    pose proof deduction1_trans _ _ _ H1 H.
    apply derivable1_impp_andp_adjoint in H2.
    apply derivable1_impp_andp_adjoint in H3.
    apply deduction_exchange. apply deduction_exchange in H2. 
    apply deduction_exchange in H3.
    pose proof derivable1_orp_elim _ _ _ H2 H3;auto.
  Qed.

Section Derivabel1ToAxiomatization.

Import Derivable1.
Local Open Scope Derivable1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {ND: NormalDeduction L GammaP GammaD1}
        {minD: MinimumDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Section Deduction2Axiomatization1.

Context {andpL: AndLanguage L}
        {andpD: AndpDeduction L GammaD1}
        {adjD: ImppAndpAdjoint L GammaD1}.

Lemma Deduction2Axiomatization_andpAX : AndAxiomatization L GammaP.
Proof.
  constructor.
  -intros.
   apply derivable1_provable.
   apply derivable1_impp_andp_adjoint. apply deduction1_refl.
  -intros.
   apply derivable1_provable.
   apply derivable1_andp_elim1.
  -intros.
   apply derivable1_provable.
   apply derivable1_andp_elim2.
  Qed.

Context {orpL: OrLanguage L}
        {orpD: OrpDeduction L GammaD1}.

Lemma Deduction2Axiomatization_orpAX: OrAxiomatization L GammaP.
Proof.
  constructor.
  -intros.
   apply derivable1_provable.
   apply derivable1_orp_intros1.
  -intros.
   apply derivable1_provable.
   apply derivable1_orp_intros2.
  -intros.
   apply derivable1_provable.
   apply derivable1_impp_andp_adjoint.
   apply derivable1_impp_andp_adjoint.
   apply derivable1_distr.
   apply derivable1_orp_elim.
     *apply derivable1_impp_andp_adjoint.
      apply derivable1_andp_elim1.
     *apply derivable1_impp_andp_adjoint.
      apply derivable1_andp_elim2.
    Qed.

End Deduction2Axiomatization1.

Section Deduction2Axiomatization_falsepAX.

Context {falsepL: FalseLanguage L}
        {falsepD: FalsepDeduction L GammaD1}.

Lemma Deduction2Axiomatization_falsepAX: FalseAxiomatization L GammaP.
  constructor.
   intros.
   apply derivable1_provable.
   apply derivable1_falsep_elim.
   Qed.

End Deduction2Axiomatization_falsepAX.

Section Deduction2Axiomatization_truepAX.

Context {truepL: TrueLanguage L}
        {truepD: TruepDeduction L GammaD1}
        {PD: Provable_Derivable1 L GammaP GammaD1}.

Lemma Deduction2Axiomatization_truepAX: TrueAxiomatization L GammaP.
Proof.
  constructor.
  pose proof derivable1_truep_intros (TT --> TT).
  apply provable_derivable1;auto.
  Qed.

End Deduction2Axiomatization_truepAX.

Section Deduction2Axiomatization_negpAX.

Context {negpL: NegLanguage L}
        {falsepL: FalseLanguage L}
        {negpD: NegpDeduction L GammaD1}.

Lemma Deduction2Axiomatization_negpAX: IntuitionisticNegAxiomatization L GammaP.
Proof.
  constructor.
  -intros.
   apply derivable1_provable.
   apply derivable1_negp_unfold.
  -intros.
   apply derivable1_provable.
   apply derivable1_negp_fold.
   Qed.

End Deduction2Axiomatization_negpAX.

Section Deduction2Axiomatization_iffpAX.

Context {iffpL: IffLanguage L}
        {iffpD: IffDeduction L GammaD1}.

Lemma Deduction2Axiomatization_iffpAX: IffAxiomatization L GammaP.
Proof.
  constructor.
  -intros.
   apply derivable1_provable.
   apply derivable1_iffp_intros.
  -intros.
   apply derivable1_provable.
   apply derivable1_iffp_elim1.
  -intros.
   apply derivable1_provable.
   apply derivable1_iffp_elim2.
   Qed.

End Deduction2Axiomatization_iffpAX.

End Derivabel1ToAxiomatization.

Instance reg_Deduction2Axiomatization_andpAX:
  RegisterClass D1ToP_reg (fun anpAX:unit => @Deduction2Axiomatization_andpAX) 4.
Qed.

Instance reg_Deduction2Axiomatization_orpAX:
  RegisterClass D1ToP_reg (fun orpAX:unit => @Deduction2Axiomatization_orpAX) 13.
Qed.

Instance reg_Deduction2Axiomatization_falsepAX:
  RegisterClass D1ToP_reg (fun falsepAX:unit => @Deduction2Axiomatization_falsepAX) 14.
Qed.

Instance reg_Deduction2Axiomatization_truepAX:
  RegisterClass D1ToP_reg (fun truepAX:unit => @Deduction2Axiomatization_truepAX) 15.
Qed.

Instance reg_Deduction2Axiomatization_negpAX:
  RegisterClass D1ToP_reg (fun negpAX:unit => @Deduction2Axiomatization_negpAX) 16.
Qed.

Instance reg_Deduction2Axiomatization_iffpAX:
  RegisterClass D1ToP_reg (fun iffpAX:unit => @Deduction2Axiomatization_iffpAX) 17.
Qed.
