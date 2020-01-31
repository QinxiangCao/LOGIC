Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
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

Class IntuitionisticNegAxiomatization (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (Gamma: Provable L) := {
  contrapositivePP: forall x y, |-- (y --> x) --> ~~ x --> ~~ y;
  contradiction_elim1: forall x y, |-- ~~ x --> x --> y;
  double_negp_intros: forall x, |-- x --> ~~ (~~ x);
}.

Class IffAxiomatization (L: Language) {minL: MinimumLanguage L} {iffpL: IffLanguage L} (Gamma: Provable L) := {
  iffp_intros: forall x y, |-- (x --> y) --> (y --> x) --> (x <--> y);
  iffp_elim1: forall x y, |-- (x <--> y) --> (x --> y);
  iffp_elim2: forall x y, |-- (x <--> y) --> (y --> x)
}.

Class TrueAxiomatization (L: Language) {truepL: TrueLanguage L} (Gamma: Provable L) := {
  truep_intros: |-- TT
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

Class AndSequentCalculus (L: Language) {andpL: AndLanguage L} (Gamma: Derivable L) := {
  deduction_andp_intros: forall Phi x y, Phi |--- x -> Phi |--- y -> Phi |--- x && y;
  deduction_andp_elim1: forall Phi x y, Phi |--- x && y -> Phi |--- x;
  deduction_andp_elim2: forall Phi x y, Phi |--- x && y -> Phi |--- y
}.

Class OrSequentCalculus (L: Language) {orpL: OrLanguage L} (Gamma: Derivable L) := {
  deduction_orp_intros1: forall Phi x y, Phi |--- x -> Phi |--- x || y;
  deduction_orp_intros2: forall Phi x y, Phi |--- y -> Phi |--- x || y;
  deduction_orp_elim: forall Phi x y z, Phi;; x |--- z -> Phi ;; y |--- z -> Phi;; x || y |--- z
}.

Class FalseSequentCalculus (L: Language) {falsepL: FalseLanguage L} (Gamma: Derivable L) := {
  deduction_falsep_elim: forall Phi x, Phi |--- FF -> Phi |--- x
}.


Class IntuitionisticNegSequentCalculus (L: Language) {negpL: NegLanguage L} (Gamma: Derivable L) := {
  deduction_contrapositivePP: forall Phi x y, Phi;; y |--- x -> Phi;; ~~x |--- ~~ y;
  deduction_contradiction_elim: forall Phi x y, Phi |--- x -> Phi |--- ~~ x -> Phi |--- y;
  deduction_double_negp_intros: forall Phi x, Phi |--- x -> Phi |--- ~~ (~~ x)
}.

Class IffSequentCalculus (L: Language) {iffpL: IffLanguage L} (Gamma: Derivable L) := {
  deduction_iffp_intros: forall Phi x y, Phi ;; x |--- y -> Phi ;; y |--- x -> Phi |--- (x <--> y);
  deduction_iffp_elim1: forall Phi x y, Phi |--- (x <--> y) -> Phi ;; x |--- y;
  deduction_iffp_elim2: forall Phi x y, Phi |--- (x <--> y) -> Phi ;; y |--- x
}.

Class TrueSequentCalculus (L: Language) {truepL: TrueLanguage L} (Gamma: Derivable L) := {
  deduction_truep_intros: forall Phi, Phi |--- TT
}.

Class AndDeduction (L: Language) {andpL: AndLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_andp_intros:forall x y z,derivable1 x y -> derivable1 x z -> derivable1 x (y && z);
  derivable1_andp_elim1: forall x y, x && y |-- x;
  derivable1_andp_elim2: forall x y, x && y |-- y
}.

Class ImpAndAdjointDeduction (L: Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_impp_andp_adjoint: forall x y z,
    x |-- y --> z <-> x && y |-- z
}.

Class OrDeduction (L: Language) {orpL: OrLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_orp_intros1: forall x y, x |-- x || y;
  derivable1_orp_intros2: forall x y, y |-- x || y;
  derivable1_orp_elim: forall x y z, x |-- z -> y |-- z -> x || y |-- z
}.

Class FalseDeduction (L: Language) {falsepL: FalseLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_falsep_elim: forall x, FF |-- x
}.

Class IntuitionisticNegDeduction (L: Language) {negpL: NegLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_contrapositivePP': forall x y, y |-- x -> ~~ x |-- ~~ y;
  derivable1_contradiction_elim: forall x y z, z |-- x -> z |-- ~~ x -> z |-- y;
  derivable1_double_negp_intros: forall x, x |-- ~~ (~~ x)
}.

Class ImpNegDeduction (L: Language) {minL: MinimumLanguage L} {negpL: NegLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_contrapositivePP: forall x y, y --> x |-- ~~ x --> ~~ y;
  derivable1_contradiction_elim': forall x y, ~~ x |-- x --> y
}.

Class TrueDeduction (L: Language) {truepL: TrueLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_truep_intros: forall x, x |-- TT
}.

Class IffDeduction (L: Language) {minL: MinimumLanguage L} {iffpL: IffLanguage L} (GammaD1: Derivable1 L) := {
  derivable1_iffp_intros: forall x y, x --> y |-- (y --> x) --> (x <--> y);
  derivable1_iffp_elim1: forall x y, x <--> y |-- x --> y;
  derivable1_iffp_elim2: forall x y, x <--> y |-- y --> x
}.

Class ImpLogicEquiv (L:Language) {minL:MinimumLanguage L} (Gamma:LogicEquiv L) := {
  logic_equiv_impp:forall x1 x2 y1 y2, x1 --||-- x2 -> y1 --||-- y2 -> 
  (x1 --> y1) --||-- (x2 --> y2)
}.

Class AndLogicEquiv (L:Language) {andpL: AndLanguage L} (GammaE:LogicEquiv L) := {
  logic_equiv_andp_congr:forall x1 x2 y1 y2,x1 --||-- x2 -> y1 --||-- y2 -> 
  (x1 && y1) --||-- (x2 && y2);
  logic_equiv_andp_comm:forall x y,x && y --||-- y && x;
  logic_equiv_andp_assoc:forall x y z,x && y && z --||-- x && (y && z)
}.

Class OrLogicEquiv (L:Language) {orpL: OrLanguage L} (GammaE:LogicEquiv L):= {
  logic_equiv_orp_congr:forall x1 x2 y1 y2,  x1 --||-- x2 -> y1 --||-- y2 ->
  (x1 || y1) --||-- (x2 || y2);
  logic_equiv_orp_comm:forall x y,x || y --||-- y || x;
  logic_equiv_orp_assoc:forall x y z, x || y || z --||-- x || (y || z)
}.

Class DistrLogicEquiv (L:Language) {andpL: AndLanguage L} {orpL: OrLanguage L} (GammaE:LogicEquiv L):= {
  logic_equiv_andp_distr:forall x y z,x && (y || z) --||-- (x && y) || (x && z);
  logic_equiv_orp_distr:forall x y z,x || (y && z) --||-- (x || y) && (x || z)
}.

Class DeMorgenLogicEquiv (L:Language) {andpL: AndLanguage L} {orpL: OrLanguage L} {negp: NegLanguage L} (GammaE:LogicEquiv L):= {
  logic_equiv_DeMorgen: forall x y,~~ (x || y) --||-- (~~ x) && (~~y)
}.

Class FalseAndLogicEquiv (L:Language) {andpL: AndLanguage L} {falsepL: FalseLanguage L} (GammaE:LogicEquiv L) := {
  logic_equiv_false_andp:forall x,x && FF --||-- FF
}.

Class FalseOrLogicEquiv (L:Language) {orpL: OrLanguage L} {falsepL: FalseLanguage L} (GammaE:LogicEquiv L) := {
  logic_equiv_falsep_orp:forall x,x || FF --||-- x
}.

Class TrueAndLogicEquiv (L:Language) {andpL: AndLanguage L} {truepL: TrueLanguage L} (GammaE:LogicEquiv L):= {
  logic_equiv_truep_andp:forall x, x && TT --||-- x
}.

Class TrueOrEquiv (L:Language) {orpL: OrLanguage L} {truepL: TrueLanguage L} (GammaE:LogicEquiv L):= {
  logic_equiv_truep_orp:forall x, x || TT --||-- TT
}.

Class IffLogicEquiv (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {iffpL: IffLanguage L} (GammaE:LogicEquiv L):= {
  logic_equiv_iffp_intros: forall x y, (x --> y) && (y --> x) --||-- (x <--> y);
}.

Class NegLogicEquiv (L:Language) {negpL: NegLanguage L} (GammaE:LogicEquiv L):= {
  logic_equiv_negp_intros:forall x y, x --||-- y -> ~~ x --||-- ~~ y
}.

Section DerivableRulesFromDeduction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {GammaD1: Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}.

Lemma derivable1_andp_comm: forall (x y: expr),
  x && y |-- y && x.
Proof.
  intros.
  apply derivable1_andp_intros.
  + apply derivable1_andp_elim2.
  + apply derivable1_andp_elim1.
Qed.

Lemma derivable1_andp_assoc: forall (x y z: expr),
  x && y && z |-- x && (y && z).
Proof.
  intros.
  repeat apply derivable1_andp_intros.
  + rewrite derivable1_andp_elim1.
    apply derivable1_andp_elim1.
  + rewrite derivable1_andp_elim1.
    apply derivable1_andp_elim2.
  + apply derivable1_andp_elim2.
Qed.

Context {adjD: ImpAndAdjointDeduction L GammaD1}.

Lemma derivable1_modus_ponens:
  forall (x y: expr), (x --> y) && x |-- y.
Proof.
  intros.
  rewrite <- derivable1_impp_andp_adjoint.
  reflexivity.
Qed.

Lemma derivable1_impp_mono:
  forall (x1 y1 x2 y2: expr),
    y1 |-- x1 -> x2 |-- y2 -> x1 --> x2 |-- y1 --> y2.
Proof.
  intros.
  rewrite derivable1_impp_andp_adjoint.
  rewrite <- H0.
  rewrite derivable1_andp_comm.
  rewrite <- derivable1_impp_andp_adjoint.
  rewrite H.
  rewrite derivable1_impp_andp_adjoint.
  rewrite derivable1_andp_comm.
  apply derivable1_modus_ponens.
Qed.

Lemma derivable1_base: forall x y,
  x |-- y --> y.
Proof.
  intros.
  rewrite derivable1_impp_andp_adjoint.
  apply derivable1_andp_elim2.
Qed.

Lemma derivable1_orp_elim'
      {orpL: OrLanguage L}
      {orpD: OrDeduction L GammaD1}:
  forall x y z, (x --> z) && (y --> z) |-- x || y --> z.
Proof.
  intros.
  apply derivable1_impp_andp_adjoint.
  rewrite derivable1_andp_comm.
  apply derivable1_impp_andp_adjoint.
  apply derivable1_orp_elim.
  + apply derivable1_impp_andp_adjoint.
    rewrite derivable1_andp_comm.
    apply derivable1_impp_andp_adjoint.
    apply derivable1_andp_elim1.
  + apply derivable1_impp_andp_adjoint.
    rewrite derivable1_andp_comm.
    apply derivable1_impp_andp_adjoint.
    apply derivable1_andp_elim2.
Qed.

Lemma derivable1_negp_unfold
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}
      {falsepD: FalseDeduction L GammaD1}
      {inegpD: IntuitionisticNegDeduction L GammaD1}:
  forall x, ~~ x |-- x --> FF.
Proof.
  intros.
  apply derivable1_impp_andp_adjoint.
  apply derivable1_contradiction_elim with x.
  + apply derivable1_andp_elim2.
  + apply derivable1_andp_elim1.
Qed.

Lemma derivable1_negp_fold
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}
      {falsepD: FalseDeduction L GammaD1}
      {inegpD: IntuitionisticNegDeduction L GammaD1}
      {impp_negp_D: ImpNegDeduction L GammaD1}:
  forall x, x --> FF |-- ~~ x.
Proof.
  intros.
  rewrite (derivable1_contrapositivePP FF x).
  assert (~~ FF --> ~~ x |-- (~~ FF --> ~~ x) && ~~ FF).
  + apply derivable1_andp_intros.
    - apply derivable1_refl.
    - rewrite derivable1_double_negp_intros.
      apply derivable1_contrapositivePP'.
      apply derivable1_falsep_elim.
  + rewrite H.
    apply derivable1_impp_andp_adjoint.
    apply derivable1_refl.
Qed.

End DerivableRulesFromDeduction.

Section Deduction2Axiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaPD1: ProvableDerivable1 L GammaP GammaD1}
        {bD: BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}.

Lemma Deduction2Axiomatization_GammaD1P: Derivable1Provable L GammaP GammaD1.
Proof.
  constructor.
  intros. split.
  + intros.
    apply provable_derivable1.
    apply derivable1_impp_andp_adjoint.
    rewrite derivable1_andp_elim2.
    apply H.
  + intros.
    apply provable_derivable1 in H.
    apply derivable1_impp_andp_adjoint in H.
    rewrite <- H.
    apply derivable1_andp_intros.
    - apply derivable1_base.
    - reflexivity.
Qed.

Lemma Deduction2Axiomatization_minAX : MinimumAxiomatization L GammaP.
Proof.
  constructor.
  + intros.
    rewrite provable_derivable1 in H, H0 |- *.
    rewrite derivable1_impp_andp_adjoint in H.
    rewrite <- H at 3.
    apply derivable1_andp_intros.
    - apply derivable1_base.
    - rewrite <- H0.
      apply derivable1_base.
  + intros.
    rewrite provable_derivable1.
    rewrite ! derivable1_impp_andp_adjoint.
    rewrite derivable1_andp_elim1.
    apply derivable1_andp_elim2.
  + intros.
    rewrite provable_derivable1.
    rewrite derivable1_impp_andp_adjoint.
    rewrite derivable1_andp_elim2.
    rewrite ! derivable1_impp_andp_adjoint.
    rewrite <- (derivable1_modus_ponens y z) at 2.
    apply derivable1_andp_intros.
    - rewrite <- derivable1_impp_andp_adjoint.
      apply derivable1_andp_elim1.
    - rewrite <- derivable1_impp_andp_adjoint.
      apply derivable1_andp_elim2.
Qed.

Context {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma Deduction2Axiomatization_andpAX : AndAxiomatization L GammaP.
Proof.
  constructor.
  -intros.
   apply derivable1_provable.
   apply derivable1_impp_andp_adjoint. apply derivable1_refl.
  -intros.
   apply derivable1_provable.
   apply derivable1_andp_elim1.
  -intros.
   apply derivable1_provable.
   apply derivable1_andp_elim2.
  Qed.

Section Deduction2Axiomatization_orpAX.

Context {orpL: OrLanguage L}
        {orpD: OrDeduction L GammaD1}.

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
   apply derivable1_orp_elim'.
Qed.

End Deduction2Axiomatization_orpAX.

Section Deduction2Axiomatization_falsepAX.

Context {falsepL: FalseLanguage L}
        {falsepD: FalseDeduction L GammaD1}.

Lemma Deduction2Axiomatization_falsepAX: FalseAxiomatization L GammaP.
  constructor.
   intros.
   apply derivable1_provable.
   apply derivable1_falsep_elim.
   Qed.

End Deduction2Axiomatization_falsepAX.

Section Deduction2Axiomatization_truepAX.

Context {truepL: TrueLanguage L}
        {truepD: TrueDeduction L GammaD1}.

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
        {inegpD: IntuitionisticNegDeduction L GammaD1}
        {impp_negp_D: ImpNegDeduction L GammaD1}.

Lemma Deduction2Axiomatization_inegpAX: IntuitionisticNegAxiomatization L GammaP.
Proof.
  constructor.
  + intros.
    apply derivable1_provable.
    apply derivable1_contrapositivePP.
  + intros.
    apply derivable1_provable.
    apply derivable1_contradiction_elim'.
  + intros.
    apply derivable1_provable.
    apply derivable1_double_negp_intros.
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

End Deduction2Axiomatization.

Instance reg_Deduction2Axiomatization_GammaD1P:
  RegisterClass D12P_reg (fun ND: unit => @Deduction2Axiomatization_GammaD1P) 0.
Qed.

Instance reg_Deduction2Axiomatization_minAX:
  RegisterClass D12P_reg (fun minAX: unit => @Deduction2Axiomatization_minAX) 1.
Qed.

Instance reg_Deduction2Axiomatization_andpAX:
  RegisterClass D12P_reg (fun anpAX:unit => @Deduction2Axiomatization_andpAX) 2.
Qed.

Instance reg_Deduction2Axiomatization_orpAX:
  RegisterClass D12P_reg (fun orpAX:unit => @Deduction2Axiomatization_orpAX) 3.
Qed.

Instance reg_Deduction2Axiomatization_falsepAX:
  RegisterClass D12P_reg (fun falsepAX:unit => @Deduction2Axiomatization_falsepAX) 4.
Qed.

Instance reg_Deduction2Axiomatization_truepAX:
  RegisterClass D12P_reg (fun truepAX:unit => @Deduction2Axiomatization_truepAX) 5.
Qed.

Instance reg_Deduction2Axiomatization_negpAX:
  RegisterClass D12P_reg (fun negpAX:unit => @Deduction2Axiomatization_inegpAX) 6.
Qed.

Instance reg_Deduction2Axiomatization_iffpAX:
  RegisterClass D12P_reg (fun iffpAX:unit => @Deduction2Axiomatization_iffpAX) 7.
Qed.

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
  Phi |--- x --> y --> x && y.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_andp_intros; solve_assum.
Qed.

Lemma derivable_andp_elim1: forall (Phi: context) (x y: expr),
  Phi |--- x && y --> x.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_elim1 with y; solve_assum.
Qed.

Lemma derivable_andp_elim2: forall (Phi: context) (x y: expr),
  Phi |--- x && y --> y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_elim2 with x; solve_assum.
Qed.

Lemma derivable_orp_intros1: forall (Phi: context) (x y: expr),
  Phi |--- x --> x || y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_orp_intros1; solve_assum.
Qed.

Lemma derivable_orp_intros2: forall (Phi: context) (x y: expr),
  Phi |--- y --> x || y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_orp_intros2; solve_assum.
Qed.

Lemma derivable_orp_elim: forall (Phi: context) (x y z: expr),
  Phi |--- (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_orp_elim.
  + rewrite deduction_theorem; solve_assum.
  + rewrite deduction_theorem; solve_assum.
Qed.

Lemma derivable_falsep_elim: forall (Phi: context) (x: expr),
  Phi |--- FF --> x.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_falsep_elim; solve_assum.
Qed.

Lemma derivable_contrapositivePP: forall (Phi: context) (x y: expr),
  Phi |--- (y --> x) --> ~~ x --> ~~ y.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_contrapositivePP.
  rewrite deduction_theorem; solve_assum.
Qed.

Lemma derivable_contradiction_elim1: forall (Phi: context) (x y: expr),
  Phi |--- ~~ x --> x --> y.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_contradiction_elim with x; solve_assum.
Qed.

Lemma derivable_double_negp_intros: forall (Phi: context) (x: expr),
  Phi |--- x --> ~~ ~~ x.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_double_negp_intros; solve_assum.
Qed.

Lemma derivable_iffp_intros: forall (Phi: context) (x y: expr),
  Phi |--- (x --> y) --> (y --> x) --> (x <--> y).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_iffp_intros.
  +rewrite deduction_theorem; solve_assum.
  +rewrite deduction_theorem; solve_assum.
Qed.

Lemma derivable_iffp_elim1: forall (Phi: context) (x y: expr),
  Phi |--- (x <--> y) --> (x --> y).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_iffp_elim1; solve_assum.
Qed.

Lemma derivable_iffp_elim2: forall (Phi: context) (x y: expr),
  Phi |--- (x <--> y) --> (y --> x).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_iffp_elim2; solve_assum.
Qed.

Lemma derivable_truep_intros: forall (Phi: context),
  Phi |--- TT.
Proof.
  intros.
  apply deduction_truep_intros; solve_assum.
Qed.

Lemma deduction_negp_unfold: forall Phi x, Phi |--- (~~x) -> Phi ;; x |--- FF.
Proof.
  intros.
  apply deduction_contradiction_elim with x; solve_assum.
Qed.

Lemma deduction_negp_fold: forall Phi x, Phi ;; x |--- FF -> Phi |--- (~~x).
Proof.
  clear - falsepSC inegpSC minSC bSC.
  intros.
  apply deduction_contrapositivePP in H.
  eapply deduction_subst1; [| exact H].
  apply deduction_subst1 with (~~ (~~ (FF --> FF))).
  + apply deduction_double_negp_intros.
    rewrite <- deduction_theorem; solve_assum.
  + apply deduction_contrapositivePP.
    apply deduction_falsep_elim; solve_assum.
Qed.

Lemma deduction_negp_fold_unfold: forall (Phi: context) (x: expr),
  Phi |--- (~~ x) <-> Phi;;x |--- FF.
Proof.
  intros.
  split.
  apply deduction_negp_unfold.
  apply deduction_negp_fold.
Qed.

Lemma deduction_orp_elim': forall (Phi: context) (x y z: expr),
  Phi |--- x --> z ->
  Phi |--- y --> z ->
  Phi |--- x || y --> z.
Proof.
  intros.
  rewrite <- deduction_theorem in H, H0 |- *.
  apply deduction_orp_elim; auto.
Qed.

Lemma derivable_contradiction_elim2: forall (Phi: context) (x y: expr),
  Phi |--- x --> ~~ x --> y.
Proof.
  clear - bSC minSC inegpSC.
  AddAxiomatization.
  intros.
  rewrite <- provable_impp_arg_switch.
  apply derivable_contradiction_elim1.
Qed.

Lemma derivable_iffp_refl: forall (Phi: context) (x: expr),
  Phi |--- x <--> x.
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
        {GammaPD: ProvableDerivable L GammaP GammaD}
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
  + apply derivable_contrapositivePP.
  + apply derivable_contradiction_elim1.
  + apply derivable_double_negp_intros.
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
        {GammaDP: DerivableProvable L GammaP GammaD}
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
  pose proof Axiomatization2SequentCalculus_GammaPD.
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
  pose proof Axiomatization2SequentCalculus_GammaPD.
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
  pose proof Axiomatization2SequentCalculus_GammaPD.
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
  pose proof Axiomatization2SequentCalculus_GammaPD.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  + rewrite deduction_theorem in H2 |- *.
    eapply deduction_modus_ponens; [exact H2 |].
    apply deduction_weaken0.
    apply contrapositivePP.
  + eapply deduction_modus_ponens; [exact H2 |].
    eapply deduction_modus_ponens; [exact H3 |].
    apply deduction_weaken0.
    apply contradiction_elim1.
  + eapply deduction_modus_ponens; [exact H2 |].
    apply deduction_weaken0.
    apply double_negp_intros.
Qed.

Lemma Axiomatization2SequentCalculus_iffpSC:
  IffSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_GammaPD.
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
  pose proof Axiomatization2SequentCalculus_GammaPD.
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

Lemma provable_iffp_refl: forall (x: expr),
  |-- x <--> x.
Proof.
  intros.
  apply solve_iffp_intros;
  apply provable_impp_refl.
Qed.

Lemma contradiction_elim2: forall x y, |-- x --> ~~ x --> y.
Proof.
  intros.
  rewrite <- provable_impp_arg_switch.
  apply contradiction_elim1.
Qed.

Lemma negp_unfold: forall x, |-- (~~x) --> (x --> FF).
Proof.
  intros.
  apply contradiction_elim1.
Qed.

Lemma negp_aux_rule: forall x y, |-- y -> |-- (x --> ~~ y) --> (~~x).
Proof.
  intros.
  rewrite (contrapositivePP (~~ y) x).
  eapply modus_ponens.
  + apply aux_minimun_theorem02.
  + rewrite <- double_negp_intros.
    auto.
Qed.

Lemma negp_fold: forall x, |-- (x --> FF) --> (~~x).
Proof.
  intros.
  rewrite (contrapositivePP FF x).
  eapply modus_ponens.
  + apply aux_minimun_theorem02.
  + apply modus_ponens with (~~ (~~ (FF --> FF))).
    - rewrite <- contrapositivePP.
      apply falsep_elim.
    - rewrite <- double_negp_intros.
      apply provable_impp_refl.
Qed.

Lemma contrapositivePN: forall (x y: expr),
  |-- (y --> ~~ x) --> (x --> ~~ y).
Proof.
  intros.
  rewrite (double_negp_intros x) at 2.
  apply contrapositivePP.
Qed.

End DerivableRulesFromAxiomatization1.

Section DerivableRulesFromSequentCalculus2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {inegpSC: IntuitionisticNegSequentCalculus L Gamma}.

Lemma deduction_contrapositivePP': forall Phi (x y: expr),
  Phi |--- y --> x ->
  Phi |--- ~~ x --> ~~ y.
Proof.
  intros.
  rewrite <- deduction_theorem in H |- *.
  apply deduction_contrapositivePP; auto.
Qed.

Lemma deduction_contrapositivePN': forall Phi (x y: expr),
  Phi |--- y --> ~~ x ->
  Phi |--- x --> ~~ y.
Proof.
  AddAxiomatization.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply deduction_weaken0.
  apply contrapositivePN.
Qed.

Lemma deduction_contrapositivePN: forall Phi (x y: expr),
  Phi;; y |--- ~~ x ->
  Phi;; x |--- ~~ y.
Proof.
  intros.
  rewrite deduction_theorem in H |- *.
  apply deduction_contrapositivePN'; auto.
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
      apply deduction_contrapositivePP'.
      rewrite <- provable_derivable.
      apply orp_intros1.
    - rewrite deduction_theorem.
      apply deduction_contrapositivePP'.
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
  clear - minAX truepAX iffpAX.
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

Lemma orp_dup1: forall (x: expr),
  |-- x || x --> x.
Proof.
  clear - orpAX minAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_theorem.
  apply deduction_orp_elim; apply derivable_assum1.
Qed.


Lemma orp_dup2: forall (x: expr),
  |-- x --> x || x.
Proof.
  intros.
  apply orp_intros1.
Qed.

Lemma orp_dup: forall (x: expr),
  |-- x || x <--> x.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply orp_dup1.
  + apply orp_dup2.
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
  clear - minAX inegpAX iffpAX falsepAX.
  AddSequentCalculus.
  intros.
  apply solve_iffp_intros.
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

Lemma impp2orp2: forall x y, |-- ~~ x || y --> (x --> y).
Proof.
  intros.
  apply solve_orp_impp.
  + apply contradiction_elim1.
  + apply axiom1.
Qed.

End DerivableRulesFromAxiomatization2.

Section DerivableRulesFromLogicEquiv.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {iffpL: IffLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaEP: EquivProvable L GammaP GammaE}
        {minAX: MinimumAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}.

Lemma equiv_iffp : forall x y,
  x --||-- y <-> |-- x <--> y.
Proof.
  intros.
  split.
  -intros. apply logic_equiv_provable in H. destruct H.
   pose proof iffp_intros x y.
   pose proof modus_ponens _ _ H1 H.
   pose proof modus_ponens _ _ H2 H0.
   auto.
  -intros.
   apply logic_equiv_provable.
   split.
     *pose proof iffp_elim1 x y.
      pose proof modus_ponens _ _ H0 H;auto.
     *pose proof iffp_elim2 x y.
      pose proof modus_ponens _ _ H0 H;auto.
  Qed.

End DerivableRulesFromLogicEquiv.

Lemma provable_derivable1_true
       {L: Language}
       {minL: MinimumLanguage L}
       {truepL: TrueLanguage L}
       {GammaP: Provable L}
       {GammaD1: Derivable1 L}
       {minAX: MinimumAxiomatization L GammaP}
       {trueD: TrueDeduction L GammaD1}
       {bD: BasicDeduction L GammaD1}
       {GammaD1P: Derivable1Provable L GammaP GammaD1}
       {GammaPD1: ProvableDerivable1 L GammaP GammaD1}
      :forall x,
  provable x <-> derivable1 TT x.
Proof.
  intros.
  split; intros.
  + apply provable_right; auto.
  + rewrite provable_derivable1.
    rewrite <- H at 3.
    apply derivable1_truep_intros.
Qed.

Instance reg_Axiomatization2Deduction_GammaPD1:
  RegisterClass P2D1_reg (fun PD: unit => @Axiomatization2Deduction_GammaPD1) 1.
Qed.

Section Axiomatization2LogicEquiv.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaE: LogicEquiv L}
        {GammaEP: EquivProvable L GammaP GammaE}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2LogicEquiv_imppE : ImpLogicEquiv L GammaE.
Proof.
  constructor.
  intros.
  apply logic_equiv_provable. apply logic_equiv_provable in H. apply logic_equiv_provable in H0.
  destruct H,H0.
  split.
  -rewrite H0. rewrite H1.
   apply provable_impp_refl.
  -rewrite H. rewrite H2.
   apply provable_impp_refl.
  Qed.

End Axiomatization2LogicEquiv.

Instance reg_Axiomatization2LogicEquiv_imppE:
  RegisterClass P2E_reg (fun imppE: unit => @Axiomatization2LogicEquiv_imppE) 1.
Qed.

