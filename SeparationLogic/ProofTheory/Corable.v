Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.

Class Corable (L: Language): Type := {
  corable: expr -> Prop;
}.

Class Corable_withAxiomatization
      (L: Language)
(*      {andpL: AndLanguage L}
      {iffpL: IffLanguage L} *)
      {minL: MinimumLanguage L}
      {pL: PropositionalLanguage L}
      {sepconL: SepconLanguage L}
      (GammaP: Provable L)
      (Cor: Corable L) := {
  corable_preserved': forall x y,
    |-- x <--> y -> corable x -> corable y;
  corable_andp_sepcon1: forall x y z,
    corable x -> |-- (x && y) * z <--> x && (y * z);
}.

Class MinimumCorable
      (L: Language)
      {minL: MinimumLanguage L}
      (Cor: Corable L) := {
  corable_impp: forall x y,
    corable x -> corable y -> corable (x --> y);
}.

Class SepconCorable
      (L: Language)
      {sepconL: SepconLanguage L}
      (Cor: Corable L) := {
  corable_sepcon: forall x y,
    corable x -> corable y -> corable (x * y);
}.

Class CoqPropCorable
      (L: Language)
      {coq_prop_L: CoqPropLanguage L}
      (Cor: Corable L) := {
  corable_coq_prop: forall P,
    corable (!! P)
}.

Section Corable.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}
        {CosAX: Corable L Gamma}.

Lemma corable_andp: forall x y, corable x -> corable y -> corable (x && y).
Proof. intros. apply (@andp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_orp: forall x y, corable x -> corable y -> corable (x || y).
Proof. intros. apply (@orp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_impp: forall x y, corable x -> corable y -> corable (x --> y).
Proof. intros. apply (@impp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_iffp: forall x y, corable x -> corable y -> corable (x <--> y).
Proof. intros. apply (@iffp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_falsep: corable FF.
Proof. apply (@falsep_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_truep: corable TT.
Proof. apply (@truep_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_sepcon: forall x y, corable x -> corable y -> corable (x * y).
Proof. intros. apply (@sepcon_stable L _ _ _ Gamma corable corable_sstable); auto. Qed.

Lemma corable_wand: forall x y, corable x -> corable y -> corable (x -* y).
Proof. intros. apply (@wand_stable L _ _ _ Gamma corable corable_sstable); auto. Qed.

Instance corable_proper_iff: Proper ((fun x y => |-- x <--> y) ==> iff) corable.
Proof. apply (@stable_proper_iffp L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_andp_sepcon1: forall x y z, corable x -> |-- (x && y) * z <--> x && (y * z).
Proof. intros. apply (@stable_andp_sepcon1 L _ _ _ _ Gamma corable corable_sabs); auto. Qed.

Lemma corable_andp_sepcon2: forall x y z, corable y -> |-- (x && y) * z <--> y && (x * z).
Proof.
  intros.
  rewrite andp_comm.
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp1: forall x y z, corable y -> |-- x * (y && z) <--> y && (x * z).
Proof.
  intros.
  rewrite sepcon_comm.
  rewrite (sepcon_comm x z).
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp2: forall x y z, corable z -> |-- x * (y && z) <--> z && (x * y).
Proof.
  intros.
  rewrite andp_comm.
  apply corable_sepcon_andp1; auto.
Qed.

Lemma corable_sepcon_imply_andp: forall x y, corable x -> corable y -> |-- x * y --> x && y.
Proof.
  intros.
  rewrite <- (andp_truep y) at 1.
  rewrite corable_sepcon_andp1 by auto.
  rewrite <- (andp_truep x) at 1.
  rewrite corable_andp_sepcon1 by auto.
  rewrite <- andp_assoc.
  rewrite (andp_comm x y).
  apply andp_elim1.
Qed.

Lemma corable_sepcon_is_andp {ExtsGamma: ExtSeparationLogic L Gamma}: forall x y, corable x -> corable y -> |-- x * y <--> x && y.
Proof.
  intros.
  rewrite <- (andp_truep y) at 1.
  rewrite corable_sepcon_andp1 by auto.
  rewrite <- (andp_truep x) at 1.
  rewrite corable_andp_sepcon1 by auto.
  rewrite <- andp_assoc.
  rewrite (andp_comm x y).
  rewrite provable_truep_sepcon_truep.
  rewrite andp_truep.
  apply provable_iffp_refl.
Qed.

End Corable.

Existing Instance corable_proper_iff.
