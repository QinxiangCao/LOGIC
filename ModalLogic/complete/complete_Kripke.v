Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Complete.Truth_Kripke.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Logic.MinimunLogic.DeepEmbedded.MinimunLanguage.
Require Import Logic.MinimunLogic.DeepEmbedded.MinimunLogic.
Require Logic.ModalLogic.ModalLanguage.
Require Logic.ModalLogic.semantics.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.ModalLogic.Syntax.
Local Open Scope syntax.

Local Open Scope logic_base.

Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Import ModalLanguageNotation.
Section Complete.
Context {Sigma: ModalLanguage.ModalVariables}
        {CV: Countable ModalLanguage.Var}.
Existing Instances ModalLanguage.L ModalLanguage.minL ModalLanguage.mL.
Existing Instances semantics.MD semantics.kMD semantics.R semantics.SM .

Section General_Completeness.

Context {Gamma: ProofTheory ModalLanguage.L}.

Definition cP : context -> Prop := Intersection _ derivable_closed consistent.

Lemma AL_DC: at_least derivable_closed cP.
Proof. solve_at_least. Qed.


Lemma AL_CONSI: at_least consistent cP.
Proof. solve_at_least. Qed.


Context {SC: NormalSequentCalculus _ Gamma}
        {bSC: BasicSequentCalculus _ Gamma}
        {fwSC: FiniteWitnessedSequentCalculus _ Gamma}
        {minSC: MinimunSequentCalculus _ Gamma}
        {AX: NormalAxiomatization _ Gamma}
        {minAX: MinimunAxiomatization _ Gamma}.

Lemma LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + (*apply ModalLanguage.formula_countable; auto.
  + apply Lindenbaum_preserves_cannot_derive.
  + unfold cP.
    repeat apply Lindenbaum_ensures_by_conjunct.
    - apply Lindenbaum_cannot_derive_ensures_derivable_closed.
    -*) Admitted.

Definition canonical_frame: semantics.frame :=
  semantics.Build_frame (sig cP) (fun a b => Included _ (proj1_sig a) (proj1_sig b)).

Definition canonical_eval: ModalLanguage.Var -> semantics.sem canonical_frame :=
  fun p a => proj1_sig a (ModalLanguage.varp p).
Print semantics.MD.
Definition canonical_Kmodel: @Kmodel semantics.MD semantics.kMD :=
  semantics.Build_Kmodel canonical_frame canonical_eval.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.

Definition H_R:
  forall m n Phi Psi, rel m Phi -> rel n Psi ->
    (m = n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
  intros.
  change (m = Phi) in H.
  change (n = Psi) in H0.
Admitted.

Definition Relation : sig cP -> sig cP -> Prop := 
fun Phi Psi => forall x : expr , proj1_sig Psi x -> proj1_sig Phi (boxp x).
Print  context.
Print sig.
Locate negp.
Lemma existence : forall x : expr ,forall m, forall Phi,
rel m Phi -> ~ proj1_sig Phi (boxp x) -> exists Psi,(Relation Phi Psi /\ ~ proj1_sig Psi x).
Proof.
  intros.
  assert (fun x:expr => proj1_sig Phi (boxp x) /\ (proj1_sig Phi (~~ x)) ).
Lemma truth_lemma_falsep (AL_CONSI: at_least consistent cP):
  forall m Phi, rel m Phi -> (KRIPKE:canonical_Kmodel , m |= falsep <-> proj1_sig Phi falsep).
Proof.
  intros.
  (*rewrite sat_falsep.
  pose proof proj2_sig Phi.
  pose proof AL_CONSI _ H0.
  rewrite consistent_spec in H1.
  split; [intros [] |].
  intro; apply H1.
  apply derivable_assum; auto.
Qed.*)
Admitted.
Lemma truth_lemma_impp
      (AL_DC: at_least derivable_closed cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: canonical_Kmodel, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: canonical_Kmodel, m |= x --> y <-> proj1_sig Phi (x --> y)).
Proof.
  intros.
Admitted.
Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + apply truth_lemma_falsep. apply AL_CONSI.
  + apply truth_lemma_impp. apply AL_DC.
  apply LIN_CD. apply IHx1. apply IHx2.
  + intros; change (m = Phi) in H; subst; reflexivity.
  + intros. split. pose proof existence x m Phi.  apply IHx in H as H1. apply H0 in H as H2.
  destruct H2. 

