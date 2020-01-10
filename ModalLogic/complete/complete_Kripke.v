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
Require Logic.ModalLogic.complete.ModalLanguage.
Require Logic.ModalLogic.complete.semantics.
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

Context {GammaP: Provable ModalLanguage.L}
        {GammaD: Derivable ModalLanguage.L}.

Definition cP : context -> Prop := Intersection _ derivable_closed consistent.

Lemma AL_DC: at_least derivable_closed cP.
Proof. solve_at_least. Qed.


Lemma AL_CONSI: at_least consistent cP.
Proof. solve_at_least. Qed.


Context {SC: NormalSequentCalculus _ GammaP GammaD}
        {bSC: BasicSequentCalculus _ GammaD}
        {fwSC: FiniteWitnessedSequentCalculus _ GammaD}
        {minSC: MinimunSequentCalculus _ GammaD}
        {AX: NormalAxiomatization _ GammaP GammaD}
        {minAX: MinimunAxiomatization _ GammaP}.

Lemma LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Proof.
Admitted.

Definition Relation : sig cP -> sig cP -> Prop := 
fun Phi Psi => forall x : expr , proj1_sig Phi (boxp x) -> proj1_sig Psi x.


Definition canonical_frame: semantics.frame :=
  semantics.Build_frame (sig cP) (fun a b => Relation a b).

Definition canonical_eval: ModalLanguage.Var -> semantics.sem canonical_frame :=
  fun p a => proj1_sig a (ModalLanguage.varp p).

Definition canonical_Kmodel: @Kmodel semantics.MD semantics.kMD :=
  semantics.Build_Kmodel canonical_frame canonical_eval.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.

Definition H_R:
  forall m n Phi Psi , rel m Phi -> rel n Psi -> (Relation m n <-> Relation Phi Psi).
Proof.
  intros.
  change (m = Phi) in H.
  change (n = Psi) in H0.
  subst. reflexivity.
Qed.

Definition boxp1 (Phi : context) : context :=
  fun x => exists y, Phi y /\ x = boxp y.

Lemma aboutboxp1 : forall Phi Psi : context, forall x : expr,
  Included _ (boxp1 Phi) Psi -> Phi |-- x -> Psi |-- boxp x.
Proof.
  intros.
  pose proof deduction_weaken (boxp1 Phi) Psi (boxp x).
  apply H1 in H. apply H.
Admitted.

Lemma existence : forall x : expr , forall Phi,
 ~ proj1_sig Phi (boxp x) -> exists Psi,(Relation Phi Psi /\ ~ proj1_sig Psi x).
Proof.
  intros.
  intros.
  set( fun a => proj1_sig Phi (boxp a)).
  pose proof ( LIN_CD).
  unfold  Lindenbaum_constructable in H0. assert(cannot_derive x P).
  Focus 2.
  unfold  Lindenbaum_constructable in H0.
  apply H0 in H1 as H3.
  destruct H3.
  exists x0.
  split.
  unfold Relation. intros. destruct H2. apply H2. auto.
  destruct H2 as [h1 h2].
  unfold not.
  intros.
  unfold not in H. apply H. unfold cannot_derive in h2. 
  Search derivable. pose proof derivable_assum.
  apply h2 in H3. exfalso. apply H3. apply H2. unfold cannot_derive.
  pose proof derivable_assum. unfold not. intros.
  pose proof aboutboxp1  P (proj1_sig Phi) x.
  assert( Included _ (boxp1 P) (proj1_sig Phi)).
  Focus 2. apply H3 in H4. pose proof aboutboxp1.
  pose proof AL_DC. unfold at_least in H6. 
  assert(cP (proj1_sig Phi)).
  Focus 2. apply H6 in H7. unfold derivable_closed in H7. apply H7 in H4.
  apply H; apply H4. apply (proj2_sig Phi). apply H2. unfold P. unfold Included. intros.
Admitted.

Hypothesis sat_falsep: forall m,(KRIPKE: canonical_Kmodel , m |= ModalLanguage.falsep <-> False).

Hypothesis truth_lemma_falsep:
  forall m Phi, rel m Phi -> (KRIPKE: canonical_Kmodel , m |= ModalLanguage.falsep <-> proj1_sig Phi ModalLanguage.falsep).


Lemma truth_lemma_impp 
      (AL_DC: at_least derivable_closed cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE:canonical_Kmodel, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE:canonical_Kmodel, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE:canonical_Kmodel, m |= x --> y <-> proj1_sig Phi (x --> y)).
Proof.
Admitted.

Hypothesis sat_boxp : forall m x Phi, (KRIPKE: canonical_Kmodel, m |= boxp x /\ rel m Phi )
 <-> forall n Psi ,rel n Psi /\ Relation Phi Psi -> KRIPKE: canonical_Kmodel , n |= x.

Lemma rel_def: forall Phi : sig cP, exists n , rel n Phi.
Proof.
  intros. exists Phi. reflexivity.
Qed.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x. Focus 2.
  + apply truth_lemma_impp. apply AL_DC.
  apply LIN_CD. apply IHx1. apply IHx2.
  Focus 2. intros; change (m = Phi) in H; subst; reflexivity.
  Focus 2. intros. split. Focus 2. pose proof existence. intros.
  pose proof sat_boxp m x Phi. destruct H2.
  apply H3. intros. destruct H4 as [h1 h2]. unfold Relation in h2. apply h2 in H1.
  apply IHx in h1. apply h1 in H1. apply H1.
  intros. pose proof existence x Phi. assert (~ (~ proj1_sig Phi (boxp x))).
  Focus 2. pose proof NNPP (proj1_sig Phi (□ x)). apply H3 in H2. apply H2.
  unfold not. intros. apply H1 in H2. destruct H2 ; destruct H2 as [h1 h2]. pose proof sat_boxp m x Phi. destruct H2.
  assert (exists n , rel n x0). apply rel_def. destruct H4. apply IHx in H4 as H5. destruct H5.
  assert(rel x1 x0 /\ Relation Phi x0 -> KRIPKE: canonical_Kmodel, x1 |= x). apply H2. auto. assert(rel x1 x0 /\ Relation Phi x0). auto. apply H7 in H8.
  apply IHx in H4. destruct H4. apply H4 in H8. apply h2. apply H8.
  apply truth_lemma_falsep.
Qed.

Theorem complete_ModalLogic_Kripke_all: 
  strongly_complete GD semantics.SM
 (KripkeModelClass _ _).


