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
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Complete.Truth_Kripke.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Logic.MinimunLogic.DeepEmbedded.MinimunLanguage.
Require Import Logic.MinimunLogic.DeepEmbedded.MinimunLogic.
Require Logic.ModalLogic.complete.ModalLanguage.
Require Logic.ModalLogic.complete.semantics.
Require Import Logic.ModalLogic.complete.Syntax.
Require Import Logic.ModalLogic.complete.prooftheoies.
Local Open Scope syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Import ModalLanguageNotation.
Section Complete.
Context {Sigma: ModalLanguage.ModalVariables}
        {CV: Countable ModalLanguage.Var}.

Existing Instances ModalLanguage.L ModalLanguage.minL ModalLanguage.pL ModalLanguage.mL.
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
  intros.
  apply Lindenbaum_constructable_suffice; auto.
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

Lemma truth_lemma_falsep:
  forall m Phi, rel m Phi -> (KRIPKE: canonical_Kmodel , m |= ModalLanguage.falsep <-> proj1_sig Phi ModalLanguage.falsep).
Admitted.
Lemma truth_lemma_impp:
  forall m Phi x y, rel m Phi -> (KRIPKE:canonical_Kmodel, m |= ModalLanguage.impp x y <-> proj1_sig Phi (ModalLanguage.impp x y)).
Admitted.
Lemma truth_lemma_andp:
  forall m Phi x y, rel m Phi -> (KRIPKE:canonical_Kmodel, m |= (andp x y) <-> proj1_sig Phi (andp x y)).
Admitted.
Lemma truth_lemma_orp:
  forall m Phi x y, rel m Phi -> (KRIPKE:canonical_Kmodel, m |=(orp x y)<-> proj1_sig Phi (orp x y)).
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


Lemma sat_boxp : forall m x Phi, (KRIPKE: canonical_Kmodel, m |= boxp x /\ rel m Phi )
 <-> forall n Psi ,rel n Psi /\ Relation Phi Psi -> KRIPKE: canonical_Kmodel , n |= x.
Admitted.
Lemma rel_def: forall Phi : sig cP, exists n , rel n Phi.
Proof.
  intros. exists Phi. reflexivity.
Qed.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  Focus 3.
  intros. apply truth_lemma_impp;auto.
  intros. apply truth_lemma_andp;auto.
  intros. apply truth_lemma_orp;auto.
  intros. apply truth_lemma_falsep;auto.
  Focus 2. intros. split. Focus 2. pose proof existence. intros.
  pose proof sat_boxp m x Phi. destruct H2.
  apply H3. intros. destruct H4 as [h1 h2]. unfold Relation in h2. apply h2 in H1.
  apply IHx in h1. apply h1 in H1. apply H1.
  intros. pose proof existence x Phi. assert (~ (~ proj1_sig Phi (boxp x))).
  Focus 2. pose proof NNPP (proj1_sig Phi (□ x)). apply H3 in H2. apply H2.
  unfold not. intros. apply H1 in H2. destruct H2 ; destruct H2 as [h1 h2]. 
  pose proof sat_boxp m x Phi. destruct H2.
  assert (exists n , rel n x0). apply rel_def. destruct H4. apply IHx in H4 as H5. 
  destruct H5. assert(rel x1 x0 /\ Relation Phi x0 -> KRIPKE: canonical_Kmodel, x1 |= x).
  apply H2. auto. assert(rel x1 x0 /\ Relation Phi x0). auto. apply H7 in H8.
  apply IHx in H4. destruct H4. apply H4 in H8. apply h2. apply H8.
  intros; change (m = Phi) in H; subst; reflexivity.
Qed.
End General_Completeness.

Section NormalModalLogic.
Existing Instances prooftheoies.NormalModalLogic.GP prooftheoies.NormalModalLogic.GD prooftheoies.NormalModalLogic.AX prooftheoies.NormalModalLogic.minAX.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC.

Theorem complete_NormalModalLogic_Kripke_all: 
  strongly_complete prooftheoies.NormalModalLogic.GD semantics.SM
 (KripkeModelClass _ semantics.Kmodel_normal).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  hnf. apply I.
Qed.
End NormalModalLogic.

Section T_ModalLogic.
Existing Instances prooftheoies.T_ModalLogic.GP prooftheoies.T_ModalLogic.GD prooftheoies.T_ModalLogic.AX prooftheoies.T_ModalLogic.minAX.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC.

Lemma denote_ref:
  semantics.Krelation_ref_Kdenote (Kworlds canonical_Kmodel).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel w1) as [Phi ?].
  pose proof H_R w1 w1 Phi Phi.
  unfold KripkeModel.KM.Krelation.
  apply H0. auto. auto.
  hnf. intros. pose proof AL_DC.
  hnf in H2.
  assert(cP (proj1_sig Phi)).
  Focus 2. apply H2 in H3 as h1. pose proof derivable_closed_element_derivable (proj1_sig Phi).
  apply H4. apply h1. assert(proj1_sig Phi |-- boxp x). apply H4. apply h1. apply H1.
  pose proof RewriteClass.TestInSequentCalculus.Unnamed_thm (proj1_sig Phi)(boxp x) x. apply H6 in H5. apply H5.
  pose proof prooftheoies.T_ModalLogic.about_T_ModalLogic. apply H7.
  apply (proj2_sig Phi).
Qed.

Theorem complete_T_ModalLogic_Kripke_all: 
  strongly_complete prooftheoies.T_ModalLogic.GD semantics.SM
 (KripkeModelClass _ (semantics.Kmodel_normal + semantics.Kmodel_ref)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  hnf. split. hnf. apply I.
  hnf. apply denote_ref. 
Qed.

End T_ModalLogic.

Section K4_ModalLogic.

Existing Instances prooftheoies.K4_ModalLogic.GP prooftheoies.K4_ModalLogic.GD prooftheoies.K4_ModalLogic.AX prooftheoies.K4_ModalLogic.minAX.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC.

Lemma denote_trans:
  semantics.Krelation_trans_Kdenote (Kworlds canonical_Kmodel).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel w1) as [Phi1 ?].
  destruct (im_bij _ _ rel w2) as [Phi2 ?].
  destruct (im_bij _ _ rel w3) as [Phi3 ?].
  pose proof H_R w1 w2 Phi1 Phi2.
  pose proof H_R w2 w3 Phi2 Phi3.
  pose proof H_R w1 w3 Phi1 Phi3.
  unfold KripkeModel.KM.Krelation.
  apply H6. auto. auto. hnf.
  intros. pose proof AL_DC.
  hnf in H. hnf in H0.
  apply H4 in H1. Focus 2. auto. apply H1 in H. hnf in H.
  apply H5 in H2. Focus 2. auto. apply H2 in H0. hnf in H0.
  pose proof derivable_closed_element_derivable (proj1_sig Phi1).
  pose proof derivable_closed_element_derivable (proj1_sig Phi2).
  pose proof derivable_closed_element_derivable (proj1_sig Phi3).
  assert (cP (proj1_sig Phi1)). Focus 2. apply H8 in H12. assert(proj1_sig Phi1 |-- boxp x). apply H9. auto. auto.
  assert (cP (proj1_sig Phi2)). Focus 2. apply H8 in H14. assert(proj1_sig Phi2 |-- boxp x). apply H10. auto.
  pose proof RewriteClass.TestInSequentCalculus.Unnamed_thm (proj1_sig Phi1)(boxp x) (boxp (boxp x)).
  pose proof prooftheoies.K4_ModalLogic.about_K4_ModalLogic. apply H15 in H16. assert (proj1_sig Phi1 (boxp (boxp x))).
  apply H9. auto. auto. apply H in H17. auto. auto. assert(proj1_sig Phi2 (boxp x)). apply H10. auto. auto.
  apply H0 in H16. auto. apply (proj2_sig Phi2). apply (proj2_sig Phi1).
Qed.

Theorem complete_K4_ModalLogic_Kripke_all: 
  strongly_complete prooftheoies.K4_ModalLogic.GD semantics.SM
 (KripkeModelClass _ (semantics.Kmodel_normal + semantics.Kmodel_trans)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  hnf. split. hnf. apply I.
  hnf. apply denote_trans.
Qed.
End K4_ModalLogic.
