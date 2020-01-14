Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Logic.ModalLogic.complete.semantics.
Require Import Logic.ModalLogic.complete.prooftheoies.
Require Logic.ModalLogic.complete.ModalLanguage.
Require Import Logic.ModalLogic.complete.Syntax.
Require Import Logic.ModalLogic.complete.NormalModal.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.
Import ModalLanguageNotation.
Section Canonical.
Context {Sigma: ModalLanguage.ModalVariables}
        {CV: Countable ModalLanguage.Var}.

Existing Instances ModalLanguage.L ModalLanguage.minL ModalLanguage.pL ModalLanguage.mL.
Existing Instances semantics.MD semantics.kMD semantics.R semantics.SM .

Section General_Completeness.
Context
        {GammaP: Provable ModalLanguage.L}
        {GammaD: Derivable ModalLanguage.L}.
Definition cP : context -> Prop := Intersection _ derivable_closed consistent.

Definition Relation : sig cP -> sig cP -> Prop := 
fun Phi Psi => forall x , proj1_sig Phi (boxp x) -> proj1_sig Psi x.

Definition canonical_frame: semantics.frame :=
  semantics.Build_frame (sig cP) (fun a b => Relation a b).

Definition canonical_eval: ModalLanguage.Var -> semantics.sem canonical_frame :=
  fun p a => proj1_sig a (ModalLanguage.varp p).

Definition canonical_Kmodel: @Kmodel semantics.MD semantics.kMD :=
  semantics.Build_Kmodel canonical_frame canonical_eval.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (Relation m n <-> Relation Phi Psi).

Lemma Canonical_denote_ref
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}
  (AL_DC: at_least derivable_closed cP)
  (AL_CONSI: at_least consistent cP)
  (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
  {KmGamma : SystemK ModalLanguage.L GammaP}
  {TmGamma :  SystemT ModalLanguage.L GammaP}:
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
  Focus 2. apply H2 in H3 as h1.
  pose proof derivable_closed_element_derivable (proj1_sig Phi).
  apply H4. apply h1. assert(proj1_sig Phi |-- boxp x). apply H4. apply h1. apply H1.
  pose proof RewriteClass.TestInSequentCalculus.Unnamed_thm (proj1_sig Phi)(boxp x) x. apply H6 in H5. apply H5.
  apply TmGamma.
  apply (proj2_sig Phi).
Qed.
Lemma Canonical_denote_trans
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}
  (AL_DC: at_least derivable_closed cP)
  (AL_CONSI: at_least consistent cP)
  (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
  {KmGamma : SystemK ModalLanguage.L GammaP}
  {TmGamma : SystemT ModalLanguage.L GammaP}
  {s4mGamma :  System4 ModalLanguage.L GammaP}:
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
  assert (|-- boxp x --> boxp (boxp x)). apply s4mGamma. apply H15 in H16. Focus 2. auto.
  assert (proj1_sig Phi1 (boxp (boxp x))).
  apply H9. auto. auto. apply H in H17. eauto. 
  assert(proj1_sig Phi2 (boxp x)). apply H10. apply AL_DC. apply (proj2_sig Phi2).
  auto. apply H0. auto. apply (proj2_sig Phi2). apply (proj2_sig Phi1).
Qed.
End General_Completeness.
End Canonical.