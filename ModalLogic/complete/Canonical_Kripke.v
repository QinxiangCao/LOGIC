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
Context {Sigma: ModalLanguage.ModalVariables}.
Existing Instances ModalLanguage.L ModalLanguage.minL ModalLanguage.pL ModalLanguage.mL.
Existing Instances semantics.MD semantics.kMD semantics.R semantics.SM .


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
Definition boxp1 (Phi : context) : context :=
  fun x => exists y, Phi y /\ x = boxp y.

Lemma aboutboxp1 
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}: 
  forall Phi Psi : context, forall x : expr,
  Included _ (boxp1 Phi) (Psi) -> Phi |-- x -> Psi |-- boxp x.
Proof.
  intros. pose proof deduction_weaken (boxp1 Phi) (Psi) (boxp x).
  apply H1. auto.
Admitted.

Lemma aboutcP
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}:
  forall Phi : sig cP , forall x : expr ,
  proj1_sig Phi x -> ~ proj1_sig Phi (negp x).
Proof.
Admitted.

Lemma Classical_negp
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}:
  forall x : expr ,forall Phi : sig cP ,proj1_sig Phi (negp (negp x)) <-> proj1_sig Phi x.
Proof.
Admitted.

Lemma about1truep
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}:
  forall Phi : sig cP , proj1_sig Phi truep.
Proof.
  intros. pose proof Intuitionistic.provable_truep.
  pose proof deduction_weaken0 (proj1_sig Phi) truep.
  apply H0 in H. pose proof derivable_closed_element_derivable (proj1_sig Phi).
  apply H1. assert (at_least derivable_closed cP). solve_at_least.
  apply H2. apply (proj2_sig Phi). auto.
Qed.

Lemma about2truep
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}
  {KmGamma : SystemK ModalLanguage.L GammaP}:
  forall Phi : sig cP , proj1_sig Phi (boxp truep).
Proof.
  intros. assert (forall x ,|-- x -> |-- boxp x).
  apply KmGamma. pose proof Intuitionistic.provable_truep.
  apply H in H0. pose proof deduction_weaken0 (proj1_sig Phi) (boxp truep).
  apply H1 in H0. apply (derivable_closed_element_derivable (proj1_sig Phi)).
  assert (at_least derivable_closed cP). solve_at_least.
  apply H2. apply(proj2_sig Phi). auto.
Qed.

Lemma existence 
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}
  (AL_DC: at_least derivable_closed cP)
  (AL_CONSI: at_least consistent cP)
  (LIN_CD:forall x, Lindenbaum_constructable (cannot_derive x) cP): 
   forall x : expr , forall Phi,
   ~ proj1_sig Phi (boxp x) -> exists Psi,(Relation Phi Psi /\ ~ proj1_sig Psi x).
Proof.
  intros.
  intros.
  set(fun a => proj1_sig Phi (boxp a)).
  pose proof (LIN_CD).
  unfold  Lindenbaum_constructable in H0.
  assert(cannot_derive x P).
  Focus 2. unfold  Lindenbaum_constructable in H0.
  apply H0 in H1 as H3.
  destruct H3. exists x0. split.
  unfold Relation. intros. destruct H2. apply H2. auto.
  destruct H2 as [h1 h2].
  unfold not. intros.
  unfold not in H. apply H. unfold cannot_derive in h2. 
  pose proof derivable_assum.
  apply h2 in H3. exfalso. apply H3. apply H2. unfold cannot_derive.
  pose proof derivable_assum. unfold not. intros.
  pose proof aboutboxp1 (P) (proj1_sig Phi) x.
  assert( Included _ (boxp1 P) (proj1_sig Phi)).
  Focus 2. apply H3 in H4. pose proof aboutboxp1.
  pose proof AL_DC. unfold at_least in H6. 
  assert(cP (proj1_sig Phi)).
  Focus 2. apply H6 in H7. unfold derivable_closed in H7. apply H7 in H4.
  apply H; apply H4. apply (proj2_sig Phi). apply H2. hnf. intros.
Admitted.

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

Lemma Canonical_denote_symmetric
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}
  (AL_DC: at_least derivable_closed cP)
  (AL_CONSI: at_least consistent cP)
  (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
  {KmGamma : SystemK ModalLanguage.L GammaP}
  {KBmGamma : SystemB ModalLanguage.L GammaP}:
semantics.Krelation_symmetric_Kdenote (Kworlds canonical_Kmodel).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel w1) as [Phi ?].
  destruct (im_bij _ _ rel w2) as [Psi ?].
  pose proof H_R w1 w2 Phi Psi.
  pose proof H_R w2 w1 Psi Phi.
  apply H3. auto. auto. hnf.
  intros. pose proof AL_DC. apply H3 in H1 as h1. destruct h1.
  Focus 2. auto. assert(~ proj1_sig Phi (negp x)).
  assert (forall x ,|-- x --> boxp (diamondp (x))). apply KBmGamma.
  assert (|-- negp x --> boxp (diamondp (negp x))). apply (H8 (negp x)).
  pose proof derivable_closed_element_derivable (proj1_sig Phi).
  unfold not; intros. 
  pose proof RewriteClass.TestInSequentCalculus.Unnamed_thm (proj1_sig Phi)(negp x) (boxp (diamondp (negp x))).
  assert (proj1_sig Phi |-- negp x). apply H10. apply AL_DC. apply (proj2_sig Phi).
  auto. apply H12 in H9. assert (proj1_sig Phi (boxp (diamondp (negp x)))).
  apply H10. apply AL_DC. apply (proj2_sig Phi). auto.
  apply H2 in H1. unfold  KripkeModel.KM.Krelation in H. apply H1 in H. hnf in H. 
  assert (proj1_sig Psi (diamondp (negp x))). apply H. auto. unfold diamondp in H15. 
  assert(proj1_sig Psi (negp (boxp x))). Focus 2. assert (forall x , proj1_sig Psi |-- x ->proj1_sig  Psi |-- negp x -> False).
  Focus 2. apply (H17 (boxp x)). pose proof derivable_closed_element_derivable(proj1_sig Psi). 
  apply H18. apply AL_DC. apply (proj2_sig Psi). auto. pose proof derivable_closed_element_derivable(proj1_sig Psi). apply H18.
  apply AL_DC. apply (proj2_sig Psi). auto.
  intros. assert(proj1_sig Psi x0). apply (derivable_closed_element_derivable (proj1_sig Psi)). apply AL_DC. apply (proj2_sig Psi). auto.
  assert(proj1_sig Psi (negp x0)). apply (derivable_closed_element_derivable (proj1_sig Psi)). apply AL_DC. apply (proj2_sig Psi). auto.
  pose proof aboutcP Psi x0. apply H21 in H19. auto.
Admitted.
Lemma Canonical_denote_r_unbounded
  {AX: NormalAxiomatization ModalLanguage.L GammaP GammaD}
  {SC: NormalSequentCalculus ModalLanguage.L GammaP GammaD}
  {bSC: BasicSequentCalculus _ GammaD}
  {minSC: MinimunSequentCalculus _ GammaD}
  {minAX: MinimunAxiomatization ModalLanguage.L GammaP}
  (AL_DC: at_least derivable_closed cP)
  (AL_CONSI: at_least consistent cP)
  (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
  {KmGamma : SystemK ModalLanguage.L GammaP}
  {KDmGamma : SystemD ModalLanguage.L GammaP}:
semantics.Krelation_r_unbounded_Kdenote (Kworlds canonical_Kmodel).
  
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel w1) as [Phi ?].
  unfold KripkeModel.KM.Krelation.
  assert (forall x : expr , forall Phi,
  ~ proj1_sig Phi (boxp x) -> exists Psi,(Relation Phi Psi /\ ~ proj1_sig Psi x)).
  assert(forall x ,|-- boxp x --> diamondp x).
  apply KDmGamma.
  assert(proj1_sig Phi |-- truep). Focus 2.
  exact (existence AL_DC AL_CONSI LIN_CD).
  Focus 2. assert (~ (~ proj1_sig Phi (boxp truep))).
  unfold not. intros. apply H0 in H1. destruct H1; destruct H1 as [h1 h2].
  apply h2. pose proof derivable_closed_element_derivable (proj1_sig x).
  apply H1. apply AL_DC. apply (proj2_sig x). Focus 2.
  pose proof NNPP. 
  apply H2 in H1. pose proof RewriteClass.TestInSequentCalculus.Unnamed_thm (proj1_sig Phi)(boxp truep) (diamondp truep).
  assert(forall x ,|-- boxp x --> diamondp x).
  apply KDmGamma. assert(|-- boxp truep --> diamondp truep). auto. apply H3 in H5.
  pose proof aboutcP Phi (diamondp truep). assert(proj1_sig Phi (diamondp truep)).
  apply (derivable_closed_element_derivable (proj1_sig Phi)). apply AL_DC. apply (proj2_sig Phi).
  auto. apply H6 in H7. unfold diamondp in H7. pose proof Classical_negp. 
  assert (~ (proj1_sig Phi (boxp (negp truep)))).
  unfold not. intros. unfold not in H7. rewrite H8 in H7. auto. apply H0 in H9.
  destruct H9. assert( exists n , rel n x).
  intros. exists x. reflexivity. destruct H10. exists x0. pose proof H_R w1 x0 Phi x.
  apply H11. auto. auto. apply H9. pose proof about2truep Phi. 
  apply (derivable_closed_element_derivable (proj1_sig Phi)).
  apply AL_DC. apply (proj2_sig Phi). auto. pose proof about1truep x. apply (derivable_closed_element_derivable (proj1_sig x)).
  apply AL_DC. apply (proj2_sig x). auto. pose proof about1truep Phi. apply (derivable_closed_element_derivable (proj1_sig Phi)).
  apply AL_DC. apply (proj2_sig Phi). auto.
Qed.

End Canonical.



