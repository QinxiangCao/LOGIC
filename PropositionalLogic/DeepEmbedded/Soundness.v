Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.
Require Logic.PropositionalLogic.Sound.Sound_Kripke.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.IntuitionisticLogic.
Require Logic.PropositionalLogic.DeepEmbedded.DeMorganLogic.
Require Logic.PropositionalLogic.DeepEmbedded.GodelDummettLogic.
Require Logic.PropositionalLogic.DeepEmbedded.ClassicalLogic.
Require Logic.PropositionalLogic.DeepEmbedded.TrivialSemantics.
Require Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Sound.

Context (Var: Type).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.

Instance Intuitionistic_G: ProofTheory L := IntuitionisticLogic.G Var.
Instance DeMorgan_G: ProofTheory L := DeMorganLogic.G Var.
Instance GodelDummett_G: ProofTheory L := GodelDummettLogic.G Var.
Instance Classical_G: ProofTheory L := ClassicalLogic.G Var.
Instance Trivial_MD: Model := TrivialSemantics.MD Var.
Instance Trivial_SM: Semantics L Trivial_MD := TrivialSemantics.SM Var.
Instance Kripke_MD: Model := KripkeSemantics.MD Var.
Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
Instance po_Kripke_R (M: Kmodel): PreOrder (@KI.Krelation _ (Kripke_R M)) := KripkeSemantics.po_R Var M.
Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
Instance Kripke_kiSM (M: Kmodel): KripkeIntuitionisticSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kiSM Var M.

Section Sound_Classical_Trivial.

Import Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.

Theorem sound_classical_trivial: sound Classical_G Trivial_SM (AllModel _).
Proof.
  hnf; intros.
  intro m.
  intros _.
  induction H.
  + pose proof sound_modus_ponens x y.
    exact (H1 m IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_excluded_middle.
Qed.

End Sound_Classical_Trivial.

Section Sound_Kripke.

Import Logic.PropositionalLogic.Sound.Sound_Kripke.

Theorem sound_intuitionistic_Kripke_all: sound Intuitionistic_G Kripke_SM (AllModel _).
Proof.
  hnf; intros.
  intros m _.
  destruct m as [M m].
  change Kmodel in M.
  change (Kworlds M) in m.
  change (KRIPKE: M, m |= x).
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
Qed.

Theorem sound_weak_classical_Kripke_branch_join: sound DeMorgan_G Kripke_SM (KripkeModelClass _ (KripkeSemantics.Kmodel_BranchJoin Var)).
Proof.
  hnf; intros.
  intros m ?.
  destruct H0.
  unfold KripkeSemantics.Kmodel_BranchJoin in H0.
  rename H0 into bkiM.
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_weak_excluded_middle_branch_join.
Qed.

Theorem sound_GodelDummett_Kripke_no_branch: sound GodelDummett_G Kripke_SM (KripkeModelClass _ (KripkeSemantics.Kmodel_NoBranch Var)).
Proof.
  hnf; intros.
  intros m ?.
  destruct H0.
  unfold KripkeSemantics.Kmodel_NoBranch in H0.
  rename H0 into nkiM.
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_impp_choice_no_branch.
Qed.

Theorem sound_classical_Kripke_identity: sound Classical_G Kripke_SM (KripkeModelClass _ (KripkeSemantics.Kmodel_Identity Var)).
Proof.
  hnf; intros.
  intros m ?.
  destruct H0.
  unfold KripkeSemantics.Kmodel_Identity in H0.
  rename H0 into ikiM.
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_excluded_middle_ident.
Qed.

End Sound_Kripke.

End Sound.
