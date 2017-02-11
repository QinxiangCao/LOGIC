Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.

Instance Pred_nL (A: Type): NormalLanguage (Pred_L A) := Build_NormalLanguage (Pred_L A) Semantics.impp.
Instance Pred_pL (A: Type): PropositionalLanguage (Pred_L A) := Build_PropositionalLanguage (Pred_L A) (Pred_nL A) Semantics.andp Semantics.orp Semantics.falsep.

Instance Pred_tpSM (A: Type): TrivialPropositionalSemantics (Pred_L A) (Build_Model A) (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + apply Same_set_refl.
Qed.

Instance Pred_Gamma (A: Type): ProofTheory (Pred_L A) := Build_AxiomaticProofTheory (fun x: expr => forall a: A, x a).
Instance Pred_nGamma (A: Type): NormalProofTheory (Pred_L A) (Pred_Gamma A) := Build_nAxiomaticProofTheory (fun x: expr => forall a: A, x a).

Instance Pred_mpGamma (A: Type): MinimunPropositionalLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y ? ? m.
    pose proof @sound_modus_ponens (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y.
    exact (H1 m (H m) (H0 m)).
  + intros x y.
    exact (@sound_axiom1 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y).
  + intros x y z.
    exact (@sound_axiom2 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y z).
Qed.

Instance Pred_ipGamma (A: Type): IntuitionisticPropositionalLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_andp_intros (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_andp_elim1 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_andp_elim2 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_orp_intros1 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_orp_intros2 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y).
  + intros x y z.
    exact (@sound_orp_elim (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x y z).
  + intros x.
    exact (@sound_falsep_elim (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x).
Qed.

Instance Pred_cpGamma (A: Type): ClassicalPropositionalLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_excluded_middle (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tpSM A) x).
Qed.

Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Semantics.SemanticEquiv.

Instance Pred_kiSM (A: Type): @KripkeIntuitionisticSemantics (Pred_L A) (Pred_nL A)  (Pred_pL A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) :=
  @Trivial2Kripke _ _ _ _ _ (Pred_tpSM A).
