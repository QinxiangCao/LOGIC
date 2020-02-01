Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.

Local Open Scope logic_base.

Class BasicLogicEquiv (L:Language) (Gamma:LogicEquiv L) := {
  logic_equiv_refl: forall x, x--||--x;
  logic_equiv_symm:forall x y,x --||-- y -> y --||-- x;
  logic_equiv_trans: forall x y z, x --||-- y -> y --||-- z -> x --||-- z}.

Class EquivDerivable1 (L:Language) (GammaD:Derivable1 L) (GammaL:LogicEquiv L): Type :={
  logic_equiv_derivable1:forall x y,x --||-- y <->
                        derivable1 x y /\ derivable1 y x
}.

Section RewriteClass.

Context {L:Language}
        {GammaE: LogicEquiv L}
        {bE: BasicLogicEquiv L GammaE}.

Instance logic_equiv_impp_rewrite: RewriteRelation logic_equiv.
Qed.

Instance logic_equiv_refl_instance: Reflexive logic_equiv.
Proof.
  hnf;intros.
  apply logic_equiv_refl.
Qed.

Instance logic_equiv_symm_instance: Symmetric logic_equiv.
Proof.
  hnf.
  apply logic_equiv_symm.
Qed.

Instance logic_equiv_trans_instance: Transitive logic_equiv.
Proof.
  hnf.
  apply logic_equiv_trans.
Qed.

Instance logic_equiv_trans_equiv: Equivalence logic_equiv.
Proof.
  constructor.
  + apply logic_equiv_refl_instance.
  + apply logic_equiv_symm_instance.
  + apply logic_equiv_trans_instance.
Qed.

Instance logic_equiv_proper_logic_equiv:
  Proper (logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv.
Proof.
  hnf;intros.
  hnf;intros.
  unfold Basics.flip in H.
  intro.
  pose proof logic_equiv_trans _ _ _ H1 H0.
  pose proof logic_equiv_symm _ _ H.
  pose proof logic_equiv_trans _ _ _ H3 H2. auto.
Qed.

Instance logic_equiv_proper_derivable1
         {GammaD1: Derivable1 L}
         {GammaED1: EquivDerivable1 L GammaD1 GammaE}
         {bD: BasicDeduction L GammaD1}:
  Proper (logic_equiv ==> logic_equiv ==> Basics.impl) derivable1.
Proof.
  hnf; intros.
  hnf; intros.
  hnf; intros.
  apply logic_equiv_derivable1 in H.
  apply logic_equiv_derivable1 in H0.
  destruct H, H0.
  rewrite H2, <- H0.
  auto.
Qed.

End RewriteClass.

Existing Instances logic_equiv_impp_rewrite
                   logic_equiv_refl_instance
                   logic_equiv_symm_instance
                   logic_equiv_trans_instance
                   logic_equiv_trans_equiv
                   logic_equiv_proper_logic_equiv
                   logic_equiv_proper_derivable1.
