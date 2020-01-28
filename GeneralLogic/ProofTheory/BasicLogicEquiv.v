Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.

Class BasicLogicEquiv (L:Language) (Gamma:LogicEquiv L) := {
  logic_equiv_refl: forall x, x--||--x;
  logic_equiv_symm:forall x y,x --||-- y -> y --||-- x;
  logic_equiv_trans: forall x y z, x --||-- y -> y --||-- z -> x --||-- z}.

Section RewriteClass.

Context {L:Language}
        {Gamma: LogicEquiv L}
        {bE: BasicLogicEquiv L Gamma}.

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

End RewriteClass.

Existing Instances logic_equiv_impp_rewrite
                   logic_equiv_refl_instance
                   logic_equiv_symm_instance
                   logic_equiv_trans_instance
                   logic_equiv_proper_logic_equiv.
