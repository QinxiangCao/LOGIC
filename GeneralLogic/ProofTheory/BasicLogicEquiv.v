Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.

Class BasicLogicEquiv (L:Language) (Gamma:LogicEquiv L) := {
  equiv_refl: forall x, x--||--x;
  equiv_symm:forall x y,x --||-- y -> y --||-- x;
  equiv_trans: forall x y z, x --||-- y -> y --||-- z -> x --||-- z}.

Section LERewriteClass.

Context {L:Language}
        {Gamma:LogicEquiv L}
        {BD:BasicLogicEquiv L Gamma}.

Instance equiv_impp_rewrite: RewriteRelation logic_equiv.
Qed.

Section Logic_equiv.

Instance logic_equiv_refl: Reflexive logic_equiv.
Proof.
  hnf;intros.
  apply equiv_refl.
  Qed.

Instance logic_equiv_symm: Symmetric logic_equiv.
Proof.
  hnf.
  apply equiv_symm.
 Qed.

Instance logic_equiv_trans: Transitive logic_equiv.
Proof.
  hnf.
  apply equiv_trans.
  Qed.

Instance equiv_proper_equiv:
  Proper ( logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv.
Proof.
  hnf;intros.
  hnf;intros.
  unfold Basics.flip in H.
  intro.
  pose proof equiv_trans _ _ _ H1 H0.
  pose proof equiv_symm _ _ H.
  pose proof equiv_trans _ _ _ H3 H2. auto.
  Qed.

End Logic_equiv.

End LERewriteClass.