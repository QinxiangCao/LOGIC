Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.
Import Derivable1.
Local Open Scope Derivable1.

Class BasicDeduction (L:Language) (Gamma:Derivable1 L) := {
  deduction1_refl: forall x, x |-- x;
  deduction1_trans: forall x y z, x |-- y -> y |-- z -> x |-- z}.

Section BDRewriteClass.

Context {L:Language}
        {Gamma:Derivable1 L}
        {BD:BasicDeduction L Gamma}.

Instance Derivable_impp_rewrite: RewriteRelation derivable1.
Qed.

Section Derivable1.

Instance derivable1_refl: Reflexive derivable1.
Proof.
  hnf; intros.
  apply deduction1_refl.
Qed.

Instance derivable1_proper_derivable1:
  Proper ( derivable1 --> derivable1 ==> Basics.impl) derivable1.
Proof.
  hnf;intros.
  hnf;intros.
  unfold Basics.flip in H.
  intro.
  pose proof deduction1_trans _ _ _ H1 H0.
  pose proof deduction1_trans _ _ _ H H2;tauto.
  Qed.

End Derivable1.

End BDRewriteClass.

Module TestRewriteClass.
Section TestRewriteClass.

Existing Instances Derivable_impp_rewrite
                   derivable1_refl
                   derivable1_proper_derivable1.

Goal forall {L: Language} {Gamma:Derivable1 L} {BD:BasicDeduction L Gamma} x1 x2 y1 y2,
  x1 |-- x2 ->
  y1 |-- y2 ->
  x2 |-- y1 -> x1 |-- y2.
Proof.
  intros.
  rewrite <- H0.
  rewrite <- H1.
  auto.
Qed.

End TestRewriteClass.
End TestRewriteClass.
