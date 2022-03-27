Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Import ListNotations.

Definition var : Type := nat.
Definition val : Type := Z.
Definition addr : Type := nat.
Definition store : Type := var -> val.
Definition heap : Type := option (addr -> val).
Definition store_Join := @equiv_Join store.
Definition heap_Join := @option_Join (addr -> val) trivial_Join.

Module NaiveLang.
  Definition model : Type := store * heap.
  Definition join := @prod_Join store heap store_Join heap_Join.
  Definition expr := (model -> Prop).
End NaiveLang.

Require Import Interface.

Module NaiveRule.
Include DerivedNames (NaiveLang).

Definition store_SA := @equiv_SA store.
Definition heap_SA := @option_SA (addr -> val) trivial_Join trivial_SA.
Definition join_SA := @prod_SA store heap store_Join heap_Join store_SA heap_SA.

Lemma join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
Proof.
  pose proof join_SA. induction H. apply join_comm.
Qed.

Lemma join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
Proof.
  pose proof join_SA. induction H. tauto.
Qed.

End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
(* Module Solver := IPSolver NaiveLang. *)
Import T.
(* Import Solver. *)
