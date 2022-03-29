Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import ZArith.
Require Import QArith.
Require Import Lqa.
Import ListNotations.

Definition Q_Join := fun q1 q2 q => 
  0 <= q1 /\ 0 <= q2 /\ 0 <= q /\ q1 <= 1 /\ q2 <= 1 /\ q <= 1 /\ Qeq q (q1 + q2).
Definition Q_SA : @SeparationAlgebra Q Q_Join.
Proof.
  constructor; intros; unfold join, Q_Join in *;
  [| exists (mxyz - mx)]; repeat (split; try tauto; lra).
Qed.

Definition var : Type := nat.
Definition val : Type := Z.
Definition addr : Type := nat.
Definition store : Type := var -> val.
Definition ASD : Type := Z.
Definition memval : Type := Q * Z.
Definition memlock : Type := Q * option Datatypes.unit * ASD.
Definition heap : Type := addr -> option (memval + memlock).

Definition store_Join := @equiv_Join store.
Definition memval_Join := @prod_Join Q Z Q_Join equiv_Join.
Check @option_Join.
Definition bool_Join := @option_Join Datatypes.unit (@trivial_Join Datatypes.unit).
Definition QB_Join := @prod_Join Q (option Datatypes.unit) Q_Join bool_Join.
Definition memlock_Join := @prod_Join _ _ QB_Join (@equiv_Join ASD).
Check @sum_Join.
Definition mem_Join := @sum_Join memval memlock memval_Join memlock_Join.


Definition heap_Join := @fun_Join addr (option (Q * val)) (@option_Join (Q*val) QV_Join).


Module NaiveLang.
  Definition model : Type := store * heap.
  Definition join := @prod_Join store 


