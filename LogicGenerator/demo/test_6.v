Require Import Logic.ExportSolvers.Normalize_Para.
Require Import HypotheticalExternLib.
Require Import interface_6.
Require Import implementation_6.
Require Import export_lib_6.

Module T.
Include DerivedNames (NaiveLang).
Include BETA.
End T.

Module Tac := ExportTactic T.

Parameter p: para.
Existing Instance p.

Local Declare Scope syntax.
Local Open Scope syntax.

Import T.
Import Tac.

Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "'!!' e" := (coq_prop e) (at level 25) : syntax.
Notation "x && y" := (andp x y) (at level 40, left associativity) : syntax.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.

Goal forall (P: Prop) (Q R S: (nat -> option X) -> Prop),
  |-- (!! P && Q) * R * S --> (!! P && Q) * (!! P && R) * (!! P && S).
Proof.
  intros.
  normalize.
  Search Morphisms.Proper sepcon.
  match goal with
  | |- context [ !! ?P && ?Q * ?R ] => pose proof (prop_andp_sepcon1 P Q R)
  end.
Print Ltac normalize1.
