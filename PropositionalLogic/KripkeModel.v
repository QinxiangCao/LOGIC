(* RODO: use Ensemble *)
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Class Relation (worlds: Type): Type :=
  Krelation: worlds -> Ensemble worlds (* <= *).

Class KripkeIntuitionisticModel (worlds: Type) {R: Relation worlds}: Type :=
  Krelation_Preorder :> PreOrder Krelation.

Module KripkeModelNotation_Intuitionistic.

Infix "<=" := Krelation: kripke_model.

End KripkeModelNotation_Intuitionistic.

Import KripkeModelNotation_Intuitionistic.

Local Open Scope kripke_model.

Definition upwards_closed_Kdenote {worlds: Type} {R: Relation worlds} (d: Ensemble worlds): Prop :=
  forall n m, n <= m -> d n -> d m.

Definition Krelation_stable_Kdenote {worlds: Type} {R: Relation worlds} (d: Ensemble worlds): Prop :=
  forall w1 w2, w1 <= w2 -> (d w1 <-> d w2).

Class IdentityKripkeIntuitionisticModel (worlds: Type) {R: Relation worlds} : Prop := {
  Korder_identity: forall m n: worlds, m <= n -> m = n
}.

Class NoBranchKripkeIntuitionisticModel (worlds: Type) {R: Relation worlds} : Prop := {
  Korder_no_branch: forall m1 m2 n: worlds, n <= m1 -> n <= m2 -> m1 <= m2 \/ m2 <= m1
}.

Class BranchJoinKripkeIntuitionisticModel (worlds: Type) {R: Relation worlds} : Prop := {
  Korder_branch_join: forall m1 m2 n: worlds, n <= m1 -> n <= m2 -> exists m, m1 <= m /\ m2 <= m
}.

