Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.Sound.Sound_Flat. 
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MetaLogicInj.Syntax.

Section M2COQPROP.
Context {M : Model}.

Instance Model_L : Language := Build_Language (model -> Prop).

Definition Model2CoqProp : CoqPropLanguage Model_L :=
  Build_CoqPropLanguage Model_L (fun (P : Prop) (m : model) => P).

Class CoqPropDefinition_Model (coq_prop_L : CoqPropLanguage Model_L) : Prop := {
  model2coqprop : forall (P : Prop) (m : model), coq_prop P m = P
}.

Lemma Model2CoqProp_Normal : CoqPropDefinition_Model Model2CoqProp.
Proof. constructor. reflexivity. Qed.

End M2COQPROP.

Section U2EMP.

Context {M : Model} {U : Unit model}.

Instance L : Language := Build_Language (model -> Prop).

Definition Unit2Emp : EmpLanguage L :=
  Build_EmpLanguage Model_L (fun (m : model) => is_unit m).

Class EmpDefinition_Unit (empL : EmpLanguage L) : Prop := {
  unit2emp : forall (m : model), emp m = is_unit m
}.

Lemma Unit2Emp_Normal : EmpDefinition_Unit Unit2Emp.
Proof. constructor. reflexivity. Qed.

End U2EMP.






(* Section M2EMP.
Context {M : Model}.

Definition Model2Emp : EmpLanguage Model_L :=
  Build_EmpLanguage Model_L (fun (m : model) => forall n, ) *)



(* 
Definition Model2Emp : EmpLanguage Model_L :=
  Build_EmpLanguage Model_L (fun (m : model) => True).

Class EmpDefinition_Model (empL : EmpLanguage Model_L) : Prop := {
  model2emp : emp = (fun m => True)
}.
 *)
