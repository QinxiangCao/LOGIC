Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.RelationPairs_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Semantics.StrongSemantics.
Require Import Logic.SeparationLogic.Sound.Sound_Flat.

Context {M : Model} {J : Join model}.

Definition L : Language := Pred_L model.

Class SepconDefinition_Join
  (* {M : Model}
  {J : Join model} *)
  {SepconL : SepconLanguage L} : Prop := {
    join2sepcon := forall x y, 
    (@sepcon L SepconL) x y = fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2
  }.
