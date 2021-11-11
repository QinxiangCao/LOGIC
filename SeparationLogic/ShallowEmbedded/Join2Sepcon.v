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

Context {M : Model} {J : Join model}.

(* Definition L : Language := Pred_L model. *)

Class SepconDefinition_Join
  (SepconL : SepconLanguage (Pred_L model)) : Prop := {
    join2sepcon : forall x y, 
    (@sepcon (Pred_L model) SepconL) x y = fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2
  }.

Definition Join2Sepcon : SepconLanguage (Pred_L model) :=
  Build_SepconLanguage (Pred_L model) (fun x y => fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2).

Lemma Join2Sepcon_Normal :
  @SepconDefinition_Join Join2Sepcon.
Proof. constructor. reflexivity. Qed.

(* Check @SepconDefinition_Join. *)

(* Check Build_SepconLanguage.
Check SepconLanguage.
Check (Build_SepconLanguage L).
Check @SepconDefinition_Join. *)

(* 
Class AndDefinition_Or_Neg
  (L: Language)
  {orpL: OrLanguage L}
  {negpL: NegLanguage L}
  {andpL: AndLanguage L}: Prop:= {
orp_negp2andp: forall x y,
x && y = ~~ ((~~ x) || (~~ y))
}.

Definition OrNeg2And
  {L: Language}
  {orpL: OrLanguage L}
  {negpL: NegLanguage L}: AndLanguage L :=
Build_AndLanguage _ (fun x y => ~~ ((~~ x) || (~~ y))).

Lemma OrNeg2And_Normal
      {L: Language}
      {orpL: OrLanguage L}
      {negpL: NegLanguage L}:
  @AndDefinition_Or_Neg L _ _ OrNeg2And.
Proof. constructor. reflexivity. Qed. *)
