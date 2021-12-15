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

Section J2SC.
Context {M : Model} {J : Join model}.

Definition Model_L := Build_Language (model -> Prop).

Definition Model_sepconL := Build_SepconLanguage Model_L WeakSemantics.sepcon.

Class SepconDefinition_Join (SepconL : SepconLanguage Model_L) : Prop := {
  join2sepcon : forall x y,
    (@sepcon Model_L SepconL) x y = fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2
}.

Definition Join2Sepcon : SepconLanguage Model_L :=
  Build_SepconLanguage Model_L (fun x y => fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2). 

Lemma Join2Sepcon_Normal :
  @SepconDefinition_Join Join2Sepcon.
Proof. constructor. reflexivity. Qed.

End J2SC.

Section SepconAXFromJoin.

Context {M : Model} {L : Language} {J : Join model} 
        {minL : MinimumLanguage L} 
        {sepconL : SepconLanguage L}
        {GammaP : Provable L}
        {J_SA : SeparationAlgebra model}
        {sepconFJ : SepconDefinition_Join (Pred_sepconL model)}.

Lemma SeparationAlgebra2SepconAxiomatization :
  SepconAxiomatization L GammaP.
Proof.
Admitted.

End SepconAXFromJoin.




(* Module Former_j2sc.

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

End Former_j2sc. *)

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
