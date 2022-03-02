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
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.
Require Import Logic.MinimumLogic.Semantics.Trivial.

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

Section M2IMP.
Context {M : Model}.

(* Definition Model_minL := Build_MinimumLanguage Model_L Semantics.impp. *)

Definition Model2Impp : MinimumLanguage Model_L :=
  Build_MinimumLanguage Model_L (fun x y => fun m => (x m -> y m)).

Class ImppDefinition_Model (minL : MinimumLanguage Model_L) : Prop := {
  model2impp : forall (x y : @expr Model_L), impp x y = (fun m  => (x m -> y m))
}.

Lemma Model2Impp_Normal :
  ImppDefinition_Model Model2Impp.
Proof. constructor. reflexivity. Qed.

End M2IMP.

Section M2P.
Context {M : Model}.

Definition Model2Provable : Provable Model_L :=
  Build_Provable Model_L (fun (x : model -> Prop) => forall m, x m).

Class ProvableDefinition_Model (GammaP : Provable Model_L) : Prop := {
  model2provable : forall (x : @expr Model_L), provable x = (forall m, x m)
}.

Lemma Model2Provable_Normal :
  ProvableDefinition_Model Model2Provable.
Proof. constructor. reflexivity. Qed.

End M2P.

Section SepconAXFromJoin.

Context {M : Model} {J : Join model} 
        {J_SA : SeparationAlgebra model}
        .

Instance modelR : KripkeModel.KI.Relation (model) := fun x y => x = y.
Instance SM : Semantics Model_L M := Build_Semantics Model_L M (fun x => x).
Instance minL : MinimumLanguage Model_L := Build_MinimumLanguage Model_L impp.
Instance sepconL : SepconLanguage Model_L := Model_sepconL.
Instance GammaP : Provable Model_L := Build_Provable Model_L provable.
Instance kminSM : @KripkeMinimumSemantics Model_L minL M (unit_kMD _) tt modelR SM.
Proof.
  pose proof (@Trivial2Kripke Model_L minL M SM). apply H. constructor. reflexivity.
Qed.
Instance sepconSM : @SepconSemantics Model_L sepconL M (unit_kMD _) tt modelR J SM.
Proof. hnf. intros. apply Same_set_refl. Qed.

Lemma SeparationAlgebra2SepconAxiomatization :
  SepconAxiomatization Model_L GammaP.
Proof.
  intros. constructor.
  + intros x y.
    exact (@sound_sepcon_comm Model_L minL sepconL M (unit_kMD _) tt modelR J J_SA SM kminSM sepconSM x y).
  + intros x y z.
    exact (@sound_sepcon_assoc1 Model_L minL sepconL M (unit_kMD _) tt modelR J J_SA SM kminSM sepconSM x y z).
  + intros x1 x2 y1 y2.
    exact (@sound_sepcon_mono Model_L minL sepconL M (unit_kMD _) tt modelR _ J SM kminSM sepconSM x1 x2 y1 y2).
Qed. 

End SepconAXFromJoin.

(* Instance Pred_kminSM (A: Type): @KripkeMinimumSemantics (Pred_L A) (Pred_minL A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) :=
  @Trivial2Kripke _ _ _ _ (Pred_tminSM A). *)


(* Class Semantics (L: Language) (MD: Model): Type := {
  denotation: expr -> model -> Prop (* better to be (expr -> Ensemble model) if Ensemble is polymorphic *)
}. *)


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
