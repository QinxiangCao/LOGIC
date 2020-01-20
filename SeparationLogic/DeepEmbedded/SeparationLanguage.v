Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.SeparationLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class PropositionalVariables: Type := {
  Var: Type
}.

Inductive expr {Sigma: PropositionalVariables}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | falsep : expr
  | sepcon : expr -> expr -> expr
  | wand : expr -> expr -> expr
  | varp : Var -> expr.

Arguments expr: clear implicits.

Definition negp {Sigma: PropositionalVariables} (x: expr Sigma): expr Sigma :=
  impp x falsep.

Definition iffp {Sigma: PropositionalVariables} (x y: expr Sigma): expr Sigma :=
  andp (impp x y) (impp y x).

Definition truep {Sigma: PropositionalVariables}: expr Sigma :=
  impp falsep falsep.

Instance L {Sigma: PropositionalVariables}: Language :=
  Build_Language (expr Sigma).

Instance minL {Sigma: PropositionalVariables}: MinimumLanguage L :=
  Build_MinimumLanguage L impp.

Instance andpL {Sigma: PropositionalVariables}: AndLanguage L :=
  Build_AndLanguage L andp.

Instance orpL {Sigma: PropositionalVariables}: OrLanguage L :=
  Build_OrLanguage L orp.

Instance falsepL {Sigma: PropositionalVariables}: FalseLanguage L :=
  Build_FalseLanguage L falsep.

Instance negpL {Sigma: PropositionalVariables}: NegLanguage L :=
  Build_NegLanguage L negp.

Instance negpDef {Sigma: PropositionalVariables}: NegDefinition_False_Imp L :=
  FalseImp2Neg_Normal.

Instance iffpL {Sigma: PropositionalVariables}: IffLanguage L :=
  Build_IffLanguage L iffp.

Instance iffpDef {Sigma: PropositionalVariables}: IffDefinition_And_Imp L :=
  AndImp2Iff_Normal.

Instance truepL {Sigma: PropositionalVariables}: TrueLanguage L :=
  Build_TrueLanguage L truep.

Instance truepDef {Sigma: PropositionalVariables}: TrueDefinition_False_Imp L :=
  FalseImp2True_Normal.

Instance sepconL {Sigma: PropositionalVariables}: SepconLanguage L :=
  Build_SepconLanguage L sepcon.

Instance wandL {Sigma: PropositionalVariables}: WandLanguage L :=
  Build_WandLanguage L wand.
