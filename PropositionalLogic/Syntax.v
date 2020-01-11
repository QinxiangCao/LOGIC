Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.

Class AndpLanguage (L: Language):
Type := {
  andp : expr -> expr -> expr
}.

Class OrpLanguage (L: Language):
Type := {
  orp : expr -> expr -> expr
}.

Class FalsepLanguage (L: Language):
Type := {
  falsep : expr
}.

Class NegpLanguage (L: Language):
Type := {
  negp : expr -> expr
}.

Class IffpLanguage (L: Language):
Type := {
  iffp : expr -> expr -> expr
}.

Class TruepLanguage (L: Language):
Type := {
  truep : expr
}.

Module PropositionalLanguageNotation.

Notation "x && y" := (andp x y) (at level 40, left associativity) : syntax.
Notation "x || y" := (orp x y) (at level 50, left associativity) : syntax.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : syntax.
Notation "~~ x" := (negp x) (at level 35) : syntax.
Notation "'FF'" := falsep : syntax.
Notation "'TT'" := truep : syntax.

End PropositionalLanguageNotation.

