Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.

Class ModalLanguage (L: Language): Type := {
  boxp : expr -> expr;
  falsep : expr
}.
Definition negp {L: Language} {MinL: MinimunLanguage L}{mL: ModalLanguage L} (x: expr): expr := impp x falsep.
Definition diamondp {L: Language} {minL: MinimunLanguage L} {mL: ModalLanguage L}: expr -> expr :=
  fun x => negp (boxp (negp x)).
Definition orp {L: Language} {MinL: MinimunLanguage L}{mL: ModalLanguage L} (l1 l2 : expr): expr :=
  impp (negp l1) l2.
Definition andp {L: Language} {MinL: MinimunLanguage L}{mL: ModalLanguage L}(l1 l2 : expr): expr :=
  negp (orp (negp l1) (negp l2)).
Definition iffp {L: Language} {MinL: MinimunLanguage L}{mL: ModalLanguage L}(l1 l2 : expr): expr :=
  andp (impp l1 l2)(impp l2 l1).
Definition truep {L: Language} {MinL: MinimunLanguage L}{mL: ModalLanguage L}: expr := negp falsep.

Module ModalLanguageNotation.

Notation "□ x" := (boxp x) (at level 35) : syntax. (* Unicode 25a1 *)
Notation "◇ x" := (diamondp x) (at level 35) : syntax. (* Unicode 25c7 *)
Notation "~~ x" := (negp x) (at level 35) : syntax.
Notation "x && y" := (andp x y)(at level 40, left associativity).
Notation "x <--> y" := (iffp x y) (at level 60, no associativity).
Reserved Notation "|-- P " (at level 71, no associativity).
Notation "x --> y" := (impp x y)(at level 55, right associativity).
Notation "x || y" := (orp x y)(at level 50, left associativity).

End ModalLanguageNotation.

