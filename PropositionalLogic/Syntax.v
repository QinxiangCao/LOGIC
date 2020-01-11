Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.GeneralLogic.Base.

Class PropositionalLanguage (L: Language): Type := {
  andp : expr -> expr -> expr;
  orp : expr -> expr -> expr;
  falsep: expr
}.

Class IterAndLanguage (L: Language): Type := {
  iter_andp : list expr -> expr;
}.

Class IterOrLanguage (L: Language): Type := {
  iter_orp : list expr -> expr;
}.

Definition negp {L: Language} {MinL: MinimumLanguage L} {pL: PropositionalLanguage L} (x: expr): expr := impp x falsep.
Definition iffp {L: Language} {MinL: MinimumLanguage L} {pL: PropositionalLanguage L} (x y: expr): expr := andp (impp x y) (impp y x).
Definition truep {L: Language} {MinL: MinimumLanguage L} {pL: PropositionalLanguage L}: expr := impp falsep falsep.

Module PropositionalLanguageNotation.

Notation "x && y" := (andp x y) (at level 40, left associativity) : syntax.
Notation "x || y" := (orp x y) (at level 50, left associativity) : syntax.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : syntax.
Notation "~~ x" := (negp x) (at level 35) : syntax.
Notation "'FF'" := falsep : syntax.
Notation "'TT'" := truep : syntax.

End PropositionalLanguageNotation.

(* TODO: do not need minL in the future *)
Class NormalIterAnd
      (L: Language)
      {minL: MinimumLanguage L}
      {pL: PropositionalLanguage L}
      {iter_andp_L: IterAndLanguage L}: Prop := {
  iter_andp_def: forall xs, 
    iter_andp xs = fold_left andp xs truep
}.

Class NormalIterOr
      (L: Language)
      {pL: PropositionalLanguage L}
      {iter_orp_L: IterOrLanguage L}: Prop := {
  iter_orp_def: forall xs, 
    iter_orp xs = fold_left orp xs falsep
}.

