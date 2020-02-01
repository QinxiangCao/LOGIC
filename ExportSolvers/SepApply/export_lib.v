Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses.

Parameter __PARA__: Type.
  
Parameter Inline expr: forall `{__PARA__}, Type.

Section ASSUM.

Context {p: __PARA__}.

Local Notation "'expr'" := (@expr p).

Parameter Inline provable: expr -> Prop.
Parameter logic_equiv: expr -> expr -> Prop.
Parameter emp: expr.
Parameter impp: expr -> expr -> expr.
Parameter Inline sepcon: expr -> expr -> expr.

Local Declare Scope syntax.
Local Open Scope syntax.
Notation "x --||-- y" := (logic_equiv x y) (at level 71, no associativity).
Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.

Axiom impp_proper_equiv:
  Proper (logic_equiv ==> logic_equiv ==> logic_equiv) impp.
Axiom sepcon_proper_logic_equiv:
  Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon.
Axiom provable_proper_equiv : Proper (logic_equiv ==> iff) provable.
Axiom logic_equiv_refl_instance: Reflexive logic_equiv.

Axiom provable_impp_refl : forall x, |-- x --> x.
Axiom provable_impp_refl' : forall x y, x = y -> |-- x --> y.
Axiom solve_impp_trans: forall (x y z: expr), |-- (x --> y) -> |-- (y --> z) -> |-- (x --> z).
Axiom sepcon_mono: forall x1 x2 y1 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- (x1 * y1) --> (x2 * y2).
Axiom sepcon_assoc_logic_equiv: forall x y z, x * (y * z) --||-- (x * y) * z.
Axiom sepcon_emp_logic_equiv: forall x, x * emp --||-- x.

Axiom cancel_ready: forall x y, |-- x * emp --> y -> |-- x --> y.
Axiom cancel_one_succeed: forall u x y z, |-- x * y --> z -> |-- (u * x) * y --> u * z.
Axiom cancel_one_giveup: forall x y z w v, |-- x * (y * z) --> w * v-> |-- (y * x) * z --> w * v.
Axiom cancel_rev: forall x y z w,  |-- (y * x) * z --> w -> |-- x * (y * z) --> w.
Axiom cancel_finish: forall x, |-- x * emp --> x.
