Require Import ZArith.
Require Import interface_7.

Definition X: Type := nat.

Definition RealProvable (e: (nat-> option X) -> Prop) := forall st, e st.
Definition join : (nat-> option X) -> (nat-> option X) -> (nat-> option X) -> Prop :=
    fun x y z =>
      forall p: nat,
       (exists v, x p = Some v /\ y p = None /\ z p = Some v) \/
       (exists v, x p = None /\ y p = Some v /\ z p = Some v) \/
       (x p = None /\ y p = None /\ z p = None).
Definition SepCon (e1 e2 : (nat-> option X) -> Prop) : (nat-> option X) -> Prop := fun st =>
    exists st1 st2, join st1 st2 st /\ e1 st1 /\ e2 st2.
Definition Emp : (nat-> option X) -> Prop :=
  fun st =>
    forall p, st p = None.

Module NaiveLang <: LanguageSig.
  Definition expr := (nat-> option X) -> Prop.
  Section NaiveLang.
  Definition context := expr -> Prop.
  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition emp : expr := Emp.
  Definition sepcon := SepCon.
  Definition provable := RealProvable.
  End NaiveLang.
End NaiveLang.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Section NaiveRule.
  (*Context `{para}.*)

  Lemma modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. unfold provable, RealProvable, impp. auto. Qed.

  Lemma axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. unfold provable, RealProvable, impp. auto. Qed.

  Lemma axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. unfold provable, RealProvable, impp. auto. Qed.

  Lemma andp_intros :
    forall x y : expr, provable (impp x (impp y (andp x y))).
  Proof. unfold provable, RealProvable, impp, andp. auto. Qed.

  Lemma andp_elim1 : forall x y : expr, provable (impp (andp x y) x).
  Proof. unfold provable, RealProvable, impp, andp. tauto. Qed.

  Lemma andp_elim2 : forall x y : expr, provable (impp (andp x y) y).
  Proof. unfold provable, RealProvable, impp, andp. tauto. Qed.

  Axiom sepcon_comm: forall x y, provable (iffp (sepcon x y) (sepcon y x)).
  Axiom sepcon_assoc: forall x y z,
      provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)).
  Axiom sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom sepcon_emp : (forall x : expr, provable (iffp (sepcon x emp) x)) .
  End NaiveRule.
End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
(*Module Solver := IPSolver NaiveLang.*)
Import T.
(*Import Solver.*)


