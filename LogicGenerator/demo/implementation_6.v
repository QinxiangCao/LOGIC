Require Import HypotheticalExternLib.
Require Import ZArith.
Require Import interface_6.

Module NaiveLang.
  Definition expr `{para} := (nat -> option X) -> Prop.
  Section NaiveLang.
  Context `{para}.
  Definition context := expr -> Prop.
  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition orp  (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
  Definition falsep : expr := fun st => False.
  Definition coq_prop (P: Prop): expr := fun _ => P.

  Definition join : (nat -> option X) -> (nat -> option X) -> (nat -> option X) -> Prop :=
    fun x y z =>
      forall p: nat,
       (exists v, x p = Some v /\ y p = None /\ z p = Some v) \/
       (exists v, x p = None /\ y p = Some v /\ z p = Some v) \/
       (x p = None /\ y p = None /\ z p = None).
  Definition sepcon (e1 e2 : expr) : expr := fun st =>
    exists st1 st2, join st1 st2 st /\ e1 st1 /\ e2 st2.
  Definition emp : expr := fun st =>
    forall p, st p = None.
  Definition corable (e: expr): Prop := forall s1 s2, e s1 <-> e s2.
  
  Definition provable (e : expr) : Prop := forall st, e st.
  End NaiveLang.
End NaiveLang.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Section NaiveRule.
  Context `{para}.

  Lemma modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. unfold provable, impp. auto. Qed.

  Lemma axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. unfold provable, impp. auto. Qed.

  Lemma axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. unfold provable, impp. auto. Qed.

  Lemma andp_intros :
    forall x y : expr, provable (impp x (impp y (andp x y))).
  Proof. unfold provable, impp, andp. auto. Qed.

  Lemma andp_elim1 : forall x y : expr, provable (impp (andp x y) x).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma andp_elim2 : forall x y : expr, provable (impp (andp x y) y).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma orp_intros1 : forall x y : expr, provable (impp x (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma orp_intros2 : forall x y : expr, provable (impp y (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma orp_elim : forall x y z : expr,
      provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z))).
  Proof. unfold provable, impp, orp. tauto. Qed.

  Lemma falsep_elim : forall x : expr, provable (impp falsep x).
  Proof. unfold provable, impp, falsep. destruct 1. Qed.

  Lemma excluded_middle : forall x : expr, provable (orp x (negp x)).
  Proof. unfold provable, orp, negp, impp, falsep. intros; tauto. Qed.

  Lemma coq_prop_intros : (forall P : Prop, P -> provable (coq_prop P)) .
  Proof. unfold provable, coq_prop. intros; tauto. Qed.
  
  Lemma coq_prop_elim : (forall (P : Prop) (x : expr), (P -> provable x) -> provable (impp (coq_prop P) x)) .
  Proof. unfold provable, impp, coq_prop. intros; auto. Qed.
    
  Lemma coq_prop_impp : (forall P Q : Prop, provable (impp (impp (coq_prop P) (coq_prop Q)) (coq_prop (P -> Q)))) .
  Proof. unfold provable, impp, coq_prop. intros; auto. Qed.
  
  Axiom sepcon_comm: forall x y, provable (iffp (sepcon x y) (sepcon y x)).
  Axiom sepcon_assoc: forall x y z,
      provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)).
  Axiom sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom sepcon_emp : (forall x : expr, provable (iffp (sepcon x emp) x)) .
  Axiom falsep_sepcon_left : (forall x : expr, provable (impp (sepcon falsep x) falsep)) .
  Axiom orp_sepcon_left : (forall x y z : expr, provable (impp (sepcon (orp x y) z) (orp (sepcon x z) (sepcon y z)))) .
  Axiom corable_coq_prop : (forall P : Prop, corable (coq_prop P)) .
  Axiom corable_preserved' : (forall x y : expr, provable (iffp x y) -> corable x -> corable y) .
  Axiom corable_andp_sepcon1 : (forall x y z : expr, corable x -> provable (iffp (sepcon (andp x y) z) (andp x (sepcon y z)))) .
  End NaiveRule.
End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
Module Solver := IPSolver NaiveLang.
Import T.
Import Solver.


