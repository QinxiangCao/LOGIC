Require Import Logic.LogicGenerator.demo931.impl1.
(* Require Import Logic.LogicGenerator.demo931.Interface. *)
Import T.

(*
1. coqprop P1 && coqprop P2 && ... coqprop Px && P |-- coqprop Q1 && coqprop Q2 && ... coqprop Qx && Q
2. coqprop P1 && coqprop P2 && ... coqprop Px && P |-- Q
3. P |-- coqprop Q1 && coqprop Q2 && ... coqprop Qx && Q
*)

(*
(coq_prop P) && Q |-- (coq_prop P') && Q'
<== P -> (Q |-- (coq_prop P') && Q')
<== (P -> P') /\ (P -> (Q |-- Q'))
*)

Lemma cp_lem1 : forall (P :Prop) (Q Q' : expr),
  (P -> (derivable1 Q Q'))
  -> (derivable1 (andp (coq_prop P) Q) Q').
Proof.
  intros. hnf. intros.
  unfold impp, andp, coq_prop.
  unfold derivable1, provable, impp in H.
  intros. apply H; try tauto.
Qed.

Lemma cp_lem2 : forall (P P' : Prop) (Q Q' : expr),
  (P -> P') -> (P -> (derivable1 Q Q')) ->
  (P -> (derivable1 Q (andp (coq_prop P') Q'))).
Proof.
  intros.
  unfold derivable1, andp, coq_prop, provable, impp in *.
  intros. split; try tauto.
  apply H0; try tauto.
Qed.





(* Lemma lem1 : (P -> (derivable1 Q (andp (coq_prop P') Q')))
  -> (derivable1 (andp (coq_prop P) Q) (andp (coq_prop P') Q')).
Admitted.

Lemma lem2 : ((P -> P') /\ (P -> (derivable1 Q Q')))
  -> (P -> (derivable1 Q (andp (coq_prop P') Q'))).
Admitted.

Theorem thm : ((P -> P') /\ (P -> (derivable1 Q Q')))
  -> (derivable1 (andp (coq_prop P) Q) (andp (coq_prop P') Q')). *)
