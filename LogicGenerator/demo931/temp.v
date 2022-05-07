Require Import Logic.LogicGenerator.demo931.impl1.
(* Require Import Logic.LogicGenerator.demo931.Interface. *)
Import T.

Context {P P' : Prop} {Q Q' : expr}.


Lemma lem1 : (P -> (derivable1 Q (andp (coq_prop P') Q')))
  -> (derivable1 (andp (coq_prop P) Q) (andp (coq_prop P') Q')).
Admitted.

Lemma lem2 : ((P -> P') /\ (P -> (derivable1 Q Q')))
  -> (P -> (derivable1 Q (andp (coq_prop P') Q'))).
Admitted.

Theorem thm : ((P -> P') /\ (P -> (derivable1 Q Q')))
  -> (derivable1 (andp (coq_prop P) Q) (andp (coq_prop P') Q')).
