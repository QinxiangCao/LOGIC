(*************************************************************************

This file include the sep_apply tactic VST/floyd/seplog_tactics. In 2020,
Qinxiang Cao adds connections of this normalized tactic to UnifySL libray.
Here is VST.msl's LICENSE information.

Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
All rights reserved.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS "AS IS" AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR THE CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

***************************************************************************)

Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses.

Module Type ASSUM.

Parameter __PARA__: Type.
  
Parameter expr: forall `{__PARA__}, Type.

Section ASSUM.

Context {p: __PARA__}.

Local Notation "'expr'" := (@expr p).

Parameter provable: expr -> Prop.
Parameter logic_equiv: expr -> expr -> Prop.
Parameter emp: expr.
Parameter impp: expr -> expr -> expr.
Parameter sepcon: expr -> expr -> expr.

Local Declare Scope syntax.
Local Open Scope syntax.
Notation "x --||-- y" := (logic_equiv x y) (at level 71, no associativity).
Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.

Axiom impp_proper_equiv:
  Proper (logic_equiv ==> logic_equiv ==> logic_equiv) impp.
Axiom sepcon_proper_equiv:
  Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon.
Axiom provable_proper_equiv : Proper (logic_equiv ==> iff) provable.
Axiom logic_equiv_refl: Reflexive logic_equiv.

Axiom provable_impp_refl : forall x, |-- x --> x.
Axiom provable_impp_refl' : forall x y, x = y -> |-- x --> y.
Axiom solve_impp_trans: forall (x y z: expr), |-- (x --> y) -> |-- (y --> z) -> |-- (x --> z).
Axiom sepcon_mono: forall x1 x2 y1 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- (x1 * y1) --> (x2 * y2).
Axiom sepcon_assoc_equiv: forall x y z, x * (y * z) --||-- (x * y) * z.
Axiom sepcon_emp_equiv: forall x, x * emp --||-- x.

Axiom cancel_ready: forall x y, |-- x * emp --> y -> |-- x --> y.
Axiom cancel_one_succeed: forall u x y z, |-- x * y --> z -> |-- (u * x) * y --> u * z.
Axiom cancel_one_giveup: forall x y z w v, |-- x * (y * z) --> w * v-> |-- (y * x) * z --> w * v.
Axiom cancel_rev: forall x y z w,  |-- (y * x) * z --> w -> |-- x * (y * z) --> w.
Axiom cancel_finish: forall x, |-- x * emp --> x.

End ASSUM.
End ASSUM.

Module ExportTactic (T: ASSUM).

Import T.

Local Declare Scope syntax.
Local Open Scope syntax.
Notation "x --||-- y" := (logic_equiv x y) (at level 71, no associativity).
Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.

Existing Instances impp_proper_equiv
                   sepcon_proper_equiv
                   provable_proper_equiv
                   logic_equiv_refl.


Ltac cancel_tac EVAR :=
  apply cancel_ready;
  rewrite <- !sepcon_assoc_equiv;
  apply cancel_ready;
  repeat
    match goal with
    | |- |-- (?u1 * _) * _ --> ?u2 * _ =>
      unify u1 u2;
      apply cancel_one_succeed;
      repeat apply cancel_rev
    | _ =>
      simple apply cancel_one_giveup
    end;
  unfold EVAR; apply cancel_finish.
  
Ltac apply_find_core X :=
 match X with
 | ?U -> ?V => match type of U with Prop => apply_find_core V end
 | provable (impp _ _) => constr:(X)
 | @eq expr ?A ?B => constr:(provable (impp A B))
 end.

Ltac head_of_type_of H :=
 match type of H with ?A => apply_find_core A end.

Ltac sep_apply_aux2 H' := 
     match head_of_type_of H' with provable (impp ?C ?D) =>
      let frame := fresh "frame" in evar (frame: expr);
       apply solve_impp_trans with (C * frame);
             [ solve [cancel_tac frame]
             | eapply solve_impp_trans;
                [ apply sepcon_mono;
                  [ clear frame; apply H'
                  | try subst frame; apply provable_impp_refl]
                | subst frame; rewrite sepcon_emp_equiv
                ]
             ]
     end.

Ltac sep_apply_aux1 H := sep_apply_aux2 H.

Ltac sep_apply_aux0 H := sep_apply_aux1 H.

(* NOTE: this is originally "adjust2_sep_apply".
   But we do not need to handle pure facts now.
   Thus it is a simplified version here. *)
Ltac adjust_sep_apply H :=
 match type of H with
 | @eq expr _ _ => constr:(provable_impp_refl' _ _ H)
 | _ => H
 end.

Ltac sep_apply_in_entailment H :=
  match goal with
  | |- provable (impp _ _) =>
     let H' := adjust_sep_apply H in
         sep_apply_aux0 H'
  | _ => fail 0 "The proof goal is not an SL entailment"
  end.

Ltac my_unshelve_evar name T cb evar_tac :=
  let x := fresh name
  in
  unshelve evar (x:T); revgoals;
  [
    let x' := eval unfold x in x
    in
    clear x; cb x'
  |
    evar_tac x
  ].

Ltac HO_sep_apply_in_entailment originalH evar_tac prop_tac :=
  let rec sep_apply_in_entailment_rec H :=
    lazymatch type of H with
    | forall x:?T, _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T);
           [ | sep_apply_in_entailment_rec (H H'); clear H'];
           [ prop_tac | .. ]
      | _ => my_unshelve_evar x T
        ltac:(fun x => sep_apply_in_entailment_rec (H x))
        evar_tac
      end
    | ?T -> _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T);
           [ | sep_apply_in_entailment_rec (H H'); clear H'];
           [ prop_tac | .. ]
      | _ => let x := fresh "arg" in
        my_unshelve_evar x T
          ltac:(fun x => sep_apply_in_entailment_rec (H x))
          evar_tac
      end
    | provable (impp ?A ?B) => sep_apply_in_entailment H
    | ?A = ?B => sep_apply_in_entailment H
    | _ => fail 0 originalH "is not an SL entailment or equivalence"
    end
  in
  sep_apply_in_entailment_rec originalH.

Ltac sep_apply_evar_tac x := fail 0 "Unable to find an instance for the variable" x.
Ltac default_sep_apply_prop_tac := first [reflexivity | assumption | idtac].
Ltac sep_apply_prop_tac := default_sep_apply_prop_tac.

Ltac sep_apply H :=
  HO_sep_apply_in_entailment H sep_apply_evar_tac sep_apply_prop_tac.

End ExportTactic.

