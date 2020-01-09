Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section PatternInstances0.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}.

Lemma or_Comm: Commutativity L Gamma orp.
Proof.
  constructor.
  intros.
  rewrite orp_comm.
  apply provable_impp_refl.
Qed.

Lemma orp_Mono: Monotonicity L Gamma orp.
Proof.
  constructor; intros.
  apply orp_proper_impp; auto.
Qed.

End PatternInstances0.

Section DerivableRulesFromPatterns.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {prodp: expr -> expr -> expr}.

Lemma prodp_comm {Comm: Commutativity L Gamma prodp}: forall x y,
  |-- prodp x y <--> prodp y x.
Proof.
  intros.
  apply solve_andp_intros; apply prodp_comm_impp.
Qed.

Section UnitTheorems.

Context {e: expr}.

Lemma left_unit {LU: LeftUnit L Gamma e prodp} : forall x, |-- prodp e x <--> x.
Proof.
  intros.
  apply solve_andp_intros.
  + apply left_unit1.
  + apply left_unit2.
Qed.

Lemma right_unit {RU: RightUnit L Gamma e prodp} : forall x, |-- prodp x e <--> x.
Proof.
  intros.
  apply solve_andp_intros.
  + apply right_unit1.
  + apply right_unit2.
Qed.

End UnitTheorems.

Section DistrTheorems.

Context {sump: expr -> expr -> expr}.

Lemma prodp_sump_distr_l {LDistr: LeftDistr L Gamma prodp sump}: forall x y z,
  |-- prodp x (sump y z) <--> sump (prodp x y) (prodp x z).
Proof.
  intros.
  apply solve_andp_intros.
  + apply left_distr1.
  + apply left_distr2.
Qed.

Lemma prodp_sump_distr_r {RDistr: RightDistr L Gamma prodp sump}: forall x y z,
  |-- prodp (sump y z) x <--> sump (prodp y x) (prodp z x).
Proof.
  intros.
  apply solve_andp_intros.
  + apply right_distr1.
  + apply right_distr2.
Qed.

End DistrTheorems.

Section AdjointTheorems.

Context {funcp: expr -> expr -> expr}
        {Adj: Adjointness L Gamma prodp funcp}.

Lemma Adjoint2RDistr: RightDistr L Gamma prodp orp.
Proof.
  constructor; intros.
  + apply adjoint.
    apply solve_orp_impp; apply adjoint.
    - apply orp_intros1.
    - apply orp_intros2.
  + apply solve_orp_impp.
    - apply prodp_mono1.
      apply orp_intros1.
    - apply prodp_mono1.
      apply orp_intros2.
Qed.

Lemma Adjoint2LDistr {Comm: Commutativity L Gamma prodp}:
  LeftDistr L Gamma prodp orp.
Proof.
  apply @RightDistr2LeftDistr; auto.
  + apply orp_Mono.
  + apply Adjoint2RDistr.
Qed.

(* TODO: l/r wrong *)
Lemma prodp_orp_distr_l: forall x y z: expr,
  |-- prodp (x || y) z <--> (prodp x z || prodp y z).
Proof.
  intros.
  apply (@prodp_sump_distr_r _ Adjoint2RDistr).
Qed.

(* TODO: l/r wrong *)
Lemma prodp_orp_distr_r {Comm: Commutativity L Gamma prodp}: forall x y z: expr,
  |-- prodp x (y || z) <--> (prodp x y || prodp x z).
Proof.
  intros.
  apply (@prodp_sump_distr_l _ Adjoint2LDistr).
Qed.

Lemma orp_funcp {Comm: Commutativity L Gamma prodp}: forall x y z: expr,
  |-- funcp (x || y) z <--> (funcp x z && funcp y z).
Proof.
  pose proof Adjoint2Mono as Mono.
  intros.
  apply solve_andp_intros.
  + apply solve_impp_andp.
    - apply funcp_mono.
      * apply orp_intros1.
      * apply provable_impp_refl.
    - apply funcp_mono.
      * apply orp_intros2.
      * apply provable_impp_refl.
  + apply adjoint.
    rewrite prodp_orp_distr_r.
    apply solve_orp_impp; apply adjoint.
    - apply andp_elim1.
    - apply andp_elim2.
Qed.

(* TODO: l/r wrong *)
Lemma funcp_andp_distr_r: forall x y z: expr,
  |-- funcp x (y && z)  <--> (funcp x y && funcp x z).
Proof.
  intros.
  apply solve_andp_intros.
  + apply solve_impp_andp.
    - apply funcp_mono2.
      apply andp_elim1.
    - apply funcp_mono2.
      apply andp_elim2.
  + apply adjoint.
    apply solve_impp_andp; apply adjoint.
    - apply andp_elim1.
    - apply andp_elim2.
Qed.

Lemma falsep_prodp: forall x: expr,
  |-- prodp falsep x <--> falsep.
Proof.
  intros.
  apply solve_andp_intros.
  + apply adjoint.
    apply falsep_elim.
  + apply falsep_elim.
Qed.

Lemma prodp_falsep {Comm: Commutativity L Gamma prodp}: forall x: expr,
  |-- prodp x falsep <--> falsep.
Proof.
  intros.
  rewrite prodp_comm.
  rewrite falsep_prodp.
  apply provable_iffp_refl.
Qed.

End AdjointTheorems.

Section MonoTheorems.

Context {Mono: Monotonicity L Gamma prodp}.

Lemma prodp_iffp: forall x1 x2 y1 y2,
  |-- x1 <--> x2 ->
  |-- y1 <--> y2 ->
  |-- prodp x1 y1 <--> prodp x2 y2.
Proof.
  intros.
  apply solve_andp_intros.
  + apply prodp_mono.
    - eapply solve_andp_elim1; exact H.
    - eapply solve_andp_elim1; exact H0.
  + apply prodp_mono.
    - eapply solve_andp_elim2; exact H.
    - eapply solve_andp_elim2; exact H0.
Qed.

Lemma fold_left_iffp: forall x1 x2 xs1 xs2,
  (Forall2 (fun x1 x2 => |-- x1 <--> x2) xs1 xs2) ->
  |-- x1 <--> x2 ->
  |-- fold_left prodp xs1 x1 <--> fold_left prodp xs2 x2.
Proof.
  intros.
  apply solve_andp_intros.
  + apply fold_left_mono.
    - revert H; apply Forall2_impl.
      intros.
      eapply solve_andp_elim1; exact H.
    - eapply solve_andp_elim1; exact H0.
  + apply fold_left_mono.
    - apply Forall2_rev.
      revert H; apply Forall2_impl.
      intros.
      eapply solve_andp_elim2; exact H.
    - eapply solve_andp_elim2; exact H0.
Qed.

Context {e: expr}.

Lemma fold_left_prodp_unfold {LU: LeftUnit L Gamma e prodp}: forall xs,
  |-- fold_left prodp xs e <-->
      match xs with
      | nil => e
      | x :: xs0 => fold_left prodp xs0 x
      end.
Proof.
  intros.
  destruct xs.
  + simpl.
    apply provable_iffp_refl.
  + simpl.
    apply fold_left_iffp.
    - induction xs.
      * constructor.
      * constructor; auto.
        apply provable_iffp_refl.
    - apply left_unit.
Qed.

Lemma fold_right_prodp_unfold {RU: RightUnit L Gamma e prodp}: forall xs,
  |-- fold_right prodp e xs <-->
      (fix f xs :=
         match xs with
         | nil => e
         | x :: nil => x
         | x :: xs0 => prodp x (f xs0)
         end) xs.
Proof.
  intros.
  set (f := (fix f xs :=
             match xs with
             | nil => e
             | x :: nil => x
             | x :: xs0 => prodp x (f xs0)
             end)).
  destruct xs.
  + apply provable_iffp_refl.
  + simpl fold_right.
    revert e0; induction xs; intros.
    - simpl.
      rewrite right_unit.
      apply provable_iffp_refl.
    - change (f (e0 :: a :: xs)) with (prodp e0 (f (a :: xs))).
      apply prodp_iffp.
      * apply provable_iffp_refl.
      * apply IHxs.
Qed.

End MonoTheorems.

Section AssocTheorems.

Context {e: expr}
        {Mono: Monotonicity L Gamma prodp}
        {Assoc: Associativity L Gamma prodp}.

Lemma prodp_assoc: forall x y z, |-- prodp x (prodp y z) <--> prodp (prodp x y) z.
Proof.
  intros.
  apply solve_andp_intros.
  + apply prodp_assoc1.
  + apply prodp_assoc2.
Qed.

Context {LU: LeftUnit L Gamma e prodp}
        {RU: RightUnit L Gamma e prodp}.

Lemma assoc_fold_left_fold_right_equiv: forall xs,
  |-- fold_left prodp xs e <--> fold_right prodp e xs.
Proof.
  intros.
  apply solve_andp_intros.
  + apply assoc_fold_left_fold_right.
  + apply assoc_fold_right_fold_left.
Qed.

Lemma assoc_prodp_fold_left_equiv: forall xs1 xs2,
  |-- prodp (fold_left prodp xs1 e) (fold_left prodp xs2 e) <--> fold_left prodp (xs1 ++ xs2) e.
Proof.
  intros.
  apply solve_andp_intros.
  + apply assoc_prodp_fold_left.
  + apply assoc_fold_left_app.
Qed.

End AssocTheorems.

Section CommAssocTheorems.

Context {e: expr}
        {Mono: Monotonicity L Gamma prodp}
        {Comm: Commutativity L Gamma prodp}
        {Assoc: Associativity L Gamma prodp}.

Lemma assoc_fold_left_Permutation: forall x ys1 ys2,
  Permutation ys1 ys2 ->
  |-- fold_left prodp ys1 x <--> fold_left prodp ys2 x.
Proof.
  intros.
  pose proof @proper_permutation_fold_left _ _ _ _ prodp.
  assert (forall x y, |-- x <--> y -> forall z1 z2, z1 = z2 -> |-- prodp x z1 <--> prodp y z2)
    by (intros; subst; apply prodp_iffp; [auto | apply provable_iffp_refl]).
  specialize (H0 H1); clear H1.
  assert (forall x1 x2 y z, |-- x1 <--> x2 -> |-- prodp (prodp x1 y) z <--> prodp (prodp x2 z) y).
  {
    intros.
    rewrite <- !prodp_assoc.
    apply prodp_iffp; [auto | apply prodp_comm].
  }
  specialize (H0 H1); clear H1.
  apply H0; auto.
  apply provable_iffp_refl.
Qed.

End CommAssocTheorems.

End DerivableRulesFromPatterns.

Section ProofTheoryPatterns.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}.

Lemma Build_LeftUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, |-- prodp e x <--> x) ->
  LeftUnit L Gamma e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x); revert H; AddSequentCalculus.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim1; eauto.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim2; eauto.
Qed.

Lemma Build_RightUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, |-- prodp x e <--> x) ->
  RightUnit L Gamma e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x); revert H; AddSequentCalculus.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim1; eauto.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim2; eauto.
Qed.

Lemma Build_Associativity': forall {prodp: expr -> expr -> expr},
  (forall x y z: expr, |-- prodp (prodp x y) z <--> prodp x (prodp y z)) ->
  Associativity L Gamma prodp.
Proof.
  intros.
  constructor; intros; specialize (H x y z); revert H; AddSequentCalculus.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim2; eauto.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim1; eauto.
Qed.

End ProofTheoryPatterns.

Section PatternInstances.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}.

Lemma impp_andp_Adjoint: Adjointness L Gamma andp impp.
Proof.
  constructor; AddSequentCalculus.
  intros; split; intros.
  + eapply modus_ponens; [| exact H].
    apply impp_uncurry.
  + eapply modus_ponens; [| exact H].
    apply impp_curry.
Qed.

Lemma andp_Comm: Commutativity L Gamma andp.
Proof.
  constructor.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  eapply deduction_andp_elim1.
  rewrite <- provable_derivable.
  apply andp_comm.
Qed.

Lemma andp_Mono: Monotonicity L Gamma andp.
Proof.
  eapply @Adjoint2Mono.
  + auto.
  + apply impp_andp_Adjoint.
  + apply andp_Comm.
Qed.

Lemma andp_LU: LeftUnit L Gamma TT andp.
Proof.
  intros.
  apply Build_LeftUnit'.
  intros.
  apply truep_andp.
Qed.

Lemma andp_RU: RightUnit L Gamma TT andp.
Proof.
  intros.
  apply Build_RightUnit'.
  intros.
  apply andp_truep.
Qed.

Lemma andp_Assoc: Associativity L Gamma andp.
Proof.
  intros.
  apply Build_Associativity'.
  intros.
  apply andp_assoc.
Qed.

End PatternInstances.

Section DerivableRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}.

Lemma falsep_andp: forall x: expr,
  |-- FF && x <--> FF.
Proof.
  intros.
  apply (@falsep_prodp _ _ _ _ _ _ _ _ impp_andp_Adjoint).
Qed.

Lemma andp_falsep: forall x: expr,
  |-- x && FF <--> FF.
Proof.
  intros.
  apply (@prodp_falsep _ _ _ _ _ _ _ _ impp_andp_Adjoint andp_Comm).
Qed.

Lemma andp_orp_distr_l: forall x y z: expr,
  |-- (x || y) && z <--> (x && z) || (y && z).
Proof.
  intros.
  apply (@prodp_orp_distr_l _ _ _ _ _ _ _ _ impp_andp_Adjoint).
Qed.

Lemma andp_orp_distr_r: forall x y z: expr,
  |-- x && (y || z) <--> (x && y) || (x && z).
Proof.
  intros.
  apply (@prodp_orp_distr_r _ _ _ _ _ _ _ _ impp_andp_Adjoint andp_Comm).
Qed.

Definition multi_and (xs: list expr): expr := fold_left andp xs truep.

Lemma multi_and_spec: forall (xs: list expr),
  |-- multi_and xs <--> fold_right andp TT xs.
Proof.
  intros.
  unfold multi_and.
  pose proof @assoc_fold_left_fold_right_equiv _ _ _ _ _ _ andp TT andp_Mono andp_Assoc andp_LU andp_RU.
  auto.
Qed.

Lemma multi_and_unfold_right_assoc:  forall (xs: list expr),
  |-- multi_and xs <-->
      (fix f xs :=
         match xs with
         | nil => TT
         | x :: nil => x
         | x :: xs0 => x && (f xs0)
         end) xs.
Proof.
  intros.
  rewrite multi_and_spec.
  pose proof @fold_right_prodp_unfold _ _ _ _ _ _ andp andp_Mono TT andp_RU.
  auto.
Qed.

Lemma multi_and_unfold_left_assoc:  forall (xs: list expr),
  |-- multi_and xs <-->
      match xs with
      | nil => TT
      | x :: xs0 =>
        (fix f xs x :=
           match xs with
           | nil => x
           | x0 :: xs0 => f xs0 (x && x0)
           end) xs0 x
      end.
Proof.
  intros.
  pose proof @fold_left_prodp_unfold _ _ _ _ _ _ andp andp_Mono TT andp_LU.
  apply H.
Qed.

Lemma multi_and_multi_imp: forall (xs: list expr) (y: expr),
  |-- (multi_and xs --> y) <--> (multi_imp xs y).
Proof.
  intros.
  unfold multi_imp.
  rewrite multi_and_spec.
  induction xs as [| x xs].
  + simpl.
    apply truep_impp.
  + simpl.
    rewrite <- impp_curry_uncurry.
    apply impp_proper_iffp; [apply provable_iffp_refl |].
    auto.
Qed.

End DerivableRules.

