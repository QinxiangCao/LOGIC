Require Import Logic.SeparationLogic.Tactics.Language.
Require Export Coq.Lists.List.

Local Open Scope shallow_syntax.
Local Open Scope list_scope.

Fixpoint delete_nth {A} (n: nat) (xs: list A) {struct n} : list A :=
 match n, xs with
 | O, y::ys => ys
 | S n', y::ys =>y :: delete_nth n' ys
 | _ , _ => nil
 end.

Fixpoint fold_right_sepcon (l: list expr) : expr :=
 match l with
 | nil => emp
 | b::r => b * fold_right_sepcon r
 end.

Definition fold_left_sepconx (l: list expr) : expr :=
match l with
| nil => emp
| a::l => (fix fold_left_sepconx (a: expr) (l: list expr) {struct l}: expr :=
          match l with
          | nil => a
          | b :: l => fold_left_sepconx (sepcon a b) l
          end) a l
end.

Lemma fold_left_sepconx_eq:
  forall l, fold_left_sepconx l = fold_right_sepcon l.
Proof.
Admitted.

Inductive find_nth_preds_rec {A: Type} (pred: A -> Prop): nat -> list A -> option (nat * A) -> Prop :=
| find_nth_preds_rec_cons_head: forall n R0 R, pred R0 -> find_nth_preds_rec pred n (R0 :: R) (Some (n, R0))
| find_nth_preds_rec_cons_tail: forall n R0 R R_res, find_nth_preds_rec pred (S n) R R_res -> find_nth_preds_rec pred n (R0 :: R) R_res
| find_nth_preds_rec_nil: forall n, find_nth_preds_rec pred n nil None.
Inductive find_nth_preds {A: Type} (pred: A -> Prop): list A -> option (nat * A) -> Prop :=
| find_nth_preds_constr: forall R R_res, find_nth_preds_rec pred 0 R R_res -> find_nth_preds pred R R_res.

Ltac find_nth_rec tac :=
  first [ simple eapply find_nth_preds_rec_cons_head; tac
        | simple eapply find_nth_preds_rec_cons_tail; find_nth_rec tac
        | simple eapply find_nth_preds_rec_nil].
Ltac find_nth tac :=
  eapply find_nth_preds_constr; find_nth_rec tac.

Inductive syntactic_cancel: list expr -> list expr -> list expr -> list expr -> Prop :=
| syntactic_cancel_nil: forall R, syntactic_cancel R nil R nil
| syntactic_cancel_cons_succeed: forall n R0 R L0 L F Res,
    find_nth_preds (fun R0 => |-- R0 --> L0) R (Some (n, R0)) ->
    syntactic_cancel (delete_nth n R) L F Res ->
    syntactic_cancel R (L0 :: L) F Res
| syntactic_cancel_cons_fail: forall R L0 L F Res,
    find_nth_preds (fun R0 => |-- R0 --> L0) R None ->
    syntactic_cancel R L F Res ->
    syntactic_cancel R (L0 :: L) F (L0 :: Res).

Lemma syntactic_cancel_cons: forall nR0 R L0 L F Res,
  find_nth_preds (fun R0 => |-- R0 --> L0) R nR0 ->
  syntactic_cancel match nR0 with
                   | Some (n, _) => delete_nth n R
                   | None => R
                   end L F Res ->
  syntactic_cancel R (L0 :: L) F (let Res' := Res in
                                 match nR0 with
                                 | Some _ => Res'
                                 | None => L0 :: Res'
                                 end).
Proof.
Admitted.

Lemma syntactic_cancel_solve1: forall F,
  |-- fold_right_sepcon F --> fold_right_sepcon nil * fold_right_sepcon F.
Proof.
Admitted.

Lemma syntactic_cancel_solve3:
  |-- fold_right_sepcon nil --> fold_right_sepcon nil.
Proof.
Admitted.

Lemma syntactic_cancel_spec1: forall G1 L1 G2 L2 F,
  syntactic_cancel G1 L1 G2 L2 ->
  |-- fold_right_sepcon G2 --> fold_right_sepcon L2 * F ->
  |-- fold_right_sepcon G1 --> fold_right_sepcon L1 * F.
Proof.
Admitted.

Lemma syntactic_cancel_spec2: forall G1 L1 G2 L2 G3 L3 F,
  syntactic_cancel G1 L1 G2 L2 ->
  syntactic_cancel G2 L2 G3 L3 ->
  |-- fold_right_sepcon G3 --> fold_right_sepcon L3 * F ->
  |-- fold_right_sepcon G1 --> fold_right_sepcon L1 * F.
Proof.
Admitted.

Lemma syntactic_cancel_spec3: forall G1 L1 G2 L2,
  syntactic_cancel G1 L1 G2 L2 ->
  |-- fold_right_sepcon G2 --> fold_right_sepcon L2 ->
  |-- fold_right_sepcon G1 --> fold_right_sepcon L1.
Proof.
Admitted.

Ltac syntactic_cancel local_tac :=
  repeat first
         [ simple apply syntactic_cancel_nil
         | simple apply syntactic_cancel_cons;
           [ find_nth local_tac
           | cbv iota; unfold delete_nth; cbv zeta iota
           ]
         ].

Ltac cancel_for_evar_frame' local_tac :=
  eapply syntactic_cancel_spec1;
  [ syntactic_cancel local_tac
  | cbv iota; cbv zeta beta;
    first [ match goal with
            | |- |-- _ --> _ * fold_right_sepcon ?F => try unfold F
            end;
            simple apply syntactic_cancel_solve1
          | match goal with
            | |- |-- fold_right_sepcon ?A --> fold_right_sepcon ?B * _ => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].
(**)

Ltac cancel_for_normal local_tac :=
  eapply syntactic_cancel_spec3;
  [ syntactic_cancel local_tac
  | cbv iota; cbv zeta beta;
    first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- |-- fold_right_sepcon ?A --> fold_right_sepcon ?B => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].

Inductive construct_fold_right_sepcon_rec: expr -> list expr -> list expr -> Prop :=
| construct_fold_right_sepcon_rec_sepcon: forall P Q R R' R'',
    construct_fold_right_sepcon_rec Q R R' ->
    construct_fold_right_sepcon_rec P R' R'' ->
    construct_fold_right_sepcon_rec (P * Q) R R''
| construct_fold_right_sepcon_rec_emp: forall R,
    construct_fold_right_sepcon_rec emp R R
| construct_fold_right_sepcon_rec_single: forall P R,
    construct_fold_right_sepcon_rec P R (P :: R).

Inductive construct_fold_right_sepcon: expr -> list expr-> Prop :=
| construct_fold_right_sepcon_constr: forall P R,
    construct_fold_right_sepcon_rec P nil R ->
    construct_fold_right_sepcon P R.

Ltac construct_fold_right_sepcon_rec :=
  match goal with
  | |- construct_fold_right_sepcon_rec (sepcon _ _) _ _ =>
         eapply construct_fold_right_sepcon_rec_sepcon;
         [construct_fold_right_sepcon_rec | construct_fold_right_sepcon_rec]
  | |- construct_fold_right_sepcon_rec emp _ _ =>
         apply construct_fold_right_sepcon_rec_emp
  | _ =>
         apply construct_fold_right_sepcon_rec_single
  end.

Ltac construct_fold_right_sepcon :=
  apply construct_fold_right_sepcon_constr;
  construct_fold_right_sepcon_rec.

Inductive merge_abnormal_expr: expr -> option expr -> option expr -> Prop :=
| merge_abnormal_expr_None: forall P, merge_abnormal_expr P None (Some P)
(*| merge_abnormal_expr_TT_Some: forall P, merge_abnormal_expr TT (Some P) (Some P)
| merge_abnormal_expr_Some_TT: forall P, merge_abnormal_expr P (Some TT) (Some P)*).

Inductive fold_abnormal_expr: list expr -> list expr -> option expr -> Prop :=
| fold_abnormal_expr_nil:
    fold_abnormal_expr nil nil None
(*| fold_abnormal_expr_TT: forall R res R' res',
    fold_abnormal_expr R R' res ->
    merge_abnormal_expr TT res res' ->
    fold_abnormal_expr (TT :: R) R' res'*)
| fold_abnormal_expr_fold: forall F R res R' res',
    fold_abnormal_expr R R' res ->
    merge_abnormal_expr (fold_right_sepcon F) res res' ->
    fold_abnormal_expr ((fold_right_sepcon F) :: R) R' res'
| fold_abnormal_expr_normal: forall P R R' res,
    fold_abnormal_expr R R' res ->
    fold_abnormal_expr (P :: R) (P :: R') res.

Ltac is_evar_def F := try first [is_var F; unfold F; fail 1 | fail 2 F "is not evar definition"].

Ltac merge_abnormal_expr :=
  first
  [ simple apply merge_abnormal_expr_None
  (*| simple apply merge_abnormal_expr_TT_Some
  | simple apply merge_abnormal_expr_Some_TT*)
  | fail 1000 "There should not be two fold_right_sepcon in the right side."
  ].

Ltac fold_abnormal_expr :=
  match goal with
  | |- fold_abnormal_expr nil _ _ =>
         simple apply fold_abnormal_expr_nil
  | |- fold_abnormal_expr (?P :: _) _ _ =>
         match P with
         (*| TT => simple eapply fold_abnormal_expr_TT; [fold_abnormal_expr | merge_abnormal_expr]
         | prop True => simple eapply fold_abnormal_expr_TT; [fold_abnormal_expr | merge_abnormal_expr]*)
         | fold_right_sepcon ?F =>
              is_evar_def F;
              simple eapply fold_abnormal_expr_fold; [fold_abnormal_expr | merge_abnormal_expr]
         | _ => simple apply fold_abnormal_expr_normal; fold_abnormal_expr
         end
  end.

Definition before_symbol_cancel (P Q: list expr) (res: option expr): Prop :=
  match res with
  | Some R => |-- fold_right_sepcon P --> fold_right_sepcon Q * R
  | None => |-- fold_right_sepcon P --> fold_right_sepcon Q
  end.

Lemma symbolic_cancel_setup: forall P P' Q Q' Q'' Qr,
  construct_fold_right_sepcon P P' ->
  construct_fold_right_sepcon Q Q' ->
  fold_abnormal_expr Q' Q'' Qr ->
  before_symbol_cancel P' Q'' Qr ->
  |-- P --> Q.
Proof.
Admitted.

Ltac cancel_seplog' local_tac :=
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_expr
  | match goal with
    | |- before_symbol_cancel _ _ None =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_normal local_tac
    | |- before_symbol_cancel _ _ (Some (fold_right_sepcon _)) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_evar_frame' local_tac
    (*| |- before_symbol_cancel _ _ (Some TT) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_TT local_tac
    | |- before_symbol_cancel _ _ (Some (prop True)) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_TT local_tac*)
    end
  ].

Ltac auto_cancel :=
  simple apply impp_refl.

Ltac cancel_seplog :=
  cancel_seplog' auto_cancel.

Section temp.
Parameter (A B C D E F G H I J K L M N O P Q R S T U V W X Y Z: Language.expr).
Local Open Scope shallow_syntax.

Lemma foo: forall P, P /\ P -> P.
Proof. intros. tauto. Qed.

Goal |-- (W --> T) * U --> S * V -> |-- (W --> T) * U * (V --> W) * (P * Q) * T --> T * S * V * Q * P * (V --> W).
  intros.
  cancel_seplog.
  auto.
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    (M * (N * O) * P) * (Q * R * S) * T * (U * V) * W * X
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (M * X * (N * W) * O) * P * Q * (T * S) * (V * R * U).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    (M * (N * O) * P) * (Q * R * S) * T * (U * V) * W * X *
    (M * (N * O) * P) * (Q * R * S) * T * (U * V) * W * X *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (M * X * (N * W) * O) * P * Q * (T * S) * (V * R * U) *
    (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (M * X * (N * W) * O) * P * Q * (T * S) * (V * R * U).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    (M * (N * O) * P) * (Q * R * S) * T * (U * V) * W * X *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    (M * (N * O) * P) * (Q * R * S) * T * (U * V) * W * X *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    (M * (N * O) * P) * (Q * R * S) * T * (U * V) * W * X
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (M * X * (N * W) * O) * P * Q * (T * S) * (V * R * U) *
    (M * X * (N * W) * O) * P * Q * (T * S) * (V * R * U) *
    (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (M * X * (N * W) * O) * P * Q * (T * S) * (V * R * U).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * C * D --> M * N * O * E ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * C * D * A * B * C * D
--> M * N * O * E * M * N * O * E ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H) *
    I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * C * D * A * B * C * D * A * B * C * D
--> M * N * O * M * N * O * E * E * M * N * O * E ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H) *
    I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H) *
    I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * C * D * E * F * G * H --> S * T * Q * X * U * V * W * R ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P)
--> (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R.
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * C * D * E * F * G * H * A * B * C * D * E * F * G * H
--> S * T * Q * X * U * V * W * R * S * T * Q * X * U * V * W * R ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P)
--> (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R *
    (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R.
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

Goal
|-- A * B * C * D * E * F * G * H * A * B * C * D * E * F * G * H * A * B * C * D * E * F * G * H
--> S * T * Q * X * U * V * W * R * S * T * Q * X * U * V * W * R * S * T * Q * X * U * V * W * R ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P)
--> (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R *
    (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R *
    (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R.
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_seplog;
  auto.
  Time
  Qed.

End temp.