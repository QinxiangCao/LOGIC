Require Import Logic.SeparationLogic.Tactics.Language.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.PTree.

Local Open Scope shallow_syntax.
Local Open Scope list_scope.

Inductive expr_deep: Type :=
  | impp_deep : expr_deep -> expr_deep -> expr_deep
  | sepcon_deep : expr_deep -> expr_deep -> expr_deep
  | emp_deep : expr_deep
  | varp_deep : nat -> expr_deep.

Fixpoint beq e1 e2 :=
  match e1, e2 with
  | emp_deep, emp_deep => true
  | varp_deep x, varp_deep y => EqNat.beq_nat x y
  | sepcon_deep p11 p12, sepcon_deep p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | impp_deep p11 p12, impp_deep p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | _, _ => false
  end.

Ltac length_cont ls k :=
  match ls with
  | nil => k O
  | _ :: ?ls' => length_cont ls' ltac:(fun n => k (S n))
  end.
Ltac length ls := length_cont ls ltac:(fun l => l).

Ltac pred n :=
  match n with
  | O => O
  | S ?m => m
  end.

Ltac search_expr' n i l l0 :=
  match l with
  | nil => let len := length l0 in constr:((S len, n :: l0))
  | n :: ?t => constr:((i, l0))
  | _ :: ?t => let pi := pred i in search_expr' n pi t l0
  end.
Ltac search_expr n l := let len := length l in search_expr' n len l l.

Ltac shallowTodeep' se l0 :=
  match se with
  | ?sp * ?sq =>
    match shallowTodeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowTodeep' sq l1 with
      | (?dq, ?l2) => constr:((sepcon_deep dp dq, l2))
      end
    end
  | ?sp --> ?sq =>
    match shallowTodeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowTodeep' sq l1 with
      | (?dq, ?l2) => constr:((impp_deep dp dq, l2))
      end
    end
  | emp => constr:((emp_deep, l0))
  | ?sp => match search_expr sp l0 with
          | (?i, ?l1) => constr:((varp_deep i, l1))
          end
  end.

Ltac shallowTodeep se :=
  match shallowTodeep' se constr:(@nil expr) with
  | (?de, ?tbl) =>
    match de with
    | impp_deep ?dep ?deq => constr:((dep, deq, tbl))
    end
  end.

Inductive tree_pos: Type :=
  | var_pos : expr -> option positive -> tree_pos
  | sepcon_pos : tree_pos -> tree_pos -> tree_pos.

Ltac shallowTotree_odd se :=
  match se with
  |?sp * ?sq =>
    match shallowTotree_odd sp with
    | ?tp =>
      match shallowTotree_odd sq with
      | ?tq => constr:(sepcon_pos tp tq)
      end
    end
  | ?sp => constr:(var_pos sp None)
  end.

Ltac shallowTotree se :=
  match se with
  | ?sep --> ?seq =>
    match shallowTotree_odd sep with
    | ?tep =>
      match shallowTotree_odd seq with
      | ?teq => constr:((tep, teq))
      end
    end
  end.

Fixpoint cancel_mark_context dep q tep key : tree_pos * bool:=
  match dep, tep with
  | sepcon_deep dp dq, sepcon_pos tp tq =>
    match cancel_mark_context dp q tp key with
    | (tp', true) => ((sepcon_pos tp' tq), true)
    | (tp', false) =>
      match cancel_mark_context dq q tq key with
      | (tq', true) => ((sepcon_pos tp tq'), true)
      | (tq', false) => (tep, false)
      end
    end
  | p, (var_pos sp o) =>
    match (beq p q) with
    | true =>
      match o with
      | None => ((var_pos sp (Some key)), true)
      | _ => (tep, false)
      end
    | false => (tep, false)
    end
  | _, _ => (tep, false)
  end.

Fixpoint cancel_mark' dep deq tep teq key : tree_pos * tree_pos * positive :=
  match deq, teq with
  | sepcon_deep dp dq, sepcon_pos tp tq =>
    match (cancel_mark' dep dp tep tp key) with
    | (tep', tp', key') =>
      match (cancel_mark' dep dq tep' tq key') with
      | (tep'', tq', key'') => (tep'', sepcon_pos tp' tq', key'')
      end
    end
  | q, (var_pos sq o) =>
    match (cancel_mark_context dep q tep key) with
    | (tep', true) => (tep', (var_pos sq (Some key)), Pos.succ key)
    | (tep', false) => (tep', var_pos sq None, key)
    end
  | _, _ => (tep, teq, key)
  end.

Definition cancel_mark dep deq tep teq : tree_pos * tree_pos :=
  match (cancel_mark' dep deq tep teq xH) with
  | (tep', teq', key') => (tep', teq')
  end.

Fixpoint unmark_sort' tep : option expr :=
  match tep with
  | sepcon_pos tp tq =>
    match unmark_sort' tp with
    | None => unmark_sort' tq
    | Some sp =>
      match unmark_sort' tq with
      | None => Some sp
      | Some sq => Some (sp * sq)
      end
    end
  | var_pos sq o =>
    match o with
    | None => Some sq
    | _ => None
    end
  end.
Definition unmark_sort tep : expr :=
  match unmark_sort' tep with
  | Some sp => sp
  | None => emp
  end.

Definition cancel_different tep teq : expr :=
  (unmark_sort tep) --> (unmark_sort teq).

(*
Fixpoint flatten tep : list expr :=
  match tep with
  | sepcon_pos tp tq => (flatten tp) ++ (flatten tq)
  | var_pos sp o =>
    match o with
    | None => sp :: nil
    | _ => nil
    end
  end.

Fixpoint unflatten' lep sp : expr :=
  match lep with
  | nil => sp
  | sq :: lep' => unflatten' lep' (sp * sq)
  end.

Definition unflatten lep : expr :=
  match lep with
  | nil => emp
  | sp :: lep' => unflatten' lep' sp
  end.

Definition cancel_different tep teq : expr :=
  (unflatten (flatten tep)) --> (unflatten (flatten teq)).
*)

Fixpoint mark_sort' tep m: PTree.tree expr :=
  match tep with
  | sepcon_pos tp tq =>
    match mark_sort' tp m with
    | m' => mark_sort' tq m'
    end
  | var_pos sq o =>
    match o with
    | None => m
    | Some pos =>
      match PTree.get_rec expr pos m with
      | None => PTree.set_rec expr pos sq m
      | Some sp => PTree.set_rec expr pos (sp * sq) m
      end
    end
  end.
Definition mark_sort tep : PTree.tree expr :=
  mark_sort' tep PTree.empty.

Definition cancel_same tep teq : Prop :=
  mark_sort tep = mark_sort teq.

Fixpoint restore' tep : expr :=
  match tep with
  | sepcon_pos tp tq => (restore' tp) * (restore' tq)
  | var_pos sp o => sp
  end.
Definition restore tep teq : expr :=
  (restore' tep) --> (restore' teq).

Section AxiomClass2.

Lemma sepcon_assoc2 : forall x y z,
  |-- (x * y) * z --> (x * (y * z)).
Proof.
  intros.
  rewrite (sepcon_comm_impp (x * y) z).
  rewrite (sepcon_assoc1 z x y).
  rewrite (sepcon_comm_impp (z * x) y).
  rewrite (sepcon_assoc1 y z x).
  rewrite (sepcon_comm_impp (y * z) x).
  apply provable_impp_refl.
Qed.

Lemma switch : forall x y p q,
  |-- x * y * (p * q) --> x * p * (y * q).
Proof.
  intros.
  rewrite <- (sepcon_assoc1 x p (y * q)).
  rewrite <- (sepcon_comm_impp (y * q) p).
  rewrite <- (sepcon_assoc1 y q p).
  rewrite <- (sepcon_comm_impp p q).
  apply sepcon_assoc2.
Qed.

End AxiomClass2.

Section Proof.

Fixpoint build l : expr :=
  match l with
  | nil => emp
  | p :: l' => p * build l'
  end.

Lemma build_cons : forall l1 l2 e,
  |-- build (l1 ++ e :: l2) --> build (l1 ++ l2) * e.
Proof.
  intros.
  induction l1; simpl.
  - apply sepcon_comm_impp.
  - rewrite IHl1.
    apply sepcon_assoc1.
Qed.

Lemma sepcon_build : forall l1 l2 e,
  |-- build (l1 ++ l2) * e --> build (l1 ++ e :: l2).
Proof.
  intros.
  induction l1; simpl.
  - apply sepcon_comm_impp.
  - rewrite <- IHl1.
    apply sepcon_assoc2.
Qed.

Lemma add1 : forall e' p m,
  |-- build (PTree.elements expr (mark_sort' (var_pos e' (Some p)) m))
  --> build (PTree.elements expr m) * e'.
Proof.
  intros.
  unfold mark_sort'.
  destruct (PTree.get_rec expr p m) eqn:?H.
  - pose proof (PTree.elements_set_some expr p e (e * e') m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite build_cons. rewrite <- sepcon_build.
    apply sepcon_assoc1.
  - pose proof (PTree.elements_set_none expr p e' m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite build_cons.
    apply provable_impp_refl.
Qed.

Lemma add2 : forall e' p m,
  |-- build (PTree.elements expr m) * e'
  --> build (PTree.elements expr (mark_sort' (var_pos e' (Some p)) m)).
Proof.
  intros.
  unfold mark_sort'.
  destruct (PTree.get_rec expr p m) eqn:?H.
  - pose proof (PTree.elements_set_some expr p e (e * e') m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite build_cons. rewrite <- sepcon_build.
    apply sepcon_assoc2.
  - pose proof (PTree.elements_set_none expr p e' m).
    apply H0 in H; clear H0.
    destruct H as [l1]; destruct H as [l2].
    destruct H as [H1 H2].
    rewrite H1, H2.
    rewrite <- sepcon_build.
    apply provable_impp_refl.
Qed.

Lemma L1_before1 : forall sp p,
  |-- sp --> build (PTree.elements expr (mark_sort (var_pos sp (Some p)))).
Proof.
  intros.
  unfold mark_sort, mark_sort'.
  rewrite PTree.get_empty.
  rewrite PTree.elements_set_empty.
  unfold build.
  apply sepcon_emp2.
Qed.

Lemma L1_before2 : forall p1 p2,
  |-- unmark_sort p1 * unmark_sort p2 --> unmark_sort (sepcon_pos p1 p2).
Proof.
  intros.
  unfold unmark_sort.
  unfold unmark_sort'; fold unmark_sort'.
  destruct (unmark_sort' p1), (unmark_sort' p2).
  - apply provable_impp_refl.
  - apply sepcon_emp1.
  - rewrite sepcon_comm_impp; apply sepcon_emp1.
  - apply sepcon_emp1.
Qed.

Lemma L1_before3 : forall p1 p2,
  |-- build (PTree.elements expr (mark_sort p1)) * build (PTree.elements expr (mark_sort p2)) --> build (PTree.elements expr (mark_sort (sepcon_pos p1 p2))).
Proof.
  intros.
  unfold  mark_sort.
  unfold mark_sort'; fold mark_sort'.
  set (m1 := mark_sort' p1 PTree.empty) at 1.
  set (m3 := mark_sort' p1 PTree.empty).
  set (m2 := PTree.empty).
  assert (|-- build (PTree.elements expr m1) * build (PTree.elements expr m2) --> build (PTree.elements expr m3)).
  { unfold m2, PTree.empty, PTree.elements, PTree.xelements. apply sepcon_emp1. }
  clearbody m1 m2 m3.
  revert m1 m2 m3 H.
  induction p2; intros.
  - destruct o.
    + rewrite add1.
      rewrite <- add2.
      rewrite sepcon_assoc1.
      rewrite H.
      apply provable_impp_refl.
    + auto.
  - apply IHp2_1 in H.
    apply IHp2_2 in H.
    auto.
Qed.

Lemma L1 : forall tep,
  |-- restore' tep --> unmark_sort tep * (build (PTree.elements expr (mark_sort tep))).
Proof.
  intros.
  induction tep as [sp op|p1 IH1 p2 IH2]; unfold restore'; fold restore'.
  - unfold unmark_sort, unmark_sort'.
    destruct op.
    + pose proof (L1_before1 sp p) as L1_before1; compute in L1_before1.
      rewrite <- L1_before1; clear L1_before1.
      rewrite <- sepcon_comm_impp.
      apply sepcon_emp2.
    + apply sepcon_emp2.
  - rewrite IH1, IH2.
    rewrite <- L1_before2, <- L1_before3.
    apply switch.
Qed.

Lemma L2_before1 : forall sq p,
  |-- build (PTree.elements expr (mark_sort (var_pos sq (Some p)))) --> sq.
Proof.
  intros.
  unfold mark_sort, mark_sort'.
  rewrite PTree.get_empty.
  rewrite PTree.elements_set_empty.
  unfold build.
  apply sepcon_emp1.
Qed.

Lemma L2_before2 : forall q1 q2,
  |-- unmark_sort (sepcon_pos q1 q2) --> unmark_sort q1 * unmark_sort q2.
Proof.
  intros.
  unfold unmark_sort.
  unfold unmark_sort'; fold unmark_sort'.
  destruct (unmark_sort' q1), (unmark_sort' q2).
  - apply provable_impp_refl.
  - apply sepcon_emp2.
  - rewrite <- sepcon_comm_impp; apply sepcon_emp2.
  - apply sepcon_emp2.
Qed.

Lemma L2_before3 : forall q1 q2,
  |-- build (PTree.elements expr (mark_sort (sepcon_pos q1 q2))) --> build (PTree.elements expr (mark_sort q1)) * build (PTree.elements expr (mark_sort q2)).
Proof.
  intros.
  unfold  mark_sort.
  unfold mark_sort'; fold mark_sort'.
  set (m1 := mark_sort' q1 PTree.empty) at 2.
  set (m3 := mark_sort' q1 PTree.empty).
  set (m2 := PTree.empty).
  assert (|-- build (PTree.elements expr m3) --> build (PTree.elements expr m1) * build (PTree.elements expr m2)).
  { unfold m2, PTree.empty, PTree.elements, PTree.xelements. apply sepcon_emp2. }
  clearbody m1 m2 m3.
  revert m1 m2 m3 H.
  induction q2; intros.
  - destruct o.
    + rewrite add1.
      rewrite <- add2.
      rewrite <- sepcon_assoc2.
      rewrite H.
      apply provable_impp_refl.
    + auto.
  - apply IHq2_1 in H.
    apply IHq2_2 in H.
    auto.
Qed.

Lemma L2 : forall teq,
  |-- unmark_sort teq * build (PTree.elements expr (mark_sort teq)) --> restore' teq.
Proof.
  intros.
  induction teq as [sq oq|q1 IH1 q2 IH2]; unfold restore'; fold restore'.
  - unfold unmark_sort, unmark_sort'.
    destruct oq.
    + pose proof (L2_before1 sq p) as L2_before1; compute in L2_before1.
      rewrite L2_before1; clear L2_before1.
      rewrite sepcon_comm_impp.
      apply sepcon_emp1.
    + apply sepcon_emp1.
  - rewrite <- IH1, <- IH2.
    rewrite L2_before2, L2_before3.
    apply switch.
Qed.

Lemma L3 : forall m1 m2,
  m1 = m2 ->
  |-- build (PTree.elements expr m1) --> build (PTree.elements expr m2).
Proof.
  intros.
  rewrite H.
  apply provable_impp_refl.
Qed.

End Proof.

Lemma cancel_new_sound : forall tep teq,
  cancel_same tep teq ->
  |-- cancel_different tep teq ->
  |-- restore tep teq.
Proof.
  unfold restore, cancel_same, cancel_different.
  intros tep teq CS CD.
  apply L3 in CS.
  rewrite L1, CS, CD.
  apply L2.
Qed.

Ltac cancel_new' se :=
  match shallowTodeep se with
    | (?dep, ?deq, ?tbl) =>
    match shallowTotree se with
    | (?tep, ?teq) =>
    let te' := eval compute in (cancel_mark dep deq tep teq) in
    let tep' := eval compute in (fst te') in
    let teq' := eval compute in (snd te') in
    apply (cancel_new_sound tep' teq');
    [ let same := eval compute in (cancel_same tep' teq') in change same;
      reflexivity
    | let different := eval compute in (cancel_different tep' teq') in change (provable different);
    try apply provable_impp_refl
    ]
    end
  end.

Ltac cancel_new :=
    match goal with
    | [|- |-- ?se] => cancel_new' se
    end.

Section Temp.
Parameter (A B C D E F G H I J K L M N O P Q R S T U V W X Y Z: expr).

Lemma foo: forall P, P /\ P -> P.
Proof. intros. tauto. Qed.

Goal |-- (W --> T) * U --> S * V -> |-- (W --> T) * U * (V --> W) * (P * Q) * T --> T * S * V * Q * P * (V --> W).
  intros.
  cancel_new.
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
  cancel_new;
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
  cancel_new;
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
  cancel_new;
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
  cancel_new;
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
  cancel_new;
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
  cancel_new;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) --> M * N * (O * E) ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_new;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * A * B * (C * D)
--> M * N * O * E * (M * N) * (O * E) ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H) *
    I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H).
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_new;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * A * B * (C * D) * A * B * (C * D)
--> M * N * O * (M * N) * (O * E) * E * (M * N) * (O * E) ->
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
  cancel_new;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H))
--> S * T * Q * X * U * (V * W) * R ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P)
--> (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R.
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_new;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * A * B * (C * D) * (E * F * (G * H))
--> S * T * Q * X * U * (V * W) * R * (S * T * Q) * X * U * (V * W) * R ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) * (M * (N * O) * P)
--> (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R *
    (P * (I * J * (S * T)) * Q) * X * (U * M * N) * (O * (L * K * V) * W) * R.
  intros.
  Time
  apply foo; split;
    apply foo; split;
      apply foo; split;
  cancel_new;
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * A * B * (C * D) * (E * F * (G * H)) * A * B * (C * D) * (E * F * (G * H))
--> S * T * Q * X * U * (V * W) * R * (S * T * Q) * X * U * (V * W) * R * (S * T * Q) * X * U * (V * W) * R ->
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
  cancel_new;
  auto.
  Time
  Qed.

End Temp.