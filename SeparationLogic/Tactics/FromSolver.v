Require Import Logic.SeparationLogic.Tactics.Language.
Require Export Coq.Lists.List.
Require Import Logic.lib.Coqlib.

Local Open Scope shallow_syntax.
Local Open Scope list_scope.

Inductive expr: Type :=
  | impp : expr -> expr -> expr
  | sepcon : expr -> expr -> expr
  | emp : expr
  | varp : nat -> expr.

Declare Scope deep_syntax.
Local Open Scope deep_syntax.

Notation "x --> y" := (impp x y) (at level 55, right associativity) : deep_syntax.
Notation "x * y" := (sepcon x y) (at level 40, left associativity) : deep_syntax.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| sepcon_emp1: forall x, provable (x * emp --> x)
| sepcon_emp2: forall x, provable (x --> x * emp)
| sepcon_comm_impp: forall x y, provable (x * y --> y * x)
| sepcon_assoc1: forall x y z, provable (x * (y * z) --> (x * y) * z)
| sepcon_mono: forall x1 x2 y1 y2,
    provable (x1 --> x2) -> provable (y1 --> y2) -> provable ((x1 * y1) --> (x2 * y2)).

Notation "|--  x" := (provable x) (at level 71, no associativity) : deep_syntax.

Fixpoint beq e1 e2 :=
  match e1, e2 with
  | emp, emp => true
  | varp x, varp y => EqNat.beq_nat x y
  | sepcon p11 p12, sepcon p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | impp p11 p12, impp p21 p22 => andb (beq p11 p21) (beq p12 p22)
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

(*
Definition rev (l: list nat): list nat :=
  (fix rev (l: list nat) (cont: list nat -> list nat): list nat :=
    match l with
    | nil => cont nil
    | a :: l0 => rev l0 (fun l => a :: cont l)
    end) l (fun l => l).
*)

Ltac reverse_cont l k :=
  match l with
  | @nil ?T => k (@nil T)
  | @cons _ ?h ?t =>
    let k' l :=
        let t' := k l in
        constr:(cons h t')
    in reverse_cont t k'
  end.
Ltac reverse l := reverse_cont l ltac:(fun l => l).

Ltac search_expr' n i l l0 :=
  match l with
  | nil => let len := length l0 in constr:((S len, n :: l0))
  | n :: ?t => constr:((i, l0))
  | _ :: ?t => let pi := pred i in search_expr' n pi t l0
  end.
Ltac search_expr n l := let len := length l in search_expr' n len l l.

Fixpoint reflect (e : expr) (tbl : list Language.expr) (default : Language.expr) : Language.expr :=
    match e with
    | varp n => nth (pred n) tbl default
    | sepcon e1 e2 => Language.sepcon (reflect e1 tbl default) (reflect e2 tbl default )
    | impp e1 e2 => Language.impp (reflect e1 tbl default) (reflect e2 tbl default)
    | emp => Language.emp
    end.

Ltac shallowTodeep' se l0 :=
  match se with
  | Language.sepcon ?sp ?sq =>
    match shallowTodeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowTodeep' sq l1 with
      | (?dq, ?l2) => constr:((sepcon dp dq, l2))
      end
    end
  | Language.impp ?sp ?sq =>
    match shallowTodeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowTodeep' sq l1 with
      | (?dq, ?l2) => constr:((impp dp dq, l2))
      end
    end
  | Language.emp => constr:((emp, l0))
  | ?sp => match search_expr sp l0 with
          | (?i, ?l1) => constr:((varp i, l1))
          end
  end.
Ltac shallowTodeep se :=
match shallowTodeep' se constr:(@nil Language.expr) with
  | (?de, ?tbl) =>
    let tbl' := reverse tbl in
    assert (reflect de tbl' se = se) by reflexivity
end.

Theorem reify_sound : forall (e : expr) table (default: Language.expr),
  provable e -> Language.provable (reflect e table default).
Admitted.

Theorem abstract_sound : forall (e' : expr) table (default: Language.expr),
  Language.provable (reflect e' table default) -> provable e'.
Admitted.

Definition flatten_imp (e : expr) : list expr * expr :=
    match e with
    | impp p q => (p :: nil, q)
    | _ => (nil, e)
    end.

Fixpoint flatten_sepcon (e : expr) : list expr :=
    match e with
    | sepcon p q => (flatten_sepcon p ++ flatten_sepcon q)
    | s => s :: nil
    end.

Definition flatten (e : expr) : list expr * list expr :=
   let (ctx, r) := flatten_imp e in
   (List.flat_map flatten_sepcon ctx, flatten_sepcon r).

(*
Definition all_in_context e :=
  let (es, rs) := flatten e in forallb (fun r => existsb (beq r) es) rs.
*)

Fixpoint cancel_deep_context es r : (list expr) * bool:=
  match es with
  | nil => (nil, false)
  | e :: et =>
    match (beq e r) with
    | true => (et, true)
    | false => let (et', isfind) := cancel_deep_context et r in (e :: et', (false || isfind)%bool)
    end
  end.

Fixpoint cancel_deep es rs : list expr * list expr:=
  match rs with
  | nil => (es, nil)
  | r :: rt =>
    match (cancel_deep_context es r) with
    | (es', true) => (cancel_deep es' rt)
    | (es', false) => let (es'', rt'') := cancel_deep es' rt in (es'', r :: rt'')
    end
  end.

Fixpoint unflatten_sepcon' et e : expr :=
  match et with
  | nil => e
  | ep :: et0 => unflatten_sepcon' et0 (sepcon e ep)
  end.

Definition unflatten_sepcon le : expr :=
  match le with
  | nil => emp
  | e :: et => unflatten_sepcon' et e
  end.

Definition unflatten (es rs : list expr) : expr:=
  impp (unflatten_sepcon es) (unflatten_sepcon rs).

Lemma cancel_solver_sound : forall e e' es rs es' rs',
  (es, rs) = flatten e ->
  (es', rs') = cancel_deep es rs ->
  e' = unflatten es' rs' ->
  provable e' ->
  provable e.
Admitted.

Ltac cancel_solver' se :=
  match shallowTodeep' se constr:(@nil Language.expr) with
    | (?de, ?tbl) =>
      let tbl' := reverse tbl in
      let p := eval compute in (flatten de) in
      let es := eval compute in (fst p) in
      let rs := eval compute in (snd p) in
      let p' := eval compute in (cancel_deep es rs) in
      let es' := eval compute in (fst p') in
      let rs' := eval compute in (snd p') in
      let de' := eval compute in (unflatten es' rs') in
      assert (@eq Language.expr (reflect de tbl' se) (se)) as ReflectH by reflexivity;
      assert (@eq (list expr * list expr) (es, rs) (flatten de)) as FlattenH by reflexivity;
      assert (@eq (list expr * list expr) (es', rs') (cancel_deep es rs)) as CancelH by reflexivity;
      assert (@eq expr de' (unflatten es' rs')) as UnflattenH by reflexivity;
      apply (reify_sound de tbl' se);
      apply (cancel_solver_sound de de' es rs es' rs');
      [ apply FlattenH
      | apply CancelH
      | apply UnflattenH
      | ];
    match goal with
        | [|- provable ?dr] =>
          apply (abstract_sound dr tbl' se);
          let rfl := eval compute in (reflect dr tbl' se) in change (Language.provable rfl)
    end;
    try apply Language.emp_refl;
    clear ReflectH FlattenH CancelH UnflattenH
  end.

Ltac cancel_solver :=
    match goal with
    | [|- Language.provable ?se] => cancel_solver' se
    end.

Section temp.
Parameter (A B C D E F G H I J K L M N O P Q R S T U V W X Y Z: Language.expr).
Local Open Scope shallow_syntax.

Lemma foo: forall P, P /\ P -> P.
Proof. intros. tauto. Qed.

Goal |-- (W --> T) * U --> S * V -> |-- (W --> T) * U * (V --> W) * (P * Q) * T --> T * S * V * Q * P * (V --> W).
  intros.
  cancel_solver.
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
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
  cancel_solver;
  auto.
  Time
  Qed.

End temp.