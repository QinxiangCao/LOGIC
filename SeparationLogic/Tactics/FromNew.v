Require Import Logic.SeparationLogic.Tactics.Language.
Require Export Coq.Lists.List.
Require Export Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.Coqlib.

Local Open Scope shallow_syntax.
Local Open Scope list_scope.

Section Deep.

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

End Deep.

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

Fixpoint reflect (de : expr) (tbl : list Language.expr) (default : Language.expr) : Language.expr :=
    match de with
    | varp n => nth (pred n) tbl default
    | sepcon e1 e2 => (reflect e1 tbl default) * (reflect e2 tbl default )
    | impp e1 e2 => (reflect e1 tbl default) --> (reflect e2 tbl default)
    | emp => Language.emp
    end.

Ltac shallowTodeep' se l0 :=
  match se with
  | ?sp * ?sq =>
    match shallowTodeep' sp l0 with
    | (?dp, ?l1) =>
      match shallowTodeep' sq l1 with
      | (?dq, ?l2) => constr:((sepcon dp dq, l2))
      end
    end
  | ?sp --> ?sq =>
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
    match de with
    | impp ?dep ?deq => constr:((dep, deq, tbl))
    end
  end.

Inductive tree_pos: Type :=
  | var_pos : Language.expr -> option positive -> tree_pos
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
  | sepcon dp dq, sepcon_pos tp tq =>
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
  | sepcon dp dq, sepcon_pos tp tq =>
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

Fixpoint unmark_sort' tep : option Language.expr :=
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
Definition unmark_sort tep : Language.expr :=
  match unmark_sort' tep with
  | Some sp => sp
  | None => Language.emp
  end.

Fixpoint flatten tep : list Language.expr :=
  match tep with
  | sepcon_pos tp tq => (flatten tp) ++ (flatten tq)
  | var_pos sp o =>
    match o with
    | None => sp :: nil
    | _ => nil
    end
  end.

Fixpoint unflatten' lep sp : Language.expr :=
  match lep with
  | nil => sp
  | sq :: lep' => unflatten' lep' (sp * sq)
  end.

Definition unflatten lep : Language.expr :=
  match lep with
  | nil => Language.emp
  | sp :: lep' => unflatten' lep' sp
  end.
(*
Definition cancel_different tep teq : Language.expr :=
  (unflatten (flatten tep)) --> (unflatten (flatten teq)).
*)
Definition cancel_different tep teq : Language.expr :=
  (unmark_sort tep) --> (unmark_sort teq).

Module PTree.

  Inductive tree (A : Type) : Type :=
    | Leaf : tree A
    | Node : tree A -> option A -> tree A -> tree A.

  Arguments Leaf {A}.
  Arguments Node [A].

  Definition empty {A : Type} := (Leaf : tree A).

  Fixpoint get (A : Type) (i : positive) (m : tree A) {struct i} : option A :=
    match m with
    | Leaf => None
    | Node l o r =>
        match i with
        | xH => o
        | xO ii => get A ii l
        | xI ii => get A ii r
        end
    end.

  Fixpoint get_rec' {A : Type} (i : positive) (m : tree A) (f : tree A -> tree A) : tree A :=
    match i with
    | xH => f m
    | xO ii => get_rec' ii m (fun m0 : tree A => match f m0 with
                                      | Leaf => Leaf
                                      | Node l o r => l
                                      end)
    | xI ii => get_rec' ii m (fun m0 : tree A => match f m0 with
                                      | Leaf => Leaf
                                      | Node l o r => r
                                      end)
    end.
  Definition get_rec {A : Type} (i : positive) (m : tree A) : option A :=
    match get_rec' i m (fun m0 : tree A => m0) with
    | Leaf => None
    | Node l o r => o
    end.

  Fixpoint set (A : Type) (i : positive) (v : A) (m : tree A) {struct i} : tree A :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf (Some v) Leaf
        | xO ii => Node (set A ii v Leaf) None Leaf
        | xI ii => Node Leaf None (set A ii v Leaf)
        end
    | Node l o r =>
        match i with
        | xH => Node l (Some v) r
        | xO ii => Node (set A ii v l) o r
        | xI ii => Node l o (set A ii v r)
        end
    end.

  Fixpoint set_rec' {A : Type} (i : positive) (v : A) (m : tree A) (f : tree A -> tree A) : tree A :=
    match m with
    | Leaf =>
        match i with
        | xH => f (Node Leaf (Some v) Leaf)
        | xO ii => set_rec' ii v Leaf (fun hole : tree A => f (Node hole None Leaf))
        | xI ii => set_rec' ii v Leaf (fun hole : tree A => f (Node Leaf None hole))
        end
    | Node l o r =>
        match i with
        | xH => f (Node l (Some v) r)
        | xO ii => set_rec' ii v l (fun hole : tree A => f (Node hole o r))
        | xI ii => set_rec' ii v r (fun hole : tree A => f (Node l o hole))
        end
    end.
  Definition set_rec {A : Type} (i : positive) (v : A) (m : tree A) : tree A :=
    set_rec' i v m (fun hole : tree A => hole).

End PTree.

Fixpoint mark_sort' tep m: PTree.tree Language.expr :=
  match tep with
  | sepcon_pos tp tq =>
    match mark_sort' tp m with
    | m' => mark_sort' tq m'
    end
  | var_pos sp o =>
    match o with
    | None => m
    | Some pos => PTree.set_rec pos sp m
    end
  end.
Definition mark_sort tep : PTree.tree Language.expr :=
  mark_sort' tep PTree.empty.

Definition cancel_same tep teq : Prop :=
  mark_sort tep = mark_sort teq.

Fixpoint restore' tep : Language.expr :=
  match tep with
  | sepcon_pos tp tq => (restore' tp) * (restore' tq)
  | var_pos sp o => sp
  end.
Definition restore tep teq : Language.expr :=
  (restore' tep) --> (restore' teq).

Fixpoint build' m p : Language.expr :=
  match m with
  | PTree.Leaf => p
  | PTree.Node l None r => build' l (build' r p)
  | PTree.Node l (Some v) r => build' l ((build' r p) * v)
  end.

Definition build m : Language.expr :=
  build' m Language.emp.

Lemma before_L1 : forall sp p,
  build (mark_sort (var_pos sp (Some p))) = sp.
Admitted.

Lemma provable_emp_sepcon2 : forall x,
  |-- x --> Language.emp * x.
Proof.
Admitted.

Lemma L1 : forall tep,
  |-- restore' tep --> unmark_sort tep * (build (mark_sort tep)).
Proof.
  intros.
  induction tep as [sp op|p1 IH1 p2 IH2].
  - compute.
    destruct op.
    + pose proof (before_L1 sp p) as before_L1; compute in before_L1.
      rewrite before_L1; clear before_L1.
      apply provable_emp_sepcon2.
    + apply Language.sepcon_emp2.
  - unfold restore'; fold restore'.
    unfold unmark_sort.
Admitted.

Lemma L2 : forall teq,
  |-- unmark_sort teq --> build (mark_sort teq) --> restore' teq.
Proof.
  intros.
  induction teq as [sq oq|q1 IH1 q2 IH2].
  - compute.
    destruct oq.
Admitted.

Lemma L3 : forall m1 m2,
  m1 = m2 ->
  |-- build m1 --> build m2.
Proof.
  intros.
  rewrite H.
  apply Language.provable_impp_refl.
Qed.

Lemma cancel_new_sound : forall tep teq,
  cancel_same tep teq ->
  |-- cancel_different tep teq ->
  |-- restore tep teq.
Proof.
  unfold restore, cancel_same, cancel_different.
  intros.
Admitted.

Ltac cancel_new' se :=
  match shallowTodeep se with
    | (?dep, ?deq, ?tbl) =>
    match shallowTotree se with
    | (?tep, ?teq) =>
    (*let tbl' := reverse tbl in*)
    let te' := eval compute in (cancel_mark dep deq tep teq) in
    let tep' := eval compute in (fst te') in
    let teq' := eval compute in (snd te') in
    apply (cancel_new_sound tep' teq');
    [ let same := eval compute in (cancel_same tep' teq') in change same;
      reflexivity
    | let different := eval compute in (cancel_different tep' teq') in change (Language.provable different);
    try apply Language.provable_emp_refl
    ]
    end
  end.

Ltac cancel_new :=
    match goal with
    | [|- Language.provable ?se] => cancel_new' se
    end.

Section temp.
Parameter (A B C D E F G H I J K L M N O P Q R S T U V W X Y Z: Language.expr).
Local Open Scope shallow_syntax.

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
|-- A * B * C * D --> M * N * O * E ->
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
  cancel_new;
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
  cancel_new;
  auto.
  Time
  Qed.

Goal
|-- A * B * C * D * E * F * G * H
--> S * T * Q * X * U * V * W * R ->
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
  cancel_new;
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
  cancel_new;
  auto.
  Time
  Qed.

End temp.