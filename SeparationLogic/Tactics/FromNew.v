Require Import Logic.SeparationLogic.Tactics.Language.
Require Export Coq.Lists.List.
Require Export Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.Coqlib.

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

Fixpoint reflect (de : expr_deep) (tbl : list expr) (default : expr) : expr :=
    match de with
    | varp_deep n => nth (pred n) tbl default
    | sepcon_deep e1 e2 => (reflect e1 tbl default) * (reflect e2 tbl default )
    | impp_deep e1 e2 => (reflect e1 tbl default) --> (reflect e2 tbl default)
    | emp_deep => emp
    end.

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

  Fixpoint get_rec' (A : Type) (i : positive) (m : tree A) (f : tree A -> tree A) : tree A :=
    match i with
    | xH => f m
    | xO ii => get_rec' A ii m (fun m0 : tree A => match f m0 with
                                      | Leaf => Leaf
                                      | Node l o r => l
                                      end)
    | xI ii => get_rec' A ii m (fun m0 : tree A => match f m0 with
                                      | Leaf => Leaf
                                      | Node l o r => r
                                      end)
    end.
  Definition get_rec (A : Type) (i : positive) (m : tree A) : option A :=
    match get_rec' A i m (fun m0 : tree A => m0) with
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

  Fixpoint set_rec' (A : Type) (i : positive) (v : A) (m : tree A) (f : tree A -> tree A) : tree A :=
    match m with
    | Leaf =>
        match i with
        | xH => f (Node Leaf (Some v) Leaf)
        | xO ii => set_rec' A ii v Leaf (fun hole : tree A => f (Node hole None Leaf))
        | xI ii => set_rec' A ii v Leaf (fun hole : tree A => f (Node Leaf None hole))
        end
    | Node l o r =>
        match i with
        | xH => f (Node l (Some v) r)
        | xO ii => set_rec' A ii v l (fun hole : tree A => f (Node hole o r))
        | xI ii => set_rec' A ii v r (fun hole : tree A => f (Node l o hole))
        end
    end.
  Definition set_rec (A : Type) (i : positive) (v : A) (m : tree A) : tree A :=
    set_rec' A i v m (fun hole : tree A => hole).

  Fixpoint xelements (A : Type) (m : tree A) (k : list A) {struct m} : list A :=
  match m with
  | Leaf => k
  | Node l None r =>
    xelements A l (xelements A r k)
  | Node l (Some x) r =>
    xelements A l (x :: xelements A r k)
  end.
  Definition elements (A : Type) (m : tree A) :=
  xelements A m nil.

  Goal forall A p x,
  elements A (set A p x empty) = x :: nil.
  intros.
  induction p.
  - compute.
    fold set. fold xelements.
    auto.
  - compute.
    fold set. fold xelements.
    auto.
  - compute.
    auto.
  Qed.

  Lemma elements_single : forall A p x,
  elements A (set_rec A p x empty) = x :: nil.
Proof.
  intros.
  unfold set_rec.
  set (f := fun hole : tree A => hole).
  assert (forall t, elements A t = elements A (f t)).
  subst; auto.
  clearbody f.
  revert f H.
  induction p; intros.
  - unfold set_rec', empty. fold set_rec'.
    apply IHp.
    intros t'; rewrite <- H.
    subst; auto.
  - unfold set_rec', empty. fold set_rec'.
    apply IHp.
    intros t'; rewrite <- H.
    subst; auto.
  - unfold set_rec', empty.
    rewrite <- H.
    subst; auto.
Qed.

End PTree.

Fixpoint mark_sort' tep m: PTree.tree expr :=
  match tep with
  | sepcon_pos tp tq =>
    match mark_sort' tp m with
    | m' => mark_sort' tq m'
    end
  | var_pos sp o =>
    match o with
    | None => m
    | Some pos => PTree.set_rec expr pos sp m
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

End AxiomClass2.

Section Proof.

Fixpoint build' l p: expr :=
  match l with
  | nil => p
  | q :: l' => build' l' (p * q)
  end.
Fixpoint build l : expr :=
  match l with
  | nil => emp
  | p :: l' => build' l' p
  end.

Lemma switch : forall x y p q,
  |-- x * y * (p * q) --> x * p * (y * q).
Proof.
  intros.
  rewrite <- (sepcon_assoc1 x p (y * q)).
  rewrite <- (sepcon_comm_impp (y * q) p).
  rewrite <- (sepcon_assoc1 y q p).
  rewrite <- (sepcon_comm_impp p q).
  rewrite (sepcon_comm_impp (x * y) (p * q)).
  rewrite (sepcon_assoc1 (p * q) x y).
  rewrite (sepcon_comm_impp ((p * q) * x) y).
  rewrite (sepcon_assoc1 y (p * q) x).
  rewrite (sepcon_comm_impp (y * (p * q)) x).
  apply provable_impp_refl.
Qed.

Lemma L1_before1 : forall sp p,
  |-- sp --> build (PTree.elements expr (mark_sort (var_pos sp (Some p)))).
Proof.
  intros.
  unfold mark_sort, mark_sort'.
  rewrite PTree.elements_single.
  compute.
  apply provable_impp_refl.
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
  set (m1 := mark_sort' p1 PTree.empty).
  induction p2.
  2:{ unfold mark_sort'; fold mark_sort'. (*
  - unfold mark_sort'. fold mark_sort'.
    destruct o.
    + rewrite PTree.elements_single.
      
    + compute.
        apply sepcon_emp1.*)
Admitted.

Lemma L1 : forall tep,
  |-- restore' tep --> unmark_sort tep * (build (PTree.elements expr (mark_sort tep))).
Proof.
  intros.
  induction tep as [sp op|p1 IH1 p2 IH2].
  - compute.
    destruct op.
    + pose proof (L1_before1 sp p) as L1_before1; compute in L1_before1.
      rewrite <- L1_before1; clear L1_before1.
      rewrite <- sepcon_comm_impp.
      apply sepcon_emp2.
    + apply sepcon_emp2.
  - unfold restore'; fold restore'.
    rewrite IH1, IH2.
    rewrite <- L1_before2, <- L1_before3.
    apply switch.
Qed.

Lemma L2_before1 : forall sq p,
  |-- build (PTree.elements expr (mark_sort (var_pos sq (Some p)))) --> sq.
Proof.
  intros.
  unfold mark_sort, mark_sort'.
  rewrite PTree.elements_single.
  compute.
  apply provable_impp_refl.
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
Admitted.

Lemma L2 : forall teq,
  |-- unmark_sort teq * build (PTree.elements expr (mark_sort teq)) --> restore' teq.
Proof.
  intros.
  induction teq as [sq oq|q1 IH1 q2 IH2].
  - compute.
    destruct oq.
    + pose proof (L2_before1 sq p) as L2_before1; compute in L2_before1.
      rewrite L2_before1; clear L2_before1.
      rewrite sepcon_comm_impp.
      apply sepcon_emp1.
    + apply sepcon_emp1.
  - unfold restore'; fold restore'.
    rewrite <- IH1, <- IH2.
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
    try apply provable_emp_refl
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