Require Import Logic.SeparationLogic.Tactics.Language.
Require Export Coq.Lists.List.
Require Export Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
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

Ltac shallowTolist_odd se l0 :=
  match se with
  | Language.sepcon ?sp ?sq =>
    match shallowTolist_odd sp l0 with
    | (?sp', ?l1) =>
      match shallowTolist_odd sq l1 with
      | (?sq', ?l2) => constr:((se, l1 ++ l2))
      end
    end
  | ?sm => constr:((sm, sm :: nil))
  end.

Ltac shallowTolist' se lsp lsq:=
  match se with
  | Language.impp ?sp ?sq =>
    match shallowTolist_odd sp constr:(@nil Language.expr) with
    | (?sp', ?l1) =>
      match shallowTolist_odd sq constr:(@nil Language.expr) with
      | (?sq', ?l2) => constr:((se, l1, l2))
      end
    end
  end.

Fixpoint match_list (es : list expr) (lsp : list Language.expr):
list (Language.expr * positive) :=
  match es, lsp with
  | nil, nil=> nil
  | nil, sp :: spt => nil
  | e :: et, nil => nil
  | e :: et, sp :: spt => (sp , xH) :: (match_list et spt)
  end.

Fixpoint cancel_mark_context es r nes key :
(list (Language.expr * positive)) * bool :=
  match es, nes with
  | nil, nil => (nes, false)
  | nil, _ :: net => (nes, false)
  | _ :: et, nil => (nes, false)
  | e :: et, (sp, xH) :: net =>
    match (beq e r) with
    | true => ((sp, key) :: net, true)
    | false => let (net', isfind) := cancel_mark_context et r net key 
                in ((sp, xH) :: net', (false || isfind)%bool)
    end
  | e :: et, p :: net =>
    let (net', isfind) := cancel_mark_context et r net key
     in (p :: net', (false || isfind)%bool)
  end.

Fixpoint cancel_mark' es rs nes nrs key :
list (Language.expr * positive) * list (Language.expr * positive) :=
  match rs, nrs with
  | nil, nil => (nes, nrs)
  | nil, _ :: nrt => (nes, nrs)
  | r :: rt, nil => (nes, nrs)
  | r :: rt, (sq, nr) :: nrt =>
    match (cancel_mark_context es r nes key) with
    | (nes', true) => let (nes'', nrt') := cancel_mark' es rt nes' nrt (Pos.succ key)
                       in (nes'', (sq, key) :: nrt')
    | (nes', false) => let (nes'', nrt') := cancel_mark' es rt nes' nrt key
                        in (nes'', (sq, xH) :: nrt')
    end
  end.

Definition cancel_mark es rs lsp lsq:
list (Language.expr * positive) * list (Language.expr * positive) :=
  cancel_mark' es rs (match_list es lsp) (match_list rs lsq) (Pos.succ xH).

Fixpoint unflatten_sepcon' net p : Language.expr :=
  match net with
  | nil => p
  | (sp, ne) :: net0 => 
    match ne with
    | xH => unflatten_sepcon' net0 (Language.sepcon p sp)
    | _ => unflatten_sepcon' net0 p
    end
  end.

Fixpoint unflatten_sepcon nes : Language.expr :=
  match nes with
  | nil => Language.emp
  | (sp, ne) :: net =>
    match ne with
    | xH => unflatten_sepcon' net sp
    | _ => unflatten_sepcon net
    end
  end.

Definition cancel_different nes nrs : Language.expr :=
  Language.impp (unflatten_sepcon nes) (unflatten_sepcon nrs).

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
(*get_rec(A : Type) (i : positive) (m : tree A) (f : tree A -> option A) : option A :=*)
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
End PTree.

Fixpoint shallow_scan nes : PTree.tree Language.expr :=
  match nes with
  | nil => PTree.empty
  | (sp, ne) :: net =>
    match ne with
    | xH => shallow_scan net
    | _ => let m := shallow_scan net in PTree.set Language.expr ne sp m
    end
  end.

Fixpoint unflatten_ptree' m p : Language.expr :=
  match m with
  | PTree.Leaf => p
  | PTree.Node l None r => unflatten_ptree' l (unflatten_ptree' r p)
  | PTree.Node l (Some v) r => unflatten_ptree' l (Language.sepcon (unflatten_ptree' r p) v)
  end.

Definition unflatten_ptree m : Language.expr :=
  unflatten_ptree' m Language.emp.

Definition cancel_same nes nrs : Language.expr :=
  Language.impp (unflatten_ptree (shallow_scan nes)) (unflatten_ptree (shallow_scan nrs)).
(*cancel_same --> m is same*)
Lemma cancel_new_sound : forall se nes nrs,
  Language.provable (cancel_same nes nrs) ->
  Language.provable (cancel_different nes nrs) ->
  Language.provable se.
Proof.
  intros.
  unfold cancel_same in H.
  unfold cancel_different in H0.
Admitted.

Ltac cancel_new' se :=
  match shallowTodeep' se constr:(@nil Language.expr) with
    | (?de, ?tbl) =>
    match shallowTolist' se (@nil Language.expr) (@nil Language.expr) with
    | (?se', ?lsp, ?lsq) =>
    let tbl' := reverse tbl in
    let lde := eval compute in (flatten de) in
    let es := eval compute in (fst lde) in
    let rs := eval compute in (snd lde) in
    let lnt := eval compute in (cancel_mark es rs lsp lsq) in
    let nes := eval compute in (fst lnt) in
    let nrs := eval compute in (snd lnt) in
    apply (cancel_new_sound se nes nrs);
    [
    let same := eval compute in (cancel_same nes nrs) in change (Language.provable same);
    apply Language.impp_refl |
    let different := eval compute in (cancel_different nes nrs) in change (Language.provable different);
    try apply Language.emp_refl
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

Goal |-- (W --> T) * U --> S * V -> |-- (W --> T) * U * (V --> W) * (P * Q) * T --> T * S * V * Q * P * (V --> W).
  intros.
  Time
  cancel_new.
  auto.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G).
  intros.
  Time
  cancel_new.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G).
  intros.
  Time
  cancel_new.
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
  cancel_new.
  Time
  Qed.

Goal
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L) *
    (M * (N * O) * P) * (Q * R * S) * T * (U * V) * W * X
--> (I * J * (D * K) * L) * A * B * (C * H) * (E * F * G) *
    (M * X * (N * W) * O) * P * Q * (T * S) * (V * R * U).
  intros.
  Time
  cancel_new.
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
  cancel_new.
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
  cancel_new.
  Time
  Qed.

Goal
|-- A * B * C * D --> M * N * O * E ->
|-- A * B * (C * D) * (E * F * (G * H)) * (I * J * K * L)
--> I * J * (G * E) * (F * M * N) * (O * (L * K * E) * H).
  intros.
  Time
  cancel_new.
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
  cancel_new.
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
  cancel_new.
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
  cancel_new.
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
  cancel_new.
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
  cancel_new.
  auto.
  Time
  Qed.

End temp.