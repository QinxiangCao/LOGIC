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

Fixpoint match_list (es : list expr) : list positive :=
  match es with
  | nil => nil
  | e :: et => xH :: (match_list et)
  end.

Fixpoint cancel_mark_context es r nes key : (list positive) * bool :=
  match es with
  | nil => (nes, false)
  | e :: et =>
    match nes with
    | nil => (nes, false)
    | xH :: net =>
      match (beq e r) with
      | true => (key :: net, true)
      | false => let (net', isfind) := cancel_mark_context et r net key in (xH :: net', (false || isfind)%bool)
      end
    | p :: net => let (net', isfind) := cancel_mark_context et r net key in (p :: net', (false || isfind)%bool)
    end
  end.

Fixpoint cancel_mark' es rs nes nrs key : list positive * list positive :=
  match rs with
  | nil => (nes, nrs)
  | r :: rt  =>
    match nrs with
    | nil => (nes, nrs)
    | nr :: nrt =>
      match (cancel_mark_context es r nes key) with
      | (nes', true) => let (nes'', nrt') := cancel_mark' es rt nes' nrt (Pos.succ key) in (nes'', key :: nrt')
      | (nes', false) => let (nes'', nrt') := cancel_mark' es rt nes' nrt key in (nes'', xH :: nrt')
      end
    end
  end.

Definition cancel_mark es rs : list positive * list positive :=
  cancel_mark' es rs (match_list es) (match_list rs) (Pos.succ xH).

(*
Definition all_in_context e :=
  let (es, rs) := flatten e in forallb (fun r => existsb (beq r) es) rs.
*)

Fixpoint unflatten_sepcon lsp nes : Language.expr :=
  match lsp with
  | nil => Language.emp
  | sp :: spt =>
    match nes with
    | nil => Language.emp
    | ne :: net => 
      match ne with
      | xH => Language.sepcon sp (unflatten_sepcon spt net)
      | _ => unflatten_sepcon spt net
      end
    end
  end.

Definition cancel_different lsp lsq nes nrs : Language.expr :=
  Language.impp (unflatten_sepcon lsp nes) (unflatten_sepcon lsq nrs).

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

Fixpoint shallow_scan lsp nes : PTree.tree Language.expr :=
  match lsp with
  | nil => PTree.empty
  | sp :: spt =>
    match nes with
    | nil => PTree.empty
    | ne :: net => 
      match ne with
      | xH => shallow_scan spt net
      | _ => let m := shallow_scan spt net in PTree.set Language.expr ne sp m
      end
    end
  end.

Fixpoint unflatten_ptree' m p : Language.expr :=
  match m with
  | PTree.Leaf => Language.emp
  | PTree.Node l None r => unflatten_ptree' l (unflatten_ptree' r Language.emp)
  | PTree.Node l (Some v) r => unflatten_ptree' l (Language.sepcon v (unflatten_ptree' r Language.emp))
  end.

Definition unflatten_ptree m : Language.expr :=
  unflatten_ptree' m Language.emp.

Definition cancel_same lsp lsq nes nrs : Language.expr :=
  Language.impp (unflatten_ptree (shallow_scan lsp nes)) (unflatten_ptree (shallow_scan lsq nrs)).

Lemma cancel_new_sound : forall se nes nrs lsp lsq,
  Language.provable (cancel_same lsp lsq nes nrs) ->
  Language.provable (cancel_different lsp lsq nes nrs) ->
  Language.provable se.
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
    let lnt := eval compute in (cancel_mark es rs) in
    let nes := eval compute in (fst lnt) in
    let nrs := eval compute in (snd lnt) in
    apply (cancel_new_sound se nes nrs lsp lsq); compute;
    repeat first [rewrite -> Language.sepcon_emp1 | rewrite <- Language.sepcon_emp2 | apply Language.emp_refl]
    end
  end.

Ltac cancel_new :=
    match goal with
    | [|- Language.provable ?se] => cancel_new' se
    end.

Section temp.
Parameter (P Q R S T U V W: Language.expr).
Local Open Scope shallow_syntax.

Goal |-- W * U --> S * V -> |-- W * U * P * Q --> S * V * Q * P.
  intros.
  Time
  cancel_new.
  auto.
  Time
  Qed.
End temp.

