Require Export Coq.Lists.List.
Require Export Coq.Numbers.BinNums.
Require Export Coq.PArith.BinPosDef.

Require Import Setoid.
Require Import Morphisms.
Require Import RelationClasses.
Require Import export_lib.
Import EXPO.
Import EXPO_TRANSPARENTS.
Local Open Scope expo_transparent_scope.
Local Declare Scope syntax.
Local Open Scope syntax.

Module SepCancelNotation.
Notation "|--  x" := ((provable) x) (only parsing, at level 71, no associativity) : syntax.
Notation "x --> y" := ((impp) x y) (only parsing, at level 55, right associativity) : syntax.
Notation "x * y" := ((sepcon) x y) (only parsing, at level 40, left associativity) : syntax.
End SepCancelNotation.
Import SepCancelNotation.

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
  match shallowTodeep' se nil with
  | (?de, ?tbl) =>
    match de with
    | impp_deep ?dep ?deq => constr:((dep, deq, tbl))
    end
  end.

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