Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.
(* how type *)

Definition how_connectives :=
  [ primitive_connective join;
    FROM_model_TO_impp;
    FROM_join_TO_sepcon].

Definition how_judgements :=
  [ FROM_model_TO_provable
  ].

Definition transparent_names :=
  [provable : parameter].

Definition primitive_rule_classes :=
  [ join_is_SA
    (* join sa *) (* unit element *)
  ].

(* Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective sepcon
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ].

Definition how_judgements :=
  [ primitive_judgement provable
  ; FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter
  ;impp:parameter
  ;andp:parameter
  ;sepcon:parameter
  ;provable:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_andp
  ; provability_OF_sepcon_rule_AS_weak
  ; provability_OF_sepcon_rule_AS_mono
  ]. *)

