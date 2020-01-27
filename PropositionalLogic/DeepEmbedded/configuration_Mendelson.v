Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective negp
  ;FROM_impp_negp_TO_orp
  ;FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ].

Definition transparent_names :=
  [expr:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_negp
  ; provability_OF_classical_logic_by_contra
  ].

