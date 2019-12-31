Require Import GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import MinimumLogic.Syntax.
Require Import MinimumLogic.ProofTheory.Minimum.
Require Import MinimumLogic.ProofTheory.RewriteClass.
Require Import PropositionalLogic.Syntax.
Require Import PropositionalLogic.ProofTheory.Intuitionistic.
Require Import PropositionalLogic.ProofTheory.Classical.
Require Import PropositionalLogic.ProofTheory.DeMorgan.
Require Import PropositionalLogic.ProofTheory.GodelDummett.
Require Import PropositionalLogic.ProofTheory.RewriteClass.
Require Import SeparationLogic.Syntax.
Require Import SeparationLogic.ProofTheory.SeparationLogic.
Require Import SeparationLogic.ProofTheory.RewriteClass.

Require Logic.LogicGenerator.ConfigLang.
Require Import Logic.LogicGenerator.Utils. 

Module D.
Import ConfigLang.
Import ListNotations.

Definition types: list type :=
  [ expr
  ; context
  ].

Definition connectives: list connective :=
  [ impp
  ; andp
  ; orp
  ; negp
  ; falsep
  ; truep
  ; sepcon
  ; wand
  ; emp
  ; multi_imp
  ; empty_context
  ].

Definition judgements: list judgement :=
  [ provable
  ; derivable
  ].

Definition how_types: list how_type :=
  [ FROM_ensemble_expr_TO_context
  ].

Definition how_connectives: list how_connective :=
  [ FROM_andp_impp_TO_iffp
  ; FROM_falsep_impp_TO_negp
  ; FROM_falsep_impp_TO_truep
  ; FROM_impp_TO_multi_imp
  ; FROM_empty_set_TO_empty_context
  ].

Definition how_judgements: list how_judgement :=
  [ FROM_provable_TO_derivable
  ; FROM_derivable_TO_provable
  ].

Definition type_classes :=
  [ Language
  ].

Definition connective_classes :=
  [ MinimumLanguage
  ; PropositionalLanguage
  ; SeparationLanguage
  ; EmpSeparationLanguage
  ].

Definition judgement_classes :=
  [ Provable
  ; Derivable
  ].

Definition rule_classes :=
  [ provability_OF_impp
  ; provability_OF_propositional_connectives
  ; provability_OF_de_morgan
  ; provability_OF_godel_dummett
  ; provability_OF_classical_logic
  ; provability_OF_separation_logic
  ; provability_OF_emp_rule
  ; provability_OF_garbage_collected_sl
  ; derivitive_OF_basic_setting
  ; derivitive_OF_finite_derivation
  ; derivitive_OF_impp
  ; derivitive_OF_propositional_connectives
(*  ; derivitive_OF_de_morgan *)
(*  ; derivitive_OF_godel_dummett *)
  ; derivitive_OF_classical_logic
  ; GEN_derivable_FROM_provable
  ; GEN_provable_FROM_derivable
  ].

Definition classes :=
  ltac:(let l := eval compute in
         (map TC type_classes ++
          map CC connective_classes ++
          map JC judgement_classes ++
          map RC rule_classes) in
        exact l).

Definition refl_classes :=
  [ RC GEN_derivable_FROM_provable
  ; RC GEN_provable_FROM_derivable
  ].

End D.

Definition Build_Language := Build_Language.
Definition Build_MinimumLanguage := Build_MinimumLanguage.
Definition Build_PropositionalLanguage := Build_PropositionalLanguage.
Definition Build_SeparationLanguage := Build_SeparationLanguage.
Definition Build_SeparationEmpLanguage := Build_SeparationEmpLanguage.
Definition Build_Provable := Build_Provable.
Definition Build_Derivable := Build_Derivable.
Definition Build_NormalAxiomatization := Build_NormalAxiomatization.
Definition Build_NormalSequentCalculus := Build_NormalSequentCalculus.
Definition Build_MinimumAxiomatization := Build_MinimumAxiomatization.
Definition Build_IntuitionisticPropositionalLogic := Build_IntuitionisticPropositionalLogic.
Definition Build_DeMorganPropositionalLogic := Build_DeMorganPropositionalLogic.
Definition Build_ClassicalPropositionalLogic := Build_ClassicalPropositionalLogic.
Definition Build_SeparationLogic := Build_SeparationLogic.
Definition Build_EmpSeparationLogic := Build_EmpSeparationLogic.
Definition Build_GarbageCollectSeparationLogic := Build_GarbageCollectSeparationLogic.
Definition Build_BasicSequentCalculus := Build_BasicSequentCalculus.
Definition Build_FiniteWitnessedSequentCalculus := Build_FiniteWitnessedSequentCalculus.
Definition Build_MinimumSequentCalculus := Build_MinimumSequentCalculus.
Definition Build_IntuitionisticPropositionalSequentCalculus := Build_IntuitionisticPropositionalSequentCalculus.
Definition Build_ClassicalPropositionalSequentCalculus := Build_ClassicalPropositionalSequentCalculus.

Module S.
Import NameListNotations.
Section S.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sL : SeparationLanguage L}
        {empL: SeparationEmpLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {AX: NormalAxiomatization L GammaP GammaD}
        {SC : NormalSequentCalculus L GammaP GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {ipAX: IntuitionisticPropositionalLogic L GammaP}
        {cpAX: ClassicalPropositionalLogic L GammaP}
        {dmpAX: DeMorganPropositionalLogic L GammaP}
        {gdpAX: GodelDummettPropositionalLogic L GammaP}
        {sAX: SeparationLogic L GammaP}
        {empsAX: EmpSeparationLogic L GammaP}
        {extsAX: ExtSeparationLogic L GammaP}
        {nsesAX: NonsplitEmpSeparationLogic L GammaP}
        {desAX: DupEmpSeparationLogic L GammaP}
        {mfsAX: MallocFreeSeparationLogic L GammaP}
        {gcsAX: GarbageCollectSeparationLogic L GammaP}
        {bSC : BasicSequentCalculus L GammaD}
        {fwSC : FiniteWitnessedSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {ipSC : IntuitionisticPropositionalSequentCalculus L GammaD}
        {cpSC : ClassicalPropositionalSequentCalculus L GammaD}
        .

Definition types: list Name :=
  [ expr
  ; context
  ].

Definition connectives: list Name :=
  [ impp
  ; andp
  ; orp
  ; negp
  ; falsep
  ; truep
  ; sepcon
  ; wand
  ; emp
  ; multi_imp
  ; empty_context
  ].

Definition judgements: list Name :=
  [ provable
  ; derivable
  ].

Definition how_types: list Name :=
  [ (context, expr -> Prop)
  ].

Definition how_connectives: list Name :=
  [ (iffp, fun x y => andp (impp x y) (impp y x))
  ; (negp, fun x => impp x falsep)
  ; (truep, impp falsep falsep)
  ; (multi_imp, fun xs y => fold_right impp y xs)
  ; (empty_context, Empty_set expr)
  ].

Definition how_judgements: list Name :=
  [ (derivable, fun Phi x => exists xs, Forall Phi xs /\ provable (multi_imp xs x))
  ; (provable, fun x => derivable empty_context x)
  ].

Definition type_instances_build :=
  [ (L, Build_Language expr)
  ].

Definition connective_instances_build :=
  [ (minL, Build_MinimumLanguage L impp)
  ; (pL, Build_PropositionalLanguage L andp orp falsep)
  ; (sL, Build_SeparationLanguage L sepcon wand)
  ; (empL, Build_SeparationEmpLanguage L emp)
  ].

Definition judgement_instances_build :=
  [ (GammaP, Build_Provable _ provable)
  ; (GammaD, Build_Derivable _ derivable)
  ].

Definition rule_instances_build :=
  [ (minAX, Build_MinimumAxiomatization L minL GammaP modus_ponens axiom1 axiom2)
  ; (ipAX, Build_IntuitionisticPropositionalLogic L minL pL GammaP minAX andp_intros andp_elim1 andp_elim2 orp_intros1 orp_intros2 orp_elim falsep_elim)
  ; (dmpAX, Build_DeMorganPropositionalLogic L minL pL GammaP minAX ipAX weak_excluded_middle)
  ; (gdpAX, Build_GodelDummettPropositionalLogic L minL pL GammaP minAX ipAX impp_choice)
  ; (cpAX, Build_ClassicalPropositionalLogic L minL pL GammaP minAX ipAX excluded_middle)
  ; (sAX, Build_SeparationLogic L minL pL sL GammaP minAX ipAX sepcon_comm_impp sepcon_assoc wand_sepcon_adjoint)
  ; (empsAX, Build_EmpSeparationLogic L minL pL sL empL GammaP minAX ipAX sAX sepcon_emp)
  ; (gcsAX, Build_GarbageCollectSeparationLogic L minL pL sL GammaP minAX ipAX sAX sepcon_elim1)
  ; (bSC, Build_BasicSequentCalculus L GammaD deduction_weaken derivable_assum deduction_subst)
  ; (fwSC, Build_FiniteWitnessedSequentCalculus L GammaD derivable_finite_witnessed)
  ; (minSC, Build_MinimumSequentCalculus L minL GammaD deduction_modus_ponens deduction_impp_intros) 
  ; (ipSC, Build_IntuitionisticPropositionalSequentCalculus L pL GammaD deduction_andp_intros deduction_andp_elim1 deduction_andp_elim2 deduction_orp_intros1 deduction_orp_intros2 deduction_orp_elim deduction_falsep_elim)
  ; (cpSC, Build_ClassicalPropositionalSequentCalculus L minL pL GammaD bSC minSC ipSC derivable_excluded_middle)
  ; (AX, Build_NormalAxiomatization L minL GammaP GammaD derivable_provable)
  ; (SC, Build_NormalSequentCalculus L GammaP GammaD provable_derivable)
  ].

Definition instances_build :=
  ltac:(let instances_build :=
          eval cbv [type_instances_build
                    connective_instances_build
                    judgement_instances_build
                    rule_instances_build
                    app] in
        (type_instances_build ++
         connective_instances_build ++
         judgement_instances_build ++
         rule_instances_build) in
        exact instances_build).

Definition refl_instances :=
  [ (AX, Provable2Derivable_Normal)
  ; (SC, Derivable2Provable_Normal)
  ].

Definition instance_transitions :=
  [ (SC, Axiomatization2SequentCalculus_SC)
  ; (bSC, Axiomatization2SequentCalculus_bSC)
  ; (fwSC, Axiomatization2SequentCalculus_fwSC)
  ; (minSC, Axiomatization2SequentCalculus_minSC)
  ; (ipSC, Axiomatization2SequentCalculus_ipSC)
  ; (AX, SequentCalculus2Axiomatization_AX)
  ; (minAX, SequentCalculus2Axiomatization_minAX)
  ; (ipAX, SequentCalculus2Axiomatization_ipAX)  
  ].

Definition type_instances: list Name :=
  map_fst type_instances_build.

Definition connective_instances :=
  map_fst connective_instances_build.

Definition judgement_instances :=
  map_fst judgement_instances_build.

Definition rule_instances :=
  map_fst rule_instances_build.

Definition instances :=
  ltac:(let instances :=
          eval cbv [type_instances
                    connective_instances
                    judgement_instances
                    rule_instances
                    app] in
        (type_instances ++
         connective_instances ++
         judgement_instances ++
         rule_instances) in
        exact instances).

Definition type_dependency_via_ins :=
  noninstance_arg_lists
    (type_instances_build, map_snd type_instances_build).

Definition connective_dependency_via_ins :=
  noninstance_arg_lists
    (connective_instances_build, map_snd connective_instances_build).

Definition judgement_dependency_via_ins :=
  noninstance_arg_lists
    (judgement_instances_build, map_snd judgement_instances_build).

Definition primary_rule_dependency_via_ins :=
  noninstance_arg_lists
    (rule_instances_build, map_snd rule_instances_build).

Definition instance_dependency_via_transition :=
  instance_arg_lists
    (instance_transitions, map_snd instance_transitions).

Definition D_type_dependency_via_ins :=
  (map_with_hint (type_instances_build, D.type_classes)
                 (map_fst type_dependency_via_ins),
   map_with_hint (types, D.types)
                 (map_snd type_dependency_via_ins)).

Definition D_connective_dependency_via_ins :=
  (map_with_hint (connective_instances_build, D.connective_classes)
                 (map_fst connective_dependency_via_ins),
   map_with_hint (connectives, D.connectives)
                 (map_snd connective_dependency_via_ins)).

Definition D_judgement_dependency_via_ins :=
  (map_with_hint (judgement_instances_build, D.judgement_classes)
                 (map_fst judgement_dependency_via_ins),
   map_with_hint (judgements, D.judgements)
                 (map_snd judgement_dependency_via_ins)).

Definition D_instance_transitions: list ConfigLang.how_instance :=
  nat_ident_list instance_transitions.

Definition D_instance_transition_results :=
  map_with_hint (instances, D.classes) (map_fst instance_transitions).

Definition D_instance_dependency_via_transition :=
  (map_with_hint (instance_transitions, D_instance_transitions)
                 (map_fst instance_dependency_via_transition),
   map_with_hint (instances, D.classes)
                 (map_snd instance_dependency_via_transition)).

Definition primary_rules: list Name :=
  map_snd primary_rule_dependency_via_ins.

Definition derived_rules :=
  [ provable_impp_refl
  ; provable_impp_arg_switch
  ; provable_impp_trans
  ; provable_multi_imp_shrink
  ; provable_multi_imp_arg_switch1
  ; provable_multi_imp_arg_switch2
  ; provable_add_multi_imp_left_head
  ; provable_add_multi_imp_left_tail
  ; provable_multi_imp_modus_ponens
  ; provable_multi_imp_weaken
  ; provable_impp_refl_instance
  ; deduction_impp_elim
  ; deduction_theorem
  ; deduction_theorem_multi_imp
  ; derivable_impp_refl
  ; deduction_left_impp_intros
  ; derivable_modus_ponens
  ; deduction_impp_trans
  ; deduction_impp_arg_switch
  ; provable_proper_impp
  ; impp_proper_impp
  ; derivable_proper_impp

  ; demorgan_orp_negp
  ; demorgan_negp_orp
  ; provable_truep
  ; andp_comm
  ; andp_assoc
  ; orp_comm
  ; orp_assoc
  ; andp_dup
  ; orp_dup
  ; impp_curry
  ; impp_uncurry
  ; double_negp_elim
  ; double_negp
  ; contrapositiveNN
  ; contrapositiveNP
  ; impp2orp
  ; andp_proper_impp
  ; orp_proper_impp
  ; negp_proper_impp
  ; provable_iffp_equiv
  ; provable_proper_iffp
  ; impp_proper_iffp
  ; andp_proper_iffp
  ; orp_proper_iffp
  ; iffp_proper_iffp
  ; negp_proper_iffp
  ; derivable_proper_iffp

  ; sepcon_orp_distr_l
  ; falsep_sepcon
  ; provable_wand_sepcon_modus_ponens1
  ; wand_andp
  ; sepcon_comm
  ; sepcon_orp_distr_r
  ; sepcon_falsep
  ; provable_wand_sepcon_modus_ponens2
  ; wand_mono
  ; orp_wand
  ; sepcon_mono
  ].

Ltac filter_instance_rec l res :=
  match l with
  | nil => res
  | cons (BuildName ?x) ?l0 =>
      let tac1 TT := filter_instance_rec l0 (cons (BuildName x) res) in
      let tac2 TT := filter_instance_rec l0 res in
      if_instance x tac1 tac2
  end.

Notation "'filter_instance' l" :=
  (ltac:(let l' := eval hnf in l in
         let res := filter_instance_rec l' (@nil Name) in
         exact res))
  (only parsing, at level 99).

Definition derived_rules_as_instance :=
  filter_instance derived_rules.

Definition D_primary_rules :=
  nat_ident_list primary_rules.

Definition D_derived_rules :=
  nat_ident_list derived_rules.

Definition D_derived_rules_as_instance :=
  map_with_hint (derived_rules, D_derived_rules) derived_rules_as_instance.

Definition primary_rules_dependency_via_ins :=
  instance_arg_lists
    (primary_rules, primary_rules).

Definition derived_rules_dependency_via_ins :=
  instance_arg_lists
    (derived_rules, derived_rules).

Definition D_primary_rules_dependency_via_ins :=
  (map_with_hint (primary_rules, D_primary_rules)
                 (map_fst primary_rules_dependency_via_ins),
   map_with_hint (instances, D.classes)
                 (map_snd primary_rules_dependency_via_ins)).

Definition D_derived_rules_dependency_via_ins :=
  (map_with_hint (derived_rules, D_derived_rules)
                 (map_fst derived_rules_dependency_via_ins),
   map_with_hint (instances, D.classes)
                 (map_snd derived_rules_dependency_via_ins)).

End S.
End S.


