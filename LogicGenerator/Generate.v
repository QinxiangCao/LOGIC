Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.

Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigDenot.
Require Import Logic.LogicGenerator.ConfigCompute.
Require Logic.LogicGenerator.ConfigLang.

Require Import GeneratedGenerate.
Require Config.

Module PARA_OPEN.

Definition instance_para_open := false.

Import Config.

Definition PARA_OPEN: bool :=
  ltac:(first [ let XXX := eval compute in instance_para_open in exact XXX
              | exact false]).

End PARA_OPEN.

Definition instance_para_open := PARA_OPEN.PARA_OPEN.
Definition instance_para_close := negb PARA_OPEN.PARA_OPEN.

Section Generate.
Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {truepL: TrueLanguage L}
        {iffpL: IffLanguage L}
        {negpL: NegLanguage L}
        {iter_andp_L: IterAndLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {sepconL : SepconLanguage L}
        {wandL : WandLanguage L}
        {empL: EmpLanguage L}
        {iter_sepcon_L: IterSepconLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {Cor: Corable L}
        {iffpDef: IffDefinition_And_Imp L}
        {truepDef: TrueDefinition_False_Imp L}
        {negpDef: NegDefinition_False_Imp L}
        {orpDef_impp_negp: OrDefinition_Imp_Neg L}
        {truepDef_impp_self: TrueDefinition_Imp_Self L}
        {truepDef_negp_falsep: TrueDefinition_Neg_False L}
        {falsepDef_negp_truep: FalseDefinition_Neg_True L}
        {iter_andp_DL: IterAndDefinition_left L}
        {iter_andp_DR: IterAndDefinition_right L}
        {iter_sepcon_DL: IterSepconDefinition_left L}
        {iter_sepcon_DR: IterSepconDefinition_right L}
        {GammaDP: DerivableProvable L GammaP GammaD}
        {GammaPD : ProvableDerivable L GammaP GammaD}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {GammaEP: EquivProvable L GammaP GammaE}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iter_andp_AXL: IterAndAxiomatization_left L GammaP}
        {cpAX: ClassicalAxiomatization L GammaP}
        {dmpAX: DeMorganAxiomatization L GammaP}
        {gdpAX: GodelDummettAxiomatization L GammaP}
        {plAX: PeirceLaw L GammaP}
        {bcAX: ByContradiction L GammaP}
        {double_negp_elim_AX: DoubleNegElimination L GammaP}
        {caAX: ClassicAnalysis L GammaP}
        {emAX: ExcludedMiddle L GammaP}
        {impp2orpAX: ImplyToOr L GammaP}
        {coq_prop_AX: CoqPropAxiomatization L GammaP}
        {coq_prop_impp_AX: CoqPropImpAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}
        {wandAX: WandAxiomatization L GammaP}
        {empAX: EmpAxiomatization L GammaP}
        {iter_sepcon_AXL: IterSepconAxiomatization_left L GammaP}
        {sepcon_orp_AX: SepconOrAxiomatization L GammaP}
        {sepcon_falsep_AX: SepconFalseAxiomatization L GammaP}
        {sepcon_coq_prop_AX: SepconCoqPropAxiomatization L GammaP}
        {sepconAX_weak: SepconAxiomatization_weak L GammaP}
        {sepconAX_weak_iffp: SepconAxiomatization_weak_iffp L GammaP}
        {sepcon_mono_AX: SepconMonoAxiomatization L GammaP}
        {empAX_iffp: EmpAxiomatization_iffp L GammaP}
        {extAX: ExtSeparationLogic L GammaP}
        {nseAX: NonsplitEmpSeparationLogic L GammaP}
        {deAX: DupEmpSeparationLogic L GammaP}
        {mfAX: MallocFreeSeparationLogic L GammaP}
        {gcAX: GarbageCollectSeparationLogic L GammaP}
        {bSC : BasicSequentCalculus L GammaD}
        {fwSC : FiniteWitnessedSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC : AndSequentCalculus L GammaD}
        {orpSC : OrSequentCalculus L GammaD}
        {falsepSC : FalseSequentCalculus L GammaD}
        {truepSC : TrueSequentCalculus L GammaD}
        {iffpSC : IffSequentCalculus L GammaD}
        {inegpSC : IntuitionisticNegSequentCalculus L GammaD}
        {cpSC: ClassicalSequentCalculus L GammaD}
        {bD : BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD : AndDeduction L GammaD1}
        {orpD : OrDeduction L GammaD1}
        {falsepD : FalseDeduction L GammaD1}
        {truepD : TrueDeduction L GammaD1}
        {iffpD : IffDeduction L GammaD1}
        {inegpD : IntuitionisticNegDeduction L GammaD1}
        {impp_negp_D : ImpNegDeduction L GammaD1}
        {sepconD : SepconDeduction L GammaD1}
        {wandD : WandDeduction L GammaD1}
        {empD : EmpDeduction L GammaD1}
        {sepcon_orp_D : SepconOrDeduction L GammaD1}
        {sepcon_falsep_D : SepconFalseDeduction L GammaD1}
        {bE: BasicLogicEquiv L GammaE}
        {imppE: ImpLogicEquiv L GammaE}
        {CorAX: Corable_withAxiomatization L GammaP Cor}
        {coq_prop_Cor: CoqPropCorable L Cor}
        .
        
Import NameListNotations.

Definition foo :=
  ltac:(
    let res := eval compute in
    (ConfigCompute.result
       Config.how_connectives
       Config.how_judgements
       Config.transparent_names
       Config.primitive_rule_classes)
    in exact res).

Definition primitive_types: list Name :=
  map_with_hint
    (ConfigDenot.D.types, ConfigDenot.S.types)
    (ConfigLang.Output.primitive_types foo).

Definition transparent_types: list Name :=
  map_with_hint
    (ConfigDenot.D.types, ConfigDenot.S.types)
    (ConfigLang.Output.transparent_types foo).
  
Definition derived_types: list Name :=
  map_with_hint
    (ConfigDenot.D.how_types, ConfigDenot.S.how_types)
    (ConfigLang.Output.derived_types foo).
  
Definition primitive_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.connectives, ConfigDenot.S.connectives)
    (ConfigLang.Output.primitive_connectives foo).

Definition transparent_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.connectives, ConfigDenot.S.connectives)
    (ConfigLang.Output.transparent_connectives foo).

Definition derived_connectives: list Name :=
  map_with_hint
    (ConfigDenot.D.how_connectives, ConfigDenot.S.how_connectives)
    (ConfigLang.Output.derived_connectives foo).

Definition primitive_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.judgements, ConfigDenot.S.judgements)
    (ConfigLang.Output.primitive_judgements foo).

Definition transparent_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.judgements, ConfigDenot.S.judgements)
    (ConfigLang.Output.transparent_judgements foo).

Definition derived_judgements: list Name :=
  map_with_hint
    (ConfigDenot.D.how_judgements, ConfigDenot.S.how_judgements)
    (ConfigLang.Output.derived_judgements foo).

Definition aux_primitive_instances: list Name :=
  map_with_hint
    (ConfigDenot.D.classes, ConfigDenot.S.instances_build)
    (ConfigLang.Output.primitive_classes foo).

Definition aux_refl_instances_for_derivation: list Name :=
  map_with_hint
    (ConfigDenot.D.refl_classes, ConfigDenot.S.refl_instances)
    (ConfigLang.Output.refl_classes_for_derivation foo).

Definition aux_derived_instances: list Name :=
  map_with_hint
    (ConfigDenot.S.D_instance_transitions, ConfigDenot.S.instance_transitions)
    (ConfigLang.Output.how_derive_classes foo).

Definition primary_rules: list Name :=
  map_with_hint
    (ConfigDenot.S.D_primary_rules, ConfigDenot.S.primary_rules)
    (ConfigLang.Output.primary_rules foo).

Let derived_rules': list Name :=
  (map_with_hint
    (ConfigDenot.S.D_primary_rules, ConfigDenot.S.primary_rules)
    (ConfigLang.Output.derived_primary_rules foo)) ++
  map_with_hint
    (ConfigDenot.S.D_derived_rules, ConfigDenot.S.derived_rules)
    (ConfigLang.Output.derived_derived_rules foo).

Definition derived_rules : list Name :=
  ltac:(let res0 := eval unfold derived_rules' in derived_rules' in
        let res1 := eval unfold app at 1 in res0 in
            exact res1).

Definition derived_rules_as_instance :=
  map_with_hint
    (ConfigDenot.S.D_derived_rules, ConfigDenot.S.derived_rules)
    (ConfigLang.Output.derived_rules_as_instance foo).

Import ListNotations.

Inductive PrintType := IPar (Inline_list: list Name) | Axm | Der | Def | AIns | DIns.

Ltac print prt name :=
  match name with
  | BuildName ?n =>
    match type of n with
    | ?T =>
      match prt with
      | IPar ?l =>
        let l := eval hnf in l in
        let should_inline := in_name_list n l in
        match n with
        | expr =>
            unify instance_para_open true;
            match should_inline with
            | true => def_inline_expr_tac
            | false => def_expr_tac
            end;
            idtac "  Section LanguageSig.";
            context_expr_tac
        | _ =>
            match should_inline with
            | true => idtac "  Parameter Inline" n ":" T "."
            | false => idtac "  Parameter" n ":" T "."
            end
        end
      | Axm => idtac "  Axiom" n ":" T "."
      | Der => match n with
               | (?n0, ?n1) => idtac "  Definition" n0 ":=" n1 "."
               end
      | Def => idtac "  Definition" n ":" T ":=" n "."
      | AIns => match n with
                | (?n0, ?n1) =>
                  match type of n0 with
                  | ?T0 => idtac "  Instance" n0 ":" T0 ":=" n1 "."
                  end
                end
      | DIns => idtac "  Existing Instance" n "."
      end
    end
  end.

Ltac newline := idtac "".

Set Printing Width 1000.

Ltac two_stage_print :=
  when instance_para_open: import_local_lib_tac;
  idtac "Require Import Coq.Numbers.BinNums.";
  idtac "Require Import Coq.PArith.BinPosDef.";
  idtac "Require Import Logic.lib.PTree.";
  idtac "Require Import Coq.Sets.Ensembles.";
  idtac "Require Import Coq.Lists.List.";
  idtac "Import ListNotations.";

  newline;

  idtac "Module Type LanguageSig.";
  dolist (print (IPar transparent_types)) primitive_types;
  dolist (print Der) derived_types;
  dolist (print (IPar transparent_judgements)) primitive_judgements;
  dolist (print (IPar transparent_connectives)) primitive_connectives;
  when instance_para_open: idtac "  End LanguageSig.";
  idtac "End LanguageSig.";

  newline;

  idtac "Module DerivedNames (Names: LanguageSig).";
  idtac "Include Names.";
  when instance_para_open: (
    def__PARA__para_tac;
    idtac "  Section DerivedNames.";
    context_expr_tac
  );
  dolist (print Der) derived_connectives;
  dolist (print Der) derived_judgements;
  when instance_para_open:
    idtac "  End DerivedNames.";
  idtac "End DerivedNames.";

  newline;

  idtac "Module Type PrimitiveRuleSig (Names: LanguageSig).";
  idtac "Include DerivedNames (Names).";
  when instance_para_open: (
    idtac "  Section PrimitiveRuleSig.";
    context_expr_tac
  );
  dolist (print Axm) primary_rules;
  when instance_para_open:
    idtac "  End PrimitiveRuleSig.";
  idtac "End PrimitiveRuleSig.";

  newline;

  idtac "Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).";
  idtac "Include Rules.";
  when instance_para_close:
    idtac "Parameter Inline tree_pos : Type .";
  when instance_para_open: (
    idtac "Parameter Inline tree_pos : forall `{ para }, Type .";
    idtac "  Section LogicTheoremSig.";
    context_expr_tac
  );
  dolist (print Axm) derived_rules;
  dolist (print DIns) derived_rules_as_instance;
  when instance_para_open:
    idtac "  End LogicTheoremSig.";
  idtac "End LogicTheoremSig.";

  newline;

  idtac "Require Import Logic.GeneralLogic.Base.";
  idtac "Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.";
  idtac "Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.";
  idtac "Require Import Logic.MinimumLogic.Syntax.";
  idtac "Require Import Logic.MinimumLogic.ProofTheory.Minimum.";
  idtac "Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.";
  idtac "Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.";
  idtac "Require Import Logic.PropositionalLogic.Syntax.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.Classical.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.";
  idtac "Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.";
  idtac "Require Import Logic.MetaLogicInj.Syntax.";
  idtac "Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.";
  idtac "Require Import Logic.SeparationLogic.Syntax.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.Corable.";
  idtac "Require Import Logic.SeparationLogic.ProofTheory.Deduction.";
  idtac "Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.";

  newline;

  (* TODO: this "<:" should be ":". Currently, this is just a work-around for generated tactics. *)
  idtac "Module LogicTheorem (Names: LanguageSig) (Rules: PrimitiveRuleSig Names) <: LogicTheoremSig Names Rules.";
  idtac "Include Rules.";
  when instance_para_open: (
    idtac "  Section LogicTheorem.";
    context_expr_tac
  );
  dolist (print AIns) aux_primitive_instances;
  dolist (print AIns) aux_refl_instances_for_derivation;
  dolist (print AIns) aux_derived_instances;
  idtac "Definition tree_pos : Type := tree_pos.";
  dolist (print Def) derived_rules;
  when instance_para_open:
    idtac "  End LogicTheorem.";
  dolist (print DIns) derived_rules_as_instance;
  idtac "End LogicTheorem.";

  newline;

  idtac "(*Require Logic.PropositionalLogic.DeepEmbedded.Solver.";
  idtac "Module IPSolver (Names: LanguageSig).";
  idtac "  Import Names.";
  idtac "  Ltac ip_solve :=";
  idtac "    change expr with Base.expr;";
  idtac "    change provable with Base.provable;";
  idtac "    change impp with Syntax.impp;";
  idtac "    change andp with Syntax.andp;";
  idtac "    intros; Solver.SolverSound.ipSolver.";
  idtac "End IPSolver.*)";



  
  idtac.
  
Goal False.
  two_stage_print.
Abort.

End Generate.
