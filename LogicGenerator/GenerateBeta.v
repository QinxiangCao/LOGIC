Require Import Coq.Lists.List.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.MetaLogicInj.ProofTheory.Deduction.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
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
        {iter_andp_DL: IterAndDefinition_left L}
        {iter_andp_DR: IterAndDefinition_right L}
        {iter_sepcon_DL: IterSepconDefinition_left L}
        {iter_sepcon_DR: IterSepconDefinition_right L}
        {AX: NormalAxiomatization L GammaP GammaD}
        {SC : NormalSequentCalculus L GammaP GammaD}
        {ND : NormalDeduction L GammaP GammaD1}
        {NE : NormalEquiv L GammaP GammaE}
        {NE2 : NormalEquiv2 L GammaD1 GammaE}
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
        {sepconD : SepconDeduction L GammaD1}
        {wandD : WandDeduction L GammaD1}
        {empD : EmpDeduction L GammaD1}
        {sepcon_orp_D : SepconOrDeduction L GammaD1}
        {sepcon_falsep_D : SepconFalseDeduction L GammaD1}
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

Inductive PrintType := IPar (Inline_list: list Name) | Axm | Der | Def | BetaDef | AIns | DIns.

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
      | BetaDef => idtac "  Definition" n ":= BETA" n "."
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

Ltac beta_print :=
  import_local_lib_tac;
  import_implementation_tac;
  idtac "Require Import Coq.Lists.List.";
  idtac "Require Import Coq.Sets.Ensembles.";
  idtac "Import ListNotations.";

  newline;

  set_up_module_name_tac;
  idtac "Module BETA.";
  idtac "Import ___LogicTheorem___.";
  idtac "  Section BETA_SECTION.";
  context_expr_tac;
  newline;
  idtac "  Ltac beta_tac x :=";
  idtac "    match type of x with";
  idtac "    | ?tx => let tx0 := eval cbv beta in tx in";
  idtac "               exact (x: tx0)";
  idtac "    end.";
  idtac "  Declare Scope BETA_scope.";
  idtac "  Local Notation ""'BETA' x"" := ltac:(beta_tac x) (at level 99): BETA_scope.";
  idtac "  Local Open Scope BETA_scope.";

  newline;

  dolist (print BetaDef) primary_rules;
  dolist (print BetaDef) derived_rules;

  newline;

  idtac "  End BETA_SECTION.";

  newline;

  dolist (print DIns) derived_rules_as_instance;

  newline;

  idtac "End BETA.";

  idtac.

  
Goal False.
  beta_print.
Abort.

End Generate.
