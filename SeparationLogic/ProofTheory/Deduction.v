Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class SepconDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_sepcon_comm: forall x y, x * y |-- y * x;
  derivable1_sepcon_assoc1: forall x y z, x * (y * z) |-- (x * y) * z;
  derivable1_sepcon_mono: forall x1 x2 y1 y2, x1 |-- x2 -> y1 |-- y2 
               -> (x1 * y1) |-- (x2 * y2);
}.

Class SepconOrDeduction
        (L: Language)
        {orpL: OrLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  orp_sepcon_left: forall x y z,
     (x || y) * z |-- x * z || y * z
}.

Class SepconFalseDeduction
        (L: Language)
        {falsepL: FalseLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  falsep_sepcon_left: forall x,
     FF * x |-- FF
}.

Class EmpDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
    sepcon_emp_left: forall x,  x * emp |-- x;
    sepcon_emp_right: forall x, x |-- x * emp
}.

Class WandDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_wand_sepcon_adjoint: forall x y z, x * y  |-- z <-> x |-- (y -* z)
}.

Class ExtSeparationLogicDeduction
        (L: Language)
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_sepcon_ext: forall x, x |-- x * TT
}.

Class NonsplitEmpSeparationLogicDeduction
        (L: Language)
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_emp_sepcon_truep_elim: forall x, (x * TT) && emp |-- x
}.

Class DupEmpSeparationLogicDeduction
        (L: Language)
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_emp_dup: forall x, x && emp |-- x * x
}.

Class GarbageCollectSeparationLogicDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  derivable1_sepcon_elim1: forall x y, x * y |-- x
}.

Section SLFromDeduction2SLFromAxiomatization1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {sepconL: SepconLanguage L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma SepconDeduction2SepconAxiomatization_sepconAX
      {sepconD: SepconDeduction L GammaD1}:
  SepconAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply derivable1_sepcon_comm.
  -intros. apply derivable1_provable. apply derivable1_sepcon_assoc1.
  -intros. apply derivable1_provable. apply derivable1_provable in H.
   apply derivable1_provable in H0. apply derivable1_sepcon_mono;auto.
   Qed.

Context {orpL: OrLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {falsepL: FalseLanguage L}.

Lemma SepconOrDeduction2SepconOrAxiomatization_sepcon_orp_AX
      {sepcon_orp_D: SepconOrDeduction L GammaD1}:
  SepconOrAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply orp_sepcon_left.
  Qed.

Lemma SepconFalseDeduction2SepconFalseAxiomatization_sepcon_false_AX
      {sepcon_falsep_D: SepconFalseDeduction L GammaD1}:
  SepconFalseAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply falsep_sepcon_left.
  Qed.

Lemma ExtSeparationLogicD2ExtSeparationLogic_esGamma
      {esD: ExtSeparationLogicDeduction L GammaD1}:
  ExtSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_sepcon_ext.
  Qed.

Lemma GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic_gcsGamma
      {gcs: GarbageCollectSeparationLogicDeduction L GammaD1}:
  GarbageCollectSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_sepcon_elim1.
  Qed.

End SLFromDeduction2SLFromAxiomatization1.

Instance reg_SepconOrDeduction2SepconOrAxiomatization:
  RegisterClass D12P_reg (fun sepcon_orp_AX:unit => @SepconOrDeduction2SepconOrAxiomatization_sepcon_orp_AX) 10.
Qed.

Instance reg_SepconFalseDeduction2SepconFalseAxiomatization:
  RegisterClass D12P_reg (fun sepcon_false_AX:unit => @SepconFalseDeduction2SepconFalseAxiomatization_sepcon_false_AX) 11.
Qed.

Instance reg_GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic:
  RegisterClass D12P_reg (fun gcsGamma:unit => @GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic_gcsGamma) 12.
Qed.

(*Rules from SeparationLogic*)

Section SLFromDeduction2SLFromAxiomatization2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma EmpDeduction2EmpAxiomatization_empAX:
EmpDeduction L GammaD1 -> EmpAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply sepcon_emp_left.
  -intros. apply derivable1_provable. apply sepcon_emp_right.
  Qed.

Section SLFromDeduction2SLFromAxiomatization3.

Context {orpL: OrLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {falsepL: FalseLanguage L}.

Lemma DupEmpSeparationLogicD2DupEmpSeparationLogic_desGamma:
DupEmpSeparationLogicDeduction L GammaD1 -> DupEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_emp_dup.
  Qed.

Lemma NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic_nssGamma:
NonsplitEmpSeparationLogicDeduction L GammaD1 -> NonsplitEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply derivable1_emp_sepcon_truep_elim.
  Qed.

End SLFromDeduction2SLFromAxiomatization3.

End SLFromDeduction2SLFromAxiomatization2.

Instance reg_NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic:
  RegisterClass D12P_reg (fun nssGamma:unit => @NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic_nssGamma) 13.
Qed.

Instance reg_EmpDeduction2EmpAxiomatization:
  RegisterClass D12P_reg (fun empAx:unit => @EmpDeduction2EmpAxiomatization_empAX) 14.
Qed.

Section SLFromDeduction2SLFromAxiomatization4.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma WandDeduction2WandAxiomatization_wandAX
      {wandD: WandDeduction L GammaD1}:
  WandAxiomatization L GammaP.
Proof.
  constructor.
  split.
  -intros. apply derivable1_provable. apply derivable1_provable in H.
   apply derivable1_wand_sepcon_adjoint;auto.
  - intros. apply derivable1_provable. apply derivable1_provable in H.
   apply derivable1_wand_sepcon_adjoint;auto.
   Qed.

End SLFromDeduction2SLFromAxiomatization4.

Instance reg_WandDeduction1WandAxiomatization:
  RegisterClass D12P_reg (fun wandAX: unit => @WandDeduction2WandAxiomatization_wandAX) 15.
Qed.

Instance reg_SepconDeduction2SepconAxiomatization:
  RegisterClass D12P_reg (fun SAx:unit => @SepconDeduction2SepconAxiomatization_sepconAX) 16.
Qed.

Section FromAxiomatizationToDeduction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma Axiomatization2Deduction_sepconD
      {sepconAX: SepconAxiomatization L GammaP}:
  SepconDeduction L GammaD1.
Proof.
  intros.
  constructor; intros.
  + rewrite derivable1_provable.
    apply sepcon_comm_impp.
  + rewrite derivable1_provable.
    apply sepcon_assoc1.
  + rewrite derivable1_provable in H, H0 |- *.
    apply sepcon_mono; auto.
Qed.

End FromAxiomatizationToDeduction.

Section SepconRulesFromDerivable1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma derivable1_sepcon_assoc2: forall x y z, (x * y) * z |-- x * (y * z).
Proof.
  AddAxiomatization.
  intros.
  apply derivable1_provable.
  apply sepcon_assoc2.
  Qed.

Lemma orp_sepcon_right
      {pL: OrLanguage L}
      {orpD: OrDeduction L GammaD1}:
  forall (x y z: expr), x * z || y * z |-- (x || y) * z.
Proof.
  AddAxiomatization.
  intros.
  apply derivable1_provable.
  apply impp_orp_sepcon.
  Qed.

Lemma falsep_sepcon_right
      {falsepL: FalseLanguage L}
      {falsepD: FalseDeduction L GammaD1}:
  forall (x: expr), FF |-- FF * x.
Proof.
  AddAxiomatization.
  intros.
  apply derivable1_provable.
  apply impp_falsep_sepcon.
  Qed.

End SepconRulesFromDerivable1.

(* TODO: This is fully temporary. *)
Section SepconRulesFromLogicEquiv'.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {GammaP: Provable L}
        {GammaE: LogicEquiv L}
        {GammEP: EquivProvable L GammaP GammaE}
        {minAX: MinimumAxiomatization L GammaP}
        {sepconAX: SepconAxiomatization L GammaP}.

Lemma sepcon_assoc_equiv:
  forall x y z, x * (y * z) --||-- (x * y) * z.
Proof.
  intros.
  apply logic_equiv_provable. split.
  + apply sepcon_assoc1.
  + apply sepcon_assoc2.
Qed.

Context {empL: EmpLanguage L}
        {empAX: EmpAxiomatization L GammaP}.

Lemma sepcon_emp_equiv: forall x, x * emp --||-- x.
Proof.
  intros.
  apply logic_equiv_provable. split.
  + apply sepcon_emp1.
  + apply sepcon_emp2.
Qed.

End SepconRulesFromLogicEquiv'.

Section SepconRulesFromLogicEquiv.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma sepcon_comm_logic_equiv:
  forall (x y: expr), x * y --||-- y * x.
Proof.
  intros.
  apply logic_equiv_derivable1. split.
  + apply derivable1_sepcon_comm.
  + apply derivable1_sepcon_comm.
Qed.

Lemma sepcon_assoc_logic_equiv:
  forall x y z, x * (y * z) --||-- (x * y) * z.
Proof.
  intros.
  apply logic_equiv_derivable1. split.
  + apply derivable1_sepcon_assoc1.
  + apply derivable1_sepcon_assoc2.
Qed.

Context {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {orpD: OrDeduction L GammaD1}
        {falsepD: FalseDeduction L GammaD1}
        {sepcon_orp_D: SepconOrDeduction L GammaD1}
        {sepcon_false_D: SepconFalseDeduction L GammaD1}.

Lemma sepcon_orp_distr_r_equiv: forall (x y z: expr),
  (x || y) * z --||-- x * z || y * z.
Proof.
  AddAxiomatization.
  AddConnective_iffp.
  intros.
  apply logic_equiv_derivable1.
  pose proof sepcon_orp_distr_r x y z.
  unfold iffp in H.
  pose proof solve_iffp_elim1 _ _ H.
  pose proof solve_iffp_elim2 _ _ H.
  rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma sepcon_orp_distr_l_equiv: forall (x y z: expr),
  x * (y || z) --||-- x * y || x * z.
Proof.
  AddAxiomatization.
  AddConnective_iffp.
  intros.
  pose proof sepcon_orp_distr_l x y z.
  unfold iffp in H.
  pose proof solve_iffp_elim1 _ _ H.
  pose proof solve_iffp_elim2 _ _ H.
  apply logic_equiv_derivable1. rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma falsep_sepcon_equiv: forall (x: expr),
  FF * x --||-- FF.
Proof.
  AddAxiomatization.
  AddConnective_iffp.
  intros.
  pose proof falsep_sepcon x.
  unfold iffp in H.
  pose proof solve_iffp_elim1 _ _ H.
  pose proof solve_iffp_elim2 _ _ H.
  apply logic_equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma sepcon_falsep_equiv: forall (x: expr),
  x * FF --||-- FF.
Proof.
  AddAxiomatization.
  AddConnective_iffp.
  intros.
  pose proof sepcon_falsep x.
  unfold iffp in H.
  pose proof solve_iffp_elim1 _ _ H.
  pose proof solve_iffp_elim2 _ _ H.
  apply logic_equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.
(*
Context {empL: EmpLanguage L}
        {empD: EmpDeduction L GammaD1}.

Lemma sepcon_emp_equiv: forall x, x * emp --||-- x.
Proof.
  AddAxiomatization.
  AddConnective_iffp.
  intros.
  pose proof sepcon_emp x.
  unfold iffp in H.
  pose proof solve_iffp_elim1 _ _ H.
  pose proof solve_iffp_elim2 _ _ H.
  apply equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.
*)
End SepconRulesFromLogicEquiv.

Section WandRules.

Context {L: Language}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {wandD: WandDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma derivable1_wand_sepcon_modus_ponens1: forall (x y: expr),
  (x -* y) * x |-- y.
Proof.
  intros.
  apply derivable1_wand_sepcon_adjoint.
  reflexivity.
Qed.

Context {sepconD: SepconDeduction L GammaD1}.

Lemma derivable1_wand_sepcon_modus_ponens2: forall (x y: expr),
  x * (x -* y) |-- y.
Proof.
  intros.
  rewrite derivable1_sepcon_comm.
  apply derivable1_wand_sepcon_adjoint.
  reflexivity.
Qed.

Lemma derivable1_wand_mono: forall x1 x2 y1 y2,
  x2 |-- x1 -> y1 |-- y2 -> (x1 -* y1) |-- (x2 -* y2).
Proof.
  intros.
  apply derivable1_wand_sepcon_adjoint.
  rewrite <- H0.
  rewrite derivable1_sepcon_comm.
  apply derivable1_wand_sepcon_adjoint.
  rewrite H.
  apply derivable1_wand_sepcon_adjoint.
  apply derivable1_wand_sepcon_modus_ponens2.
Qed.

Context {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {orpD: OrDeduction L GammaD1}
        {falsepD: FalseDeduction L GammaD1}
        {sepcon_orp_D: SepconOrDeduction L GammaD1}
        {sepcon_false_D: SepconFalseDeduction L GammaD1}.

Lemma derivable1_sepcon_elim2: forall {gcsD: GarbageCollectSeparationLogicDeduction L GammaD1} (x y: expr),
  x * y |-- y.
Proof.
  intros.
  AddAxiomatization.
  AddConnective_iffp.
  pose proof sepcon_elim2 x y.
  apply derivable1_provable;auto.
Qed.

Lemma derivable1_emp_sepcon_elim1: forall {empL: EmpLanguage L} {empD: EmpDeduction L GammaD1} {truepL: TrueLanguage L} {truepD: TrueDeduction L GammaD1} {nssD: NonsplitEmpSeparationLogicDeduction L GammaD1}  x y,
  x * y && emp |-- x.
Proof.
  intros.
  AddAxiomatization.
  pose proof emp_sepcon_elim1 x y.
  apply derivable1_provable;auto.
  Qed.

Lemma derivable1_emp_sepcon_elim2: forall {empL: EmpLanguage L} {empD: EmpDeduction L GammaD1} {truepL: TrueLanguage L} {truepD: TrueDeduction L GammaD1} {nssD: NonsplitEmpSeparationLogicDeduction L GammaD1} x y,
  x * y && emp |-- y.
Proof.
  intros.
  AddAxiomatization.
  AddConnective_iffp.
  pose proof emp_sepcon_elim2.
  apply derivable1_provable;auto.
  Qed.

Context {GammaE: LogicEquiv L}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma wand_andp_equiv: forall x y z: expr,
  x -* y && z --||-- (x -* y) && (x -* z).
Proof.
  AddAxiomatization.
  AddConnective_iffp.
  intros.
  pose proof wand_andp x y z.
  unfold iffp in H.
  pose proof solve_iffp_elim1 _ _ H.
  pose proof solve_iffp_elim2 _ _ H.
  apply logic_equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma orp_wand_equiv: forall x y z: expr,
  (x || y) -* z --||-- (x -* z) && (y -* z).
Proof.
  AddAxiomatization.
  AddConnective_iffp.
  intros.
  pose proof orp_wand x y z.
  pose proof solve_iffp_elim1 _ _ H.
  pose proof solve_iffp_elim2 _ _ H.
  apply logic_equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
Qed.

End WandRules.

(*Rules from TheoryOfSeparationAxioms*)

Class SepconMonoDeduction
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __sepcon_mono: forall x1 x2 y1 y2 : expr, x1 |-- x2 -> y1 |-- y2 -> x1 * y1 |-- x2 * y2
}.

Class SepconDeduction_weak
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __sepcon_comm_impp: forall x y, x * y |-- y * x;
  __sepcon_assoc1: forall x y z, x * (y * z) |-- (x * y) * z;
}.

Class SepconLogicEquiv_weak_iffp
        (L: Language)
        {sepconL: SepconLanguage L}
        (GammaE: LogicEquiv L) := {
  __sepcon_comm: forall x y, x * y --||-- y * x;
  __sepcon_assoc: forall x y z, x * (y * z) --||-- (x * y) * z;
}.

Class EmpLogicEquiv_iffp
        (L: Language)
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaE: LogicEquiv L) := {
  __sepcon_emp: forall x, x * emp --||-- x
}.

Lemma SepconDeductionWeak2SepconDeduction
      {L: Language}
      {minL: MinimumLanguage L}
      {sepconL: SepconLanguage L}
      {GammaD1: Derivable1 L}
      {sepconAX: SepconDeduction_weak L GammaD1}
      {sepcon_mono_AX: SepconMonoDeduction L GammaD1}:
  SepconDeduction L GammaD1.
Proof.
  constructor.
  - apply __sepcon_comm_impp.
  - apply __sepcon_assoc1.
  - apply __sepcon_mono.
Qed.

Section SepconDeduction_weak2SepconAxiomatization_weak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {sepconDw: SepconDeduction_weak L GammaD1}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Lemma SepconDeduction_weak2SepconAxiomatization_weak: SepconAxiomatization_weak L GammaP.
Proof.
  constructor.
  -intros.
   apply derivable1_provable.
   apply __sepcon_comm_impp.
  -intros.
   apply derivable1_provable.
   apply __sepcon_assoc1.
   Qed.

End SepconDeduction_weak2SepconAxiomatization_weak.

Instance reg_SepconDeduction_weak2SepconAxiomatization_weak:
  RegisterClass D12P_reg (fun sepconAX:unit => @SepconDeduction_weak2SepconAxiomatization_weak) 17.
Qed.

Section SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaPD1: ProvableDerivable1 L GammaP GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
  SepconAxiomatization_weak_iffp L GammaP.
Proof.
  pose proof Deduction2Axiomatization_minAX as minAX.
  pose proof Deduction2Axiomatization_iffpAX as iffpAX.
  constructor.
  - intros.
    pose proof __sepcon_comm x y.
    apply logic_equiv_derivable1 in H; destruct H.
    rewrite derivable1_provable in H, H0.
    apply solve_iffp_intros; auto.
  - intros.
    pose proof __sepcon_assoc x y z.
    apply logic_equiv_derivable1 in H; destruct H.
    rewrite derivable1_provable in H, H0.
    apply solve_iffp_intros; auto.
Qed.

End SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

Instance reg_SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
  RegisterClass D12P_reg (fun sepcon_weak_iffp:unit => @SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp) 18.
Qed.

Section EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {GammaPD1: ProvableDerivable1 L GammaP GammaD1}
        {empE: EmpLogicEquiv_iffp L GammaE}
        {iffpD: IffDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {andpD: AndDeduction L GammaD1}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
EmpAxiomatization_iffp L GammaP.
Proof.
  pose proof Deduction2Axiomatization_minAX as minAX.
  pose proof Deduction2Axiomatization_iffpAX as iffpAX.
  constructor.
  intros.
  pose proof __sepcon_emp x.
  apply logic_equiv_derivable1 in H; destruct H.
  rewrite derivable1_provable in H, H0.
  apply solve_iffp_intros; auto.
Qed.

End EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

Instance reg_EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
  RegisterClass D12P_reg (fun empAX_iffp:unit => @EmpLogicEquiv_iffp2EmpAxiomatization_iffp) 19.
Qed.

Section FromSepconDeductionWeakToSepcon.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {sepconD: SepconDeduction_weak L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma Adj2SepconMono: SepconMonoDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconMono.
  constructor.
  intros.
  rewrite derivable1_provable in H0, H1 |- *.
  apply TheoryOfSeparationAxioms.__sepcon_mono;auto.
  Qed.

End FromSepconDeductionWeakToSepcon.

Section FromSepconWeakIffToSepconDeductionWeak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma SepconLogicEquivWeakIff2SepconDeductionWeak:
  SepconDeduction_weak L GammaD1.
Proof.
  AddAxiomatization.
  pose proof SepconAxiomatizationWeakIff2SepconAxiomatizationWeak.
  constructor.
  -intros.
   apply derivable1_provable;apply TheoryOfSeparationAxioms.__sepcon_comm_impp.
  -intros.
   apply derivable1_provable;apply TheoryOfSeparationAxioms.__sepcon_assoc1.
   Qed.

End FromSepconWeakIffToSepconDeductionWeak.

Section FromAdjToSepconOrDeductionPropositionalCombination.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Lemma Adj2SepconOrD {orpL: OrLanguage L} {orpD: OrDeduction L GammaD1}: SepconOrDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconOr.
  constructor.
  intros.
  apply derivable1_provable.
  apply orp_sepcon_impp.
Qed.

Lemma Adj2SepconFalse {falsepL: FalseLanguage L} {falsepD: FalseDeduction L GammaD1}: SepconFalseDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconFalse.
  constructor.
  intros.
  apply derivable1_provable.
  apply falsep_sepcon_impp.
Qed.

End FromAdjToSepconOrDeductionPropositionalCombination.

Section FromEmpEIffToEmpD.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {andpD: AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {iffpD: IffDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {empD: EmpLogicEquiv_iffp L GammaE}
        {bD: BasicDeduction L GammaD1}
        {GammED1: EquivDerivable1 L GammaD1 GammaE}.

Lemma EmpLogicEquivIff2EmpDeduction:
  EmpDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof EmpAxiomatizationIff2EmpAxiomatization.
  constructor.
  + intros.
    apply derivable1_provable. apply SeparationLogic.sepcon_emp1.
  + intros.
    apply derivable1_provable. apply SeparationLogic.sepcon_emp2.
Qed.

End FromEmpEIffToEmpD.

