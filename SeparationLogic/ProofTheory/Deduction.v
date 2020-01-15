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
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.


Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import Derivable1.
Local Open Scope Derivable1.

Class SepconDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD: Derivable1 L) := {
  sepcon_comm_impp: forall x y, x * y |-- y * x;
  sepcon_assoc1: forall x y z, x * (y * z) |-- (x * y) * z;
  sepcon_mono: forall x1 x2 y1 y2, x1 |-- x2 -> y1 |-- y2 
               -> (x1 * y1) |-- (x2 * y2);
}.

Class SepconOrDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD: Derivable1 L) := {
  orp_sepcon_left: forall x y z,
     (x || y) * z |-- x * z || y * z
}.

Class SepconFalseDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD: Derivable1 L) := {
  falsep_sepcon_left: forall x,
     FF * x |-- FF
}.

Class EmpDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD: Derivable1 L) := {
    sepcon_emp1: forall x,  x * emp |-- x;
    sepcon_emp2: forall x, x |-- x * emp
}.

Class WandDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        (GammaD: Derivable1 L) := {
  wand_sepcon_adjoint: forall x y z, x * y  |-- z <-> x |-- (y -* z)
}.

Class ExtSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD: Derivable1 L) := {
  sepcon_ext: forall x, x |-- x * TT
}.

Class NonsplitEmpSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD: Derivable1 L) := {
  emp_sepcon_truep_elim: forall x, (x * TT) && emp |-- x
}.

Class DupEmpSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD: Derivable1 L) := {
  emp_dup: forall x, x && emp |-- x * x
}.

Class GarbageCollectSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD: Derivable1 L) := {
  sepcon_elim1: forall x y, x * y |-- x
}.

Section SLFromDeduction2SLFromAxiomatization1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaD: Derivable1 L}
        {GammaP: Provable L}
        {sepconL: SepconLanguage L}
        {ND: NormalDeduction L GammaP GammaD}.

Lemma SepconDeduction2SepconAxiomatization: 
          SepconDeduction L GammaD -> SepconAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply sepcon_comm_impp.
  -intros. apply derivable1_provable. apply sepcon_assoc1.
  -intros. apply derivable1_provable. apply derivable1_provable in H0.
   apply derivable1_provable in H1. apply sepcon_mono;auto.
   Qed.

Context {pL: PropositionalLanguage L}.

Lemma SepconOrDeduction2SepconOrAxiomatization:
SepconOrDeduction L GammaD -> SepconOrAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply orp_sepcon_left.
  Qed.

Lemma SepconFalseDeduction2SepconFalseAxiomatization:
SepconFalseDeduction L GammaD -> SepconFalseAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply falsep_sepcon_left.
  Qed.

Lemma ExtSeparationLogicD2ExtSeparationLogic:
ExtSeparationLogicD L GammaD -> ExtSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply sepcon_ext.
  Qed.

Lemma GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic:
GarbageCollectSeparationLogicD L GammaD -> GarbageCollectSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply sepcon_elim1.
  Qed.

End SLFromDeduction2SLFromAxiomatization1.

Instance reg_SepconOrDeduction2SepconOrAxiomatization:
  RegisterClass D1ToP_reg (fun sepcon_orp_AX:unit => @SepconOrDeduction2SepconOrAxiomatization) 5.
Qed.

Instance reg_SepconFalseDeduction2SepconFalseAxiomatization:
  RegisterClass D1ToP_reg (fun sepcon_false_AX:unit => @SepconFalseDeduction2SepconFalseAxiomatization) 6.
Qed.

Instance reg_GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic:
  RegisterClass D1ToP_reg (fun gcs:unit => @GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic) 7.
Qed.

Section SLFromDeduction2SLFromAxiomatization2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD: Derivable1 L}
        {GammaP: Provable L}
        {ND: NormalDeduction L GammaP GammaD}.

Lemma EmpDeduction2EmpAxiomatization:
EmpDeduction L GammaD -> EmpAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply sepcon_emp1.
  -intros. apply derivable1_provable. apply sepcon_emp2.
  Qed.

Section SLFromDeduction2SLFromAxiomatization3.

Context {pL: PropositionalLanguage L}.

Lemma DupEmpSeparationLogicD2DupEmpSeparationLogic:
DupEmpSeparationLogicD L GammaD -> DupEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply emp_dup.
  Qed.

Lemma NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic:
NonsplitEmpSeparationLogicD L GammaD -> NonsplitEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply emp_sepcon_truep_elim.
  Qed.

End SLFromDeduction2SLFromAxiomatization3.

End SLFromDeduction2SLFromAxiomatization2.

Instance reg_NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic:
  RegisterClass D1ToP_reg (fun nss:unit => @NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic) 8.
Qed.

Instance reg_EmpDeduction2EmpAxiomatization:
  RegisterClass D1ToP_reg (fun empAx:unit => @EmpDeduction2EmpAxiomatization) 9.
Qed.



Section SLFromDeduction2SLFromAxiomatization4.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD: Derivable1 L}
        {GammaP: Provable L}
        {ND: NormalDeduction L GammaP GammaD}.

Lemma WandDeduction2WandAxiomatization:
WandDeduction L GammaD -> WandAxiomatization L GammaP.
Proof.
  constructor.
  split.
  -intros. apply derivable1_provable. apply derivable1_provable in H0.
   apply wand_sepcon_adjoint;auto.
  - intros. apply derivable1_provable. apply derivable1_provable in H0.
   apply wand_sepcon_adjoint;auto.
   Qed.

End SLFromDeduction2SLFromAxiomatization4.

Instance reg_WandDeduction1WandAxiomatization:
  RegisterClass D1ToP_reg (fun WAx: unit => @WandDeduction2WandAxiomatization) 2.
Qed.

Instance reg_SepconDeduction2SepconAxiomatization:
  RegisterClass D1ToP_reg (fun SAx:unit => @SepconDeduction2SepconAxiomatization) 3.
Qed.

Section SepconRulesFromDerivable1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Derivable1 L}
        {minD: MinimumDeduction L Gamma}
        {sepconD: SepconDeduction L Gamma}
        {BD: BasicDeduction L Gamma}.

Lemma sepcon_assoc2: forall x y z, (x * y) * z |-- x * (y * z).
Proof.
  AddAxiomatization.
  intros.
  apply derivable1_provable.
  apply sepcon_assoc2.
  Qed.

Context {pL: PropositionalLanguage L}
        {ipD: IntuitionisticPropositionalDeduction L Gamma}.

Lemma orp_sepcon_right:
  forall (x y z: expr), x * z || y * z |-- (x || y) * z.
Proof.
  AddAxiomatization.
  intros.
  apply derivable1_provable.
  apply orp_sepcon_right.
  Qed.

Lemma falsep_sepcon_right:
  forall (x: expr), FF |-- FF * x.
Proof.
  AddAxiomatization.
  intros.
  apply derivable1_provable.
  apply falsep_sepcon_right.
  Qed.

End SepconRulesFromDerivable1.

Section SepconRulesFromLogicEquiv.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Derivable1 L}
        {GammaE: LogicEquiv L}
        {NE2: NormalEquiv2 L Gamma GammaE}
        {minD: MinimumDeduction L Gamma}
        {sepconD: SepconDeduction L Gamma}
        {BD: BasicDeduction L Gamma}.

Lemma sepcon_comm:
  forall (x y: expr), x * y --||-- y * x.
Proof.
  intros.
  apply equiv_derivable1. split.
  -apply sepcon_comm_impp.
  -apply sepcon_comm_impp.
  Qed.

Lemma sepcon_assoc:
  forall x y z, x * (y * z) --||-- (x * y) * z.
Proof.
  intros.
  apply equiv_derivable1. split.
  -apply sepcon_assoc1.
  -apply sepcon_assoc2.
  Qed.

Context {pL: PropositionalLanguage L}
        {ipD: IntuitionisticPropositionalDeduction L Gamma}
        {sepcon_orp_D: SepconOrDeduction L Gamma}
        {sepcon_false_D: SepconFalseDeduction L Gamma}.

Lemma sepcon_orp_distr_r: forall (x y z: expr),
  (x || y) * z --||-- x * z || y * z.
Proof.
  AddAxiomatization.
  intros.
  apply equiv_derivable1.
  pose proof sepcon_orp_distr_r x y z.
  unfold iffp in H.
  pose proof solve_andp_elim1 _ _ H.
  pose proof solve_andp_elim2 _ _ H.
  rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma sepcon_orp_distr_l: forall (x y z: expr),
  x * (y || z) --||-- x * y || x * z.
Proof.
  AddAxiomatization.
  intros.
  pose proof sepcon_orp_distr_l x y z.
  unfold iffp in H.
  pose proof solve_andp_elim1 _ _ H.
  pose proof solve_andp_elim2 _ _ H.
  apply equiv_derivable1. rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma falsep_sepcon: forall (x: expr),
  FF * x --||-- FF.
Proof.
  AddAxiomatization.
  intros.
  pose proof falsep_sepcon x.
  unfold iffp in H.
  pose proof solve_andp_elim1 _ _ H.
  pose proof solve_andp_elim2 _ _ H.
  apply equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma sepcon_falsep: forall (x: expr),
  x * FF --||-- FF.
Proof.
  AddAxiomatization.
  intros.
  pose proof sepcon_falsep x.
  unfold iffp in H.
  pose proof solve_andp_elim1 _ _ H.
  pose proof solve_andp_elim2 _ _ H.
  apply equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Context {empL: EmpLanguage L}
        {empAX: EmpDeduction L Gamma}.

Lemma sepcon_emp: forall x, x * emp --||-- x.
Proof.
  AddAxiomatization.
  intros.
  pose proof sepcon_emp x.
  unfold iffp in H.
  pose proof solve_andp_elim1 _ _ H.
  pose proof solve_andp_elim2 _ _ H.
  apply equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

End SepconRulesFromLogicEquiv.

Section WandRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Derivable1 L}
        {minAX: MinimumDeduction L Gamma}
        {wandX: WandDeduction L Gamma}
        {BD: BasicDeduction L Gamma}.

Lemma provable_wand_sepcon_modus_ponens1: forall (x y: expr),
  (x -* y) * x |-- y.
Proof.
  AddAxiomatization.
  intros.
  pose proof provable_wand_sepcon_modus_ponens1 x y.
  apply derivable1_provable;auto.
  Qed.

Context {sepconAX: SepconDeduction L Gamma}.

Lemma provable_wand_sepcon_modus_ponens2: forall (x y: expr),
  x * (x -* y) |-- y.
Proof.
  AddAxiomatization.
  intros.
  pose proof provable_wand_sepcon_modus_ponens2 x y.
  apply derivable1_provable;auto.
  Qed.

Lemma wand_mono: forall x1 x2 y1 y2,
  x2 |-- x1 -> y1 |-- y2 -> (x1 -* y1) |-- (x2 -* y2).
Proof.
  AddAxiomatization.
  intros.
  pose proof wand_mono x1 x2 y1 y2.
  rewrite derivable1_provable in H, H0 |- *.
  apply H1 in H;[auto|auto].
  Qed.

Context {pL: PropositionalLanguage L}
        {ipD: IntuitionisticPropositionalDeduction L Gamma}
        {sepcon_orp_D: SepconOrDeduction L Gamma}
        {sepcon_false_D: SepconFalseDeduction L Gamma}.

Lemma sepcon_elim2: forall {gcsD: GarbageCollectSeparationLogicD L Gamma} (x y: expr),
  x * y |-- y.
Proof.
  intros.
  AddAxiomatization.
  pose proof sepcon_elim2 x y.
  apply derivable1_provable;auto.
  Qed.

Lemma emp_sepcon_elim1: forall {empL: EmpLanguage L} {empD: EmpDeduction L Gamma} {nssD: NonsplitEmpSeparationLogicD L Gamma} x y,
  x * y && emp |-- x.
Proof.
  intros.
  AddAxiomatization.
  pose proof emp_sepcon_elim1 x y.
  apply derivable1_provable;auto.
  Qed.

Lemma emp_sepcon_elim2: forall {empL: EmpLanguage L} {empD: EmpDeduction L Gamma} {nssD: NonsplitEmpSeparationLogicD L Gamma} x y,
  x * y && emp |-- y.
Proof.
  intros.
  AddAxiomatization.
  pose proof emp_sepcon_elim2.
  apply derivable1_provable;auto.
  Qed.

Context {GammaE: LogicEquiv L}
        {NE2: NormalEquiv2 L Gamma GammaE}.

Lemma wand_andp: forall x y z: expr,
  x -* y && z --||-- (x -* y) && (x -* z).
Proof.
  AddAxiomatization.
  intros.
  pose proof wand_andp x y z.
  unfold iffp in H.
  pose proof solve_andp_elim1 _ _ H.
  pose proof solve_andp_elim2 _ _ H.
  apply equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

Lemma orp_wand: forall x y z: expr,
  (x || y) -* z --||-- (x -* z) && (y -* z).
Proof.
  AddAxiomatization.
  intros.
  pose proof orp_wand x y z.
  pose proof solve_andp_elim1 _ _ H.
  pose proof solve_andp_elim2 _ _ H.
  apply equiv_derivable1;rewrite !derivable1_provable.
  split;[auto|auto].
  Qed.

End WandRules.