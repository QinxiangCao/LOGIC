Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
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

Section test_Ax.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD: Derivable1 L}
        {minD: MinimumDeduction L GammaD}
        {WD: WandDeduction L GammaD}
        {SD: SepconDeduction L GammaD}
        {BD: BasicDeduction L GammaD}.

Lemma wand_mono: forall x1 x2 y1 y2,
  x2 |-- x1 -> y1 |-- y2 -> (x1 -* y1) |-- (x2 -* y2).
Proof.
  AddAxiomatization.
  intros. rewrite derivable1_provable in H, H0 |- *.
  apply wand_mono;auto.
  Qed.

End test_Ax.