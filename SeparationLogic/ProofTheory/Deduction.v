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
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.


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
        (GammaD1: Derivable1 L) := {
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
        (GammaD1: Derivable1 L) := {
  orp_sepcon_left: forall x y z,
     (x || y) * z |-- x * z || y * z
}.

Class SepconFalseDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  falsep_sepcon_left: forall x,
     FF * x |-- FF
}.

Class EmpDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
    sepcon_emp1: forall x,  x * emp |-- x;
    sepcon_emp2: forall x, x |-- x * emp
}.

Class WandDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        (GammaD1: Derivable1 L) := {
  wand_sepcon_adjoint: forall x y z, x * y  |-- z <-> x |-- (y -* z)
}.

Class ExtSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  sepcon_ext: forall x, x |-- x * TT
}.

Class NonsplitEmpSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
  emp_sepcon_truep_elim: forall x, (x * TT) && emp |-- x
}.

Class DupEmpSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (GammaD1: Derivable1 L) := {
  emp_dup: forall x, x && emp |-- x * x
}.

Class GarbageCollectSeparationLogicD
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  sepcon_elim1: forall x y, x * y |-- x
}.

Section SLFromDeduction2SLFromAxiomatization1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {sepconL: SepconLanguage L}
        {ND: NormalDeduction L GammaP GammaD1}.

Lemma SepconDeduction2SepconAxiomatization_sepconAX: 
          SepconDeduction L GammaD1 -> SepconAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply sepcon_comm_impp.
  -intros. apply derivable1_provable. apply sepcon_assoc1.
  -intros. apply derivable1_provable. apply derivable1_provable in H0.
   apply derivable1_provable in H1. apply sepcon_mono;auto.
   Qed.

Context {pL: PropositionalLanguage L}.

Lemma SepconOrDeduction2SepconOrAxiomatization_sepcon_orp_AX:
SepconOrDeduction L GammaD1 -> SepconOrAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply orp_sepcon_left.
  Qed.

Lemma SepconFalseDeduction2SepconFalseAxiomatization_sepcon_false_AX:
SepconFalseDeduction L GammaD1 -> SepconFalseAxiomatization L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply falsep_sepcon_left.
  Qed.

Lemma ExtSeparationLogicD2ExtSeparationLogic_esGamma:
ExtSeparationLogicD L GammaD1 -> ExtSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply sepcon_ext.
  Qed.

Lemma GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic_gcsGamma:
GarbageCollectSeparationLogicD L GammaD1 -> GarbageCollectSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply sepcon_elim1.
  Qed.

End SLFromDeduction2SLFromAxiomatization1.

Instance reg_SepconOrDeduction2SepconOrAxiomatization:
  RegisterClass D1ToP_reg (fun sepcon_orp_AX:unit => @SepconOrDeduction2SepconOrAxiomatization_sepcon_orp_AX) 5.
Qed.

Instance reg_SepconFalseDeduction2SepconFalseAxiomatization:
  RegisterClass D1ToP_reg (fun sepcon_false_AX:unit => @SepconFalseDeduction2SepconFalseAxiomatization_sepcon_false_AX) 6.
Qed.

Instance reg_GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic:
  RegisterClass D1ToP_reg (fun gcsGamma:unit => @GarbageCollectSeparationLogicD2GarbageCollectSeparationLogic_gcsGamma) 7.
Qed.

(*Rules from SeparationLogic*)

Section SLFromDeduction2SLFromAxiomatization2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {ND: NormalDeduction L GammaP GammaD1}.

Lemma EmpDeduction2EmpAxiomatization_empAX:
EmpDeduction L GammaD1 -> EmpAxiomatization L GammaP.
Proof.
  constructor.
  -intros. apply derivable1_provable. apply sepcon_emp1.
  -intros. apply derivable1_provable. apply sepcon_emp2.
  Qed.

Section SLFromDeduction2SLFromAxiomatization3.

Context {pL: PropositionalLanguage L}.

Lemma DupEmpSeparationLogicD2DupEmpSeparationLogic_desGamma:
DupEmpSeparationLogicD L GammaD1 -> DupEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply emp_dup.
  Qed.

Lemma NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic_nssGamma:
NonsplitEmpSeparationLogicD L GammaD1 -> NonsplitEmpSeparationLogic L GammaP.
Proof.
  constructor.
  intros. apply derivable1_provable. apply emp_sepcon_truep_elim.
  Qed.

End SLFromDeduction2SLFromAxiomatization3.

End SLFromDeduction2SLFromAxiomatization2.

Instance reg_NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic:
  RegisterClass D1ToP_reg (fun nssGamma:unit => @NonsplitEmpSeparationLogicD2NonsplitEmpSeparationLogic_nssGamma) 8.
Qed.

Instance reg_EmpDeduction2EmpAxiomatization:
  RegisterClass D1ToP_reg (fun empAx:unit => @EmpDeduction2EmpAxiomatization_empAX) 9.
Qed.

Section SLFromDeduction2SLFromAxiomatization4.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {GammaP: Provable L}
        {ND: NormalDeduction L GammaP GammaD1}.

Lemma WandDeduction2WandAxiomatization_WandX:
WandDeduction L GammaD1 -> WandAxiomatization L GammaP.
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
  RegisterClass D1ToP_reg (fun WandX: unit => @WandDeduction2WandAxiomatization_WandX) 2.
Qed.

Instance reg_SepconDeduction2SepconAxiomatization:
  RegisterClass D1ToP_reg (fun SAx:unit => @SepconDeduction2SepconAxiomatization_sepconAX) 3.
Qed.

Section SepconRulesFromDerivable1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma sepcon_assoc2: forall x y z, (x * y) * z |-- x * (y * z).
Proof.
  AddAxiomatization.
  intros.
  apply derivable1_provable.
  apply sepcon_assoc2.
  Qed.

Context {pL: PropositionalLanguage L}
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}.

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
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {NE2: NormalEquiv2 L GammaD1 GammaE}
        {minD: MinimumDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

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
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}
        {sepcon_orp_D: SepconOrDeduction L GammaD1}
        {sepcon_false_D: SepconFalseDeduction L GammaD1}.

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
        {empD: EmpDeduction L GammaD1}.

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
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma provable_wand_sepcon_modus_ponens1: forall (x y: expr),
  (x -* y) * x |-- y.
Proof.
  AddAxiomatization.
  intros.
  pose proof provable_wand_sepcon_modus_ponens1 x y.
  apply derivable1_provable;auto.
  Qed.

Context {sepconD: SepconDeduction L GammaD1}.

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
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}
        {sepcon_orp_D: SepconOrDeduction L GammaD1}
        {sepcon_false_D: SepconFalseDeduction L GammaD1}.

Lemma sepcon_elim2: forall {gcsD: GarbageCollectSeparationLogicD L GammaD1} (x y: expr),
  x * y |-- y.
Proof.
  intros.
  AddAxiomatization.
  pose proof sepcon_elim2 x y.
  apply derivable1_provable;auto.
  Qed.

Lemma emp_sepcon_elim1: forall {empL: EmpLanguage L} {empD: EmpDeduction L GammaD1} {nssD: NonsplitEmpSeparationLogicD L GammaD1} x y,
  x * y && emp |-- x.
Proof.
  intros.
  AddAxiomatization.
  pose proof emp_sepcon_elim1 x y.
  apply derivable1_provable;auto.
  Qed.

Lemma emp_sepcon_elim2: forall {empL: EmpLanguage L} {empD: EmpDeduction L GammaD1} {nssD: NonsplitEmpSeparationLogicD L GammaD1} x y,
  x * y && emp |-- y.
Proof.
  intros.
  AddAxiomatization.
  pose proof emp_sepcon_elim2.
  apply derivable1_provable;auto.
  Qed.

Context {GammaE: LogicEquiv L}
        {NE2: NormalEquiv2 L GammaD1 GammaE}.

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

(*Rules from TheoryOfSeparationAxioms*)

Class SepconMonoDeduction
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __sepcon_mono: forall x1 x2 y1 y2 : expr, x1 |-- x2 -> y1 |-- y2 -> x1 * y1 |-- x2 * y2
}.

Class SepconDeduction_weak
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (GammaD1: Derivable1 L) := {
  __sepcon_comm_impp: forall x y, x * y |-- y * x;
  __sepcon_assoc1: forall x y z, x * (y * z) |-- (x * y) * z;
}.

Class SepconLogicEquiv_weak_iffp
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        (GammaE: LogicEquiv L) := {
  __sepcon_comm: forall x y, x * y --||-- y * x;
  __sepcon_assoc: forall x y z, x * (y * z) --||-- (x * y) * z;
}.

Class EmpLogicEquiv_iffp
        (L: Language)
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
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
      {minAX: MinimumDeduction L GammaD1}
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
        {ND: NormalDeduction L GammaP GammaD1}.

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
  RegisterClass D1ToP_reg (fun sepconAX:unit => @SepconDeduction_weak2SepconAxiomatization_weak) 10.
Qed.

Section SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {D2P: Provable_Derivable1 L GammaP GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {minD:MinimumDeduction L GammaD1}
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}
        {ND: NormalDeduction L GammaP GammaD1}
        {NE2: NormalEquiv2 L GammaD1 GammaE}.

Lemma SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
SepconAxiomatization_weak_iffp L GammaP.
Proof.
  constructor.
  -intros.
   pose proof __sepcon_comm x y.
   unfold iffp.
   pose proof ipD2ipAx.
   pose proof Derivable12Axiomatization_minAX.
   apply equiv_derivable1 in H;destruct H.
   rewrite derivable1_provable in H, H2.
   pose proof andp_intros (x * y --> y * x) (y * x --> x * y).
   pose proof modus_ponens _ _ H3 H.
   pose proof modus_ponens _ _ H4 H2.
   auto.
  -intros.
   pose proof __sepcon_assoc x y z.
   unfold iffp.
   pose proof ipD2ipAx.
   pose proof Derivable12Axiomatization_minAX.
   apply equiv_derivable1 in H;destruct H.
   rewrite derivable1_provable in H, H2.
   pose proof andp_intros (x * (y * z) --> x * y * z) (x * y * z --> x * (y * z)).
   pose proof modus_ponens _ _ H3 H.
   pose proof modus_ponens _ _ H4 H2.
   auto.
   Qed.

End SepconLogicEquiv_weak_iffpToSepconAxiomatization_weak_iffp.

Instance reg_SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp:
  RegisterClass D1ToP_reg (fun sepcon_weak_iffp:unit => @SepconLogicEquiv_weak_iffp2SepconAxiomatization_weak_iffp) 11.
Qed.

Section EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaE: LogicEquiv L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {D2P: Provable_Derivable1 L GammaP GammaD1}
        {empE: EmpLogicEquiv_iffp L GammaE}
        {minD:MinimumDeduction L GammaD1}
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}
        {ND: NormalDeduction L GammaP GammaD1}
        {NE2: NormalEquiv2 L GammaD1 GammaE}.

Lemma EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
EmpAxiomatization_iffp L GammaP.
Proof.
  constructor.
  intros.
  unfold iffp.
  pose proof __sepcon_emp x.
  pose proof ipD2ipAx.
  pose proof Derivable12Axiomatization_minAX.
  apply equiv_derivable1 in H;destruct H.
  rewrite derivable1_provable in H, H2.
  pose proof andp_intros (x * emp --> x) (x --> x * emp).
  pose proof modus_ponens _ _ H3 H.
  pose proof modus_ponens _ _ H4 H2.
  auto.
  Qed.

End EmpLogicEquiv_iffp2EmpAxiomatization_iffp.

Instance reg_EmpLogicEquiv_iffp2EmpAxiomatization_iffp:
  RegisterClass D1ToP_reg (fun empAX_iffp:unit => @EmpLogicEquiv_iffp2EmpAxiomatization_iffp) 12.
Qed.

Section FromSepconDeductionWeakToSepcon.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {sepconD: SepconDeduction_weak L GammaD1}
        {BD: BasicDeduction L GammaD1}.

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
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {GammaE: LogicEquiv L}
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}
        {sepconE: SepconLogicEquiv_weak_iffp L GammaE}
        {BD: BasicDeduction L GammaD1}
        {NE2: NormalEquiv2 L GammaD1 GammaE}.

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
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {wandD: WandDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma Adj2SepconOrD: SepconOrDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconOr.
  constructor.
  intros.
  apply derivable1_provable.
  apply SeparationLogic.orp_sepcon_left.
  Qed.

Lemma Adj2SepconFalse: SepconFalseDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof Adj2SepconFalse.
  constructor.
  intros.
  apply derivable1_provable.
  apply SeparationLogic.falsep_sepcon_left.
  Qed.

End FromAdjToSepconOrDeductionPropositionalCombination.

Section FromEmpEIffToEmpD.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {minD: MinimumDeduction L GammaD1}
        {ipD: IntuitionisticPropositionalDeduction L GammaD1}
        {sepconD: SepconDeduction L GammaD1}
        {empD: EmpLogicEquiv_iffp L GammaE}
        {BD: BasicDeduction L GammaD1}
        {NE2: NormalEquiv2 L GammaD1 GammaE}.

Lemma EmpLogicEquivIff2EmpDeduction:
  EmpDeduction L GammaD1.
Proof.
  AddAxiomatization.
  pose proof EmpAxiomatizationIff2EmpAxiomatization.
  constructor.
  -intros.
   apply derivable1_provable. apply SeparationLogic.sepcon_emp1.
  -intros.
   apply derivable1_provable. apply SeparationLogic.sepcon_emp2.
   Qed.

End FromEmpEIffToEmpD.
