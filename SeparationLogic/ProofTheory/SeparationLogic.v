Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
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

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.

Class SepconAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  sepcon_comm_impp: forall x y, |-- x * y --> y * x;
  sepcon_assoc1: forall x y z, |-- x * (y * z) --> (x * y) * z;
  sepcon_mono: forall x1 x2 y1 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- (x1 * y1) --> (x2 * y2);
}.

Class SepconOrAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  orp_sepcon_impp: forall (x y z: expr),
    |-- (x || y) * z --> x * z || y * z
}.

Class SepconCoqPropAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {iffpL: IffLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  prop_andp_sepcon1: forall P Q R,
    |-- (!! P && Q) * R <--> !! P && (Q * R)
}.

Class SepconFalseAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {falsepL: FalseLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  falsep_sepcon_impp: forall (x: expr),
    |-- FF * x --> FF
}.

Class EmpAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
    sepcon_emp1: forall x, |-- x * emp --> x;
    sepcon_emp2: forall x, |-- x --> x * emp
}.

Class WandAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        (Gamma: Provable L) := {
  wand_sepcon_adjoint: forall x y z, |-- x * y --> z <-> |-- x --> (y -* z)
}.

Class ExtSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {trueL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  sepcon_ext: forall x, |-- x --> x * TT
}.

Class NonsplitEmpSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
  emp_sepcon_truep_elim: forall x, |-- (x * TT) && emp --> x
}.

Class DupEmpSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
  emp_dup: forall x, |-- x && emp --> x * x
}.

(* Only for documentation *)
Class MallocFreeSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
  MallocFreeSeparationLogic_NonsplitEmpSeparationLogic :>
    NonsplitEmpSeparationLogic L Gamma;
  MallocFreeSeparationLogic_DupEmpSeparationLogic :>
    DupEmpSeparationLogic L Gamma
}.

Class GarbageCollectSeparationLogic
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  sepcon_elim1: forall x y, |-- x * y --> x
}.

Section SepconRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}.

Lemma sepcon_Comm: Commutativity L Gamma sepcon.
Proof.
  constructor.
  intros.
  apply sepcon_comm_impp.
Qed.

Lemma sepcon_Mono: Monotonicity L Gamma sepcon.
Proof.
  constructor.
  intros.
  apply sepcon_mono; auto.
Qed.

Lemma sepcon_Assoc: Associativity L Gamma sepcon.
Proof.
  apply @Build_Associativity1; auto.
  + apply sepcon_Comm.
  + apply sepcon_Mono.
  + intros.
    apply sepcon_assoc1.
Qed.

Lemma sepcon_assoc2: forall x y z, |-- (x * y) * z --> x * (y * z).
Proof.
  intros.
  apply (@prodp_assoc2 _ _ _ _ sepcon_Assoc).
Qed.

Context {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}.

Lemma sepcon_comm:
  forall (x y: expr), |-- x * y <--> y * x.
Proof.
  intros.
  apply (@prodp_comm _ _ _ _ _ _ _ sepcon_Comm).
Qed.

Lemma sepcon_assoc:
  forall x y z, |-- x * (y * z) <--> (x * y) * z.
Proof.
  intros.
  apply (@prodp_assoc _ _ _ _ _ _ _ sepcon_Assoc).
Qed.

Lemma impp_orp_sepcon:
  forall (x y z: expr), |-- x * z || y * z --> (x || y) * z.
Proof.
  intros.
  apply solve_orp_impp; apply sepcon_mono.
  - apply orp_intros1.
  - apply provable_impp_refl.
  - apply orp_intros2.
  - apply provable_impp_refl.
Qed.

Lemma impp_falsep_sepcon:
  forall (x: expr),|-- FF --> FF * x.
Proof.
  intros.
  apply falsep_elim.
Qed.

Context {sepcon_orp_AX: SepconOrAxiomatization L Gamma}
        {sepcon_false_AX: SepconFalseAxiomatization L Gamma}.

Lemma sepcon_orp_RDistr: RightDistr L Gamma sepcon orp.
Proof.
  constructor; intros.
  + apply orp_sepcon_impp.
  + apply impp_orp_sepcon.
Qed.

Lemma sepcon_orp_LDistr: LeftDistr L Gamma sepcon orp.
Proof.
  apply @RightDistr2LeftDistr; auto.
  + apply sepcon_Comm.
  + apply orp_Mono.
  + apply sepcon_orp_RDistr.
Qed.

Lemma sepcon_orp_distr_r: forall (x y z: expr),
  |-- (x || y) * z <--> x * z || y * z.
Proof.
  intros.
  apply (@prodp_sump_distr_r _ _ _ _ _ _ _ _ sepcon_orp_RDistr).
Qed.

Lemma sepcon_orp_distr_l: forall (x y z: expr),
  |-- x * (y || z) <--> x * y || x * z.
Proof.
  intros.
  apply (@prodp_sump_distr_l _ _ _ _ _ _ _ _ sepcon_orp_LDistr).
Qed.

Lemma falsep_sepcon: forall (x: expr),
  |-- FF * x <--> FF.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply falsep_sepcon_impp.
  + apply impp_falsep_sepcon.
Qed.

Lemma sepcon_falsep: forall (x: expr),
  |-- x * FF <--> FF.
Proof.
  intros.
  rewrite sepcon_comm.
  apply falsep_sepcon.
Qed.

Context {empL: EmpLanguage L}
        {empAX: EmpAxiomatization L Gamma}.

Lemma sepcon_emp: forall x, |-- x * emp <--> x.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply sepcon_emp1.
  + apply sepcon_emp2.
Qed.

Lemma sepcon_LU: LeftUnit L Gamma emp sepcon.
Proof.
  apply Build_LeftUnit; intros.
  + rewrite sepcon_comm_impp.
    apply sepcon_emp1.
  + rewrite <- sepcon_comm_impp.
    apply sepcon_emp2.
Qed.

Lemma sepcon_RU: RightUnit L Gamma emp sepcon.
Proof.
  apply Build_RightUnit.
  intros.
  + apply sepcon_emp1.
  + apply sepcon_emp2.
Qed.

(** Proof rules for cancel. **)

Lemma cancel_ready: forall x y, |-- x * emp --> y -> |-- x --> y.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- sepcon_emp2 in H.
  auto.
Qed.

Lemma cancel_one_succeed: forall u x y z,
  |-- x * y --> z -> |-- (u * x) * y --> u * z.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite sepcon_assoc2.
  apply sepcon_mono; auto.
  apply provable_impp_refl.
Qed.

Lemma cancel_one_giveup: forall x y z w v,
  |-- x * (y * z) --> w * v-> |-- (y * x) * z --> w * v.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- H.
  pose proof sepcon_comm_impp y x.
  pose proof sepcon_mono _ _ _ _ H0 (provable_impp_refl z).
  rewrite H1.
  apply sepcon_assoc2.
Qed.

Lemma cancel_rev: forall x y z w,  |-- (y * x) * z --> w -> |-- x * (y * z) --> w.
Proof.
  clear - minAX sepconAX empAX.
  intros.
  rewrite <- H.
  pose proof sepcon_comm_impp x y.
  pose proof sepcon_mono _ _ _ _ H0 (provable_impp_refl z).
  rewrite <- H1.
  apply sepcon_assoc1.
Qed.

Lemma cancel_finish: forall x, |-- x * emp --> x.
Proof.
  apply sepcon_emp1.
Qed.

End SepconRules.

Section WandRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {wandX: WandAxiomatization L Gamma}.

Lemma wand_sepcon_Adj: Adjointness L Gamma sepcon wand.
Proof.
  constructor.
  intros.
  apply wand_sepcon_adjoint.
Qed.

Lemma provable_wand_sepcon_modus_ponens1: forall (x y: expr),
  |-- (x -* y) * x --> y.
Proof.
  intros.
  apply (@adjoint_modus_ponens _ _ _ _ _ _ wand_sepcon_Adj).
Qed.

Context {sepconAX: SepconAxiomatization L Gamma}.

Lemma provable_wand_sepcon_modus_ponens2: forall (x y: expr),
  |-- x * (x -* y) --> y.
Proof.
  intros.
  rewrite (sepcon_comm_impp x (x -* y)).
  apply provable_wand_sepcon_modus_ponens1.
Qed.

Lemma wand_mono: forall x1 x2 y1 y2,
  |-- x2 --> x1 -> |-- y1 --> y2 -> |-- (x1 -* y1) --> (x2 -* y2).
Proof.
  intros.
  apply (@funcp_mono _ _ _ _ _ _ wand_sepcon_Adj sepcon_Mono); auto.
Qed.

Context {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {sepcon_orp_AX: SepconOrAxiomatization L Gamma}
        {sepcon_false_AX: SepconFalseAxiomatization L Gamma}.

Lemma wand_andp: forall x y z: expr,
  |-- x -* y && z <--> (x -* y) && (x -* z).
Proof.
  intros.
  apply (@funcp_andp_distr_r _ _ _ _ _ _ wand_sepcon_Adj); auto.
Qed.

Lemma orp_wand: forall x y z: expr,
  |-- (x || y) -* z <--> (x -* z) && (y -* z).
Proof.
  intros.
  apply (@orp_funcp _ _ _ _ _ _ _ _ wand_sepcon_Adj _ _ _ _ sepcon_Comm); auto.
Qed.

Lemma sepcon_elim2: forall {gcsGamma: GarbageCollectSeparationLogic L Gamma} (x y: expr),
  |-- x * y --> y.
Proof.
  intros.
  rewrite (sepcon_comm x y).
  apply sepcon_elim1.
Qed.

Lemma emp_sepcon_elim1: forall {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y,
  |-- x * y && emp --> x.
Proof.
  intros.
  rewrite <- (emp_sepcon_truep_elim x) at 2.
  apply andp_proper_impp; [| apply provable_impp_refl].
  apply sepcon_mono; [apply provable_impp_refl |].
  apply solve_impp_elim_left, provable_truep.
Qed.

Lemma emp_sepcon_elim2: forall {empL: EmpLanguage L} {empAX: EmpAxiomatization L Gamma} {nssGamma: NonsplitEmpSeparationLogic L Gamma} x y,
  |-- x * y && emp --> y.
Proof.
  intros.
  rewrite sepcon_comm.
  apply emp_sepcon_elim1.
Qed.

End WandRules.

