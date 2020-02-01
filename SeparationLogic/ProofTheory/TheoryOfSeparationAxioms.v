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
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import CoqPropInLogicNotation.
Import SeparationLogicNotation.

Class SepconMonoAxiomatization
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  __sepcon_mono: forall x1 x2 y1 y2 : expr, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- x1 * y1 --> x2 * y2
}.

Class SepconAxiomatization_weak
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  __sepcon_comm_impp: forall x y, |-- x * y --> y * x;
  __sepcon_assoc1: forall x y z, |-- x * (y * z) --> (x * y) * z;
}.

Class SepconAxiomatization_weak_iffp
        (L: Language)
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        (Gamma: Provable L) := {
  __sepcon_comm: forall x y, |-- x * y <--> y * x;
  __sepcon_assoc: forall x y z, |-- x * (y * z) <--> (x * y) * z;
}.

Class EmpAxiomatization_iffp
        (L: Language)
        {iffpL: IffLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        (Gamma: Provable L) := {
  __sepcon_emp: forall x, |-- x * emp <--> x
}.

Lemma SepconAxiomatizationWeak2SepconAxiomatization
      {L: Language}
      {minL: MinimumLanguage L}
      {sepconL: SepconLanguage L}
      {Gamma: Provable L}
      {minAX: MinimumAxiomatization L Gamma}
      {sepconAX: SepconAxiomatization_weak L Gamma}
      {sepcon_mono_AX: SepconMonoAxiomatization L Gamma}:
  SepconAxiomatization L Gamma.
Proof.
  intros.
  constructor.
  + apply __sepcon_comm_impp.
  + apply __sepcon_assoc1.
  + apply __sepcon_mono.
Qed.

Section FromAdjPlusSepconWeakToSepcon.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization_weak L Gamma}.

Let sepcon_Comm: P.Commutativity L Gamma sepcon.
Proof.
  constructor.
  intros.
  apply __sepcon_comm_impp.
Qed.

Let sepcon_Mono: P.Monotonicity L Gamma sepcon.
Proof.
  apply @P.Adjoint2Mono with (funcp := wand).
  + auto.
  + apply wand_sepcon_Adj.
  + apply sepcon_Comm.
Qed.

Lemma Adj2SepconMono: SepconMonoAxiomatization L Gamma.
Proof.
  constructor.
  intros.
  apply (@P.prodp_mono _ _ _ _ sepcon_Mono); auto.
Qed.

End FromAdjPlusSepconWeakToSepcon.

Section FromSepconWeakIffToSepconWeak.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization_weak_iffp L Gamma}.

Lemma SepconAxiomatizationWeakIff2SepconAxiomatizationWeak:
  SepconAxiomatization_weak L Gamma.
Proof.
  constructor.
  + pose proof __sepcon_comm.
    intros.
    eapply solve_iffp_elim1.
    apply H.
  + pose proof __sepcon_assoc.
    intros.
    eapply solve_iffp_elim1.
    apply H.
Qed.

End FromSepconWeakIffToSepconWeak.

Section FromAdjToPropositionalCombination.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {coq_prop_L: CoqPropLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {coq_prop_AX: CoqPropAxiomatization L Gamma}
        {speconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}.

Let RDistr: P.RightDistr L Gamma sepcon orp.
Proof.
  apply (@P.Adjoint2RDistr _ _ _ _ _ _ _ wand).
  apply wand_sepcon_Adj.
Qed.

Let LDistr: P.LeftDistr L Gamma sepcon orp.
Proof.
  apply @P.RightDistr2LeftDistr; auto.
  + apply sepcon_Comm.
  + apply orp_Mono.
Qed.

Lemma Adj2SepconOr: SepconOrAxiomatization L Gamma.
Proof.
  intros.
  constructor.
  intros.
  pose proof @P.prodp_sump_distr_r _ _ _ _ _ _ _ _ RDistr.
  rewrite H.
  apply provable_impp_refl.
Qed.

Lemma Adj2SepconFalse: SepconFalseAxiomatization L Gamma.
Proof.
  intros.
  constructor.
  intros.
  rewrite (@P.falsep_prodp _ _ _ _ _ _ wand_sepcon_Adj); auto.
  apply provable_impp_refl.
Qed.

Lemma Adj2SepconCoqProp: SepconCoqPropAxiomatization L Gamma.
Proof.
  constructor.
  intros.
  apply solve_iffp_intros.
  + apply solve_impp_andp.
    - apply wand_sepcon_adjoint.
      apply coq_prop_andp_impp.
      intros.
      apply wand_sepcon_adjoint.
      apply aux_minimun_rule00.
      apply coq_prop_intros.
      auto.
    - apply sepcon_mono.
      * apply andp_elim2.
      * apply provable_impp_refl.
  + apply coq_prop_andp_impp.
    intros.
    apply sepcon_mono.
    - rewrite coq_prop_andp by auto.
      apply provable_impp_refl.
    - apply provable_impp_refl.
Qed.

End FromAdjToPropositionalCombination.

Section FromEmpIffToEmp.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {empAX: EmpAxiomatization_iffp L Gamma}.

Lemma EmpAxiomatizationIff2EmpAxiomatization:
  EmpAxiomatization L Gamma.
Proof.
  constructor.
  + pose proof __sepcon_emp.
    intros.
    eapply solve_iffp_elim1.
    apply H.
  + pose proof __sepcon_emp.
    intros.
    eapply solve_iffp_elim2.
    apply H.
Qed.

End FromEmpIffToEmp.

