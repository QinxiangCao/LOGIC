Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Logic.PropositionalLogic.DeepEmbeddedInstance.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbeddedInstance.ClassicalLogic.
Require Logic.PropositionalLogic.DeepEmbeddedInstance.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section Completeness.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance G: ProofTheory L := ClassicalLogic.G Var.
Instance nG: NormalProofTheory L G := ClassicalLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := ClassicalLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := ClassicalLogic.ipG Var.
Instance cpG: ClassicalPropositionalLogic L G := ClassicalLogic.cpG Var.
Instance MD: Model := TrivialSemantics.MD Var.
Instance SM: Semantics L MD := TrivialSemantics.SM Var.

Definition MCS: Type := sig maximal_consistent.

Definition canonical_model (Phi: MCS): model :=
  fun p => (proj1_sig Phi (PropositionalLanguage.varp p)).

Lemma Lindenbaum_lemma:
  forall Phi,
    consistent Phi ->
    exists Psi,
      Included _ Phi Psi /\ maximal_consistent Psi.
Proof.
  intros.
  assert (Countable expr) by (apply PropositionalLanguage.formula_countable; auto).
  set (step :=
          fun n Phi x =>
             Phi x \/
            (X x n /\ consistent (Union _ Phi (Singleton _ x)))).
  exists (LindenbaumConstruction step Phi).
  split; [| rewrite maximal_consistent_spec; split].
  + apply (Lindenbaum_spec_included _ _ 0).
  + rewrite consistent_spec.
    apply (Lindenbaum_spec_pos _ _
            (fun xs => |-- multi_imp xs FF)
            (fun Phi => Phi |-- FF)).
    - intros; apply derivable_provable.
    - intros ? ? ? ?; left; auto.
    - rewrite consistent_spec in H; apply H.
    - intros.
      destruct (Classical_Prop.classic (exists x, X x n /\ consistent (Union _ S (Singleton _ x)))) as [[x [? ?]] |].
      * rewrite consistent_spec in H2.
        intro; apply H2; clear H2.
        eapply deduction_weaken; [| exact H3].
        hnf; intros ? [? | [? ?]]; [left; auto |].
        pose proof in_inj _ _ X _ _ _ H1 H2.
        subst; right; constructor.
      * intro; apply H0; clear H0.
        eapply deduction_weaken; [| exact H2].
        hnf; intros ? [? | [? ?]]; [auto |].
        exfalso; apply H1; clear H1.
        exists x; auto.
  + intros.
    destruct (im_inj _ _ X x) as [n ?].
    apply (Lindenbaum_spec_neg _ _ _ (S n)).
    simpl.
    unfold step at 1.
    rewrite consistent_spec in H0 |- *.
    right; split; auto.
    intro; apply H0; clear H0.
    rewrite deduction_theorem in H2 |- *.
    eapply deduction_weaken; [| exact H2].
    apply (Lindenbaum_spec_included _ _ n); auto.
Qed.

Lemma truth_lemma: forall (Phi: MCS) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  revert x.
  pose proof MCS_element_derivable (proj1_sig Phi) (proj2_sig Phi).
  intros.
  induction x; try solve [inversion H0].
  + pose proof MCS_andp_iff (proj1_sig Phi) (proj2_sig Phi) x1 x2.
    simpl in *.
    unfold Semantics.andp.
    tauto.
  + pose proof MCS_orp_iff (proj1_sig Phi) (proj2_sig Phi) x1 x2.
    simpl in *.
    unfold Semantics.orp.
    tauto.
  + pose proof MCS_impp_iff (proj1_sig Phi) (proj2_sig Phi) x1 x2.
    simpl in *.
    unfold Semantics.impp.
    tauto.
  + simpl.
    rewrite H.
    split; [intros [] |].
    pose proof proj2_sig Phi.
    destruct H0.
    rewrite consistent_spec in H0; auto.
  + simpl.
    unfold canonical_model.
    tauto.
Qed.

Theorem complete_classical_trivial: strongly_complete (ClassicalLogic.G Var) (TrivialSemantics.SM Var) (AllModel _).
Proof.
  assert (forall Phi, consistent Phi -> satisfiable (AllModel _) Phi).
  + intros.
    assert (exists Psi, Included _ Phi Psi /\ maximal_consistent Psi)
      by (apply Lindenbaum_lemma; auto).
    destruct H0 as [Psi [? ?]].
    exists (canonical_model (exist _ Psi H1)).
    split; [hnf; auto |].
    intros.
    apply truth_lemma.
    simpl.
    apply H0; auto.
  + hnf; intros.
    rewrite classical_derivable_spec.
    intro.
    specialize (H _ H1); clear H1.

    destruct H as [m [_ ?]].
    pose proof (fun x0 (HH: Phi x0) => H x0 (Union_introl _ _ _ _ HH)).
    pose proof (H (~~ x) (Union_intror _ _ _ _ (In_singleton _ _))).
    specialize (H0 m).
    clear H.

    specialize (H0 I H1).
    exact (H2 H0).
Qed.

End Completeness.
