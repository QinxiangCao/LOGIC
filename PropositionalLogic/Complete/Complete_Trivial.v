Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Trivial.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MinimumLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.

Section Completeness.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {bSC: BasicSequentCalculus L GammaD}
        {mpSC: MinimumSequentCalculus L GammaD}
        {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD}
        {cpSC: ClassicalPropositionalSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {ipAX: IntuitionisticPropositionalLogic L GammaP}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {SM: Semantics L MD}
        {tminSM: TrivialMinimumSemantics L MD SM}
        {tpSM: TrivialPropositionalSemantics L MD SM}
        {kMC: Kmodel -> Prop}.

Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis AL_MC: at_least (maximal consistent) cP.
Hypothesis LIN_CONSI: Lindenbaum_constructable consistent cP.
Hypothesis TRUTH: forall x: expr, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x).
Hypothesis CANON: kMC M.

Lemma general_completeness: strongly_complete GammaD SM (KripkeModelClass _ kMC).
Proof.
  intros.
  assert (forall Phi, consistent Phi -> satisfiable (KripkeModelClass _ kMC) Phi).
  2: {
    clear M CANON rel TRUTH.
    hnf; intros.
    rewrite classical_derivable_spec.
    intro.
    specialize (H _ H1); clear H1.

    destruct H as [_ [[M m CANON] ?]].
    pose proof (fun x0 (HH: Phi x0) => H x0 (Union_introl _ _ _ _ HH)).
    pose proof (H (~~ x) (Union_intror _ _ _ _ (In_singleton _ _))).
    specialize (H0 (KRIPKE: M, m)).
    clear H.

    specialize (H0 ltac:(constructor; auto) H1).
    unfold negp in H2; rewrite sat_impp, sat_falsep in H2.
    auto.
  }
  intros.
  apply LIN_CONSI in H.
  destruct H as [Psi ?].
  destruct (su_bij _ _ rel Psi) as [m ?].
  exists (KRIPKE: M, m).
  split.
  + constructor.
    apply CANON.
  + intros.
    erewrite TRUTH by eauto.
    apply H, H1.
Qed.

End Completeness.
