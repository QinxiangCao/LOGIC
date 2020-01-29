Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.

Section Axiomatization2Deduction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD:Derivable L}
        {GammaD1: Derivable1 L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2Deduction_bD: BasicDeduction L GammaD1.
Proof.
  constructor.
  -intros. 
   apply derivable1_provable. apply provable_impp_refl.
  -intros.
   apply derivable1_provable. apply derivable1_provable in H. 
   apply derivable1_provable in H0.
   pose proof aux_minimun_rule02 _ _ _ H H0. auto.
Qed.

End Axiomatization2Deduction.

Section Axiomatization2LogicEquiv.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaL: LogicEquiv L}
        {GammaEP: EquivProvable L GammaP GammaL}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2Equiv_bE: BasicLogicEquiv L GammaL.
Proof.
  constructor.
  -intros.
   apply logic_equiv_provable.
   pose proof provable_impp_refl x.
   split;[auto|auto].
  -intros.
   apply logic_equiv_provable. apply logic_equiv_provable in H.
   destruct H.
   split;[auto|auto].
  -intros. apply logic_equiv_provable. apply logic_equiv_provable in H. 
   apply logic_equiv_provable in H0.
   destruct H,H0.
   pose proof aux_minimun_rule02 _ _ _ H H0.
   pose proof aux_minimun_rule02 _ _ _ H2 H1.
   split;[auto|auto].
  Qed.

End Axiomatization2LogicEquiv.

Section Derivable1_Provable.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}.

Section provable2derivable1.

Context {GammaD1P: Derivable1Provable L GammaP GammaD1}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2Deduction_GammaPD1 : ProvableDerivable1 L GammaP GammaD1.
Proof.
  constructor.
  intros. split.
  -intros.
   apply derivable1_provable.
   apply aux_minimun_rule00. auto.
  -intros.
   apply derivable1_provable in H.
   pose proof provable_impp_refl x.
   pose proof modus_ponens _ _ H H0. auto.
  Qed.

End provable2derivable1.

End Derivable1_Provable.
