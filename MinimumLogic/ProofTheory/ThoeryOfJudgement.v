Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.

Section Axiomatization2Deduction.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD:Derivable L}
        {GammaD1: Derivable1 L}
        {NDL: NormalDeduction L GammaP GammaD1}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2Deduction_minMD: MinimumDeduction L GammaD1.
Proof.
  constructor.
  -intros.
   apply derivable1_provable in H.
   apply derivable1_provable in H0. apply derivable1_provable.
   rewrite H. rewrite H0.
   apply provable_impp_refl.
  -intros.
   apply derivable1_provable. apply axiom1.
  -intros. apply  derivable1_provable. apply derivable1_provable in H.
   pose proof provable_impp_arg_switch x y z.
   pose proof modus_ponens _ _  H0 H. auto.
  Qed.

Lemma Axiomatization2BasicDeduction: BasicDeduction L GammaD1.
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
        {NEL:NormalEquiv L GammaP GammaL}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma Axiomatization2LogicEquiv_minME :MinimumEquiv L GammaL.
Proof.
  constructor.
  intros.
  apply equiv_provable. apply equiv_provable in H. apply equiv_provable in H0.
  destruct H,H0.
  split.
  -rewrite H0. rewrite H1.
   apply provable_impp_refl.
  -rewrite H. rewrite H2.
   apply provable_impp_refl.
  Qed.

Lemma Axiomatization2BasicLogicEquiv: BasicLogicEquiv L GammaL.
Proof.
  constructor.
  -intros.
   apply equiv_provable.
   pose proof provable_impp_refl x.
   split;[auto|auto].
  -intros.
   apply equiv_provable. apply equiv_provable in H.
   destruct H.
   split;[auto|auto].
  -intros. apply equiv_provable. apply equiv_provable in H. 
   apply equiv_provable in H0.
   destruct H,H0.
   pose proof aux_minimun_rule02 _ _ _ H H0.
   pose proof aux_minimun_rule02 _ _ _ H2 H1.
   split;[auto|auto].
  Qed.

End Axiomatization2LogicEquiv.