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
  -intros. apply derivable1_provable.
   apply axiom2.
  -intros. apply derivable1_provable.
   pose proof aux_minimun_theorem02 (x --> x) y.
   pose proof provable_impp_refl x.
   pose proof modus_ponens _ _ H H0.
   auto.
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

Section Derivable1Rules.

Import Derivable1.
Local Open Scope Derivable1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}.

Lemma derivable1_base:forall x y,
  (x --> x) |-- (y --> y).
Proof.
  intros.
  apply deduction_exchange.
  apply deduction1_axiom1.
  Qed.

End Derivable1Rules.

Section Derivable1ToProvable.

Existing Instances derivable1_refl
                   derivable1_proper_derivable1
                   impp_proper_derivable1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD1: Derivable1 L}
        {D2P: Provable_Derivable1 L GammaP GammaD1}
        {minD: MinimumDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Lemma Derivable1ToAxiomatization : MinimumAxiomatization L GammaP.
Proof.
  constructor.
  -intros.
   apply provable_derivable1.
   apply provable_derivable1 in H.
   apply provable_derivable1 in H0.
   rewrite <- H0 in H at 3.
   pose proof derivable1_base y x.
   pose proof deduction_exchange _ _ _ H;clear H.
   pose proof deduction_mid (x --> y) y.
   pose proof deduction1_trans _ _ _ H2 H.
   pose proof deduction1_trans _ _ _ H1 H3.
   auto.
  -intros.
   apply provable_derivable1.
   apply deduction_exchange.
   pose proof deduction1_axiom1 x y.
   pose proof deduction1_axiom1 (y --> x) ((x --> y --> x) --> x --> y --> x).
   pose proof deduction1_trans _ _ _ H H0.
   auto.
  -intros.
   apply provable_derivable1.
   apply deduction_exchange.
   pose proof deduction_md x y z.
   pose proof deduction1_axiom1 ((x --> y) --> (x --> z)) (((x --> y --> z) --> (x --> y) --> x --> z) --> (x --> y --> z) --> (x --> y) --> x --> z).
   pose proof deduction1_trans _ _ _ H H0.
   auto.
   Qed.

End Derivable1ToProvable.

Section Derivable1_Provable.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable1 L}.

Section provable2derivable1.

Context {ND: NormalDeduction L GammaP GammaD}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma ND2PD : Provable_Derivable1 L GammaP GammaD.
Proof.
  constructor.
  intros. split.
  -intros.
   apply derivable1_provable in H.
   pose proof provable_impp_refl x.
   pose proof modus_ponens _ _ H H0. auto.
  -intros.
   apply derivable1_provable.
   apply aux_minimun_rule00. auto.
  Qed.

End provable2derivable1.

Section derivable12provable.

Context {PD:Provable_Derivable1 L GammaP GammaD}
        {MD: MinimumDeduction L GammaD}
        {BD: BasicDeduction L GammaD}.

Import Derivable1.
Local Open Scope Derivable1.

Lemma PD2ND: NormalDeduction L GammaP GammaD.
Proof.
  constructor.
  intros. split.
  -intros.
   apply provable_derivable1.
   apply deduction_exchange.
   pose proof deduction1_axiom1 y ((x --> y) --> x --> y).
   pose proof deduction1_trans _ _ _ H H0. auto.
  -intros.
   apply provable_derivable1 in H.
   apply deduction_exchange in H.
   pose proof deduction_mid (x --> y) y.
   pose proof deduction1_trans _ _ _ H H0. auto.
  Qed.

End derivable12provable.

End Derivable1_Provable.