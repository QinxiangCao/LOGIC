Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.

Local Open Scope logic_base.
Local Open Scope syntax.

Section RewriteClass.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}.

Instance provable_impp_rewrite: RewriteRelation (fun x y => |-- x --> y).
Qed.

Section Provable.

Context {minAX: MinimumAxiomatization L GammaP}.

Instance provable_impp_refl_instance: Reflexive (fun x y => |-- x --> y).
Proof.
  intros.
  hnf; intros.
  apply provable_impp_refl.
Qed.

Instance provable_proper_impp:
  Proper ((fun x y => |-- impp x y) ==> Basics.impl) provable.
Proof.
  intros.
  hnf; intros.
  intro.
  eapply modus_ponens; eauto.
Qed.

Instance impp_proper_impp:
  Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) impp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  eapply modus_ponens; [apply provable_impp_arg_switch |].
  eapply aux_minimun_rule02; [apply H |].
  eapply modus_ponens; [apply provable_impp_arg_switch |].
  apply aux_minimun_rule01, H0.
Qed.

Section Derivable1_provable.

Context {GammaD: Derivable1 L}
        {GammaD1P: Derivable1Provable L GammaP GammaD}.

Instance provable_proper_derivable1:
  Proper (derivable1 ==> Basics.impl) provable.
Proof.
  hnf;intros.
  intro.
  pose proof derivable1_provable x y.
  rewrite H1 in H.
  pose proof modus_ponens _ _ H H0.
  tauto.
Qed.

End Derivable1_provable.

End Provable.

Section Derivable.

Context {GammaD: Derivable L}
        {GammaPD: ProvableDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}.

Instance derivable_proper_impp:
  Proper (eq ==> (fun x y => |-- impp x y) ==> Basics.impl) derivable.
Proof.
  hnf; intros Phi Phi' ?; subst Phi'.
  hnf; intros x1 x2 ?.
  intro.
  apply (deduction_weaken0 Phi) in H.
  exact (deduction_modus_ponens _ _ _ H0 H).
Qed.

Section Derivable1.

Context {GammaD1: Derivable1 L}
        {GammaD1P: Derivable1Provable L GammaP GammaD1}.

Instance derivable_proper_derivable1:
  Proper (eq ==> derivable1 ==> Basics.impl) derivable.
Proof.
  hnf;intros;subst y.
  hnf;intros.
  intro.
  pose proof derivable1_provable x0 y.
  rewrite H1 in H.
  rewrite H in H0.
  tauto.
Qed.

End Derivable1.

End Derivable.

Section Logic_equiv.

Existing Instance derivable_proper_impp.

Context {GammaE: LogicEquiv L}.

Context {GammaEP: EquivProvable L GammaP GammaE}
        {minAX: MinimumAxiomatization L GammaP}.

Instance provable_proper_equiv : Proper (logic_equiv ==> iff) provable.
Proof.
  hnf;intros.
  pose proof logic_equiv_provable x y.
  rewrite H0 in H.
  destruct H.
  split.
  -intros. pose proof modus_ponens _ _ H H2;auto.
  -intros. pose proof modus_ponens _ _ H1 H2;auto.
  Qed.

Context {GammaD:Derivable L}
        {GammaPD: ProvableDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}.

Instance derivable_proper_equiv:
  Proper (eq ==> logic_equiv ==> iff) derivable.
Proof.
  hnf;intros;subst y.
  hnf;intros.
  pose proof logic_equiv_provable x0 y. rewrite H0 in H.
  destruct H.
  split.
  -intros. rewrite H in H2. auto.
  -intros. rewrite H1 in H2. auto.
Qed.

End Logic_equiv.

End RewriteClass.

Existing Instances provable_impp_rewrite
                   provable_impp_refl_instance
                   provable_proper_impp
                   derivable_proper_impp
                   impp_proper_impp.

Module TestInAxiomatization.

Section TestInAxiomatization.

(* Here, "Section" is used to avoid leaking "Existing Instances". *)

Existing Instances Axiomatization2SequentCalculus_GammaPD
                   Axiomatization2SequentCalculus_bSC
                   Axiomatization2SequentCalculus_minSC.

Goal forall {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {GammaDP: DerivableProvable L GammaP GammaD} {minAX: MinimumAxiomatization L GammaP} (Phi: context) y1 y2,
  |-- y1 --> y2 ->
  Phi |--- y1 ->
  Phi |--- y2.
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {GammaDP: DerivableProvable L GammaP GammaD} {minAX: MinimumAxiomatization L GammaP} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  Phi |--- x1 --> y1 ->
  Phi |--- x2 --> y2.
Proof.
  intros.
  rewrite H0 in H1.
  rewrite H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {GammaDP: DerivableProvable L GammaP GammaD} {minAX: MinimumAxiomatization L GammaP} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  |-- (x1 --> y1) --> (x2 --> y2).
Proof.
  intros.
  rewrite <- H0, H.
  apply provable_impp_refl.
Qed.

End TestInAxiomatization.

End TestInAxiomatization.

Module TestInSequentCalculus.

Section TestInSequentCalculus.

(* Here, "Section" is used to avoid leaking "Existing Instances". *)

Existing Instances SequentCalculus2Axiomatization_minAX.

Goal forall {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {GammaPD: ProvableDerivable L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} (Phi: context) y1 y2,
  |-- y1 --> y2 ->
  Phi |--- y1 ->
  Phi |--- y2.
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {GammaPD: ProvableDerivable L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  Phi |--- x1 --> y1 ->
  Phi |--- x2 --> y2.
Proof.
  intros.
  rewrite H0 in H1.
  rewrite H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimumLanguage L} {GammaP: Provable L} {GammaD: Derivable L} {GammaPD: ProvableDerivable L GammaP GammaD} {bSC: BasicSequentCalculus L GammaD} {minSC: MinimumSequentCalculus L GammaD} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  |-- (x1 --> y1) --> (x2 --> y2).
Proof.
  intros.
  rewrite <- H0, H.
  apply provable_impp_refl.
Qed.

End TestInSequentCalculus.

End TestInSequentCalculus.

