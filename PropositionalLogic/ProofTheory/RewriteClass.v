Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section RewriteClass1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}.

Instance andp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) andp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable.
  rewrite <- !deduction_theorem.
  apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H.
  apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H0.
  pose proof derivable_assum1 empty_context (x1 && y1).
  pose proof deduction_andp_elim1 _ _ _ H1.
  pose proof deduction_andp_elim2 _ _ _ H1.
  pose proof deduction_modus_ponens _ _ _ H2 H.
  pose proof deduction_modus_ponens _ _ _ H3 H0.
  apply deduction_andp_intros; auto.
Qed.

Instance orp_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) orp.
Proof.
  clear - minAX orpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H, H0 |- *.
  apply deduction_orp_elim'.
  + eapply deduction_impp_trans; [exact H |].
    apply derivable_orp_intros1.
  + eapply deduction_impp_trans; [exact H0 |].
    apply derivable_orp_intros2.
Qed.

Instance negp_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y)) negp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  pose proof negp_unfold x1. rewrite H0.
  pose proof negp_fold x2. rewrite <- H1.
  apply impp_proper_impp; auto.
  apply provable_impp_refl.
Qed.

Instance provable_iffp_rewrite: RewriteRelation (fun x y => |-- x <--> y).
Qed.

Instance provable_iffp_equiv: Equivalence (fun x y => |-- x <--> y).
Proof.
  clear - minAX iffpAX.
  AddSequentCalculus.
  constructor.
  + hnf; intros.
    rewrite provable_derivable.
    apply deduction_iffp_intros; apply deduction_theorem; apply derivable_impp_refl.
  + hnf; intros.
    rewrite provable_derivable in H |- *.
    pose proof deduction_iffp_elim1 _ _ _ H.
    pose proof deduction_iffp_elim2 _ _ _ H.
    apply deduction_iffp_intros; auto.
  + hnf; intros.
    rewrite provable_derivable in H, H0 |- *.
    pose proof deduction_iffp_elim1 _ _ _ H; apply deduction_theorem in H1.
    pose proof deduction_iffp_elim2 _ _ _ H; apply deduction_theorem in H2.
    pose proof deduction_iffp_elim1 _ _ _ H0; apply deduction_theorem in H3.
    pose proof deduction_iffp_elim2 _ _ _ H0; apply deduction_theorem in H4.
    apply deduction_iffp_intros; apply deduction_theorem.
    - apply (deduction_impp_trans _ _ _ _ H1 H3).
    - apply (deduction_impp_trans _ _ _ _ H4 H2).
Qed.

Instance provable_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> iff) provable.
Proof.
  clear - minAX iffpAX.
  AddSequentCalculus.
  intros.
  hnf; intros.
  rewrite provable_derivable in H.
  rewrite provable_derivable.
  rewrite provable_derivable.
  pose proof deduction_iffp_elim1 _ _ _ H; apply deduction_theorem in H0.
  pose proof deduction_iffp_elim2 _ _ _ H; apply deduction_theorem in H1.
  split; intro;
  eapply deduction_modus_ponens; eauto.
Qed.

Instance impp_proper_iffp : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) impp.
Proof.
  clear - minAX iffpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H.
  rewrite provable_derivable in H0.
  rewrite provable_derivable.
  pose proof deduction_iffp_elim1 _ _ _ H; apply deduction_theorem in H1.
  pose proof deduction_iffp_elim2 _ _ _ H; apply deduction_theorem in H2.
  pose proof deduction_iffp_elim1 _ _ _ H0; apply deduction_theorem in H3.
  pose proof deduction_iffp_elim2 _ _ _ H0; apply deduction_theorem in H4.
  rewrite <- provable_derivable in H1.
  rewrite <- provable_derivable in H2.
  rewrite <- provable_derivable in H3.
  rewrite <- provable_derivable in H4.
  apply deduction_iffp_intros; apply deduction_theorem; rewrite <- provable_derivable.
  + apply impp_proper_impp; auto.
  + apply impp_proper_impp; auto.
Qed.

Instance andp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) andp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H.
  rewrite provable_derivable in H0.
  rewrite provable_derivable.
  pose proof deduction_iffp_elim1 _ _ _ H; apply deduction_theorem in H1.
  pose proof deduction_iffp_elim2 _ _ _ H; apply deduction_theorem in H2.
  pose proof deduction_iffp_elim1 _ _ _ H0; apply deduction_theorem in H3.
  pose proof deduction_iffp_elim2 _ _ _ H0; apply deduction_theorem in H4.
  rewrite <- provable_derivable in H1.
  rewrite <- provable_derivable in H2.
  rewrite <- provable_derivable in H3.
  rewrite <- provable_derivable in H4.
  apply deduction_iffp_intros; apply deduction_theorem; rewrite <- provable_derivable.
  + apply andp_proper_impp; auto.
  + apply andp_proper_impp; auto.
Qed.

Instance orp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) orp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H.
  rewrite provable_derivable in H0.
  rewrite provable_derivable.
  pose proof deduction_iffp_elim1 _ _ _ H; apply deduction_theorem in H1.
  pose proof deduction_iffp_elim2 _ _ _ H; apply deduction_theorem in H2.
  pose proof deduction_iffp_elim1 _ _ _ H0; apply deduction_theorem in H3.
  pose proof deduction_iffp_elim2 _ _ _ H0; apply deduction_theorem in H4.
  rewrite <- provable_derivable in H1.
  rewrite <- provable_derivable in H2.
  rewrite <- provable_derivable in H3.
  rewrite <- provable_derivable in H4.
  apply deduction_iffp_intros; apply deduction_theorem; rewrite <- provable_derivable.
  + apply orp_proper_impp; auto.
  + apply orp_proper_impp; auto.
Qed.

Instance iffp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) iffp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  pose proof iffp_fold_unfold (x1 <--> y1) (x2 <--> y2). rewrite H1.
  pose proof iffp_fold_unfold x1 y1. rewrite H2.
  pose proof iffp_fold_unfold x2 y2. rewrite H3.
  rewrite H, H0.
  rewrite provable_derivable. apply deduction_andp_intros; rewrite <- provable_derivable; apply provable_impp_refl.
Qed.

Instance negp_proper_iffp: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) negp.
Proof.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  pose proof negp_fold_unfold x1. rewrite H0.
  pose proof negp_fold_unfold x2. rewrite H1.
  apply impp_proper_iffp; auto.
  apply provable_iffp_refl.
Qed.

End RewriteClass1.

Section RewriteClass2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {SC: NormalSequentCalculus L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}.

Instance derivable_proper_iffp : Proper (eq ==> (fun x y => |-- x <--> y) ==> iff) derivable.
Proof.
  hnf; intros Phi Phi' ?; subst Phi'.
  hnf; intros x1 x2 ?.
  apply (deduction_weaken0 Phi) in H.
  pose proof deduction_iffp_elim1 _ _ _ H; rewrite deduction_theorem in H0.
  pose proof deduction_iffp_elim2 _ _ _ H; rewrite deduction_theorem in H1.
  split; intro;
  eapply deduction_modus_ponens; eauto.
Qed.

End RewriteClass2.

Existing Instances andp_proper_impp orp_proper_impp negp_proper_impp
                   provable_iffp_rewrite provable_iffp_equiv
                   provable_proper_iffp derivable_proper_iffp
                   impp_proper_iffp andp_proper_iffp orp_proper_iffp iffp_proper_iffp negp_proper_iffp.
