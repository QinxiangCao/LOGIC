Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import  Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import  Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
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
  clear - minAX andpAX.
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
  clear - minAX iffpAX andpAX.
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
  clear - minAX iffpAX orpAX.
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
  clear - minAX iffpAX.
  AddSequentCalculus.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable.
  apply deduction_iffp_intros; apply deduction_iffp_intros; rewrite !deduction_theorem; rewrite <- provable_derivable.
  +rewrite <- H. rewrite <- H0. apply iffp_elim1.
  +rewrite <- H. rewrite <- H0. apply iffp_elim2.
  +rewrite -> H. rewrite -> H0. apply iffp_elim1.
  +rewrite -> H. rewrite -> H0. apply iffp_elim2.
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

Section RewriteClass3.

Context {L: Language}
        {minL: MinimumLanguage L}
        {falsepL: FalseLanguage L}
        {GammaD1: Derivable1 L}
        {minD: MinimumDeduction L GammaD1}
        {BD: BasicDeduction L GammaD1}.

Section andp.

Context {andpL: AndLanguage L}
        {andpD: AndDeduction L GammaD1}.

Instance andp_proper_derivable1: Proper (derivable1 ==> derivable1 ==> derivable1) andp.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_andp_intros.
  -pose proof derivable1_andp_elim1 x x0.
   pose proof deduction1_trans _ _ _ H1 H. auto.
  -pose proof derivable1_andp_elim2 x x0.
   pose proof deduction1_trans _ _ _ H1 H0. auto.
  Qed.

End andp.

Section orp.

Context {orpL: OrLanguage L}
        {orpD: OrDeduction L GammaD1}.

Instance orp_proper_derivable1: Proper (derivable1 ==> derivable1 ==> derivable1) orp.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_orp_elim.
  -pose proof derivable1_orp_intros1 y y0.
   pose proof deduction1_trans _ _ _ H H1;auto.
  -pose proof derivable1_orp_intros2 y y0.
   pose proof deduction1_trans _ _ _ H0 H1;auto.
Qed.

End orp.

Section negp.

Context {negpL: NegLanguage L}
        {inegpD: IntuitionisticNegDeduction L GammaD1}.

Instance negp_proper_derivable1: Proper (derivable1 --> derivable1) negp.
Proof.
  hnf;intros.
  unfold Basics.flip in H.
  pose proof derivable1_negp_unfold x.
  pose proof derivable1_negp_fold y.
  pose proof deduction1_refl FF.
  pose proof deduction1_intros _ _ _ _ H H2.
  pose proof deduction1_trans _ _ _ H0 H3.
  pose proof deduction1_trans _ _ _ H4 H1.
  auto.
  Qed.

End negp.

End RewriteClass3.

Section RewriteClass4.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaE: LogicEquiv L}
        {minE: MinimumEquiv L GammaE}
        {BE: BasicLogicEquiv L GammaE}.

Section andp.

Context {andpL: AndLanguage L}
        {andpE: EquivAndp L GammaE}.

Instance andp_proper_equiv: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) andp.
Proof.
  hnf;intros.
  hnf;intros.
  apply equiv_andp_congr;[auto|auto].
  Qed.

End andp.

Section orp.

Context {orpL: OrLanguage L}
        {orpE: EquivOrp L GammaE}.

Instance orp_proper_equiv: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) orp.
Proof.
  hnf;intros.
  hnf;intros.
  apply equiv_orp_congr;[auto|auto].
  Qed.

End orp.

Section negp.

Context {negpL: NegLanguage L}
        {negpE: EquivNegp L GammaE}.

Instance negp_proper_equiv: Proper (logic_equiv  ==> logic_equiv ) negp.
Proof.
  hnf;intros.
  apply equiv_negp_intros;auto.
  Qed.

End negp.

Section iffp.

Context {iffpL: IffLanguage L}
        {andpL: AndLanguage L}
        {andpE: EquivAndp L GammaE}
        {iffE: EquivIffp L GammaE}.

Instance iffp_proper_equiv: Proper (logic_equiv  ==> logic_equiv ==> logic_equiv) iffp.
Proof.
  hnf;intros.
  hnf;intros.
  pose proof equiv_iffp_intros x x0.
  pose proof equiv_iffp_intros y y0.
  apply equiv_trans with ((x --> x0) && (x0 --> x)).
  apply equiv_symm;auto.
  apply equiv_symm.
  apply equiv_trans with ((y --> y0) && (y0 --> y)).
  apply equiv_symm;auto.
  apply equiv_andp_congr.
  -apply equiv_impp.
   apply equiv_symm;auto.
   apply equiv_symm;auto.
  -apply equiv_impp.
   apply equiv_symm;auto.
   apply equiv_symm;auto.
  Qed.

End iffp.

End RewriteClass4.

Existing Instances andp_proper_impp orp_proper_impp negp_proper_impp
                   provable_iffp_rewrite provable_iffp_equiv
                   provable_proper_iffp derivable_proper_iffp
                   impp_proper_iffp andp_proper_iffp orp_proper_iffp iffp_proper_iffp negp_proper_iffp.

