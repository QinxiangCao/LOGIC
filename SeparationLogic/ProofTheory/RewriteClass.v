Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section RewriteClass1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}.

Instance sepcon_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply sepcon_mono; auto.
Qed.

Instance wand_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  apply wand_mono; auto.
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

Instance sepcon_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply solve_iffp_intros.
  + apply sepcon_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
  + apply sepcon_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
Qed.

Instance wand_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply solve_iffp_intros.
  + apply wand_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
  + apply wand_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
Qed.

End RewriteClass1.

Section RewriteClass2.

Import Derivable1.
Local Open Scope Derivable1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD: Derivable1 L}
        {sepconD: SepconDeduction L GammaD}.

Instance sepcon_proper_derivable1: Proper (derivable1 ==> derivable1 ==> derivable1) sepcon.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_sepcon_mono;auto.
  Qed.

Context {wandL: WandLanguage L}
        {wandD: WandDeduction L GammaD}
        {bD: BasicDeduction L GammaD}.

Instance wand_proper_derivable1: Proper (derivable1 --> derivable1 ==> derivable1) wand.
Proof.
  hnf;intros.
  hnf;intros.
  apply derivable1_wand_mono;auto.
  Qed.

End RewriteClass2.

Section RewriteClass3.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {GammaD1: Derivable1 L}
        {GammaE: LogicEquiv L}
        {GammaED1: EquivDerivable1 L GammaD1 GammaE}
        {sepconD: SepconDeduction L GammaD1}.

Instance sepcon_proper_logic_equiv: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon.
Proof.
  hnf;intros.
  hnf;intros.
  apply logic_equiv_derivable1 in H;
  apply logic_equiv_derivable1 in H0.
  apply logic_equiv_derivable1; split;
  apply derivable1_sepcon_mono; tauto.
  Qed.

Context {wandL: WandLanguage L}
        {wandD: WandDeduction L GammaD1}
        {bD: BasicDeduction L GammaD1}.

Instance wand_proper_logic_equiv: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) wand.
Proof.
  hnf;intros.
  hnf;intros.
  apply logic_equiv_derivable1 in H;
  apply logic_equiv_derivable1 in H0.
  apply logic_equiv_derivable1; split;
  apply derivable1_wand_mono; tauto.
  Qed.
End RewriteClass3.

Existing Instances sepcon_proper_impp
                   wand_proper_impp
                   sepcon_proper_iffp
                   wand_proper_iffp
                   sepcon_proper_derivable1
                   wand_proper_derivable1
                   sepcon_proper_logic_equiv
                   wand_proper_logic_equiv.

