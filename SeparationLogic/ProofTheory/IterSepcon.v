Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class IterSepconAxiomatization_left
        (L: Language)
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {empL: EmpLanguage L}
        {iter_sepcon_L: IterSepconLanguage L}
        (Gamma: Provable L) := {
  iter_sepcon_spec_left1: forall xs, 
    |-- iter_sepcon xs --> fold_left sepcon xs emp;
  iter_sepcon_spec_left2: forall xs, 
    |-- fold_left sepcon xs emp --> iter_sepcon xs;
}.

Section IterSepconRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {empL: EmpLanguage L}
        {iter_sepcon_L: IterSepconLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {andpAX: AndAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {falsepAX: FalseAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {iffpAX: IffAxiomatization L Gamma}
        {truepAX: TrueAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}
        {empAX: EmpAxiomatization L Gamma}
        {iter_sepcon_AXL: IterSepconAxiomatization_left L Gamma}.

Lemma iter_sepcon_spec_left: forall xs, 
  |-- iter_sepcon xs <--> fold_left sepcon xs emp.
Proof.
  intros.
  apply solve_iffp_intros.
  + apply iter_sepcon_spec_left1.
  + apply iter_sepcon_spec_left2.
Qed.

Lemma iter_sepcon_spec_right: forall xs, 
  |-- iter_sepcon xs <--> fold_right sepcon emp xs.
Proof.
  intros.
  rewrite iter_sepcon_spec_left.
  pose proof @assoc_fold_left_fold_right_equiv _ _ _ _ sepcon _ _ emp sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU.
  rewrite H.
  apply provable_iffp_refl.
Qed.

Lemma sepcon_iter_sepcon:
  forall xs ys,
    |-- iter_sepcon xs * iter_sepcon ys <--> iter_sepcon (xs ++ ys).
Proof.
  intros.
  rewrite !iter_sepcon_spec_left.
  apply (@assoc_prodp_fold_left_equiv _ _ _ _ _ _ _ _ sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU).
Qed.

Lemma iter_sepcon_unfold_right_assoc:
  forall xs,
    |-- iter_sepcon xs <-->
        (fix f xs :=
           match xs with
           | nil => emp
           | cons x nil => x
           | cons x xs0 => x * f xs0
           end) xs.
Proof.
  intros.
  rewrite iter_sepcon_spec_left.
  pose proof @assoc_fold_left_fold_right_equiv _ _ _ _ sepcon _ _ emp sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU.
  rewrite H.
  pose proof @fold_right_prodp_unfold _ _ _ _ sepcon _ _ sepcon_Mono emp sepcon_RU.
  apply H0.
Qed.

Lemma iter_sepcon_unfold_left_assoc:
  forall xs,
    |-- iter_sepcon xs <-->
        match xs with
        | nil => emp
        | x :: xs0 => (fix f xs x :=
                         match xs with
                         | nil => x
                         | x0 :: xs0 => f xs0 (x * x0)
                         end) xs0 x
        end.
Proof.
  intros.
  rewrite iter_sepcon_spec_left.
  pose proof @fold_left_prodp_unfold _ _ _ _ sepcon _ _ sepcon_Mono emp sepcon_LU.
  apply H.
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_impp:
  Proper (Forall2 (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) iter_sepcon.
Proof.
  intros.
  hnf; intros.
  rewrite !iter_sepcon_spec_left.
  exact (proper_fold_left' sepcon _ _ H emp emp (provable_impp_refl _)).
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_iffp:
  Proper (Forall2 (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) iter_sepcon.
Proof.
  intros.
  hnf; intros.
  rewrite !iter_sepcon_spec_left.
  exact (proper_fold_left' sepcon _ _ H emp emp (provable_iffp_refl _)).
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_Permutation: Proper (@Permutation expr ==> (fun x y => |-- iffp x y)) iter_sepcon.
Proof.
  intros.
  hnf; intros.
  rewrite !iter_sepcon_spec_left.
  apply (@assoc_fold_left_Permutation _ _ _ _ _ _ _ sepcon_Mono sepcon_Comm sepcon_Assoc); auto.
Qed.

End IterSepconRules.

(*** InstanceDerivations ***)

Class IterSepconDefinition_left
      (L: Language)
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}
      {iter_sepcon_L: IterSepconLanguage L}: Prop := {
  iter_sepcon_def_l: forall xs, 
    iter_sepcon xs = fold_left sepcon xs emp
}.

Class IterSepconDefinition_right
      (L: Language)
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}
      {iter_sepcon_L: IterSepconLanguage L}: Prop := {
  iter_sepcon_def_r: forall xs, 
    iter_sepcon xs = fold_right sepcon emp xs
}.

Definition FoldLeftSepcon2IterSepcon
           {L: Language}
           {sepconL: SepconLanguage L}
           {empL: EmpLanguage L}: IterSepconLanguage L :=
  Build_IterSepconLanguage _ (fun xs => fold_left sepcon xs emp).

Definition FoldRightSepcon2IterSepcon
           {L: Language}
           {sepconL: SepconLanguage L}
           {empL: EmpLanguage L}: IterSepconLanguage L :=
  Build_IterSepconLanguage _ (fun xs => fold_right sepcon emp xs).

Lemma FoldLeftSepcon2IterSepcon_Normal
      {L: Language}
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}:
  @IterSepconDefinition_left L _ _ FoldLeftSepcon2IterSepcon.
Proof. constructor. reflexivity. Qed.

Lemma FoldRightSepcon2IterSepcon_Normal
      {L: Language}
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}:
  @IterSepconDefinition_right L _ _ FoldRightSepcon2IterSepcon.
Proof. constructor. reflexivity. Qed.

Lemma IterSepconFromDefToAX_L2L
      {L: Language}
      {minL: MinimumLanguage L}
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}
      {iter_sepcon_L: IterSepconLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {iter_sepcon_DL: IterSepconDefinition_left L}:
  IterSepconAxiomatization_left L GammaP.
Proof.
  intros.
  constructor.
  + intros.
    rewrite iter_sepcon_def_l.
    apply provable_impp_refl.
  + intros.
    rewrite iter_sepcon_def_l.
    apply provable_impp_refl.
Qed.

Lemma IterSepconFromDefToAX_R2L
      {L: Language}
      {minL: MinimumLanguage L}
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}
      {iter_sepcon_L: IterSepconLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {sepconAX: SepconAxiomatization L GammaP}
      {empAX: EmpAxiomatization L GammaP}
      {iter_sepcon_DR: IterSepconDefinition_right L}:
  IterSepconAxiomatization_left L GammaP.
Proof.
  intros.
  constructor.
  + intros.
    rewrite iter_sepcon_def_r.
    pose proof @assoc_fold_right_fold_left _ _ GammaP _ sepcon emp sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU.
    apply H.
  + intros.
    rewrite iter_sepcon_def_r.
    pose proof @assoc_fold_left_fold_right _ _ GammaP _ sepcon emp sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU.
    apply H.
Qed.

Ltac AddConnective_iter_sepcon :=
  let iter_sepcon_L := fresh "iter_sepcon_L" in
  let iter_sepcon_DL := fresh "iter_sepcon_DL" in
  let iter_sepcon_AXL := fresh "iter_sepcon_AXL" in
  set (iter_sepcon_L := FoldLeftSepcon2IterSepcon);
  set (iter_sepcon_DL := FoldLeftSepcon2IterSepcon_Normal);
  set (iter_sepcon_AXL := IterSepconFromDefToAX_L2L);
  clearbody iter_sepcon_AXL;
  clear iter_sepcon_DL;
  clearbody iter_sepcon_L.

(* TODO: Fix the following three definitions *)
Class NormalIterWand
      (L: Language)
      {wandL: WandLanguage L}
      {iter_wand_L: IterWandLanguage L}: Prop := {
  iter_wand_def: forall xs y,
    iter_wand xs y = fold_right wand y xs
}.

Definition Wand2IterWand
           {L: Language}
           {wandL: WandLanguage L}: IterWandLanguage L :=
  Build_IterWandLanguage L (fun xs y => fold_right wand y xs).

Lemma Wand2IterWand_Normal
      {L: Language}
      {wandL: WandLanguage L}:
  @NormalIterWand L _ Wand2IterWand.
Proof.
  intros.
  constructor.
  intros; reflexivity.
Qed.



           


           
