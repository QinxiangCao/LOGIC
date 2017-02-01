Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.DownwardsClosure.
Require Logic.SeparationLogic.Semantics.WeakSemanticsMono.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.PropositionalLogic.ShallowEmbedded.MonoPredicatePropositionalLogic.
Require Import Logic.SeparationLogic.ShallowEmbedded.MonoPredicateSeparationLogic.

Module SL.

Section SL.

Variable adr: Type.
Variable value: Type.

Definition buff: Type := sig (fun l: list value => not_nil l).

Definition disk: Type := adr -> option buff.

Instance buff_R: Relation buff := fun b1 b2 => exists l, proj1_sig b1 = l ++ proj1_sig b2.

Instance buff_kiM: KripkeIntuitionisticModel buff.
Proof.
  hnf; constructor; hnf.
  + intros.
    exists nil.
    auto.
  + intros.
    destruct H as [l1 ?], H0 as [l2 ?].
    exists (l1 ++ l2).
    rewrite H, H0.
    apply app_assoc.
Qed.

Instance buff_J: Join buff := equiv_Join.

Instance buff_SA: SeparationAlgebra buff := equiv_SA.

Instance disk_R: Relation disk := @fun_R adr (option buff) (option_disj_R buff).

Instance disk_kiM: KripkeIntuitionisticModel disk :=
  @fun_kiM adr (option buff) (option_disj_R buff) (option_disj_kiM buff).

Definition disk_raw_J: Join disk := @fun_Join adr (option buff) (option_Join buff).

Definition disk_raw_SA: @SeparationAlgebra disk disk_raw_J :=
  @fun_SA adr (option buff) (option_Join buff) (option_SA buff).

Definition disk_raw_uSA: @UpwardsClosedSeparationAlgebra disk disk_R disk_raw_J :=
  @fun_uSA adr (option buff) (option_disj_R buff) (option_disj_kiM buff)
    (option_Join buff) (option_disj_uSA buff (identity_uSA)).

Instance disk_cl_J: Join disk := @DownwardsClosure_J disk disk_R disk_raw_J.

Instance disk_cl_SA: SeparationAlgebra disk :=
  @DownwardsClosure_SA disk disk_R disk_kiM disk_raw_J disk_raw_SA disk_raw_uSA.

Instance disk_cl_uSA: UpwardsClosedSeparationAlgebra disk :=
  @DownwardsClosure_UpwardsClosed disk disk_R disk_raw_J disk_raw_uSA.

Instance disk_cl_dSA: DownwardsClosedSeparationAlgebra disk :=
  @DownwardsClosure_DownwardsClosed disk disk_R disk_kiM disk_raw_J.

End SL.

End SL.


