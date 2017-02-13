Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
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

(* flush buffer relation on single buffer *)
Instance buff_R: Relation buff := fun b1 b2 => exists l, proj1_sig b1 = l ++ proj1_sig b2.

(* flush buffer relation is preorder *)
Instance po_buff_R: PreOrder (@Krelation _ buff_R).
Proof.
  constructor; hnf; intros.
  + exists nil.
    auto.
  + destruct H as [l1 ?], H0 as [l2 ?].
    exists (l1 ++ l2).
    rewrite H, H0.
    apply app_assoc.
Qed.

(* flush buffer relation (on single buffer) is non-branching *)
Instance buff_nkiM: NoBranchKripkeIntuitionisticModel buff.
Proof.
  constructor; hnf; intros.
  destruct H as [l1 ?], H0 as [l2 ?].
  rewrite H in H0; clear n H.
  revert l2 H0; induction l1; intros.
  + left.
    exists l2; auto.
  + destruct l2.
    - right.
      exists (a :: l1); symmetry; auto.
    - inversion H0; subst v.
      apply IHl1 in H2; auto.
Qed.

Instance buff_J: Join buff := equiv_Join.

Instance buff_SA: SeparationAlgebra buff := equiv_SA.

(* flush buffer relation on a disk *)
Instance disk_R: Relation disk := @pointwise_relation adr (option buff) (option00_relation buff_R).

Instance po_disk_R: PreOrder (@Krelation _ disk_R) :=
  @pointwise_preorder adr (option buff) (option00_relation buff_R) (option00_preorder buff_R).

(* flush buffer relation (on a disk) has all branches joining *)
Instance disk_bkiM: BranchJoinKripkeIntuitionisticModel disk :=
  @fun_BranchJoinKripkeIntuitionisticModel _ _ _
    (@option00_BranchJoinKripkeIntuitionisticModel _ _
      (@NoBranch2BranchJoin _ _ _ buff_nkiM)).

(* the join relation on disk *)
Definition disk_raw_J: Join disk := @fun_Join adr (option buff) (option_Join buff).

(* The following shows that the join relation is upwards closed separation algebra *)
Definition disk_raw_SA: @SeparationAlgebra disk disk_raw_J :=
  @fun_SA adr (option buff) (option_Join buff) (option_SA buff).

Definition disk_raw_uSA: @UpwardsClosedSeparationAlgebra disk disk_R disk_raw_J :=
  @fun_uSA adr (option buff) (option00_relation buff_R)
    (option_Join buff) (option_disj_uSA buff (identity_uSA)).

Definition disk_raw_USA': @UnitalSeparationAlgebra' disk disk_R disk_raw_J :=
  @fun_unitSA' adr (option buff) (option00_relation buff_R)
    (option_Join buff) (option_disj_USA' buff).

(* take the closure on the join relation *)
Instance disk_cl_J: Join disk := @DownwardsClosure_J disk disk_R disk_raw_J.

Instance disk_cl_SA: SeparationAlgebra disk :=
  @DownwardsClosure_SA disk disk_R po_disk_R disk_raw_J disk_raw_SA disk_raw_uSA.

Instance disk_cl_uSA: UpwardsClosedSeparationAlgebra disk :=
  @DownwardsClosure_UpwardsClosed disk disk_R disk_raw_J disk_raw_uSA.

Instance disk_cl_dSA: DownwardsClosedSeparationAlgebra disk :=
  @DownwardsClosure_DownwardsClosed disk disk_R po_disk_R disk_raw_J.

Instance disk_cl_USA: UnitalSeparationAlgebra disk :=
  @DownwardsClosure_USA disk disk_R po_disk_R disk_raw_J disk_raw_USA'.

(* the shallow embedded separation language *)
Instance L : Language := MonoPred_L disk.
Instance nL : NormalLanguage L := MonoPred_nL disk.
Instance pL : PropositionalLanguage L := MonoPred_pL disk.
Instance sL : SeparationLanguage L := MonoPred_sL disk.
Instance s'L : SeparationEmpLanguage L := MonoPred_s'L disk.

(* the shallow embedded separation logic *)
Instance G : ProofTheory L := MonoPred_Gamma disk.
Instance nG : NormalProofTheory L G := MonoPred_nGamma disk.
Instance mpG : MinimunPropositionalLogic L G := MonoPred_mpGamma disk.
Instance ipG : IntuitionisticPropositionalLogic L G := MonoPred_ipGamma disk.
Instance dmpG : DeMorganPropositionalLogic L G := MonoPred_dmpGamma disk.
Instance sG : SeparationLogic L G := MonoPred_sGamma disk.
Instance EmpsG : EmpSeparationLogic L G := MonoPred_EmpsGamma disk.

End SL.

End SL.


