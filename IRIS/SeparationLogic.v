Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Syntax_CoreTransit.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.Extensions.ProofTheory.Corable.
Require Import Logic.Extensions.ProofTheory.CoreTransit.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.DownwardsClosure.
Require Logic.SeparationLogic.Semantics.WeakSemanticsMono.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.PropositionalLogic.ShallowEmbedded.MonoPredicatePropositionalLogic.
Require Import Logic.SeparationLogic.ShallowEmbedded.MonoPredicateSeparationLogic.
Require Import Logic.IRIS.Sound.

Module SL.

Section SL.

Context (worlds: Type)
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}
        {CJ: @CoreJoin worlds identity_R J}.

Definition SIW: Type := nat * worlds. (* step indexed worlds *)

Instance SIW_R: Relation SIW := @prod_R _ worlds nat_geR identity_R.

Instance SIW_kiM: KripkeIntuitionisticModel SIW := @prod_kiM _ _ _ _ nat_ge_kiM identity_kiM.

Instance SIW_J: Join SIW := @prod_Join nat _ min_Join J.

Instance SIW_SA: SeparationAlgebra SIW := @prod_SA _ _ _ _ minAlg SA.

Instance SIW_uSA: UpwardsClosedSeparationAlgebra SIW :=
  @prod_uSA _ _ _ _ nat_ge_kiM identity_kiM _ _ minAlg_uSA (@ikiM_uSA worlds identity_R identity_kiM (identity_ikiM _) J).

Instance SIW_dSA: DownwardsClosedSeparationAlgebra SIW :=
  @prod_dSA _ _ _ _ nat_ge_kiM identity_kiM _ _ minAlg_dSA (@ikiM_dSA worlds identity_R identity_kiM (identity_ikiM _) J).

Instance SIW_USA: UnitalSeparationAlgebra SIW :=
  @prod_unitalSA _ _ _ _ nat_ge_kiM identity_kiM _ _ minAlg_unital (USA worlds).

Instance L : Language := MonoPred_L SIW.
Instance nL : NormalLanguage L := MonoPred_nL SIW.
Instance pL : PropositionalLanguage L := MonoPred_pL SIW.
Instance sL : SeparationLanguage L := MonoPred_sL SIW.
Instance s'L : SeparationEmpLanguage L := MonoPred_s'L SIW.
(*
Instance ctrL: CoreTransitSeparationLanguage L.
Proof.
  constructor.
  exact (
*)

Instance G : ProofTheory L := MonoPred_Gamma SIW.
Instance nG : NormalProofTheory L G := MonoPred_nGamma SIW.
Instance mpG : MinimunPropositionalLogic L G := MonoPred_mpGamma SIW.
Instance ipG : IntuitionisticPropositionalLogic L G := MonoPred_ipGamma SIW.
Instance sG : SeparationLogic L G := MonoPred_sGamma SIW.
Instance EmpsG : EmpSeparationLogic L G := MonoPred_EmpsGamma SIW.
(*
Instance CorsG: Corable L G.
*)
End SL.

End SL.