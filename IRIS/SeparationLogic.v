Require Import Logic.lib.List_Func_ext.
Require Import Logic.lib.Bisimulation.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Syntax_CoreTransit.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.Extensions.ProofTheory.Stable.
Require Import Logic.Extensions.ProofTheory.ModalSeparation.
Require Import Logic.Extensions.ProofTheory.Corable.
Require Import Logic.Extensions.ProofTheory.CoreTransit.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.SeparationLogic.Model.DownwardsClosure.
Require Logic.SeparationLogic.Semantics.WeakSemanticsMono.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.PropositionalLogic.ShallowEmbedded.MonoPredicatePropositionalLogic.
Require Import Logic.ModalLogic.ShallowEmbedded.MonoPredicateModalLogic.
Require Import Logic.SeparationLogic.ShallowEmbedded.MonoPredicateSeparationLogic.
Require Import Logic.Extensions.ShallowEmbedded.MonoPredicateStable.

Require Import Logic.Extensions.Semantics.SemanticStable.
Require Import Logic.IRIS.Sound.

Module SL.

Section SL.

Context (worlds: Type)
        {J: Join worlds}
        {SA: SeparationAlgebra worlds}
        {CJ: @CoreJoin worlds eq J}.

Definition SIW: Type := nat * worlds. (* step indexed worlds *)

Instance SIW_R: KI.Relation SIW := @RelProd _ worlds nat_geR eq.

Instance po_SIW_R: PreOrder (@KI.Krelation _ SIW_R) := @RelProd_Preorder _ _ _ _ po_nat_geR (eq_preorder _).

Instance SIW_J: Join SIW := @prod_Join nat _ min_Join J.

Instance SIW_SA: SeparationAlgebra SIW := @prod_SA _ _ _ _ minAlg SA.

Instance SIW_uSA: UpwardsClosedSeparationAlgebra SIW :=
  @prod_uSA _ _ _ _ _ _ minAlg_uSA (@ikiM_uSA worlds eq (eq_preorder _) eq_ikiM J).

Instance SIW_dSA: DownwardsClosedSeparationAlgebra SIW :=
  @prod_dSA _ _ _ _ _ _ minAlg_dSA (@ikiM_dSA worlds eq (eq_preorder _) eq_ikiM J).

Instance SIW_USA: UnitalSeparationAlgebra SIW :=
  @prod_unitalSA _ _ _ _ _ _ minAlg_unital (USA worlds).

Instance SIW_Cor: SS.Relation SIW := @RelProd _ worlds eq full_relation.

Instance SIW_Ctr: KM.Relation SIW := @RelProd _ worlds eq (fun m => eq (@core _ _ _ CJ m)).

Instance SIW_R_bis: Bisimulation (@SS.Krelation _ SIW_Cor) (@KI.Krelation _ SIW_R) :=
  @RelProd_Bisimulation _ _ _ _ _ _ (eq_bis _) (@full_bis _ _ (@Functional_Serial _ _ (function_Functional ))).

Instance SIW_ukmM: UpwardsClosedOrderedKripkeModel SIW :=
  @prod_ukmM _ _ _ _ _ _ (eq2_ukmM _) (eq1_ukmM _).

Instance pf_SIW_Ctr: @PartialFunctional SIW (@KM.Krelation SIW SIW_Ctr) :=
  @RelProd_PartialFunctional _ _ _ _ (@Functional_PartialFunctional _ _ (@function_Functional _ id)) (@Functional_PartialFunctional _ _ (function_Functional)).

Instance SIW_CJ: @CoreJoin SIW SIW_R SIW_J :=
  @prod_CJ _ _ _ _ _ _ geR_min_CJ CJ.

Instance L : Language := MonoPred_L SIW.
Instance nL : NormalLanguage L := MonoPred_nL SIW.
Instance pL : PropositionalLanguage L := MonoPred_pL SIW.
Instance sL : SeparationLanguage L := MonoPred_sL SIW.
Instance s'L : SeparationEmpLanguage L := MonoPred_s'L SIW.
Definition _mL : ModalLanguage L := MonoPred_mL SIW.
Instance ctrL: CoreTransitSeparationLanguage L := Build_CoreTransitSeparationLanguage _ _ (@boxp _ _mL).
Existing Instance ct_mL.

Instance G : ProofTheory L := MonoPred_Gamma SIW.
Instance nG : NormalProofTheory L G := MonoPred_nGamma SIW.
Instance mpG : MinimunPropositionalLogic L G := MonoPred_mpGamma SIW.
Instance ipG : IntuitionisticPropositionalLogic L G := MonoPred_ipGamma SIW.
Instance sG : SeparationLogic L G := MonoPred_sGamma SIW.
Instance EmpsG : EmpSeparationLogic L G := MonoPred_EmpsGamma SIW.

Instance _KmG : SystemK L G := MonoPred_KmGamma SIW.

Instance CorsG: Corable L G.
  refine (Build_Corable _ _ _ _ _ _ _ _ _ (MonoPred_stable SIW) (MonoPred_pstable SIW) (MonoPred_sstable SIW) (MonoPred_SAS SIW)).
  + exact SIW_R_bis.
  + admit. (* SeparationAlgebraBisStable *)
  + admit. (* SeparationAlgebraAbsorbStable *)
Admitted.

Instance CtrsG: CoreTransitSeparationLogic L G.
  apply (Build_CoreTransitSeparationLogic L _ _ _ _ _ _ _ ipG sG CorsG _KmG (MonoPred_pmGamma SIW)).
  + constructor.
    intros x y.
(*
    exact (@sound_sepcon_boxp L nL pL _ _ (Build_Model SIW) (unit_kMD _) tt SIW_R SIW_J SIW_CJ _ (MonoPred_SM SIW) _ _ _ x y).
*)
Abort.

End SL.

End SL.