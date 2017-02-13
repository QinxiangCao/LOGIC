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
Require Import Logic.Extensions.Semantics.ModalSeparation.
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
        {R: KI.Relation worlds}
        {J: Join worlds}
        {C: Core worlds}
        {po_R: PreOrder (@KI.Krelation _ R)}
        {SA: SeparationAlgebra worlds}
        {uSA: UpwardsClosedSeparationAlgebra worlds}
        {dSA: DownwardsClosedSeparationAlgebra worlds}
        {CJ: CoreJoin worlds}
        {UC: UniqueCore worlds}.

Definition SIW: Type := nat * worlds. (* step indexed worlds *)

Instance SIW_R: KI.Relation SIW := @RelProd _ worlds nat_geR R.

Instance SIW_J: Join SIW := @prod_Join nat _ min_Join J.

Instance SIW_Cor: SS.Relation SIW := @RelProd _ worlds eq full_relation.

Instance SIW_C: Core SIW := @prod_C nat _ id C.

Instance SIW_Ctr: KM.Relation SIW :=
  @RelProd _ _ eq (fun m => eq (core m)).

Instance po_SIW_R: PreOrder (@KI.Krelation _ SIW_R) := @RelProd_Preorder _ _ _ _ po_nat_geR po_R.

Instance SIW_SA: SeparationAlgebra SIW := @prod_SA _ _ _ _ minAlg SA.

Instance SIW_uSA: UpwardsClosedSeparationAlgebra SIW :=
  @prod_uSA _ _ _ _ _ _ minAlg_uSA uSA.

Instance SIW_dSA: DownwardsClosedSeparationAlgebra SIW :=
  @prod_dSA _ _ _ _ _ _ minAlg_dSA dSA.

Instance SIW_R_bis: Bisimulation (@SS.Krelation _ SIW_Cor) (@KI.Krelation _ SIW_R) :=
  @RelProd_Bisimulation _ _ _ _ _ _ (eq_bis _) (@full_bis _ _ (fun n => ex_intro _ n (@reflexivity _ _ PreOrder_Reflexive n))).

Instance SIW_CJ: CoreJoin SIW :=
  @prod_CJ _ _ _ _ _ _ _ _ geR_id_CJ CJ.

Instance SIW_CM: CoreModal SIW :=
  @prod_CM nat worlds _ _ _ _ (func_CM _) (func_CM _).

Instance SIW_ukmM: UpwardsClosedOrderedKripkeModel SIW :=
  @prod_ukmM nat worlds _ _ _ _ (eq2_ukmM _) (@IrisModel.ukmM worlds R J C po_R (fun m => eq (core m)) (func_CM _) UC).

Instance pf_SIW_Ctr: @PartialFunctional SIW (@KM.Krelation SIW SIW_Ctr) :=
  @RelProd_PartialFunctional _ _ _ _ (@Functional_PartialFunctional _ _ (@function_Functional _ id)) (@Functional_PartialFunctional _ _ (function_Functional)).

Instance SIW_SAbis: SeparationAlgebraBisStable SIW :=
  @prod_SAbis _ _ _ _ _ _ (eq_SAbis nat) (IrisModel.SAbis worlds).

Instance SIW_SAabs: SeparationAlgebraAbsorbStable SIW :=
  @prod_SAabs _ _ _ _ _ _ _ _ geR_min_eq_SAabs (IrisModel.SAabs worlds).

Instance SIW_Ctr_bis_J: ModalBisJoin SIW :=
  @prod_KM_bis_J _ _ _ _ _ _ (eq_bis_J _ _) (@IrisModel.Ctr_bis_J worlds R J C CJ (fun m => eq (core m)) (func_CM _) UC).

Instance SIW_USA: UnitalSeparationAlgebra SIW :=
  @prod_unitalSA _ _ _ _ _ _ minAlg_unital (IrisModel.USA worlds).

Instance incl_SIW_Ctr_Cor: Inclusion KM.Krelation SS.Krelation :=
  @RelProd_Inclusion _ _ _ _ _ _ _ _.
Proof.
  + hnf; intros; auto.
  + hnf; intros; hnf; auto.
Qed.

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

Instance CorsG: Corable L G :=
  Build_Corable _ _ _ _ _ _ _ _ _ (MonoPred_stable SIW) (MonoPred_pstable SIW) (MonoPred_sstable SIW) (MonoPred_SAS SIW).

Instance CtrsG: CoreTransitSeparationLogic L G.
  apply (Build_CoreTransitSeparationLogic L _ _ _ _ _ _ _ ipG sG CorsG _KmG (MonoPred_pmGamma SIW)).
  + constructor.
    intros x y.
    exact (@Sound.sound_sepcon_boxp L nL pL _ _ (Build_Model SIW) (unit_kMD (Build_Model SIW)) tt SIW_R SIW_J SIW_C _ SIW_CM SIW_Ctr_bis_J (MonoPred_SM SIW) _ _ _ x y).
  + constructor.
    intros x y.
    exact (@Sound.sound_boxp_sepcon L nL pL _ _ (Build_Model SIW) (unit_kMD (Build_Model SIW)) tt SIW_R SIW_J SIW_C _ SIW_CM SIW_Ctr_bis_J (MonoPred_SM SIW) _ _ _ x y).
  + intros x y.
    exact (@Sound.sound_boxp_andp_is_sepcon L nL pL _ _ (Build_Model SIW) (unit_kMD (Build_Model SIW)) tt SIW_R SIW_J SIW_C _ SIW_Ctr SIW_CM (MonoPred_SM SIW) _ _ _ x y).
  + exact (MonoPred_MAS SIW).
Qed.

End SL.

End SL.
