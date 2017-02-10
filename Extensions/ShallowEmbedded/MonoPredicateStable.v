Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.Extensions.ProofTheory.Stable.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.Extensions.Semantics.SemanticStable.
Require Import Logic.ModalLogic.Semantics.Flat.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.Extensions.Sound.StableSound.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.PropositionalLogic.ShallowEmbedded.MonoPredicatePropositionalLogic.
Require Import Logic.ModalLogic.ShallowEmbedded.MonoPredicateModalLogic.
Require Import Logic.SeparationLogic.ShallowEmbedded.MonoPredicateSeparationLogic.

Instance MonoPred_stableSM (A: Type) {R1: KI.Relation A} {kiM: KripkeIntuitionisticModel A} {R2: SS.Relation A}: @SemanticStable (MonoPred_L A) (Build_Model A) (unit_kMD _) tt R2 (MonoPred_SM A).
Proof.
  refine (Build_SemanticStable _ _ _ _ _ _ (fun x => Semantics.stable (@Kdenotation _ _ (unit_kMD _) tt _ x)) _).
  intros. reflexivity.
Defined.

Instance MonoPred_pstable (A: Type) {R1: KI.Relation A} {kiM: KripkeIntuitionisticModel A} {R2: SS.Relation A} {KI_bis_R2: KripkeIntuitionisticBisStable A}: PropositionalStable (MonoPred_L A) (MonoPred_Gamma A) (fun x => Semantics.stable (@Kdenotation _ (Build_Model A) (unit_kMD _) tt _ x)).
Proof.
  constructor.
  + intros x y.
    exact (@Sound_KripkeIntuitionistic.sound_impp_stable (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R1 _ _ (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_stableSM A) x y).
  + intros x y.
    exact (@Sound_KripkeIntuitionistic.sound_andp_stable (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R1 _ (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_stableSM A) x y).
  + intros x y.
    exact (@Sound_KripkeIntuitionistic.sound_orp_stable (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R1 _ (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_stableSM A) x y).
  + exact (@Sound_KripkeIntuitionistic.sound_falsep_stable (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R1 _ (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_stableSM A)).
  + hnf; intros x y.
    exact (@Sound_KripkeIntuitionistic.sound_stable_proper_iffp (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R1 _ _ (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_stableSM A) x y).
Qed.

Instance MonoPred_mstable (A: Type) {R1: KI.Relation A} {kiM: KripkeIntuitionisticModel A} {R2: KM.Relation A} {R3: SS.Relation A} {ukmM: UpwardsClosedOrderedKripkeModel A} {KM_bis_R3: KripkeModalBisStable A}: ModalStable (MonoPred_L A) (MonoPred_Gamma A) (fun x => Semantics.stable (@Kdenotation _ (Build_Model A) (unit_kMD _) tt _ x)).
Proof.
  constructor.
  intros x.
  exact (@Sound_KripkeIntuitionistic.sound_boxp_stable (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R1 _ _ _ (MonoPred_SM A) (MonoPred_fmSM A) (MonoPred_stableSM A) x).
Qed.

Instance MonoPred_MAS (A: Type) {R1: KI.Relation A} {kiM: KripkeIntuitionisticModel A} {R2: KM.Relation A} {R3: SS.Relation A} {ukmM: UpwardsClosedOrderedKripkeModel A} {KM_abs_R3: KripkeModalAbsorbStable A}: ModalAbsorbStable (MonoPred_L A) (MonoPred_Gamma A) (fun x => Semantics.stable (@Kdenotation _ (Build_Model A) (unit_kMD _) tt _ x)).
Proof.
  constructor.
  intros x.
  exact (@Sound_KripkeIntuitionistic.sound_boxp_absorb_stable (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R1 _ _ _ (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_fmSM A) (MonoPred_stableSM A) x).
Qed.

Instance MonoPred_sstable (A: Type) {R1: KI.Relation A} {kiM: KripkeIntuitionisticModel A} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {R2: SS.Relation A} {SA_bis_R2: SeparationAlgebraBisStable A}: SeparationStable (MonoPred_L A) (MonoPred_Gamma A) (fun x => Semantics.stable (@Kdenotation _ (Build_Model A) (unit_kMD _) tt _ x)).
Proof.
  constructor.
  + intros x y.
    exact (@Sound_KripkeIntuitionistic.sound_sepcon_stable (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R1 _ _ _ (MonoPred_SM A) (MonoPred_fsSM A) (MonoPred_stableSM A) x y).
  + intros x y.
    exact (@Sound_KripkeIntuitionistic.sound_wand_stable (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R1 _ _ _ (MonoPred_SM A) (MonoPred_fsSM A) (MonoPred_stableSM A) x y).
Qed.

Instance MonoPred_SAS (A: Type) {R1: KI.Relation A} {kiM: KripkeIntuitionisticModel A} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {R2: SS.Relation A} {SA_abs_R2: SeparationAlgebraAbsorbStable A}: SeparationAbsorbStable (MonoPred_L A) (MonoPred_Gamma A) (fun x => Semantics.stable (@Kdenotation _ (Build_Model A) (unit_kMD _) tt _ x)).
Proof.
  constructor.
  intros x y z.
  exact (@Sound_KripkeIntuitionistic.sound_stable_andp_sepcon1 (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R1 _ _ _ (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_fsSM A) (MonoPred_stableSM A) x y z).
Qed.
