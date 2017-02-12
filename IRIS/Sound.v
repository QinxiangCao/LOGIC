Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.OSAExamples.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Syntax_CoreTransit.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.ModalLogic.Semantics.Flat.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.Extensions.Semantics.SemanticStable.
Require Import Logic.Extensions.Semantics.ModalSeparation.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import CoreTransitNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Class Core (worlds: Type): Type := core: worlds -> worlds.

Class UniqueCore (worlds: Type) {J: Join worlds} {C: Core worlds} := {
  unique_core: forall n m, core n = core m;
  core_no_split: forall n n1 n2, join n1 n2 (core n) -> n1 = core n /\ n2 = core n
}.

Class CoreJoin (worlds: Type) {R: KI.Relation worlds} {J: Join worlds} {C: Core worlds} := {
  core_incr_res: forall n, residue n (core n) /\ increasing (core n);
  core_core: forall n, core (core n) = core n;
  core_join_self: forall n, join (core n) (core n) (core n)
}.

Lemma eq_id_CJ (A: Type) {R: KI.Relation A} {po_R: PreOrder KI.Krelation}: @CoreJoin A eq equiv_Join id.
Proof.
  constructor.
  + intros.
    split.
    - exists n.
      split; [constructor; auto | reflexivity].
    - hnf; intros.
      inversion H; subst.
      reflexivity.
  + intros; auto.
  + intros; constructor; auto.
Qed.

Lemma geR_id_CJ: @CoreJoin nat nat_geR min_Join id.
Proof.
  pose proof po_nat_geR.
  constructor.
  + intros.
    split.
    - exists n.
      split; [constructor; auto | reflexivity].
    - hnf; intros.
      inversion H0; subst.
      auto.
  + intros; auto.
  + intros; constructor; auto.
Qed.

Instance prod_C {A B: Type} (CA: Core A) (CB: Core B): Core (A * B) := fun ab => (core (fst ab), core (snd ab)).
   
Instance prod_CJ (A B: Type) {RA: KI.Relation A} {RB: KI.Relation B} {JA: Join A} {JB: Join B} {CA: Core A} {CB: Core B} {CJA: CoreJoin A} {CJB: CoreJoin B}: @CoreJoin _ (@RelProd _ _ (@Krelation _ RA) (@Krelation _ RB)) (@prod_Join _ _ JA JB) (prod_C CA CB).
Proof.
  constructor.
  + intros.
    destruct (@core_incr_res _ _ _ _ CJA (fst n)).
    destruct (@core_incr_res _ _ _ _ CJB (snd n)).
    split.
    - destruct H as [m1 [? ?]].
      destruct H1 as [m2 [? ?]].
      exists (m1, m2).
      split; split; auto.
    - apply prod_incr; auto.
  + intros.
    change (@core _ (prod_C _ _)) with (fun ab: A* B => (core (fst ab), core (snd ab))).
    simpl.
    rewrite !core_core.
    reflexivity.
  + intros; split; auto; apply core_join_self.
Qed.

Module IrisModel.
Section IrisModel.

Context (worlds: Type)
        {R: KI.Relation worlds}
        {J: Join worlds}
        {C: Core worlds}
        {po_R: PreOrder (@KI.Krelation _ R)}
        {SA: SeparationAlgebra worlds}
        {dSA: DownwardsClosedSeparationAlgebra worlds}
        {CJ: CoreJoin worlds}
        {UC: UniqueCore worlds}.

Instance USA: UnitalSeparationAlgebra worlds.
Proof.
  constructor.
  intros.
  exists (core n).
  apply core_incr_res.
Qed.

Instance Ctr: KM.Relation worlds := fun n => eq (core n).

Instance pf_Ctr: PartialFunctional (@KM.Krelation _ Ctr).
Proof.
  hnf.
  intros.
  hnf in H, H0.
  congruence.
Qed.

Instance ukmM: UpwardsClosedOrderedKripkeModel worlds.
Proof.
  constructor.
  intros.
  exists n'.
  split; [reflexivity |].
  hnf in H0 |- *.
  subst n'.
  apply unique_core.
Qed.

Instance SAbis: @SeparationAlgebraBisStable worlds J full_relation.
Proof.
  apply (@full_SAbis _ R po_R _ SA dSA).
  apply unital_is_residual, USA.
Qed.

Instance SAabs: @SeparationAlgebraAbsorbStable worlds R J full_relation.
Proof.
  apply full_SAabs, po_R.
Qed.

Instance Ctr_bis_J: ModalBisJoin worlds.
Proof.
  constructor.
  intros.
  hnf in H; subst.
  split; intros.
  + apply core_no_split in H.
    destruct H; subst.
    destruct (incr_exists m) as [e [[n [? _]] _]].
    exists e, n.
    split; [| split]; auto; apply unique_core.
  + exists (core m), (core m).
    split; [| split]; [apply core_join_self | apply unique_core | apply unique_core].
Qed.

End IrisModel.
End IrisModel.

Existing Instances IrisModel.USA IrisModel.Ctr IrisModel.pf_Ctr ct_mL.

Section IrisSemantics.    

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {ctsL: CoreTransitSeparationLanguage L}.

Context {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: KI.Relation (Kworlds M)}
        {J: Join (Kworlds M)}
        {C: Core (Kworlds M)}
        {CJ: CoreJoin (Kworlds M)}
        {Ctr_bis_J: ModalBisJoin (Kworlds M)}.

Context {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {fm: FlatModalSemantics L MD M SM}
        {fsSM: SeparatingSemantics L MD M SM}.

Lemma sat_core_tr: forall x m, KRIPKE: M, m |= core_tr x <-> KRIPKE: M, (core m) |= x.
Proof.
  intros.
  change core_tr with boxp.
  rewrite sat_boxp.
  split; intros.
  + apply H.
    hnf; auto.
  + hnf in H0.
    subst; auto.
Qed.

Lemma sound_sepcon_boxp:
  forall x y: expr,
    forall m: Kworlds M, KRIPKE: M, m |= core_tr x * core_tr y --> core_tr (x * y).
Proof.
  intros.
  rewrite !sat_impp.
  intros.
  clear m H.
  rewrite sat_sepcon in H0.
  destruct H0 as [n1 [n2 [? [? ?]]]].
  rewrite sat_core_tr in H0, H1 |- *.
  pose proof KM_join_bis n _ eq_refl.
  destruct H2 as [_ ?].
  specialize (H2 _ _ H).
  destruct H2 as [m1 [m2 [? [? ?]]]].
  rewrite sat_sepcon; exists m1, m2.
  hnf in H3, H4; subst.
  auto.
Qed.

Lemma sound_boxp_sepcon:
  forall x y: expr,
    forall m: Kworlds M, KRIPKE: M, m |= core_tr (x * y) --> core_tr x * core_tr y.
Proof.
  intros.
  rewrite !sat_impp.
  intros.
  clear m H.
  rewrite sat_sepcon.
  rewrite sat_core_tr in H0.
  rewrite sat_sepcon in H0.
  destruct H0 as [c1 [c2 [? [? ?]]]].
  pose proof KM_join_bis n _ eq_refl.
  destruct H2 as [? _].
  specialize (H2 _ _ H).
  destruct H2 as [n1 [n2 [? [? ?]]]].
  exists n1, n2.
  hnf in H3, H4; subst c1 c2.
  rewrite !sat_core_tr.
  auto.
Qed.

Lemma sound_boxp_andp_is_sepcon:
  forall x y: expr,
    forall m: Kworlds M, KRIPKE: M, m |= core_tr (x && y) --> core_tr (x * y).
Proof.
  intros.
  rewrite sat_impp; intros.
  clear m H.
  rewrite sat_core_tr in H0 |- *.
  rewrite sat_sepcon.
  rewrite sat_andp in H0.
  exists (core n), (core n).
  pose proof core_join_self n.
  auto.
Qed.

End IrisSemantics.
