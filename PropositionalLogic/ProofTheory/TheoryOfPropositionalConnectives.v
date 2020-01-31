(*TODO: there should be
  and   + neg   = or
  or    + neg   = and   *
  neg   + or    = imp
  and   + imp   = iff   *
  false + imp   = true  *
  false + imp   = neg   *
  neg   + true  = false *
  neg   + false = true  *
  neg   + imp   = or    *
if possible, write about from Coq prop to true and false*)

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class AndDefinition_Or_Neg
      (L: Language)
      {orpL: OrLanguage L}
      {negpL: NegLanguage L}
      {andpL: AndLanguage L}: Prop:= {
  orp_negp2andp: forall x y,
  x && y = ~~ ((~~ x) || (~~ y))
}.

Class IffDefinition_And_Imp
      (L: Language)
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}: Prop:= {
  andp_impp2iffp: forall x y,
  x <--> y = (x --> y) && (y --> x)
}.

Class TrueDefinition_False_Imp
      (L: Language)
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}: Prop:= {
  falsep_impp2truep:
  TT = FF --> FF
}.

Class NegDefinition_False_Imp
      (L: Language)
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}: Prop:= {
  falsep_impp2negp: forall x,
  ~~ x = x --> FF
}.

Class OrDefinition_Imp_Neg
      (L: Language)
      {minL: MinimumLanguage L}
      {negpL: NegLanguage L}
      {orpL: OrLanguage L}: Prop:= {
  impp_negp2orp: forall x y,
  x || y = ((~~ x) --> y)
}.

Class TrueDefinition_Imp_Self
      (L: Language)
      {minL: MinimumLanguage L}
      {truepL: TrueLanguage L}: Prop:= {
  impp_self2truep: exists x,
  TT = x --> x
}.

Class TrueDefinition_Neg_False
      (L: Language)
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}
      {truepL: TrueLanguage L}: Prop:= {
  negp_falsep2truep:
  TT = ~~ FF
}.

Class FalseDefinition_Neg_True
      (L: Language)
      {truepL: TrueLanguage L}
      {negpL: NegLanguage L}
      {falsepL: FalseLanguage L}: Prop:= {
  negp_truep2falsep:
  FF = ~~ TT
}.

Definition OrNeg2And
           {L: Language}
           {orpL: OrLanguage L}
           {negpL: NegLanguage L}: AndLanguage L :=
  Build_AndLanguage _ (fun x y => ~~ ((~~ x) || (~~ y))).

Definition AndImp2Iff
           {L: Language}
           {minL: MinimumLanguage L}
           {andpL: AndLanguage L}: IffLanguage L :=
  Build_IffLanguage _ (fun x y => (x --> y) && (y --> x)).

Definition FalseImp2True
           {L: Language}
           {minL: MinimumLanguage L}
           {falsepL: FalseLanguage L}: TrueLanguage L :=
  Build_TrueLanguage _ (FF --> FF).


Definition FalseImp2Neg
           {L: Language}
           {minL: MinimumLanguage L}
           {falsepL: FalseLanguage L}: NegLanguage L :=
  Build_NegLanguage _ (fun x => (x --> FF)).

Definition ImpNeg2Or
           {L: Language}
           {minL: MinimumLanguage L}
           {negpL: NegLanguage L}: OrLanguage L :=
  Build_OrLanguage _ (fun x y => ((~~ x) --> y)).

Definition ImpSelf2True
           {L: Language}
           {minL: MinimumLanguage L}
           (x: expr): TrueLanguage L :=
  Build_TrueLanguage _ (impp x x).

Definition NegFalse2True
           {L: Language}
           {falsepL: FalseLanguage L}
           {negpL: NegLanguage L}: TrueLanguage L :=
  Build_TrueLanguage _ (negp falsep).
           
Definition NegTrue2False
           {L: Language}
           {truepL: TrueLanguage L}
           {negpL: NegLanguage L}: FalseLanguage L :=
  Build_FalseLanguage _ (negp truep).
           
Lemma OrNeg2And_Normal
      {L: Language}
      {orpL: OrLanguage L}
      {negpL: NegLanguage L}:
  @AndDefinition_Or_Neg L _ _ OrNeg2And.
Proof. constructor. reflexivity. Qed.

Lemma AndImp2Iff_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}:
  @IffDefinition_And_Imp L _ _ AndImp2Iff.
Proof. constructor. reflexivity. Qed.

Lemma FalseImp2True_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}:
  @TrueDefinition_False_Imp L _ _ FalseImp2True.
Proof. constructor. reflexivity. Qed.

Lemma FalseImp2Neg_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}:
  @NegDefinition_False_Imp L _ _ FalseImp2Neg.
Proof. constructor. reflexivity. Qed.

Lemma ImpNeg2Or_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      {negpL: NegLanguage L}:
  @OrDefinition_Imp_Neg L _ _ ImpNeg2Or.
Proof. constructor. reflexivity. Qed.

Lemma ImpSelf2True_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      (x: expr):
  @TrueDefinition_Imp_Self L _ (ImpSelf2True x).
Proof. constructor. eexists. reflexivity. Qed.

Lemma NegFalse2True_Normal
      {L: Language}
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}:
  @TrueDefinition_Neg_False L _ _ NegFalse2True.
Proof. constructor. reflexivity. Qed.

Lemma NegTrue2False_Normal
      {L: Language}
      {truepL: TrueLanguage L}
      {negpL: NegLanguage L}:
  @FalseDefinition_Neg_True L _ _ NegTrue2False.
Proof. constructor. reflexivity. Qed.

Lemma AndFromDefToAX_Or_Neg
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {orpL: OrLanguage L}
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {orpAX: OrAxiomatization L GammaP}
      {falsepAx: FalseAxiomatization L GammaP}
      {inegpAx: IntuitionisticNegAxiomatization L GammaP}
      {cpAX: ClassicalAxiomatization L GammaP}
      {andp_Def_orp_negp: AndDefinition_Or_Neg L}:
      AndAxiomatization L GammaP.
Proof.
  AddSequentCalculus.
  intros.
  constructor; intros; rewrite orp_negp2andp.
  + rewrite <- contrapositivePN.
    rewrite <- provable_impp_arg_switch.
    rewrite provable_derivable; rewrite <- deduction_theorem.
    apply deduction_orp_elim.
    - rewrite deduction_theorem.
      apply deduction_impp_arg_switch.
      apply derivable_contradiction_elim2.
    - rewrite <- deduction_theorem. solve_assum.
  + rewrite <- (double_negp_elim x) at 2. rewrite <- contrapositivePP.
    apply orp_intros1.
  + rewrite <- (double_negp_elim y) at 2. rewrite <- contrapositivePP.
    apply orp_intros2.
Qed.

Lemma IffFromDefToAX_And_Imp
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {andpAX: AndAxiomatization L GammaP}
      {iffp_Def_andp_impp: IffDefinition_And_Imp L}:
      IffAxiomatization L GammaP.
Proof.
  intros.
  constructor; intros; rewrite andp_impp2iffp.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
Qed.

Lemma TrueFromDefToAX_False_Imp
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {falsepAX: FalseAxiomatization L GammaP}
      {truep_Def_falsep_impp: TrueDefinition_False_Imp L}:
      TrueAxiomatization L GammaP.
Proof.
  intros.
  constructor; rewrite falsep_impp2truep.
  apply (provable_impp_refl FF).
Qed.

Lemma NegFromDefToAX_False_Imp
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {falsepAX: FalseAxiomatization L GammaP}
      {negp_Def_falsep_impp: NegDefinition_False_Imp L}:
      IntuitionisticNegAxiomatization L GammaP.
Proof.
  intros.
  constructor; intros; rewrite !falsep_impp2negp.
  + apply provable_impp_trans.
  + apply aux_minimun_rule01.
    apply falsep_elim.
  + apply aux_minimun_theorem02.
Qed.

Lemma OrFromDefToAX_Imp_Neg
      {L: Language}
      {minL: MinimumLanguage L}
      {orpL: OrLanguage L}
      {negpL: NegLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {inegpAx: IntuitionisticNegAxiomatization L GammaP}
      {cpAX: ClassicalAxiomatization L GammaP}
      {orp_Def_impp_negp: OrDefinition_Imp_Neg L}:
      OrAxiomatization L GammaP.
Proof.
  AddSequentCalculus.
  intros.
  constructor; intros; rewrite impp_negp2orp.
  + rewrite provable_derivable. apply derivable_contradiction_elim2.
  + rewrite provable_derivable. rewrite <- !deduction_theorem.
    solve_assum.
  + pose proof (aux_minimun_theorem00 (~~ x) y z).
    pose proof classic_analysis x z.
    rewrite <- (provable_impp_arg_switch (y --> z) (x --> z) ((~~ x --> y) --> z)).
    rewrite <- (provable_impp_arg_switch (~~ x --> y) (x --> z) z).
    rewrite provable_impp_arg_switch in H0.
    rewrite provable_derivable in H |- *.
    rewrite <- !deduction_theorem in H |- *. rewrite deduction_theorem in H |- *.
    rewrite H0 in H.
    apply H.
Qed.

Lemma TrueFromDefToAX_Imp_Self
      {L: Language}
      {minL: MinimumLanguage L}
      {truepL: TrueLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {truep_Def_impp_self: TrueDefinition_Imp_Self L}:
      TrueAxiomatization L GammaP.
Proof.
  pose proof impp_self2truep as [x ?].
  constructor.
  rewrite H; clear H.
  apply provable_impp_refl.
Qed.

Lemma TrueFromDefToAX_Neg_False
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}
      {negpL: NegLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {falsepAX: FalseAxiomatization L GammaP}
      {negpAX: IntuitionisticNegAxiomatization L GammaP}
      {truep_Def_negp_falsep: TrueDefinition_Neg_False L}:
      TrueAxiomatization L GammaP.
Proof.
  constructor.
  rewrite negp_falsep2truep.
  rewrite <- negp_fold.
  apply provable_impp_refl.
Qed.

Lemma FalseFromDefToAX_Neg_True
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}
      {negpL: NegLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {truepAX: TrueAxiomatization L GammaP}
      {negpAX: IntuitionisticNegAxiomatization L GammaP}
      {falsep_Def_negp_truep: FalseDefinition_Neg_True L}:
      FalseAxiomatization L GammaP.
Proof.
  constructor.
  intros.
  rewrite negp_truep2falsep.
  eapply modus_ponens; [| apply truep_intros].
  apply contradiction_elim2.
Qed.

Ltac AddConnective_iffp :=
  let iffpL := fresh "iffpL" in
  let iffpDef := fresh "iffpDef" in
  let iffpAX := fresh "iffpAX" in
  set (iffpL := AndImp2Iff);
  set (iffpDef := AndImp2Iff_Normal);
  set (iffpAX := IffFromDefToAX_And_Imp);
  clearbody iffpAX;
  clear iffpDef;
  clearbody iffpL.

Ltac AddConnective_truep :=
  let truepL := fresh "truepL" in
  let truepDef := fresh "truepDef" in
  let truepAX := fresh "truepAX" in
  set (truepL := FalseImp2True);
  set (truepDef := FalseImp2True_Normal);
  set (truepAX := TrueFromDefToAX_False_Imp);
  clearbody truepAX;
  clear truepDef;
  clearbody truepL.

Ltac AddConnective_negp :=
  let negpL := fresh "negpL" in
  let negpDef := fresh "negpDef" in
  let negpAX := fresh "inegpAX" in
  set (negpL := FalseImp2Neg);
  set (negpDef := FalseImp2Neg_Normal);
  set (negpAX := NegFromDefToAX_False_Imp);
  clearbody negpAX;
  clear negpDef;
  clearbody negpL.

Ltac AddConnective_truep_impp_self_tac1 x :=
  let truepL := fresh "truepL" in
  let truepDef := fresh "truepDef" in
  let truepAX := fresh "truepAX" in
  set (truepL := ImpSelf2True x);
  set (truepDef := ImpSelf2True_Normal x);
  set (truepAX := TrueFromDefToAX_Imp_Self);
  clearbody truepAX;
  clear truepDef;
  clearbody truepL.

Ltac AddConnective_truep_impp_self_tac0 :=
  match goal with
  | x: expr |- _ =>
          AddConnective_truep_impp_self_tac1 x
  | |- ?P =>
          let x := fresh "x" in
          ( (intro x; match type of x with | ?T => unify T expr end)
            || fail 1 "cannot find an expr");
          AddConnective_truep_impp_self_tac1 x;
          revert x;
          change P
  end.

Tactic Notation "AddConnective_truep_impp_self" :=
  AddConnective_truep_impp_self_tac0.

Tactic Notation "AddConnective_truep_impp_self" constr(x) :=
  AddConnective_truep_impp_self_tac1 x.

