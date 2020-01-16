(*TODO: there should be
  and   + neg   = or
  or    + neg   = and   *
  neg   + or    = imp
  and   + imp   = iff   *
  false + imp   = true  *
  false + imp   = neg   *
  neg   + true  = false
  neg   + false = true
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

Class IffDefinition_And_Impp
      (L: Language)
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}: Prop:= {
  andp_impp2iffp: forall x y,
  x <--> y = (x --> y) && (y --> x)
}.

Class TrueDefinition_False_Impp
      (L: Language)
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}: Prop:= {
  falsep_impp2truep:
  TT = FF --> FF
}.

Class NegDefinition_False_Impp
      (L: Language)
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}: Prop:= {
  falsep_impp2negp: forall x,
  ~~ x = x --> FF
}.

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

Lemma AndImp2Iff_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}:
  @IffDefinition_And_Impp L _ _ AndImp2Iff.
Proof. constructor. reflexivity. Qed.

Lemma FalseImp2True_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}:
  @TrueDefinition_False_Impp L _ _ FalseImp2True.
Proof. constructor. reflexivity. Qed.

Lemma FalseImp2Neg_Normal
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}:
  @NegDefinition_False_Impp L _ _ FalseImp2Neg.
Proof. constructor. reflexivity. Qed.

Lemma IffFromDefToAX_And_Impp
      {L: Language}
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {iffpL: IffLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {andpAX: AndAxiomatization L GammaP}
      {iffp_Def_andp_impp: IffDefinition_And_Impp L}:
      IffAxiomatization L GammaP.
Proof.
  intros.
  constructor; intros; rewrite andp_impp2iffp.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
Qed.

Lemma TrueFromDefToAX_False_Impp
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {falsepAX: FalseAxiomatization L GammaP}
      {truep_Def_falsep_impp: TrueDefinition_False_Impp L}:
      TrueAxiomatization L GammaP.
Proof.
  intros.
  constructor; rewrite falsep_impp2truep.
  apply (provable_impp_refl FF).
Qed.

Lemma NegFromDefToAX_False_Impp
      {L: Language}
      {minL: MinimumLanguage L}
      {falsepL: FalseLanguage L}
      {negpL: NegLanguage L}
      {GammaP: Provable L}
      {minAX: MinimumAxiomatization L GammaP}
      {falsepAX: FalseAxiomatization L GammaP}
      {negp_Def_falsep_impp: NegDefinition_False_Impp L}:
      IntuitionisticNegAxiomatization L GammaP.
Proof.
  intros.
  constructor; intros; rewrite falsep_impp2negp; apply(provable_impp_refl (x --> FF)).
Qed.




