Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Import Logic.ModalLogic.ModalLanguage.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.ModalLogic.Semantics.Kripke.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import ModalLanguage.

Record frame: Type := {
  underlying_set:> Type;
  underlying_relation: relation underlying_set
}.

Infix "<=" := (underlying_relation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.
Definition sem (f: frame) := @Ensemble (underlying_set f).

Section KripkeSemantics.
Context {Sigma: ModalVariables}.
Definition denotation (F: frame) (eval: Var -> sem F): expr Sigma -> sem F :=
  fix denotation (x: expr Sigma): sem F:=
  match x with
  | impp y z => @Semantics.impp F (underlying_relation F) (denotation y) (denotation z)
  | falsep => @Semantics.falsep F
  | varp p => eval p
  | boxp p => @Semantics.boxp F (underlying_relation F) (denotation p)
  end.

Record Kmodel : Type := {
  underlying_frame :> frame;
  sem_var: Var -> sem underlying_frame
}.

Record model: Type := {
  underlying_model :> Kmodel;
  elm: underlying_model
}.

Instance MD: Model := Build_Model model.


Instance kMD: KripkeModel MD :=
  Build_KripkeModel _
    Kmodel
    (fun M => M)
    (fun M m => Build_model M m).

Instance R (M: Kmodel): Relation (Kworlds M) :=
  @underlying_relation M.


Definition Kmodel_PreOrder: Kmodel -> Prop := fun M =>
  PreOrder (@Krelation _ (R M)).

Instance SM: Semantics L MD :=
  Build_Semantics L MD (fun x M => (denotation M (sem_var M) x) (elm M)).


End KripkeSemantics.
