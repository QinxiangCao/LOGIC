Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.lib.Countable.
Require Import Logic.lib.Bijection.
Local Open Scope logic_base.
Import ModalLanguageNotation.
Class ModalVariables: Type := {
  Var: Type
}.
Inductive expr {sigma : ModalVariables} : Type :=
  |falsep : expr
  |impp : expr -> expr -> expr
  |varp : Var -> expr
  |boxp : expr -> expr.

Arguments expr sigma: clear implicits.
Instance L {sigma: ModalVariables}: Language :=
  Build_Language (expr sigma).

Instance minL {sigma: ModalVariables}: MinimunLanguage L :=
  Build_MinimunLanguage L impp.

Instance mL {sigma: ModalVariables}: ModalLanguage L :=
  Build_ModalLanguage L boxp falsep.


(*Definition rank {sigma: ModalVariables}: expr sigma -> nat :=
  fix rank (x: expr sigma): nat :=
    match x with
    | impp y z => 1 + rank y + rank z
    | falsep => 0
    | varp p => 0
    | boxp y => 1 + rank y
    end.*)
(*Definition formula_countable: forall {sigma}, Countable Var -> Countable (expr sigma).
  intros.
  assert (forall n, Countable (sig (fun x: expr sigma => rank x <= n))).
  + induction n.
     - apply (@bijection_Countable _ (Var + unit)%type); [| solve_Countable].
       apply bijection_sym.
       apply (FBuild_bijection _ _ (fun x =>
         match x with
           | inl p => exist (fun x: expr sigma => rank x <= 0) (varp p) (le_n 0)
           | inr _ => exist (fun x: expr sigma => rank x <= 0) falsep (le_n 0)
           end)).
      * hnf; intros.
        destruct a1 as [? | []], a2 as [? | []]; inversion H; auto.
      * hnf; intros.
        destruct b as [[] HH]; try solve [inversion HH].
        1: exists (inr tt); eauto; f_equal; apply proof_irrelevance.
        1: exists (inl v); eauto; f_equal; apply proof_irrelevance.
    -set (s := sig (fun x: expr sigma => rank x <= n)).
      apply (@injection_Countable _ (s * s + s * s + s * s + unit + Var)%type); [| solve_Countable].
(* Admitted.*) *)