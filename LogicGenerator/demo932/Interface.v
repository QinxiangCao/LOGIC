Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Module Type LanguageSig.
  Parameter model : Type .
  Definition expr := (model -> Prop) .
  Parameter Inline provable : (expr -> Prop) .
  Parameter join : (model -> model -> model -> Prop) .
  Parameter impp : (expr -> expr -> expr) .
End LanguageSig.

Module DerivedNames (Names: LanguageSig).
Include Names.
  Definition sepcon := (fun (x y : model -> Prop) (m : model) => exists m1 m2 : model, join m1 m2 m /\ x m1 /\ y m2) .
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Axiom join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
  Axiom join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).
Include Rules.
Parameter Inline tree_pos : Type .
  Axiom sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) .
  Axiom sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Axiom sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) .
  Axiom expr_deep : Set .
  Axiom impp_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom sepcon_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom emp_deep : expr_deep .
  Axiom varp_deep : (nat -> expr_deep) .
  Axiom var_pos : (expr -> option positive -> tree_pos) .
  Axiom sepcon_pos : (tree_pos -> tree_pos -> tree_pos) .
  Axiom cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) .
  Axiom cancel_same : (tree_pos -> tree_pos -> Prop) .
  Axiom restore : (tree_pos -> tree_pos -> expr) .
  Axiom sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) .
  Axiom sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) .
  Existing Instance sepcon_proper_impp .
End LogicTheoremSig.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.Join2Sepcon.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.

Module LogicTheorem (Names: LanguageSig) (Rules: PrimitiveRuleSig Names) <: LogicTheoremSig Names Rules.
Include Rules.
  Instance M : Model := (Build_Model model) .
  Instance L : Language := (Build_Language expr) .
  Instance J : (Join model) := join .
  Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  Instance GammaP : (Provable L) := (Build_Provable L provable) .
  Instance J_SA : (SeparationAlgebra model) := (Build_SeparationAlgebra model J join_comm join_assoc) .
  Instance sepconFJ : (SepconDefinition_Join (Pred_sepconL model)) := Join2Sepcon_Normal .
  Instance sepconAX : (SepconAxiomatization L GammaP) := SeparationAlgebra2SepconAxiomatization .
Definition tree_pos : Type := tree_pos.
  Definition sepcon_comm_impp : (forall x y : expr, provable (impp (sepcon x y) (sepcon y x))) := sepcon_comm_impp .
  Definition sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := sepcon_assoc1 .
  Definition sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) := sepcon_mono .
  Definition sepcon_proper_impp : (Morphisms.Proper (Morphisms.respectful (fun x y : expr => provable (impp x y)) (Morphisms.respectful (fun x y : expr => provable (impp x y)) (fun x y : expr => provable (impp x y)))) sepcon) := sepcon_proper_impp .
  Definition expr_deep : Set := expr_deep .
  Definition impp_deep : (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : expr_deep := emp_deep .
  Definition varp_deep : (nat -> expr_deep) := varp_deep .
  Definition var_pos : (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition cancel_same : (tree_pos -> tree_pos -> Prop) := cancel_same .
  Definition restore : (tree_pos -> tree_pos -> expr) := restore .
  Definition sepcon_assoc1 : (forall x y z : expr, provable (impp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z))) := sepcon_assoc1 .
  Definition sepcon_mono : (forall x1 x2 y1 y2 : expr, provable (impp x1 x2) -> provable (impp y1 y2) -> provable (impp (sepcon x1 y1) (sepcon x2 y2))) := sepcon_mono .
  Existing Instance sepcon_proper_impp .
End LogicTheorem.

(*Require Logic.PropositionalLogic.DeepEmbedded.Solver.
Module IPSolver (Names: LanguageSig).
  Import Names.
  Ltac ip_solve :=
    change expr with Base.expr;
    change provable with Base.provable;
    change impp with Syntax.impp;
    change andp with Syntax.andp;
    intros; Solver.SolverSound.ipSolver.
End IPSolver.*)
