Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.micromega.Psatz.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class PropositionalVariables: Type := {
  Var: Type
}.

Inductive expr {Sigma: PropositionalVariables}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | falsep : expr
  | varp : Var -> expr.

Arguments expr Sigma: clear implicits.

Definition negp {Sigma: PropositionalVariables} (x: expr Sigma): expr Sigma :=
  impp x falsep.

Definition iffp {Sigma: PropositionalVariables} (x y: expr Sigma): expr Sigma :=
  andp (impp x y) (impp y x).

Definition truep {Sigma: PropositionalVariables}: expr Sigma :=
  impp falsep falsep.

Instance L {Sigma: PropositionalVariables}: Language :=
  Build_Language (expr Sigma).

Instance minL {Sigma: PropositionalVariables}: MinimumLanguage L :=
  Build_MinimumLanguage L impp.

Instance andpL {Sigma: PropositionalVariables}: AndLanguage L :=
  Build_AndLanguage L andp.

Instance orpL {Sigma: PropositionalVariables}: OrLanguage L :=
  Build_OrLanguage L orp.

Instance falsepL {Sigma: PropositionalVariables}: FalseLanguage L :=
  Build_FalseLanguage L falsep.

Instance negpL {Sigma: PropositionalVariables}: NegLanguage L :=
  Build_NegLanguage L negp.

Instance negpDef {Sigma: PropositionalVariables}: NegDefinition_False_Imp L :=
  FalseImp2Neg_Normal.

Instance iffpL {Sigma: PropositionalVariables}: IffLanguage L :=
  Build_IffLanguage L iffp.

Instance iffpDef {Sigma: PropositionalVariables}: IffDefinition_And_Imp L :=
  AndImp2Iff_Normal.

Instance truepL {Sigma: PropositionalVariables}: TrueLanguage L :=
  Build_TrueLanguage L truep.

Instance truepDef {Sigma: PropositionalVariables}: TrueDefinition_False_Imp L :=
  FalseImp2True_Normal.

Definition rank {Sigma: PropositionalVariables}: expr Sigma -> nat :=
  fix rank (x: expr Sigma): nat :=
    match x with
    | andp y z => 1 + rank y + rank z
    | orp y z => 1 + rank y + rank z
    | impp y z => 1 + rank y + rank z
    | falsep => 0
    | varp p => 0
    end.

Definition formula_countable: forall {Sigma}, Countable Var -> Countable (expr Sigma).
  intros.
  assert (forall n, Countable (sig (fun x: expr Sigma => rank x <= n))).
  + induction n.
    - apply (@bijection_Countable _ (Var + unit)%type); [| solve_Countable].
      apply bijection_sym.
      apply (FBuild_bijection _ _ (fun x =>
               match x with
               | inl p => exist (fun x: expr Sigma => rank x <= 0) (varp p) (le_n 0)
               | inr _ => exist (fun x: expr Sigma => rank x <= 0) falsep (le_n 0)
               end)).
      * hnf; intros.
        destruct a1 as [? | []], a2 as [? | []]; inversion H; auto.
      * hnf; intros.
        destruct b as [[] HH]; try solve [inversion HH].
        1: exists (inr tt); eauto; f_equal; apply proof_irrelevance.
        1: exists (inl v); eauto; f_equal; apply proof_irrelevance.
    - set (s := sig (fun x: expr Sigma => rank x <= n)).
      apply (@injection_Countable _ (s * s + s * s + s * s + unit + Var)%type); [| solve_Countable].

      apply (Build_injection _ _ (fun x y =>
        match y with
        | inl (inl (inl (inl (exist _ y _, exist _ z _)))) => proj1_sig x = andp y z
        | inl (inl (inl (inr (exist _ y _, exist _ z _)))) => proj1_sig x = orp y z
        | inl (inl (inr (exist _ y _, exist _ z _))) => proj1_sig x = impp y z
        | inl (inr _) => proj1_sig x = falsep
        | inr p => proj1_sig x = varp p
        end)).
      * hnf; intros.
        destruct a as [[y z | y z | y z | | p] ?H].
        (* 1 *) simpl in H. assert (rank y <= n) by lia. assert (rank z <= n) by lia.
                exists (inl (inl (inl (inl (exist _ y H0, exist _ z H1))))); auto.
        (* 2 *) simpl in H. assert (rank y <= n) by lia. assert (rank z <= n) by lia.
                exists (inl (inl (inl (inr (exist _ y H0, exist _ z H1))))); auto.
        (* 3 *) simpl in H. assert (rank y <= n) by lia. assert (rank z <= n) by lia.
                exists (inl (inl (inr (exist _ y H0, exist _ z H1)))); auto.
        (* 4 *) exists (inl (inr tt)); auto.
        (* 5 *) exists (inr p); auto.
      * hnf; intros.
        destruct a as [[y z | y z | y z | | p] ?H];
        destruct b1 as [[[[[[y1 ?H] [z1 ?H]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] |] | p1]; try solve [inversion H];
        destruct b2 as [[[[[[y2 ?H] [z2 ?H]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] |] | p2]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) destruct u, u0; auto.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
      * hnf; intros.
        destruct b as [[[[[[y ?H] [z ?H]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] |] | p];
        destruct a1 as [[y1 z1 | y1 z1 | y1 z1 | | p1] ?H]; try solve [inversion H];
        destruct a2 as [[y2 z2 | y2 z2 | y2 z2 | | p2] ?H]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
  + apply (@injection_Countable _ (sigT (fun n => sig (fun x: expr Sigma => rank x <= n)))); [| solve_Countable; auto].
    apply (FBuild_injection _ _ (fun x0 => existT (fun n => sig (fun x => rank x <= n)) (rank x0) (exist (fun x => rank x <= rank x0) x0 (le_n (rank x0))))).
    hnf; intros.
    simpl in H.
    inversion H; auto.
Qed. (* 20 seconds *)

