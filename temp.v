Definition option_Unit : Unit (option worlds) := (fun m => m = None).

Definition option_UJR {J : Join worlds} {SA : @SeparationAlgebra worlds J}: @UnitJoinRelation (option worlds) option_Unit  (@option_Join J).
Proof.
  constructor; intros; hnf in *; subst.
  + destruct n; constructor.
  + inversion H0; tauto.
Qed.

Definition fun_Join (A B: Type) {J_B: Join B}: Join (A -> B) :=
  (fun a b c => forall x, join (a x) (b x) (c x)).

Definition fun_SA
           (A B: Type)
           {Join_B: Join B}
           {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A -> B) (fun_Join A B).

  Definition sum_Unit (A B : Type) : Unit (A + B) := (fun _ => False).

  Definition sum_UJR (A B : Type) {J_A : Join A} {J_B : Join B} : @UnitJoinRelation (A + B) (sum_Unit A B) (sum_Join A B).
  Proof.
    constructor; intros; hnf in *; tauto.
  Qed.

Definition prod_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (A * B) :=
    (fun a b c => join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c)).

Definition prod_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A * B) (prod_Join A B).