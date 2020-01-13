Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Export Logic.lib.register_typeclass.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.

Inductive P2D_reg: Type :=.
Inductive D2P_reg: Type :=.
Inductive P2D1_reg: Type :=.
Inductive P2E_reg: Type :=.

Ltac pose_proof_SC_instance n :=
  let a := get_nth P2D_reg n in
  match a with
  | fun x: unit => ?T => 
    try pose_proof_instance_as T x
  end.

Ltac pose_proof_AX_instance n :=
  let a := get_nth D2P_reg n in
  match a with
  | fun x: unit => ?T => 
    try pose_proof_instance_as T x
  end.

Ltac pose_proof_ND_instance n :=
  let a := get_nth P2D1_reg n in
  match a with
  | fun x: unit => ?T =>
    try pose_proof_instance_as T x
  end.

Ltac pose_proof_NE_instance n :=
  let a := get_nth P2E_reg n in
  match a with
  | fun x: unit => ?T =>
    try pose_proof_instance_as T x
  end.

Ltac AddSequentCalculus :=
  let AX := fresh "AX" in
  let GammaD := fresh "GammaD" in
  pose proof Provable2Derivable_Normal as AX;
  set (GammaD := Provable2Derivable) in AX;
  clearbody GammaD;
  rec_from_n (0%nat) pose_proof_SC_instance.

Ltac AddAxiomatization :=
  let SC := fresh "SC" in
  let GammaP := fresh "GammaP" in
  pose proof Derivable2Provable_Normal as SC;
  set (GammaP := Derivable2Provable) in SC;
  clearbody GammaP;
  rec_from_n (0%nat) pose_proof_AX_instance.

Ltac AddDeduction :=
  let ND := fresh "ND" in
  let GammaD1 := fresh "GammaD1" in
  pose proof Provable2Derivable1_Normal as ND;
  set (GammaD1 := Provable2Derivable1) in ND;
  clearbody GammaD1;
  rec_from_n (0%nat) pose_proof_ND_instance.

Ltac AddEquiv :=
  let NEL :=fresh "NEL" in
  let GammaL :=fresh "GammaL" in
  pose proof Provable2Equiv_Normal as NEL;
  set (GammaL := Provable2Equiv) in NEL;
  rec_from_n (0%nat) pose_proof_NE_instance.

(*GammaP : Provable L
SC : NormalSequentCalculus L GammaP Gamma
AX : FiniteWitnessedSequentCalculus L Gamma ->
     NormalAxiomatization L GammaP Gamma
minAX : MinimumAxiomatization L GammaP
ipAX : IntuitionisticPropositionalLogic L GammaP

AddSequentCalculus:
GammaD : Derivable L
AX : NormalAxiomatization L Gamma GammaD
SC : NormalSequentCalculus L Gamma GammaD
bSC : BasicSequentCalculus L GammaD
fwSC : FiniteWitnessedSequentCalculus L GammaD
minSC : MinimumSequentCalculus L GammaD
ipSC : IntuitionisticPropositionalSequentCalculus L GammaD*)

Instance reg_Axiomatization2SequentCalculus_SC:
  RegisterClass P2D_reg (fun SC: unit => @Axiomatization2SequentCalculus_SC) 0.
Qed.

Instance reg_Axiomatization2SequentCalculus_bSC:
  RegisterClass P2D_reg (fun bSC: unit => @Axiomatization2SequentCalculus_bSC) 1.
Qed.

Instance reg_Axiomatization2SequentCalculus_fwSC:
  RegisterClass P2D_reg (fun fwSC: unit => @Axiomatization2SequentCalculus_fwSC) 2.
Qed.

Instance reg_Axiomatization2SequentCalculus_minSC:
  RegisterClass P2D_reg (fun minSC: unit => @Axiomatization2SequentCalculus_minSC) 3.
Qed.

Instance reg_SequentCalculus2Axiomatization_AX:
  RegisterClass D2P_reg (fun AX: unit => @SequentCalculus2Axiomatization_AX) 0.
Qed.

Instance reg_SequentCalculus2Axiomatization_minAX:
  RegisterClass D2P_reg (fun minAX: unit => @SequentCalculus2Axiomatization_minAX) 1.
Qed.

Instance reg_Axiomatization2Deduction_minMD:
  RegisterClass P2D1_reg (fun minMD: unit => @Axiomatization2Deduction_minMD) 0.
Qed.

Instance reg_Axiomatization2BasicDeduction:
  RegisterClass P2D1_reg (fun BD: unit => @Axiomatization2BasicDeduction) 1.
Qed.

Instance reg_Axiomatization2LogicEquiv_minME:
  RegisterClass P2E_reg (fun minME: unit => @Axiomatization2LogicEquiv_minME) 0.
Qed.

Instance reg_Axiomatization2BasicLogicEquiv:
  RegisterClass P2E_reg (fun BE: unit => @Axiomatization2BasicLogicEquiv) 1.
Qed.

Section Test_AddD.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimumAxiomatization L GammaP}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma test_AddD: forall (x:expr), |-- x --> x.
Proof.
  AddDeduction.
  Abort.

End Test_AddD.

Section Test_AddE.

Context {L: Language}
        {minL: MinimumLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimumAxiomatization L GammaP}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma test_AddE: forall (x:expr), |-- x --> x.
Proof.
  AddEquiv.
  Abort.

End Test_AddE.

Section Test_AddSC.

Context {L: Language}
        {minL: MinimumLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma provable_impp_refl': forall (x: expr), |-- x --> x.
Proof.
  AddSequentCalculus.
Abort.

End Test_AddSC.

Section Test_AddAX.

Context {L: Language}
        {minL: MinimumLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}.

Local Open Scope logic_base.
Local Open Scope syntax.

Lemma derivable_axiom2': forall Phi (x y z: expr), Phi |-- (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  AddAxiomatization.
Abort.

End Test_AddAX.
