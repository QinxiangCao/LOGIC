Require Import String.
Require Import Config.

Local Open Scope string.

Goal False.
  try
  let LIB := eval compute in local_lib_file in
  idtac "Ltac import_local_lib_tac := idtac ""Require Import""" LIB " ""."" .".

  try
  let IMP := eval compute in implementation_file in
  idtac "Ltac import_implementation_tac := idtac ""Require Import""" IMP " ""."" .".

  try
  let MOD := eval compute in result_module in
  idtac "Ltac set_up_module_name_tac := idtac ""Module ___LogicTheorem___ := """ MOD " ""."" .".

  try
  let PARA := eval compute in instance_para in
  idtac "Ltac def_inline_expr_tac := idtac ""  Parameter Inline expr : forall `{""" PARA """}, Type ."" .";
  idtac "Ltac def_expr_tac := idtac ""  Parameter expr : forall `{""" PARA """}, Type ."" .";
  idtac "Ltac context_expr_tac := idtac ""  Context `{""" PARA """}."" .".
Abort.
