(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp.thy                                                              *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section {* Meta-theory for the Standard Core *}

theory utp
imports
  utp_var
  utp_expr
  utp_unrest
  utp_subst
  utp_alphabet
  utp_lift
  utp_pred
  utp_deduct
  utp_rel
  utp_tactics
  utp_hoare
  utp_wp
  utp_theory
  utp_concurrency
  utp_rel_opsem
  utp_local
  utp_event
begin end