(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_theories.thy                                                     *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section {* Meta-theory for UTP Theories *}

theory utp_theories
imports
  "UTP-Designs.utp_designs"
  "UTP-Reactive.utp_reactive"
  "UTP-Reactive-Designs.utp_rea_designs"
  utp_time_rel
  utp_csp
  utp_cml
begin recall_syntax end