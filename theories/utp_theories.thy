(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_theories.thy                                                     *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Meta-theory for UTP Theories \<close>

theory utp_theories
imports
  "UTP1-Designs.utp_designs"
  "UTP1-Reactive.utp_reactive"
  "UTP1-Reactive-Designs.utp_rea_designs"
  "UTP1-Time.utp_time_rel"
  "UTP1-Circus.utp_circus"
  utp_cml
begin recall_syntax end