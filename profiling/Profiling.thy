(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: profiling.ML                                                         *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 7/12/2016 *)

section \<open> Profiling Tool \<close>

theory Profiling
imports "HOL-Eisbach.Eisbach"
keywords "profile" :: prf_script
begin

ML_file "Profiling.ML"

ML \<open> Profiling.setup_command() \<close>

end