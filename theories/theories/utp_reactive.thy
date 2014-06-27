(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster and Samuel Canham, University of York                *)
(******************************************************************************)

header {* Reactive Processes *}

theory utp_reactive
imports 
  utp_theory
  "reactive/utp_reactive_sig"
  "reactive/utp_reactive_lemmas"
  "reactive/utp_reactive_healths"
  "reactive/utp_reactive_laws"
  "reactive/utp_reactive_traces"
begin

(*
subsection {* The theory of Reactive Processes *}

lift_definition REACTIVE :: "'VALUE WF_THEORY" 
is "({vs. vs \<subseteq> REL_VAR \<and> REA \<subseteq> vs}, {R1,R2,R3})"
  by (simp add:WF_THEORY_def IDEMPOTENT_OVER_def R1_idempotent R2_idempotent R3_idempotent)
*)

end