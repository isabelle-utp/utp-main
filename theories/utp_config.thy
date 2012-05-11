(******************************************************************************)
(* Title: utp/utp_config.thy                                                  *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Configuration *}

theory utp_config
imports Main "~~/src/HOL/Library/Countable"
begin

text {* This theory acts as a meta-theory for importing libraries.*}

subsection {* Notations *}

text {* We want to use the colon for type membership in our model. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [50, 51] 50)

subsection {* Isabelle Prover *}

text {* This prevents Isabelle from automatically splitting pairs. *}

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs delSWrapper "split_all_tac")
*}
end
