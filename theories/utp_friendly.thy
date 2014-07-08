(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_friendly.thy                                                     *)
(* Author:Simon Foster and Frank Zeyda, University of York (UK)               *)
(******************************************************************************)

header {* Set up friendly syntax for new users *}

theory utp_friendly
imports utp_base
begin

no_notation (xsymbols)
  Set.member  ("op \<in>") and
  Set.member  ("(_/ \<in> _)" [51, 51] 50) and
  Set.not_member  ("op \<notin>") and
  Set.not_member  ("(_/ \<notin> _)" [51, 51] 50) and
  subset  ("op \<subset>") and
  subset  ("(_/ \<subset> _)" [51, 51] 50) and
  subset_eq  ("op \<subseteq>") and
  subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50)

default_sort type

consts
  cmember :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<in>" 50)
  cnot_member :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<notin>" 50)
  csubset :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<subset>" 50)
  csubseteq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<subseteq>" 50)

definition "set_subset = Set.subset"
definition "set_subset_eq = Set.subset_eq"

declare set_subset_def [simp]
declare set_subset_eq_def [simp]

adhoc_overloading
  cmember fmember

adhoc_overloading
  cmember Set.member

adhoc_overloading
  cnot_member Set.not_member

adhoc_overloading
  cnot_member fnmember

adhoc_overloading
  csubset set_subset

adhoc_overloading
  csubset fsubset

adhoc_overloading
  csubseteq set_subset_eq

adhoc_overloading
  csubseteq fsubset_eq


default_sort VALUE


end
