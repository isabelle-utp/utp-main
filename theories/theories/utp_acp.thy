(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* ACP Processes *}

theory utp_acp
imports 
  utp_designs
  utp_theory
  utp_reactive
begin

definition ACP1 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"ACP1 P = `P \<and> (($tr =$tr\<acute>) \<Rightarrow> $wait)` "

definition \<delta> :: "'a WF_PREDICATE" where
"\<delta> = `R3($tr =$tr\<acute> \<and> ($wait)\<acute>)`"

lemma \<delta>_is_R1 : "`R1(\<delta>)` = \<delta>" sorry
lemma \<delta>_is_R2 : "`R2(\<delta>)` = \<delta>" sorry
lemma \<delta>_is_R3 : "`R3(\<delta>)` = \<delta>" by (simp add: \<delta>_def R3_idempotent)

lemma \<delta>_closure : "\<delta> is R" by (simp add:is_healthy_def R_def \<delta>_is_R3 \<delta>_is_R2 \<delta>_is_R1)

definition B :: "'a WF_PREDICATE" where
"B = `($tr =$tr\<acute> \<and> ($wait)\<acute>) \<or> ($tr \<le> $tr\<acute>)`"

definition \<Phi> :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"\<Phi>(P) = `R1(R3(B \<and> P))`"

syntax 
  "_upred_Phi" :: "upred \<Rightarrow> upred" ("\<Phi>'(_')")

translations
  "_upred_Phi P" == "CONST \<Phi> P"

definition doA :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" where
"doA(a) = `\<Phi>(a \<notin> $ref\<acute> \<lhd> $wait \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>))`"

syntax 
  "_upred_doA" :: "uexpr \<Rightarrow> upred" ("do\<A>'(_')")

translations
  "_upred_doA a" == "CONST doA a"

lemma doA_closure : "(do\<A> a) is R" sorry

lemma L1 : "\<delta> ; P = \<delta>"
apply (simp add:\<delta>_def R3_def SkipREA_def)
oops

definition alternative :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_ +\<^bsub>ACP\<^esub> _") where
"(P +\<^bsub>ACP\<^esub> Q) = `(P \<and> Q)\<lhd> \<delta> \<rhd> (P \<or> Q)`"

lemma alternative_closure :
  assumes "(P = `P \<and> ($tr \<le> $tr\<acute>)`) \<and> (Q = `Q \<and> ($tr \<le> $tr\<acute>)`)"
  shows "(P +\<^bsub>ACP\<^esub> Q) is R1"
apply (simp add: alternative_def is_healthy_def R1_def CondR_def)
oops


lemma L2 : "P +\<^bsub>ACP\<^esub> P = P"
oops

lemma L3 : "P +\<^bsub>ACP\<^esub> Q = Q +\<^bsub>ACP\<^esub> P"
oops

lemma L4 : "(P +\<^bsub>ACP\<^esub> Q)+\<^bsub>ACP\<^esub> S = P +\<^bsub>ACP\<^esub> (Q +\<^bsub>ACP\<^esub> S)"
oops

lemma L5 : "\<delta> +\<^bsub>ACP\<^esub> Q = Q"
oops

lemma L6 : "(P +\<^bsub>ACP\<^esub> Q) ; S = (P;S) +\<^bsub>ACP\<^esub> (Q;S)"
oops



end
