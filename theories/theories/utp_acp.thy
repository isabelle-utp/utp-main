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
"ACP1 P = `P \<and> (($tr = $tr\<acute>) \<Rightarrow> $wait)` "

definition \<delta> :: "'a WF_PREDICATE" where
"\<delta> = `R3($tr = $tr\<acute> \<and> $wait\<acute>)`"

definition B :: "'a WF_PREDICATE" where
"B = `($tr = $tr\<acute> \<and> $wait\<acute>) \<or> ($tr \<le> $tr\<acute>)`"

definition \<Phi> :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"\<Phi>(P) = `R(B \<and> P)`"

syntax 
  "_upred_Phi" :: "upred \<Rightarrow> upred" ("\<Phi>'(_')")

translations
  "_upred_Phi P" == "CONST \<Phi> P"

definition doA :: "'a WF_EXPRESSION \<Rightarrow> 'a WF_PREDICATE" where
"doA(a) = `\<Phi>(a \<notin> $ref\<acute>\<lhd> $wait \<rhd> ($tr^\<langle>a\<rangle> = $tr\<acute>))`"

syntax 
  "_upred_doA" :: "uexpr \<Rightarrow> upred" ("doA'(_')")

translations
  "_upred_doA a" == "CONST doA a"

lemma L1 : "\<delta> ; P = \<delta>"
apply (simp add:\<delta>_def R3_def SkipREA_def)
oops

definition alternative :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_ +\<^bsub>ACP\<^esub> _") where
"(P +\<^bsub>ACP\<^esub> Q) = `(P \<and> Q)\<lhd> \<delta> \<rhd> (P \<or> Q)`"

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
