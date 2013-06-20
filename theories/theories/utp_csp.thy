(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp
imports 
  utp_designs
  utp_theory
  utp_reactive
begin

definition J_pred_rea :: "'VALUE WF_PREDICATE" ("J\<^bsub>rea\<^esub>") where
"J\<^bsub>rea\<^esub> \<equiv> (ok \<Rightarrow>p ok') \<and>p II (REL_VAR - OKAY)"

syntax
  "_upred_J_rea"        :: "upred" ("J\<^bsub>rea\<^esub>")

translations
  "_upred_J_rea"          == "CONST J_pred_rea"

definition CSP1 :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP1 a P = `P \<or> (\<not> ok \<and> (tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>))`"

definition CSP2 :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP2 a P = `P ; J\<^bsub>rea\<^esub>`"

definition \<delta> :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE" where
"\<delta> a = R3 a `((tr\<^bsub>a\<^esub> = tr\<^bsub>a\<^esub>\<acute>) \<and> $wait\<acute>)`"

syntax 
  "_upred_delta" :: "'a UTYPE \<Rightarrow> upred" ("\<delta>\<^bsub>_\<^esub>")

translations
  "_upred_delta a" == "CONST \<delta> a"

definition STOP :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE" ("STOP\<^bsub>CSP'(_')\<^esub>") where
"STOP\<^bsub>CSP(a)\<^esub> = CSP1 a `ok\<acute> \<and> \<delta>\<^bsub>a\<^esub>`"

syntax 
  "_upred_STOP" :: "'a UTYPE \<Rightarrow> upred" ("STOP\<^bsub>CSP'(_')\<^esub>")

translations
  "_upred_STOP a" == "CONST STOP a"

definition B :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE" where
"B a = `(tr\<^bsub>a\<^esub> = tr\<^bsub>a\<^esub>\<acute> \<and> $wait\<acute>) \<or> (tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>) `"

syntax 
  "_upred_B" :: "'a UTYPE \<Rightarrow> upred" ("B\<^bsub>CSP'(_')\<^esub>")

translations
  "_upred_B a" == "CONST B a"

definition \<Phi> :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"\<Phi> a P = R a `B\<^bsub>CSP(a)\<^esub> \<and> P`"

definition doA :: "'a UTYPE \<Rightarrow> 'a WF_EXPRESSION \<Rightarrow> 'a WF_PREDICATE" where
"doA a b = \<Phi> a `((b \<notin> ref\<^bsub>a\<^esub>\<acute>)\<lhd> $wait \<rhd> (tr\<^bsub>a\<^esub>^\<langle>b\<rangle> = tr\<^bsub>a\<^esub>\<acute>))`"

syntax 
  "_upred_B" :: "'a UTYPE \<Rightarrow> 'a WF_EXPRESSION \<Rightarrow> upred" ("doA\<^bsub>CSP'(_')\<^esub>'(_')")

translations
  "_upred_B a b" == "CONST doA a b"

definition prefix :: "'a WF_EXPRESSION \<Rightarrow> 'a UTYPE \<Rightarrow> 'a WF_PREDICATE" ("_\<rightarrow>\<^bsub>CSP'(_')\<^esub>SKIP") where
"a\<rightarrow>\<^bsub>CSP(b)\<^esub>SKIP = CSP1 b `ok\<acute> \<and> doA\<^bsub>CSP(b)\<^esub>(a)`"

definition SkipCSP :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE" ("SKIP\<^bsub>CSP'(_')\<^esub>") where 
"SKIP\<^bsub>CSP(a)\<^esub> = `\<exists> ref a. II\<^bsub>rea(a)\<^esub>`"

definition ChaosCSP :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE" ("CHAOS\<^bsub>CSP'(_')\<^esub>") where
"CHAOS\<^bsub>CSP(a)\<^esub> = R a true"

lemma L1 : "CHAOS\<^bsub>CSP(a)\<^esub> ; P = CHAOS\<^bsub>CSP(a)\<^esub>"
oops

lemma L2 : "STOP\<^bsub>CSP(a)\<^esub> ; P = STOP\<^bsub>CSP(a)\<^esub>"
oops

definition prefixed :: "'a WF_EXPRESSION \<Rightarrow> 'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<rightarrow>\<^bsub>CSP'(_')\<^esub>_") where
"a\<rightarrow>\<^bsub>CSP(b)\<^esub>P = a\<rightarrow>\<^bsub>CSP(b)\<^esub>SKIP ; P"

definition extchoice :: "'a WF_PREDICATE \<Rightarrow> 'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<box>\<^bsub>CSP'(_')\<^esub>_") where
"P\<box>\<^bsub>CSP(a)\<^esub>Q = CSP2 a `((P \<and> Q)\<lhd> ((tr\<^bsub>a\<^esub> = tr\<^bsub>a\<^esub>\<acute>) \<and> $wait\<acute>) \<rhd>(P \<or> Q))`"

lemma L3 : "(P \<sqinter> Q) \<box>\<^bsub>CSP(a)\<^esub> S = (P \<box>\<^bsub>CSP(a)\<^esub> S) \<sqinter> (Q \<box>\<^bsub>CSP(a)\<^esub> s)"
oops

lemma L4 : "P \<sqinter> (Q \<box>\<^bsub>CSP(a)\<^esub> S) = (P \<sqinter> Q) \<box>\<^bsub>CSP(a)\<^esub> (P \<sqinter> S)"
oops

lemma L5 : "P \<box>\<^bsub>CSP(a)\<^esub> SKIP\<^bsub>CSP(a)\<^esub> \<sqsubseteq> SKIP\<^bsub>CSP(a)\<^esub> "
oops

lemma L6sub : "((a1\<rightarrow>\<^bsub>CSP(a)\<^esub>P1) \<box>\<^bsub>CSP(a)\<^esub>  (a2\<rightarrow>\<^bsub>CSP(a)\<^esub>P2)); Q = ((a1\<rightarrow>\<^bsub>CSP(a)\<^esub>P1);Q) \<box>\<^bsub>CSP(a)\<^esub> ((a2\<rightarrow>\<^bsub>CSP(a)\<^esub>P2) ; Q)"
oops

end