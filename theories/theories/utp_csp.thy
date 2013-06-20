(******************************************************************************)
(* Project: Mechanation of the UTP                                          *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp
imports 
  utp_designs
  utp_theory
  utp_reactive
  utp_acp
begin

definition J_pred_rea :: "'VALUE WF_PREDICATE" ("J\<^bsub>rea\<^esub>") where
"J\<^bsub>rea\<^esub> \<equiv> `(ok \<Rightarrow> ok') \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`"

abbreviation wait_false :: 
  "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE" ("_\<^sub>f"[150]) where
"p\<^sub>f \<equiv> `p[false/wait]`"

syntax
  "_upred_J_rea"        :: "upred" ("J\<^bsub>rea\<^esub>")
  "_upred_wait_false"   :: "upred \<Rightarrow> upred" ("_\<^sub>f" [1000] 1000)

translations
  "_upred_J_rea"        == "CONST J_pred_rea"
  "_upred_wait_false p" == "CONST wait_false p"

definition CSP1 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP1 P = `P \<or> (\<not> ok \<and> ($tr \<le> $tr\<acute>))`"

definition CSP2 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP2 P = `P ; J\<^bsub>rea\<^esub>`"

syntax
  "_upred_CSP1"  :: "upred \<Rightarrow> upred" ("CSP1'(_')")
  "_upred_CSP2"  :: "upred  \<Rightarrow> upred" ("CSP2'(_')")

translations
  "_upred_CSP1 P"   == "CONST CSP1 P"
  "_upred_CSP2 P"   == "CONST CSP2 P"

lemma CSP_Closure : "P is (CSP1 \<circ> CSP2) \<longleftrightarrow> P = `R(\<not> P\<^sup>f\<^sub>f \<turnstile> P\<^sup>t\<^sub>f)`"
oops 

lemma CSP_Assignment : "`R((x :: 'a VAR):= e)` is (CSP1 \<circ> CSP2)"
oops

definition assignment :: "'a VAR \<Rightarrow> 'a WF_EXPRESSION \<Rightarrow> 'a WF_PREDICATE" ("_:=\<^bsub>CSP\<^esub>_")where
"x:=\<^bsub>CSP\<^esub>e =`R(x:=e)`"

definition deadlock :: "'a WF_PREDICATE" ("STOP") where
"STOP = `CSP1( ok\<acute> \<and> \<delta>)`"

definition prefix :: "'a WF_EXPRESSION \<Rightarrow>  'a WF_PREDICATE" ("_\<rightarrow>SKIP") where
"a\<rightarrow>SKIP = `CSP1(ok\<acute> \<and> doA(a))`"

definition SkipCSP :: "'a WF_PREDICATE" ("SKIP") where 
"SKIP = `R(true \<turnstile> (\<exists> ref . II\<^bsub>rea\<^esub>))`"

definition ChaosCSP :: "'a WF_PREDICATE" ("CHAOS") where
"CHAOS = `R(true)`"

syntax
  "_upred_deadlock" :: "upred" ("STOP")
  "_upred_prefix" :: "uexpr \<Rightarrow> upred" ("_\<rightarrow>SKIP")
  "_upred_skip" :: "upred" ("SKIP")
  "_upred_chaos" :: "upred" ("CHAOS")
  
translations
  "_upred_deadlock" == "CONST deadlock"
  "_upred_prefix a" == "CONST prefix a"
  "_upred_skip" == "CONST SkipCSP"
  "_upred_chaos" == "CONST ChaosCSP"

lemma L1 : "`CHAOS ; P` = `CHAOS`"
oops

lemma L2 : "`STOP ; P` = `STOP`"
oops

definition prefixed :: "'a WF_EXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<rightarrow>_") where
"a\<rightarrow>P = `a\<rightarrow>SKIP ; P`"

definition extchoice :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<box>_") where
"P\<box>Q = `CSP2((P \<and> Q)\<lhd> (($tr = $tr\<acute>) \<and> $wait\<acute>) \<rhd>(P \<or> Q))`"

syntax
  "_upred_prefixed" :: "uexpr \<Rightarrow> upred \<Rightarrow> upred" ("_\<rightarrow>_")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("_\<box>_")
  
translations
  "_upred_prefixed a P" == "CONST prefixed a P"
  "_upred_extchoice P Q" == "CONST extchoice P Q"

lemma L3 : "(P \<sqinter> Q) \<box> S = (P \<box> S) \<sqinter> (Q \<box> s)"
oops

lemma L4 : "P \<sqinter> (Q \<box> S) = (P \<sqinter> Q) \<box> (P \<sqinter> S)"
oops

lemma L5 : "`P \<box> SKIP` \<sqsubseteq> `SKIP` "
oops

lemma L6sub : "`((a1\<rightarrow>P1) \<box> (a2\<rightarrow>P2)); Q` = `(a1\<rightarrow>(P1;Q)) \<box> (a2\<rightarrow>(P2;Q))`"
oops

end