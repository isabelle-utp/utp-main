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

definition CSP :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP P = (CSP1 \<circ> CSP2 \<circ> R) P"

syntax
  "_upred_CSP1"  :: "upred \<Rightarrow> upred" ("CSP1'(_')")
  "_upred_CSP2"  :: "upred  \<Rightarrow> upred" ("CSP2'(_')")
  "_upred_CSP"  :: "upred  \<Rightarrow> upred" ("CSP'(_')")

translations
  "_upred_CSP1 P"   == "CONST CSP1 P"
  "_upred_CSP2 P"   == "CONST CSP2 P"
  "_upred_CSP P"   == "CONST CSP P"

declare CSP1_def [eval, evalr, evalrr, evalrx]
declare CSP2_def [eval, evalr, evalrr, evalrx]
declare CSP_def [eval, evalr, evalrr, evalrx]
declare J_pred_rea_def [eval, evalr, evalrr, evalrx]
declare \<delta>_def [eval, evalr, evalrr, evalrx]
declare doA_def [eval, evalr, evalrr, evalrx]
declare \<Phi>_def [eval, evalr, evalrr, evalrx]
declare B_def [eval, evalr, evalrr, evalrx]

lemma CSP1_idempotent:
  assumes "P is CSP1"
  shows "CSP1 P = P" 
using assms
by (utp_rel_tac)

lemma CSP2_idempotent:
  assumes "P is CSP2"
  shows "CSP2 P = P" 
using assms
by (utp_rel_tac)

lemma CSP1_monotonic: "[P\<Rightarrow>Q] \<Longrightarrow> [CSP1(P) \<Rightarrow> CSP1(Q)]"by (utp_pred_tac)
lemma CSP2_monotonic: "[P\<Rightarrow>Q] \<Longrightarrow> [CSP2(P) \<Rightarrow> CSP2(Q)]"sorry

lemma CSP1_false_is_CSP2 : "`(\<not> ok \<and> ($tr \<le> $tr\<acute>)) ; J\<^bsub>rea\<^esub>` = `(\<not> ok \<and> ($tr \<le> $tr\<acute>))`" sorry

lemma CSP1_CSP2_commute: "CSP1 (CSP2 P) = CSP2 (CSP1 P)"
proof -
  have "CSP2 (CSP1 P) = `(P \<or> \<not> ok \<and> ($tr \<le> $tr\<acute>)) ; J\<^bsub>rea\<^esub>`" by (utp_rel_tac)
  also have "... = `(P ; J\<^bsub>rea\<^esub>) \<or> (\<not> ok \<and> ($tr \<le> $tr\<acute>)) ; J\<^bsub>rea\<^esub>`" sorry
  ultimately show ?thesis by (simp add: CSP1_false_is_CSP2, utp_rel_tac)
qed

lemma R2_distributes_through_disjunction: "`R2(A \<or> C)` = `R2(A) \<or> R2(C)`" sorry
lemma R1_not_ok : "`(\<not> ok \<and> ($tr \<le> $tr\<acute>))` = `R1(\<not> ok)`"sorry
lemma R2_R1_commute :"`R2(R1(P))` = `R1(R2(P))`"sorry
lemma not_ok_is_R2 : "`R2(\<not> ok)` = `\<not> ok`"sorry

lemma CSP1_R1_commute: "CSP1 (R1 P) = R1 (CSP1 (P))"by (simp add: CSP1_def R1_def, utp_pred_auto_tac)
lemma CSP1_R2_commute: "CSP1 (R2 P) = R2 (CSP1 (P))"by (simp add: CSP1_def R2_distributes_through_disjunction R1_not_ok R2_R1_commute not_ok_is_R2)
lemma CSP1_R3_commute: "CSP1 (R3 P) = R3 (CSP1 (P))"by (simp add: CSP1_def R3_def CondR_def SkipREA_def, utp_pred_auto_tac)
lemma CSP2_R1_commute: "CSP2 (R1 P) = R1 (CSP2 (P))"sorry
lemma CSP2_R2_commute: "CSP2 (R2 P) = R2 (CSP2 (P))"sorry
lemma CSP2_R3_commute: "CSP2 (R3 P) = R3 (CSP2 (P))"sorry
lemma CSP_Closure : "P is CSP \<longleftrightarrow> P = `R(\<not> P\<^sup>f\<^sub>f \<turnstile> P\<^sup>t\<^sub>f)`"sorry 

lemma CSP_Assignment : "`R(x:= e)` is (CSP1 \<circ> CSP2)" sorry

definition assignment :: "('a::type,'m::REACTIVE_SORT) PVAR \<Rightarrow> ('a,'m) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("_:=\<^bsub>CSP\<^esub>_")where
"x:=\<^bsub>CSP\<^esub>e =`R(x:=e)`"

definition deadlock :: "'a WF_PREDICATE" ("STOP") where
"STOP = `CSP1( ok' \<and> \<delta>)`"

definition prefix :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("_\<rightarrow>SKIP") where
"a\<rightarrow>SKIP = `CSP1(ok' \<and> do\<A>(a))`"

definition SkipCSP :: "'a WF_PREDICATE" ("SKIP") where 
"SKIP = `CSP1(R3(ok' \<and> (\<exists> ref . II\<^bsub>rea\<^esub>)))`"

definition ChaosCSP :: "'a WF_PREDICATE" ("CHAOS") where
"CHAOS = `CSP1(R1(R3(true)))`"

syntax
  "_upred_deadlock" :: "upred" ("STOP")
  "_upred_prefix" :: "uexpr \<Rightarrow> upred" ("@_")
  "_upred_skip" :: "upred" ("SKIP")
  "_upred_chaos" :: "upred" ("CHAOS")
  
translations
  "_upred_deadlock" == "CONST deadlock"
  "_upred_prefix a" == "CONST prefix a"
  "_upred_skip" == "CONST SkipCSP"
  "_upred_chaos" == "CONST ChaosCSP"

declare deadlock_def [eval, evalr, evalrr, evalrx]
declare prefix_def [eval, evalr, evalrr, evalrx]
declare SkipCSP_def [eval, evalr, evalrr, evalrx]
declare ChaosCSP_def [eval, evalr, evalrr, evalrx]

lemma Stop_form : "`STOP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> $wait \<and> ok' \<and> \<delta>)`" by (utp_pred_auto_tac)
lemma Prefix_form : "`@a`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub> \<and> ($tr \<le> $tr\<acute>))\<or> (\<not> $wait \<and> ok' \<and> do\<A>(a))`"by (utp_pred_auto_tac)
lemma Skip_form : "`SKIP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> $wait \<and> ok' \<and> (\<exists> ref .II\<^bsub>rea\<^esub>))`"by (utp_pred_auto_tac)
lemma Chaos_form : "`CHAOS`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait \<and> ($tr \<le> $tr\<acute>))`"by (utp_pred_auto_tac)

lemma CSP1_false_zero_seq_comp :
  assumes "P is CSP1"
  shows "`(\<not> ok \<and> ($tr \<le> $tr\<acute>)) ; P` = `(\<not> ok \<and> ($tr \<le> $tr\<acute>))`"
sorry

lemma wait_is_R2 : "`$wait[($tr\<acute> - $tr)/tr\<acute>][\<langle>\<rangle>/tr]` = `$wait`" sorry
lemma not_wait_is_R2 : "`(\<not> $wait)[($tr\<acute> - $tr)/tr\<acute>][\<langle>\<rangle>/tr]` = `\<not> $wait`" sorry
lemma wait_then_P_equals_wait : "`(($wait \<and> II\<^bsub>rea\<^esub>) \<and> ($tr \<le> $tr\<acute>)) ; P` = `(($wait \<and> II\<^bsub>rea\<^esub>) \<and> ($tr \<le> $tr\<acute>))`" sorry

lemma L1 : "`CHAOS ; P` = `CHAOS`"
sorry

lemma L2 : "`STOP ; P` = `STOP`"
sorry

definition prefixed :: "('a EVENT, 'a) WF_PEXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<rightarrow>_") where
"a\<rightarrow>P = `@a ; P`"

definition extchoice :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<box>_") where
"P\<box>Q = `CSP2((P \<and> Q)\<lhd> STOP \<rhd>(P \<or> Q))`"

syntax
  "_upred_prefixed" :: "pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_\<rightarrow>_")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("_\<box>_")
  
translations
  "_upred_prefixed a P" == "CONST prefixed a P"
  "_upred_extchoice P Q" == "CONST extchoice P Q"

lemma "`a \<rightarrow> SKIP` = `@a`"
apply(simp add: prefixed_def )

lemma L3 : "(P \<sqinter> Q) \<box> S = (P \<box> S) \<sqinter> (Q \<box> s)"

oops

lemma L4 : "P \<sqinter> (Q \<box> S) = (P \<sqinter> Q) \<box> (P \<sqinter> S)"
oops

lemma conj_through_dist_2 : "`P \<and> Q \<or> S` = `(P \<and> Q) \<or> (P \<and> S)`" sorry
lemma negation_of_disjunction  : "`\<not>(P \<or> Q)` = `(\<not>P \<and> \<not>Q)`" sorry
lemma \<delta>_and_SKIP_is_false : "`((ok\<acute> \<and> \<delta>) \<and> (\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<and> SKIP) ; J\<^bsub>rea\<^esub> \<or> Q` = `Q`" sorry
lemma aid : "`((\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<and> (\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<and> SKIP) ; J\<^bsub>rea\<^esub>` =`(\<not> ok \<and> ($tr \<le> $tr\<acute>))`" sorry

lemma L5 : 
  assumes "P is CSP1" 
  shows "`P \<box> SKIP` \<sqsubseteq> `SKIP` "
oops

lemma L6sub : "`((a1\<rightarrow>P1) \<box> (a2\<rightarrow>P2)); Q` = `(a1\<rightarrow>(P1;Q)) \<box> (a2\<rightarrow>(P2;Q))`"
oops

end