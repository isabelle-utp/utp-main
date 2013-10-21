(******************************************************************************)
(* Project: Mechanation of the UTP                                          *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp
imports 
  utp_reactive
  utp_acp
begin

definition CSP1 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP1 P = `P \<or> (\<not> ok \<and> ($tr \<le> $tr\<acute>))`"

abbreviation "CSP2 \<equiv> H2"

definition CSP :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP P = (CSP1 \<circ> CSP2 \<circ> RH) P"

definition Skip :: "'a WF_PREDICATE" where
"Skip = `RH(\<exists> ref. II\<^bsub>rea\<^esub>)`"

declare CSP1_def [eval, evalr, evalrr, evalrx]
declare CSP_def [eval, evalr, evalrr, evalrx]
declare \<delta>_def [eval, evalr, evalrr, evalrx]
declare doA_def [eval, evalr, evalrr, evalrx]
declare \<Phi>_def [eval, evalr, evalrr, evalrx]
declare B_def [eval, evalr, evalrr, evalrx]

lemma CSP1_idempotent: "`CSP1(CSP1(P))` = `CSP1(P)`" 
  by (utp_pred_auto_tac)

lemma CSP2_idempotent: "`CSP2(CSP2(P))` = `CSP2(P)`"
  by (metis H2_idempotent)

lemma CSP1_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> CSP1(P) \<sqsubseteq> CSP1(Q)"
  by (utp_pred_tac)

lemma CSP2_monotonic:
  "P \<sqsubseteq> Q \<Longrightarrow> CSP2(P) \<sqsubseteq> CSP2(Q)"
  by (metis H2_monotone)

lemma CSP1_CSP2_commute: 
  assumes "P \<in> WF_RELATION"
  shows "CSP1 (CSP2 P) = CSP2 (CSP1 P)" 
  apply (simp add: CSP1_def usubst typing defined closure H2_def SemiR_OrP_distr)
  apply (metis (hide_lams, no_types) DesignD_extreme_point_nok(2) H1_H2_commute H1_def H2_def R1_H2_commute R1_def SemiR_FalseP_left TopD_rel_closure utp_pred_simps(15))
done
  
lemma CSP1_false_is_CSP2 : "`(\<not> ok \<and> ($tr \<le> $tr\<acute>)) ; J` = `(\<not> ok \<and> ($tr \<le> $tr\<acute>))`" sorry
lemma \<delta>_and_SKIP_is_false : "`((ok\<acute> \<and> \<delta>) \<and> (\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<and> SKIP) ; J \<or> Q` = `Q`" sorry
lemma aid : "`((\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<and> (\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<and> SKIP) ; J` =`(\<not> ok \<and> ($tr \<le> $tr\<acute>))`" oops
lemma CSP2_form: "`CSP2(P)` = `P\<^sup>f \<or> ok'\<and> P\<^sup>t`"sorry
lemma SkipREA_is_CSP2 : "`CSP2(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"sorry
lemma R3_form : "`R3(P)` = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> (P\<^sub>f)`"sorry

lemma CSP1_R1_commute: "CSP1 (R1 P) = R1 (CSP1 (P))"by utp_pred_auto_tac
lemma CSP1_R2_commute: "CSP1 (R2 P) = R2 (CSP1 (P))"by(simp add:CSP1_def R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
lemma CSP1_R3_commute: "CSP1 (R3 P) = R3 (CSP1 (P))"by utp_pred_auto_tac
lemma CSP2_R1_commute: "CSP2 (R1 P) = R1 (CSP2 (P))"by (simp add:CSP2_form, utp_pred_auto_tac)
lemma CSP2_R2_commute: "CSP2 (R2 P) = R2 (CSP2 (P))"sorry
lemma CSP2_R3_commute: "CSP2 (R3 P) = R3 (CSP2 (P))" 
proof -
have "CSP2 (R3 P) = `($wait \<and> CSP2(II\<^bsub>rea\<^esub>)) \<or> (\<not> $wait \<and> CSP2(P))`" 
  apply(simp add:CSP2_form R3_def CondR_def usubst typing defined closure)
  apply utp_pred_auto_tac
done
thus ?thesis by (simp add:SkipREA_is_CSP2 CondR_def R3_def)
qed

lemma commuting_substitutions : "`R2s(P)[false/wait]` = `R2s(P [false/wait])`" apply(simp add:R2s_def)  sorry

lemma DesignD_form : "`(P \<turnstile> Q)` = `\<not>ok \<or> \<not>P \<or> (ok' \<and> Q)`" by(simp add:DesignD_def, utp_pred_auto_tac)

lemma CSP_Closure : "P is CSP \<longleftrightarrow> `R(\<not> P\<^sup>f\<^sub>f \<turnstile> P\<^sup>t\<^sub>f)` = P"
  sorry

(*
proof -
have "`R(\<not> P\<^sup>f\<^sub>f \<turnstile> P\<^sup>t\<^sub>f)` = `R1(R3( \<not>ok \<or> R2s(P\<^sup>f\<^sub>f) \<or> R2s(ok'\<and>  P\<^sup>t\<^sub>f)))`" apply(simp add:RH_def R2_def R1_idempotent R2_R3_commute DesignD_form R2s_OrP R2s_not_ok)
also have "... = `R1(($wait \<and> II\<^bsub>rea\<^esub>) \<or> (\<not>$wait \<and> \<not>ok) \<or> (\<not>$wait \<and> R2s(P\<^sup>f\<^sub>f)) \<or> (\<not>$wait\<and> ok'\<and> R2s(P\<^sup>t\<^sub>f)))`" sorry (* apply (simp add:R3_def CondR_def R2s_distributes_through_conjunction ok_dash_is_R2s, utp_pred_auto_tac) *)
also have "... = `($wait \<and> \<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> ($tr \<le> $tr\<acute>) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> \<not>ok) \<or> (\<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> R2s(P\<^sup>f\<^sub>f)) \<or> (\<not>$wait\<and> ok'\<and> ($tr \<le> $tr\<acute>) \<and> R2s(P\<^sup>t\<^sub>f))`" by utp_pred_auto_tac
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> \<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> ($tr \<le> $tr\<acute>) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> R2(P\<^sup>f\<^sub>f)) \<or> (\<not>$wait\<and> ok'\<and> ($tr \<le> $tr\<acute>) \<and> R2s(P\<^sup>t\<^sub>f))`" by utp_pred_auto_tac
also have "... = `CSP1(R1(($wait \<and> ( \<not>ok  \<or> (ok'  \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>))) \<or> (\<not>$wait \<and> (R2s(P\<^sup>f\<^sub>f) \<or> (ok'\<and> R2s(P\<^sup>t\<^sub>f))))))`" by utp_pred_auto_tac
also have "... = `CSP1(R1(($wait \<and> ( \<not>ok  \<or> (ok'  \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>))) \<or> (\<not>$wait \<and> (R2s(P\<^sup>f) \<or> (ok'\<and> R2s(P\<^sup>t)))\<^sub>f)))`" by(simp add:usubst typing closure defined, simp add:commuting_substitutions)
also have "... = `CSP1(R1(R3(R2s(P\<^sup>f) \<or> ( ok'\<and> R2s(P\<^sup>t)))))`" by(simp add:R3_form CondR_def SkipREA_def, utp_pred_auto_tac)
also have "... = `CSP1(R1(R3(R2s(P\<^sup>f \<or> ( ok'\<and> P\<^sup>t)))))`" sorry (* by (simp add:R2s_distributes_through_disjunction R2s_distributes_through_conjunction ok_dash_is_R2s) *)
also have "... = `CSP1(R1(R2(R3(CSP2(P)))))`" by(simp add:R2_def R1_idempotent R2s_R3_commute CSP2_form)
also have "... = `CSP(P)`" by (simp add:CSP_def R_def CSP2_R1_commute CSP2_R2_commute CSP2_R3_commute)
finally show ?thesis by(simp add:is_healthy_def)
qed
*)

definition deadlock :: "'a WF_PREDICATE" ("STOP") where
"STOP = `CSP1( ok' \<and> \<delta>)`"

definition prefix :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("_ \<rightarrow> SKIP") where
"a \<rightarrow> SKIP = `CSP1(ok' \<and> do\<A>(a))`"

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

definition PrefixCSP :: 
  "('a EVENT, 'a) WF_PEXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<rightarrow>_") where
"a\<rightarrow>P = `@a ; P`"

definition InputCSP :: "'b::type CHAN \<Rightarrow> ('b \<Rightarrow> 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" where
"InputCSP n P = ExistsShP (\<lambda> v. PrefixCSP (LitPE (PEV n v)) (P v))"

definition OutputCSP :: 
  "'b::type CHAN \<Rightarrow> ('b, 'a) WF_PEXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"OutputCSP n v P = PrefixCSP (EventPE n v) P"

definition ExtChoiceCSP :: 
  "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infixl "\<box>" 65) where
"P \<box> Q = `CSP2((P \<and> Q)\<lhd> STOP \<rhd>(P \<or> Q))`"

definition MergeCSP :: 
  "('a EVENT USET, 'a) WF_PEXPRESSION \<Rightarrow> 
   ('a VAR set * 'a WF_PREDICATE)" where
  "MergeCSP A = ( {okay\<down>\<acute>, wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>}
              , `(($okay\<acute> = $okay\<^bsub>0\<^esub>\<acute> \<and> $okay\<^bsub>1\<^esub>\<acute>) \<and> 
                 ($wait\<acute> = $wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and> 
                 ($ref\<acute> = $ref\<^bsub>0\<^esub>\<acute> \<union> $ref\<^bsub>1\<^esub>\<acute>) \<and> 
                 (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>A \<^esub>($tr\<^bsub>1 \<^esub>- $tr))) ; SKIP`)"

definition HideCSP ::
  "'m WF_PREDICATE \<Rightarrow>
   ('m EVENT USET, 'm) WF_PEXPRESSION \<Rightarrow>
   'm WF_PREDICATE" where
"HideCSP P A = `RH(\<exists> tr\<acute>\<acute>. P[$tr\<acute>\<acute>/tr\<acute>][($ref\<acute> \<union> A)/ref\<acute>] 
                   \<and> $tr\<acute> = $tr ^ (($tr\<acute>\<acute> - $tr)\<upharpoonright>A)) ; SKIP`"

definition GuardCSP ::
  "'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE" where
"GuardCSP g P = P \<lhd> g \<rhd> STOP"

definition ParallelCSP :: 
  "'a WF_PREDICATE \<Rightarrow> 
   ('a EVENT USET, 'a) WF_PEXPRESSION \<Rightarrow> 
   'a WF_PREDICATE \<Rightarrow> 
   'a WF_PREDICATE" (infix "\<parallel>\<^bsub>CSP'(_')\<^esub>" 100) where
"P \<parallel>\<^bsub>CSP(A)\<^esub> Q = P \<parallel>\<^bsub>MergeCSP A\<^esub> Q"

syntax
  "_upred_prefixed"  :: "pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_ -> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> upred \<Rightarrow> upred" ("_?_ -> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_!_ -> _")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixl "[]" 65)
  "_upred_guardcsp"  :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("[_] & _" [0, 100] 100)
  "_upred_parallel"  :: "upred \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" (infixr "||\<^bsub>_\<^esub>" 100)

syntax (xsymbols)
  "_upred_prefixed"  :: "pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_ \<rightarrow> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> upred \<Rightarrow> upred" ("_?_ \<rightarrow> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_!_ \<rightarrow> _")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixl "\<box>" 65)
  "_upred_parallel"  :: "upred \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<parallel>\<^bsub>_\<^esub>" 100)

translations
  "_upred_prefixed a P"   == "CONST PrefixCSP a P"
  "_upred_input n v p"    == "CONST InputCSP n (\<lambda> v. p)"
  "_upred_output n v p"   == "CONST OutputCSP n v p"
  "_upred_extchoice P Q"  == "CONST ExtChoiceCSP P Q"
  "_upred_guardcsp b P"   == "CONST GuardCSP b P"
  "_upred_parallel P A Q" == "CONST ParallelCSP P A Q"

definition InterleaveCSP 
  :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infix "|||\<^bsub>CSP\<^esub>" 100) where
"P |||\<^bsub>CSP\<^esub> Q = ParallelCSP P |{}| Q"

syntax
  "_upred_interleave" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infix "|||" 100)
 
translations
  "_upred_interleave P Q" == "CONST InterleaveCSP P Q"

declare deadlock_def [eval, evalr, evalrr, evalrx]
declare prefix_def [eval, evalr, evalrr, evalrx]
declare SkipCSP_def [eval, evalr, evalrr, evalrx]
declare ChaosCSP_def [eval, evalr, evalrr, evalrx]
declare PrefixCSP_def [eval, evalr, evalrr, evalrx]
declare ExtChoiceCSP_def [eval, evalr, evalrr, evalrx]
declare MergeCSP_def [eval, evalr, evalrr, evalrx]
declare ParallelCSP_def [eval, evalr, evalrr, evalrx]
declare InterleaveCSP_def [eval, evalr, evalrr, evalrx]

lemma Stop_form : "`STOP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> $wait \<and> ok' \<and> \<delta>)`" by (utp_pred_auto_tac)

(*
lemma Prefix_form : "`@a`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> $wait \<and> ok' \<and> $wait\<acute> \<and> (a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait \<and> ok' \<and> \<not> $wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`" 
proof-
have "`@a`=  `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> $wait \<and> ok' \<and> (((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`" by (simp add:prefix_def CSP1_def doA_form R3_def, utp_pred_auto_tac)
also have "... = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> $wait \<and> ok' \<and> $wait\<acute> \<and> (a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait \<and> ok' \<and> \<not> $wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"  by(simp add:CondR_def, utp_pred_auto_tac)
finally show ?thesis ..
qed
*)

lemma Skip_form : "`SKIP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> $wait \<and> ok' \<and> (\<exists> ref .II\<^bsub>rea\<^esub>))`"by (utp_pred_auto_tac)
lemma Chaos_form : "`CHAOS`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait \<and> ($tr \<le> $tr\<acute>))`"by (utp_pred_auto_tac)

lemma STOP_is_R1 : "R1 STOP = STOP "
proof -
have "`R1( STOP )` = `CSP1( ok' \<and> R1(\<delta>))`" by utp_pred_auto_tac
thus ?thesis by(simp add:is_healthy_def R1_\<delta> deadlock_def)
qed

lemma STOP_is_R2 : "R2 STOP = STOP" 
proof - 
have "`R2( STOP )` = `CSP1(R2( ok' \<and> \<delta>))`" by (simp add:deadlock_def CSP1_R2_commute)
also have "... = `CSP1( ok' \<and> R2(\<delta>))`" by(simp add:R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
finally show ?thesis by (simp add:is_healthy_def R2_\<delta> deadlock_def)
qed

lemma STOP_is_R3 : "R3 STOP = STOP" 
proof - 
have "`R3( STOP )` = `CSP1(R3( ok' \<and> \<delta>))`"by (simp add:deadlock_def CSP1_R3_commute)
also have "... = `CSP1(ok' \<and> \<delta>)`" by utp_pred_auto_tac
finally show ?thesis by (simp add:is_healthy_def deadlock_def)
qed

lemma STOP_is_CSP1 : "CSP1 STOP = STOP" by(simp add:deadlock_def CSP1_idempotent)

lemma STOP_is_CSP2 : "CSP2 STOP = STOP" 
proof -
have "CSP2 STOP = `($okay\<acute> \<and> (II\<^bsub>rea\<^esub>[true/okay\<acute>] \<lhd> $wait \<rhd> (($tr = $tr\<acute>) \<and> $wait\<acute>))) \<or> (\<not> $okay \<and> ($tr \<le> $tr\<acute>))`"by(simp add:deadlock_def CSP2_form CSP1_def \<delta>_def R3_def usubst typing defined closure, utp_pred_auto_tac)
also have "... = `CSP1(($okay\<acute> \<and> II\<^bsub>rea\<^esub>[true/okay\<acute>]) \<lhd> $wait \<rhd> ($okay\<acute> \<and> ($tr = $tr\<acute>) \<and> $wait\<acute>))`" by(simp add:CSP1_def, utp_pred_auto_tac)
also have "... = `CSP1(($okay\<acute> \<and> II\<^bsub>rea\<^esub>) \<lhd> $wait \<rhd> ($okay\<acute> \<and> ($tr = $tr\<acute>) \<and> $wait\<acute>))`" 
  sorry
also have "... = `CSP1($okay\<acute> \<and> (II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> (($tr = $tr\<acute>) \<and> $wait\<acute>)))`" by(utp_pred_auto_tac)
finally show ?thesis by(simp add:deadlock_def \<delta>_def R3_def) 
qed

lemma Seq_comp_CSP : 
  assumes "P is CSP \<and> Q is CSP"
  shows "P;Q = `R(\<not>(P\<^sup>f\<^sub>f;R1(true)) \<and> \<not>(P\<^sup>t\<^sub>f;Q\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f;Q\<^sup>t)`"
using assms
proof -
from assms have "P = `R(\<not> P\<^sup>f\<^sub>f \<turnstile> P\<^sup>t\<^sub>f)`" by(metis CSP_Closure)
moreover from assms have "Q = `R(\<not> Q\<^sup>f\<^sub>f \<turnstile> Q\<^sup>t\<^sub>f)`" by(metis CSP_Closure)
ultimately have "P;Q = `R(\<not> P\<^sup>f\<^sub>f \<turnstile> P\<^sup>t\<^sub>f);R(\<not> Q\<^sup>f\<^sub>f \<turnstile> Q\<^sup>t\<^sub>f)`" by metis
thus ?thesis sorry qed

lemma "`a \<rightarrow> SKIP` = `@a`"
oops

lemma L1 : "`CHAOS ; P` = `CHAOS`"
sorry

lemma L2 : "`STOP ; P` = `STOP`"
sorry

lemma L3 : "(P \<sqinter> Q) \<box> S = (P \<box> S) \<sqinter> (Q \<box> s)"
oops

lemma L4 : "P \<sqinter> (Q \<box> S) = (P \<sqinter> Q) \<box> (P \<sqinter> S)"
oops

lemma L5 : 
  assumes "P is CSP1" 
  shows "`P \<box> SKIP` \<sqsubseteq> `SKIP` "
oops

lemma L6sub : "`((a1\<rightarrow>P1) \<box> (a2\<rightarrow>P2)); Q` = `(a1\<rightarrow>(P1;Q)) \<box> (a2\<rightarrow>(P2;Q))`"
oops
end