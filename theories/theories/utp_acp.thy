(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_acp.thy                                                          *)
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
"ACP1 P = `P \<and> (ok \<and> ($tr = $tr\<acute>) \<Rightarrow> $wait\<acute>)` "

declare ACP1_def [eval,evalr,evalrx]

lemma ACP1_idempotent: "ACP1(ACP1(P)) = ACP1(P)" 
  by (simp add:ACP1_def, utp_pred_tac)

lemma ACP1_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> ACP1(P) \<sqsubseteq> ACP1(Q)" 
  by (simp add:ACP1_def, utp_pred_auto_tac)

lemma ACP1_R1_commute: 
  "ACP1(R1(P)) = R1(ACP1(P))" 
  by (simp add:ACP1_def, utp_pred_auto_tac)

lemma ImpliesP_AndP_pre:
  "`X \<and> (Y \<Rightarrow> Z)` = `X \<and> ((X \<and> Y) \<Rightarrow> Z)`"
  by (utp_pred_auto_tac)

lemma ACP1_R2_commute: "ACP1(R2(P)) = R2(ACP1(P))" 
proof -
  have "R2(ACP1(P)) = `R2(P) \<and> (ok \<and> \<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    by (simp add:ACP1_def R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)

  also have "... = `R2(P) \<and> ($tr \<le> $tr\<acute>) \<and> (ok \<and> \<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    by (smt AndP_assoc AndP_idem R1_def R2_def)

  also have "... = `R2(P) \<and> ($tr \<le> $tr\<acute>) \<and> (($tr \<le> $tr\<acute>) \<and> ok \<and> \<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    by (metis (hide_lams, no_types) ImpliesP_AndP_pre)

  also have "... = `R2(P) \<and> (($tr \<le> $tr\<acute>) \<and> ok \<and> \<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    by (smt AndP_assoc AndP_idem R1_def R2_def)

  also have "... = `R2(P) \<and> (ok \<and> \<langle>\<rangle> = ($tr\<acute> - $tr) \<and> ($tr \<le> $tr\<acute>) \<Rightarrow> $wait\<acute>)`"
    by (smt AndP_assoc AndP_comm)

  also have "... = `R2(P) \<and> (ok \<and> ($tr = $tr\<acute>) \<Rightarrow> $wait\<acute>)`"
    by (metis (hide_lams, no_types) EqualP_sym tr_prefix_as_nil)

  finally show ?thesis 
    by (simp add:ACP1_def) 
qed

lemma ACP1_R3_commute: "ACP1 (R3 P) = R3 (ACP1 P)" 
proof -
  have "ACP1 (R3 P) = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub> \<and> ( ok \<and> ($tr =$tr\<acute>) \<Rightarrow> $wait\<acute>)) \<or> (\<not>$wait \<and> P \<and> (ok \<and> ($tr =$tr\<acute>) \<Rightarrow> $wait\<acute>))`" 
    by (simp add:ACP1_def R3_def SkipREA_def CondR_def, utp_pred_auto_tac)

  also have "... = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub> \<and> ( ok \<and> ($tr =$tr\<acute>) \<Rightarrow> $wait\<acute>)) \<or> (\<not>$wait \<and> P \<and> ( ok \<and> ($tr =$tr\<acute>) \<Rightarrow> $wait\<acute>))`" 
    by (smt AndP_assoc helper1)

  also have "... = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> P \<and> ( ok \<and> ($tr =$tr\<acute>) \<Rightarrow> $wait\<acute>))`" 
    by (utp_pred_auto_tac)

  also have "... = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> P \<and> ( ok \<and> ($tr =$tr\<acute>) \<Rightarrow> $wait\<acute>))`" 
    by (smt helper1)

  also have "... = `R3(P \<and> ( ok \<and> ($tr =$tr\<acute>) \<Rightarrow> $wait\<acute>))`" 
    by(simp add: R3_def CondR_def SkipREA_def, utp_pred_auto_tac)

  finally show ?thesis by(simp add:ACP1_def)
qed

definition \<delta> :: "'a WF_PREDICATE" where
"\<delta> = `R3($tr =$tr\<acute> \<and> $wait\<acute>)`"

definition B :: "'a WF_PREDICATE" where
"B = `($tr = $tr\<acute> \<and> $wait\<acute>) \<or> ($tr < $tr\<acute>)`"

definition \<Phi> :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"\<Phi>(P) = `RH(B \<and> P)`"

declare \<delta>_def [eval,evalr,evalrx]
declare B_def [eval,evalr,evalrx]
declare \<Phi>_def [eval,evalr,evalrx]

syntax 
  "_upred_Phi" :: "upred \<Rightarrow> upred" ("\<Phi>'(_')")

translations
  "_upred_Phi P" == "CONST \<Phi> P"

definition doA :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" where
"doA(a) = `\<Phi>(a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>))`"

syntax 
  "_upred_doA" :: "uexpr \<Rightarrow> upred" ("do\<A>'(_')")

translations
  "_upred_doA a" == "CONST doA a"

definition alternative :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_ +\<^bsub>ACP\<^esub> _") where
"(P +\<^bsub>ACP\<^esub> Q) = `(P \<and> Q) \<lhd> \<delta> \<rhd> (P \<or> Q)`"

lemma R1_\<delta> : "`R1(\<delta>)` = `\<delta>`"
proof -
  have "`R1(\<delta>)`  = `(II\<^bsub>rea\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait \<rhd> ($tr =$tr\<acute> \<and> $wait\<acute> \<and> ($tr \<le> $tr\<acute>))`" 
    by (simp add:\<delta>_def, utp_pred_auto_tac)
  also have "... = `R1(II\<^bsub>rea\<^esub>) \<lhd> $wait \<rhd> ($tr =$tr\<acute> \<and> $wait\<acute> )`" 
    by (utp_pred_auto_tac)
  finally show ?thesis 
    by (metis SkipREA_is_R1 R3_def \<delta>_def)
qed

lemma R2_\<delta> : "`R2(\<delta>)` = `\<delta>`" 
proof -
  have "`R2(\<delta>)`= `R3(R2($tr = $tr\<acute>) \<and> $wait\<acute>)`"
    by (simp add:\<delta>_def R2_R3_commute, simp add:R2_def R1_def R2s_def usubst typing closure defined, utp_pred_auto_tac)
  thus ?thesis 
    by (simp add: tr_conserved_is_R2 \<delta>_def)
qed

lemma R3_\<delta>: "`R3(\<delta>)` = `\<delta>`" 
  by (simp add: \<delta>_def R3_idempotent)

lemma \<delta>_closure: "\<delta> is RH" 
  by (simp add: is_healthy_def RH_def R3_\<delta> R2_\<delta> R1_\<delta>)

lemma ACP1_\<delta>: "ACP1(\<delta>) = \<delta>" 
  by (simp add:is_healthy_def \<delta>_def ACP1_R3_commute, simp add:ACP1_def, utp_pred_auto_tac)

lemma \<delta>_form: "\<delta> = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> $wait\<acute> \<and>  ((ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> ($tr = $tr\<acute>)))`"
proof - 
  
  have "\<delta> = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ((ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> $wait\<acute> \<and>  ($tr = $tr\<acute>)))`" 
    by (simp add:\<delta>_def R3_def SkipREA_def CondR_def,utp_pred_auto_tac)
  
  also have "... = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> $wait\<acute> \<and> ((ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> ($tr = $tr\<acute>)))`"
    by (simp add:helper1, utp_pred_auto_tac)
  
  finally show ?thesis ..

qed 

lemma doA_is_R1: "`R1(do\<A>(a))` = `do\<A>(a)`"
  by (simp add:doA_def \<Phi>_def RH_def R1_idempotent)

lemma doA_is_R2: "`R2(do\<A>(a))` = `do\<A>(a)`"
  by (simp add:doA_def \<Phi>_def RH_def R1_R2_commute R2_idempotent)

lemma doA_is_R3: "`R3(do\<A>(a))` = `do\<A>(a)`"
  by (simp add:doA_def \<Phi>_def RH_def R2_R3_commute R1_R3_commute R3_idempotent)

lemma doA_closure: "`do\<A>(a)` is RH" 
  by (simp add:is_healthy_def RH_def doA_is_R3 doA_is_R2 doA_is_R1)

lemma doA_is_ACP1: "`do\<A>(a)` is ACP1" 
proof -
  have "`ACP1(B \<and>( a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>)))` = `(B \<and>( a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>)))`" 
    by (simp add:ACP1_def CondR_def, utp_pred_auto_tac)
  moreover have "`ACP1(do\<A>(a))` = `RH(ACP1(B \<and>( a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>))))`" 
    by (simp add:doA_def \<Phi>_def RH_def ACP1_R1_commute ACP1_R2_commute ACP1_R3_commute)
  ultimately show ?thesis by(simp add:is_healthy_def doA_def \<Phi>_def)
qed

lemma B_form: "B = `R1($wait\<acute> \<or> ($tr < $tr\<acute>))`"
  apply (utp_pred_auto_tac)
  apply (metis prefixI)
done

(* lemma a_unrest : "`a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]` = `a`"sorry *)
lemma aider : "`(B \<and> ((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))` = `((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>))`"
  by (simp add:B_form, utp_pred_auto_tac)

(*
lemma aider2 : "`R2s(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>)))` = `(a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
proof-
have "`R2s(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>)))` = `((a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<notin> $ref\<acute>) \<and> (\<langle>\<rangle> \<le> $tr\<acute> - $tr)) \<lhd> $wait\<acute> \<rhd> (\<langle>\<rangle> ^ \<langle>a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]\<rangle> = ($tr\<acute> - $tr) \<and> (\<langle>\<rangle> < $tr\<acute> - $tr))`" by(simp add:R2s_def usubst typing closure defined)
also have "... = `((a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<notin> $ref\<acute>)) \<lhd> $wait\<acute> \<rhd> (\<langle>a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]\<rangle> = ($tr\<acute> - $tr) \<and> (\<langle>\<rangle> < ($tr\<acute> - $tr)))`" by(utp_pred_auto_tac)
finally show ?thesis 
  apply (utp_pred_tac)
sorry qed
*)

lemma nil_prefixeq [simp]:
  "`\<langle>\<rangle> \<le> x` = `true`"
  by (utp_pred_auto_tac)

lemma nil_append [simp]:
  "|\<langle>\<rangle> ^ x| = |x|"
  by (auto simp add:evalp)

lemma SubstP_VarP_single_UNREST [usubst]:
  "\<lbrakk> {x\<down>} \<sharp> v; e \<rhd>\<^sub>* x \<rbrakk> \<Longrightarrow> v[e/\<^sub>*x] = v"
  apply (simp add:evalp unrest UNREST_PEXPR_def)
  apply (metis (mono_tags) binding_upd_apply pevar_compat_def)
done



lemma UNREST_PEXPR_subset:
  "\<lbrakk> UNREST_PEXPR vs1 v; vs2 \<subseteq> vs1 \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs2 v"
  apply (auto simp add:UNREST_PEXPR_def)
  apply (metis Int_absorb2 binding_override_simps(6))
done

lemma doA_form: 
  assumes "TR \<sharp> a"
  shows "`do\<A>(a)` = `R3(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"
proof -
  have "`do\<A>(a)` = `RH(B \<and> ((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`" 
    by (simp add: doA_def \<Phi>_def)

  also have "... = `RH(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>)))`" 
    by (metis aider)

  also have "... = `R3(R1(R2s(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>)))))`" 
    by (simp add:RH_def R2_R3_commute R1_R3_commute, simp add:R2_def R1_idempotent)

  also from assms have "... = `R3(R1((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
  proof -
    have "`(($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>))` = `($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
      apply (utp_pred_auto_tac)
      apply (metis prefixI')
    done

    with assms show ?thesis
      apply (simp)
      apply (subgoal_tac "{tr\<down>} \<sharp> a")
      apply (subgoal_tac "{tr\<down>\<acute>} \<sharp> a")
      apply (simp add:R2s_def usubst typing defined closure unrest)
      apply (auto intro:UNREST_PEXPR_subset)
    sorry
  qed

  also have "... = `R3(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr \<le> $tr\<acute>)))`" 
    by(utp_pred_auto_tac)

  finally show ?thesis
    by (metis tr_prefix_app)

qed

lemma alternative_is_R1 :
  assumes "P is R1" "Q is R1"
  shows "P +\<^bsub>ACP\<^esub> Q is R1"
  using assms
  by (simp add:alternative_def is_healthy_def R1_CondR R1_AndP R1_OrP)

lemma alternative_is_R2 :
  assumes "P is R2" "Q is R2"
  shows "(P +\<^bsub>ACP\<^esub> Q) is R2"
proof -
  have "R2 (P +\<^bsub>ACP\<^esub> Q) =  `R2(P \<and> Q) \<lhd> R2(\<delta>) \<rhd> R2(P \<or> Q)`" 
    by (simp add:alternative_def R2_CondR_alt)

  also have "... = `(R2(P) \<and> R2(Q)) \<lhd> \<delta> \<rhd> (R2(P) \<or> R2(Q))`" 
    by (simp add: R2_\<delta> R2_AndP R2_OrP)

  also from assms 
  have "... = `(P \<and> Q) \<lhd> \<delta> \<rhd> (P \<or> Q)`" 
    by (simp add:is_healthy_def)

  also have "... = P +\<^bsub>ACP\<^esub> Q"
    by (simp add:alternative_def)

  finally show ?thesis 
    by (simp add:is_healthy_def)
qed

lemma alternative_is_R3 : 
  assumes "P is R3" "Q is R3"
  shows "(P +\<^bsub>ACP\<^esub> Q) is R3"
  using assms
  by (simp add:alternative_def is_healthy_def R3_CondR R3_AndP R3_OrP R3_\<delta>)

lemma alternative_closure : 
  assumes "P is RH" "Q is RH"
  shows "P +\<^bsub>ACP\<^esub> Q is RH"
  by (metis R_intro RH_is_R1 RH_is_R2 RH_is_R3 alternative_is_R1 alternative_is_R2 alternative_is_R3 assms(1) assms(2))

lemma ACP1_OrP:
  "`ACP1(P \<or> Q)` = `ACP1(P) \<or> ACP1(Q)`"
  by (utp_pred_auto_tac)

lemma ACP1_AndP:
  "`ACP1(P \<and> Q)` = `ACP1(P) \<and> ACP1(Q)`"
  by (utp_pred_auto_tac)

lemma ACP1_CondR:
  "`ACP1(P \<lhd> b \<rhd> Q)` = `ACP1(P) \<lhd> ACP1(b) \<rhd> ACP1(Q)`"
  by (utp_pred_auto_tac)

lemma alternative_is_ACP1 :
  assumes "P is ACP1" "Q is ACP1"
  shows "(P +\<^bsub>ACP\<^esub> Q) is ACP1"
using assms
  by (simp add:is_healthy_def alternative_def ACP1_CondR ACP1_OrP ACP1_AndP ACP1_\<delta>)

lemma helper2: "`($wait\<acute> \<and> Q) ; R3(P)` = `$wait\<acute> \<and> Q`" sorry

lemma helper3 : "`(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) ; P` = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>))`"sorry

lemma L1 :
  assumes "P is R3"
  shows "\<delta> ; P = \<delta>"
proof -
  from assms have "\<delta> ; P = `((\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)); P) \<or> ($wait\<acute> \<and> ((ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> \<not>$wait \<and> ($tr = $tr\<acute>))) ; R3(P)`"by(simp add:is_healthy_def \<delta>_form SemiR_OrP_distr)
  also have "... = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait\<acute> \<and>  ((ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> \<not>$wait \<and> ($tr = $tr\<acute>))) ; R3(P)`" by(simp add:helper3)
  also have "... = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait\<acute> \<and>  ((ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> \<not>$wait \<and> ($tr = $tr\<acute>)))`" by(metis helper2)
  also have "... = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> \<not>$wait \<and> $wait\<acute> \<and> ($tr = $tr\<acute>)`" by(simp add:helper1, utp_pred_auto_tac)
  also have "... = \<delta>" by(simp add:\<delta>_def R3_def CondR_def SkipREA_def, utp_pred_auto_tac)
  finally show ?thesis ..
qed

lemma L2 : "P +\<^bsub>ACP\<^esub> P = P" 
  by(simp add: alternative_def, utp_pred_auto_tac)

lemma L3 : "P +\<^bsub>ACP\<^esub> Q = Q +\<^bsub>ACP\<^esub> P"
  by (metis AndP_comm OrP_comm alternative_def) 

lemma L4 : "(P +\<^bsub>ACP\<^esub> Q) +\<^bsub>ACP\<^esub> R = P +\<^bsub>ACP\<^esub> (Q +\<^bsub>ACP\<^esub> R)" 
  oops

lemma L5 : "\<delta> +\<^bsub>ACP\<^esub> Q = Q" by(simp add:alternative_def, utp_pred_auto_tac)

lemma L6 : "(P +\<^bsub>ACP\<^esub> Q) ; S = (P;S) +\<^bsub>ACP\<^esub> (Q;S)"
apply(simp add:alternative_def CondR_def SemiR_OrP_distr)
oops

end
