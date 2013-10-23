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
"ACP1 P = `P \<and> (ok \<and> ($tr\<acute> = $tr) \<Rightarrow> $wait\<acute>)` "

definition \<delta> :: "'a WF_PREDICATE" where
"\<delta> = `R3($tr\<acute> =$tr \<and> $wait\<acute>)`"

definition B :: "'a WF_PREDICATE" where
"B = `($tr\<acute> = $tr \<and> $wait\<acute>) \<or> ($tr < $tr\<acute>)`"

definition \<Phi> :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"\<Phi>(P) = `RH(B \<and> P)`"

definition doA :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" where
"doA(a) = `\<Phi>(a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>))`"

definition alternative :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_ +\<^bsub>ACP\<^esub> _") where
"(P +\<^bsub>ACP\<^esub> Q) = `(P \<and> Q) \<lhd> \<delta> \<rhd> (P \<or> Q)`"

declare ACP1_def [eval,evalr,evalrx]
declare \<delta>_def [eval,evalr,evalrx]
declare B_def [eval,evalr,evalrx]
declare \<Phi>_def [eval,evalr,evalrx]
declare doA_def [eval,evalr,evalrx]
declare alternative_def [eval,evalr,evalrx]

syntax 
  "_upred_doA" :: "uexpr \<Rightarrow> upred" ("do\<A>'(_')")
  "_upred_alternative" :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("_ + _")

translations
  "_upred_doA a" == "CONST doA a"
  "_upred_alternative P Q" == "CONST alternative P Q"

declare \<delta>_def [eval, evalr, evalrr, evalrx]
declare doA_def [eval, evalr, evalrr, evalrx]
declare \<Phi>_def [eval, evalr, evalrr, evalrx]
declare B_def [eval, evalr, evalrr, evalrx]

subsection {* Closure Laws *}

lemma ACP1_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> ACP1(P) \<in> WF_RELATION"
  by(simp add:ACP1_def closure typing defined unrest)

lemma \<delta>_rel_closure [closure]:
  "`\<delta>` \<in> WF_RELATION"
  apply(simp add:\<delta>_def)
  apply(subst R3_rel_closure)
  apply(simp_all add:closure typing defined unrest)
  done

lemma B_rel_closure [closure]:
  "`B` \<in> WF_RELATION"
  by (simp add:B_def closure typing defined unrest WF_RELATION_UNREST)

lemma \<Phi>_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> `\<Phi>(P)` \<in> WF_RELATION"
  by(simp add:\<Phi>_def closure)

lemma doA_rel_closure [closure]:
  "NON_REL_VAR \<sharp> a \<Longrightarrow> `doA(a)` \<in> WF_RELATION"
  by (simp add:doA_def closure typing defined unrest WF_RELATION_UNREST)
  
lemma Alternative_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> Q \<in> WF_RELATION \<Longrightarrow> (P +\<^bsub>ACP\<^esub> Q) \<in> WF_RELATION"
  by(simp add:alternative_def closure)

subsection {* ACP1 Laws *}

lemma ACP1_idempotent: "ACP1(ACP1(P)) = ACP1(P)" 
  by (simp add:ACP1_def, utp_pred_tac)

lemma ACP1_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> ACP1(P) \<sqsubseteq> ACP1(Q)" 
  by (simp add:ACP1_def, utp_pred_auto_tac)

lemma ACP1_R1_commute: 
  "ACP1(R1(P)) = R1(ACP1(P))" 
  by (simp add:ACP1_def, utp_pred_auto_tac)

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

  also have "... = `R2(P) \<and> (ok \<and> ($tr\<acute> = $tr) \<Rightarrow> $wait\<acute>)`"
    by (metis (hide_lams, no_types) EqualP_sym tr_prefix_as_nil)

  finally show ?thesis 
    by (simp add:ACP1_def) 
qed

lemma ACP1_R3_commute: "ACP1 (R3 P) = R3 (ACP1 P)" 
proof -
  have "ACP1 (R3 P) = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub> \<and> ( ok \<and> ($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>)) \<or> (\<not>$wait \<and> P \<and> (ok \<and> ($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`" 
    by (simp add:ACP1_def R3_def SkipREA_def CondR_def, utp_pred_auto_tac)

  also have "... = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub> \<and> ( ok \<and> ($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>)) \<or> (\<not>$wait \<and> P \<and> ( ok \<and> ($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`" 
    sorry

  also have "... = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> P \<and> ( ok \<and> ($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`" 
    by (utp_pred_auto_tac)

  also have "... = `($wait \<and> \<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>) \<or> (\<not>$wait \<and> P \<and> ( ok \<and> ($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`" 
    sorry

  also have "... = `R3(P \<and> ( ok \<and> ($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`" 
    by(simp add: R3_def CondR_def SkipREA_def, utp_pred_auto_tac)

  finally show ?thesis by(simp add:ACP1_def)
qed

lemma ACP1_OrP:
  "`ACP1(P \<or> Q)` = `ACP1(P) \<or> ACP1(Q)`"
  by (utp_pred_auto_tac)

lemma ACP1_AndP:
  "`ACP1(P \<and> Q)` = `ACP1(P) \<and> ACP1(Q)`"
  by (utp_pred_auto_tac)

lemma ACP1_CondR:
  "`ACP1(P \<lhd> b \<rhd> Q)` = `ACP1(P) \<lhd> ACP1(b) \<rhd> ACP1(Q)`"
  by (utp_pred_auto_tac)

subsection {* \<delta> laws *}

lemma R1_\<delta> : "`R1(\<delta>)` = `\<delta>`"
proof -
  have "`R1(\<delta>)`  = `(II\<^bsub>rea\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait \<rhd> ($tr =$tr\<acute> \<and> $wait\<acute> \<and> ($tr \<le> $tr\<acute>))`" 
    by (simp add:\<delta>_def, utp_pred_auto_tac)
  also have "... = `R1(II\<^bsub>rea\<^esub>) \<lhd> $wait \<rhd> ($tr\<acute> =$tr \<and> $wait\<acute> )`" 
    by (utp_pred_auto_tac)
  finally show ?thesis 
    by (metis SkipREA_is_R1 R3_def \<delta>_def)
qed

lemma R2_\<delta> : "`R2(\<delta>)` = `\<delta>`" 
proof -
  have "`R2(\<delta>)`= `R3(R2($tr\<acute> = $tr) \<and> $wait\<acute>)`"
    by (simp add:\<delta>_def R2_R3_commute, simp add:R2_def R1_def R2s_def usubst typing closure defined, utp_pred_auto_tac)
  also have "... = `R3(($tr\<acute> = $tr) \<and> $wait\<acute>)`"
    proof -
    have "`R2($tr\<acute> = $tr)` = `($tr\<acute> = $tr)`" by (metis tr_conserved_is_R2)
    thus ?thesis by metis
    qed
  finally show ?thesis by (simp add:\<delta>_def) 
qed

lemma R3_\<delta>: "`R3(\<delta>)` = `\<delta>`" 
  by (simp add: \<delta>_def R3_idempotent)

lemma ACP1_\<delta>: "ACP1(\<delta>) = \<delta>" 
  by (simp add:is_healthy_def \<delta>_def ACP1_R3_commute, simp add:ACP1_def, utp_pred_auto_tac)

lemma \<delta>_form: "\<delta> = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>)`"
  by(simp add: \<delta>_def R3_form) 

subsection {* doA laws *}

lemma doA_is_R1: "`R1(do\<A>(a))` = `do\<A>(a)`"
  by (simp add:doA_def \<Phi>_def RH_def R1_idempotent)

lemma doA_is_R2: "`R2(do\<A>(a))` = `do\<A>(a)`"
  by (simp add:doA_def \<Phi>_def RH_def R1_R2_commute R2_idempotent)

lemma doA_is_R3: "`R3(do\<A>(a))` = `do\<A>(a)`"
  by (simp add:doA_def \<Phi>_def RH_def R2_R3_commute R1_R3_commute R3_idempotent)

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

lemma doA_form: 
  assumes "TR \<sharp> a"
  shows "`do\<A>(a)` = `R3(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"
proof -
  have "`do\<A>(a)` = `RH(B \<and> ((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`" 
    by (simp add: doA_def \<Phi>_def)

  also have "... = `RH(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>)))`" 
    proof -
      have 1: "`($tr \<le> $tr\<acute>)` = `($tr < $tr\<acute>) \<or> ($tr\<acute> =  $tr)`"
        by(utp_pred_auto_tac)
      have 2: "`B \<and> $wait\<acute>` = `($tr \<le> $tr\<acute>) \<and> $wait\<acute>`"
        apply(simp add:B_def "1")
        apply(utp_pred_auto_tac)
        done
      have 3: "`B \<and> \<not>$wait\<acute>` = `($tr < $tr\<acute>) \<and> \<not>$wait\<acute>`"
        apply(simp add:B_def)
        apply(utp_pred_auto_tac)
        done
      have "`B \<and> ((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))` = `(B \<and> $wait\<acute> \<and> (a \<notin> $ref\<acute>)) \<or> (B \<and> \<not>$wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"
        apply(simp add:CondR_def)
        apply(utp_pred_auto_tac)
        done
      also have "... = `(($tr \<le> $tr\<acute>) \<and> $wait\<acute> \<and> (a \<notin> $ref\<acute>)) \<or> (($tr < $tr\<acute>) \<and> \<not>$wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"
        by (smt "2" "3" AndP_assoc)
      also have "... = `(($tr \<le> $tr\<acute>) \<and> (a \<notin> $ref\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr < $tr\<acute>) \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"
        apply(simp add:CondR_def)
        apply(utp_pred_auto_tac)
        done
      finally show ?thesis
        by (metis AndP_comm)
    qed
  also have "... = `R3(R1(R2s(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>)))))`" 
    by (simp add:RH_def R2_R3_commute R1_R3_commute, simp add:R2_def R1_idempotent)

  also from assms have "... = `R3(R1((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> (\<langle>a\<rangle> = ($tr\<acute> - $tr))))`"
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
    done
  qed

  also have "... = `R3(R1((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ((\<langle>a\<rangle> = ($tr\<acute> - $tr)) \<and> ($tr \<le> $tr\<acute>))))`"
    by (smt R1_CondR R1_def R1_idempotent)

  also from assms have "... = `R3(R1((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
  proof -
    have "`\<langle>a\<rangle> = ($tr\<acute> - $tr) \<and> ($tr \<le> $tr\<acute>)` = `($tr ^ \<langle>a\<rangle>) = $tr\<acute> \<and> ($tr \<le> $tr\<acute>)`"
      apply (utp_pred_tac)
      apply (rule)
      apply (subgoal_tac "set (drop (length (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>))) (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>))) \<subseteq> dcarrier (EventType :: 'a UTYPE)")
      apply (simp add:typing defined closure)
      apply (smt drop_Cons' drop_all drop_append prefixeq_drop self_append_conv2)
      apply (rule subset_trans, rule set_drop_subset, rule DestList_tr'_dcarrier)
    done

    thus ?thesis
      by (metis tr_prefix_app)
  qed

  also have "... = `R3(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr \<le> $tr\<acute>)))`" 
    by (utp_pred_auto_tac)

  finally show ?thesis
    by (metis tr_prefix_app)

qed

subsection {*alternative laws *}

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

lemma alternative_is_ACP1 :
  assumes "P is ACP1" "Q is ACP1"
  shows "(P +\<^bsub>ACP\<^esub> Q) is ACP1"
using assms
  by (simp add:is_healthy_def alternative_def ACP1_CondR ACP1_OrP ACP1_AndP ACP1_\<delta>)

subsection {*ACP laws *}

lemma L1 :
  assumes "P is ACP1" "P is RH" "P \<in> WF_RELATION"
  shows "\<delta> ; P = \<delta>"  
proof -
  have 1: "`\<delta> ; P` is R3"
    apply(subst R3_SemiR_closure)
    apply (metis \<delta>_rel_closure)
    apply (metis assms(3))
    apply (metis Healthy_intro R3_\<delta>)
    apply (metis RH_is_R3 assms(2))
    apply (metis RH_is_R1 assms(2))
    apply (simp)
    done
  have 2: "`\<not>$wait \<and> \<delta>` = `\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`" 
    by(utp_pred_auto_tac)
  have "`\<not>$wait \<and> \<delta>;P` = `(\<not>$wait \<and> \<delta>) ; P`"
    apply(subst SemiR_AndP_left_precond)
    apply (metis \<delta>_rel_closure)
    apply (metis assms(3))
    apply (utp_pred_auto_tac)
    apply (simp)
    done
  also have "... = `(\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>) ; P`" 
    by(subst 2,simp)
  also have "... = `(\<not>$wait \<and> ($tr\<acute> = $tr)) ; ($wait \<and> P)`"
    apply(subst SemiR_AndP_right_precond)
    apply(subst AndP_rel_closure)
    apply(utp_pred_auto_tac)
    apply(metis tr_eq_rel_closure)
    apply(simp_all)
    apply(simp add: assms (3))
    apply(utp_pred_auto_tac)
    apply(simp add: urename closure typing defined )
    apply (metis (hide_lams, mono_tags) AndP_assoc)
done
 also have "... = `(\<not>$wait \<and> ($tr\<acute> = $tr)) ; ($wait \<and> R3(P))`"
    by(metis assms(2) RH_is_R3 is_healthy_def)
  also have "... = `(\<not>$wait \<and> ($tr\<acute> = $tr)) ; ($wait \<and> II\<^bsub>rea\<^esub>)`"
    by (metis AndP_comm R3_wait)
  also have "... = `(\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>) ; II\<^bsub>rea\<^esub>`"
    apply(subst SemiR_AndP_right_precond)
    apply(subst AndP_rel_closure)
    apply(utp_pred_auto_tac)
    apply(metis tr_eq_rel_closure)
    apply(simp_all)
    apply(metis SkipREA_rel_closure)
    apply(utp_pred_auto_tac)
    apply(simp add: urename closure typing defined )
by (metis (hide_lams, mono_tags) AndP_assoc)
  also have "... = `\<not>$wait \<and> (($tr\<acute> = $tr) \<and> $wait\<acute>) ; II\<^bsub>rea\<^esub>`"
    apply(subst SemiR_AndP_left_precond)
    apply(subst AndP_rel_closure)
    apply(metis tr_eq_rel_closure)
    apply(utp_pred_auto_tac)
    apply(simp_all)
    apply(metis SkipREA_rel_closure)
    apply(utp_pred_auto_tac)
    done
  finally have 3: "`\<not>$wait \<and> \<delta>;P` = `\<not>$wait \<and> (($tr\<acute> = $tr) \<and> $wait\<acute>) ; II\<^bsub>rea\<^esub>`"
    ..
  have "`(($tr\<acute> = $tr) \<and> $wait\<acute>) ; II\<^bsub>rea\<^esub>` = `
        (($tr\<acute> = $tr) \<and> $wait\<acute>) ; (ok \<and> II\<^bsub>REL_VAR\<^esub>) \<or>
        (($tr\<acute> = $tr) \<and> $wait\<acute>) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))`" 
    by(simp add:SkipREA_CondR_SkipR CondR_def SemiR_OrP_distl SkipR_as_SkipRA)
  also have "... = `
        (($tr\<acute> = $tr) \<and> $wait\<acute> \<and> ok') ; II\<^bsub>REL_VAR\<^esub> \<or>
        (($tr\<acute> = $tr) \<and> $wait\<acute> \<and> \<not>ok') ; ($tr \<le> $tr\<acute>)`"
    apply(subst SemiR_AndP_right_precond)
    apply(subst AndP_rel_closure)
    apply(metis tr_eq_rel_closure)
    apply(utp_pred_auto_tac)
    apply(simp_all)
    apply (metis SkipR_as_SkipRA SkipR_closure)
    apply(utp_pred_auto_tac)
    apply(subst SemiR_AndP_right_precond)
    apply(subst AndP_rel_closure)
    apply(metis tr_eq_rel_closure)
    apply(utp_pred_auto_tac)
    apply(simp_all)
    apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
    apply(utp_pred_auto_tac)    
    apply(simp add: urename closure typing defined )
    by (metis (hide_lams, no_types) AndP_assoc AndP_comm SemiR_assoc SkipR_as_SkipRA demorgan3 utp_pred_simps(15))
  also have "... = `
        (($tr\<acute> = $tr) \<and> $wait\<acute> \<and> ok')  \<or>
        (($tr\<acute> = $tr) \<and> $wait\<acute> \<and> \<not>ok') ; ($tr \<le> $tr\<acute>)`"
    apply(subst SkipRA_right_unit)
    apply(subst AndP_rel_closure)
    apply (metis tr_eq_rel_closure)
    apply(utp_pred_auto_tac)
    apply(simp_all add:closure unrest typing)
    done
  also have "... = `(($tr\<acute> = $tr) \<and> $wait\<acute> \<and> ok')  \<or> ($tr\<acute> = $tr) ; ($tr \<le> $tr\<acute>)`"
    sorry (*throwing away intermediate data *)
  also have "... = `(($tr\<acute> = $tr) \<and> $wait\<acute> \<and> ok')  \<or> ($tr \<le> $tr\<acute>)`"
    by (metis tr_eq_tr_leq)
  finally have 4: "`(($tr\<acute> = $tr) \<and> $wait\<acute>) ; II\<^bsub>rea\<^esub>` = `($tr \<le> $tr\<acute>)`"
    by(utp_pred_auto_tac)
  have "`\<delta> ; P` = `R3(\<delta> ; P)`"
    by(metis "1" is_healthy_def)
  also have "... = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (\<not>$wait \<and> \<delta> ; P)`"
    by (simp add:R3_form)
  also have "... = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (\<not>$wait \<and> (($tr\<acute> = $tr) \<and> $wait\<acute>) ; II\<^bsub>rea\<^esub>)`"
    by (simp add:"3")
  also have "... = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (\<not>$wait \<and> ($tr \<le> $tr\<acute>))`"
    by (metis "4")
  also have "... = RH true"
    by(simp add:RH_def R2_R3_commute R1_R3_commute, simp add:R2_def R1_idempotent R2s_def usubst typing closure defined R1_def R3_form)
  finally have 5: " \<delta> ; P = RH true " ..
oops

lemma L2 : "P +\<^bsub>ACP\<^esub> P = P" 
  by(simp add: alternative_def, utp_pred_auto_tac)

lemma L3 : "P +\<^bsub>ACP\<^esub> Q = Q +\<^bsub>ACP\<^esub> P"
  by (metis AndP_comm OrP_comm alternative_def) 

lemma L4 : "(P +\<^bsub>ACP\<^esub> Q) +\<^bsub>ACP\<^esub> R = P +\<^bsub>ACP\<^esub> (Q +\<^bsub>ACP\<^esub> R)" 
  proof -
  have "(P +\<^bsub>ACP\<^esub> Q) +\<^bsub>ACP\<^esub> R =`(P \<and> Q \<and> R)  \<lhd> \<delta> \<rhd>  (P \<or> Q \<or> R)`"
    proof-
    have 1: "`(P + Q) \<and>  \<delta>` = `P \<and> Q \<and> \<delta>`" 
      apply(simp add:alternative_def CondR_def) 
      apply (metis AndP_assoc AndP_comm CondR_def CondR_true_cond)
      done
    have 2: "`(P + Q) \<and>  \<not>\<delta>` = `(P \<or> Q) \<and> \<not>\<delta>`" 
      apply(simp add:alternative_def CondR_def) 
      apply (metis AndP_comm CondR_def CondR_false_cond)
      done
    have "(P +\<^bsub>ACP\<^esub> Q) +\<^bsub>ACP\<^esub> R = `((P + Q) \<and> R) \<lhd> \<delta> \<rhd> ((P + Q) \<or> R)` "
     by(simp add: alternative_def)
     also have "... = `((\<delta> \<and> R \<and> (P + Q)) \<or> (\<not> \<delta> \<and> (P + Q)) \<or> (R \<and> \<not> \<delta>))` "
    by(simp add:CondR_def AndP_OrP_distl AndP_comm)
    also have "... = `((\<delta> \<and> R \<and> (P \<and> Q)) \<or> (\<not> \<delta> \<and> (P \<or> Q)) \<or> (R \<and> \<not> \<delta>))` "
    by (smt "1" "2" AndP_assoc AndP_comm)
    also have "... = `(\<delta> \<and> (R \<and> P \<and> Q)) \<or> (\<not> \<delta> \<and> (P \<or> Q \<or> R))` " 
    by (smt AndP_OrP_distl AndP_comm OrP_assoc)
    finally show ?thesis by (metis AndP_assoc AndP_comm CondR_def)
  qed
  moreover have "P +\<^bsub>ACP\<^esub> (Q +\<^bsub>ACP\<^esub> R) =`(P \<and> Q \<and> R)  \<lhd> \<delta> \<rhd>  (P \<or> Q \<or> R)`"
    proof-
    have 3: "`(Q + R) \<and>  \<delta>` = `Q \<and> R \<and> \<delta>`" 
      apply(simp add:alternative_def CondR_def) 
      apply (metis AndP_assoc AndP_comm CondR_def CondR_true_cond)
      done
    have 4: "`(Q + R) \<and>  \<not>\<delta>` = `(Q \<or> R) \<and> \<not>\<delta>`" 
      apply(simp add:alternative_def CondR_def) 
      apply (metis AndP_comm CondR_def CondR_false_cond)
      done
    have "P +\<^bsub>ACP\<^esub> (Q +\<^bsub>ACP\<^esub> R) = `(P \<and> (Q + R)) \<lhd> \<delta> \<rhd> (P \<or> (Q + R))` "
     by(simp add: alternative_def)
     also have "... = `((\<delta> \<and> P \<and> (Q + R)) \<or> (P \<and> \<not> \<delta>) \<or> (\<not> \<delta> \<and> (Q + R)) )` "
    by(simp add:CondR_def AndP_OrP_distl AndP_comm)
    also have "... = `((\<delta> \<and> P \<and> (Q \<and> R))  \<or> (P \<and> \<not> \<delta>) \<or> (\<not> \<delta> \<and> (Q \<or> R)))` "
    by (smt "3" "4" AndP_assoc AndP_comm)
    also have "... = `(\<delta> \<and> (P \<and> Q \<and> R)) \<or> (\<not> \<delta> \<and> (P \<or> Q \<or> R))` " 
    by (smt AndP_OrP_distl AndP_comm OrP_assoc)
    finally show ?thesis by (metis AndP_assoc AndP_comm CondR_def)
  qed
  ultimately show ?thesis ..
qed

lemma L5 : "\<delta> +\<^bsub>ACP\<^esub> Q = Q" 
  by(simp add:alternative_def, utp_pred_auto_tac)

lemma L6 : 
  assumes "S is ACP1" "S is RH" "S \<in> WF_RELATION"
  shows "(P +\<^bsub>ACP\<^esub> Q) ; S = (P;S) +\<^bsub>ACP\<^esub> (Q;S)"
oops
end
