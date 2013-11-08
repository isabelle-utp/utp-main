(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_acp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* ACP Processes *}

theory utp_acp_prime
imports 
  utp_designs
  utp_theory
  utp_reactive_prime
begin

definition ACP1 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"ACP1 P = `P \<and> (($tr\<acute> = $tr) \<Rightarrow> $wait\<acute>)` "

definition \<delta> :: "'a WF_PREDICATE" where
"\<delta> = `R3($tr\<acute> =$tr \<and> $wait\<acute>)`"

definition B_pred :: "'a WF_PREDICATE" where
"B_pred = `($tr\<acute> = $tr \<and> $wait\<acute>) \<or> ($tr < $tr\<acute>)`"

definition \<Phi> :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"\<Phi>(P) = `RH(B_pred \<and> P)`"

definition doA :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" where
"doA(a) = `\<Phi>(a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>))`"

definition alternative :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_ +\<^bsub>ACP\<^esub> _") where
"(P +\<^bsub>ACP\<^esub> Q) = `(P \<and> Q) \<lhd> \<delta> \<rhd> (P \<or> Q)`"

declare ACP1_def [eval,evalr,evalrx,evalp]
declare \<delta>_def [eval,evalr,evalrx,evalp]
declare B_pred_def [eval,evalr,evalrx,evalp]
declare \<Phi>_def [eval,evalr,evalrx,evalp]
declare doA_def [eval,evalr,evalrx,evalp]
declare alternative_def [eval,evalr,evalrx,evalp]

syntax 
  "_upred_doA" :: "uexpr \<Rightarrow> upred" ("do\<A>'(_')")
  "_upred_alternative" :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("_ + _")

translations
  "_upred_doA a" == "CONST doA a"
  "_upred_alternative P Q" == "CONST alternative P Q"

declare \<delta>_def [eval, evalr, evalrr, evalrx]
declare doA_def [eval, evalr, evalrr, evalrx]
declare \<Phi>_def [eval, evalr, evalrr, evalrx]
declare B_pred_def [eval, evalr, evalrr, evalrx]

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
  "`B_pred` \<in> WF_RELATION"
  by (simp add:B_pred_def closure typing defined unrest WF_RELATION_UNREST)

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
  have "R2(ACP1(P)) = `R2(P) \<and> (\<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    apply (simp add:ACP1_def R2_def R2s_def usubst typing defined closure)
    apply (utp_pred_auto_tac)
    done

  also have "... = `R2(P) \<and> ($tr \<le> $tr\<acute>) \<and> (\<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    by (smt AndP_assoc AndP_idem R1_def R2_def)

  also have "... = `R2(P) \<and> ($tr \<le> $tr\<acute>) \<and> (($tr \<le> $tr\<acute>) \<and> \<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    by (metis (hide_lams, no_types) ImpliesP_AndP_pre)

  also have "... = `R2(P) \<and> (($tr \<le> $tr\<acute>) \<and> \<langle>\<rangle> = ($tr\<acute> - $tr) \<Rightarrow> $wait\<acute>)`"
    by (smt AndP_assoc AndP_idem R1_def R2_def)

  also have "... = `R2(P) \<and> (\<langle>\<rangle> = ($tr\<acute> - $tr) \<and> ($tr \<le> $tr\<acute>) \<Rightarrow> $wait\<acute>)`"
    by (smt AndP_assoc AndP_comm)

  also have "... = `R2(P) \<and> (($tr\<acute> = $tr) \<Rightarrow> $wait\<acute>)`"
    by (metis (hide_lams, no_types) EqualP_sym tr_prefix_as_nil)

  finally show ?thesis 
    by (simp add:ACP1_def) 
qed

lemma EvalP_EqualP_ty [evalp]:
  fixes e1 e2 :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>e1\<down> ==\<^sub>p e2\<down>\<rbrakk>b = (\<lbrakk>e1\<rbrakk>\<^sub>*b = \<lbrakk>e2\<rbrakk>\<^sub>*b)"
  apply (auto simp add:eval evale evalp assms)
  apply (drule TypeUSound_InjU_inj[OF assms(1)], simp)
done

lemma ACP1_R3_commute: "ACP1 (R3 P) = R3 (ACP1 P)" 
proof -
  have "ACP1 (R3 P) = `($wait \<and> II \<and> (($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>)) \<or> (\<not>$wait \<and> P \<and> (($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`" 
    by (simp add:ACP1_def R3_def CondR_def, utp_pred_auto_tac)

  also have "... = `($wait \<and> II) \<or> (\<not>$wait \<and> P \<and> (($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`"
    apply(simp add:SkipR_as_SkipRA)
    apply(subst SkipRA_unfold[of "wait\<down>"])
    apply(simp_all add:closure)
    apply(subst SkipRA_unfold[of "wait\<down>"]) back
    apply(simp_all add:closure)
    apply(utp_poly_tac)
    sorry

  also have "... = `R3(P \<and> (($tr\<acute> =$tr) \<Rightarrow> $wait\<acute>))`" 
    by(simp add: R3_def CondR_def)
    
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
  have "`R1(\<delta>)`  = `(II \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait \<rhd> ($tr =$tr\<acute> \<and> $wait\<acute> \<and> ($tr \<le> $tr\<acute>))`" 
    by (simp add:\<delta>_def, utp_pred_auto_tac)
  also have "... = `R1(II) \<lhd> $wait \<rhd> ($tr\<acute> =$tr \<and> $wait\<acute> )`" 
    by utp_poly_auto_tac
  finally show ?thesis 
    by (metis R1_SkipR R3_def \<delta>_def)
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

lemma \<delta>_form: "\<delta> = `($wait \<and> II) \<or> (\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>)`"
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
  have "`ACP1(B_pred \<and>( a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>)))` = `(B_pred \<and>( a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>)))`" 
    apply (simp add:ACP1_def CondR_def)
    apply (utp_poly_auto_tac)
    done
  moreover have "`ACP1(do\<A>(a))` = `RH(ACP1(B_pred \<and>( a \<notin> $ref\<acute> \<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>))))`" 
    by (simp add:doA_def \<Phi>_def RH_def ACP1_R1_commute ACP1_R2_commute ACP1_R3_commute)
  ultimately show ?thesis by(simp add:is_healthy_def doA_def \<Phi>_def)
qed

lemma B_form: "B_pred = `R1($wait\<acute> \<or> ($tr < $tr\<acute>))`"
  apply(utp_poly_auto_tac)
  apply(metis prefixI)
done

lemma doA_form: 
  assumes "TR \<sharp> a"
  shows "`do\<A>(a)` = `R3(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"
proof -
  have "`do\<A>(a)` = `RH(B_pred \<and> ((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`" 
    by (simp add: doA_def \<Phi>_def)

  also have "... = `RH(((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr < $tr\<acute>)))`" 
    proof -
      have 1: "`($tr \<le> $tr\<acute>)` = `($tr < $tr\<acute>) \<or> ($tr\<acute> =  $tr)`"
        by(utp_poly_auto_tac)
      have 2: "`B_pred \<and> $wait\<acute>` = `($tr \<le> $tr\<acute>) \<and> $wait\<acute>`"
        apply(simp add:B_pred_def "1")
        apply(utp_pred_auto_tac)
        done
      have 3: "`B_pred \<and> \<not>$wait\<acute>` = `($tr < $tr\<acute>) \<and> \<not>$wait\<acute>`"
        apply(simp add:B_pred_def)
        apply(utp_pred_auto_tac)
        done
      have "`B_pred \<and> ((a \<notin> $ref\<acute>) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))` = `(B_pred \<and> $wait\<acute> \<and> (a \<notin> $ref\<acute>)) \<or> (B_pred \<and> \<not>$wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`"
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
      apply (utp_poly_auto_tac)
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
      apply (utp_poly_tac)
      apply (rule)
      apply (subgoal_tac "set (drop (length (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>))) (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>))) \<subseteq> dcarrier (EventType :: 'a UTYPE)")
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
    apply(simp_all add:\<delta>_rel_closure assms(3) Healthy_intro R3_\<delta> assms(2) RH_is_R3)
    done
  have 2: "`\<not>$wait \<and> \<delta>` = `\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`" 
    by(utp_pred_auto_tac)
  have "`\<not>$wait \<and> \<delta>;P` = `(\<not>$wait \<and> \<delta>) ; P`"
    apply(subst SemiR_AndP_left_precond)
    apply(simp_all add:\<delta>_rel_closure assms(3))
    apply (utp_pred_auto_tac)
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
  also have "... = `(\<not>$wait \<and> ($tr\<acute> = $tr)) ; ($wait \<and> II)`"
    by (metis AndP_comm R3_wait)
  also have "... = `\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
    apply(subst SemiR_AndP_right_precond)
    apply(subst AndP_rel_closure)
    apply(simp_all add:closure urename)
    apply(metis tr_eq_rel_closure)
    apply(subst AndP_assoc, simp)
    done
  finally have 3: "`\<not>$wait \<and> \<delta>;P` = `\<not>$wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
    ..
  have "`\<delta> ; P` = `R3(\<delta> ; P)`"
    by(metis "1" is_healthy_def)
  also have "... = `($wait \<and> II) \<or> (\<not>$wait \<and> \<delta> ; P)`"
    by (simp add:R3_form)
  also have "... = `R3(($tr\<acute> = $tr) \<and> $wait\<acute>)`"
    by (simp add:"3" R3_def CondR_def)
  finally show ?thesis 
    by(simp add:\<delta>_def)
qed

lemma L2 : "P +\<^bsub>ACP\<^esub> P = P" 
  by(simp add: alternative_def)

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

lemma \<delta>_AndP: 
  assumes "P is ACP1" "P is RH" "P \<in> WF_RELATION"
  shows "`P \<and> \<delta>` = `P \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
proof -
have "`P \<and> \<delta>` = `R3(P) \<and> \<delta>`" by(metis assms is_healthy_def RH_is_R3)
also have "... = `R3(P \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>)`"
  by(utp_poly_auto_tac)
also have "... = `R3(P) \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
  apply(simp add: R3_form SkipR_as_SkipRA)
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(simp_all add:closure)
  apply(subst SkipRA_unfold[of "wait \<down>"])
  apply(simp_all add:closure)
  apply(subst SkipRA_unfold[of "tr \<down>"]) back
  apply(simp_all add:closure)
  apply(subst SkipRA_unfold[of "wait \<down>"]) back
  apply(simp_all add:closure)
  apply(utp_poly_auto_tac)
sorry
finally show ?thesis 
apply(simp)
apply(metis assms is_healthy_def RH_is_R3)
done
qed

lemma NotP_\<delta>_AndP: 
  assumes "P is ACP1" "P is RH" "P \<in> WF_RELATION"
  shows "`P \<and> \<not>\<delta>` = `\<not>$wait \<and> P \<and> ($tr\<acute> \<noteq> $tr)`"
proof -
have "`P \<and> \<not>\<delta>` = `R3(ACP1(P)) \<and> \<not>\<delta>`" 
  by(metis assms is_healthy_def RH_is_R3)
thus ?thesis
  by(utp_poly_auto_tac)
qed

lemma ACP1_SemiR_closure: 
  assumes "P is ACP1" "Q is ACP1" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "P;Q is ACP1"
proof -
  have "ACP1(P);ACP1(Q) = undefined"
    apply(simp add:ACP1_def)
    
    sorry
    thus ?thesis sorry
qed

theorem SemiR_AndP_left_precond_unrest: 
  assumes
    "D\<^sub>2 \<sharp> p"
    "D\<^sub>2 \<sharp> q"
    "D\<^sub>2 \<sharp> c"
    "D\<^sub>1 \<sharp> c"
  shows "(c \<and>\<^sub>p p) ; q = c \<and>\<^sub>p (p ; q)" 
    apply(subst SemiR_algebraic)
    apply(simp_all add: assms closure unrest urename)
    apply(subst RenameP_UNREST [of "D\<^sub>1 \<union> D\<^sub>2"])
    apply(simp_all add:unrest assms closure)
    apply(subst SemiR_algebraic)
    apply(simp_all add: closure assms unrest urename)
    apply(subst ExistsP_AndP_expand2)
    apply(simp_all add:assms)
    apply(subst AndP_assoc[THEN sym])
    apply(simp)
done

theorem SemiR_AndP_right_postcond_unrest: 
  assumes
    "D\<^sub>2 \<sharp> p"
    "D\<^sub>2 \<sharp> q"
    "D\<^sub>2 \<sharp> c"
    "D\<^sub>0 \<sharp> c"
  shows "p ; (q \<and>\<^sub>p c) = (p ; q) \<and>\<^sub>p c" 
    apply(subst SemiR_algebraic)
    apply(simp_all add: assms closure unrest urename)
    apply(subst RenameP_UNREST [of "D\<^sub>0 \<union> D\<^sub>2"]) back back
    apply(simp_all add:unrest assms closure)
    apply(subst SemiR_algebraic)
    apply(simp_all add: closure assms unrest urename)
    apply(subst ExistsP_AndP_expand1)
    apply(simp_all add:assms)
    apply(subst AndP_assoc[THEN sym])
    apply(simp)
    done

lemma UNREST_SubstP_simple [unrest]: 
  fixes P :: "'a WF_PREDICATE"
  assumes "vs \<sharp> v" "vs - {x} \<sharp> P" "v \<rhd>\<^sub>e x"
  shows "vs \<sharp> P[v/\<^sub>px]"
  using assms
  apply (auto simp add:UNREST_def SubstP.rep_eq)
  apply (utp_pred_tac)
done

lemma [simp]: 
  "x\<acute>\<acute>\<acute> \<notin> D\<^sub>0"
  "x\<acute>\<acute>\<acute> \<notin> D\<^sub>1"
  "x\<acute>\<acute>\<acute> \<notin> D\<^sub>2"
  by (auto, metis dash_DASHED_TWICE_elim dash_eq_undash_contra1 undash_dash)

lemma prefix_antisym:
  fixes xs ys :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" 
  shows "`($xs \<le> $ys) \<and> ($ys \<le> $xs)` = `$xs = $ys`"
  using assms 
    apply (utp_poly_tac)
    apply (metis prefix_order.eq_iff)
done

lemma tr_eq_SemiR:
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R1" "Q is R1" 
  shows "`P;Q \<and> ($tr\<acute> = $tr)` = `(P \<and> ($tr\<acute> = $tr));(Q \<and> ($tr\<acute> = $tr))`"
proof - 
  have "`P;Q \<and> ($tr\<acute> = $tr)` = `R1(P);R1(Q) \<and> ($tr\<acute> = $tr)`"
    by(metis assms is_healthy_def)
  also have "... = `(\<exists> tr\<acute>\<acute>\<acute> . ($tr \<le> $tr\<acute>\<acute>\<acute>) \<and> (P[$tr\<acute>\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>\<acute>/tr]) \<and> ($tr\<acute>\<acute>\<acute> \<le> $tr) \<and> ($tr\<acute> = $tr))`"
  proof -
    have "`($tr\<acute>\<acute>\<acute> \<le> $tr\<acute>) \<and> ($tr\<acute> = $tr)` = (`($tr\<acute>\<acute>\<acute> \<le> $tr) \<and> ($tr\<acute> = $tr)` :: 'a WF_PREDICATE)"
     by (utp_poly_auto_tac)
    thus ?thesis 
      apply(subst SemiR_extract_variable_ty[of _ _ "tr "])
      apply(simp_all add:closure unrest assms typing)
      apply(simp add:R1_def usubst typing defined closure)
      apply(subst SemiR_AndP_right_postcond_unrest)
      apply(simp_all add:assms unrest typing defined closure erasure)
      apply(subst AndP_comm) 
      apply(subst SemiR_AndP_left_precond_unrest)
      apply(simp_all add:assms unrest typing defined closure erasure)
      apply(subst ExistsP_AndP_expand1)
      apply(simp add:unrest)
      apply(subst AndP_assoc[THEN sym])  back    
      apply(subst AndP_assoc[THEN sym])   
      apply(simp)
  done
  qed
  also have "... = `(\<exists> tr\<acute>\<acute>\<acute>. ($tr = $tr\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr\<acute>\<acute>\<acute>) \<and> P[($tr\<acute>\<acute>\<acute>)/tr\<acute>] ; Q[($tr\<acute>\<acute>\<acute>)/tr])` "
  proof - 
    have "`($tr = $tr\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr)` = (`($tr = $tr\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr\<acute>\<acute>\<acute>)` :: 'a WF_PREDICATE)"
     by (utp_poly_auto_tac)
   thus ?thesis
    apply(subst AndP_comm) back
    apply(subst AndP_assoc[THEN sym])
    apply(subst AndP_assoc)
    apply(subst prefix_antisym)
    apply(simp add:typing closure)
    apply(subst AndP_assoc)
    apply(simp add: AndP_assoc[THEN sym])
    done
    qed
  also have "... = `(\<exists> tr\<acute>\<acute>\<acute> . $tr\<acute>\<acute>\<acute> = $tr \<and> P[$tr\<acute>\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>\<acute>/tr] \<and> $tr\<acute> = $tr\<acute>\<acute>\<acute>)`"
    by (metis (hide_lams, mono_tags) AndP_comm EqualP_sym calculation)
  finally show ?thesis
    apply(simp)
    apply(rule sym)
    apply(subst SemiR_extract_variable_ty[of _ _ "tr "])
    apply(simp_all add:closure assms typing tr_eq_rel_closure)
    apply(simp add:usubst typing defined closure)
    apply(subst SemiR_AndP_right_postcond_unrest)
    apply(simp_all add:assms unrest typing defined closure erasure)
    apply(subst AndP_comm) 
    apply(subst SemiR_AndP_left_precond_unrest)
    apply(simp_all add:assms unrest typing defined closure erasure)
    apply(subst AndP_assoc[THEN sym])
    apply(simp)
   done
qed

lemma ACP1_tr_eq: 
  assumes "P \<in> WF_RELATION"
  shows "`ACP1(P) \<and> ($tr\<acute> = $tr)` =`P \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
by(utp_poly_auto_tac)

lemma tr_neq_leq:
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`(P \<and> ($tr \<acute> \<noteq> $tr));(Q \<and> ($tr \<le> $tr \<acute>))` = `((P \<and> ($tr \<acute> \<noteq> $tr));(Q \<and> ($tr \<le> $tr \<acute>))) \<and> ($tr \<acute> \<noteq> $tr)`"
sorry

lemma L6 : 
  assumes "P is ACP1" "P is RH" "P \<in> WF_RELATION"
 "Q is ACP1" "Q is RH" "Q \<in> WF_RELATION"
 "R is ACP1" "R is RH" "R \<in> WF_RELATION"
  shows "(P +\<^bsub>ACP\<^esub> Q) ; R = (P;R) +\<^bsub>ACP\<^esub> (Q;R)"
proof -
  have 1: "`(\<delta> \<and> P \<and> Q) ; R` = `(P \<and> Q \<and> ($tr\<acute> = $tr));($wait \<and> R)`"
    apply(subst AndP_comm[of "\<delta>"])
    apply(subst \<delta>_AndP)
    apply(simp_all add:is_healthy_def ACP1_AndP RH_def R3_AndP R2_AndP R1_AndP)
    apply(metis assms is_healthy_def)
    apply(metis assms is_healthy_def RH_is_R3 RH_is_R2 RH_is_R1) 
    apply(subst AndP_rel_closure)
    apply(simp_all add:assms)
    apply(subst SemiR_AndP_right_precond)
    apply(subst AndP_rel_closure)
    defer 
    apply(subst AndP_rel_closure)
    apply(simp_all add:assms typing closure defined urename AndP_assoc)
    apply (metis tr_eq_rel_closure)

    done
    also have "... = `(P \<and> Q \<and> ($tr\<acute> = $tr));($wait \<and> R3(R))`"
       by(metis assms is_healthy_def RH_is_R3)
    also have "... = `(P \<and> Q \<and> ($tr\<acute> = $tr));($wait \<and> II)`"
       apply(simp add:R3_def CondR_def AndP_OrP_distl)
       by (metis (hide_lams, no_types) AndP_OrP_distl AndP_comm R3_form R3_wait)
    also have "... = `P \<and> Q \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
      apply(subst SemiR_AndP_right_precond)
      apply(subst AndP_rel_closure)
      defer
      apply(subst AndP_rel_closure)
      apply(simp_all add:urename closure typing defined AndP_assoc assms tr_eq_rel_closure)
      done
    finally have 1: "`(\<delta> \<and> P \<and> Q) ; R` = `P \<and> Q \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
      ..
    have "`\<delta> \<and> (P;R) \<and> (Q;R)` = `(P;R) \<and> (Q;R) \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
      apply(subst AndP_comm[of "\<delta>"])
      apply(subst \<delta>_AndP)
      apply (metis (full_types) ACP1_AndP ACP1_SemiR_closure Healthy_intro Healthy_simp assms(1) assms(3) assms(4) assms(6) assms(7) assms(9))
      apply (metis RH_AndP_closure RH_SemiR_closure assms(2) assms(3) assms(5) assms(6) assms(8) assms(9))
      apply (metis AndP_rel_closure SemiR_closure assms(3) assms(6) assms(9))
      apply(rule AndP_assoc[THEN sym])
    done
    also have "... = `((ACP1(P);R3(R)) \<and> ($tr\<acute> = $tr)) \<and> ((ACP1(Q);R3(R)) \<and> ($tr\<acute> = $tr)) \<and> $wait\<acute>`"
      by (smt AndP_assoc AndP_comm AndP_idem assms is_healthy_def RH_is_R3)
    also have "... = `((P \<and> ($tr\<acute> = $tr)  \<and> $wait\<acute>) ; (R3(R) \<and> ($tr\<acute> = $tr)) \<and> (Q \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>) ; (R3(R) \<and> ($tr\<acute> = $tr)) \<and> $wait\<acute>)`"
      apply(subst tr_eq_SemiR)
      apply(simp_all add:assms closure)
      apply(metis is_healthy_def assms RH_is_R1 ACP1_R1_commute[THEN sym])
      apply(metis is_healthy_def assms RH_is_R1 R1_R3_commute)
      apply(subst ACP1_tr_eq)
      apply(simp_all add:assms)
      apply(subst tr_eq_SemiR)
      apply(simp_all add:assms closure)
      apply(metis is_healthy_def assms RH_is_R1 ACP1_R1_commute[THEN sym])
      apply(metis is_healthy_def assms RH_is_R1 R1_R3_commute)
      apply(subst ACP1_tr_eq)
      apply(simp_all add:assms)
      done
    also have "... = `((P \<and> ($tr\<acute> = $tr)) ; ($wait \<and> R3(R) \<and> ($tr\<acute> = $tr)) \<and> (Q \<and> ($tr\<acute> = $tr)) ; ($wait \<and> R3(R) \<and> ($tr\<acute> = $tr)) \<and> $wait\<acute>)`"
      apply(subst SemiR_AndP_right_precond) back back
      apply(simp_all add:typing closure defined assms tr_eq_rel_closure urename)
      apply(subst SemiR_AndP_right_precond) back back back
      apply(simp_all add:typing closure defined assms tr_eq_rel_closure urename AndP_assoc)
      done
    also have "... = `P \<and> Q \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>`"
      apply(simp add: AndP_assoc AndP_comm[of "`$wait`"] R3_wait)
      apply(simp add: AndP_comm[of "`$wait`",THEN sym] AndP_assoc[THEN sym])
      apply(subst SemiR_AndP_right_precond)
      apply(simp_all add:typing closure defined assms urename tr_eq_rel_closure)
      apply(subst SemiR_AndP_right_precond) back
      apply(simp_all add:typing closure defined assms urename tr_eq_rel_closure SkipR_as_SkipRA)
      apply(subst SkipRA_unfold[of "tr \<down>"])
      apply(simp_all add:closure)
      apply(subst SkipRA_unfold[of "tr \<down>"]) back
      apply(simp_all add:closure)
      apply(simp add:erasure typing defined closure AndP_assoc[THEN sym])
      apply(subst AndP_comm) back back back
      apply(subst AndP_comm) back back back back back back back back
      apply(simp add:AndP_assoc)
      apply(subst SkipRA_unfold[of "tr \<down>",THEN sym])
      apply(simp_all add:closure)
      apply(subst SkipRA_unfold[of "tr \<down>",THEN sym])
      apply(simp_all add:closure SkipR_as_SkipRA[THEN sym])
      apply(utp_poly_auto_tac)
      done
    finally have 2: "`(\<delta> \<and> P \<and> Q) ; R` = `\<delta> \<and> (P;R) \<and> (Q;R)`"
      by(simp add:1)
  have A: "`(\<not>\<delta> \<and> P);R` = `\<not>$wait \<and> (P \<and> ($tr\<acute> \<noteq> $tr));R`"
    apply(subst AndP_comm[of "`\<not>\<delta>`"])
    apply(subst NotP_\<delta>_AndP)
    apply(simp_all add:assms)
    apply(subst SemiR_AndP_left_precond)
    apply(simp_all add:assms closure tr_eq_rel_closure)
    done
  have B: "`\<not>\<delta> \<and> (P;R)` =`\<not>$wait \<and> (P;R) \<and> ($tr\<acute> \<noteq> $tr)`"
    apply(subst AndP_comm[of "`\<not>\<delta>`"])
    apply(subst NotP_\<delta>_AndP)
    apply(subst ACP1_SemiR_closure)
    apply(simp_all add:assms closure)
    apply(subst RH_SemiR_closure)
    apply(simp_all add:assms)
    done
  also have "... = `\<not>$wait \<and> ((P \<and> (($tr\<acute> = $tr) \<or> ($tr\<acute> \<noteq> $tr)));R) \<and> ($tr\<acute> \<noteq> $tr)`"
    by (smt AndP_OrP_distl AndP_comm WF_PREDICATE_cases)
  also have "... = `\<not>$wait \<and> (((ACP1(P) \<and> ($tr\<acute> = $tr)) ; R3(R)) \<or> ((P \<and> ($tr\<acute> \<noteq> $tr)) ; R)) \<and>  ($tr\<acute> \<noteq> $tr)`"
    apply(simp add:AndP_OrP_distl SemiR_OrP_distr)
    apply(metis assms is_healthy_def RH_is_R3)
    done
  also have "... = `\<not>$wait \<and> ((P \<and> ($tr\<acute> = $tr)) ; ($wait \<and> R3(R)) \<or> ((P \<and> ($tr\<acute> \<noteq> $tr)) ; R)) \<and> ($tr\<acute> \<noteq> $tr)`" 
    apply(subst ACP1_tr_eq)
    apply(simp add:assms)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined assms tr_eq_rel_closure AndP_assoc[THEN sym] urename)
    done
  also have "... = `\<not>$wait \<and> ((P \<and> ($tr\<acute> \<noteq> $tr)) ; R1(R)) \<and> ($tr\<acute> \<noteq> $tr)`"
    apply(simp add: AndP_comm[of "`$wait`"] R3_wait)
    apply(simp add: AndP_comm[of _ "`$wait`"])
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:typing defined closure assms urename tr_eq_rel_closure AndP_assoc[THEN sym] AndP_OrP_distr)
    apply(subst AndP_comm) back back back
    apply(subst AndP_comm) back
    apply(simp add:AndP_assoc)
    apply(subst AndP_contra[of "`($tr\<acute> = $tr)`"])
    apply(simp add:AndP_assoc[THEN sym])
    apply(metis assms is_healthy_def RH_is_R1)
    done
  also have "... = `\<not>$wait \<and> ((P \<and> ($tr\<acute> \<noteq> $tr)) ; R1(R))`"
    apply(simp add:R1_def)
    apply(subst tr_neq_leq) back
    apply(simp_all add:assms)
    done
  finally have 3: "`(\<not>\<delta> \<and> P);R` = `\<not>\<delta> \<and> (P;R)`" 
    apply(simp add:A)
    apply(metis assms is_healthy_def RH_is_R1)
    done
  have A: "`(\<not>\<delta> \<and> Q);R` = `\<not>$wait \<and> (Q \<and> ($tr\<acute> \<noteq> $tr));R`"
    apply(subst AndP_comm[of "`\<not>\<delta>`"])
    apply(subst NotP_\<delta>_AndP)
    apply(simp_all add:assms)
    apply(subst SemiR_AndP_left_precond)
    apply(simp_all add:assms closure tr_eq_rel_closure)
    done
  have B: "`\<not>\<delta> \<and> (Q;R)` =`\<not>$wait \<and> (Q;R) \<and> ($tr\<acute> \<noteq> $tr)`"
    apply(subst AndP_comm[of "`\<not>\<delta>`"])
    apply(subst NotP_\<delta>_AndP)
    apply(subst ACP1_SemiR_closure)
    apply(simp_all add:assms closure)
    apply(subst RH_SemiR_closure)
    apply(simp_all add:assms)
    done
  also have "... = `\<not>$wait \<and> ((Q \<and> (($tr\<acute> = $tr) \<or> ($tr\<acute> \<noteq> $tr)));R) \<and> ($tr\<acute> \<noteq> $tr)`"
    by (smt AndP_OrP_distl AndP_comm WF_PREDICATE_cases)
  also have "... = `\<not>$wait \<and> (((ACP1(Q) \<and> ($tr\<acute> = $tr)) ; R3(R)) \<or> ((Q \<and> ($tr\<acute> \<noteq> $tr)) ; R)) \<and>  ($tr\<acute> \<noteq> $tr)`"
    apply(simp add:AndP_OrP_distl SemiR_OrP_distr)
    apply(metis assms is_healthy_def RH_is_R3)
    done
  also have "... = `\<not>$wait \<and> ((Q \<and> ($tr\<acute> = $tr)) ; ($wait \<and> R3(R)) \<or> ((Q \<and> ($tr\<acute> \<noteq> $tr)) ; R)) \<and> ($tr\<acute> \<noteq> $tr)`" 
    apply(subst ACP1_tr_eq)
    apply(simp add:assms)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined assms tr_eq_rel_closure AndP_assoc[THEN sym] urename)
    done
  also have "... = `\<not>$wait \<and> ((Q \<and> ($tr\<acute> \<noteq> $tr)) ; R1(R)) \<and> ($tr\<acute> \<noteq> $tr)`"
    apply(simp add: AndP_comm[of "`$wait`"] R3_wait)
    apply(simp add: AndP_comm[of _ "`$wait`"])
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:typing defined closure assms urename tr_eq_rel_closure AndP_assoc[THEN sym] AndP_OrP_distr)
    apply(subst AndP_comm) back back back
    apply(subst AndP_comm) back
    apply(simp add:AndP_assoc)
    apply(subst AndP_contra[of "`($tr\<acute> = $tr)`"])
    apply(simp add:AndP_assoc[THEN sym])
    apply(metis assms is_healthy_def RH_is_R1)
    done
  also have "... = `\<not>$wait \<and> ((Q \<and> ($tr\<acute> \<noteq> $tr)) ; R1(R))`"
    apply(simp add:R1_def)
    apply(subst tr_neq_leq) back
    apply(simp_all add:assms)
    done
  finally have 4: "`(\<not>\<delta> \<and> Q);R` = `\<not>\<delta> \<and> (Q;R)`" 
    apply(simp add:A)
    apply(metis assms is_healthy_def RH_is_R1)
    done
  show ?thesis
    by(simp add:alternative_def CondR_def SemiR_OrP_distr AndP_OrP_distl 2 3 4)
qed
end
