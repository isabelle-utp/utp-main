(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_refine_laws.thy                                                  *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Basic Refinement Laws *}

theory utp_refine_laws
imports 
  "../core/utp_pred" 
  "../core/utp_rename"
  "../core/utp_expr"
  "../core/utp_rel"
  "../core/utp_lattice"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../parser/utp_pred_parser"
  utp_pred_laws
  utp_rename_laws
  utp_subst_laws
  utp_rel_laws
begin

lemma SeqR_disjunctive2: 
  "disjunctive2 (op ;\<^sub>R)"
  apply (simp add: disjunctive2_def)
  apply (utp_rel_auto_tac)
done

lemma RefineP_taut [simp]: 
  "`p \<sqsubseteq> q` \<longleftrightarrow> p \<sqsubseteq> q"
  by (simp add: less_eq_WF_PREDICATE_def)

theorem RefineP_TrueP_refine [refine]:
  "true \<sqsubseteq> P"
  by (utp_pred_tac)

theorem RefineP_FalseP_refine [refine]:
  "P \<sqsubseteq> false"
  by (utp_pred_tac)

theorem RefineP_by_TrueP_refine [refine]:
  "[P] \<Longrightarrow> P \<sqsubseteq> true"
  by (utp_pred_tac)

theorem RefineP_CondR:
  "P \<sqsubseteq> Q \<lhd> b \<rhd> R \<longleftrightarrow> `P \<sqsubseteq> b \<and> Q` \<and> `P \<sqsubseteq> \<not> b \<and> R`"
  by (utp_pred_auto_tac)

theorem RefineP_CondR_refine [refine]:
  "\<lbrakk> P \<sqsubseteq> `b \<and> Q`; P \<sqsubseteq> `\<not> b \<and> R` \<rbrakk> \<Longrightarrow> P \<sqsubseteq> Q \<lhd> b \<rhd> R"
  by (utp_pred_auto_tac)

theorem RefineP_choice1:
  "(P \<sqinter> Q) \<sqsubseteq> (P :: 'a WF_PREDICATE)"
  by (utp_pred_tac)

theorem RefineP_choice2:
  "(P \<sqinter> Q) \<sqsubseteq> (Q :: 'a WF_PREDICATE)"
  by (utp_pred_tac)

theorem RefineP_seperation:
  "`P \<and> Q` \<sqsubseteq> R \<longleftrightarrow> (P \<sqsubseteq> R) \<and> (Q \<sqsubseteq> R)"
  by (utp_pred_auto_tac)

theorem RefineP_seperation_refine [refine]:
  "\<lbrakk> P \<sqsubseteq> R; Q \<sqsubseteq> R \<rbrakk> \<Longrightarrow> `P \<and> Q` \<sqsubseteq> R"
  by (utp_pred_auto_tac)

theorem SemiR_spec_refine [refine]:
  "Q \<sqsubseteq> `P \<and> R` \<Longrightarrow> `P \<Rightarrow> Q` \<sqsubseteq> R"
  by (utp_pred_tac)

theorem OrP_refine [refine]:
  "\<lbrakk> P \<sqsubseteq> Q; P \<sqsubseteq> R \<rbrakk> \<Longrightarrow> P \<sqsubseteq> `Q \<or> R`"
  by (utp_pred_tac)

theorem ChoiceP_refine [refine]:
  "\<lbrakk> (P :: 'a WF_PREDICATE) \<sqsubseteq> Q; P \<sqsubseteq> R \<rbrakk> \<Longrightarrow> P \<sqsubseteq> `Q \<sqinter> R`"
  by (utp_pred_tac)

theorem AndP_mono_refine [refine]:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow> P1 \<and>\<^sub>p Q1 \<sqsubseteq> P2 \<and>\<^sub>p Q2"
  by (utp_pred_tac)

theorem OrP_mono_refine [refine]:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow> P1 \<or>\<^sub>p Q1 \<sqsubseteq> P2 \<or>\<^sub>p Q2"
  by (utp_pred_tac)

theorem SemiR_mono_refine [refine]:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow> P1 ;\<^sub>R Q1 \<sqsubseteq> P2 ;\<^sub>R Q2"
  by (utp_rel_auto_tac)

theorem SemiR_spec_inter_refine:
  assumes "p \<in> WF_CONDITION" "q \<in> WF_CONDITION" "r \<in> WF_CONDITION"
  shows "`p \<Rightarrow> r\<acute>` \<sqsubseteq> `(p \<Rightarrow> q\<acute>) ; (q \<Rightarrow> r\<acute>)`"
proof -
  from assms have "p ;\<^sub>R true = p" "q ;\<^sub>R true = q" "r ;\<^sub>R true = r"
    by (auto dest:SemiR_TrueP_precond)
  with assms show ?thesis
    by (utp_xrel_auto_tac)
qed

lemma SemiR_AndP_dist_refine:
  "`(P ; R) \<and> (Q ; R)` \<sqsubseteq> `(P \<and> Q) ; R`"
  by (utp_rel_auto_tac)

lemma AndP_refines_1 [refine]:
  "X \<sqsubseteq> Y \<Longrightarrow> X \<sqsubseteq> `Y \<and> Z`"
  by (utp_pred_tac)

lemma AndP_refines_2 [refine]:
  "X \<sqsubseteq> Z \<Longrightarrow> X \<sqsubseteq> `Y \<and> Z`"
  by (utp_pred_tac)

lemma RefineP_equal_right_trans:
  "\<lbrakk> X \<sqsubseteq> Y; Y = Z \<rbrakk> \<Longrightarrow> X \<sqsubseteq> Z"
  by (simp)

lemma RefineP_equal_left_trans:
  "\<lbrakk> X = Y; Y \<sqsubseteq> Z \<rbrakk> \<Longrightarrow> X \<sqsubseteq> Z"
  by (simp)

lemma SkipR_transport_refine [refine]:
  "\<lbrakk> D\<^sub>1 \<sharp> p; q \<sqsubseteq> p\<acute> \<rbrakk> \<Longrightarrow> q \<sqsubseteq> p \<and>\<^sub>p II"
  by (utp_rel_auto_tac)

declare EvalP_SkipR [eval del]
declare EvalP_SkipR_alt [eval]

declare EvalP_SkipRA [eval del]
declare EvalP_SkipRA_alt [eval]

lemma SkipRA_refines_ImpliesP:
  "\<lbrakk> vs1 \<subseteq> D\<^sub>0; - vs1 \<sharp> p; HOMOGENEOUS(vs2); vs1 \<subseteq> vs2 \<rbrakk> 
   \<Longrightarrow> `p \<Rightarrow> p\<acute>` \<sqsubseteq> `II\<^bsub>vs2\<^esub>`"
  apply (utp_pred_tac)
  apply (metis EvalP_binding_equiv binding_equiv_subset in_vars_def le_inf_iff)
done

lemma AssignR_refinement [refine]:
  assumes
    "x \<in> UNDASHED" "v \<rhd>\<^sub>e x" "DASHED \<sharp> v" "q[v/\<^sub>px\<acute>] \<sqsubseteq> p"
  shows "(p \<Rightarrow>\<^sub>p q) \<sqsubseteq> x :=\<^sub>R v"
  using assms
    apply (utp_pred_auto_tac)
    apply (auto simp add:AssignF_upd_rep_eq EvalE_def)
    apply (metis (full_types) binding_upd_simps(2))
done

lemma AssignR_refine_alt [refine]:
  assumes
    "x \<in> UNDASHED" "v \<rhd>\<^sub>e x" "DASHED \<sharp> v" "p[v/\<^sub>px\<acute>]"
  shows "p \<sqsubseteq> x :=\<^sub>R v"
proof -
  from assms have "`true \<Rightarrow> p` \<sqsubseteq> x :=\<^sub>R v"
    apply (rule_tac AssignR_refinement)
    apply (simp_all)
    apply (utp_pred_tac)
  done
   
  thus ?thesis
    by (utp_pred_tac)
qed

lemma AssignRA_refinement [refine]:
  assumes
    "HOMOGENEOUS xs" "xs \<subseteq> REL_VAR" "x \<in> in(xs)"
    "- in(xs) \<sharp> v" "q[v/\<^sub>px\<acute>] \<sqsubseteq> p"
  shows "(p \<Rightarrow>\<^sub>p q) \<sqsubseteq> x :=\<^bsub>xs\<^esub> v"
  using assms
  by (utp_pred_auto_tac, metis binding_upd_simps(2) binding_upd_vcoerce_dash)

lemma AssignRA_refinement_alt:
  assumes "HOMOGENEOUS(xs)" "xs \<subseteq> REL_VAR" "x \<in> in(xs)"
          "- in(xs) \<sharp> p" "- in(xs) \<sharp> v"
  shows "(p[v/\<^sub>px] \<Rightarrow>\<^sub>p p\<acute>) \<sqsubseteq> x :=\<^bsub>xs\<^esub> v"
  using assms
  apply (utp_pred_auto_tac)
  apply (subst EvalP_binding_equiv[of _ _ _ "b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>eb)"])
  apply (simp_all)
  apply (subgoal_tac "x \<in> D\<^sub>0")
  apply (simp add: binding_equiv_def urename)
  apply (metis in_UNDASHED set_rev_mp)
done

end