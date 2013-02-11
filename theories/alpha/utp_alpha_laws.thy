(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_laws.thy                                                   *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Algebraic Laws *}

theory utp_alpha_laws
imports utp_alpha_pred utp_alpha_rel "../tactics/utp_alpha_expr_tac"
begin

theorem CondA_unfold:
"\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> p = \<alpha> q; \<alpha> b \<subseteq>\<^sub>f \<alpha> p \<rbrakk> \<Longrightarrow>
  p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q = (b \<and>\<alpha> p) \<or>\<alpha> (\<not>\<alpha> b \<and>\<alpha> q)"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_idem:
"\<lbrakk>p \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> b \<subseteq>\<^sub>f \<alpha> p\<rbrakk> \<Longrightarrow> 
 p \<triangleleft>\<alpha> b \<alpha>\<triangleright> p = p"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_sym:
"\<lbrakk>p \<in> WF_RELATION; q \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> p = \<alpha> q; \<alpha> b \<subseteq>\<^sub>f \<alpha> p\<rbrakk> \<Longrightarrow> 
  p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q = q \<triangleleft>\<alpha> \<not>\<alpha> b \<alpha>\<triangleright> p"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_assoc:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
    "b \<in> WF_CONDITION" "c \<in> WF_CONDITION" 
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p" "\<alpha> b = \<alpha> c"
  shows "(p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) \<triangleleft>\<alpha> c \<alpha>\<triangleright> r = p \<triangleleft>\<alpha> b \<and>\<alpha> c \<alpha>\<triangleright> (q \<triangleleft>\<alpha> c \<alpha>\<triangleright> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_distr:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
    "b \<in> WF_CONDITION" "c \<in> WF_CONDITION" 
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p" "\<alpha> b = \<alpha> c"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q \<triangleleft>\<alpha> c \<alpha>\<triangleright> r) = (p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) \<triangleleft>\<alpha> c \<alpha>\<triangleright> (p \<triangleleft>\<alpha> b \<alpha>\<triangleright> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_unit:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "\<alpha> p = \<alpha> q"
  shows "p \<triangleleft>\<alpha> true (\<alpha> p) \<alpha>\<triangleright> q = q \<triangleleft>\<alpha> false (\<alpha> p) \<alpha>\<triangleright> p"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done


theorem CondA_conceal:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q \<triangleleft>\<alpha> b \<alpha>\<triangleright> r) = p \<triangleleft>\<alpha> b \<alpha>\<triangleright> r"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_disj:
  assumes
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "b \<in> WF_CONDITION" "c \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> c \<subseteq>\<^sub>f \<alpha> p" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (p \<triangleleft>\<alpha> c \<alpha>\<triangleright> q) = p \<triangleleft>\<alpha> b \<or>\<alpha> c \<alpha>\<triangleright> q"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_refinement:
  assumes
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "p \<sqsubseteq>\<alpha> (q \<triangleleft>\<alpha> b \<alpha>\<triangleright> r) = (p \<sqsubseteq>\<alpha> b \<and>\<alpha> q) \<and>\<alpha> (p \<sqsubseteq>\<alpha> \<not>\<alpha> b \<and>\<alpha> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem AndA_refinement:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r"
  shows "(p \<and>\<alpha> q) \<sqsubseteq>\<alpha> r = (p \<sqsubseteq>\<alpha> r) \<and>\<alpha> (q \<sqsubseteq>\<alpha> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem UNREST_WF_RELATION_DASHED_TWICE[unrest]: 
"r \<in> WF_RELATION \<Longrightarrow> UNREST DASHED_TWICE (\<pi> r)"
  apply (auto simp add:WF_RELATION_def WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def REL_ALPHABET_def)
  apply (rule_tac ?vs1.0="VAR - \<langle>\<alpha> r\<rangle>\<^sub>f" in UNREST_subset)
  apply (auto)
done

theorem UNREST_WF_CONDITION_DASHED[unrest]: 
"r \<in> WF_CONDITION \<Longrightarrow> UNREST DASHED (\<pi> r)"
  by (simp add:WF_CONDITION_def)

theorem SemiA_CondA_distr:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "(p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) ;\<alpha> r = (p ;\<alpha> r) \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q ;\<alpha> r)"
proof -
  from assms have "\<alpha> b \<subseteq>\<^sub>f \<alpha> (p ;\<alpha> r)"
    apply (simp add:WF_CONDITION_def)
    apply (simp add:alphabet in_out_union closure)
  done
    
  moreover hence "(p ;\<alpha> r) \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q ;\<alpha> r) \<in> WF_RELATION"
    by (simp add:closure alphabet assms)

  moreover from assms have "\<alpha> b \<subseteq>\<^sub>f \<alpha> (q ;\<alpha> r)"
    apply (simp add:WF_CONDITION_def)
    apply (simp add:alphabet in_out_union closure)
  done

  ultimately show ?thesis using assms
    apply (utp_alpha_tac)
    apply (rule_tac SemiR_CondR_distr)
    apply (auto intro:SemiR_CondR_distr unrest closure simp add:EvalA_def)
  done
qed

subsection {* Alphabet laws *}

text {* These are needed so the evaluation tactic works correctly *}

theorem SubstA_alphabet_alt [alphabet]:
"\<lbrakk> \<lbrakk>v\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow>  
  \<alpha>(p[v|x]\<alpha>) = (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v
               else \<alpha> p)"
  by (simp add:EvalAE_def alphabet)

theorem SubstAE_alphabet_alt [alphabet]:
"\<lbrakk>v\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x \<Longrightarrow> \<alpha>(f[v|x]\<alpha>\<epsilon>) = (\<alpha> f -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v"
  by (simp add:EvalAE_def alphabet)

subsection {* Substitution Laws *}

lemma SubstA_AndA: "\<lbrakk> \<lbrakk>v\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (p \<and>\<alpha> q)[v|x]\<alpha> = p[v|x]\<alpha> \<and>\<alpha> q[v|x]\<alpha>"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (force)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
done

lemma SubstA_ImpliesA: "\<lbrakk> \<lbrakk>v\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (p \<Rightarrow>\<alpha> q)[v|x]\<alpha> = p[v|x]\<alpha> \<Rightarrow>\<alpha> q[v|x]\<alpha>"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (force)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
done

lemma SubstA_OrA: "\<lbrakk> \<lbrakk>v\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (p \<or>\<alpha> q)[v|x]\<alpha> = p[v|x]\<alpha> \<or>\<alpha> q[v|x]\<alpha>"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (force)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
done

lemma SubstA_no_var [simp]: "\<lbrakk> \<epsilon> v \<rhd>\<^sub>e x ; x \<notin> \<langle>\<alpha> p\<rangle>\<^sub>f; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> 
  \<Longrightarrow> p[v|x]\<alpha> = p"
  apply (utp_alpha_tac)
  apply (simp add:EvalA_SubstA)
  apply (rule SubstP_no_var)
  apply (simp_all)
  apply (metis EvalA_is_SubstP_var)
  apply (auto intro:unrest)
done

lemma SubstA_PROGRAM_ALPHABET [simp]: 
  "\<lbrakk> \<epsilon> v \<rhd>\<^sub>e x ; aux x; PROGRAM_ALPHABET (\<alpha> p); x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> 
  \<Longrightarrow> p[v|x]\<alpha> = p"
  apply (rule SubstA_no_var)
  apply (simp_all)
  apply (simp add:PROGRAM_ALPHABET_def PROGRAM_VARS_def)
  apply (auto)
done

end