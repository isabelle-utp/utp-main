theory utp_alphabet_laws
imports utp_alpha_pred utp_alpha_rel
begin

context ALPHA_PRED
begin

theorem CondA_unfold:
"\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> p = \<alpha> q; \<alpha> b \<subseteq> \<alpha> p \<rbrakk> \<Longrightarrow>
  p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q = (b \<and>\<alpha> p) \<or>\<alpha> (\<not>\<alpha> b \<and>\<alpha> q)"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_idem:
"\<lbrakk>p \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> b \<subseteq> \<alpha> p\<rbrakk> \<Longrightarrow> 
 p \<triangleleft>\<alpha> b \<alpha>\<triangleright> p = p"
  by (utp_alpha_tac, utp_pred_auto_tac)


theorem CondA_sym:
"\<lbrakk>p \<in> WF_RELATION; q \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> p = \<alpha> q; \<alpha> b \<subseteq> \<alpha> p\<rbrakk> \<Longrightarrow> 
  p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q = q \<triangleleft>\<alpha> \<not>\<alpha> b \<alpha>\<triangleright> p"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_assoc:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
    "b \<in> WF_CONDITION" "c \<in> WF_CONDITION" 
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq> \<alpha> p" "\<alpha> b = \<alpha> c"
  shows "(p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) \<triangleleft>\<alpha> c \<alpha>\<triangleright> r = p \<triangleleft>\<alpha> b \<and>\<alpha> c \<alpha>\<triangleright> (q \<triangleleft>\<alpha> c \<alpha>\<triangleright> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_distr:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
    "b \<in> WF_CONDITION" "c \<in> WF_CONDITION" 
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq> \<alpha> p" "\<alpha> b = \<alpha> c"
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
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq> \<alpha> p"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q \<triangleleft>\<alpha> b \<alpha>\<triangleright> r) = p \<triangleleft>\<alpha> b \<alpha>\<triangleright> r"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_disj:
  assumes
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "b \<in> WF_CONDITION" "c \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> c \<subseteq> \<alpha> p" "\<alpha> b \<subseteq> \<alpha> p"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (p \<triangleleft>\<alpha> c \<alpha>\<triangleright> q) = p \<triangleleft>\<alpha> b \<or>\<alpha> c \<alpha>\<triangleright> q"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_refinement:
  assumes
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq> \<alpha> p"
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
  apply (rule_tac ?vs1.0="VAR - \<alpha> r" in UNREST_subset)
  apply (auto)
done

theorem UNREST_WF_CONDITION_DASHED[unrest]: 
"r \<in> WF_CONDITION \<Longrightarrow> UNREST DASHED (\<pi> r)"
  by (simp add:WF_CONDITION_def)

theorem SemiA_CondA_distr:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq> \<alpha> p"
  shows "(p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) ;\<alpha> r = (p ;\<alpha> r) \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q ;\<alpha> r)"
proof -
  from assms have "\<alpha> b \<subseteq> \<alpha> (p ;\<alpha> r)"
    apply (simp add:WF_CONDITION_def)
    apply (simp add:alphabet in_out_union closure)
  done
    
  moreover hence "(p ;\<alpha> r) \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q ;\<alpha> r) \<in> WF_RELATION"
    by (simp add:closure alphabet assms)

  moreover from assms have "\<alpha> b \<subseteq> \<alpha> (q ;\<alpha> r)"
    apply (simp add:WF_CONDITION_def)
    apply (simp add:alphabet in_out_union closure)
  done

  ultimately show ?thesis using assms
    apply (utp_alpha_tac)
    apply (rule_tac SemiR_CondR_distr)
    apply (auto intro:SemiR_CondR_distr unrest closure simp add:EvalA_def)
  done
qed

end

end