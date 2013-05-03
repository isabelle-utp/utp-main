(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_laws.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Algebraic Laws *}

theory utp_laws
imports utp_pred utp_rel utp_rename "../alpha/utp_alphabet"
  "../tactics/utp_pred_tac"
  "../tactics/utp_rel_tac"
  "../tactics/utp_rel_tac2"
  "../tactics/utp_expr_tac"
  "../parser/utp_pred_parser"
begin




theorem SemiR_OrR_distl :
"r1 ; (r2 \<or>p r3) = (r1 ; r2) \<or>p (r1 ; r3)"
  by utp_rel_tac

theorem SemiR_OrR_distr :
"(r1 \<or>p r2) ; r3 = (r1 ; r3) \<or>p (r2 ; r3)"
  by utp_rel_tac

theorem SemiR_CondR_distr:
  assumes 
    "UNREST DASHED_TWICE p" 
    "UNREST DASHED_TWICE q" 
    "UNREST DASHED_TWICE r" 
    "UNREST DASHED_TWICE b"
    "UNREST DASHED b"
  shows "(p \<triangleleft> b \<triangleright> q) ; r = (p ; r) \<triangleleft> b \<triangleright> (q ; r)"
proof -
  from assms have "UNREST DASHED_TWICE (p \<triangleleft> b \<triangleright> q)"
    by (simp add:CondR_def, auto intro:unrest closure)

  with assms
  have "(p \<triangleleft> b \<triangleright> q) ; r = (\<exists>p DASHED_TWICE . (b \<and>p p \<or>p \<not>p b \<and>p q)[SS1] \<and>p r[SS2])" 
    by (simp add:SemiR_algebraic CondR_def closure)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b[SS1] \<and>p p[SS1] \<or>p \<not>p b[SS1] \<and>p q[SS1]) \<and>p r[SS2])"
    by (utp_pred_auto_tac)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b \<and>p p[SS1] \<or>p \<not>p b \<and>p q[SS1]) \<and>p r[SS2])"
    by (metis ExistsP_ident SS1_VAR_RENAME_ON RenameP_UNREST UNREST_ExistsP)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b \<and>p p[SS1] \<and>p r[SS2] \<or>p \<not>p b \<and>p q[SS1] \<and>p r[SS2]))"
    by (utp_pred_auto_tac)

  also from assms 
  have "... = (\<exists>p DASHED_TWICE . (b \<and>p p[SS1] \<and>p r[SS2])) \<or>p (\<exists>p DASHED_TWICE . (\<not>p b \<and>p q[SS1] \<and>p r[SS2]))"
    by (utp_pred_auto_tac)

  also from assms
  have "... = b \<and>p (\<exists>p DASHED_TWICE . (p[SS1] \<and>p r[SS2])) \<or>p \<not>p b \<and>p (\<exists>p DASHED_TWICE . (q[SS1] \<and>p r[SS2]))"
  proof -
    from assms have "UNREST DASHED_TWICE (\<not>p b)"
      by (blast intro:unrest)
      
    with assms show ?thesis
      by (simp add: ExistsP_AndP_expand2[THEN sym] closure)
  qed
    
  also from assms have "... = (p ; r) \<triangleleft> b \<triangleright> (q ; r)"
    by (simp add:SemiR_algebraic CondR_def closure)

  ultimately show ?thesis
    by simp

qed

theorem SemiR_TrueP_precond: 
  "p \<in> WF_CONDITION \<Longrightarrow> p ; true = p"
  apply (auto simp add:SemiR_def COMPOSABLE_BINDINGS_def TrueP_def UNREST_def WF_CONDITION_def)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="(RenameB SS x) \<oplus>\<^sub>b x on DASHED" in exI)
  apply (auto simp add:RenameB_rep_eq urename binding_equiv_def)
  apply (smt Compl_eq_Diff_UNIV Diff_iff NON_REL_VAR_def SS_ident_app UnCI o_apply override_on_def)
done

theorem SemiR_TrueP_postcond:
  "p \<in> WF_POSTCOND \<Longrightarrow> true ; p = p"
  apply (auto simp add:SemiR_def COMPOSABLE_BINDINGS_def TrueP_def UNREST_def WF_POSTCOND_def)
  apply (drule_tac x="b2" in bspec)
  apply (simp)
  apply (drule_tac x="b1" in spec)
  apply (subgoal_tac "b2 \<oplus>\<^sub>b b1 on UNDASHED = b1 \<oplus>\<^sub>b b2 on DASHED")
  apply (simp)
  apply (rule)
  apply (simp add:binding_equiv_def)
  apply (rule ext)
  apply (case_tac "x \<in> UNDASHED")
  apply (simp_all)
  apply (case_tac "x \<in> DASHED")
  apply (simp)
  apply (subgoal_tac "x \<in> NON_REL_VAR")
  apply (simp)
  apply (auto simp add:NON_REL_VAR_def)[1]
  apply (rule_tac x="(RenameB SS x) \<oplus>\<^sub>b x on UNDASHED" in exI)
  apply (rule_tac x="x" in exI)
  apply (auto)
  apply (rule)
  apply (rule)
  apply (simp add:RenameB_rep_eq urename)
  apply (case_tac "xa \<in> REL_VAR")
  apply (auto simp add:urename)
  apply (simp add:RenameB_rep_eq urename closure)
  apply (auto simp add:binding_equiv_def urename NON_REL_VAR_def RenameB_rep_eq)
done

theorem SemiR_AndP_right_precond: 
  "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; c \<in> WF_CONDITION \<rbrakk>
     \<Longrightarrow> p ; (c \<and>p q) = (p \<and>p c\<^sup>\<smile>) ; q"
  by (frule SemiR_TrueP_precond, auto simp add:evalrx closure)

theorem SemiR_AndP_left_postcond: 
  "\<lbrakk> UNREST DASHED_TWICE p
   ; UNREST DASHED_TWICE q
   ; UNREST (VAR - DASHED) c \<rbrakk>
     \<Longrightarrow> (p \<and>p c) ; q = p ; (c[SS] \<and>p q)"
  apply (subgoal_tac "UNREST DASHED_TWICE c")
  apply (subgoal_tac "UNREST DASHED_TWICE (p \<and>p c)")
  apply (subgoal_tac "UNREST DASHED_TWICE (c[SS] \<and>p q)")
  apply (subgoal_tac "c[SS2 \<circ>\<^sub>s SS] = c[SS1]")
  apply (simp add:SemiR_algebraic urename rename_simps)
  apply (metis (no_types) AndP_assoc)
  apply (metis (lifting) RenameP_equiv SS2_SS_eq_SS1)
  apply (rule unrest, rule unrest, simp)
  apply (force simp add:urename)
  apply (simp)
  apply (force intro:unrest)
  apply (force intro:unrest)
done

text {* Expressions renaming *}


text {* Expression substitution *}


subsubsection {* Additional EvalP laws *}

lemma EvalP_UNREST_binding_override [eval]:
  "\<lbrakk> UNREST vs p \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>p\<rbrakk>b1"
  by (metis EvalP_ExistsP EvalP_ForallP ExistsP_ident ForallP_ident)

lemma EvalP_UNREST_binding_upd [eval]:
  "\<lbrakk> UNREST vs p; x \<in> vs; v \<rhd> x \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)) = \<lbrakk>p\<rbrakk>b"
  apply (auto simp add:UNREST_def EvalP_def)
  apply (drule_tac x="b(x :=\<^sub>b v)" in bspec, simp)
  apply (drule_tac x="b" in spec)
  apply (simp)
  apply (drule_tac x="b" in bspec, simp)
  apply (drule_tac x="b(x :=\<^sub>b v)" in spec)
  apply (simp add:override_on_def binding_equiv_def)
done




end