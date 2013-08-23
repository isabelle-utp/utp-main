(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_hoare.thy                                                        *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Hoare Logic *}

theory utp_hoare
imports 
  utp_lattice 
  utp_recursion
  utp_iteration
  "../laws/utp_pred_laws"
  "../laws/utp_rel_laws"
  "../laws/utp_refine_laws"
  "../parser/utp_pred_parser"
begin

definition HoareP :: 
  "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_{_}\<^sub>p_" [200,0,201] 200) where
"p{Q}\<^sub>pr = ((p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq>\<^sub>p Q)"

declare HoareP_def [eval,evalr,evalrx]

syntax
  "_upred_hoare" :: "upred \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" ("_{_}_" [55,0,56] 55)

translations
  "_upred_hoare p Q r"  == "CONST HoareP p Q r"

lemma HoareP_intro [intro]:
  "(p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q \<Longrightarrow> `p{Q}r`"
  by (metis HoareP_def less_eq_WF_PREDICATE_def)

lemma HoareP_elim [elim]:
  "\<lbrakk> `p{Q}r`; \<lbrakk> (p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis HoareP_def less_eq_WF_PREDICATE_def)

theorem HoareP_AndP:
  "`p{Q}(r \<and> s)` = `p{Q}r \<and> p{Q}s`"
  apply (simp add:HoareP_def urename)
  apply (utp_pred_auto_tac)
done

theorem HoareP_OrP:
  "`(p \<or> q){Q}r` = `p{Q}r \<and> q{Q}r`"
  apply (simp add:HoareP_def urename)
  apply (utp_pred_auto_tac)
done

theorem HoareP_TrueR:
  "`p{Q}true`"
  by (metis ConvR_TrueP HoareP_intro RefineP_TrueP_refine utp_pred_simps(14))

theorem HoareP_SkipR:
  assumes "p \<in> WF_CONDITION"
  shows "`p{II}p`"
  using assms by (utp_xrel_auto_tac)

theorem HoareP_CondR:
  assumes "`(b \<and> p){S}q`" "`(\<not>b \<and> p){T}q`"
  shows "`p{S \<lhd> b \<rhd> T}q`"
  using assms by (utp_pred_auto_tac)
  
theorem HoareP_SemiR:
  assumes 
    "p \<in> WF_CONDITION" "r \<in> WF_CONDITION" "s \<in> WF_CONDITION"
    "Q1 \<in> WF_RELATION" "Q2 \<in> WF_RELATION"
    "`p{Q1}s`" "`s{Q2}r`" 
  shows "`p{Q1 ; Q2}r`"
proof
  from assms 


  have refs: "(p \<Rightarrow>\<^sub>p s\<acute>) \<sqsubseteq> Q1" "(s \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q2"
    by (auto elim!:HoareP_elim)

  have "`(p \<and> (p \<Rightarrow> s\<acute>) ; (s \<Rightarrow> r\<acute>))` = `((p \<and> (p \<Rightarrow> s\<acute>)) ; (s \<Rightarrow> r\<acute>))`"
    by (metis ConvR_rel_closure ImpliesP_rel_closure SemiR_AndP_left_precond WF_CONDITION_WF_RELATION assms(1) assms(2) assms(3))

  also have "... = `(p \<and> s\<acute>) ; (s \<Rightarrow> r\<acute>)`"
    by (metis (hide_lams, no_types) AndP_OrP_distl ImpliesP_def OrP_comm inf_WF_PREDICATE_def inf_compl_bot uminus_WF_PREDICATE_def utp_pred_simps(11) utp_pred_simps(2) utp_pred_simps(6))

  also have "... = `p ; (s \<and> (s \<Rightarrow> r\<acute>))`"
    by (metis ConvR_rel_closure ImpliesP_rel_closure SemiR_AndP_right_precond WF_CONDITION_WF_RELATION assms(1) assms(2) assms(3))

  also have "... = `p ; (s \<and> r\<acute>)`"
    by (metis AndP_OrP_distl AndP_contra ImpliesP_def utp_pred_simps(13) utp_pred_simps(2))

  also have "... = `(p ; s) \<and> r\<acute>`"
    by (metis PrimeP_WF_CONDITION_WF_POSTCOND SemiR_AndP_right_postcond WF_CONDITION_WF_RELATION assms(1) assms(2) assms(3))

  finally show "`(p \<Rightarrow> r\<acute>)` \<sqsubseteq> `Q1 ; Q2`"
  using refs
    apply (rule_tac order_trans)
    apply (rule SemiR_mono_refine)
    apply (assumption)
    apply (assumption)
    apply (rule SemiR_spec_refine)
    apply (simp)
    apply (metis RefineP_seperation order_refl)
  done
qed

theorem HoareP_AssignR:
  assumes "p \<in> WF_CONDITION"
   "x \<in> UNDASHED" "UNREST_EXPR DASHED v" "v \<rhd>\<^sub>e x"
  shows "p[v/\<^sub>px]{x :=\<^sub>R v}\<^sub>pp"
  using assms
  apply (rule_tac HoareP_intro)
  apply (utp_pred_auto_tac)
  apply (simp add:ConvR_def eval urename)
  apply (subgoal_tac "(SS\<bullet>b) \<cong> (b(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b)) on UNDASHED")
  apply (drule_tac x="x" in bspec, simp)
  apply (simp add:AssignF_upd_rep_eq EvalE_def)

  apply (metis EvalP_WF_CONDITION_binding_equiv binding_equiv_comm)
  apply (auto simp add:binding_equiv_def)
  apply (case_tac "xa = x")
  apply (simp add:typing urename AssignF_upd_rep_eq)
  apply (drule_tac x="xa" in bspec, simp)
  apply (simp add:typing urename AssignF_upd_rep_eq IdA.rep_eq VarE.rep_eq)
done

lemma (in left_near_kleene_algebra) 
  star_inductl_one_intro: "1 + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
  by (metis star_inductl_one)

theorem HoareP_IterP:
  assumes 
    "p \<in> WF_CONDITION" "b \<in> WF_CONDITION" "S \<in> WF_RELATION"
    "`(p \<and> b){S}p`"
  shows "`p{while b do S od}(\<not>b \<and> p)`"
proof -
  from assms have S_ref: "`p \<and> b \<Rightarrow> p\<acute>` \<sqsubseteq> S"
    by (force elim: HoareP_elim)

  moreover have "`p \<Rightarrow> p\<acute>` \<sqsubseteq> `(b \<and> S)\<^sup>\<star>`"
  proof -
    have "`p \<and> (b \<and> S) ; (p \<Rightarrow> p\<acute>)` = `(p \<and> b \<and> S) ; (p \<Rightarrow> p\<acute>)`"
      by (metis AndP_rel_closure ConvR_rel_closure ImpliesP_rel_closure SemiR_AndP_left_precond WF_CONDITION_WF_RELATION assms)

    also from S_ref
    have "... = `(p \<and> b \<and> S \<and> p\<acute>) ; (p \<Rightarrow> p\<acute>)`"
      by (utp_rel_auto_tac)

    also have "... = `(p \<and> b \<and> S) ; (p \<and> (p \<Rightarrow> p\<acute>))`"
      by (metis (lifting, no_types) AndP_rel_closure ConvR_rel_closure ImpliesP_rel_closure SemiR_AndP_left_precond SemiR_AndP_right_precond WF_CONDITION_WF_RELATION assms(1) assms(2) assms(3))

    also have "... = `((p \<and> b \<and> S) ; (p \<and> p\<acute>))`"
      by (utp_rel_auto_tac)

    also have "... = `((p \<and> b \<and> S) ; p) \<and> p\<acute>`"
      by (metis AndP_rel_closure PrimeP_WF_CONDITION_WF_POSTCOND SemiR_AndP_right_postcond WF_CONDITION_WF_RELATION assms)

    also have "p\<acute> \<sqsubseteq> ..."
      by (utp_pred_tac)

    finally show ?thesis using assms
      apply (rule_tac star_inductl_one_intro)
      apply (simp add:plus_WF_PREDICATE_def times_WF_PREDICATE_def one_WF_PREDICATE_def)
      apply (rule OrP_refine)
      apply (utp_xrel_auto_tac)
      apply (rule SemiR_spec_refine)
      apply (simp)
    done
  qed

  thus ?thesis
    apply (rule_tac HoareP_intro)
    apply (rule_tac SemiR_spec_refine)
    apply (simp add:IterP_def urename)
    apply (rule RefineP_seperation_refine)
    apply (utp_pred_tac)
    apply (utp_pred_tac)
  done
qed

end