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

ML {*
  structure hoare =
    Named_Thms (val name = @{binding hoare} val description = "Hoare Logic theorems")
*}

setup hoare.setup

definition HoareP :: 
  "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("{_}_{_}\<^sub>p" [200,0,201] 200) where
"{p}Q{r}\<^sub>p = ((p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq>\<^sub>p Q)"

declare HoareP_def [eval,evalr,evalrx]

syntax
  "_upred_hoare" :: "upred \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" ("{_}_{_}" [0,20,0] 100)

translations
  "_upred_hoare p Q r"  == "CONST HoareP p Q r"

theorem HoareP_intro [intro]:
  "(p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q \<Longrightarrow> `{p}Q{r}`"
  by (metis HoareP_def less_eq_WF_PREDICATE_def)

lemma HoareP_elim [elim]:
  "\<lbrakk> `{p}Q{r}`; \<lbrakk> (p \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis HoareP_def less_eq_WF_PREDICATE_def)

theorem HoareP_AndP:
  "`{p}Q{r \<and> s}` = `{p}Q{r} \<and> {p}Q{s}`"
  apply (simp add:HoareP_def urename)
  apply (utp_pred_auto_tac)
done

theorem HoareP_OrP:
  "`{p \<or> q}Q{r}` = `{p}Q{r} \<and> {q}Q{r}`"
  apply (simp add:HoareP_def urename)
  apply (utp_pred_auto_tac)
done

theorem HoareP_pre [hoare]:
  "`{p}Q{r}` \<Longrightarrow> `{p \<and> q}Q{r}`"
  by (utp_pred_auto_tac)

theorem HoareP_post [hoare]:
  "`{p}Q{r}` \<Longrightarrow> `{p}Q{r \<or> s}`"
  by (simp add:HoareP_def urename eval)

theorem HoareP_prepost [hoare]:
  "`{p}Q{r}` \<Longrightarrow> `{p \<and> q}Q{r \<or> s}`"
  by (simp add:HoareP_def urename eval)

theorem HoareP_weaken_pre:
  "\<lbrakk> `p' \<Rightarrow> p`; `{p}Q{r}` \<rbrakk> \<Longrightarrow> `{p'}Q{r}`"
  by (simp add: HoareP_def, utp_pred_tac)

theorem HoareP_strengthen_post:
  "\<lbrakk> `r \<Rightarrow> r'`; `{p}Q{r}` \<rbrakk> \<Longrightarrow> `{p}Q{r'}`"
  by (simp add: HoareP_def, utp_pred_tac)

theorem HoareP_pre_refine:
  "\<lbrakk> (p \<sqsubseteq> q); `{p}Q{r}` \<rbrakk> \<Longrightarrow> `{q}Q{r}`"
by (metis HoareP_pre RefP_AndP)

theorem HoareP_post_refine:
  "\<lbrakk> (r \<sqsubseteq> s); `{p}Q{s}` \<rbrakk> \<Longrightarrow> `{p}Q{r}`"
  by (metis HoareP_post OrP_comm RefP_OrP)

theorem HoareP_TrueR [hoare]:
  "`{p}Q{true}`"
  by (metis ConvR_TrueP HoareP_intro RefineP_TrueP_refine utp_pred_simps(14))

theorem HoareP_SkipR [hoare]:
  assumes "p \<in> COND"
  shows "`{p}II{p}`"
  using assms by (utp_xrel_auto_tac)

theorem HoareP_SkipRA [hoare]:
  assumes "HOMOGENEOUS vs" "- in(vs) \<sharp> p"
  shows "`{p}II\<^bsub>vs\<^esub>{p}`"
  by (metis AndP_assoc AndP_comm AndP_idem HoareP_intro RefP_AndP_intro SemiR_spec_refine SkipRA_AndP_cond assms)

theorem HoareP_CondR [hoare]:
  assumes "`{b \<and> p}S{q}`" "`{\<not>b \<and> p}T{q}`"
  shows "`{p}S \<lhd> b \<rhd> T{q}`"
  using assms by (utp_pred_auto_tac)
  
theorem HoareP_ChoiceP [hoare]:
  assumes "`{p}Q{s}`" "`{p}R{s}`" 
  shows "`{p}Q \<sqinter> R{s}`"
  using assms by (utp_pred_tac)

theorem HoareP_SemiR [hoare]:
  assumes 
    "`{p}Q1{s}`" "`{s}Q2{r}`" 
    "p \<in> COND" "r \<in> COND" "s \<in> COND"
    "Q1 \<in> REL" "Q2 \<in> REL"
  shows "`{p}Q1 ; Q2{r}`"
proof
  from assms 
  have refs: "(p \<Rightarrow>\<^sub>p s\<acute>) \<sqsubseteq> Q1" "(s \<Rightarrow>\<^sub>p r\<acute>) \<sqsubseteq> Q2"
    by (auto elim!:HoareP_elim)

  have "`(p \<and> (p \<Rightarrow> s\<acute>) ; (s \<Rightarrow> r\<acute>))` = `((p \<and> (p \<Rightarrow> s\<acute>)) ; (s \<Rightarrow> r\<acute>))`"
    by (metis ConvR_rel_closure ImpliesP_rel_closure SemiR_AndP_left_precond WF_CONDITION_WF_RELATION assms(3) assms(4) assms(5))

  also have "... = `(p \<and> s\<acute>) ; (s \<Rightarrow> r\<acute>)`"
    by (metis (hide_lams, no_types) AndP_OrP_distl ImpliesP_def OrP_comm inf_WF_PREDICATE_def inf_compl_bot uminus_WF_PREDICATE_def utp_pred_simps(11) utp_pred_simps(2) utp_pred_simps(6))

  also have "... = `p ; (s \<and> (s \<Rightarrow> r\<acute>))`"
    by (metis SemiR_AndP_right_precond assms(5))

  also have "... = `p ; (s \<and> r\<acute>)`"
    by (metis AndP_OrP_distl AndP_contra ImpliesP_def utp_pred_simps(13) utp_pred_simps(2))

  also have "... = `(p ; s) \<and> r\<acute>`"
    by (metis PrimeP_WF_CONDITION_WF_POSTCOND SemiR_AndP_right_postcond assms(4))

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

theorem HoareP_AssignR [hoare]:
  assumes "q \<in> COND" "x \<in> D\<^sub>0" 
          "D\<^sub>1 \<sharp> v" "p \<Rightarrow>\<^sub>p q[v/\<^sub>px]"
  shows "{p}x :=\<^sub>R v{q}\<^sub>p"
  using assms
  apply (rule_tac HoareP_intro)
  apply (rule AssignR_refinement_alt)
  apply (simp_all)
done

lemma HoareP_PAssignR:
  fixes x :: "('a::DEFINED, 'm::VALUE) PVAR"
    and v :: "('a::DEFINED, 'm::VALUE) WF_PEXPRESSION"
  assumes "q \<in> COND" "x\<down> \<in> D\<^sub>0" "TYPEUSOUND('a, 'm)" "D\<^sub>1 \<sharp> v" "`p \<Rightarrow> q[v/x]`"
  shows "`{p}x := v{q}`"
  using assms
  apply (simp add:PAssignF_upd_def)
  apply (rule HoareP_AssignR)
  apply (simp_all add:closure typing defined unrest)
done

lemma (in left_near_kleene_algebra) 
  star_inductl_one_intro: "1 + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
  by (metis star_inductl_one)

theorem HoareP_IterP [hoare]:
  assumes 
    "`{p \<and> b}S{p}`"
    "p \<in> COND" "b \<in> COND" "S \<in> REL"
  shows "`{p}while b do S od{\<not>b \<and> p}`"
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
      by (metis (lifting, no_types) AndP_assoc SemiR_AndP_right_precond assms(2))

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

theorem HoareP_IterInvP [hoare]:
  assumes 
    "`{p \<and> b}S{p}`" "`pre \<Rightarrow> p`" "`(\<not>b \<and> p) \<Rightarrow> post`"
    "p \<in> COND" "b \<in> COND" "S \<in> REL"
  shows "`{pre}while b inv p do S od{post}`"
  using assms
  by (auto simp add: IterInvP_def intro: HoareP_strengthen_post HoareP_weaken_pre HoareP_IterP)

declare EvalP_SkipR [eval del]
declare EvalP_SkipR_alt [eval]

lemma HoareP_VarOpenP:
  "\<lbrakk> x\<down> \<in> D\<^sub>0; {x\<down>} \<sharp> p; p \<in> COND; q \<in> COND; `p \<Rightarrow> q` \<rbrakk> \<Longrightarrow> `{p}var x{q}`"
  apply (simp add:VarOpenP_def)
  apply (utp_pred_auto_tac)
  apply (metis EvalP_UNREST_assign_1 EvalP_WF_CONDITION_binding_equiv UNDASHED_not_DASHED 
               binding_equiv_SS_DASHED binding_equiv_SS_UNDASHED binding_equiv_update_subsume)
done

lemma HoareP_VarCloseP:
  "\<lbrakk> x\<down> \<in> D\<^sub>0; {x\<down>} \<sharp> q; p \<in> COND; q \<in> COND; `p \<Rightarrow> q` \<rbrakk> \<Longrightarrow> `{p}end x{q}`"
  apply (simp add:VarCloseP_def)
  apply (utp_pred_auto_tac)
  apply (metis EvalP_UNREST_assign_1 EvalP_WF_CONDITION_binding_equiv RenameB_binding_upd_1 
               SS_DASHED_app UNDASHED_dash_DASHED undash_dash)
done

end