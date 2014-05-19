(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_hoare.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Alphabetised Hoare Logic *}

theory utp_alpha_hoare
imports 
  utp_alpha_rel
  "../core/utp_hoare"
  "../laws/utp_rel_laws"
  "../tactics/utp_solve_tac"
  "../tactics/utp_closure_tac"
  "../parser/utp_alpha_pred_parser"
  "utp_alpha_iteration"
begin

lift_definition HoareA :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE" ("{_}_{_}\<^sub>\<alpha>" [200,0,201] 200)
is "\<lambda> p q r. (\<lbrace>\<rbrace> :: 'a ALPHABET, {\<pi> p}\<pi> q{\<pi> r}\<^sub>p)"
  by (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def HoareP_def unrest)

theorem HoareA_alphabet [alphabet]: "\<alpha>({p}Q{r}\<^sub>\<alpha>) = \<lbrace>\<rbrace>"
  by (simp add:pred_alphabet_def HoareA.rep_eq)

lemma EvalA_HoareA [evala]: "\<lbrakk>{p}Q{r}\<^sub>\<alpha>\<rbrakk>\<pi> = {\<lbrakk>p\<rbrakk>\<pi>}\<lbrakk>Q\<rbrakk>\<pi>{\<lbrakk>r\<rbrakk>\<pi>}\<^sub>p"
  by (metis EvalA_def HoareA.rep_eq snd_conv)

theorem HoareA_alt_def:
  "{p}Q{r}\<^sub>\<alpha> = (p \<Rightarrow>\<^sub>\<alpha> r\<acute>) \<sqsubseteq>\<^sub>\<alpha> Q"
  by (utp_alpha_tac, utp_pred_tac)

syntax
  "_uapred_hoare" :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred" ("{_}_{_}" [0,20,0] 100)

translations
  "_uapred_hoare p Q r"  == "CONST HoareA p Q r"

theorem HoareA_AndA:
  "``{p}Q{r \<and> s}`` = ``{p}Q{r} \<and> {p}Q{s}``"
  by (utp_alpha_tac, simp add:HoareP_AndP)

theorem HoareA_OrA:
  "``{p \<or> q}Q{r}`` = ``{p}Q{r} \<and> {q}Q{r}``"
  by (utp_alpha_tac, simp add:HoareP_OrP)

theorem HoareA_pre [hoare]:
  "``{p}Q{r}`` \<Longrightarrow> ``{p \<and> q}Q{r}``"
  by (utp_alpha_tac, metis HoareP_pre)

theorem HoareA_post [hoare]:
  "``{p}Q{r}`` \<Longrightarrow> ``{p}Q{r \<or> s}``"
  by (utp_alpha_tac, metis HoareP_post)

theorem HoareA_prepost [hoare]:
  "``{p}Q{r}`` \<Longrightarrow> ``{p \<and> q}Q{r \<or> s}``"
  by (utp_alpha_tac, metis HoareP_prepost)

theorem HoareA_weaken_pre:
  "\<lbrakk> ``p' \<Rightarrow> p``; ``{p}Q{r}`` \<rbrakk> \<Longrightarrow> ``{p'}Q{r}``"
  by (simp add: HoareA_alt_def, utp_solve)

theorem HoareA_strengthen_post:
  "\<lbrakk> ``r \<Rightarrow> r'``; ``{p}Q{r}`` \<rbrakk> \<Longrightarrow> ``{p}Q{r'}``"
  apply (simp add: HoareA_alt_def, utp_solve)
  apply (metis ConvR_AndP EvalP_AndP EvalP_RefineP_intro RefP_AndP)
done

theorem HoareA_TrueA [hoare]:
  "``{p}Q{true\<^bsub>a\<^esub>}``"
  by (utp_alpha_tac, metis HoareP_TrueR)

theorem HoareA_SkipA [hoare]:
  assumes "a \<in> HOM_ALPHABET" "\<alpha>(p) \<subseteq>\<^sub>f in\<^sub>\<alpha>(a)"
  shows "``{p}II\<^bsub>a\<^esub>{p}``"
  using assms
  apply (utp_alpha_tac)
  apply (simp add:HoareP_def)
  apply (rule SkipRA_refines_ImpliesP[of "\<langle>\<alpha> p\<rangle>\<^sub>f"])
  apply (metis in_vars_def le_inf_iff)
  apply (metis UNREST_EvalA)
  apply (metis HOMOGENEOUS_HOM_ALPHA)
  apply (metis in_vars_def le_inf_iff)
done

theorem HoareA_CondA [hoare]:
  assumes "``{b \<and> p}S{q}``" "``{\<not>b \<and> p}T{q}``"
  shows "``{p}S \<lhd> b \<rhd> T{q}``"
  using assms by (utp_alpha_tac, metis HoareP_CondR)
  
theorem HoareA_SemiA [hoare]:
  assumes
    "p \<in> WF_ALPHA_COND" "r \<in> WF_ALPHA_COND" "s \<in> WF_ALPHA_COND"
    "Q1 \<in> WF_ALPHA_REL" "Q2 \<in> WF_ALPHA_REL"
    "``{p}Q1{s}``" "``{s}Q2{r}``" 
  shows "``{p}Q1 ; Q2{r}``"
  using assms
  apply (utp_alpha_tac)
  apply (rule HoareP_SemiR)
  apply (simp_all add:closure)
done

lemma UNREST_WF_ALPHA_COND:
  "p \<in> WF_ALPHA_COND \<Longrightarrow> - D\<^sub>0 \<sharp> \<lbrakk>p\<rbrakk>\<pi>"
  by (metis UNREST_WF_CONDITION WF_ALPHA_COND_EvalA_WF_CONDITION)

theorem HoareA_AssignA [hoare]:
  assumes "p \<Rightarrow>\<^sub>\<alpha> q[v/\<^sub>\<alpha>x]"
   "p \<in> COND" "q \<in> COND"
   "x \<in>\<^sub>f in\<^sub>\<alpha>(a)" "\<alpha>(p) \<subseteq>\<^sub>f a" "\<alpha>(q) \<subseteq>\<^sub>f a" "\<alpha>(v) \<subseteq>\<^sub>f in\<^sub>\<alpha>(a)" 
   "a \<in> REL_ALPHABET" "a \<in> HOM_ALPHABET"
  shows "{p}x :=\<^bsub>a\<^esub> v{q}\<^sub>\<alpha>"
  using assms
  apply (subgoal_tac "\<alpha>(v) \<subseteq>\<^sub>f a")
  apply (utp_alpha_tac)
  apply (simp add:HoareP_def)
  apply (rule AssignRA_refinement_alt)
  apply (metis HOMOGENEOUS_HOM_ALPHA)
  apply (metis REL_ALPHABET_UNDASHED_DASHED)
  apply (metis Compl_subset_Compl_iff EvalAE_UNREST_EXPR UNREST_EXPR_subset)
  apply (simp)
  apply (rule UNREST_subset[of "(- D\<^sub>0) \<union> (- \<langle>a\<rangle>\<^sub>f)"])
  apply (rule UNREST_union)
  apply (metis UNREST_WF_ALPHA_COND)
  apply (metis Compl_subset_Compl_iff UNREST_EvalA UNREST_subset)
  apply (force)
  apply (metis Compl_subset_Compl_iff EvalAE_UNREST_EXPR UNREST_EXPR_subset)
  apply (metis (no_types) Un_upper1 alphabet_split funion.rep_eq le_less_trans le_neq_trans less_eq_fset.rep_eq less_imp_le)
done

lemma HoareA_EvalA:
  "{\<lbrakk>p\<rbrakk>\<pi>}\<lbrakk>Q\<rbrakk>\<pi>{\<lbrakk>r\<rbrakk>\<pi>}\<^sub>p \<Longrightarrow> {p}Q{r}\<^sub>\<alpha>"
  by (metis EvalA_HoareA EvalA_TautologyA)

theorem HoareA_IterA [hoare]:
  assumes 
    "p \<in> COND" "b \<in> COND" "S \<in> REL" "\<alpha>(S) \<in> HOM_ALPHABET"
    "\<alpha>(b) \<subseteq>\<^sub>f \<alpha>(S)" "\<alpha>(p) \<subseteq>\<^sub>f \<alpha>(S)" "``{p \<and> b}S{p}``"
  shows "``{p}while b do S od{\<not>b \<and> p}``"
  using assms
    apply (rule_tac HoareA_EvalA)
    apply (simp add:evala)
    apply (rule HoareP_SemiR[of _ _ "\<not>\<^sub>p \<lbrakk>b\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>p\<rbrakk>\<pi>"])
    apply (simp_all add:closure)
    apply (metis HoareP_IterP WF_ALPHA_COND_EvalA_WF_CONDITION WF_ALPHA_REL_EvalA_WF_RELATION)
    apply (rule hoare)
    apply (metis HOMOGENEOUS_HOM_ALPHA)
    apply (rule unrest)
    apply (rule unrest)
    apply (rule UNREST_subset[of "(- D\<^sub>0) \<union> (- \<langle>\<alpha> b\<rangle>\<^sub>f)"])
    apply (metis UNREST_EvalA UNREST_WF_ALPHA_COND UNREST_union)
    apply (auto)[1]
    apply (rule UNREST_subset[of "(- D\<^sub>0) \<union> (- \<langle>\<alpha> p\<rangle>\<^sub>f)"])
    apply (metis UNREST_EvalA UNREST_WF_ALPHA_COND UNREST_union)
    apply (auto)[1]
done

end