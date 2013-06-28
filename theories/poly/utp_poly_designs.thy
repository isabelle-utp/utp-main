(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs.thy                                                      *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Designs *}

theory utp_poly_designs
imports 
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../tactics/utp_expr_tac"
  "../core/utp_wp"
  "../laws/utp_pred_laws"
  "../laws/utp_rename_laws"
  "../laws/utp_subst_laws"
  "../laws/utp_rel_laws"
  "../parser/utp_poly_parser"
begin

text {* Most predicates need a boolean type, so we here set the appropriate sort constraint *}

default_sort BOOL_SORT

abbreviation "okay  \<equiv> MkPVAR (bName ''okay'') True TYPE(bool) TYPE('m :: BOOL_SORT)"
abbreviation "ok    \<equiv> PVarPE okay"
abbreviation "ok'   \<equiv> PVarPE okay\<acute>"
abbreviation "ok''  \<equiv> PVarPE okay\<acute>\<acute>"
abbreviation "ok''' \<equiv> PVarPE okay\<acute>\<acute>\<acute>"
abbreviation "OKAY \<equiv> {[okay]\<^sub>*,[okay\<acute>]\<^sub>*}"

definition DesignD :: 
"(bool, 'm) WF_PEXPRESSION \<Rightarrow>
 (bool, 'm) WF_PEXPRESSION \<Rightarrow>
 (bool, 'm) WF_PEXPRESSION" (infixr "\<turnstile>" 60) where
"p \<turnstile> q = \<parallel>ok \<and> p \<Rightarrow> ok' \<and> q\<parallel>"

syntax
  "_upred_design" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<turnstile>" 30)

translations
  "_upred_design p q"  == "CONST DesignD p q"

term "\<parallel>true \<turnstile> II\<^bsub>REL_VAR - OKAY\<^esub>\<parallel>"

definition SkipD :: "(bool, 'a) WF_PEXPRESSION" where
"SkipD = \<parallel>true \<turnstile> II\<^bsub>REL_VAR - OKAY\<^esub>\<parallel>"

notation SkipD ("II\<^sub>D")

declare DesignD_def [eval,evalr,evalrx]
declare SkipD_def [eval,evalr,evalrx]

subsection {* Closure / UNREST theorems *}

lemma MkPVAR_UNDASHED [simp]: 
  "[MkPVAR (bName x) s a m]\<^sub>* \<in> UNDASHED"
  by (simp add:PVAR_VAR_MkPVAR)

lemma MkPVAR_aux [simp]:
  "aux [MkPVAR n s a m]\<^sub>* = s"
  by (simp add:PVAR_VAR_MkPVAR)

lemma UNREST_PExprP [unrest]:
  "UNREST_PEXPR vs e \<Longrightarrow> UNREST vs (PExprP e)"
  by (auto simp add:UNREST_def UNREST_PEXPR_def PExprP_def)

lemma UNREST_SkipD_NON_REL_VAR [unrest]:
  "UNREST NON_REL_VAR II\<^sub>D"
  apply (simp add:SkipD_def DesignD_def evalp)
  apply (force intro: unrest)
done


lemma DesignD_rel_closure [closure]:
  "\<lbrakk>``P`` \<in> WF_RELATION; ``Q`` \<in> WF_RELATION\<rbrakk> \<Longrightarrow> ``P \<turnstile> Q`` \<in> WF_RELATION"
  by (simp add:DesignD_def closure evalp)

lemma SkipD_rel_closure [closure]:
  "``II\<^sub>D`` \<in> WF_RELATION"
  apply (auto intro:closure simp add:SkipD_def evalp)
  apply (rule closure)

subsection {* Design Laws *}

lemma DesignD_extreme_point_true:
  "``false \<turnstile> false`` = ``false \<turnstile> true``"
  by (utp_pred_tac)

lemma DesignD_extreme_point_nok:
  "``true \<turnstile> false`` = ``\<not> ok``"
  by (utp_pred_tac)

lemma DesignD_export_precondition:
  "``P \<turnstile> Q`` = ``P \<turnstile> P \<and> Q``"
  by (utp_pred_tac)

text {* Design refinement law *}

lemma EvalPE_UNREST_upd [simp]:
  "\<lbrakk> UNREST_PEXPR vs e; v \<rhd> x; x \<in> vs \<rbrakk> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>* (b(x :=\<^sub>b v)) = \<lbrakk>e\<rbrakk>\<^sub>* b"
  apply (auto simp add:UNREST_PEXPR_def)
  apply (metis binding_upd_override)
done

lemma SubstP_PExprP_UNREST [usubst]:
  "\<lbrakk> UNREST_PEXPR vs e; v \<rhd>\<^sub>e x; x \<in> vs \<rbrakk> \<Longrightarrow> (PExprP e)[v|x] = PExprP e"
  by (utp_pred_auto_tac)

lemma DesignD_refinement:
  assumes "UNREST_PEXPR OKAY P1" "UNREST_PEXPR OKAY P2"
          "UNREST_PEXPR OKAY Q1" "UNREST_PEXPR OKAY Q2"
  shows "``P1 \<turnstile> Q1 \<sqsubseteq> P2 \<turnstile> Q2`` = ``[P1 \<Rightarrow> P2] \<and> [P1 \<and> Q2 \<Rightarrow> Q1]``"
proof -
  have "``(P1 \<turnstile> Q1) \<sqsubseteq> (P2 \<turnstile> Q2)`` = ``[P2 \<turnstile> Q2 \<Rightarrow> P1 \<turnstile> Q1]``"
    by (utp_pred_tac)

  also have "... = ``[(ok \<and> P2 \<Rightarrow> ok' \<and> Q2) \<Rightarrow> (ok \<and> P1 \<Rightarrow> ok' \<and> Q1)]``"
    by (utp_pred_tac)

  also with assms have "... = ``[(P2 \<Rightarrow> ok' \<and> Q2) \<Rightarrow> (P1 \<Rightarrow> ok' \<and> Q1)]``"
    apply (simp add:evalp)
    apply (rule_tac trans)
    apply (rule_tac x="[okay]\<^sub>*" in BoolType_aux_var_split_taut)
    apply (simp_all add:usubst typing defined unrest)
  done

  also from assms have "... = `[(\<not> P2 \<Rightarrow> \<not> P1) \<and> ((P2 \<Rightarrow> Q2) \<Rightarrow> (P1 \<Rightarrow> Q1))]`"
    apply (simp add:evalp)
    apply (rule_tac trans)
    apply (rule_tac x="[okay\<acute>]\<^sub>*" in BoolType_aux_var_split_taut)
    apply (simp_all add:usubst typing defined)
  done

  also have "... = `[(P1 \<Rightarrow> P2) \<and> ((P2 \<Rightarrow> Q2) \<Rightarrow> (P1 \<Rightarrow> Q1))]`"
    by (utp_pred_auto_tac)

  also have "... = `[(P1 \<Rightarrow> P2)] \<and> [P1 \<and> Q2 \<Rightarrow> Q1]`"
    by (utp_pred_auto_tac)

  ultimately show ?thesis
    by (metis (hide_lams, no_types) PredPE_inv)
qed

lemma SubstPE_AndPE [usubst]:
  "``(P \<and> Q)[v/x]`` = ``P[v/x] \<and> Q[v/x]``"
  by (utp_pred_tac)

lemma SubstPE_ImpliesPE [usubst]:
  "``(P \<Rightarrow> Q)[v/x]`` = ``P[v/x] \<Rightarrow> Q[v/x]``"
  by (utp_pred_tac)

lemma [simp]: 
  "``false \<Rightarrow> p`` = ``true``"
  "``false \<and> p`` = ``false``"
  by (utp_pred_tac+)

lemma DesignD_diverge:
  "``(P \<turnstile> Q)[false/okay]`` = ``true``"
  by (simp add:DesignD_def usubst typing defined)

lemma DesignD_left_zero:
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "true ; (P \<turnstile> Q) = true"
proof -

  from assms have "`true ; (P \<turnstile> Q)` = `\<exists> okay\<acute>\<acute>\<acute>. true[$okay\<acute>\<acute>\<acute>/okay\<acute>] ; (P \<turnstile> Q)[$okay\<acute>\<acute>\<acute>/okay]`"
    by (simp add: SemiR_extract_variable closure)

  also from assms have "... = `(true[false/okay\<acute>] ; (P \<turnstile> Q)[false/okay]) \<or> (true[true/okay\<acute>] ; (P \<turnstile> Q)[true/okay])`"
    apply (rule_tac trans)
    apply (rule BoolType_aux_var_split_exists, simp_all)
    apply (simp add:usubst typing assms closure defined unrest)
  done

  also have "... = `((true ; true) \<or> (true ; ((P \<turnstile> Q)[true/okay])))`"
    by (simp add:usubst closure typing DesignD_diverge)

  ultimately show ?thesis
    by (simp add:closure SemiR_TrueP_precond)
qed


end
