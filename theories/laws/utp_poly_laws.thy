(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_laws.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Laws for polymorphic predicates *}

theory utp_poly_laws
imports 
  "../poly/utp_poly_expr"
  "../parser/utp_pred_parser"
  utp_pred_laws
  utp_rel_laws
  utp_rename_laws
  utp_subst_laws
begin

lemma BoolType_pvaux_cases [ucases]:
  assumes "pvaux x" 
  shows "p = q \<longleftrightarrow> `p[false/x]` = `q[false/x]` \<and> `p[true/x]` = `q[true/x]`"
  using assms
  apply (rule_tac iffI)
  apply (utp_pred_tac)
  apply (rule BoolType_aux_var_split_eq_intro[of "x\<down>"])
  apply (simp_all add:typing defined erasure pvaux_aux)
done

theorem SemiR_extract_variable_ty:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
          "x \<in> PUNDASHED" "pvaux x"
          "TYPEUSOUND('a, 'm)"
  shows "P ; Q = `\<exists> x\<acute>\<acute>\<acute>. P[$x\<acute>\<acute>\<acute>/x\<acute>] ; Q[$x\<acute>\<acute>\<acute>/x]`"
  apply (subst SemiR_extract_variable[of _ _ "x\<down>"])
  apply (simp_all add:assms)
  apply (metis PVAR_VAR_PUNDASHED_UNDASHED assms(3))
  apply (simp add:erasure assms typing defined closure)
done

theorem AssignR_SemiR_ty:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes 
    "TYPEUSOUND('a, 'm)"
    "x \<in> PUNDASHED" 
    "e \<rhd>\<^sub>* x" 
    "DASHED \<sharp> e"
  shows "`(x := e) ; p` = `p[e/x]`"
  apply (utp_rel_tac)
  apply (simp add: EvalR_AssignR_typed evalp closure typing defined unrest relcomp_unfold assms EvalR_SubstP_UNDASHED_ty)
  apply (auto simp add: binding_upd_ty_def)
  apply (metis InjU_EvalPE_compat PVAR_VAR_PUNDASHED_UNDASHED WF_REL_BINDING_binding_upd_remove WF_REL_BINDING_member1 assms(2) assms(3))
done

text {* Declare some useful simplications for polymorphic expressions *}

lemma [simp]: "(x::int) < y \<Longrightarrow> `<x> < <y>` = true"
  by (simp add:eval)

lemma [simp]: "\<not> (x::int) < y \<Longrightarrow> `<x> < <y>` = false"
  by (simp add:eval)

lemma [simp]: "|<x :: int> + <y>| = |<x + y>|"
  by (simp add:evalp)

end