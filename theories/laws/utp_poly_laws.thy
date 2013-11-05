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
  apply (simp_all add:typing defined erasure pvaux_aux inju)
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
  by (utp_poly_tac)

lemma [simp]: "\<not> (x::int) < y \<Longrightarrow> `<x> < <y>` = false"
  by (utp_poly_tac)

lemma [simp]: "|<x :: int> + <y>| = |<x + y>|"
  by (utp_poly_tac)

lemma prefix_implies_concat_minus:
  fixes xs ys :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" "pvaux xs" "pvaux ys"
  shows "`($xs \<le> $ys) \<Rightarrow> $xs ^ ($ys - $xs) = $ys`"
  using assms
  apply (utp_poly_auto_tac)
  apply (metis prefixeq_drop)
done

lemma prefix_implies_diff:
  fixes xs ys zs :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" "pvaux xs"  "pvaux ys" "pvaux zs" 
          "zs\<down> \<noteq> xs\<down>" "zs\<down> \<noteq> ys\<down>"
  shows "`($xs \<le> $ys) \<Rightarrow> (\<exists> zs. $ys = $xs ^ $zs)`"
  using assms
  apply (rule_tac ExistsP_assm_witness[of "|($ys - $xs)|\<down>"])
  apply (simp add:typing defined closure)
  apply (simp add:usubst typing defined closure)
  apply (metis EqualP_sym prefix_implies_concat_minus)
done

lemma prefix_as_concat:
  fixes xs ys zs :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" "pvaux xs"  "pvaux ys" "pvaux zs" 
          "zs\<down> \<noteq> xs\<down>" "zs\<down> \<noteq> ys\<down>"
  shows "`($xs \<le> $ys)` = `(\<exists> zs. $ys = $xs ^ $zs)`"
  using assms
  apply (rule_tac ImpliesP_eq_intro)
  apply (simp add: prefix_implies_diff[of xs ys zs])
  apply (auto simp add:evalp)
done

lemma var_eq_trans:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x \<in> PUNDASHED" "pvaux x"
  shows "`($x\<acute> = $x) ; ($x\<acute> = $x)` = `($x\<acute> = $x)`"
  apply (subst SemiR_algebraic)
  apply (simp_all add:closure unrest typing assms urename PermPV_PVAR)
  apply (auto simp add:eval closure assms)
  apply (rule_tac x="b(x\<acute>\<acute> :=\<^sub>* \<langle>b\<rangle>\<^sub>* x)" in exI)
  apply (simp add:typing defined assms closure)
done

lemma nil_prefixeq [simp]:
  "`\<langle>\<rangle> \<le> x` = `true`"
  by (utp_poly_auto_tac)

lemma nil_append [simp]:
  "|\<langle>\<rangle> ^ x| = |x|"
  by (utp_poly_auto_tac)

lemma prefix_eq_nil:
  fixes xs ys :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" 
  shows "`($xs - $ys) = \<langle>\<rangle> \<and> ($ys \<le> $xs)` = `$ys = $xs`"
  using assms
  apply (utp_poly_auto_tac)
  apply (metis antisym prefix_length_eq prefixeq_length_le)
done

lemma prefix_app:
  fixes xs ys :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" 
  shows "`($xs ^ \<langle>a\<rangle> = $ys) \<and> ($xs \<le> $ys)` = `($xs ^ \<langle>a\<rangle> = $ys)`"
  using assms
  apply (utp_poly_auto_tac)
  apply (metis prefixeq_def)
done

end