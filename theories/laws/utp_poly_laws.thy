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

lemma BoolType_aux_var_split_exists_ty:
  "pvaux x \<Longrightarrow> `\<exists> x. P` = `P[false/x] \<or> P[true/x]`"
  by (utp_poly_auto_tac, metis)

theorem SemiR_extract_variable_ty:
  fixes x y :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "x \<in> PUNDASHED" "y \<in> PDASHED_TWICE" "TYPEUSOUND('a, 'm)" 
          "pvaux x" "pvaux y"
          "{y\<down>} \<sharp> P" "{y\<down>} \<sharp> Q"
  shows "P ; Q = `\<exists> y. P[$y/x\<acute>] ; Q[$y/x]`"
  apply (subst SemiR_extract_variable[of "x\<down>" "y\<down>"])
  apply (simp_all add:assms closure)
  apply (metis assms(4) assms(5) pvaux_aux)
  apply (simp add:erasure assms typing defined closure)
done

theorem SemiR_extract_variable_id_ty:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "x \<in> PUNDASHED" "TYPEUSOUND('a, 'm)" "pvaux x"
          "{x\<down>\<acute>\<acute>} \<sharp> P" "{x\<down>\<acute>\<acute>} \<sharp> Q"
  shows "P ; Q = `\<exists> x\<acute>\<acute>. P[$x\<acute>\<acute>/x\<acute>] ; Q[$x\<acute>\<acute>/x]`"
  apply (subst SemiR_extract_variable[of "x\<down>" "x\<down>\<acute>\<acute>"])
  apply (simp_all add:assms closure)
  apply (simp add:erasure assms typing defined closure)
done

theorem AssignR_SemiR_ty:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes 
    "TYPEUSOUND('a, 'm)"
    "x \<in> PUNDASHED" 
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
  apply (rule_tac ExistsP_assm_witness[of _ _ "|($ys - $xs)|\<down>"])
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
  apply (utp_poly_auto_tac)
done

lemma EqualP_as_EqualPE:
  fixes e f :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "EqualP e\<down> f\<down> = PExprP (EqualPE e f)"
  using assms by (utp_poly_tac)

lemma ExprP_as_PExprP:
  "ExprP e\<down> = PExprP e"
  by (utp_poly_tac)

lemma EvalR_ExprR_ty [evalpr]: 
  fixes e :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION"
  shows "\<lbrakk>ExprP e\<down>\<rbrakk>R = {(b1, b2). \<lbrakk>e\<rbrakk>\<^sub>* (b1 \<oplus>\<^sub>b SS\<bullet>b2 on D\<^sub>1) 
                                \<and> b1 \<in> WF_REL_BINDING
                                \<and> b2 \<in> WF_REL_BINDING
                                \<and> b1 \<cong> b2 on NON_REL_VAR}"
  apply (auto simp add:evalr BindR_def urename RenameB_override_distr1 closure typing defined)
  apply (metis EvalP_ExprP EvalP_ExprP_ty)
  apply (metis BindR_def BindR_right_eq_NON_REL_VAR NON_REL_VAR_minus_DASHED binding_equiv_override_subsume binding_override_simps(5))
  apply (rule_tac x="xa \<oplus>\<^sub>b SS\<bullet>y on D\<^sub>1" in exI)
  apply (auto)
  apply (metis WF_REL_BINDING_bc_DASHED_eq binding_override_equiv)
  apply (simp add:urename RenameB_override_distr1 closure)
  apply (metis (hide_lams, no_types) NON_REL_VAR_UNDASHED_DASHED SS_REL_VAR_overshadow WF_REL_BINDING_bc_DASHED_eq binding_equiv_override binding_override_assoc binding_override_minus binding_override_simps(2))
  apply (metis EvalP_ExprP EvalP_ExprP_ty)
done

lemma EvalR_EqualP_ty [evalpr]:
  fixes e f :: "('a :: DEFINED, 'm :: BOOL_SORT) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>EqualP e\<down> f\<down>\<rbrakk>R = {(b1, b2). \<lbrakk>e\<rbrakk>\<^sub>* (b1 \<oplus>\<^sub>b SS\<bullet>b2 on D\<^sub>1) = \<lbrakk>f\<rbrakk>\<^sub>* (b1 \<oplus>\<^sub>b SS\<bullet>b2 on D\<^sub>1) 
                                \<and> b1 \<in> WF_REL_BINDING
                                \<and> b2 \<in> WF_REL_BINDING
                                \<and> b1 \<cong> b2 on NON_REL_VAR}"
  apply (subst EqualP_as_EqualPE)
  apply (simp add:assms)
  apply (subst ExprP_as_PExprP[THEN sym])
  apply (simp add:evalpr evalp)
done

(*
lemma EvalR_EqualP_ty [evalpr]:
  fixes e f :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>EqualP e\<down> f\<down>\<rbrakk>R = {BindR b |b. (\<lbrakk>e\<rbrakk>\<^sub>* b = \<lbrakk>f\<rbrakk>\<^sub>* b)}"
  using assms by (auto simp add:evalr evale)
*)

lemma var_eq_trans:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x \<in> PUNDASHED" "pvaux x"
  shows "`($x\<acute> = $x) ; ($x\<acute> = $x)` = `($x\<acute> = $x)`"
  using assms
  apply (subst SemiR_algebraic)
  apply (simp_all add:closure unrest typing assms urename PermPV_PVAR)
  apply (auto simp add:eval closure assms)
  apply (rule_tac x="b(x\<acute>\<acute> :=\<^sub>* \<langle>b\<rangle>\<^sub>* x)" in exI)
  apply (simp add:typing defined assms closure)
done

theorem nil_prefixeq [simp]:
  "`\<langle>\<rangle> \<le> x` = `true`"
  by (utp_poly_auto_tac)

theorem nil_append_left [simp]:
  "|\<langle>\<rangle> ^ x| = |x|"
  by (utp_poly_auto_tac)

theorem nil_append_right [simp]:
  "|x ^ \<langle>\<rangle>| = |x|"
  by (utp_poly_auto_tac)

lemma append_assoc:
  fixes xs ys zs :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  shows "|($xs ^ $ys) ^ $zs| = |$xs ^ ($ys ^ $zs)|"
  by (utp_poly_tac)

theorem SemiR_prefix_trans:
  fixes xs :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" "xs \<in> PUNDASHED"
  shows "`($xs \<le> $xs\<acute>) ; ($xs \<le> $xs\<acute>)` = `($xs \<le> $xs\<acute>)`"
  using assms by (utp_prel_auto_tac)

lemma SemiR_prefix_eq_trans:
  fixes xs :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" "xs \<in> PUNDASHED"
  shows "`($xs \<le> $xs\<acute>) ; ($xs = $xs\<acute>)` = `($xs \<le> $xs\<acute>)`"
  using assms by (utp_prel_auto_tac)

lemma SemiR_eq_prefix_trans:
  fixes xs :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" "xs \<in> PUNDASHED"
  shows "`($xs = $xs\<acute>) ; ($xs \<le> $xs\<acute>)` = `($xs \<le> $xs\<acute>)`"
  using assms by (utp_prel_auto_tac)

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

lemma app_minus:   
  fixes xs ys :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" 
  shows "|($xs ^ $ys) - $xs| = |$ys|"
  using assms
  by (utp_poly_tac)

lemma prefix_antisym:
  fixes xs ys :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  assumes "TYPEUSOUND('a ULIST, 'm)" 
  shows "`($xs \<le> $ys) \<and> ($ys \<le> $xs)` = `$xs = $ys`"
  using assms 
    apply (utp_poly_tac)
    apply (metis prefix_order.eq_iff)
done

lemma SkipRA_unfold_aux_ty: 
  fixes v :: "('a :: DEFINED, 'm :: VALUE) PVAR" 
  assumes "TYPEUSOUND('a, 'm)" "v\<down> \<in> vs" "v\<down> \<acute> \<in> vs" "v \<in> PUNDASHED" "HOMOGENEOUS vs" "pvaux v"
  shows "II\<^bsub>vs\<^esub> = `($v\<acute> = $v) \<and> II\<^bsub>vs - {v \<down>, v \<down>\<acute>}\<^esub>`"
  apply(subst SkipRA_unfold[of "v \<down>"])
  apply(simp_all add:closure assms erasure typing defined)
done

end