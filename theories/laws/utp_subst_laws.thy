(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_subst_laws.thy                                                   *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Substitution Theorems *}

theory utp_subst_laws
imports 
  "../core/utp_pred" 
  "../core/utp_rename"
  "../core/utp_expr"
  "../core/utp_rel"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
  "../parser/utp_pred_parser"
begin

subsection {* Predicate Substitution Laws *}

ML {*
  structure usubst =
    Named_Thms (val name = @{binding usubst} val description = "substitution theorems")
*}

setup usubst.setup

lemma SubstP_NotP [usubst]: "`(\<not> p)[v/x]` = `\<not> p[v/x]`"
  by (utp_pred_tac)

lemma SubstP_TrueP [usubst]: "true[v|x] = true"
  by (utp_pred_tac)

lemma SubstP_FalseP [usubst]: "false[v|x] = false"
  by (utp_pred_tac)

lemma SubstP_AndP [usubst]: "(p \<and>p q)[v|x] = p[v|x] \<and>p q[v|x]"
  by (utp_pred_tac)

lemma SubstP_OrP [usubst]: "(p \<or>p q)[v|x] = p[v|x] \<or>p q[v|x]"
  by (utp_pred_tac)

lemma SubstP_ImpliesP [usubst]: 
  "(p \<Rightarrow>p q)[v|x] = p[v|x] \<Rightarrow>p q[v|x]"
  by (utp_pred_tac)

lemma SubstP_IffP [usubst]: 
  "(p \<Leftrightarrow>p q)[v|x] = p[v|x] \<Leftrightarrow>p q[v|x]"
  by (utp_pred_tac)

lemma SubstP_ExistsP [usubst]:
  "\<lbrakk> UNREST_EXPR vs e; x \<notin> vs; e \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> (\<exists>p vs. p)[e|x] = (\<exists>p vs. p[e|x])"
  by (utp_pred_tac, utp_expr_tac)

lemma SubstP_twice_1 [usubst]:
  "\<lbrakk> e \<rhd>\<^sub>e x; f \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> p[e|x][f|x] = SubstP p (SubstE e f x) x"
  by (utp_pred_tac, utp_expr_tac)

lemma SubstP_twice_2 [usubst]:
  "\<lbrakk> e \<rhd>\<^sub>e x; f \<rhd>\<^sub>e y; UNREST {y} p \<rbrakk> \<Longrightarrow> p[e|x][f|y] = SubstP p (SubstE e f y) x"
  apply (simp add:eval evale typing closure defined)
  apply (metis EvalE_compat EvalP_UNREST_assign_1 binding_upd_twist)
done

lemma SubstP_VarP_diff [usubst]:
  "\<lbrakk> x \<noteq> y; e \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> VarP y[e|x] = VarP y"
  by (utp_pred_tac, utp_expr_tac)

lemma SubstP_VarP_aux [usubst]:
  "\<lbrakk> UNREST AUX_VAR p; e \<rhd>\<^sub>e x; aux x \<rbrakk> \<Longrightarrow> p[e|x] = p"
  by (utp_pred_tac)

lemma SubstP_VarP [usubst]: "v \<rhd>\<^sub>e x \<Longrightarrow> VarP x[v|x] = ExprP v"
  by (utp_pred_tac, utp_expr_tac)

lemma SubstP_EqualP [usubst]: "(e ==p f)[v|x] = (SubstE e v x ==p SubstE f v x)"
  by (utp_pred_tac, utp_expr_tac)

lemma SubstP_SemiR_left [usubst]: 
  "\<lbrakk> x \<in> UNDASHED; v \<rhd>\<^sub>e x; UNREST_EXPR DASHED v \<rbrakk> \<Longrightarrow> (p ; q)[v|x] = p[v|x] ; q"
  by (utp_rel_auto_tac)

lemma SubstP_SemiR_right [usubst]: 
  "\<lbrakk> x \<in> DASHED; v \<rhd>\<^sub>e x; UNREST_EXPR UNDASHED v \<rbrakk> \<Longrightarrow> (p ; q)[v|x] = p ; q[v|x]"
  apply (utp_rel_tac)
  sorry

lemma binding_equiv_upd_match:
  "\<lbrakk> b1(x :=\<^sub>b e) \<cong> b2(x :=\<^sub>b f) on vs; e \<rhd> x; f \<rhd> x; x \<in> vs \<rbrakk> \<Longrightarrow> e = f"
  by (auto simp add:binding_equiv_def)

lemma binding_equiv_upd_cat:
"\<lbrakk> b1(x :=\<^sub>b e) \<cong> b2 on vs; e \<rhd> x; x \<in> vs \<rbrakk> \<Longrightarrow> b2(x :=\<^sub>b e) = b2"
  by (auto simp add:binding_equiv_def)

lemma binding_equiv_upd_drop:
  "\<lbrakk> b1(x :=\<^sub>b e) \<cong> b2(x :=\<^sub>b f) on vs; e \<rhd> x; f \<rhd> x \<rbrakk> \<Longrightarrow> b1 \<cong> b2 on vs - {x}"
  by (auto simp add:binding_equiv_def, metis)

lemma SubstP_NON_REL_VAR [usubst]:
  "\<lbrakk> x \<in> NON_REL_VAR; v \<rhd>\<^sub>e x; UNREST_EXPR REL_VAR v \<rbrakk> \<Longrightarrow> (p ; q)[v|x] = p[v|x] ; q[v|x]"
  apply (utp_rel_auto_tac)
  apply (rule_tac x="ya \<oplus>\<^sub>b xa on NON_REL_VAR" in exI)
  apply (simp add:typing)
  apply (subgoal_tac "\<lbrakk>v\<rbrakk>\<epsilon>(ya \<oplus>\<^sub>b xa on NON_REL_VAR) = \<lbrakk>v\<rbrakk>\<epsilon>xa")
  apply (subgoal_tac "ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>xa) \<oplus>\<^sub>b xa on NON_REL_VAR - {x} = ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>xa)")
  apply (subgoal_tac "ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>xa) = ya")
  apply (simp)
  apply (metis EvalE_compat EvalR_NON_REL_VAR binding_equiv_upd_cat)
  apply (metis (hide_lams, no_types) EvalE_compat EvalR_NON_REL_VAR binding_equiv_upd_cat binding_override_equiv binding_override_simps(4) binding_override_upd)
  apply (metis EvalE_UNREST_override NON_REL_VAR_def binding_override_minus)
done

lemma SubstP_SkipRA [usubst]: 
  "\<lbrakk> HOMOGENEOUS vs; x \<notin> vs; e \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> II vs[e|x] = II vs"
  apply (utp_pred_tac)
  apply (metis (full_types) Int_iff hom_alphabet_undash in_vars_def)
done

lemma SubstP_SkipR [usubst]:
  "\<lbrakk> x \<in> UNDASHED; UNREST_EXPR DASHED v \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>e x \<Longrightarrow> II[v|x] = II"
  apply (utp_rel_tac)
oops

lemma SubstP_AssignR_1 [usubst]:
  "\<lbrakk> x \<in> UNDASHED; y \<in> UNDASHED; e \<rhd>\<^sub>e y; v \<rhd>\<^sub>e x; x \<noteq> y\<acute>; UNREST_EXPR DASHED e; UNREST_EXPR DASHED v \<rbrakk> \<Longrightarrow> (y :=p e)[v|x] = y :=p (e[v|x])"
  apply (simp add:AssignR_alt_def usubst)
  oops

(*
lemma SubstP_UNDASHED:
  assumes 
    "x \<in> UNDASHED" "UNREST {x\<acute>\<acute>} p"
    "UNREST_EXPR {x\<acute>\<acute>} v" "v \<rhd>\<^sub>e x"
  shows "p[v|x] = (\<exists>p {x\<acute>\<acute>} . p[id(x:=x\<acute>\<acute>) on {x}] \<and>p (VarE x\<acute>\<acute> ==p v))"
  apply (insert assms)
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (subgoal_tac "rename_func_on (id(x := x\<acute>\<acute>)) {x}")
  apply (simp add:closure)
  apply (subgoal_tac "(\<langle>(id(x := dash (dash x))) on {x}\<rangle>\<^sub>s (x\<acute>\<acute>)) = x")
  apply (simp)
  apply (auto)[1]
sorry
*)

(*
lemma SubstP_DASHED:
  assumes 
    "x \<in> DASHED" "UNREST {dash x} p"
    "UNREST_EXPR {dash x} v" "v \<rhd>\<^sub>e x"
  shows "p[v|x] = (\<exists>p {dash x} . p\<^bsup>[x \<mapsto> dash x]\<^esup> \<and>p (VarE (dash x) ==p v))"
proof -

  from assms have "p[v|x] = SubstP_body p v x (SOME x'. is_SubstP_var p v x x')"
    by (simp add:SubstP_def)

  also from assms have "... = SubstP_body p v x (dash x)"
  proof -
    from assms have "is_SubstP_var p v x (dash x)"
      by (simp add: is_SubstP_var_DASHED)

    thus ?thesis using assms
      apply (rule_tac is_SubstP_var_equiv)
      apply (rule someI)
      apply (simp_all)
    done
  qed

  ultimately show ?thesis
    sorry
(*    by (simp add:SubstP_body_def) *)
qed
*)

(*
lemma SubstP_RenameP:
  assumes 
    "vtype x = vtype y" "aux x = aux y" "x \<noteq> y" 
    "\<exists> z. is_SubstP_var p (VarE y) x z" "UNREST {y} p"
  shows "p[VarE y|x] = p\<^bsup>[x \<mapsto> y]\<^esup>"
  using assms
  apply (subgoal_tac "VarE y \<rhd>\<^sub>e x")
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (metis (lifting) EvalP_UNREST_assign assms binding_value_alt insertI1 insert_is_Un)
  apply (metis VarE_defined VarE_type evar_compat_intros(1) evar_compat_intros(2))
done  
*)


subsection {* Expression Substitution Laws *}

lemma SubstE_TrueE [usubst]:
  "TrueE[e|x] = TrueE"
  by (utp_expr_tac)

lemma SubstE_FalseE [usubst]:
  "FalseE[e|x] = FalseE"
  by (utp_expr_tac)

lemma SubstE_VarE [usubst]: 
  "v \<rhd>\<^sub>e x \<Longrightarrow> VarE x[v|x] = v"
  by (utp_expr_tac)

end

