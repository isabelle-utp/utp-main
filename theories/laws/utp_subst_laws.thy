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
begin

subsection {* Predicate Substitution Laws *}

theorem SubstP_NotP [usubst]: "(\<not>\<^sub>p p)[v/\<^sub>px] = \<not>\<^sub>p p[v/\<^sub>px]"
  by (utp_pred_tac)

theorem SubstP_TrueP [usubst]: "true[v/\<^sub>px] = true"
  by (utp_pred_tac)

theorem SubstP_FalseP [usubst]: "false[v/\<^sub>px] = false"
  by (utp_pred_tac)

theorem SubstP_AndP [usubst]: "(p \<and>\<^sub>p q)[v/\<^sub>px] = p[v/\<^sub>px] \<and>\<^sub>p q[v/\<^sub>px]"
  by (utp_pred_tac)

theorem SubstP_OrP [usubst]: "(p \<or>\<^sub>p q)[v/\<^sub>px] = p[v/\<^sub>px] \<or>\<^sub>p q[v/\<^sub>px]"
  by (utp_pred_tac)

theorem SubstP_AndDistP [usubst]:
  "(\<And>\<^sub>p ps)[v/\<^sub>px] = (\<And>\<^sub>p {p[v/\<^sub>px] | p. p \<in> ps})"
  apply (utp_pred_auto_tac)
  apply (metis EvalP_SubstP)
done

theorem SubstP_ANDI [usubst]:
  "(\<And>\<^sub>p i:I. P i)[v/\<^sub>px] = (\<And>\<^sub>p i:I. (P i)[v/\<^sub>px])"
  by (utp_pred_auto_tac)

theorem SubstP_OrDistP [usubst]:
  "(\<Or>\<^sub>p ps)[v/\<^sub>px] = (\<Or>\<^sub>p {p[v/\<^sub>px] | p. p \<in> ps})"
  apply (utp_pred_auto_tac)
  apply (metis EvalP_SubstP)
done

theorem SubstP_ORDI [usubst]:
  "(\<Or>\<^sub>p i:I. P i)[v/\<^sub>px] = (\<Or>\<^sub>p i:I. (P i)[v/\<^sub>px])"
  by (utp_pred_auto_tac)

theorem SubstP_CondR [usubst]: 
  "(P \<lhd> c \<rhd> Q)[v/\<^sub>px] = (P[v/\<^sub>px]) \<lhd> (c[v/\<^sub>px]) \<rhd> (Q[v/\<^sub>px])"
  by (utp_pred_tac)

theorem SubstP_ImpliesP [usubst]: 
  "(p \<Rightarrow>\<^sub>p q)[v/\<^sub>px] = p[v/\<^sub>px] \<Rightarrow>\<^sub>p q[v/\<^sub>px]"
  by (utp_pred_tac)

theorem SubstP_IffP [usubst]: 
  "(p \<Leftrightarrow>\<^sub>p q)[v/\<^sub>px] = p[v/\<^sub>px] \<Leftrightarrow>\<^sub>p q[v/\<^sub>px]"
  by (utp_pred_tac)

theorem SubstP_ExistsP [usubst]:
  "\<lbrakk> vs \<sharp> e; x \<notin> vs \<rbrakk> \<Longrightarrow> (\<exists>\<^sub>p vs. p)[e/\<^sub>px] = (\<exists>\<^sub>p vs. p[e/\<^sub>px])"
  by (utp_pred_tac)

theorem ExistsP_SubstP_same [usubst]:
  "x \<in> xs \<Longrightarrow> (\<exists>\<^sub>p xs. p)[v/\<^sub>px] = (\<exists>\<^sub>p xs. p)"
  by (utp_pred_tac)

theorem ForallP_SubstP_same [usubst]:
  "x \<in> xs \<Longrightarrow> (\<forall>\<^sub>p xs. p)[v/\<^sub>px] = (\<forall>\<^sub>p xs. p)"
  by (utp_pred_tac)

theorem ForallP_SubstP_diff [usubst]:
  "\<lbrakk> x \<notin> xs; xs \<sharp> v \<rbrakk> \<Longrightarrow> (\<forall>\<^sub>p xs. p)[v/\<^sub>px] = (\<forall>\<^sub>p xs. p[v/\<^sub>px])"
  by (simp add: ForallP_def usubst)

theorem SubstP_ClosureP [usubst]:
  "[P]\<^sub>p[v/\<^sub>px] = [P]\<^sub>p"
  by (utp_pred_tac)

theorem SubstP_RefineP [usubst]:
  "(P \<sqsubseteq>\<^sub>p Q)[v/\<^sub>px] = (P \<sqsubseteq>\<^sub>p Q)"
  by (utp_pred_tac)

theorem SubstP_UNREST (* [usubst] *):
  "\<lbrakk> NON_REL_VAR \<sharp> p; x \<in> NON_REL_VAR \<rbrakk> 
  \<Longrightarrow> p[e/\<^sub>px] = p"
  by (utp_pred_tac)

theorem SubstP_twice_1 [usubst]:
  "p[e/\<^sub>px][f/\<^sub>px] = p[e[f/\<^sub>ex]/\<^sub>px]"
  by (utp_pred_tac)

theorem SubstP_twice_2 [usubst]:
  "{y} \<sharp> p \<Longrightarrow> p[e/\<^sub>px][f/\<^sub>py] = p[e[f/\<^sub>ey]/\<^sub>px]"
  apply (simp add:eval evale typing closure defined)
  apply (metis EvalE_compat EvalP_UNREST_assign_1 binding_upd_twist)
done

theorem SubstP_twice_3 [usubst]:
  "\<lbrakk> x \<noteq> y; {x} \<sharp> f \<rbrakk> \<Longrightarrow> p[e/\<^sub>px][f/\<^sub>py] = p[f/\<^sub>py][e[f/\<^sub>ey]/\<^sub>px]"
  by (utp_pred_tac, metis EvalE_UNREST_binding_upd EvalE_compat binding_upd_twist)

theorem SubstP_VarP_diff [usubst]:
  "x \<noteq> y \<Longrightarrow> $\<^sub>py[e/\<^sub>px] = $\<^sub>py"
  by (utp_pred_tac)

theorem SubstP_VarP_aux (* [usubst] *):
  "\<lbrakk> AUX_VAR \<sharp> p; aux x \<rbrakk> \<Longrightarrow> p[e/\<^sub>px] = p"
  by (utp_pred_tac)

theorem SubstP_VarP_single_UNREST (* [usubst] *):
  "{x} \<sharp> p \<Longrightarrow> p[e/\<^sub>px] = p"
  by (utp_pred_tac)

theorem SubstP_VarP [usubst]: "v \<rhd>\<^sub>e x \<Longrightarrow> $\<^sub>px[v/\<^sub>px] = ExprP v"
  by (utp_pred_tac)

theorem SubstP_EqualP [usubst]: "(e ==\<^sub>p f)[v/\<^sub>px] = (e[v/\<^sub>ex]) ==\<^sub>p (f[v/\<^sub>ex])"
  by (utp_pred_tac)

theorem SubstP_SemiR_left [usubst]: 
  "\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> v \<rbrakk> \<Longrightarrow> (p ;\<^sub>R q)[v/\<^sub>px] = p[v/\<^sub>px] ;\<^sub>R q"
  by (utp_rel_auto_tac)

theorem SubstP_SemiR_right [usubst]: 
  "\<lbrakk> x \<in> DASHED; UNDASHED \<sharp> v \<rbrakk> \<Longrightarrow> (p ;\<^sub>R q)[v/\<^sub>px] = p ;\<^sub>R q[v/\<^sub>px]"
  by (utp_rel_auto_tac)

lemma binding_equiv_upd_match:
  "\<lbrakk> b1(x :=\<^sub>b e) \<cong> b2(x :=\<^sub>b f) on vs; e \<rhd> x; f \<rhd> x; x \<in> vs \<rbrakk> \<Longrightarrow> e = f"
  by (auto simp add:binding_equiv_def)

lemma binding_equiv_upd_cat:
"\<lbrakk> b1(x :=\<^sub>b e) \<cong> b2 on vs; x \<in> vs \<rbrakk> \<Longrightarrow> b2(x :=\<^sub>b e) = b2"
  apply (auto simp add:binding_equiv_def)
  apply (metis binding_upd_triv binding_upd_vcoerce)
done

lemma binding_equiv_upd_drop:
  "\<lbrakk> b1(x :=\<^sub>b e) \<cong> b2(x :=\<^sub>b f) on vs \<rbrakk> \<Longrightarrow> b1 \<cong> b2 on vs - {x}"
  by (auto simp add:binding_equiv_def, metis)

theorem SubstP_NON_REL_VAR [usubst]:
  "\<lbrakk> x \<in> NON_REL_VAR; REL_VAR \<sharp> v \<rbrakk> \<Longrightarrow> (p ;\<^sub>R q)[v/\<^sub>px] = p[v/\<^sub>px] ;\<^sub>R q[v/\<^sub>px]"
  apply (utp_rel_auto_tac)
  apply (rule_tac x="ya \<oplus>\<^sub>b xa on NON_REL_VAR" in exI)
  apply (simp add:typing)
  apply (subgoal_tac "\<lbrakk>v\<rbrakk>\<^sub>e(ya \<oplus>\<^sub>b xa on NON_REL_VAR) = \<lbrakk>v\<rbrakk>\<^sub>exa")
  apply (subgoal_tac "ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>exa) \<oplus>\<^sub>b xa on NON_REL_VAR - {x} = ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>exa)")
  apply (subgoal_tac "ya(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>exa) = ya")
  apply (simp)
  apply (metis EvalE_compat EvalR_NON_REL_VAR binding_equiv_upd_cat)
  apply (metis (hide_lams, no_types) Diff_cancel EvalR_NON_REL_VAR binding_equiv_upd_cat binding_override_equiv binding_override_simps(11) binding_override_simps(5) binding_override_simps(8) binding_override_upd)
  apply (metis EvalE_UNREST_override NON_REL_VAR_def binding_override_minus)
done

theorem SubstP_SkipRA [usubst]: 
  "\<lbrakk> HOMOGENEOUS vs; x \<notin> vs; e \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> II\<^bsub>vs\<^esub>[e/\<^sub>px] = II\<^bsub>vs\<^esub>"
  apply (utp_pred_tac)
  apply (metis (full_types) Int_iff hom_alphabet_undash in_vars_def)
done

lemma SubstP_SkipR [usubst]:
  "\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> v \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>e x \<Longrightarrow> II[v/\<^sub>px] = II"
  apply (utp_rel_auto_tac)
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

theorem SubstE_LitE [usubst]:
  "v : a \<Longrightarrow> LitE v[e/\<^sub>ex] = LitE v"
  by (utp_expr_tac)

lemma [typing]: "x :! a \<Longrightarrow> x : a"
  by (auto)


(* Hmmmm, why does this proof take so much effort? It should just go through by
   utp_expr_tac but I have to explicitly guide application of EvalE_Op1E. I think
   there may be too much non-determinism. *)
theorem SubstE_Op1E [usubst]:
  "\<lbrakk> v :!\<^sub>e a; f \<in> FUNC1 a b; e :\<^sub>e vtype x \<rbrakk> \<Longrightarrow> (Op1E f v)[e/\<^sub>ex] = Op1E f (v[e/\<^sub>ex])"
  apply (auto simp add:evale typing defined)
  apply (insert SubstE_type[of e x v a])
  apply (metis EvalE_SubstE EvalE_def Op1E_rep_eq strict_etype_rel_def)
done

lemma SubstE_Op2E [usubst]:
  "\<lbrakk> v1 :!\<^sub>e a; v2 :!\<^sub>e b; f \<in> FUNC2 a b c; e :\<^sub>e vtype x \<rbrakk> \<Longrightarrow> 
     (Op2E f v1 v2)[e/\<^sub>ex] = Op2E f (v1[e/\<^sub>ex]) (v2[e/\<^sub>ex])"
  apply (auto simp add:evale typing defined)
  apply (metis EvalE_SubstE EvalE_def Op2E_rep_eq strict_etype_rel_def)
done

theorem SubstE_TrueE [usubst]:
  "TrueE[e/\<^sub>ex] = TrueE"
  by (utp_expr_tac)

theorem SubstE_FalseE [usubst]:
  "FalseE[e/\<^sub>ex] = FalseE"
  by (utp_expr_tac)

theorem SubstE_VarE [usubst]: 
  "v \<rhd>\<^sub>e x \<Longrightarrow> VarE x[v/\<^sub>ex] = v"
  by (utp_expr_tac)

theorem SubstE_VarE_other [usubst]: 
  "x \<noteq> y \<Longrightarrow> VarE y[v/\<^sub>ex] = VarE y"
  by (utp_expr_tac)

theorem SubstE_VarE_single_UNREST (* [usubst] *):
  "{x} \<sharp> f \<Longrightarrow> f[e/\<^sub>ex] = f"
  by (utp_expr_tac)

theorem SubstP_AssignR_simple [usubst]:
  assumes 
    "x \<in> UNDASHED"
    "DASHED \<sharp> e"
    "DASHED \<sharp> v"
  shows "(x :=\<^sub>R e)[v/\<^sub>px] = (x :=\<^sub>R (e[v/\<^sub>ex]))"
  using assms 
  apply (utp_rel_auto_tac)
  apply (metis (lifting, mono_tags) EvalE_SubstE EvalR_AssignR UNDASHED_not_DASHED UNDASHED_undash_elim UNREST_SubstE_simple WF_REL_BINDING_binding_upd_remove assms(1) assms(2) assms(3) mem_Collect_eq)
  apply (smt EvalE_SubstE EvalR_AssignR UNDASHED_not_DASHED UNREST_SubstE_simple WF_REL_BINDING_binding_upd mem_Collect_eq)
done
(*
Alternative proof requiring typing constraints:
by (simp add: AssignR_alt_def typing defined usubst unrest)
*)

theorem SubstP_AssignR_disjoint [usubst]:
  assumes "x \<in> D\<^sub>0" "y \<in> D\<^sub>0" "x \<noteq> y"
          "{x} \<sharp> v" "{y} \<sharp> u" "D\<^sub>1 \<sharp> u" "D\<^sub>1 \<sharp> v"
  shows "(x :=\<^sub>R u)[v/\<^sub>py] = (x :=\<^sub>R u) ;\<^sub>R (y :=\<^sub>R v)"
  using assms
  apply (utp_rel_auto_tac)
  apply (metis WF_REL_BINDING_binding_upd_remove)
  apply (metis EvalE_UNREST_binding_upd binding_upd_twist)
  apply (metis WF_REL_BINDING_binding_upd WF_REL_BINDING_binding_upd_remove)
  apply (metis EvalE_UNREST_binding_upd binding_upd_twist)
  apply (metis WF_REL_BINDING_binding_upd)
done

lemma SubstP_AssignR_1 [usubst]:
  "\<lbrakk> x \<in> UNDASHED; y \<in> UNDASHED; e \<rhd>\<^sub>e y; v \<rhd>\<^sub>e x; x \<noteq> y; 
     DASHED \<sharp> e; DASHED \<sharp> v \<rbrakk> 
     \<Longrightarrow> (y :=\<^sub>R e)[v/\<^sub>px] = y,x :=\<^sub>R (e[v/\<^sub>ex]),v"
  apply (subgoal_tac "y\<acute> \<noteq> x")
  apply (subgoal_tac "x \<notin> {y,y\<acute>}")
  apply (simp add:AssignR_alt_def usubst unrest typing defined)
  oops

end

