(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_rename_laws.thy                                                  *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Renaming Theorems *}

theory utp_rename_laws
imports 
  "../core/utp_pred" 
  "../core/utp_rename"
  "../core/utp_expr"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
begin

subsubsection {* Predicate Laws *}

theorem EvalP_RenameP [eval] :
"\<lbrakk>p[ss]\<rbrakk>b = \<lbrakk>p\<rbrakk>(RenameB (inv\<^sub>s ss) b)"
apply (simp add: EvalP_def)
apply (simp add: RenameP_def)
apply (simp add: image_def)
apply (safe)
apply (simp)
apply (rule_tac x = "RenameB (inv\<^sub>s ss) b" in bexI)
apply (simp)
apply (assumption)
done

theorem EvalP_RenamePMap_one [eval] :
"\<lbrakk> x \<noteq> x'; vtype x' = vtype x; aux x' = aux x \<rbrakk> \<Longrightarrow>
 \<lbrakk>p\<^bsup>[x \<mapsto> x']\<^esup>\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x', x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x))"
apply (simp add: RenamePMap_def)
apply (simp add: eval closure)
apply (simp add: EvalP_def)
apply (simp add: RenameP_def RenameB_def image_def closure)
apply (simp add: MapR_rep_eq[of "[x]" "[x']",simplified] CompB_def)
apply (subgoal_tac "Abs_WF_BINDING (\<langle>b\<rangle>\<^sub>b \<circ> MapRename [x \<mapsto> x']) = b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x', x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x)")
apply (simp add: closure)
apply (rule Rep_WF_BINDING_intro)
apply (simp add:closure)
apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b x \<rhd> x'")
apply (simp)
apply (rule ext)
apply (simp add: MapRename_def closure)
apply (auto)
done

theorem RenameP_id :
"p[id\<^sub>s] = p"
apply (utp_pred_auto_tac)
done

theorem RenameP_inverse1 :
"p[ss][inv\<^sub>s ss] = p"
apply (utp_pred_auto_tac)
done

theorem RenameP_inverse2 :
"p[inv\<^sub>s ss][ss] = p"
apply (utp_pred_auto_tac)
done

theorem RenameP_compose :
"p[ss1][ss2] = RenameP p (ss2 \<circ>\<^sub>s ss1)"
apply (utp_pred_tac)
apply (simp add: RenameB_compose closure)
done

theorem RenameP_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (p::'VALUE WF_PREDICATE)[ss1][ss2] = p[ss2][ss1]"
apply (utp_pred_tac)
apply (clarify)
apply (subst RenameB_commute [of "(inv\<^sub>s ss1)" "vs1" "(inv\<^sub>s ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

theorem RenameP_involution [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_INV\<rbrakk> \<Longrightarrow>
 p[ss][ss] = p"
apply (utp_pred_auto_tac)
done

theorems rename_simps =
  RenameP_id
  RenameP_inverse1
  RenameP_inverse2
  RenameP_compose
  RenameP_involution

declare rename_simps [urename]

subsection {* Distribution theorems *}

theorem RenameP_image_union [urename]:
  "\<langle>ss\<rangle>\<^sub>s ` (vs1 \<union> vs2) = \<langle>ss\<rangle>\<^sub>s ` vs1 \<union> \<langle>ss\<rangle>\<^sub>s ` vs2"
  by auto

theorem RenameP_image_inter [urename]:
  "\<langle>ss\<rangle>\<^sub>s ` (vs1 \<inter> vs2) = \<langle>ss\<rangle>\<^sub>s ` vs1 \<inter> \<langle>ss\<rangle>\<^sub>s ` vs2"
  by (auto, metis Rep_VAR_RENAME VAR_RENAME_in_image)

theorem RenameP_image_minus [urename]:
  "\<langle>ss\<rangle>\<^sub>s ` (vs1 - vs2) = \<langle>ss\<rangle>\<^sub>s ` vs1 - \<langle>ss\<rangle>\<^sub>s ` vs2"
  by (metis Rep_VAR_RENAME_inj image_set_diff)
 
lemma RenameP_image_uminus [urename]: 
  "\<langle>ss\<rangle>\<^sub>s ` (- vs) = - (\<langle>ss\<rangle>\<^sub>s ` vs)"
  by (metis (lifting) Rep_VAR_RENAME_bij bij_image_Compl_eq) 

theorems rename_dist =
  RenameP_image_union
  RenameP_image_inter
  RenameP_image_minus
  RenameP_image_uminus

subsubsection {* Predicate Renaming Theorems *}

theorem RenameP_NotP_distr [urename]:
"(\<not>p p)[ss] = \<not>p p[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_AndP_distr [urename]:
"(p1 \<and>p p2)[ss] = p1[ss] \<and>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_OrP_distr [urename]:
"(p1 \<or>p p2)[ss] = p1[ss] \<or>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_ImpliesP_distr [urename]:
"(p1 \<Rightarrow>p p2)[ss] = p1[ss] \<Rightarrow>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_IffP_distr [urename]:
"(p1 \<Leftrightarrow>p p2)[ss] = p1[ss] \<Leftrightarrow>p p2[ss]"
  by (utp_pred_auto_tac)

theorem RenameP_RefP_distr [urename]:
"(p1 \<sqsubseteq>p p2)[ss] = p1[ss] \<sqsubseteq>p p2[ss]"
  apply (utp_pred_auto_tac)
  apply (metis RenameB_inv_cancel1)
done

theorem RenameP_ExistsP_distr1 [urename]:
"(\<exists>p vs . p)[ss] = (\<exists>p ss `\<^sub>s vs . p[ss])"
apply (utp_pred_auto_tac)
apply (rule_tac x="RenameB ss b'" in exI)
apply (simp add:RenameB_override_distr1 closure)
apply (rule_tac x="RenameB (inv\<^sub>s ss) b'" in exI)
apply (simp add:RenameB_override_distr1 closure)
done

theorem RenameP_ExistsP_distr2 [urename]:
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<exists>p vs2 . p)[ss] = (\<exists>p vs2 . p[ss])"
  apply (simp add:RenameP_ExistsP_distr1)
  apply (metis VAR_RENAME_ON_disj_image rename_image_def)
done

theorem RenameP_ForallP_distr [urename]:
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (\<forall>p vs2 . p)[ss] = (\<forall>p vs2 . p[ss])"
apply (simp add: ForallP_def closure)
apply (simp add: RenameP_ExistsP_distr2 RenameP_NotP_distr closure)
done

theorem RenameP_ClosureP_1 [urename]:
"[p[ss]]p = [p]p"
apply (utp_pred_tac)
apply (safe)
apply (drule_tac x = "RenameB ss x" in spec)
apply (simp_all)
done

theorem RenameP_ClosureP_2 [urename]:
"[p]p[ss] = [p]p"
  by (utp_pred_tac)

theorem RenameP_TrueP [urename]:
  "true[ss] = true"
  by (utp_pred_tac)

theorem RenameP_FalseP [urename]:
  "false[ss] = false"
  by (utp_pred_tac)

theorem RenameP_VarP [urename]:
"(VarP x)[ss] = VarP (\<langle>ss\<rangle>\<^sub>s x)"
  by (utp_pred_tac, utp_expr_tac)

theorem RenameP_EqualP [urename]:
"(e ==p f)[ss] = e[ss]\<epsilon> ==p f[ss]\<epsilon>"
  by (utp_pred_tac, utp_expr_tac)

theorem RenameP_ExprP [urename]:
"(ExprP e)[ss] = ExprP (e[ss]\<epsilon>)"
  by (utp_pred_tac, utp_expr_tac)

lemma RenameP_SubstP [urename]:
  "\<lbrakk> ss \<in> VAR_RENAME_INV; v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> p[v|x][ss] = p[ss][v[ss]\<epsilon>|\<langle>ss\<rangle>\<^sub>s x]"
  by (utp_pred_tac, utp_expr_tac)

theorem RenameP_UNREST [simp]:
"\<lbrakk> UNREST vs p; ss \<in> VAR_RENAME_ON vs \<rbrakk> \<Longrightarrow> p[ss] = p"
  apply (utp_pred_tac)
  apply (rule allI)
  apply (frule VAR_RENAME_ON_inv)
  apply (simp add:VAR_RENAME_ON_def)
  apply (simp add:RenameB_def EvalP_def UNREST_def)
  apply (rule iffI)
  apply (subgoal_tac "(CompB b ss) \<oplus>\<^sub>b b on vs = b")
  apply (drule_tac x="CompB b ss" in bspec, simp)
  apply (drule_tac x="b" in spec, simp)
  apply (force simp add:override_on_def) 
  apply (subgoal_tac "b \<oplus>\<^sub>b (CompB b ss) on vs = CompB b ss")
  apply (drule_tac x="b" in bspec, simp)
  apply (drule_tac x="CompB b ss" in spec)
  apply (simp)
  apply (force simp add:override_on_def) 
done

lemma RenameP_equiv:
  "\<lbrakk> UNREST (VAR - vs) p; ss1 \<cong>\<^sub>s ss2 on vs \<rbrakk> \<Longrightarrow> p[ss1] = p[ss2]"
  apply (utp_pred_tac)
  apply (simp add: EvalP_def rename_equiv_def rename_equiv_def RenameB_def)
  apply (clarify)
  apply (subgoal_tac "CompB b ss1 \<cong> CompB b ss2 on vs")
  apply (simp add:UNREST_def)
  apply (auto)
  apply (drule_tac x="CompB b ss1" in bspec,simp)
  apply (smt binding_override_equiv binding_override_simps(10) binding_override_simps(2) binding_override_simps(4) binding_override_simps(5) binding_override_subset)
  apply (drule_tac x="CompB b ss2" in bspec,simp)
  apply (metis binding_override_equiv binding_override_simps(10) binding_override_simps(5) binding_override_subset)
  apply (simp add:binding_equiv_def)
done

theorem RenameP_invariant_taut :
"taut [p1 \<Leftrightarrow>p p2]p \<Leftrightarrow>p [p1[ss] \<Leftrightarrow>p p2[ss]]p"
apply (subgoal_tac "p1[ss] \<Leftrightarrow>p p2[ss] = (p1 \<Leftrightarrow>p p2)[ss]")
apply (simp)
apply (simp add: RenameP_ClosureP_1 closure)
apply (utp_pred_tac)
apply (simp add: RenameP_IffP_distr)
done

subsubsection {* Expression Renaming Theorems *}

theorem RenameE_id [urename]:
"p[id\<^sub>s]\<epsilon> = p"
  by (utp_expr_tac)

theorem RenameE_inverse1 [urename]:
"e[ss]\<epsilon>[inv\<^sub>s ss]\<epsilon> = e"
  by (utp_expr_tac)

theorem RenameE_inverse2 [urename]:
"e[inv\<^sub>s ss]\<epsilon>[ss]\<epsilon> = e"
  by (utp_expr_tac)

theorem RenameE_compose [urename]:
"e[ss1]\<epsilon>[ss2]\<epsilon> = e[ss2 \<circ>\<^sub>s ss1]\<epsilon>"
apply (utp_expr_tac)
apply (simp add: RenameB_compose closure)
done

theorem RenameE_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (e::'VALUE WF_EXPRESSION)[ss1]\<epsilon>[ss2]\<epsilon> = e[ss2]\<epsilon>[ss1]\<epsilon>"
apply (utp_expr_tac)
apply (clarify)
apply (subst RenameB_commute [of "(inv\<^sub>s ss1)" "vs1" "(inv\<^sub>s ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

lemma RenameE_equiv:
  "\<lbrakk> UNREST_EXPR (VAR - vs) e; ss1 \<cong>\<^sub>s ss2 on vs \<rbrakk> \<Longrightarrow> e[ss1]\<epsilon> = e[ss2]\<epsilon>"
  apply (utp_expr_tac)
  apply (simp add: EvalE_def rename_equiv_def rename_equiv_def RenameB_def)
  apply (clarify)
  apply (subgoal_tac "CompB b ss1 \<cong> CompB b ss2 on vs")
  apply (simp add:UNREST_EXPR_def)
  apply (drule_tac x="CompB b ss1" in spec)
  apply (drule_tac x="CompB b ss2" in spec)
  apply (smt binding_override_equiv binding_override_simps(10) binding_override_simps(2) binding_override_simps(4) binding_override_simps(5) binding_override_subset)
  apply (simp add:binding_equiv_def)
done

theorem RenameE_involution [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_INV\<rbrakk> \<Longrightarrow>
 p[ss]\<epsilon>[ss]\<epsilon> = p"
  by (utp_expr_tac)

theorem RenameE_VarE [urename]:
"(VarE x)[ss]\<epsilon> = VarE (\<langle>ss\<rangle>\<^sub>s x)"
  by (utp_expr_tac)

theorem RenameE_LitE [urename]:
  "v : t \<Longrightarrow> (LitE v)[ss]\<epsilon> = LitE v"
  by (utp_expr_tac)

theorem RenameE_TrueE [urename]:
  "(TrueE[ss]\<epsilon>) = TrueE"
  by (utp_expr_tac)

theorem RenameE_FalseE [urename]:
  "(FalseE[ss]\<epsilon>) = FalseE"
  by (utp_expr_tac)

end
