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

text {* A renamed binding can be overriden with an arbitrary binding on the 
        variables being renamed. *}

lemma EvalP_rename_on_expand_binding:
  "\<lbrakk> rename_func_on f vs; (f`vs) \<sharp> P \<rbrakk> 
     \<Longrightarrow> \<lbrakk>P\<rbrakk>(f on vs \<bullet> b) = \<lbrakk>P\<rbrakk>(f on vs \<bullet> (b \<oplus>\<^sub>b b' on vs))"
  apply (auto simp add: EvalP_def UNREST_def RenameB_override_distr1)
  apply (drule_tac x="f on vs \<bullet> b \<oplus>\<^sub>b f on vs \<bullet> b' on f ` vs" in bspec, simp)
  apply (metis binding_override_simps(2) binding_override_simps(3))
done


theorem RenameP_id :
  fixes p :: "'a WF_PREDICATE"
  shows "id\<^sub>s\<bullet>p = p"
  by (utp_pred_auto_tac)

theorem RenameP_inverse1 :
  fixes p :: "'a WF_PREDICATE"
  shows "inv\<^sub>s ss \<bullet> ss \<bullet> p = p"
  by (utp_pred_auto_tac)

theorem RenameP_inverse2 :
  fixes p :: "'a WF_PREDICATE"
  shows "ss \<bullet> inv\<^sub>s ss \<bullet> p = p"
  by (utp_pred_auto_tac)

theorem RenameP_compose :
  fixes p :: "'a WF_PREDICATE"
  shows "ss1 \<bullet> ss2 \<bullet> p = (ss1 \<circ>\<^sub>s ss2) \<bullet> p"
apply (utp_pred_tac)
apply (simp add: RenameB_compose closure)
done

theorem RenameP_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss2\<bullet>ss1\<bullet>(p :: 'a WF_PREDICATE) = ss1\<bullet>ss2\<bullet>p"
apply (utp_pred_tac)
apply (clarify)
apply (subst RenameB_commute [of "(inv\<^sub>s ss1)" "vs1" "(inv\<^sub>s ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

theorem RenameP_involution [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_INV\<rbrakk> \<Longrightarrow>
 ss\<bullet>ss\<bullet>(p :: 'a WF_PREDICATE) = p"
  by (utp_pred_auto_tac)

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
"ss \<bullet> (\<not>\<^sub>p p) = \<not>\<^sub>p (ss \<bullet> p)"
  by (utp_pred_auto_tac)

theorem RenameP_AndP_distr [urename]:
"ss \<bullet> (p1 \<and>\<^sub>p p2) = (ss \<bullet> p1) \<and>\<^sub>p (ss \<bullet> p2)"
  by (utp_pred_auto_tac)

theorem RenameP_OrP_distr [urename]:
"ss \<bullet> (p1 \<or>\<^sub>p p2) = (ss \<bullet> p1) \<or>\<^sub>p (ss \<bullet> p2)"
  by (utp_pred_auto_tac)

theorem RenameP_ImpliesP_distr [urename]:
"ss \<bullet> (p1 \<Rightarrow>\<^sub>p p2) = (ss \<bullet> p1) \<Rightarrow>\<^sub>p (ss \<bullet> p2)"
  by (utp_pred_auto_tac)

theorem RenameP_IffP_distr [urename]:
"ss \<bullet> (p1 \<Leftrightarrow>\<^sub>p p2) = (ss\<bullet>p1) \<Leftrightarrow>\<^sub>p (ss\<bullet>p2)"
  by (utp_pred_auto_tac)

theorem RenameP_RefP_distr [urename]:
"ss\<bullet>(p1 \<sqsubseteq>\<^sub>p p2) = (ss\<bullet>p1) \<sqsubseteq>\<^sub>p (ss\<bullet>p2)"
  apply (utp_pred_auto_tac)
  apply (metis RenameB_inv_cancel1)
done

theorem RenameP_ExistsP_distr1 [urename]:
"ss\<bullet>(\<exists>\<^sub>p vs . p) = (\<exists>\<^sub>p ss `\<^sub>s vs . (ss\<bullet>p))"
apply (utp_pred_auto_tac)
apply (rule_tac x="RenameB ss b'" in exI)
apply (simp add:RenameB_override_distr1 closure)
apply (rule_tac x="RenameB (inv\<^sub>s ss) b'" in exI)
apply (simp add:RenameB_override_distr1 closure)
done

theorem RenameP_ExistsP_distr2 [urename]:
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss\<bullet>(\<exists>\<^sub>p vs2 . p) = (\<exists>\<^sub>p vs2 . ss\<bullet>p)"
  apply (simp add:RenameP_ExistsP_distr1)
  apply (metis VAR_RENAME_ON_disj_image rename_image_def)
done

theorem RenameP_ForallP_distr [urename]:
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss\<bullet>(\<forall>\<^sub>p vs2 . p) = (\<forall>\<^sub>p vs2 . ss\<bullet>p)"
  by (simp add: ForallP_def RenameP_ExistsP_distr2 RenameP_NotP_distr closure)

theorem RenameP_ClosureP_1 [urename]:
"[ss\<bullet>p]\<^sub>p = [p]\<^sub>p"
apply (utp_pred_tac)
apply (safe)
apply (drule_tac x = "RenameB ss x" in spec)
apply (simp_all)
done

theorem RenameP_ClosureP_2 [urename]:
"ss\<bullet>[p]\<^sub>p = [p]\<^sub>p"
  by (utp_pred_tac)

theorem RenameP_TrueP [urename]:
  "ss\<bullet>true = true"
  by (utp_pred_tac)

theorem RenameP_FalseP [urename]:
  "ss\<bullet>false = false"
  by (utp_pred_tac)

theorem RenameP_VarP [urename]:
"ss\<bullet>($\<^sub>px) = $\<^sub>p(\<langle>ss\<rangle>\<^sub>s x)"
  by (utp_pred_tac)

theorem RenameP_EqualP [urename]:
"ss\<bullet>(e ==\<^sub>p f) = (ss\<bullet>e) ==\<^sub>p (ss\<bullet>f)"
  by (utp_pred_tac)

theorem RenameP_ExprP [urename]:
"ss\<bullet>(ExprP e) = ExprP (ss\<bullet>e)"
  by (utp_pred_tac)

lemma RenameP_SubstP [urename]:
  "ss\<bullet>(p[v/\<^sub>px]) = (ss\<bullet>p)[ss\<bullet>v/\<^sub>pss\<bullet>x]"
  by (utp_pred_tac)

theorem RenameP_UNREST [simp]:
"\<lbrakk> UNREST vs p; ss \<in> VAR_RENAME_ON vs \<rbrakk> \<Longrightarrow> ss\<bullet>p = p"
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
  "\<lbrakk> UNREST (VAR - vs) p; ss1 \<cong>\<^sub>s ss2 on vs \<rbrakk> \<Longrightarrow> ss1\<bullet>p = ss2\<bullet>p"
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
"taut [p1 \<Leftrightarrow>\<^sub>p p2]\<^sub>p \<Leftrightarrow>\<^sub>p [(ss\<bullet>p1) \<Leftrightarrow>\<^sub>p (ss\<bullet>p2)]\<^sub>p"
apply (subgoal_tac "(ss\<bullet>p1) \<Leftrightarrow>\<^sub>p (ss\<bullet>p2) = ss\<bullet>(p1 \<Leftrightarrow>\<^sub>p p2)")
apply (simp)
apply (simp add: RenameP_ClosureP_1 closure)
apply (utp_pred_tac)
apply (simp add: RenameP_IffP_distr)
done

subsubsection {* Expression Renaming Theorems *}

theorem RenameE_id [urename]:
  fixes e :: "'a WF_EXPRESSION"
  shows "id\<^sub>s\<bullet>e = e"
  by (utp_expr_tac)

theorem RenameE_inverse1 [urename]:
  fixes e :: "'a WF_EXPRESSION"
  shows "(inv\<^sub>s ss)\<bullet>ss\<bullet>e = e"
  by (utp_expr_tac)

theorem RenameE_inverse2 [urename]:
  fixes e :: "'a WF_EXPRESSION"
  shows "ss\<bullet>(inv\<^sub>s ss)\<bullet>e = e"
  by (utp_expr_tac)

theorem RenameE_compose [urename]:
  fixes e :: "'a WF_EXPRESSION"
  shows "ss1\<bullet>ss2\<bullet>e = (ss1 \<circ>\<^sub>s ss2)\<bullet>e"
apply (utp_expr_tac)
apply (simp add: RenameB_compose closure)
done

theorem RenameE_involution [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_INV\<rbrakk> \<Longrightarrow>
 ss\<bullet>ss\<bullet>e = (e :: 'a WF_EXPRESSION)"
  by (utp_expr_tac)

theorem RenameE_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss2 \<bullet> ss1 \<bullet> (e::'VALUE WF_EXPRESSION) = ss1 \<bullet> ss2 \<bullet> e"
apply (utp_expr_tac)
apply (clarify)
apply (subst RenameB_commute [of "(inv\<^sub>s ss1)" "vs1" "(inv\<^sub>s ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

lemma RenameE_equiv:
  "\<lbrakk> UNREST_EXPR (VAR - vs) e; ss1 \<cong>\<^sub>s ss2 on vs \<rbrakk> \<Longrightarrow> ss1\<bullet>e = ss2\<bullet>e"
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

theorem RenameE_VarE [urename]:
  "ss \<bullet> $\<^sub>ex = $\<^sub>e(ss \<bullet> x)"
  by (utp_expr_tac)

theorem RenameE_LitE [urename]:
  "v : t \<Longrightarrow> ss\<bullet>(LitE v) = LitE v"
  by (utp_expr_tac)

theorem RenameE_TrueE [urename]:
  "(ss\<bullet>TrueE) = TrueE"
  by (utp_expr_tac)

theorem RenameE_FalseE [urename]:
  "(ss\<bullet>FalseE) = FalseE"
  by (utp_expr_tac)

subsubsection {* Expression Prime Theorems *}

theorem PrimeE_double [urename]:
  fixes v :: "'a WF_EXPRESSION"
  shows "v\<acute>\<acute> = v"
  by (utp_expr_tac)

theorem PrimeE_TrueE [urename]:
  "TrueE\<acute> = TrueE"
  by (utp_expr_tac)

theorem PrimeE_FalseE [urename]:
  "FalseE\<acute> = FalseE"
  by (utp_expr_tac)

theorem PrimeE_LitE [urename]:
  "v : t \<Longrightarrow> (LitE v)\<acute> = LitE v"
  by (utp_expr_tac)

theorem PrimeE_VarE [urename]:
  "x \<in> UNDASHED \<Longrightarrow> ($\<^sub>ex)\<acute> = $\<^sub>ex\<acute>"
  by (simp add:PrimeE_def urename closure rename_on_perm1)

end
