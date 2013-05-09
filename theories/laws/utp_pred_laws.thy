(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred_laws.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Predicate Algebraic Laws *}

theory utp_pred_laws
imports 
  "../core/utp_pred" 
  "../core/utp_rename"
  "../core/utp_expr"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../parser/utp_pred_parser"
  utp_subst_laws
begin

subsubsection {* Boolean Algebra laws *}

theorem AndP_comm :
"`p1 \<and> p2` = `p2 \<and> p1`"
  by (utp_pred_auto_tac)

theorem AndP_idem [simp]:
"`p \<and> p` = p"
  by (utp_pred_auto_tac)

theorem AndP_assoc :
"`p1 \<and> (p2 \<and> p3)` = `(p1 \<and> p2) \<and> p3`"
  by (utp_pred_auto_tac)

theorem AndP_OrP_distl :
"`p1 \<and> (p2 \<or> p3)` = `(p1 \<and> p2) \<or> (p1 \<and> p3)`"
  by (utp_pred_auto_tac)

theorem AndP_OrP_distr:
"`(p1 \<or> p2) \<and> p3` = `(p1 \<and> p3) \<or> (p2 \<and> p3)`"
  by (utp_pred_auto_tac)

theorem OrP_comm :
"`p1 \<or> p2` = `p2 \<or> p1`"
  by (utp_pred_auto_tac)

theorem OrP_idem [simp]:
"`p \<or> p` = p"
  by (utp_pred_auto_tac)

theorem OrP_assoc :
"`p1 \<or> (p2 \<or> p3)` = `(p1 \<or> p2) \<or> p3`"
  by (utp_pred_auto_tac)

theorem OrP_AndP_distl :
"`p1 \<or> (p2 \<and> p3)` = `(p1 \<or> p2) \<and> (p1 \<or> p3)`"
  by (utp_pred_auto_tac)

theorem OrP_AndP_distr :
"`(p1 \<and> p2) \<or> p3` = `(p1 \<or> p3) \<and> (p2 \<or> p3)`"
  by (utp_pred_auto_tac)

theorem AndP_contra :
"`p \<and> \<not> p` = false"
  by (utp_pred_auto_tac)

theorem OrP_excluded_middle :
"p \<or>p \<not>p p = true"
  by (utp_pred_auto_tac)

theorem OrP_ref :
"`p1 \<or> p2` \<sqsubseteq> p1"
  by (utp_pred_auto_tac)

lemma demorgan1: "`\<not>(x \<or> y)` = `\<not>x \<and> \<not>y`"
  by (utp_pred_auto_tac)

lemma demorgan2: "`\<not>(x \<and> y)` = `\<not>x \<or> \<not>y`"
  by (utp_pred_auto_tac)

lemma demorgan3: "`x \<or> y` = `\<not>(\<not>x \<and> \<not>y)`"
  by (utp_pred_auto_tac)

lemma utp_pred_simps [simp]:
  "`\<not> false`    = true"
  "`\<not> true`     = false"
  "`\<not> \<not> p` = p"
  "`false \<and> x`  = false" 
  "`x \<and> false`  = false"
  "`true \<and> x`   = x"
  "`x \<and> true`   = x"
  "`true \<or> x`   = true"
  "`x \<or> true`   = true"
  "`false \<or> x`  = x"
  "`x \<or> false`  = x"
  "`false \<Rightarrow> x` = true" 
  "`true \<Rightarrow> x`  = x" 
  "`p \<Rightarrow> true` = true" 
  "`p \<Rightarrow> false` = `\<not> p`"
  by (utp_pred_tac)+

subsection {* Introduction rules *}

lemma RefP_OrP: "p \<sqsubseteq> q \<longleftrightarrow> p = p \<or>p q"
  by (utp_pred_auto_tac)

lemma RefP_OrP_intro [intro]:
  "`p \<or> q` = `p` \<Longrightarrow> `p \<sqsubseteq> q`"
  by (utp_pred_auto_tac)

lemma RefP_AndP: "p \<sqsubseteq> q \<longleftrightarrow> q = p \<and>p q"
  by (utp_pred_auto_tac)

lemma RefP_AndP_intro [intro]:
  "`p \<and> q` = `q` \<Longrightarrow> `p \<sqsubseteq> q`"
  by (utp_pred_auto_tac)

lemma IffP_eq_intro [intro]:
  "`p \<Leftrightarrow> q` \<Longrightarrow> p = q"
  by (utp_pred_auto_tac)

lemma ClosureP_intro: 
  "`[p]` \<Longrightarrow> taut p"
  by (utp_pred_tac)

subsection {* Quantifier Laws *}

theorem ExistsP_ident :
"\<lbrakk>UNREST vs p\<rbrakk> \<Longrightarrow> (\<exists>p vs . p) = p"
  by (utp_pred_tac)

theorem ForallP_ident :
"\<lbrakk>UNREST vs p\<rbrakk> \<Longrightarrow> (\<forall>p vs . p) = p"
  by (utp_pred_tac)

theorem ExistsP_union :
"(\<exists>p vs1 \<union> vs2 . p) = (\<exists>p vs1 . \<exists>p vs2 . p)"
apply (utp_pred_tac)
apply (auto)
apply (rule_tac x = "b'" in exI)
apply (rule_tac x = "b'" in exI)
apply (simp)+
apply (rule_tac x = "b' \<oplus>\<^sub>b b'a on vs2" in exI)
apply (simp add: binding_override_assoc)
done

theorem ForallP_union :
"(\<forall>p vs1 \<union> vs2 . p) = (\<forall>p vs1 . \<forall>p vs2 . p)"
  by (simp add: ForallP_def ExistsP_union UNREST_NotP NotP_NotP)

theorem ExistsP_OrP_expand:
"(\<exists>p vs. p1 \<or>p p2) = (\<exists>p vs. p1) \<or>p (\<exists>p vs. p2)"
  by (utp_pred_auto_tac)

theorem ExistsP_AndP_expand1:
"\<lbrakk>UNREST vs p2\<rbrakk> \<Longrightarrow>
 (\<exists>p vs. p1) \<and>p p2 = (\<exists>p vs. (p1 \<and>p p2))"
  by (utp_pred_tac)

theorem ExistsP_AndP_expand2:
"\<lbrakk>UNREST vs p1\<rbrakk> \<Longrightarrow>
 p1 \<and>p (\<exists>p vs. p2) = (\<exists>p vs. (p1 \<and>p p2))"
  by (utp_pred_tac)

text {* The one point rule *}
theorem ExistsP_one_point:
  "\<lbrakk> e \<rhd>\<^sub>e x; UNREST_EXPR {x} e \<rbrakk> \<Longrightarrow>
  `\<exists> x. (p \<and> $x = e)` = `p[e/x]`"
  apply (auto simp add:eval evale typing defined)
  apply (rule_tac x="b(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<epsilon>b)" in exI)
  apply (simp)
done

lemma ExistsP_has_value:
  "\<lbrakk> UNREST_EXPR {x} v; v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> `\<exists> x. $x = v` = `true`"
  apply (utp_pred_tac, utp_expr_tac)
  apply (auto)
  apply (rule_tac x="b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b)" in exI)
  apply (simp)
done

theorem ExistsP_SubstP_rename :
  "\<lbrakk> vtype x = vtype y; aux x = aux y; UNREST {x} p \<rbrakk> 
   \<Longrightarrow> `\<exists> y. p` = `\<exists> x. p[$x/y]`"
  apply (simp add:eval evale typing defined unrest binding_upd_twist)
  apply (clarify)
  apply (rule, erule exE)
  apply (rule_tac x="b(x :=\<^sub>b \<langle>b'\<rangle>\<^sub>b y)" in exI)
  apply (simp add:typing eval defined binding_upd_twist)
  apply (metis EvalP_UNREST_assign_1 binding_upd_twist binding_value_alt)
  apply (erule exE)
  apply (rule_tac x="b(y :=\<^sub>b \<langle>b'\<rangle>\<^sub>b x)" in exI)
  apply (simp add:typing eval defined binding_upd_twist)
  apply (metis EvalP_UNREST_assign_1 binding_upd_twist binding_value_alt)
done

subsection {* Expression theorems *}

lemma VarP_EqualP_aux:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
   `$x` = `$x = true`"
  apply (utp_pred_tac, utp_expr_tac)
  apply (auto)
  apply (metis BOOL_SORT_class.Inverse FalseV_def MkBool_cases TrueV_def aux_defined binding_type)
done

lemma VarP_NotP_EqualP_aux:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
   `\<not> $x` = `$x = false`"
  apply (utp_pred_tac, utp_expr_tac)
  apply (auto)
  apply (metis BOOL_SORT_class.Inverse FalseV_def MkBool_cases TrueV_def aux_defined binding_type)
done

lemma expr_simps [simp]:
  "ExprP TrueE = TrueP"
  "ExprP FalseE = FalseP"
  by (utp_pred_tac)+

subsection {* Case splitting *}

ML {*
  structure ucases =
    Named_Thms (val name = @{binding ucases} val description = "case splitting theorems")
*}

setup ucases.setup

lemma BoolType_aux_var_split_taut [ucases]:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
  `[p]` = `[p[false/x] \<and> p[true/x]]`"
  apply (utp_pred_tac, utp_expr_tac) 
  apply (metis FalseV_def MkBool_cases Rep_WF_BINDING_inverse TrueV_def aux_defined binding_type binding_upd_def fun_upd_idem_iff)
done

lemma BoolType_aux_var_split_exists [ucases]:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
   `\<exists> x. P` = `P[false/x] \<or> P[true/x]`"
  apply (utp_pred_tac, utp_expr_tac)
  apply (auto)
  apply (metis FalseV_def MkBool_cases Rep_WF_BINDING TrueV_def WF_BINDING_app_type aux_defined)
  apply (metis BOOL_SORT_class.Defined MkBool_type binding_upd_apply var_compat_def)
  apply (metis BOOL_SORT_class.Defined MkBool_type binding_upd_apply var_compat_def)
done

lemma BoolType_aux_var_split_eq_intro [ucases]:
  assumes "vtype x = BoolType" "aux x" 
          "`p[false/x]` = `q[false/x]`"
          "`p[true/x]` = `q[true/x]`"
  shows "p = q"
  apply (rule IffP_eq_intro)
  apply (rule ClosureP_intro)
  apply (unfold BoolType_aux_var_split_taut[OF assms(1) assms(2), of "`p \<Leftrightarrow> q`"])
  apply (simp add:usubst assms)
  apply (utp_pred_tac)
done

end