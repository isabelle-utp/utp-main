(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_expr.thy                                                         *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Expressions *}

theory utp_expr
imports utp_sorts utp_pred utp_unrest
begin

context PRED_BOT
begin

definition etype_rel ::
  "('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":e" 50) where
"etype_rel e t = (\<forall> b \<in> WF_BINDING . (e b) : t)"

definition UNREST_BFUN ::
  "('TYPE VAR) set \<Rightarrow> ('VALUE, 'TYPE) BINDING_FUN \<Rightarrow> bool" where
"UNREST_BFUN vs f =
 (\<forall> b1 \<in> WF_BINDING . \<forall> b2 \<in> WF_BINDING . f (b1 \<oplus> b2 on vs) = f b1)"

text {*
  A well-formed expression must produce a well-typed value for every binding,
  and for bindings that are not well-formed yield the aribtrary value.
*}

definition WF_EXPRESSION :: "('VALUE, 'TYPE) BINDING_FUN set" where
"WF_EXPRESSION =
 {f . \<exists> t . \<forall> b . if (b \<in> WF_BINDING) then (f b) : t else (f b) = bot}"

definition WF_EXPRESSION_OVER ::
  "('TYPE VAR) set \<Rightarrow> ('VALUE, 'TYPE) BINDING_FUN set" where
"WF_EXPRESSION_OVER vs = {e . e \<in> WF_EXPRESSION \<and> UNREST_BFUN (VAR - vs) e}"

subsection {* Construction *}

definition wf_expr ::
"('VALUE, 'TYPE) EXPRESSION \<Rightarrow>
 ('VALUE, 'TYPE) EXPRESSION" where
"wf_expr f \<equiv> (\<lambda> b. if (b \<in> WF_BINDING) then (f b) else bot)"

subsubsection {* Literal Values *}

definition LitE :: "'VALUE \<Rightarrow> ('VALUE, 'TYPE) EXPRESSION" where
"LitE v = wf_expr (\<lambda> b. v)"

subsubsection {* Plain Variable *}

definition VarE :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) EXPRESSION" where
"VarE x = wf_expr (\<lambda> b . b x)"

subsection {* Operators *}

subsubsection {* Equality *}

definition EqualE ::
"('VALUE, 'TYPE) EXPRESSION \<Rightarrow>
 ('VALUE, 'TYPE) EXPRESSION \<Rightarrow>
 ('VALUE, 'TYPE) PREDICATE" where
"e1 \<in> WF_EXPRESSION \<and>
 e2 \<in> WF_EXPRESSION \<longrightarrow>
 EqualE e1 e2 = {b \<in> WF_BINDING. (e1 b) = (e2 b)}"

notation EqualE (infixr "=e" 150)

subsubsection {* Substitution *}

definition SubstE ::
"('VALUE, 'TYPE) EXPRESSION \<Rightarrow>
 ('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 'TYPE VAR \<Rightarrow>
 ('VALUE, 'TYPE) EXPRESSION" ("_[_'/_]" [200]) where
"e1 \<in> WF_EXPRESSION \<and>
 e2 \<in> WF_EXPRESSION \<longrightarrow>
 SubstE e1 e2 v = wf_expr (\<lambda> b . e1 (b(v := (e2 b))))"

subsection {* Theorems *}

subsubsection {* Well-formed Expression Theorems *}

-- {* It would be nice to have this as a typing rule, but it confuses the
      HO unifier... *}

theorem WF_EXPRESSION_type :
"\<lbrakk>e \<in> WF_EXPRESSION; e :e t\<rbrakk> \<Longrightarrow> (e b) : t"
apply (simp add: WF_EXPRESSION_def etype_rel_def)
apply (case_tac "b \<in> WF_BINDING")
apply (simp add: WF_BINDING_def)
apply (auto intro: bot_type)
done

theorem WF_EXPRESSION_has_type [typing] :
"\<lbrakk>e \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow> (\<exists> t. e :e t)"
apply (auto simp add: WF_EXPRESSION_def etype_rel_def)
apply (rule_tac x = "t" in exI)
apply (auto)
done

theorem WF_EXPRESSION_default [simp] :
"\<lbrakk>e \<in> WF_EXPRESSION; b \<notin> WF_BINDING\<rbrakk> \<Longrightarrow> (e b) = bot"
  by (auto simp add: WF_EXPRESSION_def)

theorem WF_EXPRESSION_wf_expr_ebody [simp] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (wf_expr e) b = (e b)"
  by (simp add: wf_expr_def)

theorem WF_EXPRESSION_wf_expr_type [simp] :
"(wf_expr e) :e t \<longleftrightarrow> e :e t"
  by (simp add: wf_expr_def etype_rel_def)

theorem etype_rel_intro [intro, typing] :
"\<lbrakk>\<forall> b \<in> WF_BINDING . (e b) : t\<rbrakk> \<Longrightarrow> e :e t"
  by (simp add: etype_rel_def)

theorem etype_rel_dest [dest] :
"e :e t \<Longrightarrow> \<forall> b \<in> WF_BINDING . (e b) : t"
  by (simp add: etype_rel_def)

subsubsection {* Closure Theorems *}

theorem WF_EXPRESSION_wf_expr [closure] :
"f :e t \<Longrightarrow> wf_expr f \<in> WF_EXPRESSION"
apply (simp only: WF_EXPRESSION_def wf_expr_def etype_rel_def)
apply (auto)
done

theorem WF_EXPRESSION_BODY_wf_expr_drop [simp] :
"e \<in> WF_EXPRESSION \<Longrightarrow> wf_expr e = e"
apply (simp add: WF_EXPRESSION_def wf_expr_def)
apply (auto)
done

theorem wf_expr_idem [simp] :
"wf_expr (wf_expr e) = wf_expr e"
  by (auto simp add: wf_expr_def)

theorem EqualE_closure [closure] :
"\<lbrakk>e1 \<in> WF_EXPRESSION;
 e2 \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow>
 e1 =e e2 \<in> WF_PREDICATE"
  by (auto intro: closure
    simp add: EqualE_def WF_EXPRESSION_def WF_PREDICATE_def WF_BINDING_def)

theorem VarE_closure [closure] :
"VarE x \<in> WF_EXPRESSION"
  by (auto intro!: closure
    simp add: VarE_def closure WF_BINDING_def etype_rel_def)

theorem LitE_closure [closure] :
assumes "v : t"
shows "LitE v \<in> WF_EXPRESSION"
proof -
  from assms have "v : (Eps (op : v))"
    by (auto intro: someI)

  thus ?thesis
    by (auto intro: closure simp add: LitE_def WF_BINDING_def etype_rel_def)
qed

theorem SubstE_closure [closure] :
 assumes
  "e1 \<in> WF_EXPRESSION"
  "e2 \<in> WF_EXPRESSION"
  "e2 :e (type v)"
 shows "(e1 :: ('VALUE,'TYPE) EXPRESSION)[e2/v] \<in> WF_EXPRESSION"
proof -
  obtain t where "e1 :e t"
    by (metis WF_EXPRESSION_has_type assms)

  with assms show ?thesis
    apply (simp add: SubstE_def WF_BINDING_def)
    apply (rule_tac t = "t" in WF_EXPRESSION_wf_expr)
    apply (auto simp add: etype_rel_def WF_BINDING_def)
  done
qed

subsubsection {* Typing Theorems *}

theorem VarE_type [typing] :
"(VarE v) :e (type v)"
  by (simp add: VarE_def WF_BINDING_def typing etype_rel_def)

theorem LitE_type [typing] :
"x : t \<Longrightarrow> (LitE x) :e t"
  by (simp add: LitE_def etype_rel_def typing)

theorem SubstE_type [typing] :
"\<lbrakk>e1 \<in> WF_EXPRESSION;
 e2 \<in> WF_EXPRESSION;
 e1 :e t; e2 :e (type v)\<rbrakk> \<Longrightarrow> e1[e2/v] :e t"
  by (simp add: SubstE_def WF_EXPRESSION_type etype_rel_def typing)

subsubsection {* @{const UNREST_BFUN} Theorems *}

theorem UNREST_BFUN_member [unrest] :
"\<lbrakk>f \<in> WF_EXPRESSION;
 UNREST_BFUN vs f;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 f b1 = f (b1 \<oplus> b2 on vs)"
apply (simp only: WF_EXPRESSION_def)
apply (unfold UNREST_BFUN_def)
apply (erule_tac x = "b1" in ballE)
apply (erule_tac x = "b2" in ballE)
apply (auto)
done

theorem UNREST_BFUN_empty [unrest] :
"e \<in> WF_EXPRESSION \<Longrightarrow> UNREST_BFUN {} e"
  by (simp add: UNREST_BFUN_def)

theorem UNREST_BFUN_subset [unrest] :
"\<lbrakk>UNREST_BFUN vs1 e;
 vs2 \<subseteq> vs1;
 e \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow>
 UNREST_BFUN vs2 e"
apply (simp add: UNREST_BFUN_def)
apply (clarify)
apply (subgoal_tac "e b1 = e (b1 \<oplus> b2 on vs1)")
apply (drule_tac x = "b1 \<oplus> b2 on vs2" in bspec)
apply (simp add: closure)
apply (drule_tac x = "b2" in bspec)
apply (simp add: closure)
apply (simp add: override_on_assoc)
apply (subgoal_tac "vs2 \<union> vs1 = vs1")
apply (auto)
done

theorem UNREST_EqualP [unrest] :
"\<lbrakk>e1 \<in> WF_EXPRESSION;
 e2 \<in> WF_EXPRESSION;
 UNREST_BFUN vs1 e1;
 UNREST_BFUN vs2 e2\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<inter> vs2) (e1 =e e2)"
apply (auto simp add: EqualE_def)
apply (drule_tac ?vs2.0 = "vs1 \<inter> vs2" in UNREST_BFUN_subset)
apply (simp_all)
apply (drule_tac ?vs2.0 = "vs1 \<inter> vs2" in UNREST_BFUN_subset)
apply (simp_all)
apply (simp add: UNREST_BFUN_def UNREST_def)
apply (safe)
apply (rule closure)
apply (simp_all)
done

theorem UNREST_BFUN_wf_expr [unrest] :
"UNREST_BFUN vs e \<Longrightarrow>
 UNREST_BFUN vs (wf_expr e)"
  by (simp add: wf_expr_def UNREST_BFUN_def closure)

theorem UNREST_BFUN_VarE [unrest] :
"UNREST_BFUN (vs - {x}) (VarE x)"
apply (simp add: VarE_def)
apply (rule unrest)
apply (simp add: UNREST_BFUN_def)
done

theorem UNREST_BFUN_LitE [unrest] :
"UNREST_BFUN vs (LitE v)"
apply (simp add: LitE_def)
apply (rule unrest)
apply (simp add: UNREST_BFUN_def)
done

theorem UNREST_BFUN_SubstE [unrest] :
"\<lbrakk>e1 \<in> WF_EXPRESSION;
 e2 \<in> WF_EXPRESSION;
 e2 :e (type v);
 UNREST_BFUN vs1 e1;
 UNREST_BFUN vs2 e2\<rbrakk> \<Longrightarrow>
 UNREST_BFUN ((vs1 \<union> {v}) \<inter> vs2) (e1[e2/v])"
apply (subgoal_tac "UNREST_BFUN (vs1 \<inter> vs2) e1")
apply (subgoal_tac "UNREST_BFUN ((vs1 \<union> {v}) \<inter> vs2) e2")
apply (subgoal_tac "UNREST_BFUN ((vs1 \<union> {v}) \<inter> vs2 - {v}) e1")
apply (simp add: SubstE_def)
apply (rule unrest)
apply (simp add: UNREST_BFUN_def)
apply (clarify)
apply (subgoal_tac "b1(v := e2 b1) \<in> WF_BINDING")
apply (simp)
apply (simp add: etype_rel_def closure)
apply (force intro: UNREST_BFUN_subset)+
done
end

subsection {* Boolean Expressions *}

context PRED_BOOL
begin

definition TrueE :: "('VALUE, 'TYPE) EXPRESSION" where
"TrueE = LitE (MkBool True)"

definition FalseE :: "('VALUE, 'TYPE) EXPRESSION" where
"FalseE = LitE (MkBool False)"

definition PredE ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) EXPRESSION" where
"p \<in> WF_PREDICATE \<longrightarrow>
 PredE p = wf_expr (\<lambda> b . MkBool (b \<in> p))"

definition VarP ::
  "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) PREDICATE" where
"VarP v = LiftP (DestBool \<circ> (VarE v))"

subsubsection {* Closure Theorems *}

theorem TrueE_closed [closure] :
"TrueE \<in> WF_EXPRESSION"
  by (auto intro: closure typing simp add:TrueE_def)

theorem FalseE_closed [closure] :
"FalseE \<in> WF_EXPRESSION"
  by (auto intro: closure typing simp add: FalseE_def)

theorem PredE_closed [closure] :
"p \<in> WF_PREDICATE \<Longrightarrow> PredE p \<in> WF_EXPRESSION"
apply (simp add: PredE_def)
apply (rule closure)
apply (auto intro: typing)
done

theorem VarP_closed [closure] :
"VarP x \<in> WF_PREDICATE"
  by (simp add: VarP_def, rule closure)

subsubsection {* Typing Theorems *}

theorem TrueE_type [typing] :
"TrueE :e BoolType"
apply (simp add: TrueE_def)
apply (rule typing)+
done

theorem FalseE_type [typing] :
"FalseE :e BoolType"
apply (simp add: FalseE_def)
apply (rule typing)+
done

theorem PredE_type [typing] :
"p \<in> WF_PREDICATE \<longrightarrow>
 PredE p :e BoolType"
  by (auto intro: typing simp add: PredE_def)

subsubsection {* @{const UNREST_BFUN} Theorems *}

theorem UNREST_BFUN_TrueE [unrest] :
"UNREST_BFUN vs TrueE"
  by (simp add: TrueE_def unrest)

theorem UNREST_BFUN_FalseE [unrest] :
"UNREST_BFUN vs FalseE"
  by (simp add: FalseE_def unrest)

theorem UNREST_BFUN_PredE [unrest] :
"\<lbrakk>p \<in> WF_PREDICATE; UNREST vs p\<rbrakk> \<Longrightarrow>
 UNREST_BFUN vs (PredE p)"
apply (simp add: PredE_def)
apply (rule unrest)
apply (simp add: UNREST_BFUN_def UNREST_def WF_PREDICATE_def)
apply (safe)
apply (rule_tac f = "MkBool" and g = "MkBool" in cong, simp)
apply (auto)
apply (metis override_on_cancel1 override_on_cancel2)
done

(* The following proof does not go through at the moment. *)

theorem UNREST_VarP [unrest] :
"UNREST (vs - {x}) (VarP x)"
apply (simp add: VarP_def)
apply (rule_tac ?vs1.0 = "{x}" in UNREST_LiftP_alt)
apply (auto)
apply (simp add: WF_BINDING_PRED_def VarE_def wf_expr_def binding_equiv_def)
sorry
end
end