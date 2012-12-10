(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_expr_tac.thy                                                     *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Proof Tactic for Expressions *}

theory utp_expr_tac
imports "../core/utp_expr" utp_pred_tac
begin

text {* Theorem Attribute *}

ML {*
  structure evale =
    Named_Thms (val name = @{binding evale} val description = "evale theorems")
*}

setup evale.setup

context PRED
begin

subsection {* Interpretation Function *}

definition EvalE ::
  "('VALUE, 'TYPE) EXPRESSION \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE" ("\<lbrakk>_\<rbrakk>\<epsilon>_" [0, 1000] 51) where
"EvalE e b = expr_bfun e b"

theorem EvalE_type [typing]:
"\<lbrakk>e \<in> WF_EXPRESSION; b \<in> WF_BINDING; e :e: t\<rbrakk> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<epsilon>b : t"
  by (simp add:EvalE_def etype_rel_def)

subsection {* Transfer Theorems *}

theorem EvalE_simp [evale] :
"\<lbrakk>e1 \<in> WF_EXPRESSION;
 e2 \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow>
 e1 = e2 \<longleftrightarrow> (\<forall> b \<in> WF_BINDING . \<lbrakk>e1\<rbrakk>\<epsilon>b = \<lbrakk>e2\<rbrakk>\<epsilon>b) \<and> \<tau>e e1 = \<tau>e e2"
apply (auto simp add: EvalE_def)
apply (simp add: WF_EXPRESSION_OVER_def WF_EXPRESSION_def UNREST_EXPR_def)
apply (case_tac e1, case_tac e2)
apply (auto)
apply (rule ext)
apply (case_tac "x \<in> WF_BINDING")
apply (simp)
apply (metis expr_simps(1) expr_simps(2))
done

theorem EvalE_intro :
"\<lbrakk>e1 \<in> WF_EXPRESSION;
 e2 \<in> WF_EXPRESSION;
 (\<forall> b \<in> WF_BINDING . \<lbrakk>e1\<rbrakk>\<epsilon>b = \<lbrakk>e2\<rbrakk>\<epsilon>b);
 \<tau>e e1 = \<tau>e e2\<rbrakk> \<Longrightarrow> e1 = e2"
  by (simp add: EvalE_simp)

subsection {* Distribution Theorems *}

theorem EvalP_EqualP [eval]:
"\<lbrakk>e1 \<in> WF_EXPRESSION;
 e2 \<in> WF_EXPRESSION;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>e1 ==p e2\<rbrakk>b = (\<lbrakk>e1\<rbrakk>\<epsilon>b = \<lbrakk>e2\<rbrakk>\<epsilon>b)"
  by (simp add:EqualP_def EvalP_def EvalE_def)

theorem EvalE_VarE [evale] :
"b \<in> WF_BINDING \<Longrightarrow>
 \<lbrakk>VarE x\<rbrakk>\<epsilon>b = b x"
  by (simp add:VarE_def EvalE_def)

theorem EvalE_LitE [evale] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>LitE t v\<rbrakk>\<epsilon>b = v"
  by (simp add: LitE_def EvalE_def)

theorem EvalE_SubstE [evale] :
"\<lbrakk>f \<in> WF_EXPRESSION;
 v \<in> WF_EXPRESSION;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>SubstE f v x\<rbrakk>\<epsilon>b = \<lbrakk>f\<rbrakk>\<epsilon>(b(x := \<lbrakk>v\<rbrakk>\<epsilon>b))"
  by (simp add:SubstE_def EvalE_def)

subsection {* Proof Tactics *}

ML {*
  fun utp_expr_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evale.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt);
*}

ML {*
  fun utp_expr_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_expr_simpset ctxt) i))
*}

end

method_setup utp_expr_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_expr_tac thms ctxt))
*} "proof tactic for expressions"

subsection {* Proof Experiments *}

context PRED
begin

theorem EqualP_trans:
"\<lbrakk>e1 \<in> WF_EXPRESSION; e2 \<in> WF_EXPRESSION; e3 \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow>
 taut (((e1 ==p e2) \<and>p (e2 ==p e3)) \<Rightarrow>p (e1 ==p e3))"
  by utp_pred_tac

theorem EqualP_sym:
"\<lbrakk>e1 \<in> WF_EXPRESSION; e2 \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow>
 (e1 ==p e2) = (e2 ==p e1)"
  by utp_pred_auto_tac

theorem VarE_subst: "\<lbrakk> v \<in> WF_EXPRESSION; type x = \<tau>e v \<rbrakk> \<Longrightarrow> VarE x[v|x] = v"
  by utp_expr_tac

end

context PRED_BOOL
begin

definition 
  PROP_VARS :: "('VALUE \<Rightarrow> bool) \<Rightarrow> ('VALUE, 'TYPE) PREDICATE \<Rightarrow> 'TYPE VAR set" where
  "PROP_VARS P p = {x. \<forall>b\<in>p. P (b x)}"

lemma PROP_VARS_Defined: "\<lbrakk> x \<in> PROP_VARS \<D> p; b \<in> p \<rbrakk> \<Longrightarrow> \<D> (b x)"
  by (simp add:PROP_VARS_def)

(*
theorem Taut_subst_cases:
"\<lbrakk> p \<in> WF_PREDICATE;
   \<And> v. v : type x \<Longrightarrow> taut (p[LitE (type x) v|x]) \<rbrakk> \<Longrightarrow>
 taut p"
  apply (utp_pred_auto_tac)
  apply (subgoal_tac "xa x : type x")
  apply (auto)
  apply (simp add:SubstPE_def typing)
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (metis override_on_cancel1 override_on_singleton)
done

theorem "\<lbrakk> p \<in> WF_PREDICATE; q \<in> WF_PREDICATE; x \<in> PROP_VARS \<D> p; x \<in> PROP_VARS \<D> q; \<not> \<D> v; v : t \<rbrakk> \<Longrightarrow>
         p[LitE t v|x] = q[LitE t v|x]"
  apply (utp_pred_tac)

theorem Bool_cases:
"\<lbrakk> p \<in> WF_PREDICATE; type x = BoolType; x \<in> DEF_VARS p;
   taut (p[TrueE|x]);
   taut (p[FalseE|x]);
   taut (p[ \<rbrakk> \<Longrightarrow>
 taut p"
  apply (rule_tac x="x" in Taut_subst_cases)
  apply (simp_all)
  apply (rule allI)
  apply (rule impI)
  oops
*)

end
end