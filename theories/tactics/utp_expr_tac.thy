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

subsection {* Interpretation Function *}

definition EvalE ::
  "'VALUE WF_EXPRESSION \<Rightarrow>
   'VALUE WF_BINDING \<Rightarrow> 'VALUE" ("\<lbrakk>_\<rbrakk>\<epsilon>_" [0, 1000] 51) where
"EvalE e b = \<langle>e\<rangle>\<^sub>e b"

theorem EvalE_type [typing, simp]:
"e :\<^sub>e t \<Longrightarrow> \<lbrakk>e\<rbrakk>\<epsilon>b : t"
  by (simp add:EvalE_def etype_rel_def)

lemma EvalE_defined [defined]:
  "\<D> v \<Longrightarrow> \<D> (\<lbrakk>v\<rbrakk>\<epsilon>b)"
  by (simp add:EvalE_def Defined_WF_EXPRESSION_def)

theorem EvalE_compat [typing, simp]:
"e \<rhd>\<^sub>e t \<Longrightarrow> \<lbrakk>e\<rbrakk>\<epsilon>b \<rhd> t"
  by (simp add:EvalE_def evar_compat_def)

subsection {* Transfer Theorems *}

theorem EvalE_simp [evale] :
"e1 = e2 \<longleftrightarrow> (\<forall> b . \<lbrakk>e1\<rbrakk>\<epsilon>b = \<lbrakk>e2\<rbrakk>\<epsilon>b)"
  by (auto simp add: EvalE_def)

theorem EvalE_intro :
"\<lbrakk>(\<forall> b . \<lbrakk>e1\<rbrakk>\<epsilon>b = \<lbrakk>e2\<rbrakk>\<epsilon>b)\<rbrakk> \<Longrightarrow> e1 = e2"
  by (simp add: EvalE_simp)

subsection {* Distribution Theorems *}

theorem EvalP_EqualP [eval]:
"\<lbrakk>e1 ==p e2\<rbrakk>b = (\<lbrakk>e1\<rbrakk>\<epsilon>b = \<lbrakk>e2\<rbrakk>\<epsilon>b)"
  by (simp add:EqualP_def EvalP_def EvalE_def)

theorem EvalE_VarE [evale] :
"\<lbrakk>VarE x\<rbrakk>\<epsilon>b = \<langle>b\<rangle>\<^sub>b x"
  by (simp add:VarE.rep_eq EvalE_def)

theorem EvalP_ExprP [eval] :
"\<lbrakk>ExprP e\<rbrakk>b = DestBool (\<lbrakk>e\<rbrakk>\<epsilon>b)"
  by (simp add:ExprP_def eval EvalE_def)

theorem EvalP_VarP [eval] :
"\<lbrakk>VarP x\<rbrakk>b = DestBool (\<langle>b\<rangle>\<^sub>b x)"
  by (simp add:eval evale)

theorem EvalE_LitE [evale] :
"v : t \<Longrightarrow> \<lbrakk>LitE v\<rbrakk>\<epsilon>b = v"
  by (auto simp add: LitE_rep_eq EvalE_def)

theorem EvalE_Op1E [evale] :
"\<lbrakk> x :\<^sub>e a; f \<in> FUNC1 a b \<rbrakk> \<Longrightarrow> \<lbrakk>Op1E f x\<rbrakk>\<epsilon>b1 = f (\<lbrakk>x\<rbrakk>\<epsilon>b1)"
  by (auto simp add: Op1E_rep_eq EvalE_def)

theorem EvalE_Op2E [evale] :
"\<lbrakk> x :\<^sub>e a; y :\<^sub>e b; f \<in> FUNC2 a b c \<rbrakk> \<Longrightarrow> \<lbrakk>Op2E f x y\<rbrakk>\<epsilon>b1 = f (\<lbrakk>x\<rbrakk>\<epsilon>b1) (\<lbrakk>y\<rbrakk>\<epsilon>b1)"
  by (auto simp add: Op2E_rep_eq EvalE_def)

theorem EvalE_DefaultE [evale] :
"\<lbrakk>DefaultE t\<rbrakk>\<epsilon>b = default t"
  by (auto simp add: DefaultE_def EvalE_def LitE_rep_eq)

theorem EvalE_CoerceE_LitE [evale] :
"v : t \<Longrightarrow> \<lbrakk>CoerceE (LitE v) t\<rbrakk>\<epsilon>b = v"
  by (auto simp add:CoerceE_def typing evale)

theorem EvalE_CoerceE_ntype [evale] :
"\<not> e :\<^sub>e t \<Longrightarrow> \<lbrakk>CoerceE e t\<rbrakk>\<epsilon>b = default t"
  by (simp add:CoerceE_def evale)

theorem EvalE_AppE [evale] :
"\<lbrakk> f :\<^sub>e FuncType s t; v :\<^sub>e s; \<D> f \<rbrakk> \<Longrightarrow> \<lbrakk>AppE f v\<rbrakk>\<epsilon>b = DestFunc (\<lbrakk>f\<rbrakk>\<epsilon>b) (\<lbrakk>v\<rbrakk>\<epsilon>b)"
  by (simp add:EvalE_def AppE_rep_eq)

theorem EvalE_SubstE [evale] :
"\<lbrakk>SubstE f v x\<rbrakk>\<epsilon>b = \<lbrakk>f\<rbrakk>\<epsilon>(b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b))"
  by (simp add:SubstE.rep_eq EvalE_def)

theorem EvalE_TrueE [evale] :
"\<lbrakk>TrueE\<rbrakk>\<epsilon>b = TrueV"
  by (simp add:TrueE_def EvalE_LitE[OF MkBool_type])

theorem EvalE_FalseE [evale] :
"\<lbrakk>FalseE\<rbrakk>\<epsilon>b = FalseV"
  by (simp add:FalseE_def EvalE_LitE[OF MkBool_type])

theorem EvalE_UNREST_override [evale] :
"\<lbrakk> UNREST_EXPR vs e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>e\<rbrakk>\<epsilon>(b \<oplus>\<^sub>b b' on vs) = \<lbrakk>e\<rbrakk>\<epsilon>b"
  by (simp add:EvalE_def UNREST_EXPR_def)

theorem EvalE_UNREST_assign [evale] :
"\<lbrakk> x \<in> vs; UNREST_EXPR vs e; v \<rhd> x \<rbrakk> \<Longrightarrow> 
  \<lbrakk>e\<rbrakk>\<epsilon>(b(x :=\<^sub>b v)) = \<lbrakk>e\<rbrakk>\<epsilon>b"
  apply (auto simp add:EvalE_def UNREST_EXPR_def)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="b(x :=\<^sub>b v)" in spec)
  apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e (b \<oplus>\<^sub>b b(x :=\<^sub>b v) on vs) = \<langle>e\<rangle>\<^sub>e (b \<oplus>\<^sub>b b(x :=\<^sub>b v) on insert x vs)")
  apply (simp_all)
  apply (metis binding_override_simps(2) binding_override_simps(8))
done

theorem EvalP_UNREST_binding_equiv [evale] :
"\<lbrakk> UNREST_EXPR (VAR - vs) e; b1 \<cong> b2 on vs \<rbrakk> 
 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<epsilon>b1 = \<lbrakk>e\<rbrakk>\<epsilon>b2"
  by (metis (mono_tags) Compl_eq_Diff_UNIV EvalE_def UNREST_EXPR_member VAR_def binding_override_equiv binding_override_minus)
  
theorem EvalE_RenameE [evale] :
"\<lbrakk>e[ss]\<epsilon>\<rbrakk>\<epsilon>b = \<lbrakk>e\<rbrakk>\<epsilon>(RenameB (inv\<^sub>s ss) b)"
  by (simp add: EvalE_def RenameE.rep_eq)

theorem EvalP_SubstP [eval] :
  "\<lbrakk>p[v|x]\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b))"
  by (simp add:SubstP_def EvalP_def EvalE_def)

(*


proof -

  from assms(1) have "\<And> x'. is_SubstP_var p v x x' \<Longrightarrow> 
                       \<lbrakk>SubstP_body p v x x'\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b))"
    apply (subgoal_tac "b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b, x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x) \<oplus>\<^sub>b b on {x'} = b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b)")
    apply (drule_tac b="b" in EvalE_compat)
    apply (simp add:SubstP_body_def)
(*    apply (simp add:is_SubstP_var_def, clarify) *)
    apply (utp_pred_tac)
    apply (auto)
    apply (simp add:is_SubstP_var_def, clarify)
    apply (simp add:eval evale closure)
(*    apply (simp add:is_SubstP_var_def UNREST_def, clarify) *)
    apply (subgoal_tac "\<lbrakk>v\<rbrakk>\<epsilon> (b(x' :=\<^sub>b \<langle>b'\<rangle>\<^sub>b x')) = \<langle>v\<rangle>\<^sub>e b")
    apply (simp add:UNREST_def binding_upd_twist)
    apply (drule_tac x="b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b, x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x)" in bspec)
    apply (simp add:EvalP_def EvalE_def)
    apply (simp add:binding_upd_twist)
  sorry
(*
    apply (simp add:EvalP_def EvalE_def)
    apply (drule_tac x="b" in spec)
    apply (simp add:binding_upd_twist)
    apply (simp add:EvalE_def UNREST_EXPR_def)
    apply (metis)
    apply (rule_tac x="b(x' :=\<^sub>b \<lbrakk>v\<rbrakk>\<epsilon>b)" in exI)
    apply (simp add:is_SubstP_var_def eval evale closure binding_upd_twist)
    apply (rule conjI)
    apply (simp_all add:EvalP_def EvalE_def UNREST_def var_compat_def)
    apply (clarify)
    apply (drule_tac x="b(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b)" in bspec)
    apply (simp)
    apply (metis (lifting) assms(1) binding_upd_apply binding_upd_twist binding_value_alt evar_compat_def)
    apply (metis EvalE_UNREST_assign EvalE_def insertI1 var_compat_intros(1) var_compat_intros(2))
    apply (simp add:is_SubstP_var_def eval evale closure binding_upd_twist)
    apply (metis (lifting) binding_compat binding_upd_simps(2) binding_upd_twist evar_compat_def)
  done
*)

  with assms show ?thesis
    apply (simp add:SubstP_def)
    apply (erule exE)
    apply (rule someI2)
    apply (force)
    apply (simp del:fun_upd_apply)
  done

qed
*)

lemma EvalE_UNREST_binding_upd [evale]:
  "\<lbrakk> v \<rhd> x; UNREST_EXPR {x} e \<rbrakk> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<epsilon>(b(x :=\<^sub>b v)) = \<lbrakk>e\<rbrakk>\<epsilon>b"
  by (auto simp add:EvalE_def UNREST_EXPR_def, smt binding_upd_apply)

subsection {* Proof Tactics *}

ML {*
  fun utp_expr_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evale.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (typing.get ctxt);
*}

ML {*
  fun utp_expr_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_expr_simpset ctxt) i))
*}

method_setup utp_expr_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_expr_tac thms ctxt))
*} "proof tactic for expressions"

subsection {* Proof Experiments *}

theorem EqualP_trans:
"taut (((e1 ==p e2) \<and>p (e2 ==p e3)) \<Rightarrow>p (e1 ==p e3))"
  by utp_pred_tac

theorem EqualP_sym:
"(e1 ==p e2) = (e2 ==p e1)"
  by utp_pred_auto_tac

(* These need adapting for strictness *)
theorem VarE_subst: "\<lbrakk> v :\<^sub>e vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> VarE x[v|x] = v"
  by utp_expr_tac

theorem EvalP_UNREST_assign_1 [eval] :
"\<lbrakk> UNREST {x} p; v \<rhd> x \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)) = \<lbrakk>p\<rbrakk>b"
  apply (rule EvalP_UNREST_assign)
  apply (auto)
done

lemma ExistsP_SubstP:
  "\<lbrakk> vtype x = vtype y; aux x = aux y; UNREST {x} p \<rbrakk> \<Longrightarrow> (\<exists>p {y}. p) = (\<exists>p {x}. p[VarE x|y])"
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

(*
  apply (auto)
  apply (drule_tac v="\<lbrakk>e\<rbrakk>\<epsilon>b" and b="b" in EvalE_UNREST_assign[of x "{x}" e, simplified])
  apply (simp_all)
done
*)

(*
definition 
  PROP_VARS :: "('VALUE \<Rightarrow> bool) \<Rightarrow> 'VALUE PREDICATE \<Rightarrow> 'TYPE VAR set" where
  "PROP_VARS P p = {x. \<forall>b\<in>p. P (b x)}"

lemma PROP_VARS_Defined: "\<lbrakk> x \<in> PROP_VARS \<D> p; b \<in> p \<rbrakk> \<Longrightarrow> \<D> (b x)"
  by (simp add:PROP_VARS_def)


theorem taut_casesI:
"\<lbrakk> \<And> v. v : vtype x \<Longrightarrow> taut (p[LitE (vtype x) v|x]) \<rbrakk> \<Longrightarrow>
 taut p"
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (auto)
  apply (simp add:EvalP_def)
  apply (utp_expr_tac)
  apply (subgoal_tac "xa x : vtype x")
  apply (auto)
  apply (simp add:SubstP_def typing)
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (metis override_on_cancel1 override_on_singleton)
done

theorem "\<lbrakk> p \<in> WF_PREDICATE; q \<in> WF_PREDICATE; x \<in> PROP_VARS \<D> p; x \<in> PROP_VARS \<D> q; \<not> \<D> v; v : t \<rbrakk> \<Longrightarrow>
         p[LitE t v|x] = q[LitE t v|x]"
  apply (utp_pred_tac)

theorem Bool_cases:
"\<lbrakk> p \<in> WF_PREDICATE; vtype x = BoolType; x \<in> DEF_VARS p;
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