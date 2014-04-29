(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_expr_tac.thy                                                     *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Proof Tactic for Expressions *}

theory utp_expr_tac
imports 
  "../core/utp_expr" 
  utp_pred_tac
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
   'VALUE WF_BINDING \<Rightarrow> 'VALUE" ("\<lbrakk>_\<rbrakk>\<^sub>e_" [0, 1000] 51) where
"EvalE e b = \<langle>e\<rangle>\<^sub>e b"

theorem EvalE_type [typing, simp]:
"e :\<^sub>e t \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>eb : t"
  by (simp add:EvalE_def etype_rel_def)

lemma EvalE_defined [defined]:
  "\<D> v \<Longrightarrow> \<D> (\<lbrakk>v\<rbrakk>\<^sub>eb)"
  by (simp add:EvalE_def Defined_WF_EXPRESSION_def)

theorem EvalE_compat [typing, simp]:
"e \<rhd>\<^sub>e t \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>eb \<rhd> t"
  by (simp add:EvalE_def evar_compat_def)

subsection {* Transfer Theorems *}

theorem EvalE_simp [evale] :
"e1 = e2 \<longleftrightarrow> (\<forall> b . \<lbrakk>e1\<rbrakk>\<^sub>eb = \<lbrakk>e2\<rbrakk>\<^sub>eb)"
  by (auto simp add: EvalE_def)

theorem EvalE_intro :
"\<lbrakk>(\<forall> b . \<lbrakk>e1\<rbrakk>\<^sub>eb = \<lbrakk>e2\<rbrakk>\<^sub>eb)\<rbrakk> \<Longrightarrow> e1 = e2"
  by (simp add: EvalE_simp)

subsection {* Distribution Theorems *}

theorem EvalP_EqualP [eval]:
"\<lbrakk>e1 ==\<^sub>p e2\<rbrakk>b = (\<lbrakk>e1\<rbrakk>\<^sub>eb = \<lbrakk>e2\<rbrakk>\<^sub>eb)"
  by (simp add:EqualP_def EvalP_def EvalE_def)

theorem EvalE_VarE [eval,evale] :
"\<lbrakk>VarE x\<rbrakk>\<^sub>eb = \<langle>b\<rangle>\<^sub>b x"
  by (simp add:VarE.rep_eq EvalE_def)

theorem EvalP_ExprP [eval] :
"\<lbrakk>ExprP e\<rbrakk>b = DestBool (\<lbrakk>e\<rbrakk>\<^sub>eb)"
  by (simp add:ExprP_def eval EvalE_def)

theorem EvalP_VarP [eval] :
"\<lbrakk>VarP x\<rbrakk>b = DestBool (\<langle>b\<rangle>\<^sub>b x)"
  by (simp add:eval evale)

theorem EvalE_LitE [eval,evale] :
"v : t \<Longrightarrow> \<lbrakk>LitE v\<rbrakk>\<^sub>eb = v"
  by (auto simp add: LitE_rep_eq EvalE_def)

theorem EvalE_LitE_alt [eval,evale] :
"v \<rhd> x \<Longrightarrow> \<lbrakk>LitE v\<rbrakk>\<^sub>eb = v"
  apply (rule EvalE_LitE)
  apply (auto intro:typing)
done

theorem EvalE_Op1E [eval,evale] :
"\<lbrakk> x :!\<^sub>e a; f \<in> FUNC1 a b \<rbrakk> \<Longrightarrow> \<lbrakk>Op1E f x\<rbrakk>\<^sub>eb1 = f (\<lbrakk>x\<rbrakk>\<^sub>eb1)"
  by (auto simp add: Op1E_rep_eq EvalE_def)

theorem EvalE_Op2E [eval,evale] :
"\<lbrakk> x :!\<^sub>e a; y :!\<^sub>e b; f \<in> FUNC2 a b c \<rbrakk> \<Longrightarrow> \<lbrakk>Op2E f x y\<rbrakk>\<^sub>eb1 = f (\<lbrakk>x\<rbrakk>\<^sub>eb1) (\<lbrakk>y\<rbrakk>\<^sub>eb1)"
  by (auto simp add: Op2E_rep_eq EvalE_def)

theorem EvalE_DefaultE [eval,evale] :
"\<lbrakk>DefaultE t\<rbrakk>\<^sub>eb = default t"
  by (auto simp add: DefaultE_def EvalE_def LitE_rep_eq)

theorem EvalE_CoerceE_LitE [eval,evale] :
"v : t \<Longrightarrow> \<lbrakk>CoerceE (LitE v) t\<rbrakk>\<^sub>eb = v"
  by (auto simp add:CoerceE_def typing evale)

theorem EvalE_CoerceE_ntype [eval,evale] :
"\<not> e :\<^sub>e t \<Longrightarrow> \<lbrakk>CoerceE e t\<rbrakk>\<^sub>eb = default t"
  by (simp add:CoerceE_def evale)

theorem EvalE_AppE [eval,evale] :
"\<lbrakk> f :\<^sub>e FuncType s t; v :\<^sub>e s; \<D> f \<rbrakk> \<Longrightarrow> \<lbrakk>AppE f v\<rbrakk>\<^sub>eb = DestFunc (\<lbrakk>f\<rbrakk>\<^sub>eb) (\<lbrakk>v\<rbrakk>\<^sub>eb)"
  by (simp add:EvalE_def AppE_rep_eq)

theorem EvalE_SubstE [eval,evale] :
"\<lbrakk>f[v/\<^sub>ex]\<rbrakk>\<^sub>eb = \<lbrakk>f\<rbrakk>\<^sub>e(b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>eb))"
  by (simp add:SubstE.rep_eq EvalE_def)

theorem EvalE_TrueE [eval,evale] :
"\<lbrakk>TrueE\<rbrakk>\<^sub>eb = TrueV"
  by (simp add:TrueE_def EvalE_LitE[OF MkBool_type])

theorem EvalE_FalseE [eval,evale] :
"\<lbrakk>FalseE\<rbrakk>\<^sub>eb = FalseV"
  by (simp add:FalseE_def EvalE_LitE[OF MkBool_type])

theorem EvalE_UNREST_override [eval,evale] :
"vs \<sharp> e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e(b \<oplus>\<^sub>b b' on vs) = \<lbrakk>e\<rbrakk>\<^sub>eb"
  by (simp add:EvalE_def UNREST_EXPR_def)

theorem EvalE_UNREST_assign [eval,evale] :
"\<lbrakk> x \<in> vs; vs \<sharp> e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>e\<rbrakk>\<^sub>e(b(x :=\<^sub>b v)) = \<lbrakk>e\<rbrakk>\<^sub>eb"
  apply (auto simp add:EvalE_def UNREST_EXPR_def)
  apply (metis binding_upd_override)
done

theorem EvalP_UNREST_binding_equiv [eval,evale] :
"\<lbrakk> - vs \<sharp> e; b1 \<cong> b2 on vs \<rbrakk> 
 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>eb1 = \<lbrakk>e\<rbrakk>\<^sub>eb2"
  by (metis (mono_tags) Compl_eq_Diff_UNIV EvalE_def UNREST_EXPR_member VAR_def binding_override_equiv binding_override_minus)
  
theorem EvalE_RenameE [eval,evale] :
"\<lbrakk>ss\<bullet>e\<rbrakk>\<^sub>eb = \<lbrakk>e\<rbrakk>\<^sub>e((inv\<^sub>s ss)\<bullet>b)"
  by (simp add: EvalE_def PermE.rep_eq)

theorem EvalE_PrimeE [eval,evale] :
"\<lbrakk>e\<acute>\<rbrakk>\<^sub>eb = \<lbrakk>e\<rbrakk>\<^sub>e((inv\<^sub>s (dash on UNDASHED))\<bullet>b)"
  by (simp add:PrimeE_def evale)

theorem EvalP_SubstP [eval,eval] :
  "\<lbrakk>p[v/\<^sub>px]\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>eb))"
  by (simp add:SubstP.rep_eq EvalP_def EvalE_def)

lemma EvalE_ecoerce [evale]:
  "\<lbrakk>ecoerce e x\<rbrakk>\<^sub>eb = vcoerce (\<lbrakk>e\<rbrakk>\<^sub>eb) x"
by (metis EvalE_def ecoerce_rep_eq)

lemma EvalE_UNREST_binding_upd [evale]:
  "{x} \<sharp> e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e(b(x :=\<^sub>b v)) = \<lbrakk>e\<rbrakk>\<^sub>eb"
  apply (auto simp add:EvalE_def UNREST_EXPR_def)
  apply (metis binding_upd_upd)
done

subsection {* Proof Tactics *}

ML {*
  fun utp_expr_simpset ctxt =
    ctxt
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
"taut (((e1 ==\<^sub>p e2) \<and>\<^sub>p (e2 ==\<^sub>p e3)) \<Rightarrow>\<^sub>p (e1 ==\<^sub>p e3))"
  by utp_pred_tac

theorem EqualP_sym:
"(e1 ==\<^sub>p e2) = (e2 ==\<^sub>p e1)"
  by utp_pred_auto_tac

(* These need adapting for strictness *)
theorem VarE_subst: "\<lbrakk> v :\<^sub>e vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> $\<^sub>ex[v/\<^sub>ex] = v"
  by utp_expr_tac

theorem EvalP_UNREST_assign_1 [eval] :
"{x} \<sharp> p \<Longrightarrow> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)) = \<lbrakk>p\<rbrakk>b"
  apply (rule EvalP_UNREST_assign)
  apply (auto)
done

lemma ExistsP_SubstP:
  "\<lbrakk> vtype x = vtype y; aux x = aux y; UNREST {x} p \<rbrakk> \<Longrightarrow> 
     (\<exists>\<^sub>p {y}. p) = (\<exists>\<^sub>p {x}. p[$\<^sub>ex/\<^sub>py])"
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
  apply (drule_tac v="\<lbrakk>e\<rbrakk>\<^sub>eb" and b="b" in EvalE_UNREST_assign[of x "{x}" e, simplified])
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