(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_expr.thy                                                         *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Basic Expressions *}

theory utp_expr
imports 
  utp_pred 
  utp_unrest 
  utp_sorts 
  utp_rename
begin

type_synonym 'a EXPRESSION = "('a binding_fun)"

text {* Well-formed expression is a binding function which must yield the
        same type for any binding it is applied to. *}
definition WF_EXPRESSION :: "'a EXPRESSION set" where
"WF_EXPRESSION = {f. \<exists> t. \<forall>b. f b : t}"

typedef 'a uexpr = "WF_EXPRESSION :: 'a EXPRESSION set"
  apply (simp add:WF_EXPRESSION_def)
  apply (rule_tac x="(\<lambda> x. default someType)" in exI)
  apply (rule_tac x="someType" in exI)
  apply (force)
done

declare Rep_uexpr [simp]
declare Rep_uexpr_inverse [simp]
declare Abs_uexpr_inverse [simp]

lemma Rep_uexpr_intro [intro]:
  "Rep_uexpr x = Rep_uexpr y \<Longrightarrow> x = y"
  by (simp add:Rep_uexpr_inject)

lemma Rep_uexpr_elim [elim]:
  "\<lbrakk> x = y; Rep_uexpr x = Rep_uexpr y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_uexpr

notation Rep_uexpr ("\<langle>_\<rangle>\<^sub>e")

lemma Rep_uexpr_typed [typing]:
  "\<exists> t. \<forall> b. \<langle>e\<rangle>\<^sub>e b : t"
  apply (insert Rep_uexpr[of e])
  apply (auto simp add:WF_EXPRESSION_def)
done

definition etype_rel :: "'a uexpr \<Rightarrow> 'a utype \<Rightarrow> bool" (infix ":\<^sub>e" 50) where
"etype_rel e t \<equiv> \<forall>b. \<langle>e\<rangle>\<^sub>e b : t"

definition expr_type :: "'a uexpr \<Rightarrow> 'a utype" where
"expr_type e \<equiv> THE t. e :\<^sub>e t"

definition evar_compat :: "'a uexpr \<Rightarrow> 'a uvar \<Rightarrow> bool" (infix "\<rhd>\<^sub>e" 50) where
"evar_compat e x \<equiv> \<forall>b. \<langle>e\<rangle>\<^sub>e b \<rhd> x"

instantiation uexpr :: (VALUE) DEFINED
begin

definition Defined_uexpr :: "'a uexpr \<Rightarrow> bool" where
"Defined_uexpr e \<equiv> \<forall> b. \<D> (\<langle>e\<rangle>\<^sub>e b)"

instance ..

end

definition edtype_rel :: 
  "'a uexpr \<Rightarrow> 'a utype \<Rightarrow> bool" (infix ":!\<^sub>e" 50) where
"edtype_rel e t \<equiv> \<forall>b. \<langle>e\<rangle>\<^sub>e b :! t"

lemma edtype_intro [intro]:
  "\<lbrakk> x :\<^sub>e a; \<D> x \<rbrakk> \<Longrightarrow> x :!\<^sub>e a" 
  by (auto simp add:edtype_rel_def etype_rel_def Defined_uexpr_def)

lemma edtype_etype [typing]:
  "x :!\<^sub>e a \<Longrightarrow> x :\<^sub>e a"
  by (auto simp add:edtype_rel_def etype_rel_def)

lemma edtype_defined [defined]:
  "x :!\<^sub>e a \<Longrightarrow> \<D> x"
  by (auto simp add:edtype_rel_def Defined_uexpr_def defined)

lemma evar_compat_intros [simp,intro]:
  "\<lbrakk> v :\<^sub>e vtype x; \<D> v \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>e x"
  "\<lbrakk> v :\<^sub>e vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>e x"
  by (auto simp add:evar_compat_def etype_rel_def Defined_uexpr_def)

lemma evar_compat_cases [elim]:
  "\<lbrakk> v \<rhd>\<^sub>e x; \<lbrakk> v :\<^sub>e vtype x; \<D> v \<rbrakk> \<Longrightarrow> P
           ; \<lbrakk> v :\<^sub>e vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:evar_compat_def etype_rel_def Defined_uexpr_def)

lemma evar_compat_dash [typing]:
  "v \<rhd>\<^sub>e x \<Longrightarrow> v \<rhd>\<^sub>e x\<acute>"
  by (simp add:evar_compat_def typing)

lemma evar_compat_undash [typing]:
  "v \<rhd>\<^sub>e x \<Longrightarrow> v \<rhd>\<^sub>e undash x"
  by (auto intro:typing simp add:evar_compat_def)

lemma evar_compat [typing]:
  "e \<rhd>\<^sub>e x \<Longrightarrow> \<langle>e\<rangle>\<^sub>e b \<rhd> x"
  by (simp add:evar_compat_def)

text {* Unrestriction on expressions is equivalent to that of predicates. *}

definition UNREST_EXPR :: "('a uvar) set \<Rightarrow> 'a uexpr \<Rightarrow> bool" where
"UNREST_EXPR vs e \<equiv> (\<forall> b1 b2. \<langle>e\<rangle>\<^sub>e(b1 \<oplus>\<^sub>b b2 on vs) = \<langle>e\<rangle>\<^sub>e b1)" 

adhoc_overloading
  unrest UNREST_EXPR

definition WF_EXPR_REL :: "'m uexpr set" where
"WF_EXPR_REL = {e. - D\<^sub>0 \<sharp> e}"

adhoc_overloading
  REL WF_EXPR_REL

definition WF_EXPR_COND :: "'m uexpr set" where
"WF_EXPR_COND = {e. - D\<^sub>0 \<sharp> e}"

adhoc_overloading
  COND WF_EXPR_COND

definition WF_EXPRESSION_OVER ::
  "('a uvar) set \<Rightarrow>
   'a uexpr set" where
"WF_EXPRESSION_OVER vs = {e . - vs \<sharp> e}"

subsection {* Operators *}

subsubsection {* Equality *}

definition EqualP :: 
"'a uexpr \<Rightarrow> 
 'a uexpr \<Rightarrow> 
 'a upred" where
"EqualP e f = mkPRED {b. \<langle>e\<rangle>\<^sub>e b = \<langle>f\<rangle>\<^sub>e b}"

notation EqualP (infixr "==\<^sub>p" 200)

definition LitE :: "'a \<Rightarrow> 'a uexpr" where 
"LitE v = Abs_uexpr (if (\<exists> t. v : t) then (\<lambda> b. v) else (\<lambda> b. default someType))"

lemma LitE_rep_eq: 
  "\<langle>LitE v\<rangle>\<^sub>e = (if (\<exists> t. v : t) then (\<lambda> b. v) else (\<lambda> b. default someType))"
  apply (subgoal_tac "(if (\<exists> t. v : t) then (\<lambda> b. v) else (\<lambda> b. default someType)) \<in> WF_EXPRESSION")
  apply (auto simp add:LitE_def WF_EXPRESSION_def)
done

definition Op1E :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr" where
"Op1E f v = Abs_uexpr (\<lambda> b. f (\<langle>v\<rangle>\<^sub>e b))"

lemma Op1E_rep_eq:
  "\<lbrakk> v :!\<^sub>e a; f \<in> FUNC1 a b \<rbrakk> \<Longrightarrow> \<langle>Op1E f v\<rangle>\<^sub>e = (\<lambda> b. f (\<langle>v\<rangle>\<^sub>e b))"
  apply (subgoal_tac "(\<lambda> b. f (\<langle>v\<rangle>\<^sub>e b)) \<in> WF_EXPRESSION")
  apply (auto simp add:Op1E_def WF_EXPRESSION_def FUNC1_def edtype_rel_def)
done

definition Op2E :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
                    'a uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr" where
"Op2E f v1 v2 = Abs_uexpr (\<lambda> b. f (\<langle>v1\<rangle>\<^sub>e b) (\<langle>v2\<rangle>\<^sub>e b))"

lemma Op2E_rep_eq:
  "\<lbrakk> x :!\<^sub>e a; y :!\<^sub>e b; f \<in> FUNC2 a b c \<rbrakk> \<Longrightarrow> \<langle>Op2E f x y\<rangle>\<^sub>e = (\<lambda> b1. f (\<langle>x\<rangle>\<^sub>e b1) (\<langle>y\<rangle>\<^sub>e b1))"
  apply (subgoal_tac "(\<lambda> b1. f (\<langle>x\<rangle>\<^sub>e b1) (\<langle>y\<rangle>\<^sub>e b1)) \<in> WF_EXPRESSION")
  apply (force simp add:Op2E_def WF_EXPRESSION_def FUNC2_def edtype_rel_def)+
done

definition Op3E :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 
                    'a uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 
                    'a uexpr \<Rightarrow> 'a uexpr" where
"Op3E f v1 v2 v3 = Abs_uexpr (\<lambda> b. f (\<langle>v1\<rangle>\<^sub>e b) (\<langle>v2\<rangle>\<^sub>e b) (\<langle>v3\<rangle>\<^sub>e b))"

lemma Op3E_rep_eq:
  "\<lbrakk> x :!\<^sub>e a; y :!\<^sub>e b; z :!\<^sub>e c; f \<in> FUNC3 a b c d \<rbrakk> \<Longrightarrow> 
     \<langle>Op3E f x y z\<rangle>\<^sub>e = (\<lambda> b1. f (\<langle>x\<rangle>\<^sub>e b1) (\<langle>y\<rangle>\<^sub>e b1) (\<langle>z\<rangle>\<^sub>e b1))"
  apply (subgoal_tac "(\<lambda> b1. f (\<langle>x\<rangle>\<^sub>e b1) (\<langle>y\<rangle>\<^sub>e b1) (\<langle>z\<rangle>\<^sub>e b1)) \<in> WF_EXPRESSION")
  apply (auto intro:typing simp add:Op3E_def WF_EXPRESSION_def FUNC3_def edtype_rel_def)
  apply (rule_tac x="d" in exI)
  apply (auto intro:typing)
done

definition DefaultE :: "'a utype \<Rightarrow> 'a uexpr" where
"DefaultE t \<equiv> LitE (default t)"

definition BotE :: "'a::BOT_SORT utype \<Rightarrow> 'a uexpr" where
"BotE a = LitE (ubot a)"

definition CoerceE :: "'a uexpr \<Rightarrow> 'a utype \<Rightarrow> 'a uexpr" where
"CoerceE e t \<equiv> if (e :\<^sub>e t) then e else DefaultE t"

definition ecoerce :: "'a uexpr \<Rightarrow> 'a uvar \<Rightarrow> 'a uexpr" where  
"ecoerce e x = Abs_uexpr (\<lambda> b. vcoerce (\<langle>e\<rangle>\<^sub>e b) x)"

lemma ecoerce_rep_eq:
  "\<langle>ecoerce v x\<rangle>\<^sub>eb = vcoerce (\<langle>v\<rangle>\<^sub>e b) x"
  apply (simp add:ecoerce_def)
  apply (subst Abs_uexpr_inverse)
  apply (simp_all add:WF_EXPRESSION_def)
  apply (rule_tac x="vtype x" in exI)
  apply (auto simp add:vcoerce_def)
done

lift_definition VarE :: "'a uvar \<Rightarrow> 'a uexpr" ("$\<^sub>e_" [999] 999)
is "\<lambda> x. (\<lambda> b. \<langle>b\<rangle>\<^sub>b x)"
  by (auto simp add:WF_EXPRESSION_def)

definition AppE :: 
  "'a::FUNCTION_SORT uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr" where
"AppE f v = Abs_uexpr (\<lambda> b. DestFunc (\<langle>f\<rangle>\<^sub>e b) (\<langle>v\<rangle>\<^sub>e b))"

lemma AppE_rep_eq:
  "\<lbrakk> f :\<^sub>e FuncType a b; v :\<^sub>e a; \<D> f \<rbrakk> \<Longrightarrow> \<langle>AppE f v\<rangle>\<^sub>e = (\<lambda> b. DestFunc (\<langle>f\<rangle>\<^sub>e b) (\<langle>v\<rangle>\<^sub>e b))"
  apply (subgoal_tac "(\<lambda> b. DestFunc (\<langle>f\<rangle>\<^sub>e b) (\<langle>v\<rangle>\<^sub>e b)) \<in> WF_EXPRESSION")
  apply (simp add:AppE_def)
  apply (simp add:WF_EXPRESSION_def)
  apply (rule_tac x="b" in exI)
  apply (auto intro:typing simp add:etype_rel_def Defined_uexpr_def)
done

definition DefinedP :: "'a uexpr \<Rightarrow> 'a upred" ("\<D>\<^sub>p") where
"DefinedP e \<equiv> LiftP (\<D> \<circ> \<langle>e\<rangle>\<^sub>e)"

definition VarDefinedP :: "'a uvar \<Rightarrow> 'a upred" ("\<V>") where
"\<V> x \<equiv> DefinedP (VarE x)"

lift_definition PermE ::
  "'a VAR_RENAME \<Rightarrow>
   'a uexpr \<Rightarrow>
   'a uexpr" is
"\<lambda> ss e. (\<langle>e\<rangle>\<^sub>e \<circ> (RenameB (inv\<^sub>s ss)))"
proof -
  fix e ss
  show "\<langle>e\<rangle>\<^sub>e \<circ> RenameB (inv\<^sub>s ss) \<in> WF_EXPRESSION"
    apply (simp add:WF_EXPRESSION_def)
    apply (insert Rep_uexpr_typed[of e])    
    apply (auto)
  done
qed

abbreviation RenameE ::
  "'a uexpr \<Rightarrow>
   'a VAR_RENAME \<Rightarrow>
   'a uexpr" ("_[_]\<^sub>e" [200] 200) where
"RenameE e ss \<equiv> PermE ss e"

adhoc_overloading
  permute PermE

definition PrimeE ::
  "'a uexpr \<Rightarrow>
   'a uexpr" where
"PrimeE e = PermE (dash on UNDASHED) e"

adhoc_overloading
  prime PrimeE

lift_definition SubstE :: 
"'a uexpr \<Rightarrow> 
 'a uexpr \<Rightarrow> 
 'a uvar \<Rightarrow> 
 'a uexpr" ("_[_'/\<^sub>e_]" [200] 200) is
"\<lambda> f v x. (\<lambda> b. \<langle>f\<rangle>\<^sub>e (b(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b)))"
  apply (simp add: WF_EXPRESSION_def)
  apply (metis Rep_uexpr_typed)
done

lift_definition SubstP ::
  "'a upred \<Rightarrow> 'a uexpr \<Rightarrow> 'a uvar \<Rightarrow> 'a upred" ("_[_'/\<^sub>p_]" [200] 200)
is "\<lambda> p v x. {b. b(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b) \<in> p}" .

lemma SubstP_no_var: "{x} \<sharp> p \<Longrightarrow> p[v/\<^sub>px] = p"
  apply (auto intro!:destPRED_intro simp add:UNREST_def SubstP.rep_eq)
  apply (metis (lifting) binding_compat binding_upd_simps binding_upd_upd evar_compat_def)
  apply (metis (full_types) binding_upd_simps(1) binding_upd_triv)
done

subsection {* Theorems *}

subsubsection {* Well-formed expression properties *}

lemma EXPRESSION_eqI [intro]:
  "\<lbrakk> \<forall> b. \<langle>e\<rangle>\<^sub>e b = \<langle>f\<rangle>\<^sub>e b \<rbrakk> \<Longrightarrow>
  e = f"
  apply (case_tac e, case_tac f, auto)
  apply (rule Rep_uexpr_intro)
  apply (auto)
done

theorem uexpr_type [typing]: 
"e :\<^sub>e t \<Longrightarrow>
\<langle>e\<rangle>\<^sub>e b : t"
  by (simp add:WF_EXPRESSION_def etype_rel_def)

theorem uexpr_has_type [typing]: 
"\<exists> t. e :\<^sub>e t"
  by (metis Rep_uexpr_typed etype_rel_def)

lemma uexpr_value_exists:
  "\<exists> t v. v : t \<and> \<langle>e\<rangle>\<^sub>e b = v"
  by (metis Rep_uexpr_typed)

lemma uexpr_value_elim [elim]:
  "\<And> t v b. \<lbrakk> v : t; \<langle>e\<rangle>\<^sub>e b = v \<rbrakk> \<Longrightarrow> P \<Longrightarrow> P"
  by (simp)
 
subsubsection {* Closure Theorems *}

lemma uexpr_bindings [simp,intro]:
  "\<forall> b. e b : t \<Longrightarrow> e \<in> WF_EXPRESSION"
  by (auto simp add:WF_EXPRESSION_def)

subsubsection {* Typing Theorems *}

theorem VarE_type [typing]: "t = vtype x \<Longrightarrow> VarE x :\<^sub>e t"
  by (simp add:VarE.rep_eq binding_def typing etype_rel_def)

theorem LitE_type [typing]: 
"v : t \<Longrightarrow> LitE v :\<^sub>e t"
  by (auto simp add:etype_rel_def LitE_rep_eq)

theorem BotE_type [typing]:
"BotE a :\<^sub>e a"
  by (simp add:BotE_def typing)

theorem Op1E_type [typing]:
  "\<lbrakk> x :!\<^sub>e a; f \<in> FUNC1 a b \<rbrakk> \<Longrightarrow> Op1E f x :!\<^sub>e b"
  by (auto simp add:Op1E_rep_eq edtype_rel_def typing FUNC1_def)

theorem Op2E_type [typing]:
  "\<lbrakk> x :!\<^sub>e a; y :!\<^sub>e b; f \<in> FUNC2 a b c \<rbrakk> \<Longrightarrow> Op2E f x y :!\<^sub>e c"
  by (auto simp add:Op2E_rep_eq edtype_rel_def typing FUNC2_def)

theorem AppE_type [typing]:
"\<lbrakk> f :\<^sub>e FuncType a b; \<D> f; v :\<^sub>e a \<rbrakk> \<Longrightarrow> AppE f v :\<^sub>e b"
  by (auto intro:typing simp add:AppE_rep_eq etype_rel_def Defined_uexpr_def)

theorem DefaultE_type [typing]:
"DefaultE t :\<^sub>e t"
  by (simp add:DefaultE_def typing)

theorem CoerceE_type [typing]:
"CoerceE e t :\<^sub>e t"
  by (simp add: CoerceE_def typing)

theorem ecoerce_compat [typing]:
  "ecoerce v x \<rhd>\<^sub>e x"
  by (simp add:evar_compat_def ecoerce_rep_eq typing)

theorem RenameE_type [typing]:
  "e :\<^sub>e t \<Longrightarrow> (ss\<bullet>e) :\<^sub>e t" 
  by (simp add:etype_rel_def PermE.rep_eq)

theorem RenameE_ecompat [typing]:
  "v \<rhd>\<^sub>e x \<Longrightarrow> ss\<bullet>v \<rhd>\<^sub>e x"
  by (simp add:evar_compat_def PermE.rep_eq)

theorem PrimeE_type [typing]:
  "e :\<^sub>e t \<Longrightarrow> e\<acute> :\<^sub>e t"
  by (simp add:etype_rel_def PermE.rep_eq PrimeE_def)

theorem PrimeE_ecompat [typing]:
  "e \<rhd>\<^sub>e x \<Longrightarrow> e\<acute> \<rhd>\<^sub>e x"
  by (simp add:evar_compat_def PermE.rep_eq PrimeE_def)

theorem SubstE_type [typing]:
"\<lbrakk> v :\<^sub>e vtype x; e :\<^sub>e t \<rbrakk> \<Longrightarrow>
 e[v/\<^sub>ex] :\<^sub>e t"
  by (simp add:SubstE.rep_eq etype_rel_def binding_update1)

subsubsection {* Definedness Theorems *}

theorem LitE_defined [defined]: "\<D> v \<Longrightarrow> \<D> (LitE v)"
  by (auto simp add:LitE_rep_eq Defined_uexpr_def defined)

theorem BotE_defined [defined]: "\<not> \<D> (BotE a)"
  apply (auto simp add:BotE_def LitE_rep_eq Defined_uexpr_def defined)
  apply (metis ubot_type)
done

theorem DefaultE_defined [defined]: "\<D> (DefaultE t)"
  by (auto intro:defined typing simp add: DefaultE_def)

theorem CoerceE_defined [defined]: "\<D> e \<Longrightarrow> \<D> (CoerceE e t)"
  by (auto simp add:CoerceE_def defined)

theorem VarE_defined [defined]: "aux x \<Longrightarrow> \<D> (VarE x)"
  by (simp add:VarE.rep_eq Defined_uexpr_def defined)

theorem VarE_ecompat [typing]: "\<lbrakk> vtype x = vtype y; aux x = aux y \<rbrakk> \<Longrightarrow> VarE y \<rhd>\<^sub>e x"
  by (force intro:typing defined)

lemma SubstE_defined [defined]:
  "\<D> e \<Longrightarrow> \<D> (e[v/\<^sub>ey])"
  by (auto simp add:SubstE.rep_eq Defined_uexpr_def)

lemma SubstE_compat [typing]:
  "e \<rhd>\<^sub>e x \<Longrightarrow> e[v/\<^sub>ey] \<rhd>\<^sub>e x"
  by (auto simp add:SubstE.rep_eq Defined_uexpr_def evar_compat_def)

subsubsection {* bfun theorems *}

lemma LitE_bfun [simp]: "a : t \<Longrightarrow> \<langle>LitE a\<rangle>\<^sub>e = (\<lambda> x. a)"
  by (auto simp add:LitE_def)

lemma ecoerce_reduce1 [simp]:
  "v \<rhd>\<^sub>e x \<Longrightarrow> ecoerce v x = v"
  by (simp add:ecoerce_def typing)

(*
lemma ecoerce_reduce2 [simp]:
  "\<not> (v \<rhd>\<^sub>e x) \<Longrightarrow> ecoerce v x = DefaultE (vtype x)"
  by (simp add:ecoerce_def typing)
*)

subsubsection {* @{term UNREST_EXPR} Theorems *}

theorem UNREST_EXPR_member [simp] :
"vs \<sharp> f \<Longrightarrow> \<langle>f\<rangle>\<^sub>e (b \<oplus>\<^sub>b b' on vs) = \<langle>f\<rangle>\<^sub>e b "
  by (auto simp add:UNREST_EXPR_def)

theorem UNREST_EXPR_empty [unrest] :
"UNREST_EXPR {} e"
  by (simp add: UNREST_EXPR_def)

lemma UNREST_EXPR_union [unrest]:
"\<lbrakk>UNREST_EXPR vs1 p;
 UNREST_EXPR vs2 p\<rbrakk> \<Longrightarrow>
 UNREST_EXPR (vs1 \<union> vs2) p"
  apply (simp add: UNREST_EXPR_def)
  apply (clarify)
  apply (metis binding_override_simps(1))
done

theorem UNREST_EXPR_subset :
"\<lbrakk>vs1 \<sharp> e;
 vs2 \<subseteq> vs1\<rbrakk> \<Longrightarrow>
 UNREST_EXPR vs2 e"
  apply (auto simp add:UNREST_EXPR_def)
  apply (metis binding_override_simps(5) double_diff order_refl)
done

theorem UNREST_EXPR_unionE [elim]: 
  "\<lbrakk> UNREST_EXPR (xs \<union> ys) p; \<lbrakk> UNREST_EXPR xs p; UNREST_EXPR ys p \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (metis UNREST_EXPR_subset inf_sup_ord(4) sup_ge1)

theorem UNREST_EqualP [unrest] :
"\<lbrakk> vs \<sharp> e; vs \<sharp> f \<rbrakk> \<Longrightarrow>
 vs \<sharp> (e ==\<^sub>p f)"
  apply (auto simp add:EqualP_def)
  apply (drule_tac ?vs2.0="vs" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (drule_tac ?vs2.0="vs" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (simp add:UNREST_EXPR_def UNREST_def)
done

theorem UNREST_EqualP_alt [unrest] :
"\<lbrakk> vs1 \<sharp> e; vs2 \<sharp> f \<rbrakk> \<Longrightarrow>
 (vs1 \<inter> vs2) \<sharp> (e ==\<^sub>p f)"
  apply (auto simp add:EqualP_def)
  apply (drule_tac ?vs2.0="vs1 \<inter> vs2" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (drule_tac ?vs2.0="vs1 \<inter> vs2" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (simp add:UNREST_EXPR_def UNREST_def)
done

theorem UNREST_EXPR_VarE [unrest] :
"x \<notin> vs \<Longrightarrow> vs \<sharp> (VarE x)"
  by (simp add:VarE.rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_LitE [unrest] :
"vs \<sharp> (LitE v)"
  by (simp add:LitE_rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_Op1E [unrest] :
"\<lbrakk> x :!\<^sub>e a; f \<in> FUNC1 a b; vs \<sharp> x \<rbrakk> \<Longrightarrow> vs \<sharp> (Op1E f x)"
  by (simp add:Op1E_rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_Op2E [unrest] :
"\<lbrakk> x :!\<^sub>e a; y :!\<^sub>e b; f \<in> FUNC2 a b c; 
   vs \<sharp> x; vs \<sharp> y \<rbrakk> \<Longrightarrow> vs \<sharp> (Op2E f x y)"
  by (auto simp add:Op2E_rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_AppE [unrest] :
"\<lbrakk> f :\<^sub>e FuncType a b; v :\<^sub>e a; \<D> f; vs \<sharp> f; vs \<sharp> v \<rbrakk> \<Longrightarrow> vs \<sharp> (AppE f v)"
  by (simp add:AppE_rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_DefaultE [unrest] :
"vs \<sharp> (DefaultE t)"
  by (simp add:DefaultE_def unrest)

theorem UNREST_EXPR_CoerceE [unrest] :
"vs \<sharp> e \<Longrightarrow> vs \<sharp> (CoerceE e t)"
  by (auto intro:unrest simp add:CoerceE_def)

lemma UNREST_ecoerce [unrest]:
  "xs \<sharp> e \<Longrightarrow> xs \<sharp> (ecoerce e x)"
  by (simp add:ecoerce_rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_RenameE [unrest] :
"vs \<sharp> p \<Longrightarrow>
 UNREST_EXPR (\<langle>ss\<rangle>\<^sub>s ` vs) (ss\<bullet>p)"
  by (auto simp add: UNREST_EXPR_def PermE.rep_eq RenameB_override_distr1 closure)

theorem UNREST_EXPR_RenameE_alt [unrest] :
"\<lbrakk> UNREST_EXPR (inv\<^sub>s ss `\<^sub>s vs) p \<rbrakk>   \<Longrightarrow>
   UNREST_EXPR vs (ss\<bullet>p)"
  by (auto simp add: UNREST_EXPR_def PermE.rep_eq RenameB_override_distr1 closure)

theorem UNREST_EXPR_PrimeE [unrest] :
"UNREST_EXPR vs e \<Longrightarrow>
 UNREST_EXPR (\<langle>dash on UNDASHED\<rangle>\<^sub>s ` vs) e\<acute>"
  by (auto intro:unrest simp add:PrimeE_def)

theorem UNREST_EXPR_PrimeE_alt [unrest] :
"UNREST_EXPR (\<langle>dash on UNDASHED\<rangle>\<^sub>s ` vs) e \<Longrightarrow>
 UNREST_EXPR vs e\<acute>"
  by (simp add:PrimeE_def urename closure unrest)

theorem UNREST_EXPR_SubstE [unrest] :  
"\<lbrakk> vs1 \<sharp> e; vs2 \<sharp> v; x \<notin> vs1; vs = (vs1 \<inter> vs2) \<rbrakk> \<Longrightarrow>
 vs \<sharp> (e[v/\<^sub>ex])"
  apply (auto simp add:UNREST_EXPR_def SubstE.rep_eq evar_compat_def)
  apply (metis binding_override_simps(6) inf_commute)
done

theorem UNREST_SubstE_var [unrest] :  
  "\<lbrakk> vs1 \<sharp> e; vs2 \<sharp> v; x \<notin> vs1; x \<in> vs2 \<rbrakk> \<Longrightarrow>
   {x} \<sharp> (e[v/\<^sub>ex])"
  apply (auto simp add:SubstE.rep_eq UNREST_def UNREST_EXPR_def)
  apply (metis binding_compat binding_upd_override binding_upd_upd evar_compat_def)
done

lemma UNREST_SubstE_simple [unrest]:
  "\<lbrakk> vs \<sharp> e; vs \<sharp> v; y \<notin> vs \<rbrakk> \<Longrightarrow> vs \<sharp> e[v/\<^sub>ey]"
  by (rule unrest, auto)

lemma dash_single_rename_func_on [closure]: "rename_func_on dash {x}"
  by (simp add:rename_func_on_def)

theorem UNREST_SubstP [unrest] :  
  "\<lbrakk> vs1 \<sharp> p; vs2 \<sharp> v; x \<notin> vs1; vs = (vs1 \<inter> vs2) \<rbrakk> \<Longrightarrow>
   vs \<sharp> (p[v/\<^sub>px])"
  apply (auto simp add:SubstP_def UNREST_def UNREST_EXPR_def)
  apply (drule_tac x="b1(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b1)" in bspec, simp)
  apply (drule_tac x="b1" in spec)
  apply (drule_tac x="b1 \<oplus>\<^sub>b b2 on vs1" in spec) back
  apply (simp)
  apply (drule_tac x="b1(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b1) \<oplus>\<^sub>b b2 on vs2" in spec)
  apply (simp)
  apply (subgoal_tac "x \<notin> vs1 \<inter> vs2")
  apply (simp)
  apply (metis inf_commute)
  apply (auto)
done

theorem UNREST_SubstP_var [unrest] :  
   "{x} \<sharp> v \<Longrightarrow>
    {x} \<sharp> (p[v/\<^sub>px])"
  by (auto simp add:SubstP_def UNREST_def UNREST_EXPR_def)

lemma UNREST_SubstP_simple [unrest]: 
  fixes P :: "'a upred"
  assumes "vs \<sharp> v" "vs - {x} \<sharp> P"
  shows "vs \<sharp> P[v/\<^sub>px]"
  using assms by (auto simp add:UNREST_def SubstP.rep_eq)

lemma UNREST_UNDASHED_PrimeE [unrest]:
  "UNREST_EXPR DASHED e \<Longrightarrow> UNREST_EXPR UNDASHED e\<acute>"
  by (metis (full_types) UNREST_EXPR_PrimeE_alt dash_UNDASHED_image dash_UNDASHED_rename_func rename_on_image1 subset_refl)

lemma UNREST_DASHED_PrimeE [unrest]:
  "UNREST_EXPR UNDASHED e \<Longrightarrow> UNREST_EXPR DASHED e\<acute>"
  by (metis (full_types) UNREST_EXPR_PrimeE_alt dash_UNDASHED_image dash_UNDASHED_rename_func rename_on_image2 subset_refl)

text {* Some unrestriction laws relating to variable classes *}

lemma UNREST_NON_REL_VAR_DASHED [unrest]:
  "x \<in> DASHED \<Longrightarrow> NON_REL_VAR \<sharp> (VarE x)"
  by (auto intro:unrest)

subsection {* Boolean Expressions *}

definition "TrueE \<equiv> LitE (MkBool True)"
definition "FalseE \<equiv> LitE (MkBool False)"
definition "ExprP e = LiftP (DestBool \<circ> \<langle>e\<rangle>\<^sub>e)"
abbreviation VarP :: "'a::BOOL_SORT uvar \<Rightarrow> 'a upred" ("$\<^sub>p_" [999] 999) where
"VarP x \<equiv> ExprP (VarE x)"

lift_definition PredE :: "'a::BOOL_SORT upred \<Rightarrow> 'a uexpr" is "\<lambda> p. \<lambda> b. MkBool (b \<in> destPRED p)"
  by (auto intro:typing simp add:WF_EXPRESSION_def)

subsubsection {* Typing Theorems *}

theorem TrueE_type [typing]: "TrueE :\<^sub>e BoolType"
  apply (simp add: TrueE_def)
  apply (rule typing)+
done

theorem FalseE_type [typing]: "FalseE :\<^sub>e BoolType"
  apply (simp add: FalseE_def)
  apply (rule typing)+
done

theorem PredE_type [typing]:
"PredE p :\<^sub>e BoolType"
  by (auto intro:typing simp add:PredE.rep_eq etype_rel_def)

subsubsection {* Definedness Theorems *}

theorem TrueE_defined [defined]: "\<D> TrueE"
  by (auto intro: defined typing simp add:TrueE_def)

theorem FalseE_defined [defined]: "\<D> FalseE"
  by (auto intro: defined typing simp add:FalseE_def)

subsubsection {* Laws about booleans *}
 
lemma ExprP_TrueE [simp]: "ExprP TrueE = true"
  by (auto intro:typing simp add:ExprP_def LitE_rep_eq TrueE_def LiftP_def TrueP_def)

lemma ExprP_FalseE [simp]: "ExprP FalseE = false"
  by (auto intro:typing simp add:ExprP_def LitE_rep_eq FalseE_def LiftP_def FalseP_def)

subsubsection {* @{term UNREST_EXPR} Theorems *}

theorem UNREST_EXPR_TrueE [unrest]: "vs \<sharp> TrueE"
  by (simp add:TrueE_def unrest)

theorem UNREST_EXPR_FalseE [unrest]: "vs \<sharp> FalseE"
  by (simp add:FalseE_def unrest)

theorem UNREST_ExprP [unrest]:
"\<lbrakk> vs \<sharp> e \<rbrakk> \<Longrightarrow> vs \<sharp> (ExprP e)"
  apply (simp add:ExprP_def)
  apply (rule_tac ?vs1.0="- vs" in UNREST_LiftP_alt)
  apply (simp add:WF_BINDING_PRED_def UNREST_EXPR_def)
  apply (clarify)
  apply (drule_tac x="b2" in spec)
  apply (drule_tac x="b1" in spec)
  apply (drule binding_override_equiv)
  apply (metis binding_override_minus)
  apply (force)
done

theorem UNREST_EXPR_PredE [unrest]: 
"vs \<sharp> p \<Longrightarrow> vs \<sharp> (PredE p)"
  apply (auto simp add:UNREST_EXPR_def UNREST_def MkBool_type PredE.rep_eq)
  apply (metis (full_types) binding_override_simps(2) binding_override_simps(3))
done
  
lemma UNREST_VarP [unrest]:
  "x \<notin> vs \<Longrightarrow> vs \<sharp> (VarP x)"
  by (auto intro:unrest)

theorem uexpr_UNREST_binding_equiv :
"\<lbrakk> - vs \<sharp> e; b1 \<cong> b2 on vs \<rbrakk> 
 \<Longrightarrow> \<langle>e\<rangle>\<^sub>eb1 = \<langle>e\<rangle>\<^sub>eb2"
  by (metis UNREST_EXPR_def binding_equiv_override)

subsection {* List Expressions *}

default_sort LIST_SORT

abbreviation NilE :: "'a utype \<Rightarrow> 'a uexpr" where
"NilE a \<equiv> LitE (NilV a)"

abbreviation ConsE :: 
  "'a utype \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr" where
"ConsE a x xs \<equiv> Op2E (ConsV a) x xs"

fun ListE :: "'a utype \<Rightarrow> ('a uexpr) list \<Rightarrow> 'a uexpr" where
"ListE a [] = NilE a" |
"ListE a (x # xs) = ConsE a x (ListE a xs)"

abbreviation ConcatE ::
  "'a utype \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr" where
"ConcatE a xs ys \<equiv> Op2E (ConcatV a) xs ys"

abbreviation PrefixE ::
  "'a uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr" where
"PrefixE xs ys \<equiv> Op2E PrefixV xs ys"

(*
abbreviation IntersyncE ::
  "'a::REACTIVE_SORT UTYPE \<Rightarrow>
   'a uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr \<Rightarrow> 'a uexpr" where
"IntersyncE a s xs ys \<equiv> Op3E (IntersyncV a) s xs ys"
*)

default_sort VALUE

subsubsection {* Typing Theorems *}

lemma NilE_type [typing]: 
  "a \<in> ListPerm \<Longrightarrow> NilE a :!\<^sub>e ListType a"
  by (auto intro:typing simp add:edtype_rel_def LitE_rep_eq)

(*
lemma ConsE_type [typing]:
  "\<lbrakk> a \<in> ListPerm; x :!\<^sub>e a; xs :!\<^sub>e ListType a \<rbrakk> \<Longrightarrow> ConsE a x xs :!\<^sub>e ListType a"
  by (auto intro:typing closure simp add: Op2E_rep_eq)

lemma ConcatE_type [typing]:
  "\<lbrakk> a \<in> ListPerm; xs :!\<^sub>e ListType a; ys :!\<^sub>e ListType a \<rbrakk> 
    \<Longrightarrow> ConcatE a xs ys :!\<^sub>e ListType a"
  by (auto intro:typing closure simp add: Op2E_rep_eq)
*)

subsubsection {* Definedness Theorems *}

lemma NilE_defined [defined]:
  "a \<in> ListPerm \<Longrightarrow> \<D> (NilE a)"
  by (auto intro:typing defined simp add:Defined_uexpr_def LitE_rep_eq edtype_rel_def)

(*
lemma ConsE_defined [defined]:
  "\<lbrakk> a \<in> ListPerm; x :!\<^sub>e a; xs :!\<^sub>e ListType a \<rbrakk> \<Longrightarrow> \<D> (ConsE a x xs)"
  by (metis ConsE_type edtype_defined)

lemma ConcatE_defined [defined]:
  "\<lbrakk> a \<in> ListPerm; xs :!\<^sub>e ListType a; ys :!\<^sub>e ListType a \<rbrakk> 
    \<Longrightarrow> \<D> (ConcatE a xs ys)"
  by (metis ConcatE_type edtype_defined)
*)  

subsection {* Finite Set Expressions *}

abbreviation "FEmptyE a \<equiv> LitE (FEmptyV a)"
abbreviation "FInsertE a \<equiv> Op2E (FInsertV a)"
abbreviation "FUnionE a \<equiv> Op2E (FUnionV a)"
abbreviation "FInterE a \<equiv> Op2E (FUnionV a)"
abbreviation "FMemberE  \<equiv> Op2E FMemberV"
abbreviation "FNMemberE  \<equiv> Op2E FNMemberV"

subsection {* Event List / Set Hack *}

(* FIXME: Until polymorphic expressions are implemented, we supply type-specific constructs
   for event lists and sets *)

abbreviation "EvNilE       \<equiv> NilE EventType"
abbreviation "EvConsE      \<equiv> ConsE EventType"
abbreviation "EvConcatE    \<equiv> ConcatE EventType"
(* abbreviation "EvIntersyncE \<equiv> IntersyncE EventType" *)

abbreviation "EvFEmptyE \<equiv> FEmptyE EventType"
abbreviation "EvFInsertE \<equiv> FInsertE EventType"
abbreviation "EvFUnionE \<equiv> FUnionE EventType"
abbreviation "EvFInterE \<equiv> FInterE EventType"

end