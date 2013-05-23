(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_expr.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM expressions *}

theory utp_vdm_expr
imports 
  utp_vdm_sorts 
begin

text {* Getting an accurate representation of VDM expressions is hard,
in as much as Isabelle's type-system limits our ability to do proper
type-inference. Although we can infer the type of an expression, the
types of variables are immediately erased when placed in a
context. This means that if the context doesn't fully qualify the type
of a variable, there is no way to quantify it other than by coercing
it in place. It is therefore impossible to create quantifiers which *}

default_sort vbasic

subsection {* VDM expresssion type *}

typedef 'a vdme = "UNIV :: (vdmv WF_BINDING \<rightharpoonup> 'a::vbasic) set" ..

declare Rep_vdme [simp]
declare Rep_vdme_inverse [simp]
declare Abs_vdme_inverse [simp]

lemma Rep_vdme_intro [intro]:
  "Rep_vdme x = Rep_vdme y \<Longrightarrow> x = y"
  by (simp add:Rep_vdme_inject)

lemma Rep_vdme_elim [elim]:
  "\<lbrakk> x = y; Rep_vdme x = Rep_vdme y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_vdme

abbreviation "EvalD \<equiv> Rep_vdme"

notation EvalD ("\<lbrakk>_\<rbrakk>\<^sub>v")

subsection {* Constants *}

definition UNREST_VDME :: "(vdmv VAR) set \<Rightarrow> 'a vdme \<Rightarrow> bool" where
"UNREST_VDME vs e \<equiv> (\<forall> b1 b2. \<lbrakk>e\<rbrakk>\<^sub>v(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>e\<rbrakk>\<^sub>v b1)" 

abbreviation MkVarD :: "char list \<Rightarrow> 'a::vbasic itself \<Rightarrow> vdmv VAR" where
"MkVarD n t \<equiv> (MkPlain n (embTYPE (Type t)) False)"

definition VarD :: "string \<Rightarrow> 'a::vbasic vdme" ("$_") where
"VarD n = Abs_vdme (\<lambda> b. Project (ProjBasicD (\<langle>b\<rangle>\<^sub>b (MkVarD n TYPE('a)))))"

(* declare [[coercion VarD]] *)

definition BotDE :: "'a vdme" ("\<bottom>\<^sub>v") where
"BotDE = Abs_vdme (\<lambda> b. None)"

definition LitD :: "'a::vbasic \<Rightarrow> 'a vdme" ("<_>") where
"LitD x = Abs_vdme (\<lambda> b. Some x)"

definition UOpD :: "('a::vbasic \<rightharpoonup> 'b::vbasic) \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme" where
"UOpD f v = Abs_vdme (\<lambda> b. (Rep_vdme v b) >>= f)"

text {* Build a unary partial function from a normal binary HOL function *}

definition upfun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b option)" where
"upfun f = (\<lambda> v. Some (f v))"

abbreviation "UOpD' f \<equiv> UOpD (upfun f)"

definition BOpD :: "('a::vbasic * 'b::vbasic \<rightharpoonup> 'c::vbasic) 
                   \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme \<Rightarrow> 'c vdme" where
"BOpD f v1 v2 = Abs_vdme (\<lambda> b. do { x <- \<lbrakk>v1\<rbrakk>\<^sub>v b; y <- \<lbrakk>v2\<rbrakk>\<^sub>v b; f (x, y) })"

text {* Build a binary partial function from a normal binary HOL function *}

definition bpfun :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a * 'b \<Rightarrow> 'c option)" where
"bpfun f \<equiv> (\<lambda> (v1, v2). Some (f v1 v2))"

abbreviation "BOpD' f \<equiv> BOpD (bpfun f)"

definition ListD :: "'a::vbasic vdme list \<Rightarrow> 'a list vdme" where
"ListD xs = Abs_vdme (\<lambda> b. mapM (\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>v b) xs)"

(* declare [[coercion ListD]] *)

definition FSetD :: "'a::vbasic vdme fset \<Rightarrow> 'a fset vdme" where
"FSetD xs = Abs_vdme (\<lambda> b. fset_option ((\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>v b) `\<^sub>f xs))"

(* declare [[coercion FSetD]] *)

lift_definition LiftD :: "'a::vbasic vdme \<Rightarrow> vdmv WF_EXPRESSION" is
"\<lambda> f. (\<lambda> b. case \<lbrakk>f\<rbrakk>\<^sub>v b of Some v \<Rightarrow> BasicD (Inject v) | None \<Rightarrow> \<bottom>\<^bsub>VTYPE('a)\<^esub>)"
  apply (simp add:WF_EXPRESSION_def)
  apply (rule_tac x="embTYPE VTYPE('a)" in exI)
  apply (rule)
  apply (simp add:type_rel_vdmt)
  apply (case_tac "\<lbrakk>vdme\<rbrakk>\<^sub>v b")
  apply (auto)
done

definition ForallD :: "('a \<Rightarrow> bool vdme) \<Rightarrow> bool vdme" where
"ForallD f = Abs_vdme (\<lambda> b. (Some (\<forall> x. \<lbrakk>f x\<rbrakk>\<^sub>v b = Some True)))"

definition ExistsD :: "('a \<Rightarrow> bool vdme) \<Rightarrow> bool vdme" where
"ExistsD f = Abs_vdme (\<lambda> b. (Some (\<exists> x. \<lbrakk>f x\<rbrakk>\<^sub>v b = Some True)))"

instantiation option :: (type) DEFINED
begin

definition Defined_option :: "'a option \<Rightarrow> bool" where
"\<D>(x) \<longleftrightarrow> x \<noteq> None"

instance ..

end

instantiation vdme :: (vbasic) DEFINED
begin

definition Defined_vdme :: "'a vdme \<Rightarrow> bool" where
"\<D>(e) \<longleftrightarrow> (\<forall> b. (\<lbrakk>e\<rbrakk>\<^sub>v b \<noteq> None))"

instance ..

end

abbreviation DefinedD :: "'a vdme \<Rightarrow> bool vdme" where
"DefinedD v \<equiv> LitD (\<D> v)"

definition CoerceD :: "'a vdme \<Rightarrow> 'a set \<Rightarrow> 'a vdme" where
"CoerceD e t \<equiv> Abs_vdme (\<lambda> b. if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>v b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>v b) \<in> t)
                              then \<lbrakk>e\<rbrakk>\<^sub>v b 
                              else None)"

subsection {* Extend the UTP parser for VDM expressions *}

nonterminal vexpr and vexprs and vty

syntax
  "_uexpr_vdme"   :: "vexpr \<Rightarrow> uexpr" ("_")
  "_vexpr_brack"  :: "vexpr \<Rightarrow> vexpr" ("'(_')")
  "_vexprs"       :: "[vexpr, vexprs] => vexprs" ("_,/ _")
  ""              :: "vexpr => vexprs" ("_")
  "_vexpr_var"    :: "string \<Rightarrow> vexpr" ("$_")
  "_vexpr_lit"    :: "'a::vbasic \<Rightarrow> vexpr" ("!_!")
  "_vexpr_forall" :: "pttrn \<Rightarrow> vexpr \<Rightarrow> vexpr" ("(3forall _./ _)" [0, 10] 10)
  "_vexpr_exists" :: "pttrn \<Rightarrow> vexpr \<Rightarrow> vexpr" ("(3exists _./ _)" [0, 10] 10)
  "_vexpr_coerce"  :: "vexpr \<Rightarrow> vty \<Rightarrow> vexpr" (infix ":" 50)

translations
  "_uexpr_vdme e"      == "CONST LiftD e"
  "_vexpr_var x"       == "CONST VarD x"
  "_vexpr_lit v"       == "CONST LitD v"
  "_vexpr_brack e"     => "e"
  "_vexpr_forall x e"  == "CONST ForallD (\<lambda>x. e)"
  "_vexpr_exists x e"  == "CONST ExistsD (\<lambda>x. e)"
  "_vexpr_coerce e t"  == "CONST CoerceD e t"

subsection {* @{term UNREST_VDME} theorems *}

lemma UNREST_VDME_VarE [unrest]: 
  "UNREST_VDME (VAR - {MkVarD n TYPE('a)}) ($n :: 'a vdme)"
  by (simp add: UNREST_VDME_def VarD_def)

lemma UNREST_VDME_BotDE [unrest]: 
  "UNREST_VDME vs \<bottom>\<^sub>v"
  by (simp add:UNREST_VDME_def BotDE_def)

lemma UNREST_VDME_LitD [unrest]: 
  "UNREST_VDME vs <x>"
  by (simp add:UNREST_VDME_def LitD_def)

lemma UNREST_VDME_ForallD [unrest]:
  "\<forall> e. UNREST_VDME vs (f e) \<Longrightarrow> UNREST_VDME vs (ForallD f)"
  by (simp add:UNREST_VDME_def ForallD_def)

lemma UNREST_VDME_ExistsD [unrest]:
  "\<forall> e. UNREST_VDME vs (f e) \<Longrightarrow> UNREST_VDME vs (ExistsD f)"
  by (simp add:UNREST_VDME_def ExistsD_def)

lemma UNREST_VDME_UOpD [unrest]: 
  "UNREST_VDME vs v \<Longrightarrow> UNREST_VDME vs (UOpD f v)"
  by (simp add:UNREST_VDME_def UOpD_def)

lemma UNREST_VDME_BOpD [unrest]: 
  "\<lbrakk> UNREST_VDME vs v1; UNREST_VDME vs v2 \<rbrakk> \<Longrightarrow> UNREST_VDME vs (BOpD f v1 v2)"
  by (simp add:UNREST_VDME_def BOpD_def)

lemma UNREST_VDME_ListD [unrest]: 
  "\<lbrakk> \<forall> x \<in> set xs. UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (ListD xs)"
  apply (induct xs)
  apply (auto simp add:UNREST_VDME_def ListD_def)
done

lemma UNREST_VDME_FSetE [unrest]: 
  "\<lbrakk> \<forall> x \<in>\<^sub>f xs. UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (FSetD xs)"
  apply (simp add:UNREST_VDME_def FSetD_def)
  apply (clarify)
  apply (simp add:fimage.rep_eq fset_option_def)
  apply (safe)
oops

lemma UNREST_VDME_CoerceD [unrest]:
  "\<lbrakk> UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (CoerceD x t)"
  by (auto simp add:UNREST_VDME_def CoerceD_def)

lemma UNREST_EXPR_LiftD [unrest]:
  "UNREST_VDME vs e \<Longrightarrow> UNREST_EXPR vs (LiftD e)"
  by (simp add:UNREST_EXPR_def UNREST_VDME_def LiftD.rep_eq)

subsection {* Definedness theorems *}

lemma LiftD_defined [defined]: "\<D> v \<Longrightarrow> \<D> (LiftD v)"
  apply (auto simp add:Defined_WF_EXPRESSION_def Defined_vdme_def LiftD.rep_eq)
  apply (metis Defined_vdmv_def InjVB_def InjVB_nbot option.simps(5))
done

lemma LitD_defined [defined]:
  "\<D> (LitD v)"
  by (simp add:LitD_def Defined_vdme_def)

lemma BotDE_not_defined [defined]:
  "\<D> \<bottom>\<^sub>v = False"
  by (simp add:BotDE_def Defined_vdme_def)

lemma UOpD_EvalD_defined [defined]: 
  "\<lbrakk> \<D> v; \<forall> b. the (\<lbrakk>v\<rbrakk>\<^sub>v b) \<in> dom f \<rbrakk> \<Longrightarrow> \<D> (UOpD f v)"
  apply (auto simp add:UOpD_def Defined_vdme_def, (drule_tac x="b" in spec)+)
  apply (auto)
done

lemma BOpD_EvalD_defined [defined]: 
  "\<lbrakk> \<D> v1; \<D> v2; \<forall> b. (the (\<lbrakk>v1\<rbrakk>\<^sub>v b), the (\<lbrakk>v2\<rbrakk>\<^sub>v b)) \<in> dom f \<rbrakk> \<Longrightarrow> \<D> (BOpD f v1 v2)"
  apply (auto simp add:BOpD_def Defined_vdme_def, (drule_tac x="b" in spec)+)
  apply (auto)
done

lemma upfun_dom [defined]: 
  "dom (upfun f) = UNIV"
  by (auto simp add:upfun_def)

lemma bpfun_dom [defined]: 
  "dom (bpfun f) = UNIV"
  by (auto simp add:bpfun_def)

lemma EvalD_defined [defined]: "\<D> v \<Longrightarrow> \<D> (\<lbrakk>v\<rbrakk>\<^sub>vb)"
  by (simp add:Defined_option_def Defined_vdme_def)

lemma Some_defined [defined]: "\<D> (Some x)"
  by (simp add:Defined_option_def)

lemma None_not_defined [defined]: "\<not> \<D> None"
  by (simp add:Defined_option_def)

subsection {* Typing theorems *}

text {* This lemma glues typing in the VDM model to general UTP typing *}

lemma SemE_expr_type [simp]: 
  "expr_type (LiftD (v::'a vdme)) = embTYPE VTYPE('a)"
  apply (simp add:expr_type_def etype_rel_def LiftD.rep_eq type_rel_vdmt)
  apply (rule the_equality, rule)
  apply (case_tac "\<lbrakk>v\<rbrakk>\<^sub>v b")
  apply (auto)
  apply (drule_tac x="\<B>" in spec)
  apply (case_tac "\<lbrakk>v\<rbrakk>\<^sub>v \<B>")
  apply (auto)
  apply (metis BasicD_type_cases BotI_type_cases prjTYPE_inv_vdm)
  apply (metis BasicD_type_cases Inject_type prjTYPE_inv_vdm vbasic_type_rel_uniq)
done

lemma LiftD_type [typing]: 
  "LiftD (v :: 'a vdme) :\<^sub>e embTYPE VTYPE('a)"
  apply (auto simp add:etype_rel_def LiftD.rep_eq)
  apply (case_tac "\<lbrakk>v\<rbrakk>\<^sub>v b")
  apply (auto simp add:type_rel_vdmt)
done

lemma LiftD_EvalE_compat [typing]:
  "\<lbrakk> \<D> v; vtype x = embTYPE VTYPE('a) \<rbrakk> \<Longrightarrow> \<lbrakk>LiftD (v :: 'a vdme)\<rbrakk>\<epsilon>b \<rhd> x"
  apply (rule) back back
  apply (force intro:typing defined)
  apply (force intro:defined)
done

lemma LiftD_expr_compat [typing]:
  "\<lbrakk> \<D> v; vtype x = embTYPE VTYPE('a) \<rbrakk> \<Longrightarrow> LiftD (v :: 'a vdme) \<rhd>\<^sub>e x"
  apply (rule) back
  apply (force intro:typing defined)
  apply (force intro:defined)
done

subsection {* Evaluation theorems *}

lemma EvalE_LiftD [evale]:
  "\<D> (\<lbrakk>v\<rbrakk>\<^sub>vb) \<Longrightarrow> \<lbrakk>LiftD v\<rbrakk>\<epsilon>b = BasicD (Inject (the (\<lbrakk>v\<rbrakk>\<^sub>vb)))"
  by (auto simp add:EvalE_def LiftD.rep_eq Defined_option_def)

lemma EvalE_LiftD_ndefined [evale]:
  "\<not> \<D> (\<lbrakk>v :: 'a vdme\<rbrakk>\<^sub>vb) \<Longrightarrow> \<lbrakk>LiftD v\<rbrakk>\<epsilon>b = \<bottom>\<^bsub>VTYPE('a)\<^esub>"
  by (simp add:EvalE_def LiftD.rep_eq Defined_option_def)

lemma EvalD_LitD [evale]:
  "\<lbrakk><x>\<rbrakk>\<^sub>vb = Some x"
  by (simp add:LitD_def)

lemma EvalD_BotDE [evale]:
  "\<lbrakk>\<bottom>\<^sub>v\<rbrakk>\<^sub>vb = None"
  by (simp add:BotDE_def)

lemma EvalD_ForallD [evale]:
  "\<lbrakk>ForallD f\<rbrakk>\<^sub>vb = \<lfloor>\<forall>x. \<lbrakk>f x\<rbrakk>\<^sub>v b = \<lfloor>True\<rfloor>\<rfloor>"
  by (simp add:ForallD_def)

lemma EvalD_UOpD [evale]:
  "\<D> (\<lbrakk>x\<rbrakk>\<^sub>vb) \<Longrightarrow> \<lbrakk>UOpD f x\<rbrakk>\<^sub>vb = f (the (\<lbrakk>x\<rbrakk>\<^sub>vb))"
  by (auto simp add:UOpD_def Defined_option_def)

lemma EvalD_BOpD [evale]:
  "\<lbrakk> \<D> (\<lbrakk>x\<rbrakk>\<^sub>vb); \<D> (\<lbrakk>y\<rbrakk>\<^sub>vb) \<rbrakk> \<Longrightarrow> \<lbrakk>BOpD f x y\<rbrakk>\<^sub>vb = f (the (\<lbrakk>x\<rbrakk>\<^sub>vb), the (\<lbrakk>y\<rbrakk>\<^sub>vb))"
  by (auto simp add:BOpD_def Defined_option_def)

lemma EvalD_CoerceD [evale]:
  "\<lbrakk> \<D> (\<lbrakk>x\<rbrakk>\<^sub>v b); the (\<lbrakk>x\<rbrakk>\<^sub>v b) \<in> t \<rbrakk> \<Longrightarrow> \<lbrakk>CoerceD x t\<rbrakk>\<^sub>vb = \<lbrakk>x\<rbrakk>\<^sub>vb"
  by (simp add:CoerceD_def)

lemma upfun_apply [simp]:
  "upfun f x = Some (f x)"
  by (simp add:upfun_def)

lemma bpfun_apply [simp]:
  "bpfun f x = Some (f (fst x) (snd x))"
  apply (case_tac x)
  apply (auto simp add:bpfun_def)
done

end