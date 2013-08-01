(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_expr.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM expressions *}

theory utp_vdm_expr
imports 
  utp_vdm_sorts 
  "../../theories/utp_definedness"
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

defs (overloaded)
  InjU_vdm [simp]:  "InjU (x::'a::vbasic option) \<equiv> InjVB x"
  ProjU_vdm [simp]: "ProjU (x::vdmv) \<equiv> ProjVB x"
  TypeU_vdm [simp]: "TypeU (x::('a::vbasic option) itself) \<equiv> embTYPE (VTYPE('a))"

lemma TypeUSound_vdm [typing]: "TYPEUSOUND('a::vbasic option, vdmv)"
  by (force simp add: type_rel_vdmt typing defined)

type_synonym 'a vdme = "('a option, vdmv) WF_PEXPRESSION"

translations
  (type) "'a vdme" <= (type) "('a option, vdmv) WF_PEXPRESSION"

definition BotDE :: "'a vdme" ("\<bottom>\<^sub>v") where
"BotDE = LitPE None"

declare BotDE_def [eval,evale,evalp]

abbreviation LitD :: "'a \<Rightarrow> 'a vdme" where
"LitD x \<equiv> LitPE (Some x)"

abbreviation "TrueDE  \<equiv> LitD True"
abbreviation "FalseDE \<equiv> LitD False"

abbreviation MkVarD :: "string \<Rightarrow> 'a set \<Rightarrow> ('a option, vdmv) PVAR" where
"MkVarD n t \<equiv> MkPlainP n False TYPE('a option) TYPE(vdmv)"

abbreviation MkChanD :: "string \<Rightarrow> 'a set \<Rightarrow> ('a option) CHANNEL" where
"MkChanD n xs \<equiv> MkCHAN (bName n) TYPE('a option)"

abbreviation UnitD :: "unit vdme" where
"UnitD \<equiv> LitD ()"

definition Op1D :: "('a::vbasic \<rightharpoonup> 'b::vbasic) \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme" where
"Op1D f v = Op1PE (\<lambda> x. x >>= f) v"

(* declare Op1D_def [eval, evale, evalp] *)

text {* Build a unary partial function from a normal binary HOL function *}

definition upfun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b option)" where
"upfun f = (\<lambda> v. Some (f v))"

abbreviation "Op1D' f \<equiv> Op1D (upfun f)"

definition Op2D :: "('a::vbasic * 'b::vbasic \<rightharpoonup> 'c::vbasic) 
                   \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme \<Rightarrow> 'c vdme" where
"Op2D f u v = Op2PE (\<lambda> v1 v2. do { x <- v1; y <- v2; f (x, y) }) u v"

(* declare Op2D_def [eval, evale, evalp] *)

text {* Build a binary partial function from a normal binary HOL function *}

definition bpfun :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a * 'b \<Rightarrow> 'c option)" where
"bpfun f \<equiv> (\<lambda> (v1, v2). Some (f v1 v2))"

abbreviation "Op2D' f \<equiv> Op2D (bpfun f)"

definition SingleD :: "'a vdme \<Rightarrow> ('a*unit) vdme" where
"SingleD x = Op1D' (\<lambda> x. (x, ())) x"

declare SingleD_def [eval,evale,evalp]

definition ListD :: "'a::vbasic vdme list \<Rightarrow> 'a list vdme" where
"ListD xs = MkPExpr (\<lambda> b. mapM (\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>* b) xs)"

definition FSetD :: "'a::vbasic vdme fset \<Rightarrow> 'a fset vdme" where
"FSetD xs = MkPExpr (\<lambda> b. fset_option ((\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>* b) `\<^sub>f xs))"

definition ForallD :: "'a set \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> bool vdme" where
"ForallD xs f = MkPExpr (\<lambda> b. (Some (\<forall> x \<in> xs. \<lbrakk>f x\<rbrakk>\<^sub>* b = Some True)))"

definition ExistsD :: "'a set \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> bool vdme" where
"ExistsD xs f = MkPExpr (\<lambda> b. (Some (\<exists> x \<in> xs. \<lbrakk>f x\<rbrakk>\<^sub>* b = Some True)))"

abbreviation DefinedD :: "'a vdme \<Rightarrow> bool vdme" where
"DefinedD v \<equiv> LitD (\<D> v)"

definition HasTypeD :: "'a vdme \<Rightarrow> 'a set \<Rightarrow> bool vdme" where
"HasTypeD e t \<equiv> MkPExpr (\<lambda> b. if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t)
                              then Some True 
                              else Some False)"

definition CoerceD :: "'a vdme \<Rightarrow> 'a set \<Rightarrow> 'a vdme" where
"CoerceD e t \<equiv> MkPExpr (\<lambda> b. if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t)
                             then \<lbrakk>e\<rbrakk>\<^sub>* b 
                             else None)"

definition CollectD :: "'a::vbasic vdme \<Rightarrow> bool vdme \<Rightarrow> 'a set" where
"CollectD v p = {the (\<lbrakk>v\<rbrakk>\<^sub>*b) | b. \<D> (\<lbrakk>v\<rbrakk>\<^sub>*b) \<and> \<lbrakk>p\<rbrakk>\<^sub>*b = Some True}"

declare CollectD_def [eval,evale,evalp]

definition ParallelD :: 
  "vdmv WF_PREDICATE \<Rightarrow> 
   (vdmv EVENT fset option, vdmv) WF_PEXPRESSION \<Rightarrow> 
   vdmv WF_PREDICATE \<Rightarrow> 
   vdmv WF_PREDICATE" where
"ParallelD p vs q = ParallelCSP p (Op1PE (Abs_UFSET \<circ> the) vs) q"

subsection {* Extend the UTP parser for VDM expressions *}

abbreviation "vexpr_equal     \<equiv> Op2D' (op =)"
abbreviation "vexpr_nequal    \<equiv> Op2D' (op \<noteq>)"
abbreviation "vexpr_prod      \<equiv> Op2D' (\<lambda> x y. (x,y))"
abbreviation "vexpr_nil       \<equiv> LitD []"
abbreviation "vexpr_cons      \<equiv> Op2D' list.Cons"
definition "vexpr_empty     \<equiv> LitD \<lbrace>\<rbrace>"
definition "vexpr_insert    \<equiv> Op2D' finsert"

declare vexpr_empty_def [eval,evalp]
declare vexpr_insert_def [eval,evalp]

nonterminal vty and vprod

subsection {* Product Projections *}

abbreviation "vproj1  \<equiv> fst"
abbreviation "vproj2  \<equiv> fst \<circ> snd"
abbreviation "vproj3  \<equiv> fst \<circ> snd \<circ> snd"
abbreviation "vproj4  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj5  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj6  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj7  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj8  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj9  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj10 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj11 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj12 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj13 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd 
                       \<circ> snd"
abbreviation "vproj14 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd 
                       \<circ> snd \<circ> snd"
abbreviation "vproj15 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd 
                       \<circ> snd \<circ> snd \<circ> snd"
abbreviation "vproj16 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd 
                       \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

notation vproj1  ("#1")
notation vproj2  ("#2")
notation vproj3  ("#3")
notation vproj4  ("#4")
notation vproj5  ("#5")
notation vproj6  ("#6")
notation vproj7  ("#7")
notation vproj8  ("#8")
notation vproj9  ("#9")
notation vproj10 ("#10")
notation vproj11 ("#11")
notation vproj12 ("#12")
notation vproj13 ("#13")
notation vproj14 ("#14")
notation vproj15 ("#15")
notation vproj16 ("#16")

(* These seemingly vacuous definitions are there to help the pretty printer *)

definition "NumD (x :: real) = LitD x"
declare NumD_def [simp]

definition "ApplyD f  = Op1D' f"
declare ApplyD_def [simp]

definition "SelectD f = Op1D' f"
declare SelectD_def [simp]

definition VExprD :: 
  "'a vdme \<Rightarrow> 'a vdme" where
"VExprD = id"

text {* We remove some of the generic syntax in favour of our own *}

no_syntax
  "_pexpr_equal"       :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "=" 50)
  "_pexpr_true"        :: "pexpr" ("true")
  "_pexpr_false"       :: "pexpr" ("false")
(*  "_pexpr_brack"       :: "pexpr \<Rightarrow> pexpr" ("'(_')") *)
  "_pexpr_plus"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "+" 65)
  "_pexpr_minus"       :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "-" 65)
  "_pexpr_less"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "<" 25)
  "_pexpr_less_eq"     :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<le>" 25)
  "_pexpr_int"         :: "int \<Rightarrow> pexpr" ("<_>")
  "_pexpr_fset_empty"  :: "pexpr" ("{}")
  "_pexpr_fset"        :: "pexprs \<Rightarrow> pexpr" ("{_}")
  "_pexpr_list"        :: "pexprs \<Rightarrow> pexpr" ("\<langle>_\<rangle>")
  "_pexpr_list_nil"    :: "pexpr" ("\<langle>\<rangle>")
  "_pexpr_expr_var"    :: "idt \<Rightarrow> pexpr" ("(_)")
  "_pexpr_pred_var"     :: "idt \<Rightarrow> pexpr" ("@(_)")
  "_uexpr_quote"       :: "uexpr \<Rightarrow> 'a WF_EXPRESSION" ("(1^_^)")
  "_upred_pexpr"       :: "pexpr \<Rightarrow> upred" ("\<lparr>_\<rparr>")

syntax
  "_vexpr_expr_var" :: "idt \<Rightarrow> pexpr" ("@_" [999] 999)
  "_vexpr_val_var"  :: "idt \<Rightarrow> pexpr" ("&_" [999] 999)
  "_vexpr_equal"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "=" 50)
  "_vexpr_nequal"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "<>" 50)
  "_vexpr_unit"     :: "pexpr" ("'(')")
  "_vexpr_true"     :: "pexpr" ("true")
  "_vexpr_false"    :: "pexpr" ("false")
  "_vexpr_num"      :: "real \<Rightarrow> pexpr" ("_")
  "_vexpr_bot"      :: "pexpr" ("undefined")
  "_vexpr_lit"      :: "'a::vbasic \<Rightarrow> pexpr" ("(1^_^)")
  "_vexpr_forall"   :: "pttrn \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3forall _ : _ &/ _)" [0, 0, 10] 10)
  "_vexpr_exists"   :: "pttrn \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3exists _ : _ &/ _)" [0, 0, 10] 10)
  "_vexpr_coerce"   :: "pexpr \<Rightarrow> vty \<Rightarrow> pexpr" (infix ":" 50)
  "_vexpr_hasType"  :: "pexpr \<Rightarrow> vty \<Rightarrow> pexpr" (infix "hasType" 50)
  "_vexpr_apply"    :: "('a \<Rightarrow> 'b) \<Rightarrow> pexprs \<Rightarrow> pexpr"    ("_'(_')")
  "_vexpr_prod"     :: "pexprs \<Rightarrow> vprod" ("_")
  "_vexpr_select"   :: "pexpr \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> pexpr" ("_._")
  "_vexpr_nil"      :: "pexpr" ("[]")
  "_vexpr_list"     :: "pexprs => pexpr"    ("[(_)]")
  "_vexpr_empty"    :: "pexpr" ("{}")
  "_vexpr_fset"     :: "pexprs => pexpr"    ("{(_)}")
  "_upred_parcml"   :: "upred \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" (infixl "[|_|]" 50)

(*
  "_vexpr_vexpr"  :: "'a vdme \<Rightarrow> pexpr" ("_")

  "_vexpr_vexpr x" == "CONST vexpr_vexpr x"
*)

syntax (xsymbols)
  "_vexpr_bot"     :: "pexpr" ("\<bottom>")

translations
  "_vexpr_expr_var x"          => "x"
  "_vexpr_val_var x"           == "CONST LitPE x"
  "_vexpr_equal"               == "CONST vexpr_equal"
  "_vexpr_nequal"              == "CONST vexpr_nequal"
  "_vexpr_unit"                == "CONST UnitD"
  "_vexpr_true"                == "CONST TrueDE"
  "_vexpr_false"               == "CONST FalseDE"
  "_vexpr_num n"               == "CONST NumD n"
  "_vexpr_bot"                 == "CONST BotDE"
  "_vexpr_lit v"               == "CONST LitD v"
  "_vexpr_forall x xs e"       == "CONST ForallD xs (\<lambda>x. e)"
  "_vexpr_exists x xs e"       == "CONST ExistsD xs (\<lambda>x. e)"
  "_vexpr_coerce e t"          == "CONST CoerceD e t"
  "_vexpr_hasType e t"         == "CONST HasTypeD e t"
  "_vexpr_apply f x"           == "CONST ApplyD f (_vexpr_prod x)"
  "_vexpr_prod (_pexprs x xs)" == "CONST vexpr_prod x (_vexpr_prod xs)"
  "_vexpr_prod x"              == "CONST SingleD x"
  "_vexpr_select e f"          == "CONST SelectD f e"
  "_vexpr_nil"                 == "CONST vexpr_nil"
  "_vexpr_list (_pexprs x xs)" == "CONST vexpr_cons x (_vexpr_list xs)"
  "_vexpr_list x"              == "CONST vexpr_cons x CONST vexpr_nil"
  "_vexpr_empty"               == "CONST vexpr_empty"
  "_vexpr_fset (_pexprs x xs)" == "CONST vexpr_insert x (_vexpr_fset xs)"
  "_vexpr_fset x"              == "CONST vexpr_insert x CONST vexpr_empty"
  "_upred_parcml p vs q"       == "CONST ParallelD p vs q"

abbreviation mk_prod :: "'a \<Rightarrow> 'a" where
"mk_prod \<equiv> id"

term "Op1D' id (vexpr_prod TrueDE (SingleD FalseDE))"

term "|mk_prod(true, false, 1).#1|"
term "|mk_prod($x,2,5)|"


term "LitD (1 :: real)"

term "|x = 1.1|"
term "|mk_prod(1,2,3,4).#3|"

subsection {* Tautologies *}

definition VExprTrueT :: "bool vdme \<Rightarrow> vdmv WF_PREDICATE" where
"VExprTrueT e = `@e = true`"

definition VExprDefinedT :: "bool vdme \<Rightarrow> vdmv WF_PREDICATE" where
"VExprDefinedT e = `\<not> (@e = \<bottom>)`"

abbreviation VTautT :: "bool vdme \<Rightarrow> vdmv WF_PREDICATE" where
"VTautT e \<equiv> TVL (VExprTrueT e, VExprDefinedT e)"

syntax
  "_upred_vexpr"       :: "pexpr \<Rightarrow> upred" ("\<lparr>_\<rparr>")

translations
  "_upred_vexpr e" == "CONST VTautT e"

subsection {* @{term UNREST_PEXPR} theorems *}

lemma UNREST_PEXPR_BotDE [unrest]: 
  "UNREST_PEXPR vs \<bottom>\<^sub>v"
  by (simp add:UNREST_PEXPR_def evalp)


lemma UNREST_PEXPR_ForallD [unrest]:
  "\<forall> e. UNREST_PEXPR vs (f e) \<Longrightarrow> UNREST_PEXPR vs (ForallD xs f)"
  by (simp add:UNREST_PEXPR_def ForallD_def)

lemma UNREST_PEXPR_ExistsD [unrest]:
  "\<forall> e. UNREST_PEXPR vs (f e) \<Longrightarrow> UNREST_PEXPR vs (ExistsD xs f)"
  by (simp add:UNREST_PEXPR_def ExistsD_def)

lemma UNREST_PEXPR_Op1D [unrest]: 
  "UNREST_PEXPR vs v \<Longrightarrow> UNREST_PEXPR vs (Op1D f v)"
  by (simp add:UNREST_PEXPR_def Op1D_def evalp)

lemma UNREST_PEXPR_Op2D [unrest]: 
  "\<lbrakk> UNREST_PEXPR vs v1; UNREST_PEXPR vs v2 \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs (Op2D f v1 v2)"
  by (simp add:UNREST_PEXPR_def Op2D_def evalp EvalPE_ProdPE)

lemma UNREST_PEXPR_ListD [unrest]: 
  "\<lbrakk> \<forall> x \<in> set xs. UNREST_PEXPR vs x \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs (ListD xs)"
  apply (induct xs)
  apply (auto simp add:UNREST_PEXPR_def ListD_def)
done

lemma UNREST_PEXPR_FSetE [unrest]: 
  "\<lbrakk> \<forall> x \<in>\<^sub>f xs. UNREST_PEXPR vs x \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs (FSetD xs)"
  apply (simp add:UNREST_PEXPR_def FSetD_def)
  apply (clarify)
  apply (simp add:fimage.rep_eq fset_option_def)
  apply (metis (lifting, no_types) Rep_fset_inject fimage.rep_eq image_cong)
done

lemma UNREST_PEXPR_CoerceD [unrest]:
  "\<lbrakk> UNREST_PEXPR vs x \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs (CoerceD x t)"
  by (auto simp add:UNREST_PEXPR_def CoerceD_def)

subsection {* Definedness theorems *}

lemma LitD_defined [defined]:
  "\<D> (LitD v)"
  by (simp add:Defined_option_def Defined_WF_PEXPRESSION_def evalp)

lemma BotDE_not_defined [defined]:
  "\<D> \<bottom>\<^sub>v = False"
  by (simp add:BotDE_def Defined_WF_PEXPRESSION_def evalp)

lemma Defined_option_elim [elim]:
  "\<lbrakk> \<D> x; \<And> y. \<lbrakk> x = Some y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add:Defined_option_def)
  apply (metis not_None_eq option.simps(6) option.simps(7))
done

lemma Op1D_EvalD_defined [defined]: 
  "\<lbrakk> \<D> v; \<forall> b. the (\<lbrakk>v\<rbrakk>\<^sub>* b) \<in> dom f \<rbrakk> \<Longrightarrow> \<D> (Op1D f v)"
  apply (auto simp add:Op1D_def Defined_WF_PEXPRESSION_def evalp)
  apply (drule_tac x="b" in spec)+
  apply (erule Defined_option_elim)
  apply (auto simp add:dom_def)
done

lemma Op2D_EvalD_defined [defined]: 
  "\<lbrakk> \<D> v1; \<D> v2; \<forall> b. (the (\<lbrakk>v1\<rbrakk>\<^sub>* b), the (\<lbrakk>v2\<rbrakk>\<^sub>* b)) \<in> dom f \<rbrakk> \<Longrightarrow> \<D> (Op2D f v1 v2)"
  apply (auto simp add:Op2D_def Defined_WF_PEXPRESSION_def evalp EvalPE_ProdPE)
  apply (drule_tac x="b" in spec)+
  apply (erule Defined_option_elim)
  apply (erule Defined_option_elim)
  apply (auto simp add:dom_def)
done

lemma upfun_dom [defined]: 
  "dom (upfun f) = UNIV"
  by (auto simp add:upfun_def)

lemma bpfun_dom [defined]: 
  "dom (bpfun f) = UNIV"
  by (auto simp add:bpfun_def)

lemma EvalD_defined [defined]: "\<D> v \<Longrightarrow> \<D> (\<lbrakk>v\<rbrakk>\<^sub>*b)"
  by (simp add:Defined_option_def Defined_WF_PEXPRESSION_def)

lemma Some_defined [defined]: "\<D> (Some x)"
  by (simp add:Defined_option_def)

lemma None_not_defined [defined]: "\<not> \<D> None"
  by (simp add:Defined_option_def)

subsection {* Evaluation theorems *}

lemma EvalD_LitD [eval,evalp,evale]:
  "\<lbrakk>LitD x\<rbrakk>\<^sub>*b = Some x"
  by (simp add:evalp)

lemma EvalD_BotDE [eval,evalp,evale]:
  "\<lbrakk>\<bottom>\<^sub>v\<rbrakk>\<^sub>*b = None"
  by (simp add:BotDE_def evalp)

lemma EvalD_ForallD [eval,evalp,evale]:
  "\<lbrakk>ForallD xs f\<rbrakk>\<^sub>*b = \<lfloor>\<forall>x\<in>xs. \<lbrakk>f x\<rbrakk>\<^sub>*b = \<lfloor>True\<rfloor>\<rfloor>"
  by (simp add:ForallD_def)

lemma EvalD_Op1D [eval,evalp,evale]:
  "\<D> (\<lbrakk>x\<rbrakk>\<^sub>*b) \<Longrightarrow> \<lbrakk>Op1D f x\<rbrakk>\<^sub>*b = f (the (\<lbrakk>x\<rbrakk>\<^sub>*b))"
  by (auto simp add:Op1D_def evalp)

lemma EvalD_Op2D [eval,evalp,evale]:
  "\<lbrakk> \<D> (\<lbrakk>x\<rbrakk>\<^sub>*b); \<D> (\<lbrakk>y\<rbrakk>\<^sub>*b) \<rbrakk> \<Longrightarrow> \<lbrakk>Op2D f x y\<rbrakk>\<^sub>*b = f (the (\<lbrakk>x\<rbrakk>\<^sub>*b), the (\<lbrakk>y\<rbrakk>\<^sub>*b))"
  by (force simp add:Op2D_def evalp EvalPE_ProdPE)

lemma EvalD_CoerceD [eval,evalp,evale]:
  "\<lbrakk> \<D> (\<lbrakk>x\<rbrakk>\<^sub>*b); the (\<lbrakk>x\<rbrakk>\<^sub>*b) \<in> t \<rbrakk> \<Longrightarrow> \<lbrakk>CoerceD x t\<rbrakk>\<^sub>*b = \<lbrakk>x\<rbrakk>\<^sub>*b"
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