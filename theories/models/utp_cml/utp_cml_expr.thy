(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_expr.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML expressions *}

theory utp_cml_expr
imports 
  utp_cml_sorts 
  "../../theories/utp_definedness"
begin

lemma EqualP_refine [refine]:
  "P[v/\<^sub>px] \<Longrightarrow> P \<sqsubseteq> $\<^sub>ex ==\<^sub>p v"
  by (metis ImpliesP_eq_subst RefP_def Tautology_def TrueP_eq_ClosureP less_eq_WF_PREDICATE_def utp_pred_simps(14) utp_pred_simps(21))

text {* Getting an accurate representation of CML expressions is hard,
in as much as Isabelle's type-system limits our ability to do proper
type-inference. Although we can infer the type of an expression, the
types of variables are immediately erased when placed in a
context. This means that if the context doesn't fully qualify the type
of a variable, there is no way to quantify it other than by coercing
it in place. It is therefore impossible to create quantifiers which *}

default_sort vbasic

subsection {* CML expresssion type *}

defs (overloaded)
  InjU_cml [simp]:  "InjU (x::'a::vbasic option) \<equiv> InjVB x"
  ProjU_cml [simp]: "ProjU (x::cmlv) \<equiv> ProjVB x"
  TypeU_cml [simp]: "TypeU (x::('a::vbasic option) itself) \<equiv> embTYPE (VTYPE('a))"

lemma TypeUSound_cml [typing]: "TYPEUSOUND('a::vbasic option, cmlv)"
  by (force simp add: type_rel_cmlt typing defined)

(* CML expressions and CML predicates *)

type_synonym 'a cmle        = "('a option, cmlv) WF_PEXPRESSION"
type_synonym cmlp           = "cmlv WF_PREDICATE" 
type_synonym 'a cmlvar      = "('a option, cmlv) PVAR"
type_synonym ('a, 'b) cmlop = "('a option, 'b option, cmlv) WF_POPERATION"

translations
  (type) "'a cmle" <= (type) "('a option, cmlv) WF_PEXPRESSION"
  (type) "cmlp" <= (type) "cmlv WF_PREDICATE"
  (type) "'a cmlvar" <= (type) "('a option, cmlv) PVAR"
  (type) "('a, 'b) cmlop" <= (type) "'a cmle \<Rightarrow> 'b cmlvar \<times> bool \<Rightarrow> cmlp"

definition BotDE :: "'a cmle" ("\<bottom>\<^sub>v") where
"BotDE = LitPE None"

declare BotDE_def [eval,evale,evalp]

abbreviation LitD :: "'a \<Rightarrow> 'a cmle" where
"LitD x \<equiv> LitPE (Some x)"

abbreviation "TrueDE  \<equiv> LitD True"
abbreviation "FalseDE \<equiv> LitD False"

definition MkVarD :: "string \<Rightarrow> 'a set \<Rightarrow> 'a cmlvar" where
"MkVarD n t \<equiv> MkPlainP n False TYPE('a option) TYPE(cmlv)"

lemma pvname_MkVarD [simp]:
  "pvname (MkVarD s t) = bName s"
  by (simp add:MkVarD_def)

lemma pvaux_MkVarD [simp]:
  "pvaux (MkVarD s t) = False"
  by (simp add:MkVarD_def)

abbreviation UnitD :: "unit cmle" where
"UnitD \<equiv> LitD ()"

definition Op1D :: "('a::vbasic \<rightharpoonup> 'b::vbasic) \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle" where
"Op1D f v = Op1PE (\<lambda> x. x >>= f) v"

(* declare Op1D_def [eval, evale, evalp] *)

text {* Build a unary partial function from a normal binary HOL function *}

definition upfun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b option)" where
"upfun f = (\<lambda> v. Some (f v))"

abbreviation "Op1D' f \<equiv> Op1D (upfun f)"

definition Op2D :: "('a::vbasic * 'b::vbasic \<rightharpoonup> 'c::vbasic) 
                   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle" where
"Op2D f u v = Op2PE (\<lambda> v1 v2. do { x <- v1; y <- v2; f (x, y) }) u v"

(* declare Op2D_def [eval, evale, evalp] *)

text {* Build a binary partial function from a normal binary HOL function *}

definition bpfun :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a * 'b \<Rightarrow> 'c option)" where
"bpfun f \<equiv> (\<lambda> (v1, v2). Some (f v1 v2))"

abbreviation "Op2D' f \<equiv> Op2D (bpfun f)"

definition Op3D :: "('a::vbasic * 'b::vbasic * 'c::vbasic \<rightharpoonup> 'd::vbasic) 
                   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle" where
"Op3D f u v w = Op3PE (\<lambda> v1 v2 v3. do { x <- v1; y <- v2; z <- v3; f (x, y, z) }) u v w"

definition tpfun :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a * 'b * 'c \<Rightarrow> 'd option)" where
"tpfun f \<equiv> (\<lambda> (v1, v2, v3). Some (f v1 v2 v3))"

abbreviation "Op3D' f \<equiv> Op3D (tpfun f)"

definition SingleD :: "'a cmle \<Rightarrow> ('a*unit) cmle" where
"SingleD x = Op1D' (\<lambda> x. (x, ())) x"

declare SingleD_def [eval,evale,evalp]

abbreviation TokenD :: "'a::vbasic cmle \<Rightarrow> token cmle" where
"TokenD v \<equiv> Op1D' (Abs_token \<circ> Inject) v"

definition ListD :: "'a::vbasic cmle list \<Rightarrow> 'a list cmle" where
"ListD xs = MkPExpr (\<lambda> b. mapM (\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>* b) xs)"

definition FSetD :: "'a::vbasic cmle fset \<Rightarrow> 'a fset cmle" where
"FSetD xs = MkPExpr (\<lambda> b. fset_option ((\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>* b) `\<^sub>f xs))"

definition ForallD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"ForallD xs f = MkPExpr (\<lambda> b. (Some (\<forall> x \<in> xs. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)))"

definition ExistsD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"ExistsD xs f = MkPExpr (\<lambda> b. (Some (\<exists> x \<in> xs. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)))"

definition Exists1D :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"Exists1D xs f = MkPExpr (\<lambda> b. (Some (\<exists>! x \<in> xs. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)))"

definition IotaD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> 'a cmle" where 
"IotaD xs f = MkPExpr (\<lambda> b. (if (\<exists>! x \<in> xs. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)
                                then Some (THE x. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)
                                else None))"

definition EpsD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> 'a cmle" where 
"EpsD xs f = MkPExpr (\<lambda> b. (if (\<exists> x \<in> xs. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)
                                then Some (SOME x. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)
                                else None))"

definition FunD :: "'a set \<Rightarrow> ('a option \<Rightarrow> 'b cmle) \<Rightarrow> 'a \<Rightarrow> 'b option" where
"FunD t P = (\<lambda> x. \<lbrakk>P (Some x)\<rbrakk>\<^sub>*\<B>)"

declare FunD_def [evalp]

abbreviation DefinedD :: "'a cmle \<Rightarrow> bool cmle" where
"DefinedD v \<equiv> LitD (\<D> v)"

definition HasType :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> bool" (infix ":\<^sub>d" 50) where
"HasType e t = (\<forall> b. \<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<longrightarrow> the (\<lbrakk>e\<rbrakk>\<^sub>*b) \<in> t)"

definition HasTypeD :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> bool cmle" where
"HasTypeD e t \<equiv> MkPExpr (\<lambda> b. if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t)
                              then Some True 
                              else Some False)"

definition CoerceD :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> 'a cmle" where
"CoerceD e t \<equiv> MkPExpr (\<lambda> b. if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t)
                             then \<lbrakk>e\<rbrakk>\<^sub>* b 
                             else None)"

definition CollectD :: "'a::vbasic cmle \<Rightarrow> bool cmle \<Rightarrow> 'a set" where
"CollectD v p = {the (\<lbrakk>v\<rbrakk>\<^sub>*b) | b. \<D> (\<lbrakk>v\<rbrakk>\<^sub>*b) \<and> \<lbrakk>p\<rbrakk>\<^sub>*b = Some True}"

declare CollectD_def [eval,evale,evalp]

definition IfThenElseD :: "bool cmle \<Rightarrow> 'a::vbasic cmle \<Rightarrow> 'a cmle \<Rightarrow> 'a cmle" where
"IfThenElseD = Op3PE (\<lambda> b v1 v2. do { c <- b; if c then v1 else v2 })"

declare IfThenElseD_def [eval,evale,evalp]

subsection {* Extend the UTP parser for CML expressions *}

abbreviation "vexpr_equal     \<equiv> Op2D' (op =)"
abbreviation "vexpr_nequal    \<equiv> Op2D' (op \<noteq>)"
abbreviation "vexpr_prod      \<equiv> Op2D' (\<lambda> x y. (x,y))"
abbreviation "vexpr_nil       \<equiv> LitD []"
abbreviation "vexpr_cons      \<equiv> Op2D' list.Cons"
definition "vexpr_empty       \<equiv> LitD \<lbrace>\<rbrace>"
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

definition "ApplyD f  = Op1D f"

definition "SelectD f = Op1D' f"

definition VExprD :: 
  "'a cmle \<Rightarrow> 'a cmle" where
"VExprD = id"

text {* We remove some of the generic syntax in favour of our own *}

no_syntax
  "_pexpr_equal"       :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "=" 50)
  "_pexpr_true"        :: "pexpr" ("true")
  "_pexpr_false"       :: "pexpr" ("false")
  "_pexpr_plus"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "+" 65)
  "_pexpr_minus"       :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "-" 65)
  "_pexpr_less"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "<" 25)
  "_pexpr_less_eq"     :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<le>" 25)
  "_pexpr_int"         :: "int \<Rightarrow> pexpr" ("<_>")
  "_pexpr_set"        :: "pexprs \<Rightarrow> pexpr" ("{_}")
  "_pexpr_set_empty"  :: "pexpr" ("{}")
  "_pexpr_fset_empty"  :: "pexpr" ("{}")
  "_pexpr_fset"        :: "pexprs \<Rightarrow> pexpr" ("{_}")
  "_pexpr_list"        :: "pexprs \<Rightarrow> pexpr" ("\<langle>_\<rangle>")
  "_pexpr_list_nil"    :: "pexpr" ("\<langle>\<rangle>")
  "_pexpr_expr_var"    :: "idt \<Rightarrow> pexpr" ("(_)")
  "_pexpr_pred_var"     :: "idt \<Rightarrow> pexpr" ("@(_)")
  "_uexpr_quote"       :: "uexpr \<Rightarrow> 'a WF_EXPRESSION" ("(1^_^)")
  "_upred_pexpr"       :: "pexpr \<Rightarrow> upred" ("\<lparr>_\<rparr>")
  "_uproc_pexpr"      :: "pexpr \<Rightarrow> uproc" ("\<lparr>_\<rparr>")
  "_upred_callpr"     :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> pexpr \<Rightarrow> upred" ("call _'[_']")

no_translations
  "_upred_callpr f v"       == "CONST CallRO f v"

abbreviation "vexpr_defined   \<equiv> (DefinedD :: 'a cmle \<Rightarrow> bool cmle)"

syntax
  "_vexpr_eval"     :: "pexpr \<Rightarrow> 'a" ("+|_|+")
  "_vexpr_defined"  :: "pexpr \<Rightarrow> pexpr" ("defn'(_')")
  "_vexpr_expr_var" :: "idt \<Rightarrow> pexpr" ("@_" [999] 999)
  "_vexpr_val_var"  :: "idt \<Rightarrow> pexpr" ("&_" [999] 999)
  "_vexpr_equal"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "=" 50)
  "_vexpr_nequal"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "<>" 50)
  "_vexpr_unit"     :: "pexpr" ("'(')")
  "_vexpr_true"     :: "pexpr" ("true")
  "_vexpr_false"    :: "pexpr" ("false")
  "_vexpr_token"    :: "pexpr \<Rightarrow> pexpr" ("mk'_token'(_')")
  "_vexpr_num"      :: "real \<Rightarrow> pexpr" ("_")
  "_vexpr_bot"      :: "pexpr" ("undefined")
  "_vexpr_lit"      :: "'a::vbasic option \<Rightarrow> pexpr" ("(1^_^)")
  "_vexpr_litd"     :: "'a::vbasic \<Rightarrow> pexpr" ("(1<<_>>)")
  "_vexpr_lambda"    :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3lambda _ @/ _)" [0, 10] 10)
  "_vexpr_lambda_ty" :: "idt \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3lambda _ : _ @/ _)" [0, 0, 10] 10)
  "_vexpr_forall"   :: "pttrn \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3forall _ : _ @/ _)" [0, 0, 10] 10)
  "_vexpr_exists"   :: "pttrn \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3exists _ : _ @/ _)" [0, 0, 10] 10)
  "_vexpr_exists1"  :: "pttrn \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3exists1 _ : _ @/ _)" [0, 0, 10] 10)
  "_vexpr_iota"     :: "pttrn \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3iota _ : _ @/ _)" [0, 0, 10] 10)
  "_vexpr_eps"      :: "pttrn \<Rightarrow> vty \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3eps _ : _ @/ _)" [0, 0, 10] 10)
  "_vexpr_coerce"   :: "pexpr \<Rightarrow> vty \<Rightarrow> pexpr" (infix ":" 50)
  "_vexpr_ifthen"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("if _ then _ else _")
  "_vexpr_hasType"  :: "pexpr \<Rightarrow> vty \<Rightarrow> pexpr" (infix "hasType" 50)
  "_vexpr_apply"    :: "('a \<Rightarrow> 'b) \<Rightarrow> pexprs \<Rightarrow> pexpr"    ("_'(_')" [998,0] 998)
  "_vexpr_vapply"   :: "'a \<Rightarrow> pexpr"    ("_'(')" [998] 998)
  "_vexpr_prod"     :: "pexprs \<Rightarrow> vprod" ("_")
  "_vexpr_select"   :: "pexpr \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> pexpr" ("_._")
  "_vexpr_nil"      :: "pexpr" ("[]")
  "_vexpr_list"     :: "pexprs => pexpr"    ("[(_)]")
  "_vexpr_empty"    :: "pexpr" ("{}")
  "_vexpr_fset"     :: "pexprs => pexpr"    ("{(_)}")

syntax (xsymbols)
  "_vexpr_bot"     :: "pexpr" ("\<bottom>")

translations
  "_vexpr_eval e"              == "\<lbrakk>e\<rbrakk>\<^sub>* \<B>"
  "_vexpr_defined x"           == "CONST vexpr_defined x"
  "_vexpr_expr_var x"          => "x"
  "_vexpr_val_var x"           == "CONST LitPE x"
  "_vexpr_equal"               == "CONST vexpr_equal"
  "_vexpr_nequal"              == "CONST vexpr_nequal"
  "_vexpr_unit"                == "CONST UnitD"
  "_vexpr_true"                == "CONST TrueDE"
  "_vexpr_false"               == "CONST FalseDE"
  "_vexpr_token x"             == "CONST TokenD x"
  "_vexpr_num n"               == "CONST NumD n"
  "_vexpr_bot"                 == "CONST BotDE"
  "_vexpr_lit v"               == "CONST LitPE v"
  "_vexpr_litd v"              == "CONST LitD v"
  "_vexpr_lambda x e"          == "CONST FunD CONST UNIV (\<lambda> x. e)"
  "_vexpr_lambda_ty x t e"     == "CONST FunD t (\<lambda> x. e)"
  "_vexpr_forall x xs e"       == "CONST ForallD xs (\<lambda>x. e)"
  "_vexpr_exists x xs e"       == "CONST ExistsD xs (\<lambda>x. e)"
  "_vexpr_exists1 x xs e"      == "CONST Exists1D xs (\<lambda>x. e)"
  "_vexpr_iota x xs e"         == "CONST IotaD xs (\<lambda>x. e)"
  "_vexpr_eps x xs e"          == "CONST EpsD xs (\<lambda>x. e)"
  "_vexpr_coerce e t"          == "CONST CoerceD e t"
  "_vexpr_ifthen b x y"        == "CONST IfThenElseD b x y"
  "_vexpr_hasType e t"         == "CONST HasTypeD e t"
  "_vexpr_apply f x"           == "CONST ApplyD f (_vexpr_prod x)"
  "_vexpr_vapply f"            => "CONST ApplyD f (CONST LitD ())"
  "_vexpr_prod (_pexprs x xs)" == "CONST vexpr_prod x (_vexpr_prod xs)"
  "_vexpr_prod x"              == "CONST SingleD x"
  "_vexpr_select e f"          == "CONST SelectD f e"
  "_vexpr_nil"                 == "CONST vexpr_nil"
  "_vexpr_list (_pexprs x xs)" == "CONST vexpr_cons x (_vexpr_list xs)"
  "_vexpr_list x"              == "CONST vexpr_cons x CONST vexpr_nil"
  "_vexpr_empty"               == "CONST vexpr_empty"
  "_vexpr_fset (_pexprs x xs)" == "CONST vexpr_insert x (_vexpr_fset xs)"
  "_vexpr_fset x"              == "CONST vexpr_insert x CONST vexpr_empty"

abbreviation mk_prod :: "'a \<Rightarrow> 'a option" where
"mk_prod \<equiv> Some"

term "Op1D' id (vexpr_prod TrueDE (SingleD FalseDE))"

term "|mk_prod(true, false, 1)|"

term "|mk_prod(true, false, 1).#1|"
term "|mk_prod($x,2,5)|"

term "LitD (1 :: real)"

term "|1.1|"
term "|mk_prod(1,2,3,4).#3|"

subsection {* Tautologies *}

definition VExprTrueT :: "bool cmle \<Rightarrow> cmlp" where
"VExprTrueT e = `@e = true`"

definition VExprDefinedT :: "bool cmle \<Rightarrow> cmlp" where
"VExprDefinedT e = `\<not> (@e = \<bottom>)`"

abbreviation VTautT :: "bool cmle \<Rightarrow> cmlp" where
"VTautT e \<equiv> TVL (VExprTrueT e, VExprDefinedT e)"

definition VTautHideT :: "bool cmle \<Rightarrow> cmlp" where
"VTautHideT e \<equiv> (\<exists>\<^sub>p {def\<down>}. VTautT e \<Leftrightarrow>\<^sub>p TrueT)"

definition "VTautHideO e = (\<lambda> r. VTautHideT e)"

declare [[coercion VTautHideT]]

declare VExprTrueT_def [eval, evale, evalp]
declare VExprDefinedT_def [eval, evale, evalp]
declare VTautHideT_def [eval, evale, evalp]
declare VTautHideO_def [eval, evalpp, evalr, evalpr, uop_defs]

syntax
  "_upred_vexpr"       :: "pexpr \<Rightarrow> upred" ("\<lparr>_\<rparr>")
  "_uproc_vexpr"       :: "pexpr \<Rightarrow> uproc" ("\<lparr>_\<rparr>")
  "_upred_vcallpr"     :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> pexprs \<Rightarrow> upred" ("call _'[_']")
  "_upred_vcallpr_nil" :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> upred" ("call _'[']")

translations
  "_upred_vexpr e" == "CONST VTautHideT e"
  "_uproc_vexpr e" == "CONST VTautHideO e"
  "_upred_vcallpr f ps" == "CONST CallRO f (_vexpr_prod ps)"
  "_upred_vcallpr_nil f" == "CONST CallRO f CONST UnitD"

subsection {* Evaluation theorems *}

lemma EvalE_cmle [evale, evalp, eval]:
  fixes e :: "'a::vbasic cmle"
  shows "\<lbrakk>e\<down>\<rbrakk>\<^sub>eb = InjVB (\<lbrakk>e\<rbrakk>\<^sub>*b)"
  by (simp add:evale typing)

lemma EvalD_LitD [eval,evalp,evale]:
  "\<lbrakk>LitD x\<rbrakk>\<^sub>*b = Some x"
  by (simp add:evalp)

lemma EvalD_NumD [eval,evalp,evale]:
  "\<lbrakk>NumD x\<rbrakk>\<^sub>*b = Some x"
  by (simp add:NumD_def evalp)

lemma EvalD_BotDE [eval,evalp,evale]:
  "\<lbrakk>\<bottom>\<^sub>v\<rbrakk>\<^sub>*b = None"
  by (simp add:BotDE_def evalp)

lemma EvalD_ForallD [eval,evalp,evale]:
  "\<lbrakk>ForallD xs f\<rbrakk>\<^sub>*b = \<lfloor>\<forall>x\<in>xs. \<lbrakk>f (Some x)\<rbrakk>\<^sub>*b = \<lfloor>True\<rfloor>\<rfloor>"
  by (simp add:ForallD_def)

lemma EvalD_Op1D [eval,evalp,evale]:
  "\<lbrakk>Op1D f x\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>*b >>= f)"
  by (simp add:Op1D_def evalp)

lemma EvalD_ApplyD [eval,evalp,evale]:
  "\<lbrakk>ApplyD f x\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>*b >>= f)"
  by (simp add:ApplyD_def evalp)

lemma EvalD_SelectD [eval,evalp,evale]:
  "\<lbrakk>SelectD f x\<rbrakk>\<^sub>*b = \<lbrakk>x\<rbrakk>\<^sub>* b >>= upfun f"
  by (simp add:SelectD_def evalp)

lemma EvalD_Op2D [eval,evalp,evale]:
  "\<lbrakk>Op2D f x y\<rbrakk>\<^sub>*b = do { v1 <- \<lbrakk>x\<rbrakk>\<^sub>*b; v2 <- \<lbrakk>y\<rbrakk>\<^sub>*b; f (v1, v2) }"
  by (simp add:Op2D_def evalp)

lemma EvalD_Op3D [eval,evalp,evale]:
  "\<lbrakk>Op3D f x y z\<rbrakk>\<^sub>*b = do { v1 <- \<lbrakk>x\<rbrakk>\<^sub>*b; v2 <- \<lbrakk>y\<rbrakk>\<^sub>*b; v3 <- \<lbrakk>z\<rbrakk>\<^sub>*b; f (v1, v2, v3) }"
  by (simp add:Op3D_def evalp)

lemma EvalD_HasTypeD [eval,evalp,evale]:
  "\<lbrakk>HasTypeD e t\<rbrakk>\<^sub>*b = (if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t) then \<lfloor>True\<rfloor> else \<lfloor>False\<rfloor>)"
  by (simp add:HasTypeD_def)

lemma EvalD_CoerceD [eval,evalp,evale]:
  "\<lbrakk> \<D> (\<lbrakk>x\<rbrakk>\<^sub>*b); the (\<lbrakk>x\<rbrakk>\<^sub>*b) \<in> t \<rbrakk> \<Longrightarrow> \<lbrakk>CoerceD x t\<rbrakk>\<^sub>*b = \<lbrakk>x\<rbrakk>\<^sub>*b"
  by (simp add:CoerceD_def)

declare IotaD_def [evalp]
declare EpsD_def [evalp]

lemma upfun_apply [simp]:
  "upfun f x = Some (f x)"
  by (simp add:upfun_def)

lemma bpfun_apply [simp]:
  "bpfun f x = Some (f (fst x) (snd x))"
  apply (case_tac x)
  apply (auto simp add:bpfun_def)
done

lemma tpfun_apply [simp]:
  "tpfun f x = Some (f (fst x) (fst (snd x)) (snd (snd x)))"
  apply (case_tac x)
  apply (auto simp add:tpfun_def)
done

declare Inject_bool_def [eval,evale,evalp]

subsection {* @{term UNREST_PEXPR} theorems *}

lemma MkVarD_PUNDASHED [closure]:
  "MkVarD n a \<in> PUNDASHED"
  by (simp add:MkVarD_def PUNDASHED_def PVAR_VAR_MkPVAR)

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

lemma UNREST_PEXPR_ApplyD [unrest]: 
  "UNREST_PEXPR vs v \<Longrightarrow> UNREST_PEXPR vs (ApplyD f v)"
  by (simp add:UNREST_PEXPR_def ApplyD_def evalp Op1D_def)

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

lemma UNREST_PEXPR_NumD [unrest]:
  "vs \<sharp> NumD n"
  by (metis NumD_def UNREST_LitPE)

lemma VExprTrueT_unrest [unrest]: 
  "vs \<sharp> e \<Longrightarrow> vs \<sharp> VExprTrueT e"
  by (simp add:VExprTrueT_def unrest typing)

lemma VExprDefinedT_unrest [unrest]: 
  "vs \<sharp> e \<Longrightarrow> vs \<sharp> VExprDefinedT e"
  by (simp add:VExprDefinedT_def unrest typing)

lemma VTautHideT_unrest [unrest]:
  "vs \<sharp> e \<Longrightarrow> vs \<sharp> VTautHideT e"
  by (simp add:VTautHideT_def unrest UNREST_PEXPR_subset)

subsection {* Substitution theorems *}

lemma LitD_subst [usubst]:
  "LitD v[e/\<^sub>*x] = LitD v"
  by (simp add:usubst)

lemma Op1D_subst [usubst]:
  "(Op1D f v)[e/\<^sub>*x] = Op1D f (v[e/\<^sub>*x])"
  by (simp add:Op1D_def usubst)

lemma Op2D_subst [usubst]:
  "(Op2D f v1 v2)[e/\<^sub>*x] = Op2D f (v1[e/\<^sub>*x]) (v2[e/\<^sub>*x])"
  by (simp add:Op2D_def usubst)

lemma BotDE_subst [usubst]:
  fixes x :: "('a::vbasic) cmlvar"
  shows "(BotDE :: 'b cmle)[e/\<^sub>*x] = BotDE"
  by (simp add:evalp)

lemma VTautT_subst [usubst]:
  fixes e :: "('a::vbasic) cmle"
  assumes "x\<down> \<noteq> def\<down>" "e \<rhd>\<^sub>* x"
  shows "(VTautT v)[e\<down>/\<^sub>px\<down>] = VTautT (v[e/\<^sub>*x])"
  by (simp add:TVL_def usubst VExprDefinedT_def VExprTrueT_def typing defined unrest assms)

lemma VTautHideT_subst [usubst]:
  fixes e :: "('a::vbasic) cmle"
  assumes "x\<down> \<noteq> def\<down>" "e \<rhd>\<^sub>* x" "UNREST_PEXPR {def\<down>} e"
  shows "(VTautHideT v)[e\<down>/\<^sub>px\<down>] = VTautHideT (v[e/\<^sub>*x])"
  by (simp add:TVL_def usubst VExprDefinedT_def VExprTrueT_def typing defined unrest assms TrueT_def VTautHideT_def)

lemma VTautT_dash_subst [usubst]:
  fixes e :: "('a::vbasic) cmle"
  assumes "e \<rhd>\<^sub>* x\<acute>"
  shows "(VTautT v)[e\<down>/\<^sub>px\<down>\<acute>] = VTautT (v[e/\<^sub>*x\<acute>])"
  using assms
  apply (simp add:TVL_def VExprDefinedT_def VExprTrueT_def VTautHideT_def)
  apply (simp add:usubst typing defined unrest assms erasure SubstE_VarE_single_UNREST)
done

lemma VTautHideT_dash_subst [usubst]:
  fixes e :: "('a::vbasic) cmle"
  assumes "e \<rhd>\<^sub>* x\<acute>" "UNREST_PEXPR {def\<down>} e"
  shows "(VTautHideT v)[e\<down>/\<^sub>px\<down>\<acute>] = VTautHideT (v[e/\<^sub>*x\<acute>])"
  using assms
  apply (simp add:TVL_def VExprDefinedT_def VExprTrueT_def VTautHideT_def TrueT_def)
  apply (simp add:usubst typing defined unrest assms erasure SubstE_VarE_single_UNREST)
done

lemma HasTypeD_subst [usubst]:
  "(HasTypeD e t)[v/\<^sub>*x] = HasTypeD (e[v/\<^sub>*x]) t"
  by (simp add:evalp)
 
subsection {* Definedness theorems *}

lemma LitD_defined [defined]:
  "\<D> (LitD v)"
  by (simp add:Defined_option_def Defined_WF_PEXPRESSION_def evalp)

lemma NumD_defined [defined]:
  "\<D> (NumD n)"
  by (simp add:NumD_def defined)

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

lemma mk_prod_dom [defined]: 
  "dom (mk_prod \<circ> f) = UNIV"
  by (auto)

lemma ApplyD_defined [defined]:
  "\<lbrakk> \<D> v; \<forall> b. the (\<lbrakk>v\<rbrakk>\<^sub>* b) \<in> dom f \<rbrakk> \<Longrightarrow> \<D> (ApplyD f v)"
  by (simp add:ApplyD_def defined)

lemma vexpr_insert_defined [defined]:
  "\<lbrakk> \<D> x; \<D> xs \<rbrakk> \<Longrightarrow> \<D> (vexpr_insert x xs)"
  by (auto intro:defined simp add:bpfun_def vexpr_insert_def)

lemma vexpr_empty_defined [defined]:
  "\<D> vexpr_empty"
  by (simp add:vexpr_empty_def defined)

lemma EvalD_defined [defined]: "\<D> v \<Longrightarrow> \<D> (\<lbrakk>v\<rbrakk>\<^sub>*b)"
  by (simp add:Defined_option_def Defined_WF_PEXPRESSION_def)

lemma Some_defined [defined]: "\<D> (Some x)"
  by (simp add:Defined_option_def)

lemma None_not_defined [defined]: "\<not> \<D> None"
  by (simp add:Defined_option_def)

lemma VTaut_TrueD [simp]:
  "`\<lparr>true\<rparr>` = `true`"
  by (utp_pred_tac)

lemma SelectD_SingleD [simp]:
  "SelectD #1 (SingleD x) = x"
  by (simp add:evalp)

lemma VExprDefinedT_TrueDE [simp]: 
  "VExprDefinedT TrueDE = TrueP"
  by (utp_poly_tac)


(*
lemma VTaut_FalseD [simp]:
  "`\<lparr>false\<rparr>` = `false`"
  apply (utp_pred_tac)
  apply (rule_tac x="\<B>(def\<down> :=\<^sub>b TrueV)" in exI) 
  apply (simp del: MkBool_cmlv add:typing defined closure)
done  
*)

lemma BotD_defn: "|defn(undefined)| = |false|"
  by (simp add:evalp Defined_WF_PEXPRESSION_def)

lemma LitD_defn: "|defn(<<x>>)| = |true|"
  by (simp add:evalp Defined_WF_PEXPRESSION_def)

end