(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_expr.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML expressions *}

theory utp_cml_expr
imports 
  utp_cml_monad
begin

lemma EqualP_refine [refine]:
  "P[v/\<^sub>px] \<Longrightarrow> P \<sqsubseteq> $\<^sub>ex ==\<^sub>p v"
  by (metis ImpliesP_eq_subst RefP_def Tautology_def TrueP_eq_ClosureP less_eq_upred_def utp_pred_simps(14) utp_pred_simps(21))

default_sort vbasic

subsection {* CML expresssion type *}

defs (overloaded)
  InjU_cml [simp]:  "InjU (x::'a::vbasic option) \<equiv> InjVB x"
  ProjU_cml [simp]: "ProjU (x::cmlv) \<equiv> ProjVB x"
  TypeU_cml [simp]: "TypeU (x::('a::vbasic option) itself) \<equiv> embTYPE (VTYPE('a))"

lemma TypeUSound_cml [typing]: "TYPEUSOUND('a::vbasic option, cmlv)"
  by (force simp add: type_rel_cmlt typing defined)

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

definition upfun :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"upfun A f = ((\<lambda> v. Some (f v)) |` A)"

abbreviation "Op1DR A f \<equiv> Op1D (upfun A f)"
abbreviation "Op1D' f \<equiv> Op1DR UNIV f"

definition Op2D :: "('a::vbasic * 'b::vbasic \<rightharpoonup> 'c::vbasic) 
                   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle" where
"Op2D f u v = Op2PE (\<lambda> v1 v2. do { x <- v1; y <- v2; f (x, y) }) u v"

(* declare Op2D_def [eval, evale, evalp] *)

text {* Build a binary partial function from a normal binary HOL function *}

definition bpfun :: "('a * 'b) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a * 'b \<Rightarrow> 'c option)" where
"bpfun AB f \<equiv> (\<lambda> (v1, v2). Some (f v1 v2)) |` AB"

abbreviation "Op2DR AB f \<equiv> Op2D (bpfun AB f)"
abbreviation "Op2D' f \<equiv> Op2DR UNIV f"

definition Op3D :: "('a::vbasic * 'b::vbasic * 'c::vbasic \<rightharpoonup> 'd::vbasic) 
                   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle" where
"Op3D f u v w = Op3PE (\<lambda> v1 v2 v3. do { x <- v1; y <- v2; z <- v3; f (x, y, z) }) u v w"

definition tpfun :: "('a * 'b * 'c) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a * 'b * 'c \<Rightarrow> 'd option)" where
"tpfun ABC f \<equiv> (\<lambda> (v1, v2, v3). Some (f v1 v2 v3)) |` ABC"

abbreviation "Op3DR ABC f \<equiv> Op3D (tpfun ABC f)"
abbreviation "Op3D' f \<equiv> Op3DR UNIV f"

definition SingleD :: "'a cmle \<Rightarrow> ('a*unit) cmle" where
"SingleD x = Op1D' (\<lambda> x. (x, ())) x"

declare SingleD_def [eval,evale,evalp]

abbreviation TokenD :: "'a::vbasic cmle \<Rightarrow> token cmle" where
"TokenD v \<equiv> Op1D' (Abs_token \<circ> Inject) v"

definition ListD :: "'a::vbasic cmle list \<Rightarrow> 'a list cmle" where
"ListD xs = MkPExpr (\<lambda> b. mapM (\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>* b) xs)"

definition FSetD :: "'a::vbasic cmle fset \<Rightarrow> 'a fset cmle" where
"FSetD xs = MkPExpr (\<lambda> b. fset_option ((\<lambda> v. \<lbrakk>v\<rbrakk>\<^sub>* b) `\<^sub>f xs))"

abbreviation "NotD     \<equiv> (Op1PE mnot :: bool cmle \<Rightarrow> bool cmle)"
abbreviation "AndD     \<equiv> (Op2PE mconj :: bool cmle \<Rightarrow> bool cmle \<Rightarrow> bool cmle)"
abbreviation "OrD      \<equiv> (Op2PE mdisj :: bool cmle \<Rightarrow> bool cmle \<Rightarrow> bool cmle)"
abbreviation "ImpliesD \<equiv> (Op2PE mimplies :: bool cmle \<Rightarrow> bool cmle \<Rightarrow> bool cmle)"

definition LetD :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> ('a option \<Rightarrow> 'b cmle) \<Rightarrow> 'b cmle" where
"LetD v A f = do { x <- v; f (Some x) }"

definition ForallD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"ForallD xs f = MkPExpr (\<lambda> b. (Some (\<forall> x \<in> xs. [\<lbrakk>f (Some x)\<rbrakk>\<^sub>* b]\<^sub>3)))"

definition ExistsD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"ExistsD xs f = MkPExpr (\<lambda> b. (Some (\<exists> x \<in> xs. [\<lbrakk>f (Some x)\<rbrakk>\<^sub>* b]\<^sub>3)))"

definition Exists1D :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"Exists1D xs f = MkPExpr (\<lambda> b. (Some (\<exists>! x \<in> xs. [\<lbrakk>f (Some x)\<rbrakk>\<^sub>* b]\<^sub>3)))"

definition IotaD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> 'a cmle" where 
"IotaD xs f = MkPExpr (\<lambda> b. (if (\<exists>! x \<in> xs. [\<lbrakk>f (Some x)\<rbrakk>\<^sub>* b]\<^sub>3)
                                then Some (THE x. [\<lbrakk>f (Some x)\<rbrakk>\<^sub>* b]\<^sub>3)
                                else None))"

definition EpsD :: "'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> 'a cmle" where 
"EpsD xs f = MkPExpr (\<lambda> b. (if (\<exists> x \<in> xs. [\<lbrakk>f (Some x)\<rbrakk>\<^sub>* b]\<^sub>3)
                                then Some (SOME x. [\<lbrakk>f (Some x)\<rbrakk>\<^sub>* b]\<^sub>3)
                                else None))"

definition FunD :: "'a set \<Rightarrow> ('a option \<Rightarrow> 'b cmle) \<Rightarrow> 'a \<Rightarrow> 'b option" where
"FunD t P = (\<lambda> x. \<lbrakk>P (Some x)\<rbrakk>\<^sub>*\<B>)"

declare FunD_def [evalp]

abbreviation DefinedD :: "'a cmle \<Rightarrow> bool cmle" where
"DefinedD v \<equiv> LitD (\<D> v)"

definition HasTypeD :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> bool cmle" where
"HasTypeD e t \<equiv> MkPExpr (\<lambda> b. \<lbrakk>e\<rbrakk>\<^sub>*b \<guillemotright>= (\<lambda> x. \<lfloor>x \<in> t\<rfloor>))"

(*
definition HasType :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> bool" (infix ":\<^sub>d" 50) where
"HasType e t = (\<forall> b. \<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<longrightarrow> the (\<lbrakk>e\<rbrakk>\<^sub>*b) \<in> t)"

definition HasTypeD :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> bool cmle" where
"HasTypeD e t \<equiv> MkPExpr (\<lambda> b. if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t)
                              then Some True 
                              else Some False)"
*)

definition CoerceD :: "'a cmle \<Rightarrow> 'a set \<Rightarrow> 'a cmle" where
"CoerceD e t \<equiv> MkPExpr (\<lambda> b. if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t)
                             then \<lbrakk>e\<rbrakk>\<^sub>* b 
                             else None)"

definition CollectD :: "'a::vbasic cmle \<Rightarrow> bool cmle \<Rightarrow> 'a set" where
"CollectD v p = {the (\<lbrakk>v\<rbrakk>\<^sub>*b) | b. \<D> (\<lbrakk>v\<rbrakk>\<^sub>*b) \<and> [\<lbrakk>p\<rbrakk>\<^sub>*b]\<^sub>3}"

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

nonterminal 
  idt_list and
  vty and 
  vprod and 
  vbind and 
  vset_bind and
  vset_binds and
  vtype_bind and
  vtype_binds and
  vbinds

syntax
  "_vidt"        :: "idt \<Rightarrow> idt_list" ("_")
  "_vidts"       :: "idt \<Rightarrow> idt_list \<Rightarrow> idt_list" ("_,/ _")
  "_vidt_cl"     :: "vbinds \<Rightarrow> logic" ("\<bar>_\<bar>")
  "_vtybind"     :: "idt_list \<Rightarrow> vty \<Rightarrow> vtype_bind" ("_ : _")
  "_vsetbind"    :: "idt_list \<Rightarrow> n_pexpr \<Rightarrow> vset_bind" ("_ in @set _")
  "_vsb"         :: "vset_bind \<Rightarrow> vbind" ("_")
  "_vtb"         :: "vtype_bind \<Rightarrow> vbind" ("_")
  "_vbind"       :: "vbind \<Rightarrow> vbinds" ("_")
  "_vbinds"      :: "vbind \<Rightarrow> vbinds \<Rightarrow> vbinds" ("_,/ _")
  "_vtype_bind"  :: "vtype_bind \<Rightarrow> vtype_binds" ("_")
  "_vtype_binds" :: "vtype_bind \<Rightarrow> vtype_binds \<Rightarrow> vtype_binds" ("_,/ _")

translations 
  "_vtb x" => "x"
  "_vsb x" => "x"

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
  "_n_pexpr_equal"       :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "=" 50)
  "_n_pexpr_true"        :: "n_pexpr" ("true")
  "_n_pexpr_false"       :: "n_pexpr" ("false")
  "_n_pexpr_num_0"       :: "n_pexpr" ("0")
  "_n_pexpr_num_1"       :: "n_pexpr" ("1")
  "_n_pexpr_num"         :: "num_const \<Rightarrow> n_pexpr" ("_")
  "_n_pexpr_float"       :: "float_const \<Rightarrow> n_pexpr" ("_")
  "_n_pexpr_string"      :: "str_position \<Rightarrow> n_pexpr" ("_")
  "_n_pexpr_plus"        :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "+" 65)
  "_n_pexpr_minus"       :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "-" 65)
  "_n_pexpr_mult"        :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "*" 70)
  "_n_pexpr_div"         :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "'/" 70)
  "_n_pexpr_less"        :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "<" 25)
  "_n_pexpr_less_eq"     :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<le>" 25)
  "_n_pexpr_greater"     :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr ">" 25)
  "_n_pexpr_greater_eq"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<ge>" 25)
  "_n_pexpr_int"         :: "int \<Rightarrow> n_pexpr" ("<_>")
  "_n_pexpr_set"         :: "n_pexprs \<Rightarrow> n_pexpr" ("{_}")
  "_n_pexpr_set_empty"   :: "n_pexpr" ("{}")
  "_n_pexpr_fset_empty"  :: "n_pexpr" ("{}")
  "_n_pexpr_fset"        :: "n_pexprs \<Rightarrow> n_pexpr" ("{_}")
  "_n_pexpr_list"        :: "n_pexprs \<Rightarrow> n_pexpr" ("\<langle>_\<rangle>")
  "_n_pexpr_list_nil"    :: "n_pexpr" ("\<langle>\<rangle>")
  "_n_pexpr_expr_var"    :: "idt \<Rightarrow> n_pexpr" ("(_)")
  "_n_pexpr_pred_var"    :: "idt \<Rightarrow> n_pexpr" ("@(_)")
  "_n_expr_quote"        :: "n_expr \<Rightarrow> 'a uexpr" ("(1^_^)")
  "_n_upred_n_pexpr"       :: "n_pexpr \<Rightarrow> n_upred" ("\<lparr>_\<rparr>")
  "_uproc_n_pexpr"       :: "n_pexpr \<Rightarrow> n_uproc" ("\<lparr>_\<rparr>")
  "_n_upred_callpr"      :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("call _'[_']")
  "_n_pexpr_op1"         :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'(_')")
  "_n_pexpr_op2"         :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'(_,_')")
  "_n_pexpr_op3"         :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'(_,_,_')")

no_translations
  "_upred_callpr f v"       == "CONST CallRO f v"

abbreviation "vexpr_defined   \<equiv> (DefinedD :: 'a cmle \<Rightarrow> bool cmle)"

syntax
  "_vexpr_eval"     :: "n_pexpr \<Rightarrow> 'a" ("+|_|+")
  "_vexpr_defined"  :: "n_pexpr \<Rightarrow> n_pexpr" ("defn'(_')")
  "_vexpr_expr_var" :: "idt \<Rightarrow> n_pexpr" ("@_" [999] 999)
  "_vexpr_val_var"  :: "idt \<Rightarrow> n_pexpr" ("&_" [999] 999)
  "_vexpr_lit_var"  :: "idt \<Rightarrow> n_pexpr" ("%_" [999] 999)
  "_vexpr_equal"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "=" 50)
  "_vexpr_nequal"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "<>" 50)
  "_vexpr_unit"     :: "n_pexpr" ("'(')")
  "_vexpr_true"     :: "n_pexpr" ("true")
  "_vexpr_false"    :: "n_pexpr" ("false")
  "_vexpr_not"     :: "n_pexpr \<Rightarrow> n_pexpr" ("not _" [40] 40)
  "_vexpr_and"     :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "and" 35)
  "_vexpr_or"      :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "or" 30)
  "_vexpr_implies" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "=>" 25)
  "_vexpr_token"    :: "n_pexpr \<Rightarrow> n_pexpr" ("mk'_token'(_')")
  "_vexpr_num"      :: "real \<Rightarrow> n_pexpr" ("_")
  "_vexpr_bot"      :: "n_pexpr" ("undef")
  "_vexpr_lit"      :: "'a::vbasic option \<Rightarrow> n_pexpr" ("(1^_^)")
  "_vexpr_litd"     :: "'a::vbasic \<Rightarrow> n_pexpr" ("(1<<_>>)")
  "_vexpr_let"      :: "idt \<Rightarrow> vty \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("let _ : _ = _ in _")
  "_vexpr_lambda"   :: "idt \<Rightarrow> vty \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3lambda _ : _ @/ _)" [0, 10] 10)
  "_vexpr_ulambda"  :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3lambda _ @/ _)" [0, 10] 10)
  "_vexpr_forall"   :: "vbinds \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3forall _ @/ _)" [0, 10] 10)
  "_vexpr_exists"   :: "vbinds \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3exists _ @/ _)" [0, 10] 10)
  "_vexpr_exists1"  :: "vbinds \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3exists1 _ @/ _)" [0, 10] 10)
  "_vexpr_iota"     :: "vbinds \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3iota _ @/ _)" [0, 10] 10)
  "_vexpr_eps"      :: "pttrn \<Rightarrow> vty \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3eps _ : _ @/ _)" [0, 0, 10] 10)
  "_vexpr_coerce"   :: "n_pexpr \<Rightarrow> vty \<Rightarrow> n_pexpr" (infix ":" 50)
  "_vexpr_ifthen"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("if _ then _ else _")
  "_vexpr_hasType"  :: "n_pexpr \<Rightarrow> vty \<Rightarrow> n_pexpr" (infix "hasType" 50)
  "_vexpr_apply"    :: "('a \<Rightarrow> 'b) \<Rightarrow> n_pexprs \<Rightarrow> n_pexpr"    ("_'(_')" [998,0] 998)
  "_vexpr_vapply"   :: "'a \<Rightarrow> n_pexpr"    ("_'(')" [998] 998)
  "_vexpr_prod"     :: "n_pexprs \<Rightarrow> vprod" ("_")
  "_vexpr_select"   :: "n_pexpr \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> n_pexpr" ("_._" [89,90] 90)
  "_vexpr_nil"      :: "n_pexpr" ("[]")
  "_vexpr_list"     :: "n_pexprs => n_pexpr"    ("[(_)]")
  "_vexpr_empty"    :: "n_pexpr" ("{}")
  "_vexpr_fset"     :: "n_pexprs => n_pexpr"    ("{(_)}")

syntax (xsymbols)
  "_vexpr_bot"     :: "n_pexpr" ("\<bottom>")

translations
  "_vexpr_eval e"              == "\<lbrakk>e\<rbrakk>\<^sub>* \<B>"
  "_vexpr_defined x"           == "CONST vexpr_defined x"
  "_vexpr_expr_var x"          => "x"
  "_vexpr_val_var x"           == "CONST LitPE x"
  "_vexpr_lit_var x"           == "CONST LitD x"
  "_vexpr_equal"               == "CONST vexpr_equal"
  "_vexpr_nequal"              == "CONST vexpr_nequal"
  "_vexpr_unit"                == "CONST UnitD"
  "_vexpr_true"                == "CONST TrueDE"
  "_vexpr_false"               == "CONST FalseDE"
  "_vexpr_not x"               == "CONST NotD x"
  "_vexpr_and x y"             == "CONST AndD x y"
  "_vexpr_or x y"              == "CONST OrD x y"
  "_vexpr_implies x y"         == "CONST ImpliesD x y"
  "_vexpr_token x"             == "CONST TokenD x"
  "_vexpr_num n"               == "CONST NumD n"
  "_vexpr_bot"                 == "CONST BotDE"
  "_vexpr_lit v"               == "CONST LitPE v"
  "_vexpr_litd v"              == "CONST LitD v"
  "_vexpr_let x A v e"         == "CONST LetD v A (\<lambda> x. e)"

  (* Parse rules for lambda abstractions *)

  "_vexpr_lambda x A e" == "CONST FunD A (\<lambda> x. e)"

  "_vexpr_ulambda x e" == "CONST FunD CONST UNIV (\<lambda> x. e)"

  (* Parse rules for forall quantifiers *)

  "_vexpr_forall 
    (_vbinds 
      (_vtybind 
        (_vidts x xs) A) bs) e" => "CONST ForallD A (\<lambda>x. _vexpr_forall 
                                                          (_vbinds (_vtybind xs A) bs) e)"
  "_vexpr_forall 
    (_vbinds 
      (_vtybind 
        (_vidt x) xs) bs) e" == "CONST ForallD xs (\<lambda>x. _vexpr_forall bs e)"
  "_vexpr_forall 
    (_vbind 
      (_vtybind 
        (_vidts x xs) A)) e" => "CONST ForallD A (\<lambda>x. _vexpr_forall (_vbind (_vtybind xs A)) e)"
  "_vexpr_forall 
    (_vbind 
      (_vtybind 
        (_vidt x) xs)) e" == "CONST ForallD xs (\<lambda>x. e)"

  (* Parse rules for exists quantifiers *)

  "_vexpr_exists 
    (_vbinds 
      (_vtybind 
        (_vidts x xs) A) bs) e" => "CONST ExistsD A (\<lambda>x. _vexpr_exists
                                                          (_vbinds (_vtybind xs A) bs) e)"
  "_vexpr_exists 
    (_vbinds 
      (_vtybind 
        (_vidt x) xs) bs) e" == "CONST ExistsD xs (\<lambda>x. _vexpr_exists bs e)"
  "_vexpr_exists 
    (_vbind 
      (_vtybind 
        (_vidts x xs) A)) e" => "CONST ExistsD A (\<lambda>x. _vexpr_exists (_vbind (_vtybind xs A)) e)"
  "_vexpr_exists 
    (_vbind 
      (_vtybind 
        (_vidt x) xs)) e" == "CONST ExistsD xs (\<lambda>x. e)"

  (* Parse rules for exists1 quantifiers *)

  "_vexpr_exists1 
    (_vbinds 
      (_vtybind 
        (_vidts x xs) A) bs) e" => "CONST Exists1D A (\<lambda>x. _vexpr_exists1
                                                          (_vbinds (_vtybind xs A) bs) e)"
  "_vexpr_exists1 
    (_vbinds 
      (_vtybind 
        (_vidt x) xs) bs) e" == "CONST Exists1D xs (\<lambda>x. _vexpr_exists1 bs e)"
  "_vexpr_exists1 
    (_vbind 
      (_vtybind 
        (_vidts x xs) A)) e" => "CONST Exists1D A (\<lambda>x. _vexpr_exists1 (_vbind (_vtybind xs A)) e)"
  "_vexpr_exists1 
    (_vbind 
      (_vtybind 
        (_vidt x) xs)) e" == "CONST Exists1D xs (\<lambda>x. e)"

  (* Parse rules for iota description operator *)

  "_vexpr_iota 
    (_vbinds 
      (_vtybind 
        (_vidts x xs) A) bs) e" => "CONST IotaD A (\<lambda>x. _vexpr_iota
                                                          (_vbinds (_vtybind xs A) bs) e)"
  "_vexpr_iota 
    (_vbinds 
      (_vtybind 
        (_vidt x) xs) bs) e" == "CONST IotaD xs (\<lambda>x. _vexpr_iota bs e)"
  "_vexpr_iota 
    (_vbind 
      (_vtybind 
        (_vidts x xs) A)) e" => "CONST IotaD A (\<lambda>x. _vexpr_iota (_vbind (_vtybind xs A)) e)"
  "_vexpr_iota 
    (_vbind 
      (_vtybind 
        (_vidt x) xs)) e" == "CONST IotaD xs (\<lambda>x. e)"

  "_vexpr_eps x xs e"          == "CONST EpsD xs (\<lambda>x. e)"
  "_vexpr_coerce e t"          == "CONST CoerceD e t"
  "_vexpr_ifthen b x y"        == "CONST IfThenElseD b x y"
  "_vexpr_hasType e t"         == "CONST HasTypeD e t"
  "_vexpr_apply f x"           == "CONST ApplyD f (_vexpr_prod x)"
  "_vexpr_vapply f"            => "CONST ApplyD f (CONST LitD ())"
  "_vexpr_prod (_n_pexprs x xs)" == "CONST vexpr_prod x (_vexpr_prod xs)"
  "_vexpr_prod x"              == "CONST SingleD x"
  "_vexpr_select e f"          == "CONST SelectD f e"
  "_vexpr_nil"                 == "CONST vexpr_nil"
  "_vexpr_list (_n_pexprs x xs)" == "CONST vexpr_cons x (_vexpr_list xs)"
  "_vexpr_list x"              == "CONST vexpr_cons x CONST vexpr_nil"
  "_vexpr_empty"               == "CONST vexpr_empty"
  "_vexpr_fset (_n_pexprs x xs)" == "CONST vexpr_insert x (_vexpr_fset xs)"
  "_vexpr_fset x"              == "CONST vexpr_insert x CONST vexpr_empty"

definition mk_prod :: "'a \<Rightarrow> 'a option" where
"mk_prod = Some"

declare mk_prod_def [evalp]

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
  "_n_upred_vexpr"       :: "n_pexpr \<Rightarrow> n_upred" ("\<lparr>_\<rparr>")
  "_n_uproc_vexpr"       :: "n_pexpr \<Rightarrow> n_uproc" ("\<lparr>_\<rparr>")
  "_n_upred_vcallpr"     :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> n_pexprs \<Rightarrow> n_upred" ("call _'[_']")
  "_n_upred_vcallpr_nil" :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> n_upred" ("call _'[']")

translations
  "_n_upred_vexpr e" == "CONST VTautHideT e"
  "_n_uproc_vexpr e" == "CONST VTautHideO e"
  "_n_upred_vcallpr f ps" == "CONST CallRO f (_vexpr_prod ps)"
  "_n_upred_vcallpr_nil f" == "CONST CallRO f CONST UnitD"

subsection {* Evaluation theorems *}

lemma EvalE_cmle [evale, evalp, eval]:
  fixes e :: "'a::vbasic cmle"
  shows "\<lbrakk>e\<down>\<rbrakk>\<^sub>eb = InjVB (\<lbrakk>e\<rbrakk>\<^sub>*b)"
  by (simp add:evale typing)

lemma EvalD_LitD [eval,evalp,evale]:
  "\<lbrakk>LitD x\<rbrakk>\<^sub>*b = Some x"
  by (simp add:evalp)

lemma EvalD_LetD [evalp]:
  "\<lbrakk>LetD v A f\<rbrakk>\<^sub>*b = do { x <- \<lbrakk>v\<rbrakk>\<^sub>*b; \<lbrakk>f(Some x)\<rbrakk>\<^sub>*b }"
  by (simp add:LetD_def evalp)

lemma EvalD_NumD [eval,evalp,evale]:
  "\<lbrakk>NumD x\<rbrakk>\<^sub>*b = Some x"
  by (simp add:NumD_def evalp)

lemma EvalD_BotDE [eval,evalp,evale]:
  "\<lbrakk>\<bottom>\<^sub>v\<rbrakk>\<^sub>*b = None"
  by (simp add:BotDE_def evalp)

lemma EvalD_ForallD [eval,evalp,evale]:
  "\<lbrakk>ForallD xs f\<rbrakk>\<^sub>*b = \<lfloor>\<forall>x\<in>xs. [\<lbrakk>f \<lfloor>x\<rfloor>\<rbrakk>\<^sub>*b]\<^sub>3\<rfloor>"
  by (simp add:ForallD_def)

lemma EvalD_Op1D [eval,evalp,evale]:
  "\<lbrakk>Op1D f x\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>*b >>= f)"
  by (simp add:Op1D_def evalp)

lemma EvalD_ApplyD [eval,evalp,evale]:
  "\<lbrakk>ApplyD f x\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>*b >>= f)"
  by (simp add:ApplyD_def evalp)

lemma EvalD_SelectD [eval,evalp,evale]:
  "\<lbrakk>SelectD f x\<rbrakk>\<^sub>*b = \<lbrakk>x\<rbrakk>\<^sub>* b >>= upfun UNIV f"
  by (simp add:SelectD_def evalp)

lemma EvalD_Op2D [eval,evalp,evale]:
  "\<lbrakk>Op2D f x y\<rbrakk>\<^sub>*b = do { v1 <- \<lbrakk>x\<rbrakk>\<^sub>*b; v2 <- \<lbrakk>y\<rbrakk>\<^sub>*b; f (v1, v2) }"
  by (simp add:Op2D_def evalp)

lemma EvalD_Op3D [eval,evalp,evale]:
  "\<lbrakk>Op3D f x y z\<rbrakk>\<^sub>*b = do { v1 <- \<lbrakk>x\<rbrakk>\<^sub>*b; v2 <- \<lbrakk>y\<rbrakk>\<^sub>*b; v3 <- \<lbrakk>z\<rbrakk>\<^sub>*b; f (v1, v2, v3) }"
  by (simp add:Op3D_def evalp)

(*
lemma EvalD_HasTypeD [eval,evalp,evale]:
  "\<lbrakk>HasTypeD e t\<rbrakk>\<^sub>*b = (if (\<D> (\<lbrakk>e\<rbrakk>\<^sub>* b) \<and> the (\<lbrakk>e\<rbrakk>\<^sub>* b) \<in> t) then \<lfloor>True\<rfloor> else \<lfloor>False\<rfloor>)"
  by (simp add:HasTypeD_def)
*)

lemma EvalD_HasTypeD [eval,evalp,evale]:
  "\<lbrakk>HasTypeD e t\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>*b \<guillemotright>= (\<lambda> x. \<lfloor>x \<in> t\<rfloor>)"
  by (simp add:HasTypeD_def)

lemma EvalD_CoerceD [eval,evalp,evale]:
  "\<lbrakk> \<D> (\<lbrakk>x\<rbrakk>\<^sub>*b); the (\<lbrakk>x\<rbrakk>\<^sub>*b) \<in> t \<rbrakk> \<Longrightarrow> \<lbrakk>CoerceD x t\<rbrakk>\<^sub>*b = \<lbrakk>x\<rbrakk>\<^sub>*b"
  by (simp add:CoerceD_def)

declare IotaD_def [evalp]
declare EpsD_def [evalp]

lemma upfun_apply [simp]:
  "upfun A f x = (if (x \<in> A) then Some (f x) else None)"
  by (simp add:upfun_def)

lemma bpfun_apply [simp]:
  "bpfun AB f x = (if (x \<in> AB) 
                   then Some (f (fst x) (snd x))
                   else None)"
  apply (auto)
  apply (case_tac x)
  apply (auto simp add:bpfun_def)
done

lemma tpfun_apply [simp]:
  "tpfun ABC f x = (if (x \<in> ABC)
                    then Some (f (fst x) (fst (snd x)) (snd (snd x)))
                    else None)"
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
  by (utp_poly_tac)

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
  by (utp_poly_tac)
 
subsection {* Definedness theorems *}

lemma LitD_defined [defined]:
  "\<D> (LitD v)"
  by (simp add:Defined_option_def Defined_pexpr_def evalp)

lemma NumD_defined [defined]:
  "\<D> (NumD n)"
  by (simp add:NumD_def defined)

lemma BotDE_not_defined [defined]:
  "\<D> \<bottom>\<^sub>v = False"
  by (simp add:BotDE_def Defined_pexpr_def evalp)

lemma Defined_option_elim [elim]:
  "\<lbrakk> \<D> x; \<And> y. \<lbrakk> x = Some y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add:Defined_option_def)
  apply (metis not_None_eq option.simps(6) option.simps(7))
done

lemma Op1D_EvalD_defined [defined]: 
  "\<lbrakk> \<D> v; \<forall> b. the (\<lbrakk>v\<rbrakk>\<^sub>* b) \<in> dom f \<rbrakk> \<Longrightarrow> \<D> (Op1D f v)"
  apply (auto simp add:Op1D_def Defined_pexpr_def evalp)
  apply (drule_tac x="b" in spec)+
  apply (erule Defined_option_elim)
  apply (auto simp add:dom_def)
done

lemma Op2D_EvalD_defined [defined]: 
  "\<lbrakk> \<D> v1; \<D> v2; \<forall> b. (the (\<lbrakk>v1\<rbrakk>\<^sub>* b), the (\<lbrakk>v2\<rbrakk>\<^sub>* b)) \<in> dom f \<rbrakk> \<Longrightarrow> \<D> (Op2D f v1 v2)"
  apply (auto simp add:Op2D_def Defined_pexpr_def evalp EvalPE_ProdPE)
  apply (drule_tac x="b" in spec)+
  apply (erule Defined_option_elim)
  apply (erule Defined_option_elim)
  apply (auto simp add:dom_def)
done

lemma upfun_dom [defined]: 
  "dom (upfun A f) = A"
  by (auto simp add:upfun_def)

lemma bpfun_dom [defined]: 
  "dom (bpfun AB f) = AB"
  by (auto simp add:bpfun_def)

lemma mk_prod_dom [defined]: 
  "dom (mk_prod \<circ> f) = UNIV"
  by (auto simp add:mk_prod_def)

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
  by (simp add:Defined_option_def Defined_pexpr_def)

lemma Some_defined [defined]: "\<D> (Some x)"
  by (simp add:Defined_option_def)

lemma None_not_defined [defined]: "\<not> \<D> None"
  by (simp add:Defined_option_def)

lemma VTaut_TrueD [simp]:
  "`\<lparr>true\<rparr>` = `true`"
  by (utp_poly_tac)

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

lemma BotD_defn: "|defn(undef)| = |false|"
  by (simp add:evalp Defined_pexpr_def)

lemma LitD_defn: "|defn(<<x>>)| = |true|"
  by (simp add:evalp Defined_pexpr_def)

end