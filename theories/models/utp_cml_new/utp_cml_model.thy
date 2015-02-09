(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_values.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Value Domain *}

theory utp_cml_model
imports 
  Derive
  Char_ord
  Option_ord
  Monad_Syntax
  utp_base
  utp_designs
  utp_definedness
  utp_csp
begin

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

no_notation
  residual_r (infixr "\<rightarrow>" 60) and
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

subsection {* CML types *}

datatype cmlt =
    BoolT
  | ChanT
  | CharT
  | EventT
  | SetT cmlt 
  | FuncT cmlt cmlt
  | ListT cmlt
  | NameT
  | NumberT
  | OptionT cmlt
  | PairT cmlt cmlt 
  | QuoteT
  | TagT "string" "cmlt"
  | TokenT
  | TypeT
  | UnitT

(*
derive countable cmlt
derive linorder cmlt
*)

subsection {* CML domain types *}

text {* We introduce countable values using a normal datatype. This representation
  is not fully canonical, as we use lists to represents sets, maps and records.
  However, we later introduce constructors for these which use the correct types
  and thus ensure canonicity. *}

datatype_new cmlv 
  = BoolD bool
  | BotD cmlt
  | ChanD uname cmlt
  | CharD "char"
  | EvD uname cmlt cmlv
  | SetD cmlt "cmlv bset"
  | ListD cmlt "cmlv list"
  | FuncD cmlt cmlt 
         "(cmlv * cmlv) bset" 
  | NameD uname
  | NumberD "real"
  | OptionD cmlt "cmlv option"
  | PairD cmlv cmlv
  | QuoteD "string" 
  | TagD "string" "cmlv"
  | TokenD cmlv
  | TypeD "cmlt"
  | UnitD

abbreviation "TrueD \<equiv> BoolD True"
abbreviation "FalseD \<equiv> BoolD False"

subsection {* Injections *}

text {* We create interface constructors for finite sets, maps and records which
  use derived subtypes as inputs and therefore preserve canonicity of vbasic *}

fun ProjPairD :: "cmlv \<Rightarrow> (cmlv * cmlv) option" where
"ProjPairD (PairD x y) = Some (x,y)" | "ProjPairD x = None"

fun ProjCharD :: "cmlv \<Rightarrow> char option" where
"ProjCharD (CharD x) = Some x" | "ProjCharD x = None"

fun ProjBoolD :: "cmlv \<Rightarrow> bool option" where
"ProjBoolD (BoolD x) = Some x" | "ProjBoolD x = None"

fun ProjListD :: "cmlv \<Rightarrow> (cmlv list) option" where
"ProjListD (ListD t xs) = Some xs" | "ProjListD xs = None"

fun ProjOptionD :: "cmlv \<Rightarrow> (cmlv option) option" where
"ProjOptionD (OptionD t x) = Some x" | "ProjOptionD x = None"

fun ProjTagD :: "cmlv \<Rightarrow> (string * cmlv) option" where
"ProjTagD (TagD n r) = Some (n,r)" | "ProjTagD xs = None"

fun ProjFuncD :: "cmlv \<Rightarrow> ((cmlv * cmlv) bset) option" where
"ProjFuncD (FuncD a b f) = Some f" | "ProjFuncD x = None"

fun IsFuncD :: "cmlv \<Rightarrow> bool" where
"IsFuncD (FuncD a b f) = True" |
"IsFuncD _ = False"

primrec ProjSetD :: "cmlv \<Rightarrow> cmlv bset" where
"ProjSetD (SetD a x) = x"

fun IsSetD :: "cmlv \<Rightarrow> bool" where
"IsSetD (SetD a x) = True" |
"IsSetD _ = False"

subsection {* CML basic type-system *}
 
inductive cmlv_type_rel :: 
  "cmlv \<Rightarrow> cmlt \<Rightarrow> bool" (infix ":\<^sub>v" 50) where
BoolD_type[intro!]: "BoolD x :\<^sub>v BoolT" |
BotD_type[intro]: "BotD a :\<^sub>v a" |
ChanD_type[intro!]: "ChanD n t :\<^sub>v ChanT" |
CharD_type[intro!]: "CharD x :\<^sub>v CharT" |
EvD_type[intro!]: "v :\<^sub>v t \<Longrightarrow> EvD n t v :\<^sub>v EventT" |
SetD_type[intro!]: "\<lbrakk> \<forall>x\<in>\<^sub>bA. x :\<^sub>v a \<rbrakk> \<Longrightarrow> SetD a A :\<^sub>v SetT a" |
FuncD_type[intro!]: "\<lbrakk> (\<forall> (x,y)\<in>\<^sub>b F. x :\<^sub>v a \<and> y :\<^sub>v b); bfunctional F \<rbrakk> \<Longrightarrow> FuncD a b F :\<^sub>v FuncT a b" | 
ListD_type[intro!]:  "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>v a \<rbrakk> \<Longrightarrow> ListD a xs :\<^sub>v ListT a" |
NameD_type[intro]: "NameD n :\<^sub>v NameT" |
NumberD_type[intro!]: "NumberD x :\<^sub>v NumberT" | 
OptionD_None_type[intro]: 
  "OptionD a None :\<^sub>v OptionT a" |
OptionD_Some_type[intro]: 
  "x :\<^sub>v a \<Longrightarrow> OptionD a (Some x) :\<^sub>v OptionT a" |
PairD_type[intro!]: 
  "\<lbrakk> x :\<^sub>v a; y :\<^sub>v b \<rbrakk> \<Longrightarrow> PairD x y :\<^sub>v PairT a b" |
QuoteD_type[intro!]: "QuoteD x :\<^sub>v QuoteT" |
TagD_type[intro]: 
  "x :\<^sub>v t \<Longrightarrow> TagD n x :\<^sub>v TagT n t" |
TokenD_type[intro!]: "TokenD x :\<^sub>v TokenT" |
TypeD_type[intro]: "TypeD t :\<^sub>v TypeT" |
UnitD_type[intro!]: "UnitD :\<^sub>v UnitT" 

inductive_cases 
  BoolD_type_cases [elim]: "BoolD x :\<^sub>v t" and
  BoolT_type_cases [elim!]: "x :\<^sub>v BoolT" and
  BotD_type_cases[elim]: "BotD a :\<^sub>v b" and
  ChanD_type_cases [elim]: "ChanD n t :\<^sub>v a" and
  ChanT_type_cases [elim!]: "x :\<^sub>v ChanT" and
  CharD_type_cases [elim]: "CharD x :\<^sub>v t" and
  CharT_type_cases [elim!]: "x :\<^sub>v CharT" and
  EvD_type_cases [elim]: "EvD n t v :\<^sub>v a" and
  EventT_type_cases [elim!]: "x :\<^sub>v EventT" and
  SetD_type_cases [elim]: "SetD a x :\<^sub>v b" and
  SetT_type_cases: "x :\<^sub>v SetT a" and
  ListD_type_cases [elim]: "ListD a xs :\<^sub>v b" and
  ListT_type_cases [elim!]: "x :\<^sub>v ListT a" and
  FuncD_type_cases [elim]: "FuncD a b xs :\<^sub>v t" and
  FuncT_type_cases [elim!]: "x :\<^sub>v FuncT a b" and
  NameD_type_cases [elim]: "NameD x :\<^sub>v t" and
  NameT_type_cases [elim!]: "x :\<^sub>v NameT" and
  NumberD_type_cases [elim]: "NumberD x :\<^sub>v t" and
  NumberT_type_cases [elim!]: "x :\<^sub>v NumberT" and
  OptionI_type_cases [elim]: "OptionD a x :\<^sub>v b" and
  OptionT_type_cases [elim]: "x :\<^sub>v OptionT a" and
  PairD_type_cases [elim]: "PairD x y :\<^sub>v t" and
  PairT_type_cases [elim!]: "x :\<^sub>v PairT a b" and
  QuoteD_type_cases [elim]: "QuoteD x :\<^sub>v t" and
  QuoteT_type_cases [elim!]: "x :\<^sub>v QuoteT" and
  TagD_type_cases [elim]: "TagD n x :\<^sub>v t" and
  TagT_type_cases [elim!]: "x :\<^sub>v TagT n t" and
  TokenD_type_cases [elim]: "TokenD x :\<^sub>v t" and
  TokenT_type_cases [elim!]: "x :\<^sub>v TokenT" and
  TypeD_type_cases [elim]: "TypeD x :\<^sub>v t" and
  TypeT_type_cases [elim!]: "x :\<^sub>v TypeT" and
  UnitD_type_cases [elim]: "UnitD :\<^sub>v t" and
  UnitT_type_cases [elim!]: "x :\<^sub>v UnitT"

definition bcarrier :: "cmlt \<Rightarrow> cmlv set" where
"bcarrier t = {x. x :\<^sub>v t}"

subsubsection {* Derived Typing Rules *}

lemma NilD_type[intro]: "ListD a [] :\<^sub>v ListT a"
  by auto

lemma ConsD_type[intro]: 
  "\<lbrakk> x :\<^sub>v a; ListD a xs :\<^sub>v ListT a \<rbrakk> 
   \<Longrightarrow> ListD a (x # xs) :\<^sub>v ListT a"
  by (auto)

lemma dom_map_of: "x \<in> dom (map_of xs) \<Longrightarrow> \<exists> y. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:dom_def)

lemma ran_map_of: "y \<in> ran (map_of xs) \<Longrightarrow> \<exists> x. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:ran_def)

subsection {* Definedness of CML values *}

instantiation cmlv :: DEFINED_NE
begin

inductive defined_cmlv :: "cmlv \<Rightarrow> bool" where
BoolD_defn [simp]: "\<D> (BoolD x)" | NumD_defn [simp]: "\<D> (NumberD n)" | 
ChanD_defn [simp]: "\<D> (ChanD n t)" | CharD_defn [simp]: "\<D> (CharD x)" | 
EvD_defn [simp]: "\<D> (EvD n t v)" | NameD_defn [simp]: "\<D> (NameD n)" |
ListD_defn [intro]: "(\<forall> x \<in> set xs. \<D> x) \<Longrightarrow> \<D> (ListD a xs)" |
SetD_defn [intro]: "\<forall> x \<in>\<^sub>b xs. \<D> x \<Longrightarrow> \<D> (SetD a xs)" |
FuncD_defn [intro]: "\<forall> (x, y) \<in>\<^sub>b f. \<D> x \<and> \<D> y \<Longrightarrow> \<D> (FuncD a b f)" |
OptionD_None_defn [simp]: "\<D> (OptionD a None)" | 
OptionD_Some_defn [intro]: "\<D> x \<Longrightarrow> \<D> (OptionD a (Some x))" |
PairD_defn [intro]: "\<lbrakk> \<D> x; \<D> y \<rbrakk> \<Longrightarrow> \<D> (PairD x y)" | QuoteD_defn [simp]: "\<D> (QuoteD x)" | 
TagD_defn [intro]: "\<D> x \<Longrightarrow> \<D> (TagD n x)" | TokenD_defn [intro]: "\<D> x \<Longrightarrow> \<D> (TokenD x)" | 
TypeD_defn [simp]: "\<D> (TypeD t)" | UnitD_defn [simp]: "\<D> UnitD"

inductive_cases
  BotD_defn_cases [elim!]: "\<D> (BotD a)" and
  ListD_defn_cases [elim!]: "\<D> (ListD a xs)" and
  SetD_defn_cases [elim!]: "\<D> (SetD a xs)" and
  FuncD_defn_cases [elim!]: "\<D> (FuncD a b f)" and
  OptionD_defn_cases [elim!]: "\<D> (OptionD a (Some x))" and
  PairD_defn_cases [elim!]: "\<D> (PairD x y)" and
  TagD_defn_cases [elim!]: "\<D> (TagD n x)" and
  TokenD_defn_cases [elim!]: "\<D> (TokenD x)"
  
lemma defined_cmlv_simps [simp]:
  "\<D> (BotD a) = False"
  "\<D> (ListD a xs) = (\<forall> x \<in> set xs. \<D> x)"
  "\<D> (SetD a A) = (\<forall> x \<in>\<^sub>b A. \<D> x)"
  "\<D> (FuncD a b f) = (\<forall> (x, y) \<in>\<^sub>b f. \<D> x \<and> \<D> y)"
  "\<D> (OptionD a (Some x)) = \<D> x"
  "\<D> (PairD x y) = (\<D> x \<and> \<D> y)"
  "\<D> (TagD n x) = \<D> x"
  "\<D> (TokenD x) = \<D> x"
  by (auto)

instance  
  by (intro_classes, rule_tac x="UnitD" in exI, simp)

end

definition bdcarrier :: "cmlt \<Rightarrow> cmlv set" where
"bdcarrier t = {x \<in> bcarrier t. \<D> x}"

lemma bdcarrierI: "\<lbrakk> x :\<^sub>v a; \<D> x \<rbrakk> \<Longrightarrow> x \<in> bdcarrier a"
  by (simp add: bdcarrier_def bcarrier_def)

subsection {* Injecting basic values into cmlv *}

lemma vbasic_type_rel_uniq: "\<lbrakk> x :\<^sub>v a; x :\<^sub>v b \<rbrakk> \<Longrightarrow> a = b"
  apply (induct x arbitrary: a b)
  apply (auto)
  apply (metis PairD_type_cases)
  apply (force)
done

fun default_cmlt :: "cmlt \<Rightarrow> cmlv" where
"default_cmlt UnitT        = UnitD" |
"default_cmlt BoolT        = BoolD False" |
"default_cmlt NumberT      = NumberD 0" |
"default_cmlt CharT        = CharD (CHR ''x'')" |
"default_cmlt QuoteT       = QuoteD ''x''" |
"default_cmlt TokenT       = TokenD (BoolD False)" |
"default_cmlt ChanT        = ChanD (MkName ''x'' 0 NoSub) BoolT" |
"default_cmlt EventT       = EvD (MkName ''x'' 0 NoSub) BoolT (BoolD False)" |
"default_cmlt NameT        = NameD (MkName ''x'' 0 NoSub)" |
"default_cmlt TypeT        = TypeD BoolT" |
"default_cmlt (PairT s t)  = PairD (default_cmlt s) (default_cmlt t)" |
"default_cmlt (OptionT t)  = OptionD t None" |
"default_cmlt (SetT t)     = SetD t {}\<^sub>b" |
"default_cmlt (ListT t)    = ListD t []" |
"default_cmlt (FuncT s t)  = FuncD s t {}\<^sub>b" |
"default_cmlt (TagT n t)   = TagD n (default_cmlt t)"

lemma bBallI [intro!]: "(\<And> x. x \<in>\<^sub>b A \<Longrightarrow> P x) \<Longrightarrow> \<forall> x \<in>\<^sub>b A. P x"
  by (auto simp add: bBall_def)

lemma default_cmlt_type: 
  "default_cmlt t :\<^sub>v t"
  by (induct t, auto)

declare default_cmlt_type [typing]

lemma default_cmlt_defined: 
  "\<D> (default_cmlt t)"
  by (induct t, auto)

declare default_cmlt_defined [defined]

lemma cmlt_total: 
  "\<exists> v. v :\<^sub>v t \<and> \<D> v"
  apply (rule_tac x="default_cmlt t" in exI)
  apply (auto simp add:typing defined)
done

abbreviation "StringT \<equiv> ListT CharT"
abbreviation "StringD xs \<equiv> ListD CharT (map CharD xs)"
abbreviation "ProjStringD xs \<equiv> map (the \<circ> ProjCharD) (the (ProjListD xs))"

end
