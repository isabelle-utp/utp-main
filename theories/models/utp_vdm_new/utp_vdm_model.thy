(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_model.thy                                                    *)
(* Authors: Original CML model by Simon Foster, University of York (UK)       *)
(*          Adapted to VDM by Luis Diogo Couto, Aarhus University (DK)        *)
(******************************************************************************)

header {* VDM Value Domain *}

theory utp_vdm_model
imports 
  Derive
  Char_ord
  Option_ord
  Monad_Syntax
  utp_base
  utp_designs
  utp_definedness
begin

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

no_notation
  residual_r (infixr "\<rightarrow>" 60) and
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

subsection {* VDM types *}

datatype vdmt =
    BoolT
  | CharT
  | SetT vdmt 
  | FuncT vdmt vdmt
  | ListT vdmt
  | NameT
  | NumberT
  | OptionT vdmt
  | PairT vdmt vdmt 
  | QuoteT
  | TagT "string" "vdmt"
  | TokenT
  | TypeT
  | UnitT

(*
derive countable vdmt
derive linorder vdmt
*)

subsection {* VDM domain types *}

text {* We introduce countable values using a normal datatype. This representation
  is not fully canonical, as we use lists to represents sets, maps and records.
  However, we later introduce constructors for these which use the correct types
  and thus ensure canonicity. *}

datatype_new vdmv 
  = BoolD bool
  | BotD vdmt
  | CharD "char"
  | SetD vdmt "vdmv bset"
  | ListD vdmt "vdmv list"
  | FuncD vdmt vdmt 
         "(vdmv * vdmv) bset" 
  | NameD uname
  | NumberD "real"
  | OptionD vdmt "vdmv option"
  | PairD vdmv vdmv
  | QuoteD "string" 
  | TagD "string" "vdmv"
  | TokenD vdmv
  | TypeD "vdmt"
  | UnitD

abbreviation "TrueD \<equiv> BoolD True"
abbreviation "FalseD \<equiv> BoolD False"

subsection {* Injections *}

text {* We create interface constructors for finite sets, maps and records which
  use derived subtypes as inputs and therefore preserve canonicity of vbasic *}

fun ProjPairD :: "vdmv \<Rightarrow> (vdmv * vdmv) option" where
"ProjPairD (PairD x y) = Some (x,y)" | "ProjPairD x = None"

fun ProjCharD :: "vdmv \<Rightarrow> char option" where
"ProjCharD (CharD x) = Some x" | "ProjCharD x = None"

fun ProjBoolD :: "vdmv \<Rightarrow> bool option" where
"ProjBoolD (BoolD x) = Some x" | "ProjBoolD x = None"

fun ProjListD :: "vdmv \<Rightarrow> (vdmv list) option" where
"ProjListD (ListD t xs) = Some xs" | "ProjListD xs = None"

fun ProjOptionD :: "vdmv \<Rightarrow> (vdmv option) option" where
"ProjOptionD (OptionD t x) = Some x" | "ProjOptionD x = None"

fun ProjTagD :: "vdmv \<Rightarrow> (string * vdmv) option" where
"ProjTagD (TagD n r) = Some (n,r)" | "ProjTagD xs = None"

fun ProjFuncD :: "vdmv \<Rightarrow> ((vdmv * vdmv) bset) option" where
"ProjFuncD (FuncD a b f) = Some f" | "ProjFuncD x = None"

fun IsFuncD :: "vdmv \<Rightarrow> bool" where
"IsFuncD (FuncD a b f) = True" |
"IsFuncD _ = False"

primrec ProjSetD :: "vdmv \<Rightarrow> vdmv bset" where
"ProjSetD (SetD a x) = x"

fun IsSetD :: "vdmv \<Rightarrow> bool" where
"IsSetD (SetD a x) = True" |
"IsSetD _ = False"

subsection {* VDM basic type-system *}
 
inductive vdmv_type_rel :: 
  "vdmv \<Rightarrow> vdmt \<Rightarrow> bool" (infix ":\<^sub>v" 50) where
BoolD_type[intro!]: "BoolD x :\<^sub>v BoolT" |
BotD_type[intro]: "BotD a :\<^sub>v a" |
CharD_type[intro!]: "CharD x :\<^sub>v CharT" |
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
  CharD_type_cases [elim]: "CharD x :\<^sub>v t" and
  CharT_type_cases [elim!]: "x :\<^sub>v CharT" and
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

definition bcarrier :: "vdmt \<Rightarrow> vdmv set" where
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

subsection {* Definedness of VDM values *}

instantiation vdmv :: DEFINED_NE
begin

inductive defined_vdmv :: "vdmv \<Rightarrow> bool" where
BoolD_defn [simp]: "\<D> (BoolD x)" | 
NumD_defn [simp]: "\<D> (NumberD n)" |  
CharD_defn [simp]: "\<D> (CharD x)" | 
NameD_defn [simp]: "\<D> (NameD n)" |
ListD_defn [intro]: "(\<forall> x \<in> set xs. \<D> x) \<Longrightarrow> \<D> (ListD a xs)" |
SetD_defn [intro]: "\<forall> x \<in>\<^sub>b xs. \<D> x \<Longrightarrow> \<D> (SetD a xs)" |
FuncD_defn [intro]: "\<forall> (x, y) \<in>\<^sub>b f. \<D> x \<and> \<D> y \<Longrightarrow> \<D> (FuncD a b f)" |
OptionD_None_defn [simp]: "\<D> (OptionD a None)" | 
OptionD_Some_defn [intro]: "\<D> x \<Longrightarrow> \<D> (OptionD a (Some x))" |
PairD_defn [intro]: "\<lbrakk> \<D> x; \<D> y \<rbrakk> \<Longrightarrow> \<D> (PairD x y)" | 
QuoteD_defn [simp]: "\<D> (QuoteD x)" | 
TagD_defn [intro]: "\<D> x \<Longrightarrow> \<D> (TagD n x)" | 
TokenD_defn [intro]: "\<D> x \<Longrightarrow> \<D> (TokenD x)" | 
TypeD_defn [simp]: "\<D> (TypeD t)" | 
UnitD_defn [simp]: "\<D> UnitD"

inductive_cases
  BotD_defn_cases [elim!]: "\<D> (BotD a)" and
  ListD_defn_cases [elim!]: "\<D> (ListD a xs)" and
  SetD_defn_cases [elim!]: "\<D> (SetD a xs)" and
  FuncD_defn_cases [elim!]: "\<D> (FuncD a b f)" and
  OptionD_defn_cases [elim!]: "\<D> (OptionD a (Some x))" and
  PairD_defn_cases [elim!]: "\<D> (PairD x y)" and
  TagD_defn_cases [elim!]: "\<D> (TagD n x)" and
  TokenD_defn_cases [elim!]: "\<D> (TokenD x)"
  
lemma defined_vdmv_simps [simp]:
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

definition bdcarrier :: "vdmt \<Rightarrow> vdmv set" where
"bdcarrier t = {x \<in> bcarrier t. \<D> x}"

lemma bdcarrierI: "\<lbrakk> x :\<^sub>v a; \<D> x \<rbrakk> \<Longrightarrow> x \<in> bdcarrier a"
  by (simp add: bdcarrier_def bcarrier_def)

subsection {* Injecting basic values into vdmv *}

lemma vbasic_type_rel_uniq: "\<lbrakk> x :\<^sub>v a; x :\<^sub>v b \<rbrakk> \<Longrightarrow> a = b"
  apply (induct x arbitrary: a b)
  apply (auto)
  apply (metis PairD_type_cases)
  apply (force)
done

fun default_vdmt :: "vdmt \<Rightarrow> vdmv" where
"default_vdmt UnitT        = UnitD" |
"default_vdmt BoolT        = BoolD False" |
"default_vdmt NumberT      = NumberD 0" |
"default_vdmt CharT        = CharD (CHR ''x'')" |
"default_vdmt QuoteT       = QuoteD ''x''" |
"default_vdmt TokenT       = TokenD (BoolD False)" |
"default_vdmt NameT        = NameD (MkName ''x'' 0 NoSub)" |
"default_vdmt TypeT        = TypeD BoolT" |
"default_vdmt (PairT s t)  = PairD (default_vdmt s) (default_vdmt t)" |
"default_vdmt (OptionT t)  = OptionD t None" |
"default_vdmt (SetT t)     = SetD t {}\<^sub>b" |
"default_vdmt (ListT t)    = ListD t []" |
"default_vdmt (FuncT s t)  = FuncD s t {}\<^sub>b" |
"default_vdmt (TagT n t)   = TagD n (default_vdmt t)"

lemma bBallI [intro!]: "(\<And> x. x \<in>\<^sub>b A \<Longrightarrow> P x) \<Longrightarrow> \<forall> x \<in>\<^sub>b A. P x"
  by (auto simp add: bBall_def)

lemma default_vdmt_type: 
  "default_vdmt t :\<^sub>v t"
  by (induct t, auto)

declare default_vdmt_type [typing]

lemma default_vdmt_defined: 
  "\<D> (default_vdmt t)"
  by (induct t, auto)

declare default_vdmt_defined [defined]

lemma vdmt_total: 
  "\<exists> v. v :\<^sub>v t \<and> \<D> v"
  apply (rule_tac x="default_vdmt t" in exI)
  apply (auto simp add:typing defined)
done

abbreviation "StringT \<equiv> ListT CharT"
abbreviation "StringD xs \<equiv> ListD CharT (map CharD xs)"
abbreviation "ProjStringD xs \<equiv> map (the \<circ> ProjCharD) (the (ProjListD xs))"

end
