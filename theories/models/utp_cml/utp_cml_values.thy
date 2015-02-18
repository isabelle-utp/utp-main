(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_values.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Value Domain *}

theory utp_cml_values
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
  residual_r (infixr "\<rightarrow>" 60)

subsection {* CML types *}

datatype vbasict =
    BoolBT
  | ChanBT
  | CharBT
  | EventBT
  | FSetBT vbasict 
  | ListBT vbasict
  | MapBT vbasict vbasict 
  | NameBT
  | NumberBT
  | OptionBT vbasict
  | PairBT vbasict vbasict 
  | QuoteBT
  | TagBT "string" "vbasict"
  | TokenBT
  | TypeBT
  | UnitBT

datatype cmlt =
    BasicT vbasict
  | SetT vbasict ("\<pow>")
  | FuncT vbasict cmlt (infixr "\<rightarrow>" 60)

derive countable vbasict
derive linorder vbasict
derive countable cmlt
derive linorder cmlt

subsection {* CML domain types *}

text {* We introduce countable values using a normal datatype. This representation
  is not fully canonical, as we use lists to represents sets, maps and records.
  However, we later introduce constructors for these which use the correct types
  and thus ensure canonicity. *}

datatype vbasic 
  = BoolI bool
  | BotI "vbasict"
  | ChanI uname "vbasict"
  | CharI "char"
  | EvI uname "vbasict" "vbasic"
  | FinI vbasict "vbasic list"
  | ListI vbasict "vbasic list"
  | MapI vbasict vbasict 
         "(vbasic * vbasic) list" 
  | NameI uname
  | NumberI "real"
  | OptionI vbasict "vbasic option"
  | PairI vbasic vbasic
  | QuoteI "string" 
  | TagI "string" "vbasic"
  | TokenI vbasic
  | TypeI "vbasict"
  | UnitI

datatype cmlv 
  = SetD vbasict "vbasic set"
  | FuncD vbasict cmlt 
          "vbasic \<Rightarrow> cmlv"
  | BasicD vbasic
  | BotD' cmlt

text {* Deriving the linear order necessarily takes a while *}

derive linorder vbasic

fun BotD :: "cmlt \<Rightarrow> cmlv" ("\<bottom>\<^bsub>_\<^esub>") where
"BotD (BasicT t) = BasicD (BotI t)" |
"BotD t = BotD' t"

abbreviation "TrueD \<equiv> BasicD (BoolI True)"
abbreviation "FalseD \<equiv> BasicD (BoolI False)"

subsection {* Injections *}

text {* We create interface constructors for finite sets, maps and records which
  use derived subtypes as inputs and therefore preserve canonicity of vbasic *}

primrec ProjBasicT :: "cmlt \<Rightarrow> vbasict" where
"ProjBasicT (BasicT t) = t"

abbreviation "LiftT f t \<equiv> BasicT (f (ProjBasicT t))"
abbreviation "BoolT  \<equiv> BasicT BoolBT"
abbreviation "NumberT \<equiv> BasicT NumberBT"
abbreviation "CharT   \<equiv> BasicT CharBT"
abbreviation "QuoteT  \<equiv> BasicT QuoteBT"
abbreviation "TokenT  \<equiv> BasicT TokenBT"
abbreviation "ChanT   \<equiv> BasicT ChanBT"
abbreviation "EventT  \<equiv> BasicT EventBT"
abbreviation "NameT   \<equiv> BasicT NameBT"
abbreviation "TypeT   \<equiv> BasicT TypeBT"
abbreviation "FSetT   \<equiv> LiftT FSetBT"
abbreviation "ListT   \<equiv> LiftT ListBT"
abbreviation "StringT \<equiv> ListT CharT"

definition FSetI :: "vbasict \<Rightarrow> vbasic fset \<Rightarrow> vbasic" where
"FSetI t vs = FinI t (flist vs)"

definition FinMapI :: "vbasict \<Rightarrow> vbasict \<Rightarrow> (vbasic, vbasic) fmap \<Rightarrow> vbasic" where
"FinMapI a b f = MapI a b (fmap_list f)"

subsection {* Projections *}

text {* Projections functions produce Some value for a correctly formed values,
  and None otherwise *}
  
fun ProjFSetI :: "vbasic \<Rightarrow> (vbasic fset) option" where
"ProjFSetI (FinI t xs) = Some (finset xs)" |
"ProjFSetI x = None"

lemma FSetI_inv [simp]:
  "ProjFSetI (FSetI t xs) = Some xs"
  by (simp add:FSetI_def)

lemma FSetI_inj: "FSetI a f = FSetI b g \<Longrightarrow> f = g"
  apply (simp add:FSetI_def flist_def)
  apply (metis finite_fset fset_inject sorted_list_of_set_inj)
done

declare ProjFSetI.simps [simp del]

fun ProjPairI :: "vbasic \<Rightarrow> (vbasic * vbasic) option" where
"ProjPairI (PairI x y) = Some (x,y)" | "ProjPairI x = None"

fun ProjCharI :: "vbasic \<Rightarrow> char option" where
"ProjCharI (CharI x) = Some x" | "ProjCharI x = None"

fun ProjBoolI :: "vbasic \<Rightarrow> bool option" where
"ProjBoolI (BoolI x) = Some x" | "ProjBoolI x = None"

fun ProjListI :: "vbasic \<Rightarrow> (vbasic list) option" where
"ProjListI (ListI t xs) = Some xs" | "ProjListI xs = None"

fun ProjOptionI :: "vbasic \<Rightarrow> (vbasic option) option" where
"ProjOptionI (OptionI t x) = Some x" | "ProjOptionI x = None"

fun ProjTagI :: "vbasic \<Rightarrow> (string * vbasic) option" where
"ProjTagI (TagI n r) = Some (n,r)" | "ProjTagI xs = None"

fun ProjMapI :: "vbasic \<Rightarrow> ((vbasic* vbasic) list) option" where
"ProjMapI (MapI a b f) = Some f" | "ProjMapI x = None"

fun ProjFinMapI :: "vbasic \<Rightarrow> ((vbasic, vbasic) fmap) option" where
"ProjFinMapI (MapI a b xs) = Some (list_fmap xs)" | "ProjFinMapI x = None"

lemma FinMapI_inj [simp]: "FinMapI a b f = FinMapI a b g \<Longrightarrow> f = g"
  apply (auto simp add: FinMapI_def)
  apply (metis fmap_list_inv)
done

fun ProjNameI :: "vbasic \<Rightarrow> uname option" where
"ProjNameI (NameI n) = Some n" | "ProjNameI _ = None"

fun ProjTypeI :: "vbasic \<Rightarrow> vbasict option" where
"ProjTypeI (TypeI t) = Some t" | "ProjTypeI _ = None"

fun ProjBasicD :: "cmlv \<Rightarrow> vbasic" where
"ProjBasicD (BasicD x) = x" |
"ProjBasicD _ = BotI NumberBT"

fun IsBasicD :: "cmlv \<Rightarrow> bool" where
"IsBasicD (BasicD x) = True" |
"IsBasicD _ = False"

lemma ProjBasicD_inv [simp] :
  "IsBasicD x \<Longrightarrow> BasicD (ProjBasicD x) = x"
  by (case_tac x, simp_all)

lemma ProjBasicD_o_BasicD [simp]: 
  "ProjBasicD \<circ> BasicD = id"
  by (auto)

primrec ProjFuncD :: "cmlv \<Rightarrow> (vbasic \<Rightarrow> cmlv)" where
"ProjFuncD (FuncD a b f) = f"

fun IsFuncD :: "cmlv \<Rightarrow> bool" where
"IsFuncD (FuncD a b f) = True" |
"IsFuncD _ = False"

primrec ProjSetD :: "cmlv \<Rightarrow> vbasic set" where
"ProjSetD (SetD a x) = x"

fun IsSetD :: "cmlv \<Rightarrow> bool" where
"IsSetD (SetD a x) = True" |
"IsSetD _ = False"

subsection {* CML basic type-system *}

inductive vbasic_type_rel :: 
  "vbasic \<Rightarrow> vbasict \<Rightarrow> bool" (infix ":\<^sub>b" 50) where
BoolI_type[intro!]: "BoolI x :\<^sub>b BoolBT" |
BotI_type[intro]: "BotI a :\<^sub>b a" |
ChanI_type[intro!]: "ChanI n t :\<^sub>b ChanBT" |
CharI_type[intro!]: "CharI x :\<^sub>b CharBT" |
EvI_type[intro!]: "v :\<^sub>b t \<Longrightarrow> EvI n t v :\<^sub>b EventBT" |
FinI_type[intro]: 
  "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a; sorted xs; distinct xs \<rbrakk> 
   \<Longrightarrow> FinI a xs :\<^sub>b FSetBT a" |
ListI_type[intro!]: 
  "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a \<rbrakk> 
   \<Longrightarrow> ListI a xs :\<^sub>b ListBT a" |
MapI_type[intro]: 
  "\<lbrakk> \<forall>(x,y)\<in>set xs. x :\<^sub>b a \<and> y :\<^sub>b b
   ; sorted (map fst xs)
   ; distinct (map fst xs) \<rbrakk> 
   \<Longrightarrow> MapI a b xs :\<^sub>b MapBT a b" |
NameI_type[intro]: "NameI n :\<^sub>b NameBT" |
NumberI_type[intro!]: "NumberI x :\<^sub>b NumberBT" |
OptionI_None_type[intro]: 
  "OptionI a None :\<^sub>b OptionBT a" |
OptionI_Some_type[intro]: 
  "\<lbrakk> x :\<^sub>b a \<rbrakk> 
   \<Longrightarrow> OptionI a (Some x) :\<^sub>b OptionBT a" |
PairI_type[intro!]: 
  "\<lbrakk> x :\<^sub>b a; y :\<^sub>b b \<rbrakk> 
  \<Longrightarrow> PairI x y :\<^sub>b PairBT a b" |
QuoteI_type[intro!]: "QuoteI x :\<^sub>b QuoteBT" |
TagI_type[intro]: 
  "x :\<^sub>b t \<Longrightarrow> TagI n x :\<^sub>b TagBT n t" |
TokenI_type[intro!]: "TokenI x :\<^sub>b TokenBT" |
TypeI_type[intro]: "TypeI t :\<^sub>b TypeBT" |
UnitI_type[intro!]: "UnitI :\<^sub>b UnitBT" 

inductive_cases 
  BoolI_type_cases [elim]: "BoolI x :\<^sub>b t" and
  BoolT_type_cases [elim!]: "x :\<^sub>b BoolBT" and
  BotI_type_cases[elim]: "BotI a :\<^sub>b b" and
  ChanI_type_cases [elim]: "ChanI n t :\<^sub>b a" and
  ChanT_type_cases [elim!]: "x :\<^sub>b ChanBT" and
  CharI_type_cases [elim]: "CharI x :\<^sub>b t" and
  CharT_type_cases [elim!]: "x :\<^sub>b CharBT" and
  EvI_type_cases [elim]: "EvI n t v :\<^sub>b a" and
  EventT_type_cases [elim!]: "x :\<^sub>b EventBT" and
  FinI_type_cases [elim]: "FinI a x :\<^sub>b b" and
  FinT_type_cases: "x :\<^sub>b FSetBT a" and
  ListI_type_cases [elim]: "ListI a xs :\<^sub>b b" and
  ListT_type_cases [elim!]: "x :\<^sub>b ListBT a" and
  MapI_type_cases [elim]: "MapI a b xs :\<^sub>b t" and
  MapT_type_cases [elim!]: "x :\<^sub>b MapBT a b" and
  NameI_type_cases [elim]: "NameI x :\<^sub>b t" and
  NameT_type_cases [elim!]: "x :\<^sub>b NameBT" and
  NumberI_type_cases [elim]: "NumberI x :\<^sub>b t" and
  NumberT_type_cases [elim!]: "x :\<^sub>b NumberBT" and
  OptionI_type_cases [elim]: "OptionI a x :\<^sub>b b" and
  OptionT_type_cases [elim]: "x :\<^sub>b OptionBT a" and
  PairI_type_cases [elim]: "PairI x y :\<^sub>b t" and
  PairT_type_cases [elim!]: "x :\<^sub>b PairBT a b" and
  QuoteI_type_cases [elim]: "QuoteI x :\<^sub>b t" and
  QuoteT_type_cases [elim!]: "x :\<^sub>b QuoteBT" and
  TagI_type_cases [elim]: "TagI n x :\<^sub>b t" and
  TagT_type_cases [elim!]: "x :\<^sub>b TagBT n t" and
  TokenI_type_cases [elim]: "TokenI x :\<^sub>b t" and
  TokenT_type_cases [elim!]: "x :\<^sub>b TokenBT" and
  TypeI_type_cases [elim]: "TypeI x :\<^sub>b t" and
  TypeT_type_cases [elim!]: "x :\<^sub>b TypeBT" and
  UnitI_type_cases [elim]: "UnitI :\<^sub>b t" and
  UnitT_type_cases [elim!]: "x :\<^sub>b UnitBT"

definition bcarrier :: "vbasict \<Rightarrow> vbasic set" where
"bcarrier t = {x. x :\<^sub>b t}"

subsubsection {* Derived Typing Rules *}

lemma NilI_type[intro]: "ListI a [] :\<^sub>b ListBT a"
  by auto

lemma ConsI_type[intro]: 
  "\<lbrakk> x :\<^sub>b a; ListI a xs :\<^sub>b ListBT a \<rbrakk> 
   \<Longrightarrow> ListI a (x # xs) :\<^sub>b ListBT a"
  by (auto)

lemma FSetI_type[intro]:
  assumes "\<forall>x|\<in>|xs. x :\<^sub>b a" 
  shows "FSetI a xs :\<^sub>b FSetBT a"
  using assms by (force simp add:FSetI_def)

lemma finset_set_member:
  "x |\<in>| finset(xs) \<Longrightarrow> x \<in> set(xs)"
  by (metis finset.rep_eq fnmember_intro)
  
lemma FSetT_type_cases [elim!]:
  assumes
  "x :\<^sub>b FSetBT t" 
  "\<And> xs. \<lbrakk> x = FSetI t xs; \<forall>x|\<in>|xs. x :\<^sub>b t \<rbrakk> \<Longrightarrow> P"
  "x = BotI (FSetBT t) \<Longrightarrow> P" 
  shows "P"
proof (cases rule: FinT_type_cases[OF assms(1)])
  assume "x = BotI (FSetBT t)"
  thus P by (fact assms(3))
next
  fix xs
  assume "x = FinI t xs" "\<forall>x\<in>set xs. x :\<^sub>b t" "sorted xs" "distinct xs"
  thus P
    apply (rule_tac assms(2)[of "finset xs"])
    apply (metis FSetI_def fset_inv)
    apply (metis fBallI finset_set_member)
  done
qed

lemma FSetI_type_cases [elim]:
  "\<lbrakk>FSetI a xs :\<^sub>b t; \<And>a. \<lbrakk>t = FSetBT a; \<forall>x|\<in>|xs. x :\<^sub>b a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (metis FSetI_def FinI_type_cases fBallI flist_set fmember.rep_eq)

lemma FinMapI_type[intro]: 
  "\<lbrakk> \<forall> x|\<in>|fdom f. x :\<^sub>b a; \<forall> y|\<in>|fran f. y :\<^sub>b b \<rbrakk> \<Longrightarrow> FinMapI a b f :\<^sub>b MapBT a b"
  by (force intro!:MapI_type simp add:fdom_list fran_list FinMapI_def)

lemma dom_map_of: "x \<in> dom (map_of xs) \<Longrightarrow> \<exists> y. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:dom_def)

lemma ran_map_of: "y \<in> ran (map_of xs) \<Longrightarrow> \<exists> x. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:ran_def)

lemma FinMapI_type_cases [elim!]:
  "\<lbrakk> x :\<^sub>b MapBT a b; x \<noteq> BotI (MapBT a b); 
    \<And>f. \<lbrakk>x = FinMapI a b f; \<forall> x|\<in>|fdom f. x :\<^sub>b a; \<forall> y|\<in>|fran f. y :\<^sub>b b \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (case_tac x, auto elim!:MapI_type_cases)
  apply (simp add:FinMapI_def fdom_def fran_def)
  apply (subgoal_tac "list = fmap_list (list_fmap list)")
  apply (subgoal_tac "\<forall>x\<in>dom (Rep_fmap (list_fmap list)). x :\<^sub>b a")
  apply (subgoal_tac "\<forall>y\<in>ran (Rep_fmap (list_fmap list)). y :\<^sub>b b")
  sledgehammer
  apply (metis)
  apply (simp add: list_fmap_def finite_dom_map_of)
  apply (metis Rep_fmap_inverse list_fmap.rep_eq ran_map_of split_conv)
  apply (metis (lifting) dom_map_of list_fmap.rep_eq split_conv)
  apply (force dest: ran_map_of)
done

subsection {* Definedness of CML values *}

instantiation vbasic :: DEFINED_NE
begin

fun Defined_vbasic :: "vbasic \<Rightarrow> bool" where
"\<D> (BoolI x) = True" |
"\<D> (BotI a) = False" |
"\<D> (ChanI n t) = True" |
"\<D> (CharI x) = True" |
"\<D> (EvI n t v) = True" |
"\<D> (FinI a xs) = (\<forall> x \<in> set xs. \<D> x)" |
"\<D> (ListI a xs) = (\<forall> x \<in> set xs. \<D> x)" |
"\<D> (MapI a b xs) = 
  (\<forall> (x,y) \<in> set xs. \<D> x \<and> \<D> y)" | 
"\<D> (NameI n) = True" |
"\<D> (NumberI n) = True" |
"\<D> (OptionI a None) = True" |
"\<D> (OptionI a (Some x)) = \<D> x" |
"\<D> (PairI x y) = (\<D> x \<and> \<D> y)" |
"\<D> (QuoteI x) = True" |
"\<D> (TagI n x) = \<D> x" |
"\<D> (TokenI x) = \<D> x" |
"\<D> (TypeI t) = True" |
"\<D> UnitI = True"

instance 
  by (intro_classes, rule_tac x="NumberI 0" in exI, simp)

end

lemma vbdefined_FSetI [simp]:
  "\<D> (FSetI a xs) = (\<forall>x\<in>\<^sub>fxs. \<D> x)"
proof -
  obtain ys where xsys: "xs = fset ys" and sys:"sorted ys" and dys:"distinct ys"
    by (metis flist_inv flist_props(1) flist_props(2))

  from sys dys have "\<D> (FSetI a (fset ys)) = (\<forall>x\<in>\<^sub>ffset ys. \<D> x)"
    apply (induct ys)
    apply (simp_all add:FSetI_def)
    apply (subgoal_tac "\<forall>x'\<in>\<^sub>ffset xs. x < x'")
    apply (auto)
    apply (metis less_le)
  done

  with xsys show ?thesis by simp
qed

instantiation cmlv :: DEFINED_NE
begin

fun Defined_cmlv :: "cmlv \<Rightarrow> bool" where
"\<D> (BasicD x) = \<D> x" |
"\<D> (SetD t xs) = (\<forall>x\<in>xs. \<D> x)" |
"\<D> (FuncD s t f) = True" |
"\<D> (BotD' s) = False"

instance 
  by (intro_classes, rule_tac x="BasicD (NumberI 0)" in exI, simp)
end

lemma Defined_nbot [simp]: "\<D> x \<Longrightarrow> x \<noteq> BotD a"
  by (case_tac a, auto)

definition "vbtypes = (BasicT ` UNIV)"

lemma ProjBasicT_inv [simp]: 
  "t \<in> vbtypes \<Longrightarrow> BasicT (ProjBasicT t) = t"
  by (auto simp add:vbtypes_def)

definition vbvalues :: "cmlv set" where
"vbvalues = {BasicD x | x t. x :\<^sub>b t}"

lemma FinMapI_defined [defined]:
  "\<D> (FinMapI a b f) = (\<langle>fdom f\<rangle>\<^sub>f \<subseteq> DEFINED \<and> \<langle>fran f\<rangle>\<^sub>f \<subseteq> DEFINED)"
  apply (auto simp add:FinMapI_def fdom.rep_eq fran.rep_eq)
  apply (drule_tac x="(x, y)" in bspec)
  apply (metis fmap_list_inv list_fmap.rep_eq map_of_SomeD)
  apply (simp add:DEFINED_def)
  apply (auto simp add:ran_def)[1]
  apply (drule_tac x="(a, x)" in bspec)
  apply (metis fmap_list_inv list_fmap.rep_eq map_of_SomeD)
  apply (simp add:DEFINED_def)
  apply (force dest:fmap_list_fdom_fran simp add:fdom.rep_eq fran.rep_eq DEFINED_def)+
done
  
subsection {* CML full typing relation *}

(* At the moment the type-system only supports functions of type vbtype \<Rightarrow> cmlt.
   Treatment of higher-order functions needs more work *)

inductive cmlt_rel :: "cmlv \<Rightarrow> cmlt \<Rightarrow> bool" (infix ":\<^sub>v" 50) where
SetD_type[intro]: "\<lbrakk> \<forall> x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> SetD a xs :\<^sub>v SetT a" |
BasicD_type[intro]: "x :\<^sub>b a \<Longrightarrow> BasicD x :\<^sub>v BasicT a" |
FuncD_type[intro]: "\<lbrakk> \<And> x. \<lbrakk> x :\<^sub>b a; \<D> x \<rbrakk> \<Longrightarrow> f x :\<^sub>v b 
                    ; \<And> x. \<not> \<D> x \<Longrightarrow> f x = BotD b \<rbrakk> \<Longrightarrow> FuncD a b f :\<^sub>v a \<rightarrow> b" |
BotD'_type[intro]: "a \<notin> range BasicT \<Longrightarrow> BotD' a :\<^sub>v a"

inductive_cases
  SetT_type_cases'[elim!]: "x :\<^sub>v SetT a" and
  SetD_type_cases[elim]: "SetD a x :\<^sub>v t" and
  FuncT_type_cases'[elim!]: "x :\<^sub>v a \<rightarrow> b" and
  FuncI_type_cases[elim]: "FuncD a b f :\<^sub>v t" and
  BasicD_type_cases[elim]: "BasicD x :\<^sub>v t" and
  BasicT_type_cases[elim!]: "x :\<^sub>v BasicT t" and
  BotD'_type_cases[elim]: "BotD' a :\<^sub>v t"

lemma BotD_type [intro]:
  "BotD t :\<^sub>v t"
  by (case_tac t, auto)

lemma BotD_defined [simp]:
  "\<not> \<D> (BotD t)"
  by (case_tac t, simp_all)

lemma SetT_type_cases [elim]: 
  "\<lbrakk> x :\<^sub>v SetT a; \<And> xs. \<lbrakk> x = SetD a xs; \<forall>x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> P; x = BotD (SetT a) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule SetT_type_cases')
  apply (metis ProjBasicT.simps)
  apply (metis BotD.simps(2))
done

lemma FuncT_type_cases [elim]: 
  "\<lbrakk> x :\<^sub>v a \<rightarrow> b; \<And> f. \<lbrakk> x = FuncD a b f; \<And> x. \<lbrakk> x :\<^sub>b a; \<D> x \<rbrakk> \<Longrightarrow> f x :\<^sub>v b ; \<And> x. \<not> \<D> x \<Longrightarrow> f x = BotD b \<rbrakk> \<Longrightarrow> P
   ; x = BotD (a \<rightarrow> b) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule FuncT_type_cases')
  apply (auto)
done

definition vcarrier :: "cmlt \<Rightarrow> cmlv set" where
"vcarrier t = {x. x :\<^sub>v t}"

lemma vcarrier [simp]: "x :\<^sub>v t \<Longrightarrow> x \<in> vcarrier t"
  by (simp add:vcarrier_def)

lemma vcarrier_simps [simp]:
  "vcarrier BoolT = {BotD BoolT} \<union> {BasicD (BoolI x) | x . True}"
  apply (simp_all add:vcarrier_def)
  apply (force)+
done

(* Flatness of vbasic values *)

subsection {* Injecting basic values into cmlv *}

lemma vbasic_type_rel_uniq: "\<lbrakk> x :\<^sub>b a; x :\<^sub>b b \<rbrakk> \<Longrightarrow> a = b"
(*  and "\<lbrakk> xs :\<^sub>r as; xs :\<^sub>r bs \<rbrakk> \<Longrightarrow> as = bs" *)
  apply (induct x arbitrary: a b)
  apply (auto)
  apply (metis PairI_type_cases)
  apply (force)
done

fun default_vbasict :: "vbasict \<Rightarrow> vbasic" where
"default_vbasict UnitBT        = UnitI" |
"default_vbasict BoolBT        = BoolI False" |
"default_vbasict NumberBT      = NumberI 0" |
"default_vbasict CharBT        = CharI (CHR ''x'')" |
"default_vbasict QuoteBT       = QuoteI ''x''" |
"default_vbasict TokenBT       = TokenI (BoolI False)" |
"default_vbasict ChanBT        = ChanI (MkName ''x'' 0 NoSub) BoolBT" |
"default_vbasict EventBT       = EvI (MkName ''x'' 0 NoSub) BoolBT (BoolI False)" |
"default_vbasict NameBT        = NameI (MkName ''x'' 0 NoSub)" |
"default_vbasict TypeBT        = TypeI BoolBT" |
"default_vbasict (PairBT s t)  = PairI (default_vbasict s) (default_vbasict t)" |
"default_vbasict (OptionBT t)  = OptionI t None" |
"default_vbasict (FSetBT t)    = FSetI t \<lbrace>\<rbrace>" |
"default_vbasict (ListBT t)    = ListI t []" |
"default_vbasict (MapBT s t)   = MapI s t []" |
"default_vbasict (TagBT n t)   = TagI n (default_vbasict t)"

lemma default_vbasict_type: 
  "default_vbasict t :\<^sub>b t"
  by (induct t, auto)

declare default_vbasict_type [typing]

lemma default_vbasict_defined: 
  "\<D> (default_vbasict t)"
  by (induct t, auto)

declare default_vbasict_defined [defined]

lemma vbasict_total: 
  "\<exists> v. v :\<^sub>b t \<and> \<D> v"
  apply (rule_tac x="default_vbasict t" in exI)
  apply (auto simp add:typing defined)
done
  
fun default_cmlt :: "cmlt \<Rightarrow> cmlv" where
"default_cmlt (SetT t)       = SetD t {}" |
"default_cmlt (FuncT s t)    = FuncD s t(\<lambda> x. if (\<D> x) then default_cmlt t else BotD t)" |
"default_cmlt (BasicT t)     = BasicD (default_vbasict t)"

lemma default_cmlt_type: 
  "default_cmlt t :\<^sub>v t"
  by (induct t, auto intro:typing)

declare default_cmlt_type(1) [typing]

lemma default_cmltt_defined: 
  "\<D> (default_cmlt t)"
  by (induct t, auto intro:defined)

declare default_cmltt_defined(1) [defined]

lemma cmlt_total: 
  "\<exists> v. v :\<^sub>v t \<and> \<D> v"
  apply (rule_tac x="default_cmlt t" in exI)
  apply (auto simp add:typing defined)
done

end