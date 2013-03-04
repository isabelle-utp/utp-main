(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_values.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)
theory utp_vdm_values
imports 
   Derive
  "~~/src/HOL/Library/Char_ord" 
  "~~/src/HOL/Library/Monad_Syntax" 
  "../../core/utp_var"
  "../../utils/Library_extra"

begin

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

section {* Main domain types *}

subsection {* Types *}

text {* We only introduce a single datatype for types, as the move between vdmval and
  vbasic should be transparent *}

datatype vdmtype =
    FSetT vdmtype
  | MapT vdmtype vdmtype 
  | ListT vdmtype
  | OptionT vdmtype
  | PairT vdmtype vdmtype 
  | RecordT "vdmtype list"
  | BoolT ("\<bool>")
  | NatT ("\<nat>")
  | IntT ("\<int>")
  | RatT ("\<rat>")
  | CharT
  | QuoteT
  | TokenT
  | TVarT nat
  | SetT vdmtype 
  | FuncT vdmtype vdmtype (infixr "→" 60)
  | NameT
  | TypeT

derive countable vdmtype
(* derive linorder vdmtype *)
instantiation vdmtype :: linorder
begin

instance sorry

end

subsection {* Basic (countable) values *}

text {* We introduce countable values using a normal datatype. This representation
  is not fully canonical, as we use lists to represents sets, maps and records.
  However, we later introduce constructors for these which use the correct types
  and thus ensure canonicity. *}
datatype vbasic 
  = PairI vbasic vbasic
  | NatI "nat"
  | IntI "int" 
  | RatI "rat" 
  | RealI "real"
  | CharI "char"
  | QuoteI "string" 
  | TokenI vbasic
  | ListI "vbasic list" 
  | OptionI "vbasic option"
  | FinI "vbasic list"
  | BoolI bool
  | RecI "vbasic list"
  | MapI "(vbasic * vbasic) list" 
  | NameI "NAME"
  | TypeI "vdmtype"


(* Deriving the linear order necessarily takes a while *)


(* derive linorder vbasic *)

instantiation vbasic :: linorder
begin

instance sorry

end


subsection {* Full values *}

text {* Full values are represented using a domain, which adds functions, 
  uncountable sets, reals etc. to what we already have. Domains are harder to
  manipulate than datatypes so we only use them where necessary. Functions
  and sets must have a continuous representation, but since vbasic is "flat"
  any function whose domain is vbasic is automatically continuous.
*}

datatype vdmval = SetV "vbasic set"
                | FuncV "vbasic \<Rightarrow> vdmval"
                | BasicV "vbasic"
                | BotV

abbreviation "TrueV \<equiv> BasicV (BoolI True)"
abbreviation "FalseV \<equiv> BasicV (BoolI False)"

subsection {* Injections *}

text {* We create interface constructors for finite sets, maps and records which
  use derived subtypes as inputs and therefore preserve canonicity of vbasic *}

definition FSetI :: "vbasic fset \<Rightarrow> vbasic" where
"FSetI vs = FinI (flist vs)"

definition FinMapI :: "(vbasic, vbasic) fmap \<Rightarrow> vbasic" where
"FinMapI f = MapI (fmap_list f)"

(*
definition RecordI :: "(string \<rightharpoonup> vbasic) \<Rightarrow> vbasic" where
"RecordI f = RecI (sorted_list_of_set (map_graph f))"
*)

subsection {* Projections *}

text {* Projections functions produce Some value for a correctly formed values,
  and None otherwise *}

fun ProjFSetI :: "vbasic \<Rightarrow> (vbasic fset) option" where
"ProjFSetI (FinI xs) = Some (fset xs)" |
"ProjFSetI x = None"

fun ProjPairI :: "vbasic \<Rightarrow> (vbasic * vbasic) option" where
"ProjPairI (PairI x y) = Some (x,y)" | "ProjPairI x = None"

fun ProjRatI :: "vbasic \<Rightarrow> rat option" where
"ProjRatI (RatI x) = Some x" | "ProjRatI x = None"

fun ProjIntI :: "vbasic \<Rightarrow> int option" where
"ProjIntI (IntI x) = Some x" | "ProjIntI x = None"

fun ProjCharI :: "vbasic \<Rightarrow> char option" where
"ProjCharI (CharI x) = Some x" | "ProjCharI x = None"

fun ProjBoolI :: "vbasic \<Rightarrow> bool option" where
"ProjBoolI (BoolI x) = Some x" | "ProjBoolI x = None"

fun ProjListI :: "vbasic \<Rightarrow> (vbasic list) option" where
"ProjListI (ListI xs) = Some xs" | "ProjListI xs = None"

fun ProjOptionI :: "vbasic \<Rightarrow> (vbasic option) option" where
"ProjOptionI (OptionI x) = Some x" | "ProjOptionI x = None"

fun ProjRecI :: "vbasic \<Rightarrow> (vbasic list) option" where
"ProjRecI (RecI r) = Some r" | "ProjRecI xs = None"

fun ProjMapI :: "vbasic \<Rightarrow> ((vbasic* vbasic) list) option" where
"ProjMapI (MapI f) = Some f" | "ProjMapI x = None"

fun ProjFinMapI :: "vbasic \<Rightarrow> ((vbasic, vbasic) fmap) option" where
"ProjFinMapI (MapI xs) = Some (list_fmap xs)" | "ProjFinMapI x = None"

lemma FinMapI_inj [simp]: "FinMapI f = FinMapI g \<Longrightarrow> f = g"
  apply (auto simp add: FinMapI_def)
  apply (metis fmap_list_inv)
done

fun ProjNameI :: "vbasic \<Rightarrow> NAME option" where
"ProjNameI (NameI n) = Some n" | "ProjNameI _ = None"

fun ProjTypeI :: "vbasic \<Rightarrow> vdmtype option" where
"ProjTypeI (TypeI t) = Some t" | "ProjTypeI _ = None"

section {* The type-system *}

subsection {* Basic value typing relation *}

inductive vbasic_type_rel :: "vbasic \<Rightarrow> vdmtype \<Rightarrow> bool" (infix ":\<^sub>b" 50) 
  and vbasic_type_list_rel :: "vbasic list \<Rightarrow> vdmtype list \<Rightarrow> bool" (infix ":\<^sub>r" 50) where
BoolI_type[intro]: "BoolI x :\<^sub>b BoolT" |
NatI_type[intro]: "NatI x :\<^sub>b NatT" |
IntI_type[intro]: "IntI x :\<^sub>b IntT" |
RatI_type[intro]: "RatI x :\<^sub>b RatT" |
CharI_type[intro]: "CharI x :\<^sub>b CharT" |
TokenI_type[intro]: "TokenI x :\<^sub>b TokenT" |
QuoteI_type[intro]: "QuoteI x :\<^sub>b QuoteT" |
ListI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> ListI xs :\<^sub>b ListT a" |
OptionI_Some_type[intro]: "\<lbrakk> x :\<^sub>b a \<rbrakk> \<Longrightarrow> OptionI (Some x) :\<^sub>b OptionT a" |
OptionI_None_type[intro]: "OptionI None :\<^sub>b OptionT a" |
FinI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a; sorted xs; distinct xs \<rbrakk> \<Longrightarrow> FinI xs :\<^sub>b FSetT a" |
PairI_type[intro]: "\<lbrakk> x :\<^sub>b a; y :\<^sub>b b \<rbrakk> \<Longrightarrow> PairI x y :\<^sub>b PairT a b" |
MapI_type[intro]: "\<lbrakk> \<forall>(x,y)\<in>set xs. x :\<^sub>b a \<and> y :\<^sub>b b; sorted (map fst xs); distinct (map fst xs) \<rbrakk> \<Longrightarrow> MapI xs :\<^sub>b MapT a b" |
RecI_type[intro]: "\<lbrakk> xs :\<^sub>r ts \<rbrakk>  \<Longrightarrow> RecI xs :\<^sub>b RecordT ts" |
NameI_type[intro]: "NameI n :\<^sub>b NameT" |
TypeI_type[intro]: "TypeI t :\<^sub>b TypeT" |
Cons_type[intro]: "\<lbrakk> x :\<^sub>b t; xs :\<^sub>r ts \<rbrakk> \<Longrightarrow> (x # xs) :\<^sub>r (t # ts)" |
Nil_type[intro]: "[] :\<^sub>r []"

inductive_cases 
  BoolI_type_cases [elim]: "BoolI x :\<^sub>b t" and
  BoolT_type_cases [elim!]: "x :\<^sub>b BoolT" and
  NatI_type_cases [elim]: "NatI x :\<^sub>b t" and
  NatT_type_cases [elim!]: "x :\<^sub>b NatT" and
  IntI_type_cases [elim]: "IntI x :\<^sub>b t" and
  IntT_type_cases [elim!]: "x :\<^sub>b IntT" and
  RatI_type_cases [elim]: "RatI x :\<^sub>b t" and
  RatT_type_cases [elim!]: "x :\<^sub>b RatT" and
  CharI_type_cases [elim]: "CharI x :\<^sub>b t" and
  CharT_type_cases [elim!]: "x :\<^sub>b CharT" and
  TokenI_type_cases [elim]: "TokenI x :\<^sub>b t" and
  TokenT_type_cases [elim!]: "x :\<^sub>b TokenT" and
  QuoteI_type_cases [elim]: "QuoteI x :\<^sub>b t" and
  QuoteT_type_cases [elim!]: "x :\<^sub>b QuoteT" and
  ListI_type_cases [elim]: "ListI xs :\<^sub>b t" and
  ListT_type_cases [elim!]: "x :\<^sub>b ListT a" and
  OptionI_type_cases [elim]: "OptionI x :\<^sub>b t" and
  OptionT_type_cases [elim]: "x :\<^sub>b OptionT a" and
  FinI_type_cases [elim]: "FinI x :\<^sub>b t" and
  FinT_type_cases [elim!]: "x :\<^sub>b FSetT a" and
  PairI_type_cases [elim]: "PairI x y :\<^sub>b t" and
  PairT_type_cases [elim!]: "x :\<^sub>b PairT a b" and
  MapI_type_cases [elim]: "MapI xs :\<^sub>b t" and
  MapT_type_cases [elim!]: "x :\<^sub>b MapT a b" and
  RecI_type_cases [elim]: "RecI xs :\<^sub>b t" and
  RecT_type_cases [elim!]: "x :\<^sub>b RecordT fs" and
  Cons_type_cases [elim!]: "x :\<^sub>r f # fs" and
  Nil_type_cases [elim!]: "x :\<^sub>r []" and
  FuncT_type_casesB [elim!]: "x :\<^sub>b a → b" and
  SetT_type_casesB [elim!]: "x :\<^sub>b SetT a"

definition bcarrier :: "vdmtype \<Rightarrow> vbasic set" where
"bcarrier t = {x. x :\<^sub>b t}"

definition vbtypes :: "vdmtype set" where
"vbtypes = {t. \<exists> x. x :\<^sub>b t}"

definition vbvalues :: "vdmval set" where
"vbvalues = {BotV} \<union> {BasicV x | x t. x :\<^sub>b t}"

lemma vbtypes_simps [simp]:
  "\<nat> \<in> vbtypes" "\<int> \<in> vbtypes" "\<rat> \<in> vbtypes"
  "\<bool> \<in> vbtypes" "CharT \<in> vbtypes" "TokenT \<in> vbtypes"
  "a → b \<notin> vbtypes"
  "SetT a \<notin> vbtypes"
  by (auto simp add:vbtypes_def)

text {* We introduce a couple of derived typing rules *}

lemma NilI_type[intro]: "ListI [] :\<^sub>b ListT a"
  by auto

lemma ConsI_type[intro]: 
  "\<lbrakk> x :\<^sub>b a; ListI xs :\<^sub>b ListT a \<rbrakk> \<Longrightarrow> ListI (x # xs) :\<^sub>b ListT a"
  by (force intro!: ListI_type)

lemma FSetI_type[intro]:
  assumes sty: "\<forall>x\<in>set (flist xs). x :\<^sub>b a" 
  shows "FSetI xs :\<^sub>b FSetT a"
  by (auto simp add:FSetI_def sty)

lemma FinMapI_type[intro]: 
  "\<lbrakk> \<forall> x\<in>Rep_fset(fdom f). x :\<^sub>b a; \<forall> y\<in>Rep_fset(fran f). y :\<^sub>b b \<rbrakk> \<Longrightarrow> FinMapI f :\<^sub>b MapT a b"
  by (auto intro!:MapI_type simp add:fdom_list fran_list FinMapI_def)

lemma dom_map_of: "x \<in> dom (map_of xs) \<Longrightarrow> \<exists> y. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:dom_def)

lemma ran_map_of: "y \<in> ran (map_of xs) \<Longrightarrow> \<exists> x. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:ran_def)

lemma FinMapI_type_cases [elim!]:
  "\<lbrakk>x :\<^sub>b MapT a b; \<And>f. \<lbrakk>x = FinMapI f; \<forall> x\<in>Rep_fset(fdom f). x :\<^sub>b a; \<forall> y\<in>Rep_fset(fran f). y :\<^sub>b b \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (case_tac x, auto elim!:MapI_type_cases)
  apply (simp add:FinMapI_def fdom_def fran_def)
  apply (subgoal_tac "list = fmap_list (list_fmap list)")
  apply (subgoal_tac "\<forall>x\<in>dom (Rep_fmap (list_fmap list)). x :\<^sub>b a")
  apply (subgoal_tac "\<forall>y\<in>ran (Rep_fmap (list_fmap list)). y :\<^sub>b b")
  apply (metis)
  apply (simp add: list_fmap_def finite_dom_map_of)
  apply (force dest: ran_map_of)
  apply (simp add: list_fmap_def finite_dom_map_of)
  apply (rule ballI)
  apply (drule dom_map_of)
  apply (force)
  apply (simp)
done
  
subsection {* Full value typing relation *}

(* At the moment the type-system only supports functions of type vbtype \<Rightarrow> vdmtype.
   Treatment of higher-order functions needs more work *)

inductive vdmtype_rel :: "vdmval \<Rightarrow> vdmtype \<Rightarrow> bool" (infix ":\<^sub>v" 50) where
BotV_type[intro]: "BotV :\<^sub>v a" |
SetV_type[intro]: "\<lbrakk> \<forall> x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> SetV xs :\<^sub>v SetT a" |
BasicV_type[intro]: "x :\<^sub>b a \<Longrightarrow> BasicV x :\<^sub>v a" |
FuncV_type[intro]: "\<lbrakk> \<forall> x. x :\<^sub>b a \<longrightarrow> f x :\<^sub>v b \<rbrakk> \<Longrightarrow> FuncV f :\<^sub>v a → b"

inductive_cases
  BotV_type_cases[elim]: "BotV :\<^sub>v a" and
  SetT_type_cases[elim]: "x :\<^sub>v SetT a" and
  SetV_type_cases[elim!]: "SetV x :\<^sub>v t" and
  FuncT_type_cases[elim!]: "x :\<^sub>v a → b" and
  FuncI_type_cases[elim!]: "FuncV f :\<^sub>v t" and
  BasicV_type_cases[elim]: "BasicV x :\<^sub>v t"

lemma vbtypes_type_cases [elim]: 
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes; \<And> x. \<lbrakk> a = BasicV x; x :\<^sub>b t \<rbrakk> \<Longrightarrow> P; a = BotV \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac a)
  apply (auto elim:BasicV_type_cases simp add:vbtypes_def)
done

lemma vbvalues_vbtype:
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes \<rbrakk> \<Longrightarrow> a \<in> vbvalues"
  by (auto simp add:vbvalues_def)

definition vcarrier :: "vdmtype \<Rightarrow> vdmval set" where
"vcarrier t = {x. x :\<^sub>v t}"

lemma vcarrier [simp]: "x :\<^sub>v t \<Longrightarrow> x \<in> vcarrier t"
  by (simp add:vcarrier_def)

lemma vcarrier_simps [simp]:
  "vcarrier \<nat> = {BotV} \<union> {BasicV (NatI x) | x . True}"
  "vcarrier \<int> = {BotV} \<union> {BasicV (IntI x) | x . True}"
  "vcarrier \<rat> = {BotV} \<union> {BasicV (RatI x) | x . True}"
  "vcarrier \<bool> = {BotV} \<union> {BasicV (BoolI x) | x . True}"
  by (auto simp add:vcarrier_def)

(*
lemma vbvalues_vbtypes [simp]: 
  "\<lbrakk> x \<in> vbvalues; x :\<^sub>v t \<rbrakk> \<Longrightarrow> t \<in> vbtypes"
  by (auto simp add:vbvalues_def vbtypes_def)
*)

(* Flatness of vbasic values *)

subsection {* Injecting basic values into vdmval *}

fun ProjBasicV :: "vdmval \<Rightarrow> vbasic option" where
"ProjBasicV (BasicV x) = Some x" |
"ProjBasicV _ = None"

fun IsBasicV :: "vdmval \<Rightarrow> bool" where
"IsBasicV (BasicV x) = True" |
"IsBasicV _ = False"

lemma ProjBasicV_inv [simp] :
  "IsBasicV x \<Longrightarrow> BasicV (the (ProjBasicV x)) = x"
  by (case_tac x, simp_all)

definition vbasic_fun1 :: "(vbasic \<Rightarrow> vbasic) \<Rightarrow> vdmval" where
"vbasic_fun1 f \<equiv> FuncV (BasicV \<circ> f)"

definition vbasic_fun2 :: "(vbasic \<Rightarrow> vbasic \<Rightarrow> vbasic) \<Rightarrow> vdmval" where
"vbasic_fun2 f \<equiv> FuncV (\<lambda> x. FuncV (\<lambda> y. BasicV (f x y)))"

primrec ProjFuncV :: "vdmval \<Rightarrow> (vbasic \<Rightarrow> vdmval)" where
"ProjFuncV (FuncV f) = f"

fun IsFuncV :: "vdmval \<Rightarrow> bool" where
"IsFuncV (FuncV f) = True" |
"IsFuncV _ = False"

primrec ProjSetV :: "vdmval \<Rightarrow> vbasic set" where
"ProjSetV (SetV x) = x"

fun IsSetV :: "vdmval \<Rightarrow> bool" where
"IsSetV (SetV x) = True" |
"IsSetV _ = False"

end