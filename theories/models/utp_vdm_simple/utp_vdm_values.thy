(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_values.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)
theory utp_vdm_values
imports 
   Derive
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/Option_ord"
  "~~/src/HOL/Library/Monad_Syntax"
  utp_base
begin

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

no_notation
  residual_r (infixr "\<rightarrow>" 60)

section {* Main domain types *}

subsection {* Types *}

text {* We only introduce a single datatype for types, as the move between vdmv and
  vbasic should be transparent *}

datatype vdmt =
    FSetT vdmt ("\<fin>")
  | MapT vdmt vdmt 
  | ListT vdmt
  | OptionT vdmt
  | PairT vdmt vdmt 
  | RecordT "vdmt list"
  | BoolT ("\<bool>")
  | NatT ("\<nat>")
  | IntT ("\<int>")
  | RatT ("\<rat>")
  | RealT ("\<real>")
  | CharT
  | QuoteT
  | TokenT
  | SetT vdmt ("\<pow>")
  | FuncT vdmt vdmt (infixr "\<rightarrow>" 60)
  | NameT
  | TypeT

derive countable vdmt
(* derive linorder vdmt *)

instantiation vdmt :: linorder
begin

instance sorry

end

abbreviation "StringT \<equiv> ListT CharT"

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
  | ListI vdmt "vbasic list"
  | OptionI vdmt "vbasic option"
  | FinI vdmt "vbasic list"
  | BoolI bool
  | RecI "vbasic list"
  | MapI vdmt vdmt "(vbasic * vbasic) list" 
  | NameI "NAME"
  | TypeI "vdmt"
  | BotI "vdmt"

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

datatype vdmv = SetD "vbasic set"
                | FuncD "vbasic \<Rightarrow> vdmv"
                | BasicD "vbasic"

abbreviation BotD :: "vdmt \<Rightarrow> vdmv" ("\<bottom>\<^bsub>_\<^esub>") where
"BotD t \<equiv> BasicD (BotI t)"
abbreviation "TrueD \<equiv> BasicD (BoolI True)"
abbreviation "FalseD \<equiv> BasicD (BoolI False)"

subsection {* Injections *}

text {* We create interface constructors for finite sets, maps and records which
  use derived subtypes as inputs and therefore preserve canonicity of vbasic *}

definition FSetI :: "vdmt \<Rightarrow> vbasic fset \<Rightarrow> vbasic" where
"FSetI t vs = FinI t (flist vs)"

definition FinMapI :: "vdmt \<Rightarrow> vdmt \<Rightarrow> (vbasic, vbasic) fmap \<Rightarrow> vbasic" where
"FinMapI a b f = MapI a b (fmap_list f)"

(*
definition RecordI :: "(string \<rightharpoonup> vbasic) \<Rightarrow> vbasic" where
"RecordI f = RecI (sorted_list_of_set (map_graph f))"
*)

subsection {* Projections *}

text {* Projections functions produce Some value for a correctly formed values,
  and None otherwise *}

fun ProjFSetI :: "vbasic \<Rightarrow> (vbasic fset) option" where
"ProjFSetI (FinI t xs) = Some (fset xs)" |
"ProjFSetI x = None"

lemma FSetI_inv [simp]:
  "ProjFSetI (FSetI t xs) = Some xs"
  by (simp add:FSetI_def)

lemma FSetI_inj: "FSetI a f = FSetI b g \<Longrightarrow> f = g"
  apply (simp add:FSetI_def flist_def)
  apply (metis Rep_fset_finite Rep_fset_inject sorted_list_of_set_inj)
done

declare ProjFSetI.simps [simp del]

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
"ProjListI (ListI t xs) = Some xs" | "ProjListI xs = None"

fun ProjOptionI :: "vbasic \<Rightarrow> (vbasic option) option" where
"ProjOptionI (OptionI t x) = Some x" | "ProjOptionI x = None"

fun ProjRecI :: "vbasic \<Rightarrow> (vbasic list) option" where
"ProjRecI (RecI r) = Some r" | "ProjRecI xs = None"

fun ProjMapI :: "vbasic \<Rightarrow> ((vbasic* vbasic) list) option" where
"ProjMapI (MapI a b f) = Some f" | "ProjMapI x = None"

fun ProjFinMapI :: "vbasic \<Rightarrow> ((vbasic, vbasic) fmap) option" where
"ProjFinMapI (MapI a b xs) = Some (list_fmap xs)" | "ProjFinMapI x = None"

lemma FinMapI_inj [simp]: "FinMapI a b f = FinMapI a b g \<Longrightarrow> f = g"
  apply (auto simp add: FinMapI_def)
  apply (metis fmap_list_inv)
done

fun ProjNameI :: "vbasic \<Rightarrow> NAME option" where
"ProjNameI (NameI n) = Some n" | "ProjNameI _ = None"

fun ProjTypeI :: "vbasic \<Rightarrow> vdmt option" where
"ProjTypeI (TypeI t) = Some t" | "ProjTypeI _ = None"

section {* The type-system *}

subsection {* Basic value typing relation *}

inductive vbasic_type_rel :: "vbasic \<Rightarrow> vdmt \<Rightarrow> bool" (infix ":\<^sub>b" 50) 
and vbasic_type_list_rel :: "vbasic list \<Rightarrow> vdmt list \<Rightarrow> bool" (infix ":\<^sub>r" 50) where
BoolI_type[intro!]: "BoolI x :\<^sub>b BoolT" |
NatI_type[intro!]: "NatI x :\<^sub>b NatT" |
IntI_type[intro!]: "IntI x :\<^sub>b IntT" |
RatI_type[intro!]: "RatI x :\<^sub>b RatT" |
RealI_type[intro!]: "RealI x :\<^sub>b RealT" |
CharI_type[intro!]: "CharI x :\<^sub>b CharT" |
TokenI_type[intro!]: "TokenI x :\<^sub>b TokenT" |
QuoteI_type[intro!]: "QuoteI x :\<^sub>b QuoteT" |
ListI_type[intro!]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> ListI a xs :\<^sub>b ListT a" |
OptionI_Some_type[intro]: "\<lbrakk> x :\<^sub>b a \<rbrakk> \<Longrightarrow> OptionI a (Some x) :\<^sub>b OptionT a" |
OptionI_None_type[intro]: "OptionI a None :\<^sub>b OptionT a" |
FinI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a; sorted xs; distinct xs \<rbrakk> \<Longrightarrow> FinI a xs :\<^sub>b FSetT a" |
PairI_type[intro!]: "\<lbrakk> x :\<^sub>b a; y :\<^sub>b b \<rbrakk> \<Longrightarrow> PairI x y :\<^sub>b PairT a b" |
MapI_type[intro]: "\<lbrakk> \<forall>(x,y)\<in>set xs. x :\<^sub>b a \<and> y :\<^sub>b b; sorted (map fst xs); distinct (map fst xs) \<rbrakk> \<Longrightarrow> MapI a b xs :\<^sub>b MapT a b" |
RecI_type[intro]: "\<lbrakk> xs :\<^sub>r ts \<rbrakk>  \<Longrightarrow> RecI xs :\<^sub>b RecordT ts" |
NameI_type[intro]: "NameI n :\<^sub>b NameT" |
TypeI_type[intro]: "TypeI t :\<^sub>b TypeT" |
BotI_type[intro]: "BotI a :\<^sub>b a" |
Cons_type[intro]: "\<lbrakk> x :\<^sub>b t; xs :\<^sub>r ts \<rbrakk> \<Longrightarrow> (x # xs) :\<^sub>r (t # ts)" |
Nil_type[intro]: "[] :\<^sub>r []"

lemma fdom_fmempty [simp]: "fdom fmempty = \<lbrace>\<rbrace>"
  by (auto simp add:fdom.rep_eq fmempty.rep_eq)


inductive_cases 
  BoolI_type_cases [elim]: "BoolI x :\<^sub>b t" and
  BoolT_type_cases [elim!]: "x :\<^sub>b BoolT" and
  NatI_type_cases [elim]: "NatI x :\<^sub>b t" and
  NatT_type_cases [elim!]: "x :\<^sub>b NatT" and
  IntI_type_cases [elim]: "IntI x :\<^sub>b t" and
  IntT_type_cases [elim!]: "x :\<^sub>b IntT" and
  RatI_type_cases [elim]: "RatI x :\<^sub>b t" and
  RatT_type_cases [elim!]: "x :\<^sub>b RatT" and
  RealI_type_cases [elim]: "RealI x :\<^sub>b t" and
  RealT_type_cases [elim!]: "x :\<^sub>b RealT" and
  CharI_type_cases [elim]: "CharI x :\<^sub>b t" and
  CharT_type_cases [elim!]: "x :\<^sub>b CharT" and
  TokenI_type_cases [elim]: "TokenI x :\<^sub>b t" and
  TokenT_type_cases [elim!]: "x :\<^sub>b TokenT" and
  QuoteI_type_cases [elim]: "QuoteI x :\<^sub>b t" and
  QuoteT_type_cases [elim!]: "x :\<^sub>b QuoteT" and
  ListI_type_cases [elim]: "ListI a xs :\<^sub>b b" and
  ListT_type_cases [elim!]: "x :\<^sub>b ListT a" and
  OptionI_type_cases [elim]: "OptionI a x :\<^sub>b b" and
  OptionT_type_cases [elim]: "x :\<^sub>b OptionT a" and
  FinI_type_cases [elim]: "FinI a x :\<^sub>b b" and
  FinT_type_cases: "x :\<^sub>b FSetT a" and
  PairI_type_cases [elim]: "PairI x y :\<^sub>b t" and
  PairT_type_cases [elim!]: "x :\<^sub>b PairT a b" and
  MapI_type_cases [elim]: "MapI a b xs :\<^sub>b t" and
  MapT_type_cases [elim!]: "x :\<^sub>b MapT a b" and
  RecI_type_cases [elim]: "RecI xs :\<^sub>b t" and
  RecT_type_cases [elim!]: "x :\<^sub>b RecordT fs" and
  Cons_type_cases [elim!]: "x :\<^sub>r f # fs" and
  Cons_value_cases [elim!]: "x # xs :\<^sub>r ts" and
  Nil_type_cases [elim!]: "x :\<^sub>r []" and
  Nil_value_cases [elim!]: "[] :\<^sub>r ts" and
  FuncT_type_casesB [elim!]: "x :\<^sub>b a \<rightarrow> b" and
  SetT_type_casesB [elim!]: "x :\<^sub>b SetT a" and
  BotI_type_cases[elim]: "BotI a :\<^sub>b b" and
  NameI_type_cases [elim]: "NameI x :\<^sub>b t" and
  NameT_type_cases [elim!]: "x :\<^sub>b NameT" and
  TypeI_type_cases [elim]: "TypeI x :\<^sub>b t" and
  TypeT_type_cases [elim!]: "x :\<^sub>b TypeT"

definition bcarrier :: "vdmt \<Rightarrow> vbasic set" where
"bcarrier t = {x. x :\<^sub>b t}"

fun vbdefined :: "vbasic \<Rightarrow> bool" ("\<D>\<^sub>b") where
"\<D>\<^sub>b (BotI a) = False" |
"\<D>\<^sub>b (PairI x y) = (\<D>\<^sub>b x \<and> \<D>\<^sub>b y)" |
"\<D>\<^sub>b (BoolI x) = True" |
"\<D>\<^sub>b (NatI n) = True" |
"\<D>\<^sub>b (IntI n) = True" |
"\<D>\<^sub>b (RatI n) = True" |
"\<D>\<^sub>b (RealI n) = True" |
"\<D>\<^sub>b (CharI x) = True" |
"\<D>\<^sub>b (QuoteI x) = True" |
"\<D>\<^sub>b (TokenI x) = \<D>\<^sub>b x" |
"\<D>\<^sub>b (ListI a xs) = foldr (op \<and> \<circ> \<D>\<^sub>b) xs True" |
"\<D>\<^sub>b (OptionI a None) = True" |
"\<D>\<^sub>b (OptionI a (Some x)) = \<D>\<^sub>b x" |
"\<D>\<^sub>b (FinI a xs) = foldr (op \<and> \<circ> \<D>\<^sub>b) xs True" |
"\<D>\<^sub>b (RecI xs) = foldr (op \<and> \<circ> \<D>\<^sub>b) xs True" |
"\<D>\<^sub>b (MapI a b xs) = foldr (op \<and> \<circ> (\<lambda> x. \<D>\<^sub>b (fst x) \<and> \<D>\<^sub>b (snd x))) xs True" | 
"\<D>\<^sub>b (NameI n) = True" |
"\<D>\<^sub>b (TypeI t) = True"

lemma vbdefined_FSetI [simp]:
  "\<D>\<^sub>b (FSetI a xs) = (\<forall>x\<in>\<^sub>fxs. \<D>\<^sub>b x)"
proof -
  obtain ys where xsys: "xs = fset ys" and sys:"sorted ys" and dys:"distinct ys"
    by (metis flist_inv flist_props(1) flist_props(2))

  from sys dys have "\<D>\<^sub>b (FSetI a (fset ys)) = (\<forall>x\<in>\<^sub>ffset ys. \<D>\<^sub>b x)"
    apply (induct ys)
    apply (simp_all add:FSetI_def)
    apply (subgoal_tac "\<forall>x'\<in>\<^sub>ffset xs. x < x'")
    apply (auto)
    apply (metis less_le)
  done

  with xsys show ?thesis by simp
qed

fun vdefined :: "vdmv \<Rightarrow> bool" ("\<D>\<^sub>v") where
"\<D>\<^sub>v (BasicD x) = \<D>\<^sub>b x" |
"\<D>\<^sub>v (SetD xs) = (\<forall>x\<in>xs. \<D>\<^sub>b x)" |
"\<D>\<^sub>v (FuncD f) = True"

lemma Defined_nbot [simp]: "\<D>\<^sub>v x \<Longrightarrow> \<forall> a. x \<noteq> BotD a"
  by (auto)

definition vbtypes :: "vdmt set" where
"vbtypes = {t. \<exists> x. x :\<^sub>b t \<and> \<D>\<^sub>b x}"

definition vbvalues :: "vdmv set" where
"vbvalues = {BasicD x | x t. x :\<^sub>b t}"

lemma vbtypes_simps [simp]:
  "\<nat> \<in> vbtypes" "\<int> \<in> vbtypes" "\<rat> \<in> vbtypes"
  "\<bool> \<in> vbtypes" "CharT \<in> vbtypes" "TokenT \<in> vbtypes"
  "FSetT a \<in> vbtypes" "ListT a \<in> vbtypes"
  "a \<rightarrow> b \<notin> vbtypes"
  "SetT a \<notin> vbtypes"
 apply (auto simp add:vbtypes_def)
 apply (rule_tac x="TokenI (NatI 0)" in exI)
 apply (force)
 apply (rule_tac x="FSetI a \<lbrace>\<rbrace>" in exI)
 apply (force simp add:FSetI_def)
 apply (rule_tac x="ListI a []" in exI)
 apply (force)
done

text {* We introduce a couple of derived typing rules *}

lemma NilI_type[intro]: "ListI a [] :\<^sub>b ListT a"
  by auto

lemma ConsI_type[intro]: 
  "\<lbrakk> x :\<^sub>b a; ListI a xs :\<^sub>b ListT a \<rbrakk> 
   \<Longrightarrow> ListI a (x # xs) :\<^sub>b ListT a"
  by (auto)

lemma FSetI_type[intro]:
  assumes sty: "\<forall>x\<in>\<^sub>fxs. x :\<^sub>b a" 
  shows "FSetI a xs :\<^sub>b FSetT a"
  by (auto simp add:FSetI_def sty)

lemma FSetT_type_cases [elim!]: 
  "\<lbrakk> x :\<^sub>b FSetT t; \<And> xs. \<lbrakk> x = FSetI t xs; \<forall>x\<in>\<^sub>fxs. x :\<^sub>b t \<rbrakk> \<Longrightarrow> P; x = BotI (\<fin> t) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule FinT_type_cases)
  apply (auto simp add:FSetI_def)
  apply (metis fset_inv)
done

lemma FSetI_type_cases [elim]:
  "\<lbrakk>FSetI a xs :\<^sub>b t; \<And>a. \<lbrakk>t = FSetT a; \<forall>x\<in>\<^sub>fxs. x :\<^sub>b a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add:FSetI_def)

lemma FinMapI_type[intro]: 
  "\<lbrakk> \<forall> x\<in>Rep_fset(fdom f). x :\<^sub>b a; \<forall> y\<in>Rep_fset(fran f). y :\<^sub>b b \<rbrakk> \<Longrightarrow> FinMapI a b f :\<^sub>b MapT a b"
  by (auto intro!:MapI_type simp add:fdom_list fran_list FinMapI_def)

lemma dom_map_of: "x \<in> dom (map_of xs) \<Longrightarrow> \<exists> y. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:dom_def)

lemma ran_map_of: "y \<in> ran (map_of xs) \<Longrightarrow> \<exists> x. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:ran_def)

lemma FinMapI_type_cases [elim!]:
  "\<lbrakk>x :\<^sub>b MapT a b; x \<noteq> BotI (MapT a b); \<And>f. \<lbrakk>x = FinMapI a b f; \<forall> x\<in>Rep_fset(fdom f). x :\<^sub>b a; \<forall> y\<in>Rep_fset(fran f). y :\<^sub>b b \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
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

(* At the moment the type-system only supports functions of type vbtype \<Rightarrow> vdmt.
   Treatment of higher-order functions needs more work *)

inductive vdmt_rel :: "vdmv \<Rightarrow> vdmt \<Rightarrow> bool" (infix ":\<^sub>v" 50) where
SetD_type[intro]: "\<lbrakk> \<forall> x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> SetD xs :\<^sub>v SetT a" |
BasicD_type[intro]: "x :\<^sub>b a \<Longrightarrow> BasicD x :\<^sub>v a" |
FuncD_type[intro]: "\<lbrakk> \<And> x. x :\<^sub>b a \<Longrightarrow> f x :\<^sub>v b; f (BotI a) = BotD b \<rbrakk> \<Longrightarrow> FuncD f :\<^sub>v a \<rightarrow> b"

inductive_cases
  SetT_type_cases': "x :\<^sub>v SetT a" and
  SetD_type_cases[elim!]: "SetD x :\<^sub>v t" and
  FuncT_type_cases': "x :\<^sub>v a \<rightarrow> b" and
  FuncI_type_cases[elim!]: "FuncD f :\<^sub>v t" and
  BasicD_type_cases[elim]: "BasicD x :\<^sub>v t"

lemma SetT_type_cases [elim]: 
  "\<lbrakk> x :\<^sub>v SetT a; \<And> xs. \<lbrakk> x = SetD xs; \<forall>x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> P; x = BotD (SetT a) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule SetT_type_cases')
  apply (auto)
done

lemma FuncT_type_cases [elim]: 
  "\<lbrakk> x :\<^sub>v a \<rightarrow> b; \<And> f. \<lbrakk> x = FuncD f; \<forall> x. x :\<^sub>b a \<longrightarrow> f x :\<^sub>v b; f (BotI a) = BotD b \<rbrakk> \<Longrightarrow> P
   ; x = BotD (a \<rightarrow> b) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule FuncT_type_cases')
  apply (auto)
done

lemma vbtypes_type_cases [elim]: 
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes; \<And> x. \<lbrakk> a = BasicD x; x :\<^sub>b t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac a)
  apply (auto elim:BasicD_type_cases simp add:vbtypes_def)
done

lemma vbvalues_vbtype:
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes \<rbrakk> \<Longrightarrow> a \<in> vbvalues"
  by (auto simp add:vbvalues_def)

definition vcarrier :: "vdmt \<Rightarrow> vdmv set" where
"vcarrier t = {x. x :\<^sub>v t}"

lemma vcarrier [simp]: "x :\<^sub>v t \<Longrightarrow> x \<in> vcarrier t"
  by (simp add:vcarrier_def)

lemma vcarrier_simps [simp]:
  "vcarrier \<nat> = {BotD \<nat>} \<union> {BasicD (NatI x) | x . True}"
  "vcarrier \<int> = {BotD \<int>} \<union> {BasicD (IntI x) | x . True}"
  "vcarrier \<rat> = {BotD \<rat>} \<union> {BasicD (RatI x) | x . True}"
  "vcarrier \<bool> = {BotD \<bool>} \<union> {BasicD (BoolI x) | x . True}"
  by (auto simp add:vcarrier_def)

(*
lemma vbvalues_vbtypes [simp]: 
  "\<lbrakk> x \<in> vbvalues; x :\<^sub>v t \<rbrakk> \<Longrightarrow> t \<in> vbtypes"
  by (auto simp add:vbvalues_def vbtypes_def)
*)

(* Flatness of vbasic values *)

subsection {* Injecting basic values into vdmv *}

fun ProjBasicD :: "vdmv \<Rightarrow> vbasic" where
"ProjBasicD (BasicD x) = x" |
"ProjBasicD _ = BotI NatT"

fun IsBasicD :: "vdmv \<Rightarrow> bool" where
"IsBasicD (BasicD x) = True" |
"IsBasicD _ = False"

lemma ProjBasicD_inv [simp] :
  "IsBasicD x \<Longrightarrow> BasicD (ProjBasicD x) = x"
  by (case_tac x, simp_all)

(*
definition vstrictify :: "(vbasic \<Rightarrow> vdmv) \<Rightarrow> (vbasic \<Rightarrow> vdmv)" where
"vstrictify f = (\<lambda> x. if (x = BotI) then BotD else f x)"

lemma vstrictify_idem [simp]: 
  "vstrictify (vstrictify f) = vstrictify f"
  by (auto simp add:vstrictify_def)

lemma vstrictify_bot [simp]:
  "vstrictify f BotI = BotD"
  by (simp add:vstrictify_def)

lemma vstrictify_type [intro]:
  "f x :\<^sub>v t \<Longrightarrow> vstrictify f x :\<^sub>v t"
  by (auto simp add:vstrictify_def)

abbreviation SFuncD :: "(vbasic \<Rightarrow> vdmv) \<Rightarrow> vdmv" where
"SFuncD f \<equiv> FuncD (vstrictify f)"

definition vbasic_fun1 :: "(vbasic \<Rightarrow> vbasic) \<Rightarrow> vdmv" where
"vbasic_fun1 f \<equiv> SFuncD (BasicD \<circ> f)"

definition vbasic_fun2 :: "(vbasic \<Rightarrow> vbasic \<Rightarrow> vbasic) \<Rightarrow> vdmv" where
"vbasic_fun2 f \<equiv> SFuncD (\<lambda> x. SFuncD (\<lambda> y. BasicD (f x y)))"
*)

primrec ProjFuncD :: "vdmv \<Rightarrow> (vbasic \<Rightarrow> vdmv)" where
"ProjFuncD (FuncD f) = f"

fun IsFuncD :: "vdmv \<Rightarrow> bool" where
"IsFuncD (FuncD f) = True" |
"IsFuncD _ = False"

primrec ProjSetD :: "vdmv \<Rightarrow> vbasic set" where
"ProjSetD (SetD x) = x"

fun IsSetD :: "vdmv \<Rightarrow> bool" where
"IsSetD (SetD x) = True" |
"IsSetD _ = False"

lemma vbasic_type_rel_uniq: "\<lbrakk> x :\<^sub>b a; x :\<^sub>b b \<rbrakk> \<Longrightarrow> a = b"
  and "\<lbrakk> xs :\<^sub>r as; xs :\<^sub>r bs \<rbrakk> \<Longrightarrow> as = bs"
  apply (induct x and xs arbitrary: a b and as bs)
  apply (auto)
  apply (metis PairI_type_cases)
  apply (force)
done

thm vbasic_type_rel_uniq

end