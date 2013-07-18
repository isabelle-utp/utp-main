(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_values.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)
theory utp_vdm_values
imports 
  Derive
  Char_ord
  Option_ord
  Monad_Syntax
  "../../utp_base"
begin

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

no_notation
  residual_r (infixr "\<rightarrow>" 60)

section {* Main domain types *}

subsection {* Types *}

text {* We only introduce a single datatype for types, as the move between vdmv and
  vbasic should be transparent *}

datatype vbasict =
    FSetBT vbasict ("\<fin>")
  | MapBT vbasict vbasict 
  | ListBT vbasict
  | OptionBT vbasict
  | PairBT vbasict vbasict 
  | RecordBT "vbasict list"
  | BoolBT ("\<bool>")
  | NatBT ("\<nat>")
  | IntBT ("\<int>")
  | RatBT ("\<rat>")
  | RealBT ("\<real>")
  | CharBT
  | QuoteBT
  | TokenBT
  | EventBT
  | NameBT
  | TypeBT

datatype vdmt =
    BasicT vbasict
  | SetT vbasict ("\<pow>")
  | FuncT vbasict vdmt (infixr "\<rightarrow>" 60)

derive countable vbasict
derive countable vdmt
(* derive linorder vdmt *)

instantiation vdmt :: linorder
begin

instance sorry

end

primrec ProjBasicT :: "vdmt \<Rightarrow> vbasict" where
"ProjBasicT (BasicT t) = t"

(* declare [[coercion BasicT]] *)

abbreviation "LiftT f t \<equiv> BasicT (f (ProjBasicT t))"

abbreviation "BoolT  \<equiv> BasicT BoolBT"
abbreviation "NatT   \<equiv> BasicT NatBT"
abbreviation "IntT   \<equiv> BasicT IntBT"
abbreviation "RatT   \<equiv> BasicT RatBT"
abbreviation "RealT  \<equiv> BasicT RealBT"
abbreviation "CharT  \<equiv> BasicT CharBT"
abbreviation "QuoteT \<equiv> BasicT QuoteBT"
abbreviation "TokenT \<equiv> BasicT TokenBT"
abbreviation "EventT \<equiv> BasicT EventBT"
abbreviation "NameT  \<equiv> BasicT NameBT"
abbreviation "TypeT  \<equiv> BasicT TypeBT"

abbreviation "FSetT \<equiv> LiftT FSetBT"
abbreviation "ListT \<equiv> LiftT ListBT"

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
  | EvI NAME "vbasict" "vbasic"
  | ListI vbasict "vbasic list"
  | OptionI vbasict "vbasic option"
  | FinI vbasict "vbasic list"
  | BoolI bool
  | RecI "vbasic list"
  | MapI vbasict vbasict "(vbasic * vbasic) list" 
  | NameI "NAME"
  | TypeI "vbasict"
  | BotI "vbasict"


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

datatype vdmv = SetD vbasict "vbasic set"
                | FuncD  vbasict vdmt "vbasic \<Rightarrow> vdmv"
                | BasicD "vbasic"
                | BotD' "vdmt"

fun BotD :: "vdmt \<Rightarrow> vdmv" ("\<bottom>\<^bsub>_\<^esub>") where
"BotD (BasicT t) = BasicD (BotI t)" |
"BotD t = BotD' t"

abbreviation "TrueD \<equiv> BasicD (BoolI True)"
abbreviation "FalseD \<equiv> BasicD (BoolI False)"

subsection {* Injections *}

text {* We create interface constructors for finite sets, maps and records which
  use derived subtypes as inputs and therefore preserve canonicity of vbasic *}

definition FSetI :: "vbasict \<Rightarrow> vbasic fset \<Rightarrow> vbasic" where
"FSetI t vs = FinI t (flist vs)"

definition FinMapI :: "vbasict \<Rightarrow> vbasict \<Rightarrow> (vbasic, vbasic) fmap \<Rightarrow> vbasic" where
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

fun ProjTypeI :: "vbasic \<Rightarrow> vbasict option" where
"ProjTypeI (TypeI t) = Some t" | "ProjTypeI _ = None"

section {* The type-system *}

subsection {* Basic value typing relation *}

inductive vbasic_type_rel :: "vbasic \<Rightarrow> vbasict \<Rightarrow> bool" (infix ":\<^sub>b" 50) 
and vbasic_type_list_rel :: "vbasic list \<Rightarrow> vbasict list \<Rightarrow> bool" (infix ":\<^sub>r" 50) where
BoolI_type[intro!]: "BoolI x :\<^sub>b BoolBT" |
NatI_type[intro!]: "NatI x :\<^sub>b NatBT" |
IntI_type[intro!]: "IntI x :\<^sub>b IntBT" |
RatI_type[intro!]: "RatI x :\<^sub>b RatBT" |
RealI_type[intro!]: "RealI x :\<^sub>b RealBT" |
CharI_type[intro!]: "CharI x :\<^sub>b CharBT" |
TokenI_type[intro!]: "TokenI x :\<^sub>b TokenBT" |
EvI_type[intro!]: "v :\<^sub>b t \<Longrightarrow> EvI n t v :\<^sub>b EventBT" |
QuoteI_type[intro!]: "QuoteI x :\<^sub>b QuoteBT" |
ListI_type[intro!]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> ListI a xs :\<^sub>b ListBT a" |
OptionI_Some_type[intro]: "\<lbrakk> x :\<^sub>b a \<rbrakk> \<Longrightarrow> OptionI a (Some x) :\<^sub>b OptionBT a" |
OptionI_None_type[intro]: "OptionI a None :\<^sub>b OptionBT a" |
FinI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a; sorted xs; distinct xs \<rbrakk> \<Longrightarrow> FinI a xs :\<^sub>b FSetBT a" |
PairI_type[intro!]: "\<lbrakk> x :\<^sub>b a; y :\<^sub>b b \<rbrakk> \<Longrightarrow> PairI x y :\<^sub>b PairBT a b" |
MapI_type[intro]: "\<lbrakk> \<forall>(x,y)\<in>set xs. x :\<^sub>b a \<and> y :\<^sub>b b; sorted (map fst xs); distinct (map fst xs) \<rbrakk> \<Longrightarrow> MapI a b xs :\<^sub>b MapBT a b" |
RecI_type[intro]: "\<lbrakk> xs :\<^sub>r ts \<rbrakk>  \<Longrightarrow> RecI xs :\<^sub>b RecordBT ts" |
NameI_type[intro]: "NameI n :\<^sub>b NameBT" |
TypeI_type[intro]: "TypeI t :\<^sub>b TypeBT" |
BotI_type[intro]: "BotI a :\<^sub>b a" |
Cons_type[intro]: "\<lbrakk> x :\<^sub>b t; xs :\<^sub>r ts \<rbrakk> \<Longrightarrow> (x # xs) :\<^sub>r (t # ts)" |
Nil_type[intro]: "[] :\<^sub>r []"

lemma fdom_fmempty [simp]: "fdom fmempty = \<lbrace>\<rbrace>"
  by (auto simp add:fdom.rep_eq fmempty.rep_eq)

inductive_cases 
  BoolI_type_cases [elim]: "BoolI x :\<^sub>b t" and
  BoolT_type_cases [elim!]: "x :\<^sub>b BoolBT" and
  NatI_type_cases [elim]: "NatI x :\<^sub>b t" and
  NatT_type_cases [elim!]: "x :\<^sub>b NatBT" and
  IntI_type_cases [elim]: "IntI x :\<^sub>b t" and
  IntT_type_cases [elim!]: "x :\<^sub>b IntBT" and
  RatI_type_cases [elim]: "RatI x :\<^sub>b t" and
  RatT_type_cases [elim!]: "x :\<^sub>b RatBT" and
  RealI_type_cases [elim]: "RealI x :\<^sub>b t" and
  RealT_type_cases [elim!]: "x :\<^sub>b RealBT" and
  CharI_type_cases [elim]: "CharI x :\<^sub>b t" and
  CharT_type_cases [elim!]: "x :\<^sub>b CharBT" and
  TokenI_type_cases [elim]: "TokenI x :\<^sub>b t" and
  TokenT_type_cases [elim!]: "x :\<^sub>b TokenBT" and
  EvI_type_cases [elim]: "EvI n t v :\<^sub>b a" and
  EventT_type_cases [elim!]: "x :\<^sub>b EventBT" and
  QuoteI_type_cases [elim]: "QuoteI x :\<^sub>b t" and
  QuoteT_type_cases [elim!]: "x :\<^sub>b QuoteBT" and
  ListI_type_cases [elim]: "ListI a xs :\<^sub>b b" and
  ListT_type_cases [elim!]: "x :\<^sub>b ListBT a" and
  OptionI_type_cases [elim]: "OptionI a x :\<^sub>b b" and
  OptionT_type_cases [elim]: "x :\<^sub>b OptionBT a" and
  FinI_type_cases [elim]: "FinI a x :\<^sub>b b" and
  FinT_type_cases: "x :\<^sub>b FSetBT a" and
  PairI_type_cases [elim]: "PairI x y :\<^sub>b t" and
  PairT_type_cases [elim!]: "x :\<^sub>b PairBT a b" and
  MapI_type_cases [elim]: "MapI a b xs :\<^sub>b t" and
  MapT_type_cases [elim!]: "x :\<^sub>b MapBT a b" and
  RecI_type_cases [elim]: "RecI xs :\<^sub>b t" and
  RecT_type_cases [elim!]: "x :\<^sub>b RecordBT fs" and
  Cons_type_cases [elim!]: "x :\<^sub>r f # fs" and
  Cons_value_cases [elim!]: "x # xs :\<^sub>r ts" and
  Nil_type_cases [elim!]: "x :\<^sub>r []" and
  Nil_value_cases [elim!]: "[] :\<^sub>r ts" and
(*
and
  FuncT_type_casesB [elim!]: "x :\<^sub>b a \<rightarrow> b" and
  SetT_type_casesB [elim!]: "x :\<^sub>b SetT a" and
*)
  BotI_type_cases[elim]: "BotI a :\<^sub>b b" and
  NameI_type_cases [elim]: "NameI x :\<^sub>b t" and
  NameT_type_cases [elim!]: "x :\<^sub>b NameBT" and
  TypeI_type_cases [elim]: "TypeI x :\<^sub>b t" and
  TypeT_type_cases [elim!]: "x :\<^sub>b TypeBT"

definition bcarrier :: "vbasict \<Rightarrow> vbasic set" where
"bcarrier t = {x. x :\<^sub>b t}"

instantiation vbasic :: DEFINED_NE
begin

fun Defined_vbasic :: "vbasic \<Rightarrow> bool" where
"Defined_vbasic (BotI a) = False" |
"Defined_vbasic (PairI x y) = (Defined_vbasic x \<and> Defined_vbasic y)" |
"Defined_vbasic (BoolI x) = True" |
"Defined_vbasic (NatI n) = True" |
"Defined_vbasic (IntI n) = True" |
"Defined_vbasic (RatI n) = True" |
"Defined_vbasic (RealI n) = True" |
"Defined_vbasic (CharI x) = True" |
"Defined_vbasic (QuoteI x) = True" |
"Defined_vbasic (TokenI x) = Defined_vbasic x" |
"Defined_vbasic (EvI n t v) = True" |
"Defined_vbasic (ListI a xs) = (\<forall> x \<in> set xs. Defined_vbasic x)" |
"Defined_vbasic (OptionI a None) = True" |
"Defined_vbasic (OptionI a (Some x)) = Defined_vbasic x" |
"Defined_vbasic (FinI a xs) = (\<forall> x \<in> set xs. Defined_vbasic x)" |
"Defined_vbasic (RecI xs) = (\<forall> x \<in> set xs. Defined_vbasic x)" |
"Defined_vbasic (MapI a b xs) = (\<forall> (x,y) \<in> set xs. Defined_vbasic x \<and> Defined_vbasic y)" | 
"Defined_vbasic (NameI n) = True" |
"Defined_vbasic (TypeI t) = True"

instance 
  by (intro_classes, rule_tac x="NatI 0" in exI, simp)

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

instantiation vdmv :: DEFINED_NE
begin

fun Defined_vdmv :: "vdmv \<Rightarrow> bool" where
"Defined_vdmv (BasicD x) = \<D> x" |
"Defined_vdmv (SetD t xs) = (\<forall>x\<in>xs. \<D> x)" |
"Defined_vdmv (FuncD s t f) = True" |
"Defined_vdmv (BotD' s) = False"

instance 
  by (intro_classes, rule_tac x="BasicD (IntI 0)" in exI, simp)

end

lemma Defined_nbot [simp]: "\<D> x \<Longrightarrow> x \<noteq> BotD a"
  by (case_tac a, auto)

definition "vbtypes = (BasicT ` UNIV)"

(*
definition vbtypes :: "vdmt set" where
"vbtypes = {t. \<exists> x. x :\<^sub>b t \<and> \<D>\<^sub>b x}"
*)

definition vbvalues :: "vdmv set" where
"vbvalues = {BasicD x | x t. x :\<^sub>b t}"

(*
lemma vbtypes_simps [simp]:
  "\<nat> \<in> vbtypes" "\<int> \<in> vbtypes" "\<rat> \<in> vbtypes"
  "\<bool> \<in> vbtypes" "CharT \<in> vbtypes" "TokenT \<in> vbtypes"
  "FSetBT a \<in> vbtypes" "ListBT a \<in> vbtypes" "EventBT \<in> vbtypes"
 apply (auto simp add:vbtypes_def)
 apply (rule_tac x="TokenI (NatI 0)" in exI)
 apply (force)
 apply (rule_tac x="FSetI a \<lbrace>\<rbrace>" in exI)
 apply (force simp add:FSetI_def)
 apply (rule_tac x="ListI a []" in exI)
 apply (force)
done
*)

text {* Coercion *}

fun CoerceI :: "vbasic \<Rightarrow> vbasict \<Rightarrow> vbasic" where
"CoerceI (NatI x) IntBT  = (IntI (of_nat x))" |
"CoerceI (NatI x) RatBT  = (RatI (of_nat x))" |
"CoerceI (NatI x) RealBT = (RealI (of_nat x))" |
"CoerceI (IntI x) RatBT  = (RatI (of_int x))" |
"CoerceI (IntI x) RealBT = (RealI (of_int x))" |
"CoerceI (RatI x) RealBT = (RealI (of_rat x))" |
"CoerceI x t = (if (x :\<^sub>b t) then x else BotI t)" 

lemma CoerceI_refl [simp]:
  "x :\<^sub>b t \<Longrightarrow> CoerceI x t = x"
  apply (case_tac x, case_tac[!] t)
  apply (auto)
done

lemma CoerceI_idem [simp]:
  "CoerceI (CoerceI x t) t = CoerceI x t"
  apply (case_tac x, case_tac[!] t)
  apply (auto)
done

lemma CoerceI_type [intro]:
  "CoerceI x t :\<^sub>b t"
  apply (case_tac x, case_tac[!] t)
  apply (auto)
done

text {* We introduce a couple of derived typing rules *}

lemma NilI_type[intro]: "ListI a [] :\<^sub>b ListBT a"
  by auto

lemma ConsI_type[intro]: 
  "\<lbrakk> x :\<^sub>b a; ListI a xs :\<^sub>b ListBT a \<rbrakk> 
   \<Longrightarrow> ListI a (x # xs) :\<^sub>b ListBT a"
  by (auto)

lemma FSetI_type[intro]:
  assumes sty: "\<forall>x\<in>\<^sub>fxs. x :\<^sub>b a" 
  shows "FSetI a xs :\<^sub>b FSetBT a"
  by (auto simp add:FSetI_def sty)

lemma FSetT_type_cases [elim!]: 
  "\<lbrakk> x :\<^sub>b FSetBT t; \<And> xs. \<lbrakk> x = FSetI t xs; \<forall>x\<in>\<^sub>fxs. x :\<^sub>b t \<rbrakk> \<Longrightarrow> P; x = BotI (\<fin> t) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule FinT_type_cases)
  apply (auto simp add:FSetI_def)
  apply (metis fset_inv)
done

lemma FSetI_type_cases [elim]:
  "\<lbrakk>FSetI a xs :\<^sub>b t; \<And>a. \<lbrakk>t = FSetBT a; \<forall>x\<in>\<^sub>fxs. x :\<^sub>b a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add:FSetI_def)

lemma FinMapI_type[intro]: 
  "\<lbrakk> \<forall> x\<in>\<^sub>ffdom f. x :\<^sub>b a; \<forall> y\<in>\<^sub>ffran f. y :\<^sub>b b \<rbrakk> \<Longrightarrow> FinMapI a b f :\<^sub>b MapBT a b"
  by (auto intro!:MapI_type simp add:fdom_list fran_list FinMapI_def)

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
  
lemma dom_map_of: "x \<in> dom (map_of xs) \<Longrightarrow> \<exists> y. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:dom_def)

lemma ran_map_of: "y \<in> ran (map_of xs) \<Longrightarrow> \<exists> x. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:ran_def)

lemma FinMapI_type_cases [elim!]:
  "\<lbrakk> x :\<^sub>b MapBT a b; x \<noteq> BotI (MapBT a b); 
    \<And>f. \<lbrakk>x = FinMapI a b f; \<forall> x\<in>\<^sub>ffdom f. x :\<^sub>b a; \<forall> y\<in>\<^sub>ffran f. y :\<^sub>b b \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
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
SetD_type[intro]: "\<lbrakk> \<forall> x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> SetD a xs :\<^sub>v SetT a" |
BasicD_type[intro]: "x :\<^sub>b a \<Longrightarrow> BasicD x :\<^sub>v BasicT a" |
FuncD_type[intro]: "\<lbrakk> \<And> x. \<lbrakk> x :\<^sub>b a; \<D> x \<rbrakk> \<Longrightarrow> f x :\<^sub>v b 
                    ; \<And> x. \<not> \<D> x \<Longrightarrow> f x = BotD b \<rbrakk> \<Longrightarrow> FuncD a b f :\<^sub>v a \<rightarrow> b" |
BotD'_type[intro]: "a \<notin> range BasicT \<Longrightarrow> BotD' a :\<^sub>v a"

inductive_cases
  SetT_type_cases': "x :\<^sub>v SetT a" and
  SetD_type_cases[elim!]: "SetD a x :\<^sub>v t" and
  FuncT_type_cases': "x :\<^sub>v a \<rightarrow> b" and
  FuncI_type_cases[elim!]: "FuncD a b f :\<^sub>v t" and
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

(*
lemma vbtypes_type_cases [elim]: 
  "\<lbrakk> a :\<^sub>v t; \<And> x. \<lbrakk> a = BasicD x; x :\<^sub>b t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac a)
  apply (auto elim:BasicD_type_cases simp add:vbtypes_def)
done

lemma vbvalues_vbtype:
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes \<rbrakk> \<Longrightarrow> a \<in> vbvalues"
  by (auto simp add:vbvalues_def)
*)

definition vcarrier :: "vdmt \<Rightarrow> vdmv set" where
"vcarrier t = {x. x :\<^sub>v t}"

lemma vcarrier [simp]: "x :\<^sub>v t \<Longrightarrow> x \<in> vcarrier t"
  by (simp add:vcarrier_def)

lemma vcarrier_simps [simp]:
  "vcarrier NatT  = {BotD NatT} \<union> {BasicD (NatI x) | x . True}"
  "vcarrier IntT  = {BotD IntT} \<union> {BasicD (IntI x) | x . True}"
  "vcarrier RatT  = {BotD RatT} \<union> {BasicD (RatI x) | x . True}"
  "vcarrier BoolT = {BotD BoolT} \<union> {BasicD (BoolI x) | x . True}"
  apply (simp_all add:vcarrier_def)
  apply (force)+
done

(*
lemma vbvalues_vbtypes [simp]: 
  "\<lbrakk> x \<in> vbvalues; x :\<^sub>v t \<rbrakk> \<Longrightarrow> t \<in> vbtypes"
  by (auto simp add:vbvalues_def vbtypes_def)
*)

(* Flatness of vbasic values *)

subsection {* Injecting basic values into vdmv *}

fun ProjBasicD :: "vdmv \<Rightarrow> vbasic" where
"ProjBasicD (BasicD x) = x" |
"ProjBasicD _ = BotI NatBT"

fun IsBasicD :: "vdmv \<Rightarrow> bool" where
"IsBasicD (BasicD x) = True" |
"IsBasicD _ = False"

lemma ProjBasicD_inv [simp] :
  "IsBasicD x \<Longrightarrow> BasicD (ProjBasicD x) = x"
  by (case_tac x, simp_all)

lemma ProjBasicD_o_BasicD [simp]: 
  "ProjBasicD \<circ> BasicD = id"
  by (auto)


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
"ProjFuncD (FuncD a b f) = f"

fun IsFuncD :: "vdmv \<Rightarrow> bool" where
"IsFuncD (FuncD a b f) = True" |
"IsFuncD _ = False"

primrec ProjSetD :: "vdmv \<Rightarrow> vbasic set" where
"ProjSetD (SetD a x) = x"

fun IsSetD :: "vdmv \<Rightarrow> bool" where
"IsSetD (SetD a x) = True" |
"IsSetD _ = False"

thm EvI_type_cases

lemma vbasic_type_rel_uniq: "\<lbrakk> x :\<^sub>b a; x :\<^sub>b b \<rbrakk> \<Longrightarrow> a = b"
  and "\<lbrakk> xs :\<^sub>r as; xs :\<^sub>r bs \<rbrakk> \<Longrightarrow> as = bs"
  apply (induct x and xs arbitrary: a b and as bs)
  apply (auto)
  apply (metis PairI_type_cases)
  apply (force)
done

fun default_vbasict :: "vbasict \<Rightarrow> vbasic" where
"default_vbasict BoolBT        = BoolI False" |
"default_vbasict NatBT         = NatI 0" |
"default_vbasict IntBT         = IntI 0" |
"default_vbasict RatBT         = RatI 0" |
"default_vbasict RealBT        = RealI 0" |
"default_vbasict CharBT        = CharI (CHR ''x'')" |
"default_vbasict QuoteBT       = QuoteI ''x''" |
"default_vbasict TokenBT       = TokenI (BoolI False)" |
"default_vbasict EventBT       = EvI (MkName ''x'' 0 NoSub) BoolBT (BoolI False)" |
"default_vbasict NameBT        = NameI (MkName ''x'' 0 NoSub)" |
"default_vbasict TypeBT        = TypeI BoolBT" |
"default_vbasict (PairBT s t)  = PairI (default_vbasict s) (default_vbasict t)" |
"default_vbasict (OptionBT t)  = OptionI t None" |
"default_vbasict (FSetBT t)    = FSetI t \<lbrace>\<rbrace>" |
"default_vbasict (ListBT t)    = ListI t []" |
"default_vbasict (MapBT s t)   = MapI s t []" |
"default_vbasict (RecordBT ts) = RecI (map default_vbasict ts)"

lemma default_vbasict_type: 
  "default_vbasict t :\<^sub>b t" and
  "map default_vbasict ts :\<^sub>r ts"
  by (induct t and ts, auto)

declare default_vbasict_type(1) [typing]

lemma default_vbasict_defined: 
  "\<D> (default_vbasict t)" and
  "(\<forall> x \<in> set (map default_vbasict ts). \<D> x)"
  by (induct t and ts, auto)

declare default_vbasict_defined(1) [defined]

lemma vbasict_total: 
  "\<exists> v. v :\<^sub>b t \<and> \<D> v"
  apply (rule_tac x="default_vbasict t" in exI)
  apply (auto simp add:typing defined)
done
  
fun default_vdmt :: "vdmt \<Rightarrow> vdmv" where
"default_vdmt (SetT t)       = SetD t {}" |
"default_vdmt (FuncT s t)    = FuncD s t(\<lambda> x. if (\<D> x) then default_vdmt t else BotD t)" |
"default_vdmt (BasicT t)     = BasicD (default_vbasict t)"

lemma default_vdmt_type: 
  "default_vdmt t :\<^sub>v t"
  apply (induct t)
  apply (auto intro:typing)
done

declare default_vdmt_type(1) [typing]

lemma default_vdmtt_defined: 
  "\<D> (default_vdmt t)"
  by (induct t, auto intro:defined)

declare default_vdmtt_defined(1) [defined]

lemma vdmt_total: 
  "\<exists> v. v :\<^sub>v t \<and> \<D> v"
  apply (rule_tac x="default_vdmt t" in exI)
  apply (auto simp add:typing defined)
done

end