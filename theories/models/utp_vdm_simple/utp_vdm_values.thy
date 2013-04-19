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

text {* We only introduce a single datatype for types, as the move between vdmv and
  vbasic should be transparent *}

datatype vdmt =
    FSetT vdmt
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
  | TVarT nat
  | SetT vdmt 
  | FuncT vdmt vdmt (infixr "→" 60)
  | NameT
  | TypeT

derive countable vdmt
(* derive linorder vdmt *)
instantiation vdmt :: linorder
begin

instance sorry

end

type_synonym tyctx = "(nat, vdmt) fmap"

fun vtsubst :: "tyctx \<Rightarrow> vdmt \<Rightarrow> vdmt" where
"vtsubst f (FSetT t)  = FSetT (vtsubst f t)" | 
"vtsubst f (MapT s t) = MapT (vtsubst f s) (vtsubst f t)" |
"vtsubst f (ListT t)  = ListT (vtsubst f t)" | 
"vtsubst f (OptionT t) = OptionT (vtsubst f t)" |
"vtsubst f (PairT s t) = PairT (vtsubst f s) (vtsubst f t)" |
"vtsubst f (FuncT s t) = FuncT (vtsubst f s) (vtsubst f t)" |
"vtsubst f (SetT t) = SetT (vtsubst f t)" |
"vtsubst f (RecordT ts) = RecordT (map (vtsubst f) ts)" |
"vtsubst f (TVarT x) = (if (x \<in>\<^sub>f fdom f) then (the (\<langle>f\<rangle>\<^sub>m x)) else (TVarT x))" |
"vtsubst f t = t"

definition vunifies_under :: "tyctx \<Rightarrow> (vdmt * vdmt) \<Rightarrow> bool" (infix "unifies" 50) where
"\<rho> unifies v = (vtsubst \<rho> (fst v) = vtsubst \<rho> (snd v))"

fun tyvars :: "vdmt \<Rightarrow> nat fset" where
"tyvars (FSetT t)  = tyvars t" | 
"tyvars (MapT s t) = (tyvars s) \<union>\<^sub>f (tyvars t)" |
"tyvars (ListT t)  = tyvars t" | 
"tyvars (OptionT t) = tyvars t" |
"tyvars (PairT s t) = (tyvars s) \<union>\<^sub>f (tyvars t)" |
"tyvars (FuncT s t) = (tyvars s) \<union>\<^sub>f (tyvars t)" |
"tyvars (SetT t) = (tyvars t)" |
"tyvars (RecordT ts) = (foldr (\<lambda> x. op \<union>\<^sub>f (tyvars x)) ts \<lbrace>\<rbrace>) " |
"tyvars (TVarT x) = \<lbrace>x\<rbrace>" |
"tyvars t = \<lbrace>\<rbrace>"

lemma unifies_refl [intro]: "\<Delta> unifies (x,x)"
  by (simp add:vunifies_under_def)

lemma unifies_sym: "\<Delta> unifies (x,y) \<Longrightarrow> \<Delta> unifies (y,x)"
  by (simp add:vunifies_under_def)

lemma unifies_trans:
  "\<lbrakk> \<Delta> unifies (x,y); \<Delta> unifies (y,z) \<rbrakk> \<Longrightarrow> \<Delta> unifies (x,z)"
  by (simp add:vunifies_under_def)

lemma vtsubst_nfree [simp]: "tyvars t = \<lbrace>\<rbrace> \<Longrightarrow> vtsubst \<Delta> t = t"
  and "foldr (\<lambda>t. op \<union>\<^sub>f (tyvars t)) ts \<lbrace>\<rbrace> = \<lbrace>\<rbrace> \<Longrightarrow> map (vtsubst \<Delta>) ts = ts"
  by (induct t and ts, (force)+)

lemma vtsubst_disj_vars [simp]: 
  "tyvars t \<inter>\<^sub>f fdom \<Delta> = \<lbrace>\<rbrace> \<Longrightarrow> vtsubst \<Delta> t = t"
  and "foldr (\<lambda>t. op \<union>\<^sub>f (tyvars t)) ts \<lbrace>\<rbrace> \<inter>\<^sub>f fdom \<Delta> = \<lbrace>\<rbrace> 
       \<Longrightarrow> map (vtsubst \<Delta>) ts = ts"
  by (induct t and ts, (force)+)

lemma unifies_TVarT_simple [intro!]:
  "\<lbrakk> tyvars a \<inter>\<^sub>f fdom \<Delta> = \<lbrace>\<rbrace>; \<langle>\<Delta>\<rangle>\<^sub>m x = Some a \<rbrakk> \<Longrightarrow> \<Delta> unifies (a, TVarT x)"
  "\<lbrakk> tyvars a \<inter>\<^sub>f fdom \<Delta> = \<lbrace>\<rbrace>; \<langle>\<Delta>\<rangle>\<^sub>m x = Some a \<rbrakk> \<Longrightarrow> \<Delta> unifies (TVarT x, a)"
  by (auto simp add:vunifies_under_def fdom.rep_eq)

lemma unifies_FSetT [intro!]: 
  "\<Delta> unifies (a,b) \<Longrightarrow> \<Delta> unifies (FSetT a, FSetT b)"
  by (simp add:vunifies_under_def)

lemma unifies_MapT [intro!]: 
  "\<lbrakk> \<Delta> unifies (a1,b1); \<Delta> unifies (a2,b2) \<rbrakk> 
  \<Longrightarrow> \<Delta> unifies (MapT a1 a2, MapT b1 b2)"
  by (simp add:vunifies_under_def)

lemma unifies_ListT [intro!]: 
  "\<Delta> unifies (a,b) \<Longrightarrow> \<Delta> unifies (ListT a, ListT b)"
  by (simp add:vunifies_under_def)

lemma unifies_OptionT [intro!]: 
  "\<Delta> unifies (a,b) \<Longrightarrow> \<Delta> unifies (OptionT a, OptionT b)"
  by (simp add:vunifies_under_def)

lemma unifies_PairT [intro!]: 
  "\<lbrakk> \<Delta> unifies (a1,b1); \<Delta> unifies (a2,b2) \<rbrakk> 
  \<Longrightarrow> \<Delta> unifies (PairT a1 a2, PairT b1 b2)"
  by (simp add:vunifies_under_def)

lemma unifies_FuncT [intro!]: 
  "\<lbrakk> \<Delta> unifies (a1,b1); \<Delta> unifies (a2,b2) \<rbrakk> 
  \<Longrightarrow> \<Delta> unifies (FuncT a1 a2, FuncT b1 b2)"
  by (simp add:vunifies_under_def)

lemma unifies_SetT [intro!]: 
  "\<Delta> unifies (a,b) \<Longrightarrow> \<Delta> unifies (SetT a, SetT b)"
  by (simp add:vunifies_under_def)

lemma unifies_NatT_cases [elim]:
  "\<lbrakk> \<Delta> unifies (t, \<nat>)
   ; t = \<nat> \<Longrightarrow> P
   ; \<And> x. \<lbrakk> t = TVarT x; \<langle>\<Delta>\<rangle>\<^sub>m x = Some \<nat> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac t, auto simp add:vunifies_under_def)
  apply (case_tac "nat \<in>\<^sub>f fdom \<Delta>", auto simp add:fdom.rep_eq)
done

lemma unifies_IntT_cases [elim]:
  "\<lbrakk> \<Delta> unifies (t, \<int>)
   ; t = \<int> \<Longrightarrow> P
   ; \<And> x. \<lbrakk> t = TVarT x; \<langle>\<Delta>\<rangle>\<^sub>m x = Some \<int> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac t, auto simp add:vunifies_under_def)
  apply (case_tac "nat \<in>\<^sub>f fdom \<Delta>", auto simp add:fdom.rep_eq)
done

lemma unifies_ListT_cases [elim]:
  "\<lbrakk> \<Delta> unifies (t, ListT a)
   ; \<And> a'. \<lbrakk> t = ListT a'
            ; \<Delta> unifies (a, a') \<rbrakk> \<Longrightarrow> P
   ; \<And> x. \<lbrakk> t = TVarT x; \<langle>\<Delta>\<rangle>\<^sub>m x = Some (ListT (vtsubst \<Delta> a)) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac t, auto simp add:vunifies_under_def)
  apply (case_tac "nat \<in>\<^sub>f fdom \<Delta>", auto simp add:fdom.rep_eq)
done

lemma unifies_FuncT_cases [elim]:
  "\<lbrakk> \<Delta> unifies (t, FuncT a b)
   ; \<And> a' b'. \<lbrakk> t = FuncT a' b'
               ; \<Delta> unifies (a, a')
               ; \<Delta> unifies (b, b') \<rbrakk> \<Longrightarrow> P
   ; \<And> x. \<lbrakk> t = TVarT x; \<langle>\<Delta>\<rangle>\<^sub>m x = Some (vtsubst \<Delta> a → vtsubst \<Delta> b) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac t, auto simp add:vunifies_under_def)
  apply (case_tac "nat \<in>\<^sub>f fdom \<Delta>", auto simp add:fdom.rep_eq)
  apply (force)
done

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
  | TypeI "vdmt"
  | BotI

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

datatype vdmv = SetV "vbasic set"
                | FuncV "vbasic \<Rightarrow> vdmv"
                | BasicV "vbasic"

abbreviation "BotV \<equiv> BasicV BotI"
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

lemma FSetI_inv [simp]:
  "ProjFSetI (FSetI xs) = Some xs"
  by (simp add:FSetI_def)

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

fun ProjTypeI :: "vbasic \<Rightarrow> vdmt option" where
"ProjTypeI (TypeI t) = Some t" | "ProjTypeI _ = None"

section {* The type-system *}

subsection {* Basic value typing relation *}

inductive vbasic_type_rel :: "tyctx \<Rightarrow> vbasic \<Rightarrow> vdmt \<Rightarrow> bool" ("_ \<turnstile> _ :\<^sub>b _") 
and vbasic_type_list_rel :: "tyctx \<Rightarrow> vbasic list \<Rightarrow> vdmt list \<Rightarrow> bool" ("_ \<turnstile> _ :\<^sub>r _") where
unifies_type[intro]: 
  "\<lbrakk> \<Delta> \<turnstile> x :\<^sub>b a'; \<Delta> unifies (a, a') \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> x :\<^sub>b a" |
BoolI_type[intro!]: "\<Delta> \<turnstile> BoolI x :\<^sub>b BoolT" |
NatI_type[intro!]: "\<Delta> \<turnstile> NatI x :\<^sub>b NatT" |
IntI_type[intro!]: "\<Delta> \<turnstile> IntI x :\<^sub>b IntT" |
RatI_type[intro!]: "\<Delta> \<turnstile> RatI x :\<^sub>b RatT" |
RealI_type[intro!]: "\<Delta> \<turnstile> RealI x :\<^sub>b RealT" |
CharI_type[intro!]: "\<Delta> \<turnstile> CharI x :\<^sub>b CharT" |
TokenI_type[intro!]: "\<Delta> \<turnstile> TokenI x :\<^sub>b TokenT" |
QuoteI_type[intro!]: "\<Delta> \<turnstile> QuoteI x :\<^sub>b QuoteT" |
ListI_type[intro!]: "\<lbrakk> \<forall>x\<in>set xs. \<Delta> \<turnstile> x :\<^sub>b a \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> ListI xs :\<^sub>b ListT a" |
OptionI_Some_type[intro]: "\<lbrakk> \<Delta> \<turnstile> x :\<^sub>b a \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> OptionI (Some x) :\<^sub>b OptionT a" |
OptionI_None_type[intro]: "\<Delta> \<turnstile> OptionI None :\<^sub>b OptionT a" |
FinI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. \<Delta> \<turnstile> x :\<^sub>b a; sorted xs; distinct xs \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> FinI xs :\<^sub>b FSetT a" |
PairI_type[intro!]: "\<lbrakk> \<Delta> \<turnstile> x :\<^sub>b a; \<Delta> \<turnstile> y :\<^sub>b b \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> PairI x y :\<^sub>b PairT a b" |
MapI_type[intro]: "\<lbrakk> \<forall>(x,y)\<in>set xs. \<Delta> \<turnstile> x :\<^sub>b a \<and> \<Delta> \<turnstile> y :\<^sub>b b; sorted (map fst xs); distinct (map fst xs) \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> MapI xs :\<^sub>b MapT a b" |
RecI_type[intro]: "\<lbrakk> \<Delta> \<turnstile> xs :\<^sub>r ts \<rbrakk>  \<Longrightarrow> \<Delta> \<turnstile> RecI xs :\<^sub>b RecordT ts" |
NameI_type[intro]: "\<Delta> \<turnstile> NameI n :\<^sub>b NameT" |
TypeI_type[intro]: "\<Delta> \<turnstile> TypeI t :\<^sub>b TypeT" |
BotI_type[intro]: "\<Delta> \<turnstile> BotI :\<^sub>b TVarT n" |
Cons_type[intro]: "\<lbrakk> \<Delta> \<turnstile> x :\<^sub>b t; \<Delta> \<turnstile> xs :\<^sub>r ts \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> (x # xs) :\<^sub>r (t # ts)" |
Nil_type[intro]: "\<Delta> \<turnstile> [] :\<^sub>r []"

abbreviation vbasic_type_rel_nctx :: "vbasic \<Rightarrow> vdmt \<Rightarrow> bool" (infix ":\<^sub>b" 50) where
"v :\<^sub>b t  \<equiv> (\<exists> \<Delta>. \<Delta> \<turnstile> v :\<^sub>b t)"

lemma fdom_fmempty [simp]: "fdom fmempty = \<lbrace>\<rbrace>"
  by (auto simp add:fdom.rep_eq fmempty.rep_eq)

lemma vtsubst_fempty [simp]: "vtsubst fmempty t = t"
  and "map (vtsubst fmempty) ts = ts"
  apply (induct t and ts)
  apply (simp_all)
  apply (metis fdom_fmempty fset_simps(3) vdmt.simps(6) vtsubst.simps(8) vtsubst_disj_vars)
done

lemma vtsubst_fmap_upd [simp]: "x \<notin>\<^sub>f tyvars t \<Longrightarrow> vtsubst (\<Delta>(x:=\<^sub>mSome a)) t = vtsubst \<Delta> t"
  and "x \<notin>\<^sub>f foldr (\<lambda>t. op \<union>\<^sub>f (tyvars t)) ts \<lbrace>\<rbrace> 
       \<Longrightarrow> map (vtsubst (\<Delta>(x:=\<^sub>mSome a))) ts = map (vtsubst \<Delta>) ts"
  by (induct t and ts, simp_all)

lemma unifies_TVarT_simple' [intro]:
  "\<lbrakk> x \<notin>\<^sub>f tyvars t \<rbrakk> \<Longrightarrow> fmempty(x:=\<^sub>mSome t) unifies (TVarT x, t)"
  by (simp add: vunifies_under_def)

lemma fmap_eq_intros[intro]: 
  "\<langle>\<Delta>(x :=\<^sub>m Some t)\<rangle>\<^sub>m x = Some t"
  "\<lbrakk> a \<noteq> b; x \<noteq> y; \<langle>\<Delta>\<rangle>\<^sub>m y = Some b \<rbrakk> 
   \<Longrightarrow> \<langle>\<Delta>(x :=\<^sub>m Some a)\<rangle>\<^sub>m y = Some b"
  by (simp_all)

lemma fdom_femptyE: "x \<in> \<langle>fdom fmempty\<rangle>\<^sub>f \<Longrightarrow> False"
  by (simp)

lemma "ListI [ListI []] :\<^sub>b ListT (ListT (TVarT 0))"
  by (force)

lemma "ListI [] :\<^sub>b ListT (ListT NatT)"
  by (force)

lemma "ListI [ListI []] :\<^sub>b ListT (ListT \<nat>)"
  by (force)

lemma "ListI [ListI [], ListI [NatI 0], ListI [], BotI] :\<^sub>b ListT (ListT NatT)"
  by (force)


(* Typing relation without parametric polymorphism *)
(*
inductive vbasic_type_rel :: "vbasic \<Rightarrow> vdmt \<Rightarrow> bool" (infix ":\<^sub>b" 50) 
  and vbasic_type_list_rel :: "vbasic list \<Rightarrow> vdmt list \<Rightarrow> bool" (infix ":\<^sub>r" 50) where
BoolI_type[intro]: "BoolI x :\<^sub>b BoolT" |
NatI_type[intro]: "NatI x :\<^sub>b NatT" |
IntI_type[intro]: "IntI x :\<^sub>b IntT" |
RatI_type[intro]: "RatI x :\<^sub>b RatT" |
RealI_type[intro]: "RealI x :\<^sub>b RealT" |
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
BotI_type[intro]: "BotI :\<^sub>b a" |
Cons_type[intro]: "\<lbrakk> x :\<^sub>b t; xs :\<^sub>r ts \<rbrakk> \<Longrightarrow> (x # xs) :\<^sub>r (t # ts)" |
Nil_type[intro]: "[] :\<^sub>r []"
*)

inductive_cases 
  BoolI_type_cases [elim]: "\<Delta> \<turnstile> BoolI x :\<^sub>b t" and
  BoolT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b BoolT" and
  NatI_type_cases [elim]: "\<Delta> \<turnstile> NatI x :\<^sub>b t" and
  NatT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b NatT" and
  IntI_type_cases [elim]: "\<Delta> \<turnstile> IntI x :\<^sub>b t" and
  IntT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b IntT" and
  RatI_type_cases [elim]: "\<Delta> \<turnstile> RatI x :\<^sub>b t" and
  RatT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b RatT" and
  CharI_type_cases [elim]: "\<Delta> \<turnstile> CharI x :\<^sub>b t" and
  CharT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b CharT" and
  TokenI_type_cases [elim]: "\<Delta> \<turnstile> TokenI x :\<^sub>b t" and
  TokenT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b TokenT" and
  QuoteI_type_cases [elim]: "\<Delta> \<turnstile> QuoteI x :\<^sub>b t" and
  QuoteT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b QuoteT" and
  ListI_type_cases [elim]: "\<Delta> \<turnstile> ListI xs :\<^sub>b t" and
  ListT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b ListT a" and
  OptionI_type_cases [elim]: "\<Delta> \<turnstile> OptionI x :\<^sub>b t" and
  OptionT_type_cases [elim]: "\<Delta> \<turnstile> x :\<^sub>b OptionT a" and
  FinI_type_cases [elim]: "\<Delta> \<turnstile> FinI x :\<^sub>b t" and
  FinT_type_cases: "\<Delta> \<turnstile> x :\<^sub>b FSetT a" and
  PairI_type_cases [elim]: "\<Delta> \<turnstile> PairI x y :\<^sub>b t" and
  PairT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b PairT a b" and
  MapI_type_cases [elim]: "\<Delta> \<turnstile> MapI xs :\<^sub>b t" and
  MapT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b MapT a b" and
  RecI_type_cases [elim]: "\<Delta> \<turnstile> RecI xs :\<^sub>b t" and
  RecT_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>b RecordT fs" and
  Cons_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>r f # fs" and
  Nil_type_cases [elim!]: "\<Delta> \<turnstile> x :\<^sub>r []" and
  FuncT_type_casesB [elim!]: "\<Delta> \<turnstile> x :\<^sub>b a → b" and
  SetT_type_casesB [elim!]: "\<Delta> \<turnstile> x :\<^sub>b SetT a" and
  BotI_type_cases[elim]: "\<Delta> \<turnstile> BotI :\<^sub>b a"

definition bcarrier :: "vdmt \<Rightarrow> vbasic set" where
"bcarrier t = {x. x :\<^sub>b t}"

fun vbdefined :: "vbasic \<Rightarrow> bool" ("\<D>\<^sub>b") where
"\<D>\<^sub>b BotI = False" |
"\<D>\<^sub>b (PairI x y) = (\<D>\<^sub>b x \<and> \<D>\<^sub>b y)" |
"\<D>\<^sub>b (BoolI x) = True" |
"\<D>\<^sub>b (NatI n) = True" |
"\<D>\<^sub>b (IntI n) = True" |
"\<D>\<^sub>b (RatI n) = True" |
"\<D>\<^sub>b (RealI n) = True" |
"\<D>\<^sub>b (CharI x) = True" |
"\<D>\<^sub>b (QuoteI x) = True" |
"\<D>\<^sub>b (TokenI x) = \<D>\<^sub>b x" |
"\<D>\<^sub>b (ListI xs) = foldr (op \<and> \<circ> \<D>\<^sub>b) xs True" |
"\<D>\<^sub>b (OptionI None) = True" |
"\<D>\<^sub>b (OptionI (Some x)) = \<D>\<^sub>b x" |
"\<D>\<^sub>b (FinI xs) = foldr (op \<and> \<circ> \<D>\<^sub>b) xs True" |
"\<D>\<^sub>b (RecI xs) = foldr (op \<and> \<circ> \<D>\<^sub>b) xs True" |
"\<D>\<^sub>b (MapI xs) = foldr (op \<and> \<circ> (\<lambda> x. \<D>\<^sub>b (fst x) \<and> \<D>\<^sub>b (snd x))) xs True" | 
"\<D>\<^sub>b (NameI n) = True" |
"\<D>\<^sub>b (TypeI t) = True"

fun vdefined :: "vdmv \<Rightarrow> bool" ("\<D>\<^sub>v") where
"\<D>\<^sub>v (BasicV x) = \<D>\<^sub>b x" |
"\<D>\<^sub>v (SetV xs) = (\<forall>x\<in>xs. \<D>\<^sub>b x)" |
"\<D>\<^sub>v (FuncV f) = True"

definition vbtypes :: "vdmt set" where
"vbtypes = {t. \<exists> x. x :\<^sub>b t \<and> \<D>\<^sub>b x}"

definition vbvalues :: "vdmv set" where
"vbvalues = {BasicV x | x t. x :\<^sub>b t}"

lemma vbtypes_simps [simp]:
  "\<nat> \<in> vbtypes" "\<int> \<in> vbtypes" "\<rat> \<in> vbtypes"
  "\<bool> \<in> vbtypes" "CharT \<in> vbtypes" "TokenT \<in> vbtypes"
  "FSetT a \<in> vbtypes" "ListT a \<in> vbtypes"
  "a → b \<notin> vbtypes"
  "SetT a \<notin> vbtypes"
 apply (auto simp add:vbtypes_def)
 apply (rule_tac x="TokenI (NatI 0)" in exI)
 apply (force)
 apply (rule_tac x="FSetI \<lbrace>\<rbrace>" in exI)
 apply (force simp add:FSetI_def)
 apply (rule_tac x="ListI []" in exI)
 apply (force)
sorry

text {* We introduce a couple of derived typing rules *}

lemma NilI_type[intro]: "\<Delta> \<turnstile> ListI [] :\<^sub>b ListT a"
  by auto

lemma ConsI_type[intro]: 
  "\<lbrakk> \<Delta> \<turnstile> x :\<^sub>b a; \<Delta> \<turnstile> ListI xs :\<^sub>b ListT a \<rbrakk> 
   \<Longrightarrow> \<Delta> \<turnstile> ListI (x # xs) :\<^sub>b ListT a"
  apply (erule ListI_type_cases)
  apply (auto)
  apply (drule unifies_sym)
  apply (erule unifies_ListT_cases)
  apply (auto)
  apply (drule unifies_sym) back
  apply (erule unifies_ListT_cases)
  apply (auto)
  apply (rule)
  apply (auto)
  apply (erule ListI_type_cases)
  apply (force)
  apply (rule)
  apply (rule)
  apply (auto)
  apply (simp)
  apply (drule unifies_sym)
  apply (erule unifies_ListT_cases)
  apply (auto)
  apply (rule ListI_type)
  apply (auto)
  apply (simp)
  apply (rule)
  apply (force)
  apply (auto intro!: ListI_type)
  by (force intro!: ListI_type)

lemma FSetI_type[intro]:
  assumes sty: "\<forall>x\<in>\<^sub>fxs. x :\<^sub>b a" 
  shows "FSetI xs :\<^sub>b FSetT a"
  by (auto simp add:FSetI_def sty)

lemma FSetT_type_cases [elim!]: 
  "\<lbrakk> x :\<^sub>b FSetT t; \<And> xs. \<lbrakk> x = FSetI xs; \<forall>x\<in>\<^sub>fxs. x :\<^sub>b t \<rbrakk> \<Longrightarrow> P; x = BotI \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule FinT_type_cases)
  apply (auto simp add:FSetI_def)
  apply (metis fset_inv)
done

lemma FSetI_type_cases [elim]:
  "\<lbrakk>FSetI xs :\<^sub>b t; \<And>a. \<lbrakk>t = FSetT a; \<forall>x\<in>\<^sub>fxs. x :\<^sub>b a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add:FSetI_def)

lemma FinMapI_type[intro]: 
  "\<lbrakk> \<forall> x\<in>Rep_fset(fdom f). x :\<^sub>b a; \<forall> y\<in>Rep_fset(fran f). y :\<^sub>b b \<rbrakk> \<Longrightarrow> FinMapI f :\<^sub>b MapT a b"
  by (auto intro!:MapI_type simp add:fdom_list fran_list FinMapI_def)

lemma dom_map_of: "x \<in> dom (map_of xs) \<Longrightarrow> \<exists> y. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:dom_def)

lemma ran_map_of: "y \<in> ran (map_of xs) \<Longrightarrow> \<exists> x. (x,y) \<in> set xs"
  by (auto dest:map_of_SomeD simp add:ran_def)

lemma FinMapI_type_cases [elim!]:
  "\<lbrakk>x :\<^sub>b MapT a b; x \<noteq> BotI; \<And>f. \<lbrakk>x = FinMapI f; \<forall> x\<in>Rep_fset(fdom f). x :\<^sub>b a; \<forall> y\<in>Rep_fset(fran f). y :\<^sub>b b \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
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
SetV_type[intro]: "\<lbrakk> \<forall> x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> SetV xs :\<^sub>v SetT a" |
BasicV_type[intro]: "x :\<^sub>b a \<Longrightarrow> BasicV x :\<^sub>v a" |
FuncV_type[intro]: "\<lbrakk> \<And> x. x :\<^sub>b a \<Longrightarrow> f x :\<^sub>v b; f BotI = BotV \<rbrakk> \<Longrightarrow> FuncV f :\<^sub>v a → b"

inductive_cases
  SetT_type_cases': "x :\<^sub>v SetT a" and
  SetV_type_cases[elim!]: "SetV x :\<^sub>v t" and
  FuncT_type_cases': "x :\<^sub>v a → b" and
  FuncI_type_cases[elim!]: "FuncV f :\<^sub>v t" and
  BasicV_type_cases[elim]: "BasicV x :\<^sub>v t"

lemma SetT_type_cases [elim]: 
  "\<lbrakk> x :\<^sub>v SetT a; \<And> xs. \<lbrakk> x = SetV xs; \<forall>x\<in>xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> P; x = BotV \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule SetT_type_cases')
  apply (auto)
done

lemma FuncT_type_cases [elim]: 
  "\<lbrakk> x :\<^sub>v a → b; \<And> f. \<lbrakk> x = FuncV f; \<forall> x. x :\<^sub>b a \<longrightarrow> f x :\<^sub>v b; f BotI = BotV \<rbrakk> \<Longrightarrow> P
   ; x = BotV \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule FuncT_type_cases')
  apply (auto)
done

lemma vbtypes_type_cases [elim]: 
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes; \<And> x. \<lbrakk> a = BasicV x; x :\<^sub>b t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac a)
  apply (auto elim:BasicV_type_cases simp add:vbtypes_def)
done

lemma vbvalues_vbtype:
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes \<rbrakk> \<Longrightarrow> a \<in> vbvalues"
  by (auto simp add:vbvalues_def)

definition vcarrier :: "vdmt \<Rightarrow> vdmv set" where
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

subsection {* Injecting basic values into vdmv *}

fun ProjBasicV :: "vdmv \<Rightarrow> vbasic" where
"ProjBasicV (BasicV x) = x" |
"ProjBasicV _ = BotI"

fun IsBasicV :: "vdmv \<Rightarrow> bool" where
"IsBasicV (BasicV x) = True" |
"IsBasicV _ = False"

lemma ProjBasicV_inv [simp] :
  "IsBasicV x \<Longrightarrow> BasicV (ProjBasicV x) = x"
  by (case_tac x, simp_all)

definition vstrictify :: "(vbasic \<Rightarrow> vdmv) \<Rightarrow> (vbasic \<Rightarrow> vdmv)" where
"vstrictify f = (\<lambda> x. if (x = BotI) then BotV else f x)"

lemma vstrictify_idem [simp]: 
  "vstrictify (vstrictify f) = vstrictify f"
  by (auto simp add:vstrictify_def)

lemma vstrictify_bot [simp]:
  "vstrictify f BotI = BotV"
  by (simp add:vstrictify_def)

lemma vstrictify_type [intro]:
  "f x :\<^sub>v t \<Longrightarrow> vstrictify f x :\<^sub>v t"
  by (auto simp add:vstrictify_def)

abbreviation SFuncV :: "(vbasic \<Rightarrow> vdmv) \<Rightarrow> vdmv" where
"SFuncV f \<equiv> FuncV (vstrictify f)"

definition vbasic_fun1 :: "(vbasic \<Rightarrow> vbasic) \<Rightarrow> vdmv" where
"vbasic_fun1 f \<equiv> SFuncV (BasicV \<circ> f)"

definition vbasic_fun2 :: "(vbasic \<Rightarrow> vbasic \<Rightarrow> vbasic) \<Rightarrow> vdmv" where
"vbasic_fun2 f \<equiv> SFuncV (\<lambda> x. SFuncV (\<lambda> y. BasicV (f x y)))"

primrec ProjFuncV :: "vdmv \<Rightarrow> (vbasic \<Rightarrow> vdmv)" where
"ProjFuncV (FuncV f) = f"

fun IsFuncV :: "vdmv \<Rightarrow> bool" where
"IsFuncV (FuncV f) = True" |
"IsFuncV _ = False"

primrec ProjSetV :: "vdmv \<Rightarrow> vbasic set" where
"ProjSetV (SetV x) = x"

fun IsSetV :: "vdmv \<Rightarrow> bool" where
"IsSetV (SetV x) = True" |
"IsSetV _ = False"


end