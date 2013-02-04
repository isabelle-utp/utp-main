theory utp_vdm_values
imports 
   HOLCF 
  "~~/src/HOL/HOLCF/Library/HOL_Cpo" 
  "~~/src/HOL/Library/Char_ord" 
  "~~/src/HOL/Library/Monad_Syntax" 
  "../../utils/HOLCF_extra" "../../utils/Library_extra"
  "../../utils/HOLCF_extra/Sfun_Extra"
   Derive
begin

(*
hide_const (open) Lattice.top
hide_const (open) Lattice.inf
hide_const (open) Lattice.sup
*)

section {* Main domain types *}

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
  | CharI "char"
  | QuoteI "string" 
  | TokenI vbasic
  | ListI "vbasic list" 
  | FinI "vbasic list"
  | BoolI bool
  | RecI "vbasic list"
  | MapI "(vbasic * vbasic) list" 

(* Deriving the linear order necessarily takes a while *)

(*
derive linorder vbasic
*)

instantiation vbasic :: linorder
begin

instance sorry

end


derive countable vbasic

instantiation vbasic :: discrete_cpo
begin

definition below_vbasic_def:
  "(x::vbasic) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_vbasic_def)

end

text {* We make a vbasic a predomain so that it can be injected into the full value
  domain below. This requires that all values are countable, and that hence the 
  type is "flat" (wrt. the definedness cpo). *}
instantiation vbasic :: predomain
begin

definition
  "(liftemb :: vbasic u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> vbasic u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::vbasic itself). LIFTDEFL(vbasic discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> vbasic u)"
    unfolding liftemb_vbasic_def liftprj_vbasic_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(vbasic) = liftemb oo (liftprj :: udom u \<rightarrow> vbasic u)"
    unfolding liftemb_vbasic_def liftprj_vbasic_def liftdefl_vbasic_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end

subsection {* Full values *}

text {* Full values are represented using a domain, which adds functions, 
  uncountable sets, reals etc. to what we already have. Domains are harder to
  manipulate than datatypes so we only use them where necessary. Functions
  and sets must have a continuous representation, but since vbasic is "flat"
  any function whose domain is vbasic is automatically continuous.
*}

domain vval = SetV "(vbasic lift) cset" 
            | FuncV "vval \<rightarrow>! vval" 
            | BasicV "vbasic lift"

lemma vval_induct: 
  "\<lbrakk> P \<bottom>
   ; \<And>cset. cset \<noteq> \<bottom> \<Longrightarrow> P (SetV\<cdot>cset)
   ; \<And>sfun. sfun \<noteq> \<bottom> \<Longrightarrow> P (FuncV\<cdot>sfun)
   ; \<And>lift. lift \<noteq> \<bottom> \<Longrightarrow> P (BasicV\<cdot>lift)\<rbrakk> \<Longrightarrow> P x"
  by (induct x, metis vval.exhaust)

abbreviation "sfun_abs2 \<equiv> \<Lambda> f. (\<Lambda>! x. sfun_abs\<cdot>(\<Lambda> x. sfun_abs\<cdot>(f\<cdot>x))\<cdot>!x)"

abbreviation "FuncV2 \<equiv> \<Lambda> f. FuncV\<cdot>(\<Lambda>! x. FuncV\<cdot>(f\<cdot>!x))"
abbreviation "SFuncV \<equiv> \<Lambda> f. FuncV\<cdot>(sfun_abs\<cdot>f)"
abbreviation "SFuncV2 \<equiv> \<Lambda> f. FuncV\<cdot>(sfun_abs\<cdot>(\<Lambda> x. FuncV\<cdot>(sfun_abs\<cdot>(f\<cdot>x))))"

abbreviation "TrueV \<equiv> BasicV\<cdot>(Def (BoolI True))"
abbreviation "FalseV \<equiv> BasicV\<cdot>(Def (BoolI False))"

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

fun ProjMapI :: "vbasic \<Rightarrow> ((vbasic* vbasic) list) option" where
"ProjMapI (MapI f) = Some f" | "ProjMapI x = None"

fun ProjFinMapI :: "vbasic \<Rightarrow> ((vbasic, vbasic) fmap) option" where
"ProjFinMapI (MapI xs) = Some (list_fmap xs)" | "ProjFinMapI x = None"

lemma FinMapI_inj [simp]: "FinMapI f = FinMapI g \<Longrightarrow> f = g"
  apply (simp add: FinMapI_def fmap_list_def)
  apply (drule sorted_list_of_set_inj[OF fin_map_graph_fmap fin_map_graph_fmap])
  apply (metis Rep_fmap_inject map_graph_inv)
done

section {* The type-system *}

subsection {* Types *}

text {* We only introduce a single datatype for types, as the move between vval and
  vbasic should be transparent *}

(*
*)


(*
datatype vbtype = 
    FSetBT vbtype
  | MapBT vbtype vbtype 
  | ListBT vbtype
  | PairBT vbtype vbtype 
  | RecordBT "vbtype list"
  | BoolBT 
  | NatBT
  | IntBT 
  | RatBT 
  | CharBT
  | QuoteBT
  | TokenBT
  | VarBT nat
(*  | SubtypeBT vbtype "vbasic \<Rightarrow> bool" *)

derive countable vbtype

fun vbt_subst :: "vbtype \<Rightarrow> vbtype list \<Rightarrow> vbtype" where
"vbt_subst (FSetBT a) f = FSetBT (vbt_subst a f)" |
"vbt_subst (MapBT a b) f = MapBT (vbt_subst a f) (vbt_subst b f)" |
"vbt_subst (ListBT a) f = ListBT (vbt_subst a f)" |
"vbt_subst (PairBT a b) f = PairBT (vbt_subst a f) (vbt_subst b f)" |
"vbt_subst (RecordBT as) f = RecordBT (map (\<lambda> a. vbt_subst a f) as)" |
"vbt_subst (VarBT x) f = (if (x < length f) then f!x else VarBT x)" |
"vbt_subst a f = a"
*)

datatype vtype =
    FSetT vtype
  | MapT vtype vtype 
  | ListT vtype
  | PairT vtype vtype 
  | RecordT "vtype list"
  | BoolT ("\<bool>")
  | NatT ("\<nat>")
  | IntT ("\<int>")
  | RatT ("\<rat>")
  | CharT
  | QuoteT "string fset"
  | TokenT
  | VarT nat
  | SetT vtype 
  | FuncT vtype vtype (infixr "→" 60)
(*  | RealT ("\<real>") *)
(*  | SubType vtype "vval \<rightarrow> tr" *)
(*  | BasicT "vbtype" *)

(*
primrec ProjBasicT :: "vtype \<Rightarrow> vbtype" where
"ProjBasicT (BasicT t) = t"
*)

(*
fun vt_subst :: "vtype \<Rightarrow> vtype list \<Rightarrow> vtype" ("_[_]vt") where
"vt_subst (FSetT a) f = FSetT (vt_subst a f)" |
"vt_subst (MapT a b) f = MapT (vt_subst a f) (vt_subst b f)" |
"vt_subst (ListT a) f = ListT (vt_subst a f)" |
"vt_subst (PairT a b) f = PairT (vt_subst a f) (vt_subst b f)" |
"vt_subst (RecordT as) f = RecordT (map (\<lambda> a. vt_subst a f) as)" |
"vt_subst (VarT x) f = (if (x < length f) then f!x else VarT x)" |
"vt_subst (SetT a) f = SetT (vt_subst a f)" |
"vt_subst (FuncT a b) f = FuncT (vt_subst a f) (vt_subst b f)" |
"vt_subst a f = a"
*)

derive countable vtype

instantiation vtype :: discrete_cpo
begin

definition below_vtype_def:
  "(x::vtype) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_vtype_def)

end

instantiation vtype :: predomain
begin

definition
  "(liftemb :: vtype u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> vtype u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::vtype itself). LIFTDEFL(vtype discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> vtype u)"
    unfolding liftemb_vtype_def liftprj_vtype_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(vtype) = liftemb oo (liftprj :: udom u \<rightarrow> vtype u)"
    unfolding liftemb_vtype_def liftprj_vtype_def liftdefl_vtype_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end


(*
fixrec ProjBasicT :: "vtype \<rightarrow> vbtype lift" where
"t \<noteq> \<bottom> \<Longrightarrow> ProjBasicT\<cdot>(BasicT\<cdot>t) = t"
*)

(*
abbreviation "FSetT t \<equiv> BasicT (FSetBT (ProjBasicT t))"
abbreviation "ListT t \<equiv> BasicT (ListBT (ProjBasicT t))"
abbreviation MapT :: "vtype \<Rightarrow> vtype \<Rightarrow> vtype" (infixr "\<Rightarrow>f" 60) where
"MapT s t \<equiv> BasicT (MapBT (ProjBasicT s) (ProjBasicT t))"
abbreviation PairT :: "vtype \<Rightarrow> vtype \<Rightarrow> vtype" (infix "\<times>v" 60) where
"PairT s t \<equiv> BasicT (PairBT (ProjBasicT s) (ProjBasicT t))"
abbreviation "RecordT xs \<equiv> BasicT (RecordBT (map (\<lambda>t. ProjBasicT t) xs))"

abbreviation BoolT :: vtype ("\<bool>") where 
"BoolT \<equiv> BasicT BoolBT"
abbreviation IntT :: vtype ("\<int>") where
"IntT \<equiv> BasicT IntBT"
abbreviation RatT :: vtype ("\<rat>") where
"RatT \<equiv> BasicT RatBT"
abbreviation "CharT \<equiv> BasicT CharBT"
abbreviation "QuoteT \<equiv> BasicT QuoteBT"
abbreviation "TokenT \<equiv> BasicT TokenBT"
*)

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [50, 51] 50)

subsection {* Basic value typing relation *}

inductive vbasic_type_rel :: "vbasic \<Rightarrow> vtype \<Rightarrow> bool" (infix ":\<^sub>b" 50) 
  and vbasic_type_list_rel :: "vbasic list \<Rightarrow> vtype list \<Rightarrow> bool" (infix ":\<^sub>r" 50) where
BoolI_type[intro]: "BoolI x :\<^sub>b BoolT" |
NatI_type[intro]: "NatI x :\<^sub>b NatT" |
IntI_type[intro]: "IntI x :\<^sub>b IntT" |
RatI_type[intro]: "RatI x :\<^sub>b RatT" |
CharI_type[intro]: "CharI x :\<^sub>b CharT" |
TokenI_type[intro]: "TokenI x :\<^sub>b TokenT" |
QuoteI_type[intro]: "x \<in>\<^sub>f xs \<Longrightarrow> QuoteI x :\<^sub>b QuoteT xs" |
ListI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> ListI xs :\<^sub>b ListT a" |
FinI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a; sorted xs; distinct xs \<rbrakk> \<Longrightarrow> FinI xs :\<^sub>b FSetT a" |
PairI_type[intro]: "\<lbrakk> x :\<^sub>b a; y :\<^sub>b b \<rbrakk> \<Longrightarrow> PairI x y :\<^sub>b PairT a b" |
MapI_type[intro]: "\<lbrakk> \<forall>(x,y)\<in>set xs. x :\<^sub>b a \<and> y :\<^sub>b b; sorted xs; distinct (map fst xs) \<rbrakk> \<Longrightarrow> MapI xs :\<^sub>b MapT a b" |
RecI_type[intro]: "\<lbrakk> xs :\<^sub>r ts \<rbrakk>  \<Longrightarrow> RecI xs :\<^sub>b RecordT ts" |
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
  QuoteT_type_cases [elim!]: "x :\<^sub>b QuoteT xs" and
  ListI_type_cases [elim]: "ListI xs :\<^sub>b t" and
  ListT_type_cases [elim!]: "x :\<^sub>b ListT a" and
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

definition bcarrier :: "vtype \<Rightarrow> vbasic set" where
"bcarrier t = {x. x :\<^sub>b t}"

definition vbtypes :: "vtype set" where
"vbtypes = {t. \<exists> x. x :\<^sub>b t}"

definition vbvalues :: "vval set" where
"vbvalues = {BasicV\<cdot>(Def x) | x t. x :\<^sub>b t}"

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
  by (auto intro!:MapI_type simp add:fdom_fmap_list fran_fmap_list FinMapI_def)

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

(*
inductive vtype_rel :: "vval \<Rightarrow> vtype \<Rightarrow> bool" (infix ":" 50) where
BotV_type[intro]: "\<bottom> : a" |
FuncV_type[intro]: "\<lbrakk> \<And> x. x : a \<Longrightarrow> f\<cdot>!x : b \<rbrakk>
                    \<Longrightarrow> FuncV\<cdot>f : FuncT a b"

SetV_type[intro]: "\<lbrakk> \<forall> x. \<lbrakk>x \<in>\<in> xs\<rbrakk>st \<longrightarrow> x :\<^sub>b a \<rbrakk> \<Longrightarrow> SetV\<cdot>xs : SetT a" |
BasicV_type[intro]: "x :\<^sub>b a \<Longrightarrow> BasicV\<cdot>(Def x) : BasicT a" |
*)

(* At the moment the type-system only supports functions of type vbtype \<rightarrow> vtype.
   Treatment of higher-order functions needs more work *)

inductive vtype_rel :: "vval \<Rightarrow> vtype \<Rightarrow> bool" (infix ":\<^sub>v" 50) where
BotV_type[intro]: "\<bottom> :\<^sub>v a" |
SetV_type[intro]: "\<lbrakk> \<forall> x. \<lbrakk>Def x \<in>\<in> xs\<rbrakk>st \<longrightarrow> x :\<^sub>b a \<rbrakk> \<Longrightarrow> SetV\<cdot>xs :\<^sub>v SetT a" |
BasicV_type[intro]: "x :\<^sub>b a \<Longrightarrow> BasicV\<cdot>(Def x) :\<^sub>v a" |
FuncV_type[intro]: "\<lbrakk> \<forall> x. x :\<^sub>b a \<longrightarrow> f\<cdot>!(BasicV\<cdot>(Def x)) :\<^sub>v b \<rbrakk> \<Longrightarrow> FuncV\<cdot>f :\<^sub>v a → b"

(*
|
FuncV_type[intro]: "\<forall>x. f\<cdot>!x \<noteq> \<bottom> \<longrightarrow> (\<exists> \<sigma>. (x : a[\<sigma>]vt \<and> f\<cdot>!x : b[\<sigma>]vt))
                    \<Longrightarrow> FuncV\<cdot>f : a → b"
*)

(*
FuncV_type[intro]: "\<forall>(x,y)\<in>cgraph (Rep_cfun (sfun_rep\<cdot>f)). (\<exists> \<sigma>. (x : a[\<sigma>]vt \<and> y : b[\<sigma>]vt))
                    \<Longrightarrow> FuncV\<cdot>f : FuncT a b"
*)

inductive_cases 
  SetT_type_cases[elim]: "x :\<^sub>v SetT a" and
  SetI_type_cases[elim!]: "SetI\<cdot>x :\<^sub>v t" and
  FuncT_type_cases[elim!]: "x :\<^sub>v a → b" and
  FuncI_type_cases[elim!]: "FuncV\<cdot>f :\<^sub>v t" 

lemma vbtypes_type_cases [elim]: 
  "\<lbrakk> a :\<^sub>v t; t \<in> vbtypes; \<And> x. \<lbrakk> a = BasicV\<cdot>(Def x); x :\<^sub>b t \<rbrakk> \<Longrightarrow> P; a = \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac a)
  apply (auto simp add:vbtypes_def)
done

definition vcarrier :: "vtype \<Rightarrow> vval set" where
"vcarrier t = {x. x :\<^sub>v t}"

lemma vcarrier [simp]: "x :\<^sub>v t \<Longrightarrow> x \<in> vcarrier t"
  by (simp add:vcarrier_def)

lemma vcarrier_simps [simp]:
  "\<bottom> \<in> vcarrier t"
  "vcarrier \<nat> = {\<bottom>} \<union> {BasicV\<cdot>(Def (NatI x)) | x . True}"
  "vcarrier \<int> = {\<bottom>} \<union> {BasicV\<cdot>(Def (IntI x)) | x . True}"
  "vcarrier \<rat> = {\<bottom>} \<union> {BasicV\<cdot>(Def (RatI x)) | x . True}"
  "vcarrier \<bool> = {\<bottom>} \<union> {BasicV\<cdot>(Def (BoolI x)) | x . True}"
  by (auto simp add:vcarrier_def)

lemma vbvalues_vbtypes [simp]: 
  "\<lbrakk> x \<in> vbvalues; x :\<^sub>v t \<rbrakk> \<Longrightarrow> t \<in> vbtypes"
  by (force simp add:vbvalues_def vbtypes_def)

subsection {* Some useful subtypes *}

(*
definition NatType :: "vtype" ("\<nat>") where
"NatType = SubType IntType {BasicV\<cdot>(Def (IntI x)) | x. x \<ge> 0}"

definition TotalFuncType :: "vtype \<Rightarrow> vtype \<Rightarrow> vtype" (infixr "⇸" 60) where
"TotalFuncType a b = SubType (FuncType a b) {FuncV\<cdot>f | f. cdom (Rep_cfun (sfun_rep\<cdot>f)) = carrier a}"
*)

(* Flatness of vbasic values *)

lemma BasicV_below_elim1 [elim!]:
  "\<lbrakk> BasicV\<cdot>(Def x) \<sqsubseteq> y; y = BasicV\<cdot>(Def x) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (case_tac y, simp_all)

lemma BasicV_below_elim2 [elim!]:
  "\<lbrakk> x \<sqsubseteq> BasicV\<cdot>(Def y); x = \<bottom> \<Longrightarrow> P; x = BasicV\<cdot>(Def y) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (case_tac x, simp_all add:flat_below_iff)

lemma flat_value_BasicV: "flat_value (BasicV\<cdot>(Def x))"
  apply (simp add:flat_value_def)
  apply (auto)
  apply (case_tac "xa \<le> xb")
  apply (metis BasicV_below_elim2 chain_mono)
  apply (metis BasicV_below_elim1 chain_mono linorder_le_cases)
done

subsection {* Injecting basic values into vval *}

fixrec ProjBasicV :: "vval \<rightarrow> vbasic lift" where
"x \<noteq> \<bottom> \<Longrightarrow> ProjBasicV\<cdot>(BasicV\<cdot>x) = x"

lemma ProjBasicV_bot [simp]: 
  "ProjBasicV\<cdot>\<bottom> = \<bottom>"
  "\<And> xs. xs \<noteq> \<bottom> \<Longrightarrow> ProjBasicV\<cdot>(SetV\<cdot>xs) = \<bottom>"
  "\<And> f. f \<noteq> \<bottom> \<Longrightarrow> ProjBasicV\<cdot>(FuncV\<cdot>f) = \<bottom>" 
  by (fixrec_simp)+

lemma ProjBasicV_simps [simp]:
  "ProjBasicV\<cdot>(SetV\<cdot>xs) = \<bottom>"
  "ProjBasicV\<cdot>(FuncV\<cdot>f) = \<bottom>"
  apply (case_tac "xs = \<bottom>", simp_all)
  apply (case_tac "f = \<bottom>", simp_all)
done

lemma BasicV_inv [simp]:
  "ProjBasicV\<cdot>(BasicV\<cdot>x) = x"
  by (case_tac x, simp_all)

definition IsBasicV where "IsBasicV v \<longleftrightarrow> ProjBasicV\<cdot>v \<noteq> \<bottom>"

lemma IsBasicV_simps [simp]: 
  "IsBasicV x \<Longrightarrow> x \<noteq> \<bottom>"
  "\<not> IsBasicV \<bottom>"
  "\<And> x. \<not> IsBasicV (SetV\<cdot>x)"
  "\<And> x. \<not> IsBasicV (FuncV\<cdot>x)"
  by (case_tac[!] x, simp_all add:IsBasicV_def)

lemma ProjBasicV_inv [simp] :
  "IsBasicV x \<Longrightarrow> BasicV\<cdot>(ProjBasicV\<cdot>x) = x"
  apply (simp add:IsBasicV_def)
  apply (case_tac x, simp_all)
done

definition vbasic_fun1 :: "(vbasic \<Rightarrow> vbasic) \<Rightarrow> vval" where
"vbasic_fun1 f \<equiv> FuncV\<cdot>(sfun_abs\<cdot>(BasicV oo (\<Lambda> (Def x). Def (f x)) oo ProjBasicV))"

definition vbasic_fun2 :: "(vbasic \<Rightarrow> vbasic \<Rightarrow> vbasic) \<Rightarrow> vval" where
"vbasic_fun2 f \<equiv> SFuncV2\<cdot>(\<Lambda> x y. BasicV\<cdot>((\<Lambda> (Def x) (Def y). Def (f x y))\<cdot>(ProjBasicV\<cdot>x)\<cdot>(ProjBasicV\<cdot>y)))"

fixrec ProjFuncV :: "vval \<rightarrow> (vval \<rightarrow>! vval)" where
"f \<noteq> \<bottom> \<Longrightarrow> ProjFuncV\<cdot>(FuncV\<cdot>f) = f"

lemma ProjFuncV_bot [simp]: 
  "ProjFuncV\<cdot>\<bottom> = \<bottom>" 
  "\<And> x y. \<lbrakk>x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> ProjFuncV\<cdot>(BasicV\<cdot>x) = \<bottom>" 
  "\<And> xs. xs \<noteq> \<bottom> \<Longrightarrow> ProjFuncV\<cdot>(SetV\<cdot>xs) = \<bottom>" 
  by (fixrec_simp)+

lemma ProjFuncV_simps [simp]:
  "ProjFuncV\<cdot>(BasicV\<cdot>v) = \<bottom>"
  "ProjFuncV\<cdot>(SetV\<cdot>xs) = \<bottom>"
  apply (case_tac v, simp_all)
  apply (case_tac "xs = \<bottom>", simp_all)
done

lemma FuncV_inv [simp]: "ProjFuncV\<cdot>(FuncV\<cdot>f) = f"
  by (case_tac "f = \<bottom>", simp_all)

lemma cont_vbasic_fun [simp]: "f \<bottom> = \<bottom> \<Longrightarrow> cont (f :: vbasic lift \<Rightarrow> vval)" 
  by (simp add: flatdom_strict2cont)

abbreviation "BFuncV \<equiv> \<Lambda> f. FuncV\<cdot>(\<Lambda>! x. f\<cdot>!(ProjBasicV\<cdot>x))"
abbreviation "ProjBFuncV \<equiv> \<Lambda> f. \<Lambda>! x. (ProjFuncV\<cdot>f)\<cdot>!(BasicV\<cdot>x)"

fixrec ProjSetV :: "vval \<rightarrow> vbasic lift cset" where
"xs \<noteq> \<bottom> \<Longrightarrow> ProjSetV\<cdot>(SetV\<cdot>xs) = xs"

lemma ProjSetV_bot [simp]: 
  "ProjSetV\<cdot>\<bottom> = \<bottom>" 
  "\<And> x y. \<lbrakk>x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> ProjSetV\<cdot>(BasicV\<cdot>x) = \<bottom>" 
  "\<And> xs. f \<noteq> \<bottom> \<Longrightarrow> ProjSetV\<cdot>(FuncV\<cdot>f) = \<bottom>" 
  by (fixrec_simp)+

lemma ProjSetV_simps [simp]:
  "ProjSetV\<cdot>(BasicV\<cdot>v) = \<bottom>"
  "ProjSetV\<cdot>(FuncV\<cdot>f) = \<bottom>"
  apply (case_tac v, simp_all)
  apply (case_tac "f = \<bottom>", simp_all)
done

lemma SetV_inv [simp]: "ProjSetV\<cdot>(SetV\<cdot>xs) = xs"
  by (case_tac "xs = \<bottom>", simp_all)

definition SetVS :: "vbasic set \<Rightarrow> vval" where
"SetVS xs = SetV\<cdot>(set2cset (Def ` xs))"

definition ProjSetVS :: "vval \<Rightarrow> vbasic set" where
"ProjSetVS v = Undef ` cset2set (ProjSetV\<cdot>v)"

lemma SetVS_inv [simp]: "ProjSetVS (SetVS xs) = xs"
  apply (simp add:SetVS_def ProjSetVS_def)
  apply (subgoal_tac "Def ` xs \<subseteq> flat")
  apply (force)
  apply (auto simp add:flat_def)
done

(*
lemma "\<exists> v. v :\<^sub>v t \<and> v \<noteq> \<bottom>"
  apply (induct t)
  apply (auto)
  apply (rule_tac x="BasicV\<cdot>(Def (FSetI {}\<^sub>f))" in exI) 
  apply (force)
  apply (rule_tac x="BasicV\<cdot>(Def (MapI []))" in exI) 
  apply (force)
  apply (rule_tac x="BasicV\<cdot>(Def (ListI []))" in exI) 
  apply (force)
*) 

end