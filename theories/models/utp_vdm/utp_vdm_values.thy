theory utp_vdm_values
imports 
  "../../core/utp_sorts" "../../core/utp_value" HOLCF 
  "~~/src/HOL/HOLCF/Library/HOL_Cpo" 
  "~~/src/HOL/Library/Char_ord" 
  "~~/src/HOL/Library/Monad_Syntax" 
  "../../utils/HOLCF_extra" "../../utils/Library_extra" Derive
begin

hide_const (open) Lattice.top
hide_const (open) Lattice.inf
hide_const (open) Lattice.sup

section {* Main domain types *}

subsection {* Basic (countable) values *}

text {* We introduce countable values using a normal datatype. This representation
  is not fully canonical, as we use lists to represents sets, maps and records.
  However, we later introduce constructors for these which use the correct types
  and thus ensure canonicity. *}
datatype vbasic 
  = PairI vbasic vbasic 
  | RatI "rat" 
  | IntI "int" 
  | CharI "char"
  | QuoteI "string" 
  | TokenI vbasic
  | ListI "vbasic list" 
  | FinI "vbasic list"
  | BoolI bool
  | RecI "(string * vbasic) list"
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

domain vval = SetV "vval cset" 
            | FuncV "vval \<rightarrow>! vval" 
            | BasicV "vbasic lift"

lemma vval_induct: 
  "\<lbrakk> P \<bottom>
   ; \<And>cset. cset \<noteq> \<bottom> \<Longrightarrow> P (SetV\<cdot>cset)
   ; \<And>sfun. sfun \<noteq> \<bottom> \<Longrightarrow> P (FuncV\<cdot>sfun)
   ; \<And>lift. lift \<noteq> \<bottom> \<Longrightarrow> P (BasicV\<cdot>lift)\<rbrakk> \<Longrightarrow> P x"
  by (induct x, metis vval.exhaust)

subsection {* Injections *}

text {* We create interface constructors for finite sets, maps and records which
  use derived subtypes as inputs and therefore preserve canonicity of vbasic *}

definition FSetI :: "vbasic fset \<Rightarrow> vbasic" where
"FSetI vs = FinI (flist vs)"

definition FinMapI :: "(vbasic, vbasic) fmap \<Rightarrow> vbasic" where
"FinMapI f = MapI (fmap_list f)"

definition RecordI :: "(string \<rightharpoonup> vbasic) \<Rightarrow> vbasic" where
"RecordI f = RecI (sorted_list_of_set (map_graph f))"

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

datatype vbtype = 
    FSetT vbtype
  | MapT vbtype vbtype 
  | ListT vbtype
  | PairT vbtype vbtype 
  | RecordT "(string * vbtype) list"
  | BoolT 
  | IntT 
  | RatT 
  | CharT
  | QuoteT
  | TokenT
 
datatype vtype 
  = SetType vtype 
  | FuncType vtype vtype (infixr "→" 60)
  | RealType ("\<real>")
  | SubType vtype "vval set"
  | BasicType vbtype

primrec ProjBType :: "vtype \<Rightarrow> vbtype" where
"ProjBType (BasicType t) = t"

abbreviation "FSetType t \<equiv> BasicType (FSetT (ProjBType t))"
abbreviation "ListType t \<equiv> BasicType (ListT (ProjBType t))"
abbreviation MapType :: "vtype \<Rightarrow> vtype \<Rightarrow> vtype" (infixr "\<Rightarrow>f" 60) where
"MapType s t \<equiv> BasicType (MapT (ProjBType s) (ProjBType t))"
abbreviation PairType :: "vtype \<Rightarrow> vtype \<Rightarrow> vtype" (infix "\<times>v" 60) where
"PairType s t \<equiv> BasicType (PairT (ProjBType s) (ProjBType t))"
abbreviation "RecordType xs \<equiv> RecordT (map (\<lambda>(n,t). (n, ProjBType t)) xs)"
abbreviation BoolType :: vtype ("\<bool>") where 
"BoolType \<equiv> BasicType BoolT"
abbreviation IntType :: vtype ("\<int>") where
"IntType \<equiv> BasicType IntT"
abbreviation RatType :: vtype ("\<rat>") where
"RatType \<equiv> BasicType RatT"
abbreviation "CharType \<equiv> BasicType CharT"
abbreviation "QuoteType \<equiv> BasicType QuoteT"
abbreviation "TokenType \<equiv> BasicType TokenT"


no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [50, 51] 50)

subsection {* Basic value typing relation *}

inductive vbasic_type_rel :: "vbasic \<Rightarrow> vbtype \<Rightarrow> bool" (infix ":\<^sub>b" 50) 
  and rec_type_rel :: "(string * vbasic) list \<Rightarrow> (string * vbtype) list \<Rightarrow> bool" (infix ":\<^sub>r" 50) where
BoolI_type[intro]: "BoolI x :\<^sub>b BoolT" |
IntI_type[intro]: "IntI x :\<^sub>b IntT" |
RatI_type[intro]: "RatI x :\<^sub>b RatT" |
CharI_type[intro]: "CharI x :\<^sub>b CharT" |
TokenI_type[intro]: "TokenI x :\<^sub>b TokenT" |
QuoteI_type[intro]: "QuoteI x :\<^sub>b QuoteT" |
ListI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> ListI xs :\<^sub>b ListT a" |
FinI_type[intro]: "\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>b a; sorted xs; distinct xs \<rbrakk> \<Longrightarrow> FinI xs :\<^sub>b FSetT a" |
PairI_type[intro]: "\<lbrakk> x :\<^sub>b a; y :\<^sub>b b \<rbrakk> \<Longrightarrow> PairI x y :\<^sub>b PairT a b" |
MapI_type[intro]: "\<lbrakk> \<forall>(x,y)\<in>set xs. x :\<^sub>b a \<and> y :\<^sub>b b; sorted xs; distinct (map fst xs) \<rbrakk> \<Longrightarrow> MapI xs :\<^sub>b MapT a b" |
RecI_type[intro]: "\<lbrakk> xs :\<^sub>r ts \<rbrakk>  \<Longrightarrow> RecI xs :\<^sub>b RecordT ts" |
RecCons_type[intro]: "\<lbrakk> x :\<^sub>b t; xs :\<^sub>r ts \<rbrakk> \<Longrightarrow> ((n,x) # xs) :\<^sub>r ((n,t) # ts)" |
RecNil_type[intro]: "[] :\<^sub>r []"

inductive_cases 
  BoolI_type_cases [elim!]: "x :\<^sub>b BoolT" and
  IntI_type_cases [elim!]: "x :\<^sub>b IntT" and
  RatI_type_cases [elim!]: "x :\<^sub>b RatT" and
  CharI_type_cases [elim!]: "x :\<^sub>b CharT" and
  TokenI_type_cases [elim!]: "x :\<^sub>b TokenT" and
  QuoteI_type_cases [elim!]: "x :\<^sub>b QuoteT" and
  ListI_type_cases [elim!]: "x :\<^sub>b ListT a" and
  FinI_type_cases [elim!]: "x :\<^sub>b FSetT a" and
  PairI_type_cases [elim!]: "x :\<^sub>b PairT a b" and
  MapI_type_cases [elim]: "x :\<^sub>b MapT a b"

definition bcarrier :: "vbtype \<Rightarrow> vbasic set" where
"bcarrier t = {x. x :\<^sub>b t}"

text {* We introduce a couple of derived typing rules *}

lemma NilI_type[intro]: "ListI [] :\<^sub>b ListT a"
  by auto

lemma ConsI_type[intro]: 
  "\<lbrakk> x :\<^sub>b a; ListI xs :\<^sub>b ListT a \<rbrakk> \<Longrightarrow> ListI (x # xs) :\<^sub>b ListT a"
  by (auto intro!: ListI_type)

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
  apply (subgoal_tac "xs = fmap_list (list_fmap xs)")
  apply (subgoal_tac "\<forall>x\<in>dom (Rep_fmap (list_fmap xs)). x :\<^sub>b a")
  apply (subgoal_tac "\<forall>y\<in>ran (Rep_fmap (list_fmap xs)). y :\<^sub>b b")
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

inductive vtype_rel :: "vval \<Rightarrow> vtype \<Rightarrow> bool" (infix ":" 50) where
BotV_type[intro]: "\<bottom> : a" |
SetV_type[intro]: "\<lbrakk> \<forall> x. \<lbrakk>x \<in>\<in> xs\<rbrakk>wt \<longrightarrow> x : a \<rbrakk> \<Longrightarrow> SetV\<cdot>xs : SetType a" |
FuncV_type[intro]: "\<lbrakk> \<forall>x\<in>cdom (Rep_cfun (sfun_rep\<cdot>f)). x : a
                    ; \<forall>y\<in>cran (Rep_cfun (sfun_rep\<cdot>f)). y : b \<rbrakk> 
                    \<Longrightarrow> FuncV\<cdot>f : a → b" |
BasicV_type[intro]: "x :\<^sub>b t \<Longrightarrow> BasicV\<cdot>(Def x) : BasicType t" |
SubType_type[intro]: "\<lbrakk> x : t; x \<in> P \<union> {\<bottom>} \<rbrakk> \<Longrightarrow> x : SubType t P"

inductive_cases 
  SetV_type_cases [elim!]: "x : SetType a" and
  FuncV_type_cases [elim!]: "x : a → b" and
  BasicV_type_cases [elim!]: "x : BasicType t" and
  SubType_type_cases [elim!]: "x : SubType t P"  

definition carrier :: "vtype \<Rightarrow> vval set" where
"carrier t = {x. x : t}"

lemma carrier [simp]: "x : t \<Longrightarrow> x \<in> carrier t"
  by (simp add:carrier_def)

subsection {* Some useful subtypes *}

definition NatType :: "vtype" ("\<nat>") where
"NatType = SubType IntType {BasicV\<cdot>(Def (IntI x)) | x. x \<ge> 0}"

definition TotalFuncType :: "vtype \<Rightarrow> vtype \<Rightarrow> vtype" (infixr "⇸" 60) where
"TotalFuncType a b = SubType (FuncType a b) {FuncV\<cdot>f | f. cdom (Rep_cfun (sfun_rep\<cdot>f)) = carrier a}"

end