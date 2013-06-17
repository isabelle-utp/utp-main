(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_sorts.thy                                                        *)
(* Author: Mrank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Value Sorts *}

theory utp_sorts
imports "../utp_common" utp_value
begin

text {* Some sorts still need to be developed in terms of their operators. *}

subsection {* Bottom Element Sort *}

class BOT_SORT = VALUE +
  fixes ubot :: "'a"
  assumes not_Defined_ubot [simp] : "\<not> \<D> ubot"

subsubsection {* Notations *}

notation ubot ("\<bottom>v")

subsubsection {* Theorems *}

theorem Defined_not_eq_bot [simp] :
"\<D> v \<Longrightarrow> v \<noteq> \<bottom>v"
  by (metis not_Defined_ubot)

subsubsection {* Partial Functions (Simon) *}

context BOT_SORT
begin

definition to_map :: "('b \<Rightarrow> 'a) \<Rightarrow> ('b \<rightharpoonup> 'a)" where
"to_map f = (\<lambda> x . if (f x = \<bottom>v) then None else Some (f x))"

definition from_map :: "('b \<rightharpoonup> 'a) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"from_map m = (\<lambda> x . case (m x) of Some y \<Rightarrow> y | None \<Rightarrow> \<bottom>v)"

definition mdom :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set" where
"mdom f = dom (to_map f)"

definition mran :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a set" where
"mran f = ran (to_map f)"

definition fempty :: "'b \<Rightarrow> 'a" where
"fempty = from_map Map.empty"

subsubsection {* Graph of Functions *}

text {* Since we can only inject certain kinds of data, to allow the injection
  of functions we must first strip out part of the domain before graphing. *}

definition to_graph_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'a) set" where
"to_graph_on a f = {(x, f x) | x . x \<in> a}"

abbreviation to_graph :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'a) set" where
"to_graph f \<equiv> to_graph_on (mdom f) f"

definition from_graph :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a)" where
"from_graph s =
 (\<lambda> x . if (\<exists> y . (x, y) \<in> s) then (SOME y . (x, y) \<in> s) else \<bottom>v)"

text {* A function with a domain restriction. *}

definition func_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"func_on a f = (\<lambda> x . if (x \<in> a) then (f x) else \<bottom>v)"

subsubsection {* Simon's Theorems *}

theorem to_map_inv [simp] :
"from_map (to_map x) = x"
  by (auto simp: to_map_def from_map_def)

theorem from_map_inv [simp] :
"\<bottom>v \<notin> ran m \<Longrightarrow> to_map (from_map m) = m"
apply (auto simp: to_map_def from_map_def ran_def dom_def)
apply (rule ext)
(* The following step is a little slow. *)
apply (metis not_Some_eq option.simps)
done

theorem mdom_mran [dest] :
"x \<in> mdom f \<Longrightarrow> f x \<in> mran f"
apply (simp add: mdom_def mran_def to_map_def)
apply (case_tac "f x = \<bottom>v")
apply (auto simp: ran_def)
done

theorem mdom_elseBot [simp] :
"mdom (\<lambda> x . if (P x) then (f x) else \<bottom>v) = {x . (P x) \<and> x \<in> mdom f}"
  by (auto simp: mdom_def to_map_def dom_def)

theorem mran_elseBot [simp] :
"mran (\<lambda> x. if (P x) then (f x) else \<bottom>v) = {f x | x . (P x) \<and> f x \<noteq> \<bottom>v}"
  by (auto simp: mran_def to_map_def ran_def)

theorem to_graph_on_inv [simp] :
"from_graph (to_graph_on a f) = func_on a f"
  by (auto simp: to_graph_on_def from_graph_def func_on_def)

theorem func_on_mdom [simp] :
"func_on (mdom f) f = f"
apply (simp add: func_on_def)
apply (rule ext)
apply (case_tac "x \<in> mdom f")
apply (force)
apply (force simp: mdom_def to_map_def)
done

theorem to_graph_inv [simp] :
"from_graph (to_graph f) = f"
  by (simp)
end

subsection {* Integer Sort *}

text {* The @{term "INT_SORT"} and most other sorts in this file
define three constants and several properties. The constants are an
injection @{term "MkInt"}, a projection @{term "DestInt"}, and 
a type. *}

class INT_SORT = VALUE +
  fixes MkInt    :: "int \<Rightarrow> 'a"
  fixes DestInt  :: "'a \<Rightarrow> int"
  fixes IntUType :: "'a itself \<Rightarrow> nat"
  -- {* The injection can always be reversed. *}
  assumes Inverse [simp] : "DestInt (MkInt i) = i"
  -- {* The values produced by the injection are precisely the well typed 
        and defined integer values. *}
  assumes MkInt_range: "range MkInt = {x. x :\<^sub>u IntUType TYPE('a) \<and> \<D> x}"
begin

subsubsection {* Derived theorems *}

definition IntType :: "'a UTYPE" where
"IntType = Abs_UTYPE (IntUType TYPE('a))"

lemma IntUType_UTYPES [simp]: "IntUType TYPE('a) \<in> UTYPES TYPE('a)"
  apply (simp add:UTYPES_def)
  apply (metis (lifting) CollectD MkInt_range rangeI)
done

text {* The results of the injection are always defined. *}

lemma Defined [simp]: "\<D> (MkInt i)"
  by (metis (lifting) CollectD MkInt_range rangeI)

lemma MkInt_type [typing]: "MkInt n : IntType"
  apply (simp add:type_rel_def IntType_def)
  apply (metis (lifting) CollectD MkInt_range rangeI)
done

lemma MkInt_cases [elim]: 
  "\<lbrakk> x : IntType; \<not> \<D> x \<Longrightarrow> P; \<And> i. x = MkInt i \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (case_tac "\<D> x")
  apply (simp)
  apply (subgoal_tac "x \<in> range MkInt")
  apply (auto)
  apply (simp add:IntType_def type_rel_def)
  apply (metis (lifting) CollectI MkInt_range)
done

subsubsection {* Integer Operators *}

definition UMinusV :: "'a \<Rightarrow> 'a" where
"UMinusV i = MkInt (-DestInt(i))"
notation UMinusV ("-v _" [81] 80)

definition PlusV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"PlusV i1 i2 = MkInt (DestInt(i1) + DestInt(i2))"
notation PlusV (infixl "+v" 65)

definition MinusV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"MinusV i1 i2 = MkInt (DestInt(i1) - DestInt(i2))"
notation MinusV (infixl "-v" 65)

definition MultV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"MultV i1 i2 = MkInt (DestInt(i1) * DestInt(i2))"
notation MultV (infixl "*v" 70)

definition DivideV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"DivideV i1 i2 = MkInt (DestInt(i1) div DestInt(i2))"
notation DivideV (infixl "divv" 70)

definition ModulusV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"ModulusV i1 i2 = MkInt (DestInt(i1) mod DestInt(i2))"
notation ModulusV (infixl "modv" 70)

subsubsection {* Default Simplifications *}

declare UMinusV_def [simp]
declare PlusV_def [simp]
declare MinusV_def [simp]
declare MultV_def [simp]
declare DivideV_def [simp]
declare ModulusV_def [simp]

end

subsection {* Boolean Sort *}

class BOOL_SORT = VALUE +
  fixes MkBool :: "bool \<Rightarrow> 'a"
  fixes DestBool :: "'a \<Rightarrow> bool"
  fixes BoolUType :: "'a itself \<Rightarrow> nat"
  assumes Inverse [simp] : "DestBool (MkBool b) = b"
  assumes MkBool_range: "range MkBool = {x. x :\<^sub>u BoolUType TYPE('a) \<and> \<D> x}"
begin

subsubsection {* Derived theorems *}

definition BoolType :: "'a UTYPE" where
"BoolType = Abs_UTYPE (BoolUType TYPE('a))"

lemma BoolUType_UTYPES [simp]: "BoolUType TYPE('a) \<in> UTYPES TYPE('a)"
  apply (simp add:UTYPES_def)
  apply (metis (lifting) CollectD MkBool_range rangeI)
done

lemma Defined [simp] : "\<D> (MkBool b)"
  by (metis (lifting) CollectE MkBool_range rangeI)

lemma MkBool_type [typing]: "MkBool b : BoolType"
  apply (simp add:type_rel_def BoolType_def)
  apply (metis (lifting) CollectD MkBool_range rangeI)
done

lemma DestBool_inj: "inj_on DestBool (range MkBool)"
  by (simp add:inj_on_def)

lemma MkBool_inj: "inj MkBool"
  by (smt Inverse injI)

lemma DestBool_inv: "x \<in> range MkBool \<Longrightarrow> MkBool (DestBool x) = x"
  by (smt DestBool_inj Inverse inj_on_iff rangeI)

subsubsection {* Boolean Operators *}

definition TrueV :: "'a" where
"TrueV = MkBool True"

definition FalseV :: "'a" where
"FalseV = MkBool False"

text {* The precedence of boolean operators is similar to those in HOL. *}

definition NotV :: "'a \<Rightarrow> 'a" where
"NotV x = MkBool (\<not> DestBool x)"
notation NotV ("\<not>v _" [40] 40)

definition AndV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"AndV b1 b2 = MkBool (DestBool(b1) \<and> DestBool(b2))"
notation AndV (infixr "\<and>v" 35)

definition OrV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"OrV b1 b2 = MkBool (DestBool(b1) \<or> DestBool(b2))"
notation OrV (infixr "\<and>v" 30)

definition ImpliesV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"ImpliesV b1 b2 = MkBool (DestBool(b1) \<longrightarrow> DestBool(b2))"
notation OrV (infixr "\<Rightarrow>v" 25)

definition IffV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"IffV b1 b2 = MkBool (DestBool(b1) \<longleftrightarrow> DestBool(b2))"
notation IffV (infixr "\<Leftrightarrow>v" 25)

subsubsection {* Default Simplifications *}

declare TrueV_def [simp]
declare FalseV_def [simp]
declare NotV_def [simp]
declare AndV_def [simp]
declare OrV_def [simp]
declare ImpliesV_def [simp]
declare IffV_def [simp]

lemma MkBool_cases [elim]: 
  "\<lbrakk> x : BoolType; \<not> \<D> x \<Longrightarrow> P; x = TrueV \<Longrightarrow> P; x = FalseV \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add:BoolType_def type_rel_def)
  apply (case_tac "\<D> x")
  apply (simp)
  apply (subgoal_tac "x \<in> range MkBool")
  apply (auto)
  apply (metis (lifting) CollectI MkInt_range)
  apply (metis (lifting) CollectI MkBool_range)
done  

lemma MkBool_unq [simp]: 
  "MkBool True \<noteq> MkBool False"
  "MkBool False \<noteq> MkBool True"
  by (metis Inverse)+

end

subsection {* Countable Subsorts *}

class COUNTABLE = VALUE +
  fixes   Countable :: "'a set"
  and     count     :: "'a \<Rightarrow> nat"
  assumes count_inj: "inj_on count Countable"

subsection {* Sets of countable values *}

class SET_COUNTABLE = COUNTABLE +
  fixes   MkSetC   :: "'a set \<Rightarrow> 'a"
  and     DestSetC :: "'a \<Rightarrow> 'a set"
  and     SetCType :: "'a UTYPE \<Rightarrow> 'a UTYPE"
  assumes Inverse: "xs \<subseteq> Countable \<Longrightarrow> DestCSet (MkCSet vs) = vs"
  and     MkSetC_range: "range MkSetC = {xs. xs : SetCType t 
                                           \<and> (\<forall>x\<in>DestSetC xs. x : t)
                                        }"


subsection {* Set Sort *}

class SET_SORT_PRE = VALUE +
  fixes MkSet :: "'a set \<Rightarrow> 'a"
  fixes DestSet :: "'a \<Rightarrow> 'a set"
  fixes IsSetElemType :: "'a UTYPE \<Rightarrow> bool"
  fixes SetType :: "'a UTYPE \<Rightarrow> 'a UTYPE"
begin

abbreviation IsSet :: "'a set \<Rightarrow> bool" where
"IsSet xs \<equiv> (\<exists> t. IsSetElemType t \<and> (\<forall>x\<in>xs. x : t \<and> \<D> x))"

end

class SET_SORT = SET_SORT_PRE +
  assumes Inverse [simp]:
    "IsSet vs \<Longrightarrow> DestSet (MkSet vs) = vs"
  assumes MkSet_range: 
    "IsSetElemType t \<Longrightarrow> MkSet ` Pow (dcarrier t) = dcarrier (SetType t)"

begin

lemma Defined [simp] :
  "IsSet vs \<Longrightarrow> \<D> (MkSet vs)"
  apply (auto)
  apply (drule MkSet_range)
  apply (auto simp add:set_eq_iff dcarrier_def)
done

lemma MkSet_type [typing]: 
  "\<lbrakk> IsSetElemType t; \<forall> x \<in> xs. x : t \<and> \<D> x \<rbrakk> \<Longrightarrow> MkSet xs : SetType t"
  apply (drule MkSet_range)
  apply (auto simp add:set_eq_iff dcarrier_def)
done

subsubsection {* Set Operators *}

definition UnionV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"UnionV v1 v2 = MkSet ((DestSet v1) \<union> (DestSet v2))"
notation UnionV (infixl "\<union>v" 65)

definition InterV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"InterV v1 v2 = MkSet ((DestSet v1) \<inter> (DestSet v2))"
notation InterV (infixl "\<inter>v" 70)

definition diff :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"diff v1 v2 = MkSet ((DestSet v1) - (DestSet v2))"
notation diff (infixl "\\v" 75)

definition MemberV :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"MemberV v1 v2 = (v1 \<in> (DestSet v2))"
notation MemberV ("(_/ \<in>v _)" [50, 51] 50)

definition NotMemberV :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"NotMemberV v1 v2 = (v1 \<notin> (DestSet v2))"
notation NotMemberV ("(_/ \<notin>v _)" [50, 51] 50)

definition SubsetEqV :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"SubsetEqV v1 v2 = ((DestSet v1) \<subseteq> (DestSet v2))"
notation SubsetEqV ("(_/ \<subseteq>v _)" [50, 51] 50)

definition SubsetV :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"SubsetV v1 v2 = ((DestSet v1) \<subset> (DestSet v2))"
notation SubsetV ("(_/ \<subset>v _)" [50, 51] 50)

subsubsection {* Default Simplifications *}

declare UnionV_def [simp]
declare InterV_def [simp]
declare MemberV_def [simp]
declare NotMemberV_def [simp]
declare SubsetEqV_def [simp]
declare SubsetV_def [simp]
end


subsection {* Character Sort *}

class CHAR_SORT = VALUE +
  fixes MkChar :: "char \<Rightarrow> 'a"
  fixes DestChar :: "'a \<Rightarrow> char"
  fixes CharType :: "'a UTYPE"
  assumes Inverse [simp] : "DestChar (MkChar c) = c"
  assumes MkChar_range: "range MkChar = {x. x : CharType \<and> \<D> x}"
begin

subsubsection {* Derived theorems *}

lemma Defined [simp] : "Defined (MkChar c)"
  by (metis (lifting) CollectD MkChar_range rangeI)

lemma MkChar_type [typing] : "MkChar x : CharType"
  by (metis (lifting) CollectD MkChar_range rangeI)

end

subsection {* String Sort *}

class STRING_SORT = VALUE +
  fixes MkStr :: "string \<Rightarrow> 'a"
  fixes DestStr :: "'a \<Rightarrow> string"
  fixes StringType :: "'a UTYPE"
  assumes Inverse [simp] : "DestStr (MkStr s) = s"
  assumes MkString_range: "range MkString = {x. x : StringType \<and> \<D> x}"
begin

subsubsection {* Derived theorems *}

lemma Defined [simp] : "\<D> (MkStr s)"
  by (metis (lifting) CollectD MkString_range image_ident iso_tuple_UNIV_I)

lemma MkStr_type [typing] : "MkStr s : StringType"
  by (metis (lifting) CollectD MkString_range UNIV_I image_ident)

end

subsection {* Real Sort *}

class REAL_SORT = VALUE +
  fixes MkReal :: "real \<Rightarrow> 'a"
  fixes DestReal :: "'a \<Rightarrow> real"
  fixes IsReal :: "'a \<Rightarrow> bool"
  fixes RealType :: "'a UTYPE" ("\<real>")
  assumes Defined [simp] : "Defined (MkReal r)"
  assumes Inverse [simp] : "DestReal (MkReal r) = r"
  assumes MkReal_type [typing] : "MkReal r : \<real>"

subsection {* Pair Sort *}

class PAIR_SORT = VALUE +
  fixes MkPair :: "('a \<times> 'a) \<Rightarrow> 'a"
  fixes DestPair :: "'a \<Rightarrow> ('a \<times> 'a)"
  fixes PairType :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> 'a UTYPE"
  fixes InjTypes :: "'a UTYPE set"
  assumes Inverse [simp] :
    "Defined (MkPair v1_v2) \<Longrightarrow> DestPair (MkPair v1_v2) = v1_v2"
  assumes MkPair_range: "MkPair ` Collect IsPair = {x. (\<exists> a b. x : PairType a b) \<and> \<D> x}"

subsection {* List Sort *}

class LIST_SIG = 
  fixes MkList :: "'a list \<Rightarrow> 'a"
  and   DestList :: "'a \<Rightarrow> 'a list"
  and   ListType :: "'a UTYPE \<Rightarrow> 'a UTYPE"
begin

subsubsection {* List Operators *}

definition NilV :: "'a" where
"NilV = MkList []"
notation NilV ("[]v")

definition ConsV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"ConsV x l = MkList (x # DestList(l))"
notation ConsV (infixr "#" 65)

definition ConcatV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"ConcatV l1 l2 = MkList (DestList(l1) @ DestList (l2))"
notation ConcatV (infixr "@" 65)

subsubsection {* Default Simplifications *}

declare NilV_def [simp]
declare ConsV_def [simp]
declare ConcatV_def [simp]
end

class LIST_SORT = VALUE + LIST_SIG +
  assumes Inverse [simp] :
    "\<lbrakk> \<forall> x\<in>set xs. x : a; \<D> (MkList xs) \<rbrakk> \<Longrightarrow> DestList (MkList xs) = xs"
  and ListType_cases:
    "\<And> xs. \<lbrakk> xs : ListType a; \<D> xs \<rbrakk> 
           \<Longrightarrow> (xs = NilV) \<or> (\<exists> y ys. y : a \<and> ys : ListType a \<and> xs = ConsV y ys)"
  and MkList_type [typing]:
    "\<lbrakk> \<forall> x \<in> set xs. x : a \<rbrakk> \<Longrightarrow> MkList xs : ListType a"

subsection {* Function Sort *}

class FUNCTION_SORT = BOT_SORT +
  fixes MkFunc   :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  and   DestFunc :: "'a \<Rightarrow> ('a \<Rightarrow> 'a)"
  and   IsFunc   :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  and   FuncType :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> 'a UTYPE"
  assumes Inverse [simp]: "IsFunc f \<Longrightarrow> DestFunc (MkFunc f) = f"
  and     Defined [simp]: "IsFunc f \<Longrightarrow> Defined (MkFunc f)"
  and     MkFunc_range: "{MkFunc f | f . \<forall> x : a. f x : b \<and> IsFunc f} = dcarrier (FuncType a b)"
  and     FuncType_inj1: "FuncType a1 b1 = FuncType a2 b2 \<Longrightarrow> a1 = a2"
  and     FuncType_inj2: "FuncType a1 b1 = FuncType a2 b2 \<Longrightarrow> b1 = b2"

begin

lemma MkFunc_type [typing]: 
  "\<lbrakk> \<forall> x : a. f x : b; IsFunc f \<rbrakk> \<Longrightarrow> MkFunc f : FuncType a b"
  apply (insert MkFunc_range[of a b])
  apply (auto simp add:dcarrier_def)
done

lemma DestFunc_type [typing]:
  "\<lbrakk> f : FuncType a b; x : a; \<D> f \<rbrakk> \<Longrightarrow> DestFunc f x : b"
  apply (insert MkFunc_range[of a b])
  apply (auto simp add:dcarrier_def)
  apply (smt CollectE CollectI Inverse)
done

definition func_inp_type :: "'a UTYPE \<Rightarrow> 'a UTYPE" where
"func_inp_type t = (SOME a. \<exists> b. t = FuncType a b)"

definition func_out_type :: "'a UTYPE \<Rightarrow> 'a UTYPE" where
"func_out_type t = (SOME b. \<exists> a. t = FuncType a b)"

lemma func_inp_type [simp]:
  "func_inp_type (FuncType a b) = a"
  apply (simp add:func_inp_type_def)
  apply (rule some_equality)
  apply (auto dest: FuncType_inj1)
done

lemma func_out_type [simp]:
  "func_out_type (FuncType a b) = b"
  apply (simp add:func_out_type_def)
  apply (rule some_equality)
  apply (auto dest: FuncType_inj2)
done

subsubsection {* Function Type *}

definition FuncBetw :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"FuncBetw a b f \<equiv> f \<in> MkFunc ` Collect IsFunc
                \<and> (mdom (DestFunc f) \<subseteq> a)
                \<and> (mran (DestFunc f) \<subseteq> b)"

subsubsection {* Function Operators *}

definition AppV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"AppV f \<equiv> DestFunc f"

definition CompV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"CompV f g = MkFunc (DestFunc f \<circ> DestFunc g)"

definition IdV_on :: "'a set \<Rightarrow> 'a" where
"IdV_on a = MkFunc (func_on a id)"

subsubsection {* Default Simplifications *}

declare AppV_def [simp] CompV_def [simp] IdV_on_def [simp]

end


class BASIC_SORT =
  INT_SORT + BOOL_SORT + STRING_SORT + REAL_SORT

class COMPOSITE_SORT =
  BASIC_SORT + PAIR_SORT + SET_SORT + FUNCTION_SORT


end
