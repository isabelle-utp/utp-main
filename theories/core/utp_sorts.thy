(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_sorts.thy                                                        *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
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
(*  fixes BoolUType :: "'a itself \<Rightarrow> nat" *)
  fixes BoolType  :: "'a UTYPE"
  assumes Inverse [simp] : "DestBool (MkBool b) = b"
(*  assumes MkBool_range: "range MkBool = {x. x :\<^sub>u BoolUType TYPE('a) \<and> \<D> x}" *)
  and     MkBool_range: "range MkBool = {x. x :! BoolType}"
  and     MkBool_monotype: "monotype BoolType"
begin

subsubsection {* Derived theorems *}

lemma Defined [simp] : "\<D> (MkBool b)"
  by (metis (lifting) MkBool_range dtype_relE mem_Collect_eq rangeI)

lemma MkBool_type [typing]: "MkBool b : BoolType"
  by (metis MkBool_range dtype_relE mem_Collect_eq rangeI)

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
  apply (case_tac "\<D> x")
  apply (simp)
  apply (subgoal_tac "x \<in> range MkBool")
  apply (auto)
  apply (metis (lifting) CollectI MkInt_range)
  apply (metis MkBool_range dtype_relI mem_Collect_eq)
done

lemma MkBool_cases_defined [elim]:
  "\<lbrakk> x :! BoolType; x = TrueV \<Longrightarrow> P; x = FalseV \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis MkBool_cases dtype_relE)

lemma MkBool_unq [simp]: 
  "MkBool True \<noteq> MkBool False"
  "MkBool False \<noteq> MkBool True"
  by (metis Inverse)+

end

subsection {* Order operation class *}

class LESS_EQ_SORT = VALUE + BOOL_SORT +
  fixes ulesseq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ulesseq_type: "ulesseq x y : BoolType"

subsection {* Minus operation class *}

class MINUS_SORT = VALUE +
  fixes utminus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

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

subsection {* Finite set sort *}

class FSET_SORT = BOOL_SORT +
  fixes   MkFSet   :: "'a fset \<Rightarrow> 'a"
  and     DestFSet :: "'a \<Rightarrow> 'a fset"
  and     FSetType :: "'a UTYPE \<Rightarrow> 'a UTYPE"
begin

definition FEmptyV  :: "'a" where
"FEmptyV = MkFSet \<lbrace>\<rbrace>"

definition FInsertV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"FInsertV x xs = MkFSet (finsert x (DestFSet xs))"

definition FUnionV  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"FUnionV xs ys = MkFSet (DestFSet xs \<union>\<^sub>f DestFSet ys)"

definition FInterV  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"FInterV xs ys = MkFSet (DestFSet xs \<inter>\<^sub>f DestFSet ys)"

definition FSubsetV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"FSubsetV xs ys = MkBool (DestFSet xs \<subseteq>\<^sub>f DestFSet ys)"

definition FMemberV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"FMemberV x xs = MkBool (x \<in>\<^sub>f DestFSet xs)"

definition FNMemberV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"FNMemberV x xs = MkBool (x \<notin>\<^sub>f DestFSet xs)"

end

(* FIXME: Add assumptions *)

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

class LIST_SIG = BOOL_SORT +
  fixes MkList :: "'a list \<Rightarrow> 'a"
  and   DestList :: "'a \<Rightarrow> 'a list"
  and   ListType :: "'a UTYPE \<Rightarrow> 'a UTYPE"
  (* The permissible element types of a list *)
  and   ListPerm :: "'a UTYPE set"
begin

subsubsection {* List Operators *}

definition NilV :: "'a" where
"NilV = MkList []"
notation NilV ("[]\<^sub>u")

definition ConsV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"ConsV x xs = MkList (x # DestList xs)"
notation ConsV (infixr "#\<^sub>u" 65)

definition ConcatV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"ConcatV xs ys = MkList (DestList xs @ DestList ys)"
notation ConcatV (infixr "@\<^sub>u" 65)

definition PrefixV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"PrefixV xs ys = MkBool (prefixeq (DestList xs) (DestList ys))"

end

class LIST_SORT = VALUE + LIST_SIG + LESS_EQ_SORT +
  assumes Inverse [simp] :
    "\<lbrakk> a \<in> ListPerm; set xs \<subseteq> dcarrier a \<rbrakk> \<Longrightarrow> DestList (MkList xs) = xs"
  and MkList_range: 
        "a \<in> ListPerm \<Longrightarrow> MkList ` {xs. set xs \<subseteq> dcarrier a} = dcarrier (ListType a)"
begin

lemma Defined [simp] : "\<lbrakk> a \<in> ListPerm; set xs \<subseteq> dcarrier a \<rbrakk> \<Longrightarrow> \<D> (MkList xs)"
  by (metis (lifting, full_types) MkList_range dcarrier_defined imageI mem_Collect_eq)

lemma MkList_type [typing]:
  "\<lbrakk> a \<in> ListPerm; set xs \<subseteq> dcarrier a \<rbrakk> \<Longrightarrow> MkList xs :! ListType a"
  by (metis (lifting) MkList_range dcarrier_dtype imageI mem_Collect_eq)

lemma ListType_witness [elim]:
  "\<lbrakk> a \<in> ListPerm; xs :! ListType a \<rbrakk> \<Longrightarrow> \<exists> ys. set ys \<subseteq> dcarrier a \<and> xs = MkList ys"
  apply (unfold dtype_as_dcarrier)
  apply (unfold MkList_range[THEN sym])
  apply (auto)
done

lemma ListType_elim [elim]:
  "\<lbrakk> xs :! ListType a; a \<in> ListPerm
   ; \<And> ys. \<lbrakk> xs = MkList ys; set ys \<subseteq> dcarrier a \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis ListType_witness)

lemma NilV_type [typing]:
  "a \<in> ListPerm \<Longrightarrow> NilV :! ListType a"
  by (auto intro:typing simp add:NilV_def)

lemma ConsV_type [typing]:
  "\<lbrakk> a \<in> ListPerm; x :! a; xs :! ListType a \<rbrakk> 
     \<Longrightarrow> ConsV x xs :! ListType a"
  by (force intro:typing simp add:ConsV_def)

lemma ConcatV_type [typing]:
  "\<lbrakk> a \<in> ListPerm; xs :! ListType a; ys :! ListType a \<rbrakk>
     \<Longrightarrow> ConcatV xs ys :! ListType a" 
  by (force intro:typing simp add:ConcatV_def)

lemma PrefixV_type [typing]:
  "\<lbrakk> a \<in> ListPerm; xs :! ListType a; ys :! ListType a \<rbrakk>
     \<Longrightarrow> PrefixV xs ys :! BoolType" 
  by (force intro:typing simp add:PrefixV_def)

text {* This lemma is sort of a lifting on the induction rule for lists *}

lemma ListType_cases:
  assumes "a \<in> ListPerm" "xs :! ListType a"
  shows "(xs = NilV) \<or> (\<exists> y ys. y :! a \<and> ys :! ListType a \<and> xs = ConsV y ys)"
proof -
  from assms have "xs \<in> MkList ` {xs. set xs \<subseteq> dcarrier a}"
    apply (unfold MkList_range)
    apply (unfold dcarrier_def)
    apply (auto)
  done

  then obtain ys where xsys: "xs = MkList ys" and yscarrier: "set ys \<subseteq> dcarrier a"
    by (auto)

  from assms(1) yscarrier
  have "MkList ys = NilV \<or> (\<exists>z zs. z :! a \<and> zs :! ListType a \<and> MkList ys = ConsV z zs)"
  proof (induct ys)
    case Nil thus ?case
      by (simp add:NilV_def)
  next
    case (Cons y ys) thus ?case
      apply (rule_tac disjI2)
      apply (rule_tac x="y" in exI)
      apply (rule_tac x="MkList ys" in exI)
      apply (auto intro:typing)
      apply (metis ConsV_def Inverse)
      apply (metis ConsV_def Inverse)
    done
  qed

  with xsys show ?thesis
    by (simp)
qed

lemma ConsV_FUNC2: "a \<in> ListPerm \<Longrightarrow> ConsV \<in> FUNC2 a (ListType a) (ListType a)"
  by (auto intro:typing simp add:FUNC2_def)

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
  and     MkString_range: "range MkString = {x. x : StringType \<and> \<D> x}"
begin

subsubsection {* Derived theorems *}

lemma Defined [simp] : "\<D> (MkStr s)"
  by (metis (lifting) CollectD MkString_range image_ident iso_tuple_UNIV_I)

lemma MkStr_type [typing] : "MkStr s : StringType"
  by (metis (lifting) CollectD MkString_range UNIV_I image_ident)

end

class STRING_LIST_SORT = STRING_SORT + LIST_SORT +
  assumes StringType_ListElTypes [closure]: "StringType \<in> ListElTypes"

subsection {* Real Sort *}

class REAL_SORT = VALUE +
  fixes MkReal :: "real \<Rightarrow> 'a"
  fixes DestReal :: "'a \<Rightarrow> real"
  fixes IsReal :: "'a \<Rightarrow> bool"
  fixes RealType :: "'a UTYPE" ("\<real>")
  assumes Defined [simp] : "Defined (MkReal r)"
  assumes Inverse [simp] : "DestReal (MkReal r) = r"
  assumes MkReal_type [typing] : "MkReal r : \<real>"

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

subsubsection {* Function Operators *}

definition AppV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"AppV f \<equiv> DestFunc f"

definition CompV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"CompV f g = MkFunc (DestFunc f \<circ> DestFunc g)"

subsubsection {* Default Simplifications *}

declare AppV_def [simp] CompV_def [simp]

end

class BASIC_SORT =
  INT_SORT + BOOL_SORT + STRING_SORT + REAL_SORT

class COMPOSITE_SORT =
  BASIC_SORT + PAIR_SORT + SET_SORT + FUNCTION_SORT


end
