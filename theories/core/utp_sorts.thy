(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_sorts.thy                                                        *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Value Sorts *}

theory utp_sorts
imports "../utp_common"
begin

hide_const (open) Lattice.top
hide_const (open) Lattice.inf
hide_const (open) Lattice.sup

text {* Some sorts still need to be developed in terms of their operators. *}

subsection {* Root Value Sort *}

text {*
  It is still an open issue whether to include a notion of well-formedness
  of a value. From our experience with concrete value models, we noticed that
  this can be useful. Examples are the HO model and Simon's injectable values.
  Despite this, for reasons of simplicity, we require refinement to be defined
  on the entire carrier set of the value type. Possible this design needs to
  be evaluated too.
*}

text {*
  It would be nice to introduce typing in @{text "VALUE_SORT"} but this seems
  not to be feasible as it would require a second HOL type parameter in the
  respective fixed constant, namely for the underlying value type. Our design
  thus opted for introducing the connection to types by virtue of locales.
*}

class VALUE_SORT =
  fixes Defined :: "'a \<Rightarrow> bool" ("\<D>")

subsection {* Bottom Element Sort *}

class BOT_SORT = VALUE_SORT + bot +
  assumes not_Defined_bot [simp] : "\<not> \<D> bot"
begin

subsubsection {* Notations *}

notation bot ("\<bottom>v")

subsubsection {* Theorems *}

theorem Defined_not_eq_bot [simp] :
"Defined v \<Longrightarrow> v \<noteq> \<bottom>v"
apply (auto)
done

subsubsection {* Partial Functions (Simon) *}

definition to_map :: "('b \<Rightarrow> 'a) \<Rightarrow> ('b \<rightharpoonup> 'a)" where
"to_map f = (\<lambda> x . if (f x = \<bottom>v) then None else Some (f x))"

definition from_map :: "('b \<rightharpoonup> 'a) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"from_map m = (\<lambda> x . case (m x) of Some y \<Rightarrow> y | None \<Rightarrow> \<bottom>v)"

definition fdom :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set" where
"fdom f = dom (to_map f)"

definition fran :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a set" where
"fran f = ran (to_map f)"

definition fempty :: "'b \<Rightarrow> 'a" where
"fempty = from_map Map.empty"

subsubsection {* Graph of Functions *}

text {* Since we can only inject certain kinds of data, to allow the injection
  of functions we must first strip out part of the domain before graphing. *}

definition to_graph_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'a) set" where
"to_graph_on a f = {(x, f x) | x . x \<in> a}"

abbreviation to_graph :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'a) set" where
"to_graph f \<equiv> to_graph_on (fdom f) f"

definition from_graph :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a)" where
"from_graph s =
 (\<lambda> x . if (\<exists> y . (x, y) \<in> s) then (SOME y . (x, y) \<in> s) else \<bottom>v)"

text {* A function with a domain restriction. *}

definition func_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"func_on a f = (\<lambda> x . if (x \<in> a) then (f x) else \<bottom>v)"

subsubsection {* Simon's Theorems *}

theorem to_map_inv [simp] :
"from_map (to_map x) = x"
apply (auto simp: to_map_def from_map_def)
done

theorem from_map_inv [simp] :
"\<bottom>v \<notin> ran m \<Longrightarrow> to_map (from_map m) = m"
apply (auto simp: to_map_def from_map_def ran_def dom_def)
apply (rule ext)
(* The following step is a little slow. *)
apply (metis not_Some_eq option.simps)
done

theorem fdom_fran [dest] :
"x \<in> fdom f \<Longrightarrow> f x \<in> fran f"
apply (simp add: fdom_def fran_def to_map_def)
apply (case_tac "f x = \<bottom>v")
apply (auto simp: ran_def)
done

theorem fdom_elseBot [simp] :
"fdom (\<lambda> x . if (P x) then (f x) else \<bottom>v) = {x . (P x) \<and> x \<in> fdom f}"
apply (auto simp: fdom_def to_map_def dom_def)
done

theorem fran_elseBot [simp] :
"fran (\<lambda> x. if (P x) then (f x) else \<bottom>v) = {f x | x . (P x) \<and> f x \<noteq> \<bottom>v}"
apply (auto simp: fran_def to_map_def ran_def)
done

theorem to_graph_on_inv [simp] :
"from_graph (to_graph_on a f) = func_on a f"
apply (auto simp: to_graph_on_def from_graph_def func_on_def)
done

theorem func_on_fdom [simp] :
"func_on (fdom f) f = f"
apply (simp add: func_on_def)
apply (rule ext)
apply (case_tac "x \<in> fdom f")
apply (force)
apply (force simp: fdom_def to_map_def)
done

theorem to_graph_inv [simp] :
"from_graph (to_graph f) = f"
apply (simp)
done
end

subsection {* Refinable Values *}

class REF_VALUE_SORT = BOT_SORT + complete_lattice
begin

subsubsection {* Notations *}

text {* Infimum and Supremum *}

notation Inf ("\<Sqinter>v")
notation Sup ("\<Squnion>v")

text {* Meet and Join *}

text {* The precedence of the following two operators is still an open issue. *}

notation inf (infixr "\<sqinter>v" 200)
notation sup (infixr "\<squnion>v" 200)

text {* Refinement *}

notation less_eq (infixr "\<sqsubseteq>v" 50)
notation less (infixr "\<sqsubset>v" 50)

text {* Top *}

notation top ("\<top>v")
subsubsection {* Theorems *}

theorem Defined_not_eq_bot :
"Defined v \<Longrightarrow> \<not> v = \<bottom>v"
apply (auto)
done
end

subsection {* Integer Sort *}

class INT_SORT = VALUE_SORT +
  fixes MkInt :: "int \<Rightarrow> 'a"
  fixes DestInt :: "'a \<Rightarrow> int"
  fixes IsInt :: "'a \<Rightarrow> bool"
  assumes Defined [simp] : "Defined (MkInt i)"
  assumes Inverse [simp] : "DestInt (MkInt i) = i"
begin

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

class BOOL_SORT = VALUE_SORT +
  fixes MkBool :: "bool \<Rightarrow> 'a"
  fixes DestBool :: "'a \<Rightarrow> bool"
  fixes IsBool :: "'a \<Rightarrow> bool"
  assumes Defined [simp] : "Defined (MkBool b)"
  assumes Inverse [simp] : "DestBool (MkBool b) = b"
begin

subsubsection {* Simple Lemmas *}

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
end

subsection {* Character Sort *}

class CHAR_SORT = VALUE_SORT +
  fixes MkChar :: "char \<Rightarrow> 'a"
  fixes DestChar :: "'a \<Rightarrow> char"
  fixes IsChar :: "'a \<Rightarrow> bool"
  assumes Defined [simp] : "Defined (MkChar c)"
  assumes Inverse [simp] : "DestChar (MkChar c) = c"

subsection {* String Sort *}

class STRING_SORT = VALUE_SORT +
  fixes MkStr :: "string \<Rightarrow> 'a"
  fixes DestStr :: "'a \<Rightarrow> string"
  fixes IsStr :: "'a \<Rightarrow> bool"
  assumes Defined [simp] : "Defined (MkStr s)"
  assumes Inverse [simp] : "DestStr (MkStr s) = s"

subsection {* Real Sort *}

class REAL_SORT = VALUE_SORT +
  fixes MkReal :: "real \<Rightarrow> 'a"
  fixes DestReal :: "'a \<Rightarrow> real"
  fixes IsReal :: "'a \<Rightarrow> bool"
  assumes Defined [simp] : "Defined (MkReal r)"
  assumes Inverse [simp] : "DestReal (MkReal r) = r"

subsection {* Pair Sort *}

class PAIR_SORT = VALUE_SORT +
  fixes MkPair :: "('a \<times> 'a) \<Rightarrow> 'a"
  fixes DestPair :: "'a \<Rightarrow> ('a \<times> 'a)"
  fixes IsPair :: "'a \<Rightarrow> bool"
  assumes Inverse [simp] :
    "Defined (MkPair v1_v2) \<longrightarrow> DestPair (MkPair v1_v2) = v1_v2"

subsection {* Set Sort *}

class SET_SORT = VALUE_SORT +
  fixes MkSet :: "'a set \<Rightarrow> 'a"
  fixes DestSet :: "'a \<Rightarrow> 'a set"
  fixes IsSet :: "'a set \<Rightarrow> bool"
  assumes Defined [simp] :
    "IsSet vs \<Longrightarrow> Defined (MkSet vs)"
  assumes Inverse [simp]:
    "IsSet vs \<Longrightarrow> DestSet (MkSet vs) = vs"
begin

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

subsection {* List Sort *}

class LIST_SORT = VALUE_SORT +
  fixes MkList :: "'a list \<Rightarrow> 'a"
  fixes DestList :: "'a \<Rightarrow> 'a list"
  fixes IsList :: "'a list \<Rightarrow> bool"
  assumes Inverse [simp] :
    "IsList l \<Longrightarrow> DestList (MkList l) = l"
  assumes Defined [simp] :
    "IsList l \<Longrightarrow> Defined (MkList l)"

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

subsection {* Function Sort *}

class FUNCTION_SORT = BOT_SORT +
  fixes MkFunc   :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  and   DestFunc :: "'a \<Rightarrow> ('a \<Rightarrow> 'a)"
  and   IsFunc   :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  assumes Inverse [simp]: "IsFunc f \<Longrightarrow> DestFunc (MkFunc f) = f"
  and     Defined [simp]: "IsFunc f \<Longrightarrow> Defined (MkFunc f)"

begin

subsubsection {* Function Type *}

definition FuncBetw :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"FuncBetw a b f \<equiv> f \<in> MkFunc ` Collect IsFunc
                \<and> (fdom (DestFunc f) \<subseteq> a)
                \<and> (fran (DestFunc f) \<subseteq> b)"

subsubsection {* Function Operators *}

definition AppV :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"AppV f = DestFunc f"

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
