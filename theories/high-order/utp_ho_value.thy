(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_ho_value.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* HO Values *}

theory utp_ho_value
imports
  "../utp_global"
  "../core/utp_sorts"
  "../core/utp_var"
  "../models/utp_default_value"
  "../models/utp_complex_value"
  "../models/utp_flat_value"
begin

subsection {* Type Definitions *}

type_synonym NORM_VALUE = "DEFAULT_VALUE COMPLEX_VALUE FLAT_VALUE"
type_synonym NORM_TYPE = "DEFAULT_TYPE COMPLEX_TYPE"

text {* Program Type *}

text {* We do not give a model for program values at this stage. *}

typedecl PROG_VALUE

text {* Value Type *}

datatype HO_VALUE =
  NormVal "NORM_VALUE" |
  ProgVal "PROG_VALUE"

datatype HO_TYPE =
  NormType "NORM_TYPE" |
  ProgType "(HO_TYPE VAR) list"

text {* Type Synonyms *}

type_synonym PROG_TYPE = "(HO_TYPE VAR) list"

text {* Destructors *}

primrec NormValOf :: "HO_VALUE \<Rightarrow> NORM_VALUE" where
"NormValOf (NormVal v) = v"

primrec ProgValOf :: "HO_VALUE \<Rightarrow> PROG_VALUE" where
"ProgValOf (ProgVal p) = p"

primrec NormTypeOf :: "HO_TYPE \<Rightarrow> NORM_TYPE" where
"NormTypeOf (NormType t) = t"

primrec ProgTypeOf :: "HO_TYPE \<Rightarrow> PROG_TYPE" where
"ProgTypeOf (ProgType t) = t"

text {* Tests *}

primrec IsNormVal :: "HO_VALUE \<Rightarrow> bool" where
"IsNormVal (NormVal _) = True" |
"IsNormVal (ProgVal _) = False"

primrec IsProgVal :: "HO_VALUE \<Rightarrow> bool" where
"IsProgVal (NormVal _) = False" |
"IsProgVal (ProgVal _) = True"

primrec IsNormType :: "HO_TYPE \<Rightarrow> bool" where
"IsNormType (NormType _) = True" |
"IsNormType (ProgType _) = False"

primrec IsProgType :: "HO_TYPE \<Rightarrow> bool" where
"IsProgType (NormType _) = False" |
"IsProgType (ProgType _) = True"

text {* Variables *}

definition IsNormVar :: "HO_TYPE VAR \<Rightarrow> bool" where
"IsNormVar x = IsNormType (type x)"

definition IsProgVar :: "HO_TYPE VAR \<Rightarrow> bool" where
"IsProgVar x = IsProgType (type x)"

text {* Inverse Theorems *}

theorem NormValOf_inverse [simp, intro] :
"IsNormVal v \<Longrightarrow> NormVal (NormValOf v) = v"
apply (case_tac v)
apply (simp_all)
done

subsection {* Ranking Functions *}

primrec max_list :: "nat list \<Rightarrow> nat" where
"max_list [] = 0" |
"max_list (h # t) = max h (max_list t)"

fun RankType :: "HO_TYPE \<Rightarrow> nat" where
"RankType (NormType _) = 0" |
"RankType (ProgType l) = max_list (map (RankType o type) l) + 1"

definition RankVar :: "HO_TYPE VAR \<Rightarrow> nat" where
"RankVar v = RankType (type v)"

definition RankAlpha :: "HO_TYPE ALPHABET \<Rightarrow> nat" where
"a \<in> WF_ALPHABET \<Longrightarrow>
 RankAlpha a = max_list (map RankVar (SOME l . set l = a))"

subsection {* Typing and Refinement *}

text {* We introduce deferred functions for program alphabets and refinement. *}

consts ProgAlpha :: "PROG_VALUE \<Rightarrow> (HO_TYPE VAR) set" ("\<alpha>v")
consts ProgRefine :: "PROG_VALUE \<Rightarrow> PROG_VALUE \<Rightarrow> bool" (infix "\<sqsubseteq>pv" 50)

definition prog_type_rel :: "PROG_VALUE \<Rightarrow> PROG_TYPE \<Rightarrow> bool" where
"prog_type_rel p t \<longleftrightarrow> (\<alpha>v p) = set t"

declare prog_type_rel_def [simp]

text {*
  Refinement of higher-order values as defined below doesn't quite give us a
  lattice. However, such a lattice would in any case have to be be defined on
  all program values and I am not sure this is even desirable. To work around
  the this issue, we have to alter the construction of higher-order values to
  introduce bottom and top here rather than in utp\_flat\_value. At present,
  it is too early to assess the complications of different possible designs.
  It might be that we should only introduce the (refinement) operators in
  REF\_VALUE but not the particular properties of refinement forming a lattice.
*}

fun ho_type_rel :: "HO_VALUE \<Rightarrow> HO_TYPE \<Rightarrow> bool" where
"ho_type_rel (NormVal v) (NormType t) = (v : t)" |
"ho_type_rel (NormVal v) (ProgType t) = False" |
"ho_type_rel (ProgVal p) (NormType t) = False" |
"ho_type_rel (ProgVal p) (ProgType t) = (p : t)"

defs global_prog_type_rel [simp] :
"global_type_rel p t \<equiv> (\<alpha>v p) = set t"

defs global_ho_type_rel [simp] :
"global_type_rel \<equiv> ho_type_rel"

fun ho_value_ref :: "HO_VALUE \<Rightarrow> HO_VALUE \<Rightarrow> bool" where
(* "ho_value_ref (NormVal v1) (NormVal v2) = (v1 = v2)" | *)
"ho_value_ref (NormVal v1) (NormVal v2) = (v1 \<sqsubseteq>v v2)" |
"ho_value_ref (NormVal v1) (ProgVal v2) = False" |
"ho_value_ref (ProgVal v1) (NormVal v2) = False" |
"ho_value_ref (ProgVal v1) (ProgVal v2) = (v1 \<sqsubseteq>pv v2)"

subsection {* Sort Membership *}

instantiation HO_VALUE :: COMPOSITE_SORT
begin
primrec Defined_HO_VALUE :: "HO_VALUE \<Rightarrow> bool" where
"Defined_HO_VALUE (NormVal v) = (Defined v)" |
-- {* We cannot establish a definedness notion of program values yet. *}
"Defined_HO_VALUE (ProgVal v) = True"
definition MkInt_HO_VALUE [simp] :
"MkInt_HO_VALUE i = NormVal (MkInt i)"
definition DestInt_HO_VALUE [simp] :
"DestInt_HO_VALUE v = DestInt (NormValOf v)"
definition IsInt_HO_VALUE [simp] :
"IsInt_HO_VALUE v = ((IsNormVal v) \<and> IsInt (NormValOf v))"
definition MkBool_HO_VALUE [simp] :
"MkBool_HO_VALUE i = NormVal (MkBool i)"
definition DestBool_HO_VALUE [simp] :
"DestBool_HO_VALUE v = DestBool (NormValOf v)"
definition IsBool_HO_VALUE [simp] :
"IsBool_HO_VALUE v = ((IsNormVal v) \<and> IsBool (NormValOf v))"
definition MkStr_HO_VALUE [simp] :
"MkStr_HO_VALUE i = NormVal (MkStr i)"
definition DestStr_HO_VALUE [simp] :
"DestStr_HO_VALUE v = DestStr (NormValOf v)"
definition IsStr_HO_VALUE [simp] :
"IsStr_HO_VALUE v = ((IsNormVal v) \<and> IsStr (NormValOf v))"
definition MkReal_HO_VALUE [simp] :
"MkReal_HO_VALUE r = NormVal (MkReal r)"
definition DestReal_HO_VALUE [simp] :
"DestReal_HO_VALUE v = DestReal (NormValOf v)"
definition IsReal_HO_VALUE [simp] :
"IsReal_HO_VALUE v = ((IsNormVal v) \<and> IsReal (NormValOf v))"
definition MkPair_HO_VALUE [simp] :
"MkPair_HO_VALUE v1_v2 = (
   if IsNormVal (fst v1_v2) \<and> IsNormVal (snd v1_v2)
   then NormVal (MkPair (NormValOf (fst v1_v2), NormValOf (snd v1_v2)))
   else NormVal (PropVal VoidVal))"
definition DestPair_HO_VALUE [simp] :
"DestPair_HO_VALUE v = (
   NormVal (fst (DestPair (NormValOf v))),
   NormVal (snd (DestPair (NormValOf v))))"
definition IsPair_HO_VALUE [simp] :
"IsPair_HO_VALUE v = ((IsNormVal v) \<and> IsPair (NormValOf v))"
definition MkSet_HO_VALUE [simp] :
"MkSet_HO_VALUE vs = (
   if (\<forall> v \<in> vs . IsNormVal v)
   then NormVal (MkSet (NormValOf ` vs))
   else NormVal (PropVal VoidVal))"
definition DestSet_HO_VALUE [simp] :
"DestSet_HO_VALUE v = NormVal ` (DestSet (NormValOf v))"
definition IsSet_HO_VALUE [simp] :
"IsSet_HO_VALUE v = ((IsNormVal v) \<and> IsSet (NormValOf v))"
instance
apply (intro_classes)
apply (simp_all) [8]
-- {* Subgoal 1 *}
apply (simp add: uncurry_def)
-- {* Subgoal 2 *}
apply (clarsimp)
apply (simp add: image_image)
apply (simp add: image_def)
done
end

subsection {* Locale @{text "HO_VALUE"} *}

locale HO_VALUE (* = VALUE "ho_type_rel" *)
begin

text {* Constructors *}

definition MkBot :: "HO_VALUE" where
"MkBot = NormVal bot_class.bot"

definition MkTop :: "HO_VALUE" where
"MkTop = NormVal top_class.top"

definition MkInt :: "int \<Rightarrow> HO_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool :: "bool \<Rightarrow> HO_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr :: "string \<Rightarrow> HO_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkReal :: "real \<Rightarrow> HO_VALUE" where
"MkReal = REAL_SORT_class.MkReal"

definition MkPair :: "HO_VALUE \<times> HO_VALUE \<Rightarrow> HO_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet :: "HO_VALUE set \<Rightarrow> HO_VALUE" where
"MkSet = SET_SORT_class.MkSet"

definition MkProg :: "PROG_VALUE \<Rightarrow> HO_VALUE" where
"MkProg = ProgVal"

text {* Destructors *}

definition DestInt :: "HO_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool :: "HO_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr :: "HO_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestReal :: "HO_VALUE \<Rightarrow> real" where
"DestReal = REAL_SORT_class.DestReal"

definition DestPair :: "HO_VALUE \<Rightarrow> HO_VALUE \<times> HO_VALUE" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet :: "HO_VALUE \<Rightarrow> HO_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

definition DestProg :: "HO_VALUE \<Rightarrow> PROG_VALUE" where
"DestProg = ProgValOf"

text {* Tests *}

definition IsBot :: "HO_VALUE \<Rightarrow> bool" where
"IsBot v = ((IsNormVal v) \<and> (NormValOf v) = bot_class.bot)"

definition IsTop :: "HO_VALUE \<Rightarrow> bool" where
"IsTop v = ((IsNormVal v) \<and> (NormValOf v) = top_class.top)"

definition IsInt :: "HO_VALUE \<Rightarrow> bool" where
"IsInt = INT_SORT_class.IsInt"

definition IsBool :: "HO_VALUE \<Rightarrow> bool" where
"IsBool = BOOL_SORT_class.IsBool"

definition IsStr :: "HO_VALUE \<Rightarrow> bool" where
"IsStr = STRING_SORT_class.IsStr"
definition IsReal :: "HO_VALUE \<Rightarrow> bool" where
"IsReal = REAL_SORT_class.IsReal"

definition IsPair :: "HO_VALUE \<Rightarrow> bool" where
"IsPair = PAIR_SORT_class.IsPair"

definition IsSet :: "HO_VALUE \<Rightarrow> bool" where
"IsSet = SET_SORT_class.IsSet"

definition IsProg :: "HO_VALUE \<Rightarrow> bool" where
"IsProg = IsProgVal"

text {* Default Simplifications *}

declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkReal_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]
declare MkProg_def [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestReal_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]
declare DestProg_def [simp]

declare IsBot_def [simp]
declare IsTop_def [simp]
declare IsInt_def [simp]
declare IsBool_def [simp]
declare IsStr_def [simp]
declare IsReal_def [simp]
declare IsPair_def [simp]
declare IsSet_def [simp]
declare IsProg_def [simp]
end

subsection {* Theorems *}

theorem VALUE_ho_type_rel [simp] :
"VALUE prog_type_rel \<Longrightarrow> VALUE ho_type_rel"
apply (simp add: VALUE_def)
apply (clarify)
apply (case_tac t)
apply (simp_all)
-- {* Subgoal 1 *}
apply (subgoal_tac
  "VALUE (flat_type_rel :: NORM_VALUE \<Rightarrow> NORM_TYPE \<Rightarrow> bool)")
apply (simp add: VALUE_def)
apply (drule_tac x = "COMPLEX_TYPE" in spec)
apply (clarify)
apply (rule_tac x = "NormVal x" in exI)
apply (simp)
apply (simp)
-- {* Subgoal 2 *}
apply (drule_tac x = "list" in spec)
apply (clarify)
apply (rule_tac x = "ProgVal x" in exI)
apply (simp)
done

subsubsection {* Rank Theorems *}

text {* Generic Rank Induction Theorems *}

lemma generic_rank_intro :
"(\<forall> x . P x) = (\<forall> n :: nat . \<forall> x . r x = n \<longrightarrow> P x)"
apply (auto)
done

theorem generic_rank_induct_thm :
"\<lbrakk>(\<forall> x . r x = 0 \<longrightarrow> P x);
 (\<forall> n :: nat .
   (\<forall> x . r x = n \<longrightarrow> P x) \<longrightarrow>
   (\<forall> x . r x = n + 1 \<longrightarrow> P x))\<rbrakk> \<Longrightarrow>
 (\<forall> x . P x)"
apply (subst generic_rank_intro [where r = "r"])
apply (rule allI)
apply (atomize (full))
apply (rule allI)
apply (induct_tac n)
apply (safe)
apply (drule_tac x = "na" in spec)
apply (simp (no_asm_simp))
done

theorem generic_rank_induct_rule :
"\<lbrakk>\<And> x . r x = 0 \<Longrightarrow> P x;
 \<And> x n :: nat . \<lbrakk>\<forall> x . r x = n \<longrightarrow> P x; r x = n + 1\<rbrakk> \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P x"
apply (atomize (full))
apply (clarify)
apply (subgoal_tac "(\<forall> x . P x)")
apply (auto) [1]
apply (rule generic_rank_induct_thm [where r = "r"])
apply (safe)
apply (drule_tac x = "x" in spec) back
apply (drule_tac x = "n" in spec)
apply (safe)
done

text {* Concrete Rank Induction Theorems *}

theorems RankType_induct_thm = generic_rank_induct_thm [where r = "RankType"]
theorems RankType_induct_rule = generic_rank_induct_rule [where r = "RankType"]
theorems RankVar_induct_thm = generic_rank_induct_thm [where r = "RankVar"]
theorems RankVar_induct_rule = generic_rank_induct_rule [where r = "RankVar"]
theorems RankAlpha_induct_thm = generic_rank_induct_thm [where r = "RankAlpha"]
theorems RankAlpha_induct_rule = generic_rank_induct_rule [where r = "RankAlpha"]
end
