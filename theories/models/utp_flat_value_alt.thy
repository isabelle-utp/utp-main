(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_flat_value_alt.thy                                               *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Flat Value Lattice *}

theory utp_flat_value_alt
imports
  "../utp_common"
  "../utp_global"
  "../core/utp_sorts"
  "../core/utp_value"
begin

subsection {* Value Model *}

datatype 'a FLAT_VALUE =
  PropVal 'a | BotVal | TopVal

datatype 'a FLAT_TYPE =
  FlatType 'a

type_synonym ('VALUE, 'TYPE) FLAT_TYPE_REL =
  "('VALUE FLAT_VALUE) \<Rightarrow> ('TYPE FLAT_TYPE) \<Rightarrow> bool"

text {* Destructors *}

primrec PropValOf ::
  "'a FLAT_VALUE \<Rightarrow> 'a" where
"PropValOf (PropVal v) = v"

text {* Testing Functions *}

primrec IsPropVal ::
  "'a FLAT_VALUE \<Rightarrow> bool" where
"IsPropVal (PropVal _) = True" |
"IsPropVal BotVal = False" |
"IsPropVal TopVal = False"

primrec IsBotVal ::
  "'a FLAT_VALUE \<Rightarrow> bool" where
"IsBotVal (PropVal _) = False" |
"IsBotVal BotVal = True" |
"IsBotVal TopVal = False"

primrec IsTopVal ::
  "'a FLAT_VALUE \<Rightarrow> bool" where
"IsTopVal (PropVal _) = False" |
"IsTopVal BotVal = False" |
"IsTopVal TopVal = True"

text {* Inverse Theorems *}

theorem PropValOf_inverse [simp, intro] :
"IsPropVal v \<Longrightarrow> PropVal (PropValOf v) = v"
apply (case_tac v)
apply (simp_all)
done

subsection {* Typing Relation *}

fun flat_type_rel ::
  "('VALUE, 'TYPE) FLAT_TYPE_REL" where
"flat_type_rel (PropVal v) (FlatType t) = (global_type_rel v t)" |
"flat_type_rel BotVal (FlatType t) = True" |
"flat_type_rel TopVal (FlatType t) = True"

defs global_flat_type_rel [simp] :
"global_type_rel \<equiv> flat_type_rel"

subsection {* Sort Membership *}

instantiation FLAT_VALUE :: (VALUE_SORT) VALUE_SORT
begin
primrec Defined_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> bool" where
"Defined_FLAT_VALUE (PropVal v) = (Defined v)" |
"Defined_FLAT_VALUE BotVal = False" |
"Defined_FLAT_VALUE TopVal = True"
instance
apply (intro_classes)
done
end

instantiation FLAT_VALUE :: (BASIC_SORT) BASIC_SORT
begin
definition MkInt_FLAT_VALUE :: "int \<Rightarrow> 'a FLAT_VALUE" where
"MkInt_FLAT_VALUE i = PropVal (MkInt i)"
primrec DestInt_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> int" where
"DestInt_FLAT_VALUE (PropVal v) = (DestInt v)"
primrec IsInt_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> bool" where
"IsInt_FLAT_VALUE (PropVal v) = (IsInt v)"
definition MkBool_FLAT_VALUE :: "bool \<Rightarrow> 'a FLAT_VALUE" where
"MkBool_FLAT_VALUE b = PropVal (MkBool b)"
primrec DestBool_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> bool" where
"DestBool_FLAT_VALUE (PropVal v) = (DestBool v)"
primrec IsBool_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> bool" where
"IsBool_FLAT_VALUE (PropVal v) = (IsBool v)"
definition MkStr_FLAT_VALUE :: "string \<Rightarrow> 'a FLAT_VALUE" where
"MkStr_FLAT_VALUE s = PropVal (MkStr s)"
primrec DestStr_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> string" where
"DestStr_FLAT_VALUE (PropVal v) = (DestStr v)"
primrec IsStr_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> bool" where
"IsStr_FLAT_VALUE (PropVal v) = (IsStr v)"
definition MkReal_FLAT_VALUE :: "real \<Rightarrow> 'a FLAT_VALUE" where
"MkReal_FLAT_VALUE r = PropVal (MkReal r)"
primrec DestReal_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> real" where
"DestReal_FLAT_VALUE (PropVal v) = (DestReal v)"
primrec IsReal_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> bool" where
"IsReal_FLAT_VALUE (PropVal v) = (IsReal v)"
instance
apply (intro_classes)
apply (simp add: MkBool_FLAT_VALUE_def)
apply (simp add: MkBool_FLAT_VALUE_def DestBool_FLAT_VALUE_def)
apply (simp add: MkInt_FLAT_VALUE_def)
apply (simp add: MkInt_FLAT_VALUE_def DestInt_FLAT_VALUE_def)
apply (simp add: MkReal_FLAT_VALUE_def)
apply (simp add: MkReal_FLAT_VALUE_def DestReal_FLAT_VALUE_def)
apply (simp add: MkStr_FLAT_VALUE_def)
apply (simp add: MkStr_FLAT_VALUE_def DestStr_FLAT_VALUE_def)
done
end

instantiation FLAT_VALUE :: (COMPOSITE_SORT) COMPOSITE_SORT
begin
definition MkPair_FLAT_VALUE ::
  "'a FLAT_VALUE \<times> 'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE" where
"MkPair_FLAT_VALUE v1_v2 = (
   if IsPropVal (fst v1_v2) \<and> IsPropVal (snd v1_v2)
   then PropVal (MkPair (PropValOf (fst v1_v2), PropValOf (snd v1_v2)))
   else BotVal)"
definition DestPair_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE \<times> 'a FLAT_VALUE" where
"DestPair_FLAT_VALUE v = (
   PropVal (fst (DestPair (PropValOf v))),
   PropVal (snd (DestPair (PropValOf v))))"
definition IsPair_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> bool" where
"IsPair_FLAT_VALUE v = ((IsPropVal v) \<and> IsPair (PropValOf v))"
definition MkSet_FLAT_VALUE ::
  "'a FLAT_VALUE set \<Rightarrow> 'a FLAT_VALUE" where
"MkSet_FLAT_VALUE vs = (
   if (\<forall> v \<in> vs . IsPropVal v)
   then PropVal (MkSet (PropValOf ` vs))
   else BotVal)"
definition DestSet_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE set" where
"DestSet_FLAT_VALUE v = PropVal ` (DestSet (PropValOf v))"
definition IsSet_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> bool" where
"IsSet_FLAT_VALUE v = ((IsPropVal v) \<and> IsSet (PropValOf v))"
instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (simp add: MkPair_FLAT_VALUE_def DestPair_FLAT_VALUE_def)
-- {* Subgoal 2 *}
apply (simp add: MkSet_FLAT_VALUE_def DestSet_FLAT_VALUE_def)
apply (clarify)
apply (simp add: image_image)
apply (simp add: image_def)
done
end

instantiation FLAT_VALUE :: (VALUE_SORT) REF_VALUE_SORT
begin
definition top_FLAT_VALUE :: "'a FLAT_VALUE" where
"top_FLAT_VALUE = TopVal"
definition bot_FLAT_VALUE :: "'a FLAT_VALUE" where
"bot_FLAT_VALUE = BotVal"
fun less_eq_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE \<Rightarrow> bool" where
"less_eq_FLAT_VALUE BotVal _ = True" |
"less_eq_FLAT_VALUE _ TopVal = True" |
"less_eq_FLAT_VALUE TopVal v = (v = TopVal)" |
"less_eq_FLAT_VALUE v BotVal = (v = BotVal)" |
"less_eq_FLAT_VALUE (PropVal v1) (PropVal v2) = (v1 = v2)"
definition less_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE \<Rightarrow> bool" where
"less_FLAT_VALUE v1 v2 \<longleftrightarrow> (less_eq v1 v2) \<and> (v1 \<noteq> v2)"
definition Inf_FLAT_VALUE ::
  "'a FLAT_VALUE set \<Rightarrow> 'a FLAT_VALUE" where
"Inf_FLAT_VALUE vs =
 (if vs \<subseteq> {TopVal} then TopVal else
 (if (\<exists> v . (IsPropVal v) \<and> vs - {TopVal} = {v}) then
   (THE v . v \<in> vs \<and> IsPropVal v) else BotVal))"
definition Sup_FLAT_VALUE ::
  "'a FLAT_VALUE set \<Rightarrow> 'a FLAT_VALUE" where
"Sup_FLAT_VALUE vs =
 (if vs \<subseteq> {BotVal} then BotVal else
 (if (\<exists> v . (IsPropVal v) \<and> vs - {BotVal} = {v}) then
   (THE v . v \<in> vs \<and> IsPropVal v) else TopVal))"
definition inf_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE" where
"inf_FLAT_VALUE v1 v2 = Inf {v1, v2}"
definition sup_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE" where
"sup_FLAT_VALUE v1 v2 = Sup {v1, v2}"

text {* Utility Simplifications *}

lemma FLAT_VALUE_simp1 :
"(v = PropVal a \<and> IsPropVal v) = (v = PropVal a)"
apply (auto)
done

lemma FLAT_VALUE_simp2 :
"({PropVal a, BotVal} - {BotVal} = {v}) = (v = PropVal a)"
apply (auto)
done

lemma FLAT_VALUE_simp3 :
"({PropVal a, TopVal} - {TopVal} = {v}) = (v = PropVal a)"
apply (auto)
done

lemma FLAT_VALUE_simp4 :
"({BotVal, TopVal} - {TopVal} = {v}) = (v = BotVal)"
apply (auto)
done

lemma FLAT_VALUE_simp5 :
"({TopVal, BotVal} - {BotVal} = {v}) = (v = TopVal)"
apply (auto)
done

lemma FLAT_VALUE_simp6 :
"((v = PropVal a \<or> v = BotVal) \<and> IsPropVal v) = (v = PropVal a)"
apply (auto)
done

lemma FLAT_VALUE_simp7 :
"((v = PropVal a \<or> v = TopVal) \<and> IsPropVal v) = (v = PropVal a)"
apply (auto)
done

lemma FLAT_VALUE_simp8 :
"((v = BotVal \<or> v = PropVal a) \<and> IsPropVal v) = (v = PropVal a)"
apply (auto)
done

lemma FLAT_VALUE_simp9 :
"((v = TopVal \<or> v = PropVal a) \<and> IsPropVal v) = (v = PropVal a)"
apply (auto)
done

lemma FLAT_VALUE_simp10 :
"(IsPropVal v \<and> A - {BotVal} = {v}) =
 (IsPropVal v \<and> (A = {v} \<or> A = {v, BotVal}))"
apply (auto)
done

lemma FLAT_VALUE_simp11 :
"(IsPropVal v \<and> A - {TopVal} = {v}) =
 (IsPropVal v \<and> (A = {v} \<or> A = {v, TopVal}))"
apply (auto)
done

lemma FLAT_VALUE_simp12 :
"(\<exists> v . IsPropVal v \<and> A - {BotVal} = {v}) =
 (\<exists> x . A = {PropVal x} \<or> A = {PropVal x, BotVal})"
apply (simp add: FLAT_VALUE_simp10)
apply (safe)
apply (rule_tac x = "PropValOf v" in exI)
apply (simp)
apply (rule_tac x = "PropValOf v" in exI)
apply (simp)
apply (rule_tac x = "PropVal x" in exI)
apply (simp)
apply (rule_tac x = "PropVal x" in exI)
apply (simp)
done

lemma FLAT_VALUE_simp13 :
"(\<exists> v . IsPropVal v \<and> A - {TopVal} = {v}) =
 (\<exists> x . A = {PropVal x} \<or> A = {PropVal x, TopVal})"
apply (simp add: FLAT_VALUE_simp11)
apply (safe)
apply (rule_tac x = "PropValOf v" in exI)
apply (simp)
apply (rule_tac x = "PropValOf v" in exI)
apply (simp)
apply (rule_tac x = "PropVal x" in exI)
apply (simp)
apply (rule_tac x = "PropVal x" in exI)
apply (simp)
done

lemma FLAT_VALUE_simp14 :
"(\<forall> v . IsPropVal v \<longrightarrow> A - {BotVal} \<noteq> {v}) =
 (\<forall> x . A \<noteq> {PropVal x} \<and> A \<noteq> {PropVal x, BotVal})"
apply (subst all_not_ex) back
apply (simp only: sym [OF de_Morgan_disj])
apply (simp only: not_not)
apply (simp only: sym [OF FLAT_VALUE_simp12])
apply (simp)
done

lemma FLAT_VALUE_simp15 :
"(\<forall> v . IsPropVal v \<longrightarrow> A - {TopVal} \<noteq> {v}) =
 (\<forall> x . A \<noteq> {PropVal x} \<and> A \<noteq> {PropVal x, TopVal})"
apply (subst all_not_ex) back
apply (simp only: sym [OF de_Morgan_disj])
apply (simp only: not_not)
apply (simp only: sym [OF FLAT_VALUE_simp13])
apply (simp)
done

lemma FLAT_VALUE_simp16 :
"(\<forall> x . x \<in> A \<longrightarrow> x \<sqsubseteq>v PropVal a) = (A \<subseteq> {PropVal a, BotVal})"
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (drule_tac x = "x" in spec)
apply (case_tac x)
apply (simp_all) [3]
-- {* Subgoal 2 *}
apply (case_tac x)
apply (auto)
done

lemma FLAT_VALUE_simp17 :
"(\<forall> x . x \<in> A \<longrightarrow> PropVal a \<sqsubseteq>v x) = (A \<subseteq> {PropVal a, TopVal})"
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (drule_tac x = "x" in spec)
apply (case_tac x)
apply (simp_all) [3]
-- {* Subgoal 2 *}
apply (case_tac x)
apply (auto)
done

lemma FLAT_VALUE_simp18 :
"(\<forall> x . x \<in> A \<longrightarrow> x \<sqsubseteq>v BotVal) = (A \<subseteq> {BotVal})"
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (drule_tac x = "x" in spec)
apply (case_tac x)
apply (simp_all) [3]
-- {* Subgoal 2 *}
apply (case_tac x)
apply (auto)
done

lemma FLAT_VALUE_simp19 :
"(\<forall> x . x \<in> A \<longrightarrow> TopVal \<sqsubseteq>v x) = (A \<subseteq> {TopVal})"
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (drule_tac x = "x" in spec)
apply (case_tac x)
apply (simp_all) [3]
-- {* Subgoal 2 *}
apply (case_tac x)
apply (auto)
done

lemma FLAT_VALUE_simp20 :
"(A \<subseteq> {BotVal}) = (A = {} \<or> A = {BotVal})"
apply (auto)
done

lemma FLAT_VALUE_simp21 :
"(A \<subseteq> {TopVal}) = (A = {} \<or> A = {TopVal})"
apply (auto)
done

lemma FLAT_VALUE_simp22 :
"(A \<subseteq> {PropVal a, BotVal}) =
 (A = {} \<or> A = {PropVal a} \<or> A = {BotVal} \<or> A = {PropVal a, BotVal})"
apply (auto)
done

lemma FLAT_VALUE_simp23 :
"(A \<subseteq> {PropVal a, TopVal}) =
 (A = {} \<or> A = {PropVal a} \<or> A = {TopVal} \<or> A = {PropVal a, TopVal})"
apply (auto)
done

theorems FLAT_VALUE_simps =
  FLAT_VALUE_simp1
  FLAT_VALUE_simp2
  FLAT_VALUE_simp3
  FLAT_VALUE_simp4
  FLAT_VALUE_simp5
  FLAT_VALUE_simp6
  FLAT_VALUE_simp7
  FLAT_VALUE_simp8
  FLAT_VALUE_simp9
(* FLAT_VALUE_simp10 *)
(* FLAT_VALUE_simp11 *)
(* FLAT_VALUE_simp12 *)
(* FLAT_VALUE_simp13 *)
  FLAT_VALUE_simp14
  FLAT_VALUE_simp15
  FLAT_VALUE_simp16
  FLAT_VALUE_simp17
  FLAT_VALUE_simp18
  FLAT_VALUE_simp19
  FLAT_VALUE_simp20
  FLAT_VALUE_simp21
  FLAT_VALUE_simp22
  FLAT_VALUE_simp23

declare FLAT_VALUE_simps [simp]

text {* Instantiation Lemmas *}

lemma less_le_not_le_FLAT_VALUE :
"((x :: 'a FLAT_VALUE) \<sqsubset>v y) = (x \<sqsubseteq>v y \<and> \<not> y \<sqsubseteq>v x)"
apply (simp add: less_FLAT_VALUE_def)
apply (induct_tac x, induct_tac[!] y)
apply (simp_all)
done

lemma order_refl_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<sqsubseteq>v x"
apply (induct_tac x)
apply (simp_all)
done

lemma order_trans_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<sqsubseteq>v y \<Longrightarrow> y \<sqsubseteq>v z \<Longrightarrow> x \<sqsubseteq>v z"
apply (atomize (full))
apply (induct_tac x, induct_tac[!] y, induct_tac[!] z)
apply (simp_all)
done

lemma antisym_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<sqsubseteq>v y \<Longrightarrow> y \<sqsubseteq>v x \<Longrightarrow> x = y"
apply (atomize (full))
apply (induct_tac x, induct_tac[!] y)
apply (simp_all)
done

lemma inf_le1_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<sqinter>v y \<sqsubseteq>v x"
apply (simp add: inf_FLAT_VALUE_def Inf_FLAT_VALUE_def)
apply (induct_tac x, induct_tac[!] y)
apply (simp_all)
done

lemma inf_le2_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<sqinter>v y \<sqsubseteq>v y"
apply (simp add: inf_FLAT_VALUE_def Inf_FLAT_VALUE_def)
apply (induct_tac x, induct_tac[!] y)
apply (simp_all)
done

lemma inf_greatest_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<sqsubseteq>v y \<Longrightarrow> x \<sqsubseteq>v z \<Longrightarrow> x \<sqsubseteq>v y \<sqinter>v z"
apply (atomize (full))
apply (simp add: inf_FLAT_VALUE_def Inf_FLAT_VALUE_def)
apply (induct_tac x, induct_tac[!] y, induct_tac[!] z)
apply (simp_all)
apply (auto)
done

lemma sup_ge1_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<sqsubseteq>v x \<squnion>v y"
apply (simp add: sup_FLAT_VALUE_def Sup_FLAT_VALUE_def)
apply (induct_tac x, induct_tac[!] y)
apply (simp_all)
done

lemma sup_ge2_FLAT_VALUE :
"(y :: 'a FLAT_VALUE) \<sqsubseteq>v x \<squnion>v y"
apply (simp add: sup_FLAT_VALUE_def Sup_FLAT_VALUE_def)
apply (induct_tac x, induct_tac[!] y)
apply (simp_all)
done

lemma sup_least_FLAT_VALUE :
"(y :: 'a FLAT_VALUE) \<sqsubseteq>v x \<Longrightarrow> z \<sqsubseteq>v x \<Longrightarrow> y \<squnion>v z \<sqsubseteq>v x"
apply (atomize (full))
apply (simp add: sup_FLAT_VALUE_def Sup_FLAT_VALUE_def)
apply (induct_tac x, induct_tac[!] y, induct_tac[!] z)
apply (simp_all)
apply (force, force)
done

lemma bot_least_FLAT_VALUE :
"\<bottom>v \<sqsubseteq>v (a :: 'a FLAT_VALUE)"
apply (simp add: bot_FLAT_VALUE_def)
done

lemma top_greatest_FLAT_VALUE :
"(a :: 'a FLAT_VALUE) \<sqsubseteq>v \<top>v"
apply (simp add: top_FLAT_VALUE_def)
apply (induct_tac a)
apply (simp_all)
done

lemma Inf_lower_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<in> A \<Longrightarrow> \<Sqinter>v A \<sqsubseteq>v x"
apply (atomize (full))
apply (simp add: Inf_FLAT_VALUE_def)
apply (simp only: FLAT_VALUE_simp13)
apply (induct_tac x)
apply (auto)
done

lemma Inf_greatest_FLAT_VALUE :
"(\<And> (x :: 'a FLAT_VALUE) . x \<in> A \<Longrightarrow> z \<sqsubseteq>v x) \<Longrightarrow> z \<sqsubseteq>v \<Sqinter>v A"
apply (atomize (full))
apply (simp add: Inf_FLAT_VALUE_def)
apply (simp only: FLAT_VALUE_simp13)
apply (induct_tac z)
apply (simp_all)
done

lemma Sup_upper_FLAT_VALUE :
"(x :: 'a FLAT_VALUE) \<in> A \<Longrightarrow> x \<sqsubseteq>v \<Squnion>v A"
apply (atomize (full))
apply (simp add: Sup_FLAT_VALUE_def)
apply (simp only: FLAT_VALUE_simp12)
apply (induct_tac x)
apply (auto)
done

lemma Sup_least_FLAT_VALUE :
"(\<And> (x :: 'a FLAT_VALUE) . x \<in> A \<Longrightarrow> x \<sqsubseteq>v z) \<Longrightarrow> \<Squnion>v A \<sqsubseteq>v z"
apply (atomize (full))
apply (simp add: Sup_FLAT_VALUE_def)
apply (simp only: FLAT_VALUE_simp12)
apply (induct_tac z)
apply (simp_all)
apply (fold top_FLAT_VALUE_def)
apply (simp add: top_greatest_FLAT_VALUE)
done

instance
apply (intro_classes)
apply (rule less_le_not_le_FLAT_VALUE)
apply (rule order_refl_FLAT_VALUE)
apply (erule order_trans_FLAT_VALUE)
apply (assumption)
apply (erule antisym_FLAT_VALUE)
apply (assumption)
apply (rule inf_le1_FLAT_VALUE)
apply (rule inf_le2_FLAT_VALUE)
apply (erule inf_greatest_FLAT_VALUE)
apply (assumption)
apply (rule sup_ge1_FLAT_VALUE)
apply (rule sup_ge2_FLAT_VALUE)
apply (erule sup_least_FLAT_VALUE)
apply (assumption)
apply (rule bot_least_FLAT_VALUE)
apply (rule top_greatest_FLAT_VALUE)
apply (erule Inf_lower_FLAT_VALUE)
apply (erule Inf_greatest_FLAT_VALUE)
apply (erule Sup_upper_FLAT_VALUE)
apply (erule Sup_least_FLAT_VALUE)
apply (simp add: bot_FLAT_VALUE_def)
done
end

text {* Default Simplifications *}

declare FLAT_VALUE_simps [simp del]
declare Defined_FLAT_VALUE_def [simp]
declare MkInt_FLAT_VALUE_def [simp]
declare DestInt_FLAT_VALUE_def [simp]
declare IsInt_FLAT_VALUE_def [simp]
declare MkBool_FLAT_VALUE_def [simp]
declare DestBool_FLAT_VALUE_def [simp]
declare IsBool_FLAT_VALUE_def [simp]
declare MkStr_FLAT_VALUE_def [simp]
declare DestStr_FLAT_VALUE_def [simp]
declare IsStr_FLAT_VALUE_def [simp]
declare MkReal_FLAT_VALUE_def [simp]
declare DestReal_FLAT_VALUE_def [simp]
declare IsReal_FLAT_VALUE_def [simp]
declare MkPair_FLAT_VALUE_def [simp]
declare DestPair_FLAT_VALUE_def [simp]
declare IsPair_FLAT_VALUE_def [simp]
declare MkSet_FLAT_VALUE_def [simp]
declare DestSet_FLAT_VALUE_def [simp]
declare IsSet_FLAT_VALUE_def [simp]

(*
declare top_FLAT_VALUE_def [simp]
declare bot_FLAT_VALUE_def [simp]
declare less_eq_FLAT_VALUE_def [simp]
declare less_FLAT_VALUE_def [simp]
declare inf_FLAT_VALUE_def [simp]
declare sup_FLAT_VALUE_def [simp]
declare Inf_FLAT_VALUE_def [simp]
declare Sup_FLAT_VALUE_def [simp]
*)

subsection {* Locale @{text "FLAT_VALUE"} *}

locale FLAT_VALUE =
  fixes basic_type_rel :: "'VALUE :: COMPOSITE_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool"
begin

text {* Constructors *}

definition MkBot ::
  "'VALUE FLAT_VALUE" where
"MkBot = bot_class.bot"

definition MkTop ::
  "'VALUE FLAT_VALUE" where
"MkTop = top_class.top"

definition MkInt ::
  "int \<Rightarrow> 'VALUE FLAT_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool ::
  "bool \<Rightarrow> 'VALUE FLAT_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr ::
  "string \<Rightarrow> 'VALUE FLAT_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkReal ::
  "real \<Rightarrow> 'VALUE FLAT_VALUE" where
"MkReal = REAL_SORT_class.MkReal"

definition MkPair ::
  "'VALUE FLAT_VALUE \<times>
   'VALUE FLAT_VALUE \<Rightarrow>
   'VALUE FLAT_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet ::
  "'VALUE FLAT_VALUE set \<Rightarrow>
   'VALUE FLAT_VALUE" where
"MkSet = SET_SORT_class.MkSet"

text {* Destructors *}

definition DestInt ::
  "'VALUE FLAT_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr ::
  "'VALUE FLAT_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestReal ::
  "'VALUE FLAT_VALUE \<Rightarrow> real" where
"DestReal = REAL_SORT_class.DestReal"

definition DestPair ::
  "'VALUE FLAT_VALUE \<Rightarrow>
   'VALUE FLAT_VALUE \<times>
   'VALUE FLAT_VALUE" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet ::
  "'VALUE FLAT_VALUE \<Rightarrow>
   'VALUE FLAT_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

text {* Testing Functions *}

definition IsBot ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsBot v = (v = bot_class.bot)"

definition IsTop ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsTop v = (v = top_class.top)"

definition IsInt ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsInt = INT_SORT_class.IsInt"

definition IsBool ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsBool = BOOL_SORT_class.IsBool"

definition IsStr ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsStr = STRING_SORT_class.IsStr"

definition IsReal ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsReal = REAL_SORT_class.IsReal"

definition IsPair ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsPair = PAIR_SORT_class.IsPair"

definition IsSet ::
  "'VALUE FLAT_VALUE \<Rightarrow> bool" where
"IsSet = SET_SORT_class.IsSet"

text {* Default Simplifications *}

declare MkBot_def [simp]
declare MkTop_def [simp]
declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkReal_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestReal_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]

declare IsBot_def [simp]
declare IsTop_def [simp]
declare IsInt_def [simp]
declare IsBool_def [simp]
declare IsStr_def [simp]
declare IsReal_def [simp]
declare IsPair_def [simp]
declare IsSet_def [simp]
end

subsection {* Theorems *}

theorem VALUE_flat_type_rel [simp] :
"VALUE flat_type_rel"
apply (unfold_locales)
apply (induct_tac t)
apply (rule_tac x = "BotVal" in exI)
apply (simp)
done
end
