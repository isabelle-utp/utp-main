(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_flat_value.thy                                                   *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Flat Values *}

theory utp_flat_value
imports
  "../utp_common"
  "../utp_global"
  "../core/utp_sorts"
  "../core/utp_value"
begin

subsection {* Value Model *}

datatype 'a FLAT_VALUE =
  PropVal 'a | BotVal | TopVal

text {* Testing Functions *}

primrec IsPropVal :: "'a FLAT_VALUE \<Rightarrow> bool" where
"IsPropVal (PropVal _) = True" |
"IsPropVal BotVal = False" |
"IsPropVal TopVal = False"

subsection {* Typing Relation *}

primrec flat_type_rel :: "('a FLAT_VALUE) \<Rightarrow> 'b \<Rightarrow> bool" where
"flat_type_rel (PropVal v) t = (global_type_rel v t)" |
"flat_type_rel BotVal t = True" |
"flat_type_rel TopVal t = True"

defs flat_type_rel [simp] :
"global_type_rel \<equiv> flat_type_rel"

subsection {* Sort Membership *}

instantiation FLAT_VALUE :: (BASIC_VALUE) BASIC_VALUE
begin
primrec WellFormed_FLAT_VALUE :: "'a FLAT_VALUE \<Rightarrow> bool" where
"WellFormed_FLAT_VALUE (PropVal v) = (WellFormed v)" |
"WellFormed_FLAT_VALUE BotVal = True" |
"WellFormed_FLAT_VALUE TopVal = True"
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
instance
apply (intro_classes)
apply(simp add: WellFormed_FLAT_VALUE_def MkBool_FLAT_VALUE_def)
apply(simp add: MkBool_FLAT_VALUE_def DestBool_FLAT_VALUE_def)
apply(simp add: WellFormed_FLAT_VALUE_def MkInt_FLAT_VALUE_def)
apply(simp add: MkInt_FLAT_VALUE_def DestInt_FLAT_VALUE_def)
apply(simp add: WellFormed_FLAT_VALUE_def MkStr_FLAT_VALUE_def)
apply(simp add: MkStr_FLAT_VALUE_def DestStr_FLAT_VALUE_def)
done
end

(*
instantiation FLAT_VALUE :: (COMPOSITE_VALUE) COMPOSITE_VALUE
begin
end
*)

instantiation FLAT_VALUE :: (UTP_VALUE) REF_VALUE
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
 (if vs = {} then TopVal else
 (if (\<exists> v . (IsPropVal v) \<and> vs - {TopVal} = {v}) then
   (THE v . v \<in> vs \<and> v \<noteq> TopVal) else BotVal))"
definition Sup_FLAT_VALUE ::
  "'a FLAT_VALUE set \<Rightarrow> 'a FLAT_VALUE" where
"Sup_FLAT_VALUE vs =
 (if vs = {} then BotVal else
 (if (\<exists> v . (IsPropVal v) \<and> vs - {BotVal} = {v}) then
   (THE v . v \<in> vs \<and> v \<noteq> BotVal) else TopVal))"
definition inf_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE" where
"inf_FLAT_VALUE v1 v2 = Inf {v1, v2}"
definition sup_FLAT_VALUE ::
  "'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE \<Rightarrow> 'a FLAT_VALUE" where
"sup_FLAT_VALUE v1 v2 = Sup {v1, v2}"
instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (simp add: less_FLAT_VALUE_def)
apply (induct_tac x)
apply (induct_tac y, simp, simp, simp)
apply (induct_tac y, simp, simp, simp)
apply (induct_tac y, simp, simp, simp)
-- {* Subgoal 2 *}
apply (induct_tac x, simp, simp, simp)
-- {* Subgoal 3 *}
-- {* TODO: Finish this proof! *}
sorry
end

text {* Default Simplifications *}

declare WellFormed_FLAT_VALUE_def [simp]
declare MkInt_FLAT_VALUE_def [simp]
declare DestInt_FLAT_VALUE_def [simp]
declare IsInt_FLAT_VALUE_def [simp]
declare MkBool_FLAT_VALUE_def [simp]
declare DestBool_FLAT_VALUE_def [simp]
declare IsBool_FLAT_VALUE_def [simp]
declare MkStr_FLAT_VALUE_def [simp]
declare DestStr_FLAT_VALUE_def [simp]
declare IsStr_FLAT_VALUE_def [simp]

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

subsection {* Theorems *}

theorem VALUE_flat_type_rel [simp] :
"VALUE flat_type_rel"
apply (unfold_locales)
apply (rule_tac x = "BotVal" in exI)
apply (simp)
done
end