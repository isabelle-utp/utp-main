(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_list.thy                                                         *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* UTP Lists *}

theory utp_list
imports 
  "../core/utp_value"
  "../core/utp_sorts"
  "../core/utp_event"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
begin

typedef 'a::DEFINED ULIST = "{xs :: 'a list. \<forall>x\<in>set xs. \<D> x}"
  apply (rule_tac x="[]" in exI)
  apply (auto)
done

theorems Rep_ULIST' = Rep_ULIST [simplified]
declare Rep_ULIST' [simp]
declare Rep_ULIST_inverse [simp]
theorems Abs_ULIST_inverse' = Abs_ULIST_inverse [simplified]
declare Abs_ULIST_inverse' [simp]

lemma Rep_ULIST_intro [intro!]:
  "Rep_ULIST x = Rep_ULIST y \<Longrightarrow> x = y"
  by (simp add:Rep_ULIST_inject)

lemma Rep_ULIST_elim [elim]:
  "\<lbrakk> x = y; Rep_ULIST x = Rep_ULIST y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_ULIST

lift_definition NilUL :: "'a::DEFINED ULIST" is "Nil" by (simp)

lift_definition AppendUL :: 
  "'a::DEFINED ULIST \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST" (infixr "@\<^sub>u" 65) is "op @"
  by (auto)

lift_definition PrefixUL ::
  "'a::DEFINED ULIST \<Rightarrow> 'a ULIST \<Rightarrow> bool" is "prefix"
  by (auto)

lift_definition PrefixeqUL ::
  "'a::DEFINED ULIST \<Rightarrow> 'a ULIST \<Rightarrow> bool" is "prefixeq"
  by (auto)

lift_definition MinusUL :: 
  "'a::DEFINED ULIST \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST" is "\<lambda> xs ys. drop (length ys) xs"
  by (metis in_set_dropD)

definition ConsUL :: "'a::DEFINED \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST" (infixr "#\<^sub>u" 65) where
"ConsUL x xs = Abs_ULIST (x # Rep_ULIST xs)"

lemma ConsUL_rep_eq: 
  "\<D> x \<Longrightarrow> Rep_ULIST (x #\<^sub>u xs) = x # Rep_ULIST xs"
  by (simp_all add:ConsUL_def)

lemma ULIST_elems_defined [defined]:
  "x \<in> set (Rep_ULIST xs) \<Longrightarrow> \<D> x"
  apply (insert Rep_ULIST[of xs])
  apply (auto)
done

instantiation ULIST :: (DEFINED) DEFINED_NE
begin
definition "Defined_ULIST (xs :: 'a ULIST) = True"
instance
  by (intro_classes, auto simp add:Defined_ULIST_def)
end

lemma Defined_ULIST [defined]: "\<D> (xs :: ('a::DEFINED) ULIST)"
  by (simp add:Defined_ULIST_def)

text {* Set up the predicate and expression tactics to evaluate lists *}

lemma ULIST_transfer [eval, evale]: 
  "xs = ys \<longleftrightarrow> Rep_ULIST xs = Rep_ULIST ys"
  by (auto)

declare NilUL.rep_eq [eval, evale]
declare ConsUL_rep_eq [eval, evale]
declare AppendUL.rep_eq [eval, evale]
declare PrefixUL.rep_eq [eval, evale]
declare PrefixeqUL.rep_eq [eval, evale]

end