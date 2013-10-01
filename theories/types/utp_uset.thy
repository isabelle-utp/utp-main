(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_uset.thy                                                         *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* UTP Sets *}

theory utp_uset
imports 
  "../core/utp_value"
  "../core/utp_sorts"
  "../core/utp_event"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  utp_list
begin

typedef 'a::DEFINED USET = "{xs :: 'a set. \<forall>x\<in>xs. \<D> x}"
  apply (rule_tac x="{}" in exI)
  apply (auto)
done

theorems Rep_USET' = Rep_USET [simplified]
declare Rep_USET' [simp]
declare Rep_USET_inverse [simp]
theorems Abs_USET_inverse' = Abs_USET_inverse [simplified]
declare Abs_USET_inverse' [simp]

lemma Rep_USET_intro [intro!]:
  "Rep_USET x = Rep_USET y \<Longrightarrow> x = y"
  by (simp add:Rep_USET_inject)

lemma Rep_USET_elim [elim]:
  "\<lbrakk> x = y; Rep_USET x = Rep_USET y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_USET

instantiation USET :: (DEFINED) DEFINED_NE
begin
definition "Defined_USET (xs :: 'a USET) = True"
instance 
  by (intro_classes, auto simp add:Defined_USET_def)
end

lemma Defined_USET [defined]: 
  "\<D> (xs :: ('a::DEFINED USET))"
  by (simp add:Defined_USET_def)

lift_definition EmptyUS :: "'a::DEFINED USET" is "{}"
  by simp

definition InsertUS :: "'a::DEFINED \<Rightarrow> 'a USET \<Rightarrow> 'a USET" where
"InsertUS x xs = Abs_USET (insert x (Rep_USET xs))"

lemma InsertUS_rep_eq: 
  "\<D> x \<Longrightarrow> Rep_USET (InsertUS x xs) = insert x (Rep_USET xs)"
  apply (subgoal_tac "(\<forall>y\<in>(insert x (Rep_USET xs)). \<D> y)")
  apply (auto simp add:InsertUS_def)
done

lift_definition MemberUS :: "'a::DEFINED \<Rightarrow> 'a USET \<Rightarrow> bool" is "op \<in>"
  by (auto)

lift_definition NMemberUS :: "'a::DEFINED \<Rightarrow> 'a USET \<Rightarrow> bool" is "op \<notin>"
  by (auto)

lift_definition UnionUS :: "'a::DEFINED USET \<Rightarrow> 'a USET \<Rightarrow> 'a USET" is "union"
  by (auto)

lift_definition InterUS :: "'a::DEFINED USET \<Rightarrow> 'a USET \<Rightarrow> 'a USET" is "inter"
  by (auto)

lift_definition MinusUS :: "'a::DEFINED USET \<Rightarrow> 'a USET \<Rightarrow> 'a USET" is "minus"
  by (auto)

lift_definition SubsetUS :: "'a::DEFINED USET \<Rightarrow> 'a USET \<Rightarrow> bool" is "subset"
  by (auto)

lift_definition SubseteqUS :: "'a::DEFINED USET \<Rightarrow> 'a USET \<Rightarrow> bool" is "subset_eq"
  by (auto)

lift_definition SetUS :: "'a::DEFINED ULIST \<Rightarrow> 'a USET" is "set"
  by (auto)

lift_definition RestrictUL :: "'a::DEFINED ULIST \<Rightarrow> 'a USET \<Rightarrow> 'a ULIST"
is "\<lambda> xs v. filter (\<lambda> x. x \<notin> v) xs"
  by (auto)

end