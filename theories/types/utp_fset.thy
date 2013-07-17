(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_fset.thy                                                         *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* UTP Finite Sets *}

theory utp_fset
imports 
  "../core/utp_value"
  "../core/utp_sorts"
  "../core/utp_event"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  utp_list
begin

typedef 'a::DEFINED UFSET = "{xs :: 'a fset. \<forall>x\<in>\<^sub>fxs. \<D> x}"
  apply (rule_tac x="\<lbrace>\<rbrace>" in exI)
  apply (auto)
done

theorems Rep_UFSET' = Rep_UFSET [simplified]
declare Rep_UFSET' [simp]
declare Rep_UFSET_inverse [simp]
theorems Abs_UFSET_inverse' = Abs_UFSET_inverse [simplified]
declare Abs_UFSET_inverse' [simp]

lemma Rep_UFSET_intro [intro!]:
  "Rep_UFSET x = Rep_UFSET y \<Longrightarrow> x = y"
  by (simp add:Rep_UFSET_inject)

lemma Rep_UFSET_elim [elim]:
  "\<lbrakk> x = y; Rep_UFSET x = Rep_UFSET y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_UFSET

instantiation UFSET :: (DEFINED) DEFINED_NE
begin
definition "Defined_UFSET (xs :: 'a UFSET) = True"
instance 
  by (intro_classes, auto simp add:Defined_UFSET_def)
end

lemma Defined_UFSET [defined]: 
  "\<D> (xs :: ('a::DEFINED UFSET))"
  by (simp add:Defined_UFSET_def)

lift_definition EmptyUF :: "'a::DEFINED UFSET" is "fempty"
  by simp

definition InsertUF :: "'a::DEFINED \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET" where
"InsertUF x xs = Abs_UFSET (finsert x (Rep_UFSET xs))"

lemma InsertUF_rep_eq: 
  "\<D> x \<Longrightarrow> Rep_UFSET (InsertUF x xs) = finsert x (Rep_UFSET xs)"
  apply (subgoal_tac "(\<forall>y\<in>\<^sub>f(finsert x (Rep_UFSET xs)). \<D> y)")
  apply (auto simp add:InsertUF_def)
done

lift_definition MemberUF :: "'a::DEFINED \<Rightarrow> 'a UFSET \<Rightarrow> bool" is "fmember"
  by (auto)

lift_definition NMemberUF :: "'a::DEFINED \<Rightarrow> 'a UFSET \<Rightarrow> bool" is "fnmember"
  by (auto)

lift_definition UnionUF :: "'a::DEFINED UFSET \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET" is "funion"
  by (auto)

lift_definition InterUF :: "'a::DEFINED UFSET \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET" is "finter"
  by (auto)

lift_definition MinusUF :: "'a::DEFINED UFSET \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET" is "fminus"
  by (auto)

lift_definition SubsetUF :: "'a::DEFINED UFSET \<Rightarrow> 'a UFSET \<Rightarrow> bool" is "fsubset"
  by (auto)

lift_definition SubseteqUF :: "'a::DEFINED UFSET \<Rightarrow> 'a UFSET \<Rightarrow> bool" is "fsubset_eq"
  by (auto)

lift_definition FSetUF :: "'a::DEFINED ULIST \<Rightarrow> 'a UFSET" is "fset"
  by (auto)

definition IntersyncUF :: 
  "'a::DEFINED UFSET \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> ('a ULIST) UFSET"  where
"IntersyncUF xs ys zs = Abs_UFSET (Abs_ULIST `\<^sub>f (intersync (Rep_UFSET xs) (Rep_ULIST ys) (Rep_ULIST zs)))"

lemma UFSET_elems_defined [defined]:
  "x \<in>\<^sub>f (Rep_UFSET xs) \<Longrightarrow> \<D> x"
  apply (insert Rep_UFSET[of xs])
  apply (auto)
done

text {* Set up the predicate and expression tactics to evaluate lists *}

lemma UFSET_transfer [eval, evale]: 
  "xs = ys \<longleftrightarrow> Rep_UFSET xs = Rep_UFSET ys"
  by (auto)

declare EmptyUF.rep_eq [eval, evale]
declare InsertUF_rep_eq [eval, evale]
declare UnionUF.rep_eq [eval, evale]
declare InterUF.rep_eq [eval, evale]
declare MinusUF.rep_eq [eval, evale]
declare MemberUF.rep_eq [eval, evale]
declare NMemberUF.rep_eq [eval, evale]
declare SubsetUF.rep_eq [eval, evale]
declare SubseteqUF.rep_eq [eval, evale]
declare FSetUF.rep_eq [eval, evale]
declare IntersyncUF_def [eval, evale]

end