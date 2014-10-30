(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_dfset.thy                                                        *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 30 July 2014 *)

header {* Defined Finite Sets *}

theory utp_dfset
imports utp_dlist
  (* "../utils/Library_extra/Fset" *)
  "../core/utp_defined"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
begin

default_sort DEFINED

subsection {* Type Definition *}

text {* Rename the following type into @{text "'a dfset"}. *}

typedef 'a UFSET = "{fs :: 'a fset . \<forall> x |\<in>| fs . \<D> x}"
apply (rule_tac x="\<lbrace>\<rbrace>" in exI)
apply (auto)
done

setup_lifting type_definition_UFSET

theorems Rep_UFSET' = Rep_UFSET [simplified]
theorems Abs_UFSET_inverse' = Abs_UFSET_inverse [simplified]
declare Rep_UFSET' [simp]
declare Abs_UFSET_inverse' [simp]
declare Rep_UFSET_inverse [simp]

lemma Rep_UFSET_intro [intro!] :
"Rep_UFSET x = Rep_UFSET y \<Longrightarrow> x = y"
apply (metis Rep_UFSET_inverse)
done

lemma Rep_UFSET_elim [elim] :
"x = y \<Longrightarrow> \<lbrakk>Rep_UFSET x = Rep_UFSET y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (auto)
done

subsection {* Constants *}

lift_definition EmptyUF :: "'a UFSET"
is "\<lbrace>\<rbrace>" by (simp)

subsection {* Operators *}

definition InsertUF :: "'a \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET" where
"InsertUF x xs = Abs_UFSET (finsert x (Rep_UFSET xs))"

lemma InsertUF_rep_eq:
"\<D> x \<Longrightarrow> Rep_UFSET (InsertUF x xs) = finsert x (Rep_UFSET xs)"
apply (subgoal_tac "\<forall> y |\<in>| (finsert x (Rep_UFSET xs)) . \<D> y")
apply (auto simp add: InsertUF_def)
done

lift_definition MemberUF :: "'a \<Rightarrow> 'a UFSET \<Rightarrow> bool"
is "fmember" .

lift_definition NMemberUF :: "'a \<Rightarrow> 'a UFSET \<Rightarrow> bool"
is "notin_fset" .

lift_definition UnionUF :: "'a UFSET \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET"
is "funion" by (auto)

lift_definition InterUF :: "'a UFSET \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET"
is "finter" by (auto)

lift_definition MinusUF :: "'a UFSET \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET"
is "fminus" by (auto)

lift_definition SubsetUF :: "'a UFSET \<Rightarrow> 'a UFSET \<Rightarrow> bool"
is "fsubset" .

lift_definition SubseteqUF :: "'a UFSET \<Rightarrow> 'a UFSET \<Rightarrow> bool"
is "fsubset_eq" .

lift_definition FSetUF :: "'a ULIST \<Rightarrow> 'a UFSET"
is "finset" by (metis fBall_intro finset.rep_eq) 

lift_definition RestrictUF :: "'a ULIST \<Rightarrow> 'a UFSET \<Rightarrow> 'a ULIST"
is "\<lambda> xs v . filter (\<lambda> x . x |\<notin>| v) xs"
  by (auto)

definition IntersyncUF ::
  "'a set \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> ('a ULIST) UFSET" where
"IntersyncUF xs ys zs = Abs_UFSET
  (Abs_fset (Abs_ULIST ` (intersync xs (Rep_ULIST ys) (Rep_ULIST zs))))"

subsection {* Definedness *}

lemma UFSET_elems_defined [defined] :
"x |\<in>| (Rep_UFSET xs) \<Longrightarrow> \<D> x"
  apply (insert Rep_UFSET [of xs])
  apply (auto)
  apply (metis Rep_UFSET' fBallE)
done

instantiation UFSET :: (DEFINED) DEFINED_NE
begin
definition "defined_UFSET (xs :: 'a UFSET) = True"

lemma defined_UFSET [defined] :
"\<D> (xs :: 'a UFSET)"
  by (simp add: defined_UFSET_def)

instance
  by (intro_classes, auto simp add: defined_UFSET_def)
end

subsection {* Proof Support *}

text {* Set up the predicate and expression tactics to evaluate lists *}

lemma UFSET_transfer [eval, evale] :
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
declare RestrictUF.rep_eq [eval, evale]
end
