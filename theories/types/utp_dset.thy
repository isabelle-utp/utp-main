(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_dset.thy                                                         *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 30 July 2014 *)

header {* Defined Sets *}

theory utp_dset
imports utp_dlist
  "../core/utp_defined"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
begin

default_sort DEFINED

subsection {* Type Definition *}

text {* Rename the following type into @{text "'a dset"}. *}

typedef 'a USET = "{s :: 'a bset . \<forall> x \<in>\<^sub>b s . \<D> x}"
apply (rule_tac x = "{}\<^sub>b" in exI)
apply (auto simp add: bBall_def)
done

setup_lifting type_definition_USET

theorems Rep_USET' = Rep_USET [simplified]
theorems Abs_USET_inverse' = Abs_USET_inverse [simplified]
declare Rep_USET' [simp]
declare Abs_USET_inverse' [simp]
declare Rep_USET_inverse [simp]

lemma Rep_USET_intro [intro!] :
"Rep_USET x = Rep_USET y \<Longrightarrow> x = y"
apply (metis Rep_USET_inject)
done

lemma Rep_USET_elim [elim] :
"x = y \<Longrightarrow> \<lbrakk>Rep_USET x = Rep_USET y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (auto)
done

subsection {* Constants *}

lift_definition EmptyUS :: "'a USET"
is "{}\<^sub>b" by (simp add: bBall_def)

subsection {* Operators *}

lift_definition InsertUS :: "'a \<Rightarrow> 'a USET \<Rightarrow> 'a USET" 
is "\<lambda> x A. if (\<D> x) then bset_insert x A else A"
  by (auto simp add:bBall_def)

lift_definition MemberUS :: "'a \<Rightarrow> 'a USET \<Rightarrow> bool"
is "bset_member" .

lift_definition NMemberUS :: "'a \<Rightarrow> 'a USET \<Rightarrow> bool"
is "\<lambda> x A. Not (bset_member x A)" .

lift_definition UnionUS :: "'a USET \<Rightarrow> 'a USET \<Rightarrow> 'a USET"
is "bset_union" by (auto simp add: bBall_def)

lift_definition InterUS :: "'a USET \<Rightarrow> 'a USET \<Rightarrow> 'a USET"
is "bset_inter" by (auto simp add: bBall_def)

lift_definition MinusUS :: "'a USET \<Rightarrow> 'a USET \<Rightarrow> 'a USET"
is "bset_minus" by (auto simp add: bBall_def)

lift_definition SubsetUS :: "'a USET \<Rightarrow> 'a USET \<Rightarrow> bool"
is "bset_subset" .

lift_definition SubseteqUS :: "'a USET \<Rightarrow> 'a USET \<Rightarrow> bool"
is "bset_subset_eq" .

lift_definition SetUS :: "'a ULIST \<Rightarrow> 'a USET"
is "bset_set" by (auto)

lift_definition RestrictUS :: "'a ULIST \<Rightarrow> 'a USET \<Rightarrow> 'a ULIST"
is "\<lambda> xs A . filter (\<lambda> x . x \<notin>\<^sub>b A) xs" by (auto)

definition IntersyncUS ::
  "'a USET \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> ('a ULIST) USET" where
"IntersyncUS xs ys zs = Abs_USET
  (MkBSet (Abs_ULIST ` (intersync (DestBSet (Rep_USET xs)) (Rep_ULIST ys) (Rep_ULIST zs))))"

subsection {* Definedness *}

lemma USET_elems_defined [defined] :
"x \<in>\<^sub>b (Rep_USET xs) \<Longrightarrow> \<D> x"
apply (insert Rep_USET [of xs])
apply (auto)
done

instantiation USET :: (DEFINED) DEFINED_NE
begin
definition "defined_USET (xs :: 'a USET) = True"

lemma defined_USET [defined] :
"\<D> (xs :: 'a USET)"
  by (simp add: defined_USET_def)

instance
  by (intro_classes, auto simp add: defined_USET_def)
end

subsection {* Proof Support *}

text {* Set up the UTP proof tactics to evaluate defined sets. *}

lemma USET_transfer [eval, evale] :
"xs = ys \<longleftrightarrow> Rep_USET xs = Rep_USET ys"
  by (auto)

declare EmptyUS.rep_eq [eval, evale]
declare InsertUS.rep_eq [eval, evale]
declare UnionUS.rep_eq [eval, evale]
declare InterUS.rep_eq [eval, evale]
declare MinusUS.rep_eq [eval, evale]
declare MemberUS.rep_eq [eval, evale]
declare NMemberUS.rep_eq [eval, evale]
declare SubsetUS.rep_eq [eval, evale]
declare SubseteqUS.rep_eq [eval, evale]
declare SetUS.rep_eq [eval, evale]
declare IntersyncUS_def [eval, evale]
declare RestrictUS.rep_eq [eval, evale]
end
