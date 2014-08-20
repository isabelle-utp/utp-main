(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_fset.thy                                                         *)
(* Authors: Frank Zeyda & Simon Foster, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 24 June 2014 *)

header {* Finite Sets *}

theory fset
imports Main Countable "~~/src/HOL/BNF/BNF"
  "../utp_document"
begin

text {* Hide the existing type for finite sets from the BNF package. *}

hide_type "FSet.fset"
hide_const "FSet.fset"
hide_const "FSet.Abs_fset"

subsection {* Type Definition *}

definition fset :: "'a set set" where
"fset = Collect finite"

theorem fset_member_iff [iff] :
"s \<in> fset \<longleftrightarrow> finite s"
apply (simp add: fset_def)
done

typedef 'a fset = "fset :: 'a set set"
apply (rule_tac x = "{}" in exI)
apply (unfold fset_def)
apply (simp)
done

notation Rep_fset ("\<sim>_" [1000] 1000)

theorems Abs_fset_inject_sym = sym [OF Abs_fset_inject]
theorems Rep_fset_inject_sym = sym [OF Rep_fset_inject]

subsubsection {* Proof Support *}

declare Abs_fset_inverse [simp, intro!]
declare Rep_fset_inverse [simp]
declare Abs_fset_inject [simp, intro!]
declare Rep_fset_inject_sym [simp, intro!]
declare Rep_fset [simp]

theorem Rep_fset_finite [simp] :
"finite \<sim>fs"
apply (subst sym [OF fset_member_iff])
apply (rule Rep_fset)
done

subsection {* Finite Set Construction *}

setup_lifting type_definition_fset

paragraph {* Finite Empty Set *}

lift_definition fempty :: "'a fset" ("{}\<^sub>f")
is "{}"
apply (simp add: fset_def)
done

paragraph {* Finite Set Display *}

lift_definition finsert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
is "insert"
apply (simp add: fset_def)
done

syntax
  "_fset" :: "args \<Rightarrow> 'a fset" ("{(_)}\<^sub>f")

translations
  "{x, xs}\<^sub>f" == "(CONST finsert) x {xs}\<^sub>f"
  "{x}\<^sub>f"     == "(CONST finsert) x {}\<^sub>f"

subsection {* Lifted Operators *}

paragraph {* Finite Set Membership *}

lift_definition fmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "\<in>\<^sub>f" 50)
is "op \<in>" ..

lift_definition fnot_member :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "\<notin>\<^sub>f" 50)
is "op \<notin>" ..

paragraph {* Finite Set Union *}

lift_definition funion :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "\<union>\<^sub>f" 65)
is "op \<union>"
apply (simp add: fset_def)
done

paragraph {* Finite Set Intersection *}

lift_definition finter :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "\<inter>\<^sub>f" 70)
is "op \<inter>"
apply (simp add: fset_def)
done

paragraph {* Finite Set Difference *}

lift_definition fminus :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "-\<^sub>f" 65)
is "op -"
apply (simp add: fset_def)
done

paragraph {* Finite Set Image *}

lift_definition fimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset "(infixr "`\<^sub>f" 90)
is "image"
apply (simp add: fset_def)
done

paragraph {* Finite Set Inclusion *}

instantiation fset :: (type) ord
begin
lift_definition less_eq_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool"
is "op \<subseteq>" ..

lift_definition less_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool"
is "op \<subset>" ..
instance ..
end

abbreviation fsubset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "\<subseteq>\<^sub>f" 50) where
"fsubset_eq \<equiv> op \<le>"

abbreviation fsubset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "\<subset>\<^sub>f" 50) where
"fsubset \<equiv> op <"

paragraph {* Finite Set Cardinality *}

lift_definition fcard :: "'a fset \<Rightarrow> nat" ("card\<^sub>f")
is "card" ..

paragraph {* Finite Set Maximum *}

lift_definition fmax :: "'a::linorder fset \<Rightarrow> 'a" ("max\<^sub>f")
is "Max" ..

paragraph {* Finite Set of a List *}

lift_definition fset_of_list :: "'a list \<Rightarrow> 'a fset"
is "set"
apply (simp add: fset_def)
done

paragraph {* List of a Finite Set *}

lift_definition list_of_fset :: "'a fset \<Rightarrow> 'a list"
is "(\<lambda> s . SOME l . set l = s \<and> distinct l)" ..

paragraph {* Sorted List of a Finite Set *}

lift_definition sorted_list_of_fset :: "'a::linorder fset \<Rightarrow> 'a list"
is "sorted_list_of_set" ..

subsubsection {* Proof Support *}

declare fempty.rep_eq [simp]
declare finsert.rep_eq [simp]
declare fmember.rep_eq [simp]
declare fnot_member.rep_eq [simp]
declare funion.rep_eq [simp]
declare finter.rep_eq [simp]
declare fminus.rep_eq [simp]
declare fimage.rep_eq [simp]
declare fcard.rep_eq [simp]
declare fmax.rep_eq [simp]
declare less_eq_fset.rep_eq [simp]
declare less_fset.rep_eq [simp]
declare fset_of_list.rep_eq [simp]
(* declare list_of_fset.rep_eq [simp] *)
declare sorted_list_of_fset.rep_eq [simp]

subsection {* Finite Set Binders *}

abbreviation Fall :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Fall t p \<equiv> (\<forall> x . x \<in>\<^sub>f t \<longrightarrow> p x)"

abbreviation Fex :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Fex t p \<equiv> (\<exists> x . x \<in>\<^sub>f t \<and> p x)"

syntax
  "_Fall" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall> _\<in>\<^sub>f_./ _)" [0, 0, 10] 10)
  "_Fex"  :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists> _\<in>\<^sub>f_./ _)" [0, 0, 10] 10)

translations
  "\<forall> x\<in>\<^sub>fA. P" == "CONST Fall A (%x. P)"
  "\<exists> x\<in>\<^sub>fA. P" == "CONST Fex  A (%x. P)"

subsection {* Induction Rule *}

theorem fset_induct [induct type: fset] :
  assumes fempty_case : "P {}\<^sub>f" and
    finsert_case : "\<And> x fs . P fs \<Longrightarrow> x \<notin>\<^sub>f fs \<Longrightarrow> P (finsert x fs)"
  shows "P fs"
apply (induct_tac fs)
apply (rename_tac fs)
apply (simp)
apply (erule finite_induct)
-- {* Subgoal 1 *}
apply (insert fempty_case)
apply (unfold fempty_def)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "x" in finsert_case)
apply (unfold finsert_def)
apply (simp_all)
done

subsection {* Class Instantiations *}

subsubsection {* Instantiation of @{class order} *}

instance fset :: (type) order
apply (intro_classes)
apply (auto)
done

subsubsection {* Instantiation of @{class countable} *}

instance fset :: (countable) countable
apply (intro_classes)
apply (rule_tac x = "to_nat \<circ> list_of_fset" in exI)
apply (rule inj_comp)
apply (simp)
apply (rule injI)
apply (transfer)
apply (clarsimp)
apply (metis (lifting, mono_tags) finite_distinct_list some_eq_ex)
done

subsection {* Theorems *}

text {* Do we need these kinds of algebraic theorems despite transfer? *}

theorem funion_commute :
"a1 \<union>\<^sub>f a2 = a2 \<union>\<^sub>f a1"
apply (simp)
apply (auto)
done

subsubsection {* Distinct Lists of Sets *}

lemma set_some_list_from_set [simp] :
"finite fs \<Longrightarrow> set (SOME l . set l = fs \<and> distinct l) = fs"
apply (rule someI2_ex)
apply (erule finite_distinct_list)
apply (clarify)
done

lemma distinct_some_list_from_set [simp] :
"finite fs \<Longrightarrow> distinct (SOME l . set l = fs \<and> distinct l)"
apply (rule someI2_ex)
apply (erule finite_distinct_list)
apply (clarify)
done

subsubsection {* Sorted Lists *}

theorem sorted_leq_last [simp] :
"\<lbrakk>sorted l; x \<in> set l\<rbrakk> \<Longrightarrow> x \<le> last l"
apply (induct l)
apply (simp_all)
apply (auto simp: sorted_Cons)
done

theorem strict_mono_sorted_map [simp] :
"\<lbrakk>sorted l; strict_mono f\<rbrakk> \<Longrightarrow> sorted (map f l)"
apply (induct l)
apply (simp_all)
apply (simp add: sorted_Cons)
apply (metis strict_mono_less_eq)
done

theorem strict_mono_distinct_map [simp] :
"\<lbrakk>sorted l; strict_mono f; distinct l\<rbrakk> \<Longrightarrow> distinct (map f l)"
apply (induct l)
apply (simp_all)
apply (simp add: sorted_Cons)
apply (simp add: image_iff)
apply (metis strict_mono_eq)
done

theorem sorted_list_of_set_inverse [simp, intro!] :
"sorted l \<Longrightarrow> distinct l \<Longrightarrow>
 sorted_list_of_set (set l) = l"
apply (metis finite_set finite_sorted_distinct_unique sorted_list_of_set)
done

theorem sorted_list_of_set_inject :
"finite xs \<Longrightarrow> finite ys \<Longrightarrow>
 sorted_list_of_set xs = sorted_list_of_set ys \<longleftrightarrow> xs = ys"
apply (metis sorted_list_of_set)
done

subsubsection {* Finite Sets and Lists *}

theorem set_list_of_fset [simp] :
"set (list_of_fset fs) = \<sim>fs"
apply (transfer)
apply (unfold fset_member_iff)
apply (erule set_some_list_from_set)
done

theorem distinct_list_of_fset [simp] :
"distinct (list_of_fset fs)"
apply (transfer)
apply (unfold fset_member_iff)
apply (erule distinct_some_list_from_set)
done

theorem list_of_fset_inject [simp] :
"list_of_fset fs1 = list_of_fset fs2 \<longleftrightarrow> fs1 = fs2"
apply (metis Rep_fset_inject set_list_of_fset)
done

theorem sorted_list_of_fset_inject [simp] :
"sorted_list_of_fset fs1 = sorted_list_of_fset fs2 \<longleftrightarrow> fs1 = fs2"
apply (transfer)
apply (simp add: sorted_list_of_set_inject)
done

theorem inj_list_of_fset :
"inj list_of_fset"
apply (rule injI)
apply (unfold list_of_fset_inject)
apply (simp)
done

theorem inj_sorted_list_of_fset :
"inj sorted_list_of_fset"
apply (rule injI)
apply (unfold sorted_list_of_fset_inject)
apply (simp)
done

theorem sorted_list_of_fset_equal1  :
"sorted_list_of_fset fs = l \<longleftrightarrow>
 (\<sim>fs) = set l \<and> (sorted l) \<and> (distinct l)"
apply (transfer)
apply (safe)
apply (simp_all)
done

theorem sorted_list_of_fset_equal2 :
"l = sorted_list_of_fset fs \<longleftrightarrow>
 (\<sim>fs) = set l \<and> (sorted l) \<and> (distinct l)"
apply (transfer)
apply (safe)
apply (simp_all)
done

theorems sorted_list_of_fset_equal =
  sorted_list_of_fset_equal1
  sorted_list_of_fset_equal2

theorem sorted_list_of_fset_fempty :
"sorted_list_of_fset {}\<^sub>f = []"
apply (simp add: sorted_list_of_fset_equal1)
done

theorem sorted_list_of_fset_finsert :
"(\<And> y . y \<in>\<^sub>f fs \<longrightarrow> x < y) \<Longrightarrow>
  sorted_list_of_fset (finsert x fs) = x # (sorted_list_of_fset fs)"
apply (simp only: atomize_all)
apply (subst sorted_list_of_fset_equal1)
apply (simp add: sorted_list_of_fset_def)
apply (auto simp: sorted_Cons)
done

theorem sorted_list_of_fset_fimage :
"strict_mono f \<Longrightarrow>
 sorted_list_of_fset (f `\<^sub>f fs) = map f (sorted_list_of_fset fs)"
apply (subst sorted_list_of_fset_equal1)
apply (simp add: sorted_list_of_fset_def)
done

theorem fcard_length_sorted_list_of_fset :
"card\<^sub>f fs = length (sorted_list_of_fset fs)"
apply (induct fs)
apply (simp_all add: add: sorted_list_of_fset_def)
done

subsection {* BNF Datatype *}

subsubsection {* Auxiliary Operators *}

lift_definition fset_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> bool"
is "set_rel" ..

declare fset_rel.rep_eq [simp]

subsubsection {* Instantiation Lemmas *}

lemma finite_subset_image_aux :
"finite (f ` A) \<Longrightarrow>
 \<exists> B \<subseteq> A . finite B \<and> f ` B = f ` A"
apply (metis finite_subset_image order_refl)
done

lemma finite_rel_set :
"finite A \<Longrightarrow>
 finite B \<Longrightarrow>
 finite {(x, y). x \<in> A \<and> y \<in> B \<and> R x y}"
apply (subgoal_tac  "{(x, y). x \<in> A \<and> y \<in> B \<and> R x y} \<subseteq> A \<times> B")
apply (erule finite_subset)
apply (rule finite_cartesian_product)
apply (auto)
done

subsubsection {* BNF Registration *}

bnf fimage [Rep_fset] "\<lambda> _::'a fset. natLeq" ["{}\<^sub>f"] fset_rel
apply -
-- {* Subgoal 1 *}
apply (rule ext)
apply (simp)
-- {* Subgoal 2 *}
apply (rule ext)
apply (simp add: image_comp)
-- {* Subgoal 3 *}
apply (simp add: image_def)
-- {* Subgoal 4 *}
apply (rule ext)
apply (simp)
-- {* Subgoal 5 *}
apply (rule natLeq_card_order)
-- {* Subgoal 6 *}
apply (rule natLeq_cinfinite)
-- {* Subgoal 7 *}
apply (transfer)
apply (simp add: fset_def)
apply (metis ordLess_imp_ordLeq finite_iff_ordLess_natLeq)
-- {* Subgoal 8 *}
apply (drule wpull_image)
apply (simp add: wpull_def)
apply (transfer)
apply (simp add: fset_def)
apply (clarify)
apply (drule_tac x = "b1" in spec)
apply (drule_tac x = "b2" in spec)
apply (clarsimp)
apply (drule finite_subset_image_aux)+
apply (clarify)
apply (rename_tac A B1 B2 f1 f2 p1 p2 a b1' b2')
apply (rule_tac x = "b1' \<union> b2'" in exI)
apply (simp add: image_Un)
apply (auto) [1]
-- {* Subgoal 9 *}
apply (rule ext)+
apply (rename_tac R x y)
apply (simp)
apply (simp add: Grp_def relcompp.simps conversep.simps )
apply (transfer)
apply (simp add: fset_def)
apply (safe)
-- {* Subgoal 9.1 *}
apply (rule_tac x = "{(a, b) . a \<in> x \<and> b \<in> y \<and> R a b}" in exI)
apply (simp add: finite_rel_set)
apply (simp add: set_rel_def)
apply (auto simp: image_def) [1]
apply (rule_tac x = "xa" in exI)
apply (auto simp: image_def) [1]
-- {* Subgoal 9.2 *}
apply (simp add: set_rel_def)
apply (metis Collect_splitD set_rev_mp)
-- {* Subgoal 10 *}
apply (simp)
done

hide_fact finite_subset_image_aux finite_rel_set
end
