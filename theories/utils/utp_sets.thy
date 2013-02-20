(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_sets.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Cardinality-Bounded Sets *}

theory utp_sets
imports "../utp_common"
begin

text {*
  The benefit of considering sets with a bounded cardinality is that we can
  use them without soundness issues in recursive constructor functions of data
  types. They thus can provide a limited facility to handle infinite sets in
  the semantic model of UTP values. We make use of a type class to facilitate
  automation of proofs about such sets constructed over the various HOL types.
*}

subsection {* Type Definition *}

text {*
  For now we only consider countably infinite sets. However, higher degrees of
  infinity can in principle be supported.
*}

type_synonym IDX = "nat"

datatype 'a SET = MakeSet "IDX \<Rightarrow> 'a" | EmptySet

subsection {* Core Operators *}

definition IdxSet :: "'a set \<Rightarrow> bool" where
"(IdxSet s) \<longleftrightarrow> (s = {}) \<or> (\<exists> f :: IDX \<Rightarrow> 'a . s = range f)"

primrec DecSet :: "'a SET \<Rightarrow> 'a set" where
"DecSet (MakeSet f) = range f" |
"DecSet EmptySet = {}"

definition EncSet :: "'a set \<Rightarrow> 'a SET" where
"EncSet = (inv DecSet)"

text {* We observe that the representation is not canonical. *}

definition CongSet :: "'a SET \<Rightarrow> 'a SET \<Rightarrow> bool" (infix "\<cong>" 50) where
"s1 \<cong> s2 \<longleftrightarrow> (DecSet s1) = (DecSet s2)"

subsection {* Inverse Theorems *}

theorem DecSet_EncSet_inv :
"\<lbrakk>IdxSet s\<rbrakk> \<Longrightarrow> DecSet (EncSet s) = s"
apply (unfold EncSet_def)
apply (unfold inv_def)
apply (case_tac "s = {}")
-- {* Case 1: @{text "s = {}"} *}
apply (simp)
apply (rule_tac a = "EmptySet" in someI2)
apply (simp_all)
-- {* Case 2: @{text "s \<noteq> {}"} *}
apply (unfold IdxSet_def)
apply (clarify)
apply (rule_tac Q =
  "DecSet (SOME x . DecSet x = range f) = range f" in contrapos_np)
apply (assumption)
apply (rule_tac a = "MakeSet f" in someI2)
apply (simp_all)
done

theorem EncSet_DecSet_inv :
"EncSet (DecSet s) \<cong> s"
apply (unfold CongSet_def)
apply (rule DecSet_EncSet_inv)
apply (induct_tac)
apply (simp_all add: IdxSet_def)
apply (auto)
done

subsection {* Congruence Theorems *}

theorem CongSet_refl :
"s \<cong> s"
apply (simp add: CongSet_def)
done

theorem CongSet_sym :
"s1 \<cong> s2 \<longrightarrow> s2 \<cong> s1"
apply (simp add: CongSet_def)
done

theorem CongSet_trans :
"s1 \<cong> s2 \<and> s2 \<cong> s3 \<longrightarrow> s1 \<cong> s3"
apply (simp add: CongSet_def)
done

subsection {* Indexing Theorems *}

theorem IdxSet_DecSet :
"IdxSet (DecSet s)"
apply (unfold IdxSet_def)
apply (induct_tac)
apply (simp_all)
apply (auto)
done

theorem IdxSet_empty [simp] :
"IdxSet {}"
apply (simp add: IdxSet_def)
done

theorem IdxSet_subset [simp] :
"\<lbrakk>s \<subseteq> t; IdxSet t\<rbrakk> \<Longrightarrow> IdxSet s"
apply (simp add: IdxSet_def)
apply (case_tac "s = {}")
apply (simp_all)
apply (case_tac "t = {}")
apply (simp_all)
apply (erule "exE")+
apply (rule_tac x =
  "(\<lambda> i . if (f i) \<in> s then (f i) else (SOME x . x \<in> s))" in exI)
apply (auto)
apply (rule_tac a = "x" in someI2)
apply (simp_all)
done

text {* The following proof may fail if the definition of @{typ IDX} changes. *}

theorem IdxSet_union [simp] :
"\<lbrakk>IdxSet s1; IdxSet s2\<rbrakk> \<Longrightarrow> IdxSet (s1 \<union> s2)"
apply (simp add: IdxSet_def)
apply (case_tac "s1 = {}")
apply (simp_all)
apply (case_tac "s2 = {}")
apply (simp_all)
apply (erule "exE")+
apply (rule_tac x =
  "(\<lambda> n . case (sum_decode n) of
     (Inl n1) \<Rightarrow> f n1 |
     (Inr n2) \<Rightarrow> fa n2)" in exI)
apply (clarsimp)
apply (simp add: image_def)
apply (safe)
apply (rule_tac x = "sum_encode (Inl xa)" in exI)
apply (simp)
apply (rule_tac x = "sum_encode (Inr xa)" in exI)
apply (simp)
apply (clarsimp)
apply (rule_tac x = "xa div 2" in exI)
apply (drule_tac x = "xa div 2" in spec)
apply (simp add: sum_encode_def sum_decode_def)
apply (auto)
done

theorem IdxSet_inter [simp] :
"\<lbrakk>IdxSet s1; IdxSet s2\<rbrakk> \<Longrightarrow> IdxSet (s1 \<inter> s2)"
apply (simp add: IdxSet_def)
apply (case_tac "s1 \<inter> s2 = {}")
apply (simp_all)
apply (drule_tac R = "\<exists>f. s1 \<inter> s2 = range f" in disjE)
apply (simp_all)
apply (drule_tac R = "\<exists>f. s1 \<inter> s2 = range f" in disjE)
apply (simp_all)
apply (erule exE)+
apply (rule_tac x =
  "(\<lambda> i . if (\<exists> i' . (f i) = (fa i')) then (f i) else
   (SOME x . x \<in> s1 \<inter> s2))" in exI)
apply (auto)
apply (rule_tac a = "f xa" in someI2)
apply (simp_all)
apply (drule sym)
apply (simp)
apply (rule_tac a = "f xa" in someI2)
apply (simp_all)
apply (drule sym)
apply (simp)
done

theorem IdxSet_insert [simp] :
"IdxSet s \<Longrightarrow> IdxSet (insert x s)"
apply (unfold insert_def)
apply (subst IdxSet_union)
apply (simp_all)
apply (simp add: IdxSet_def)
apply (rule_tac x = "(\<lambda> i . x)" in exI)
apply (auto)
done

theorem IdxSet_image :
"IdxSet s \<Longrightarrow> IdxSet (f ` s)"
apply (unfold IdxSet_def)
apply (induct_tac)
apply (simp_all)
apply (auto)
done

subsection {* Lifted Set Operators *}

definition set_compl :: "'a SET \<Rightarrow> 'a SET" ("-s _" [81] 80) where
"-s s = EncSet(- DecSet(s))"

definition set_union ::"'a SET \<Rightarrow> 'a SET \<Rightarrow> 'a SET" (infixl "\<union>s" 65) where
"s1 \<union>s s2 = EncSet(DecSet(s1) \<union> DecSet(s2))"

definition set_inter :: "'a SET \<Rightarrow> 'a SET \<Rightarrow> 'a SET" (infixl "\<inter>s" 70) where
"s1 \<inter>s s2 = EncSet(DecSet(s1) \<inter> DecSet(s2))"

definition set_minus :: "'a SET \<Rightarrow> 'a SET \<Rightarrow> 'a SET" (infixl "-s" 65) where
"s1 -s s2 = EncSet(DecSet(s1) - DecSet(s2))"

definition set_member :: "'a \<Rightarrow> 'a SET \<Rightarrow> bool" ("(_/ \<in>s _)" [50, 51] 50) where
"x \<in>s s = (x \<in> DecSet(s))"

definition set_not_member :: "'a \<Rightarrow> 'a SET \<Rightarrow> bool" ("(_/ \<notin>s _)" [50, 51] 50) where
"x \<notin>s s = (x \<notin> DecSet(s))"

definition set_subset :: "'a SET \<Rightarrow> 'a SET \<Rightarrow> bool" ("(_/ \<subset>s _)" [50, 51] 50) where
"s1 \<subset>s s2 = (DecSet(s1) \<subset> DecSet(s2))"

definition set_subset_eq :: "'a SET \<Rightarrow> 'a SET \<Rightarrow> bool" ("(_/ \<subseteq>s _)" [50, 51] 50) where
"s1 \<subseteq>s s2 = (DecSet(s1) \<subseteq> DecSet(s2))"

subsection {* Default Simplifications *}

declare DecSet_EncSet_inv [simp]
declare EncSet_DecSet_inv [simp]
declare IdxSet_DecSet [simp]
declare IdxSet_empty [simp]
declare IdxSet_subset [simp]
declare IdxSet_union [simp]
declare IdxSet_inter [simp]
declare IdxSet_insert [simp]
declare IdxSet_image [simp]
declare CongSet_refl [simp]

declare set_compl_def [simp]
declare set_union_def [simp]
declare set_inter_def [simp]
declare set_minus_def [simp]
declare set_member_def [simp]
declare set_not_member_def [simp]
declare set_subset_def [simp]
declare set_subset_eq_def [simp]

subsection {* Type Class Indexable *}

class indexable =
  assumes IdxSet [simp] : "\<forall> s :: 'a set . IdxSet s"

text {* The following proof may fail if the definition of @{typ IDX} changes. *}

instance countable \<subseteq> indexable
apply (intro_classes)
apply (clarify)
apply (unfold IdxSet_def)
apply (case_tac "s = {}")
-- {* Case 1: @{text "s = {}"} *}
apply (simp_all)
-- {* Case 2: @{text "s \<noteq> {}"} *}
-- {* The witness is the most tricky bit here. *}
apply (rule_tac x =
  "(\<lambda> i :: IDX .
     if (inv to_nat) i \<in> s then (inv to_nat) i else (SOME x . x \<in> s))" in exI)
apply (simp add: image_def)
apply (safe)
apply (rule_tac Q = "\<exists> x . inv to_nat x \<in> s \<and> xa = inv to_nat x" in contrapos_np)
apply (assumption)
apply (rule_tac x = "to_nat xa" in exI)
apply (simp)
apply (rule_tac Q = "\<exists> x . inv to_nat x \<in> s \<and> xa = inv to_nat x" in contrapos_np)
apply (assumption)
apply (rule_tac x = "to_nat xa" in exI)
apply (simp)
apply (rule_tac a = "x" in someI2)
apply (auto)
done

instance finite \<subseteq> indexable
apply (intro_classes)
done

subsection {* Proof Experiments *}

theorem sets_test_lemma_1 :
"DecSet(EncSet {1, 2, 3}) = {1, 2, 3}"
apply (simp)
done

theorem sets_test_lemma_2 :
"DecSet(EncSet {[1, 2]} \<union>s EncSet {[3]}) = {[1, 2], [3]}"
apply (auto)
done
end
