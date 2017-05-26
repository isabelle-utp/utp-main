section {* LPF Proofs *}

text {* 
  This theory provides useful laws and illustrates the use of proof tactics 
  along with giving various examples of proof
*}

theory LPF_Operators_Proofs
imports LPF_Operators
begin

lemma "(lpf_Some x = lpf_Some y) \<longleftrightarrow> (x = y)"
by (lpf_simp)

lemma lifted_card_undefined_example: "lift1_lpf' card \<bottom>\<^sub>L = \<bottom>\<^sub>L"
by (lpf_simp)

lemma lifted_union_undefined_undefined_example: "lift2_lpf' union \<bottom>\<^sub>L \<bottom>\<^sub>L = \<bottom>\<^sub>L"
by (lpf_simp)

lemma lifted_union_defined_undefined_example: "lift2_lpf' union (lpf_Some {True}) \<bottom>\<^sub>L = \<bottom>\<^sub>L"
by (lpf_simp)

lemma lifted_union_defined_defined_example: "lift2_lpf' union (lpf_Some {True}) (lpf_Some {False}) = lpf_Some(union {True} {False} )"
by (lpf_simp)

lemma lifted_card_defined_example: "lift1_lpf' card (lpf_Some ({1,2,3}::nat set)) = lpf_Some 3"
by (lpf_simp)

lemma lpf_The_Some : "lpf_the (lpf_Some a) = a"
apply (simp add: lpf_Some_def)
apply (simp add: lpf_the_def)
by (simp add: Abs_lpf_inverse)

lemma "A \<union>\<^sub>L B = B \<union>\<^sub>L A"
  by(lpf_auto)

text {* Proof that a function returning undefined for values for which the 
  predicate holds makes the comprehension undefined. 
*}

lemma set_comprehension_lpf_undefined_fun: "(set_comprehension_lpf (\<lambda>x . \<bottom>\<^sub>L) 
  (lpf_Some {1::nat,2,3}) (\<lambda>x . true\<^sub>L)) = \<bottom>\<^sub>L"
apply(simp add: set_comprehension_lpf_def)
apply(simp add: defined_def)
by(simp add: lpf_The_Some)

text {* Proof that a predicate returning undefined makes the comprehension undefined. *}

lemma set_comprehension_lpf_undefined_pred: "(set_comprehension_lpf (\<lambda>x . lpf_Some x) 
  (lpf_Some {1::nat,2,3}) (\<lambda>x . \<bottom>\<^sub>L)) = \<bottom>\<^sub>L"
apply(simp add: set_comprehension_lpf_def)
apply(simp add: defined_def)
by(simp add: lpf_The_Some)

text {* Proof that a an undefined set makes the comprehension undefined. *}

lemma set_comprehension_lpf_undefined_set: "(set_comprehension_lpf (\<lambda>x . lpf_Some x) 
  \<bottom>\<^sub>L (\<lambda>x . \<bottom>\<^sub>L)) = \<bottom>\<^sub>L"
apply(simp add: set_comprehension_lpf_def)
by(simp add: defined_def)

subsection {* Example of proving a set comprehension *}
text {* 
  In this section we prove the same set comprehension in different ways.
*}

text {* This is a manual proof, which does not scale *}

lemma set_comprehension_lpf_manual: 
  "(set_comprehension_lpf (\<lambda>x. lpf_Some x) (lpf_Some {1,2,3}) (\<lambda>x. true\<^sub>L)) 
  = (lpf_Some {1,2,3})"
apply(simp add: set_comprehension_lpf_def)
apply(lpf_auto)
apply (rule_tac x = "Some 1" in exI)
apply(simp)
apply (rule_tac x = "Some 2" in exI)
apply(simp)
apply (rule_tac x = "Some 3" in exI)
by(simp)

text {* 
  As the proof above does not scale, we are interested in improving the automation.
  Therefore we provide the following lemma
*}

lemma ex_the_one_point [intro]:
"P (Some c) \<Longrightarrow> (\<exists>x. the x = c \<and> P x)"
apply (rule_tac x = "Some c" in exI)
apply (clarsimp)
done
text {*
  Application of the lemma @{thm ex_the_one_point} using rule transforms
  @{text "\<exists>x. the x = 1 \<and> (\<exists>xa. x = Some xa \<and> (xa = 1 \<or> xa = 2 \<or> xa = 3))"}
  into
  @{text "\<exists>x. Some 1 = Some x \<and> (x = 1 \<or> x = 2 \<or> x = 3)"}.
  The theorem replaces the goal with the premise.
  Next, we introduce another lemma, as the process is still manual.  
*}

lemma ex_Some_one_point [simp]:
"(\<exists>x. Some c = Some x \<and> P x) = (P c)"
apply (safe)
apply (rule_tac x = "c" in exI)
apply (clarsimp)
done

text {*
  Application of the lemma @{thm ex_Some_one_point} using subst transforms
  @{text "\<exists>x. Some 1 = Some x \<and> (x = 1 \<or> x = 2 \<or> x = 3)"}
  into
  @{text " 1. 1 = 1 \<or> 1 = 2 \<or> 1 = "}.
  which is easily solved by simp.
*}

text {* 
  To automate the process, one can create methods. 
*}

method ex_one_point =
  (rule ex_the_one_point, subst ex_Some_one_point, simp)

method ex_one_point' =
  (auto intro: ex_the_one_point simp: ex_Some_one_point)

text {* 
  These methods are interchangeable with auto in the example below.
  auto works, because the rules have been added to intro and simp respectively.
*}

lemma set_comprehension_lpf_automated: 
  "(set_comprehension_lpf (\<lambda>x. lpf_Some x) (lpf_Some {1,2,3}) (\<lambda>x. true\<^sub>L)) 
  = (lpf_Some {1,2,3})"
apply (simp add: set_comprehension_lpf_def)
apply (lpf_auto)
by (auto)

section {* LPF Logic *}



subsection {* Homomorphisms *}
lemma lpf_and_Some [simp]: "\<lbrakk>p \<and>\<^sub>L q\<rbrakk>\<^sub>L = \<lbrakk>p\<rbrakk>\<^sub>L \<and> \<lbrakk>q\<rbrakk>\<^sub>L"
  by (lpf_auto)
end