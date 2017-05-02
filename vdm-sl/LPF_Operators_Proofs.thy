section {* LPF Proofs *}

text {* 
  This theory provides useful laws and illustrates the use of proof tactics 
  along with giving various examples of proof
*}

theory LPF_Operators_Proofs
imports LPF_Operators
begin

lemma lpf_cases [elim]:
  "\<lbrakk> p = true\<^sub>L \<Longrightarrow> P; p = false\<^sub>L \<Longrightarrow> P; p = \<bottom>\<^sub>L \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis (full_types) Rep_lpf_inject lpf_False.transfer lpf_None.rep_eq 
            lpf_Some.rep_eq lpf_True.transfer not_None_eq)

lemma all_lpf_transfer [lpf_transfer]:
"(\<forall>x::'a lpf. P x) = (\<forall>x::'a option. P (Abs_lpf x))" 
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs_lpf x" in spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep_lpf x" in spec)
by (simp add: Rep_lpf_inverse)

lemma ex_lpf_transfer [lpf_transfer]:
"(\<exists>x::'a lpf. P x) = (\<exists>x::'a option. P (Abs_lpf x))"
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "Rep_lpf x" in exI)
apply (simp add: Rep_lpf_inverse)
-- {* Subgoal 2 *}
apply (rule_tac x = "Abs_lpf x" in exI)
by (assumption)

lemma meta_lpf_transfer [lpf_transfer]:
"(\<And>x::'a lpf. P x) \<equiv> (\<And>x::'a option. P (Abs_lpf x))" 
apply (rule)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs_lpf x" in meta_spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep_lpf x" in meta_spec)
by (simp add: Rep_lpf_inverse)

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

lemma "(true\<^sub>L \<or>\<^sub>L true\<^sub>L) = true\<^sub>L"
by (lpf_auto)

lemma "(\<bottom>\<^sub>L \<or>\<^sub>L true\<^sub>L) = true\<^sub>L"
by (lpf_auto)

lemma "(true\<^sub>L \<or>\<^sub>L \<bottom>\<^sub>L) = true\<^sub>L"
by (lpf_auto)

lemma "(true\<^sub>L \<and>\<^sub>L true\<^sub>L) = true\<^sub>L"
  by (lpf_auto)

lemma "(false\<^sub>L \<and>\<^sub>L false\<^sub>L) = false\<^sub>L"
  by (lpf_auto)

lemma "(\<bottom>\<^sub>L \<and>\<^sub>L \<bottom>\<^sub>L) = \<bottom>\<^sub>L"
  by (lpf_auto)    
  
lemma double_negation : "(\<not>\<^sub>L\<not>\<^sub>Lp) = p"
by(lpf_auto)
    
lemma domination_or: "(p \<or>\<^sub>L true\<^sub>L) = true\<^sub>L"
by(lpf_auto)

lemma domination_and: "(p \<and>\<^sub>L false\<^sub>L) = false\<^sub>L"
by(lpf_auto)

lemma idempotent_and: "(p \<and>\<^sub>L p) = p"
  apply (cases p rule: lpf_cases)
  by(lpf_simp)+

lemma idempotent_or: "(p \<or>\<^sub>L p) = p"
  apply(cases p rule: lpf_cases)
  by(lpf_simp)+

lemma Commutative_Law : "(p \<and>\<^sub>L q) = (q  \<and>\<^sub>L p )"
  by(lpf_auto)
    
lemma associativity_Law : "(p \<and>\<^sub>L(q \<and>\<^sub>L r)) = ((p  \<and>\<^sub>L q ) \<and>\<^sub>L r)"
  by(lpf_auto)
    
lemma distributive_Law :  "(p \<and>\<^sub>L(q \<or>\<^sub>L r)) = ((p  \<and>\<^sub>L q ) \<or>\<^sub>L (p \<and>\<^sub>L r))"
  by(lpf_auto)
    
lemma DeMorgans_Law : "(\<not>\<^sub>L(p \<and>\<^sub>L q)) = (\<not>\<^sub>Lp \<or>\<^sub>L \<not>\<^sub>Lq )"
  by(lpf_auto)
  
lemma "A \<union>\<^sub>L B = B \<union>\<^sub>L A"
  by(lpf_auto)

end