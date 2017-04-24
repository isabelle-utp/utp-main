theory LPF_Operators_Proofs
imports LPF_Operators
begin

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

subsection {* Boolean LPF *}

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

lemma lpf_cases [elim]:
  "\<lbrakk> p = true\<^sub>L \<Longrightarrow> P; p = false\<^sub>L \<Longrightarrow> P; p = \<bottom>\<^sub>L \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis (full_types) Rep_lpf_inject lpf_False.transfer lpf_None.rep_eq 
            lpf_Some.rep_eq lpf_True.transfer not_None_eq)

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