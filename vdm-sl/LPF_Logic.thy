theory LPF_Logic
imports LPF
begin

section {*  LPF logic *}
text {* This definitions are based on the LPF logic described in
Moddelling systems - Practical Tools and techniques in software development
page 71-73 (Kleene logic)*}

subsection {* Logical operators *}

definition not_lpf :: "bool lpf \<Rightarrow> bool lpf" ("\<not>\<^sub>L _" [40] 40) where
[lpf_defs]: "not_lpf p = ( if (p = \<bottom>\<^sub>L) then \<bottom>\<^sub>L else Some\<^sub>L(\<not>(the\<^sub>L p)))"

definition conj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" (infixr "\<and>\<^sub>L" 35) where
[lpf_defs]: "conj_lpf p q = ( if (p = true\<^sub>L \<and> q = true\<^sub>L)
                              then true\<^sub>L
                              else 
                                if (p = false\<^sub>L \<or> q = false\<^sub>L) 
                                then false\<^sub>L 
                                else \<bottom>\<^sub>L)"

definition disj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" (infixr "\<or>\<^sub>L" 35) where
[lpf_defs]: "disj_lpf p q = (if(p = true\<^sub>L \<or> q = true\<^sub>L)
                                then true\<^sub>L
                              else if ((p = false\<^sub>L) \<and> (q = false\<^sub>L))
                                then false\<^sub>L
                              else \<bottom>\<^sub>L)"

definition implies_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" (infixr "\<Rightarrow>\<^sub>L" 25) where
[lpf_defs]: "implies_lpf p q = (if(p = false\<^sub>L \<or> q = true\<^sub>L) 
                                  then true\<^sub>L 
                                else if (p = true\<^sub>L \<and> q = false\<^sub>L)
                                  then false\<^sub>L
                                else \<bottom>\<^sub>L)"


(*
  TODO:
  kEx
  kAll
  kBAll
  kBEx
 *)
subsection {* Definedness rules *}

text {* The first task in setting up proof automation is automate definedness checking. We
        first prove some laws about the definedness of the logical connectives. We need
        to do this first, as these laws will be necessary for the proof calculus. *}

lemma lpf_defined [intro, simp]: "\<D>(Some\<^sub>L(x))"
  apply(simp add: defined_def)
  apply(simp add: lpf_Some_def)
  apply(simp add: lpf_None_def)
  by(simp add: Abs_lpf_inject)
 
lemma kdefined_alt_def: "\<D>(p) = \<lbrakk>p\<rbrakk>\<^sub>L \<or> \<lbrakk>\<not>\<^sub>L p\<rbrakk>\<^sub>L"
  by (lpf_simp)

lemma knot_defined [simp]: "\<D>(\<not>\<^sub>L p) = \<D>(p)"
  by (lpf_simp)

lemma knot_def_i [intro]: "\<D>(p) \<Longrightarrow> \<D>(\<not>\<^sub>L p)"
  by(lpf_simp)

lemma kand_def_i [intro]: "\<lbrakk>\<D>(p);\<D>(q)\<rbrakk> \<Longrightarrow> \<D>(p \<and>\<^sub>L q)"
  by (lpf_auto)

lemma kor_def_i [intro]: "\<lbrakk>\<D>(p);\<D>(q)\<rbrakk> \<Longrightarrow> \<D>(p \<or>\<^sub>Lq)"
  by (lpf_auto)

lemma kimpl_def_i [intro]: "\<lbrakk>\<D>(p); \<D>(q) \<rbrakk> \<Longrightarrow> \<D>(p \<Rightarrow>\<^sub>L q)"
  by (lpf_auto)

subsection {* Proof rules *}

lemma k_eq_i [intro]: "\<lbrakk> \<lbrakk>P \<Rightarrow>\<^sub>L Q\<rbrakk>\<^sub>L;\<lbrakk>Q \<Rightarrow>\<^sub>L P\<rbrakk>\<^sub>L \<rbrakk> \<Longrightarrow> P = Q"
  apply(cases P rule: lpf_cases)
  apply(cases Q rule: lpf_cases)
  apply(lpf_simp)
  apply(lpf_simp)
  apply(lpf_simp)
  apply(simp add: implies_lpf_def)
  apply(simp add: lpf_taut_def)
  oops
  

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
  
lemma double_negation [simp]: "(\<not>\<^sub>L(\<not>\<^sub>Lp)) = p"
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

lemma LPF_And_I [intro]: "\<lbrakk> \<lbrakk>P\<rbrakk>\<^sub>L; \<lbrakk>Q\<rbrakk>\<^sub>L \<rbrakk> \<Longrightarrow> \<lbrakk>P \<and>\<^sub>L Q\<rbrakk>\<^sub>L"
  by (simp add: conj_lpf_def lpf_taut_def)

lemma LPF_And_E [elim]: "\<lbrakk> \<lbrakk>P \<and>\<^sub>L Q\<rbrakk>\<^sub>L ; \<lbrakk>P\<rbrakk>\<^sub>L \<Longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>L \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  oops

lemma lpf_and_Some [simp]: "\<lbrakk>(p \<and>\<^sub>L q)\<rbrakk>\<^sub>L = \<lbrakk>p\<rbrakk>\<^sub>L \<and> \<lbrakk>q\<rbrakk>\<^sub>L"
 apply(simp add: lpf_taut_def)
 apply(rule lpf_cases)
 apply(lpf_auto)
 oops
end