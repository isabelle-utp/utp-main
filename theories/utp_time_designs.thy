section {* Timed Designs *}

theory utp_time_designs
  imports utp_time_rel
begin

named_theorems td_simps and tdes
  
text {* We define timed designs via an embedding into reactive designs, where the pericondition
  is simply false: an instantaneous reactive design. The healthiness condition is therefore
  simply @{term ISRD}.  This allows us to reuse much of the infrastructure. *}
  
type_synonym 's tdes = "('s, real pos) rdes"
  
definition time_design :: "'s tdes \<Rightarrow> 's tdes \<Rightarrow> 's tdes" (infixl "\<turnstile>\<^sub>t" 60) where
[upred_defs]: "time_design P Q = \<^bold>R\<^sub>s(P \<turnstile> false \<diamondop> Q)"

abbreviation time_skip :: "'s tdes" ("II\<^sub>t") where
"II\<^sub>t \<equiv> II\<^sub>R"

definition time_wait :: "(real pos, 's) uexpr \<Rightarrow> 's tdes" ("wait\<^sub>t") where
[upred_defs, td_simps]: "wait\<^sub>t(n) = true\<^sub>r \<turnstile>\<^sub>t wait\<^sub>r(n)"

abbreviation time_pre :: "'s tdes \<Rightarrow> 's tdes" ("pre\<^sub>t") where
"pre\<^sub>t(P) \<equiv> pre\<^sub>R(P)"

abbreviation time_post :: "'s tdes \<Rightarrow> 's tdes" ("post\<^sub>t") where
"post\<^sub>t(P) \<equiv> post\<^sub>R(P)"

lemma pre_time_design [tdes]:
  assumes "P is RC" "Q is RR"
  shows "pre\<^sub>t(P \<turnstile>\<^sub>t Q) = P"
  by (simp add: time_design_def rdes assms closure)

lemma post_time_design [tdes]:
  assumes "P is RC" "Q is RR"
  shows "post\<^sub>t(P \<turnstile>\<^sub>t Q) = (P \<Rightarrow>\<^sub>r Q)"
  by (simp add: time_design_def rdes assms closure)
  
definition TD :: "'s tdes \<Rightarrow> 's tdes" where
[upred_defs]: "TD = ISRD"
    
lemma TD_implies_ISRD [closure]: "P is TD \<Longrightarrow> P is ISRD"
  by (simp add: TD_def)

lemma TD_elim: "\<lbrakk> P is TD; Q(pre\<^sub>t(P) \<turnstile>\<^sub>t post\<^sub>t(P)) \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: TD_def time_design_def ISRD_elim)
    
thm RHS_tri_normal_design_composition'
    
lemma skip_time_design [td_simps]:
  "II\<^sub>t = true\<^sub>r \<turnstile>\<^sub>t II\<^sub>r"
  by (simp add: rdes_def time_design_def) 
  
lemma seq_time_design [td_simps]: 
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "Q\<^sub>1 is RC" "Q\<^sub>2 is RR"
  shows "(P\<^sub>1 \<turnstile>\<^sub>t P\<^sub>2) ;; (Q\<^sub>1 \<turnstile>\<^sub>t Q\<^sub>2) = (P\<^sub>1 \<and> P\<^sub>2 wp\<^sub>R Q\<^sub>1) \<turnstile>\<^sub>t P\<^sub>2 ;; Q\<^sub>2"
  by (simp add: time_design_def RHS_tri_normal_design_composition' assms closure unrest)

lemma time_design_eq_intro: "\<lbrakk> P\<^sub>1 = Q\<^sub>1; (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) = (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<turnstile>\<^sub>t P\<^sub>2) = (Q\<^sub>1 \<turnstile>\<^sub>t Q\<^sub>2)"
  by (rel_auto, blast+)
     
method td_expand uses cls = (insert cls, (erule TD_elim)+)
  
method td_simp uses cls =
  ((td_expand cls: cls)?, (simp add: cls td_simps closure rpred alpha usubst unrest wp prod.case_eq_if))
  
method td_eq uses cls =
  (td_simp cls: cls; rule_tac time_design_eq_intro; (insert cls; rel_simp; auto?))
  
lemma time_skip_left_unit [simp]:
  assumes "P is TD"
  shows "II\<^sub>t ;; P = P"
  by (td_simp cls: assms)

lemma time_skip_right_unit [simp]:
  assumes "P is TD"
  shows "P ;; II\<^sub>t = P"
  by (td_simp cls: assms)

lemma time_wait_0 [simp]: "wait\<^sub>t(0) = II\<^sub>t"
  by (td_simp, simp add: wait_zero)
    
lemma time_wait_seq [simp]: "wait\<^sub>t(m) ;; wait\<^sub>t(n) = wait\<^sub>t(m + n)"
  by (td_simp, simp add: wait_plus)
    
end