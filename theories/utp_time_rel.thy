section {* Timed Relations *}

theory utp_time_rel
imports
  utp_rea_designs
  utp_reactive_hoare
begin

type_synonym '\<alpha> trel = "('\<alpha>, real pos) rdes"

translations
  (type) "'\<alpha> trel" <= (type) "('\<alpha>, real pos) rdes"

abbreviation time :: "real pos \<Longrightarrow> (real pos, 'a) rp" where
"time \<equiv> tr"
  
definition wait_trel :: "(real pos, '\<alpha>) uexpr \<Rightarrow> '\<alpha> trel" ("wait\<^sub>r") where
[upred_defs]: "wait\<^sub>r(n) = ($st\<acute> =\<^sub>u $st \<and> $time\<acute> =\<^sub>u $time + \<lceil>n\<rceil>\<^sub>S\<^sub><)"

lemma wait_RR_closed [closure]: "wait\<^sub>r n is RR"
  by (rel_auto, metis add_monoid_diff_cancel_left minus_def trace_class.le_iff_add)
    
lemma st_subst_rea_wait [usubst]:
  "\<sigma> \<dagger>\<^sub>S wait\<^sub>r n = wait\<^sub>r (\<sigma> \<dagger> n) ;; \<langle>\<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
    
lemma wait_zero: "wait\<^sub>r(0) = II\<^sub>r"
  by (rel_auto)

lemma wait_plus: "wait\<^sub>r(m) ;; wait\<^sub>r(n) = wait\<^sub>r(m + n)"
  by (rel_auto, simp_all add: add.commute add.left_commute)
    
lemma wait_cond: "wait\<^sub>r(m) ;; (P \<triangleleft> b \<triangleright>\<^sub>R Q) = (wait\<^sub>r(m) ;; P \<triangleleft> b \<triangleright>\<^sub>R wait\<^sub>r(m) ;; Q)"
  by (rel_auto)

lemma wait_assign: "x \<sharp> m \<Longrightarrow> wait\<^sub>r(m) ;; x :=\<^sub>r v = x :=\<^sub>r v ;; wait\<^sub>r(m)"
  by (rel_auto)
    
lemma wait_hoare_rp [hoare_safe]:
  "\<lbrace>p\<rbrace>wait\<^sub>r n\<lbrace>p\<rbrace>\<^sub>r"
  by (rel_auto)
   
lemma hoare_rp_wait_comp [hoare_safe]:
  "\<lbrace>p\<rbrace> Q \<lbrace>r\<rbrace>\<^sub>r \<Longrightarrow> \<lbrace>p\<rbrace> wait\<^sub>r n ;; Q \<lbrace>r\<rbrace>\<^sub>r"
  by (rel_auto)
    
end
