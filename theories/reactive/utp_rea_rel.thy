section \<open> Reactive Relations \<close>

theory utp_rea_rel
  imports 
    utp_rea_healths
    "UTP-KAT.utp_kleene"
begin

text \<open> This theory defines a reactive relational calculus for @{term R1}-@{term R2} predicates as an 
  extension of the standard alphabetised predicate calculus. This enables us to formally characterise
  relational programs that refer to both state variables and a trace history. For more details on
  reactive relations, please see the associated journal paper~\cite{Foster17c}. \<close>

subsection \<open> Healthiness Conditions \<close>

definition RR :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "RR(P) = (\<exists> {$ok,$ok\<acute>,$wait,$wait\<acute>} \<bullet> R2(P))"
  
lemma RR_idem: "RR(RR(P)) = RR(P)"
  by (rel_auto)

lemma RR_Idempotent [closure]: "Idempotent RR"
  by (simp add: Idempotent_def RR_idem)

lemma RR_Continuous [closure]: "Continuous RR"
  by (rel_blast)
    
lemma R1_RR: "R1(RR(P)) = RR(P)"
  by (rel_auto)
    
lemma R2c_RR: "R2c(RR(P)) = RR(P)"
  by (rel_auto)
    
lemma RR_implies_R1 [closure]: "P is RR \<Longrightarrow> P is R1"
  by (metis Healthy_def R1_RR)
  
lemma RR_implies_R2c: "P is RR \<Longrightarrow> P is R2c"
  by (metis Healthy_def R2c_RR)
  
lemma RR_implies_R2 [closure]: "P is RR \<Longrightarrow> P is R2"
  by (metis Healthy_def R1_RR R2_R2c_def R2c_RR)

lemma RR_intro:
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "P is R1" "P is R2c"
  shows "P is RR"
  by (simp add: RR_def Healthy_def ex_plus R2_R2c_def, simp add: Healthy_if assms ex_unrest)
    
lemma RR_R2_intro:
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P" "P is R2"
  shows "P is RR"
  by (simp add: RR_def Healthy_def ex_plus, simp add: Healthy_if assms ex_unrest)
    
lemma RR_unrests [unrest]: 
  assumes "P is RR"
  shows "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
proof -
  have "$ok \<sharp> RR(P)" "$ok\<acute> \<sharp> RR(P)" "$wait \<sharp> RR(P)" "$wait\<acute> \<sharp> RR(P)"
    by (simp_all add: RR_def ex_plus unrest)
  thus "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (simp_all add: assms Healthy_if)
qed

lemma RR_refine_intro:
  assumes "P is RR" "Q is RR" "\<And> t. P\<lbrakk>0,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> Q\<lbrakk>0,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>"
  shows "P \<sqsubseteq> Q"
proof -
  have "\<And> t. (RR P)\<lbrakk>0,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> (RR Q)\<lbrakk>0,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>"
    by (simp add: Healthy_if assms)
  hence "RR(P) \<sqsubseteq> RR(Q)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma R4_RR_closed [closure]:
  assumes "P is RR"
  shows "R4(P) is RR"
proof -
  have "R4(RR(P)) is RR"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma R5_RR_closed [closure]:
  assumes "P is RR"
  shows "R5(P) is RR"
proof -
  have "R5(RR(P)) is RR"
    using minus_zero_eq by rel_auto
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

subsection \<open> Reactive relational operators \<close>

named_theorems rpred
  
abbreviation rea_true :: "('t::trace,'\<alpha>,'\<beta>) rel_rp" ("true\<^sub>r") where 
"true\<^sub>r \<equiv> R1(true)"     

definition rea_not :: "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" ("\<not>\<^sub>r _" [40] 40) 
where [upred_defs]: "(\<not>\<^sub>r P) = R1(\<not> P)"

definition rea_diff :: "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" (infixl "-\<^sub>r" 65)
where [upred_defs]: "rea_diff P Q = (P \<and> \<not>\<^sub>r Q)"
  
definition rea_impl :: 
  "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" (infixr "\<Rightarrow>\<^sub>r" 25) 
where [upred_defs]: "(P \<Rightarrow>\<^sub>r Q) = (\<not>\<^sub>r P \<or> Q)"

definition rea_lift :: "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" ("[_]\<^sub>r") 
where [upred_defs]: "[P]\<^sub>r = R1(P)"
   
definition rea_skip :: "('t::trace,'\<alpha>) hrel_rp" ("II\<^sub>r") 
where [upred_defs]: "II\<^sub>r = ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
  
definition rea_assert :: "('t::trace,'\<alpha>) hrel_rp \<Rightarrow> ('t,'\<alpha>) hrel_rp" ("{_}\<^sub>r")
where [upred_defs]: "{b}\<^sub>r = (II\<^sub>r \<or> \<not>\<^sub>r b)"

text \<open> Convert from one trace algebra to another using renamer functions, which are a kind of
  monoid homomorphism. \<close>

locale renamer =
  fixes f :: "'a::trace \<Rightarrow> 'b::trace"
  assumes 
    injective: "inj f" and
    add: "f (x + y) = f x + f y"
begin
  lemma zero: "f 0 = 0"
    by (metis add add.right_neutral add_monoid_diff_cancel_left)

  lemma monotonic: "mono f"
    by (metis add monoI trace_class.le_iff_add)

  lemma minus: "x \<le> y \<Longrightarrow> f (y - x) = f(y) - f(x)"
    by (metis add diff_add_cancel_left' trace_class.add_diff_cancel_left)
end

declare renamer.add [simp]
declare renamer.zero [simp]
declare renamer.minus [simp]

lemma renamer_id: "renamer id"
  by (unfold_locales, simp_all)

lemma renamer_comp: "\<lbrakk> renamer f; renamer g \<rbrakk> \<Longrightarrow> renamer (f \<circ> g)"
  by (unfold_locales, simp_all add: inj_compose renamer.injective)

lemma renamer_map: "inj f \<Longrightarrow> renamer (map f)"
  by (unfold_locales, simp_all add: plus_list_def)

definition rea_rename :: "('t\<^sub>1::trace,'\<alpha>) hrel_rp \<Rightarrow> ('t\<^sub>1 \<Rightarrow> 't\<^sub>2) \<Rightarrow> ('t\<^sub>2::trace,'\<alpha>) hrel_rp" ("(_)\<lparr>_\<rparr>\<^sub>r" [999, 0] 999) where
[upred_defs]: "rea_rename P f = R2(($tr\<acute> =\<^sub>u 0 \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; P ;; ($tr\<acute> =\<^sub>u uop f $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"

text \<open> Trace contribution substitution: make a substitution for the trace contribution lens 
  @{term tt}, and apply @{term R1} to make the resulting predicate healthy again. \<close>
  
definition rea_subst :: "('t::trace, '\<alpha>) hrel_rp \<Rightarrow> ('t, ('t, '\<alpha>) rp) hexpr \<Rightarrow> ('t, '\<alpha>) hrel_rp" ("_\<lbrakk>_\<rbrakk>\<^sub>r" [999,0] 999) 
where [upred_defs]: "P\<lbrakk>v\<rbrakk>\<^sub>r = R1(P\<lbrakk>v/&tt\<rbrakk>)"

subsection \<open> Unrestriction and substitution laws \<close>

lemma rea_true_unrest [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> true\<^sub>r"
  by (simp add: R1_def unrest lens_indep_sym)

lemma rea_not_unrest [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> \<not>\<^sub>r P"
  by (simp add: rea_not_def R1_def unrest lens_indep_sym)

lemma rea_impl_unrest [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<Rightarrow>\<^sub>r Q)"
  by (simp add: rea_impl_def unrest)

lemma rea_true_usubst [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; $tr\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> true\<^sub>r = true\<^sub>r"
  by (simp add: R1_def usubst)
  
lemma rea_not_usubst [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; $tr\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (\<not>\<^sub>r P) = (\<not>\<^sub>r \<sigma> \<dagger> P)"
  by (simp add: rea_not_def R1_def usubst)

lemma rea_impl_usubst [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; $tr\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (P \<Rightarrow>\<^sub>r Q) = (\<sigma> \<dagger> P \<Rightarrow>\<^sub>r \<sigma> \<dagger> Q)"
  by (simp add: rea_impl_def usubst R1_def)

lemma rea_true_usubst_tt [usubst]: 
  "R1(true)\<lbrakk>e/&tt\<rbrakk> = true"
  by (rel_simp)

lemma unrests_rea_rename [unrest]: 
  "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$wait \<sharp> P \<Longrightarrow> $wait \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  "$wait\<acute> \<sharp> P \<Longrightarrow> $wait\<acute> \<sharp> P\<lparr>f\<rparr>\<^sub>r"
  by (simp_all add: rea_rename_def R2_def unrest)

lemma unrest_rea_subst [unrest]: 
  "\<lbrakk> mwb_lens x; x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<sharp> v; x \<sharp> P \<rbrakk> \<Longrightarrow>  x \<sharp> P\<lbrakk>v\<rbrakk>\<^sub>r"
  by (simp add: rea_subst_def R1_def unrest lens_indep_sym)

lemma rea_substs [usubst]: 
  "true\<^sub>r\<lbrakk>v\<rbrakk>\<^sub>r = true\<^sub>r" "true\<lbrakk>v\<rbrakk>\<^sub>r = true\<^sub>r" "false\<lbrakk>v\<rbrakk>\<^sub>r = false"
  "(\<not>\<^sub>r P)\<lbrakk>v\<rbrakk>\<^sub>r = (\<not>\<^sub>r P\<lbrakk>v\<rbrakk>\<^sub>r)" "(P \<and> Q)\<lbrakk>v\<rbrakk>\<^sub>r = (P\<lbrakk>v\<rbrakk>\<^sub>r \<and> Q\<lbrakk>v\<rbrakk>\<^sub>r)" "(P \<or> Q)\<lbrakk>v\<rbrakk>\<^sub>r = (P\<lbrakk>v\<rbrakk>\<^sub>r \<or> Q\<lbrakk>v\<rbrakk>\<^sub>r)"
  "(P \<Rightarrow>\<^sub>r Q)\<lbrakk>v\<rbrakk>\<^sub>r = (P\<lbrakk>v\<rbrakk>\<^sub>r \<Rightarrow>\<^sub>r Q\<lbrakk>v\<rbrakk>\<^sub>r)"
  by rel_auto+

lemma rea_substs_lattice [usubst]:
  "(\<Sqinter> i \<bullet> P(i))\<lbrakk>v\<rbrakk>\<^sub>r   = (\<Sqinter> i \<bullet> (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
  "(\<Sqinter> i\<in>A \<bullet> P(i))\<lbrakk>v\<rbrakk>\<^sub>r = (\<Sqinter> i\<in>A \<bullet> (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
  "(\<Squnion> i \<bullet> P(i))\<lbrakk>v\<rbrakk>\<^sub>r   = (\<Squnion> i \<bullet> (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
   by (rel_auto)+
    
lemma rea_subst_USUP_set [usubst]:
  "A \<noteq> {} \<Longrightarrow> (\<Squnion> i\<in>A \<bullet> P(i))\<lbrakk>v\<rbrakk>\<^sub>r   = (\<Squnion> i\<in>A \<bullet> (P(i))\<lbrakk>v\<rbrakk>\<^sub>r)"
  by (rel_auto)+

subsection \<open> Closure laws \<close>

lemma rea_lift_R1 [closure]: "[P]\<^sub>r is R1"
  by (rel_simp)
    
lemma R1_rea_not: "R1(\<not>\<^sub>r P) = (\<not>\<^sub>r P)"
  by rel_auto
    
lemma R1_rea_not': "R1(\<not>\<^sub>r P) = (\<not>\<^sub>r R1(P))"
  by rel_auto  
  
lemma R2c_rea_not: "R2c(\<not>\<^sub>r P) = (\<not>\<^sub>r R2c(P))"
  by rel_auto

lemma RR_rea_not: "RR(\<not>\<^sub>r RR(P)) = (\<not>\<^sub>r RR(P))"
  by (rel_auto)
    
lemma R1_rea_impl: "R1(P \<Rightarrow>\<^sub>r Q) = (P \<Rightarrow>\<^sub>r R1(Q))"
  by (rel_auto)

lemma R1_rea_impl': "R1(P \<Rightarrow>\<^sub>r Q) = (R1(P) \<Rightarrow>\<^sub>r R1(Q))"
  by (rel_auto)
    
lemma R2c_rea_impl: "R2c(P \<Rightarrow>\<^sub>r Q) = (R2c(P) \<Rightarrow>\<^sub>r R2c(Q))"
  by (rel_auto)

lemma RR_rea_impl: "RR(RR(P) \<Rightarrow>\<^sub>r RR(Q)) = (RR(P) \<Rightarrow>\<^sub>r RR(Q))"
  by (rel_auto)
 
lemma rea_true_R1 [closure]: "true\<^sub>r is R1"
  by (rel_auto)
  
lemma rea_true_R2c [closure]: "true\<^sub>r is R2c"
  by (rel_auto)
    
lemma rea_true_RR [closure]: "true\<^sub>r is RR"
  by (rel_auto)
     
lemma rea_not_R1 [closure]: "\<not>\<^sub>r P is R1"
  by (rel_auto)

lemma rea_not_R2c [closure]: "P is R2c \<Longrightarrow> \<not>\<^sub>r P is R2c"
  by (simp add: Healthy_def rea_not_def R1_R2c_commute[THEN sym] R2c_not)
   
lemma rea_not_R2_closed [closure]:
  "P is R2 \<Longrightarrow> (\<not>\<^sub>r P) is R2"
  by (simp add: Healthy_def' R1_rea_not' R2_R2c_def R2c_rea_not)

lemma rea_no_RR [closure]:
  "\<lbrakk> P is RR \<rbrakk> \<Longrightarrow> (\<not>\<^sub>r P) is RR"
  by (metis Healthy_def' RR_rea_not)

lemma rea_impl_R1 [closure]: 
  "Q is R1 \<Longrightarrow> (P \<Rightarrow>\<^sub>r Q) is R1"
  by (rel_blast)

lemma rea_impl_R2c [closure]: 
  "\<lbrakk> P is R2c; Q is R2c \<rbrakk> \<Longrightarrow> (P \<Rightarrow>\<^sub>r Q) is R2c"
  by (simp add: rea_impl_def Healthy_def rea_not_def R1_R2c_commute[THEN sym] R2c_not R2c_disj)

lemma rea_impl_R2 [closure]: 
  "\<lbrakk> P is R2; Q is R2 \<rbrakk> \<Longrightarrow> (P \<Rightarrow>\<^sub>r Q) is R2"
  by (rel_blast)

lemma rea_impl_RR [closure]:
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> (P \<Rightarrow>\<^sub>r Q) is RR"
  by (metis Healthy_def' RR_rea_impl)
  
lemma conj_RR [closure]:
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> (P \<and> Q) is RR"
  by (meson RR_implies_R1 RR_implies_R2c RR_intro RR_unrests(1-4) conj_R1_closed_1 conj_R2c_closed unrest_conj)

lemma disj_RR [closure]:
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> (P \<or> Q) is RR"
  by (metis Healthy_def' R1_RR R1_idem R1_rea_not' RR_rea_impl RR_rea_not disj_comm double_negation rea_impl_def rea_not_def)

lemma USUP_mem_RR_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is RR" "A \<noteq> {}"
  shows "(\<Squnion> i\<in>A \<bullet> P(i)) is RR"
proof -
  have 1:"(\<Squnion> i\<in>A \<bullet> P(i)) is R1"
    by (unfold Healthy_def, subst R1_UINF, simp_all add: Healthy_if assms closure cong: USUP_cong)
  have 2:"(\<Squnion> i\<in>A \<bullet> P(i)) is R2c"
    by (unfold Healthy_def, subst R2c_UINF, simp_all add: Healthy_if assms RR_implies_R2c closure cong: USUP_cong)
  show ?thesis
    using 1 2 by (rule_tac RR_intro, simp_all add: unrest assms)
qed

lemma USUP_ind_RR_closed [closure]:
  assumes "\<And> i. P i is RR"
  shows "(\<Squnion> i \<bullet> P(i)) is RR"
  using USUP_mem_RR_closed[of UNIV P] by (simp add: assms)

lemma UINF_mem_RR_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is RR"
  shows "(\<Sqinter> i\<in>A \<bullet> P(i)) is RR"
proof -
  have 1:"(\<Sqinter> i\<in>A \<bullet> P(i)) is R1"
    by (unfold Healthy_def, subst R1_USUP, simp add: Healthy_if RR_implies_R1 assms cong: UINF_cong)
  have 2:"(\<Sqinter> i\<in>A \<bullet> P(i)) is R2c"
    by (unfold Healthy_def, subst R2c_USUP, simp add: Healthy_if RR_implies_R2c assms cong: UINF_cong)
  show ?thesis
    using 1 2 by (rule_tac RR_intro, simp_all add: unrest assms)
qed
    
lemma UINF_ind_RR_closed [closure]:
  assumes "\<And> i. P i is RR"
  shows "(\<Sqinter> i \<bullet> P(i)) is RR"
  by (simp add: assms closure)
    
lemma USUP_elem_RR [closure]: 
  assumes "\<And> i. P i is RR" "A \<noteq> {}"
  shows "(\<Squnion> i \<in> A \<bullet> P i) is RR"
proof -
  have 1:"(\<Squnion> i\<in>A \<bullet> P(i)) is R1"
    by (unfold Healthy_def, subst R1_UINF, simp_all add: Healthy_if assms closure)
  have 2:"(\<Squnion> i\<in>A \<bullet> P(i)) is R2c"
    by (unfold Healthy_def, subst R2c_UINF, simp_all add: Healthy_if assms RR_implies_R2c closure)
  show ?thesis
    using 1 2 by (rule_tac RR_intro, simp_all add: unrest assms)
qed

lemma seq_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P ;; Q is RR"
  unfolding Healthy_def
  by (simp add: RR_def  Healthy_if assms closure RR_implies_R2 ex_unrest unrest)
    
lemma power_Suc_RR_closed [closure]:
  "P is RR \<Longrightarrow> P ;; P \<^bold>^ i is RR"
  by (induct i, simp_all add: closure upred_semiring.power_Suc)
    
lemma seqr_iter_RR_closed [closure]:
  "\<lbrakk> I \<noteq> []; \<And> i. i \<in> set(I) \<Longrightarrow> P(i) is RR \<rbrakk> \<Longrightarrow> (;; i : I \<bullet> P(i)) is RR"
  apply (induct I, simp_all)
  apply (rename_tac i I)
  apply (case_tac I)
  apply (simp_all add: seq_RR_closed)
done
    
lemma cond_tt_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> Q is RR"
  apply (rule RR_intro)
  apply (simp_all add: unrest assms)
  apply (simp_all add: Healthy_def) 
  apply (simp_all add: R1_cond R2c_condr Healthy_if assms RR_implies_R2c closure R2c_tr'_minus_tr)
done

lemma rea_skip_RR [closure]:
  "II\<^sub>r is RR"
  apply (rel_auto) using minus_zero_eq by blast

lemma tr'_eq_tr_RR_closed [closure]: "$tr\<acute> =\<^sub>u $tr is RR"
  apply (rel_auto) using minus_zero_eq by auto

lemma inf_RR_closed [closure]: 
  "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> P \<sqinter> Q is RR"
  by (simp add: disj_RR uinf_or)

lemma conj_tr_strict_RR_closed [closure]: 
  assumes "P is RR"
  shows "(P \<and> $tr <\<^sub>u $tr\<acute>) is RR"
proof -
  have "RR(RR(P) \<and> $tr <\<^sub>u $tr\<acute>) = (RR(P) \<and> $tr <\<^sub>u $tr\<acute>)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma rea_assert_RR_closed [closure]:
  assumes "b is RR"
  shows "{b}\<^sub>r is RR"
  by (simp add: closure assms rea_assert_def)
  
lemma upower_RR_closed [closure]:
  "\<lbrakk> i > 0; P is RR \<rbrakk> \<Longrightarrow> P \<^bold>^ i is RR"
  apply (induct i, simp_all)
  apply (rename_tac i)
  apply (case_tac "i = 0")
   apply (simp_all add: closure upred_semiring.power_Suc)
  done

lemma seq_power_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "(P \<^bold>^ i) ;; Q is RR"
  by (metis assms neq0_conv seq_RR_closed seqr_left_unit upower_RR_closed upred_semiring.power_0)

lemma ustar_right_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "P ;; Q\<^sup>\<star> is RR"
proof -
  have "P ;; Q\<^sup>\<star> = P ;; (\<Sqinter> i \<in> {0..} \<bullet> Q \<^bold>^ i)"
    by (simp add: ustar_def)
  also have "... = P ;; (II \<sqinter> (\<Sqinter> i \<in> {1..} \<bullet> Q \<^bold>^ i))"
    by (metis One_nat_def UINF_atLeast_first upred_semiring.power_0)
  also have "... = (P \<or> P ;; (\<Sqinter> i \<in> {1..} \<bullet> Q \<^bold>^ i))"
    by (simp add: disj_upred_def[THEN sym] seqr_or_distr)
  also have "... is RR"
  proof -
    have "(\<Sqinter> i \<in> {1..} \<bullet> Q \<^bold>^ i) is RR"
      by (rule UINF_mem_Continuous_closed, simp_all add: assms closure)
    thus ?thesis
      by (simp add: assms closure)
  qed
  finally show ?thesis .
qed

lemma ustar_left_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "P\<^sup>\<star> ;; Q is RR"
proof -
  have "P\<^sup>\<star> ;; Q = (\<Sqinter> i \<in> {0..} \<bullet> P \<^bold>^ i) ;; Q"
    by (simp add: ustar_def)
  also have "... = (II \<sqinter> (\<Sqinter> i \<in> {1..} \<bullet> P \<^bold>^ i)) ;; Q"
    by (metis One_nat_def UINF_atLeast_first upred_semiring.power_0)
  also have "... = (Q \<or> (\<Sqinter> i \<in> {1..} \<bullet> P \<^bold>^ i) ;; Q)"
    by (simp add: disj_upred_def[THEN sym] seqr_or_distl)
  also have "... is RR"
  proof -
    have "(\<Sqinter> i \<in> {1..} \<bullet> P \<^bold>^ i) is RR"
      by (rule UINF_mem_Continuous_closed, simp_all add: assms closure)
    thus ?thesis
      by (simp add: assms closure)
  qed
  finally show ?thesis .
qed

lemma uplus_RR_closed [closure]: "P is RR \<Longrightarrow> P\<^sup>+ is RR"
  by (simp add: uplus_def ustar_right_RR_closed)

lemma trace_ext_prefix_RR [closure]: 
  "\<lbrakk> $tr \<sharp> e; $ok \<sharp> e; $wait \<sharp> e; out\<alpha> \<sharp> e \<rbrakk> \<Longrightarrow> $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute> is RR"
  apply (rel_auto)
  apply (metis (no_types, lifting) Prefix_Order.same_prefix_prefix less_eq_list_def prefix_concat_minus zero_list_def)
  apply (metis append_minus list_append_prefixD minus_cancel_le order_refl)
done  

lemma rea_subst_R1_closed [closure]: "P\<lbrakk>v\<rbrakk>\<^sub>r is R1"
  by (rel_auto)

lemma R5_comp [rpred]:
  assumes "P is RR" "Q is RR"
  shows "R5(P ;; Q) = R5(P) ;; R5(Q)"
proof -
  have "R5(RR(P) ;; RR(Q)) = R5(RR(P)) ;; R5(RR(Q))"
    by (rel_auto; force)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma R4_comp [rpred]:
  assumes "P is R4" "Q is RR"
  shows "R4(P ;; Q) = P ;; Q"
proof -
  have "R4(R4(P) ;; RR(Q)) = R4(P) ;; RR(Q)"
    by (rel_auto, blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_rename_RR_closed [closure]: 
  assumes "P is RR"
  shows "P\<lparr>f\<rparr>\<^sub>r is RR"
proof -
  have "(RR P)\<lparr>f\<rparr>\<^sub>r is RR"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

subsection \<open> Reactive relational calculus \<close>

lemma rea_skip_unit [rpred]:
  assumes "P is RR"
  shows "P ;; II\<^sub>r = P" "II\<^sub>r ;; P = P"
proof -
  have 1: "RR(P) ;; II\<^sub>r = RR(P)"
    by (rel_auto)
  have 2: "II\<^sub>r ;; RR(P) = RR(P)"
    by (rel_auto)
  from 1 2 show "P ;; II\<^sub>r = P" "II\<^sub>r ;; P = P"
    by (simp_all add: Healthy_if assms)
qed
  
lemma rea_true_conj [rpred]: 
  assumes "P is R1"
  shows "(true\<^sub>r \<and> P) = P" "(P \<and> true\<^sub>r) = P"
  using assms
  by (simp_all add: Healthy_def R1_def utp_pred_laws.inf_commute) 

lemma rea_true_disj [rpred]: 
  assumes "P is R1"
  shows "(true\<^sub>r \<or> P) = true\<^sub>r" "(P \<or> true\<^sub>r) = true\<^sub>r"
  using assms by (metis Healthy_def R1_disj disj_comm true_disj_zero)+
  
lemma rea_not_not [rpred]: "P is R1 \<Longrightarrow> (\<not>\<^sub>r \<not>\<^sub>r P) = P"
  by (simp add: rea_not_def R1_negate_R1 Healthy_if)
    
lemma rea_not_rea_true [simp]: "(\<not>\<^sub>r true\<^sub>r) = false"
  by (simp add: rea_not_def R1_negate_R1 R1_false)
    
lemma rea_not_false [simp]: "(\<not>\<^sub>r false) = true\<^sub>r"
  by (simp add: rea_not_def)
    
lemma rea_true_impl [rpred]:
  "P is R1 \<Longrightarrow> (true\<^sub>r \<Rightarrow>\<^sub>r P) = P"
  by (simp add: rea_not_def rea_impl_def R1_negate_R1 R1_false Healthy_if)

lemma rea_true_impl' [rpred]:
  "P is R1 \<Longrightarrow>(true \<Rightarrow>\<^sub>r P) = P"
  by (simp add: rea_not_def rea_impl_def R1_negate_R1 R1_false Healthy_if)
    
lemma rea_false_impl [rpred]:
  "P is R1 \<Longrightarrow> (false \<Rightarrow>\<^sub>r P) = true\<^sub>r"
  by (simp add: rea_impl_def rpred Healthy_if)
   
lemma rea_impl_true [simp]: "(P \<Rightarrow>\<^sub>r true\<^sub>r) = true\<^sub>r"
  by (rel_auto)
    
lemma rea_impl_false [simp]: "(P \<Rightarrow>\<^sub>r false) = (\<not>\<^sub>r P)"
  by (rel_simp)

lemma rea_imp_refl [rpred]: "P is R1 \<Longrightarrow> (P \<Rightarrow>\<^sub>r P) = true\<^sub>r"
  by (rel_blast)

lemma rea_impl_conj [rpred]: 
  "(P \<Rightarrow>\<^sub>r Q \<Rightarrow>\<^sub>r R) = ((P \<and> Q) \<Rightarrow>\<^sub>r R)"
  by (rel_auto)

lemma rea_impl_mp [rpred]:
  "(P \<and> (P \<Rightarrow>\<^sub>r Q)) = (P \<and> Q)"
  by (rel_auto)

lemma rea_impl_conj_combine [rpred]: 
  "((P \<Rightarrow>\<^sub>r Q) \<and> (P \<Rightarrow>\<^sub>r R)) = (P \<Rightarrow>\<^sub>r Q \<and> R)"
  by (rel_auto)

lemma rea_impl_alt_def:
  assumes "Q is R1"
  shows "(P \<Rightarrow>\<^sub>r Q) = R1(P \<Rightarrow> Q)"
proof -
  have "(P \<Rightarrow>\<^sub>r R1(Q)) = R1(P \<Rightarrow> Q)"
    by (rel_auto)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma rea_impl_disj:
  "(P \<Rightarrow>\<^sub>r Q \<or> R) = (Q \<or> (P \<Rightarrow>\<^sub>r R))"
  by (rel_auto)

lemma rea_not_true [simp]: "(\<not>\<^sub>r true) = false"
  by (rel_auto)
    
lemma rea_not_demorgan1 [simp]:
  "(\<not>\<^sub>r (P \<and> Q)) = (\<not>\<^sub>r P \<or> \<not>\<^sub>r Q)"
  by (rel_auto)

lemma rea_not_demorgan2 [simp]:
  "(\<not>\<^sub>r (P \<or> Q)) = (\<not>\<^sub>r P \<and> \<not>\<^sub>r Q)"
  by (rel_auto)

lemma rea_not_or [rpred]:
  "P is R1 \<Longrightarrow> (P \<or> \<not>\<^sub>r P) = true\<^sub>r"
  by (rel_blast)

lemma rea_not_and [simp]:
  "(P \<and> \<not>\<^sub>r P) = false"
  by (rel_auto)

lemma truer_bottom_rpred [rpred]: "P is RR \<Longrightarrow> R1(true) \<sqsubseteq> P"
  by (metis Healthy_def R1_RR R1_mono utp_pred_laws.top_greatest)

lemma ext_close_weakening: "P ;; true\<^sub>r \<sqsubseteq> P"
  by (rel_auto)

lemma rea_not_INFIMUM [simp]:
  "(\<not>\<^sub>r (\<Squnion>i\<in>A. Q(i))) = (\<Sqinter>i\<in>A. \<not>\<^sub>r Q(i))"
  by (rel_auto)

lemma rea_not_USUP [simp]:
  "(\<not>\<^sub>r (\<Squnion>i\<in>A \<bullet> Q(i))) = (\<Sqinter>i\<in>A \<bullet> \<not>\<^sub>r Q(i))"
  by (rel_auto)
    
lemma rea_not_SUPREMUM [simp]:
  "A \<noteq> {} \<Longrightarrow> (\<not>\<^sub>r (\<Sqinter>i\<in>A. Q(i))) = (\<Squnion>i\<in>A. \<not>\<^sub>r Q(i))"
  by (rel_auto)

lemma rea_not_UINF [simp]:
  "A \<noteq> {} \<Longrightarrow> (\<not>\<^sub>r (\<Sqinter>i\<in>A \<bullet> Q(i))) = (\<Squnion>i\<in>A \<bullet> \<not>\<^sub>r Q(i))"
  by (rel_auto)

lemma USUP_mem_rea_true [simp]: "A \<noteq> {} \<Longrightarrow> (\<Squnion> i \<in> A \<bullet> true\<^sub>r) = true\<^sub>r"
  by (rel_auto)

lemma USUP_ind_rea_true [simp]: "(\<Squnion> i \<bullet> true\<^sub>r) = true\<^sub>r"
  by (rel_auto)
    
lemma UINF_ind_rea_true [rpred]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter> i\<in>A \<bullet> true\<^sub>r) = true\<^sub>r"
  by (rel_auto)

lemma UINF_rea_impl: "(\<Sqinter> P\<in>A \<bullet> F(P) \<Rightarrow>\<^sub>r G(P)) = ((\<Squnion> P\<in>A \<bullet> F(P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> G(P)))"
  by (rel_auto)  

lemma rea_not_shEx [rpred]: "(\<not>\<^sub>r shEx P) = (shAll (\<lambda> x. \<not>\<^sub>r P x))"
  by (rel_auto)

lemma rea_assert_true:
  "{true\<^sub>r}\<^sub>r = II\<^sub>r"
  by (rel_auto)

lemma rea_false_true:
  "{false}\<^sub>r = true\<^sub>r"
  by (rel_auto)

lemma rea_rename_id [rpred]: 
  assumes "P is RR"
  shows "P\<lparr>id\<rparr>\<^sub>r = P"
proof -
  have "(RR P)\<lparr>id\<rparr>\<^sub>r = RR P"
    by (rel_auto)
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma rea_rename_comp [rpred]: 
  assumes "renamer f" "renamer g" "P is RR"
  shows "P\<lparr>g \<circ> f\<rparr>\<^sub>r = P\<lparr>g\<rparr>\<^sub>r\<lparr>f\<rparr>\<^sub>r"
  oops

lemma rea_rename_false [rpred]: "false\<lparr>f\<rparr>\<^sub>r = false"
  by (rel_auto)

lemma rea_rename_disj [rpred]: 
  "(P \<or> Q)\<lparr>f\<rparr>\<^sub>r = (P\<lparr>f\<rparr>\<^sub>r \<or> Q\<lparr>f\<rparr>\<^sub>r)"
  by (rel_blast)

lemma rea_rename_UINF_ind [rpred]:
  "(\<Sqinter> i \<bullet> P i)\<lparr>f\<rparr>\<^sub>r = (\<Sqinter> i \<bullet> (P i)\<lparr>f\<rparr>\<^sub>r)"
  by (rel_blast)

lemma rea_rename_UINF_mem [rpred]:
  "(\<Sqinter> i\<in>A \<bullet> P i)\<lparr>f\<rparr>\<^sub>r = (\<Sqinter> i\<in>A \<bullet> (P i)\<lparr>f\<rparr>\<^sub>r)"
  by (rel_blast)

lemma rea_rename_conj [rpred]: 
  assumes "renamer f" "P is RR" "Q is RR"
  shows "(P \<and> Q)\<lparr>f\<rparr>\<^sub>r = (P\<lparr>f\<rparr>\<^sub>r \<and> Q\<lparr>f\<rparr>\<^sub>r)"
proof -
  interpret ren: renamer f by (simp add: assms)
  have "(RR P \<and> RR Q)\<lparr>f\<rparr>\<^sub>r = ((RR P)\<lparr>f\<rparr>\<^sub>r \<and> (RR Q)\<lparr>f\<rparr>\<^sub>r)"
    using injD[OF ren.injective]
    by (rel_auto; blast)
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma rea_rename_USUP_ind [rpred]:
  assumes "renamer f" "\<And> i. P i is RR"
  shows "(\<Squnion> i \<bullet> P i)\<lparr>f\<rparr>\<^sub>r = (\<Squnion> i \<bullet> (P i)\<lparr>f\<rparr>\<^sub>r)"
proof -
  interpret ren: renamer f by (simp add: assms)
  have "(\<Squnion> i \<bullet> RR(P i))\<lparr>f\<rparr>\<^sub>r = (\<Squnion> i \<bullet> (RR (P i))\<lparr>f\<rparr>\<^sub>r)"
    using injD[OF ren.injective]
    by (rel_auto, blast, metis (mono_tags, hide_lams))
  thus ?thesis
    by (simp add: Healthy_if assms cong: USUP_all_cong)
qed

lemma rea_rename_USUP_mem [rpred]:
  assumes "renamer f" "A \<noteq> {}" "\<And> i. i \<in> A \<Longrightarrow> P i is RR"
  shows "(\<Squnion> i\<in>A \<bullet> P i)\<lparr>f\<rparr>\<^sub>r = (\<Squnion> i\<in>A \<bullet> (P i)\<lparr>f\<rparr>\<^sub>r)"
proof -
  interpret ren: renamer f by (simp add: assms)
  have "(\<Squnion> i\<in>A \<bullet> RR(P i))\<lparr>f\<rparr>\<^sub>r = (\<Squnion> i\<in>A \<bullet> (RR (P i))\<lparr>f\<rparr>\<^sub>r)"
    using injD[OF ren.injective] assms(2)
    by (rel_auto, blast, metis (no_types, hide_lams))
  thus ?thesis
    by (simp add: Healthy_if assms cong: USUP_cong)
qed

lemma rea_rename_skip_rea [rpred]: "renamer f \<Longrightarrow> II\<^sub>r\<lparr>f\<rparr>\<^sub>r = II\<^sub>r"
  using minus_zero_eq by (rel_auto)

lemma rea_rename_seq [rpred]: 
  assumes "renamer f" "P is RR" "Q is RR"
  shows "(P ;; Q)\<lparr>f\<rparr>\<^sub>r = P\<lparr>f\<rparr>\<^sub>r ;; Q\<lparr>f\<rparr>\<^sub>r"
proof -
  interpret ren: renamer f by (simp add: assms)
  from assms(1) have "(RR(P) ;; RR(Q))\<lparr>f\<rparr>\<^sub>r = (RR P)\<lparr>f\<rparr>\<^sub>r ;; (RR Q)\<lparr>f\<rparr>\<^sub>r"
    by (rel_auto)
       (metis (no_types, lifting) diff_add_cancel_left' le_add minus_assoc mono_def ren.minus ren.monotonic trace_class.add_diff_cancel_left trace_class.add_left_mono)+
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

declare R4_idem [rpred]
declare R4_false [rpred]
declare R4_conj [rpred]
declare R4_disj [rpred]

declare R4_R5 [rpred]
declare R5_R4 [rpred]

declare R5_conj [rpred]
declare R5_disj [rpred]

lemma R4_USUP [rpred]: "I \<noteq> {} \<Longrightarrow> R4(\<Squnion> i\<in>I \<bullet> P(i)) = (\<Squnion> i\<in>I \<bullet> R4(P(i)))"
  by (rel_auto)

lemma R5_USUP [rpred]: "I \<noteq> {} \<Longrightarrow> R5(\<Squnion> i\<in>I \<bullet> P(i)) = (\<Squnion> i\<in>I \<bullet> R5(P(i)))"
  by (rel_auto)

lemma R4_UINF [rpred]: "R4(\<Sqinter> i\<in>I \<bullet> P(i)) = (\<Sqinter> i\<in>I \<bullet> R4(P(i)))"
  by (rel_auto)

lemma R5_UINF [rpred]: "R5(\<Sqinter> i\<in>I \<bullet> P(i)) = (\<Sqinter> i\<in>I \<bullet> R5(P(i)))"
  by (rel_auto)

subsection \<open> UTP theory \<close>

text \<open> We create a UTP theory of reactive relations which in particular provides Kleene star theorems \<close>

interpretation rrel_theory: utp_theory_kleene RR II\<^sub>r
  rewrites "P \<in> carrier rrel_theory.thy_order \<longleftrightarrow> P is RR"
  and "le rrel_theory.thy_order = (\<sqsubseteq>)"
  and "eq rrel_theory.thy_order = (=)"  
  and rrel_top: "rrel_theory.utp_top = false"
  and rrel_bottom: "rrel_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous RR
    by (unfold_locales, simp_all add: add: RR_idem RR_Continuous)
  show top:"utp_top = false"
    by (simp add: healthy_top, rel_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, rel_auto)
  show "utp_theory_kleene RR II\<^sub>r"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)

abbreviation rea_star :: "_ \<Rightarrow> _"  ("_\<^sup>\<star>\<^sup>r" [999] 999) where
"P\<^sup>\<star>\<^sup>r \<equiv> rrel_theory.utp_star P"

text \<open> The supernova tactic explodes conjectures using the Kleene star laws and relational calculus \<close>

method supernova = ((safe intro!: rrel_theory.Star_inductr rrel_theory.Star_inductl, simp_all add: closure) ; rel_auto)[1]

subsection \<open> Instantaneous Reactive Relations \<close>

text \<open> Instantaneous Reactive Relations, where the trace stays the same. \<close>
  
abbreviation Instant :: "('t::trace, '\<alpha>) hrel_rp \<Rightarrow> ('t, '\<alpha>) hrel_rp" where
"Instant(P) \<equiv> RID(tr)(P)"

lemma skip_rea_Instant [closure]: "II\<^sub>r is Instant"
  by (rel_auto)

end