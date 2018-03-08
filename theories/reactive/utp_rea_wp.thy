section \<open> Reactive Weakest Preconditions \<close>

theory utp_rea_wp
  imports utp_rea_prog
begin

definition wp_rea ::
  "('t::trace, '\<alpha>) hrel_rp \<Rightarrow>  
   ('t, '\<alpha>) hrel_rp \<Rightarrow> 
   ('t, '\<alpha>) hrel_rp" (infix "wp\<^sub>r" 60)
where [upred_defs]: "P wp\<^sub>r Q = (\<not>\<^sub>r P ;; (\<not>\<^sub>r Q))"

lemma in_var_unrest_wp_rea [unrest]: "\<lbrakk> $x \<sharp> P; tr \<bowtie> x \<rbrakk> \<Longrightarrow> $x \<sharp> (P wp\<^sub>r Q)"
  by (simp add: wp_rea_def unrest R1_def rea_not_def)

lemma out_var_unrest_wp_rea [unrest]: "\<lbrakk> $x\<acute> \<sharp> Q; tr \<bowtie> x \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> (P wp\<^sub>r Q)"
  by (simp add: wp_rea_def unrest R1_def rea_not_def)
  
lemma wp_rea_R1 [closure]: "P wp\<^sub>r Q is R1"
  by (rel_auto)

lemma wp_rea_RR_closed [closure]: "\<lbrakk> P is RR; Q is RR \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is RR"
  by (simp add: wp_rea_def closure)    

lemma wp_rea_impl_lemma:
  "((P wp\<^sub>r Q) \<Rightarrow>\<^sub>r (R1(P) ;; R1(Q \<Rightarrow>\<^sub>r R))) = ((P wp\<^sub>r Q) \<Rightarrow>\<^sub>r (R1(P) ;; R1(R)))"
  by (rel_auto, blast)

lemma wpR_R1_right [wp]:
  "P wp\<^sub>r R1(Q) = P wp\<^sub>r Q"
  by (rel_auto)

lemma wp_rea_true [wp]: "P wp\<^sub>r true = true\<^sub>r"
  by (rel_auto)
    
lemma wp_rea_conj [wp]: "P wp\<^sub>r (Q \<and> R) = (P wp\<^sub>r Q \<and> P wp\<^sub>r R)"
  by (simp add: wp_rea_def seqr_or_distr)
    
lemma wp_rea_USUP_mem [wp]: 
  "A \<noteq> {} \<Longrightarrow> P wp\<^sub>r (\<Squnion> i\<in>A \<bullet> Q(i)) = (\<Squnion> i\<in>A \<bullet> P wp\<^sub>r Q(i))"
  by (simp add: wp_rea_def seq_UINF_distl)

lemma wp_rea_Inf_pre [wp]: 
  "P wp\<^sub>r (\<Squnion>i\<in>{0..n::nat}. Q(i)) = (\<Squnion>i\<in>{0..n}. P wp\<^sub>r Q(i))"
  by (simp add: wp_rea_def seq_SUP_distl)

lemma wp_rea_div [wp]:
  "(\<not>\<^sub>r P ;; true\<^sub>r) = true\<^sub>r \<Longrightarrow> true\<^sub>r wp\<^sub>r P = false"
  by (simp add: wp_rea_def rpred, rel_blast)

lemma wp_rea_st_cond_div [wp]:
  "P \<noteq> true \<Longrightarrow> true\<^sub>r wp\<^sub>r [P]\<^sub>S\<^sub>< = false"
  by (rel_auto)

lemma wp_rea_cond [wp]:
  "out\<alpha> \<sharp> b \<Longrightarrow> (P \<triangleleft> b \<triangleright> Q) wp\<^sub>r R = P wp\<^sub>r R \<triangleleft> b \<triangleright> Q wp\<^sub>r R"
  by (simp add: wp_rea_def cond_seq_left_distr, rel_auto)
    
lemma wp_rea_RC_false [wp]: 
  "P is RC \<Longrightarrow> (\<not>\<^sub>r P) wp\<^sub>r false = P"
  by (metis Healthy_if RC1_def RC_implies_RC1 rea_not_false wp_rea_def)
    
lemma wp_rea_seq [wp]:
  assumes "Q is R1"
  shows "(P ;; Q) wp\<^sub>r R = P wp\<^sub>r (Q wp\<^sub>r R)" (is "?lhs = ?rhs")
proof -
  have "?rhs = R1 (\<not> P ;; R1 (Q ;; R1 (\<not> R)))"
    by (simp add: wp_rea_def rea_not_def R1_negate_R1 assms)
  also have "... = R1 (\<not> P ;; (Q ;; R1 (\<not> R)))"
    by (metis Healthy_if R1_seqr assms)
  also have "... = R1 (\<not> (P ;; Q) ;; R1 (\<not> R))"
    by (simp add: seqr_assoc)
  finally show ?thesis
    by (simp add: wp_rea_def rea_not_def)
qed
  
lemma wp_rea_skip [wp]:
  assumes "Q is R1"
  shows "II wp\<^sub>r Q = Q"
  by (simp add: wp_rea_def rpred assms Healthy_if)

lemma wp_rea_rea_skip [wp]:
  assumes "Q is RR"
  shows "II\<^sub>r wp\<^sub>r Q = Q"
  by (simp add: wp_rea_def rpred closure assms Healthy_if)
    
lemma power_wp_rea_RR_closed [closure]: 
  "\<lbrakk> R is RR; P is RR \<rbrakk> \<Longrightarrow> R \<^bold>^ i wp\<^sub>r P is RR"
  by (induct i, simp_all add: wp closure)

lemma wp_rea_rea_assigns [wp]:
  assumes "P is RR"
  shows "\<langle>\<sigma>\<rangle>\<^sub>r wp\<^sub>r P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"
proof -
  have "\<langle>\<sigma>\<rangle>\<^sub>r wp\<^sub>r (RR P) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> (RR P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed
  
lemma wp_rea_miracle [wp]: "false wp\<^sub>r Q = true\<^sub>r"
  by (simp add: wp_rea_def)

lemma wp_rea_disj [wp]: "(P \<or> Q) wp\<^sub>r R = (P wp\<^sub>r R \<and> Q wp\<^sub>r R)"
  by (rel_blast)

lemma wp_rea_UINF [wp]:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> x\<in>A \<bullet> P(x)) wp\<^sub>r Q = (\<Squnion> x\<in>A \<bullet> P(x) wp\<^sub>r Q)"
  by (simp add: wp_rea_def rea_not_def seq_UINF_distr not_UINF R1_UINF assms)

lemma wp_rea_choice [wp]:
  "(P \<sqinter> Q) wp\<^sub>r R = (P wp\<^sub>r R \<and> Q wp\<^sub>r R)"
  by (rel_blast)

lemma wp_rea_UINF_ind [wp]:
  "(\<Sqinter> i \<bullet> P(i)) wp\<^sub>r Q = (\<Squnion> i \<bullet> P(i) wp\<^sub>r Q)"
  by (simp add: wp_rea_def rea_not_def seq_UINF_distr' not_UINF_ind R1_UINF_ind)

lemma rea_assume_wp [wp]: 
  assumes "P is RC"  
  shows "([b]\<^sup>\<top>\<^sub>r wp\<^sub>r P) = ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P)"
proof -
  have "([b]\<^sup>\<top>\<^sub>r wp\<^sub>r RC P) = ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r RC P)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_star_wp [wp]: 
  assumes "P is RR" "Q is RR"  
  shows "P\<^sup>\<star>\<^sup>r wp\<^sub>r Q = (\<Squnion> i \<bullet> P \<^bold>^ i wp\<^sub>r Q)"
proof -
  have "P\<^sup>\<star>\<^sup>r wp\<^sub>r Q = (Q \<and> P\<^sup>+ wp\<^sub>r Q)"
    by (simp add: assms rrel_thy.Star_alt_def wp_rea_choice wp_rea_rea_skip)
  also have "... = (II wp\<^sub>r Q \<and> (\<Squnion> i \<bullet> P \<^bold>^ Suc i wp\<^sub>r Q))"
    by (simp add: uplus_power_def wp closure assms)
  also have "... = (\<Squnion> i \<bullet> P \<^bold>^ i wp\<^sub>r Q)"
  proof -
    have "P\<^sup>\<star> wp\<^sub>r Q = P\<^sup>\<star>\<^sup>r wp\<^sub>r Q"
      by (metis (no_types) RA1 assms(2) rea_no_RR rea_skip_unit(2) rrel_thy.Star_def wp_rea_def)
    then show ?thesis
      by (simp add: calculation ustar_def wp_rea_UINF_ind)
  qed
  finally show ?thesis .
qed

lemma wp_rea_R2_closed [closure]:
  "\<lbrakk> P is R2; Q is R2 \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is R2"
  by (simp add: wp_rea_def closure)

lemma wp_rea_false_RC1': "P is R2 \<Longrightarrow> RC1(P wp\<^sub>r false) = P wp\<^sub>r false"
  by (simp add: wp_rea_def RC1_def closure rpred seqr_assoc)
    
lemma wp_rea_false_RC1: "P is R2 \<Longrightarrow> P wp\<^sub>r false is RC1"
  by (simp add :Healthy_def wp_rea_false_RC1')
  
lemma wp_rea_false_RR:
  "\<lbrakk> $ok \<sharp> P; $wait \<sharp> P; P is R2 \<rbrakk> \<Longrightarrow> P wp\<^sub>r false is RR"
  by (rule RR_R2_intro, simp_all add: unrest closure)

lemma wp_rea_false_RC:
  "\<lbrakk> $ok \<sharp> P; $wait \<sharp> P; P is R2 \<rbrakk> \<Longrightarrow> P wp\<^sub>r false is RC"
  by (rule RC_intro', simp_all add:  wp_rea_false_RC1 wp_rea_false_RR)
 
lemma wp_rea_RC1: "\<lbrakk> P is RR; Q is RC \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is RC1"
  by (rule Healthy_intro, simp add: wp_rea_def RC1_def rpred closure seqr_assoc RC1_prop RC_implies_RC1)
    
lemma wp_rea_RC [closure]: "\<lbrakk> P is RR; Q is RC \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is RC"
  by (rule RC_intro', simp_all add: wp_rea_RC1 closure)

lemma wpR_power_RC_closed [closure]:
  assumes "P is RR" "Q is RC"
  shows "P \<^bold>^ i wp\<^sub>r Q is RC"
  by (metis RC_implies_RR RR_implies_R1 assms power.power_eq_if power_Suc_RR_closed wp_rea_RC wp_rea_skip)

end