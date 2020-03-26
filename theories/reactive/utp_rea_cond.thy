section \<open> Reactive Conditions \<close>

theory utp_rea_cond
  imports utp_rea_rel
begin

subsection \<open> Healthiness Conditions \<close>
    
definition RC1 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "RC1(P) = (\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r)"
  
definition RC :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "RC = RC1 \<circ> RR"
  
lemma RC_intro: "\<lbrakk> P is RR; ((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) = P) \<rbrakk> \<Longrightarrow> P is RC"
  by (simp add: Healthy_def RC1_def RC_def)

lemma RC_intro': "\<lbrakk> P is RR; P is RC1 \<rbrakk> \<Longrightarrow> P is RC"
  by (simp add: Healthy_def RC1_def RC_def)
lemma RC1_idem: "RC1(RC1(P)) = RC1(P)"
  by (rel_auto, (blast intro: dual_order.trans)+)
  
lemma RC1_mono: "P \<sqsubseteq> Q \<Longrightarrow> RC1(P) \<sqsubseteq> RC1(Q)"
  by (rel_blast)
      
lemma RC1_prop: 
  assumes "P is RC1"
  shows "(\<not>\<^sub>r P) ;; R1 true = (\<not>\<^sub>r P)"
proof -
  have "(\<not>\<^sub>r P) = (\<not>\<^sub>r (RC1 P))"
    by (simp add: Healthy_if assms)
  also have "... = (\<not>\<^sub>r P) ;; R1 true"
    by (simp add: RC1_def rpred closure)
  finally show ?thesis ..
qed
    
lemma R2_RC: "R2 (RC P) = RC P"
proof -
  have "\<not>\<^sub>r RR P is RR"
    by (metis (no_types) Healthy_Idempotent RR_Idempotent RR_rea_not)
  then show ?thesis
    by (metis (no_types) Healthy_def' R1_R2c_seqr_distribute R2_R2c_def RC1_def RC_def RR_implies_R1 RR_implies_R2c comp_apply rea_not_R2_closed rea_true_R1 rea_true_R2c)
qed

lemma RC_R2_def: "RC = RC1 \<circ> RR"
  by (auto simp add: RC_def fun_eq_iff R1_R2c_commute[THEN sym] R1_R2c_is_R2)
    
lemma RC_implies_R2: "P is RC \<Longrightarrow> P is R2"
  by (metis Healthy_def' R2_RC)
    
lemma RC_ex_ok_wait: "(\<exists> {$ok, $ok\<acute>, $wait, $wait\<acute>} \<bullet> RC P) = RC P"
  by (rel_auto)

text \<open> An important property of reactive conditions is they are monotonic with respect to the trace.
  That is, $P$ with a shorter trace is refined by $P$ with a longer trace. \<close>

lemma RC_prefix_refine:
  assumes "P is RC" "s \<le> t"
  shows "P\<lbrakk>0,\<guillemotleft>s\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> P\<lbrakk>0,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>"
proof -
  from assms(2) have "(RC P)\<lbrakk>0,\<guillemotleft>s\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> (RC P)\<lbrakk>0,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>"
    apply (rel_auto)
    using dual_order.trans apply blast
    done
  thus ?thesis
    by (simp only: assms(1) Healthy_if)
qed

text \<open> The @{term RC} healthy relations can also be defined in terms of prefix closure,
  which is characterised by the healthiness condition below. \<close>

definition RC2 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "RC2(P) = R1(P ;; ($tr\<acute> \<le>\<^sub>u $tr))"

lemma RC2_RR_commute: 
  "RC2(RR(P)) = RR(RC2(P))"
  apply (rel_auto)
  using minus_cancel_le apply blast
  apply (metis diff_add_cancel_left' le_add trace_class.add_diff_cancel_left trace_class.add_left_mono)
  done

text \<open> Intuitive meaning of @{term RC2} \<close>

lemma RC2_form_1:
  assumes "P is RR"
  shows "RC2(P) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (\<exists> $\<Sigma>\<^sub>R\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> \<le>\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<and> $tr \<le>\<^sub>u $tr\<acute>)"
proof -
  have "RC2(RR(P)) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (\<exists> $\<Sigma>\<^sub>R\<acute> \<bullet> RR P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> \<le>\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<and> $tr \<le>\<^sub>u $tr\<acute>)"
    by (rel_blast)
  thus ?thesis
    by (metis (mono_tags, lifting) Healthy_if assms shEx_cong)
qed

lemma RC2_form_2:
  assumes "P is RR"  
    shows "RC2(P) = (\<^bold>\<exists> (t\<^sub>0, t\<^sub>1) \<bullet> (\<exists> $\<Sigma>\<^sub>R\<acute> \<bullet> P)\<lbrakk>0,\<guillemotleft>t\<^sub>1\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>t\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>t\<^sub>0\<guillemotright>)"
proof -
  have "RC2(RR(P)) = (\<^bold>\<exists> (t\<^sub>0, t\<^sub>1) \<bullet> (\<exists> $\<Sigma>\<^sub>R\<acute> \<bullet> RR(P))\<lbrakk>0,\<guillemotleft>t\<^sub>1\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>t\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>t\<^sub>0\<guillemotright>)"
    apply (rel_auto)
    apply (metis diff_add_cancel_left' trace_class.add_le_imp_le_left)
    apply (metis le_add trace_class.add_diff_cancel_left trace_class.add_left_mono)
    done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

text \<open> Every reactive condition is prefix closed \<close>

lemma RC_prefix_closed:
  assumes "P is RC"
  shows "P is RC2"
proof -
  have "RC2(RC(P)) = RC(P)"
    apply (rel_auto) using dual_order.trans by blast
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma RC2_RR_is_RC1:
  assumes "P is RR" "P is RC2"
  shows "P is RC1"
proof -
  have "RC1(RC2(RR(P))) = RC2(RR(P))"
    apply (rel_auto) using dual_order.trans by blast
  thus ?thesis
    by (metis Healthy_def assms(1) assms(2))
qed

text \<open> @{term RC} closure can be demonstrated in terms of prefix closure. \<close>

lemma RC_intro_prefix_closed:
  assumes "P is RR" "P is RC2"
  shows "P is RC"
  by (simp add: RC2_RR_is_RC1 RC_intro' assms)

subsection \<open> Closure laws \<close>

lemma RC_implies_RR [closure]: 
  assumes "P is RC"
  shows "P is RR"
  by (metis Healthy_def RC_ex_ok_wait RC_implies_R2 RR_def assms)

lemma RC_implies_RC1: "P is RC \<Longrightarrow> P is RC1"
  by (metis Healthy_def RC_R2_def RC_implies_RR comp_eq_dest_lhs)

lemma RC1_trace_ext_prefix:
  "out\<alpha> \<sharp> e \<Longrightarrow> RC1(\<not>\<^sub>r $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>) = (\<not>\<^sub>r $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto, blast, metis (no_types, lifting) dual_order.trans)
    
lemma RC1_conj [rpred]: "RC1(P \<and> Q) = (RC1(P) \<and> RC1(Q))"
  by (rel_blast)
    
lemma conj_RC1_closed [closure]:
  "\<lbrakk> P is RC1; Q is RC1 \<rbrakk> \<Longrightarrow> P \<and> Q is RC1"
  by (simp add: Healthy_def RC1_conj)
    
lemma disj_RC1_closed [closure]:
  assumes "P is RC1" "Q is RC1"
  shows "(P \<or> Q) is RC1"
proof -
  have 1:"RC1(RC1(P) \<or> RC1(Q)) = (RC1(P) \<or> RC1(Q))"
    apply (rel_auto) using dual_order.trans by blast+
  show ?thesis
    by (metis (no_types) Healthy_def 1 assms)
qed

lemma conj_RC_closed [closure]:
  assumes "P is RC" "Q is RC"
  shows "(P \<and> Q) is RC"
  by (metis Healthy_def RC_R2_def RC_implies_RR assms comp_apply conj_RC1_closed conj_RR)
    
lemma rea_true_RC [closure]: "true\<^sub>r is RC"
  by (rel_auto)
    
lemma false_RC [closure]: "false is RC"
  by (rel_auto)
   
lemma disj_RC_closed [closure]: "\<lbrakk> P is RC; Q is RC \<rbrakk> \<Longrightarrow> (P \<or> Q) is RC"
  by (metis Healthy_def RC_R2_def RC_implies_RR comp_apply disj_RC1_closed disj_RR)
  
lemma UINF_mem_RC1_closed [closure]:
  assumes "\<And> i. P i is RC1"
  shows "(\<Sqinter> i\<in>A \<bullet> P i) is RC1"
proof -
  have 1:"RC1(\<Sqinter> i\<in>A \<bullet> RC1(P i)) = (\<Sqinter> i\<in>A \<bullet> RC1(P i))"
    by (rel_auto, meson order.trans)
  show ?thesis
    by (metis (mono_tags, lifting) "1" Healthy_def UINF_cong assms)
qed
  
lemma UINF_mem_RC_closed [closure]:
  assumes "\<And> i. P i is RC"
  shows "(\<Sqinter> i\<in>A \<bullet> P i) is RC"
proof -
  have "RC(\<Sqinter> i\<in>A \<bullet> P i) = (RC1 \<circ> RR)(\<Sqinter> i\<in>A \<bullet> P i)"
    by (simp add: RC_def)
  also have "... = RC1(\<Sqinter> i\<in>A \<bullet> RR(P i))"
    by (rel_blast)
  also have "... = RC1(\<Sqinter> i\<in>A \<bullet> RC1(P i))"
    by (simp add: Healthy_if RC_implies_RR RC_implies_RC1 assms)
  also have "... = (\<Sqinter> i\<in>A \<bullet> RC1(P i))"
    by (rel_auto, meson order.trans)
  also have "... = (\<Sqinter> i\<in>A \<bullet> P i)"
    by (simp add: Healthy_if RC_implies_RC1 assms)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma UINF_ind_RC_closed [closure]:
  assumes "\<And> i. P i is RC"
  shows "(\<Sqinter> i \<bullet> P i) is RC"
  by (metis (no_types) UINF_as_Sup_collect' UINF_as_Sup_image UINF_mem_RC_closed assms)

lemma USUP_mem_RC1_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is RC1" "A \<noteq> {}"
  shows "(\<Squnion> i\<in>A \<bullet> P i) is RC1"
proof -
  have "RC1(\<Squnion> i\<in>A \<bullet> P i) = RC1(\<Squnion> i\<in>A \<bullet> RC1(P i))"
    by (simp add: Healthy_if assms(1) cong: USUP_cong)
  also from assms(2) have "... = (\<Squnion> i\<in>A \<bullet> RC1(P i))"
    using dual_order.trans by (rel_blast)
  also have "... = (\<Squnion> i\<in>A \<bullet> P i)"
    by (simp add: Healthy_if assms(1) cong: USUP_cong)
  finally show ?thesis
    using Healthy_def by blast
qed

lemma USUP_mem_RC_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is RC" "A \<noteq> {}"
  shows "(\<Squnion> i\<in>A \<bullet> P i) is RC"
  by (rule RC_intro', simp_all add: closure assms RC_implies_RC1)

lemma USUP_ind_RC_closed [closure]:
  "\<lbrakk> \<And> i. P i is RC \<rbrakk> \<Longrightarrow> (\<Squnion> i \<bullet> P i) is RC"
  by (metis UNIV_not_empty USUP_mem_RC_closed)

lemma neg_trace_ext_prefix_RC [closure]: 
  "\<lbrakk> $tr \<sharp> e; $ok \<sharp> e; $wait \<sharp> e; out\<alpha> \<sharp> e \<rbrakk> \<Longrightarrow> \<not>\<^sub>r $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute> is RC"
  by (rule RC_intro, simp add: closure, metis RC1_def RC1_trace_ext_prefix)

lemma RC1_unrest:
  "\<lbrakk> mwb_lens x; x \<bowtie> tr \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> RC1(P)"
  by (simp add: RC1_def unrest)
    
lemma RC_unrest_dashed [unrest]:
  "\<lbrakk> P is RC; mwb_lens x; x \<bowtie> tr \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (metis Healthy_if RC1_unrest RC_implies_RC1)

lemma RC1_RR_closed [closure]: "P is RR \<Longrightarrow> RC1(P) is RR"
  by (simp add: RC1_def closure)

end