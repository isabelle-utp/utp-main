section \<open> Weakest Precondition Calculus \<close>

theory utp_wp
  imports utp_wlp
begin

text \<open> This calculus is like the liberal version, but also accounts for termination. It is equivalent
  to the relational preimage.  \<close>

consts
  uwp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" 

utp_const uwp(0)

utp_lift_notation uwp (0)

syntax
  "_uwp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "wp" 60)

translations
  "_uwp P b" == "CONST uwp P b"

definition wp_upred :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> cond \<Rightarrow> '\<alpha> cond" where
[upred_defs]: "wp_upred P b = Pre(P ;; ?[b])"

adhoc_overloading
  uwp wp_upred

term "P wp true"

theorem refine_iff_wp: 
  fixes P Q :: "('\<alpha>, '\<beta>) urel"
  shows "P \<sqsubseteq> Q \<longleftrightarrow> (\<forall> b. `P wp b \<Rightarrow> Q wp b`)"
  apply (rel_auto)
  oops

theorem wp_refine_iff: "(\<forall> r. `Q wp r \<Rightarrow> P wp r`) \<longleftrightarrow> P \<sqsubseteq> Q"
  by (rel_auto robust; fastforce)

theorem wp_refine_intro: "(\<And> r. `Q wp r \<Rightarrow> P wp r`) \<Longrightarrow> P \<sqsubseteq> Q"
  using wp_refine_iff by blast
  
theorem wp_eq_iff: "(\<forall> r. P wp r = Q wp r) \<longrightarrow> P = Q"
  by (rel_auto robust; fastforce)

theorem wp_eq_intro: "(\<And> r. P wp r = Q wp r) \<Longrightarrow> P = Q"
  by (simp add: wp_eq_iff)

lemma wp_true: "P wp true = Pre(P)"
  by (rel_auto)

lemma wp_false [wp]: "P wp false = false"
  by (rel_auto)

lemma wp_abort [wp]: "false wp b = false"
  by (rel_auto)

lemma wp_seq [wp]: "(P ;; Q) wp b = P wp (Q wp b)"
  by (simp add: wp_upred_def, metis Pre_seq RA1)

lemma wp_disj [wp]: "(P \<or> Q) wp b = (P wp b \<or> Q wp b)"
  by (rel_auto)

lemma wp_ndet [wp]: "(P \<sqinter> Q) wp b = (P wp b \<or> Q wp b)"
  by (rel_auto)

lemma wp_cond [wp]: "(P \<triangleleft> b \<triangleright>\<^sub>r Q) wp r = ((b \<Rightarrow> P wp r) \<and> ((\<not> b) \<Rightarrow> Q wp r))"
  by rel_auto

lemma wp_UINF_mem [wp]: "(\<Sqinter> i\<in>I \<bullet> P(i)) wp b = (\<Sqinter> i\<in>I \<bullet> P(i) wp b)"
  by (rel_auto)

lemma wp_UINF_ind [wp]: "(\<Sqinter> i \<bullet> P(i)) wp b = (\<Sqinter> i \<bullet> P(i) wp b)"
  by (rel_auto)

lemma wp_UINF_ind_2 [wp]: "(\<Sqinter> (i, j) \<bullet> P i j) wp b = (\<Or> (i, j) \<bullet> (P i j) wp b)"
  by (rel_auto)

lemma wp_UINF_ind_3 [wp]: "(\<Sqinter> (i, j, k) \<bullet> P i j k) wp b = (\<Or> (i, j, k) \<bullet> (P i j k) wp b)"
  by (rel_blast)

lemma wp_test [wp]: "?[b] wp c = (b \<and> c)"
  by (rel_auto)

lemma wp_gcmd [wp]: "(b \<longrightarrow>\<^sub>r P) wp c = (b \<and> P wp c)"
  by (rel_auto)

theorem wp_skip [wp]:
  "II wp r = r"
  by rel_auto

lemma wp_assigns [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a wp b = \<sigma> \<dagger> b"
  by (rel_auto)

lemma wp_nd_assign [wp]: "(x := *) wp b = (\<^bold>\<exists> v \<bullet> b\<lbrakk>\<guillemotleft>v\<guillemotright>/&x\<rbrakk>)"
  by (simp add: nd_assign_def wp, rel_auto)

lemma wp_rel_frext [wp]: 
  assumes "vwb_lens a" "a \<sharp> q"
  shows "a:[P]\<^sup>+ wp (p \<oplus>\<^sub>p a \<and> q) = ((P wp p) \<oplus>\<^sub>p a \<and> q)"
  using assms
  by (rel_auto, metis (full_types), metis mwb_lens_def vwb_lens_mwb weak_lens.put_get)

lemma wp_rel_aext_unrest [wp]: "\<lbrakk> vwb_lens a; a \<sharp> b \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ wp b = (b \<and> (P wp true) \<oplus>\<^sub>p a)"
  by (rel_auto, metis, metis mwb_lens_def vwb_lens_mwb weak_lens.put_get)

lemma wp_rel_aext_usedby [wp]: "\<lbrakk> vwb_lens a; a \<natural> b \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ wp b = (P wp (b \<restriction>\<^sub>e a)) \<oplus>\<^sub>p a"
  by (rel_auto, metis mwb_lens_def vwb_lens_mwb weak_lens.put_get)

lemma wp_wlp_conjugate: "P wp b = (\<not> P wlp (\<not> b))"
  by (rel_auto)

text \<open> Weakest Precondition and Weakest Liberal Precondition are equivalent for 
  terminating deterministic programs. \<close>

lemma wlp_wp_equiv_lem: "\<lbrakk>(mk\<^sub>e (Pair a)) \<dagger> II\<rbrakk>\<^sub>e a"
  by (rel_auto)

lemma wlp_wp_equiv_total_det: "(\<forall> b . P wp b = P wlp b) \<longleftrightarrow> (Pre(P) = true \<and> ufunctional P)"
  apply (rel_auto)
    apply blast
   apply (rename_tac a b y)
  apply (subgoal_tac "\<lbrakk>(mk\<^sub>e (Pair a)) \<dagger> II\<rbrakk>\<^sub>e b")
  apply (simp add: assigns_r.rep_eq skip_r_def subst.rep_eq subst_id.rep_eq Abs_uexpr_inverse)
  using wlp_wp_equiv_lem apply fastforce
  apply blast
  done

lemma total_det_then_wlp_wp_equiv: "\<lbrakk> Pre(P) = true; ufunctional P \<rbrakk> \<Longrightarrow> P wp b = P wlp b"
  using wlp_wp_equiv_total_det by blast

lemma Pre_as_wp: "Pre(P) = P wp true"
  by (simp add: wp_true)

method wp_calc =
  (rule wp_refine_intro wp_eq_intro, wp_tac)

method wp_auto = (wp_calc, rel_auto)

end