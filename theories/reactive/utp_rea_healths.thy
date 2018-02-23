section \<open> Reactive Healthiness Conditions \<close>

theory utp_rea_healths
  imports utp_rea_core
begin

subsection \<open> R1: Events cannot be undone \<close>

definition R1 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
R1_def [upred_defs]: "R1 (P) = (P \<and> ($tr \<le>\<^sub>u $tr\<acute>))"

lemma R1_idem: "R1(R1(P)) = R1(P)"
  by pred_auto

lemma R1_Idempotent [closure]: "Idempotent R1"
  by (simp add: Idempotent_def R1_idem)

lemma R1_mono: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)"
  by pred_auto

lemma R1_Monotonic: "Monotonic R1"
  by (simp add: mono_def R1_mono)

lemma R1_Continuous: "Continuous R1"
  by (auto simp add: Continuous_def, rel_auto)

lemma R1_unrest [unrest]: "\<lbrakk> x \<bowtie> in_var tr; x \<bowtie> out_var tr; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> R1(P)"
  by (simp add: R1_def unrest lens_indep_sym)

lemma R1_false: "R1(false) = false"
  by pred_auto

lemma R1_conj: "R1(P \<and> Q) = (R1(P) \<and> R1(Q))"
  by pred_auto

lemma conj_R1_closed_1 [closure]: "P is R1 \<Longrightarrow> (P \<and> Q) is R1"
  by (rel_blast)

lemma conj_R1_closed_2 [closure]: "Q is R1 \<Longrightarrow> (P \<and> Q) is R1"
  by (rel_blast)

lemma R1_disj: "R1(P \<or> Q) = (R1(P) \<or> R1(Q))"
  by pred_auto

lemma R1_impl: "R1(P \<Rightarrow> Q) = ((\<not> R1(\<not> P)) \<Rightarrow> R1(Q))"
  by (rel_auto)

lemma R1_inf: "R1(P \<sqinter> Q) = (R1(P) \<sqinter> R1(Q))"
  by pred_auto

lemma R1_USUP:
  "R1(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R1(P(i)))"
  by (rel_auto)

lemma R1_Sup [closure]: "\<lbrakk> \<And> P. P \<in> A \<Longrightarrow> P is R1; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter> A is R1"
  using R1_Continuous by (auto simp add: Continuous_def Healthy_def)

lemma R1_UINF:
  assumes "A \<noteq> {}"
  shows "R1(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R1(P(i)))"
  using assms by (rel_auto)

lemma UINF_ind_R1_closed [closure]:
  "\<lbrakk> \<And> i. P(i) is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<bullet> P(i)) is R1"
  by (rel_blast)

lemma UINF_R1_closed [closure]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<in> A \<bullet> P i) is R1"
  by (rel_blast)
    
lemma tr_ext_conj_R1 [closure]: 
  "$tr\<acute> =\<^sub>u $tr ^\<^sub>u e \<and> P is R1"
  by (rel_auto, simp add: Prefix_Order.prefixI)

lemma tr_id_conj_R1 [closure]: 
  "$tr\<acute> =\<^sub>u $tr \<and> P is R1"
  by (rel_auto)

lemma R1_extend_conj: "R1(P \<and> Q) = (R1(P) \<and> Q)"
  by pred_auto

lemma R1_extend_conj': "R1(P \<and> Q) = (P \<and> R1(Q))"
  by pred_auto

lemma R1_cond: "R1(P \<triangleleft> b \<triangleright> Q) = (R1(P) \<triangleleft> b \<triangleright> R1(Q))"
  by (rel_auto)

lemma R1_cond': "R1(P \<triangleleft> b \<triangleright> Q) = (R1(P) \<triangleleft> R1(b) \<triangleright> R1(Q))"
  by (rel_auto)

lemma R1_negate_R1: "R1(\<not> R1(P)) = R1(\<not> P)"
  by pred_auto

lemma R1_wait_true [usubst]: "(R1 P)\<^sub>t = R1(P)\<^sub>t"
  by pred_auto

lemma R1_wait_false [usubst]: "(R1 P) \<^sub>f = R1(P) \<^sub>f"
  by pred_auto

lemma R1_wait'_true [usubst]: "(R1 P)\<lbrakk>true/$wait\<acute>\<rbrakk> = R1(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (rel_auto)

lemma R1_wait'_false [usubst]: "(R1 P)\<lbrakk>false/$wait\<acute>\<rbrakk> = R1(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (rel_auto)

lemma R1_wait_false_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>false/$wait\<rbrakk> is R1"
  by (rel_auto)

lemma R1_wait'_false_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>false/$wait\<acute>\<rbrakk> is R1"
  by (rel_auto)

lemma R1_skip: "R1(II) = II"
  by (rel_auto)

lemma skip_is_R1 [closure]: "II is R1"
  by (rel_auto)

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> (($tr \<le>\<^sub>u $tr\<acute>) \<sqsubseteq> P)"
  by (rel_blast)

lemma R1_trace_extension [closure]:
  "$tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u e is R1"
  by (rel_auto)
    
lemma tr_le_trans:
  "(($tr \<le>\<^sub>u $tr\<acute>) ;; ($tr \<le>\<^sub>u $tr\<acute>)) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto)
    
lemma R1_seqr:
  "R1(R1(P) ;; R1(Q)) = (R1(P) ;; R1(Q))"
  by (rel_auto)

lemma R1_seqr_closure [closure]:
  assumes "P is R1" "Q is R1"
  shows "(P ;; Q) is R1"
  using assms unfolding R1_by_refinement
  by (metis seqr_mono tr_le_trans)

lemma R1_power [closure]: "P is R1 \<Longrightarrow> P\<^bold>^n is R1"
  by (induct n, simp_all add: closure)

lemma R1_true_comp [simp]: "(R1(true) ;; R1(true)) = R1(true)"
  by (rel_auto)

lemma R1_ok'_true: "(R1(P))\<^sup>t = R1(P\<^sup>t)"
  by pred_auto

lemma R1_ok'_false: "(R1(P))\<^sup>f = R1(P\<^sup>f)"
  by pred_auto

lemma R1_ok_true: "(R1(P))\<lbrakk>true/$ok\<rbrakk> = R1(P\<lbrakk>true/$ok\<rbrakk>)"
  by pred_auto

lemma R1_ok_false: "(R1(P))\<lbrakk>false/$ok\<rbrakk> = R1(P\<lbrakk>false/$ok\<rbrakk>)"
  by pred_auto

lemma seqr_R1_true_right: "((P ;; R1(true)) \<or> P) = (P ;; ($tr \<le>\<^sub>u $tr\<acute>))"
  by (rel_auto)

lemma conj_R1_true_right: "(P;;R1(true) \<and> Q;;R1(true)) ;; R1(true) = (P;;R1(true) \<and> Q;;R1(true))"
  apply (rel_auto) using dual_order.trans by blast+

lemma R1_extend_conj_unrest: "\<lbrakk> $tr \<sharp> Q; $tr\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> R1(P \<and> Q) = (R1(P) \<and> Q)"
  by pred_auto

lemma R1_extend_conj_unrest': "\<lbrakk> $tr \<sharp> P; $tr\<acute> \<sharp> P \<rbrakk> \<Longrightarrow> R1(P \<and> Q) = (P \<and> R1(Q))"
  by pred_auto

lemma R1_tr'_eq_tr: "R1($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto)

lemma R1_tr_less_tr': "R1($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_auto)

lemma tr_strict_prefix_R1_closed [closure]: "$tr <\<^sub>u $tr\<acute> is R1"
  by (rel_auto)
    
lemma R1_H2_commute: "R1(H2(P)) = H2(R1(P))"
  by (simp add: H2_split R1_def usubst, rel_auto)

subsection \<open> R2: No dependence upon trace history \<close>

text \<open> There are various ways of expressing $R2$, which are enumerated below. \<close>

definition R2a :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[upred_defs]: "R2a (P) = (\<Sqinter> s \<bullet> P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s\<guillemotright>+($tr\<acute>-$tr)/$tr,$tr\<acute>\<rbrakk>)"

definition R2a' :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[upred_defs]: "R2a' P = (R2a(P) \<triangleleft> R1(true) \<triangleright> P)"

definition R2s :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[upred_defs]: "R2s (P) = (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>($tr\<acute>-$tr)/$tr\<acute>\<rbrakk>)"

definition R2 :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "R2(P) = R1(R2s(P))"

definition R2c :: "('t::trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "R2c(P) = (R2s(P) \<triangleleft> R1(true) \<triangleright> P)"

text \<open> @{term R2a} and @{term R2s} are the standard definitions from the UTP book~\cite{Hoare&98}.
  An issue with these forms is that their definition depends upon @{term R1} also being 
  satisfied~\cite{Foster17b}, since otherwise the trace minus operator is not well defined. 
  We overcome this with our own version, @{term R2c}, which applies @{term R2s} if @{term R1} holds,
  and otherwise has no effect. This latter healthiness condition can therefore be reasoned about
  independently of @{term R1}, which is useful in some circumstances. \<close>

lemma unrest_ok_R2s [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok'_R2s [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok_R2c [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma unrest_ok'_R2c [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R2s_unrest [unrest]: "\<lbrakk> vwb_lens x; x \<bowtie> in_var tr; x \<bowtie> out_var tr; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> R2s(P)"
  by (simp add: R2s_def unrest usubst lens_indep_sym)

lemma R2s_subst_wait_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<rbrakk> = R2s(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2s_subst_wait'_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2s(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2_subst_wait_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<rbrakk> = R2(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<rbrakk> = R2(P\<lbrakk>false/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2c_R2s_absorb: "R2c(R2s(P)) = R2s(P)"
  by (rel_auto)

lemma R2a_R2s: "R2a(R2s(P)) = R2s(P)"
  by (rel_auto)

lemma R2s_R2a: "R2s(R2a(P)) = R2a(P)"
  by (rel_auto)

lemma R2a_equiv_R2s: "P is R2a \<longleftrightarrow> P is R2s"
  by (metis Healthy_def' R2a_R2s R2s_R2a)

lemma R2a_idem: "R2a(R2a(P)) = R2a(P)"
  by (rel_auto)

lemma R2a'_idem: "R2a'(R2a'(P)) = R2a'(P)"
  by (rel_auto)

lemma R2a_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2a(P) \<sqsubseteq> R2a(Q)"
  by (rel_blast)

lemma R2a'_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2a'(P) \<sqsubseteq> R2a'(Q)"
  by (rel_blast)

lemma R2a'_weakening: "R2a'(P) \<sqsubseteq> P"
  apply (rel_simp)
  apply (rename_tac ok wait tr more ok' wait' tr' more')
  apply (rule_tac x="tr" in exI)
  apply (simp add: diff_add_cancel_left')
  done

lemma R2s_idem: "R2s(R2s(P)) = R2s(P)"
  by (pred_auto)

lemma R2_idem: "R2(R2(P)) = R2(P)"
  by (pred_auto)

lemma R2_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)"
  by (pred_auto)

lemma R2_implies_R1 [closure]: "P is R2 \<Longrightarrow> P is R1"
  by (rel_blast)
    
lemma R2c_Continuous: "Continuous R2c"
  by (rel_simp)

lemma R2c_lit: "R2c(\<guillemotleft>x\<guillemotright>) = \<guillemotleft>x\<guillemotright>"
  by (rel_auto)

lemma tr_strict_prefix_R2c_closed [closure]: "$tr <\<^sub>u $tr\<acute> is R2c"
  by (rel_auto)

lemma R2s_conj: "R2s(P \<and> Q) = (R2s(P) \<and> R2s(Q))"
  by (pred_auto)

lemma R2_conj: "R2(P \<and> Q) = (R2(P) \<and> R2(Q))"
  by (pred_auto)

lemma R2s_disj: "R2s(P \<or> Q) = (R2s(P) \<or> R2s(Q))"
  by pred_auto

lemma R2s_USUP:
  "R2s(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R2s(P(i)))"
  by (simp add: R2s_def usubst)

lemma R2c_USUP:
  "R2c(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R2c(P(i)))"
  by (rel_auto)

lemma R2s_UINF:
  "R2s(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R2s(P(i)))"
  by (simp add: R2s_def usubst)

lemma R2c_UINF:
  "R2c(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R2c(P(i)))"
  by (rel_auto)

lemma R2_disj: "R2(P \<or> Q) = (R2(P) \<or> R2(Q))"
  by (pred_auto)

lemma R2s_not: "R2s(\<not> P) = (\<not> R2s(P))"
  by pred_auto

lemma R2s_condr: "R2s(P \<triangleleft> b \<triangleright> Q) = (R2s(P) \<triangleleft> R2s(b) \<triangleright> R2s(Q))"
  by (rel_auto)

lemma R2_condr: "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2(b) \<triangleright> R2(Q))"
  by (rel_auto)

lemma R2_condr': "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2s(b) \<triangleright> R2(Q))"
  by (rel_auto)

lemma R2s_ok: "R2s($ok) = $ok"
  by (rel_auto)

lemma R2s_ok': "R2s($ok\<acute>) = $ok\<acute>"
  by (rel_auto)

lemma R2s_wait: "R2s($wait) = $wait"
  by (rel_auto)

lemma R2s_wait': "R2s($wait\<acute>) = $wait\<acute>"
  by (rel_auto)

lemma R2s_true: "R2s(true) = true"
  by pred_auto

lemma R2s_false: "R2s(false) = false"
  by pred_auto

lemma true_is_R2s:
  "true is R2s"
  by (simp add: Healthy_def R2s_true)

lemma R2s_lift_rea: "R2s(\<lceil>P\<rceil>\<^sub>R) = \<lceil>P\<rceil>\<^sub>R"
  by (simp add: R2s_def usubst unrest)

lemma R2c_lift_rea: "R2c(\<lceil>P\<rceil>\<^sub>R) = \<lceil>P\<rceil>\<^sub>R"
  by (simp add: R2c_def R2s_lift_rea cond_idem usubst unrest)

lemma R2c_true: "R2c(true) = true"
  by (rel_auto)

lemma R2c_false: "R2c(false) = false"
  by (rel_auto)

lemma R2c_and: "R2c(P \<and> Q) = (R2c(P) \<and> R2c(Q))"
  by (rel_auto)

lemma conj_R2c_closed [closure]: "\<lbrakk> P is R2c; Q is R2c \<rbrakk> \<Longrightarrow> (P \<and> Q) is R2c"
  by (simp add: Healthy_def R2c_and)

lemma R2c_disj: "R2c(P \<or> Q) = (R2c(P) \<or> R2c(Q))"
  by (rel_auto)

lemma R2c_inf: "R2c(P \<sqinter> Q) = (R2c(P) \<sqinter> R2c(Q))"
  by (rel_auto)

lemma R2c_not: "R2c(\<not> P) = (\<not> R2c(P))"
  by (rel_auto)

lemma R2c_ok: "R2c($ok) = ($ok)"
  by (rel_auto)

lemma R2c_ok': "R2c($ok\<acute>) = ($ok\<acute>)"
  by (rel_auto)

lemma R2c_wait: "R2c($wait) = $wait"
  by (rel_auto)

lemma R2c_wait': "R2c($wait\<acute>) = $wait\<acute>"
  by (rel_auto)

lemma R2c_wait'_true [usubst]: "(R2c P)\<lbrakk>true/$wait\<acute>\<rbrakk> = R2c(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (rel_auto)

lemma R2c_wait'_false [usubst]: "(R2c P)\<lbrakk>false/$wait\<acute>\<rbrakk> = R2c(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (rel_auto)

lemma R2c_tr'_minus_tr: "R2c($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_auto) using minus_zero_eq by blast

lemma R2c_tr'_ge_tr: "R2c($tr\<acute> \<ge>\<^sub>u $tr) = ($tr\<acute> \<ge>\<^sub>u $tr)"
  by (rel_auto)

lemma R2c_tr_less_tr': "R2c($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_auto)

lemma R2c_condr: "R2c(P \<triangleleft> b \<triangleright> Q) = (R2c(P) \<triangleleft> R2c(b) \<triangleright> R2c(Q))"
  by (rel_auto)

lemma R2c_shAll: "R2c (\<^bold>\<forall> x \<bullet> P x) = (\<^bold>\<forall> x \<bullet> R2c(P x))"
  by (rel_auto)

lemma R2c_impl: "R2c(P \<Rightarrow> Q) = (R2c(P) \<Rightarrow> R2c(Q))"
  by (metis (no_types, lifting) R2c_and R2c_not double_negation impl_alt_def not_conj_deMorgans)

lemma R2c_skip_r: "R2c(II) = II"
proof -
  have "R2c(II) = R2c($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (subst skip_r_unfold[of tr], simp_all)
  also have "... = (R2c($tr\<acute> =\<^sub>u $tr) \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2c_and, simp add: R2c_def R2s_def usubst unrest cond_idem)
  also have "... = ($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2c_tr'_minus_tr)
  finally show ?thesis
    by (subst skip_r_unfold[of tr], simp_all)
qed

lemma R1_R2c_commute: "R1(R2c(P)) = R2c(R1(P))"
  by (rel_auto)

lemma R1_R2c_is_R2: "R1(R2c(P)) = R2(P)"
  by (rel_auto)

lemma R1_R2s_R2c: "R1(R2s(P)) = R1(R2c(P))"
  by (rel_auto)

lemma R1_R2s_tr_wait:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)) = ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)"
  apply rel_auto using minus_zero_eq by blast

lemma R1_R2s_tr'_eq_tr:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr)) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_auto) using minus_zero_eq by blast

lemma R1_R2s_tr'_extend_tr:
  "\<lbrakk> $tr \<sharp> v; $tr\<acute> \<sharp> v \<rbrakk> \<Longrightarrow> R1 (R2s ($tr\<acute> =\<^sub>u $tr ^\<^sub>u v)) = ($tr\<acute> =\<^sub>u $tr  ^\<^sub>u v)"
  apply (rel_auto)
   apply (metis append_minus)
  apply (simp add: Prefix_Order.prefixI)
  done

lemma R2_tr_prefix: "R2($tr \<le>\<^sub>u $tr\<acute>) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (pred_auto)

lemma R2_form:
  "R2(P) = (\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)"
  by (rel_auto, metis trace_class.add_diff_cancel_left trace_class.le_iff_add)

lemma R2_subst_tr: 
  assumes "P is R2" 
  shows "[$tr \<mapsto>\<^sub>s tr\<^sub>0, $tr\<acute> \<mapsto>\<^sub>s tr\<^sub>0 + t] \<dagger> P = [$tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s t] \<dagger> P"
proof -
  have "[$tr \<mapsto>\<^sub>s tr\<^sub>0, $tr\<acute> \<mapsto>\<^sub>s tr\<^sub>0 + t] \<dagger> R2 P = [$tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s t] \<dagger> R2 P"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma R2_seqr_form:
  shows "(R2(P) ;; R2(Q)) =
         (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
proof -
  have "(R2(P) ;; R2(Q)) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (R2(P))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2(Q))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)"
    by (subst seqr_middle[of tr], simp_all)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) ;;
                                (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: R2_form usubst unrest uquant_lift, rel_blast)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;;
                                (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: conj_comm)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (rel_blast)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by (rel_auto)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma R2_seqr_form':
  assumes "P is R2" "Q is R2"
  shows "P ;; Q =
         (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  using R2_seqr_form[of P Q] by (simp add: Healthy_if assms)

lemma R2_tr_middle:
  assumes "P is R2" "Q is R2"
  shows "(\<^bold>\<exists> tr\<^sub>0 \<bullet> (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>) = (P ;; Q)"
proof -
  have "(P ;; Q) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>))"
    by (simp add: seqr_middle)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((R2 P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2 Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>))"
    by (simp add: assms Healthy_if)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((R2 P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2 Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (rel_auto)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (simp add: assms Healthy_if)
  finally show ?thesis ..
qed

lemma R2_seqr_distribute:
  fixes P :: "('t::trace,'\<alpha>,'\<beta>) rel_rp" and Q :: "('t,'\<beta>,'\<gamma>) rel_rp"
  shows "R2(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
proof -
  have "R2(R2(P) ;; R2(Q)) =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>($tr\<acute> - $tr)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
    by (simp add: R2_seqr_form, simp add: R2s_def usubst unrest, rel_auto)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (subst subst_eq_replace, simp)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (rel_auto)
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> ($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr\<acute> \<ge>\<^sub>u $tr))"
    by pred_auto
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  proof -
    have "\<And> tt\<^sub>1 tt\<^sub>2. ((($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr) :: ('t,'\<alpha>,'\<gamma>) rel_rp)
           = ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      apply (rel_auto)
        apply (metis add.assoc diff_add_cancel_left')
       apply (simp add: add.assoc)
      apply (meson le_add order_trans)
      done
    thus ?thesis by simp
  qed
  also have "... = (R2(P) ;; R2(Q))"
    by (simp add: R2_seqr_form)
  finally show ?thesis .
qed

lemma R2_seqr_closure [closure]:
  assumes "P is R2" "Q is R2"
  shows "(P ;; Q) is R2"
  by (metis Healthy_def' R2_seqr_distribute assms(1) assms(2))

lemma false_R2 [closure]: "false is R2"
  by (rel_auto)
    
lemma R1_R2_commute:
  "R1(R2(P)) = R2(R1(P))"
  by pred_auto

lemma R2_R1_form: "R2(R1(P)) = R1(R2s(P))"
  by (rel_auto)

lemma R2s_H1_commute:
  "R2s(H1(P)) = H1(R2s(P))"
  by (rel_auto)

lemma R2s_H2_commute:
  "R2s(H2(P)) = H2(R2s(P))"
  by (simp add: H2_split R2s_def usubst)

lemma R2_R1_seq_drop_left:
  "R2(R1(P) ;; R1(Q)) = R2(P ;; R1(Q))"
  by (rel_auto)

lemma R2c_idem: "R2c(R2c(P)) = R2c(P)"
  by (rel_auto)

lemma R2c_Idempotent [closure]: "Idempotent R2c"
  by (simp add: Idempotent_def R2c_idem)

lemma R2c_Monotonic [closure]: "Monotonic R2c"
  by (rel_auto)

lemma R2c_H2_commute: "R2c(H2(P)) = H2(R2c(P))"
  by (simp add: H2_split R2c_disj R2c_def R2s_def usubst, rel_auto)

lemma R2c_seq: "R2c(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
  by (metis (no_types, lifting) R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute R2c_idem)

lemma R2_R2c_def: "R2(P) = R1(R2c(P))"
  by (rel_auto)

lemma R2_comp_def: "R2 = R1 \<circ> R2c"
  by (auto simp add: R2_R2c_def)
    
lemma R2c_R1_seq: "R2c(R1(R2c(P)) ;; R1(R2c(Q))) = (R1(R2c(P)) ;; R1(R2c(Q)))"
  using R2c_seq[of P Q] by (simp add: R2_R2c_def)

lemma R1_R2c_seqr_distribute:
  fixes P :: "('t::trace,'\<alpha>,'\<beta>) rel_rp" and Q :: "('t,'\<beta>,'\<gamma>) rel_rp"
  assumes "P is R1" "P is R2c" "Q is R1" "Q is R2c"
  shows "R1(R2c(P ;; Q)) = P ;; Q"
  by (metis Healthy_if R1_seqr R2c_R1_seq assms)

lemma R2_R1_true:
  "R2(R1(true)) = R1(true)"
  by (simp add: R2_R1_form R2s_true)
    
lemma R1_true_R2 [closure]: "R1(true) is R2"
  by (rel_auto)

lemma R1_R2s_R1_true_lemma:
  "R1(R2s(R1 (\<not> R2s P) ;; R1 true)) = R1(R2s((\<not> P) ;; R1 true))"
  by (rel_auto)

lemma R2c_healthy_R2s: "P is R2c \<Longrightarrow> R1(R2s(P)) = R1(P)"
  by (simp add: Healthy_def R1_R2s_R2c) 

subsection \<open> R3: No activity while predecessor is waiting \<close>

definition R3 :: "('t::trace, '\<alpha>) hrel_rp \<Rightarrow> ('t, '\<alpha>) hrel_rp" where
[upred_defs]: "R3(P) = (II \<triangleleft> $wait \<triangleright> P)"

lemma R3_idem: "R3(R3(P)) = R3(P)"
  by (rel_auto)

lemma R3_Idempotent [closure]: "Idempotent R3"
  by (simp add: Idempotent_def R3_idem)

lemma R3_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)"
  by (rel_auto)

lemma R3_Monotonic: "Monotonic R3"
  by (simp add: mono_def R3_mono)

lemma R3_Continuous: "Continuous R3"
  by (rel_auto)

lemma R3_conj: "R3(P \<and> Q) = (R3(P) \<and> R3(Q))"
  by (rel_auto)

lemma R3_disj: "R3(P \<or> Q) = (R3(P) \<or> R3(Q))"
  by (rel_auto)

lemma R3_USUP:
  assumes "A \<noteq> {}"
  shows "R3(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R3(P(i)))"
  using assms by (rel_auto)

lemma R3_UINF:
  assumes "A \<noteq> {}"
  shows "R3(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R3(P(i)))"
  using assms by (rel_auto)

lemma R3_condr: "R3(P \<triangleleft> b \<triangleright> Q) = (R3(P) \<triangleleft> b \<triangleright> R3(Q))"
  by (rel_auto)

lemma R3_skipr: "R3(II) = II"
  by (rel_auto)

lemma R3_form: "R3(P) = (($wait \<and> II) \<or> (\<not> $wait \<and> P))"
  by (rel_auto)

lemma wait_R3:
  "($wait \<and> R3(P)) = (II \<and> $wait\<acute>)"
  by (rel_auto)

lemma nwait_R3:
  "(\<not>$wait \<and> R3(P)) = (\<not>$wait \<and> P)"
  by (rel_auto)

lemma R3_semir_form:
  "(R3(P) ;; R3(Q)) = R3(P ;; R3(Q))"
  by (rel_auto)

lemma R3_semir_closure:
  assumes "P is R3" "Q is R3"
  shows "(P ;; Q) is R3"
  using assms
  by (metis Healthy_def' R3_semir_form)

lemma R1_R3_commute: "R1(R3(P)) = R3(R1(P))"
  by (rel_auto)

lemma R2_R3_commute: "R2(R3(P)) = R3(R2(P))"
  apply (rel_auto)
  using minus_zero_eq apply blast+
  done

subsection {* RP laws *}

definition RP_def [upred_defs]: "RP(P) = R1(R2c(R3(P)))"

lemma RP_comp_def: "RP = R1 \<circ> R2c \<circ> R3"
  by (auto simp add: RP_def)

lemma RP_alt_def: "RP(P) = R1(R2(R3(P)))"
  by (metis R1_R2c_is_R2 R1_idem RP_def)

lemma RP_intro: "\<lbrakk> P is R1; P is R2; P is R3 \<rbrakk> \<Longrightarrow> P is RP"
  by (simp add: Healthy_def' RP_alt_def)

lemma RP_idem: "RP(RP(P)) = RP(P)"
  by (simp add: R1_R2c_is_R2 R2_R3_commute R2_idem R3_idem RP_def)

lemma RP_Idempotent [closure]: "Idempotent RP"
  by (simp add: Idempotent_def RP_idem)

lemma RP_mono: "P \<sqsubseteq> Q \<Longrightarrow> RP(P) \<sqsubseteq> RP(Q)"
  by (simp add: R1_R2c_is_R2 R2_mono R3_mono RP_def)

lemma RP_Monotonic: "Monotonic RP"
  by (simp add: mono_def RP_mono)

lemma RP_Continuous: "Continuous RP"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3_Continuous RP_comp_def)

lemma RP_skip:
  "RP(II) = II"
  by (simp add: R1_skip R2c_skip_r R3_skipr RP_def)

lemma RP_skip_closure:
  "II is RP"
  by (simp add: Healthy_def' RP_skip)

lemma RP_seq_closure:
  assumes "P is RP" "Q is RP"
  shows "(P ;; Q) is RP"
proof (rule RP_intro)
  show "(P ;; Q) is R1"
    by (metis Healthy_def R1_seqr RP_def assms)
  thus "(P ;; Q) is R2"
    by (metis Healthy_def' R2_R2c_def R2c_R1_seq RP_def  assms)
  show "(P ;; Q) is R3"
    by (metis (no_types, lifting) Healthy_def' R1_R2c_is_R2 R2_R3_commute R3_idem R3_semir_form RP_def assms)
qed

subsection \<open> UTP theories \<close>

typedecl REA
abbreviation "REA \<equiv> UTHY(REA, ('t::trace,'\<alpha>) rp)"

overloading
  rea_hcond == "utp_hcond :: (REA, ('t::trace,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health"
  rea_unit == "utp_unit :: (REA, ('t::trace,'\<alpha>) rp) uthy \<Rightarrow> ('t,'\<alpha>) hrel_rp"
begin
  definition rea_hcond :: "(REA, ('t::trace,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health"
  where [upred_defs]: "rea_hcond T = RP"
  definition rea_unit :: "(REA, ('t::trace,'\<alpha>) rp) uthy \<Rightarrow> ('t,'\<alpha>) hrel_rp"
  where [upred_defs]: "rea_unit T = II"
end

interpretation rea_utp_theory: utp_theory "UTHY(REA, ('t::trace,'\<alpha>) rp)"
  rewrites "carrier (uthy_order REA) = \<lbrakk>RP\<rbrakk>\<^sub>H"
  by (simp_all add: rea_hcond_def utp_theory_def RP_idem)

interpretation rea_utp_theory_mono: utp_theory_continuous "UTHY(REA, ('t::trace,'\<alpha>) rp)"
  rewrites "carrier (uthy_order REA) = \<lbrakk>RP\<rbrakk>\<^sub>H"
  by (unfold_locales, simp_all add: RP_Continuous rea_hcond_def)

interpretation rea_utp_theory_rel: utp_theory_unital "UTHY(REA, ('t::trace,'\<alpha>) rp)"
  rewrites "carrier (uthy_order REA) = \<lbrakk>RP\<rbrakk>\<^sub>H"
  by (unfold_locales, simp_all add: rea_hcond_def rea_unit_def RP_seq_closure RP_skip_closure)

lemma rea_top: "\<^bold>\<top>\<^bsub>REA\<^esub> = ($wait \<and> II)"
proof -
  have "\<^bold>\<top>\<^bsub>REA\<^esub> = RP(false)"
    by (simp add: rea_utp_theory_mono.healthy_top, simp add: rea_hcond_def)
  also have "... = ($wait \<and> II)"
    by (rel_auto, metis minus_zero_eq)
  finally show ?thesis .
qed

lemma rea_top_left_zero:
  assumes "P is RP"
  shows "(\<^bold>\<top>\<^bsub>REA\<^esub> ;; P) = \<^bold>\<top>\<^bsub>REA\<^esub>"
proof -
  have "(\<^bold>\<top>\<^bsub>REA\<^esub> ;; P) = (($wait \<and> II) ;; R3(P))"
    by (metis (no_types, lifting) Healthy_def R1_R2c_is_R2 R2_R3_commute R3_idem RP_def assms rea_top)
  also have "... = ($wait \<and> R3(P))"
    by (rel_auto)
  also have "... = ($wait \<and> II)"
    by (metis R3_skipr wait_R3)
  also have "... = \<^bold>\<top>\<^bsub>REA\<^esub>"
    by (simp add: rea_top)
  finally show ?thesis .
qed

lemma rea_bottom: "\<^bold>\<bottom>\<^bsub>REA\<^esub> = R1($wait \<Rightarrow> II)"
proof -
  have "\<^bold>\<bottom>\<^bsub>REA\<^esub> = RP(true)"
    by (simp add: rea_utp_theory_mono.healthy_bottom, simp add: rea_hcond_def)
  also have "... = R1($wait \<Rightarrow> II)"
    by (rel_auto, metis minus_zero_eq)
  finally show ?thesis .
qed

end