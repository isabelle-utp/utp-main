section {* Design Healthiness Conditions *}

theory utp_des_healths
  imports utp_des_core
begin

subsection {* H1: No observation is allowed before initiation *}

definition H1 :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" where
[upred_defs]: "H1(P) = ($ok \<Rightarrow> P)"

lemma H1_idem:
  "H1 (H1 P) = H1(P)"
  by (pred_auto)

lemma H1_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> H1(P) \<sqsubseteq> H1(Q)"
  by (pred_auto)

lemma H1_Continuous: "Continuous H1"
  by (rel_auto)

lemma H1_below_top:
  "H1(P) \<sqsubseteq> \<top>\<^sub>D"
  by (pred_auto)

lemma H1_design_skip:
  "H1(II) = II\<^sub>D"
  by (rel_auto)

lemma H1_cond: "H1(P \<triangleleft> b \<triangleright> Q) = H1(P) \<triangleleft> b \<triangleright> H1(Q)"
  by (rel_auto)

lemma H1_conj: "H1(P \<and> Q) = (H1(P) \<and> H1(Q))"
  by (rel_auto)

lemma H1_disj: "H1(P \<or> Q) = (H1(P) \<or> H1(Q))"
  by (rel_auto)

lemma design_export_H1: "(P \<turnstile> Q) = (P \<turnstile> H1(Q))"
  by (rel_auto)

text {* The H1 algebraic laws are valid only when $\alpha(R)$ is homogeneous. This should maybe be
        generalised. *}

theorem H1_algebraic_intro:
  assumes
    "(true\<^sub>h ;; R) = true\<^sub>h"
    "(II\<^sub>D ;; R) = R"
  shows "R is H1"
proof -
  have "R = (II\<^sub>D ;; R)" by (simp add: assms(2))
  also have "... = (H1(II) ;; R)"
    by (simp add: H1_design_skip)
  also have "... = (($ok \<Rightarrow> II) ;; R)"
    by (simp add: H1_def)
  also have "... = (((\<not> $ok) ;; R) \<or> R)"
    by (simp add: impl_alt_def seqr_or_distl)
  also have "... = ((((\<not> $ok) ;; true\<^sub>h) ;; R) \<or> R)"
    by (simp add: precond_right_unit unrest)
  also have "... = (((\<not> $ok) ;; true\<^sub>h) \<or> R)"
    by (metis assms(1) seqr_assoc)
  also have "... = ($ok \<Rightarrow> R)"
    by (simp add: impl_alt_def precond_right_unit unrest)
  finally show ?thesis by (metis H1_def Healthy_def')
qed

lemma nok_not_false:
  "(\<not> $ok) \<noteq> false"
  by (pred_auto)

theorem H1_left_zero:
  assumes "P is H1"
  shows "(true ;; P) = true"
proof -
  from assms have "(true ;; P) = (true ;; ($ok \<Rightarrow> P))"
    by (simp add: H1_def Healthy_def')
  (* The next step ensures we get the right alphabet for true by copying it *)
  also from assms have "... = (true ;; (\<not> $ok \<or> P))" (is "_ = (?true ;; _)")
    by (simp add: impl_alt_def)
  also from assms have "... = ((?true ;; (\<not> $ok)) \<or> (?true ;; P))"
    using seqr_or_distr by blast
  also from assms have "... = (true \<or> (true ;; P))"
    by (simp add: nok_not_false precond_left_zero unrest)
  finally show ?thesis
    by (simp add: upred_defs urel_defs)
qed

theorem H1_left_unit:
  fixes P :: "'\<alpha> hrel_des"
  assumes "P is H1"
  shows "(II\<^sub>D ;; P) = P"
proof -
  have "(II\<^sub>D ;; P) = (($ok \<Rightarrow> II) ;; P)"
    by (metis H1_def H1_design_skip)
  also have "... = (((\<not> $ok) ;; P) \<or> P)"
    by (simp add: impl_alt_def seqr_or_distl)
  also from assms have "... = ((((\<not> $ok) ;; true\<^sub>h) ;; P) \<or> P)"
    by (simp add: precond_right_unit unrest)
  also have "... = (((\<not> $ok) ;; (true\<^sub>h ;; P)) \<or> P)"
    by (simp add: seqr_assoc)
  also from assms have "... = ($ok \<Rightarrow> P)"
    by (simp add: H1_left_zero impl_alt_def precond_right_unit unrest)
  finally show ?thesis using assms
    by (simp add: H1_def Healthy_def')
qed

theorem H1_algebraic:
  "P is H1 \<longleftrightarrow> (true\<^sub>h ;; P) = true\<^sub>h \<and> (II\<^sub>D ;; P) = P"
  using H1_algebraic_intro H1_left_unit H1_left_zero by blast

theorem H1_nok_left_zero:
  fixes P :: "'\<alpha> hrel_des"
  assumes "P is H1"
  shows "((\<not> $ok) ;; P) = (\<not> $ok)"
proof -
  have "((\<not> $ok) ;; P) = (((\<not> $ok) ;; true\<^sub>h) ;; P)"
    by (simp add: precond_right_unit unrest)
  also have "... = ((\<not> $ok) ;; true\<^sub>h)"
    by (metis H1_left_zero assms seqr_assoc)
  also have "... = (\<not> $ok)"
    by (simp add: precond_right_unit unrest)
  finally show ?thesis .
qed

lemma H1_design:
  "H1(P \<turnstile> Q) = (P \<turnstile> Q)"
  by (rel_auto)

lemma H1_rdesign:
  "H1(P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
  by (rel_auto)

lemma H1_choice_closed [closure]:
  "\<lbrakk> P is H1; Q is H1 \<rbrakk> \<Longrightarrow> P \<sqinter> Q is H1"
  by (simp add: H1_def Healthy_def' disj_upred_def impl_alt_def semilattice_sup_class.sup_left_commute)

lemma H1_inf_closed [closure]:
  "\<lbrakk> P is H1; Q is H1 \<rbrakk> \<Longrightarrow> P \<squnion> Q is H1"
  by (rel_blast)

lemma H1_UINF:
  assumes "A \<noteq> {}"
  shows "H1(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> H1(P(i)))"
  using assms by (rel_auto)

lemma H1_Sup:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is H1"
  shows "(\<Sqinter> A) is H1"
proof -
  from assms(2) have "H1 ` A = A"
    by (auto simp add: Healthy_def rev_image_eqI)
  with H1_UINF[of A id, OF assms(1)] show ?thesis
    by (simp add: UINF_as_Sup_image Healthy_def, presburger)
qed

lemma H1_USUP:
  shows "H1(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> H1(P(i)))"
  by (rel_auto)

lemma H1_Inf [closure]:
  assumes "\<forall> P \<in> A. P is H1"
  shows "(\<Squnion> A) is H1"
proof -
  from assms have "H1 ` A = A"
    by (auto simp add: Healthy_def rev_image_eqI)
  with H1_USUP[of A id] show ?thesis
    by (simp add: USUP_as_Inf_image Healthy_def, presburger)
qed

subsection {* H2: A specification cannot require non-termination *}

definition J :: "'\<alpha> hrel_des" where 
[upred_defs]: "J = (($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D)"

definition H2 where
[upred_defs]: "H2 (P)  \<equiv>  P ;; J"

lemma J_split:
  shows "(P ;; J) = (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))"
proof -
  have "(P ;; J) = (P ;; (($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D))"
    by (simp add: H2_def J_def design_def)
  also have "... = (P ;; (($ok \<Rightarrow> $ok \<and> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D))"
    by (rel_auto)
  also have "... = ((P ;; (\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D)) \<or> (P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))))"
    by (rel_auto)
  also have "... = (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))"
  proof -
    have "(P ;; (\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D)) = P\<^sup>f"
    proof -
      have "(P ;; (\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D)) = ((P \<and> \<not> $ok\<acute>) ;; \<lceil>II\<rceil>\<^sub>D)"
        by (rel_auto)
      also have "... = (\<exists> $ok\<acute> \<bullet> P \<and> $ok\<acute> =\<^sub>u false)"
        by (rel_auto)
      also have "... = P\<^sup>f"
        by (metis C1 one_point out_var_uvar unrest_as_exists ok_vwb_lens vwb_lens_mwb)
     finally show ?thesis .
    qed
    moreover have "(P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))) = (P\<^sup>t \<and> $ok\<acute>)"
    proof -
      have "(P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))) = (P ;; ($ok \<and> II))"
        by (rel_auto)
      also have "... = (P\<^sup>t \<and> $ok\<acute>)"
        by (rel_auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma H2_split:
  shows "H2(P) = (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))"
  by (simp add: H2_def J_split)

theorem H2_equivalence:
  "P is H2 \<longleftrightarrow> `P\<^sup>f \<Rightarrow> P\<^sup>t`"
proof -
  have "`P \<Leftrightarrow> (P ;; J)` \<longleftrightarrow> `P \<Leftrightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))`"
    by (simp add: J_split)
  also have "... \<longleftrightarrow> `(P \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>)\<^sup>f \<and> (P \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>)\<^sup>t`"
    by (simp add: subst_bool_split)
  also have "... = `(P\<^sup>f \<Leftrightarrow> P\<^sup>f) \<and> (P\<^sup>t \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t)`"
    by subst_tac
  also have "... = `P\<^sup>t \<Leftrightarrow> (P\<^sup>f \<or> P\<^sup>t)`"
    by (pred_auto robust)
  also have "... = `(P\<^sup>f \<Rightarrow> P\<^sup>t)`"
    by (pred_auto)
  finally show ?thesis
    by (metis H2_def Healthy_def' taut_iff_eq)
qed

lemma H2_equiv:
  "P is H2 \<longleftrightarrow> P\<^sup>t \<sqsubseteq> P\<^sup>f"
  using H2_equivalence refBy_order by blast

lemma H2_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "H2(P \<turnstile> Q) = P \<turnstile> Q"
  using assms
  by (simp add: H2_split design_def usubst unrest, pred_auto)

lemma H2_rdesign:
  "H2(P \<turnstile>\<^sub>r Q) = P \<turnstile>\<^sub>r Q"
  by (simp add: H2_design unrest rdesign_def)

theorem J_idem:
  "(J ;; J) = J"
  by (rel_auto)

theorem H2_idem:
  "H2(H2(P)) = H2(P)"
  by (metis H2_def J_idem seqr_assoc)

theorem H2_Continuous: "Continuous H2"
  by (rel_auto)

theorem H2_not_okay: "H2 (\<not> $ok) = (\<not> $ok)"
proof -
  have "H2 (\<not> $ok) = ((\<not> $ok)\<^sup>f \<or> ((\<not> $ok)\<^sup>t \<and> $ok\<acute>))"
    by (simp add: H2_split)
  also have "... = (\<not> $ok \<or> (\<not> $ok) \<and> $ok\<acute>)"
    by (subst_tac)
  also have "... = (\<not> $ok)"
    by (pred_auto)
  finally show ?thesis .
qed

lemma H2_true: "H2(true) = true"
  by (rel_auto)

lemma H2_choice_closed [closure]:
  "\<lbrakk> P is H2; Q is H2 \<rbrakk> \<Longrightarrow> P \<sqinter> Q is H2"
  by (metis H2_def Healthy_def' disj_upred_def seqr_or_distl)

lemma H2_inf_closed [closure]:
  assumes "P is H2" "Q is H2"
  shows "P \<squnion> Q is H2"
proof -
  have "P \<squnion> Q = (P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>) \<squnion> (Q\<^sup>f \<or> Q\<^sup>t \<and> $ok\<acute>)"
    by (metis H2_def Healthy_def J_split assms(1) assms(2))
  moreover have "H2(...) = ..."
    by (simp add: H2_split usubst, pred_auto)
  ultimately show ?thesis
    by (simp add: Healthy_def)
qed

lemma H2_USUP:
  shows "H2(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> H2(P(i)))"
  by (rel_auto)

theorem H1_H2_commute:
  "H1 (H2 P) = H2 (H1 P)"
proof -
  have "H2 (H1 P) = (($ok \<Rightarrow> P) ;; J)"
    by (simp add: H1_def H2_def)
  also have "... = ((\<not> $ok \<or> P) ;; J)"
    by (rel_auto)
  also have "... = (((\<not> $ok) ;; J) \<or> (P ;; J))"
    using seqr_or_distl by blast
  also have "... =  ((H2 (\<not> $ok)) \<or> H2(P))"
    by (simp add: H2_def)
  also have "... =  ((\<not> $ok) \<or> H2(P))"
    by (simp add: H2_not_okay)
  also have "... = H1(H2(P))"
    by (rel_auto)
  finally show ?thesis by simp
qed

subsection {* Designs as $H1$-$H2$ predicates *}

abbreviation H1_H2 :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<^bold>H") where
"H1_H2 P \<equiv> H1 (H2 P)"

lemma H1_H2_comp: "\<^bold>H = H1 \<circ> H2"
  by (auto)

theorem H1_H2_eq_design:
  "\<^bold>H(P) = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
proof -
  have "\<^bold>H(P) = ($ok \<Rightarrow> H2(P))"
    by (simp add: H1_def)
  also have "... = ($ok \<Rightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)))"
    by (metis H2_split)
  also have "... = ($ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> $ok \<and> P\<^sup>t)"
    by (rel_auto)
  also have "... = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
    by (rel_auto)
  finally show ?thesis .
qed

theorem H1_H2_is_design:
  assumes "P is H1" "P is H2"
  shows "P = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
  using assms by (metis H1_H2_eq_design Healthy_def)

theorem H1_H2_eq_rdesign:
  "\<^bold>H(P) = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
proof -
  have "\<^bold>H(P) = ($ok \<Rightarrow> H2(P))"
    by (simp add: H1_def Healthy_def')
  also have "... = ($ok \<Rightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)))"
    by (metis H2_split)
  also have "... = ($ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> P\<^sup>t)"
    by (pred_auto)
  also have "... = ($ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> $ok \<and> P\<^sup>t)"
    by (pred_auto)
  also have "... = ($ok \<and> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D \<Rightarrow> $ok\<acute> \<and> $ok \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>D)"
    by (simp add: ok_post ok_pre)
  also have "... = ($ok \<and> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D \<Rightarrow> $ok\<acute> \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>D)"
    by (pred_auto)
  also have "... =  pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
    by (simp add: rdesign_def design_def)
  finally show ?thesis .
qed

theorem H1_H2_is_rdesign:
  assumes "P is H1" "P is H2"
  shows "P = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
  by (metis H1_H2_eq_rdesign Healthy_def assms(1) assms(2))

lemma H1_H2_refinement:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "P \<sqsubseteq> Q \<longleftrightarrow> (`pre\<^sub>D(P) \<Rightarrow> pre\<^sub>D(Q)` \<and> `pre\<^sub>D(P) \<and> post\<^sub>D(Q) \<Rightarrow> post\<^sub>D(P)`)"
  by (metis H1_H2_eq_rdesign Healthy_if assms rdesign_refinement)

lemma H1_H2_refines:
  assumes "P is \<^bold>H" "Q is \<^bold>H" "P \<sqsubseteq> Q"
  shows "pre\<^sub>D(Q) \<sqsubseteq> pre\<^sub>D(P)" "post\<^sub>D(P) \<sqsubseteq> (pre\<^sub>D(P) \<and> post\<^sub>D(Q))"
  using H1_H2_refinement assms refBy_order by auto

lemma H1_H2_idempotent: "\<^bold>H (\<^bold>H P) = \<^bold>H P"
  by (simp add: H1_H2_commute H1_idem H2_idem)

lemma H1_H2_Idempotent [closure]: "Idempotent \<^bold>H"
  by (simp add: Idempotent_def H1_H2_idempotent)

lemma H1_H2_monotonic [closure]: "Monotonic \<^bold>H"
  by (simp add: H1_monotone H2_def mono_def seqr_mono)

lemma H1_H2_Continuous [closure]: "Continuous \<^bold>H"
  by (simp add: Continuous_comp H1_Continuous H1_H2_comp H2_Continuous)

lemma design_is_H1_H2 [closure]:
  "\<lbrakk> $ok\<acute> \<sharp> P; $ok\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> (P \<turnstile> Q) is \<^bold>H"
  by (simp add: H1_design H2_design Healthy_def')

lemma rdesign_is_H1_H2 [closure]:
  "(P \<turnstile>\<^sub>r Q) is \<^bold>H"
  by (simp add: Healthy_def H1_rdesign H2_rdesign)

lemma top_d_is_H1_H2 [closure]: "\<top>\<^sub>D is \<^bold>H"
  by (simp add: H1_def H2_not_okay Healthy_intro impl_alt_def)

lemma bot_d_is_H1_H2 [closure]: "\<bottom>\<^sub>D is \<^bold>H"
  by (simp add: bot_d_def closure unrest)

lemma seq_r_H1_H2_closed [closure]:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P ;; Q) is \<^bold>H"
proof -
  obtain P\<^sub>1 P\<^sub>2 where "P = P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(1))
  moreover obtain Q\<^sub>1 Q\<^sub>2 where "Q = Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2"
   by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(2))
  moreover have "((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) ;; (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) is \<^bold>H"
    by (simp add: rdesign_composition rdesign_is_H1_H2)
  ultimately show ?thesis by simp
qed

lemma H1_H2_left_unit: "P is \<^bold>H \<Longrightarrow> II\<^sub>D ;; P = P"
  by (metis H1_H2_eq_rdesign Healthy_def' rdesign_left_unit)

lemma UINF_H1_H2_closed [closure]:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Sqinter> A) is H1_H2"
proof -
  from assms have A: "A = H1_H2 ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Sqinter> ...) = (\<Sqinter> P \<in> A \<bullet> H1_H2(P))"
    by (simp add: UINF_as_Sup_collect)
  also have "... = (\<Sqinter> P \<in> A \<bullet> (\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (meson H1_H2_eq_design)
  also have "... = (\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f) \<turnstile> (\<Sqinter> P \<in> A \<bullet> P\<^sup>t)"
    by (simp add: design_UINF_mem assms)
  also have "... is H1_H2"
    by (simp add: design_is_H1_H2 unrest)
  finally show ?thesis .
qed

definition design_inf :: "('\<alpha>, '\<beta>) rel_des set \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<Sqinter>\<^sub>D_" [900] 900) where
"\<Sqinter>\<^sub>D A = (if (A = {}) then \<top>\<^sub>D else \<Sqinter> A)"

abbreviation design_sup :: "('\<alpha>, '\<beta>) rel_des set \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<Squnion>\<^sub>D_" [900] 900) where
"\<Squnion>\<^sub>D A \<equiv> \<Squnion> A"

lemma design_inf_H1_H2_closed:
  assumes "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Sqinter>\<^sub>D A) is \<^bold>H"
  apply (auto simp add: design_inf_def closure)
  apply (simp add: H1_def H2_not_okay Healthy_def impl_alt_def)
  apply (metis H1_def Healthy_def UINF_H1_H2_closed assms empty_iff impl_alt_def)
done

lemma design_sup_empty [simp]: "\<Sqinter>\<^sub>D {} = \<top>\<^sub>D"
  by (simp add: design_inf_def)

lemma design_sup_non_empty [simp]: "A \<noteq> {} \<Longrightarrow> \<Sqinter>\<^sub>D A = \<Sqinter> A"
  by (simp add: design_inf_def)

lemma USUP_mem_H1_H2_closed:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is \<^bold>H"
  shows "(\<Squnion> i\<in>A \<bullet> P i) is \<^bold>H"
proof -
  from assms have "(\<Squnion> i\<in>A \<bullet> P i) = (\<Squnion> i\<in>A \<bullet> \<^bold>H(P i))"
    by (auto intro: USUP_cong simp add: Healthy_def)
  also have "... = (\<Squnion> i\<in>A \<bullet> (\<not> (P i)\<^sup>f) \<turnstile> (P i)\<^sup>t)"
    by (meson H1_H2_eq_design)
  also have "... = (\<Sqinter> i\<in>A \<bullet> \<not> (P i)\<^sup>f) \<turnstile> (\<Squnion> i\<in>A \<bullet> \<not> (P i)\<^sup>f \<Rightarrow> (P i)\<^sup>t)"    
    by (simp add: design_USUP_mem)  
  also have "... is \<^bold>H"
    by (simp add: design_is_H1_H2 unrest)
  finally show ?thesis .
qed

lemma USUP_ind_H1_H2_closed:
  assumes "\<And> i. P i is \<^bold>H"
  shows "(\<Squnion> i \<bullet> P i) is \<^bold>H"
  using assms USUP_mem_H1_H2_closed[of UNIV P] by simp
  
lemma Inf_H1_H2_closed:
  assumes "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Squnion> A) is \<^bold>H"
proof -
  from assms have A: "A = \<^bold>H ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Squnion> ...) = (\<Squnion> P \<in> A \<bullet> \<^bold>H(P))"
    by (simp add: USUP_as_Inf_collect)
  also have "... = (\<Squnion> P \<in> A \<bullet> (\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (meson H1_H2_eq_design)
  also have "... = (\<Sqinter> P \<in> A \<bullet> \<not> P\<^sup>f) \<turnstile> (\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f \<Rightarrow> P\<^sup>t)"
    by (simp add: design_USUP_mem)
  also have "... is \<^bold>H"
    by (simp add: design_is_H1_H2 unrest)
  finally show ?thesis .
qed

lemma rdesign_ref_monos:
  assumes "P is \<^bold>H" "Q is \<^bold>H" "P \<sqsubseteq> Q"
  shows "pre\<^sub>D(Q) \<sqsubseteq> pre\<^sub>D(P)" "post\<^sub>D(P) \<sqsubseteq> (pre\<^sub>D(P) \<and> post\<^sub>D(Q))"
proof -
  have r: "P \<sqsubseteq> Q \<longleftrightarrow> (`pre\<^sub>D(P) \<Rightarrow> pre\<^sub>D(Q)` \<and> `pre\<^sub>D(P) \<and> post\<^sub>D(Q) \<Rightarrow> post\<^sub>D(P)`)"
    by (metis H1_H2_eq_rdesign Healthy_if assms(1) assms(2) rdesign_refinement)
  from r assms show "pre\<^sub>D(Q) \<sqsubseteq> pre\<^sub>D(P)"
    by (auto simp add: refBy_order)
  from r assms show "post\<^sub>D(P) \<sqsubseteq> (pre\<^sub>D(P) \<and> post\<^sub>D(Q))"
    by (auto simp add: refBy_order)
qed

subsection {* H3: The design assumption is a precondition *}

definition H3 :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" where
[upred_defs]: "H3 (P)  \<equiv>  P ;; II\<^sub>D"

theorem H3_idem:
  "H3(H3(P)) = H3(P)"
  by (metis H3_def design_skip_idem seqr_assoc)

theorem H3_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> H3(P) \<sqsubseteq> H3(Q)"
  by (simp add: H3_def seqr_mono)

theorem H3_Monotonic:
  "Monotonic H3"
  by (simp add: H3_mono mono_def)

theorem H3_Continuous: "Continuous H3"
  by (rel_auto)

theorem design_condition_is_H3:
  assumes "out\<alpha> \<sharp> p"
  shows "(p \<turnstile> Q) is H3"
proof -
  have "((p \<turnstile> Q) ;; II\<^sub>D) = (\<not> ((\<not> p) ;; true)) \<turnstile> (Q\<^sup>t ;; II\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: skip_d_alt_def design_composition_subst unrest assms)
  also have "... = p \<turnstile> (Q\<^sup>t ;; II\<lbrakk>true/$ok\<rbrakk>)"
    using assms precond_equiv seqr_true_lemma by force
  also have "... = p \<turnstile> Q"
    by (rel_auto)
  finally show ?thesis
    by (simp add: H3_def Healthy_def')
qed

theorem rdesign_H3_iff_pre:
  "P \<turnstile>\<^sub>r Q is H3 \<longleftrightarrow> P = (P ;; true)"
proof -
  have "(P \<turnstile>\<^sub>r Q) ;; II\<^sub>D = (P \<turnstile>\<^sub>r Q) ;; (true \<turnstile>\<^sub>r II)"
    by (simp add: skip_d_def)
  also have "... = (\<not> ((\<not> P) ;; true) \<and> \<not> (Q ;; (\<not> true))) \<turnstile>\<^sub>r (Q ;; II)"
    by (simp add: rdesign_composition)
  also have "... = (\<not> ((\<not> P) ;; true) \<and> \<not> (Q ;; (\<not> true))) \<turnstile>\<^sub>r Q"
    by simp
  also have "... = (\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r Q"
    by (pred_auto)
  finally have "P \<turnstile>\<^sub>r Q is H3 \<longleftrightarrow> P \<turnstile>\<^sub>r Q = (\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r Q"
    by (metis H3_def Healthy_def')
  also have "... \<longleftrightarrow> P = (\<not> ((\<not> P) ;; true))"
    by (metis rdesign_pre)
      thm seqr_true_lemma
  also have "... \<longleftrightarrow> P = (P ;; true)"
    by (simp add: seqr_true_lemma)
  finally show ?thesis .
qed

theorem design_H3_iff_pre:
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q"
  shows "P \<turnstile> Q is H3 \<longleftrightarrow> P = (P ;; true)"
proof -
  have "P \<turnstile> Q = \<lfloor>P\<rfloor>\<^sub>D \<turnstile>\<^sub>r \<lfloor>Q\<rfloor>\<^sub>D"
    by (simp add: assms lift_desr_inv rdesign_def)
  moreover hence "\<lfloor>P\<rfloor>\<^sub>D \<turnstile>\<^sub>r \<lfloor>Q\<rfloor>\<^sub>D is H3 \<longleftrightarrow> \<lfloor>P\<rfloor>\<^sub>D = (\<lfloor>P\<rfloor>\<^sub>D ;; true)"
    using rdesign_H3_iff_pre by blast
  ultimately show ?thesis
    by (metis assms(1,2) drop_desr_inv lift_desr_inv lift_dist_seq aext_true)
qed

theorem H1_H3_commute:
  "H1 (H3 P) = H3 (H1 P)"
  by (rel_auto)

lemma skip_d_absorb_J_1:
  "(II\<^sub>D ;; J) = II\<^sub>D"
  by (metis H2_def H2_rdesign skip_d_def)

lemma skip_d_absorb_J_2:
  "(J ;; II\<^sub>D) = II\<^sub>D"
proof -
  have "(J ;; II\<^sub>D) = (($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D) ;; (true \<turnstile> II)"
    by (simp add: J_def skip_d_alt_def)
  also have "... = (((($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>false/$ok\<acute>\<rbrakk> ;; (true \<turnstile> II)\<lbrakk>false/$ok\<rbrakk>)
                  \<or> ((($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (true \<turnstile> II)\<lbrakk>true/$ok\<rbrakk>))"
    by (rel_auto)
  also have "... = ((\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D ;; true) \<or> (\<lceil>II\<rceil>\<^sub>D ;; $ok\<acute> \<and> \<lceil>II\<rceil>\<^sub>D))"
    by (rel_auto)
  also have "... = II\<^sub>D"
    by (rel_auto)
  finally show ?thesis .
qed

lemma H2_H3_absorb:
  "H2 (H3 P) = H3 P"
  by (metis H2_def H3_def seqr_assoc skip_d_absorb_J_1)

lemma H3_H2_absorb:
  "H3 (H2 P) = H3 P"
  by (metis H2_def H3_def seqr_assoc skip_d_absorb_J_2)

theorem H2_H3_commute:
  "H2 (H3 P) = H3 (H2 P)"
  by (simp add: H2_H3_absorb H3_H2_absorb)

theorem H3_design_pre:
  assumes "$ok \<sharp> p" "out\<alpha> \<sharp> p" "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q"
  shows "H3(p \<turnstile> Q) = p \<turnstile> Q"
  using assms
  by (metis Healthy_def' design_H3_iff_pre precond_right_unit unrest_out\<alpha>_var ok_vwb_lens vwb_lens_mwb)

theorem H3_rdesign_pre:
  assumes "out\<alpha> \<sharp> p"
  shows "H3(p \<turnstile>\<^sub>r Q) = p \<turnstile>\<^sub>r Q"
  using assms
  by (simp add: H3_def)

theorem H3_ndesign: "H3(p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n Q)"
  by (simp add: H3_def ndesign_def unrest_pre_out\<alpha>)

theorem ndesign_is_H3 [closure]: "p \<turnstile>\<^sub>n Q is H3"
  by (simp add: H3_ndesign Healthy_def)

subsection {* Normal Designs as $H1$-$H3$ predicates *}

text \<open> A normal design~\cite{Guttman2010} refers only to initial state variables in the precondition. \<close>

abbreviation H1_H3 :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<^bold>N") where
"H1_H3 p \<equiv> H1 (H3 p)"

lemma H1_H3_comp: "H1_H3 = H1 \<circ> H3"
  by (auto)

theorem H1_H3_is_design:
  assumes "P is H1" "P is H3"
  shows "P = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
  by (metis H1_H2_eq_design H2_H3_absorb Healthy_def' assms(1) assms(2))

theorem H1_H3_is_rdesign:
  assumes "P is H1" "P is H3"
  shows "P = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
  by (metis H1_H2_is_rdesign H2_H3_absorb Healthy_def' assms)

theorem H1_H3_is_normal_design:
  assumes "P is H1" "P is H3"
  shows "P = \<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)"
  by (metis H1_H3_is_rdesign assms drop_pre_inv ndesign_def precond_equiv rdesign_H3_iff_pre)

lemma H1_H3_idempotent: "\<^bold>N (\<^bold>N P) = \<^bold>N P"
  by (simp add: H1_H3_commute H1_idem H3_idem)

lemma H1_H3_Idempotent [closure]: "Idempotent \<^bold>N"
  by (simp add: Idempotent_def H1_H3_idempotent)

lemma H1_H3_monotonic [closure]: "Monotonic \<^bold>N"
  by (simp add: H1_monotone H3_mono mono_def)

lemma H1_H3_Continuous [closure]: "Continuous \<^bold>N"
  by (simp add: Continuous_comp H1_Continuous H1_H3_comp H3_Continuous)

lemma H1_H3_intro:
  assumes "P is \<^bold>H" "out\<alpha> \<sharp> pre\<^sub>D(P)"
  shows "P is \<^bold>N"
  by (metis H1_H2_eq_rdesign H1_rdesign H3_rdesign_pre Healthy_def' assms)

lemma H1_H3_left_unit: "P is \<^bold>N \<Longrightarrow> II\<^sub>D ;; P = P"
  by (metis H1_H2_left_unit H1_H3_commute H2_H3_absorb H3_idem Healthy_def)
  
lemma H1_H3_right_unit: "P is \<^bold>N \<Longrightarrow> P ;; II\<^sub>D = P"
  by (metis H1_H3_commute H3_def H3_idem Healthy_def)

lemma H1_H3_top_left: "P is \<^bold>N \<Longrightarrow> \<top>\<^sub>D ;; P = \<top>\<^sub>D"
  by (metis H1_H2_eq_design H2_H3_absorb Healthy_if design_top_left_zero)
  
lemma H1_H3_bot_left: "P is \<^bold>N \<Longrightarrow> \<bottom>\<^sub>D ;; P = \<bottom>\<^sub>D"
  by (metis H1_idem H1_left_zero Healthy_def bot_d_true)

lemma H1_H3_impl_H2 [closure]: "P is \<^bold>N \<Longrightarrow> P is \<^bold>H"
  by (metis H1_H2_commute H1_idem H2_H3_absorb Healthy_def')

lemma H1_H3_eq_design_d_comp: "\<^bold>N(P) = ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t) ;; II\<^sub>D"
  by (metis H1_H2_eq_design H1_H3_commute H3_H2_absorb H3_def)

lemma H1_H3_eq_design: "\<^bold>N(P) = (\<not> (P\<^sup>f ;; true)) \<turnstile> P\<^sup>t"
  apply (simp add: H1_H3_eq_design_d_comp skip_d_alt_def)
  apply (subst design_composition_subst)
  apply (simp_all add: usubst unrest)
  apply (rel_auto)
done

lemma H3_unrest_out_alpha_nok [unrest]:
  assumes "P is \<^bold>N"
  shows "out\<alpha> \<sharp> P\<^sup>f"
proof -
  have "P = (\<not> (P\<^sup>f ;; true)) \<turnstile> P\<^sup>t"
    by (metis H1_H3_eq_design Healthy_def assms)
  also have "out\<alpha> \<sharp> (...\<^sup>f)"
    by (simp add: design_def usubst unrest, rel_auto)
  finally show ?thesis .
qed

lemma H3_unrest_out_alpha [unrest]: "P is \<^bold>N \<Longrightarrow> out\<alpha> \<sharp> pre\<^sub>D(P)"
  by (metis H1_H3_commute H1_H3_is_rdesign H1_idem Healthy_def' precond_equiv rdesign_H3_iff_pre)

lemma ndesign_H1_H3 [closure]: "p \<turnstile>\<^sub>n Q is \<^bold>N"
  by (simp add: H1_rdesign H3_def Healthy_def' ndesign_def unrest_pre_out\<alpha>)

lemma ndesign_form: "P is \<^bold>N \<Longrightarrow> (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) = P"
  by (metis H1_H2_eq_rdesign H1_H3_impl_H2 H3_unrest_out_alpha Healthy_def drop_pre_inv ndesign_def)

lemma des_bot_H1_H3 [closure]: "\<bottom>\<^sub>D is \<^bold>N"
  by (metis H1_design H3_def Healthy_def' design_false_pre design_true_left_zero skip_d_alt_def bot_d_def)

lemma des_top_is_H1_H3 [closure]: "\<top>\<^sub>D is \<^bold>N"
  by (metis ndesign_H1_H3 ndesign_miracle) 
    
lemma skip_d_is_H1_H3 [closure]: "II\<^sub>D is \<^bold>N"
  by (simp add: ndesign_H1_H3 skip_d_ndes_def)
    
lemma seq_r_H1_H3_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P ;; Q) is \<^bold>N"
  by (metis (no_types) H1_H2_eq_design H1_H3_eq_design_d_comp H1_H3_impl_H2 Healthy_def assms(1) assms(2) seq_r_H1_H2_closed seqr_assoc)
  
lemma dcond_H1_H2_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>D Q) is \<^bold>N"
  by (metis assms ndesign_H1_H3 ndesign_dcond ndesign_form)

lemma inf_H1_H2_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<sqinter> Q) is \<^bold>N"
  by (metis assms ndesign_H1_H3 ndesign_choice ndesign_form)

lemma sup_H1_H2_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<squnion> Q) is \<^bold>N"
  by (metis assms ndesign_H1_H3 ndesign_inf ndesign_form)
    
lemma ndes_seqr_miracle:
  assumes "P is \<^bold>N"
  shows "P ;; \<top>\<^sub>D = \<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n false"
proof -
  have "P ;; \<top>\<^sub>D = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) ;; (true \<turnstile>\<^sub>n false)"
    by (simp add: assms ndesign_form ndesign_miracle)
  also have "... = \<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<turnstile>\<^sub>n false"
    by (simp add: ndesign_composition_wp wp alpha)
  finally show ?thesis .
qed
    
lemma ndes_seqr_abort: 
  assumes "P is \<^bold>N"
  shows "P ;; \<bottom>\<^sub>D = (\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<and> post\<^sub>D P wp false) \<turnstile>\<^sub>n false"
proof -
  have "P ;; \<bottom>\<^sub>D = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) ;; (false \<turnstile>\<^sub>n false)"
    by (simp add: assms bot_d_true ndesign_false_pre ndesign_form)
  also have "... = (\<lfloor>pre\<^sub>D P\<rfloor>\<^sub>< \<and> post\<^sub>D P wp false) \<turnstile>\<^sub>n false"
    by (simp add: ndesign_composition_wp alpha)
  finally show ?thesis .
qed

lemma USUP_ind_H1_H3_closed [closure]:
  "\<lbrakk> \<And> i. P i is \<^bold>N \<rbrakk> \<Longrightarrow> (\<Squnion> i \<bullet> P i) is \<^bold>N"
  by (rule H1_H3_intro, simp_all add: H1_H3_impl_H2 USUP_ind_H1_H2_closed preD_USUP_ind unrest)

subsection {* H4: Feasibility *}

definition H4 :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" where
[upred_defs]: "H4(P) = ((P;;true) \<Rightarrow> P)"

theorem H4_idem:
  "H4(H4(P)) = H4(P)"
  by (rel_auto)

lemma is_H4_alt_def:
  "P is H4 \<longleftrightarrow> (P ;; true) = true"
  by (rel_blast)

end