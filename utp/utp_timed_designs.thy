theory utp_timed_designs
imports utp_rea_designs
begin

type_synonym '\<alpha> alphabet_td = "(nat, '\<alpha>) alphabet_rp"

abbreviation time :: "nat \<Longrightarrow> '\<alpha> alphabet_td" where
"time \<equiv> tr"

definition "Instant(P) = R2((\<not> P\<^sup>f) \<turnstile> ($time\<acute> =\<^sub>u $time \<and> (\<exists> $time\<acute> \<bullet> P\<^sup>t)))"

definition "Wait(n) = R2(true \<turnstile> ($time\<acute> =\<^sub>u $time + \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"

definition "Override(n)(P) = (Wait(n) ;; Instant(P))"

definition "Deadline(n)(P) = (R2((\<not> P\<^sup>f) \<turnstile> (P\<^sup>t \<and> $time\<acute> - $time \<le>\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub><)))"

lemma R2_ok_true [usubst]: "(R2 P)\<^sup>t = R2(P\<^sup>t)"
  by (simp add: R1_def R2_def R2s_def usubst)

lemma R2_ok_false [usubst]: "(R2 P)\<^sup>f = R2(P\<^sup>f)"
  by (simp add: R1_def R2_def R2s_def usubst)

lemma R2_design_R2_pre: "R2(R2(P) \<turnstile> Q) = R2(P \<turnstile> Q)"
  by (rel_auto)

lemma R2_design_R2_neg_pre: "R2((\<not> R2(\<not> P)) \<turnstile> Q) = R2(P \<turnstile> Q)"
  by (rel_auto)

lemma R2_design_R2_post: "R2(P \<turnstile> R2(Q)) = R2(P \<turnstile> Q)"
  by (rel_auto)

lemma R2_design_pre_R2:
  "R2((\<not> (R2(P \<turnstile> Q))\<^sup>f) \<turnstile> R) = R2(P\<^sup>f \<turnstile> R)"
proof -
  have 1:"(\<not> $ok \<or> \<not> P\<^sup>f) \<turnstile> R = (\<not> P\<^sup>f) \<turnstile> R"
    by (rel_auto)
  have "R2((\<not> (R2(P \<turnstile> Q))\<^sup>f) \<turnstile> R) = R2 ((\<not> R2 (\<not> ($ok \<and> P\<^sup>f))) \<turnstile> R)"
    by (simp add: R2_ok_false design_npre R2_design_R2_pre 1)
  also have "... = R2 (($ok \<and> P\<^sup>f) \<turnstile> R)"
    by (simp only: R2_design_R2_neg_pre)
  also have "... = R2 (P\<^sup>f \<turnstile> R)"
    by (rel_auto)
  finally show ?thesis .
qed

lemma R2_design_post_R2:
  "R2(P \<turnstile> (R2(P \<turnstile> Q))\<^sup>t) = R2(P \<turnstile> Q)"
proof -
  have "P \<turnstile> ($ok \<and> P\<^sup>t \<Rightarrow> Q\<^sup>t) = P \<turnstile> (P\<^sup>t \<Rightarrow> Q\<^sup>t)"
    by (rel_auto)
  also have "... = P \<turnstile> (P \<Rightarrow> Q)"
    by (metis design_subst_ok' subst_impl)
  also have "... = P \<turnstile> Q"
    by (rel_auto)
  finally show ?thesis
    by (simp add: R2_ok_true design_post R2_design_R2_post design_export_ok[THEN sym])
qed

lemma unrest_ok_R2 [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2(P)"
  by (simp add: R2_def unrest)

lemma unrest_ok'_R2 [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2(P)"
  by (simp add: R2_def unrest)

definition tskip :: "_" ("II\<^sub>T") where
[upred_defs]: "tskip = R2(true \<turnstile> ($time\<acute> =\<^sub>u $time \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"

lemma R1_time_advance: "R1 ($time\<acute> =\<^sub>u $time + \<lceil>m\<rceil>\<^sub>R\<^sub><) = ($time\<acute> =\<^sub>u $time + \<lceil>m\<rceil>\<^sub>R\<^sub><)"
  by (rel_auto)

lemma R2c_time_advance: "R2c ($time\<acute> =\<^sub>u $time + \<lceil>m\<rceil>\<^sub>R\<^sub><) = ($time\<acute> =\<^sub>u $time + \<lceil>m\<rceil>\<^sub>R\<^sub><)"
  by (rel_auto)

lemma R2c_alpha_ident: "R2c ($\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) = ($\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
  by (rel_auto)

lemma Wait_m_plus_n:
  "(Wait m ;; Wait n) = Wait (m + n)"
proof -
  have "($time\<acute> =\<^sub>u $time + \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;; $time\<acute> =\<^sub>u $time + \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) = ($time\<acute> =\<^sub>u $time + \<lceil>m + n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
    by (rel_auto, metis (no_types, hide_lams) add.assoc alpha_d.select_convs(2) alpha_rp'.select_convs(2) alpha_rp'.select_convs(3))
  thus ?thesis
    by (simp add: Wait_def R2_design_composition unrest R2c_true R2c_and R1_false R1_time_advance R2c_time_advance R1_extend_conj R2c_alpha_ident)
qed

lemma Instant_Wait: "Instant(Wait(n)) = II\<^sub>T"
proof -
  have "Instant(Wait(n)) = R2 (true \<turnstile> ($time\<acute> =\<^sub>u $time \<and> (\<exists> $time\<acute> \<bullet> R2 (true \<turnstile> ($time\<acute> =\<^sub>u $time + \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))\<^sup>t)))"
    by (simp add: Instant_def Wait_def R2_design_pre_R2 R2_design_post_R2, simp add: usubst)
  also have "... = R2 (true \<turnstile> ($time\<acute> =\<^sub>u $time \<and> (\<exists> $time\<acute> \<bullet> $time\<acute> =\<^sub>u $time + \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)))"
    by (rel_auto)
  also have "... = R2 (true \<turnstile> ($time\<acute> =\<^sub>u $time \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
    by (rel_auto)
  also have "... = II\<^sub>T"
    by (simp add: tskip_def)
  finally show ?thesis .
qed
end