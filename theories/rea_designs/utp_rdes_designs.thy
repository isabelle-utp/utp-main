section \<open> Reactive Design Specifications \<close>

theory utp_rdes_designs
  imports utp_rdes_healths
begin

subsection \<open> Reactive design forms \<close>

lemma srdes_skip_def: "II\<^sub>R = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R))"
  apply (rel_auto) using minus_zero_eq by blast+

lemma Chaos_def: "Chaos = \<^bold>R\<^sub>s(false \<turnstile> true)"
proof -
  have "Chaos = SRD(true)"
    by (metis srdes_theory.healthy_bottom)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(true))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(false \<turnstile> true)"
    by (metis H1_design H2_true design_false_pre)
  finally show ?thesis .
qed

lemma Miracle_def: "Miracle = \<^bold>R\<^sub>s(true \<turnstile> false)"
proof -
  have "Miracle = SRD(false)"
    by (metis srdes_theory.healthy_top)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(false))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (metis (no_types, lifting) H1_H2_eq_design p_imp_p subst_impl subst_not utp_pred_laws.compl_bot_eq utp_pred_laws.compl_top_eq)
  finally show ?thesis .
qed

lemma RD1_reactive_design: "RD1(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by (rel_auto)

lemma RD2_reactive_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "RD2(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RH_commute RD2_def)

lemma RD1_st_reactive_design: "RD1(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma RD2_st_reactive_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "RD2(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RHS_commute RD2_def)

lemma wait_false_design:
  "(P \<turnstile> Q) \<^sub>f = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by (rel_auto)

lemma RD_RH_design_form:
  "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "RD(P) = RD1(RD2(R1(R2c(R3c(P)))))"
    by (simp add: RD_alt_def RH_def)
  also have "... = RD1(H2(R1(R2s(R3c(P)))))"
    by (simp add: R1_R2s_R2c RD2_def)
  also have "... = RD1(R1(H2(R2s(R3c(P)))))"
    by (simp add: R1_H2_commute)
  also have "... = R1(H1(R1(H2(R2s(R3c(P))))))"
    by (simp add: R1_idem RD1_via_R1)
  also have "... = R1(H1(H2(R2s(R3c(R1(P))))))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R2s_R2c R1_R3c_commute RD1_via_R1)
  also have "... = R1(R2s(H1(H2(R3c(R1(P))))))"
    by (simp add: R2s_H1_commute R2s_H2_commute)
  also have "... = R1(R2s(H1(R3c(H2(R1(P))))))"
    by (metis RD2_R3c_commute RD2_def)
  also have "... = R2(R1(H1(R3c(H2(R1(P))))))"
    by (metis R1_R2_commute R1_idem R2_def)
  also have "... = R2(R3c(R1(\<^bold>H(R1(P)))))"
    by (simp add: R1_R3c_commute RD1_R3c_commute RD1_via_R1)
  also have "... = RH(\<^bold>H(R1(P)))"
    by (metis R1_R2s_R2c R1_R3c_commute R2_R1_form RH_def)
  also have "... = RH(\<^bold>H(P))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R3c_commute R1_idem RD1_via_R1 RH_def)
  also have "... = RH((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis (no_types, lifting) R3c_subst_wait RH_def subst_not wait_false_design)
  finally show ?thesis .
qed

lemma RD_reactive_design:
  assumes "P is RD"
  shows "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis RD_RH_design_form Healthy_def' assms)

lemma RD_RH_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "RD(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by (simp add: RD1_reactive_design RD2_reactive_design RD_alt_def RH_idem assms(1) assms(2))

lemma RH_design_is_RD:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "\<^bold>R(P \<turnstile> Q) is RD"
  by (simp add: RD_RH_design Healthy_def' assms(1) assms(2))

lemma SRD_RH_design_form:
  "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "SRD(P) = R1(R2c(R3h(RD1(RD2(R1(P))))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_commute R1_R3h_commute R1_idem R2c_H2_commute RD1_R1_commute RD1_R2c_commute RD1_R3h_commute RD2_R3h_commute RD2_def RHS_def SRD_def)
  also have "... = R1(R2s(R3h(\<^bold>H(P))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_is_R2 R1_R3h_commute R2_R1_form RD1_via_R1 RD2_def)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(P))"
    by (simp add: R1_R2s_R2c RHS_def)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis (no_types, lifting) R3h_subst_wait RHS_def subst_not wait_false_design)
  finally show ?thesis .
qed

lemma SRD_reactive_design:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis SRD_RH_design_form Healthy_def' assms)

lemma SRD_RH_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "SRD(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (simp add: RD1_st_reactive_design RD2_st_reactive_design RHS_idem SRD_def assms(1) assms(2))

lemma RHS_design_is_SRD:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q) is SRD"
  by (simp add: Healthy_def' SRD_RH_design assms(1) assms(2))

lemma SRD_RHS_H1_H2: "SRD(P) = \<^bold>R\<^sub>s(\<^bold>H(P))"
  by (metis (no_types, lifting) H1_H2_eq_design R3h_subst_wait RHS_def SRD_RH_design_form subst_not wait_false_design)

subsection \<open> Auxiliary healthiness conditions \<close>

definition [upred_defs]: "R3c_pre(P) = (true \<triangleleft> $wait \<triangleright> P)"

definition [upred_defs]: "R3c_post(P) = (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> P)"

definition [upred_defs]: "R3h_post(P) = ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> P)"

lemma R3c_pre_conj: "R3c_pre(P \<and> Q) = (R3c_pre(P) \<and> R3c_pre(Q))"
  by (rel_auto)

lemma R3c_pre_seq:
  "(true ;; Q) = true \<Longrightarrow> R3c_pre(P ;; Q) = (R3c_pre(P) ;; Q)"
  by (rel_auto)

lemma unrest_ok_R3c_pre [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok'_R3c_pre [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok_R3c_post [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma unrest_ok_R3c_post' [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma unrest_ok_R3h_post [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3h_post(P)"
  by (simp add: R3h_post_def cond_def unrest)

lemma unrest_ok_R3h_post' [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3h_post(P)"
  by (simp add: R3h_post_def cond_def unrest)

subsection \<open> Composition laws \<close>

theorem R1_design_composition:
  fixes P Q :: "('t::trace,'\<alpha>,'\<beta>) rel_rp"
  and R S :: "('t,'\<beta>,'\<gamma>) rel_rp"
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) =
   R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
proof -
  have "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = ((R1 (P \<turnstile> Q))\<^sup>t ;; R1 (R \<turnstile> S)\<lbrakk>true/$ok\<rbrakk> \<or> (R1 (P \<turnstile> Q))\<^sup>f ;; R1 (R \<turnstile> S)\<lbrakk>false/$ok\<rbrakk>)"
    by (rule seqr_bool_split[of ok], simp)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> (true \<and> Q)) ;; R1((true \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (R1(($ok \<and> P) \<Rightarrow> (false \<and> Q)) ;; R1((false \<and> R) \<Rightarrow> ($ok\<acute> \<and> S))))"
    by (simp add: design_def usubst R1_def)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> Q) ;; R1(R \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (R1(\<not> ($ok \<and> P)) ;; R1(true)))"
    by simp
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P \<or> Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                             \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: impl_alt_def utp_pred_laws.sup.assoc)
  also from assms have "... = (((R1(\<not> $ok \<or> \<not> P) \<or> R1(Q)) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj utp_pred_laws.disj_assoc)
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distl utp_pred_laws.sup.assoc)
  also from assms have "... = ((R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (rel_blast)
  also from assms have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_extend_conj utp_pred_laws.inf_commute)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                  \<or> ((R1(\<not> $ok) :: ('t,'\<alpha>,'\<beta>) rel_rp) ;; R1(true))
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj seqr_or_distl)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                  \<or> (R1(\<not> $ok))
                  \<or> (R1(\<not> P) ;; R1(true)))"
  proof -
    have "((R1(\<not> $ok) :: ('t,'\<alpha>,'\<beta>) rel_rp) ;; R1(true)) =
           (R1(\<not> $ok) :: ('t,'\<alpha>,'\<gamma>) rel_rp)"
      by (rel_auto)
    thus ?thesis
      by simp
  qed
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> (R1(S \<and> $ok\<acute>))))
                  \<or> R1(\<not> $ok)
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_extend_conj)
  also have "... = ( (R1(Q) ;; (R1 (\<not> R)))
                   \<or> (R1(Q) ;; (R1(S \<and> $ok\<acute>)))
                   \<or> R1(\<not> $ok)
                   \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distr utp_pred_laws.sup.assoc)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> (R1(Q) ;; (R1(S \<and> $ok\<acute>)))
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_seqr)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> ((R1(Q) ;; R1(S)) \<and> $ok\<acute>)
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (rel_blast)
  also have "... = R1(\<not>($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                     \<or>  ((R1(Q) ;; R1(S)) \<and> $ok\<acute>))"
    by (rel_blast)
  also have "... = R1(($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                      \<Rightarrow> ($ok\<acute> \<and> (R1(Q) ;; R1(S))))"
    by (simp add: impl_alt_def utp_pred_laws.inf_commute)
  also have "... = R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
    by (simp add: design_def)
  finally show ?thesis .
qed

theorem R1_design_composition_RR:
  assumes "P is RR" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  apply (subst R1_design_composition)
  apply (simp_all add: assms unrest wp_rea_def Healthy_if closure)
  apply (rel_auto)
done

theorem R1_design_composition_RC:
  assumes "P is RC" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1((P \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  by (simp add: R1_design_composition_RR assms unrest Healthy_if closure wp)

lemma R2s_design: "R2s(P \<turnstile> Q) = (R2s(P) \<turnstile> R2s(Q))"
  by (simp add: R2s_def design_def usubst)

lemma R2c_design: "R2c(P \<turnstile> Q) = (R2c(P) \<turnstile> R2c(Q))"
  by (simp add: design_def impl_alt_def R2c_disj R2c_not R2c_ok R2c_and R2c_ok')

lemma R1_R3c_design:
  "R1(R3c(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by (rel_auto)

lemma R1_R3h_design:
  "R1(R3h(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3h_post(Q))"
  by (rel_auto)

lemma R3c_R1_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R3c(R1(P \<turnstile> Q)) ;; R3c(R1(R \<turnstile> S))) =
       R3c(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> $wait\<acute>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
    by (rel_auto)
  have 2:"(\<not> (R1 (R3c_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> $wait\<acute>) ;; R1 (\<not> R)))"
    by (rel_auto, blast+)
  have 3:"(R1 (R3c_post Q) ;; R1 (R3c_post S)) = R3c_post (R1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 S))"
    by (rel_auto)
  show ?thesis
    apply (simp add: R3c_semir_form R1_R3c_commute[THEN sym] R1_R3c_design unrest )
    apply (subst R1_design_composition)
        apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
    done
qed

lemma R3h_R1_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R3h(R1(P \<turnstile> Q)) ;; R3h(R1(R \<turnstile> S))) =
       R3h(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> $wait\<acute>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
   by (rel_auto)
  have 2:"(\<not> (R1 (R3h_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> $wait\<acute>) ;; R1 (\<not> R)))"
    by (rel_auto, blast+)
  have 3:"(R1 (R3h_post Q) ;; R1 (R3h_post S)) = R3h_post (R1 Q ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 S))"
    by (rel_auto, blast+)
  show ?thesis
    apply (simp add: R3h_semir_form R1_R3h_commute[THEN sym] R1_R3h_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma R2_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R2(P \<turnstile> Q) ;; R2(R \<turnstile> S)) =
       R2((\<not> (R1 (\<not> R2c P) ;; R1 true) \<and> \<not> (R1 (R2c Q) ;; R1 (\<not> R2c R))) \<turnstile> (R1 (R2c Q) ;; R1 (R2c S)))"
  apply (simp add: R2_R2c_def R2c_design R1_design_composition assms unrest R2c_not R2c_and R2c_disj R1_R2c_commute[THEN sym] R2c_idem R2c_R1_seq)
  apply (metis (no_types, lifting) R2c_R1_seq R2c_not R2c_true)
done

lemma RH_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(RH(P \<turnstile> Q) ;; RH(R \<turnstile> S)) =
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> $wait\<acute>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (rel_auto)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
  proof -
    have "((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (rel_auto)
    hence "R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (metis R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
      by (rel_auto)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))) = (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)) =
            R2c(R1 (R2s (Q\<lbrakk>true/$wait\<acute>\<rbrakk>)) ;; \<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>)"
        by (simp add: usubst cond_unit_T R1_def R2s_def)
      also have "... = R2c(R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        by (metis R2_def R2_des_lift_skip R2_subst_wait_true)
      also have "... = (R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
        apply (simp add: usubst R2_des_lift_skip)
        apply (metis R2_def R2_des_lift_skip R2_subst_wait'_true R2_subst_wait_true)
        done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>)"
      by (simp add: usubst cond_unit_F)
         (metis (no_types, hide_lams) R1_wait'_false R1_wait_false R2_def R2_subst_wait'_false R2_subst_wait_false R2c_seq)
    ultimately show ?thesis
    proof -
      have "\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S) = R2 (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> S)"
        by (simp add: R1_R2c_is_R2 R1_R2s_R2c R2_condr' R2_des_lift_skip R2s_wait)
      then show ?thesis
        by (simp add: R1_R2c_is_R2 R1_R2s_R2c R2c_seq)
    qed
  qed

  have "(R1(R2s(R3c(P \<turnstile> Q))) ;; R1(R2s(R3c(R \<turnstile> S)))) =
        ((R3c(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3c(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, hide_lams) R1_R2s_R2c R1_R3c_commute R2c_R3c_commute R2s_design)
  also have "... = R3c (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))))"
    by (simp add: R3c_R1_design_composition assms unrest)
  also have "... = R3c(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3c_commute R2c_R3c_commute RH_def)
qed

lemma RHS_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> $wait\<acute>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (rel_auto, blast)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
  proof -
    have "((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (rel_auto, blast+)
    hence "R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (metis (no_types, lifting) R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
      by (rel_auto, blast+)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))) =
          (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)) =
            R2c(R1 (R2s (Q\<lbrakk>true/$wait\<acute>\<rbrakk>)) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>)"
        by (simp add: usubst cond_unit_T R1_def R2s_def)
      also have "... = R2c(R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>))"
        by (metis (no_types, lifting) R2_def R2_des_lift_skip R2_subst_wait_true R2_st_ex)
      also have "... = (R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
        apply (simp add: usubst R2_des_lift_skip)
        apply (metis (no_types) R2_def R2_des_lift_skip R2_st_ex R2_subst_wait'_true R2_subst_wait_true)
      done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>)"
      by (simp add: usubst)
         (metis (no_types, lifting) R1_wait'_false R1_wait_false R2_R1_form R2_subst_wait'_false R2_subst_wait_false R2c_seq)
    ultimately show ?thesis
      by (smt R2_R1_form R2_condr' R2_des_lift_skip R2_st_ex R2c_seq R2s_wait)
  qed

  have "(R1(R2s(R3h(P \<turnstile> Q))) ;; R1(R2s(R3h(R \<turnstile> S)))) =
        ((R3h(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3h(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, hide_lams) R1_R2s_R2c R1_R3h_commute R2c_R3h_commute R2s_design)
  also have "... = R3h (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))))"
    by (simp add: R3h_R1_design_composition assms unrest)
  also have "... = R3h(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3h_commute R2c_R3h_commute RHS_def)
qed

lemma RHS_R2s_design_composition:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
    "P is R2s" "Q is R2s" "R is R2s" "S is R2s"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> P) ;; R1 true) \<and> \<not> ((R1 Q \<and> \<not> $wait\<acute>) ;; R1 (\<not> R))) \<turnstile>
                       (R1 Q ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 S)))"
proof -
  have f1: "R2s P = P"
    by (meson Healthy_def assms(5))
  have f2: "R2s Q = Q"
    by (meson Healthy_def assms(6))
  have f3: "R2s R = R"
    by (meson Healthy_def assms(7))
  have "R2s S = S"
    by (meson Healthy_def assms(8))
  then show ?thesis
    using f3 f2 f1 by (simp add: RHS_design_composition assms(1) assms(2) assms(3) assms(4))
qed

lemma RH_design_export_R1: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R1(Q))"
  by (rel_auto)

lemma RH_design_export_R2s: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2s(Q))"
  by (rel_auto)

lemma RH_design_export_R2c: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2c(Q))"
  by (rel_auto)

lemma RHS_design_export_R1: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R1(Q))"
  by (rel_auto)

lemma RHS_design_export_R2s: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2s(Q))"
  by (rel_auto)

lemma RHS_design_export_R2c: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2c(Q))"
  by (rel_auto)

lemma RHS_design_export_R2: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2(Q))"
  by (rel_auto)

lemma R1_design_R1_pre: 
  "\<^bold>R\<^sub>s(R1(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma RHS_design_ok_wait: "\<^bold>R\<^sub>s(P\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<lbrakk>true,false/$ok,$wait\<rbrakk>) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma RHS_design_neg_R1_pre:
  "\<^bold>R\<^sub>s ((\<not> R1 P) \<turnstile> R) = \<^bold>R\<^sub>s ((\<not> P) \<turnstile> R)"
  by (rel_auto)

lemma RHS_design_conj_neg_R1_pre:
  "\<^bold>R\<^sub>s (((\<not> R1 P) \<and> Q) \<turnstile> R) = \<^bold>R\<^sub>s (((\<not> P) \<and> Q) \<turnstile> R)"
  by (rel_auto)

lemma RHS_pre_lemma: "(\<^bold>R\<^sub>s P)\<^sup>f\<^sub>f = R1(R2c(P\<^sup>f\<^sub>f))"
  by (rel_auto)

lemma RHS_design_R2c_pre:
  "\<^bold>R\<^sub>s(R2c(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

subsection \<open> Refinement introduction laws \<close>

lemma R1_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "$ok \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>1" "$ok \<sharp> P\<^sub>2" "$ok\<acute> \<sharp> P\<^sub>2"
    "$ok \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok \<sharp> Q\<^sub>2" "$ok\<acute> \<sharp> Q\<^sub>2"    
  shows "R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> P\<^sub>2`"
proof -
  have "R1((\<exists> $ok;$ok\<acute> \<bullet> P\<^sub>1) \<turnstile> (\<exists> $ok;$ok\<acute> \<bullet> P\<^sub>2)) \<sqsubseteq> R1((\<exists> $ok;$ok\<acute> \<bullet> Q\<^sub>1) \<turnstile> (\<exists> $ok;$ok\<acute> \<bullet> Q\<^sub>2)) 
       \<longleftrightarrow> `R1(\<exists> $ok;$ok\<acute> \<bullet> P\<^sub>1) \<Rightarrow> R1(\<exists> $ok;$ok\<acute> \<bullet> Q\<^sub>1)` \<and> `R1(\<exists> $ok;$ok\<acute> \<bullet> P\<^sub>1) \<and> R1(\<exists> $ok;$ok\<acute> \<bullet> Q\<^sub>2) \<Rightarrow> R1(\<exists> $ok;$ok\<acute> \<bullet> P\<^sub>2)`"
    by (rel_auto, meson+)
  thus ?thesis
    by (simp_all add: ex_unrest ex_plus Healthy_if assms)
qed

lemma R1_design_refine_RR:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR"
  shows "R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> P\<^sub>2`"
  by (simp add: R1_design_refine assms unrest closure)
    
lemma RHS_design_refine:
  assumes 
    "P\<^sub>1 is R1" "P\<^sub>2 is R1" "Q\<^sub>1 is R1" "Q\<^sub>2 is R1"
    "P\<^sub>1 is R2c" "P\<^sub>2 is R2c" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R2c"
    "$ok \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>1" "$ok \<sharp> P\<^sub>2" "$ok\<acute> \<sharp> P\<^sub>2"
    "$ok \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok \<sharp> Q\<^sub>2" "$ok\<acute> \<sharp> Q\<^sub>2"    
    "$wait \<sharp> P\<^sub>1" "$wait \<sharp> P\<^sub>2" "$wait \<sharp> Q\<^sub>1" "$wait \<sharp> Q\<^sub>2"    
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> P\<^sub>2`"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) \<longleftrightarrow> R1(R3h(R2c(P\<^sub>1 \<turnstile> P\<^sub>2))) \<sqsubseteq> R1(R3h(R2c(Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp add: R2c_R3h_commute RHS_def)
  also have "... \<longleftrightarrow> R1(R3h(P\<^sub>1 \<turnstile> P\<^sub>2)) \<sqsubseteq> R1(R3h(Q\<^sub>1 \<turnstile> Q\<^sub>2))"
    by (simp add: Healthy_if R2c_design assms)
  also have "... \<longleftrightarrow> R1(R3h(P\<^sub>1 \<turnstile> P\<^sub>2))\<lbrakk>false/$wait\<rbrakk> \<sqsubseteq> R1(R3h(Q\<^sub>1 \<turnstile> Q\<^sub>2))\<lbrakk>false/$wait\<rbrakk>"
    by (rel_auto, metis+)
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2)\<lbrakk>false/$wait\<rbrakk> \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)\<lbrakk>false/$wait\<rbrakk>"      
    by (rel_auto)
  also have "... \<longleftrightarrow> R1(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqsubseteq> R1(Q\<^sub>1 \<turnstile> Q\<^sub>2)"      
    by (simp add: usubst assms closure unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> P\<^sub>2`"
    by (simp add: R1_design_refine assms)
  finally show ?thesis .
qed 

lemma srdes_refine_intro:
  assumes "`P\<^sub>1 \<Rightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> Q\<^sub>1`"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2)"
  by (simp add: RHS_mono assms design_refine_intro)

subsection \<open> Distribution laws \<close>

lemma RHS_design_choice: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqinter> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<or> Q\<^sub>2))"
  by (metis RHS_inf design_choice)
    
lemma RHS_design_sup: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<squnion> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<or> P\<^sub>2) \<turnstile> ((P\<^sub>1 \<Rightarrow> Q\<^sub>1) \<and> (P\<^sub>2 \<Rightarrow> Q\<^sub>2)))"
  by (metis RHS_sup design_inf)

lemma RHS_design_USUP:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion> i \<in> A \<bullet> P(i)) \<turnstile> (\<Sqinter> i \<in> A \<bullet> Q(i)))"
  by (subst RHS_INF[OF assms, THEN sym], simp add: design_UINF_mem assms)

end