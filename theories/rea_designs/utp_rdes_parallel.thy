section {* Reactive design parallel-by-merge *}

theory utp_rdes_parallel
  imports 
    utp_rdes_normal 
    utp_rdes_tactics
begin

text {* R3h implicitly depends on RD1, and therefore it requires that both sides be RD1. We also
  require that both sides are R3c, and that @{term "wait\<^sub>m"} is a quasi-unit, and @{term "div\<^sub>m"} yields
  divergence. *}

lemma st_U0_alpha: "\<lceil>\<exists> $st \<bullet> II\<rceil>\<^sub>0 = (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>0)"
  by (rel_auto)

lemma st_U1_alpha: "\<lceil>\<exists> $st \<bullet> II\<rceil>\<^sub>1 = (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>1)"
  by (rel_auto)

definition skip_rm :: "('s,'t::trace,'\<alpha>) rsp merge" ("II\<^sub>R\<^sub>M") where
  [upred_defs]: "II\<^sub>R\<^sub>M = (\<exists> $st\<^sub>< \<bullet> skip\<^sub>m \<or> (\<not> $ok\<^sub>< \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>))"

definition [upred_defs]: "R3hm(M) = (II\<^sub>R\<^sub>M \<triangleleft> $wait\<^sub>< \<triangleright> M)"

lemma R3hm_idem: "R3hm(R3hm(P)) = R3hm(P)"
  by (rel_auto)

lemma R3h_par_by_merge [closure]:
  assumes "P is R3h" "Q is R3h" "M is R3hm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3h"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true/$ok\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: cond_idem cond_var_subst_left cond_var_subst_right)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false,true/$ok,$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = (((\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false,true/$ok,$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; R3hm(M))\<lbrakk>true,true/$ok,$wait\<rbrakk>"
      by (simp add: par_by_merge_def U0_as_alpha U1_as_alpha assms Healthy_if)
    also have "... = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (\<exists> $st\<^sub>< \<bullet> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v\<^sub><))\<lbrakk>true,true/$ok,$wait\<rbrakk>"
      by (rel_blast)
    also have "... = ((\<lceil>R3h(P)\<rceil>\<^sub>0 \<and> \<lceil>R3h(Q)\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (\<exists> $st\<^sub>< \<bullet> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v\<^sub><))\<lbrakk>true,true/$ok,$wait\<rbrakk>"
      by (simp add: assms Healthy_if)
    also have "... = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
      by (rel_auto)
    finally show ?thesis by simp
  qed
  also have "... = (((\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (R1(true))\<lbrakk>false,true/$ok,$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false,true/$ok,$wait\<rbrakk> = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; R3hm(M))\<lbrakk>false,true/$ok,$wait\<rbrakk>"
      by (simp add: par_by_merge_def U0_as_alpha U1_as_alpha assms Healthy_if)
    also have "... = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; ($tr\<^sub>< \<le>\<^sub>u $tr\<acute>))\<lbrakk>false,true/$ok,$wait\<rbrakk>"
      by (rel_blast)
    also have "... = ((\<lceil>R3h(P)\<rceil>\<^sub>0 \<and> \<lceil>R3h(Q)\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; ($tr\<^sub>< \<le>\<^sub>u $tr\<acute>))\<lbrakk>false,true/$ok,$wait\<rbrakk>"
      by (simp add: assms Healthy_if)
    also have "... = (R1(true))\<lbrakk>false,true/$ok,$wait\<rbrakk>"
      by (rel_blast)
    finally show ?thesis by simp
  qed
  also have "... = (((\<exists> $st \<bullet> II) \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = R3h(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3h_cases)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

definition [upred_defs]: "RD1m(M) = (M \<or> \<not> $ok\<^sub>< \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>)"

lemma RD1_par_by_merge [closure]:
  assumes "P is R1" "Q is R1" "M is R1m" "P is RD1" "Q is RD1" "M is RD1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD1"
proof -
  have 1: "(RD1(R1(P)) \<parallel>\<^bsub>RD1m(R1m(M))\<^esub> RD1(R1(Q)))\<lbrakk>false/$ok\<rbrakk> = R1(true)"
    by (rel_blast)
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true/$ok\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>"
    by (simp add: cond_var_split)
  also have "... = R1(P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok \<triangleright> R1(true)"
    by (metis "1" Healthy_if R1_par_by_merge assms calculation
              cond_idem cond_var_subst_right in_var_uvar ok_vwb_lens)
  also have "... = RD1(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: Healthy_if R1_par_by_merge RD1_alt_def assms(3))
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma RD2_par_by_merge [closure]:
  assumes "M is RD2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD2"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^sub>s Q) ;; M)"
    by (simp add: par_by_merge_def)
  also from assms have "... = ((P \<parallel>\<^sub>s Q) ;; (M ;; J))"
    by (simp add: Healthy_def' RD2_def H2_def)
  also from assms have "... = (((P \<parallel>\<^sub>s Q) ;; M) ;; J)"
    by (simp add: seqr_assoc)
  also from assms have "... = RD2(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: RD2_def H2_def par_by_merge_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma SRD_par_by_merge:
  assumes "P is SRD" "Q is SRD" "M is R1m" "M is R2m" "M is R3hm" "M is RD1m" "M is RD2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is SRD"
  by (rule SRD_intro, simp_all add: assms closure SRD_healths)

definition nmerge_rd0 ("N\<^sub>0") where
[upred_defs]: "N\<^sub>0(M) = ($wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>
                        \<and> (\<exists> $0-ok;$1-ok;$ok\<^sub><;$ok\<acute>;$0-wait;$1-wait;$wait\<^sub><;$wait\<acute> \<bullet> M))"

definition nmerge_rd1 ("N\<^sub>1") where
[upred_defs]: "N\<^sub>1(M) = ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and> N\<^sub>0(M))"

definition nmerge_rd ("N\<^sub>R") where
[upred_defs]: "N\<^sub>R(M) = ((\<exists> $st\<^sub>< \<bullet> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v\<^sub><) \<triangleleft> $wait\<^sub>< \<triangleright> N\<^sub>1(M)) \<triangleleft> $ok\<^sub>< \<triangleright> ($tr\<^sub>< \<le>\<^sub>u $tr\<acute>)"

definition merge_rd1 ("M\<^sub>1") where
[upred_defs]: "M\<^sub>1(M) = (N\<^sub>1(M) ;; II\<^sub>R)"

definition merge_rd ("M\<^sub>R") where
[upred_defs]: "M\<^sub>R(M) = N\<^sub>R(M) ;; II\<^sub>R"

abbreviation rdes_par ("_ \<parallel>\<^sub>R\<^bsub>_\<^esub> _" [85,0,86] 85) where
"P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q \<equiv> P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q"

text {* Healthiness condition for reactive design merge predicates *}

definition [upred_defs]: "RDM(M) = R2m(\<exists> $0-ok;$1-ok;$ok\<^sub><;$ok\<acute>;$0-wait;$1-wait;$wait\<^sub><;$wait\<acute> \<bullet> M)"

lemma nmerge_rd_is_R1m [closure]:
  "N\<^sub>R(M) is R1m"
  by (rel_blast)

lemma R2m_nmerge_rd: "R2m(N\<^sub>R(R2m(M))) = N\<^sub>R(R2m(M))"
  apply (rel_auto) using minus_zero_eq by blast+
    
lemma nmerge_rd_is_R2m [closure]:
  "M is R2m \<Longrightarrow> N\<^sub>R(M) is R2m"
  by (metis Healthy_def' R2m_nmerge_rd)

lemma nmerge_rd_is_R3hm [closure]: "N\<^sub>R(M) is R3hm"
  by (rel_blast)

lemma nmerge_rd_is_RD1m [closure]: "N\<^sub>R(M) is RD1m"
  by (rel_blast)

lemma merge_rd_is_RD3: "M\<^sub>R(M) is RD3"
  by (metis Healthy_Idempotent RD3_Idempotent RD3_def merge_rd_def)

lemma merge_rd_is_RD2: "M\<^sub>R(M) is RD2"
  by (simp add: RD3_implies_RD2 merge_rd_is_RD3)
    
lemma par_rdes_NSRD [closure]:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q is NSRD"
proof -
  have "(P \<parallel>\<^bsub>N\<^sub>R M\<^esub> Q ;; II\<^sub>R) is NSRD"
    by (rule NSRD_intro', simp_all add: SRD_healths closure assms)
       (metis (no_types, lifting) Healthy_def R2_par_by_merge R2_seqr_closure R2m_nmerge_rd RDM_def SRD_healths(2) assms skip_srea_R2
       ,metis Healthy_Idempotent RD3_Idempotent RD3_def)
  thus ?thesis
    by (simp add: merge_rd_def par_by_merge_def seqr_assoc)
qed

lemma RDM_intro:
  assumes "M is R2m" "$0-ok \<sharp> M" "$1-ok \<sharp> M" "$ok\<^sub>< \<sharp> M" "$ok\<acute> \<sharp> M"
          "$0-wait \<sharp> M" "$1-wait \<sharp> M" "$wait\<^sub>< \<sharp> M" "$wait\<acute> \<sharp> M"
  shows "M is RDM"
  using assms
  by (simp add: Healthy_def RDM_def ex_unrest unrest)

lemma RDM_unrests [unrest]:
  assumes "M is RDM"
  shows "$0-ok \<sharp> M" "$1-ok \<sharp> M" "$ok\<^sub>< \<sharp> M" "$ok\<acute> \<sharp> M"
        "$0-wait \<sharp> M" "$1-wait \<sharp> M" "$wait\<^sub>< \<sharp> M" "$wait\<acute> \<sharp> M"
  by (subst Healthy_if[OF assms, THEN sym], simp_all add: RDM_def unrest, rel_auto)+

lemma RDM_R1m [closure]: "M is RDM \<Longrightarrow> M is R1m"
  by (metis (no_types, hide_lams) Healthy_def R1m_idem R2m_def RDM_def)

lemma RDM_R2m [closure]: "M is RDM \<Longrightarrow> M is R2m"
  by (metis (no_types, hide_lams) Healthy_def R2m_idem RDM_def)

lemma ex_st'_R2m_closed [closure]: 
  assumes "P is R2m"
  shows "(\<exists> $st\<acute> \<bullet> P) is R2m"
proof -
  have "R2m(\<exists> $st\<acute> \<bullet> R2m P) = (\<exists> $st\<acute> \<bullet> R2m P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms) 
qed
    
lemma parallel_RR_closed: 
  assumes "P is RR" "Q is RR" "M is R2m" 
          "$ok\<^sub>< \<sharp> M" "$wait\<^sub>< \<sharp> M" "$ok\<acute> \<sharp> M" "$wait\<acute> \<sharp> M"
  shows "P \<parallel>\<^bsub>M\<^esub> Q is RR"
  by (rule RR_R2_intro, simp_all add: unrest assms RR_implies_R2 closure)

lemma parallel_ok_cases:
"((P \<parallel>\<^sub>s Q) ;; M) = (
  ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
  ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
  ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
  ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
proof -
  have "((P \<parallel>\<^sub>s Q) ;; M) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (P \<parallel>\<^sub>s Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<acute>\<rbrakk> ;; M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<rbrakk>)"
    by (subst seqr_middle[of "left_uvar ok"], simp_all)
  also have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> \<^bold>\<exists> ok\<^sub>1 \<bullet> ((P \<parallel>\<^sub>s Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<acute>\<rbrakk>\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$1-ok\<acute>\<rbrakk>) ;; (M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<rbrakk>\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$1-ok\<rbrakk>))"
    by (subst seqr_middle[of "right_uvar ok"], simp_all)
  also have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> \<^bold>\<exists> ok\<^sub>1 \<bullet> (P\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> \<parallel>\<^sub>s Q\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$ok\<acute>\<rbrakk>) ;; (M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>ok\<^sub>1\<guillemotright>/$0-ok,$1-ok\<rbrakk>))"
    by (rel_auto robust)
  also have "... = (
      ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (simp add: true_alt_def[THEN sym] false_alt_def[THEN sym] disj_assoc
      utp_pred_laws.sup.left_commute utp_pred_laws.sup_commute usubst)
  finally show ?thesis .
qed

lemma skip_srea_ok_f [usubst]:
  "II\<^sub>R\<^sup>f = R1(\<not>$ok)"
  by (rel_auto)

lemma nmerge0_rd_unrest [unrest]:
  "$0-ok \<sharp> N\<^sub>0 M" "$1-ok \<sharp> N\<^sub>0 M"
  by (pred_auto)+

lemma parallel_assm_lemma:
  assumes "P is RD2"
  shows "pre\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (((pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (cmt\<^sub>s \<dagger> Q))
                                 \<or> ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (pre\<^sub>s \<dagger> Q)))"
proof -
  have "pre\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = pre\<^sub>s \<dagger> ((P \<parallel>\<^sub>s Q) ;; M\<^sub>R(M))"
    by (simp add: par_by_merge_def)
  also have "... = ((P \<parallel>\<^sub>s Q)\<lbrakk>true,false/$ok,$wait\<rbrakk> ;; N\<^sub>R M ;; R1(\<not> $ok))"
    by (simp add: merge_rd_def usubst, rel_auto)
  also have "... = ((P\<lbrakk>true,false/$ok,$wait\<rbrakk> \<parallel>\<^sub>s Q\<lbrakk>true,false/$ok,$wait\<rbrakk>) ;; N\<^sub>1(M) ;; R1(\<not> $ok))"
    by (rel_auto robust, (metis)+)
  also have "... = ((
      (((P\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>t \<parallel>\<^sub>s (Q\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>t) ;; ((N\<^sub>1 M)\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
      (((P\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>f \<parallel>\<^sub>s (Q\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>t) ;; ((N\<^sub>1 M)\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
      (((P\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>t \<parallel>\<^sub>s (Q\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>f) ;; ((N\<^sub>1 M)\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
      (((P\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>f \<parallel>\<^sub>s (Q\<lbrakk>true,false/$ok,$wait\<rbrakk>)\<^sup>f) ;; ((N\<^sub>1 M)\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok)))) )"
    (is "_ = (?C1 \<or>\<^sub>p ?C2 \<or>\<^sub>p ?C3 \<or>\<^sub>p ?C4)")
    by (subst parallel_ok_cases, subst_tac)
  also have "... = (?C2 \<or> ?C3)"
  proof -
    have "?C1 = false"
      by (rel_auto)
    moreover have "`?C4 \<Rightarrow> ?C3`" (is "`(?A ;; ?B) \<Rightarrow> (?C ;; ?D)`")
    proof -
      from assms have "`P\<^sup>f \<Rightarrow> P\<^sup>t`"
        by (metis RD2_def H2_equivalence Healthy_def')
      hence P: "`P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f`"
        by (rel_auto)
      have "`?A \<Rightarrow> ?C`"
        using P by (rel_auto)
      moreover have "`?B \<Rightarrow> ?D`"
        by (rel_auto)
      ultimately show ?thesis
        by (simp add: impl_seqr_mono)
    qed
    ultimately show ?thesis
      by (simp add: subsumption2)
  qed
  also have "... = (
      (((pre\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; ((N\<^sub>0 M ;; R1(true)))) \<or>
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (pre\<^sub>s \<dagger> Q)) ;; ((N\<^sub>0 M ;; R1(true)))))"
    by (rel_auto, metis+)
  also have "... = (
      ((pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1(true)\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or>
      ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1(true)\<^esub> (pre\<^sub>s \<dagger> Q)))"
    by (simp add: par_by_merge_def)
  finally show ?thesis .
qed

(*
lemma parallel_assm:
  assumes "P is SRD"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (\<not> ((\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
                                   \<not> (cmt\<^sub>R(P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q))))"
  by (simp add: pre\<^sub>R_def parallel_assm_lemma SRD_healths assms, rel_auto)
*)
  
lemma pre\<^sub>s_SRD:
  assumes "P is SRD"
  shows "pre\<^sub>s \<dagger> P = (\<not>\<^sub>r pre\<^sub>R(P))"
proof -
  have "pre\<^sub>s \<dagger> P = pre\<^sub>s \<dagger> \<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = R1(R2c(\<not> pre\<^sub>s \<dagger> pre\<^sub>R P))"
    by (simp add: RHS_def usubst R3h_def pre\<^sub>s_design)
  also have "... = R1(R2c(\<not> pre\<^sub>R P))"
    by (rel_auto)
  also have "... = (\<not>\<^sub>r pre\<^sub>R P)"
    by (simp add: R2c_not R2c_preR assms rea_not_def)
  finally show ?thesis .
qed

lemma parallel_assm:
  assumes "P is SRD" "Q is SRD"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (\<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
                                   \<not>\<^sub>r (cmt\<^sub>R(P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (\<not>\<^sub>r pre\<^sub>R(Q))))"
  (is "?lhs = ?rhs")
proof -
  have "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (\<not>\<^sub>r (pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1 true\<^esub> (cmt\<^sub>s \<dagger> Q) \<and>
                             \<not>\<^sub>r (cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1 true\<^esub> (pre\<^sub>s \<dagger> Q))"
    by (simp add: pre\<^sub>R_def parallel_assm_lemma assms SRD_healths R1_conj rea_not_def[THEN sym])
  also have "... = ?rhs"
    by (simp add: pre\<^sub>s_SRD assms cmt\<^sub>R_def Healthy_if closure unrest)
  finally show ?thesis .
qed

lemma parallel_assm_unrest_wait' [unrest]:
  "\<lbrakk> P is SRD; Q is SRD \<rbrakk> \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q)"
  by (simp add: parallel_assm, simp add: par_by_merge_def unrest)

lemma JL1: "(M\<^sub>1 M)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk> = N\<^sub>0(M) ;; R1(true)"
  by (rel_blast)

lemma JL2: "(M\<^sub>1 M)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk> = N\<^sub>0(M) ;; R1(true)"
  by (rel_blast)

lemma JL3: "(M\<^sub>1 M)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk> = N\<^sub>0(M) ;; R1(true)"
  by (rel_blast)

lemma JL4: "(M\<^sub>1 M)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk> = ($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t"
  by (simp add: merge_rd1_def usubst nmerge_rd1_def unrest)

lemma parallel_commitment_lemma_1:
  assumes "P is RD2"
  shows "cmt\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (
  ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or>
  ((pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or>
  ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (pre\<^sub>s \<dagger> Q)))"
proof -
  have "cmt\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (P\<lbrakk>true,false/$ok,$wait\<rbrakk> \<parallel>\<^bsub>(M\<^sub>1(M))\<^sup>t\<^esub> Q\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: usubst, rel_auto)
  also have "... = ((P\<lbrakk>true,false/$ok,$wait\<rbrakk> \<parallel>\<^sub>s Q\<lbrakk>true,false/$ok,$wait\<rbrakk>) ;; (M\<^sub>1 M)\<^sup>t)"
    by (simp add: par_by_merge_def)
  also have "... = (
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; ((M\<^sub>1 M)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      (((pre\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; ((M\<^sub>1 M)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (pre\<^sub>s \<dagger> Q)) ;; ((M\<^sub>1 M)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      (((pre\<^sub>s \<dagger> P) \<parallel>\<^sub>s (pre\<^sub>s \<dagger> Q)) ;; ((M\<^sub>1 M)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (subst parallel_ok_cases, subst_tac)
  also have "... = (
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; ((M\<^sub>1 M)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      (((pre\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; (N\<^sub>0(M) ;; R1(true))) \<or>
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (pre\<^sub>s \<dagger> Q)) ;; (N\<^sub>0(M) ;; R1(true))) \<or>
      (((pre\<^sub>s \<dagger> P) \<parallel>\<^sub>s (pre\<^sub>s \<dagger> Q)) ;; (N\<^sub>0(M) ;; R1(true))))"
      (is "_ = (?C1 \<or>\<^sub>p ?C2 \<or>\<^sub>p ?C3 \<or>\<^sub>p ?C4)")
    by (simp add: JL1 JL2 JL3)
  also have "... = (
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; ((M\<^sub>1(M))\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      (((pre\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; (N\<^sub>0(M) ;; R1(true))) \<or>
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (pre\<^sub>s \<dagger> Q)) ;; (N\<^sub>0(M) ;; R1(true))))"
  proof -
    from assms have "`P\<^sup>f \<Rightarrow> P\<^sup>t`"
      by (metis RD2_def H2_equivalence Healthy_def')
    hence P:"`P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f`"
      by (rel_auto)
    have "`?C4 \<Rightarrow> ?C3`" (is "`(?A ;; ?B) \<Rightarrow> (?C ;; ?D)`")
    proof -
      have "`?A \<Rightarrow> ?C`"
        using P by (rel_auto)
      thus ?thesis
        by (simp add: impl_seqr_mono)
    qed
    thus ?thesis
      by (simp add: subsumption2)
  qed
  finally show ?thesis
    by (simp add: par_by_merge_def JL4)
qed

lemma parallel_commitment_lemma_2:
  assumes "P is RD2"
  shows "cmt\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
         (((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or> pre\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q))"
  by (simp add: parallel_commitment_lemma_1 assms parallel_assm_lemma)
    
lemma parallel_commitment_lemma_3:
  "M is R1m \<Longrightarrow> ($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t is R1m"
  by (rel_simp, safe, metis+)  

lemma parallel_commitment:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "cmt\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) \<Rightarrow>\<^sub>r cmt\<^sub>R(P) \<parallel>\<^bsub>($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t\<^esub> cmt\<^sub>R(Q))"
  by (simp add: parallel_commitment_lemma_2 parallel_commitment_lemma_3 Healthy_if assms cmt\<^sub>R_def pre\<^sub>s_SRD closure rea_impl_def disj_comm unrest)  
  
theorem parallel_reactive_design:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = \<^bold>R\<^sub>s(
    (\<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
     \<not>\<^sub>r (cmt\<^sub>R(P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (\<not>\<^sub>r pre\<^sub>R(Q)))) \<turnstile>
    (cmt\<^sub>R(P) \<parallel>\<^bsub>($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t\<^esub> cmt\<^sub>R(Q)))" (is "?lhs = ?rhs")
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = \<^bold>R\<^sub>s(pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) \<turnstile> cmt\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q))"
    by (metis Healthy_def NSRD_is_SRD SRD_as_reactive_design assms(1) assms(2) assms(3) par_rdes_NSRD)
  also have "... = ?rhs"
    by (simp add: parallel_assm parallel_commitment design_export_spec assms, rel_auto)
  finally show ?thesis .
qed

lemma parallel_pericondition_lemma1:
  "($ok\<acute> \<and> P) ;; II\<^sub>R\<lbrakk>true,true/$ok\<acute>, $wait\<acute>\<rbrakk> = (\<exists> $st\<acute> \<bullet> P)\<lbrakk>true,true/$ok\<acute>,$wait\<acute>\<rbrakk>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = ($ok\<acute> \<and> P) ;; (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok\<acute>, $wait\<acute>\<rbrakk>"
    by (rel_blast)
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

lemma parallel_pericondition_lemma2:
  assumes "M is RDM"
  shows "(\<exists> $st\<acute> \<bullet> N\<^sub>0(M))\<lbrakk>true,true/$ok\<acute>, $wait\<acute>\<rbrakk> = (($0-wait \<or> $1-wait) \<and> (\<exists> $st\<acute> \<bullet> M))"
proof -
  have "(\<exists> $st\<acute> \<bullet> N\<^sub>0(M))\<lbrakk>true,true/$ok\<acute>, $wait\<acute>\<rbrakk> = (\<exists> $st\<acute> \<bullet> ($0-wait \<or> $1-wait) \<and> $tr\<acute> \<ge>\<^sub>u $tr\<^sub>< \<and> M)"
    by (simp add: usubst unrest nmerge_rd0_def ex_unrest Healthy_if R1m_def assms)
  also have "... =  (\<exists> $st\<acute> \<bullet> ($0-wait \<or> $1-wait) \<and> M)"
    by (metis (no_types, hide_lams) Healthy_if R1m_def R1m_idem R2m_def RDM_def assms utp_pred_laws.inf_commute)
  also have "... = (($0-wait \<or> $1-wait) \<and> (\<exists> $st\<acute> \<bullet> M))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma parallel_pericondition_lemma3:
  "(($0-wait \<or> $1-wait) \<and> (\<exists> $st\<acute> \<bullet> M)) = (($0-wait \<and> $1-wait \<and> (\<exists> $st\<acute> \<bullet> M)) \<or> (\<not> $0-wait \<and> $1-wait \<and> (\<exists> $st\<acute> \<bullet> M)) \<or> ($0-wait \<and> \<not> $1-wait \<and> (\<exists> $st\<acute> \<bullet> M)))"
  by (rel_auto)

lemma parallel_pericondition [rdes]:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "peri\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> peri\<^sub>R(Q)
                                                  \<or> post\<^sub>R(P) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> peri\<^sub>R(Q)
                                                  \<or> peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> post\<^sub>R(Q))"
proof -
  have "peri\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
        (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<lbrakk>true,true/$ok\<acute>, $wait\<acute>\<rbrakk>\<^esub> cmt\<^sub>R Q)"
    by (simp add: peri_cmt_def parallel_commitment SRD_healths assms usubst unrest assms)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>(\<exists> $st\<acute> \<bullet> N\<^sub>0 M)\<lbrakk>true,true/$ok\<acute>, $wait\<acute>\<rbrakk>\<^esub> cmt\<^sub>R Q)"
    by (simp add: parallel_pericondition_lemma1)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>($0-wait \<or> $1-wait) \<and> (\<exists> $st\<acute> \<bullet> M)\<^esub> cmt\<^sub>R Q)"
    by (simp add: parallel_pericondition_lemma2 assms)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r ((\<lceil>cmt\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>cmt\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; ($0-wait \<and> $1-wait \<and> (\<exists> $st\<acute> \<bullet> M))
                                       \<or> (\<lceil>cmt\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>cmt\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (\<not> $0-wait \<and> $1-wait \<and> (\<exists> $st\<acute> \<bullet> M))
                                       \<or> (\<lceil>cmt\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>cmt\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; ($0-wait \<and> \<not> $1-wait \<and> (\<exists> $st\<acute> \<bullet> M))))"
    by (simp add: par_by_merge_alt_def parallel_pericondition_lemma3 seqr_or_distr)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r ((\<lceil>peri\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (\<exists> $st\<acute> \<bullet> M)
                                       \<or> (\<lceil>post\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (\<exists> $st\<acute> \<bullet> M)
                                       \<or> (\<lceil>peri\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (\<exists> $st\<acute> \<bullet> M)))"
    by (simp add: seqr_right_one_point_true seqr_right_one_point_false cmt\<^sub>R_def post\<^sub>R_def peri\<^sub>R_def usubst unrest assms)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> peri\<^sub>R(Q)
                                       \<or> post\<^sub>R(P) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> peri\<^sub>R(Q)
                                       \<or> peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> post\<^sub>R(Q))"
    by (simp add: par_by_merge_alt_def)
  finally show ?thesis .
qed

lemma parallel_postcondition_lemma1:
  "($ok\<acute> \<and> P) ;; II\<^sub>R\<lbrakk>true,false/$ok\<acute>,$wait\<acute>\<rbrakk> = P\<lbrakk>true,false/$ok\<acute>,$wait\<acute>\<rbrakk>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = ($ok\<acute> \<and> P) ;; II\<lbrakk>true,false/$ok\<acute>, $wait\<acute>\<rbrakk>"
    by (rel_blast)
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

lemma parallel_postcondition_lemma2:
  assumes "M is RDM"
  shows "(N\<^sub>0(M))\<lbrakk>true,false/$ok\<acute>,$wait\<acute>\<rbrakk> = ((\<not> $0-wait \<and> \<not> $1-wait) \<and> M)"
proof -
  have "(N\<^sub>0(M))\<lbrakk>true,false/$ok\<acute>,$wait\<acute>\<rbrakk> = ((\<not> $0-wait \<and> \<not> $1-wait) \<and> $tr\<acute> \<ge>\<^sub>u $tr\<^sub>< \<and> M)"
    by (simp add: usubst unrest nmerge_rd0_def ex_unrest Healthy_if R1m_def assms)
  also have "... = ((\<not> $0-wait \<and> \<not> $1-wait) \<and> M)"
    by (metis Healthy_if R1m_def RDM_R1m assms utp_pred_laws.inf_commute)
  finally show ?thesis .
qed

lemma parallel_postcondition [rdes]:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "post\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r post\<^sub>R(P) \<parallel>\<^bsub>M\<^esub> post\<^sub>R(Q))"
proof -
  have "post\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
        (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>($ok\<acute> \<and> N\<^sub>0 M) ;; II\<^sub>R\<lbrakk>true,false/$ok\<acute>, $wait\<acute>\<rbrakk>\<^esub> cmt\<^sub>R Q)"
    by (simp add: post_cmt_def parallel_commitment assms usubst unrest SRD_healths)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>(\<not> $0-wait \<and> \<not> $1-wait \<and> M)\<^esub> cmt\<^sub>R Q)"
    by (simp add: parallel_postcondition_lemma1 parallel_postcondition_lemma2 assms,
        simp add: utp_pred_laws.inf_commute utp_pred_laws.inf_left_commute)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<Rightarrow>\<^sub>r post\<^sub>R P \<parallel>\<^bsub>M\<^esub> post\<^sub>R Q)"
    by (simp add: par_by_merge_alt_def seqr_right_one_point_false usubst unrest cmt\<^sub>R_def post\<^sub>R_def assms)
  finally show ?thesis .
qed

lemma parallel_precondition_lemma:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is NSRD" "Q is NSRD" "M is RDM"
  shows "(\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q) =
         ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q \<or> (\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q)"
proof -
  have "((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) =
        ((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: wait'_cond_peri_post_cmt)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; N\<^sub>0(M) ;; R1(true))"
    by (simp add: par_by_merge_alt_def)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R(Q)\<rceil>\<^sub>1 \<triangleleft> $1-wait\<acute> \<triangleright> \<lceil>post\<^sub>R(Q)\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; N\<^sub>0(M) ;; R1(true))"
    by (simp add: wait'_cond_def alpha)
  also have "... = (((\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R(Q)\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) \<triangleleft> $1-wait\<acute> \<triangleright> (\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R(Q)\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v)) ;; N\<^sub>0(M) ;; R1(true))"
    (is "(?P ;; _) = (?Q ;; _)")
  proof -
    have "?P = ?Q"
      by (rel_auto)
    thus ?thesis by simp
  qed
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v)\<lbrakk>true/$1-wait\<acute>\<rbrakk> ;; (N\<^sub>0 M ;; R1 true)\<lbrakk>true/$1-wait\<rbrakk> \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v)\<lbrakk>false/$1-wait\<acute>\<rbrakk> ;; (N\<^sub>0 M ;; R1 true)\<lbrakk>false/$1-wait\<rbrakk>)"
    by (simp add: cond_inter_var_split)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; N\<^sub>0 M\<lbrakk>true/$1-wait\<rbrakk> ;; R1 true \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; N\<^sub>0 M\<lbrakk>false/$1-wait\<rbrakk> ;; R1 true)"
    by (simp add: usubst unrest)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; ($wait\<acute> \<and> M) ;; R1 true \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; ($wait\<acute> =\<^sub>u $0-wait \<and> M) ;; R1 true)"
  proof -
    have "($tr\<acute> \<ge>\<^sub>u $tr\<^sub>< \<and> M) = M"
      using RDM_R1m[OF assms(3)]
      by (simp add: Healthy_def R1m_def conj_comm)
    thus ?thesis
      by (simp add: nmerge_rd0_def unrest assms closure ex_unrest usubst)
  qed
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M ;; R1 true \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M ;; R1 true)"
    (is "(?P\<^sub>1 \<or>\<^sub>p ?P\<^sub>2) = (?Q\<^sub>1 \<or> ?Q\<^sub>2)")
  proof -
    have "?P\<^sub>1 = (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (M \<and> $wait\<acute>) ;; R1 true"
      by (simp add: conj_comm)
    hence 1: "?P\<^sub>1 = ?Q\<^sub>1"
      by (simp add: seqr_left_one_point_true seqr_left_one_point_false add: unrest usubst closure assms)
    have "?P\<^sub>2 = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (M \<and> $wait\<acute>) ;; R1 true \<or>
                 (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; (M \<and> \<not> $wait\<acute>) ;; R1 true)"
      by (subst seqr_bool_split[of "left_uvar wait"], simp_all add: usubst unrest assms closure conj_comm)
    hence 2: "?P\<^sub>2 = ?Q\<^sub>2"
      by (simp add: seqr_left_one_point_true seqr_left_one_point_false unrest usubst closure assms)
    from 1 2 show ?thesis by simp
  qed
  also have "... = ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q \<or> (\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q)"
    by (simp add: par_by_merge_alt_def)
  finally show ?thesis .
qed

lemma swap_nmerge_rd0:
  "swap\<^sub>m ;; N\<^sub>0(M) = N\<^sub>0(swap\<^sub>m ;; M)"
  by (rel_auto, meson+)

lemma SymMerge_nmerge_rd0 [closure]:
  "M is SymMerge \<Longrightarrow> N\<^sub>0(M) is SymMerge"
  by (rel_auto, meson+)
    
lemma swap_merge_rd':
  "swap\<^sub>m ;; N\<^sub>R(M) = N\<^sub>R(swap\<^sub>m ;; M)"
  by (rel_blast)
    
lemma swap_merge_rd:
  "swap\<^sub>m ;; M\<^sub>R(M) = M\<^sub>R(swap\<^sub>m ;; M)"
  by (simp add: merge_rd_def seqr_assoc[THEN sym] swap_merge_rd')

lemma SymMerge_merge_rd [closure]:
  "M is SymMerge \<Longrightarrow> M\<^sub>R(M) is SymMerge"
  by (simp add: Healthy_def swap_merge_rd)
    
lemma nmerge_rd1_merge3:
  assumes "M is RDM"
  shows "\<^bold>M3(N\<^sub>1(M)) = ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-0-ok \<and> $1-1-ok) \<and> 
                      $wait\<acute> =\<^sub>u ($0-wait \<or> $1-0-wait \<or> $1-1-wait) \<and> 
                      \<^bold>M3(M))"
proof -
  have "\<^bold>M3(N\<^sub>1(M)) = \<^bold>M3($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and>
                       $wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and> 
                       $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and> 
                       (\<exists> {$0-ok, $1-ok, $ok\<^sub><, $ok\<acute>, $0-wait, $1-wait, $wait\<^sub><, $wait\<acute>} \<bullet> RDM(M)))"
    by (simp add: nmerge_rd1_def nmerge_rd0_def assms Healthy_if)
  also have "... = \<^bold>M3($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and> $wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and> RDM(M))"
    by (rel_blast)
  also have "... = ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-0-ok \<and> $1-1-ok) \<and> $wait\<acute> =\<^sub>u ($0-wait \<or> $1-0-wait \<or> $1-1-wait) \<and> \<^bold>M3(RDM(M)))"  
    by (rel_blast)
  also have "... = ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-0-ok \<and> $1-1-ok) \<and> $wait\<acute> =\<^sub>u ($0-wait \<or> $1-0-wait \<or> $1-1-wait) \<and> \<^bold>M3(M))"
    by (simp add: assms Healthy_if)
  finally show ?thesis .
qed

lemma nmerge_rd_merge3:
  "\<^bold>M3(N\<^sub>R(M)) = (\<exists> $st\<^sub>< \<bullet> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v\<^sub><) \<triangleleft> $wait\<^sub>< \<triangleright> \<^bold>M3(N\<^sub>1 M) \<triangleleft> $ok\<^sub>< \<triangleright> ($tr\<^sub>< \<le>\<^sub>u $tr\<acute>)"
  by (rel_blast) (* 15 seconds *)
    
lemma swap_merge_RDM_closed [closure]:
  assumes "M is RDM" 
  shows "swap\<^sub>m ;; M is RDM"
proof -
  have "RDM(swap\<^sub>m ;; RDM(M)) = (swap\<^sub>m ;; RDM(M))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms)
qed
  
lemma parallel_precondition:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is NSRD" "Q is NSRD" "M is RDM"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
          (\<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q) \<and>
           \<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q) \<and>
           \<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> peri\<^sub>R P) \<and>
           \<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> post\<^sub>R P))"
proof -
  have a: "(\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q) =
           ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q \<or> (\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q)"
    by (simp add: parallel_precondition_lemma assms)

  have b: "(\<not>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>N\<^sub>0 M ;; R1 true\<^esub> (\<not>\<^sub>r pre\<^sub>R Q)) =
           (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(Q)) \<parallel>\<^bsub>N\<^sub>0(swap\<^sub>m ;; M) ;; R1(true)\<^esub> cmt\<^sub>R(P))"
    by (simp add: swap_nmerge_rd0[THEN sym] seqr_assoc[THEN sym] par_by_merge_def par_sep_swap)
  have c: "(\<not>\<^sub>r pre\<^sub>R(Q)) \<parallel>\<^bsub>N\<^sub>0(swap\<^sub>m ;; M) ;; R1(true)\<^esub> cmt\<^sub>R(P) =
           ((\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> peri\<^sub>R P \<or> (\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> post\<^sub>R P)"
    by (simp add: parallel_precondition_lemma closure assms)

  show ?thesis
    by (simp add: parallel_assm closure assms a b c, rel_auto)
qed

text {* Weakest Parallel Precondition *}

definition wrR :: 
  "('t::trace, '\<alpha>) hrel_rp \<Rightarrow> 
   ('t :: trace, '\<alpha>) rp merge \<Rightarrow> 
   ('t, '\<alpha>) hrel_rp \<Rightarrow> 
   ('t, '\<alpha>) hrel_rp" ("_ wr\<^sub>R'(_') _" [60,0,61] 61)
where [upred_defs]: "Q wr\<^sub>R(M) P = (\<not>\<^sub>r ((\<not>\<^sub>r P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> Q))"

lemma wrR_R1 [closure]: 
  "M is R1m \<Longrightarrow> Q wr\<^sub>R(M) P is R1"
  by (simp add: wrR_def closure)
    
lemma R2_rea_not: "R2(\<not>\<^sub>r P) = (\<not>\<^sub>r R2(P))"
  by (rel_auto)
        
lemma wrR_R2_lemma:
  assumes "P is R2" "Q is R2" "M is R2m"
  shows "((\<not>\<^sub>r P) \<parallel>\<^bsub>M\<^esub> Q) ;; R1(true\<^sub>h) is R2"
proof -
  have "(\<not>\<^sub>r P) \<parallel>\<^bsub>M\<^esub> Q is R2"
    by (simp add: closure assms)
  thus ?thesis
    by (simp add: closure)
qed
    
lemma wrR_R2 [closure]: 
  assumes "P is R2" "Q is R2" "M is R2m"
  shows "Q wr\<^sub>R(M) P is R2"
proof -
  have "((\<not>\<^sub>r P) \<parallel>\<^bsub>M\<^esub> Q) ;; R1(true\<^sub>h) is R2"
    by (simp add: wrR_R2_lemma assms)
  thus ?thesis
    by (simp add: wrR_def wrR_R2_lemma par_by_merge_seq_add closure) 
qed
 
lemma wrR_RR [closure]: 
  assumes "P is RR" "Q is RR" "M is RDM"
  shows "Q wr\<^sub>R(M) P is RR"
  apply (rule RR_intro)
  apply (simp_all add: unrest assms closure wrR_def rpred)
  apply (metis (no_types, lifting) Healthy_def' R1_R2c_commute R1_R2c_is_R2 R1_rea_not RDM_R2m 
               RR_implies_R2 assms(1) assms(2) assms(3) par_by_merge_seq_add rea_not_R2_closed 
               wrR_R2_lemma)
done
             
lemma wrR_RC [closure]: 
  assumes "P is RR" "Q is RR" "M is RDM"
  shows "(Q wr\<^sub>R(M) P) is RC"
  apply (rule RC_intro)
  apply (simp add: closure assms)
  apply (simp add: wrR_def rpred closure assms )
  apply (simp add: par_by_merge_def seqr_assoc)
done
    
lemma wppR_choice [wp]: "(P \<or> Q) wr\<^sub>R(M) R = (P wr\<^sub>R(M) R \<and> Q wr\<^sub>R(M) R)"
proof -
  have "(P \<or> Q) wr\<^sub>R(M) R = 
        (\<not>\<^sub>r ((\<not>\<^sub>r R) ;; U0 \<and> (P ;; U1 \<or> Q ;; U1) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M ;; true\<^sub>r)"
    by (simp add: wrR_def par_by_merge_def seqr_or_distl)
  also have "... = (\<not>\<^sub>r ((\<not>\<^sub>r R) ;; U0 \<and> P ;; U1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v \<or> (\<not>\<^sub>r R) ;; U0 \<and> Q ;; U1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M ;; true\<^sub>r)"
    by (simp add: conj_disj_distr utp_pred_laws.inf_sup_distrib2)
  also have "... = (\<not>\<^sub>r (((\<not>\<^sub>r R) ;; U0 \<and> P ;; U1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M ;; true\<^sub>r \<or> 
                        ((\<not>\<^sub>r R) ;; U0 \<and> Q ;; U1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M ;; true\<^sub>r))"    
    by (simp add: seqr_or_distl)
  also have "... = (P wr\<^sub>R(M) R \<and> Q wr\<^sub>R(M) R)"
    by (simp add: wrR_def par_by_merge_def)
  finally show ?thesis .
qed
      
lemma wppR_miracle [wp]: "false wr\<^sub>R(M) P = true\<^sub>r"
  by (simp add: wrR_def)

lemma wppR_true [wp]: "P wr\<^sub>R(M) true\<^sub>r = true\<^sub>r"
  by (simp add: wrR_def)

lemma parallel_precondition_wr [rdes]:
  assumes "P is NSRD" "Q is NSRD" "M is RDM"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (peri\<^sub>R(Q) wr\<^sub>R(M) pre\<^sub>R(P) \<and> post\<^sub>R(Q) wr\<^sub>R(M) pre\<^sub>R(P) \<and>
                              peri\<^sub>R(P) wr\<^sub>R(swap\<^sub>m ;; M) pre\<^sub>R(Q) \<and> post\<^sub>R(P) wr\<^sub>R(swap\<^sub>m ;; M) pre\<^sub>R(Q))"
  by (simp add: assms parallel_precondition wrR_def)

lemma parallel_rdes_def [rdes_def]:
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RC" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
          "$st\<acute> \<sharp> P\<^sub>2" "$st\<acute> \<sharp> Q\<^sub>2"
          "M is RDM"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = 
         \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr\<^sub>R(M) P\<^sub>1 \<and> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr\<^sub>R(M) P\<^sub>1 \<and> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr\<^sub>R(swap\<^sub>m ;; M) Q\<^sub>1 \<and> (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr\<^sub>R(swap\<^sub>m ;; M) Q\<^sub>1) \<turnstile>
          ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
           (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> M\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
          ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>M\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)))" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s (pre\<^sub>R ?lhs \<turnstile> peri\<^sub>R ?lhs \<diamondop> post\<^sub>R ?lhs)"
    by (simp add: SRD_reactive_tri_design assms closure)
  also have "... = ?rhs"
    by (simp add: rdes closure unrest assms, rel_auto) 
  finally show ?thesis .
qed

lemma Miracle_parallel_left_zero:
  assumes "P is SRD" "M is RDM"
  shows "Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P = Miracle"
proof -
  have "pre\<^sub>R(Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P) = true\<^sub>r"
    by (simp add: parallel_assm wait'_cond_idem rdes closure assms)
  moreover hence "cmt\<^sub>R(Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P) = false"
    by (simp add: rdes closure wait'_cond_idem SRD_healths assms)
  ultimately have "Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false)"
    by (metis NSRD_iff SRD_reactive_design_alt assms par_rdes_NSRD srdes_theory_continuous.weak.top_closed)
  thus ?thesis
    by (simp add: Miracle_def R1_design_R1_pre)
qed

lemma Miracle_parallel_right_zero:
  assumes "P is SRD" "M is RDM"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle = Miracle"
proof -
  have "pre\<^sub>R(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle) = true\<^sub>r"
    by (simp add: wait'_cond_idem parallel_assm rdes closure assms)
  moreover hence "cmt\<^sub>R(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle) = false"
    by (simp add: wait'_cond_idem rdes closure SRD_healths assms)
  ultimately have "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false)"
    by (metis NSRD_iff SRD_reactive_design_alt assms par_rdes_NSRD srdes_theory_continuous.weak.top_closed)
  thus ?thesis
    by (simp add: Miracle_def R1_design_R1_pre)
qed

subsection {* Example basic merge *}
  
definition BasicMerge :: "(('s, 't::trace, unit) rsp) merge" ("N\<^sub>B") where
[upred_defs]: "BasicMerge = ($tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and> $tr\<acute> - $tr\<^sub>< =\<^sub>u $0-tr - $tr\<^sub>< \<and> $tr\<acute> - $tr\<^sub>< =\<^sub>u $1-tr - $tr\<^sub>< \<and> $st\<acute> =\<^sub>u $st\<^sub><)"

abbreviation rbasic_par ("_ \<parallel>\<^sub>B _" [85,86] 85) where
"P \<parallel>\<^sub>B Q \<equiv> P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>B)\<^esub> Q"

lemma BasicMerge_RDM [closure]: "N\<^sub>B is RDM"
  by (rule RDM_intro, (rel_auto)+)

lemma BasicMerge_SymMerge [closure]: 
  "N\<^sub>B is SymMerge"
  by (rel_auto)
   
lemma BasicMerge'_calc:
  assumes "$ok\<acute> \<sharp> P" "$wait\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$wait\<acute> \<sharp> Q" "P is R2" "Q is R2"
  shows "P \<parallel>\<^bsub>N\<^sub>B\<^esub> Q = ((\<exists> $st\<acute> \<bullet> P) \<and> (\<exists> $st\<acute> \<bullet> Q) \<and> $st\<acute> =\<^sub>u $st)"
  using assms
proof -
  have P:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(P)) = P" (is "?P' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  have Q:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(Q)) = Q" (is "?Q' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  have "?P' \<parallel>\<^bsub>N\<^sub>B\<^esub> ?Q' = ((\<exists> $st\<acute> \<bullet> ?P') \<and> (\<exists> $st\<acute> \<bullet> ?Q') \<and> $st\<acute> =\<^sub>u $st)"
    by (simp add: par_by_merge_alt_def, rel_auto, blast+)
  thus ?thesis
    by (simp add: P Q)
qed 
  
subsection {* Simple parallel composition *}

definition rea_design_par ::
  "('s, 't::trace, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" (infixr "\<parallel>\<^sub>R" 85)
where [upred_defs]: "P \<parallel>\<^sub>R Q = \<^bold>R\<^sub>s((pre\<^sub>R(P)  \<and> pre\<^sub>R(Q)) \<turnstile> (cmt\<^sub>R(P) \<and> cmt\<^sub>R(Q)))"

lemma RHS_design_par:
  assumes
    "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) =
        \<^bold>R\<^sub>s(P\<^sub>1\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<^sub>1\<lbrakk>true,false/$ok,$wait\<rbrakk>) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<^sub>2\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: RHS_design_ok_wait)

  also from assms
  have "... =
        \<^bold>R\<^sub>s((R1 (R2c (P\<^sub>1)) \<and> R1 (R2c (P\<^sub>2)))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile>
           (R1 (R2c (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2c (P\<^sub>2 \<Rightarrow> Q\<^sub>2)))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
      apply (simp add: rea_design_par_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest assms)
      apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp)
      using assms apply (rel_auto)
  done
  also have "... =
        \<^bold>R\<^sub>s((R2c(P\<^sub>1) \<and> R2c(P\<^sub>2)) \<turnstile>
           (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (metis (no_types, hide_lams) R1_R2s_R2c R1_conj R1_design_R1_pre RHS_design_ok_wait)
  also have "... =
        \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: R2c_R3h_commute R2c_and R2c_design R2c_idem R2c_not RHS_def)
  also have "... = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> ((P\<^sub>1 \<Rightarrow> Q\<^sub>1) \<and> (P\<^sub>2 \<Rightarrow> Q\<^sub>2)))"
    by (metis (no_types, lifting) R1_conj R2s_conj RHS_design_export_R1 RHS_design_export_R2s)
  also have "... = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma RHS_tri_design_par:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (R\<^sub>1 \<and> R\<^sub>2))"
  by (simp add: RHS_design_par assms unrest wait'_cond_conj_exchange)

lemma RHS_tri_design_par_RR [rdes_def]:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (R\<^sub>1 \<and> R\<^sub>2))"
  by (simp add: RHS_tri_design_par unrest assms)

lemma RHS_comp_assoc: 
  assumes "P is NSRD" "Q is NSRD" "R is NSRD"
  shows "(P \<parallel>\<^sub>R Q) \<parallel>\<^sub>R R = P \<parallel>\<^sub>R Q \<parallel>\<^sub>R R"
  by (rdes_eq cls: assms)

end