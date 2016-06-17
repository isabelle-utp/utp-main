section {* Hybrid reactive designs *}

theory utp_hrd
imports 
  utp_designs
  utp_rea_designs
begin

record 't::linordered_ring htime =
  htime :: 't

type_synonym ('t, '\<theta>, '\<alpha>) alphabet_hrd = "('\<theta>, ('t, '\<alpha>) htime_scheme) alphabet_rp"
type_synonym ('a, 't, '\<theta>, '\<alpha>) hrde = "('a, ('t, '\<theta>, '\<alpha>) alphabet_hrd) uexpr"
type_synonym ('t, '\<theta>, '\<alpha>, '\<beta>) hrd = "(('t, '\<theta>, '\<alpha>) alphabet_hrd, ('t, '\<theta>, '\<beta>) alphabet_hrd) relation"
type_synonym ('t, '\<theta>, '\<alpha>) hhrd = "(('t, '\<theta>, '\<alpha>) alphabet_hrd, ('t, '\<theta>, '\<alpha>) alphabet_hrd) relation"

definition [upred_defs]: "time\<^sub>h = VAR htime"

definition [upred_defs]: "time = time\<^sub>h ;\<^sub>L \<Sigma>\<^sub>R"

definition [upred_defs]: "\<Sigma>\<^sub>h = VAR more"

definition [upred_defs]: "\<Sigma>\<^sub>H = \<Sigma>\<^sub>h ;\<^sub>L \<Sigma>\<^sub>R"

lemma time\<^sub>h_uvar [simp]: "uvar time\<^sub>h"
  by (unfold_locales, simp_all add: time\<^sub>h_def)

lemma \<Sigma>\<^sub>h_uvar [simp]: "uvar \<Sigma>\<^sub>h"
  by (unfold_locales, simp_all add: \<Sigma>\<^sub>h_def)

lemma time_uvar [simp]: "uvar time"
  by (metis comp_vwb_lens rea_lens_under_des_lens sublens_pres_vwb time\<^sub>h_uvar time_def uvar_des_lens)

lemma \<Sigma>\<^sub>H_uvar [simp]: "uvar \<Sigma>\<^sub>H"
  by (metis \<Sigma>\<^sub>H_def \<Sigma>\<^sub>h_uvar comp_vwb_lens rea_lens_under_des_lens sublens_pres_vwb uvar_des_lens)

lemma hy_lens_under_des_lens: "\<Sigma>\<^sub>H \<subseteq>\<^sub>L \<Sigma>\<^sub>R"
  by (simp add: \<Sigma>\<^sub>H_def lens_comp_lb) 

lemma time_ok_indep [simp]: "time \<bowtie> ok" "ok \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_wait_indep [simp]: "time \<bowtie> wait" "wait \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_tr_indep [simp]: "time \<bowtie> tr" "tr \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_ref_indep [simp]: "time \<bowtie> ref" "ref \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_hy_indep [simp]: "time\<^sub>h \<bowtie> \<Sigma>\<^sub>h" "\<Sigma>\<^sub>h \<bowtie> time\<^sub>h"
  by (auto intro!:lens_indepI simp add: time\<^sub>h_def \<Sigma>\<^sub>h_def)

lemma time_hy_lens_indep [simp]: "time \<bowtie> \<Sigma>\<^sub>H" "\<Sigma>\<^sub>H \<bowtie> time"
  by (auto intro: lens_indep_left_comp simp add: time_def \<Sigma>\<^sub>H_def)

lemma hy_lens_indep_ok [simp]:
  "\<Sigma>\<^sub>H \<bowtie> ok" "ok \<bowtie> \<Sigma>\<^sub>H"
  using hy_lens_under_des_lens rea_lens_indep_ok(1) sublens_pres_indep apply blast
  using hy_lens_under_des_lens lens_indep_sym rea_lens_indep_ok(1) sublens_pres_indep apply blast
done

lemma hy_lens_indep_tr [simp]:
  "\<Sigma>\<^sub>H \<bowtie> tr" "tr \<bowtie> \<Sigma>\<^sub>H"
using hy_lens_under_des_lens rea_lens_indep_tr(1) sublens_pres_indep apply blast
using hy_lens_under_des_lens lens_indep_sym rea_lens_indep_tr(1) sublens_pres_indep apply blast
done

lemma hy_lens_indep_wait [simp]:
  "\<Sigma>\<^sub>H \<bowtie> wait" "wait \<bowtie> \<Sigma>\<^sub>H"
  apply (simp_all add: \<Sigma>\<^sub>H_def lens_indep_left_ext)
  using lens_indep_left_ext lens_indep_sym rea_lens_indep_wait(1) apply blast
done

lemma hy_lens_indep_ref [simp]:
  "\<Sigma>\<^sub>H \<bowtie> ref" "ref \<bowtie> \<Sigma>\<^sub>H"
  by (simp_all add: \<Sigma>\<^sub>H_def lens_indep_left_ext lens_indep_sym)

abbreviation lift_hrd :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>H") where
"\<lceil>P\<rceil>\<^sub>H \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

abbreviation drop_hrd :: "_ \<Rightarrow> _" ("\<lfloor>_\<rfloor>\<^sub>H") where
"\<lfloor>P\<rfloor>\<^sub>H \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

abbreviation "\<L> \<equiv> $time\<acute> - $time"

definition [upred_defs]: "TI1(P) = (P \<and> $time \<le>\<^sub>u $time\<acute>)"

definition [upred_defs]: "HR1(P) = TI1(R1(P))"

definition [upred_defs]: "TI2(P) = P\<lbrakk>0,($time\<acute>-$time)/$time,$time\<acute>\<rbrakk>"

definition [upred_defs]: "TI2c(P) = (P\<lbrakk>0,($time\<acute>-$time)/$time,$time\<acute>\<rbrakk> \<triangleleft> TI1(true) \<triangleright> P)"

definition [upred_defs]: "HR2(P) = R2(TI2(P))"

definition [upred_defs]: "HR2s(P) = R2s(TI2(P))"

definition [upred_defs]: "HR2c(P) = R2c(TI2(P))"

definition [urel_defs]: "II\<^sub>H = (II \<or> (\<not> $ok \<and> HR1(true)))"

definition [upred_defs]: "HR3(P) = (II\<^sub>H \<triangleleft> $wait \<triangleright> P)" 

lemma lift_hrd_unrests [unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>H" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H" "$wait \<sharp> \<lceil>P\<rceil>\<^sub>H" "$wait\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H"
  "$tr \<sharp> \<lceil>P\<rceil>\<^sub>H" "$tr\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H" "$ref \<sharp> \<lceil>P\<rceil>\<^sub>H" "$ref\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H"
  "$time \<sharp> \<lceil>P\<rceil>\<^sub>H" "$time\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H"
  by (simp_all add: unrest_aext_indep)
  
lemma TI1_idem: "TI1(TI1(P)) = TI1(P)"
  by rel_tac

lemma TI1_conj_left:
  "TI1(P \<and> Q) = (TI1(P) \<and> Q)"
  by rel_tac

lemma TI1_conj_right:
  "TI1(P \<and> Q) = (P \<and> TI1(Q))"
  by rel_tac

lemma TI1_conj:
  "TI1(P \<and> Q) = (TI1(P) \<and> TI1(Q))"
  by rel_tac

lemma TI1_disj:
  "TI1(P \<or> Q) = (TI1(P) \<or> TI1(Q))"
  by (rel_tac)

lemma TI1_HR1:
  "TI1(HR1(P)) = HR1(P)"
  by (rel_tac)

lemma TI1_TI2_commute:
  "TI1(TI2(P)) = TI2(TI1(P))"
  by rel_tac

lemma TI1_R1_commute:
  "TI1(R1(P)) = R1(TI1(P))"
  by rel_tac

lemma TI1_HR3_commute:
  "TI1(HR3(P)) = HR3(TI1(P))"
  by rel_tac

lemma TI1_skip_ti:
  "TI1(II\<^sub>H) = II\<^sub>H"
  by rel_tac

lemma TI2_idem: "TI2(TI2(P)) = TI2(P)"
  by rel_tac

lemma TI2_not:
  "TI2(\<not> P) = (\<not> TI2(P))"
  by (rel_tac)

lemma TI2_conj:
  "TI2(P \<and> Q) = (TI2(P) \<and> TI2(Q))"
  by (rel_tac)
  
lemma TI2_disj:
  "TI2(P \<or> Q) = (TI2(P) \<or> TI2(Q))"
  by (rel_tac)

lemma TI2_cond:
  "TI2(P \<triangleleft> b \<triangleright> Q) = (TI2(P) \<triangleleft> TI2(b) \<triangleright> TI2(Q))"
  by (simp add: cond_def TI2_disj TI2_conj TI2_not)
  
lemma TI2_wait:
  "TI2($wait) = $wait"
  by (rel_tac)

lemma TI2_skip:
  "TI2(II) = II"
proof -
  have "TI2(II) = TI2 ($time\<acute> =\<^sub>u $time \<and> II \<restriction>\<^sub>\<alpha> time)"
    by (metis skip_r_unfold time_uvar)
  also have "... = ($time\<acute>-$time =\<^sub>u 0 \<and> II \<restriction>\<^sub>\<alpha> time)" 
    by (simp add: TI2_def usubst unrest)
  also have "... = ($time\<acute> =\<^sub>u $time \<and> II \<restriction>\<^sub>\<alpha> time)"
    by (rel_tac)
  also have "... = II"
    by (metis skip_r_unfold time_uvar)
  finally show ?thesis .
qed

lemma TI2_not_ok: "TI2(\<not>$ok) = (\<not>$ok)"
  by (rel_tac)

lemma TI2_HR1_true: "TI2(HR1(true)) = HR1(true)"
  by (rel_tac)

lemma TI2_skip_ti:
  "TI2(II\<^sub>H) = II\<^sub>H"
  by (simp add: II\<^sub>H_def TI2_conj TI2_disj TI2_skip TI2_not_ok TI2_HR1_true TI1_TI2_commute[THEN sym] usubst)

lemma TI2_R1_commute:
  "TI2(R1(P)) = R1(TI2(P))"
  by rel_tac

lemma TI2_HR3_commute:
  "TI2(HR3(P)) = HR3(TI2(P))"
  by (simp add: HR3_def usubst TI2_cond TI2_skip_ti TI2_wait)

lemma HR1_idem: "HR1(HR1(P)) = HR1(P)"
  by (rel_tac)

lemma HR1_disj: "HR1(P \<or> Q) = (HR1(P) \<or> HR1(Q))"
  by (rel_tac)

lemma HR1_extend_conj: "HR1(P \<and> Q) = (HR1(P) \<and> Q)"
  by (rel_tac)

lemma HR1_extend_conj': "HR1(P \<and> Q) = (P \<and> HR1(Q))"
  by (rel_tac)

lemma HR1_HR3_commute: "HR1(HR3(P)) = HR3(HR1(P))"
  by (rel_tac)

lemma HR2s_TI1_commute: "HR2s(TI1(P)) = TI1(HR2s(P))"
  by (rel_tac)

definition [upred_defs]: "HR(P) = HR1(HR2s(HR3(P)))"

lemma HR_R2c_def: "HR(P) = HR1(HR2c(HR3(P)))"
  by (rel_tac)

lemma HR1_hskip:"HR1(II\<^sub>H) = II\<^sub>H"
  by (rel_tac)

lemma R2c_tr'_minus_tr: "R2c($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_tac) using list_minus_anhil by blast

lemma R2c_condr: "R2c(P \<triangleleft> b \<triangleright> Q) = (R2c(P) \<triangleleft> R2c(b) \<triangleright> R2c(Q))"
  by (rel_tac)

lemma R2c_skip_r: "R2c(II) = II"
proof -
  have "R2c(II) = R2c($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (subst skip_r_unfold[of tr], simp_all)
  also have "... = (R2c($tr\<acute> =\<^sub>u $tr) \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2c_def R2s_def usubst unrest, 
        metis LNil_def cond_idem eq_upred_sym tr'_minus_tr_prefix)
  also have "... = ($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2c_tr'_minus_tr)
  finally show ?thesis
    by (subst skip_r_unfold[of tr], simp_all)
qed

lemma R2s_skip_r: "R2s(II) = II"
proof -
  have "R2s(II) = R2s($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (subst skip_r_unfold[of tr], simp_all)
  also have "... = (R2s($tr\<acute> =\<^sub>u $tr) \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2s_def usubst unrest)
  also have "... = ($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2s_tr'_eq_tr)
  finally show ?thesis
    by (subst skip_r_unfold[of tr], simp_all)
qed

lemma R2c_hskip:
  "R2c(II\<^sub>H) = II\<^sub>H"
  by (simp add: II\<^sub>H_def R2c_disj R2c_skip_r, rel_tac)

lemma R2c_HR1_true:
  "R2c(HR1(true)) = HR1(true)"
  by (rel_tac)

lemma R2c_not_ok: "R2c(\<not> $ok) = (\<not> $ok)"
  by (rel_tac)

lemma HR2c_hskip:
  "HR2c(II\<^sub>H) = II\<^sub>H"
  by (simp add: II\<^sub>H_def HR2c_def TI2_disj TI2_conj TI2_not_ok TI2_HR1_true TI2_skip  
                R2c_disj R2c_and R2c_skip_r R2c_HR1_true R2c_not_ok)

lemma HR3_hskip: "HR3(II\<^sub>H) = II\<^sub>H"
  by (rel_tac)

lemma HR_hskip: "HR(II\<^sub>H) = II\<^sub>H"
  by (simp add: HR_R2c_def HR3_hskip HR2c_hskip HR1_hskip)

lemma H2_hskip: "H2(II\<^sub>H) = II\<^sub>H"
  by (rel_tac, simp add: alpha_d.equality)

definition [upred_defs]: "HCSP1(P) = (P \<or> \<not> $ok \<and> HR1(true))"

lemma HCSP1_idem: "HCSP1(HCSP1(P)) = HCSP1(P)"
  by (rel_tac)

lemma HCSP1_hskip: "HCSP1(II\<^sub>H) = II\<^sub>H"
  by (rel_tac)

abbreviation (input) "HCSP2(P) \<equiv> H2(P)"

abbreviation  "HCSP(P) \<equiv> HCSP1(HCSP2(HR(P)))"

lemma TI1_H2_commute: "TI1(H2(P)) = H2(TI1(P))"
  by (rel_tac)

lemma HR1_H2_commute: "HR1(H2(P)) = H2(HR1(P))"
  by (simp add: HR1_def R1_H2_commute TI1_H2_commute)

lemma HCSP1_HR1_H1: 
  "HR1(H1(P)) = HCSP1(HR1(P))"
  by rel_tac

definition
  "Wait n = HR(true \<turnstile> ((($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<L> <\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) \<diamondop> 
                        ($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<L> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)))))"

definition "hlift(s) = HR(true \<turnstile> \<lceil>\<langle>s\<rangle>\<^sub>a\<rceil>\<^sub>H \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute>)"

fun time_trel :: "_ \<times> _ \<Rightarrow> _ \<Rightarrow> _ \<times> _ \<Rightarrow> bool" (infix "\<leadsto>[_]\<^sub>h" 85) where
"(\<sigma>, P) \<leadsto>[t]\<^sub>h (\<rho>, Q) \<longleftrightarrow> (hlift(\<sigma>) ;; P) \<sqsubseteq> (hlift(\<rho>) ;; Wait t ;; Q)"

lemma HR1_HR3_design:
  "HR1(HR3(P \<turnstile> Q)) = HR1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by (rel_tac, simp_all add: alpha_d.equality)

lemma HR1_seq: "HR1(HR1(P) ;; HR1(Q)) = (HR1(P) ;; HR1(Q))"
  by (rel_tac)

lemma HR1_design_composition:
  fixes P Q :: "('t::linordered_ring, '\<theta>, '\<alpha>, '\<beta>) hrd"
  and R S :: "('t, '\<theta>, '\<beta>, '\<gamma>) hrd"
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows
  "(HR1(P \<turnstile> Q) ;; HR1(R \<turnstile> S)) = 
   HR1((\<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; HR1(\<not> R))) \<turnstile> (HR1(Q) ;; HR1(S)))"
proof -
  have "(HR1(P \<turnstile> Q) ;; HR1(R \<turnstile> S)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (HR1(P \<turnstile> Q))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (HR1(R \<turnstile> S))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    using seqr_middle uvar_ok by blast
  also from assms have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> HR1(($ok \<and> P) \<Rightarrow> (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> Q)) ;; HR1((\<guillemotleft>ok\<^sub>0\<guillemotright>  \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))"
    by (simp add: design_def HR1_def TI1_def R1_def usubst unrest)
  also from assms have "... = ((HR1(($ok \<and> P) \<Rightarrow> (true \<and> Q)) ;; HR1((true \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (HR1(($ok \<and> P) \<Rightarrow> (false \<and> Q)) ;; HR1((false \<and> R) \<Rightarrow> ($ok\<acute> \<and> S))))"
    by (simp add: false_alt_def true_alt_def)
  also from assms have "... = ((HR1(($ok \<and> P) \<Rightarrow> Q) ;; HR1(R \<Rightarrow> ($ok\<acute> \<and> S))) 
                             \<or> (HR1(\<not> ($ok \<and> P)) ;; HR1(true)))"
    by simp
  also from assms have "... = ((HR1(\<not> $ok \<or> \<not> P \<or> Q) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                             \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: impl_alt_def utp_pred.sup.assoc)
  also from assms have "... = (((HR1(\<not> $ok \<or> \<not> P) \<or> HR1(Q)) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj utp_pred.disj_assoc)
  also from assms have "... = ((HR1(\<not> $ok \<or> \<not> P) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (HR1(Q) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: seqr_or_distl utp_pred.sup.assoc)
  also from assms have "... = ((HR1(Q) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by rel_tac
  also from assms have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> HR1(S) \<and> $ok\<acute>)) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj HR1_extend_conj utp_pred.inf_commute)
  also have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> HR1(S) \<and> $ok\<acute>)) 
                  \<or> ((HR1(\<not> $ok) :: ('t,'\<theta>,'\<alpha>,'\<beta>) hrd) ;; HR1(true)) 
                  \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj seqr_or_distl)
  also have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> HR1(S) \<and> $ok\<acute>)) 
                  \<or> (HR1(\<not> $ok))
                  \<or> (HR1(\<not> P) ;; HR1(true)))"
  proof -
    have "((HR1(\<not> $ok) :: ('t,'\<theta>,'\<alpha>,'\<beta>) hrd) ;; HR1(true)) = 
           (HR1(\<not> $ok) :: ('t,'\<theta>,'\<alpha>,'\<gamma>) hrd)"
      by (rel_tac, metis alpha_d.select_convs(2) alpha_rp'.select_convs(2) alpha_rp'.select_convs(4) htime.select_convs(1) order_refl)
    thus ?thesis
      by simp
  qed
  also have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> (HR1(S \<and> $ok\<acute>)))) 
                  \<or> HR1(\<not> $ok)
                  \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: HR1_extend_conj)
  also have "... = ( (HR1(Q) ;; (HR1 (\<not> R)))
                   \<or> (HR1(Q) ;; (HR1(S \<and> $ok\<acute>)))
                   \<or> HR1(\<not> $ok)
                   \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: seqr_or_distr utp_pred.sup.assoc)
  also have "... = HR1( (HR1(Q) ;; (HR1 (\<not> R)))
                     \<or> (HR1(Q) ;; (HR1(S \<and> $ok\<acute>)))
                     \<or> (\<not> $ok)
                     \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj HR1_seq)
  also have "... = HR1( (HR1(Q) ;; (HR1 (\<not> R)))
                     \<or> ((HR1(Q) ;; HR1(S)) \<and> $ok\<acute>)
                     \<or> (\<not> $ok)
                     \<or> (HR1(\<not> P) ;; HR1(true)))"
  proof -
    have "(HR1(Q) ;; (HR1(S \<and> $ok\<acute>))) = ((HR1(Q) ;; HR1(S)) \<and> $ok\<acute>)"
      by (simp add: HR1_extend_conj, rel_tac)
    thus ?thesis
      by (simp)
  qed
  also have "... = HR1(\<not>($ok \<and> \<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; (HR1 (\<not> R))))
                     \<or>  ((HR1(Q) ;; HR1(S)) \<and> $ok\<acute>))"
    by (simp add: utp_pred.sup_commute utp_pred.sup_left_commute)
    
  also have "... = HR1(($ok \<and> \<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; (HR1 (\<not> R))))
                      \<Rightarrow> ($ok\<acute> \<and> (HR1(Q) ;; HR1(S))))"
    by (simp add: impl_alt_def utp_pred.inf_commute)
  also have "... = HR1((\<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; HR1(\<not> R))) \<turnstile> (HR1(Q) ;; HR1(S)))"
    by (simp add: design_def)
  finally show ?thesis .
qed

lemma HR3_semir_form:
  "(HR3 P ;; HR3(HR1(Q))) = HR3 (P ;; HR3(HR1(Q)))"
  by (rel_tac)

lemma HR3_HR1_design_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(HR3(HR1(P \<turnstile> Q)) ;; HR3(HR1(R \<turnstile> S))) = 
       HR3(HR1((\<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> ((HR1(Q) \<and> \<not> $wait\<acute>) ;; HR1(\<not> R))) 
       \<turnstile> (HR1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1(S)))))"
proof -
  have 1:"(\<not> (HR1 (\<not> R3c_pre P) ;; HR1 true)) = (R3c_pre (\<not> (HR1 (\<not> P) ;; HR1 true)))"
    by rel_tac
  have 2:"(\<not> (HR1 (R3c_post Q) ;; HR1 (\<not> R3c_pre R))) = R3c_pre(\<not> (HR1 Q \<and> \<not> $wait\<acute> ;; HR1 (\<not> R)))"
    by rel_tac
  have 3:"(HR1 (R3c_post Q) ;; HR1 (R3c_post S)) = R3c_post (HR1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 S))"
    by rel_tac
  show ?thesis
    apply (simp add: HR3_semir_form HR1_HR3_commute[THEN sym] HR1_HR3_design unrest)
    apply (subst HR1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma HR2s_design: "HR2s(P \<turnstile> Q) = (HR2s(P) \<turnstile> HR2s(Q))"
  by (simp add: design_def HR2s_def R2s_def usubst TI2_def)

lemma HR2c_design: "HR2c(P \<turnstile> Q) = (HR2c(P) \<turnstile> HR2c(Q))"
  by (rel_tac)

lemma HR2s_disj: "HR2s(P \<or> Q) = (HR2s(P) \<or> HR2s(Q))"
  by (rel_tac)

lemma HR2s_conj: "HR2s(P \<and> Q) = (HR2s(P) \<and> HR2s(Q))"
  by (rel_tac)

lemma HR2s_not: "HR2s(\<not> P) = (\<not> (HR2s P))"
  by (rel_tac)

lemma R2_skip_ti: "R2(II\<^sub>H) = II\<^sub>H"
  apply (simp add: II\<^sub>H_def R2_def R2s_conj R2s_disj R2s_skip_r R2s_nok)
  apply (metis (mono_tags, hide_lams) HR1_def HR2s_TI1_commute HR2s_def HR3_hskip HR_def HR_hskip II\<^sub>H_def R2s_conj R2s_disj R2s_nok R2s_skip_r TI1_R1_commute TI1_skip_ti TI2_skip_ti)
done

lemma R2_HR3_commute: "R2(HR3(P)) = HR3(R2(P))"
  by (simp add: HR3_def R2_skip_ti R2_condr' R2s_wait)

lemma HR2_alt_def: "HR2(P) = R1(HR2s(P))"
  by (rel_tac)

lemma HR2_HR3_commute: "HR2(HR3(P)) = HR3(HR2(P))"
  by (simp add: HR2_def R2_HR3_commute TI2_HR3_commute)

lemma R1_HR3_commute: "R1(HR3(P)) = HR3(R1(P))"
  by (rel_tac)

lemma HR2c_HR1_true: "HR2c(HR1(true)) = HR1(true)"
  by (rel_tac)

lemma unrest_ok_HR2s [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> HR2s(P)"
  by (simp add: HR2s_def R2s_def TI2_def unrest)

lemma unrest_ok'_HR2s [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> HR2s(P)"
  by (simp add: HR2s_def R2s_def TI2_def unrest)

lemma TI2_form:
  "TI2(P) = (\<^bold>\<exists> t \<bullet> P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<guillemotright>/$time\<acute>\<rbrakk> \<and> $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<guillemotright>)"
  by (rel_tac)

lemma TI1_TI2_form:
  "TI1(TI2(P)) = (\<^bold>\<exists> t \<bullet> P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<guillemotright>/$time\<acute>\<rbrakk> \<and> $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
  by (rel_tac)

lemma TI2_seqr_form: 
  shows "(TI2(P) ;; TI2(Q)) = 
         (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                        \<and> ($time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>))"
proof -
  have "(TI2(P) ;; TI2(Q)) = (\<^bold>\<exists> t\<^sub>0 \<bullet> (TI2(P))\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$time\<acute>\<rbrakk> ;; (TI2(Q))\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$time\<rbrakk>)"
    by (subst seqr_middle[of time], simp_all)
  also have "... =
       (\<^bold>\<exists> t\<^sub>0 \<bullet> \<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright>) ;; 
                             (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk> \<and> $time\<acute> =\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>)))"
    by (simp add: TI2_form usubst unrest, rel_tac)
  also have "... =
       (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> \<^bold>\<exists> t\<^sub>0 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                             \<and> \<guillemotleft>t\<^sub>0\<guillemotright> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> \<and> $time\<acute> =\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>)"
    by rel_tac
  also have "... =
       (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                        \<and> (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> \<and> $time\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>))"
    by rel_tac
  also have "... =
       (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                        \<and> ($time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>))"
    by rel_tac
  finally show ?thesis .
qed

lemma TI1_TI2_seqr_form:
  "(TI1(TI2(P)) ;; TI1(TI2(Q))) 
        = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                       \<and> ($time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>) \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
  apply (simp add: TI1_TI2_commute TI2_seqr_form)
  apply (simp add: TI1_def usubst)
  apply (rel_tac)
done
 
lemma time'_minus_form: "($time\<acute> - $time =\<^sub>u v) = ($time\<acute> =\<^sub>u $time + v)"
  by (pred_tac, metis add.commute diff_add_cancel)

lemma TI2_seq:
  "TI2(TI2(P) ;; TI2(Q)) = (TI2(P) ;; TI2(Q))"
  apply (simp add: TI2_seqr_form)
  apply (simp add: TI2_def usubst unrest time'_minus_form add.assoc)
done

lemma ok_time_ords [usubst]:
  "$ok <\<^sub>v $time" "$ok\<acute> <\<^sub>v $time" "$ok <\<^sub>v $time\<acute>" "$ok\<acute> <\<^sub>v $time\<acute>"
  by (simp_all add: var_name_ord_def)

lemma time_tr_ords [usubst]:
  "$time <\<^sub>v $tr" "$time\<acute> <\<^sub>v $tr\<acute>" "$time <\<^sub>v $tr\<acute>" "$time\<acute> <\<^sub>v $tr"
  by (simp_all add: var_name_ord_def)

lemma tr_wait_ords [usubst]: 
  "$tr <\<^sub>v $wait" "$tr\<acute> <\<^sub>v $wait\<acute>" "$tr <\<^sub>v $wait\<acute>" "$tr <\<^sub>v $wait"
  by (simp_all add: var_name_ord_def)

lemma time_wait_ords [usubst]: 
  "$time <\<^sub>v $wait" "$time\<acute> <\<^sub>v $wait\<acute>" "$time <\<^sub>v $wait\<acute>" "$time <\<^sub>v $wait"
  by (simp_all add: var_name_ord_def)

lemma R2s_TI2_commute: "R2s(TI2(P)) = TI2(R2s(P))"
  by (simp add: R2s_def TI2_def usubst)
  
lemma R2_TI2_commute: "R2(TI2(P)) = TI2(R2(P))"
  by (simp add: R2_def R2s_TI2_commute TI2_R1_commute)

lemma HR2_seq:
  "HR2(HR2(P) ;; HR2(Q)) = (HR2(P) ;; HR2(Q))"
  by (metis (no_types, lifting) HR2_def R2_TI2_commute R2_seqr_distribute TI2_seq)

lemma HR2_HR1_true: "HR2(HR1(true)) = HR1(true)"
  by (rel_tac)

lemma HR1_HR2s: "HR1(HR2s(P)) = HR1(HR2(P))"
  by (simp add: HR1_def HR2_alt_def R1_idem)

lemma HR2c_not: "HR2c(\<not> P) = (\<not> HR2c(P))"
  by (rel_tac)

lemma HR2c_and: "HR2c(P \<and> Q) = (HR2c(P) \<and> HR2c(Q))"
  by (rel_tac)

lemma HR2c_HR1: "HR2c(HR1(P)) = HR2(HR1(P))"
  by (rel_tac)

lemma HR1_HR2_commute: "HR1(HR2(P)) = HR2(HR1(P))"
  by (rel_tac)

lemma HR2s_wait: "HR2s($wait) = $wait"
  by (rel_tac)

lemma HR2s_wait': "HR2s($wait\<acute>) = $wait\<acute>"
  by (rel_tac)

lemma HR2s_skip_lift_d: "HR2s(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
apply (rel_tac)
by (smt alpha_rp'.ext_inject alpha_rp'.surjective alpha_rp'.update_convs(2) alpha_rp'.update_convs(4) eq_iff_diff_eq_0 htime.ext_inject htime.surjective htime.update_convs(1) list_minus_anhil)

lemma HR2s_cond: "HR2s(P \<triangleleft> b \<triangleright> Q) = (HR2s(P) \<triangleleft> HR2s(b) \<triangleright> HR2s(Q))"
  by (simp add: cond_def HR2s_conj HR2s_disj HR2s_not)
  
lemma HR_HR2c_def: "HR(P) = HR3(HR1(HR2c(P)))"
  by (metis (no_types, hide_lams) HR1_HR2_commute HR1_HR2s HR1_HR3_commute HR1_extend_conj' HR2_HR3_commute HR2c_HR1 HR2c_HR1_true HR2c_and HR_def utp_pred.inf_top_right)

lemma HR_design_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(HR(P \<turnstile> Q) ;; HR(R \<turnstile> S)) = 
       HR((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S))))"
proof -
  have 1: "HR2c (HR1 (\<not> HR2s P) ;; HR1 true) = (HR1 (\<not> HR2s P) ;; HR1 true)"
  proof -
    have "HR2c (HR1 (\<not> HR2s P) ;; HR1 true) = HR1(HR2(HR1 (\<not> HR2s P) ;; HR1 true))"
      by (metis HR1_HR2_commute HR1_seq HR2c_HR1)
    also have "... = HR1(HR2(HR2(HR1(\<not> P)) ;; HR2(HR1(true))))"
      by (metis (no_types, lifting) HR1_HR2_commute HR1_HR2s HR2_HR1_true HR2s_def R2s_not TI2_not)
    also have "... = (HR2(HR1(\<not> P)) ;; HR2(HR1(true)))"
      by (metis (mono_tags, lifting) HR1_HR2_commute HR1_seq HR2_seq)
    also have "... =  (HR1 (\<not> HR2s P) ;; HR1 true)"
      by (metis (no_types, hide_lams) HR1_HR2_commute HR1_HR2s HR2_HR1_true HR2s_def R2s_not TI2_not)
    finally show ?thesis .
  qed

  have 2:"HR2c (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R)) = (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))"
  proof -
    have "HR2c (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R)) = HR1 (HR2 (HR1 (HR2s (Q \<and> \<not> $wait\<acute>)) ;; HR1 (\<not> HR2s R)))"
      by (metis (no_types, lifting) HR1_HR2_commute HR1_extend_conj HR1_seq HR2c_HR1 HR2s_conj HR2s_not HR2s_wait')
    also have "... = HR1 (HR2 (HR2 (HR1 (Q \<and> \<not> $wait\<acute>)) ;; HR2 (HR1 (\<not> R))))"
      by (metis (no_types, hide_lams) HR1_HR2_commute HR1_HR2s HR2s_not)
    also have "... = (HR2 (HR1 (Q \<and> \<not> $wait\<acute>)) ;; HR2 (HR1 (\<not> R)))"
      by (metis (no_types, lifting) HR1_HR2_commute HR1_seq HR2_seq)
    also have "... = (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))"
      by (metis (no_types, lifting) HR1_HR2_commute HR1_HR2s HR1_extend_conj HR2s_conj HR2s_not HR2s_wait')
    finally show ?thesis .
  qed

  have 3: "HR2c(HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S))) = (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S)))"
    sorry

  have "(HR1(HR2s(HR3(P \<turnstile> Q))) ;; HR1(HR2s(HR3(R \<turnstile> S)))) =
        (HR3(HR1(HR2s(P) \<turnstile> HR2s(Q))) ;; HR3(HR1(HR2s(R) \<turnstile> HR2s(S))))"
    by (metis (no_types, lifting) HR1_def HR2_HR3_commute HR1_HR3_commute R1_HR3_commute HR2_alt_def HR2s_design)
  also have "... = HR3 (HR1 ((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S)))))"
    by (simp add: HR3_HR1_design_composition unrest assms)

  also have "... = HR3(HR1(HR2c((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                              (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S))))))"
    by (simp add: HR2c_design HR2c_and HR2c_not 1 2 3)
  finally show ?thesis
    by (metis HR_HR2c_def HR_def)
qed

lemma wait'_cond_true: "(P \<diamondop> Q \<and> $wait\<acute>) = (P \<and> $wait\<acute>)" 
  by (rel_tac)

lemma wait'_cond_false: "(P \<diamondop> Q \<and> (\<not>$wait\<acute>)) = (Q \<and> (\<not>$wait\<acute>))" 
  by (rel_tac)    

lemma HR1_false: "HR1(false) = false"
  by (pred_tac)

lemma HR2s_true: "HR2s(true) = true"
  by (pred_tac)

lemma HR2s_not_wait': "HR2s(\<not>$wait\<acute>) = (\<not>$wait\<acute>)"
  by rel_tac

lemma HR2s_tr'_eq_tr: "HR2s($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_tac)
  using list_minus_anhil apply blast
done

lemma HR2s_ref'_eq_ref: "HR2s($ref\<acute> =\<^sub>u $ref) = ($ref\<acute> =\<^sub>u $ref)"
  by (rel_tac)

lemma HR2s_hy'_eq_hy: "HR2s ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H) = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H)"
  by (rel_tac)

lemma HR_des_eqI: "\<lbrakk> P = R; Q = S \<rbrakk> \<Longrightarrow> HR(P \<turnstile> Q) = HR(R \<turnstile> S)"
  by (simp)

lemma HR_des_tri_eqI: "\<lbrakk> P = R; Q\<^sub>1 = S\<^sub>1; Q\<^sub>2 = S\<^sub>2 \<rbrakk> \<Longrightarrow> HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) = HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)"
  by (simp)

lemma HR2s_dur: "HR2s(\<L>) = \<L>"
  by (rel_tac)

lemma HR2s_bop: "HR2s(bop f u v) = bop f (HR2s(u)) (HR2s(v))"
  by (pred_tac)

lemma HR2s_ueq: "HR2s(u =\<^sub>u v) = (HR2s(u) =\<^sub>u HR2s(v))"
  by pred_tac

lemma HR2s_pre_lit: "HR2s \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< = \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub><"
  by (pred_tac)

lemma HR1_subst_wait'_true [usubst]: "(HR1(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = (HR1(P\<lbrakk>true/$wait\<acute>\<rbrakk>))"
  by (rel_tac)

lemma HR1_subst_wait'_false [usubst]: "(HR1(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = (HR1(P\<lbrakk>false/$wait\<acute>\<rbrakk>))"
  by (rel_tac)

 
lemma HR2s_subst_wait'_true [usubst]: "(HR2s(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = (HR2s(P\<lbrakk>true/$wait\<acute>\<rbrakk>))"
  by (simp add: HR2s_def usubst R2s_def TI2_def)

lemma HR2s_subst_wait'_false [usubst]: "(HR2s(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = (HR2s(P\<lbrakk>false/$wait\<acute>\<rbrakk>))"
  by (simp add: HR2s_def usubst R2s_def TI2_def)

lemma HR1_wait'_cond: "HR1(P \<diamondop> Q) = HR1(P) \<diamondop> HR1(Q)"
  by rel_tac

lemma HR2s_wait'_cond: "HR2s(P \<diamondop> Q) = HR2s(P) \<diamondop> HR2s(Q)"
  by (simp add: wait'_cond_def HR2s_def R2s_def TI2_def usubst)

lemma wait'_cond_seq: "((P \<diamondop> Q) ;; R) = ((P ;; $wait \<and> R) \<or> (Q ;; \<not>$wait \<and> R))"
  by (simp add: wait'_cond_def cond_def seqr_or_distl, rel_tac)

lemma subst_wait'_cond_true [usubst]: "(P \<diamondop> Q)\<lbrakk>true/$wait\<acute>\<rbrakk> = P\<lbrakk>true/$wait\<acute>\<rbrakk>"
  by rel_tac

lemma subst_wait'_cond_false [usubst]: "(P \<diamondop> Q)\<lbrakk>false/$wait\<acute>\<rbrakk> = Q\<lbrakk>false/$wait\<acute>\<rbrakk>"
  by rel_tac  

lemma lift_des_skip_dr_unit_unrest: "$ok\<acute> \<sharp> P \<Longrightarrow> (P ;; \<lceil>II\<rceil>\<^sub>D) = P"
  by (rel_tac, metis alpha_d.surjective alpha_d.update_convs(1))

lemma TI1_unrest [unrest]: "\<lbrakk> x \<sharp> P; in_var time \<bowtie> x; out_var time \<bowtie> x \<rbrakk> \<Longrightarrow> x \<sharp> TI1(P)"
  by (simp add: TI1_def R1_def unrest)

lemma HR1_unrest [unrest]: "\<lbrakk> x \<sharp> P; in_var tr \<bowtie> x; out_var tr \<bowtie> x; in_var time \<bowtie> x; out_var time \<bowtie> x \<rbrakk> \<Longrightarrow> x \<sharp> HR1(P)"
  by (simp add: HR1_def TI1_def R1_def unrest)

lemma HR2s_unrest [unrest]: "\<lbrakk> uvar x; x \<sharp> P; in_var tr \<bowtie> x; out_var tr \<bowtie> x; in_var time \<bowtie> x; out_var time \<bowtie> x \<rbrakk> \<Longrightarrow> x \<sharp> HR2s(P)"
  by (simp add: HR2s_def R2s_def TI2_def unrest lens_indep_sym)

lemma HR2s_H1_commute: "HR2s(H1(P)) = H1(HR2s(P))"
  by (rel_tac)

lemma TI2_H2_commute: "TI2(H2(P)) = H2(TI2(P))"
  by (simp add: H2_split TI2_def usubst unrest)

lemma HR2s_H2_commute: "HR2s(H2(P)) = H2(HR2s(P))"
  by (simp add: HR2s_def TI2_H2_commute R2s_H2_commute)

lemma hskip_non_term:
  "II\<^sub>H\<^sup>f = (\<not> $ok \<and> HR1(true))"
  by (rel_tac)

lemma HR3_H2_commute: "HR3(H2(P)) = H2(HR3(P))"
  by (rel_tac, simp_all add: alpha_d.equality)

lemma HR1_H1_HR3_commute: "HR1(H1(HR3(P))) = HR3(HR1(H1(P)))"
  by (rel_tac)

thm R3c_subst_wait

lemma HR3_subst_wait: "HR3(P) = HR3(P\<lbrakk>false/$wait\<rbrakk>)"
  by (metis HR3_def cond_var_subst_right wait_uvar)

lemma HCSP_hybrid_reactive_design:
  assumes "P is HCSP"
  shows "P = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "P = HCSP1(H2(HR1(HR2s(HR3(P)))))"
    by (metis HR_def Healthy_def assms)
  also have "... = HCSP1(HR1(H2(HR2s(HR3(P)))))"
    by (simp add: HR1_H2_commute)
  also have "... = HR1(H1(HR1(H2(HR2s(HR3(P))))))"
    by (simp add: HCSP1_HR1_H1 HR1_idem)
  also have "... = HR1(H1(H2(HR2s(HR3(HR1(P))))))"
    by (simp add: HCSP1_HR1_H1 HR1_H2_commute HR1_HR2_commute HR1_HR2s HR1_HR3_commute)
  also have "... = HR1(HR2s(H1(H2(HR3(HR1(P))))))"
    by (simp add: HR2s_H1_commute HR2s_H2_commute)
  also have "... = HR1(HR2s(H1(HR3(H2(HR1(P))))))"
    by (simp add: HR3_H2_commute)
  also have "... = HR2(HR1(H1(HR3(H2(HR1(P))))))"
    by (simp add: HR1_HR2_commute HR1_HR2s)
  also have "... = HR2(HR3(HR1(H1(H2(HR1(P))))))"
    by (simp add: HR1_H1_HR3_commute)
  also have "... = HR(H1_H2(HR1(P)))"
    by (simp add: HR1_HR2_commute HR1_HR2s HR1_HR3_commute HR_def)
  also have "... = HR(H1_H2(P))"
    by (metis HR1_idem HR_def calculation)
  also have "... = HR((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
  proof -
    have 0:"(\<not> (H1_H2(P))\<^sup>f) = ($ok \<and> \<not> P\<^sup>f)"
      by (simp add: H1_def H2_split, pred_tac)
    have 1:"(H1_H2(P))\<^sup>t = ($ok \<Rightarrow> (P\<^sup>f \<or> P\<^sup>t))"
      by (simp add: H1_def H2_split, pred_tac)
    have "(\<not> (H1_H2(P))\<^sup>f) \<turnstile> (H1_H2(P))\<^sup>t = ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
      by (simp add: 0 1, pred_tac)
    thus ?thesis
      by (metis H1_H2_commute H1_H2_is_design H1_idem H2_idem Healthy_def')
  qed
  also have "... = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis HR3_subst_wait HR_def subst_not wait_false_design)
  finally show ?thesis .
qed

lemma R2c_wait: "R2c($wait) = $wait"
  by (rel_tac)

(* TODO: Do this proof properly *)

lemma hskip_reactive_design:
  "II\<^sub>H = HR(true \<turnstile> II)"
proof -
  have 1:"TI2 (true \<turnstile> II) = (true \<turnstile> II)"
    by (simp add: design_def impl_alt_def TI2_disj TI2_not_ok TI2_conj TI2_skip, rel_tac)
  have 2:"R2c (true \<turnstile> II) = (true \<turnstile> II)"
    by (rel_tac, smt alpha_d.surjective alpha_d.update_convs(2) alpha_rp'.surjective alpha_rp'.update_convs(2) append_Nil2 prefix_subst1 strict_prefixE)
  have 3: "HR1(II\<^sub>H \<triangleleft> $wait \<triangleright> true \<turnstile> II) = II\<^sub>H"
    by (rel_tac)
  show ?thesis
    by (simp add: HR2c_def TI2_cond TI2_wait TI2_skip_ti HR_R2c_def HR3_def R2c_condr R2c_hskip R2c_wait 1 2 3)
qed

lemma HR_design_tri_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait\<acute> \<sharp> Q\<^sub>1" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = 
       HR((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       ((HR1 (HR2s Q\<^sub>1) \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> ((HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> (HR1 (HR2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) = 
        (\<not> (HR1 (HR2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R)))"
    by (metis (no_types, lifting) HR1_extend_conj HR2s_conj HR2s_not_wait' wait'_cond_false)
  have 2: "(HR1 (HR2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 ((HR1 (HR2s Q\<^sub>1) \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))"
  proof -
    have "(HR1 (HR2s Q\<^sub>1) ;; $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))
                       = (HR1 (HR2s Q\<^sub>1) \<and> $wait\<acute>)"
    proof -
      have "(HR1 (HR2s Q\<^sub>1) ;; $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2))) 
           = (HR1 (HR2s Q\<^sub>1) ;; $wait \<and> \<lceil>II\<rceil>\<^sub>D)"
        by (rel_tac)
      also have "... = ((HR1 (HR2s Q\<^sub>1) ;; \<lceil>II\<rceil>\<^sub>D) \<and> $wait\<acute>)"
        by (rel_tac)
      also from assms(2) have "... = ((HR1 (HR2s Q\<^sub>1)) \<and> $wait\<acute>)"
        by (simp add: lift_des_skip_dr_unit_unrest unrest)
      finally show ?thesis .
    qed
 
    moreover have "(HR1 (HR2s Q\<^sub>2) ;; \<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))
                  = ((HR1 (HR2s Q\<^sub>2)) ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))"
    proof - 
      have "(HR1 (HR2s Q\<^sub>2) ;; \<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))
            = (HR1 (HR2s Q\<^sub>2) ;; \<not> $wait \<and> (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))"
        by (metis (no_types, lifting) cond_def conj_disj_not_abs utp_pred.double_compl utp_pred.inf.left_idem utp_pred.sup_assoc utp_pred.sup_inf_absorb)

      also have "... = ((HR1 (HR2s Q\<^sub>2))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2))\<lbrakk>false/$wait\<rbrakk>)"
        by (metis false_alt_def seqr_right_one_point upred_eq_false wait_uvar)

      also have "... = ((HR1 (HR2s Q\<^sub>2)) ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms)
      
      finally show ?thesis .
    qed
      
    moreover
    have "((HR1 (HR2s Q\<^sub>1) \<and> $wait\<acute>) \<or> ((HR1 (HR2s Q\<^sub>2)) ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2))))
          = (HR1 (HR2s Q\<^sub>1) \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> ((HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))"
      by (simp add: wait'_cond_def cond_seq_right_distr cond_and_T_integrate unrest)

    ultimately show ?thesis
      by (simp add: HR2s_wait'_cond HR1_wait'_cond wait'_cond_seq)
  qed

  show ?thesis
    apply (subst HR_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2)
  done
qed

(*
lemma HR_design_tri_composition_frame: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait\<acute> \<sharp> Q\<^sub>1" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(HR(w:\<lbrakk>P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2\<rbrakk>) ;; HR(w:\<lbrakk>R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2\<rbrakk>)) = 
       HR((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       ((HR1 (HR2s Q\<^sub>1) \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> ((HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))))"
*)

lemma HR2s_time'_time_eq: "HR2s ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) = ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
  by (rel_tac)

lemma HR2s_time'_time_less: "HR2s ($time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) = ($time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
  by (rel_tac)
 
lemma R1_extend_conj_unrest: "\<lbrakk> $tr \<sharp> Q; $tr\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> R1(P \<and> Q) = (R1(P) \<and> Q)"
  by pred_tac

lemma R1_extend_conj_unrest': "\<lbrakk> $tr \<sharp> P; $tr\<acute> \<sharp> P \<rbrakk> \<Longrightarrow> R1(P \<and> Q) = (P \<and> R1(Q))"
  by pred_tac

lemma R1_tr'_eq_tr: "R1($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_tac)

lemma hy_lift_unrest [unrest]: "$\<Sigma>\<^sub>H\<acute> \<sharp> \<lceil>\<lceil>P\<rceil>\<^sub><\<rceil>\<^sub>H"
  by (rel_tac)

lemma aext_seq [alpha]:
  "wb_lens a \<Longrightarrow> ((P ;; Q) \<oplus>\<^sub>p (a \<times>\<^sub>L a)) = ((P \<oplus>\<^sub>p (a \<times>\<^sub>L a)) ;; (Q \<oplus>\<^sub>p (a \<times>\<^sub>L a)))"
  by (rel_tac, metis wb_lens_weak weak_lens.put_get)

lemma aext_upred_eq [alpha]:
  "((e =\<^sub>u f) \<oplus>\<^sub>p a) = ((e \<oplus>\<^sub>p a) =\<^sub>u (f \<oplus>\<^sub>p a))"
  by (pred_tac)

lemma skip_h_lift_def:
  "\<lceil>II\<rceil>\<^sub>H = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H)"
  by (rel_tac)

(*
lemma "($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H ;; $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>) =
       (\<lceil>(II \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<bar>m\<bar>\<rceil>\<^sub><) ;; (II \<and> \<lceil>\<bar>n\<bar>\<rceil>\<^sub>< >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>)\<rceil>\<^sub>H :: ('t::linordered_ring, '\<nu>, '\<alpha>) hhrd)"
       apply (simp add: alpha skip_h_lift_def)
       apply (subst alpha_ext_seq)
       apply (rel_tac)
*)

(*
       (\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>)"
       apply (rel_tac)
       apply (rule_tac x="a" in exI)
*)

abbreviation hseqr :: "'\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" (infixr ";;\<^sub>h" 15) where
"P ;;\<^sub>h Q \<equiv> P ;; Q"

lemma TI1_time_diff_abs: "TI1($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) = ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
  by (rel_tac, metis abs_ge_zero less_iff_diff_less_0 not_le)

lemma Wait_pericondition_lemma1:
  "(($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) ;;\<^sub>h 
        ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time)))
       = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<le>\<^sub>u $time\<acute> - $time \<and> $time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (TI1(TI2($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))) ;;\<^sub>h 
                TI1(TI2($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time)))"
    by (simp add: TI1_conj_right TI2_def usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H ;;\<^sub>h $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: TI1_TI2_seqr_form usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h II \<and> \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: alpha skip_h_lift_def)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub>< \<and> II\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: conj_comm)

  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< \<and> \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub>>\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: seqr_post_transfer unrest conj_assoc)

  also have "... = (\<^bold>\<exists> t \<bullet> \<lceil>II \<and> \<lceil>\<bar>n\<bar>\<rceil>\<^sub>< >\<^sub>u \<guillemotleft>t\<guillemotright>\<rceil>\<^sub>H \<and> $time\<acute> =\<^sub>u $time + \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
    by (rel_tac)

  also have "... = (\<^bold>\<exists> t \<bullet> ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u \<guillemotleft>t\<guillemotright>) \<and> $time\<acute> =\<^sub>u $time + \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: alpha skip_h_lift_def)

  also have "... = (\<^bold>\<exists> t \<bullet> ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u \<guillemotleft>t\<guillemotright>) \<and> $time\<acute> - $time - \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H =\<^sub>u \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
    by (rel_tac)

  also have "... = (($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time - \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and> $time\<acute> - $time - \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<ge>\<^sub>u 0)"
    by (rel_tac)

  also have "... = (($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) \<and> $time\<acute> - $time  \<ge>\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
    by (rel_tac, simp_all add: add.commute diff_less_eq)

  also have "... = (($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) \<and> $time\<acute> - $time  \<ge>\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
    by (simp add: alpha)

  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1($time\<acute> - $time  \<ge>\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time))"
    by (rel_tac, meson abs_ge_zero less_iff_diff_less_0 less_le_trans not_less)

  finally show ?thesis .
qed    

lemma Wait_pericondition_lemma2:
  "($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) \<or>
        ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<le>\<^sub>u $time\<acute> - $time \<and> $time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))) =
    ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time))"
  by (rel_tac, meson abs_ge_zero leD leI le_add_same_cancel1 order.trans)

lemma Wait_postcondition_lemma:
  "($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) ;;\<^sub>h
    $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<L> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) =
   ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (TI1(TI2($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) ;;\<^sub>h TI1(TI2($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<L> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)))"
    by (simp add: TI1_conj_right TI2_def usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H ;;\<^sub>h $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: TI1_TI2_seqr_form usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h II \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: alpha skip_h_lift_def)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<bar>n\<bar>\<rceil>\<^sub>< \<and> II\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: conj_comm)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<bar>m\<bar>\<rceil>\<^sub>< \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: seqr_post_transfer unrest conj_assoc)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: alpha skip_h_lift_def)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time + \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H)" 
    by (rel_tac)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H =\<^sub>u $time\<acute> - $time)"
    by (rel_tac, simp add: add.commute add.left_commute)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H =\<^sub>u $time\<acute> - $time)"
    by (simp add: alpha skip_h_lift_def, rel_tac)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))"
    by (rel_tac, metis abs_ge_zero add_nonneg_nonneg diff_ge_0_iff_ge)
  finally show ?thesis .
qed

lemma Wait_m_plus_n:
  "(Wait m ;; Wait n) = Wait (\<bar>m\<bar> + \<bar>n\<bar>)"
  apply (simp add: Wait_def)
  apply (subst HR_design_tri_composition)
  apply (simp_all add: unrest)
  apply (simp add: HR2s_true HR1_false HR2s_conj HR2s_cond HR2s_tr'_eq_tr HR2s_ref'_eq_ref HR2s_hy'_eq_hy
                   HR2s_wait' HR2s_dur HR2s_pre_lit HR2s_time'_time_eq HR2s_time'_time_less HR2s_TI1_commute)
  apply (rule HR_des_tri_eqI)
  apply (simp)
  apply (simp add: HR1_def R1_extend_conj_unrest R1_extend_conj_unrest' R1_tr'_eq_tr TI1_conj_right unrest)
  apply (simp add: seq_var_ident_lift HR1_extend_conj' unrest eq_cong_left conj_disj_distr[THEN sym] TI1_idem)
  apply (simp add: Wait_pericondition_lemma1 Wait_pericondition_lemma2)
  apply (simp add: HR1_def R1_extend_conj_unrest R1_extend_conj_unrest' R1_tr'_eq_tr TI1_conj_right unrest)
  apply (simp add: seq_var_ident_lift HR1_extend_conj' unrest eq_cong_left conj_disj_distr[THEN sym] TI1_idem)
  using Wait_postcondition_lemma by blast
  
lemma wait'_cond_left_false: "false \<diamondop> P = (\<not> $wait\<acute> \<and> P)"
  by (rel_tac)

lemma skip_hy_conj:
  "($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time) = II"
  by (rel_tac, simp_all add: alpha_d.equality alpha_rp'.equality)

lemma Wait_0: "Wait 0 = (II\<^sub>H :: ('t::linordered_ring, '\<theta>, '\<alpha>) hhrd)" (is "?lhs = ?rhs")
proof -
  have 1:"TI1 (\<lceil>\<lceil>0\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) = (false :: ('t, '\<theta>, '\<alpha>) hhrd)"
    by (rel_tac)
  have 2:"($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>0::('t, '\<alpha>) uexpr\<rceil>\<^sub><\<rceil>\<^sub>H))
         = (($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time) :: ('t, '\<theta>, '\<alpha>) hhrd)"
    by (rel_tac)

  have "?lhs = HR (true \<turnstile> (\<not> $wait\<acute> \<and> $ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time))"
    by (simp add:  Wait_def 1 2 wait'_cond_left_false)
  also have "... = HR (true \<turnstile> ($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time))"
    by (rel_tac) (* REDO -- too slow! *)
  also have "... = ?rhs"
    by (simp add: skip_hy_conj hskip_reactive_design)
  finally show ?thesis .
qed
   

lemma Wait_trel:
  "\<lbrakk> m \<ge> 0; n \<ge> 0 \<rbrakk> \<Longrightarrow> (\<sigma>, Wait (m + n)) \<leadsto>[m]\<^sub>h (\<sigma>, Wait n)"
  by (simp add: Wait_m_plus_n)         


end