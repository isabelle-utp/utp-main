section {* Hybrid reactive designs *}

theory utp_hrd
imports 
  utp_designs
  utp_rea_designs
begin

record 't::linordered_field htime =
  htime :: 't

type_synonym ('t, '\<theta>, '\<alpha>) alphabet_hrd = "('\<theta>, ('t, '\<alpha>) htime_scheme) alphabet_rp"
type_synonym ('t, '\<theta>, '\<alpha>, '\<beta>) hrd = "(('t, '\<theta>, '\<alpha>) alphabet_hrd, ('t, '\<theta>, '\<beta>) alphabet_hrd) relation"

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

definition lift_hrd :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>H") where
"\<lceil>P\<rceil>\<^sub>H = P \<oplus>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

definition drop_hrd :: "_ \<Rightarrow> _" ("\<lfloor>_\<rfloor>\<^sub>H") where
"\<lfloor>P\<rfloor>\<^sub>H = P \<restriction>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

definition "\<L> = $time\<acute> - $time"

definition [upred_defs]: "TI1(P) = (P \<and> $time \<le>\<^sub>u $time\<acute>)"

definition [upred_defs]: "HR1(P) =(TI1(P) \<and> R1(P))"

definition [upred_defs]: "TI2(P) = (P\<lbrakk>0/$time\<rbrakk>\<lbrakk>($time\<acute>-$time)/$time\<acute>\<rbrakk>)"

definition [urel_defs]: "II\<^sub>H = (II \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute> \<and> $time \<le>\<^sub>u $time\<acute>))"

definition [upred_defs]: "HR2(P) = (II\<^sub>H \<triangleleft> $wait \<triangleright> P)"

lemma TI1_skip_ti:
  "TI1(II\<^sub>H) = II\<^sub>H"
  by rel_tac

lemma TI1_idem: "TI1(TI1(P)) = TI1(P)"
  by rel_tac

lemma TI2_idem: "TI2(TI2(P)) = TI2(P)"
  by rel_tac

lemma TI1_TI2_commute:
  "TI1(TI2(P)) = TI2(TI1(P))"
  by rel_tac

lemma TI1_R1_commute:
  "TI1(R1(P)) = R1(TI1(P))"
  by rel_tac

lemma TI2_R1_commute:
  "TI2(R1(P)) = R1(TI2(P))"
  by rel_tac

lemma TI1_HR2_commute:
  "TI1(HR2(P)) = HR2(TI1(P))"
  by rel_tac

lemma TI2_HR2_commute:
  "TI2(HR2(P)) = HR2(TI2(P))"
  apply (simp add: TI2_def HR2_def usubst)


lemma HR1_disj: "HR1(P \<or> Q) = (HR1(P) \<or> HR1(Q))"
  by (rel_tac)

lemma HR1_extend_conj: "HR1(P \<and> Q) = (HR1(P) \<and> Q)"
  by (rel_tac)

definition "HR = RH \<circ> TI2 \<circ> TI1"

definition "Wait n = HR(true \<turnstile> ((\<L> <\<^sub>u n) \<diamondop> (\<L> =\<^sub>u n)) \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $tr\<acute> =\<^sub>u $tr)"

definition "hlift(s) = HR(true \<turnstile> \<lceil>\<langle>s\<rangle>\<^sub>a\<rceil>\<^sub>H \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute>)"

fun time_trel :: "_ \<times> _ \<Rightarrow> _ \<Rightarrow> _ \<times> _ \<Rightarrow> bool" (infix "\<leadsto>[_]\<^sub>h" 85) where
"(\<sigma>, P) \<leadsto>[t]\<^sub>h (\<rho>, Q) \<longleftrightarrow> (hlift(\<sigma>) ;; P) \<sqsubseteq> (hlift(\<rho>) ;; Wait t ;; Q)"

lemma HR1_seq: "HR1(HR1(P) ;; HR1(Q)) = (HR1(P) ;; HR1(Q))"
  by (rel_tac)

lemma HR1_design_composition:
  fixes P Q :: "('t::linordered_semidom, '\<theta>, '\<alpha>, '\<beta>) hrd"
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


lemma hrd_composition:
  assumes "out\<alpha> \<sharp> p\<^sub>1" "p\<^sub>1 is R2" "P\<^sub>2 is R2" "Q\<^sub>1 is R2" "Q\<^sub>2 is R2"
  shows
  "(HR(p\<^sub>1 \<turnstile> Q\<^sub>1) ;; HR(P\<^sub>2 \<turnstile> Q\<^sub>2)) = 
    HR((p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1 (\<not> P\<^sub>2)))
       \<turnstile> ((($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; Q\<^sub>2))))" (is "?lhs = ?rhs")
  oops



lemma "(Wait m ;; Wait n) = Wait (m + n)"
  oops

lemma "(\<sigma>, Wait (m + n)) \<leadsto>[m]\<^sub>h (\<sigma>, Wait n)"
  oops

end