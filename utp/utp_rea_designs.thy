section {* Reactive designs *}

theory utp_rea_designs
  imports utp_reactive
begin

definition wait'_cond :: "_ \<Rightarrow> _ \<Rightarrow> _" (infix "\<diamondop>" 65) where
[upred_defs]: "P \<diamondop> Q = (P \<triangleleft> $wait\<acute> \<triangleright> Q)"

lemma wait_false_design:
  "(P \<turnstile> Q) \<^sub>f = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by (rel_tac)

lemma wait'_cond_subst [usubst]:
  "$wait\<acute> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P \<diamondop> Q) = (\<sigma> \<dagger> P) \<diamondop> (\<sigma> \<dagger> Q)"
  by (simp add: wait'_cond_def usubst unrest)

lemma R2s_ok': "R2s($ok\<acute>) = $ok\<acute>"
  by pred_tac

lemma R2s_nok: "R2s(\<not> $ok) = (\<not> $ok)"
  by (pred_tac)

lemma H2_R1_comm: "H2(R1(P)) = R1(H2(P))"
  by (simp add: H2_split R1_def usubst, rel_tac)

lemma H2_R2s_comm: "H2(R2s(P)) = R2s(H2(P))"
  by (simp add: H2_split R2s_def usubst, rel_tac)  

lemma H2_R2_comm: "H2(R2(P)) = R2(H2(P))"
  by (simp add: H2_R1_comm H2_R2s_comm R2_def)

lemma H2_R3_comm: "H2(R3c(P)) = R3c(H2(P))"
  by (simp add: R3c_H2_commute)

lemma R3c_via_H1: "R1(R3c(H1(P))) = R1(H1(R3(P)))"
  by rel_tac

lemma skip_rea_via_H1: "II\<^sub>r = R1(H1(R3(II)))"
  by rel_tac

text {* Pedro's proof for R1 design composition *}

lemma R1_design_composition:
  fixes P Q :: "('\<theta>,'\<alpha>,'\<beta>) relation_rp"
  and R S :: "('\<theta>,'\<beta>,'\<gamma>) relation_rp"
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = 
   R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
proof -
  have "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (R1(P \<turnstile> Q))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (R1(R \<turnstile> S))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    using seqr_middle uvar_ok by blast
  also from assms have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> R1(($ok \<and> P) \<Rightarrow> (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> Q)) ;; R1((\<guillemotleft>ok\<^sub>0\<guillemotright>  \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))"
    by (simp add: design_def R1_def usubst unrest)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> (true \<and> Q)) ;; R1((true \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (R1(($ok \<and> P) \<Rightarrow> (false \<and> Q)) ;; R1((false \<and> R) \<Rightarrow> ($ok\<acute> \<and> S))))"
    by (simp add: false_alt_def true_alt_def)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> Q) ;; R1(R \<Rightarrow> ($ok\<acute> \<and> S))) 
                             \<or> (R1(\<not> ($ok \<and> P)) ;; R1(true)))"
    by simp
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P \<or> Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                             \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: impl_alt_def utp_pred.sup.assoc)
  also from assms have "... = (((R1(\<not> $ok \<or> \<not> P) \<or> R1(Q)) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj utp_pred.disj_assoc)
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distl utp_pred.sup.assoc)
  also from assms have "... = ((R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by rel_tac
  also from assms have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>)) 
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_extend_conj utp_pred.inf_commute)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>)) 
                  \<or> ((R1(\<not> $ok) :: ('\<theta>,'\<alpha>,'\<beta>) relation_rp) ;; R1(true)) 
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj seqr_or_distl)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>)) 
                  \<or> (R1(\<not> $ok))
                  \<or> (R1(\<not> P) ;; R1(true)))"
  proof -
    have "((R1(\<not> $ok) :: ('\<theta>,'\<alpha>,'\<beta>) relation_rp) ;; R1(true)) = 
           (R1(\<not> $ok) :: ('\<theta>,'\<alpha>,'\<gamma>) relation_rp)"
      by (rel_tac, metis alpha_d.select_convs(2) alpha_rp'.select_convs(2) order_refl)
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
    by (simp add: seqr_or_distr utp_pred.sup.assoc)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> (R1(Q) ;; (R1(S \<and> $ok\<acute>)))
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_seqr)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> ((R1(Q) ;; R1(S)) \<and> $ok\<acute>)
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (rel_tac)
  also have "... = R1(\<not>($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                     \<or>  ((R1(Q) ;; R1(S)) \<and> $ok\<acute>))"
    by (rel_tac)
  also have "... = R1(($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                      \<Rightarrow> ($ok\<acute> \<and> (R1(Q) ;; R1(S))))"
    by (simp add: impl_alt_def utp_pred.inf_commute)
  also have "... = R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
    by (simp add: design_def)
  finally show ?thesis .
qed

definition [upred_defs]: "R3c_pre(P) = (true \<triangleleft> $wait \<triangleright> P)"

definition [upred_defs]: "R3c_post(P) = (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> P)"

lemma R3c_pre_conj: "R3c_pre(P \<and> Q) = (R3c_pre(P) \<and> R3c_pre(Q))"
  by rel_tac

lemma R3c_pre_seq:
  "(true ;; Q) = true \<Longrightarrow> R3c_pre(P ;; Q) = (R3c_pre(P) ;; Q)"
  by (rel_tac)

lemma R2s_design: "R2s(P \<turnstile> Q) = (R2s(P) \<turnstile> R2s(Q))"
  by (simp add: R2s_def design_def usubst)

lemma R1_R3c_design:
  "R1(R3c(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by (rel_tac, simp_all add: alpha_d.equality)

lemma unrest_ok_R2s [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok'_R2s [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok_R3c_pre [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok'_R3c_pre [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok_R3c_post [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma unrest_ok_R3c_post' [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma R3c_R1_design_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R3c(R1(P \<turnstile> Q)) ;; R3c(R1(R \<turnstile> S))) = 
       R3c(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> $wait\<acute>) ;; R1(\<not> R))) 
       \<turnstile> (R1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
    by (rel_tac)
  have 2:"(\<not> (R1 (R3c_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> (R1 Q \<and> \<not> $wait\<acute> ;; R1 (\<not> R)))"
    by (rel_tac)
  have 3:"(R1 (R3c_post Q) ;; R1 (R3c_post S)) = R3c_post (R1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 S))"
    by (rel_tac)
  show ?thesis
    apply (simp add: R3c_semir_form R1_R3c_commute[THEN sym] R1_R3c_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

definition [upred_defs]: "R2c(P) = (R2s(P) \<triangleleft> R1(true) \<triangleright> P)"

lemma R2c_and: "R2c(P \<and> Q) = (R2c(P) \<and> R2c(Q))"
  by (rel_tac)

lemma R2c_disj: "R2c(P \<or> Q) = (R2c(P) \<or> R2c(Q))"
  by (rel_tac)

lemma R2c_not: "R2c(\<not> P) = (\<not> R2c(P))"
  by (rel_tac)

lemma R2c_design: "R2c(P \<turnstile> Q) = R2c(P) \<turnstile> R2c(Q)"
  by (rel_tac)

lemma R2c_idem: "R2c(R2c(P)) = R2c(P)"
  by (rel_tac)

lemma R1_R2c_commute: "R1(R2c(P)) = R2c(R1(P))"
  by (rel_tac)

lemma R1_R2c_is_R2: "R1(R2c(P)) = R2(P)"
  by (rel_tac)

lemma RH_R2c_def: "RH(P) = R3c(R1(R2c(P)))"
  by (simp add: R1_R2c_is_R2 R2_R3c_commute RH_alt_def')

lemma RH_absorbs_R2c: "RH(R2c(P)) = RH(P)"
  by (metis R1_R2_commute R1_R2c_is_R2 R1_R3c_commute R2_R3c_commute R2_idem RH_alt_def RH_alt_def')
  
lemma R2c_seq: "R2c(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
  by (metis R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute R2c_idem)

lemma R1_des_lift_skip: "R1(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  by (rel_tac)

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

lemma R2_des_lift_skip:
  "R2(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  by (rel_tac, metis (no_types, lifting) alpha_rp'.surjective alpha_rp'.update_convs(2) append_Nil2 append_minus strict_prefixE)

lemma RH_design_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(RH(P \<turnstile> Q) ;; RH(R \<turnstile> S)) = 
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (rel_tac)
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

  have 2:"R2c (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))"
  proof -
    have "(R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (rel_tac)
    hence "R2c (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (metis R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))"
      by rel_tac
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))) = (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)) = 
            R2c(R1 (R2s (Q\<lbrakk>true/$wait\<acute>\<rbrakk>)) ;; \<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>)"
        by (simp add: usubst cond_unit_T R1_def R2s_def, rel_tac)
      also have "... = R2c(R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        by (metis R2_def R2_des_lift_skip R2_subst_wait_true)
      also have "... = (R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
        apply (simp add: usubst cond_unit_T R2_des_lift_skip)
        apply (metis R2_def R2_des_lift_skip R2_subst_wait'_true R2_subst_wait_true)
      done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>)"
      by (simp add: usubst cond_unit_F, metis R2_R1_form R2_subst_wait'_false R2_subst_wait_false R2c_seq)
    ultimately show ?thesis
      by (smt R2_R1_form R2_condr' R2_des_lift_skip R2c_seq R2s_wait)
  qed

  have "(R1(R2s(R3c(P \<turnstile> Q))) ;; R1(R2s(R3c(R \<turnstile> S)))) =
        ((R3c(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3c(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis R2_R3c_commute R2_def R2s_design)
  also have "... = R3c (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))))"
    by (simp add: R3c_R1_design_composition assms unrest)
  also have "... = R3c(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (metis RH_R2c_def RH_def)
qed

text {* Marcel's proof for reactive design composition *}

lemma reactive_design_composition:
  assumes "out\<alpha> \<sharp> p\<^sub>1" "p\<^sub>1 is R2s" "P\<^sub>2 is R2s" "Q\<^sub>1 is R2s" "Q\<^sub>2 is R2s"
  shows
  "(RH(p\<^sub>1 \<turnstile> Q\<^sub>1) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)) = 
    RH((p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1 (\<not> P\<^sub>2)))
       \<turnstile> ((($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))" (is "?lhs = ?rhs")
proof -
  have "?lhs = RH(?lhs)"
    by (metis Healthy_def' RH_idem RH_seq_closure)
  also have "... = RH ((R2 \<circ> R1) (p\<^sub>1 \<turnstile> Q\<^sub>1) ;; RH (P\<^sub>2 \<turnstile> Q\<^sub>2))"
    by (metis R1_R2_commute R1_idem R2_R3c_commute R2_def R3c_idem R3c_semir_form RH_def comp_apply)
  also have "... = RH (R1 ((\<not> $ok \<or> R2s (\<not> p\<^sub>1)) \<or> $ok\<acute> \<and> R2s Q\<^sub>1) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))"
    by (simp add: design_def R2_R1_form impl_alt_def R2s_nok R2s_disj R2s_conj R2s_ok')
  also have "... = RH(((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> ((\<not> R2s(p\<^sub>1) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> (($ok\<acute> \<and> R2s(Q\<^sub>1) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)))"
    by (smt R1_conj R1_def R1_disj R1_negate_R1 R2_def R2s_not seqr_or_distl utp_pred.conj_assoc utp_pred.inf.commute utp_pred.sup.assoc)
  also have "... = RH(((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> ((\<not> p\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)))"
    by (metis Healthy_def' assms(2) assms(4))

  also have "... = RH((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (\<not> p\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)))"
  proof -
    have "((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)) = (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)"
      by (rel_tac, metis alpha_d.select_convs(1) alpha_d.select_convs(2) order_refl)
    moreover have "(((\<not> p\<^sub>1 ;; true) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)) = ((\<not> p\<^sub>1 ;; true) \<and> $tr \<le>\<^sub>u $tr\<acute>)"
      by (rel_tac, metis alpha_d.select_convs(1) alpha_d.select_convs(2) order_refl)
    ultimately show ?thesis
      by (smt assms(1) precond_right_unit unrest_not)
  qed

  also have "... = RH((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (\<not> p\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; ($wait \<and> $ok\<acute> \<and> II))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> R1(\<not> P\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> $ok\<acute> \<and> R2(Q\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>)))"
  proof -
    have 1:"RH(P\<^sub>2 \<turnstile> Q\<^sub>2) = (($wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                        \<or> ($wait \<and> $ok\<acute> \<and> II)
                        \<or> (\<not> $wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                        \<or> (\<not> $wait \<and> R2(\<not> P\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>)
                        \<or> (\<not> $wait \<and> $ok\<acute> \<and> R2(Q\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>))"
      by (simp add: RH_alt_def' R2_condr' R2s_wait R2_skip_rea R3c_def usubst, rel_tac)
    have 2:"(($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; ($wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)) = false"
      by rel_tac
    have 3:"(($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)) = false"
      by rel_tac
    have 4:"R2(\<not> P\<^sub>2) = R1(\<not> P\<^sub>2)"
      by (metis Healthy_def' R1_negate_R1 R2_def R2s_not assms(3))
    show ?thesis
      by (simp add: "1" "2" "3" "4" seqr_or_distr)
  qed
  
  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; ($wait \<and> $ok\<acute> \<and> II))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> R1(\<not> P\<^sub>2)))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> $ok\<acute> \<and> R2(Q\<^sub>2))))"
    by (rel_tac) (* 14 seconds *)

  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1)
                      \<or> ($ok\<acute> \<and> $wait\<acute> \<and> Q\<^sub>1)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> R1(\<not> P\<^sub>2)))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> $ok\<acute> \<and> R1(Q\<^sub>2))))"
  proof -
    have "(($ok\<acute> \<and> Q\<^sub>1) ;; ($wait \<and> $ok\<acute> \<and> II)) = ($ok\<acute> \<and> $wait\<acute> \<and> Q\<^sub>1)"
      by (rel_tac)
    moreover have "R2(Q\<^sub>2) = R1(Q\<^sub>2)"
      by (metis Healthy_def' R2_def assms(5))
    ultimately show ?thesis by simp
  qed

  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1)
                      \<or> ($ok\<acute> \<and> $wait\<acute> \<and> Q\<^sub>1)
                      \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; (R1(\<not> P\<^sub>2)))
                      \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; ($ok\<acute> \<and> R1(Q\<^sub>2))))"
    by rel_tac

  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2))
                      \<or> ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))"
    by rel_tac

  also have "... = RH(\<not> ($ok \<and> p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2)))
                      \<or> ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))"
    by rel_tac

  also have "... = ?rhs"
  proof -
    have "(\<not> ($ok \<and> p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2)))
                      \<or> ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))
          = (($ok \<and> (p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2)))) \<Rightarrow> 
            ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))"  
      by pred_tac
    thus ?thesis
      by (simp add: design_def)
  qed

  finally show ?thesis .
qed

end