section {* Reactive designs *}

theory utp_rea_designs
  imports utp_reactive
begin

lemma R2_tr_prefix: "R2($tr \<le>\<^sub>u $tr\<acute>) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (pred_tac)

lemma R2s_ok': "R2s($ok\<acute>) = $ok\<acute>"
  by pred_tac

lemma R2s_nok: "R2s(\<not> $ok) = (\<not> $ok)"
  by (pred_tac)

lemma R2_R1_form: "R2(R1(P)) = R1(R2s(P))"
  by (rel_tac)

lemma reactive_design_composition:
  assumes "out\<alpha> \<sharp> p\<^sub>1" "p\<^sub>1 is R2" "P\<^sub>2 is R2" "Q\<^sub>1 is R2" "Q\<^sub>2 is R2"
  shows
  "(RH(p\<^sub>1 \<turnstile> Q\<^sub>1) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)) = 
    RH(p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; \<not> P\<^sub>2)
       \<turnstile> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; Q\<^sub>2)))" (is "?lhs = ?rhs")
proof -
  have "?lhs = RH(?lhs)"
    by (metis Healthy_def' RH_idem RH_seq_closure)
  also have "... = RH ((R2 \<circ> R1) (p\<^sub>1 \<turnstile> Q\<^sub>1) ;; RH (P\<^sub>2 \<turnstile> Q\<^sub>2))"
    by (metis R1_R2_commute R1_idem R2_R3c_commute R2_def R3c_idem R3c_semir_form RH_def comp_apply)
  also have "... = RH (R1 ((\<not> $ok \<or> R2s (\<not> p\<^sub>1)) \<or> $ok\<acute> \<and> R2s Q\<^sub>1) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))"
    by (simp add: design_def R2_R1_form impl_alt_def R2s_nok R2s_disj R2s_conj R2s_ok')
  also have "... = RH(((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> ((\<not> R2(p\<^sub>1) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> (($ok\<acute> \<and> R2(Q\<^sub>1) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)))"
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
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; ($wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; ($wait \<and> $ok\<acute> \<and> II))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> R2(\<not> P\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> $ok\<acute> \<and> R2(Q\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>)))"
    oops


end