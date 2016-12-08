theory ex_rea_1
  imports "../utp/utp_csp"
begin

definition [urel_defs]: "DEAD = R3($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)"

definition [urel_defs]: "perform(a) = R3((($tr\<acute> =\<^sub>u $tr \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle>)) \<and> \<lceil>II\<rceil>\<^sub>R)"

definition rassign :: "('a, '\<alpha>) uvar \<Rightarrow> _ \<Rightarrow> _" (infixr ":=\<^sub>r" 55) where
"rassign x v = (R3(\<Sigma>\<^sub>R:x := v))"

lemma DEAD_wait': "(DEAD \<and> $wait\<acute>) = DEAD"
  by (rel_auto)

lemma 
  assumes "P is R3"
  shows "(DEAD ;; P) = DEAD"
proof -
  have "(DEAD ;; P) = (DEAD ;; R3(P))"
    by (metis Healthy_if assms)
  also have "... = (DEAD ;; (II \<triangleleft> $wait \<triangleright> P))"
    by (simp add: R3_def)
  also have "... = ((DEAD \<and> $wait\<acute>) ;; (II \<triangleleft> $wait \<triangleright> P))"
    by (simp add: DEAD_wait')
  also have "... = (DEAD ;; ($wait \<and> (II \<triangleleft> $wait \<triangleright> P)))"
    by (simp add: seqr_post_transfer utp_rel.unrest_iuvar)
  also have "... = (DEAD ;; II)"
    by (rel_auto)
  also have "... = DEAD"
    by simp
  finally show ?thesis .
qed

lemma "(x :=\<^sub>r v ;; perform(a)) = (perform(a) ;; x :=\<^sub>r v)"
proof -
  have 1: "($wait \<and> (x :=\<^sub>r v ;; perform(a))) = ($wait \<and> (perform(a) ;; x :=\<^sub>r v))"
    by (simp add: R3_semir_form perform_def rassign_def wait_R3)
  have 2: "(\<not>$wait \<and> (x :=\<^sub>r v ;; perform(a))) = (\<not>$wait \<and> (perform(a) ;; x :=\<^sub>r v))"
  proof -
    have "(\<not>$wait \<and> (x :=\<^sub>r v ;; perform(a))) = ((\<not>$wait \<and> \<Sigma>\<^sub>R:x := v) ;; perform(a))"
      by (metis nwait_R3 rassign_def seqr_pre_out unrest_not utp_rel.unrest_iuvar vwb_lens_mwb wait_uvar)
    also have "... = ((\<Sigma>\<^sub>R:x := v \<and> \<not>$wait\<acute>) ;; perform(a))"
      apply (subst assign_pred_transfer)
      apply (rule unrest)
      apply (rule unrest)
      apply (simp_all)
      using in_var_indep lens_indep_left_ext lens_indep_sym rea_lens_indep_wait(1) apply blast
      apply (simp add: unrest)
    done
    also have "... = ((\<Sigma>\<^sub>R:x := v \<and> \<not>$wait\<acute>) ;; perform(a))"

end
