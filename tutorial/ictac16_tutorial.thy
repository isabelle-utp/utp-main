section {* ICTAC 2016 tutorial. Taipei, 24/10/2016 *}

theory ictac16_tutorial
  imports "../theories/utp_designs"
begin

subsection {* Laws of programming *}

theorem cond_shadow: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)" oops

theorem seqr_assoc: "(P ;; (Q ;; R)) = ((P ;; Q) ;; R)" oops

theorem seqr_left_unit: "(II ;; P) = P" oops

theorem seqr_left_zero: "(false ;; P) = false" oops

theorem cond_seq_left_distr:
  assumes "out\<alpha> \<sharp> b"
  shows "((P \<triangleleft> b \<triangleright> Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright> (Q ;; R))"
  using assms by (rel_simp, blast+)

theorem assign_twice:
  assumes "vwb_lens x" "x \<sharp> f"
  shows "(x := e ;; x := f) = (x := f)"
  using assms by rel_auto

theorem assign_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x := e ;; y := f) = (y := f ;; x := e)"
  using assms by (rel_auto, simp_all add: lens_indep_comm)

subsection {* Design laws *}

theorem design_false_pre: "(false \<turnstile> P) = true" by rel_auto

theorem design_true_left_zero: "(true ;; (P \<turnstile> Q)) = true"
proof -
  have "(true ;; (P \<turnstile> Q)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> true\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (P \<turnstile> Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    by (subst seqr_middle[of ok], simp_all)
  also have "... = ((true\<lbrakk>false/$ok\<acute>\<rbrakk> ;; (P \<turnstile> Q)\<lbrakk>false/$ok\<rbrakk>) \<or> (true\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (P \<turnstile> Q)\<lbrakk>true/$ok\<rbrakk>))"
    by (simp add: disj_comm false_alt_def true_alt_def)
  also have "... = ((true\<lbrakk>false/$ok\<acute>\<rbrakk> ;; true\<^sub>h) \<or> (true ;; ((P \<turnstile> Q)\<lbrakk>true/$ok\<rbrakk>)))"
    by (subst_tac, rel_auto)
  also have "... = true"
    by (subst_tac, simp add: precond_right_unit unrest)
  finally show ?thesis .
qed

theorem rdesign_left_unit:
  fixes P Q :: "'\<alpha> hrel_des"
  shows "II\<^sub>D ;; (P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
proof -
  -- {* We first expand out the definition of the design identity *}
  have "II\<^sub>D ;; (P \<turnstile>\<^sub>r Q) = (true \<turnstile>\<^sub>r II) ;; (P \<turnstile>\<^sub>r Q)"
    by (simp add: skip_d_def)
  -- {* Next, we apply the design composition law above in a subproof *}
  also have "... = (true \<and> \<not> (II ;; (\<not> P))) \<turnstile>\<^sub>r (II ;; Q)"
  proof -
    -- {* The assumption of identity is $\true$ so it is easy to discharge the proviso *}
    have "out\<alpha> \<sharp> true"
      by unrest_tac
    -- {* From this we can apply the composition law *}
    thus ?thesis
      using rdesign_composition_cond by blast
  qed
  -- {* Simplification then allows us to remove extraneous terms *}
  also have "... = (\<not> (\<not> P)) \<turnstile>\<^sub>r Q"
    by simp
  -- {* Finally, we can show the thesis *}
  finally show ?thesis by simp
qed

subsection {* Program example *}

alphabet my_state =
  x :: int
  y :: int
  z :: int

lemma "(x := 1 ;; x := (&x + 1)) = (x := 2)"
  oops

lemma "($x\<acute> >\<^sub>u $x \<and> $y\<acute> <\<^sub>u $y) \<sqsubseteq> x, y := &x + 1, &y"
  oops

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = ((x,y) := (1,7))"
  oops

(* Need following law:  *)
theorem ndesign_composition_wp: "((p1 \<turnstile>\<^sub>n Q1) ;; (p2 \<turnstile>\<^sub>n Q2)) = ((p1 \<and> Q1 wp p2) \<turnstile>\<^sub>n (Q1 ;; Q2))"
  oops

lemma violate_precond:
  "(true \<turnstile>\<^sub>n x := 1) ;; ((&x >\<^sub>u 1) \<turnstile>\<^sub>n y := 2) = \<bottom>\<^sub>D"
  apply (subst ndesign_composition_wp)
  apply (simp)
  apply (wp_tac)
  apply (subst_tac)
  apply (rel_auto)
done
end