section {* ICTAC 2016 tutorial. Taipei, 24/10/2016 *}

theory ictac16_tutorial
  imports "../utp/utp_trd"
begin

subsection {* Laws of programming *}

theorem cond_shadow: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)" by rel_tac

theorem seqr_assoc: "(P ;; (Q ;; R)) = ((P ;; Q) ;; R)" by rel_tac

theorem seqr_left_unit: "(II ;; P) = P" by rel_tac

theorem seqr_left_zero: "(false ;; P) = false" by rel_tac

theorem cond_seq_left_distr:
  assumes "out\<alpha> \<sharp> b"
  shows "((P \<triangleleft> b \<triangleright> Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright> (Q ;; R))"
  using assms by (rel_tac, blast+)

theorem assign_twice: 
  assumes "uvar x" "x \<sharp> f" 
  shows "(x := e ;; x := f) = (x := f)"
  using assms by rel_tac

theorem assign_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x := e ;; y := f) = (y := f ;; x := e)"
  using assms by (rel_tac, simp_all add: lens_indep_comm)

subsection {* Design laws *}

theorem design_false_pre: "(false \<turnstile> P) = true" by rel_tac

theorem H1_H2_eq_design: "H1 (H2 P) = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
proof -
  have "H1 (H2 P) = ($ok \<Rightarrow> H2(P))"
    by (simp add: H1_def)
  also have "... = ($ok \<Rightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)))"
    by (metis H2_split)
  also have "... = ($ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> $ok \<and> P\<^sup>t)"
    by rel_tac
  also have "... = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
    by rel_tac
  finally show ?thesis .
qed

theorem design_left_unit:
  fixes P Q :: "'\<alpha> hrelation_d"
  shows "(II\<^sub>D ;; P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
proof -
  have "(II\<^sub>D ;; P \<turnstile>\<^sub>r Q) = (true \<turnstile>\<^sub>r II ;; P \<turnstile>\<^sub>r Q)"
    by (simp add: skip_d_def)
  also have "... = (true \<and> \<not> (II ;; \<not> P)) \<turnstile>\<^sub>r (II ;; Q)"
  proof -
    have "out\<alpha> \<sharp> true"
      by unrest_tac
    thus ?thesis
      using rdesign_composition_cond by blast
  qed
  also have "... = (\<not> (\<not> P)) \<turnstile>\<^sub>r Q"
    by simp
  finally show ?thesis by simp
qed

subsection {* Program example *}

(* Boiler plate: Set up the lenses for our two state variables, x and y *)

record my_state =
  st_x :: int
  st_y :: int
  st_z :: int

definition "x = VAR st_x"
definition "y = VAR st_y"
definition "z = VAR st_z"

lemma uvar_x [simp]: "vwb_lens x"
  by (unfold_locales, auto simp add: x_def)

lemma uvar_y [simp]: "vwb_lens y"
  by (unfold_locales, auto simp add: y_def)

lemma uvar_z [simp]: "vwb_lens z"
  by (unfold_locales, auto simp add: z_def)

lemma my_state_indeps [simp]: "x \<bowtie> y" "y \<bowtie> x" "x \<bowtie> z" "z \<bowtie> x" "y \<bowtie> z" "z \<bowtie> y"
  by (simp_all add: lens_indep_def x_def y_def z_def)

(* Beginning of examples *)

lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
  oops

lemma "($x\<acute> >\<^sub>u $x \<and> $y\<acute> <\<^sub>u $y) \<sqsubseteq> x, y := &x + 1, &y"
  oops

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
  oops

(* Need law ndesign_composition_wp: "((p1 \<turnstile>\<^sub>n Q1) ;; (p2 \<turnstile>\<^sub>n Q2)) = ((p1 \<and> Q1 wp p2) \<turnstile>\<^sub>n (Q1 ;; Q2))" *)

lemma violate_precond:
  "(true \<turnstile>\<^sub>n x := 1 ;; (&x >\<^sub>u 1) \<turnstile>\<^sub>n y := 2) = \<bottom>\<^sub>D"
  oops

end

