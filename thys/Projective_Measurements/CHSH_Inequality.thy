(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory CHSH_Inequality imports 
  Projective_Measurements


begin


section \<open>The CHSH inequality\<close>

text \<open>The local hidden variable assumption for quantum  mechanics was developed to make the case 
that quantum theory was incomplete. In this part we formalize the CHSH inequality, which provides 
an upper-bound of a quantity involving expectations in a probability space, and exploit this 
inequality to show that the local hidden variable assumption does not hold.\<close>

subsection \<open>Inequality statement\<close>

lemma chsh_real:
  fixes A0::real
  assumes "\<bar>A0 * B1\<bar> \<le> 1"
  and "\<bar>A0 * B0\<bar> \<le> 1"
  and "\<bar>A1 * B0\<bar> \<le> 1"
  and "\<bar>A1 * B1\<bar> \<le> 1"
  shows "\<bar>A0 * B1 - A0 * B0 + A1 * B0 + A1*B1\<bar> \<le> 2"
proof -
  have "A0 * B1 - A0 * B0 = A0 * B1 - A0 * B0 + A0 * B1 * A1 * B0 - A0 * B1 * A1 * B0" by simp
  also have "... = A0 * B1 * (1 + A1*B0) - A0 * B0 * (1 + A1* B1)"
    by (metis (no_types, hide_lams) add_diff_cancel_right calculation diff_add_eq 
        group_cancel.sub1 mult.commute mult.right_neutral 
        vector_space_over_itself.scale_left_commute 
        vector_space_over_itself.scale_right_diff_distrib 
        vector_space_over_itself.scale_right_distrib 
        vector_space_over_itself.scale_scale) 
  finally have "A0 * B1 - A0 * B0 = A0 * B1 * (1 + A1*B0) - A0 * B0 * (1 + A1* B1)" .
  hence "\<bar>A0 * B1 - A0 * B0\<bar> \<le> \<bar>A0 * B1 * (1 + A1*B0)\<bar> + \<bar>A0 * B0 * (1 + A1* B1)\<bar>" by simp
  also have "... = \<bar>A0 * B1\<bar> * \<bar>(1 + A1*B0)\<bar> + \<bar>A0 * B0\<bar> * \<bar>(1 + A1* B1)\<bar>" by (simp add: abs_mult)
  also have "... \<le> \<bar>(1 + A1*B0)\<bar> + \<bar>(1 + A1* B1)\<bar>" 
  proof-
    have "\<bar>A0 * B1\<bar> * \<bar>(1 + A1*B0)\<bar> \<le> \<bar>(1 + A1*B0)\<bar>" 
      using assms(1) mult_left_le_one_le[of "\<bar>(1 + A1*B0)\<bar>"] by simp
    moreover have "\<bar>A0 * B0\<bar> *\<bar>(1 + A1* B1)\<bar> \<le> \<bar>(1 + A1* B1)\<bar>"
      using assms mult_left_le_one_le[of "\<bar>(1 + A1*B1)\<bar>"] by simp
    ultimately show ?thesis by simp
  qed
  also have "... = 1 + A1*B0 + 1 + A1* B1" using assms by (simp add: abs_le_iff) 
  also have "... = 2 + A1 * B0 + A1 * B1" by simp
  finally have pls: "\<bar>A0 * B1 - A0 * B0\<bar> \<le> 2 + A1 * B0 + A1 * B1" .
  have "A0 * B1 - A0 * B0 = A0 * B1 - A0 * B0 + A0 * B1 * A1 * B0 - A0 * B1 * A1 * B0" by simp
  also have "... = A0 * B1 * (1 - A1*B0) - A0 * B0 * (1 - A1* B1)"
  proof -
    have "A0 * (B1 - (B0 - A1 * (B1 * B0)) - A1 * (B1 * B0)) = A0 * (B1 - B0)"
      by fastforce
    then show ?thesis
      by (metis (no_types) add.commute calculation diff_diff_add mult.right_neutral 
          vector_space_over_itself.scale_left_commute 
          vector_space_over_itself.scale_right_diff_distrib vector_space_over_itself.scale_scale)
  qed
  finally have "A0 * B1 - A0 * B0 = A0 * B1 * (1 - A1*B0) - A0 * B0 * (1 - A1* B1)" .
  hence "\<bar>A0 * B1 - A0 * B0\<bar> \<le> \<bar>A0 * B1 * (1 - A1*B0)\<bar> + \<bar>A0 * B0 * (1 - A1* B1)\<bar>" by simp
  also have "... = \<bar>A0 * B1\<bar> * \<bar>(1 - A1*B0)\<bar> + \<bar>A0 * B0\<bar> * \<bar>(1 - A1* B1)\<bar>" by (simp add: abs_mult)
  also have "... \<le> \<bar>(1 - A1*B0)\<bar> + \<bar>(1 - A1* B1)\<bar>" 
  proof-
    have "\<bar>A0 * B1\<bar> * \<bar>(1 - A1*B0)\<bar> \<le> \<bar>(1 - A1*B0)\<bar>" 
      using assms(1) mult_left_le_one_le[of "\<bar>(1 - A1*B0)\<bar>"] by simp
    moreover have "\<bar>A0 * B0\<bar> *\<bar>(1 - A1* B1)\<bar> \<le> \<bar>(1 - A1* B1)\<bar>"
      using assms mult_left_le_one_le[of "\<bar>(1 - A1*B1)\<bar>"] by simp
    ultimately show ?thesis by simp
  qed
  also have "... = 1 - A1*B0 + 1 - A1* B1" using assms by (simp add: abs_le_iff) 
  also have "... = 2 - A1 * B0 - A1 * B1" by simp
  finally have mns: "\<bar>A0 * B1 - A0 * B0\<bar> \<le> 2 - (A1 * B0 + A1 * B1)" by simp
  have ls: "\<bar>A0 * B1 - A0 * B0\<bar> \<le> 2 - \<bar>A1 * B0 + A1 * B1\<bar>"
  proof (cases "0 \<le> A1 * B0 + A1 * B1")
  case True
    then show ?thesis using mns by simp
  next
  case False
    then show ?thesis using pls by simp
  qed
  have "\<bar>A0 * B1 - A0 * B0 + A1 * B0 + A1 * B1\<bar> \<le> \<bar>A0 * B1 - A0 * B0\<bar> + \<bar>A1 * B0 + A1 * B1\<bar>" 
    by simp
  also have "... \<le> 2" using ls by simp
  finally show ?thesis .
qed

lemma (in prob_space) chsh_expect:
  fixes A0::"'a \<Rightarrow> real"
  assumes "AE w in M. \<bar>A0 w\<bar> \<le> 1"
  and "AE w in M. \<bar>A1 w\<bar> \<le> 1"
  and "AE w in M. \<bar>B0 w\<bar> \<le> 1"
  and "AE w in M. \<bar>B1 w\<bar> \<le> 1"
and "integrable M (\<lambda>w. A0 w * B1 w)"
and "integrable M (\<lambda>w. A1 w * B1 w)"
and "integrable M (\<lambda>w. A1 w * B0 w)"
and "integrable M (\<lambda>w. A0 w * B0 w)"
shows "\<bar>expectation (\<lambda>w. A1 w * B0 w) + expectation (\<lambda>w. A0 w *B1 w) + 
  expectation (\<lambda>w. A1 w * B1 w) - expectation (\<lambda>w. A0 w * B0 w)\<bar> \<le> 2" 
proof -
  have exeq: "expectation (\<lambda>w. A1 w * B0 w) + expectation (\<lambda>w. A0 w * B1 w) + 
    expectation (\<lambda>w. A1 w * B1 w) - expectation (\<lambda>w. A0 w * B0 w) = 
    expectation (\<lambda>w. A0 w * B1 w - A0 w * B0 w + A1 w * B0 w + A1 w * B1 w)"
    using assms by auto
  have "\<bar>expectation (\<lambda>w. A0 w * B1 w - A0 w * B0 w + A1 w * B0 w + A1 w * B1 w)\<bar> \<le>
    expectation (\<lambda>w. \<bar>A0 w * B1 w - A0 w * B0 w + A1 w * B0 w + A1 w * B1 w\<bar>)"  
    using integral_abs_bound by blast
  also have "... \<le> 2" 
  proof (rule integral_le_const)
    show "AE w in M. \<bar>A0 w * B1 w - A0 w * B0 w + A1 w * B0 w + A1 w * B1 w\<bar> \<le> (2::real)" 
    proof (rule AE_mp)
      show "AE w in M. \<bar>A0 w\<bar> \<le> 1 \<and> \<bar>A1 w\<bar> \<le> 1 \<and> \<bar>B0 w\<bar> \<le> 1 \<and> \<bar>B1 w\<bar> \<le> 1"
        using assms by simp
      show "AE w in M. \<bar>A0 w\<bar> \<le> 1 \<and> \<bar>A1 w\<bar> \<le> 1 \<and> \<bar>B0 w\<bar> \<le> 1 \<and> \<bar>B1 w\<bar> \<le> 1 \<longrightarrow>
               \<bar>A0 w * B1 w - A0 w * B0 w + A1 w * B0 w + A1 w * B1 w\<bar> \<le> 2"
      proof
        fix w
        assume "w\<in> space M"
        show "\<bar>A0 w\<bar> \<le> 1 \<and> \<bar>A1 w\<bar> \<le> 1 \<and> \<bar>B0 w\<bar> \<le> 1 \<and> \<bar>B1 w\<bar> \<le> 1 \<longrightarrow>
         \<bar>A0 w * B1 w - A0 w * B0 w + A1 w * B0 w + A1 w * B1 w\<bar> \<le> 2"
        proof 
          assume ineq: "\<bar>A0 w\<bar> \<le> 1 \<and> \<bar>A1 w\<bar> \<le> 1 \<and> \<bar>B0 w\<bar> \<le> 1 \<and> \<bar>B1 w\<bar> \<le> 1"
          show "\<bar>A0 w * B1 w - A0 w * B0 w + A1 w * B0 w + A1 w * B1 w\<bar> \<le> 2"
          proof (rule chsh_real)
            show "\<bar>A0 w * B1 w\<bar> \<le> 1" using ineq by (simp add: abs_mult mult_le_one)
            show "\<bar>A0 w * B0 w\<bar> \<le> 1" using ineq by (simp add: abs_mult mult_le_one)
            show "\<bar>A1 w * B1 w\<bar> \<le> 1" using ineq by (simp add: abs_mult mult_le_one)
            show "\<bar>A1 w * B0 w\<bar> \<le> 1" using ineq by (simp add: abs_mult mult_le_one)
          qed
        qed
      qed
    qed
    show "integrable M (\<lambda>x. \<bar>A0 x * B1 x - A0 x * B0 x + A1 x * B0 x + A1 x * B1 x\<bar>)" 
    proof (rule Bochner_Integration.integrable_abs)
      show "integrable M (\<lambda>x. A0 x * B1 x - A0 x * B0 x + A1 x * B0 x + A1 x * B1 x)"
        using assms by auto
    qed
  qed
  finally show ?thesis using exeq by simp
qed

text \<open>The local hidden variable assumption states that separated quantum measurements are 
independent. It is standard for this assumption to be stated in a context where the hidden 
variable admits a density; it is stated here in a more general contest involving expectations, 
with no assumption on the existence of a density.\<close>

definition pos_rv:: "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
"pos_rv M Xr \<equiv> Xr \<in> borel_measurable M \<and> (AE w in M. (0::real) \<le> Xr w)"

definition prv_sum:: "'a measure \<Rightarrow> complex Matrix.mat \<Rightarrow> (complex \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
"prv_sum M A Xr \<equiv> (AE w in M. (\<Sum> a\<in> spectrum A. Xr a w) = 1)"

definition (in cpx_sq_mat) lhv where
"lhv M A B R XA XB \<equiv> 
  prob_space M \<and>
  (\<forall>a \<in>spectrum A. pos_rv M (XA a)) \<and> 
  (prv_sum M A XA) \<and> 
  (\<forall>b \<in>spectrum B. pos_rv M (XB b)) \<and>
  (prv_sum M B XB) \<and> 
  (\<forall>a \<in>spectrum A . \<forall>b \<in> spectrum B. 
    (integrable M (\<lambda>w. XA a w * XB b w)) \<and> 
    integral\<^sup>L M (\<lambda>w. XA a w * XB b w) = 
    Re (Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R)))"

(*definition (in cpx_sq_mat) lhv where
"lhv M A B R XA XB \<equiv> 
  prob_space M \<and>
  (\<forall>a \<in>spectrum A. (XA a \<in> borel_measurable M) \<and> 
    (AE w in M. ((0::real) \<le> XA a w))) \<and> 
  (AE w in M. (\<Sum> a\<in> spectrum A. XA a w) = 1) \<and> 
  (\<forall>b \<in>spectrum B. (XB b \<in> borel_measurable M) \<and> 
    (AE w in M. (0 \<le> XB b w))) \<and>
  (AE w in M. (\<Sum> b\<in> spectrum B. XB b w) = 1) \<and> 
  (\<forall>a \<in>spectrum A . \<forall>b \<in> spectrum B. 
    (integrable M (\<lambda>w. XA a w * XB b w)) \<and> 
    integral\<^sup>L M (\<lambda>w. XA a w * XB b w) = 
    Re (Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R)))"*)

lemma (in cpx_sq_mat) lhv_posl:
  assumes "lhv M A B R XA XB"
  shows "AE w in M. (\<forall> a \<in> spectrum A. 0 \<le> XA a w)" 
proof (rule AE_ball_countable[THEN iffD2])
  show "countable (spectrum A)" using spectrum_finite[of A]
    by (simp add: countable_finite)
  show "\<forall>a\<in>spectrum A. AE w in M. 0 \<le> XA a w" using assms unfolding lhv_def pos_rv_def by simp
qed

lemma (in cpx_sq_mat) lhv_lt1_l:
  assumes "lhv M A B R XA XB"
  shows "AE w in M. (\<forall> a \<in> spectrum A. XA a w \<le> 1)" 
proof (rule AE_mp)
  show "AE w in M. (\<forall> a \<in> spectrum A. 0 \<le> XA a w) \<and> (\<Sum> a\<in> spectrum A. XA a w) = 1"
    using lhv_posl assms unfolding lhv_def pos_rv_def prv_sum_def by simp
  show "AE w in M. (\<forall>a\<in>spectrum A. 0 \<le> XA a w) \<and> (\<Sum>a\<in>spectrum A. XA a w) = 1 \<longrightarrow> 
    (\<forall>a\<in>spectrum A. XA a w \<le> 1)"
  proof
    fix w
    assume "w\<in> space M"
    show "(\<forall>a\<in>spectrum A. 0 \<le> XA a w) \<and> (\<Sum>a\<in>spectrum A. XA a w) = 1 \<longrightarrow> 
      (\<forall>a\<in>spectrum A. XA a w \<le> 1)" 
    proof (rule impI)
      assume pr: "(\<forall>a\<in>spectrum A. 0 \<le> XA a w) \<and> (\<Sum>a\<in>spectrum A. XA a w) = 1"
      show "\<forall>a\<in>spectrum A. XA a w \<le> 1"
      proof
        fix a
        assume "a\<in> spectrum A"
        show "XA a w \<le> 1"
        proof (rule pos_sum_1_le[of "spectrum A"])
          show "finite (spectrum A)" using spectrum_finite[of A] by simp
          show "a \<in> spectrum A" using \<open>a \<in> spectrum A\<close> .
          show " \<forall>i\<in>spectrum A. 0 \<le> XA i w" using pr by simp
          show "(\<Sum>i\<in>spectrum A. XA i w) = 1" using pr by simp
        qed
      qed
    qed
  qed
qed

lemma (in cpx_sq_mat) lhv_posr:
  assumes "lhv M A B R XA XB"
  shows "AE w in M. (\<forall> b \<in> spectrum B. 0 \<le> XB b w)" 
proof (rule AE_ball_countable[THEN iffD2])
  show "countable (spectrum B)" using spectrum_finite[of B]
    by (simp add: countable_finite)
  show "\<forall>b\<in>spectrum B. AE w in M. 0 \<le> XB b w" using assms unfolding lhv_def pos_rv_def by simp
qed

lemma (in cpx_sq_mat) lhv_lt1_r:
  assumes "lhv M A B R XA XB"
  shows "AE w in M. (\<forall> a \<in> spectrum B. XB a w \<le> 1)" 
proof (rule AE_mp)
  show "AE w in M. (\<forall> a \<in> spectrum B. 0 \<le> XB a w) \<and> (\<Sum> a\<in> spectrum B. XB a w) = 1"
    using lhv_posr assms unfolding lhv_def prv_sum_def pos_rv_def by simp
  show "AE w in M. (\<forall>a\<in>spectrum B. 0 \<le> XB a w) \<and> (\<Sum>a\<in>spectrum B. XB a w) = 1 \<longrightarrow> 
    (\<forall>a\<in>spectrum B. XB a w \<le> 1)"
  proof
    fix w
    assume "w\<in> space M"
    show "(\<forall>a\<in>spectrum B. 0 \<le> XB a w) \<and> (\<Sum>a\<in>spectrum B. XB a w) = 1 \<longrightarrow> 
      (\<forall>a\<in>spectrum B. XB a w \<le> 1)" 
    proof (rule impI)
      assume pr: "(\<forall>a\<in>spectrum B. 0 \<le> XB a w) \<and> (\<Sum>a\<in>spectrum B. XB a w) = 1"
      show "\<forall>a\<in>spectrum B. XB a w \<le> 1"
      proof
        fix a
        assume "a\<in> spectrum B"
        show "XB a w \<le> 1"
        proof (rule pos_sum_1_le[of "spectrum B"])
          show "finite (spectrum B)" using spectrum_finite[of B] by simp
          show "a \<in> spectrum B" using \<open>a \<in> spectrum B\<close> .
          show " \<forall>i\<in>spectrum B. 0 \<le> XB i w" using pr by simp
          show "(\<Sum>i\<in>spectrum B. XB i w) = 1" using pr by simp
        qed
      qed
    qed
  qed
qed

lemma (in cpx_sq_mat) lhv_AE_propl:
  assumes "lhv M A B R XA XB"
  shows "AE w in M. (\<forall> a \<in> spectrum A. 0 \<le> XA a w \<and> XA a w \<le> 1) \<and> (\<Sum> a\<in> spectrum A. XA a w) = 1"
proof (rule AE_conjI)
  show "AE w in M. \<forall>a\<in>spectrum A. 0 \<le> XA a w \<and> XA a w \<le> 1" 
  proof (rule AE_mp)
    show "AE w in M. (\<forall> a \<in> spectrum A. 0 \<le> XA a w) \<and> (\<forall> a \<in> spectrum A. XA a w \<le> 1)"
      using assms lhv_posl[of M A] lhv_lt1_l[of M A] by simp
    show "AE w in M. (\<forall>a\<in>spectrum A. 0 \<le> XA a w) \<and> (\<forall>a\<in>spectrum A. XA a w \<le> 1) \<longrightarrow>
               (\<forall>a\<in>spectrum A. 0 \<le> XA a w \<and> XA a w \<le> 1)" by auto
  qed
  show "AE w in M. (\<Sum>a\<in>spectrum A. XA a w) = 1" using assms unfolding lhv_def prv_sum_def 
    by simp
qed

lemma (in cpx_sq_mat) lhv_AE_propr:
  assumes "lhv M A B R XA XB"
  shows "AE w in M. (\<forall> a \<in> spectrum B. 0 \<le> XB a w \<and> XB a w \<le> 1) \<and> (\<Sum> a\<in> spectrum B. XB a w) = 1"
proof (rule AE_conjI)
  show "AE w in M. \<forall>a\<in>spectrum B. 0 \<le> XB a w \<and> XB a w \<le> 1" 
  proof (rule AE_mp)
    show "AE w in M. (\<forall> a \<in> spectrum B. 0 \<le> XB a w) \<and> (\<forall> a \<in> spectrum B. XB a w \<le> 1)"
      using assms lhv_posr[of M _ B] lhv_lt1_r[of M _ B] by simp
    show "AE w in M. (\<forall>a\<in>spectrum B. 0 \<le> XB a w) \<and> (\<forall>a\<in>spectrum B. XB a w \<le> 1) \<longrightarrow>
               (\<forall>a\<in>spectrum B. 0 \<le> XB a w \<and> XB a w \<le> 1)" by auto
  qed
  show "AE w in M. (\<Sum>a\<in>spectrum B. XB a w) = 1" using assms unfolding lhv_def prv_sum_def 
    by simp
qed

lemma (in cpx_sq_mat) lhv_integral_eq:
  fixes c::real
  assumes "lhv M A B R XA XB"
  and "a\<in> spectrum A"
and "b\<in> spectrum B"
shows "integral\<^sup>L M (\<lambda>w. XA a w * XB b w) = 
  Re (Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))"
  using assms unfolding lhv_def by simp

lemma (in cpx_sq_mat) lhv_integrable:
  fixes c::real
  assumes "lhv M A B R XA XB"
  and "a\<in> spectrum A"
and "b\<in> spectrum B"
shows "integrable M (\<lambda>w. XA a w * XB b w)" using assms unfolding lhv_def by simp

lemma (in cpx_sq_mat) lhv_scal_integrable:
  fixes c::real
  assumes "lhv M A B R XA XB"
  and "a\<in> spectrum A"
and "b\<in> spectrum B"
shows "integrable M (\<lambda>w. c *XA a w * d * XB b w)" 
proof -
  {
    fix x
    assume "x\<in> space M"
    have "c * d * (XA a x * XB b x) = c * XA a x * d * XB b x" by simp 
  } note eq = this
  have "integrable M (\<lambda>w. XA a w * XB b w)" using assms unfolding lhv_def by simp
  hence g:"integrable M (\<lambda>w. c * d * (XA a w * XB b w))" using integrable_real_mult_right by simp
  show ?thesis 
  proof (rule Bochner_Integration.integrable_cong[THEN iffD2], simp)
    show "integrable M (\<lambda>w. c * d * (XA a w * XB b w))" using g .
    show "\<And>x. x \<in> space M \<Longrightarrow> c * XA a x * d * XB b x = c * d * (XA a x * XB b x)" using eq by simp
  qed
qed

lemma (in cpx_sq_mat) lhv_lsum_scal_integrable:
  assumes "lhv M A B R XA XB"
  and  "a\<in> spectrum A"
shows "integrable M (\<lambda>x. \<Sum>b\<in>spectrum B. c * XA a x * (f b) * XB b x)"
proof (rule Bochner_Integration.integrable_sum)
  fix b
  assume "b\<in> spectrum B"
  thus "integrable M (\<lambda>x. c * XA a x * f b *XB b x)" using \<open>a\<in> spectrum A\<close> assms 
    lhv_scal_integrable[of M] by simp
qed

lemma (in cpx_sq_mat) lhv_sum_integrable:
  assumes "lhv M A B R XA XB"
shows "integrable M (\<lambda>w.  (\<Sum> a \<in> spectrum A. (\<Sum> b \<in> spectrum B. f a * XA a w * g b * XB b w)))"
proof (rule Bochner_Integration.integrable_sum)
  fix a
  assume "a\<in> spectrum A"
  thus "integrable M (\<lambda>x. \<Sum>b\<in>spectrum B. f a * XA a x * g b * XB b x)" 
    using assms lhv_lsum_scal_integrable[of M] 
    by simp  
qed

lemma (in cpx_sq_mat) spectrum_abs_1_weighted_suml:
  assumes "lhv M A B R Va Vb"
and "{Re x |x. x \<in> spectrum A} \<noteq> {}"
  and "{Re x |x. x \<in> spectrum A} \<subseteq> {- 1, 1}"
and "hermitian A"
  and "A\<in> fc_mats"
shows "AE w in M. \<bar>(\<Sum>a\<in>spectrum A. Re a * Va a w)\<bar> \<le> 1" 
proof (rule AE_mp)
  show "AE w in M. (\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1"
    using assms lhv_AE_propl[of M A B _ Va] by simp
  show "AE w in M. (\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1 \<longrightarrow>
               \<bar>\<Sum>a\<in>spectrum A. Re a * Va a w\<bar> \<le> 1"
  proof
    fix w
    assume "w\<in> space M"
    show "(\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1 \<longrightarrow>
         \<bar>\<Sum>a\<in>spectrum A. Re a * Va a w\<bar> \<le> 1"
    proof (intro impI)
      assume pr: "(\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1"
      show "\<bar>(\<Sum>a\<in>spectrum A. Re a * Va a w)\<bar> \<le> 1"
      proof (cases "{Re x |x. x \<in> spectrum A} = {- 1, 1}")
        case True
        hence sp: "spectrum A = {-1, 1}" using hermitian_Re_spectrum[of A] assms by simp
        hence scsum: "(\<Sum>a\<in>spectrum A. Re a * Va a w) = Va 1 w - Va (-1) w"
          using sum_2_elems by simp
        have sum: "(\<Sum>a\<in>spectrum A. Va a w) = Va (-1) w + Va 1 w"
          using sp sum_2_elems by simp
        have "\<bar>Va 1 w - Va (-1) w\<bar> \<le> 1"
        proof (rule fct_bound')
          have "1 \<in> spectrum A" using sp by simp
          thus "0 \<le> Va 1 w" using pr  by simp
          have "-1 \<in> spectrum A" using sp by simp
          thus "0 \<le> Va (- 1) w" using pr by simp
          show "Va (- 1) w + Va 1 w = 1" using pr sum by simp
        qed
        thus ?thesis using scsum by simp
      next      
        case False
        then show ?thesis 
        proof (cases "{Re x |x. x \<in> spectrum A} = {- 1}")
          case True
          hence "spectrum A = {-1}" using hermitian_Re_spectrum[of A] assms by simp
          hence "(\<Sum>a\<in>spectrum A. Re a * Va a w) = - Va (-1) w" by simp 
          moreover have "-1 \<in> spectrum A" using \<open>spectrum A = {-1}\<close> by simp
          ultimately show ?thesis using pr by simp
        next
          case False
          hence "{Re x |x. x \<in> spectrum A} = {1}" using assms \<open>{Re x |x. x \<in> spectrum A} \<noteq> {-1, 1}\<close>
            last_subset[of "{Re x |x. x \<in> spectrum A}"] by simp
          hence "spectrum A = {1}" using hermitian_Re_spectrum[of A] assms by simp
          hence "(\<Sum>a\<in>spectrum A. Re a * Va a w) = Va 1 w" by simp 
          moreover have "1 \<in> spectrum A" using \<open>spectrum A = {1}\<close> by simp
          ultimately show ?thesis using pr by simp
        qed        
      qed
    qed
  qed
qed

lemma (in cpx_sq_mat) spectrum_abs_1_weighted_sumr:
  assumes "lhv M B A R Vb Va"
and "{Re x |x. x \<in> spectrum A} \<noteq> {}"
  and "{Re x |x. x \<in> spectrum A} \<subseteq> {- 1, 1}"
and "hermitian A"
  and "A\<in> fc_mats"
shows "AE w in M. \<bar>(\<Sum>a\<in>spectrum A. Re a * Va a w)\<bar> \<le> 1" 
proof (rule AE_mp)
  show "AE w in M. (\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1"
    using assms lhv_AE_propr[of M B A _ Vb] by simp
  show "AE w in M. (\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1 \<longrightarrow>
               \<bar>\<Sum>a\<in>spectrum A. Re a * Va a w\<bar> \<le> 1"
  proof
    fix w
    assume "w\<in> space M"
    show "(\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1 \<longrightarrow>
         \<bar>\<Sum>a\<in>spectrum A. Re a * Va a w\<bar> \<le> 1"
    proof (intro impI)
      assume pr: "(\<forall>a\<in>spectrum A. 0 \<le> Va a w \<and> Va a w \<le> 1) \<and> (\<Sum>a\<in>spectrum A. Va a w) = 1"
      show "\<bar>(\<Sum>a\<in>spectrum A. Re a * Va a w)\<bar> \<le> 1"
      proof (cases "{Re x |x. x \<in> spectrum A} = {- 1, 1}")
        case True
        hence sp: "spectrum A = {-1, 1}" using hermitian_Re_spectrum[of A] assms by simp
        hence scsum: "(\<Sum>a\<in>spectrum A. Re a * Va a w) = Va 1 w - Va (-1) w"
          using sum_2_elems by simp
        have sum: "(\<Sum>a\<in>spectrum A. Va a w) = Va (-1) w + Va 1 w"
          using sp sum_2_elems by simp
        have "\<bar>Va 1 w - Va (-1) w\<bar> \<le> 1"
        proof (rule fct_bound')
          have "1 \<in> spectrum A" using sp by simp
          thus "0 \<le> Va 1 w" using pr  by simp
          have "-1 \<in> spectrum A" using sp by simp
          thus "0 \<le> Va (- 1) w" using pr by simp
          show "Va (- 1) w + Va 1 w = 1" using pr sum by simp
        qed
        thus ?thesis using scsum by simp
      next      
        case False
        then show ?thesis 
        proof (cases "{Re x |x. x \<in> spectrum A} = {- 1}")
          case True
          hence "spectrum A = {-1}" using hermitian_Re_spectrum[of A] assms by simp
          hence "(\<Sum>a\<in>spectrum A. Re a * Va a w) = - Va (-1) w" by simp 
          moreover have "-1 \<in> spectrum A" using \<open>spectrum A = {-1}\<close> by simp
          ultimately show ?thesis using pr by simp
        next
          case False
          hence "{Re x |x. x \<in> spectrum A} = {1}" using assms \<open>{Re x |x. x \<in> spectrum A} \<noteq> {-1, 1}\<close>
            last_subset[of "{Re x |x. x \<in> spectrum A}"] by simp
          hence "spectrum A = {1}" using hermitian_Re_spectrum[of A] assms by simp
          hence "(\<Sum>a\<in>spectrum A. Re a * Va a w) = Va 1 w" by simp 
          moreover have "1 \<in> spectrum A" using \<open>spectrum A = {1}\<close> by simp
          ultimately show ?thesis using pr by simp
        qed        
      qed
    qed
  qed
qed

definition qt_expect where
"qt_expect A Va = (\<lambda>w. (\<Sum>a\<in>spectrum A. Re a * Va a w))"

lemma (in cpx_sq_mat) spectr_sum_integrable:
assumes "lhv M A B R Va Vb"
shows "integrable M (\<lambda>w. qt_expect A Va w * qt_expect B Vb w)" 
proof (rule Bochner_Integration.integrable_cong[THEN iffD2])
  show "M = M" by simp
  show "\<And>w. w \<in> space M \<Longrightarrow> qt_expect A Va w * qt_expect B Vb w = 
    (\<Sum>a\<in>spectrum A. (\<Sum>b\<in>spectrum B. Re a * Va a w * Re b * Vb b w))"
  proof -
    fix w
    assume "w\<in> space M"
    show "qt_expect A Va w * qt_expect B Vb w = 
      (\<Sum>a\<in>spectrum A. (\<Sum>b\<in>spectrum B. Re a * Va a w * Re b * Vb b w))" unfolding qt_expect_def
      by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux sum_product 
          vector_space_over_itself.scale_scale)
  qed
  show "integrable M (\<lambda>w. \<Sum>a\<in>spectrum A. (\<Sum>b\<in>spectrum B. Re a * Va a w * Re b * Vb b w))" 
    using lhv_sum_integrable[of M] assms by simp
qed 

lemma (in cpx_sq_mat) lhv_sum_integral':
  assumes "lhv M A B R XA XB"
shows "integral\<^sup>L M (\<lambda>w. (\<Sum> a \<in> spectrum A. f a * XA a w) * (\<Sum> b \<in> spectrum B. g b * XB b w)) =
  (\<Sum> a \<in> spectrum A. f a * (\<Sum> b \<in> spectrum B. g b  * integral\<^sup>L M (\<lambda>w. XA a w * XB b w)))" 
proof -
  have "integral\<^sup>L M (\<lambda>w. (\<Sum> a \<in> spectrum A. f a * XA a w) * (\<Sum> b \<in> spectrum B. g b * XB b w)) =
    integral\<^sup>L M (\<lambda>w. (\<Sum> a \<in> spectrum A. (\<Sum> b \<in> spectrum B. f a * XA a w * g b * XB b w)))"  
  proof (rule Bochner_Integration.integral_cong, simp)
    fix w
    assume "w\<in> space M"
    show "(\<Sum>a\<in>spectrum A. f a * XA a w) * (\<Sum>b\<in>spectrum B. g b * XB b w) = 
      (\<Sum>a\<in>spectrum A. (\<Sum>b\<in>spectrum B. f a * XA a w * (g b) * XB b w))"
      by (simp add: sum_product vector_space_over_itself.scale_scale) 
  qed
  also have "... = (\<Sum> a \<in> spectrum A. 
    integral\<^sup>L M (\<lambda>w. (\<Sum> b \<in> spectrum B. f a * XA a w * g b * XB b w)))" 
  proof (rule Bochner_Integration.integral_sum)
    fix a
    assume "a\<in> spectrum A"
    thus "integrable M (\<lambda>x. \<Sum>b\<in>spectrum B. f a * XA a x * g b * XB b x)" 
      using lhv_lsum_scal_integrable[of M] assms by simp
  qed
  also have "... = (\<Sum> a \<in> spectrum A. f a *
    integral\<^sup>L M (\<lambda>w. (\<Sum> b \<in> spectrum B. XA a w * g b * XB b w)))" 
  proof -
    have "\<forall> a\<in> spectrum A. integral\<^sup>L M (\<lambda>w. (\<Sum> b \<in> spectrum B. f a * XA a w * g b * XB b w)) =
      f a * integral\<^sup>L M (\<lambda>w. (\<Sum> b \<in> spectrum B. XA a w * g b * XB b w))"
    proof
      fix a
      assume "a\<in> spectrum A"
      have "(LINT w|M. (\<Sum>b\<in>spectrum B. f a * XA a w * g b * XB b w)) = 
        (LINT w|M. f a* (\<Sum>b\<in>spectrum B. XA a w * g b * XB b w))"
      proof (rule Bochner_Integration.integral_cong, simp)
        fix x
        assume "x \<in> space M"
        show "(\<Sum>b\<in>spectrum B. f a * XA a x * g b * XB b x) = 
          f a * (\<Sum>b\<in>spectrum B. XA a x * g b * XB b x)"
          by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux 
              vector_space_over_itself.scale_scale vector_space_over_itself.scale_sum_right)
      qed
      also have "... = f a * (LINT w|M. (\<Sum>b\<in>spectrum B. XA a w * g b * XB b w))" by simp
      finally show "(LINT w|M. (\<Sum>b\<in>spectrum B. f a * XA a w * g b * XB b w)) = 
        f a * (LINT w|M. (\<Sum>b\<in>spectrum B. XA a w * g b * XB b w))" .
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum> a \<in> spectrum A. f a * (\<Sum> b \<in> spectrum B. g b *
    integral\<^sup>L M (\<lambda>w. XA a w * XB b w)))"
  proof (rule sum.cong, simp)
    fix a
      assume "a\<in> spectrum A"
      have "integral\<^sup>L M (\<lambda>w. (\<Sum> b \<in> spectrum B. XA a w * g b * XB b w)) = (\<Sum> b \<in> spectrum B. 
      integral\<^sup>L M (\<lambda>w. XA a w * g b * XB b w))"
      proof (rule Bochner_Integration.integral_sum)
        show "\<And>b. b \<in> spectrum B \<Longrightarrow> integrable M (\<lambda>x. XA a x * g b * XB b x)"
        proof -
          fix b
          assume "b\<in> spectrum B"
          thus "integrable M (\<lambda>x. XA a x * g b * XB b x)" 
            using assms lhv_scal_integrable[of M _ _ _ _ _ a b 1] \<open>a\<in> spectrum A\<close> by simp
        qed
      qed
      also have "... = (\<Sum> b \<in> spectrum B. g b * integral\<^sup>L M (\<lambda>w. XA a w * XB b w))" 
      proof (rule sum.cong, simp)
        fix x
        assume "x\<in> spectrum B"
        have "LINT w|M. XA a w * g x * XB x w = LINT w|M. g x * (XA a w * XB x w)"
          by (rule Bochner_Integration.integral_cong, auto)
        also have "... = g x * (LINT w|M. XA a w * XB x w)"
          using Bochner_Integration.integral_mult_right_zero[of M "g x" "\<lambda>w. XA a w * XB x w"] 
          by simp
        finally show "LINT w|M. XA a w * g x * XB x w = g x * (LINT w|M. XA a w * XB x w)" .
      qed
      finally have "integral\<^sup>L M (\<lambda>w. (\<Sum> b \<in> spectrum B. XA a w * g b * XB b w)) = 
        (\<Sum> b \<in> spectrum B. g b * integral\<^sup>L M (\<lambda>w. XA a w * XB b w))" .
      thus "f a * (LINT w|M. (\<Sum>b\<in>spectrum B. XA a w * g b * XB b w)) =
        f a * (\<Sum> b \<in> spectrum B. g b * integral\<^sup>L M (\<lambda>w. XA a w * XB b w))" by simp 
    qed
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) sum_qt_expect_trace:
  assumes "lhv M A B R XA XB"
  shows "(\<Sum> a \<in> spectrum A. f a * (\<Sum> b \<in> spectrum B. g b * integral\<^sup>L M (\<lambda>w. XA a w * XB b w))) =
    (\<Sum> a \<in> spectrum A. f a * (\<Sum> b \<in> spectrum B. g b * 
    Re (Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))))"
proof (rule sum.cong, simp)
  fix a
  assume "a\<in> spectrum A"
  have "(\<Sum>b\<in>spectrum B. g b * (LINT w|M. XA a w * XB b w)) =
       (\<Sum>b\<in>spectrum B. g b * 
        Re (Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R)))" 
  proof (rule sum.cong, simp)
    fix b
    assume "b\<in> spectrum B"
    show "g b * (LINT w|M. XA a w * XB b w) = 
      g b * Re (Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R))"
      using lhv_integral_eq[of M] assms \<open>a \<in> spectrum A\<close> \<open>b \<in> spectrum B\<close> by simp
  qed
  thus "f a * (\<Sum>b\<in>spectrum B. g b * (LINT w|M. XA a w * XB b w)) =
        f a * (\<Sum>b\<in>spectrum B. g b * 
        Re (Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R)))" by simp
qed

lemma (in cpx_sq_mat) sum_eigen_projector_trace_dist:
  assumes "hermitian B"
and "A\<in> fc_mats"
and "B\<in> fc_mats"
and "R\<in> fc_mats"
  shows "(\<Sum> b \<in> spectrum B. (b * 
    Complex_Matrix.trace(A * (eigen_projector B b) * R))) = Complex_Matrix.trace(A * B * R)" 
proof -
  have "(\<Sum>b\<in>spectrum B. b * Complex_Matrix.trace (A * eigen_projector B b * R)) =
       (\<Sum>b\<in>spectrum B. Complex_Matrix.trace (A * (b \<cdot>\<^sub>m (eigen_projector B b)) * R))"
  proof (rule sum.cong, simp)
    fix b
    assume "b\<in> spectrum B"
    have "b * Complex_Matrix.trace (A * eigen_projector B b * R) = 
      Complex_Matrix.trace (b \<cdot>\<^sub>m (A * eigen_projector B b * R))" 
    proof (rule trace_smult[symmetric])
      show "A * eigen_projector B b * R \<in> carrier_mat dimR dimR" using eigen_projector_carrier 
          assms fc_mats_carrier dim_eq  \<open>b \<in> spectrum B\<close> cpx_sq_mat_mult by meson
    qed
    also have "... = Complex_Matrix.trace (A * (b \<cdot>\<^sub>m eigen_projector B b) * R)"
    proof -
      have "b \<cdot>\<^sub>m (A * eigen_projector B b * R) = b \<cdot>\<^sub>m (A * (eigen_projector B b * R))" 
      proof -
        have "A * eigen_projector B b * R = A * (eigen_projector B b * R)"
          by (metis \<open>b \<in> spectrum B\<close> assms(1) assms(2) assms(3) assms(4) assoc_mult_mat dim_eq 
              fc_mats_carrier eigen_projector_carrier)
        thus ?thesis by simp
      qed
      also have "... = A * (b \<cdot>\<^sub>m (eigen_projector B b * R))" 
      proof (rule mult_smult_distrib[symmetric])
        show "A \<in> carrier_mat dimR dimR" using eigen_projector_carrier  assms 
            fc_mats_carrier dim_eq by simp
        show "eigen_projector B b * R \<in> carrier_mat dimR dimR" using eigen_projector_carrier 
            \<open>b \<in> spectrum B\<close> assms fc_mats_carrier dim_eq cpx_sq_mat_mult by blast
      qed
      also have "... = A * ((b \<cdot>\<^sub>m eigen_projector B b) * R)"
      proof -
        have "b \<cdot>\<^sub>m (eigen_projector B b * R) = (b \<cdot>\<^sub>m eigen_projector B b) * R"
        proof (rule mult_smult_assoc_mat[symmetric])
          show "eigen_projector B b \<in> carrier_mat dimR dimR" using eigen_projector_carrier 
              \<open>b \<in> spectrum B\<close> assms fc_mats_carrier dim_eq by simp
          show "R \<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
        qed
        thus ?thesis by simp
      qed
      also have "... = A * (b \<cdot>\<^sub>m eigen_projector B b) * R"
        by (metis \<open>b \<in> spectrum B\<close> assms(1) assms(2) assms(3) assms(4) assoc_mult_mat 
            cpx_sq_mat_smult dim_eq fc_mats_carrier eigen_projector_carrier)
      finally have "b \<cdot>\<^sub>m (A * eigen_projector B b * R) = A * (b \<cdot>\<^sub>m eigen_projector B b) * R" .
      then show ?thesis by simp
    qed
    finally show "b * Complex_Matrix.trace (A * eigen_projector B b * R) = 
      Complex_Matrix.trace (A * (b \<cdot>\<^sub>m eigen_projector B b) * R)" .
  qed
  also have "... = Complex_Matrix.trace (A * 
    (sum_mat (\<lambda>b. b \<cdot>\<^sub>m eigen_projector B b) (spectrum B)) * R)" 
  proof (rule trace_sum_mat_mat_distrib, (auto simp add: assms))
    show "finite (spectrum B)" using spectrum_finite[of B] by simp
    fix b
    assume "b\<in> spectrum B"
    show "b \<cdot>\<^sub>m eigen_projector B b \<in> fc_mats"
      by (simp add: \<open>b \<in> spectrum B\<close> assms(1) assms(3) cpx_sq_mat_smult eigen_projector_carrier)
  qed
  also have "... = Complex_Matrix.trace (A * B * R)"
  proof -
    have "sum_mat (\<lambda>b. b \<cdot>\<^sub>m eigen_projector B b) (spectrum B) = B" using make_pm_sum' assms by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) sum_eigen_projector_trace_right:
  assumes "hermitian A"
and "A\<in> fc_mats"
and "B\<in> fc_mats"
shows "(\<Sum> a \<in> spectrum A. Complex_Matrix.trace (a \<cdot>\<^sub>m eigen_projector A a * B)) = 
  Complex_Matrix.trace (A * B)"
proof -
  have "sum_mat (\<lambda>a. a \<cdot>\<^sub>m eigen_projector A a * B) (spectrum A) = 
    sum_mat (\<lambda>a. a \<cdot>\<^sub>m eigen_projector A a) (spectrum A) * B"
  proof (rule mult_sum_mat_distrib_right)
    show "finite (spectrum A)" using spectrum_finite[of A] by simp
    show "\<And>a. a \<in> spectrum A \<Longrightarrow> a \<cdot>\<^sub>m eigen_projector A a \<in> fc_mats"
      using assms(1) assms(2) cpx_sq_mat_smult eigen_projector_carrier by blast
    show "B\<in> fc_mats" using assms by simp
  qed
  also have "... = A * B" using make_pm_sum' assms by simp
  finally have seq: "sum_mat (\<lambda>a. a \<cdot>\<^sub>m eigen_projector A a * B) (spectrum A) = A * B" .
  have "(\<Sum> a \<in> spectrum A. Complex_Matrix.trace (a \<cdot>\<^sub>m eigen_projector A a * B)) =
    Complex_Matrix.trace (sum_mat (\<lambda>a. a \<cdot>\<^sub>m eigen_projector A a * B) (spectrum A))" 
  proof (rule trace_sum_mat[symmetric])
    show "finite (spectrum A)" using spectrum_finite[of A] by simp
    show "\<And>a. a \<in> spectrum A \<Longrightarrow> a \<cdot>\<^sub>m eigen_projector A a * B \<in> fc_mats"
      by (simp add: assms(1) assms(2) assms(3) cpx_sq_mat_mult cpx_sq_mat_smult 
          eigen_projector_carrier)
  qed
  also have "... = Complex_Matrix.trace (A * B)" using seq by simp
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) sum_eigen_projector_trace:
  assumes "hermitian A"
  and "hermitian B"
  and "A\<in> fc_mats"
  and "B\<in> fc_mats"
and "R\<in> fc_mats"
  shows "(\<Sum> a \<in> spectrum A.  a *  (\<Sum> b \<in> spectrum B. (b * 
    Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R)))) = 
    Complex_Matrix.trace(A * B * R)" 
proof -
  have "(\<Sum> a \<in> spectrum A.  a *  (\<Sum> b \<in> spectrum B. (b * 
    Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R)))) = (\<Sum> a \<in> spectrum A.   
    Complex_Matrix.trace (a \<cdot>\<^sub>m eigen_projector A a * (B * R)))" 
  proof (rule sum.cong, simp)
    fix a
    assume "a\<in> spectrum A"
    hence "(\<Sum>b\<in>spectrum B. b * 
      Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R)) =
      Complex_Matrix.trace (eigen_projector A a * B * R)" using 
      sum_eigen_projector_trace_dist[of B "eigen_projector A a" R] assms eigen_projector_carrier 
      by blast 
    hence "a *  (\<Sum> b \<in> spectrum B. (b * 
      Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))) = 
      a * Complex_Matrix.trace (eigen_projector A a * B * R)" by simp
    also have "... = Complex_Matrix.trace (a \<cdot>\<^sub>m (eigen_projector A a * B * R))" 
      using trace_smult[symmetric, of "eigen_projector A a * B * R" dimR a] assms
       \<open>a \<in> spectrum A\<close> cpx_sq_mat_mult dim_eq fc_mats_carrier eigen_projector_carrier by force
    also have "... = Complex_Matrix.trace (a \<cdot>\<^sub>m eigen_projector A a * (B * R))"
    proof -
      have "a \<cdot>\<^sub>m (eigen_projector A a * B * R) = a \<cdot>\<^sub>m (eigen_projector A a * B) * R" 
      proof (rule  mult_smult_assoc_mat[symmetric])
        show "R\<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
        show "eigen_projector A a * B \<in> carrier_mat dimR dimR" using assms eigen_projector_carrier 
            cpx_sq_mat_mult fc_mats_carrier dim_eq \<open>a \<in> spectrum A\<close> by blast
      qed
      also have "... = a \<cdot>\<^sub>m eigen_projector A a * B * R"
      proof -
        have "a \<cdot>\<^sub>m (eigen_projector A a * B) = a \<cdot>\<^sub>m eigen_projector A a * B" 
          using mult_smult_assoc_mat[symmetric]
        proof -
          show ?thesis
            by (metis \<open>\<And>nr nc n k B A. \<lbrakk>A \<in> carrier_mat nr n; B \<in> carrier_mat n nc\<rbrakk> \<Longrightarrow> 
              k \<cdot>\<^sub>m (A * B) = k \<cdot>\<^sub>m A * B\<close> \<open>a \<in> spectrum A\<close> assms(1) assms(3) assms(4) dim_eq 
                fc_mats_carrier eigen_projector_carrier)
        qed
        thus ?thesis by simp
      qed
      also have "... = a \<cdot>\<^sub>m eigen_projector A a * (B * R)"
        by (metis \<open>a \<in> spectrum A\<close> assms(1) assms(3) assms(4) assms(5) assoc_mult_mat 
            cpx_sq_mat_smult dim_eq fc_mats_carrier eigen_projector_carrier)
      finally show ?thesis by simp
    qed
    finally show "a *  (\<Sum> b \<in> spectrum B. (b * 
      Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))) =
      Complex_Matrix.trace (a \<cdot>\<^sub>m eigen_projector A a * (B * R))"  . 
  qed
  also have "... = Complex_Matrix.trace (A * (B * R))" 
    using sum_eigen_projector_trace_right[of A "B * R"] assms by (simp add: cpx_sq_mat_mult) 
  also have "... = Complex_Matrix.trace (A * B * R)"
  proof -
    have "A * (B * R) = A * B * R" 
    proof (rule assoc_mult_mat[symmetric])
      show "A\<in>  carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
      show "B\<in>  carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
      show "R\<in>  carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
    qed
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

text \<open>We obtain the main result of this part, which relates the quantum expectation value of a 
joint measurement with an expectation.\<close>

lemma (in cpx_sq_mat) sum_qt_expect:
  assumes "lhv M A B R XA XB"
  and "A\<in> fc_mats"
  and "B\<in> fc_mats"
  and "R\<in> fc_mats"
  and "hermitian A"
  and "hermitian B"
  shows "integral\<^sup>L M (\<lambda>w. (qt_expect A XA w) * (qt_expect B XB w)) = 
    Re (Complex_Matrix.trace(A * B * R))"
proof -
  have br: "\<forall> b \<in> spectrum B. b\<in> Reals" using assms hermitian_spectrum_real[of B] by auto
  have ar: "\<forall>a \<in> spectrum A. a\<in> Reals" using hermitian_spectrum_real[of A] assms by auto
  have "integral\<^sup>L M (\<lambda>w. (\<Sum> a \<in> spectrum A. Re a* XA a w) * (\<Sum> b \<in> spectrum B. Re b *XB b w)) = 
    (\<Sum> a \<in> spectrum A. Re a * (\<Sum> b \<in> spectrum B. Re b * integral\<^sup>L M (\<lambda>w. XA a w * XB b w)))"
    using lhv_sum_integral'[of M] assms by simp
  also have "... = (\<Sum> a \<in> spectrum A. Re a * (\<Sum> b \<in> spectrum B. Re b * 
    Re (Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))))"
    using assms sum_qt_expect_trace[of M] by simp
  also have "... = (\<Sum> a \<in> spectrum A. Re a * Re (\<Sum> b \<in> spectrum B. (b * 
    Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))))"
  proof (rule sum.cong, simp)
    fix a 
    assume "a\<in> spectrum A" 
    have "(\<Sum>b\<in>spectrum B. Re b * 
      Re (Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R))) =
      (\<Sum> b \<in> spectrum B. Re (b * 
      Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R)))"
    proof (rule sum.cong, simp)
      fix b
      assume "b\<in> spectrum B"
      hence "b\<in> Reals" using hermitian_spectrum_real[of B] assms by simp
      hence "Re b = b" by simp
      thus "Re b * Re (Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R)) =
         Re (b * Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R))" 
        using hermitian_spectrum_real using \<open>b \<in> \<real>\<close> mult_real_cpx by auto
    qed
    also have "... = 
      Re (\<Sum> b \<in> spectrum B. b * 
        Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))" by simp
    finally have "(\<Sum>b\<in>spectrum B. Re b * 
      Re (Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R))) =
      Re (\<Sum> b \<in> spectrum B. b * 
        Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))" .
    thus "Re a * (\<Sum>b\<in>spectrum B. Re b * 
      Re (Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R))) =
         Re a * Re (\<Sum>b\<in>spectrum B.  
          (b * Complex_Matrix.trace (eigen_projector A a * eigen_projector B b * R)))"
      by simp
  qed
  also have "... =  (\<Sum> a \<in> spectrum A. Re (a * (\<Sum> b \<in> spectrum B. (b * 
    Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R)))))"
  proof (rule sum.cong, simp)
    fix x
    assume "x\<in> spectrum A"
    hence "Re x = x" using ar by simp
    thus "Re x * Re (\<Sum>b\<in>spectrum B. b * 
      Complex_Matrix.trace (eigen_projector A x * eigen_projector B b * R)) =
         Re (x * (\<Sum>b\<in>spectrum B. b * 
        Complex_Matrix.trace (eigen_projector A x * eigen_projector B b * R)))"
      using \<open>x \<in> spectrum A\<close> ar mult_real_cpx by auto
  qed
  also have "... = Re (\<Sum> a \<in> spectrum A.  a *  (\<Sum> b \<in> spectrum B. (b * 
    Complex_Matrix.trace(eigen_projector A a * (eigen_projector B b) * R))))" by simp
  also have "... = Re (Complex_Matrix.trace(A *B * R))" using assms 
    sum_eigen_projector_trace[of A B] by simp
  finally show ?thesis unfolding qt_expect_def .
qed


subsection \<open>Properties of specific observables\<close>

text \<open>In this part we consider a specific density operator and specific observables corresponding 
to joint bipartite measurements. We will compute the quantum expectation value of this system and 
prove that it violates the CHSH inequality, thus proving that the local hidden variable assumption 
cannot hold.\<close>

subsubsection \<open>Ket 0, Ket 1 and the corresponding projectors\<close>

definition ket_0::"complex Matrix.vec" where
"ket_0 = unit_vec 2 0"

lemma ket_0_dim:
  shows "dim_vec ket_0 = 2" unfolding ket_0_def by simp

lemma ket_0_norm:
  shows "\<parallel>ket_0\<parallel> = 1" using unit_cpx_vec_length unfolding ket_0_def by simp

lemma ket_0_mat:
  shows "ket_vec ket_0 =  Matrix.mat_of_cols_list 2 [[1, 0]]"
  by (auto simp add: ket_vec_def Matrix.mat_of_cols_list_def ket_0_def)

definition ket_1::"complex Matrix.vec" where
"ket_1 = unit_vec 2 1"

lemma ket_1_dim:
  shows "dim_vec ket_1 = 2" unfolding ket_1_def by simp

lemma ket_1_norm:
  shows "\<parallel>ket_1\<parallel> = 1" using unit_cpx_vec_length unfolding ket_1_def by simp

definition ket_01
  where "ket_01 = tensor_vec ket_0 ket_1"

lemma ket_01_dim:
  shows "dim_vec ket_01 = 4" unfolding ket_01_def
  by (simp add: ket_0_dim ket_1_dim)

definition  ket_10 
  where "ket_10 = tensor_vec ket_1 ket_0"

lemma ket_10_dim:
  shows "dim_vec ket_10 = 4" unfolding ket_10_def by (simp add: ket_0_dim ket_1_dim)

text \<open>We define \verb+ket_psim+, one of the Bell states (or EPR pair).\<close>

definition ket_psim where
"ket_psim = 1/(sqrt 2) \<cdot>\<^sub>v (ket_01 - ket_10)"

lemma  ket_psim_dim:
  shows "dim_vec ket_psim = 4" using ket_01_dim ket_10_dim unfolding ket_psim_def by simp

lemma ket_psim_norm:
  shows "\<parallel>ket_psim\<parallel> = 1" 
proof -
  have "dim_vec ket_psim = 2\<^sup>2" unfolding ket_psim_def ket_01_def ket_10_def ket_0_def ket_1_def 
  by simp
  moreover have "(\<Sum>i<4. (cmod (vec_index ket_psim i))\<^sup>2) = 1"
    apply (auto simp add: ket_psim_def ket_01_def ket_10_def ket_0_def ket_1_def)
    apply (simp add: sum_4_elems)
    done
  ultimately show ?thesis by (simp add: cpx_vec_length_def)
qed

text \<open>\verb+rho_psim+ represents the density operator associated with the quantum 
state \verb+ket_psim+.\<close>

definition  rho_psim where
"rho_psim = rank_1_proj ket_psim"

lemma rho_psim_carrier:
  shows "rho_psim \<in> carrier_mat 4 4" using rank_1_proj_carrier[of ket_psim] ket_psim_dim  
    rho_psim_def by simp

lemma  rho_psim_dim_row:
  shows "dim_row rho_psim = 4" using rho_psim_carrier by simp

lemma rho_psim_density:
  shows "density_operator rho_psim" unfolding density_operator_def
proof
  show "Complex_Matrix.positive rho_psim" using rank_1_proj_positive[of ket_psim] ket_psim_norm 
      rho_psim_def by simp
  show "Complex_Matrix.trace rho_psim = 1" using rank_1_proj_trace[of ket_psim] ket_psim_norm 
      rho_psim_def by simp
qed


subsubsection \<open>The X and Z matrices and two of their combinations\<close>

text \<open>In this part we prove properties of two standard matrices in quantum theory, $X$ and $Z$, 
as well as two of their combinations: $\frac{X+Z}{\sqrt{2}}$ and $\frac{Z - X}{\sqrt{2}}$. 
Note that all of these matrices are observables, they will be used to violate the CHSH inequality.\<close>

lemma Z_carrier: shows "Z \<in> carrier_mat 2 2" unfolding Z_def by simp

lemma Z_hermitian:
  shows "hermitian Z" using dagger_adjoint dagger_of_Z unfolding  hermitian_def by simp

lemma unitary_Z:
  shows "Complex_Matrix.unitary Z" 
proof -
  have "Complex_Matrix.adjoint Z * Z = (1\<^sub>m 2)" using dagger_adjoint[of Z] by simp
  thus ?thesis unfolding unitary_def
    by (metis Complex_Matrix.adjoint_adjoint Complex_Matrix.unitary_def Z_carrier adjoint_dim 
        carrier_matD(1) inverts_mat_def unitary_adjoint)
qed

lemma X_carrier: shows "X \<in> carrier_mat 2 2" unfolding X_def by simp

lemma X_hermitian:
  shows "hermitian X" using dagger_adjoint dagger_of_X unfolding  hermitian_def by simp

lemma unitary_X:
  shows "Complex_Matrix.unitary X" 
proof -
  have "Complex_Matrix.adjoint X * X = (1\<^sub>m 2)" using dagger_adjoint[of X] by simp
  thus ?thesis unfolding unitary_def
    by (metis Complex_Matrix.adjoint_adjoint Complex_Matrix.unitary_def X_carrier adjoint_dim 
        carrier_matD(1) inverts_mat_def unitary_adjoint) 
qed

definition XpZ
  where "XpZ = -1/sqrt(2) \<cdot>\<^sub>m (X + Z)"

lemma XpZ_carrier:
  shows "XpZ \<in> carrier_mat 2 2" unfolding XpZ_def X_def Z_def by simp

lemma XpZ_hermitian:
  shows "hermitian XpZ"
proof - 
  have "X + Z \<in> carrier_mat 2 2" using Z_carrier X_carrier by simp
  moreover have "hermitian (X + Z)" using X_hermitian Z_hermitian hermitian_add Matrix.mat_carrier
    unfolding X_def Z_def  by blast
  ultimately show ?thesis using hermitian_smult[of "X + Z" 2 "- 1 / sqrt 2"] unfolding XpZ_def  
    by auto
qed

lemma XpZ_inv:
  "XpZ * XpZ = 1\<^sub>m 2" unfolding XpZ_def X_def Z_def times_mat_def one_mat_def
  apply (rule cong_mat, simp+)
  apply (auto simp add: Matrix.scalar_prod_def)
   apply (auto simp add: Gates.csqrt_2_sq)
  done

lemma unitary_XpZ:
  shows "Complex_Matrix.unitary XpZ" 
proof -
  have "Complex_Matrix.adjoint XpZ * XpZ = (1\<^sub>m 2)" using XpZ_inv XpZ_hermitian 
    unfolding hermitian_def by simp
  thus ?thesis unfolding unitary_def
    by (metis Complex_Matrix.adjoint_adjoint Complex_Matrix.unitary_def XpZ_carrier adjoint_dim 
        carrier_matD(1) inverts_mat_def unitary_adjoint)
qed

definition ZmX
  where "ZmX = 1/sqrt(2) \<cdot>\<^sub>m (Z - X)"

lemma ZmX_carrier:
  shows "ZmX \<in> carrier_mat 2 2" unfolding ZmX_def X_def Z_def
  by (simp add: minus_carrier_mat')

lemma ZmX_hermitian:
  shows "hermitian ZmX"
proof - 
  have "Z - X \<in> carrier_mat 2 2" unfolding X_def Z_def
    by (simp add: minus_carrier_mat)
  moreover have "hermitian (Z - X)" using X_hermitian Z_hermitian hermitian_minus Matrix.mat_carrier
    unfolding X_def Z_def by blast
  ultimately show ?thesis using hermitian_smult[of "Z - X" 2 "1 / sqrt 2"] unfolding ZmX_def  
    by auto
qed

lemma ZmX_inv:
  "ZmX * ZmX = 1\<^sub>m 2" unfolding ZmX_def X_def Z_def times_mat_def one_mat_def
  apply (rule cong_mat, simp+)
  apply (auto simp add: Matrix.scalar_prod_def)
   apply (auto simp add: Gates.csqrt_2_sq)
  done

lemma unitary_ZmX:
  shows "Complex_Matrix.unitary ZmX" 
proof -
  have "Complex_Matrix.adjoint ZmX * ZmX = (1\<^sub>m 2)" using ZmX_inv ZmX_hermitian 
    unfolding hermitian_def by simp
  thus ?thesis unfolding unitary_def
    by (metis Complex_Matrix.adjoint_adjoint Complex_Matrix.unitary_def ZmX_carrier adjoint_dim 
        carrier_matD(1) inverts_mat_def unitary_adjoint)
qed

definition  Z_XpZ 
  where "Z_XpZ = tensor_mat Z XpZ"

lemma Z_XpZ_carrier:
  shows "Z_XpZ \<in> carrier_mat 4 4" unfolding Z_XpZ_def using tensor_mat_carrier XpZ_carrier 
    Z_carrier by auto

definition X_XpZ 
  where "X_XpZ = tensor_mat X XpZ"

lemma X_XpZ_carrier:
  shows "X_XpZ \<in> carrier_mat 4 4" using tensor_mat_carrier XpZ_carrier X_carrier 
  unfolding X_XpZ_def by auto

definition Z_ZmX
  where "Z_ZmX = tensor_mat Z ZmX"

lemma Z_ZmX_carrier:
  shows "Z_ZmX \<in> carrier_mat 4 4" using tensor_mat_carrier ZmX_carrier Z_carrier 
  unfolding Z_ZmX_def by auto

definition X_ZmX
  where "X_ZmX = tensor_mat X ZmX"

lemma X_ZmX_carrier:
  shows "X_ZmX \<in> carrier_mat 4 4" using tensor_mat_carrier X_carrier ZmX_carrier
  unfolding X_ZmX_def by auto

lemma  X_ZmX_rho_psim[simp]:
  shows "Complex_Matrix.trace (rho_psim * X_ZmX) = 1/ (sqrt 2)"
  apply (auto simp add: ket_10_def ket_1_def X_ZmX_def ZmX_def X_def ket_01_def
      Z_def rho_psim_def ket_psim_def rank_1_proj_def outer_prod_def ket_0_def)
  apply (auto simp add: Complex_Matrix.trace_def)  
  apply (simp add: sum_4_elems)
  apply (simp add: csqrt_2_sq)
  done

lemma  Z_ZmX_rho_psim[simp]:
  shows "Complex_Matrix.trace (rho_psim * Z_ZmX) = -1/ (sqrt 2)"
  apply (auto simp add: rho_psim_def ket_psim_def ket_10_def)
  apply (auto simp add: Z_ZmX_def Z_def ZmX_def X_def)
  apply (auto simp add: rank_1_proj_def outer_prod_def ket_01_def ket_1_def ket_0_def)
  apply (auto simp add: Complex_Matrix.trace_def sum_4_elems)
  apply (simp add: csqrt_2_sq)
  done

lemma X_XpZ_rho_psim[simp]:
  shows "Complex_Matrix.trace (rho_psim * X_XpZ) =1/ (sqrt 2)"
  apply (auto simp add: rho_psim_def ket_psim_def ket_10_def)
  apply (auto simp add: X_XpZ_def Z_def XpZ_def X_def)
  apply (auto simp add: rank_1_proj_def outer_prod_def ket_01_def ket_1_def ket_0_def)
  apply (auto simp add: Complex_Matrix.trace_def sum_4_elems)
  apply (simp add: csqrt_2_sq)
  done

lemma Z_XpZ_rho_psim[simp]:
  shows "Complex_Matrix.trace (rho_psim * Z_XpZ) =1/ (sqrt 2)"
  apply (auto simp add: rho_psim_def ket_psim_def ket_10_def)
  apply (auto simp add: Z_XpZ_def  XpZ_def X_def Z_def)
  apply (auto simp add: rank_1_proj_def outer_prod_def ket_01_def ket_1_def ket_0_def)
  apply (auto simp add: Complex_Matrix.trace_def sum_4_elems)
  apply (simp add: csqrt_2_sq)
  done

definition Z_I where
"Z_I = tensor_mat Z (1\<^sub>m 2)"

lemma Z_I_carrier:
  shows "Z_I \<in> carrier_mat 4 4" using tensor_mat_carrier Z_carrier unfolding Z_I_def by auto

lemma Z_I_hermitian:
  shows "hermitian Z_I" unfolding Z_I_def using tensor_mat_hermitian[of Z 2 "1\<^sub>m 2" 2]
  by (simp add: Z_carrier Z_hermitian hermitian_one)

lemma  Z_I_unitary:
  shows "unitary Z_I" unfolding Z_I_def using tensor_mat_unitary[of Z "1\<^sub>m 2"] Z_carrier unitary_Z
  using unitary_one by auto

lemma Z_I_spectrum:
  shows "{Re x |x. x \<in> spectrum Z_I} \<subseteq> {- 1, 1}" using unitary_hermitian_Re_spectrum Z_I_hermitian
    Z_I_unitary Z_I_carrier by simp

definition X_I where
"X_I = tensor_mat X (1\<^sub>m 2)"

lemma  X_I_carrier:
  shows "X_I \<in> carrier_mat 4 4" using tensor_mat_carrier X_carrier unfolding X_I_def by auto

lemma X_I_hermitian:
  shows "hermitian X_I" unfolding X_I_def using tensor_mat_hermitian[of X 2 "1\<^sub>m 2" 2]
  by (simp add: X_carrier X_hermitian hermitian_one)

lemma X_I_unitary:
  shows "unitary X_I" unfolding X_I_def using tensor_mat_unitary[of X "1\<^sub>m 2"] X_carrier unitary_X
  using unitary_one by auto

lemma  X_I_spectrum:
  shows "{Re x |x. x \<in> spectrum X_I} \<subseteq> {- 1, 1}" using unitary_hermitian_Re_spectrum X_I_hermitian
    X_I_unitary X_I_carrier by simp

definition  I_XpZ where
"I_XpZ = tensor_mat (1\<^sub>m 2) XpZ"

lemma  I_XpZ_carrier:
  shows "I_XpZ \<in> carrier_mat 4 4" using tensor_mat_carrier XpZ_carrier unfolding I_XpZ_def by auto

lemma  I_XpZ_hermitian:
  shows "hermitian I_XpZ" unfolding I_XpZ_def using tensor_mat_hermitian[of "1\<^sub>m 2" 2 XpZ 2]
  by (simp add: XpZ_carrier XpZ_hermitian hermitian_one)

lemma I_XpZ_unitary:
  shows "unitary I_XpZ" unfolding I_XpZ_def using tensor_mat_unitary[of "1\<^sub>m 2" XpZ] XpZ_carrier 
    unitary_XpZ using unitary_one by auto

lemma I_XpZ_spectrum:
  shows "{Re x |x. x \<in> spectrum I_XpZ} \<subseteq> {- 1, 1}" using unitary_hermitian_Re_spectrum 
    I_XpZ_hermitian I_XpZ_unitary I_XpZ_carrier by simp

definition I_ZmX where
"I_ZmX = tensor_mat (1\<^sub>m 2) ZmX"

lemma  I_ZmX_carrier:
  shows "I_ZmX \<in> carrier_mat 4 4" using tensor_mat_carrier ZmX_carrier unfolding I_ZmX_def by auto

lemma I_ZmX_hermitian:
  shows "hermitian I_ZmX" unfolding I_ZmX_def using tensor_mat_hermitian[of "1\<^sub>m 2" 2 ZmX 2]
  by (simp add: ZmX_carrier ZmX_hermitian hermitian_one)

lemma I_ZmX_unitary:
  shows "unitary I_ZmX" unfolding I_ZmX_def using tensor_mat_unitary[of "1\<^sub>m 2" ZmX] ZmX_carrier 
    unitary_ZmX using unitary_one by auto

lemma I_ZmX_spectrum:
  shows "{Re x |x. x \<in> spectrum I_ZmX} \<subseteq> {- 1, 1}" using unitary_hermitian_Re_spectrum I_ZmX_hermitian
    I_ZmX_unitary I_ZmX_carrier by simp

lemma X_I_ZmX_eq:
  shows "X_I * I_ZmX = X_ZmX" unfolding X_I_def I_ZmX_def X_ZmX_def using mult_distr_tensor
  by (metis (no_types, lifting) X_inv ZmX_inv index_mult_mat(2) index_mult_mat(3) index_one_mat(2) 
      index_one_mat(3) left_mult_one_mat' pos2 right_mult_one_mat')

lemma X_I_XpZ_eq:
  shows "X_I * I_XpZ = X_XpZ" unfolding X_I_def I_XpZ_def X_XpZ_def using mult_distr_tensor
  by (metis (no_types, lifting) X_inv XpZ_inv index_mult_mat(2) index_mult_mat(3) index_one_mat(2) 
      index_one_mat(3) left_mult_one_mat' pos2 right_mult_one_mat')

lemma Z_I_XpZ_eq:
  shows "Z_I * I_XpZ = Z_XpZ" unfolding Z_I_def I_XpZ_def Z_XpZ_def using mult_distr_tensor
  by (metis (no_types, lifting) Z_inv XpZ_inv index_mult_mat(2) index_mult_mat(3) index_one_mat(2) 
      index_one_mat(3) left_mult_one_mat' pos2 right_mult_one_mat')

lemma Z_I_ZmX_eq:
  shows "Z_I * I_ZmX = Z_ZmX" unfolding Z_I_def I_ZmX_def Z_ZmX_def using mult_distr_tensor
  by (metis (no_types, lifting) Z_inv ZmX_inv index_mult_mat(2) index_mult_mat(3) index_one_mat(2) 
      index_one_mat(3) left_mult_one_mat' pos2 right_mult_one_mat')


subsubsection \<open>No local hidden variable\<close>

text \<open>We show that the local hidden variable hypothesis cannot hold by exhibiting a quantum 
expectation value that is greater than the upper-bound givven by the CHSH inequality.\<close>

locale bin_cpx = cpx_sq_mat +
  assumes dim4: "dimR = 4"

lemma (in bin_cpx) X_I_XpZ_trace:
  assumes "lhv M X_I I_XpZ R Vx Vp"
  and "R\<in> fc_mats"
  shows "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_XpZ  Vp w) =
  Re (Complex_Matrix.trace (R * X_XpZ))" 
proof -
  have "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_XpZ  Vp w) =
  Re (Complex_Matrix.trace (X_I * I_XpZ * R))" 
  proof (rule sum_qt_expect, (simp add: assms))
    show "X_I \<in> fc_mats" using X_I_carrier dim4  fc_mats_carrier dim_eq by simp
    show "R\<in> fc_mats" using assms by simp
    show "I_XpZ \<in> fc_mats" using I_XpZ_carrier dim4 fc_mats_carrier dim_eq by simp
    show "hermitian X_I" using X_I_hermitian .
    show "hermitian I_XpZ" using I_XpZ_hermitian .
  qed
  also have "... = Re (Complex_Matrix.trace (X_XpZ * R))" using X_I_XpZ_eq by simp
  also have "... = Re (Complex_Matrix.trace (R * X_XpZ))" 
  proof -
    have "Complex_Matrix.trace (X_XpZ * R) = Complex_Matrix.trace (R * X_XpZ)" 
      using trace_comm[of X_XpZ 4 R] X_XpZ_carrier assms dim4 fc_mats_carrier dim_eq by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma (in bin_cpx) X_I_XpZ_chsh:
  assumes "lhv M X_I I_XpZ rho_psim Vx Vp"
  shows "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_XpZ Vp w) =
  1/sqrt 2" 
proof -
  have "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_XpZ Vp w) =
  Re (Complex_Matrix.trace (rho_psim * X_XpZ))" 
  proof (rule X_I_XpZ_trace, (simp add: assms))
    show "rho_psim \<in> fc_mats" using rho_psim_carrier fc_mats_carrier dim_eq dim4 by simp
  qed
  also have "... = 1/sqrt 2" using X_XpZ_rho_psim by simp
  finally show ?thesis .
qed

lemma (in bin_cpx) Z_I_XpZ_trace:
  assumes "lhv M Z_I I_XpZ R Vz Vp"
  and "R\<in> fc_mats"
  shows "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_XpZ Vp w) =
  Re (Complex_Matrix.trace (R * Z_XpZ))" 
proof -
  have "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_XpZ Vp w) =
  Re (Complex_Matrix.trace (Z_I * I_XpZ * R))" 
  proof (rule sum_qt_expect, (simp add: assms))
    show "Z_I \<in> fc_mats" using Z_I_carrier dim4 fc_mats_carrier dim_eq by simp
    show "R\<in> fc_mats" using assms by simp
    show "I_XpZ \<in> fc_mats" using I_XpZ_carrier dim4 fc_mats_carrier dim_eq by simp
    show "hermitian Z_I" using Z_I_hermitian .
    show "hermitian I_XpZ" using I_XpZ_hermitian .
  qed
  also have "... = Re (Complex_Matrix.trace (Z_XpZ * R))" using Z_I_XpZ_eq by simp
  also have "... = Re (Complex_Matrix.trace (R * Z_XpZ))" 
  proof -
    have "Complex_Matrix.trace (Z_XpZ * R) = Complex_Matrix.trace (R * Z_XpZ)" 
      using trace_comm[of Z_XpZ 4 R] Z_XpZ_carrier assms dim4 fc_mats_carrier dim_eq by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma (in bin_cpx) Z_I_XpZ_chsh:
  assumes "lhv M Z_I I_XpZ rho_psim Vz Vp"
  shows "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_XpZ Vp w) =
  1/sqrt 2" 
proof -
  have "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_XpZ Vp w) =
  Re (Complex_Matrix.trace (rho_psim * Z_XpZ))" 
  proof (rule Z_I_XpZ_trace, (simp add: assms))
    show "rho_psim \<in> fc_mats" using rho_psim_carrier fc_mats_carrier dim_eq dim4 by simp
  qed
  also have "... = 1/sqrt 2" using Z_XpZ_rho_psim by simp
  finally show ?thesis unfolding qt_expect_def .
qed

lemma (in bin_cpx) X_I_ZmX_trace:
  assumes "lhv M X_I I_ZmX R Vx Vp"
  and "R\<in> fc_mats"
  shows "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_ZmX Vp w) =
  Re (Complex_Matrix.trace (R * X_ZmX))" 
proof -
  have "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_ZmX Vp w) =
  Re (Complex_Matrix.trace (X_I * I_ZmX * R))" 
  proof (rule sum_qt_expect, (simp add: assms))
    show "X_I \<in> fc_mats" using X_I_carrier dim4 fc_mats_carrier dim_eq by simp
    show "R\<in> fc_mats" using assms by simp
    show "I_ZmX \<in> fc_mats" using I_ZmX_carrier dim4 fc_mats_carrier dim_eq by simp
    show "hermitian X_I" using X_I_hermitian .
    show "hermitian I_ZmX" using I_ZmX_hermitian .
  qed
  also have "... = Re (Complex_Matrix.trace (X_ZmX * R))" using X_I_ZmX_eq by simp
  also have "... = Re (Complex_Matrix.trace (R * X_ZmX))" 
  proof -
    have "Complex_Matrix.trace (X_ZmX * R) = Complex_Matrix.trace (R * X_ZmX)" 
      using trace_comm[of X_ZmX 4 R] X_ZmX_carrier assms dim4 fc_mats_carrier dim_eq by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma (in bin_cpx) X_I_ZmX_chsh:
  assumes "lhv M X_I I_ZmX rho_psim Vx Vp"
  shows "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_ZmX Vp w) =
  1/sqrt 2" 
proof -
  have "LINT w|M. (qt_expect X_I Vx w) * (qt_expect I_ZmX Vp w) =
  Re (Complex_Matrix.trace (rho_psim * X_ZmX))" 
  proof (rule X_I_ZmX_trace, (simp add: assms))
    show "rho_psim \<in> fc_mats" using rho_psim_carrier fc_mats_carrier dim_eq dim4 by simp
  qed
  also have "... = 1/sqrt 2" using X_ZmX_rho_psim by simp
  finally show ?thesis unfolding qt_expect_def .
qed

lemma (in bin_cpx) Z_I_ZmX_trace:
  assumes "lhv M Z_I I_ZmX R Vz Vp"
  and "R\<in> fc_mats"
  shows "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_ZmX Vp w) =
  Re (Complex_Matrix.trace (R * Z_ZmX))" 
proof -
  have "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_ZmX Vp w) =
  Re (Complex_Matrix.trace (Z_I * I_ZmX * R))" 
  proof (rule sum_qt_expect, (simp add: assms))
    show "Z_I \<in> fc_mats" using Z_I_carrier dim4 fc_mats_carrier dim_eq by simp
    show "R\<in> fc_mats" using assms by simp
    show "I_ZmX \<in> fc_mats" using I_ZmX_carrier dim4 fc_mats_carrier dim_eq by simp
    show "hermitian Z_I" using Z_I_hermitian .
    show "hermitian I_ZmX" using I_ZmX_hermitian .
  qed
  also have "... = Re (Complex_Matrix.trace (Z_ZmX * R))" using Z_I_ZmX_eq by simp
  also have "... = Re (Complex_Matrix.trace (R * Z_ZmX))" 
  proof -
    have "Complex_Matrix.trace (Z_ZmX * R) = Complex_Matrix.trace (R * Z_ZmX)" 
      using trace_comm[of Z_ZmX 4 R] Z_ZmX_carrier assms dim4 fc_mats_carrier dim_eq by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma (in bin_cpx) Z_I_ZmX_chsh:
  assumes "lhv M Z_I I_ZmX rho_psim Vz Vp"
shows "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_ZmX Vp w) =
  -1/sqrt 2" 
proof -
  have "LINT w|M. (qt_expect Z_I Vz w) * (qt_expect I_ZmX Vp w) =
  Re (Complex_Matrix.trace (rho_psim * Z_ZmX))" 
  proof (rule Z_I_ZmX_trace, (simp add: assms))
    show "rho_psim \<in> fc_mats" using rho_psim_carrier fc_mats_carrier dim_eq dim4 by simp
  qed
  also have "... = -1/sqrt 2" using Z_ZmX_rho_psim by simp
  finally show ?thesis unfolding qt_expect_def .
qed

lemma (in bin_cpx) chsh_upper_bound:
  assumes "prob_space M"
  and "lhv M X_I I_XpZ rho_psim Vx Vp"
  and "lhv M Z_I I_XpZ rho_psim Vz Vp"
  and "lhv M X_I I_ZmX rho_psim Vx Vm"
  and "lhv M Z_I I_ZmX rho_psim Vz Vm"
shows "\<bar>(LINT w|M. qt_expect X_I Vx w * qt_expect I_ZmX Vm w) + 
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_XpZ Vp w) + 
        (LINT w|M. qt_expect X_I Vx w * qt_expect I_XpZ Vp w) -
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_ZmX Vm w)\<bar>
  \<le> 2" 
proof (rule prob_space.chsh_expect)
  show "AE w in M. \<bar>qt_expect X_I Vx w\<bar> \<le> 1" unfolding qt_expect_def
  proof (rule spectrum_abs_1_weighted_suml)
    show "X_I \<in> fc_mats" using X_I_carrier fc_mats_carrier dim_eq dim4 by simp
    show "hermitian X_I" using X_I_hermitian .
    show "lhv M X_I I_XpZ rho_psim Vx Vp" using assms by simp
    show "{Re x |x. x \<in> spectrum X_I} \<subseteq> {- 1, 1}" using X_I_spectrum by simp
    show "{Re x |x. x \<in> spectrum X_I} \<noteq> {}" using spectrum_ne X_I_hermitian \<open>X_I \<in> fc_mats\<close> by auto
  qed
  show "AE w in M. \<bar>qt_expect Z_I Vz w\<bar> \<le> 1" unfolding qt_expect_def
  proof (rule spectrum_abs_1_weighted_suml)
    show "Z_I \<in> fc_mats" using Z_I_carrier fc_mats_carrier dim_eq dim4 by simp
    show "hermitian Z_I" using Z_I_hermitian .
    show "lhv M Z_I I_XpZ rho_psim Vz Vp" using assms by simp
    show "{Re x |x. x \<in> spectrum Z_I} \<subseteq> {- 1, 1}" using Z_I_spectrum by simp
    show "{Re x |x. x \<in> spectrum Z_I} \<noteq> {}" using spectrum_ne Z_I_hermitian \<open>Z_I \<in> fc_mats\<close> by auto
  qed
  show "AE w in M. \<bar>qt_expect I_XpZ Vp w\<bar> \<le> 1" unfolding qt_expect_def
  proof (rule spectrum_abs_1_weighted_sumr)
    show "I_XpZ \<in> fc_mats" using I_XpZ_carrier fc_mats_carrier dim_eq dim4 by simp
    show "hermitian I_XpZ" using I_XpZ_hermitian .
    show "lhv M Z_I I_XpZ rho_psim Vz Vp" using assms by simp
    show "{Re x |x. x \<in> spectrum I_XpZ} \<subseteq> {- 1, 1}" using I_XpZ_spectrum by simp
    show "{Re x |x. x \<in> spectrum I_XpZ} \<noteq> {}" using spectrum_ne I_XpZ_hermitian \<open>I_XpZ \<in> fc_mats\<close> 
      by auto
  qed
  show "AE w in M. \<bar>qt_expect I_ZmX Vm w\<bar> \<le> 1" unfolding qt_expect_def
  proof (rule spectrum_abs_1_weighted_sumr)
    show "I_ZmX \<in> fc_mats" using I_ZmX_carrier fc_mats_carrier dim_eq dim4 by simp
    show "hermitian I_ZmX" using I_ZmX_hermitian .
    show "lhv M Z_I I_ZmX rho_psim Vz Vm" using assms by simp
    show "{Re x |x. x \<in> spectrum I_ZmX} \<subseteq> {- 1, 1}" using I_ZmX_spectrum by simp
    show "{Re x |x. x \<in> spectrum I_ZmX} \<noteq> {}" using spectrum_ne I_ZmX_hermitian \<open>I_ZmX \<in> fc_mats\<close> 
      by auto
  qed
  show "prob_space M" using assms by simp
  show "integrable M (\<lambda>w. qt_expect X_I Vx w * qt_expect I_ZmX Vm w)" 
    using spectr_sum_integrable[of M] assms by simp
  show "integrable M (\<lambda>w. qt_expect Z_I Vz w * qt_expect I_ZmX Vm w)" 
    using spectr_sum_integrable[of M] assms by simp
  show "integrable M (\<lambda>w. qt_expect X_I Vx w * qt_expect I_XpZ Vp w)" 
    using spectr_sum_integrable[of M] assms by simp
  show "integrable M (\<lambda>w. qt_expect Z_I Vz w * qt_expect I_XpZ Vp w)" 
    using spectr_sum_integrable[of M] assms by simp
qed

lemma (in bin_cpx) quantum_value:
  assumes "lhv M X_I I_XpZ rho_psim Vx Vp"
  and "lhv M Z_I I_XpZ rho_psim Vz Vp"
  and "lhv M X_I I_ZmX rho_psim Vx Vm"
  and "lhv M Z_I I_ZmX rho_psim Vz Vm"
shows "\<bar>(LINT w|M. qt_expect X_I Vx w * qt_expect I_ZmX Vm w) + 
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_XpZ Vp w) + 
        (LINT w|M. qt_expect X_I Vx w * qt_expect I_XpZ Vp w) -
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_ZmX Vm w)\<bar>
  = 2* sqrt 2" 
proof -
  have "LINT w|M. qt_expect X_I Vx w * qt_expect I_ZmX Vm w = 1/sqrt 2"
    using X_I_ZmX_chsh[of M] assms unfolding qt_expect_def by simp
  moreover have b: "LINT w|M. qt_expect X_I Vx w * qt_expect I_XpZ Vp w = 1/sqrt 2"
    using X_I_XpZ_chsh[of M] assms unfolding qt_expect_def by simp
  moreover have c: "LINT w|M. qt_expect Z_I Vz w * qt_expect I_XpZ Vp w = 1/sqrt 2"
    using Z_I_XpZ_chsh[of M] assms unfolding qt_expect_def by simp
  moreover have "LINT w|M. qt_expect Z_I Vz w * qt_expect I_ZmX Vm w = -1/sqrt 2"
    using Z_I_ZmX_chsh[of M] assms unfolding qt_expect_def by simp
  ultimately have "(LINT w|M. qt_expect X_I Vx w * qt_expect I_ZmX Vm w) + 
        (LINT w|M. qt_expect X_I Vx w * qt_expect I_XpZ Vp w) + 
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_XpZ Vp w) -
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_ZmX Vm w) = 4/(sqrt 2)"  by simp
  also have "... = (4 * (sqrt 2))/(sqrt 2 * (sqrt 2))"
    by (metis mult_numeral_1_right real_divide_square_eq times_divide_eq_right)
  also have "... = (4 * (sqrt 2)) / 2" by simp
  also have "... = 2 * (sqrt 2)" by simp
  finally have "(LINT w|M. qt_expect X_I Vx w * qt_expect I_ZmX Vm w) + 
        (LINT w|M. qt_expect X_I Vx w * qt_expect I_XpZ Vp w) + 
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_XpZ Vp w) -
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_ZmX Vm w) = 2 * sqrt 2" .
  thus ?thesis by (simp add: b c)  
qed

lemma (in bin_cpx) no_lhv:
  assumes "lhv M X_I I_XpZ rho_psim Vx Vp"
  and "lhv M Z_I I_XpZ rho_psim Vz Vp"
  and "lhv M X_I I_ZmX rho_psim Vx Vm"
  and "lhv M Z_I I_ZmX rho_psim Vz Vm"
shows False
proof -
  have "prob_space M" using assms unfolding lhv_def by simp
  have "2 * sqrt 2 = \<bar>(LINT w|M. qt_expect X_I Vx w * qt_expect I_ZmX Vm w) + 
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_XpZ Vp w) + 
        (LINT w|M. qt_expect X_I Vx w * qt_expect I_XpZ Vp w) -
        (LINT w|M. qt_expect Z_I Vz w * qt_expect I_ZmX Vm w)\<bar>"
    using assms quantum_value[of M] by simp
  also have "... \<le> 2" using chsh_upper_bound[of M] assms \<open>prob_space M\<close> by simp
  finally have "2 * sqrt 2 \<le> 2" .
  thus False by simp
qed


end