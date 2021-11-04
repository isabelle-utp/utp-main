(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

section \<open>\<open>Complex_Inner_Product\<close> -- Complex Inner Product Spaces\<close>

theory Complex_Inner_Product
  imports 
    Complex_Vector_Spaces
    "HOL-Analysis.Infinite_Set_Sum" 

    Complex_Inner_Product0
begin

subsection \<open>Complex inner product spaces\<close>

bundle cinner_bracket_notation begin
notation cinner ("\<langle>_, _\<rangle>")
end
unbundle cinner_bracket_notation

bundle no_cinner_bracket_notation begin
no_notation cinner ("\<langle>_, _\<rangle>")
end

lemma cinner_real: "cinner x x \<in> \<real>"
  by (meson cinner_ge_zero reals_zero_comparable_iff)

lemmas cinner_commute' [simp] = cinner_commute[symmetric]

lemma (in complex_inner) cinner_eq_flip: \<open>(cinner x y = cinner z w) \<longleftrightarrow> (cinner y x = cinner w z)\<close>
  by (metis cinner_commute)

lemma Im_cinner_x_x[simp]: "Im \<langle>x , x\<rangle> = 0"
  using comp_Im_same[OF cinner_ge_zero] by simp


lemma of_complex_inner_1' [simp]:
  "cinner (1 :: 'a :: {complex_inner, complex_normed_algebra_1}) (of_complex x) = x"
  by (metis cinner_commute complex_cnj_cnj of_complex_inner_1)


class chilbert_space =  complex_inner + complete_space
begin
subclass cbanach by standard
end

instantiation complex :: "chilbert_space" begin
instance ..
end

subsection \<open>Misc facts\<close>

text \<open>This is a useful rule for establishing the equality of vectors\<close>
lemma cinner_extensionality:
  assumes \<open>\<And>\<gamma>. \<langle>\<gamma>, \<psi>\<rangle> = \<langle>\<gamma>, \<phi>\<rangle>\<close>
  shows \<open>\<psi> = \<phi>\<close>
  by (metis assms cinner_eq_zero_iff cinner_simps(3) right_minus_eq)

lemma polar_identity:
  includes notation_norm
  shows \<open>\<parallel>x + y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 + 2*Re \<langle>x, y\<rangle>\<close>
    \<comment> \<open>Shown in the proof of Corollary 1.5 in @{cite conway2013course}\<close>
proof -
  have \<open>\<langle>x , y\<rangle> + \<langle>y , x\<rangle> = \<langle>x , y\<rangle> + cnj \<langle>x , y\<rangle>\<close>
    by simp
  hence \<open>\<langle>x , y\<rangle> + \<langle>y , x\<rangle> = 2 * Re \<langle>x , y\<rangle> \<close>
    using complex_add_cnj by presburger
  have \<open>\<parallel>x + y\<parallel>^2 = \<langle>x+y, x+y\<rangle>\<close>
    by (simp add: cdot_square_norm) 
  hence \<open>\<parallel>x + y\<parallel>^2 = \<langle>x , x\<rangle> + \<langle>x , y\<rangle> + \<langle>y , x\<rangle> + \<langle>y , y\<rangle>\<close>
    by (simp add: cinner_add_left cinner_add_right)
  thus ?thesis using  \<open>\<langle>x , y\<rangle> + \<langle>y , x\<rangle> = 2 * Re \<langle>x , y\<rangle>\<close>
    by (smt (verit, ccfv_SIG) Re_complex_of_real plus_complex.simps(1) power2_norm_eq_cinner')
qed

lemma polar_identity_minus:
  includes notation_norm 
  shows \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2 * Re \<langle>x, y\<rangle>\<close>
proof-
  have \<open>\<parallel>x + (-y)\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>-y\<parallel>^2 + 2 * Re \<langle>x , (-y)\<rangle>\<close>
    using polar_identity by blast
  hence \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2*Re \<langle>x , y\<rangle>\<close>
    by simp
  thus ?thesis 
    by blast
qed

proposition parallelogram_law:
  includes notation_norm
  fixes x y :: "'a::complex_inner"
  shows \<open>\<parallel>x+y\<parallel>^2 + \<parallel>x-y\<parallel>^2 = 2*( \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 )\<close>
    \<comment> \<open>Shown in the proof of Theorem 2.3 in @{cite conway2013course}\<close> 
  by (simp add: polar_identity_minus polar_identity)


theorem pythagorean_theorem:
  includes notation_norm
  shows \<open>\<langle>x , y\<rangle> = 0 \<Longrightarrow> \<parallel> x + y \<parallel>^2 = \<parallel> x \<parallel>^2 + \<parallel> y \<parallel>^2\<close> 
    \<comment> \<open>Shown in the proof of Theorem 2.2 in @{cite conway2013course}\<close> 
  by (simp add: polar_identity)

lemma pythagorean_theorem_sum:
  assumes q1: "\<And>a a'. a \<in> t \<Longrightarrow> a' \<in> t \<Longrightarrow> a \<noteq> a' \<Longrightarrow> \<langle>f a, f a'\<rangle> = 0"
    and q2: "finite t"
  shows "(norm  (\<Sum>a\<in>t. f a))^2 = (\<Sum>a\<in>t.(norm (f a))^2)"
proof (insert q1, use q2 in induction)
  case empty
  show ?case
    by auto 
next
  case (insert x F)
  have r1: "\<langle>f x, f a\<rangle> = 0"
    if "a \<in> F"
    for a
    using that insert.hyps(2) insert.prems by auto 
  have "sum f F = (\<Sum>a\<in>F. f a)"
    by simp
  hence s4: "\<langle>f x, sum f F\<rangle> = \<langle>f x, (\<Sum>a\<in>F. f a)\<rangle>"
    by simp
  also have s3: "\<dots> = (\<Sum>a\<in>F. \<langle>f x, f a\<rangle>)"
    using cinner_sum_right by auto
  also have s2: "\<dots> = (\<Sum>a\<in>F. 0)"
    using r1
    by simp
  also have s1: "\<dots> = 0"
    by simp
  finally have xF_ortho: "\<langle>f x, sum f F\<rangle> = 0"
    using s2 s3 by auto       
  have "(norm (sum f (insert x F)))\<^sup>2 = (norm (f x + sum f F))\<^sup>2"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "\<dots> = (norm (f x))\<^sup>2 + (norm (sum f F))\<^sup>2"
    using xF_ortho by (rule pythagorean_theorem)
  also have "\<dots> = (norm (f x))\<^sup>2 + (\<Sum>a\<in>F.(norm (f a))^2)"
    apply (subst insert.IH) using insert.prems by auto
  also have "\<dots> = (\<Sum>a\<in>insert x F.(norm (f a))^2)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case
    by simp
qed


lemma Cauchy_cinner_Cauchy:
  fixes x y :: \<open>nat \<Rightarrow> 'a::complex_inner\<close>
  assumes a1: \<open>Cauchy x\<close> and a2: \<open>Cauchy y\<close>
  shows \<open>Cauchy (\<lambda> n. \<langle> x n, y n \<rangle>)\<close>
proof-
  have \<open>bounded (range x)\<close>
    using a1
    by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
  hence b1: \<open>\<exists>M. \<forall>n. norm (x n) < M\<close>
    by (meson bounded_pos_less rangeI)  
  have \<open>bounded (range y)\<close>
    using a2
    by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
  hence b2: \<open>\<exists> M. \<forall> n. norm (y n) < M\<close>
    by (meson bounded_pos_less rangeI)  
  have \<open>\<exists>M. \<forall>n. norm (x n) < M \<and> norm (y n) < M\<close>
    using b1 b2
    by (metis dual_order.strict_trans linorder_neqE_linordered_idom)  
  then obtain M where M1: \<open>\<And>n. norm (x n) < M\<close> and M2: \<open>\<And>n. norm (y n) < M\<close>
    by blast
  have M3: \<open>M > 0\<close>
    by (smt M2 norm_not_less_zero)     
  have \<open>\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. norm ( (\<lambda> i. \<langle> x i, y i \<rangle>) n -  (\<lambda> i. \<langle> x i, y i \<rangle>) m ) < e\<close>
    if "e > 0" for e
  proof-
    have \<open>e / (2*M) > 0\<close>
      using M3
      by (simp add: that)
    hence \<open>\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. norm (x n - x m) < e / (2*M)\<close>
      using a1
      by (simp add: Cauchy_iff) 
    then obtain N1 where N1_def: \<open>\<And>n m. n\<ge>N1 \<Longrightarrow> m\<ge>N1 \<Longrightarrow> norm (x n - x m) < e / (2*M)\<close>
      by blast
    have x1: \<open>\<exists>N. \<forall> n\<ge>N. \<forall> m\<ge>N. norm (y n - y m) < e / (2*M)\<close>
      using a2 \<open>e / (2*M) > 0\<close>
      by (simp add: Cauchy_iff) 
    obtain N2 where N2_def: \<open>\<And>n m.  n\<ge>N2 \<Longrightarrow> m\<ge>N2 \<Longrightarrow> norm (y n - y m) < e / (2*M)\<close>
      using x1
      by blast
    define N where N_def: \<open>N = N1 + N2\<close>
    hence \<open>N \<ge> N1\<close>
      by auto
    have \<open>N \<ge> N2\<close>
      using N_def
      by auto
    have \<open>norm ( \<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> ) < e\<close>
      if \<open>n \<ge> N\<close> and \<open>m \<ge> N\<close>
      for n m
    proof -
      have \<open>\<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> = (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) + (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>)\<close>
        by simp
      hence y1: \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle>) \<le> norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>)
           + norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>)\<close>
        by (metis norm_triangle_ineq)

      have \<open>\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle> = \<langle> x n - x m, y n \<rangle>\<close>
        by (simp add: cinner_diff_left)
      hence \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) = norm \<langle> x n - x m, y n \<rangle>\<close>
        by simp
      moreover have \<open>norm \<langle> x n - x m, y n \<rangle> \<le> norm (x n - x m) * norm (y n)\<close>
        using complex_inner_class.Cauchy_Schwarz_ineq2 by blast
      moreover have \<open>norm (y n) < M\<close>
        by (simp add: M2)        
      moreover have \<open>norm (x n - x m) < e/(2*M)\<close>
        using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N1 \<le> N\<close> N1_def by auto
      ultimately have \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < (e/(2*M)) * M\<close>
        by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
      moreover have \<open> (e/(2*M)) * M = e/2\<close>
        using \<open>M > 0\<close> by simp
      ultimately have  \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < e/2\<close>
        by simp      
      hence y2: \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < e/2\<close>
        by blast        
      have \<open>\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle> = \<langle> x m, y n - y m \<rangle>\<close>
        by (simp add: cinner_diff_right)
      hence \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) = norm \<langle> x m, y n - y m \<rangle>\<close>
        by simp
      moreover have \<open>norm \<langle> x m, y n - y m \<rangle> \<le> norm (x m) * norm (y n - y m)\<close>
        by (meson complex_inner_class.Cauchy_Schwarz_ineq2)
      moreover have \<open>norm (x m) < M\<close>
        by (simp add: M1)
      moreover have \<open>norm (y n - y m) < e/(2*M)\<close>
        using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N2 \<le> N\<close> N2_def by auto 
      ultimately have \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < M * (e/(2*M))\<close>
        by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
      moreover have \<open>M * (e/(2*M)) = e/2\<close>
        using \<open>M > 0\<close> by simp
      ultimately have  \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < e/2\<close>
        by simp
      hence y3: \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < e/2\<close>
        by blast
      show \<open>norm ( \<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> ) < e\<close>
        using y1 y2 y3 by simp
    qed
    thus ?thesis by blast
  qed
  thus ?thesis
    by (simp add: CauchyI)
qed


lemma cinner_sup_norm: \<open>norm \<psi> = (SUP \<phi>. cmod (cinner \<phi> \<psi>) / norm \<phi>)\<close>
proof (rule sym, rule cSup_eq_maximum)
  have \<open>norm \<psi> = cmod (cinner \<psi> \<psi>) / norm \<psi>\<close>
    by (metis norm_eq_sqrt_cinner norm_ge_zero real_div_sqrt)
  then show \<open>norm \<psi> \<in> range (\<lambda>\<phi>. cmod (cinner \<phi> \<psi>) / norm \<phi>)\<close>
    by blast
next
  fix n assume \<open>n \<in> range (\<lambda>\<phi>. cmod (cinner \<phi> \<psi>) / norm \<phi>)\<close>
  then obtain \<phi> where n\<phi>: \<open>n = cmod (cinner \<phi> \<psi>) / norm \<phi>\<close>
    by auto
  show \<open>n \<le> norm \<psi>\<close>
    unfolding n\<phi>
    by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2 divide_le_eq ordered_field_class.sign_simps(33))
qed

lemma cinner_sup_onorm: 
  fixes A :: \<open>'a::{real_normed_vector,not_singleton} \<Rightarrow> 'b::complex_inner\<close>
  assumes \<open>bounded_linear A\<close>
  shows \<open>onorm A = (SUP (\<psi>,\<phi>). cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
proof (unfold onorm_def, rule cSup_eq_cSup)
  show \<open>bdd_above (range (\<lambda>x. norm (A x) / norm x))\<close>
    by (meson assms bdd_aboveI2 le_onorm)
next
  fix a
  assume \<open>a \<in> range (\<lambda>\<phi>. norm (A \<phi>) / norm \<phi>)\<close>
  then obtain \<phi> where \<open>a = norm (A \<phi>) / norm \<phi>\<close>
    by auto
  then have \<open>a \<le> cmod (cinner (A \<phi>) (A \<phi>)) / (norm (A \<phi>) * norm \<phi>)\<close>
    apply auto
    by (smt (verit) divide_divide_eq_left norm_eq_sqrt_cinner norm_imp_pos_and_ge real_div_sqrt)
  then show \<open>\<exists>b\<in>range (\<lambda>(\<psi>, \<phi>). cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>)). a \<le> b\<close>
    by force
next
  fix b
  assume \<open>b \<in> range (\<lambda>(\<psi>, \<phi>). cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
  then obtain \<psi> \<phi> where b: \<open>b = cmod (cinner \<psi> (A \<phi>)) / (norm \<psi> * norm \<phi>)\<close>
    by auto
  then have \<open>b \<le> norm (A \<phi>) / norm \<phi>\<close>
    apply auto
    by (smt (verit, ccfv_threshold) complex_inner_class.Cauchy_Schwarz_ineq2 division_ring_divide_zero linordered_field_class.divide_right_mono mult_cancel_left1 nonzero_mult_divide_mult_cancel_left2 norm_imp_pos_and_ge ordered_field_class.sign_simps(33) zero_le_divide_iff)
  then show \<open>\<exists>a\<in>range (\<lambda>x. norm (A x) / norm x). b \<le> a\<close>
    by auto
qed


subsection \<open>Orthogonality\<close>


definition "orthogonal_complement S = {x| x. \<forall>y\<in>S. cinner x y = 0}" 

lemma orthogonal_complement_orthoI:
  \<open>x \<in> orthogonal_complement M \<Longrightarrow> y \<in> M \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
  unfolding orthogonal_complement_def by auto

lemma orthogonal_complement_orthoI':
  \<open>x \<in> M \<Longrightarrow> y \<in> orthogonal_complement M \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
  by (metis cinner_commute' complex_cnj_zero orthogonal_complement_orthoI)

lemma orthogonal_complementI:
  \<open>(\<And>x. x \<in> M \<Longrightarrow> \<langle> y, x \<rangle> = 0) \<Longrightarrow> y \<in> orthogonal_complement M\<close>
  unfolding orthogonal_complement_def
  by simp

abbreviation is_orthogonal::\<open>'a::complex_inner \<Rightarrow> 'a \<Rightarrow> bool\<close>  where
  \<open>is_orthogonal x y \<equiv> \<langle> x, y \<rangle> = 0\<close>

bundle orthogonal_notation begin
notation is_orthogonal (infixl "\<bottom>" 69)
end

bundle no_orthogonal_notation begin
no_notation is_orthogonal (infixl "\<bottom>" 69)
end


lemma is_orthogonal_sym: "is_orthogonal \<psi> \<phi> = is_orthogonal \<phi> \<psi>"
  by (metis cinner_commute' complex_cnj_zero)

lemma orthogonal_complement_closed_subspace[simp]: 
  "closed_csubspace (orthogonal_complement A)"
  for A :: \<open>('a::complex_inner) set\<close>
proof (intro closed_csubspace.intro complex_vector.subspaceI)
  fix x y and c
  show \<open>0 \<in> orthogonal_complement A\<close>
    by (rule orthogonal_complementI, simp)
  show \<open>x + y \<in> orthogonal_complement A\<close>
    if \<open>x \<in> orthogonal_complement A\<close> and \<open>y \<in> orthogonal_complement A\<close>
    using that by (auto intro!: orthogonal_complementI dest!: orthogonal_complement_orthoI
        simp add: cinner_add_left)
  show \<open>c *\<^sub>C x \<in> orthogonal_complement A\<close> if \<open>x \<in> orthogonal_complement A\<close> 
    using that by (auto intro!: orthogonal_complementI dest!: orthogonal_complement_orthoI)

  show "closed (orthogonal_complement A)"
  proof (auto simp add: closed_sequential_limits, rename_tac an a)
    fix an a
    assume ortho: \<open>\<forall>n::nat. an n \<in> orthogonal_complement A\<close>
    assume lim: \<open>an \<longlonglongrightarrow> a\<close>

    have \<open>\<forall> y \<in> A. \<forall> n. \<langle> y , an n \<rangle> = 0\<close>
      using orthogonal_complement_orthoI'
      by (simp add: orthogonal_complement_orthoI' ortho)
    moreover have \<open>isCont (\<lambda> x. \<langle> y , x \<rangle>) a\<close> for y
      using bounded_clinear_cinner_right clinear_continuous_at
      by (simp add: clinear_continuous_at bounded_clinear_cinner_right)
    ultimately have \<open>(\<lambda> n. (\<lambda> v. \<langle> y , v \<rangle>) (an n)) \<longlonglongrightarrow> (\<lambda> v. \<langle> y , v \<rangle>) a\<close> for y
      using isCont_tendsto_compose
      by (simp add: isCont_tendsto_compose lim)
    hence  \<open>\<forall> y\<in>A. (\<lambda> n. \<langle> y , an n \<rangle>  ) \<longlonglongrightarrow>  \<langle> y , a \<rangle>\<close>
      by simp
    hence  \<open>\<forall> y\<in>A. (\<lambda> n. 0  ) \<longlonglongrightarrow>  \<langle> y , a \<rangle>\<close> 
      using \<open>\<forall> y \<in> A. \<forall> n. \<langle> y , an n \<rangle> = 0\<close> 
      by fastforce
    hence  \<open>\<forall> y \<in> A. \<langle> y , a \<rangle> = 0\<close> 
      using limI by fastforce
    then show \<open>a \<in> orthogonal_complement A\<close>
      by (simp add: orthogonal_complementI is_orthogonal_sym)
  qed
qed

lemma orthogonal_complement_zero_intersection:
  assumes "0\<in>M"
  shows \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
proof -
  have "x=0" if "x\<in>M" and "x\<in>orthogonal_complement M" for x
  proof -
    from that have "\<langle> x, x \<rangle> = 0"
      unfolding orthogonal_complement_def by auto
    thus "x=0"
      by auto
  qed
  with assms show ?thesis
    unfolding orthogonal_complement_def by auto
qed

lemma is_orthogonal_closure_cspan:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> is_orthogonal x y"
  assumes \<open>x \<in> closure (cspan X)\<close> \<open>y \<in> closure (cspan Y)\<close>
  shows "is_orthogonal x y"
proof -
  have *: \<open>cinner x y = 0\<close> if \<open>y \<in> Y\<close> for y
    using bounded_antilinear_cinner_left apply (rule bounded_antilinear_eq_on[where G=X])
    using assms that by auto
  show \<open>cinner x y = 0\<close>
    using bounded_clinear_cinner_right apply (rule bounded_clinear_eq_on[where G=Y])
    using * assms by auto
qed


instantiation ccsubspace :: (complex_inner) "uminus"
begin
lift_definition uminus_ccsubspace::\<open>'a ccsubspace  \<Rightarrow> 'a ccsubspace\<close>
  is \<open>orthogonal_complement\<close>
  by simp

instance ..
end


instantiation ccsubspace :: (complex_inner) minus begin
lift_definition minus_ccsubspace :: "'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace"
  is "\<lambda>A B. A \<inter> (orthogonal_complement B)"
  by simp
instance..
end


text \<open>Orthogonal set\<close>
definition is_ortho_set :: "'a::complex_inner set \<Rightarrow> bool" where
  \<open>is_ortho_set S = ((\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> \<langle>x, y\<rangle> = 0) \<and> 0 \<notin> S)\<close>

lemma is_ortho_set_empty[simp]: "is_ortho_set {}"
  unfolding is_ortho_set_def by auto

lemma is_ortho_set_antimono: \<open>A \<subseteq> B \<Longrightarrow> is_ortho_set B \<Longrightarrow> is_ortho_set A\<close>
  unfolding is_ortho_set_def by auto

lemma orthogonal_complement_of_closure:
  fixes A ::"('a::complex_inner) set"
  shows "orthogonal_complement A = orthogonal_complement (closure A)"
proof-
  have s1: \<open>\<langle> y, x \<rangle> = 0\<close> 
    if a1: "x \<in> (orthogonal_complement A)"
      and a2: \<open>y \<in> closure A\<close>  
    for x y
  proof-
    have \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>
      by (simp add: a1 orthogonal_complement_orthoI')
    then obtain yy where \<open>\<forall> n. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
      using a2 closure_sequential by blast
    have \<open>isCont (\<lambda> t. \<langle> t , x \<rangle>) y\<close>
      by simp
    hence \<open>(\<lambda> n. \<langle> yy n , x \<rangle>) \<longlonglongrightarrow>  \<langle> y , x \<rangle>\<close>
      using \<open>yy \<longlonglongrightarrow> y\<close> isCont_tendsto_compose
      by fastforce
    hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow>  \<langle> y , x \<rangle>\<close>
      using \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>  \<open>\<forall> n. yy n \<in> A\<close> by simp
    thus ?thesis 
      using limI by force
  qed
  hence "x \<in> orthogonal_complement (closure A)"
    if a1: "x \<in> (orthogonal_complement A)"
    for x
    using that
    by (meson orthogonal_complementI is_orthogonal_sym)
  moreover have \<open>x \<in> (orthogonal_complement A)\<close> 
    if "x \<in> (orthogonal_complement (closure A))"
    for x
    using that
    by (meson closure_subset orthogonal_complement_orthoI orthogonal_complementI subset_eq)
  ultimately show ?thesis by blast
qed


lemma is_orthogonal_closure: 
  assumes \<open>\<And>s. s \<in> S \<Longrightarrow> is_orthogonal a  s\<close>
  assumes \<open>x \<in> closure S\<close> 
  shows \<open>is_orthogonal a x\<close>
  by (metis assms(1) assms(2) orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_orthoI)


lemma is_orthogonal_cspan:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> is_orthogonal a s" and a3: "x \<in> cspan S"
  shows "\<langle>a, x\<rangle> = 0"
proof-
  have "\<exists>t r. finite t \<and> t \<subseteq> S \<and> (\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    using complex_vector.span_explicit
    by (smt a3 mem_Collect_eq)
  then obtain t r where b1: "finite t" and b2: "t \<subseteq> S" and b3: "(\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    by blast
  have x1: "\<langle>a, i\<rangle> = 0"
    if "i\<in>t" for i
    using b2 a1 that by blast
  have  "\<langle>a, x\<rangle> = \<langle>a, (\<Sum>i\<in>t. r i *\<^sub>C i)\<rangle>"
    by (simp add: b3) 
  also have  "\<dots> = (\<Sum>i\<in>t. r i *\<^sub>C \<langle>a, i\<rangle>)"
    by (simp add: cinner_sum_right)
  also have  "\<dots> = 0"
    using x1 by simp
  finally show ?thesis.
qed

lemma ccspan_leq_ortho_ccspan:
  assumes "\<And>s t. s\<in>S \<Longrightarrow> t\<in>T \<Longrightarrow> is_orthogonal s t"
  shows "ccspan S \<le> - (ccspan T)"
  using assms apply transfer
  by (smt (verit, ccfv_threshold) is_orthogonal_closure is_orthogonal_cspan is_orthogonal_sym orthogonal_complementI subsetI) 

lemma double_orthogonal_complement_increasing[simp]:
  shows "M \<subseteq> orthogonal_complement (orthogonal_complement M)"
proof (rule subsetI)
  fix x assume s1: "x \<in> M"
  have \<open>\<forall> y \<in> (orthogonal_complement M). \<langle> x, y \<rangle> = 0\<close>
    using s1 orthogonal_complement_orthoI' by auto
  hence \<open>x \<in> orthogonal_complement (orthogonal_complement M)\<close>
    by (simp add: orthogonal_complement_def)
  then show "x \<in> orthogonal_complement (orthogonal_complement M)"
    by blast
qed


lemma orthonormal_basis_of_cspan:
  fixes S::"'a::complex_inner set"
  assumes "finite S"
  shows "\<exists>A. is_ortho_set A \<and> (\<forall>x\<in>A. norm x = 1) \<and> cspan A = cspan S \<and> finite A"
proof (use assms in induction)
  case empty
  show ?case
    apply (rule exI[of _ "{}"])
    by auto
next
  case (insert s S)
  from insert.IH
  obtain A where orthoA: "is_ortho_set A" and normA: "\<And>x. x\<in>A \<Longrightarrow> norm x = 1" and spanA: "cspan A = cspan S" and finiteA: "finite A"
    by auto
  show ?case
  proof (cases \<open>s \<in> cspan S\<close>)
    case True
    then have \<open>cspan (insert s S) = cspan S\<close>
      by (simp add: complex_vector.span_redundant)
    with orthoA normA spanA finiteA
    show ?thesis
      by auto
  next
    case False
    obtain a where a_ortho: \<open>\<And>x. x\<in>A \<Longrightarrow> is_orthogonal x a\<close> and sa_span: \<open>s - a \<in> cspan A\<close>
    proof (atomize_elim, use \<open>finite A\<close> \<open>is_ortho_set A\<close> in induction)
      case empty
      then show ?case
        by auto
    next
      case (insert x A)
      then obtain a where orthoA: \<open>\<And>x. x \<in> A \<Longrightarrow> is_orthogonal x a\<close> and sa: \<open>s - a \<in> cspan A\<close>
        by (meson is_ortho_set_antimono subset_insertI)
      define a' where \<open>a' = a - cinner x a *\<^sub>C inverse (cinner x x) *\<^sub>C x\<close>
      have \<open>is_orthogonal x a'\<close>
        unfolding a'_def cinner_diff_right cinner_scaleC_right
        apply (cases \<open>cinner x x = 0\<close>)
        by auto
      have orthoA: \<open>is_orthogonal y a'\<close> if \<open>y \<in> A\<close> for y
        unfolding a'_def cinner_diff_right cinner_scaleC_right
        apply auto by (metis insert.prems insertCI is_ortho_set_def mult_not_zero orthoA that)
      have \<open>s - a' \<in> cspan (insert x A)\<close>
        unfolding a'_def apply auto
        by (metis (no_types, lifting) complex_vector.span_breakdown_eq diff_add_cancel diff_diff_add sa)
      with \<open>is_orthogonal x a'\<close> orthoA
      show ?case
        apply (rule_tac exI[of _ a'])
        by auto
    qed

    from False sa_span
    have \<open>a \<noteq> 0\<close>
      unfolding spanA by auto
    define a' where \<open>a' = inverse (norm a) *\<^sub>C a\<close>
    with \<open>a \<noteq> 0\<close> have \<open>norm a' = 1\<close>
      by (simp add: norm_inverse)
    have a: \<open>a = norm a *\<^sub>C a'\<close>
      by (simp add: \<open>a \<noteq> 0\<close> a'_def)

    from sa_span spanA
    have a'_span: \<open>a' \<in> cspan (insert s S)\<close>
      unfolding a'_def
      by (metis complex_vector.eq_span_insert_eq complex_vector.span_scale complex_vector.span_superset in_mono insertI1)
    from sa_span
    have s_span: \<open>s \<in> cspan (insert a' A)\<close>
      apply (subst (asm) a)
      using complex_vector.span_breakdown_eq by blast

    from \<open>a \<noteq> 0\<close> a_ortho orthoA
    have ortho: "is_ortho_set (insert a' A)"
      unfolding is_ortho_set_def a'_def
      apply auto
      by (meson is_orthogonal_sym)

    have span: \<open>cspan (insert a' A) = cspan (insert s S)\<close>
      using a'_span s_span spanA apply auto
       apply (metis (full_types) complex_vector.span_breakdown_eq complex_vector.span_redundant insert_commute s_span)
      by (metis (full_types) complex_vector.span_breakdown_eq complex_vector.span_redundant insert_commute s_span)

    show ?thesis
      apply (rule exI[of _ \<open>insert a' A\<close>])
      by (simp add: ortho \<open>norm a' = 1\<close> normA finiteA span)
  qed
qed

lemma is_ortho_set_cindependent:
  assumes "is_ortho_set A" 
  shows "cindependent A"
proof -
  have "u v = 0"
    if b1: "finite t" and b2: "t \<subseteq> A" and b3: "(\<Sum>v\<in>t. u v *\<^sub>C v) = 0" and b4: "v \<in> t"
    for t u v
  proof -
    have "\<langle>v, v'\<rangle> = 0" if c1: "v'\<in>t-{v}" for v'
      by (metis DiffE assms b2 b4 insertI1 is_ortho_set_antimono is_ortho_set_def that)
    hence sum0: "(\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>) = 0"
      by simp
    have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> = (\<Sum>v'\<in>t. u v' * \<langle>v, v'\<rangle>)"
      using b1
      by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong) 
    also have "\<dots> = u v * \<langle>v, v\<rangle> + (\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>)"
      by (meson b1 b4 sum.remove)
    also have "\<dots> = u v * \<langle>v, v\<rangle>"
      using sum0 by simp
    finally have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> =  u v * \<langle>v, v\<rangle>"
      by blast
    hence "u v * \<langle>v, v\<rangle> = 0" using b3 by simp
    moreover have "\<langle>v, v\<rangle> \<noteq> 0"
      using assms is_ortho_set_def b2 b4 by auto    
    ultimately show "u v = 0" by simp
  qed
  thus ?thesis using complex_vector.independent_explicit_module
    by (smt cdependent_raw_def)
qed


lemma onb_expansion_finite:
  includes notation_norm
  fixes T::\<open>'a::{complex_inner,cfinite_dim} set\<close>
  assumes a1: \<open>cspan T = UNIV\<close> and a3: \<open>is_ortho_set T\<close>
    and a4: \<open>\<And>t. t\<in>T \<Longrightarrow> \<parallel>t\<parallel> = 1\<close>
  shows \<open>x = (\<Sum>t\<in>T. \<langle> t, x \<rangle> *\<^sub>C t)\<close>
proof -
  have \<open>finite T\<close>
    apply (rule cindependent_cfinite_dim_finite)
    by (simp add: a3 is_ortho_set_cindependent)
  have \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
    by (simp add: a1)
  have \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close>
    apply auto
     apply (rule_tac x=\<open>\<lambda>a. if a \<in> t then r a else 0\<close> in exI)
     apply (simp add: \<open>finite T\<close> sum.mono_neutral_cong_right)
    using \<open>finite T\<close> by blast

  have f1: "\<forall>A. {a. \<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A} = cspan A"
    by (simp add: complex_vector.span_explicit)      
  have f2: "\<forall>a. (\<exists>f. a = (\<Sum>a\<in>T. f a *\<^sub>C a)) \<or> (\<forall>A. (\<forall>f. a \<noteq> (\<Sum>a\<in>A. f a *\<^sub>C a)) \<or> infinite A \<or> \<not> A \<subseteq> T)"
    using \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close> by auto
  have f3: "\<forall>A a. (\<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A) \<or> a \<notin> cspan A"
    using f1 by blast
  have "cspan T = UNIV"
    by (metis (full_types, lifting)  \<open>complex_vector.span T = UNIV\<close>)
  hence \<open>\<exists> r. x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    using f3 f2 by blast
  then obtain r where \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by blast

  have \<open>r a = \<langle>a, x\<rangle>\<close> if \<open>a \<in> T\<close> for a
  proof-
    have \<open>norm a = 1\<close>
      using a4
      by (simp add: \<open>a \<in> T\<close>)
    moreover have \<open>norm a = sqrt (norm \<langle>a, a\<rangle>)\<close>
      using norm_eq_sqrt_cinner by auto        
    ultimately have \<open>sqrt (norm \<langle>a, a\<rangle>) = 1\<close>
      by simp
    hence \<open>norm \<langle>a, a\<rangle> = 1\<close>
      using real_sqrt_eq_1_iff by blast
    moreover have \<open>\<langle>a, a\<rangle> \<in> \<real>\<close>
      by (simp add: cinner_real)        
    moreover have \<open>\<langle>a, a\<rangle> \<ge> 0\<close>
      using cinner_ge_zero by blast
    ultimately have w1: \<open>\<langle>a, a\<rangle> = 1\<close>
      by (metis \<open>0 \<le> \<langle>a, a\<rangle>\<close> \<open>cmod \<langle>a, a\<rangle> = 1\<close> complex_of_real_cmod of_real_1)

    have \<open>r t * \<langle>a, t\<rangle> = 0\<close> if \<open>t \<in> T-{a}\<close> for t
      by (metis DiffD1 DiffD2 \<open>a \<in> T\<close> a3 is_ortho_set_def mult_eq_0_iff singletonI that)
    hence s1: \<open>(\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>) = 0\<close>
      by (simp add: \<open>\<And>t. t \<in> T - {a} \<Longrightarrow> r t * \<langle>a, t\<rangle> = 0\<close>) 
    have \<open>\<langle>a, x\<rangle> = \<langle>a, (\<Sum> t\<in>T. r t *\<^sub>C t)\<rangle>\<close>
      using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum> t\<in>T. \<langle>a, r t *\<^sub>C t\<rangle>)\<close>
      using cinner_sum_right by blast
    also have \<open>\<dots> = (\<Sum> t\<in>T. r t * \<langle>a, t\<rangle>)\<close>
      by simp    
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle> + (\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>)\<close>
      using \<open>a \<in> T\<close>
      by (meson \<open>finite T\<close> sum.remove)
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle>\<close>
      using s1
      by simp
    also have \<open>\<dots> = r a\<close>
      by (simp add: w1)
    finally show ?thesis by auto
  qed
  thus ?thesis 
    using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by fastforce 
qed

subsection \<open>Projections\<close>

lemma smallest_norm_exists:
  \<comment> \<open>Theorem 2.5 in @{cite conway2013course} (inside the proof)\<close>
  includes notation_norm
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes q1: \<open>convex M\<close> and q2: \<open>closed M\<close> and q3: \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close>
proof-
  define d where \<open>d = Inf { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>    
  have w4: \<open>{ \<parallel>x\<parallel>^2 | x. x \<in> M } \<noteq> {}\<close>
    by (simp add: assms(3))
  have \<open>\<forall> x. \<parallel>x\<parallel>^2 \<ge> 0\<close>
    by simp
  hence bdd_below1: \<open>bdd_below { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>
    by fastforce    
  have \<open>d \<le> \<parallel>x\<parallel>^2\<close> 
    if a1: "x \<in> M"
    for x
  proof-
    have "\<forall>v. (\<exists>w. Re (\<langle>v , v\<rangle> ) = \<parallel>w\<parallel>\<^sup>2 \<and> w \<in> M) \<or> v \<notin> M"
      by (metis (no_types) power2_norm_eq_cinner')
    hence "Re (\<langle>x , x\<rangle> ) \<in> {\<parallel>v\<parallel>\<^sup>2 |v. v \<in> M}"
      using a1 by blast
    thus ?thesis
      unfolding d_def
      by (metis (lifting) bdd_below1 cInf_lower power2_norm_eq_cinner')
  qed

  have \<open>\<forall> \<epsilon> > 0. \<exists> t \<in> { \<parallel>x\<parallel>^2 | x. x \<in> M }.  t < d + \<epsilon>\<close>
    unfolding d_def
    using w4  bdd_below1
    by (meson cInf_lessD less_add_same_cancel1)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
    by auto    
  hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
    by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
  hence w1: \<open>\<forall> n::nat. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + 1/(n+1)\<close> by auto

  then obtain r::\<open>nat \<Rightarrow> 'a\<close> where w2: \<open>\<forall> n. r n \<in> M \<and>  \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
    by metis
  have w3: \<open>\<forall> n. r n \<in> M\<close> 
    by (simp add: w2)
  have \<open>\<forall> n. \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
    by (simp add: w2)    
  have w5: \<open>\<parallel> (r n) - (r m) \<parallel>^2 < 2*(1/(n+1) + 1/(m+1))\<close> 
    for m n 
  proof-
    have w6: \<open>\<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
      by (metis w2  of_nat_1 of_nat_add)
    have \<open> \<parallel> r m \<parallel>^2 < d + 1/(m+1)\<close>
      by (metis w2 of_nat_1 of_nat_add)
    have \<open>(r n) \<in> M\<close>
      by (simp add: \<open>\<forall>n. r n \<in> M\<close>) 
    moreover have \<open>(r m) \<in> M\<close> 
      by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
    ultimately have \<open>(1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<in> M\<close>
      using \<open>convex M\<close> 
      by (simp add: convexD)
    hence \<open>\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2 \<ge> d\<close>
      by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
    have \<open>\<parallel> (1/2) *\<^sub>R (r n) - (1/2) *\<^sub>R (r m) \<parallel>^2
              = (1/2)*( \<parallel> r n \<parallel>^2 + \<parallel> r m \<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close> 
      by (smt (z3) div_by_1 field_sum_of_halves nonzero_mult_div_cancel_left parallelogram_law polar_identity power2_norm_eq_cinner' scaleR_collapse times_divide_eq_left)
    also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + \<parallel> r m \<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close>
      using \<open>\<parallel>r n\<parallel>\<^sup>2 < d + 1 / real (n + 1)\<close> by auto
    also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close>
      using \<open>\<parallel>r m\<parallel>\<^sup>2 < d + 1 / real (m + 1)\<close> by auto
    also have  \<open>...  
              \<le> (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - d\<close>
      by (simp add: \<open>d \<le> \<parallel>(1 / 2) *\<^sub>R r n + (1 / 2) *\<^sub>R r m\<parallel>\<^sup>2\<close>)
    also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) + 2*d ) - d\<close>
      by simp
    also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) ) + (1/2)*(2*d) - d\<close>
      by (simp add: distrib_left)
    also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) ) + d - d\<close>
      by simp
    also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) )\<close>
      by simp
    finally have \<open> \<parallel>(1 / 2) *\<^sub>R r n - (1 / 2) *\<^sub>R r m\<parallel>\<^sup>2 < 1 / 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by blast
    hence \<open> \<parallel>(1 / 2) *\<^sub>R (r n - r m) \<parallel>\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by (simp add: real_vector.scale_right_diff_distrib)          
    hence \<open> ((1 / 2)*\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by simp
    hence \<open> (1 / 2)^2*(\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by (metis power_mult_distrib)
    hence \<open> (1 / 4) *(\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by (simp add: power_divide)
    hence \<open> \<parallel> (r n - r m) \<parallel>\<^sup>2 < 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
      by simp
    thus ?thesis 
      by (metis of_nat_1 of_nat_add)
  qed
  hence "\<exists> N. \<forall> n m. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2"
    if "\<epsilon> > 0" 
    for \<epsilon>
  proof-
    obtain N::nat where \<open>1/(N + 1) < \<epsilon>^2/4\<close>
      using LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1]
      by (metis Suc_eq_plus1 \<open>0 < \<epsilon>\<close> nat_approx_posE zero_less_divide_iff zero_less_numeral 
          zero_less_power )
    hence \<open>4/(N + 1) < \<epsilon>^2\<close>
      by simp
    have "2*(1/(n+1) + 1/(m+1)) < \<epsilon>^2"
      if f1: "n \<ge> N" and f2: "m \<ge> N" 
      for m n::nat
    proof-
      have \<open>1/(n+1) \<le> 1/(N+1)\<close> 
        by (simp add: f1 linordered_field_class.frac_le)
      moreover have \<open>1/(m+1) \<le> 1/(N+1)\<close> 
        by (simp add: f2 linordered_field_class.frac_le)
      ultimately have  \<open>2*(1/(n+1) + 1/(m+1)) \<le> 4/(N+1)\<close>
        by simp
      thus ?thesis using \<open>4/(N + 1) < \<epsilon>^2\<close> 
        by linarith
    qed
    hence "\<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2"
      if y1: "n \<ge> N" and y2: "m \<ge> N" 
      for m n::nat
      using that
      by (smt \<open>\<And>n m. \<parallel>r n - r m\<parallel>\<^sup>2 < 2 * (1 / (real n + 1) + 1 / (real m + 1))\<close> of_nat_1 of_nat_add)
    thus ?thesis 
      by blast
  qed
  hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2\<close>
    by blast
  hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel> < \<epsilon>\<close>
    by (meson less_eq_real_def power_less_imp_less_base)
  hence \<open>Cauchy r\<close>
    using CauchyI by fastforce
  then obtain k where \<open>r \<longlonglongrightarrow> k\<close>
    using  convergent_eq_Cauchy by auto
  have \<open>k \<in> M\<close> using \<open>closed M\<close>
    using \<open>\<forall>n. r n \<in> M\<close> \<open>r \<longlonglongrightarrow> k\<close> closed_sequentially by auto
  have  \<open>(\<lambda> n.  \<parallel> r n \<parallel>^2) \<longlonglongrightarrow>  \<parallel> k \<parallel>^2\<close>
    by (simp add: \<open>r \<longlonglongrightarrow> k\<close> tendsto_norm tendsto_power)
  moreover  have  \<open>(\<lambda> n.  \<parallel> r n \<parallel>^2) \<longlonglongrightarrow>  d\<close>
  proof-
    have \<open>\<bar>\<parallel> r n \<parallel>^2 - d\<bar> < 1/(n+1)\<close> for n :: nat
      using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close> \<open>\<forall>n. r n \<in> M \<and> \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close> of_nat_1 of_nat_add
      by smt
    moreover have \<open>(\<lambda>n. 1 / real (n + 1)) \<longlonglongrightarrow> 0\<close> 
      using  LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1] by blast        
    ultimately have \<open>(\<lambda> n. \<bar>\<parallel> r n \<parallel>^2 - d\<bar> ) \<longlonglongrightarrow> 0\<close> 
      by (simp add: LIMSEQ_norm_0)
    hence \<open>(\<lambda> n. \<parallel> r n \<parallel>^2 - d ) \<longlonglongrightarrow> 0\<close> 
      by (simp add: tendsto_rabs_zero_iff)
    moreover have \<open>(\<lambda> n. d ) \<longlonglongrightarrow> d\<close>
      by simp
    ultimately have \<open>(\<lambda> n. (\<parallel> r n \<parallel>^2 - d)+d ) \<longlonglongrightarrow> 0+d\<close> 
      using tendsto_add by fastforce
    thus ?thesis by simp
  qed
  ultimately have \<open>d = \<parallel> k \<parallel>^2\<close>
    using LIMSEQ_unique by auto
  hence \<open>t \<in> M \<Longrightarrow> \<parallel> k \<parallel>^2 \<le> \<parallel> t \<parallel>^2\<close> for t
    using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close> by auto
  hence q1: \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>^2) (\<lambda> t. t \<in> M) k\<close> 
    using \<open>k \<in> M\<close>
      is_arg_min_def \<open>d = \<parallel>k\<parallel>\<^sup>2\<close>
    by smt
  thus \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close> 
    by (smt is_arg_min_def norm_ge_zero power2_eq_square power2_le_imp_le)
qed


lemma smallest_norm_unique:
  \<comment> \<open>Theorem 2.5 in @{cite conway2013course} (inside the proof)\<close>
  includes notation_norm
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes q1: \<open>convex M\<close>
  assumes r: \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close>
  assumes s: \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>
  shows \<open>r = s\<close>
proof -
  have \<open>r \<in> M\<close> 
    using \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close>
    by (simp add: is_arg_min_def)
  moreover have \<open>s \<in> M\<close> 
    using \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>
    by (simp add: is_arg_min_def)
  ultimately have \<open>((1/2) *\<^sub>R r + (1/2) *\<^sub>R s) \<in> M\<close> using \<open>convex M\<close>
    by (simp add: convexD)
  hence \<open>\<parallel>r\<parallel> \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>\<close>
    by (metis is_arg_min_linorder r)
  hence u2: \<open>\<parallel>r\<parallel>^2 \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close>
    using norm_ge_zero power_mono by blast

  have \<open>\<parallel>r\<parallel> \<le> \<parallel>s\<parallel>\<close> 
    using r s is_arg_min_def
    by (metis is_arg_min_linorder)
  moreover have \<open>\<parallel>s\<parallel> \<le> \<parallel>r\<parallel>\<close>
    using r s is_arg_min_def
    by (metis is_arg_min_linorder)
  ultimately have u3: \<open>\<parallel>r\<parallel> = \<parallel>s\<parallel>\<close> by simp      

  have \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 \<le> 0\<close>
    using u2 u3 parallelogram_law
    by (smt (verit, ccfv_SIG) polar_identity_minus power2_norm_eq_cinner' scaleR_add_right scaleR_half_double)
  hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 = 0\<close>
    by simp
  hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel> = 0\<close>
    by auto
  hence \<open>(1/2) *\<^sub>R r - (1/2) *\<^sub>R s = 0\<close>
    using norm_eq_zero by blast
  thus ?thesis by simp
qed

theorem smallest_dist_exists:
  \<comment> \<open>Theorem 2.5 in @{cite conway2013course}\<close> 
  fixes M::\<open>'a::chilbert_space set\<close> and h 
  assumes a1: \<open>convex M\<close> and a2: \<open>closed M\<close> and a3: \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>k. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
proof-
  have *: "is_arg_min (\<lambda>x. dist x h) (\<lambda>x. x\<in>M) (k+h) \<longleftrightarrow> is_arg_min (\<lambda>x. norm x) (\<lambda>x. x\<in>(\<lambda>x. x-h) ` M) k" for k
    unfolding dist_norm is_arg_min_def apply auto using add_implies_diff by blast
  have \<open>\<exists>k. is_arg_min (\<lambda>x. dist x h) (\<lambda>x. x\<in>M) (k+h)\<close>
    apply (subst *)
    apply (rule smallest_norm_exists)
    using assms by (auto simp: closed_translation_subtract)
  then show \<open>\<exists>k. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    by metis
qed

theorem smallest_dist_unique:
  \<comment> \<open>Theorem 2.5 in @{cite conway2013course}\<close> 
  fixes M::\<open>'a::complex_inner set\<close> and h 
  assumes a1: \<open>convex M\<close>
  assumes \<open>is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) r\<close>
  assumes \<open>is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) s\<close>
  shows  \<open>r = s\<close>
proof-
  have *: "is_arg_min (\<lambda>x. dist x h) (\<lambda>x. x\<in>M) k \<longleftrightarrow> is_arg_min (\<lambda>x. norm x) (\<lambda>x. x\<in>(\<lambda>x. x-h) ` M) (k-h)" for k
    unfolding dist_norm is_arg_min_def by auto
  have \<open>r - h = s - h\<close>
    using _ assms(2,3)[unfolded *] apply (rule smallest_norm_unique)
    by (simp add: a1)
  thus \<open>r = s\<close>
    by auto
qed


\<comment> \<open>Theorem 2.6 in @{cite conway2013course}\<close>
theorem smallest_dist_is_ortho:
  fixes M::\<open>'a::complex_inner set\<close> and h k::'a 
  assumes b1: \<open>closed_csubspace M\<close>
  shows  \<open>(is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k) \<longleftrightarrow> 
          h - k \<in> (orthogonal_complement M) \<and> k \<in> M\<close>
proof-
  include notation_norm
  have  \<open>csubspace M\<close>
    using \<open>closed_csubspace M\<close> unfolding closed_csubspace_def by blast
  have r1: \<open>2 * Re (\<langle> h - k , f \<rangle>) \<le> \<parallel> f \<parallel>^2\<close>
    if "f \<in> M" and \<open>k \<in> M\<close> and \<open>is_arg_min (\<lambda>x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    for f
  proof-
    have \<open>k + f \<in>  M\<close> 
      using \<open>csubspace M\<close>
      by (simp add:complex_vector.subspace_add that)
    have "\<forall>f A a b. \<not> is_arg_min f (\<lambda> x. x \<in> A) (a::'a) \<or> (f a::real) \<le> f b \<or> b \<notin> A"
      by (metis (no_types) is_arg_min_linorder)
    hence "dist k h \<le> dist (f + k) h"
      by (metis \<open>is_arg_min (\<lambda>x. dist x h) (\<lambda> x. x \<in> M) k\<close> \<open>k + f \<in> M\<close> add.commute)
    hence \<open>dist h k \<le> dist  h (k + f)\<close>
      by (simp add: add.commute dist_commute)
    hence \<open>\<parallel> h - k \<parallel> \<le> \<parallel> h - (k + f) \<parallel>\<close>
      by (simp add: dist_norm)
    hence \<open>\<parallel> h - k \<parallel>^2 \<le> \<parallel> h - (k + f) \<parallel>^2\<close>
      by (simp add: power_mono)
    also have \<open>... \<le> \<parallel> (h - k) - f \<parallel>^2\<close>
      by (simp add: diff_diff_add)
    also have \<open>... \<le> \<parallel> (h - k) \<parallel>^2 + \<parallel> f \<parallel>^2 -  2 * Re (\<langle> h - k , f \<rangle>)\<close>
      by (simp add: polar_identity_minus)
    finally have \<open>\<parallel> (h - k) \<parallel>^2 \<le> \<parallel> (h - k) \<parallel>^2 + \<parallel> f \<parallel>^2 -  2 * Re (\<langle> h - k , f \<rangle>)\<close>
      by simp
    thus ?thesis by simp
  qed

  have q4: \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> c\<close>
    if  \<open>\<forall>c>0. 2 * Re (\<langle>h - k , f\<rangle> ) \<le> c * \<parallel>f\<parallel>\<^sup>2\<close>
    for f
  proof (cases \<open>\<parallel> f \<parallel>^2 > 0\<close>)
    case True
    hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> (c/\<parallel> f \<parallel>^2)*\<parallel> f \<parallel>^2\<close>
      using that linordered_field_class.divide_pos_pos by blast
    thus ?thesis 
      using True by auto
  next
    case False
    hence \<open>\<parallel> f \<parallel>^2 = 0\<close> 
      by simp
    thus ?thesis 
      by auto
  qed
  have q3: \<open>\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> 0\<close> 
    if a3: \<open>\<forall>f. f \<in> M \<longrightarrow> (\<forall>c>0. 2 * Re \<langle>h - k , f\<rangle> \<le> c * \<parallel>f\<parallel>\<^sup>2)\<close>
      and a2: "f \<in>  M"
      and a1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
    for f
  proof-
    have \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> c*\<parallel> f \<parallel>^2\<close>
      by (simp add: that )    
    thus ?thesis 
      using q4 by smt
  qed
  have w2: "h - k \<in> orthogonal_complement M \<and> k \<in> M"
    if a1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
  proof-
    have  \<open>k \<in> M\<close>
      using is_arg_min_def that by fastforce    
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> \<parallel> f \<parallel>^2\<close>
      using r1
      by (simp add: that) 
    have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real.  2 * Re (\<langle> h - k , c *\<^sub>R f \<rangle>) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
      using  assms scaleR_scaleC complex_vector.subspace_def \<open>csubspace M\<close>
      by (metis \<open>\<forall>f. f \<in> M \<longrightarrow> 2 * Re \<langle>h - k, f\<rangle> \<le> \<parallel>f\<parallel>\<^sup>2\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
      by (metis Re_complex_of_real cinner_scaleC_right complex_add_cnj complex_cnj_complex_of_real
          complex_cnj_mult of_real_mult scaleR_scaleC semiring_normalization_rules(34))
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> \<bar>c\<bar>^2*\<parallel> f \<parallel>^2)\<close>
      by (simp add: power_mult_distrib)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> c^2*\<parallel> f \<parallel>^2)\<close>
      by auto
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> c^2*\<parallel> f \<parallel>^2)\<close>
      by simp
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c*(2 * Re (\<langle> h - k , f \<rangle>)) \<le> c*(c*\<parallel> f \<parallel>^2))\<close>
      by (simp add: power2_eq_square)
    hence  q4: \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> c*\<parallel> f \<parallel>^2)\<close>
      by simp     
    have  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> 0)\<close>
      using q3
      by (simp add: q4 that)      
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k , (-1) *\<^sub>R f \<rangle>)) \<le> 0)\<close>
      using assms scaleR_scaleC complex_vector.subspace_def
      by (metis \<open>csubspace M\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> -(2 * Re (\<langle> h - k , f \<rangle>)) \<le> 0)\<close>
      by simp
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<ge> 0)\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0)\<close>
      using  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k , f \<rangle>)) \<le> 0)\<close>
      by fastforce

    have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                 ((1::real) > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0)\<close>
      using \<open>\<forall>f. f \<in>  M \<longrightarrow> (\<forall>c>0. 2 * Re (\<langle>h - k , f\<rangle> ) = 0)\<close> by blast
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k , f \<rangle>) = 0\<close> 
      by simp     
    have  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k , (Complex 0 (-1)) *\<^sub>C f \<rangle>) = 0\<close>
      using assms  complex_vector.subspace_def \<open>csubspace M\<close>
      by (metis \<open>\<forall>f. f \<in> M \<longrightarrow> Re \<langle>h - k, f\<rangle> = 0\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re ( (Complex 0 (-1))*(\<langle> h - k , f \<rangle>) ) = 0\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> Im (\<langle> h - k , f \<rangle>) = 0\<close> 
      using Complex_eq_neg_1 Re_i_times cinner_scaleC_right complex_of_real_def by auto        

    have \<open>\<forall> f. f \<in>  M \<longrightarrow> (\<langle> h - k , f \<rangle>) = 0\<close>
      using complex_eq_iff
      by (simp add: \<open>\<forall>f. f \<in> M \<longrightarrow> Im \<langle>h - k, f\<rangle> = 0\<close> \<open>\<forall>f. f \<in> M \<longrightarrow> Re \<langle>h - k, f\<rangle> = 0\<close>)
    hence \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
      by (simp add: \<open>k \<in> M\<close> orthogonal_complementI) 
    have  \<open>\<forall> c. c *\<^sub>R f \<in> M\<close>
      if "f \<in> M"
      for f
      using that scaleR_scaleC  \<open>csubspace M\<close> complex_vector.subspace_def
      by (simp add: complex_vector.subspace_def scaleR_scaleC)
    have \<open>\<langle> h - k , f \<rangle> = 0\<close> 
      if "f \<in> M"
      for f
      using \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> orthogonal_complement_orthoI that by auto
    hence \<open>h - k \<in> orthogonal_complement M\<close> 
      by (simp add: orthogonal_complement_def)
    thus ?thesis
      using \<open>k \<in> M\<close> by auto       
  qed

  have q1: \<open>dist h k \<le> dist h f \<close> 
    if "f \<in> M" and  \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
    for f
  proof-
    have \<open>\<langle> h - k,  k - f \<rangle> = 0\<close>
      by (metis (no_types, lifting) that 
          cinner_diff_right diff_0_right orthogonal_complement_orthoI that)
    have \<open>\<parallel> h - f \<parallel>^2 = \<parallel> (h - k) + (k - f) \<parallel>^2\<close>
      by simp
    also have \<open>... = \<parallel> h - k \<parallel>^2 + \<parallel> k - f \<parallel>^2\<close>
      using  \<open>\<langle> h - k, k - f \<rangle> = 0\<close> pythagorean_theorem by blast
    also have \<open>... \<ge> \<parallel> h - k \<parallel>^2\<close>
      by simp
    finally have \<open>\<parallel>h - k\<parallel>\<^sup>2 \<le> \<parallel>h - f\<parallel>\<^sup>2 \<close>
      by blast
    hence \<open>\<parallel>h - k\<parallel> \<le> \<parallel>h - f\<parallel>\<close>
      using norm_ge_zero power2_le_imp_le by blast
    thus ?thesis 
      by (simp add: dist_norm)
  qed

  have  w1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
    if "h - k \<in> orthogonal_complement M \<and> k \<in>  M"
  proof-
    have \<open>h - k \<in> orthogonal_complement M\<close>
      using that by blast
    have \<open>k \<in> M\<close> using \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M\<close>
      by blast   
    thus ?thesis
      by (metis (no_types, lifting) dist_commute is_arg_min_linorder q1 that) 
  qed
  show ?thesis
    using w1 w2 by blast 
qed

corollary orthog_proj_exists:
  fixes M :: \<open>'a::chilbert_space set\<close> 
  assumes \<open>closed_csubspace M\<close>
  shows  \<open>\<exists>k. h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
proof-
  from  \<open>closed_csubspace M\<close>
  have \<open>M \<noteq> {}\<close>
    using closed_csubspace.subspace complex_vector.subspace_0 by blast
  have \<open>closed  M\<close>
    using  \<open>closed_csubspace M\<close>
    by (simp add: closed_csubspace.closed)
  have \<open>convex  M\<close>
    using  \<open>closed_csubspace M\<close>
    by (simp)
  have \<open>\<exists>k.  is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    by (simp add: smallest_dist_exists \<open>closed M\<close> \<open>convex M\<close> \<open>M \<noteq> {}\<close>)
  thus ?thesis
    by (simp add: assms smallest_dist_is_ortho)  
qed

corollary orthog_proj_unique:
  fixes M :: \<open>'a::complex_inner set\<close> 
  assumes \<open>closed_csubspace M\<close>
  assumes \<open>h - r \<in> orthogonal_complement M \<and> r \<in> M\<close>
  assumes \<open>h - s \<in> orthogonal_complement M \<and> s \<in> M\<close>
  shows  \<open>r = s\<close>
  using _ assms(2,3) unfolding smallest_dist_is_ortho[OF assms(1), symmetric]
  apply (rule smallest_dist_unique)
  using assms(1) by (simp)

definition is_projection_on::\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a::metric_space) set \<Rightarrow> bool\<close> where
  \<open>is_projection_on \<pi> M \<longleftrightarrow> (\<forall>h. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) (\<pi> h))\<close>

lemma is_projection_on_iff_orthog:
  \<open>closed_csubspace M \<Longrightarrow> is_projection_on \<pi> M \<longleftrightarrow> (\<forall>h. h - \<pi> h \<in> orthogonal_complement M \<and> \<pi> h \<in> M)\<close>
  by (simp add: is_projection_on_def smallest_dist_is_ortho)

lemma is_projection_on_exists:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows "\<exists>\<pi>. is_projection_on \<pi> M"
  unfolding is_projection_on_def apply (rule choice)
  using smallest_dist_exists[OF assms] by auto

lemma is_projection_on_unique:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes \<open>convex M\<close>
  assumes "is_projection_on \<pi>\<^sub>1 M"
  assumes "is_projection_on \<pi>\<^sub>2 M"
  shows "\<pi>\<^sub>1 = \<pi>\<^sub>2"
  using smallest_dist_unique[OF assms(1)] using assms(2,3)
  unfolding is_projection_on_def by blast

definition projection :: \<open>'a::metric_space set \<Rightarrow> ('a \<Rightarrow> 'a)\<close> where
  \<open>projection M \<equiv> SOME \<pi>. is_projection_on \<pi> M\<close>

lemma projection_is_projection_on:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows "is_projection_on (projection M) M"
  by (metis assms(1) assms(2) assms(3) is_projection_on_exists projection_def someI)

lemma projection_is_projection_on'[simp]:
  \<comment> \<open>Common special case of @{thm projection_is_projection_on}\<close>
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>closed_csubspace M\<close>
  shows "is_projection_on (projection M) M"
  apply (rule projection_is_projection_on)
    apply (auto simp add: assms closed_csubspace.closed)
  using assms closed_csubspace.subspace complex_vector.subspace_0 by blast

lemma projection_orthogonal:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes "closed_csubspace M" and \<open>m \<in> M\<close>
  shows \<open>is_orthogonal (h - projection M h) m\<close>
  by (metis assms(1) assms(2) closed_csubspace.closed closed_csubspace.subspace csubspace_is_convex empty_iff is_projection_on_iff_orthog orthogonal_complement_orthoI projection_is_projection_on)

lemma is_projection_on_in_image:
  assumes "is_projection_on \<pi> M"
  shows "\<pi> h \<in> M"
  using assms
  by (simp add: is_arg_min_def is_projection_on_def)

lemma is_projection_on_image:
  assumes "is_projection_on \<pi> M"
  shows "range \<pi> = M"
  using assms
  apply (auto simp: is_projection_on_in_image)
  by (smt (verit, ccfv_threshold) dist_pos_lt dist_self is_arg_min_def is_projection_on_def rangeI)

lemma projection_in_image[simp]:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows \<open>projection M h \<in> M\<close>
  by (simp add: assms(1) assms(2) assms(3) is_projection_on_in_image projection_is_projection_on)

lemma projection_image[simp]:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows \<open>range (projection M) = M\<close>
  by (simp add: assms(1) assms(2) assms(3) is_projection_on_image projection_is_projection_on)

lemma projection_eqI':
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes \<open>convex M\<close>
  assumes \<open>is_projection_on f M\<close>
  shows \<open>projection M = f\<close>
  by (metis assms(1) assms(2) is_projection_on_unique projection_def someI_ex)

lemma is_projection_on_eqI:
  fixes  M :: \<open>'a::complex_inner set\<close>
  assumes a1: \<open>closed_csubspace M\<close> and a2: \<open>h - x \<in> orthogonal_complement M\<close> and a3: \<open>x \<in> M\<close> 
    and a4: \<open>is_projection_on \<pi> M\<close>
  shows \<open>\<pi> h = x\<close>
  by (meson a1 a2 a3 a4 closed_csubspace.subspace csubspace_is_convex is_projection_on_def smallest_dist_is_ortho smallest_dist_unique)

lemma projection_eqI:
  fixes  M :: \<open>('a::chilbert_space) set\<close>
  assumes  \<open>closed_csubspace M\<close> and \<open>h - x \<in> orthogonal_complement M\<close> and \<open>x \<in> M\<close>
  shows \<open>projection M h = x\<close>
  by (metis assms(1) assms(2) assms(3) is_projection_on_iff_orthog orthog_proj_exists projection_def is_projection_on_eqI tfl_some)

lemma is_projection_on_fixes_image:
  fixes M :: \<open>'a::metric_space set\<close>
  assumes a1: "is_projection_on \<pi> M" and a3: "x \<in> M"
  shows "\<pi> x = x"
  by (metis a1 a3 dist_pos_lt dist_self is_arg_min_def is_projection_on_def)

lemma projection_fixes_image:
  fixes M :: \<open>('a::chilbert_space) set\<close>
  assumes a1: "closed_csubspace M" and a2: "x \<in> M"
  shows "(projection M) x = x"
  using is_projection_on_fixes_image
    \<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close>
  by (simp add: a1 a2 complex_vector.subspace_0 projection_eqI)

proposition is_projection_on_reduces_norm:
  includes notation_norm
  fixes M :: \<open>('a::complex_inner) set\<close>
  assumes \<open>is_projection_on \<pi> M\<close> and \<open>closed_csubspace M\<close>
  shows \<open>\<parallel> \<pi>  h \<parallel> \<le> \<parallel> h \<parallel>\<close>
proof-
  have \<open>h - \<pi> h \<in> orthogonal_complement M\<close>
    using assms is_projection_on_iff_orthog by blast 
  hence \<open>\<forall> k \<in> M. \<langle>  h - \<pi> h , k \<rangle> = 0\<close>
    using orthogonal_complement_orthoI by blast 
  also have \<open>\<pi> h \<in>  M\<close>
    using \<open>is_projection_on \<pi> M\<close>
    by (simp add: is_projection_on_in_image)
  ultimately have \<open>\<langle>  h - \<pi> h , \<pi> h \<rangle> = 0\<close>
    by auto
  hence \<open>\<parallel> \<pi> h \<parallel>^2 + \<parallel> h - \<pi> h \<parallel>^2 = \<parallel> h \<parallel>^2\<close>
    using pythagorean_theorem by fastforce
  hence \<open>\<parallel>\<pi> h \<parallel>^2 \<le> \<parallel> h \<parallel>^2\<close>
    by (smt zero_le_power2)    
  thus ?thesis 
    using norm_ge_zero power2_le_imp_le by blast
qed

proposition projection_reduces_norm:
  includes notation_norm
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_csubspace M"
  shows \<open>\<parallel> projection M h \<parallel> \<le> \<parallel> h \<parallel>\<close>
  using assms is_projection_on_iff_orthog orthog_proj_exists is_projection_on_reduces_norm projection_eqI by blast

\<comment> \<open>Theorem 2.7 (version) in @{cite conway2013course}\<close>
theorem is_projection_on_bounded_clinear:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_csubspace M"
  shows "bounded_clinear \<pi>"
proof
  have b1:  \<open>csubspace (orthogonal_complement M)\<close>
    by (simp add: a2)
  have f1: "\<forall>a. a - \<pi> a \<in> orthogonal_complement M \<and> \<pi> a \<in> M"
    using a1 a2 is_projection_on_iff_orthog by blast
  hence "c *\<^sub>C x - c *\<^sub>C \<pi> x \<in> orthogonal_complement M"
    for c x
    by (metis (no_types) b1 
        add_diff_cancel_right' complex_vector.subspace_def diff_add_cancel scaleC_add_right)
  thus r1: \<open>\<pi> (c *\<^sub>C x) = c *\<^sub>C (\<pi> x)\<close> for x c
    using f1 by (meson a2 a1 closed_csubspace.subspace 
        complex_vector.subspace_def is_projection_on_eqI)
  show r2: \<open>\<pi> (x + y) =  (\<pi> x) + (\<pi> y)\<close>
    for x y
  proof-
    have "\<forall>A. \<not> closed_csubspace (A::'a set) \<or> csubspace A"
      by (metis closed_csubspace.subspace)
    hence "csubspace M"
      using a2 by auto      
    hence \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M\<close>
      by (simp add: complex_vector.subspace_add complex_vector.subspace_diff f1)      
    have \<open>closed_csubspace (orthogonal_complement M)\<close>
      using a2
      by simp
    have f1: "\<forall>a b. (b::'a) + (a - b) = a"
      by (metis add.commute diff_add_cancel)
    have f2: "\<forall>a b. (b::'a) - b = a - a"
      by auto
    hence f3: "\<forall>a. a - a \<in> orthogonal_complement M"
      by (simp add: complex_vector.subspace_0)
    have "\<forall>a b. (a \<in> orthogonal_complement M \<or> a + b \<notin> orthogonal_complement M)
             \<or> b \<notin> orthogonal_complement M"
      using add_diff_cancel_right' b1 complex_vector.subspace_diff
      by metis
    hence "\<forall>a b c. (a \<in> orthogonal_complement M \<or> c - (b + a) \<notin> orthogonal_complement M) 
              \<or> c - b \<notin> orthogonal_complement M"
      using f1 by (metis diff_diff_add)
    hence f4: "\<forall>a b f. (f a - b \<in> orthogonal_complement M \<or> a - b \<notin> orthogonal_complement M) 
              \<or> \<not> is_projection_on f M"
      using f1
      by (metis a2 is_projection_on_iff_orthog)
    have f5: "\<forall>a b c d. (d::'a) - (c + (b - a)) = d + (a - (b + c))"
      by auto
    have "x - \<pi> x \<in> orthogonal_complement M"
      using a1 a2 is_projection_on_iff_orthog by blast
    hence q1: \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> orthogonal_complement M\<close>
      using f5 f4 f3 by (metis \<open>csubspace (orthogonal_complement M)\<close> 
          \<open>is_projection_on \<pi> M\<close> add_diff_eq complex_vector.subspace_diff diff_diff_add 
          diff_diff_eq2)
    hence \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M \<inter> (orthogonal_complement M)\<close>
      by (simp add: \<open>\<pi> (x + y) - (\<pi> x + \<pi> y) \<in> M\<close>)      
    moreover have \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
      by (simp add: \<open>closed_csubspace M\<close> complex_vector.subspace_0 orthogonal_complement_zero_intersection)
    ultimately have \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) = 0\<close>
      by auto      
    thus ?thesis by simp
  qed
  from is_projection_on_reduces_norm
  show t1: \<open>\<exists> K. \<forall> x. norm (\<pi> x) \<le> norm x * K\<close>
    by (metis a1 a2 mult.left_neutral ordered_field_class.sign_simps(5))
qed

theorem projection_bounded_clinear:
  fixes M :: \<open>('a::chilbert_space) set\<close>
  assumes a1: "closed_csubspace M"
  shows \<open>bounded_clinear (projection M)\<close> 
    \<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close>
  using assms is_projection_on_iff_orthog orthog_proj_exists is_projection_on_bounded_clinear projection_eqI by blast      

proposition is_projection_on_idem:
  fixes M :: \<open>('a::complex_inner) set\<close>
  assumes "is_projection_on \<pi> M"
  shows "\<pi> (\<pi> x) = \<pi> x"
  using is_projection_on_fixes_image is_projection_on_in_image assms by blast

proposition projection_idem:
  fixes M :: "'a::chilbert_space set"
  assumes a1: "closed_csubspace M"
  shows "projection M (projection M x) = projection M x"
  by (metis assms closed_csubspace.closed closed_csubspace.subspace complex_vector.subspace_0 csubspace_is_convex equals0D projection_fixes_image projection_in_image)


proposition is_projection_on_kernel_is_orthogonal_complement:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_csubspace M"
  shows "\<pi> -` {0} = orthogonal_complement M"
proof-
  have "x \<in> (\<pi> -` {0})" 
    if "x \<in> orthogonal_complement M"
    for x
    by (smt (verit, ccfv_SIG) a1 a2 closed_csubspace_def complex_vector.subspace_def complex_vector.subspace_diff is_projection_on_eqI orthogonal_complement_closed_subspace that vimage_singleton_eq)
  moreover have "x \<in> orthogonal_complement M"
    if s1: "x \<in> \<pi> -` {0}" for x
    by (metis a1 a2 diff_zero is_projection_on_iff_orthog that vimage_singleton_eq)
  ultimately show ?thesis 
    by blast
qed

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
proposition projection_kernel_is_orthogonal_complement:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes "closed_csubspace M"
  shows "(projection M) -` {0} = (orthogonal_complement M)"
  by (metis assms closed_csubspace_def complex_vector.subspace_def csubspace_is_convex insert_absorb insert_not_empty is_projection_on_kernel_is_orthogonal_complement projection_is_projection_on)

lemma is_projection_on_id_minus:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes is_proj: "is_projection_on \<pi> M"
    and cc: "closed_csubspace M"
  shows "is_projection_on (id - \<pi>) (orthogonal_complement M)"
  using is_proj apply (simp add: cc is_projection_on_iff_orthog)
  using double_orthogonal_complement_increasing by blast


text \<open>Exercise 2 (section 2, chapter I) in  @{cite conway2013course}\<close>
lemma projection_on_orthogonal_complement[simp]:
  fixes M :: "'a::chilbert_space set"
  assumes a1: "closed_csubspace M"
  shows "projection (orthogonal_complement M) = id - projection M"
  apply (auto intro!: ext)
  by (smt (verit, ccfv_SIG) add_diff_cancel_left' assms closed_csubspace.closed closed_csubspace.subspace complex_vector.subspace_0 csubspace_is_convex diff_add_cancel double_orthogonal_complement_increasing insert_absorb insert_not_empty is_projection_on_iff_orthog orthogonal_complement_closed_subspace projection_eqI projection_is_projection_on subset_eq)

lemma is_projection_on_zero:
  "is_projection_on (\<lambda>_. 0) {0}"
  by (simp add: is_projection_on_def is_arg_min_def)

lemma projection_zero[simp]:
  "projection {0} = (\<lambda>_. 0)"
  using is_projection_on_zero
  by (metis (full_types) is_projection_on_in_image projection_def singletonD someI_ex)

lemma is_projection_on_rank1:
  fixes t :: \<open>'a::complex_inner\<close>
  shows \<open>is_projection_on (\<lambda>x. (\<langle>t , x\<rangle> / \<langle>t , t\<rangle>) *\<^sub>C t) (cspan {t})\<close>
proof (cases \<open>t = 0\<close>)
  case True
  then show ?thesis
    by (simp add: is_projection_on_zero)
next
  case False
  define P where \<open>P x = (\<langle>t , x\<rangle> / \<langle>t , t\<rangle>) *\<^sub>C t\<close> for x
  define t' where \<open>t' = t /\<^sub>C norm t\<close>
  with False have \<open>norm t' = 1\<close>
    by (simp add: norm_inverse)
  have P_def': \<open>P x = cinner t' x *\<^sub>C t'\<close> for x
    unfolding P_def t'_def apply auto
    by (metis divide_divide_eq_left divide_inverse mult.commute power2_eq_square power2_norm_eq_cinner)
  have spant': \<open>cspan {t} = cspan {t'}\<close>
    by (simp add: False t'_def)
  have cc: \<open>closed_csubspace (cspan {t})\<close>
    by (auto intro!: finite_cspan_closed closed_csubspace.intro)
  have ortho: \<open>h - P h \<in> orthogonal_complement (cspan {t})\<close> for h
    unfolding orthogonal_complement_def P_def' spant' apply auto
    by (smt (verit, ccfv_threshold) \<open>norm t' = 1\<close> add_cancel_right_left cinner_add_right cinner_commute' cinner_scaleC_right cnorm_eq_1 complex_vector.span_breakdown_eq complex_vector.span_empty diff_add_cancel mult_cancel_left1 singletonD)
  have inspan: \<open>P h \<in> cspan {t}\<close> for h
    unfolding P_def' spant'
    by (simp add: complex_vector.span_base complex_vector.span_scale)
  show \<open>is_projection_on P (cspan {t})\<close>
    apply (subst is_projection_on_iff_orthog)
    using cc ortho inspan by auto      
qed

lemma projection_rank1:
  fixes t x :: \<open>'a::complex_inner\<close>
  shows \<open>projection (cspan {t}) x = (\<langle>t , x\<rangle> / \<langle>t , t\<rangle>) *\<^sub>C t\<close>
  apply (rule fun_cong, rule projection_eqI', simp)
  by (rule is_projection_on_rank1)

subsection \<open>More orthogonal complement\<close>

text \<open>The following lemmas logically fit into the "orthogonality" section but depend on projections for their proofs.\<close>

text \<open>Corollary 2.8 in  @{cite conway2013course}\<close>
theorem double_orthogonal_complement_id[simp]:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_csubspace M"
  shows "orthogonal_complement (orthogonal_complement M) = M"  
proof-
  have b2: "x \<in> (id - projection M) -` {0}"
    if c1: "x \<in> M" for x
    by (simp add: assms projection_fixes_image that)

  have b3: \<open>x \<in> M\<close> 
    if c1: \<open>x \<in> (id - projection M) -` {0}\<close> for x
    by (metis assms closed_csubspace.closed closed_csubspace.subspace complex_vector.subspace_0 csubspace_is_convex eq_id_iff equals0D fun_diff_def projection_in_image right_minus_eq that vimage_singleton_eq)
  have \<open>x \<in>  M \<longleftrightarrow> x \<in> (id - projection M) -` {0}\<close> for x
    using b2 b3 by blast      
  hence b4: \<open>( id - (projection M) ) -` {0} =  M\<close>
    by blast
  have b1: "orthogonal_complement (orthogonal_complement M) 
          = (projection (orthogonal_complement M)) -` {0}"
    by (simp add: a1 projection_kernel_is_orthogonal_complement del: projection_on_orthogonal_complement)
  also have \<open>... = ( id - (projection M) ) -` {0}\<close>
    by (simp add: a1)
  also have \<open>... = M\<close>
    by (simp add: b4)     
  finally show ?thesis by blast
qed

lemma orthogonal_complement_antimono[simp]:
  fixes  A B :: \<open>('a::complex_inner) set\<close>
  assumes "A \<supseteq> B"
  shows \<open>orthogonal_complement A \<subseteq> orthogonal_complement B\<close>
  by (meson assms orthogonal_complementI orthogonal_complement_orthoI' subsetD subsetI)

lemma orthogonal_complement_antimono_iff[simp]:
  fixes  A B :: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_csubspace A\<close> and  \<open>closed_csubspace B\<close>
  shows \<open>orthogonal_complement A \<subseteq> orthogonal_complement B \<longleftrightarrow> A \<supseteq> B\<close>
proof
  show \<open>orthogonal_complement A \<subseteq> orthogonal_complement B\<close> if \<open>A \<supseteq> B\<close>
    using that by auto

  assume \<open>orthogonal_complement A \<subseteq> orthogonal_complement B\<close>
  then have \<open>orthogonal_complement (orthogonal_complement A) \<supseteq> orthogonal_complement (orthogonal_complement B)\<close>
    by simp
  then show \<open>A \<supseteq> B\<close>
    using assms by auto
qed

lemma orthogonal_complement_UNIV[simp]: 
  "orthogonal_complement UNIV = {0}"
  by (metis Int_UNIV_left complex_vector.subspace_UNIV complex_vector.subspace_def orthogonal_complement_zero_intersection)

lemma orthogonal_complement_zero[simp]:
  "orthogonal_complement {0} = UNIV"
  unfolding orthogonal_complement_def by auto


lemma de_morgan_orthogonal_complement_plus:        
  fixes A B::"('a::complex_inner) set"
  assumes \<open>0 \<in> A\<close> and \<open>0 \<in> B\<close>
  shows \<open>orthogonal_complement (A +\<^sub>M B) = (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close>
proof-
  have "x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)"
    if "x \<in> orthogonal_complement (A +\<^sub>M B)" 
    for x
  proof-
    have \<open>orthogonal_complement (A +\<^sub>M B) = orthogonal_complement (A + B)\<close>
      unfolding closed_sum_def by (subst orthogonal_complement_of_closure[symmetric], simp)
    hence \<open>x \<in> orthogonal_complement (A + B)\<close>
      using that by blast      
    hence t1: \<open>\<forall>z \<in> (A + B). \<langle> z , x \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_orthoI') 
    have \<open>A \<subseteq> A + B\<close>
      using subset_iff add.commute set_zero_plus2 \<open>0 \<in> B\<close>
      by fastforce
    hence \<open>\<forall>z \<in> A. \<langle> z , x \<rangle> = 0\<close> 
      using t1 by auto
    hence w1: \<open>x \<in> (orthogonal_complement A)\<close>
      by (smt mem_Collect_eq is_orthogonal_sym orthogonal_complement_def)
    have \<open>B \<subseteq> A + B\<close>
      using \<open>0 \<in> A\<close> subset_iff set_zero_plus2 by blast        
    hence \<open>\<forall> z \<in> B. \<langle> z , x \<rangle> = 0\<close>
      using t1 by auto   
    hence \<open>x \<in> (orthogonal_complement B)\<close>
      by (smt mem_Collect_eq is_orthogonal_sym orthogonal_complement_def)
    thus ?thesis 
      using w1 by auto
  qed
  moreover have "x \<in> (orthogonal_complement (A +\<^sub>M B))"
    if v1: "x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)"
    for x
  proof-
    have \<open>x \<in> (orthogonal_complement A)\<close> 
      using v1
      by blast
    hence \<open>\<forall>y\<in> A. \<langle> y , x \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_orthoI')
    have \<open>x \<in> (orthogonal_complement B)\<close> 
      using v1 
      by blast
    hence \<open>\<forall> y\<in> B. \<langle> y , x \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_orthoI')
    have \<open>\<forall> a\<in>A. \<forall> b\<in>B. \<langle> a+b , x \<rangle> = 0\<close>
      by (simp add: \<open>\<forall>y\<in>A. \<langle>y , x\<rangle> = 0\<close> \<open>\<forall>y\<in>B. \<langle>y , x\<rangle> = 0\<close> cinner_add_left)
    hence \<open>\<forall> y \<in> (A + B). \<langle> y , x \<rangle> = 0\<close>
      using set_plus_elim by force
    hence \<open>x \<in> (orthogonal_complement (A + B))\<close>
      by (smt mem_Collect_eq is_orthogonal_sym orthogonal_complement_def)
    moreover have \<open>(orthogonal_complement (A + B)) = (orthogonal_complement (A +\<^sub>M B))\<close>
      unfolding closed_sum_def by (subst orthogonal_complement_of_closure[symmetric], simp)
    ultimately have \<open>x \<in> (orthogonal_complement (A +\<^sub>M B))\<close>
      by blast
    thus ?thesis
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma de_morgan_orthogonal_complement_inter:
  fixes A B::"'a::chilbert_space set"
  assumes a1: \<open>closed_csubspace A\<close> and a2: \<open>closed_csubspace B\<close>
  shows  \<open>orthogonal_complement (A \<inter> B) = orthogonal_complement A +\<^sub>M orthogonal_complement B\<close>
proof-
  have \<open>orthogonal_complement A +\<^sub>M orthogonal_complement B
    = orthogonal_complement (orthogonal_complement (orthogonal_complement A +\<^sub>M orthogonal_complement B))\<close>
    by (simp add: closed_subspace_closed_sum)
  also have \<open>\<dots> = orthogonal_complement (orthogonal_complement (orthogonal_complement A) \<inter> orthogonal_complement (orthogonal_complement B))\<close>
    by (simp add: de_morgan_orthogonal_complement_plus orthogonal_complementI)
  also have \<open>\<dots> = orthogonal_complement (A \<inter> B)\<close>
    by (simp add: a1 a2)
  finally show ?thesis
    by simp
qed

subsection \<open>Riesz-representation theorem\<close>

lemma orthogonal_complement_kernel_functional:
  fixes f :: \<open>'a::complex_inner \<Rightarrow> complex\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>\<exists>x. orthogonal_complement (f -` {0}) = cspan {x}\<close>
proof (cases \<open>orthogonal_complement (f -` {0}) = {0}\<close>)
  case True
  then show ?thesis
    apply (rule_tac x=0 in exI) by auto
next
  case False
  then obtain x where xortho: \<open>x \<in> orthogonal_complement (f -` {0})\<close> and xnon0: \<open>x \<noteq> 0\<close>
    using complex_vector.subspace_def by fastforce

  from xnon0 xortho
  have r1: \<open>f x \<noteq> 0\<close>
    by (metis cinner_eq_zero_iff orthogonal_complement_orthoI vimage_singleton_eq)

  have \<open>\<exists> k. y = k *\<^sub>C x\<close> if \<open>y \<in> orthogonal_complement (f -` {0})\<close> for y
  proof (cases \<open>y = 0\<close>)
    case True
    then show ?thesis by auto
  next
    case False
    with that
    have \<open>f y \<noteq> 0\<close>
      by (metis cinner_eq_zero_iff orthogonal_complement_orthoI vimage_singleton_eq)
    then obtain k where k_def: \<open>f x = k * f y\<close>
      by (metis add.inverse_inverse minus_divide_eq_eq)
    with assms have \<open>f x = f (k *\<^sub>C y)\<close>
      by (simp add: bounded_clinear.axioms(1) clinear.scaleC)
    hence \<open>f x - f (k *\<^sub>C y) = 0\<close>
      by simp
    with assms have s1: \<open>f (x - k *\<^sub>C y) = 0\<close>
      by (simp add: bounded_clinear.axioms(1) complex_vector.linear_diff)
    from that have \<open>k *\<^sub>C y \<in> orthogonal_complement (f -` {0})\<close>
      by (simp add: complex_vector.subspace_scale)
    with xortho have s2: \<open>x - (k *\<^sub>C y) \<in> orthogonal_complement (f -` {0})\<close>
      by (simp add: complex_vector.subspace_diff)
    have s3: \<open>(x - (k *\<^sub>C y)) \<in> f -` {0}\<close>
      using s1 by simp
    moreover have \<open>(f -` {0}) \<inter> (orthogonal_complement (f -` {0})) = {0}\<close>
      by (meson assms closed_csubspace_def complex_vector.subspace_def kernel_is_closed_csubspace 
          orthogonal_complement_zero_intersection)
    ultimately have \<open>x - (k *\<^sub>C y) = 0\<close>
      using s2 by blast
    thus ?thesis
      by (metis ceq_vector_fraction_iff eq_iff_diff_eq_0 k_def r1 scaleC_scaleC)
  qed
  then have \<open>orthogonal_complement (f -` {0}) \<subseteq> cspan {x}\<close>
    using complex_vector.span_superset complex_vector.subspace_scale by blast

  moreover from xortho have \<open>orthogonal_complement (f -` {0}) \<supseteq> cspan {x}\<close>
    by (simp add: complex_vector.span_minimal)

  ultimately show ?thesis
    by auto
qed

lemma riesz_frechet_representation_existence:
  \<comment> \<open>Theorem 3.4 in @{cite conway2013course}\<close>
  fixes f::\<open>'a::chilbert_space \<Rightarrow> complex\<close>
  assumes a1: \<open>bounded_clinear f\<close>
  shows \<open>\<exists>t. \<forall>x.  f x = \<langle>t, x\<rangle>\<close>
proof(cases \<open>\<forall> x. f x = 0\<close>)
  case True
  thus ?thesis
    by (metis cinner_zero_left) 
next
  case False
  obtain t where spant: \<open>orthogonal_complement (f -` {0}) = cspan {t}\<close>
    using orthogonal_complement_kernel_functional
    using assms by blast
  have \<open>projection (orthogonal_complement (f -` {0})) x = (\<langle>t , x\<rangle>/\<langle>t , t\<rangle>) *\<^sub>C t\<close> for x
    apply (subst spant) by (rule projection_rank1)
  hence \<open>f (projection (orthogonal_complement (f -` {0})) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close> for x
    using a1 unfolding bounded_clinear_def
    by (simp add: complex_vector.linear_scale)
  hence l2: \<open>f (projection (orthogonal_complement (f -` {0})) x) = \<langle>((cnj (f t)/\<langle>t , t\<rangle>) *\<^sub>C t) , x\<rangle>\<close> for x
    using complex_cnj_divide by force
  have \<open>f (projection (f -` {0}) x) = 0\<close> for x
    by (metis (no_types, lifting) assms bounded_clinear_def closed_csubspace.closed
        complex_vector.linear_subspace_vimage complex_vector.subspace_0 complex_vector.subspace_single_0
        csubspace_is_convex insert_absorb insert_not_empty kernel_is_closed_csubspace projection_in_image vimage_singleton_eq)
  hence "\<And>a b. f (projection (f -` {0}) a + b) = 0 + f b"
    using additive.add assms
    by (simp add: bounded_clinear_def complex_vector.linear_add)
  hence "\<And>a. 0 + f (projection (orthogonal_complement (f -` {0})) a) = f a"
    apply (simp add: assms)
    by (metis add.commute diff_add_cancel)
  hence \<open>f x = \<langle>(cnj (f t)/\<langle>t , t\<rangle>) *\<^sub>C t, x\<rangle>\<close> for x
    by (simp add: l2) 
  thus ?thesis
    by blast
qed

lemma riesz_frechet_representation_unique:
  \<comment> \<open>Theorem 3.4 in @{cite conway2013course}\<close>
  fixes f::\<open>'a::complex_inner \<Rightarrow> complex\<close>
  assumes \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close>
  assumes \<open>\<And>x. f x = \<langle>u, x\<rangle>\<close>
  shows \<open>t = u\<close>
  by (metis add_diff_cancel_left' assms(1) assms(2) cinner_diff_left cinner_gt_zero_iff diff_add_cancel diff_zero)


subsection \<open>Adjoints\<close>

definition "is_cadjoint F G \<longleftrightarrow> (\<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>)"

lemma is_adjoint_sym:
  \<open>is_cadjoint F G \<Longrightarrow> is_cadjoint G F\<close>
  unfolding is_cadjoint_def apply auto
  by (metis cinner_commute')

definition \<open>cadjoint G = (SOME F. is_cadjoint F G)\<close>
  for G :: "'b::complex_inner \<Rightarrow> 'a::complex_inner"

lemma cadjoint_exists:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes [simp]: \<open>bounded_clinear G\<close>
  shows \<open>\<exists>F. is_cadjoint F G\<close>
proof -
  include notation_norm
  have [simp]: \<open>clinear G\<close>
    using assms unfolding bounded_clinear_def by blast
  define g :: \<open>'a \<Rightarrow> 'b \<Rightarrow> complex\<close> 
    where \<open>g x y = \<langle>x , G y\<rangle>\<close> for x y
  have \<open>bounded_clinear (g x)\<close> for x
  proof -
    have \<open>g x (a + b) = g x a + g x b\<close> for a b
      unfolding g_def
      using additive.add cinner_add_right clinear_def
      by (simp add: cinner_add_right complex_vector.linear_add)
    moreover have  \<open>g x (k *\<^sub>C a) = k *\<^sub>C (g x a)\<close>
      for a k
      unfolding g_def
      by (simp add: complex_vector.linear_scale)
    ultimately have \<open>clinear (g x)\<close>
      by (simp add: clinearI)    
    moreover 
    have \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using \<open>bounded_clinear G\<close>
      unfolding bounded_clinear_def bounded_clinear_axioms_def by blast
    then have \<open>\<exists>M. \<forall>y. \<parallel> g x y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using g_def
      by (simp add: bounded_clinear.bounded bounded_clinear_cinner_right_comp)
    ultimately show ?thesis unfolding bounded_linear_def
      using bounded_clinear.intro
      using bounded_clinear_axioms_def by blast
  qed
  hence \<open>\<forall>x. \<exists>t. \<forall>y.  g x y = \<langle>t, y\<rangle>\<close>
    using riesz_frechet_representation_existence by blast
  then obtain F where \<open>\<forall>x. \<forall>y. g x y = \<langle>F x, y\<rangle>\<close>
    by metis
  then have \<open>is_cadjoint F G\<close>
    unfolding is_cadjoint_def g_def by simp
  thus ?thesis
    by auto
qed

lemma cadjoint_is_cadjoint[simp]:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes [simp]: \<open>bounded_clinear G\<close>
  shows \<open>is_cadjoint (cadjoint G) G\<close>
  by (metis assms cadjoint_def cadjoint_exists someI_ex)

lemma is_cadjoint_unique:
  assumes \<open>is_cadjoint F1 G\<close>
  assumes \<open>is_cadjoint F2 G\<close>
  shows \<open>F1 = F2\<close>
proof (rule ext)
  fix x
  { 
    fix y
    have \<open>cinner (F1 x - F2 x) y = cinner (F1 x) y - cinner (F2 x) y\<close>
      by (simp add: cinner_diff_left)
    also have \<open>\<dots> = cinner x (G y) - cinner x (G y)\<close>
      by (metis assms(1) assms(2) is_cadjoint_def)
    also have \<open>\<dots> = 0\<close>
      by simp
    finally have \<open>cinner (F1 x - F2 x) y = 0\<close>
      by -
  }
  then show \<open>F1 x = F2 x\<close>
    by fastforce
qed

lemma cadjoint_univ_prop:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes a1: \<open>bounded_clinear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>cadjoint G x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
  using assms cadjoint_is_cadjoint is_cadjoint_def by blast

lemma cadjoint_univ_prop':
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes a1: \<open>bounded_clinear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>x, cadjoint G y\<rangle> = \<langle>G x, y\<rangle>\<close>
  by (metis cadjoint_univ_prop assms cinner_commute')

notation cadjoint ("_\<^sup>\<dagger>" [99] 100)

lemma cadjoint_eqI:
  fixes G:: \<open>'b::complex_inner \<Rightarrow> 'a::complex_inner\<close>
    and F:: \<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<And>x y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
  shows \<open>G\<^sup>\<dagger> = F\<close>
  by (metis assms cadjoint_def is_cadjoint_def is_cadjoint_unique someI_ex)

lemma cadjoint_bounded_clinear:
  fixes A :: "'a::chilbert_space \<Rightarrow> 'b::complex_inner"
  assumes a1: "bounded_clinear A"
  shows \<open>bounded_clinear (A\<^sup>\<dagger>)\<close>
proof
  include notation_norm 
  have b1: \<open>\<langle>(A\<^sup>\<dagger>) x, y\<rangle> = \<langle>x , A y\<rangle>\<close> for x y
    using cadjoint_univ_prop a1 by auto
  have \<open>\<langle>(A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) , y\<rangle> = 0\<close> for x1 x2 y
    by (simp add: b1 cinner_diff_left cinner_add_left)        
  hence b2: \<open>(A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) = 0\<close> for x1 x2
    using cinner_eq_zero_iff by blast
  thus z1: \<open>(A\<^sup>\<dagger>) (x1 + x2) = (A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2\<close> for x1 x2
    by (simp add: b2 eq_iff_diff_eq_0)

  have f1: \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x) - (r *\<^sub>C (A\<^sup>\<dagger>) x ), y\<rangle> = 0\<close> for r x y
    by (simp add: b1 cinner_diff_left)
  thus z2: \<open>(A\<^sup>\<dagger>) (r *\<^sub>C x) = r *\<^sub>C (A\<^sup>\<dagger>) x\<close> for r x
    using cinner_eq_zero_iff eq_iff_diff_eq_0 by blast
  have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<langle>(A\<^sup>\<dagger>) x, (A\<^sup>\<dagger>) x\<rangle>\<close> for x
    by (metis cnorm_eq_square)
  moreover have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<ge> 0\<close> for x
    by simp
  ultimately have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>(A\<^sup>\<dagger>) x, (A\<^sup>\<dagger>) x\<rangle> \<bar>\<close> for x
    by (metis abs_pos cinner_ge_zero)
  hence \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>x, A ((A\<^sup>\<dagger>) x)\<rangle> \<bar>\<close> for x
    by (simp add: b1)
  moreover have  \<open>\<bar>\<langle>x , A ((A\<^sup>\<dagger>) x)\<rangle>\<bar> \<le> \<parallel>x\<parallel> *  \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close> for x
    by (simp add: abs_complex_def complex_inner_class.Cauchy_Schwarz_ineq2)
  ultimately have b5: \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2  \<le> \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close> for x
    by (metis complex_of_real_mono_iff)
  have \<open>\<exists>M. M \<ge> 0 \<and> (\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
    using a1
    by (metis (mono_tags, hide_lams) bounded_clinear.bounded linear mult_nonneg_nonpos
        mult_zero_right norm_ge_zero order.trans semiring_normalization_rules(7)) 
  then obtain M where q1: \<open>M \<ge> 0\<close> and q2: \<open>\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
    by blast
  have \<open>\<forall> x::'b. \<parallel>x\<parallel> \<ge> 0\<close>
    by simp
  hence b6: \<open>\<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le>  \<parallel>x\<parallel> * M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close> for x
    using q2
    by (smt ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale) 
  have z3: \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel> \<le> \<parallel>x\<parallel> * M\<close> for x
  proof(cases \<open>\<parallel>(A\<^sup>\<dagger>) x\<parallel> = 0\<close>)
    case True
    thus ?thesis
      by (simp add: \<open>0 \<le> M\<close>) 
  next
    case False
    have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
      by (smt b5 b6)
    thus ?thesis
      by (smt False mult_right_cancel mult_right_mono norm_ge_zero semiring_normalization_rules(29)) 
  qed
  thus \<open>\<exists>K. \<forall>x. \<parallel>(A\<^sup>\<dagger>) x\<parallel> \<le> \<parallel>x\<parallel> * K\<close>
    by auto
qed

proposition double_cadjoint:
  fixes U :: \<open>'a::chilbert_space \<Rightarrow> 'b::complex_inner\<close>
  assumes a1: "bounded_clinear U"
  shows "U\<^sup>\<dagger>\<^sup>\<dagger> = U"
  by (metis assms cadjoint_def cadjoint_is_cadjoint is_adjoint_sym is_cadjoint_unique someI_ex)

lemma cadjoint_id: \<open>(id::'a::complex_inner\<Rightarrow>'a)\<^sup>\<dagger> = id\<close>
  by (simp add: cadjoint_eqI id_def)

lemma scaleC_cadjoint:
  fixes A::"'a::chilbert_space \<Rightarrow> 'b::complex_inner"
  assumes "bounded_clinear A"
  shows \<open>(\<lambda>t. a *\<^sub>C (A t))\<^sup>\<dagger> = (\<lambda>s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s))\<close>
proof-
  have b3: \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>x, (\<lambda> t. a *\<^sub>C (A t)) y \<rangle>\<close>
    for x y
    by (simp add: assms cadjoint_univ_prop)

  have "((\<lambda>t. a *\<^sub>C A t)\<^sup>\<dagger>) b = cnj a *\<^sub>C (A\<^sup>\<dagger>) b"
    for b::'b
  proof-
    have "bounded_clinear (\<lambda>t. a *\<^sub>C A t)"
      by (simp add: assms bounded_clinear_const_scaleC)
    thus ?thesis
      by (metis (no_types) cadjoint_eqI b3) 
  qed
  thus ?thesis
    by blast
qed


lemma is_projection_on_is_cadjoint:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: \<open>is_projection_on \<pi> M\<close> and a2: \<open>closed_csubspace M\<close>
  shows \<open>is_cadjoint \<pi> \<pi>\<close>
proof -
  have \<open>cinner (x - \<pi> x) y = 0\<close> if \<open>y\<in>M\<close> for x y
    using a1 a2 is_projection_on_iff_orthog orthogonal_complement_orthoI that by blast
  then have \<open>cinner x y = cinner (\<pi> x) y\<close> if \<open>y\<in>M\<close> for x y
    by (metis cinner_diff_left eq_iff_diff_eq_0 that)
  moreover have \<open>cinner x y = cinner x (\<pi> y)\<close> if \<open>y\<in>M\<close> for x y
    using a1 is_projection_on_fixes_image that by fastforce
  ultimately have 1: \<open>cinner (\<pi> x) y = cinner x (\<pi> y)\<close> if \<open>y\<in>M\<close> for x y
    using that by metis

  have \<open>cinner (\<pi> x) y = 0\<close> if \<open>y \<in> orthogonal_complement M\<close> for x y
    by (meson a1 is_projection_on_in_image orthogonal_complement_orthoI' that)
  also have \<open>0 = cinner x (\<pi> y)\<close> if \<open>y \<in> orthogonal_complement M\<close> for x y
    by (metis a1 a2 cinner_zero_right closed_csubspace.subspace complex_vector.subspace_0 diff_zero is_projection_on_eqI that)
  finally have 2: \<open>cinner (\<pi> x) y = cinner x (\<pi> y)\<close> if \<open>y \<in> orthogonal_complement M\<close> for x y
    using that by simp

  from 1 2
  have \<open>cinner (\<pi> x) y = cinner x (\<pi> y)\<close> for x y
    by (smt (verit, ccfv_threshold) a1 a2 cinner_commute cinner_diff_left eq_iff_diff_eq_0 is_projection_on_iff_orthog orthogonal_complement_orthoI)
  then show ?thesis
    by (simp add: is_cadjoint_def)
qed

lemma is_projection_on_cadjoint:
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes \<open>is_projection_on \<pi> M\<close> and \<open>closed_csubspace M\<close>
  shows \<open>\<pi>\<^sup>\<dagger> = \<pi>\<close>
  using assms is_projection_on_is_cadjoint cadjoint_eqI is_cadjoint_def by blast

lemma projection_cadjoint:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>closed_csubspace M\<close>
  shows \<open>(projection M)\<^sup>\<dagger> = projection M\<close>
  using is_projection_on_cadjoint assms
  by (metis closed_csubspace.closed closed_csubspace.subspace csubspace_is_convex empty_iff orthog_proj_exists projection_is_projection_on) 

instance ccsubspace :: (chilbert_space) complete_orthomodular_lattice
proof
  show "inf x (- x) = bot"
    for x :: "'a ccsubspace"
    apply transfer
    by (simp add: closed_csubspace_def complex_vector.subspace_0 orthogonal_complement_zero_intersection)

  have \<open>t \<in> x +\<^sub>M orthogonal_complement x\<close>
    if a1: \<open>closed_csubspace x\<close>
    for t::'a and x
  proof-
    have e1: \<open>t = (projection x) t + (projection (orthogonal_complement x)) t\<close>
      by (simp add: that)
    have e2: \<open>(projection x) t \<in> x\<close>
      by (metis closed_csubspace.closed closed_csubspace.subspace csubspace_is_convex empty_iff orthog_proj_exists projection_in_image that)
    have e3: \<open>(projection (orthogonal_complement x)) t \<in> orthogonal_complement x\<close>
      by (metis add_diff_cancel_left' e1 orthogonal_complementI projection_orthogonal that)
    have "orthogonal_complement x \<subseteq> x +\<^sub>M orthogonal_complement x"
      by (simp add: closed_sum_right_subset complex_vector.subspace_0 that)
    thus ?thesis
      using \<open>closed_csubspace x\<close> 
        \<open>projection (orthogonal_complement x) t \<in> orthogonal_complement x\<close> \<open>projection x t \<in> x\<close>
        \<open>t = projection x t + projection (orthogonal_complement x) t\<close> in_mono 
        closed_sum_left_subset complex_vector.subspace_def
      by (metis closed_csubspace.subspace closed_subspace_closed_sum orthogonal_complement_closed_subspace) 
  qed  
  hence b1: \<open>x +\<^sub>M orthogonal_complement x = UNIV\<close>
    if a1: \<open>closed_csubspace x\<close>
    for x::\<open>'a set\<close>
    using that by blast
  show "sup x (- x) = top"
    for x :: "'a ccsubspace"
    apply transfer
    using b1 by auto
  show "- (- x) = x"
    for x :: "'a ccsubspace"
    apply transfer
    by (simp)

  show "- y \<le> - x"
    if "x \<le> y"
    for x :: "'a ccsubspace"
      and y :: "'a ccsubspace"
    using that apply transfer
    by simp 

  have c1: "x +\<^sub>M orthogonal_complement x \<inter> y \<subseteq> y"
    if "closed_csubspace x"
      and "closed_csubspace y"
      and "x \<subseteq> y"
    for x :: "'a set"
      and y :: "'a set"
    using that
    by (simp add: closed_sum_is_sup) 

  have c2: \<open>u \<in> x +\<^sub>M ((orthogonal_complement x) \<inter> y)\<close>
    if a1: "closed_csubspace x" and a2: "closed_csubspace y" and a3: "x \<subseteq> y" and x1: \<open>u \<in> y\<close>
    for x :: "'a set" and y :: "'a set"  and u
  proof-
    have d4: \<open>(projection x) u \<in> x\<close>
      by (metis a1 closed_csubspace_def csubspace_is_convex equals0D orthog_proj_exists projection_in_image)
    hence d2: \<open>(projection x) u \<in> y\<close>
      using a3 by auto
    have d1: \<open>csubspace y\<close>
      by (simp add: a2)
    have \<open>u - (projection x) u \<in> orthogonal_complement x\<close>
      by (simp add: a1 orthogonal_complementI projection_orthogonal)
    moreover have  \<open>u - (projection x) u \<in> y\<close>
      by (simp add: d1 d2 complex_vector.subspace_diff x1)      
    ultimately have d3: \<open>u - (projection x) u \<in> ((orthogonal_complement x) \<inter> y)\<close>
      by simp
    hence \<open>\<exists> v \<in> ((orthogonal_complement x) \<inter> y). u = (projection x) u + v\<close>
      by (metis d3 diff_add_cancel ordered_field_class.sign_simps(2))
    then obtain v where \<open>v \<in> ((orthogonal_complement x) \<inter> y)\<close> and \<open>u = (projection x) u + v\<close>
      by blast
    hence \<open>u \<in> x + ((orthogonal_complement x) \<inter> y)\<close>
      by (metis d4 set_plus_intro)
    thus ?thesis
      unfolding closed_sum_def
      using closure_subset by blast 
  qed

  have c3: "y \<subseteq> x +\<^sub>M ((orthogonal_complement x) \<inter> y)"
    if a1: "closed_csubspace x" and a2: "closed_csubspace y" and a3: "x \<subseteq> y"
    for x y :: "'a set"   
    using c2 a1 a2 a3 by auto 

  show "sup x (inf (- x) y) = y"
    if "x \<le> y"
    for x y :: "'a ccsubspace"
    using that apply transfer
    using c1 c3
    by (simp add: subset_antisym)

  show "x - y = inf x (- y)"
    for x y :: "'a ccsubspace"
    apply transfer
    by simp
qed

subsection \<open>More projections\<close>

text \<open>These lemmas logically belong in the "projections" section above but depend on lemmas developed later.\<close>

lemma is_projection_on_plus:
  assumes "\<And>x y. x:A \<Longrightarrow> y:B \<Longrightarrow> is_orthogonal x y"
  assumes \<open>closed_csubspace A\<close>
  assumes \<open>closed_csubspace B\<close>
  assumes \<open>is_projection_on \<pi>A A\<close>
  assumes \<open>is_projection_on \<pi>B B\<close>
  shows \<open>is_projection_on (\<lambda>x. \<pi>A x + \<pi>B x) (A +\<^sub>M B)\<close>
proof (rule is_projection_on_iff_orthog[THEN iffD2, rule_format])
  show clAB: \<open>closed_csubspace (A +\<^sub>M B)\<close>
    by (simp add: assms(2) assms(3) closed_subspace_closed_sum)
  fix h
  have 1: \<open>\<pi>A h + \<pi>B h \<in> A +\<^sub>M B\<close>
    by (meson clAB assms(2) assms(3) assms(4) assms(5) closed_csubspace_def closed_sum_left_subset closed_sum_right_subset complex_vector.subspace_def in_mono is_projection_on_in_image)

  have \<open>\<pi>A (\<pi>B h) = 0\<close>
    by (smt (verit, del_insts) assms(1) assms(2) assms(4) assms(5) cinner_eq_zero_iff is_cadjoint_def is_projection_on_in_image is_projection_on_is_cadjoint)
  then have \<open>h - (\<pi>A h + \<pi>B h) = (h - \<pi>B h) - \<pi>A (h - \<pi>B h)\<close>
    by (smt (verit) add.right_neutral add_diff_cancel_left' assms(2) assms(4) closed_csubspace.subspace complex_vector.subspace_diff diff_add_eq_diff_diff_swap diff_diff_add is_projection_on_iff_orthog orthog_proj_unique orthogonal_complement_closed_subspace)
  also have \<open>\<dots> \<in> orthogonal_complement A\<close>
    using assms(2) assms(4) is_projection_on_iff_orthog by blast
  finally have orthoA: \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement A\<close>
    by -

  have \<open>\<pi>B (\<pi>A h) = 0\<close>
    by (smt (verit, del_insts) assms(1) assms(3) assms(4) assms(5) cinner_eq_zero_iff is_cadjoint_def is_projection_on_in_image is_projection_on_is_cadjoint)
  then have \<open>h - (\<pi>A h + \<pi>B h) = (h - \<pi>A h) - \<pi>B (h - \<pi>A h)\<close>
    by (smt (verit) add.right_neutral add_diff_cancel assms(3) assms(5) closed_csubspace.subspace complex_vector.subspace_diff diff_add_eq_diff_diff_swap diff_diff_add is_projection_on_iff_orthog orthog_proj_unique orthogonal_complement_closed_subspace)
  also have \<open>\<dots> \<in> orthogonal_complement B\<close>
    using assms(3) assms(5) is_projection_on_iff_orthog by blast
  finally have orthoB: \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement B\<close>
    by -

  from orthoA orthoB
  have 2: \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement (A +\<^sub>M B)\<close>
    by (metis IntI assms(2) assms(3) closed_csubspace_def complex_vector.subspace_def de_morgan_orthogonal_complement_plus)

  from 1 2 show \<open>h - (\<pi>A h + \<pi>B h) \<in> orthogonal_complement (A +\<^sub>M B) \<and> \<pi>A h + \<pi>B h \<in> A +\<^sub>M B\<close>
    by simp
qed

lemma projection_plus:
  fixes A B :: "'a::chilbert_space set"
  assumes "\<And>x y. x:A \<Longrightarrow> y:B \<Longrightarrow> is_orthogonal x y"
  assumes \<open>closed_csubspace A\<close>
  assumes \<open>closed_csubspace B\<close>
  shows \<open>projection (A +\<^sub>M B) = (\<lambda>x. projection A x + projection B x)\<close>
proof -
  have \<open>is_projection_on (\<lambda>x. projection A x + projection B x) (A +\<^sub>M B)\<close>
    apply (rule is_projection_on_plus)
    using assms by auto
  then show ?thesis
    by (meson assms(2) assms(3) closed_csubspace.subspace closed_subspace_closed_sum csubspace_is_convex projection_eqI')
qed

lemma is_projection_on_insert:
  assumes ortho: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0"
  assumes \<open>is_projection_on \<pi> (closure (cspan S))\<close>
  assumes \<open>is_projection_on \<pi>a (cspan {a})\<close>
  shows "is_projection_on (\<lambda>x. \<pi>a x + \<pi> x) (closure (cspan (insert a S)))"
proof -
  from ortho
  have \<open>x \<in> cspan {a} \<Longrightarrow> y \<in> closure (cspan S) \<Longrightarrow> is_orthogonal x y\<close> for x y
    using is_orthogonal_cspan is_orthogonal_closure is_orthogonal_sym
    by (smt (verit, ccfv_threshold) empty_iff insert_iff)
  then have \<open>is_projection_on (\<lambda>x. \<pi>a x + \<pi> x) (cspan {a} +\<^sub>M closure (cspan S))\<close>
    apply (rule is_projection_on_plus)
    using assms by (auto simp add: closed_csubspace.intro)
  also have \<open>\<dots> = closure (cspan (insert a S))\<close>
    using closed_sum_cspan[where X=\<open>{a}\<close>] by simp
  finally show ?thesis
    by -
qed

lemma projection_insert:
  fixes a :: \<open>'a::chilbert_space\<close>
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0"
  shows "projection (closure (cspan (insert a S))) u
        = projection (cspan {a}) u + projection (closure (cspan S)) u"
  using is_projection_on_insert[where S=S, OF a1]
  by (metis (no_types, lifting) closed_closure closed_csubspace.intro closure_is_csubspace complex_vector.subspace_span csubspace_is_convex finite.intros(1) finite.intros(2) finite_cspan_closed_csubspace projection_eqI' projection_is_projection_on')

lemma projection_insert_finite:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0" and a2: "finite (S::'a::chilbert_space set)"
  shows "projection (cspan (insert a S)) u
        = projection (cspan {a}) u + projection (cspan S) u"
  using projection_insert
  by (metis a1 a2 closure_finite_cspan finite.insertI) 

subsection \<open>Canonical basis (\<open>onb_enum\<close>)\<close>

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>is_ortho_set\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>

class onb_enum = basis_enum + complex_inner +
  assumes is_orthonormal: "is_ortho_set (set canonical_basis)"
    and is_normal: "\<And>x. x \<in> (set canonical_basis) \<Longrightarrow> norm x = 1"

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>is_ortho_set\<close>, SOME \<^typ>\<open>'a::complex_inner set \<Rightarrow> bool\<close>)\<close>

lemma cinner_canonical_basis:
  assumes \<open>i < length (canonical_basis :: 'a::onb_enum list)\<close>
  assumes \<open>j < length (canonical_basis :: 'a::onb_enum list)\<close>
  shows \<open>cinner (canonical_basis!i :: 'a) (canonical_basis!j) = (if i=j then 1 else 0)\<close>
  by (metis assms(1) assms(2) distinct_canonical_basis is_normal is_ortho_set_def is_orthonormal nth_eq_iff_index_eq nth_mem of_real_1 power2_norm_eq_cinner power_one)

instance onb_enum \<subseteq> chilbert_space
proof
  show "convergent X"
    if "Cauchy X"
    for X :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>finite (set canonical_basis)\<close>
      by simp
    have \<open>Cauchy (\<lambda> n. \<langle> t, X n \<rangle>)\<close> for t
      by (simp add: bounded_clinear.Cauchy bounded_clinear_cinner_right that)
    hence \<open>convergent (\<lambda> n. \<langle> t, X n \<rangle>)\<close>
      for t
      by (simp add: Cauchy_convergent_iff)      
    hence \<open>\<forall> t\<in>set canonical_basis. \<exists> L. (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L\<close>
      by (simp add: convergentD)
    hence \<open>\<exists> L. \<forall> t\<in>set canonical_basis. (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
      by metis
    then obtain L where \<open>\<And> t. t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
      by blast
    define l where \<open>l = (\<Sum>t\<in>set canonical_basis. L t *\<^sub>C t)\<close>
    have x1: \<open>X n = (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)\<close>
      for n
      using onb_expansion_finite[where T = "set canonical_basis" and x = "X n"]
        \<open>finite (set canonical_basis)\<close> 
      by (smt is_generator_set is_normal is_orthonormal)

    have \<open>(\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close> 
      if r1: \<open>t\<in>set canonical_basis\<close>
      for t
    proof-
      have \<open>(\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
        using r1  \<open>\<And> t. t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
        by blast
      define f where \<open>f x = x *\<^sub>C t\<close> for x
      have \<open>isCont f r\<close>
        for r
        unfolding f_def
        by (simp add: bounded_clinear_scaleC_left clinear_continuous_at)
      hence \<open>(\<lambda> n. f \<langle> t, X n \<rangle>) \<longlonglongrightarrow> f (L t)\<close>
        using \<open>(\<lambda>n. \<langle>t, X n\<rangle>) \<longlonglongrightarrow> L t\<close> isCont_tendsto_compose by blast
      hence \<open>(\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close>
        unfolding f_def
        by simp
      thus ?thesis by blast
    qed
    hence \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t))
    \<longlonglongrightarrow>  (\<Sum>t\<in>set canonical_basis. L t *\<^sub>C t)\<close>
      using \<open>finite (set canonical_basis)\<close>
        tendsto_sum[where I = "set canonical_basis" and f = "\<lambda> t. \<lambda> n. \<langle>t, X n\<rangle> *\<^sub>C t"
          and a = "\<lambda> t. L t *\<^sub>C t"]
      by auto      
    hence x2: \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)) \<longlonglongrightarrow> l\<close>
      using l_def by blast 
    have \<open>X \<longlonglongrightarrow> l\<close>
      using x1 x2 by simp
    thus ?thesis 
      unfolding convergent_def by blast
  qed
qed

subsection \<open>Conjugate space\<close>

instantiation conjugate_space :: (complex_inner) complex_inner begin
lift_definition cinner_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> complex" is
  \<open>\<lambda>x y. cinner y x\<close>.
instance
  apply (intro_classes; transfer)
       apply (simp_all add: )
    apply (simp add: cinner_add_right)
  using cinner_ge_zero norm_eq_sqrt_cinner by auto
end

instance conjugate_space :: (chilbert_space) chilbert_space..

end
