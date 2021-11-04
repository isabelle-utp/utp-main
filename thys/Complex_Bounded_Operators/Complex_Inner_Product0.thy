(*  Based on HOL/Real_Vector_Spaces.thy by Brian Huffman
    Adapted to the complex case by Dominique Unruh *)

section \<open>\<open>Complex_Inner_Product0\<close> -- Inner Product Spaces and Gradient Derivative\<close>

theory Complex_Inner_Product0
  imports
    Complex_Main Complex_Vector_Spaces
    "HOL-Analysis.Inner_Product"
    "Complex_Bounded_Operators.Extra_Ordered_Fields"
begin

subsection \<open>Complex inner product spaces\<close>

text \<open>
  Temporarily relax type constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::open set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::dist \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::norm \<Rightarrow> real\<close>)\<close>

class complex_inner = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"
  assumes cinner_commute: "cinner x y = cnj (cinner y x)"
    and cinner_add_left: "cinner (x + y) z = cinner x z + cinner y z"
    and cinner_scaleC_left [simp]: "cinner (scaleC r x) y = (cnj r) * (cinner x y)"
    and cinner_ge_zero [simp]: "0 \<le> cinner x x"
    and cinner_eq_zero_iff [simp]: "cinner x x = 0 \<longleftrightarrow> x = 0"
    and norm_eq_sqrt_cinner: "norm x = sqrt (cmod (cinner x x))"
begin

lemma cinner_zero_left [simp]: "cinner 0 x = 0"
  using cinner_add_left [of 0 0 x] by simp

lemma cinner_minus_left [simp]: "cinner (- x) y = - cinner x y"
  using cinner_add_left [of x "- x" y]
  by (simp add: group_add_class.add_eq_0_iff)

lemma cinner_diff_left: "cinner (x - y) z = cinner x z - cinner y z"
  using cinner_add_left [of x "- y" z] by simp

lemma cinner_sum_left: "cinner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. cinner (f x) y)"
  by (cases "finite A", induct set: finite, simp_all add: cinner_add_left)

lemma call_zero_iff [simp]: "(\<forall>u. cinner x u = 0) \<longleftrightarrow> (x = 0)"
  by auto (use cinner_eq_zero_iff in blast)

text \<open>Transfer distributivity rules to right argument.\<close>

lemma cinner_add_right: "cinner x (y + z) = cinner x y + cinner x z"
  using cinner_add_left [of y z x]
  by (metis complex_cnj_add local.cinner_commute)

lemma cinner_scaleC_right [simp]: "cinner x (scaleC r y) = r * (cinner x y)"
  using cinner_scaleC_left [of r y x]
  by (metis complex_cnj_cnj complex_cnj_mult local.cinner_commute)

lemma cinner_zero_right [simp]: "cinner x 0 = 0"
  using cinner_zero_left [of x]
  by (metis (mono_tags, hide_lams) complex_cnj_zero local.cinner_commute)

lemma cinner_minus_right [simp]: "cinner x (- y) = - cinner x y"
  using cinner_minus_left [of y x]
  by (metis complex_cnj_minus local.cinner_commute)

lemma cinner_diff_right: "cinner x (y - z) = cinner x y - cinner x z"
  using cinner_diff_left [of y z x]
  by (metis complex_cnj_diff local.cinner_commute)

lemma cinner_sum_right: "cinner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. cinner x (f y))"
proof (subst cinner_commute)
  have "(\<Sum>y\<in>A. cinner (f y) x) = (\<Sum>y\<in>A. cinner (f y) x)" 
    by blast   
  hence "cnj (\<Sum>y\<in>A. cinner (f y) x) = cnj (\<Sum>y\<in>A. (cinner (f y) x))"
    by simp
  hence "cnj (cinner (sum f A) x) = (\<Sum>y\<in>A. cnj (cinner (f y) x))"
    by (simp add: cinner_sum_left)
  thus "cnj (cinner (sum f A) x) = (\<Sum>y\<in>A. (cinner x (f y)))"
    by (subst (2) cinner_commute)    
qed

lemmas cinner_add [algebra_simps] = cinner_add_left cinner_add_right
lemmas cinner_diff [algebra_simps]  = cinner_diff_left cinner_diff_right
lemmas cinner_scaleC = cinner_scaleC_left cinner_scaleC_right

(* text \<open>Legacy theorem names\<close>
lemmas cinner_left_distrib = cinner_add_left
lemmas cinner_right_distrib = cinner_add_right
lemmas cinner_distrib = cinner_left_distrib cinner_right_distrib *)

lemma cinner_gt_zero_iff [simp]: "0 < cinner x x \<longleftrightarrow> x \<noteq> 0"
  by (smt (verit) less_irrefl local.cinner_eq_zero_iff local.cinner_ge_zero order.not_eq_order_implies_strict)

(* In Inner_Product, we have
  lemma power2_norm_eq_cinner: "(norm x)\<^sup>2 = cinner x x"
The following are two ways of inserting the conversions between real and complex into this:
*)

lemma power2_norm_eq_cinner:
  shows "(complex_of_real (norm x))\<^sup>2 = (cinner x x)"
  by (smt (verit, del_insts) Im_complex_of_real Re_complex_of_real cinner_gt_zero_iff cinner_zero_right cmod_def complex_eq_0 complex_eq_iff less_complex_def local.norm_eq_sqrt_cinner of_real_power real_sqrt_abs real_sqrt_pow2_iff zero_complex.sel(1))

lemma power2_norm_eq_cinner':
  shows "(norm x)\<^sup>2 = Re (cinner x x)"
  by (metis Re_complex_of_real of_real_power power2_norm_eq_cinner)

text \<open>Identities involving real multiplication and division.\<close>

lemma cinner_mult_left: "cinner (of_complex m * a) b = cnj m * (cinner a b)"
  by (simp add: of_complex_def)

lemma cinner_mult_right: "cinner a (of_complex m * b) = m * (cinner a b)"
  by (metis complex_inner_class.cinner_scaleC_right scaleC_conv_of_complex)

lemma cinner_mult_left': "cinner (a * of_complex m) b = cnj m * (cinner a b)"
  by (metis cinner_mult_left mult.right_neutral mult_scaleC_right scaleC_conv_of_complex)

lemma cinner_mult_right': "cinner a (b * of_complex m) = (cinner a b) * m"
  by (simp add: complex_inner_class.cinner_scaleC_right of_complex_def)

(* In Inner_Product, we have
lemma Cauchy_Schwarz_ineq:
  "(cinner x y)\<^sup>2 \<le> cinner x x * cinner y y"
The following are two ways of inserting the conversions between real and complex into this:
*)

lemma Cauchy_Schwarz_ineq:
  "(cinner x y) * (cinner y x) \<le> cinner x x * cinner y y"
proof (cases)
  assume "y = 0"
  thus ?thesis by simp
next
  assume y: "y \<noteq> 0"
  have [simp]: "cnj (cinner y y) = cinner y y" for y
    by (metis cinner_commute)
  define r where "r = cnj (cinner x y) / cinner y y"
  have "0 \<le> cinner (x - scaleC r y) (x - scaleC r y)"
    by (rule cinner_ge_zero)
  also have "\<dots> = cinner x x - r * cinner x y - cnj r * cinner y x + r * cnj r * cinner y y"
    unfolding cinner_diff_left cinner_diff_right cinner_scaleC_left cinner_scaleC_right
    by (smt (z3) cancel_comm_monoid_add_class.diff_cancel cancel_comm_monoid_add_class.diff_zero complex_cnj_divide group_add_class.diff_add_cancel local.cinner_commute local.cinner_eq_zero_iff local.cinner_scaleC_left mult.assoc mult.commute mult_eq_0_iff nonzero_eq_divide_eq r_def y)
  also have "\<dots> = cinner x x - cinner y x * cnj r"
    unfolding r_def by auto
  also have "\<dots> = cinner x x - cinner x y * cnj (cinner x y) / cinner y y"
    unfolding r_def
    by (metis complex_cnj_divide local.cinner_commute mult.commute times_divide_eq_left)
  finally have "0 \<le> cinner x x - cinner x y * cnj (cinner x y) / cinner y y" .
  hence "cinner x y * cnj (cinner x y) / cinner y y \<le> cinner x x"
    by (simp add: le_diff_eq)
  thus "cinner x y * cinner y x \<le> cinner x x * cinner y y"
    by (metis cinner_gt_zero_iff local.cinner_commute nice_ordered_field_class.pos_divide_le_eq y)
qed


lemma Cauchy_Schwarz_ineq2:
  shows "norm (cinner x y) \<le> norm x * norm y"
proof (rule power2_le_imp_le)
  have "(norm (cinner x y))^2 = Re (cinner x y * cinner y x)"
    by (metis (full_types) Re_complex_of_real complex_norm_square local.cinner_commute)
  also have "\<dots> \<le> Re (cinner x x * cinner y y)"
    using Cauchy_Schwarz_ineq by (rule Re_mono)
  also have "\<dots> = Re (complex_of_real ((norm x)^2) * complex_of_real ((norm y)^2))"
    by (simp add: power2_norm_eq_cinner)
  also have "\<dots> = (norm x * norm y)\<^sup>2"
    by (simp add: power_mult_distrib)
  finally show "(cmod (cinner x y))^2 \<le> (norm x * norm y)\<^sup>2" .
  show "0 \<le> norm x * norm y"
    by (simp add: local.norm_eq_sqrt_cinner)
qed

(* The following variant does not hold in the complex case: *)
(* lemma norm_cauchy_schwarz: "cinner x y \<le> norm x * norm y"
  using Cauchy_Schwarz_ineq2 [of x y] by auto *)

subclass complex_normed_vector
proof
  fix a :: complex and r :: real and x y :: 'a
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_eq_sqrt_cinner by simp
  show "norm (x + y) \<le> norm x + norm y"
  proof (rule power2_le_imp_le)
    have "Re (cinner x y) \<le> cmod (cinner x y)"
      if "\<And>x. Re x \<le> cmod x" and
        "\<And>x y. x \<le> y \<Longrightarrow> complex_of_real x \<le> complex_of_real y"
      using that by simp
    hence a1: "2 * Re (cinner x y) \<le> 2 * cmod (cinner x y)"
      if "\<And>x. Re x \<le> cmod x" and
        "\<And>x y. x \<le> y \<Longrightarrow> complex_of_real x \<le> complex_of_real y"
      using that by simp
    have "cinner x y + cinner y x = complex_of_real (2 * Re (cinner x y))"
      by (metis complex_add_cnj local.cinner_commute)
    also have "\<dots> \<le> complex_of_real (2 * cmod (cinner x y))"
      using complex_Re_le_cmod complex_of_real_mono a1
      by blast      
    also have "\<dots> = 2 * abs (cinner x y)"
      unfolding abs_complex_def by simp
    also have "\<dots> \<le> 2 * complex_of_real (norm x) * complex_of_real (norm y)"
      using Cauchy_Schwarz_ineq2 unfolding abs_complex_def by auto
    finally have xyyx: "cinner x y + cinner y x \<le> complex_of_real (2 * norm x * norm y)" 
      by auto
    have "complex_of_real ((norm (x + y))\<^sup>2) = cinner (x+y) (x+y)"
      by (simp add: power2_norm_eq_cinner)
    also have "\<dots> = cinner x x + cinner x y + cinner y x + cinner y y"
      by (simp add: cinner_add)
    also have "\<dots> = complex_of_real ((norm x)\<^sup>2) + complex_of_real ((norm y)\<^sup>2) + cinner x y + cinner y x"
      by (simp add: power2_norm_eq_cinner)
    also have "\<dots> \<le> complex_of_real ((norm x)\<^sup>2) + complex_of_real ((norm y)\<^sup>2) + complex_of_real (2 * norm x * norm y)"
      using xyyx by auto
    also have "\<dots> = complex_of_real ((norm x + norm y)\<^sup>2)"
      unfolding power2_sum by auto
    finally show "(norm (x + y))\<^sup>2 \<le> (norm x + norm y)\<^sup>2"
      using complex_of_real_mono_iff by blast
    show "0 \<le> norm x + norm y"
      unfolding norm_eq_sqrt_cinner by simp
  qed
  show norm_scaleC: "norm (a *\<^sub>C x) = cmod a * norm x" for a
  proof (rule power2_eq_imp_eq)
    show "(norm (a *\<^sub>C x))\<^sup>2 = (cmod a * norm x)\<^sup>2"
      by (simp_all add: norm_eq_sqrt_cinner norm_mult power2_eq_square)
    show "0 \<le> norm (a *\<^sub>C x)"
      by (simp_all add: norm_eq_sqrt_cinner)     
    show "0 \<le> cmod a * norm x"
      by (simp_all add: norm_eq_sqrt_cinner)     
  qed
  show "norm (r *\<^sub>R x) = \<bar>r\<bar> * norm x"
    unfolding scaleR_scaleC norm_scaleC by auto
qed

end

(* Does not hold in the complex case *)
(* lemma csquare_bound_lemma:
  fixes x :: complex
  shows "x < (1 + x) * (1 + x)" *)

lemma csquare_continuous:
  fixes e :: real
  shows "e > 0 \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>y. cmod (y - x) < d \<longrightarrow> cmod (y * y - x * x) < e)"
  using isCont_power[OF continuous_ident, of x, unfolded isCont_def LIM_eq, rule_format, of e 2]
  by (force simp add: power2_eq_square)

lemma cnorm_le: "norm x \<le> norm y \<longleftrightarrow> cinner x x \<le> cinner y y"
  by (smt (verit) complex_of_real_mono_iff norm_eq_sqrt_cinner norm_ge_zero of_real_power power2_norm_eq_cinner real_sqrt_le_mono real_sqrt_pow2)

lemma cnorm_lt: "norm x < norm y \<longleftrightarrow> cinner x x < cinner y y"
  by (meson cnorm_le less_le_not_le)

lemma cnorm_eq: "norm x = norm y \<longleftrightarrow> cinner x x = cinner y y"
  by (metis norm_eq_sqrt_cinner power2_norm_eq_cinner)

lemma cnorm_eq_1: "norm x = 1 \<longleftrightarrow> cinner x x = 1"
  by (metis cinner_ge_zero complex_of_real_cmod norm_eq_sqrt_cinner norm_one of_real_1 real_sqrt_eq_iff real_sqrt_one)

lemma cinner_divide_left:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "cinner (a / of_complex m) b = (cinner a b) / cnj m"
  by (metis cinner_mult_left' complex_cnj_inverse divide_inverse of_complex_inverse ordered_field_class.sign_simps(33))

lemma cinner_divide_right:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "cinner a (b / of_complex m) = (cinner a b) / m"
  by (metis cinner_mult_right' divide_inverse of_complex_inverse)

text \<open>
  Re-enable constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
  \<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniform_space \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::real_normed_vector \<Rightarrow> real\<close>)\<close>


lemma bounded_sesquilinear_cinner:
  "bounded_sesquilinear (cinner::'a::complex_inner \<Rightarrow> 'a \<Rightarrow> complex)"
proof
  fix x y z :: 'a and r :: complex
  show "cinner (x + y) z = cinner x z + cinner y z"
    by (rule cinner_add_left)
  show "cinner x (y + z) = cinner x y + cinner x z"
    by (rule cinner_add_right)
  show "cinner (scaleC r x) y = scaleC (cnj r) (cinner x y)"
    unfolding complex_scaleC_def by (rule cinner_scaleC_left)
  show "cinner x (scaleC r y) = scaleC r (cinner x y)"
    unfolding complex_scaleC_def by (rule cinner_scaleC_right)
  have "\<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * 1"
    by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
  thus "\<exists>K. \<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * K"
    by metis
qed

lemmas tendsto_cinner [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas isCont_cinner [simp] =
  bounded_bilinear.isCont [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas has_derivative_cinner [derivative_intros] =
  bounded_bilinear.FDERIV [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas bounded_antilinear_cinner_left =
  bounded_sesquilinear.bounded_antilinear_left [OF bounded_sesquilinear_cinner]

lemmas bounded_clinear_cinner_right =
  bounded_sesquilinear.bounded_clinear_right [OF bounded_sesquilinear_cinner]

lemmas bounded_antilinear_cinner_left_comp = bounded_antilinear_cinner_left[THEN bounded_antilinear_o_bounded_clinear]

lemmas bounded_clinear_cinner_right_comp = bounded_clinear_cinner_right[THEN bounded_clinear_compose]

lemmas has_derivative_cinner_right [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_clinear_cinner_right[THEN bounded_clinear.bounded_linear]]

lemmas has_derivative_cinner_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_antilinear_cinner_left[THEN bounded_antilinear.bounded_linear]]

lemma differentiable_cinner [simp]:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable at x within s \<Longrightarrow> (\<lambda>x. cinner (f x) (g x)) differentiable at x within s"
  unfolding differentiable_def by (blast intro: has_derivative_cinner)


subsection \<open>Class instances\<close>

instantiation complex :: complex_inner
begin

definition cinner_complex_def [simp]: "cinner x y = cnj x * y"

instance
proof
  fix x y z r :: complex
  show "cinner x y = cnj (cinner y x)"
    unfolding cinner_complex_def by auto
  show "cinner (x + y) z = cinner x z + cinner y z"
    unfolding cinner_complex_def
    by (simp add: ring_class.ring_distribs(2))
  show "cinner (scaleC r x) y = cnj r * cinner x y"
    unfolding cinner_complex_def complex_scaleC_def by simp
  show "0 \<le> cinner x x"
    by simp
  show "cinner x x = 0 \<longleftrightarrow> x = 0"
    unfolding cinner_complex_def by simp
  have "cmod (Complex x1 x2) = sqrt (cmod (cinner (Complex x1 x2) (Complex x1 x2)))"
    for x1 x2
    unfolding cinner_complex_def complex_cnj complex_mult complex_norm
    by (simp add: power2_eq_square)
  thus "norm x = sqrt (cmod (cinner x x))"
    by (cases x, hypsubst_thin) 
qed

end

lemma
  shows complex_inner_1_left[simp]: "cinner 1 x = x"
    and complex_inner_1_right[simp]: "cinner x 1 = cnj x"
  by simp_all

(* No analogous to \<open>instantiation complex :: real_inner\<close> or to
lemma complex_inner_1 [simp]: "inner 1 x = Re x"
lemma complex_inner_1_right [simp]: "inner x 1 = Re x"
lemma complex_inner_i_left [simp]: "inner \<i> x = Im x"
lemma complex_inner_i_right [simp]: "inner x \<i> = Im x"
 *)

lemma cdot_square_norm: "cinner x x = complex_of_real ((norm x)\<^sup>2)"
  by (metis Im_complex_of_real Re_complex_of_real cinner_ge_zero complex_eq_iff less_eq_complex_def power2_norm_eq_cinner' zero_complex.simps(2))

lemma cnorm_eq_square: "norm x = a \<longleftrightarrow> 0 \<le> a \<and> cinner x x = complex_of_real (a\<^sup>2)"
  by (metis cdot_square_norm norm_ge_zero of_real_eq_iff power2_eq_iff_nonneg)

lemma cnorm_le_square: "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and> cinner x x \<le> complex_of_real (a\<^sup>2)"
  by (smt (verit) cdot_square_norm complex_of_real_mono_iff norm_ge_zero power2_le_imp_le)

lemma cnorm_ge_square: "norm x \<ge> a \<longleftrightarrow> a \<le> 0 \<or> cinner x x \<ge> complex_of_real (a\<^sup>2)"
  by (smt (verit, best) antisym_conv cnorm_eq_square cnorm_le_square complex_of_real_nn_iff nn_comparable zero_le_power2)

lemma norm_lt_square: "norm x < a \<longleftrightarrow> 0 < a \<and> cinner x x < complex_of_real (a\<^sup>2)"
  by (meson cnorm_ge_square cnorm_le_square less_le_not_le)

lemma norm_gt_square: "norm x > a \<longleftrightarrow> a < 0 \<or> cinner x x > complex_of_real (a\<^sup>2)"
  by (smt (verit, ccfv_SIG) cdot_square_norm complex_of_real_strict_mono_iff norm_ge_zero power2_eq_imp_eq power_mono)

text\<open>Dot product in terms of the norm rather than conversely.\<close>

lemmas cinner_simps = cinner_add_left cinner_add_right cinner_diff_right cinner_diff_left
  cinner_scaleC_left cinner_scaleC_right

(* Analogue to both dot_norm and dot_norm_neg *)
lemma cdot_norm: "cinner x y = ((norm (x+y))\<^sup>2 - (norm (x-y))\<^sup>2 - \<i> * (norm (x + \<i> *\<^sub>C y))\<^sup>2 + \<i> * (norm (x - \<i> *\<^sub>C y))\<^sup>2) / 4"
  unfolding power2_norm_eq_cinner
  by (simp add: power2_norm_eq_cinner cinner_add_left cinner_add_right 
      cinner_diff_left cinner_diff_right ring_distribs)

lemma of_complex_inner_1 [simp]: 
  "cinner (of_complex x) (1 :: 'a :: {complex_inner, complex_normed_algebra_1}) = cnj x"
  by (metis Complex_Inner_Product0.complex_inner_1_right cinner_complex_def cinner_mult_left complex_cnj_one norm_one of_complex_def power2_norm_eq_cinner scaleC_conv_of_complex)

lemma summable_of_complex_iff: 
  "summable (\<lambda>x. of_complex (f x) :: 'a :: {complex_normed_algebra_1,complex_inner}) \<longleftrightarrow> summable f"
proof
  assume *: "summable (\<lambda>x. of_complex (f x) :: 'a)"
  have "bounded_clinear (cinner (1::'a))"
    by (rule bounded_clinear_cinner_right)
  then interpret bounded_linear "\<lambda>x::'a. cinner 1 x"
    by (rule bounded_clinear.bounded_linear)
  from summable [OF *] show "summable f"
    apply (subst (asm) cinner_commute) by simp
next
  assume sum: "summable f"
  thus "summable (\<lambda>x. of_complex (f x) :: 'a)"
    by (rule summable_of_complex)
qed

subsection \<open>Gradient derivative\<close>

definition\<^marker>\<open>tag important\<close>
  cgderiv :: "['a::complex_inner \<Rightarrow> complex, 'a, 'a] \<Rightarrow> bool"
  ("(cGDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where
    (* Must be "cinner D" not "\<lambda>h. cinner h D", otherwise not even "cGDERIV id x :> 1" holds *)
    "cGDERIV f x :> D \<longleftrightarrow> FDERIV f x :> cinner D"

lemma cgderiv_deriv [simp]: "cGDERIV f x :> D \<longleftrightarrow> DERIV f x :> cnj D"
  by (simp only: cgderiv_def has_field_derivative_def cinner_complex_def[THEN ext])

lemma cGDERIV_DERIV_compose:
  assumes "cGDERIV f x :> df" and "DERIV g (f x) :> cnj dg"
  shows "cGDERIV (\<lambda>x. g (f x)) x :> scaleC dg df"
proof (insert assms)
  show "cGDERIV (\<lambda>x. g (f x)) x :> dg *\<^sub>C df"
    if "cGDERIV f x :> df"
      and "(g has_field_derivative cnj dg) (at (f x))"
    unfolding cgderiv_def has_field_derivative_def cinner_scaleC_left complex_cnj_cnj
    using that
    by (simp add: cgderiv_def has_derivative_compose has_field_derivative_imp_has_derivative) 

qed

(* Not specific to complex/real *)
(* lemma has_derivative_subst: "\<lbrakk>FDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> FDERIV f x :> d" *)

lemma cGDERIV_subst: "\<lbrakk>cGDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> cGDERIV f x :> d"
  by simp

lemma cGDERIV_const: "cGDERIV (\<lambda>x. k) x :> 0"
  unfolding cgderiv_def cinner_zero_left[THEN ext] by (rule has_derivative_const)

lemma cGDERIV_add:
  "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. f x + g x) x :> df + dg"
  unfolding cgderiv_def cinner_add_left[THEN ext] by (rule has_derivative_add)

lemma cGDERIV_minus:
  "cGDERIV f x :> df \<Longrightarrow> cGDERIV (\<lambda>x. - f x) x :> - df"
  unfolding cgderiv_def cinner_minus_left[THEN ext] by (rule has_derivative_minus)

lemma cGDERIV_diff:
  "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. f x - g x) x :> df - dg"
  unfolding cgderiv_def cinner_diff_left by (rule has_derivative_diff)

lemma cGDERIV_scaleC:
  "\<lbrakk>DERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. scaleC (f x) (g x)) x
      :> (scaleC (cnj (f x)) dg + scaleC (cnj df) (cnj (g x)))"
  unfolding cgderiv_def has_field_derivative_def cinner_add_left cinner_scaleC_left
  apply (rule has_derivative_subst)
   apply (erule (1) has_derivative_scaleC)
  by (simp add: ac_simps)

lemma GDERIV_mult:
  "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. f x * g x) x :> cnj (f x) *\<^sub>C dg + cnj (g x) *\<^sub>C df"
  unfolding cgderiv_def
  apply (rule has_derivative_subst)
   apply (erule (1) has_derivative_mult)
  apply (rule ext)
  by (simp add: cinner_add ac_simps)

lemma cGDERIV_inverse:
  "\<lbrakk>cGDERIV f x :> df; f x \<noteq> 0\<rbrakk>
     \<Longrightarrow> cGDERIV (\<lambda>x. inverse (f x)) x :> - cnj ((inverse (f x))\<^sup>2) *\<^sub>C df"
  by (metis DERIV_inverse cGDERIV_DERIV_compose complex_cnj_cnj complex_cnj_minus numerals(2))

(* Don't know if this holds: *)
(* lemma cGDERIV_norm:
  assumes "x \<noteq> 0" shows "cGDERIV (\<lambda>x. norm x) x :> sgn x" 
*)


lemma has_derivative_norm[derivative_intros]:
  fixes x :: "'a::complex_inner"
  assumes "x \<noteq> 0" 
  shows "(norm has_derivative (\<lambda>h. Re (cinner (sgn x) h))) (at x)"
  thm has_derivative_norm
proof -
  have Re_pos: "0 < Re (cinner x x)"
    using assms 
    by (metis Re_strict_mono cinner_gt_zero_iff zero_complex.simps(1))
  have Re_plus_Re: "Re (cinner x y) + Re (cinner y x) = 2 * Re (cinner x y)" 
    for x y :: 'a
    by (metis cinner_commute cnj.simps(1) mult_2_right semiring_normalization_rules(7))
  have norm: "norm x = sqrt (Re (cinner x x))" for x :: 'a
    apply (subst norm_eq_sqrt_cinner, subst cmod_Re)
    using cinner_ge_zero by auto
  have v2:"((\<lambda>x. sqrt (Re (cinner x x))) has_derivative
          (\<lambda>xa. (Re (cinner x xa) + Re (cinner xa x)) * (inverse (sqrt (Re (cinner x x))) / 2))) (at x)" 
    by (rule derivative_eq_intros | simp add: Re_pos)+
  have v1: "((\<lambda>x. sqrt (Re (cinner x x))) has_derivative (\<lambda>y. Re (cinner x y) / sqrt (Re (cinner x x)))) (at x)"
    if "((\<lambda>x. sqrt (Re (cinner x x))) has_derivative (\<lambda>xa. Re (cinner x xa) * inverse (sqrt (Re (cinner x x))))) (at x)"
    using that apply (subst divide_real_def)
    by simp
  have \<open>(norm has_derivative (\<lambda>y. Re (cinner x y) / norm x)) (at x)\<close>
    using v2
    apply (auto simp: Re_plus_Re norm [abs_def])
    using v1 by blast
  then show ?thesis
    by (auto simp: power2_eq_square sgn_div_norm scaleR_scaleC)
qed


bundle cinner_syntax begin
notation cinner (infix "\<bullet>\<^sub>C" 70)
end

bundle no_cinner_syntax begin
no_notation cinner (infix "\<bullet>\<^sub>C" 70)
end

end
