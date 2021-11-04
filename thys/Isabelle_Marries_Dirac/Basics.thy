section \<open>Basic Results\<close>

theory Basics
imports
  HOL.Set_Interval
  HOL.Semiring_Normalization
  HOL.Real_Vector_Spaces
  HOL.Power
  HOL.Complex
  Jordan_Normal_Form.Jordan_Normal_Form
begin



subsection \<open>Basic Set-Theoretic Results\<close>

lemma set_2_atLeast0 [simp]: "{0..<2::nat} = {0,1}" by auto

lemma set_2: "{..<2::nat} = {0,1}" by auto

lemma set_4_atLeast0 [simp]:"{0..<4::nat} = {0,1,2,3}" by auto

lemma set_4: "{..<4::nat} = {0,1,2,3}" by auto

lemma set_4_disj [simp]: 
  fixes i:: nat
  assumes "i < 4"
  shows "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" 
  using assms by auto

lemma set_8_atLeast0 [simp]: "{0..<8::nat} = {0,1,2,3,4,5,6,7}" by auto

lemma index_is_2 [simp]: "\<forall>i::nat. i \<noteq> Suc 0 \<longrightarrow> i \<noteq> 3 \<longrightarrow> 0 < i \<longrightarrow> i < 4 \<longrightarrow> i = 2" by simp

lemma index_sl_four [simp]: "\<forall>i::nat. i < 4 \<longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by auto


subsection \<open>Basic Arithmetic Results\<close>

lemma index_div_eq [simp]:
  fixes i::nat
  shows "i\<in>{a*b..<(a+1)*b} \<Longrightarrow> i div b = a"
proof-
  fix i::nat 
  assume a:"i\<in>{a*b..<(a+1)*b}"
  then have "i div b \<ge> a"
    by (metis Suc_eq_plus1 atLeastLessThan_iff le_refl semiring_normalization_rules(7) split_div')
  moreover have "i div b < a+1"
    using a by (simp add: less_mult_imp_div_less)
  ultimately show "i div b = a" by simp
qed

lemma index_mod_eq [simp]:
  fixes i::nat
  shows "i\<in>{a*b..<(a+1)*b} \<Longrightarrow> i mod b = i-a*b"
  by (simp add: modulo_nat_def)

lemma sqr_of_cmod_of_prod:
  shows "(cmod (z1 * z2))\<^sup>2 = (cmod z1)\<^sup>2 * (cmod z2)\<^sup>2"
  by (simp add: norm_mult power_mult_distrib)

lemma less_power_add_imp_div_less [simp]:
  fixes i m n:: nat
  assumes "i < 2^(m+n)"
  shows "i div 2^n < 2^m"
  using assms by (simp add: less_mult_imp_div_less power_add)

lemma div_mult_mod_eq_minus:
  fixes i j:: nat
  shows "(i div 2^n) * 2^n + i mod 2^n - (j div 2^n) * 2^n - j mod 2^n = i - j"
  by (simp add: div_mult_mod_eq algebra_simps)

lemma neq_imp_neq_div_or_mod:
  fixes i j:: nat
  assumes "i \<noteq> j"
  shows "i div 2^n \<noteq> j div 2^n \<or> i mod 2^n \<noteq> j mod 2^n"
  using assms div_mult_mod_eq_minus
  by (metis add.right_neutral cancel_div_mod_rules(2))
  
lemma index_one_mat_div_mod:
  assumes "i < 2^(m+n)" and "j < 2^(m+n)"
  shows "((1\<^sub>m(2^m) $$ (i div 2^n, j div 2^n))::complex) * 1\<^sub>m(2^n) $$ (i mod 2^n, j mod 2^n) = 1\<^sub>m(2^(m+n)) $$ (i, j)"
proof (cases "i = j")
  case True
  then show ?thesis by(simp add: assms)
next
  case c1:False
  have "i div 2^n \<noteq> j div 2^n \<or> i mod 2^n \<noteq> j mod 2^n"
    using c1 neq_imp_neq_div_or_mod by simp 
  then have "1\<^sub>m (2^m) $$ (i div 2^n, j div 2^n) = 0 \<or> 1\<^sub>m (2^n) $$ (i mod 2^n, j mod 2^n) = 0"
    using assms by simp
  then show ?thesis
    using assms by (simp add: c1)
qed

lemma sqr_of_sqrt_2 [simp]:
  fixes z:: "complex"
  shows "z * 2 / (complex_of_real (sqrt 2) * complex_of_real (sqrt 2)) = z"
  by(metis nonzero_mult_div_cancel_right norm_numeral of_real_numeral of_real_power power2_eq_square 
real_norm_def real_sqrt_abs real_sqrt_power zero_neq_numeral)

lemma two_div_sqrt_two [simp]:
  shows "2 * complex_of_real (sqrt (1/2)) = complex_of_real (sqrt 2)"
    apply(auto simp add: real_sqrt_divide algebra_simps)
    by (metis divide_eq_0_iff nonzero_mult_div_cancel_left sqr_of_sqrt_2)

lemma two_div_sqr_of_cmd_sqrt_two [simp]: 
  shows "2 * (cmod (1 / complex_of_real (sqrt 2)))\<^sup>2 = 1" 
  using cmod_def by (simp add: power_divide)

lemma two_div_two [simp]: 
  shows "2 div Suc (Suc 0) = 1" by simp

lemma two_mod_two [simp]: 
  shows "2 mod Suc (Suc 0) = 0" by (simp add: numeral_2_eq_2)

lemma three_div_two [simp]: 
  shows "3 div Suc (Suc 0) = 1" by (simp add: numeral_3_eq_3)

lemma three_mod_two [simp]: 
  shows "3 mod Suc (Suc 0) = 1" by (simp add: mod_Suc numeral_3_eq_3)


subsection \<open>Basic Results on Matrices\<close>

lemma index_matrix_prod [simp]:
  assumes "i < dim_row A" and "j < dim_col B" and "dim_col A = dim_row B"
  shows "(A * B) $$ (i,j) = (\<Sum>k<dim_row B. (A $$ (i,k)) * (B $$ (k,j)))"
  using assms 
    apply(simp add: scalar_prod_def atLeast0LessThan).


subsection \<open>Basic Results on Sums\<close>

lemma sum_insert [simp]:
  assumes "x \<notin> F" and "finite F"
  shows "(\<Sum>y\<in>insert x F. P y) = (\<Sum>y\<in>F. P y) + P x"
  using assms insert_def by(simp add: add.commute)

lemma sum_of_index_diff [simp]:
  fixes f:: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<in>{a..<a+b}. f(i-a)) = (\<Sum>i\<in>{..<b}. f(i))"
proof (induction b)
  case 0
  then show ?case by simp
next
  case (Suc b)
  then show ?case by simp
qed


subsection \<open>Basic Results Involving the Exponential Function.\<close>

lemma exp_of_real_cnj:
  fixes x ::real
  shows "cnj (exp (\<i> * x)) = exp (-(\<i> * x))"
proof
  show "Re (cnj (exp (\<i> * x))) = Re (exp (-(\<i> * x)))"
    using Re_exp by simp
  show "Im (cnj (exp (\<i> * x))) = Im (exp (-(\<i> * x)))"
    using Im_exp by simp
qed

lemma exp_of_real_cnj2:
  fixes x ::real
  shows "cnj (exp (-(\<i> * x))) = exp (\<i> * x)"
proof
  show "Re (cnj (exp (-(\<i> * x)))) = Re (exp (\<i> * x))"
    using Re_exp by simp
  show "Im (cnj (exp (-(\<i> * x)))) = Im (exp (\<i> * x))"
    using Im_exp by simp
qed

lemma exp_of_half_pi: 
  fixes x:: real
  assumes "x = pi/2"
  shows "exp (\<i> * complex_of_real x) = \<i>"
  using assms cis_conv_exp cis_pi_half by fastforce

lemma exp_of_minus_half_pi: 
  fixes x:: real
  assumes "x = pi/2"
  shows "exp (-(\<i> * complex_of_real x)) = -\<i>"
  using assms cis_conv_exp cis_minus_pi_half by fastforce

lemma exp_of_real:
  fixes x:: real
  shows "exp (\<i> * x) = cos x + \<i> * (sin x)"
proof
  show "Re (exp (\<i> * x)) = Re ((cos x) + \<i> * (sin x))"
    using Re_exp by simp
  show "Im (exp (\<i> * x)) = Im ((cos x) + \<i> * (sin x))"
    using Im_exp by simp
qed

lemma exp_of_real_inv:
  fixes x:: real
  shows "exp (-(\<i> * x)) = cos x - \<i> * (sin x)"
proof
  show "Re (exp (-(\<i> * x))) = Re ((cos x) - \<i> * (sin x))"
    using Re_exp by simp
  show "Im (exp (-(\<i> * x))) = Im ((cos x) - \<i> * (sin x))"
    using Im_exp by simp
qed


subsection \<open>Basic Results with Trigonometric Functions.\<close>

subsubsection \<open>Basic Inequalities\<close>

lemma sin_squared_le_one:
  fixes x:: real
  shows "(sin x)\<^sup>2 \<le> 1"
  using abs_sin_le_one abs_square_le_1 by blast

lemma cos_squared_le_one:
  fixes x:: real
  shows "(cos x)\<^sup>2 \<le> 1"
  using abs_cos_le_one abs_square_le_1 by blast

subsubsection \<open>Basic Equalities\<close>

lemma sin_of_quarter_pi:
  fixes x:: real
  assumes "x = pi/2"
  shows "sin (x/2) = (sqrt 2)/2"
  by (auto simp add: assms sin_45)

lemma cos_of_quarter_pi:
  fixes x:: real
  assumes "x = pi/2"
  shows "cos (x/2) = (sqrt 2)/2"
  by (auto simp add: assms cos_45)

end