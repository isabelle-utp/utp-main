(*
  File:     More_Algebraic_Numbers_HLW.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>More facts about algebraic numbers\<close>
theory More_Algebraic_Numbers_HLW
  imports "Algebraic_Numbers.Algebraic_Numbers"
begin

subsection \<open>Miscellaneous\<close>

(* TODO: Move! All of this belongs in Algebraic_Numbers *)

lemma in_Ints_imp_algebraic [simp, intro]: "x \<in> \<int> \<Longrightarrow> algebraic x"
  by (intro algebraic_int_imp_algebraic int_imp_algebraic_int)

lemma in_Rats_imp_algebraic [simp, intro]: "x \<in> \<rat> \<Longrightarrow> algebraic x"
  by (auto elim!: Rats_cases' intro: algebraic_div)

lemma algebraic_uminus_iff [simp]: "algebraic (-x) \<longleftrightarrow> algebraic x"
  using algebraic_uminus[of x] algebraic_uminus[of "-x"] by auto

lemma algebraic_0 [simp]: "algebraic (0 :: 'a :: field_char_0)"
  and algebraic_1 [simp]: "algebraic (1 :: 'a :: field_char_0)"
  by auto  

lemma algebraic_sum [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> algebraic (f x)) \<Longrightarrow> algebraic (sum f A)"
  by (induction A rule: infinite_finite_induct) (auto intro!: algebraic_plus)

lemma algebraic_prod [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> algebraic (f x)) \<Longrightarrow> algebraic (prod f A)"
  by (induction A rule: infinite_finite_induct) (auto intro!: algebraic_times)

lemma algebraic_sum_list [intro]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> algebraic x) \<Longrightarrow> algebraic (sum_list xs)"
  by (induction xs) (auto intro!: algebraic_plus)

lemma algebraic_prod_list [intro]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> algebraic x) \<Longrightarrow> algebraic (prod_list xs)"
  by (induction xs) (auto intro!: algebraic_times)

lemma algebraic_sum_mset [intro]:
  "(\<And>x. x \<in># A \<Longrightarrow> algebraic x) \<Longrightarrow> algebraic (sum_mset A)"
  by (induction A) (auto intro!: algebraic_plus)

lemma algebraic_prod_mset [intro]:
  "(\<And>x. x \<in># A \<Longrightarrow> algebraic x) \<Longrightarrow> algebraic (prod_mset A)"
  by (induction A) (auto intro!: algebraic_times)

lemma algebraic_power [intro]: "algebraic x \<Longrightarrow> algebraic (x ^ n)"
  by (induction n) (auto intro: algebraic_times)

lemma algebraic_csqrt [intro]: "algebraic x \<Longrightarrow> algebraic (csqrt x)"
  by (rule algebraic_nth_root[of 2 x]) auto

lemma algebraic_csqrt_iff [simp]: "algebraic (csqrt x) \<longleftrightarrow> algebraic x"
proof
  assume "algebraic (csqrt x)"
  hence "algebraic (csqrt x ^ 2)"
    by (rule algebraic_power)
  also have "csqrt x ^ 2 = x"
    by simp
  finally show "algebraic x" .
qed auto

lemmas [intro] = algebraic_plus algebraic_times algebraic_uminus algebraic_div

lemma algebraic_power_iff [simp]:
  assumes "n > 0"
  shows   "algebraic (x ^ n) \<longleftrightarrow> algebraic x"
  using algebraic_nth_root[of n "x ^ n" x] assms by auto

lemma algebraic_ii [simp]: "algebraic \<i>"
  by (intro algebraic_int_imp_algebraic) auto

lemma algebraic_int_fact [simp, intro]: "algebraic_int (fact n)"
  by (intro int_imp_algebraic_int fact_in_Ints)

lemma algebraic_minus [intro]: "algebraic x \<Longrightarrow> algebraic y \<Longrightarrow> algebraic (x - y)"
  using algebraic_plus[of x "-y"] by simp

lemma algebraic_add_cancel_left [simp]:
  assumes "algebraic x"
  shows   "algebraic (x + y) \<longleftrightarrow> algebraic y"
proof
  assume "algebraic (x + y)"
  hence "algebraic (x + y - x)"
    using assms by (intro algebraic_minus) auto
  thus "algebraic y" by simp
qed (auto intro: algebraic_plus assms)

lemma algebraic_add_cancel_right [simp]:
  assumes "algebraic y"
  shows   "algebraic (x + y) \<longleftrightarrow> algebraic x"
  using algebraic_add_cancel_left[of y x] assms
  by (simp add: add.commute del: algebraic_add_cancel_left)

lemma algebraic_diff_cancel_left [simp]:
  assumes "algebraic x"
  shows   "algebraic (x - y) \<longleftrightarrow> algebraic y"
  using algebraic_add_cancel_left[of x "-y"] assms by (simp del: algebraic_add_cancel_left)

lemma algebraic_diff_cancel_right [simp]:
  assumes "algebraic y"
  shows   "algebraic (x - y) \<longleftrightarrow> algebraic x"
  using algebraic_add_cancel_right[of "-y" x] assms by (simp del: algebraic_add_cancel_right)

lemma algebraic_mult_cancel_left [simp]:
  assumes "algebraic x" "x \<noteq> 0"
  shows   "algebraic (x * y) \<longleftrightarrow> algebraic y"
proof
  assume "algebraic (x * y)"
  hence "algebraic (x * y / x)"
    using assms by (intro algebraic_div) auto
  also have "x * y / x = y"
    using assms by auto
  finally show "algebraic y" .
qed (auto intro: algebraic_times assms)

lemma algebraic_mult_cancel_right [simp]:
  assumes "algebraic y" "y \<noteq> 0"
  shows   "algebraic (x * y) \<longleftrightarrow> algebraic x"
  using algebraic_mult_cancel_left[of y x] assms
  by (simp add: mult.commute del: algebraic_mult_cancel_left)

lemma algebraic_inverse_iff [simp]: "algebraic (inverse y) \<longleftrightarrow> algebraic y"
proof
  assume "algebraic (inverse y)"
  hence "algebraic (inverse (inverse y))"
    by (rule algebraic_inverse)
  thus "algebraic y" by simp
qed (auto intro: algebraic_inverse)

lemma algebraic_divide_cancel_left [simp]:
  assumes "algebraic x" "x \<noteq> 0"
  shows   "algebraic (x / y) \<longleftrightarrow> algebraic y"
proof -
  have "algebraic (x * inverse y) \<longleftrightarrow> algebraic (inverse y)"
    by (intro algebraic_mult_cancel_left assms)
  also have "\<dots> \<longleftrightarrow> algebraic y"
    by (intro algebraic_inverse_iff)
  finally show ?thesis by (simp add: field_simps)
qed

lemma algebraic_divide_cancel_right [simp]:
  assumes "algebraic y" "y \<noteq> 0"
  shows   "algebraic (x / y) \<longleftrightarrow> algebraic x"
proof -
  have "algebraic (x * inverse y) \<longleftrightarrow> algebraic x"
    using assms by (intro algebraic_mult_cancel_right) auto
  thus ?thesis by (simp add: field_simps)
qed


subsection \<open>Turning an algebraic number into an algebraic integer\<close>

subsection \<open>
  Multiplying an algebraic number with a suitable integer turns it into an algebraic integer.
\<close>

lemma algebraic_imp_algebraic_int:
  fixes x :: "'a :: field_char_0"
  assumes "ipoly p x = 0" "p \<noteq> 0"
  defines "c \<equiv> Polynomial.lead_coeff p"
  shows   "algebraic_int (of_int c * x)"
proof -
  define n where "n = Polynomial.degree p"
  define p' where "p' = Abs_poly (\<lambda>i. if i = n then 1 else c ^ (n - i - 1) * poly.coeff p i)"
  have "n > 0"
    using assms unfolding n_def by (intro Nat.gr0I) (auto elim!: degree_eq_zeroE)

  have coeff_p': "poly.coeff p' i =
                    (if i = n then 1 else c ^ (n - i - 1) * poly.coeff p i)"
    (is "_ = ?f i") for i unfolding p'_def
  proof (subst poly.Abs_poly_inverse)
    have "eventually (\<lambda>i. poly.coeff p i = 0) cofinite"
      using MOST_coeff_eq_0 by blast
    hence "eventually (\<lambda>i. ?f i = 0) cofinite"
      by eventually_elim (use assms in \<open>auto simp: n_def\<close>)
    thus "?f \<in> {f. eventually (\<lambda>i. f i = 0) cofinite}" by simp
  qed auto

  have deg_p': "Polynomial.degree p' = n"
  proof -
    from assms have "(\<lambda>n. \<forall>i>n. poly.coeff p' i = 0) = (\<lambda>n. \<forall>i>n. poly.coeff p i = 0)"
      by (auto simp: coeff_p' fun_eq_iff n_def)
    thus ?thesis
      by (simp add: Polynomial.degree_def n_def)
  qed

  have lead_coeff_p': "Polynomial.lead_coeff p' = 1"
    by (simp add: coeff_p' deg_p')

  have "0 = of_int (c ^ (n - 1)) * (\<Sum>i\<le>n. of_int (poly.coeff p i) * x ^ i)"
    using assms unfolding n_def poly_altdef by simp
  also have "\<dots> = (\<Sum>i\<le>n. of_int (c ^ (n - 1) * poly.coeff p i) * x ^ i)"
    by (simp add: sum_distrib_left sum_distrib_right mult_ac)
  also have "\<dots> = (\<Sum>i\<le>n. of_int (poly.coeff p' i) * (of_int c * x) ^ i)"
  proof (intro sum.cong, goal_cases)
    case (2 i)
    have "of_int (poly.coeff p' i) * (of_int c * x) ^ i =
          of_int (c ^ i * poly.coeff p' i) * x ^ i"
      by (simp add: algebra_simps)
    also have "c ^ i * poly.coeff p' i = c ^ (n - 1) * poly.coeff p i"
    proof (cases "i = n")
      case True
      hence "c ^ i * poly.coeff p' i = c ^ n"
        by (auto simp: coeff_p' simp flip: power_Suc)
      also have "n = Suc (n - 1)"
        using \<open>n > 0\<close> by simp
      also have "c ^ \<dots> = c * c ^ (n - 1)"
        by simp
      finally show ?thesis
        using True by (simp add: c_def n_def)
    next
      case False
      thus ?thesis using 2
        by (auto simp: coeff_p' simp flip: power_add)
    qed
    finally show ?case ..
  qed auto
  also have "\<dots> = ipoly p' (of_int c * x)"
    by (simp add: poly_altdef n_def deg_p')
  finally have "ipoly p' (of_int c * x) = 0" ..

  with lead_coeff_p' show ?thesis
    unfolding algebraic_int_altdef_ipoly by blast
qed

lemma algebraic_imp_algebraic_int':
  fixes x :: "'a :: field_char_0"
  assumes "ipoly p x = 0" "p \<noteq> 0" "Polynomial.lead_coeff p dvd c"
  shows   "algebraic_int (of_int c * x)"
proof -
  from assms(3) obtain c' where c_eq: "c = Polynomial.lead_coeff p * c'"
    by auto
  have "algebraic_int (of_int c' * (of_int (Polynomial.lead_coeff p) * x))"
    by (rule algebraic_int_times[OF _ algebraic_imp_algebraic_int]) (use assms in auto)
  also have "of_int c' * (of_int (Polynomial.lead_coeff p) * x) = of_int c * x"
    by (simp add: c_eq mult_ac)
  finally show ?thesis .
qed

end