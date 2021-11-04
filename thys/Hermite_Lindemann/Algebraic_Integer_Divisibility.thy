(*
  File:     Algebraic_Integer_Divisibility.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>Divisibility of algebraic integers\<close>
theory Algebraic_Integer_Divisibility
  imports "Algebraic_Numbers.Algebraic_Numbers"
begin

text \<open>
  In this section, we define a notion of divisibility of algebraic integers: \<open>y\<close> is divisible
  by \<open>x\<close> if \<open>y / x\<close> is an algebraic integer (or if \<open>x\<close> and \<open>y\<close> are both zero).

  Technically, the definition does not require \<open>x\<close> and \<open>y\<close> to be algebraic integers themselves,
  but we will always use it that way (in fact, in our case \<open>x\<close> will always be a rational integer).
\<close>

definition alg_dvd :: "'a :: field \<Rightarrow> 'a \<Rightarrow> bool" (infix "alg'_dvd" 50) where
  "x alg_dvd y \<longleftrightarrow> (x = 0 \<longrightarrow> y = 0) \<and> algebraic_int (y / x)"

lemma alg_dvd_imp_algebraic_int:
  fixes x y :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> algebraic_int x \<Longrightarrow> algebraic_int y"
  using algebraic_int_times[of "y / x" x] by (auto simp: alg_dvd_def)

lemma alg_dvd_0_left_iff [simp]: "0 alg_dvd x \<longleftrightarrow> x = 0"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_0_right [iff]: "x alg_dvd 0"
  by (auto simp: alg_dvd_def)

lemma one_alg_dvd_iff [simp]: "1 alg_dvd x \<longleftrightarrow> algebraic_int x"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_of_int [intro]:
  assumes "x dvd y"
  shows   "of_int x alg_dvd of_int y"
proof (cases "of_int x = (0 :: 'a)")
  case False
  from assms obtain z where z: "y = x * z"
    by (elim dvdE)
  have "algebraic_int (of_int z)"
    by auto
  also have "of_int z = of_int y / (of_int x :: 'a)"
    using False by (simp add: z field_simps)
  finally show ?thesis
    using False by (simp add: alg_dvd_def)
qed (use assms in \<open>auto simp: alg_dvd_def\<close>)

lemma alg_dvd_of_nat [intro]:
  assumes "x dvd y"
  shows   "of_nat x alg_dvd of_nat y"
  using alg_dvd_of_int[of "int x" "int y"] assms by simp

lemma alg_dvd_of_int_iff [simp]:
  "(of_int x :: 'a :: field_char_0) alg_dvd of_int y \<longleftrightarrow> x dvd y"
proof
  assume "(of_int x :: 'a) alg_dvd of_int y"
  hence "of_int y / (of_int x :: 'a) \<in> \<int>" and nz: "of_int x = (0::'a) \<longrightarrow> of_int y = (0::'a)"
    by (auto simp: alg_dvd_def dest!: rational_algebraic_int_is_int)
  then obtain n where "of_int y / of_int x = (of_int n :: 'a)"
    by (elim Ints_cases)
  hence "of_int y = (of_int (x * n) :: 'a)"
    unfolding of_int_mult using nz by (auto simp: field_simps)
  hence "y = x * n"
    by (subst (asm) of_int_eq_iff)
  thus "x dvd y"
    by auto
qed blast

lemma alg_dvd_of_nat_iff [simp]:
  "(of_nat x :: 'a :: field_char_0) alg_dvd of_nat y \<longleftrightarrow> x dvd y"
proof -
  have "(of_int (int x) :: 'a) alg_dvd of_int (int y) \<longleftrightarrow> x dvd y"
    by (subst alg_dvd_of_int_iff) auto
  thus ?thesis unfolding of_int_of_nat_eq .
qed

lemma alg_dvd_add [intro]:
  fixes x y z :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> x alg_dvd z \<Longrightarrow> x alg_dvd (y + z)"
  unfolding alg_dvd_def by (auto simp: add_divide_distrib)

lemma alg_dvd_uminus_right [intro]: "x alg_dvd y \<Longrightarrow> x alg_dvd -y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_uminus_right_iff [simp]: "x alg_dvd -y \<longleftrightarrow> x alg_dvd y"
  using alg_dvd_uminus_right[of x y] alg_dvd_uminus_right[of x "-y"] by auto

lemma alg_dvd_diff [intro]:
  fixes x y z :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> x alg_dvd z \<Longrightarrow> x alg_dvd (y - z)"
  unfolding alg_dvd_def by (auto simp: diff_divide_distrib)

lemma alg_dvd_triv_left [intro]: "algebraic_int y \<Longrightarrow> x alg_dvd x * y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_right [intro]: "algebraic_int x \<Longrightarrow> y alg_dvd x * y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_left_iff: "x alg_dvd x * y \<longleftrightarrow> x = 0 \<or> algebraic_int y"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_right_iff: "y alg_dvd x * y \<longleftrightarrow> y = 0 \<or> algebraic_int x"
  by (auto simp: alg_dvd_def)

lemma alg_dvd_triv_left_iff' [simp]: "x \<noteq> 0 \<Longrightarrow> x alg_dvd x * y \<longleftrightarrow> algebraic_int y"
  by (simp add: alg_dvd_triv_left_iff)

lemma alg_dvd_triv_right_iff' [simp]: "y \<noteq> 0 \<Longrightarrow> y alg_dvd x * y \<longleftrightarrow> algebraic_int x"
  by (simp add: alg_dvd_triv_right_iff)

lemma alg_dvd_trans [trans]:
  fixes x y z :: "'a :: field_char_0"
  shows "x alg_dvd y \<Longrightarrow> y alg_dvd z \<Longrightarrow> x alg_dvd z"
  using algebraic_int_times[of "y / x" "z / y"] by (auto simp: alg_dvd_def)

lemma alg_dvd_mono [simp]: 
  fixes a b c d :: "'a :: field_char_0"
  shows "a alg_dvd c \<Longrightarrow> b alg_dvd d \<Longrightarrow> (a * b) alg_dvd (c * d)"
  using algebraic_int_times[of "c / a" "d / b"] by (auto simp: alg_dvd_def)

lemma alg_dvd_mult [simp]: 
  fixes a b c :: "'a :: field_char_0"
  shows "a alg_dvd c \<Longrightarrow> algebraic_int b \<Longrightarrow> a alg_dvd (b * c)"
  using alg_dvd_mono[of a c 1 b] by (auto simp: mult.commute)

lemma alg_dvd_mult2 [simp]:
  fixes a b c :: "'a :: field_char_0"
  shows "a alg_dvd b \<Longrightarrow> algebraic_int c \<Longrightarrow> a alg_dvd (b * c)"
  using alg_dvd_mult[of a b c] by (simp add: mult.commute)

text \<open>
  A crucial theorem: if an integer \<open>x\<close> divides a rational number \<open>y\<close>, then \<open>y\<close> is in fact
  also an integer, and that integer is a multiple of \<open>x\<close>.
\<close>
lemma alg_dvd_int_rat:
  fixes y :: "'a :: field_char_0"
  assumes "of_int x alg_dvd y" and "y \<in> \<rat>"
  shows   "\<exists>n. y = of_int n \<and> x dvd n"
proof (cases "x = 0")
  case False
  have "y / of_int x \<in> \<int>"
    by (intro rational_algebraic_int_is_int) (use assms in \<open>auto simp: alg_dvd_def\<close>)
  then obtain n where n: "of_int n = y / (of_int x :: 'a)"
    by (elim Ints_cases) auto
  hence "y = of_int (n * x)"
    using False by (simp add: field_simps)
  thus ?thesis by (intro exI[of _ "x * n"]) auto
qed (use assms in auto)

lemma prod_alg_dvd_prod:
  fixes f :: "'a \<Rightarrow> 'b :: field_char_0"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x alg_dvd g x"
  shows   "prod f A alg_dvd prod g A"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma alg_dvd_sum:
  fixes f :: "'a \<Rightarrow> 'b :: field_char_0"
  assumes "\<And>x. x \<in> A \<Longrightarrow> y alg_dvd f x"
  shows   "y alg_dvd sum f A"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma not_alg_dvd_sum:
  fixes f :: "'a \<Rightarrow> 'b :: field_char_0"
  assumes "\<And>x. x \<in> A-{x'} \<Longrightarrow> y alg_dvd f x"
  assumes "\<not>y alg_dvd f x'"
  assumes "x' \<in> A" "finite A"
  shows   "\<not>y alg_dvd sum f A"
proof
  assume *: "y alg_dvd sum f A"
  have "y alg_dvd sum f A - sum f (A - {x'})"
    using \<open>x' \<in> A\<close> by (intro alg_dvd_diff[OF * alg_dvd_sum] assms) auto
  also have "\<dots> = sum f (A - (A - {x'}))"
    using assms by (subst sum_diff) auto
  also have "A - (A - {x'}) = {x'}"
    using assms by auto
  finally show False using assms by simp
qed

lemma fact_dvd_pochhammer:
  assumes "m \<le> n + 1"
  shows   "fact m dvd pochhammer (int n - int m + 1) m"
proof -
  have "(real n gchoose m) * fact m = of_int (pochhammer (int n - int m + 1) m)"
    by (simp add: gbinomial_pochhammer' pochhammer_of_int [symmetric])
  also have "(real n gchoose m) * fact m = of_int (int (n choose m) * fact m)"
    by (simp add: binomial_gbinomial)
  finally have "int (n choose m) * fact m = pochhammer (int n - int m + 1) m"
    by (subst (asm) of_int_eq_iff)
  from this [symmetric] show ?thesis by simp
qed

lemma coeff_higher_pderiv:
  "coeff ((pderiv ^^ m) f) n = pochhammer (of_nat (Suc n)) m * coeff f (n + m)"
  by (induction m arbitrary: n) (simp_all add: coeff_pderiv pochhammer_rec algebra_simps)

lemma fact_alg_dvd_poly_higher_pderiv:
  fixes p :: "'a :: field_char_0 poly"
  assumes "\<And>i. algebraic_int (poly.coeff p i)" "algebraic_int x" "m \<le> k"
  shows   "fact m alg_dvd poly ((pderiv ^^ k) p) x"
  unfolding poly_altdef
proof (intro alg_dvd_sum, goal_cases)
  case (1 i)
  have "(of_int (fact m) :: 'a) alg_dvd (of_int (fact k))"
    by (intro alg_dvd_of_int fact_dvd assms)
  also have "(of_int (fact k) :: 'a) alg_dvd of_int (pochhammer (int i + 1) k)"
    using fact_dvd_pochhammer[of k "i + k"]
    by (intro alg_dvd_of_int fact_dvd_pochhammer) (auto simp: algebra_simps)
  finally have "fact m alg_dvd (pochhammer (of_nat i + 1) k :: 'a)"
    by (simp flip: pochhammer_of_int)
  also have "\<dots> alg_dvd pochhammer (of_nat i + 1) k * poly.coeff p (i + k)"
    by (rule alg_dvd_triv_left) (rule assms)
  also have "\<dots> = poly.coeff ((pderiv ^^ k) p) i"
    unfolding coeff_higher_pderiv by (simp add: add_ac flip: pochhammer_of_int)
  also have "\<dots> alg_dvd poly.coeff ((pderiv ^^ k) p) i * x ^ i"
    by (intro alg_dvd_triv_left algebraic_int_power assms)
  finally show ?case .
qed

end