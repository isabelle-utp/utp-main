section\<open>Sum of divisors function\<close>

theory Sigma
imports PerfectBasics "HOL-Library.Infinite_Set"
begin

definition divisors :: "nat \<Rightarrow> nat set" where
    "divisors m \<equiv> {n . n dvd m}"

abbreviation sigma :: "nat \<Rightarrow> nat" where
    "sigma m \<equiv> \<Sum> (divisors(m))"

lemma divisors_eq_dvd[iff]: "(a \<in> divisors(n)) \<longleftrightarrow> (a dvd n)"
  by(simp add: divisors_def)

lemma finite_divisors [simp]:
   assumes "n>0" shows "finite (divisors n)"
  by (simp add: assms divisors_def)

lemma divs_of_zero_UNIV[simp]: "divisors(0) = UNIV"
  by(auto simp add: divisors_def)

lemma sigma0[simp]: "sigma(0) = 0"
  by simp

lemma sigma1[simp]: "sigma(Suc 0) = 1"
  by (simp add: sum_eq_Suc0_iff)

lemma prime_divisors: "prime p \<longleftrightarrow> divisors p = {1,p} \<and> p>1"
  by (auto simp add: divisors_def prime_nat_iff)

lemma prime_imp_sigma: "prime (p::nat) \<Longrightarrow> sigma(p) = p+1"
proof -
  assume "prime (p::nat)"
  hence "p>1 \<and> divisors(p) = {1,p}" by (simp add: prime_divisors)
  hence "p>1 \<and> sigma(p) = \<Sum> {1,p}" by (auto simp only: divisors_def)
  thus "sigma(p) = p+1" by simp
qed

lemma sigma_third_divisor:
  assumes "1 < a" "a < n" "a dvd n"
  shows "1+a+n \<le> sigma(n)"
proof -
  from assms have "{1,a,n} \<le> divisors n" 
    by auto
  hence "\<Sum> {1,a,n} \<le> sigma n"
    by (meson \<open>a < n\<close> finite_divisors order.strict_trans1 sum_mono2 zero_le)
  with assms show ?thesis by auto
qed

proposition prime_iff_sigma: "prime n \<longleftrightarrow> sigma(n) = Suc n"
proof
  assume L: "sigma(n) = Suc n"
  then have "n > 1"
    using less_linear sigma1 by fastforce
  moreover
  have "m = Suc 0" if "m dvd n" "m \<noteq> n" for m
  proof -
    have "0 < m"
      using that by auto
    then have "\<not> 1 + m + n \<le> 1 + n"
      by linarith
    then show ?thesis
      using sigma_third_divisor [of m]
      by (metis L One_nat_def Suc_lessD Suc_lessI \<open>n > 1\<close> dvd_imp_le \<open>0 < m\<close> less_le plus_1_eq_Suc that)
  qed
  then have "divisors n = {n,1}" 
    by (auto simp: divisors_def)
  ultimately show "prime n"
    by (simp add: insert_commute prime_divisors)
qed (use prime_divisors in auto)

lemma dvd_prime_power_iff:
  fixes p::nat
  assumes prime: "prime p"
  shows "{d. d dvd p^n} = (\<lambda>k. p^k) ` {0..n}"
  using divides_primepow_nat prime by (auto simp add: le_imp_power_dvd)

lemma rewrite_sum_of_powers:
  assumes p: "(p::nat)>1"
  shows "\<Sum> ((^) p ` {0..n}) = (\<Sum> i = 0 .. n . p^i)" (is "?l = ?r")
  by (metis inj_on_def p power_inject_exp sum.reindex_cong)

lemma sum_of_powers_int: "(x - 1::int) * (\<Sum>i=0..n . x^i) = x ^ Suc n - 1"
  by (metis atLeast0AtMost lessThan_Suc_atMost power_diff_1_eq) 

lemma sum_of_powers_nat: "(x - 1::nat) * (\<Sum>i=0..n . x^i) = x ^ Suc n - 1"
   (is "?l = ?r")
proof (cases "x = 0")
  case False
  then have "int ((x - 1) * sum ((^) x) {0..n}) = int (x ^ Suc n - 1)"
    using sum_of_powers_int [of "int x" n] by (simp add: of_nat_diff)
  then show ?thesis
    using of_nat_eq_iff by blast
qed auto


theorem sigma_primepower:
  assumes "prime p"
  shows "(p - 1) * sigma(p^e) = p^(e+1) - 1"
proof -
  have "sigma(p^e) = (\<Sum>i=0..e . p^i)"
    using assms divisors_def dvd_prime_power_iff prime_nat_iff rewrite_sum_of_powers by auto
  thus "(p - 1)*sigma(p^e) = p^(e+1) - 1"
    using sum_of_powers_nat by auto
qed

proposition sigma_prime_power_two: "sigma(2^n) = 2^(n+1) - 1"
proof -
  have "(2 - 1) * sigma(2^n) = 2^(n+1) - 1"
    by (auto simp only: sigma_primepower two_is_prime_nat)
  thus ?thesis by simp
qed

lemma prodsums_eq_sumprods:
  fixes p :: nat and m :: nat
  assumes "coprime p m"
  shows "\<Sum>((\<lambda>k. p^k) ` {0..n}) * sigma m = \<Sum>{p^k * b |k b. k \<le> n \<and> b dvd m}"
    (is "?lhs = ?rhs")
proof -
  have "coprime p x" if "x dvd m" for x
    using assms by (rule coprime_imp_coprime) (auto intro: dvd_trans that)
  then have "coprime (p ^ f) x" if "x dvd m" for x f
    using that by simp
  then have "?lhs = \<Sum>{a * b |a b. (\<exists>f. a = p ^ f \<and> f \<le> n) \<and> b dvd m}"
    apply (subst sum_mult_sum_if_inj [OF mult_inj_if_coprime_nat]) 
       apply (force intro!: sum.cong)+
    done
  also have "... = ?rhs"
    by (blast intro: sum.cong)
  finally show ?thesis .
qed

lemma div_decomp_comp:
  fixes a::nat
  shows "coprime m n \<Longrightarrow> a dvd m*n \<longleftrightarrow> (\<exists>b c. a = b * c \<and> b dvd m \<and> c dvd n)"
by (auto simp only: division_decomp mult_dvd_mono)

theorem sigma_semimultiplicative:
  assumes p: "prime p" and cop: "coprime p m"
  shows "sigma (p^n) * sigma m = sigma (p^n * m)" (is "?lhs = ?rhs")
proof -
  from cop have cop2: "coprime (p^n) m"
    by simp
  from p have "?lhs = \<Sum>((\<lambda>f. p^f) ` {0..n}) * sigma m"
    using divisors_def dvd_prime_power_iff by auto
  also from cop have "... = (\<Sum> {p^f*b| f b . f\<le>n \<and> b dvd m})"
    by (auto simp add: prodsums_eq_sumprods prime_nat_iff)
  also have "... = (\<Sum> {a*b| a b . a dvd (p^n) \<and> b dvd m})"
    by (metis (no_types, hide_lams) le_imp_power_dvd divides_primepow_nat p)
  also have "\<dots> = \<Sum>{c. c dvd (p^n*m)}"
    using cop2 div_decomp_comp by auto
  finally show ?thesis
    by (simp add: divisors_def)
qed

end
