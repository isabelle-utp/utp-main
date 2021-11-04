theory LTE
  imports
    "HOL-Number_Theory.Number_Theory"
begin

section "Library additions"

lemma cong_sum_mono_neutral_right:
  assumes "finite T"
  assumes "S \<subseteq> T"
  assumes zeros: "\<forall>i \<in> T - S. [g i = 0] (mod n)"
  shows "[sum g T = sum g S] (mod n)"
proof -
  have "[sum g T = (\<Sum>x\<in>T. if x \<in> S then g x else 0)] (mod n)"
    using zeros by (auto intro: cong_sum)
  also have "(\<Sum>x\<in>T. if x \<in> S then g x else 0) = (\<Sum>x\<in>S. if x \<in> S then g x else 0)"
    by (intro sum.mono_neutral_right; fact?; auto)
  also have "... = sum g S"
    by (auto intro: sum.cong)
  finally show ?thesis.
qed

lemma power_odd_inj:
  fixes a b :: "'a::linordered_idom"
  assumes "odd k" and "a^k = b^k"
  shows "a = b"
proof (cases "a \<ge> 0")
  case True
  then have "b \<ge> 0"
    using assms zero_le_odd_power by metis
  moreover from `odd k` have "k > 0" by presburger
  show ?thesis
    by (rule power_eq_imp_eq_base; fact)
next
  case False
  then have "b < 0"
    using assms power_less_zero_eq not_less by metis 
  from `a^k = b^k` have "(-a)^k = (-b)^k"
    using `odd k` power_minus_odd by simp
  moreover have "-a \<ge> 0" and "-b \<ge> 0"
    using `\<not> a \<ge> 0` and `b < 0` by auto
  moreover from `odd k` have "k > 0" by presburger
  ultimately have "-a = -b" by (rule power_eq_imp_eq_base)
  then show ?thesis by simp
qed

lemma power_eq_abs:
  fixes a b :: "'a::linordered_idom"
  assumes "a^k = b^k" and "k > 0"
  shows "\<bar>a\<bar> = \<bar>b\<bar>"
proof -
  from `a^k = b^k` have "\<bar>a\<bar>^k = \<bar>b\<bar>^k"
    using power_abs by metis
  show "\<bar>a\<bar> = \<bar>b\<bar>"
    by (rule power_eq_imp_eq_base; fact?; auto)
qed

lemma cong_scale:
  "k \<noteq> 0 \<Longrightarrow> [a = b] (mod c) \<longleftrightarrow> [k*a = k*b] (mod k*c)"
  unfolding cong_def by auto

lemma odd_square_mod_4:
  fixes x :: int
  assumes "odd x"
  shows "[x^2 = 1] (mod 4)"
proof -
  have "x^2 - 1 = (x - 1) * (x + 1)" 
    by (simp add: ring_distribs power2_eq_square)
  moreover from `odd x` have "2 dvd x - 1" and "2 dvd x + 1"
    by auto
  ultimately have "4 dvd x^2 - 1"
    by fastforce
  thus ?thesis
    by (simp add: cong_iff_dvd_diff)
qed

section \<open>The \<open>p > 2\<close> case\<close>

context
  fixes x y :: int and p :: nat
  assumes "prime p"
  assumes "p dvd x - y"
  assumes "\<not>p dvd x"   "\<not>p dvd y"
begin

lemma decompose_mod_p:
  "[(\<Sum>i<n. y^(n - Suc i) * x^i) = n*x^(n-1)] (mod p)"
proof -
  {
    fix i
    assume "i < n"
    from `p dvd x - y` have "[x = y] (mod p)"
      by (simp add: cong_iff_dvd_diff)
    hence "[y^(n - Suc i) * x^i = x^(n - Suc i) * x^i] (mod p)"
      by (intro cong_scalar_right cong_pow; rule cong_sym)
    also have "x^(n - Suc i) * x^i = x^(n - 1)"
      using `i < n` by (simp flip: power_add)
    finally have "[y^(n - Suc i) * x^i = x^(n - 1)] (mod p)"
      by auto
  }
  hence "[(\<Sum>i<n. y^(n - Suc i) * x^i) = (\<Sum>i<n. x^(n-1))] (mod p)"
    by (intro cong_sum; auto)
  thus "[(\<Sum>i<n. y^(n - Suc i) * x^i) = n * x^(n-1)] (mod p)"
    by simp
qed

text \<open>Lemma 1:\<close>

lemma multiplicity_diff_pow_coprime:
  assumes "coprime p n"
  shows "multiplicity p (x^n - y^n) = multiplicity p (x - y)"
proof -
  have factor: "x^n - y^n = (\<Sum>i<n. y^(n - Suc i) * x^i) * (x - y)"
    by (simp add: power_diff_sumr2)
  moreover have "\<not> p dvd (\<Sum>i<n. y^(n - Suc i) * x^i)"
  proof
    assume "p dvd (\<Sum>i<n. y^(n - Suc i) * x^i)"
    with decompose_mod_p have "p dvd n * x^(n-1)"
      using cong_dvd_iff by blast
    with `prime p` have "p dvd n \<or> p dvd x^(n-1)"
      by (simp add: prime_dvd_mult_eq_int)
    moreover from `coprime p n` and `prime p` have "\<not>p dvd n"
      using coprime_absorb_right not_prime_unit by auto
    ultimately have "p dvd x^(n-1)"
      by simp
    hence "p dvd x"
      using `prime p` prime_dvd_power_int prime_nat_int_transfer by blast 
    with `\<not>p dvd x` show False by simp
  qed
  ultimately show "multiplicity p (x^n - y^n) = multiplicity p (x - y)"
    using `prime p`
    by (auto intro: multiplicity_prime_elem_times_other)
qed  

text \<open>The inductive step:\<close>

lemma multiplicity_diff_self_pow:
  assumes "p > 2" and "x \<noteq> y"
  shows "multiplicity p (x^p - y^p) = Suc (multiplicity p (x - y))"
proof -
  have *: "multiplicity p (\<Sum>i<p. y^(p - Suc i) * x^i) = 1"
  proof (rule multiplicity_eqI)
    have "[(\<Sum>t<p. y^(p - Suc t) * x^t) = p * x^(p-1)] (mod p)"
      by (rule decompose_mod_p)
    also have "[p * x^(p-1) = 0] (mod p)"
      by (simp add: cong_mult_self_left)
    finally show "(int p)^1 dvd (\<Sum>i<p. y^(p - Suc i) * x^i)"
      by (simp add: cong_0_iff)

    from `p dvd x - y` obtain k::int where kp: "x = y + k * p"
      by (metis add.commute diff_add_cancel dvd_def mult.commute)

    have "[y^(p - Suc t) * x^t = y^(p-1) + t*k*p*y^(p-2)] (mod p^2)" if "t < p" for t
    proof (cases "t = 0")
      case False
      have "y^(p - Suc t) * x^t = y^(p - Suc t) * (y + k*p)^t"
        unfolding kp..
      also have "... = y^(p - Suc t) * (\<Sum>i\<le>t. (t choose i) * (k*p)^i * y^(t-i))"
        by (simp flip: binomial_ring add: add.commute)
      also have "[... = y^(p - Suc t) * (\<Sum>i\<le>1. (t choose i) * (k*p)^i * y^(t-i))] (mod p^2)"
        \<comment> \<open>discard \<open>i > 1\<close>\<close>
      proof (intro cong_scalar_left cong_sum_mono_neutral_right; rule)
        fix i
        assume "i \<in> {..t} - {..1}"
        then have "i \<ge> 2" by simp
        then obtain i' where "i = i' + 2"
          using add.commute le_Suc_ex by blast
        hence "(k*p)^i = (k*p)^i' * k^2 * p^2"
          by (simp add: ac_simps power2_eq_square)
        hence "[(k*p)^i = 0] (mod p^2)"
          by (simp add: cong_mult_self_right)
        thus "[(t choose i) * (k*p)^i * y^(t-i) = 0] (mod p^2)"
          by (simp add: cong_0_iff)
      qed (use `t \<noteq> 0` in auto)
      also have "(\<Sum>i\<le>1. (t choose i) * (k*p)^i * y^(t-i)) = y^t + t*k*p*y^(t-1)"
        by simp
      also have "y^(p - Suc t) * ... = y^(p-1) + t*k*p*y^(p-2)"
        using `t < p` `t \<noteq> 0` by (auto simp add: algebra_simps numeral_eq_Suc simp flip: power_add)
      finally show ?thesis.
    qed simp

    hence "[(\<Sum>t<p. y^(p - Suc t) * x^t) = (\<Sum>t<p. y^(p-1) + t*k*p*y^(p-2))] (mod p^2)"
      by (auto intro: cong_sum)
    also have "(\<Sum>t<p. y^(p-1) + t*k*p*y^(p-2)) = p*y^(p-1) + (\<Sum>t<p. t) * k*p*y^(p-2)"
      by (simp add: sum.distrib sum_distrib_right)
    also have "(\<Sum>t<p. t) = p*(p - 1) div 2"
      by (simp add: Sum_Ico_nat lessThan_atLeast0)
    finally have "[(\<Sum>t<p. y^(p - Suc t) * x^t) = p*y^(p-1) + (p*(p - 1) div 2) * k*p*y^(p-2)] (mod p^2)".
    moreover have "[(p*(p - 1) div 2) * k*p*y^(p-2) = 0] (mod p^2)"
    proof -
      have "[(p * (p - 1) div 2) * p = 0] (mod p^2)"
      proof -
        from `p > 2` and `prime p` have "odd p"
          using prime_odd_nat by blast
        thus ?thesis
          by (metis (no_types, lifting) cong_0_iff div_mult_swap dvd_times_left_cancel_iff
              dvd_triv_left le_0_eq linorder_not_less mult.commute odd_pos odd_two_times_div_two_nat
              one_add_one power_add power_one_right)
      qed
      hence "[int ((p*(p - 1) div 2) * p)*k*y^(p-2) = 0] (mod p^2)"
        unfolding cong_0_iff using int_dvd_int_iff by fastforce
      thus ?thesis
        by (simp add: ac_simps)
    qed
    ultimately have "[(\<Sum>t<p. y^(p - Suc t) * x^t) = p*y^(p-1)] (mod p^2)"
      by (smt cong_add cong_iff_dvd_diff)
    moreover have "\<not> p^2 dvd p*y^(p-1)"
      using `p > 2` `prime p` `\<not> p dvd y` by (simp add: power2_eq_square prime_dvd_power_int_iff)
    ultimately show "\<not> int p^(Suc 1) dvd (\<Sum>t<p. y^(p - Suc t) * x^t)"
      by (metis (no_types, lifting) Suc_1 of_nat_power cong_dvd_iff)
  qed
  moreover have "multiplicity p (x^p - y^p) = multiplicity p (x - y) + multiplicity p (\<Sum>i<p. y^(p - Suc i) * x^i)"
    apply (unfold power_diff_sumr2, intro prime_elem_multiplicity_mult_distrib)
    using `prime p` `x \<noteq> y` multiplicity_zero * by auto
  ultimately show ?thesis by simp
qed

text \<open>Theorem 1:\<close>

theorem multiplicity_diff_pow:
  assumes "p > 2" and "x \<noteq> y" and "n > 0"
  shows "multiplicity p (x^n - y^n) = multiplicity p (x - y) + multiplicity p n"
proof -
  obtain k where n: "n = p^multiplicity p n * k" and "\<not> p dvd k"
    using `n > 0` `prime p`
    by (metis neq0_conv not_prime_unit multiplicity_decompose')
  have "multiplicity p (x^(p^a * k) - y^(p^a * k)) = multiplicity p (x - y) + a" for a
  proof (induction a)
    case 0
    from `\<not> p dvd k` have "coprime p k"
      using `prime p` by (intro prime_imp_coprime)
    thus ?case
      by (simp add: multiplicity_diff_pow_coprime)
  next
    case (Suc a)
    let ?x' = "x^(p^a*k)" and ?y' = "y^(p^a*k)"
    have "\<not> p dvd ?x'" and "\<not> p dvd ?y'"
      using `\<not> p dvd x`  `\<not> p dvd y` and `prime p`
      by (meson prime_dvd_power prime_nat_int_transfer)+
    moreover have "p dvd ?x' - ?y'"
      using `p dvd x - y` by (simp add: power_diff_sumr2)
    moreover have "?x' \<noteq> ?y'"
    proof
      assume "?x' = ?y'"
      moreover have "0 < p^a * k"
        using `prime p` `n > 0` n
        by (metis gr0I mult_is_0 power_not_zero prime_gt_0_nat)
      ultimately have "\<bar>x\<bar> = \<bar>y\<bar>"
        by (intro power_eq_abs)
      with `x \<noteq> y` have "x = -y"
        using abs_eq_iff by simp
      with `p dvd x - y` have "p dvd 2*x"
        by simp
      with `prime p` have "p dvd 2 \<or> p dvd x"
        by (metis int_dvd_int_iff of_nat_numeral prime_dvd_mult_iff prime_nat_int_transfer)
      with `p > 2` have "p dvd x"
        by auto
      with `\<not> p dvd x` show False..
    qed
    moreover have "p^Suc a * k = p^a * k * p"
      by (simp add: ac_simps)
    ultimately show ?case
      using LTE.multiplicity_diff_self_pow[where x="?x'" and y="?y'", OF `prime p`] `p > 2`
        and Suc.IH
      by (metis add_Suc_right power_mult)
  qed
  with n show ?thesis by metis
qed

end

text \<open>Theorem 2:\<close>

corollary multiplicity_add_pow:
  fixes x y :: int and p n :: nat
  assumes "odd n"
    and "prime p" and "p > 2"
    and "p dvd x + y" and "\<not> p dvd x"  "\<not> p dvd y"
    and "x \<noteq> -y"
  shows "multiplicity p (x^n + y^n) = multiplicity p (x + y) + multiplicity p n"
proof -
  have [simp]: "(-y)^n = -(y^n)"
    using `odd n` by (rule power_minus_odd)
  moreover have "n > 0"
    using `odd n` by presburger
  with assms show ?thesis
    using multiplicity_diff_pow[where x=x and y="-y" and n=n]
    by simp
qed

section \<open>The \<open>p = 2\<close> case\<close>

text \<open>Theorem 3:\<close>

theorem multiplicity_2_diff_pow_4div:
  fixes x y :: int
  assumes "odd x"  "odd y" and "4 dvd x - y" and "n > 0"  "x \<noteq> y"
  shows "multiplicity 2 (x^n - y^n) = multiplicity 2 (x - y) + multiplicity 2 n"
proof -
  have "prime (2::nat)" by simp
  then obtain k where n: "n = 2^multiplicity 2 n * k" and "\<not> 2 dvd k"
    using `n > 0`
    by (metis neq0_conv not_prime_unit multiplicity_decompose')

  have pow2: "multiplicity 2 (x^(2^k) - y^(2^k)) = multiplicity 2 (x - y) + k" for k
  proof (induction k)
    case (Suc k)
    have "x^(2^Suc k) - y^(2^Suc k) = (x^2^k)^2 - (y^2^k)^2"
      by (simp flip: power_mult algebra_simps)
    also have "... = (x^2^k - y^2^k)*(x^2^k + y^2^k)"
      by (simp add: power2_eq_square algebra_simps)
    finally have factor: "x^(2^Suc k) - y^(2^Suc k) = (x^2^k - y^2^k)*(x^2^k + y^2^k)".
    moreover have m_plus: "multiplicity 2 (x^2^k + y^2^k) = 1"
    proof (rule multiplicity_eqI)
      show "2^1 dvd x^2^k + y^2^k"
        using `odd x` and `odd y` by simp

      have "[x^2^k + y^2^k = 2] (mod 4)"
      proof (cases k)
        case 0
        from `odd y` have "[y = 1] (mod 2)"
          using cong_def by fastforce
        hence "[2*y = 2] (mod 4)"
          using cong_scale[where k=2 and b=1 and c=2, simplified] by force
        moreover from `4 dvd x - y` have "[x - y = 0] (mod 4)"
          by (simp add: cong_0_iff)
        ultimately have "[x + y = 2] (mod 4)"
          by (smt cong_add)
        with `k = 0` show ?thesis by simp
      next
        case (Suc k')
        then have "[x^2^k = 1] (mod 4)" and "[y^2^k = 1] (mod 4)"
          using `odd x` `odd y`
          by (auto simp add: power_mult power_Suc2 simp del: power_Suc intro: odd_square_mod_4)
        thus "[x^2^k + y^2^k = 2] (mod 4)"
          by (smt cong_add)
      qed
      thus "\<not> 2^Suc 1 dvd x^2^k + y^2^k"
        by (simp add: cong_dvd_iff)
    qed
    moreover have "x^2^k + y^2^k \<noteq> 0"
      using m_plus multiplicity_zero by auto
    moreover have "x^2^k - y^2^k \<noteq> 0"
    proof
      assume "x^2^k - y^2^k = 0"
      then have "\<bar>x\<bar> = \<bar>y\<bar>"
        by (intro power_eq_abs, simp, simp)
      hence "x = y \<or> x = -y"
        using abs_eq_iff by auto
      with `x \<noteq> y` have "x = -y"
        by simp
      with `4 dvd x - y` have "4 dvd 2*x"
        by simp
      hence "2 dvd x"
        by auto
      with `odd x` show False..
    qed
    ultimately have "multiplicity 2 (x^2^Suc k - y^2^Suc k) =
            multiplicity 2 (x^2^k - y^2^k) + multiplicity 2 (x^2^k + y^2^k)"
      by (unfold factor; intro prime_elem_multiplicity_mult_distrib; auto)
    then show ?case
      using m_plus Suc.IH by simp
  qed simp

  moreover have even_diff: "int 2 dvd x^2^multiplicity 2 n - y^2^multiplicity 2 n"
    using `odd x` and `odd y` by simp
  moreover have odd_parts: "\<not> int 2 dvd x^2^multiplicity 2 n"   "\<not> int 2 dvd y^2^multiplicity 2 n"
    using `odd x` and `odd y` by simp+
  moreover have coprime: "coprime 2 k"
    using `\<not> 2 dvd k` by simp

  show ?thesis
    apply (subst (1) n)
    apply (subst (2) n)
    apply (simp only: power_mult)
    apply (simp only: multiplicity_diff_pow_coprime[OF `prime 2` even_diff odd_parts coprime, simplified])
    by (rule pow2)
qed

text \<open>Theorem 4:\<close>

theorem multiplicity_2_diff_even_pow:
  fixes x y :: int
  assumes "odd x"  "odd y" and "even n" and "n > 0" and "\<bar>x\<bar> \<noteq> \<bar>y\<bar>"
  shows "multiplicity 2 (x^n - y^n) = multiplicity 2 (x - y) + multiplicity 2 (x + y) + multiplicity 2 n - 1"
proof -
  obtain n' where "n = 2*n'"
    using `even n` by auto
  with `n > 0` have "n' > 0" by simp

  moreover have "4 dvd x^2 - y^2"
  proof -
    have "x^2 - y^2 = (x + y) * (x - y)"
      by (simp add: algebra_simps power2_eq_square)
    moreover have "2 dvd x + y" and "2 dvd x - y"
      using `odd x` and `odd y` by auto
    ultimately show "4 dvd x^2 - y^2" by fastforce
  qed

  moreover have "odd (x^2)" and "odd (y^2)"
    using `odd x` `odd y` by auto
  moreover from `\<bar>x\<bar> \<noteq> \<bar>y\<bar>` have "x^2 \<noteq> y^2"
    using diff_0 diff_0_right power2_eq_iff by fastforce

  ultimately have "multiplicity 2 ((x^2)^n' - (y^2)^n') = multiplicity 2 (x^2 - y^2) + multiplicity 2 n'"
    by (intro multiplicity_2_diff_pow_4div)
  also have "multiplicity 2 ((x^2)^n' - (y^2)^n') = multiplicity 2 (x^n - y^n)"
    unfolding `n = 2*n'` by (simp add: power_mult)
  also have "multiplicity 2 (x^2 - y^2) = multiplicity 2 ((x - y) * (x + y))"
    by (simp add: algebra_simps power2_eq_square)
  also have "... = multiplicity 2 (x - y) + multiplicity 2 (x + y)"
    using `\<bar>x\<bar> \<noteq> \<bar>y\<bar>` by (auto intro: prime_elem_multiplicity_mult_distrib)
  also have "multiplicity 2 n = Suc (multiplicity 2 n')"
    unfolding `n = 2*n'` using `n' > 0` by (simp add: multiplicity_times_same)
  ultimately show ?thesis by simp
qed

end