theory Digits
  imports Complex_Main
begin

section \<open>Representation of integers in different bases\<close>

text \<open>\<close>

text \<open> First, we look at some useful lemmas for splitting sums. \<close>
lemma split_sum_first_elt_less: assumes "n<m" 
  shows "(\<Sum>i\<in>{n..<m}. f i) = f n + (\<Sum>i\<in>{Suc n ..<m}. f i)"
  using sum.atLeast_Suc_lessThan assms by blast

lemma split_sum_mid_less: assumes "i<(n::nat)"
  shows "(\<Sum>j<n. f j) = (\<Sum>j<i. f j) + (\<Sum>j=i..<n. f j)"
proof -
  have "(\<Sum>j<n. f j) = (\<Sum>j\<in>{..<i} \<union> {i..<n}. f j)"
    using \<open>i < n\<close> by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>j<i. f j) + (\<Sum>j=i..<n. f j)"
    by (subst sum.union_disjoint) auto
  finally show "(\<Sum>j<n. f j) = (\<Sum>j<i. f j) + (\<Sum>j=i..<n. f j)" .
qed

text \<open>In order to use representation of numbers in a basis \<open>base\<close> and to calculate the conversion 
to and from integers, we introduce the following locale.\<close>
locale digits =
  fixes base :: nat
  assumes base_pos: "base > 0"
begin

text \<open>Conversion from basis base to integers: \<open>from_digits n d\<close>

\begin{tabular}{lcp{8cm}}
  n:& \<open>nat\<close>& length of representation in basis base\\
  d:& \<open>nat \<Rightarrow> nat\<close>& function of digits in basis base where \<open>d i\<close> is the $i$-th digit in basis base\\
  output:& \<open>nat\<close>& natural number corresponding to $d(n-1) \dots d(0)$ as integer\\
\end{tabular}
\<close>
fun from_digits :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "from_digits 0 d = 0"
| "from_digits (Suc n) d = d 0 + base * from_digits n (d \<circ> Suc)"

text \<open>Alternative definition using sum:\<close>
lemma from_digits_altdef: "from_digits n d = (\<Sum>i<n. d i * base ^ i)"
  by (induction n d rule: from_digits.induct)
     (auto simp add: sum.lessThan_Suc_shift o_def sum_distrib_left 
       sum_distrib_right mult_ac simp del: sum.lessThan_Suc)

text \<open>Digit in basis base of some integer number: \<open>digit x i\<close>

\begin{tabular}{lcp{8cm}}
  x:& \<open>nat\<close>& integer\\
  i:& \<open>nat\<close>& index\\
  output:& \<open>nat\<close>& $i$-th digit of representation in basis base of $x$\\
\end{tabular}
\<close>
fun digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "digit x 0 = x mod base"
| "digit x (Suc i) = digit (x div base) i"

text \<open>Alternative definition using divisor and modulo:\<close>
lemma digit_altdef: "digit x i = (x div (base ^ i)) mod base"
  by (induction x i rule: digit.induct) (auto simp: div_mult2_eq) 

text \<open>Every digit must be smaller that the base.\<close>
lemma digit_less_base: "digit x i < base"
  using base_pos by (auto simp: digit_altdef)

text \<open>A representation in basis \<open>base\<close> of length $n$ must be less than $\<open>base\<close> ^ n$.\<close>
lemma from_digits_less: 
  assumes "\<forall>i<n. d i < base" 
  shows "from_digits n d < base ^ n"
using assms proof (induct n d rule: from_digits.induct)
  case (2 n d)
  have "from_digits n (d \<circ> Suc) \<le> base ^ n -1" using 2 
    by (metis One_nat_def Suc_leI Suc_pred base_pos comp_apply 
        less_Suc_eq_le zero_less_power)
  moreover have "d 0 \<le> base -1" using 2 
    by (metis One_nat_def Suc_pred base_pos less_Suc_eq_0_disj 
        less_Suc_eq_le)
  ultimately have "d 0 + base * from_digits n (d \<circ> Suc) \<le> 
      base - 1 + base * (base^(n) - 1)"
    by (simp add: add_mono_thms_linordered_semiring(1))
  then show "from_digits (Suc n) d < base ^ Suc n" 
    using base_pos by (auto simp:comp_def) 
    (metis Suc_pred add_gr_0 le_imp_less_Suc mult_Suc_right 
      zero_less_power)
qed auto

text \<open>Lemmas for \<open>mod\<close> and \<open>div\<close> in number systems of basis \<open>base\<close>:\<close>
lemma mod_base:  assumes "\<And>i. i<n \<Longrightarrow> d i < base" "n>0"
  shows "from_digits n d mod base = d 0 "
proof -
  have "(\<Sum>i<n. d i * base ^ i) mod base = 
          (\<Sum>i<n. d i * base ^ i mod base) mod base"  
  by (subst mod_sum_eq[symmetric]) simp
  then show ?thesis using assms 
      sum.lessThan_Suc_shift[of "(\<lambda>i. d i * base ^ i mod base)" "n-1"]
    unfolding from_digits_altdef by simp
qed

lemma mod_base_i:  
  assumes "\<And>i. i<n \<Longrightarrow> d i < base" "n>0" "i<n"
  shows "(\<Sum>j=i..<n. d j * base ^ (j-i)) mod base = d i "
proof -
  have "(\<Sum>j=i..<n. d j * base ^ (j-i)) mod base = 
        (\<Sum>j=i..<n. d j * base ^ (j-i) mod base) mod base"  
    by (subst mod_sum_eq[symmetric]) simp
  then show ?thesis 
    using assms split_sum_first_elt_less[where 
        f = "(\<lambda>j. d j * base ^ (j-i) mod base)"] 
    unfolding from_digits_altdef by simp
qed

lemma div_base_i: 
  assumes "\<And>i. i<n \<Longrightarrow> d i < base" "n>0" "i<n"
  shows "from_digits n d div (base ^i) = (\<Sum>j=i..<n. d j * base ^ (j-i))"
  unfolding from_digits_altdef proof -
  have base_exp: "base^(j) =  base^(j-i) * base^i" 
    if "j\<in>{i..<n}" for j 
    by (metis Nat.add_diff_assoc2 add_diff_cancel_right' atLeastLessThan_iff 
        power_add that)
  have first:"(\<Sum>j<i. d j * base ^ j)< base ^ i" 
    using assms from_digits_less[where n="i"] 
    unfolding from_digits_altdef by auto
  have "(\<Sum>j<n. d j * base ^ j) = 
          (\<Sum>j<i. d j * base ^ j) + (\<Sum>j=i..<n. d j * base ^ j)" 
    using assms split_sum_mid_less[where f="(\<lambda>j. d j * base^j)"] by auto
  then have split_sum: "(\<Sum>j<n. d j * base ^ j) = 
      (\<Sum>j<i. d j * base ^ j) + base^i * (\<Sum>j=i..<n. d j * base ^ (j-i))"
    using base_exp mult.assoc sum_distrib_right 
    by (smt (z3) mult.commute sum.cong)
  then show "(\<Sum>i<n. d i * base ^ i) div base ^ i = 
              (\<Sum>j = i..<n. d j * base ^ (j - i))" 
    using first by (simp add:split_sum base_pos)
qed



text \<open>Conversions are inverse to each other.\<close>
lemma digit_from_digits:
  assumes "\<And>j. j<n \<Longrightarrow> d j < base" "n>0" "i<n"
  shows   "digit (from_digits n d) i = d i"
  using assms proof (cases "i=0")
  case True
  then show ?thesis 
    by (simp add: assms(1) assms(2) digits.mod_base digits_axioms)
next
  case False
  have "from_digits n d div base^i mod base = d i" 
    using assms by (auto simp add: div_base_i mod_base_i) 
  then show "digit (from_digits n d) i = d i" 
    unfolding digit_altdef by auto
qed

lemma div_distrib: assumes "i<n" 
  shows "(a*base^n + b) div base^i mod base = b div base^i mod base"
proof -
  have "base^i dvd (a*base^n)" using assms 
    by (simp add: le_imp_power_dvd)
  moreover have "a*base^n div base^i mod base = 0" 
    by (metis Suc_leI assms dvd_imp_mod_0 dvd_mult 
        dvd_mult_imp_div le_imp_power_dvd power_Suc)
  ultimately show ?thesis
    by (metis add.right_neutral div_mult_mod_eq 
        div_plus_div_distrib_dvd_left mod_mult_self3)
qed

lemma from_digits_digit:
  assumes "x < base ^ n"
  shows   "from_digits n (digit x) = x"
  using assms unfolding digit_altdef from_digits_altdef 
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define x_less where "x_less = x mod base^n"
  define x_n where "x_n = x div base^n"
  have "x_less < base^n" 
    using x_less_def base_pos mod_less_divisor by presburger
  then have IH_x_less:
    "(\<Sum>i<n. x_less div base ^ i mod base * base ^ i) = x_less" 
    using Suc.IH by simp
  have "x_n < base" using \<open>x<base^Suc n\<close> 
    by auto (metis less_mult_imp_div_less x_n_def)
  then have "x_n mod base = x_n" by simp
  have x_less_i_eq_x_i:"x mod base^n div base ^i mod base = 
    x div base^i mod base" if "i<n" for i
  proof -
    have "x div base^i mod base = 
          ((x div base^n) * base^n + x mod base^n) div base^i mod base"
      using div_mult_mod_eq[of x "base^n"] by simp
    also have "\<dots> = x mod base^n div base^i mod base" 
      using div_distrib[where a="x div base^n" and b = "x mod base^n"]
        that by auto
    finally show ?thesis by simp
  qed
  have "x = (x_n mod base)*base^n + x_less" 
    unfolding \<open>x_n mod base=x_n\<close> 
    using x_n_def x_less_def div_mod_decomp by blast 
  also have "\<dots> = (x div base^n mod base) * base^n + 
                (\<Sum>i<n. x div base ^ i mod base * base ^ i)"
    using IH_x_less x_less_def x_less_i_eq_x_i x_n_def by auto
  finally show ?case using sum.atMost_Suc 
    by (simp add: add.commute)
qed

text \<open>Stronger formulation of above lemma.\<close>
lemma from_digits_digit': 
  "from_digits n (digit x) = x mod (base ^ n)"
  unfolding from_digits_altdef digit_altdef 
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define x_less where "x_less = x mod base^n"
  define x_n where "x_n = x div base^n mod base"
  have "x_less < base^n" using x_less_def base_pos 
      mod_less_divisor by presburger
  then have IH_x_less:
    "(\<Sum>i<n. x_less div base ^ i mod base * base ^ i) = x_less" 
    using Suc.IH by simp
  have "x_n < base" using base_pos mod_less_divisor x_n_def 
    by blast
  then have "x_n mod base = x_n" by simp
  have x_less_i_eq_x_i:"x mod base^n div base ^i mod base = 
    x div base^i mod base" if "i<n" for i
  proof -
    have "x div base^i mod base = 
      ((x div base^n) * base^n + x mod base^n) div base^i mod base"
      using div_mult_mod_eq[of x "base^n"] by simp
    also have "\<dots> = x mod base^n div base^i mod base" 
      using div_distrib[where a="x div base^n" and b = "x mod base^n"] 
        that by auto
    finally show ?thesis by simp
  qed
  have "x mod base^Suc n = x_n*base^n + x_less" 
    by (metis mod_mult2_eq mult.commute power_Suc2 x_less_def x_n_def)
  also have "\<dots> = (x div base^n mod base) * base^n + 
                (\<Sum>i<n. x div base ^ i mod base * base ^ i)"
    using IH_x_less x_less_def x_less_i_eq_x_i x_n_def by auto
  finally show ?case using sum.atMost_Suc 
    by (simp add: add.commute)
qed

end
end
