section \<open> Encoding real numbers as bit sequences \<close>

theory Real_Bit
imports
  HOL.Transcendental
  "HOL-Library.Z2"
  "HOL-Library.Sublist"
  Dyadic
begin

text \<open> The objective of this theory is to show how every real number can be encoded as an infinite
  sequences of bits. Whilst being an interesting property in its own right, this in particular
  means that we can show that the real numbers can be encoded as a a set of natural numbers
  (i.e. a function of type @{typ "nat \<Rightarrow> bool"} -- a bit sequence), and thus have the same
  cardinality. \<close>

declare [[linarith_split_limit=12]]

definition bits_to_nats :: "(nat \<Rightarrow> bit) \<Rightarrow> nat set" where
"bits_to_nats f = {x. f x = 1}"

lemma bij_bits_to_nats: "bij bits_to_nats"
  apply (rule bijI)
   apply (rule injI)
   apply (simp add: bits_to_nats_def set_eq_iff)
  apply (rule ext)
  apply (rename_tac x y i)
  apply (case_tac "x i", auto)
  apply (metis bit.exhaust)
  apply (simp add: image_def bits_to_nats_def)
  apply (rename_tac x)
  apply (rule_tac x="\<lambda> i. if (i \<in> x) then 1 else 0" in exI)
  apply (auto)
  done

lemma card_of_bit_seq: "|UNIV :: (nat \<Rightarrow> bit) set| =o |UNIV :: nat set set|"
  using bij_bits_to_nats card_of_ordIsoI by blast

lemma uncountable_UNIV_nat_set: "uncountable (UNIV :: nat set set)"
  by (auto simp add: uncountable_def, metis Cantors_paradox Pow_UNIV)

lemma card_rat_less_nat_set: "|\<rat> :: real set| <o |UNIV :: nat set set|"
proof -
  have "countable (\<rat> :: real set)"
    by (simp add: countable_rat)
  moreover have "uncountable (UNIV :: nat set set)"
    by (simp add: uncountable_UNIV_nat_set)
  ultimately show ?thesis
    by (metis card_of_ordLess2 countable_empty countable_image)
qed

definition terminates_at :: "(nat \<Rightarrow> 'a::zero) \<Rightarrow> nat \<Rightarrow> bool" where
"terminates_at x i = (\<forall> j \<ge> i. x(j) = 0)"

definition terminal :: "(nat \<Rightarrow> 'a::zero) \<Rightarrow> bool" where
"terminal x = (\<exists> i. terminates_at x i)"

abbreviation "BitSeqs \<equiv> (UNIV :: (nat \<Rightarrow> bit) set)"

abbreviation "TermSeqs \<equiv> {x. terminal x}"

abbreviation "TermBitSeqs \<equiv> TermSeqs :: (nat \<Rightarrow> bit) set"

abbreviation "nonterminal x \<equiv> \<not> terminal x"

abbreviation "NonTermSeqs \<equiv> {x. nonterminal x}"

abbreviation "NonTermBitSeqs \<equiv> NonTermSeqs :: (nat \<Rightarrow> bit) set"

definition subsequence :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
"subsequence n x = (\<lambda> i. x (i + n))"

definition recur :: "('a list) \<Rightarrow> (nat \<Rightarrow> 'a)" where
"recur xs = (\<lambda> i. xs ! (i mod (length xs)))"

lemma recur_example: "recur [x,y] i = (if even i then x else y)"
  apply (auto simp add: recur_def)
  apply (simp add: numeral_2_eq_2)
  apply (metis One_nat_def even_iff_mod_2_eq_zero not_mod_2_eq_0_eq_1 nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
done

definition recurrent :: "(nat \<Rightarrow> bit) \<Rightarrow> bool" where
"recurrent x = (\<exists> n xs. subsequence n x = recur xs)"

lemma recurrent_recur: "recurrent (recur xs)"
  apply (auto simp add: recurrent_def recur_def subsequence_def)
  apply (rule_tac x="0" in exI)
  apply (rule_tac x="xs" in exI)
  apply (auto)
done

text \<open> Convert a binary representation to a real number in [0..1] \<close>

definition binlist :: "bit list \<Rightarrow> real" where
"binlist xs = (\<Sum> i<length xs. of_bit(xs!i)/2^(i+1))"

lemma Ints_of_bit: "of_bit x \<in> \<int>"
  by (cases "x", simp_all)

lemma dyadic_bin_list: "dyadic (binlist xs)"
  apply (unfold binlist_def)
  apply (rule dyadic_sum)
  apply (blast)
  apply (blast intro: Ints_of_bit dyadic_div_pow_2)
done

(*
lemma "bij_betw binlist {xs. length xs > 0 \<longrightarrow> last xs = 1} \<rat>\<^sub>D"
  apply (rule bij_betwI')
*)

text \<open> For real number x, calculate the nth binary digit, given all the bits from 0..n-1 \<close>

definition rbit :: "real \<Rightarrow> nat \<Rightarrow> bit list \<Rightarrow> bit" where
  "rbit x n xs = of_int \<lfloor>(x - binlist xs) * 2^(n+2)\<rfloor>"

text \<open> Convert a real number in the range [0..1) to a sequence of binary digits \<close>

text \<open> Extract the nth bit of a real number by shifting it to the left n+1 places (power multiplication),
        chopping off the fractional part (flooring it), and removing all but the first bit of
        the integer part (by takes modulus 2). \<close>

definition rbseq :: "real \<Rightarrow> (nat \<Rightarrow> bit)" where
"rbseq x = (\<lambda> i.  of_int (\<lfloor>(x * (2 ^ (i+1)))\<rfloor> mod 2))"

lemma of_drat_DFract: "coprime a (2^b) \<Longrightarrow> of_drat (DFract a b) = a / 2^b"
  by (transfer, auto simp add: quotient_of_Fract of_int_power)

definition real_bits2 :: "real \<Rightarrow> nat \<Rightarrow> bit list" where
"real_bits2 x n = map (rbseq x) [0..<n+1]"

fun real_bits :: "real \<Rightarrow> nat \<Rightarrow> bit list" where
"real_bits x 0 = [of_int \<lfloor>x * 2\<rfloor>]" |
"real_bits x (Suc n) =
   (real_bits x n @ [rbit x n (real_bits x n)])"

definition drat_bits :: "drat \<Rightarrow> bit list" where
"drat_bits x = real_bits (of_drat x) (snd (dfrac_of x))"

(* Produce version that produces a non-terminating number for dyadics *)

definition real_bin :: "real \<Rightarrow> (nat \<Rightarrow> bit)" where
"real_bin x = (\<lambda> n. (real_bits x n) ! n)"

definition real_bin_seq :: "real \<Rightarrow> (nat \<Rightarrow> bool)" where
"real_bin_seq x n = (last (real_bits x n) = 1)"

definition binseq :: "(nat \<Rightarrow> bit) \<Rightarrow> (nat \<Rightarrow> real)" where
"binseq x = (\<lambda> i. of_bit (x(i)) / 2^(i+1))"

definition bin_real :: "(nat \<Rightarrow> bit) \<Rightarrow> real" where
"bin_real x = (\<Sum> i. binseq x i)"

lemma binseq_le_bin_series: "(\<Sum> i<n. binseq x i) \<le> (\<Sum> i<n. 1/2^i)"
  apply (rule sum_mono)
  apply (rename_tac i)
  apply (simp add: binseq_def)
  apply (case_tac "x i")
  apply (auto simp add: frac_le)
done

lemma bin_series_geometric:
  "((\<Sum> i\<le>n. 1/2^(i+1)) :: rat) = 1 - (1 / 2^(n + 1))"
proof -
  have "((\<Sum> i\<le>n. 1/2^(i+1)) :: rat) = (\<Sum> i<n+2. (1/2)^i) - 1"
    by (induct n, simp_all add: power_one_over)
  also have "... = 1 - (1 / 2^(n + 1))"
    by (subst geometric_sum, simp_all add: power_one_over)
  finally show ?thesis .
qed

lemma binseq_pos: "binseq x i \<ge> 0"
  by (case_tac "x i", simp_all add: binseq_def)

lemma sum_minus_triv:
  fixes f :: "nat \<Rightarrow> 'b::ab_group_add"
  assumes "n \<ge> m"
  shows "(\<Sum>i\<le>n. f(i)) - (\<Sum>i\<le>m. f(i)) = (\<Sum>i=m+1..n. f(i))"
proof -
  have "{..n} - {..m} = {m + 1..n}"
    by auto
  with assms show ?thesis
    by (simp add: sum_diff[THEN sym])
qed

lemma binary_ub:
  assumes "n \<ge> m"
  shows "((1 / 2 ^ m) :: real) > (\<Sum>i=m+1..n. 1 / 2 ^ i)"
proof -
  from assms have "((\<Sum>i=m+1..n. 1 / 2 ^ i) :: real) = (\<Sum>i<n+1. 1/2^i) - (\<Sum>i<m+1. 1/2^i)"
    by (subst sum_minus_triv[THEN sym], simp_all add: lessThan_Suc_atMost)
  also have "... = (\<Sum>i<n+1. (1/2)^i) - (\<Sum>i<m+1. (1/2)^i)"
    by (simp add: power_one_over)
  also have "... = 2 / 2 ^ (m + 1) - 2 / 2 ^ (n + 1)"
    by (simp only: geometric_sum, simp add: power_one_over)
  moreover have "(1/2^m :: real) > 2 / 2 ^ (m + 1) - 2 / 2 ^ (n + 1)"
    by (auto)
  ultimately show ?thesis
    by linarith
qed

lemma real_bin_ub:
  assumes "m > 0"
  shows "\<exists> n. 2^n > (m::real)"
proof -
  have "m \<le> \<lceil>m\<rceil>"
    by (simp add: le_of_int_ceiling)
  moreover from assms have "2 powr \<lceil>log 2 \<lceil>m\<rceil>\<rceil> \<ge> \<lceil>m\<rceil>"
    by (subst log_le_iff[THEN sym], simp_all)
  moreover from assms have "2 powr \<lceil>log 2 \<lceil>m\<rceil>\<rceil> = 2 powr (real (nat (\<lceil>log 2 \<lceil>m\<rceil>\<rceil> :: int)))"
  proof -
    from assms have "log 2 \<lceil>m\<rceil> \<ge> 0"
      by simp
    thus ?thesis
      by simp
  qed
  ultimately have "2 ^ nat \<lceil>log 2 \<lceil>m\<rceil>\<rceil> \<ge> m"
    by (metis order_trans powr_realpow zero_less_numeral)
  with assms have "2 ^ (nat \<lceil>log 2 \<lceil>m\<rceil>\<rceil> + 1) > m"
    by simp
  thus ?thesis
    by blast
qed

lemma real_bin_lower_bound:
  assumes "(m::real) > 0"
  shows "\<exists> n::nat. 1 / 2^n < m"
proof -
  from assms obtain n where "2^n > (1/m)"
    using real_bin_ub[of "1/m"] by auto
  with assms have "1/2^n < 1/(1/m)"
    by (subst frac_less2, auto)
  thus ?thesis
    by (rule_tac x="n" in exI, auto)
qed

theorem binseq_summable: "summable (binseq x)"
proof (simp add: summable_Cauchy, clarify)
  fix r :: real
  assume "r > 0"
  then obtain j where wits: "1/2^j < r"
    using real_bin_lower_bound[of "r"] by auto
  then show "\<exists>k. \<forall>m\<ge>k. \<forall>n. \<bar>sum (binseq x) {m..<n}\<bar> < r"
  proof (rule_tac x="j+1" in exI, clarify)
    fix m n :: nat
    assume mnassm: "j+1 \<le> m"
    have "(\<Sum> i=m..<n. binseq x i) \<le> 1/2^j"
    proof -
      have "(\<Sum> i=m..<n. binseq x i) \<le> (\<Sum>i=m..<n. 1/2^i)"
        by (rule sum_mono)
           (simp add: binseq_def frac_le)
      also from mnassm have "... \<le> (\<Sum>i=j+1..n-1. 1/2^i)"
        by (auto intro!: sum_mono2)
      also have "... < 1/2^j"
      proof (cases "j \<le> n - 1")
        case True thus ?thesis
          by (rule binary_ub)
      next
        case False thus ?thesis
          by auto
      qed
      finally show ?thesis by auto
    qed
    with mnassm wits show "\<bar>sum (binseq x) {m..<n}\<bar> < r"
      by (auto simp add: sum_minus_triv binseq_pos sum_nonneg)
  qed
qed

lemma binlist_nil [simp]:
  "binlist [] = 0"
  by (simp add: binlist_def)

lemma binlist_append [simp]:
  "binlist (xs @ [x]) = binlist xs + (of_bit x*(1/2^(length xs + 1)))"
  by (simp add: binlist_def nth_append)

lemma of_bit_pos: "of_bit x \<ge> (0::real)"
  by (cases x, auto)

lemma bit_real_pos: "of_bit x * (1/2^n) \<ge> (0::real)"
proof -
  have "of_bit x \<ge> (0::real)"
    by (cases x, auto)
  moreover have "1/2^n \<ge> (0::real)"
    by auto
  ultimately show ?thesis
    by auto
qed

lemma binlist_pos [simp]:
  "binlist xs \<ge> 0"
  by (induct xs rule: rev_induct, auto simp add: of_bit_pos)

lemma real_bits_length [simp]:
  "length (real_bits x n) = n + 1"
  by (induct n, simp_all)

lemma real_bits_first [simp]:
  "real_bits x m ! 0 = of_int \<lfloor>x * 2\<rfloor>"
  by (induct m, simp_all add: nth_append)

lemma real_bits_plus:
  assumes "i \<le> m"
  shows "real_bits x (m + k) ! i = real_bits x m ! i"
  using assms
  by (induct k, auto simp add: nth_append)

lemma prefix_nth:
  "\<lbrakk> length xs \<le> length ys; \<forall> i < length xs. xs!i = ys!i \<rbrakk> \<Longrightarrow> prefix xs ys"
proof (induct xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons x xs') note hyp = this
  then obtain ys' where "ys = x # ys'"
    by (metis Cons_prefix_Cons in_set_takeD list.set_cases list.set_intros(1) nth_take_lemma order_refl take_all take_is_prefix)
  with hyp show ?case
    by (auto, metis le_trans not_less not_less_eq_eq not_less_iff_gr_or_eq nth_Cons_Suc)
qed

lemma real_bits_prefix:
  assumes "m \<le> n"
  shows "prefix (real_bits x m) (real_bits x n)"
proof -
  obtain k where "n = m + k"
    by (metis assms le_add_diff_inverse)
  thus ?thesis
    by (auto intro: prefix_nth simp add: real_bits_plus)
qed

lemma binseq_rbseq: "binseq (rbseq x) i = (\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) / (2 ^ (i+1))"
  by (simp add: binseq_def rbseq_def)
     (metis not_mod_2_eq_1_eq_0 of_int_0 of_int_1)

text \<open> The contribution of the nth bit to a real number \<close>

definition nth_cont :: "real \<Rightarrow> nat \<Rightarrow> real" where
"nth_cont x i = \<lfloor>x * (2^(i+1))\<rfloor> mod 2 / (2^(i+1))"

text \<open> Every bit contribution is less than the whole \<close>

lemma nth_cont_cases [case_names zero nzero]:
  "\<lbrakk> nth_cont x i = 0 \<Longrightarrow> P; nth_cont x i = 1/2^(i+1) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (simp add: nth_cont_def)
  apply (cases "\<lfloor>x * (2 * 2 ^ i)\<rfloor>" rule: parity_cases)
  apply (simp_all)
done

lemma nth_cont_le_geometric:
  "(\<Sum> i\<le>n. nth_cont x i) \<le> 1 - (1 / 2^(n + 1))"
proof -
  have "(\<Sum> i\<le>n. nth_cont x i) \<le> (\<Sum> i\<le>n. 1 / (2^(i+1)))"
    by (rule sum_mono, metis nth_cont_cases order_refl zero_le_divide_1_iff zero_le_numeral zero_le_power)
  also have "... = (\<Sum> i<n+2. (1/2)^i) - 1"
    by (induct n, simp_all add: power_one_over)
  also have "... = 1 - (1 / 2^(n + 1))"
    by (subst geometric_sum, simp_all add: power_one_over)
  finally show ?thesis .
qed

lemma nth_cont_bit_diff_ge_zero:
  assumes "0 \<le> x" "x < 1"
  shows "0 \<le> x - nth_cont x i"
proof (cases "\<lfloor>x * (2 ^ (i+1))\<rfloor>" rule: parity_cases)
  case even
  with assms show ?thesis by (simp add: nth_cont_def)
next
  case odd
  have "\<lfloor>x * (2 ^ (i+1))\<rfloor> \<ge> 0"
    by (simp add: assms(1))
  with odd have "\<lfloor>x * (2 ^ (i+1))\<rfloor> \<ge> (1::int)"
    by (metis zmod_le_nonneg_dividend)
  with odd show ?thesis
    by (simp add: nth_cont_def pos_divide_le_eq)
qed

lemma bin_series_geometric':
  "((\<Sum> i\<le>n. 1/2^(i+1)) :: real) = 1 - (1 / 2^(n + 1))"
proof -
  have "((\<Sum> i\<le>n. 1/2^(i+1)) :: real) = (\<Sum> i<n+2. (1/2)^i) - 1"
    by (induct n, simp_all add: power_one_over)
  also have "... = 1 - (1 / 2^(n + 1))"
    by (subst geometric_sum, simp_all add: power_one_over)
  finally show ?thesis .
qed

text \<open> The removal of the (contribution of) the ith bit from a real number does not affect
        the jth bit. \<close>

lemma nth_cont_removed:
  "nth_cont (x - nth_cont x i) i = 0"
proof -
  have "(x - 1 / (2 * 2 ^ i)) * (2 * 2 ^ i) = x * (2 * 2 ^ i) - 1"
  proof -
    have "(x - 1 / (2 * 2 ^ i)) * (2 * 2 ^ i) = (x*(2 * 2 ^ i) - (1 / (2 * 2 ^ i))*(2 * 2 ^ i))"
      using left_diff_distrib by blast
    also have "... = x * (2 * 2 ^ i) - 1"
      by (simp)
    finally show ?thesis .
  qed
  thus ?thesis
    apply (simp add: nth_cont_def)
    apply (cases "\<lfloor>x * (2 * 2 ^ i)\<rfloor>" rule: parity_cases)
    apply (simp_all)
  done
qed

lemma nth_cont_indep1:
  assumes "i < j"
  shows "nth_cont (x - nth_cont x i) j = nth_cont x j"
proof -
  have "(x - (\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) / (2 ^ (i+1))) * (2 ^ (j+1)) =
        (x * 2 ^ (j+1)) - ((\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) / (2 ^ (i+1)) * (2 ^ (j+1)))"
    using left_diff_distrib by blast
  moreover have "x * (2 * 2 ^ j) - 2 ^ j / 2 ^ i = x * (2 * 2 ^ j) - real ((2::nat) ^ (j - i))"
    by (simp add: assms order_less_imp_le power_diff power_one_over)
       (metis assms le_less of_nat_numeral of_nat_power power_diff rel_simps(76))
  moreover have "\<lfloor>x * (2 * 2 ^ j) - of_int ((2::nat) ^ (j - i))\<rfloor> = \<lfloor>x * (2 * 2 ^ j)\<rfloor> - ((2::nat) ^ (j - i))"
    using floor_diff_of_int by blast
  moreover have "(2::int) ^ (j - i) mod 2 = 0"
    by (simp add: assms)
(*
  moreover have "x * (2 * 2 ^ j) - 2 ^ j / 2 ^ i = 2^j * (2*x - 1/(2^i))"
    by (simp add: linordered_field_class.sign_simps(38))
*)
  ultimately show ?thesis
  apply (simp add: nth_cont_def)
  apply (cases "\<lfloor>x * (2 * 2 ^ i)\<rfloor>" rule: parity_cases)
  apply (simp_all)
    apply (metis minus_int_code(1) mod_diff_right_eq)
  done
qed

(*
lemma nth_cont_indep2:
  assumes "i > j"
  shows "nth_cont (x - nth_cont x i) j = nth_cont x j"
proof -
  have "(x - (\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) / (2 ^ (i+1))) * (2 ^ (j+1)) =
        (x * 2 ^ (j+1)) - ((\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) / (2 ^ (i+1)) * (2 ^ (j+1)))"
    using left_diff_distrib by blast

  moreover have "x * (2 * 2 ^ j) - 2 ^ j / 2 ^ i = 2^j * (2*x - 1/(2^i))"
    by (simp add: linordered_field_class.sign_simps(38))

  moreover have "i > 0"
    using assms by linarith

  ultimately show ?thesis
    apply (simp add: nth_cont_def)
    apply (cases "\<lfloor>x * (2 * 2 ^ i)\<rfloor>" rule: parity_cases)
    apply (simp_all)
  sorry
qed

lemma nth_cont_indep:
  assumes "i \<noteq> j"
  shows "nth_cont (x - nth_cont x i) j = nth_cont x j"
  using assms nat_neq_iff nth_cont_indep1 nth_cont_indep2 by auto

lemma sum_nth_cont_removed:
  assumes "finite A" "n \<in> A"
  shows "sum (nth_cont (x - nth_cont x n)) A = sum (nth_cont x) (A - {n})"
proof -
  from assms have A: "A = insert n (A - {n})" by auto
  moreover hence "sum (nth_cont (x - nth_cont x n)) (insert n (A - {n})) = sum (nth_cont x) (A - {n})"
    apply (subst sum.insert)
    apply (auto simp add: assms nth_cont_removed)
    apply (rule sum.cong)
    apply (auto simp add: nth_cont_indep)
  done
  ultimately show ?thesis
    by simp
qed
*)

lemma nth_cont_shift: "nth_cont (2*x) n = (nth_cont x (n+1) * 2)"
  by (simp add: nth_cont_def mult.left_commute)

lemma modulus_2_via_shift_lemma:
  fixes x :: real
  assumes "0 \<le> x" "x < 1"
  shows "(\<Sum> i < n. \<lfloor>x * 2^(i+1)\<rfloor> mod 2 * 2^(n-i)) = \<lfloor>x * 2^(n+1)\<rfloor> - \<lfloor>x * 2^(n+1)\<rfloor> mod 2"
proof (induct n)
  case 0 with assms(1,2) show ?case
    using mod_pos_pos_trivial by auto
next
  case (Suc n) note hyp = this
  have "(\<Sum>i<n. \<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2 * 2 ^ (Suc n - i)) = (\<Sum>i<n. \<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2 * 2 ^ (n - i))*2"
    by (auto intro: sum.cong simp add: Suc_diff_le sum_distrib_right)
  \<comment> \<open> This can be proven with reference to integer division and modulus \<close>
  moreover have "\<lfloor>x * (2 ^ (n+1))\<rfloor> * 2 = \<lfloor>x * (2 ^ (n+2))\<rfloor> - \<lfloor>x * (2 ^ (n+2))\<rfloor> mod 2"
  proof -
    have "\<lfloor>x * 2^(n+1)\<rfloor> = \<lfloor>x * 2^(n+2)\<rfloor> div 2"
    proof -
      \<comment> \<open> This result should maybe be extracted? It says how an integer division can
           be expressed in binary more or less... \<close>
      have "\<lfloor>x * 2^(n+2)\<rfloor> div 2 = \<lfloor>(x * 2^(n+2)) / 2\<rfloor>"
        by linarith
      thus ?thesis
        by (simp, subst mult.assoc[THEN sym], subst mult.commute, simp add: mult.assoc)
    qed
    hence "(\<lfloor>x * 2^(n+1)\<rfloor> * 2) + \<lfloor>x * (2 ^ (n+2))\<rfloor> mod 2 = \<lfloor>x * (2 ^ (n+2))\<rfloor>"
      by simp
    hence "\<lfloor>x * (2 ^ (n+1))\<rfloor> * 2 = \<lfloor>x * (2 ^ (n+2))\<rfloor> - \<lfloor>x * (2 ^ (n+2))\<rfloor> mod 2"
      by simp
    thus ?thesis
      by (simp)
  qed
  ultimately show ?case
    using hyp by simp
qed

text \<open> This theorem shows that the nth digit of a real number x in [0..1) can equivalently
        be obtained either by shift;floor;modulus 2, or alternatively by subtracting the
        approximation of the real number up to the nth digit, followed by a shift and floor.
        It can be used to show that the recursive algorithm and functional specification
        co-incide. \<close>

theorem modulus_2_via_shift:
  fixes x :: real
  assumes "0 \<le> x" "x < 1"
  shows "\<lfloor>(x - (\<Sum>i<n. nth_cont x i))*2^(n+1)\<rfloor> = \<lfloor>x * 2^(n+1)\<rfloor> mod 2"
proof -
  have "\<lfloor>(x - (\<Sum>i<n. nth_cont x i))*2^(n+1)\<rfloor> = \<lfloor>(x*2^(n+1) - (\<Sum>i<n. nth_cont x i)*2^(n+1))\<rfloor>"
    by (simp add: left_diff_distrib)
  moreover have "(\<Sum>i<n. nth_cont x i)*2^(n+1) = of_int (\<Sum>i<n. (\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) * (2 ^ (n-i)))"
  proof -
    have "(\<Sum>i<n. nth_cont x i)*2^(n+1) = (\<Sum>i<n. (\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) / (2 ^ (i+1))) * (2 ^ (n+1))"
      by (simp add: nth_cont_def)
    also have "... = (\<Sum>i<n. (\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) / (2 ^ (i+1)) * (2 ^ (n+1)))"
      by (rule sum_distrib_right)
    also have "... = (\<Sum>i<n. (of_int ((\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) * (2 ^ (n-i)))))"
      by (rule sum.cong, auto simp add: power_diff)
         (metis (no_types, opaque_lifting) le_less of_int_numeral of_int_power power_diff times_divide_eq_right zero_neq_numeral)
    finally show ?thesis
      by auto
  qed
  ultimately have "\<lfloor>(x - (\<Sum>i<n. nth_cont x i))*2^(n+1)\<rfloor> =
                   \<lfloor>x * 2^(n+1)\<rfloor> - (\<Sum>i<n. (\<lfloor>x * (2 ^ (i+1))\<rfloor> mod 2) * (2 ^ (n-i)))"
    by linarith
  also from assms have "... = \<lfloor>x * 2 ^ (n + 1)\<rfloor> - (\<lfloor>x * 2 ^ (n + 1)\<rfloor> - \<lfloor>x * 2 ^ (n + 1)\<rfloor> mod 2)"
    by (subst modulus_2_via_shift_lemma, simp_all)
  finally show ?thesis
    by linarith
qed

lemma binlist_as_nth_cont:
  fixes x :: real
  assumes "0 \<le> x" "x < 1"
  shows "binlist (real_bits x n) = (\<Sum>i<n+1. nth_cont x i)"
proof (induct n)
  case 0 with assms show ?case
  proof -
    from assms have "\<lfloor>x * 2\<rfloor> = 0 \<or> \<lfloor>x * 2\<rfloor> = 1"
      by linarith
    thus ?thesis
      by (auto simp add: binlist_def nth_cont_def)
  qed
next
  case (Suc n) note hyp = this
  thus ?case
    using modulus_2_via_shift[of x "Suc n"] assms
      by (simp add: rbit_def nth_cont_def)
       (metis not_mod_2_eq_0_eq_1 of_int_0 of_int_1)
qed

lemma real_bits_rbseq:
  assumes "0 \<le> x" "x < 1" "n \<ge> i"
  shows "real_bits x n ! i = rbseq x i"
using assms proof (induct n arbitrary: i)
  case 0 with assms show ?case
    by (simp add: rbseq_def mod_pos_pos_trivial)
next
  case (Suc n')
  thus ?case
    using modulus_2_via_shift[of x "Suc n'"] assms
    by (auto simp add: nth_append rbit_def binlist_as_nth_cont rbseq_def)
qed

lemma real_bin_eq_rbseq:
  "\<lbrakk> 0 \<le> x; x < 1 \<rbrakk> \<Longrightarrow> real_bin x = rbseq x"
  by (auto simp add: real_bin_def real_bits_rbseq)

lemma of_int_floor: "\<lbrakk> 0 \<le> x; x < 1; of_int \<lfloor>x\<rfloor> = 0 \<rbrakk> \<Longrightarrow> \<lfloor>x\<rfloor> = 0"
  by (simp add: floor_unique)

lemma binlist_approaching_range:
  assumes "0 \<le> x" "x < 1"
  shows "x - binlist (real_bits x n) \<in> {0..<1/2^(n+1)}"
proof (induct n)
  case 0
  from assms have "0 \<le> x - binlist (real_bits x 0)"
  proof -
    from assms have "\<lfloor>x * 2\<rfloor> \<in> {0,1}"
      by (auto, linarith)
    with assms show ?thesis
      by (auto simp add: binlist_def, linarith)
  qed
  moreover from assms have "x - binlist (real_bits x 0) < 1/2^(0+1)"
    apply (simp add: binlist_def)
    apply (case_tac "of_int \<lfloor>x * 2\<rfloor> :: bit")
    apply (auto)
    apply (metis bit.distinct(1) floor_less_iff linorder_neqE_linordered_idom mult.left_neutral not_le of_int_1 one_less_floor mult_le_cancel_iff1 zero_less_numeral)
  done
  ultimately show ?case
    by auto
next
  case (Suc n) note hyp = this
  from hyp have blran: "(x - binlist (real_bits x n)) * (4 * 2 ^ n) \<in> {0..<2}"
    by (auto simp add: mult.commute mult.left_commute pos_less_divide_eq)
  show ?case
  proof (cases "rbit x n (real_bits x n)")
    case zero
    with hyp blran have "(x - binlist (real_bits x n)) * (4 * 2 ^ n) < 1"
      apply (auto simp add: rbit_def pos_less_divide_eq)
      apply (subgoal_tac "\<lfloor>(x - binlist (real_bits x n)) * (4 * 2 ^ n)\<rfloor> = 0")
      apply linarith
      apply (metis atLeastLessThan_iff bit.distinct(1) blran floor_less_one linorder_neqE_linordered_idom linorder_not_less of_int_1 of_int_floor one_less_floor)
    done
    with hyp zero show ?thesis
      by (auto simp add: mult_imp_less_div_pos)
  next
    case one
    with hyp blran have "(x - binlist (real_bits x n)) * (4 * 2 ^ n) \<ge> 1"
      by (auto simp add: rbit_def, metis atLeastLessThan_iff blran floor_less_iff linorder_neqE_linordered_idom not_le of_int_0 zero_less_floor zero_neq_one)
    with hyp one show ?thesis
      apply (auto)
      apply (subst add.commute)
      apply (simp add: le_diff_eq[THEN sym] pos_divide_le_eq)
    done
  qed
qed

lemma sum_binlist: "sum (binseq (real_bin x)) {..n} = binlist (real_bits x n)"
  apply (unfold binlist_def binseq_def real_bits_length real_bin_def)
  apply (rule sum.cong)
  apply (auto)
  apply (metis le_add_diff_inverse less_Suc_eq_le order_refl real_bits_plus)
  apply (metis diff_Suc_1 less_imp_Suc_add less_or_eq_imp_le real_bits_plus)
done

lemma sum_binseq_diff:
  "\<lbrakk> 0 \<le> x; x < 1 \<rbrakk> \<Longrightarrow> x - sum (binseq (real_bin x)) {..n} < 1/2^n"
  using binlist_approaching_range[of x n] sum_binlist by fastforce

lemma sum_binseq_approx: "\<lbrakk> 0 \<le> x; x < 1 \<rbrakk> \<Longrightarrow> sum (binseq (real_bin x)) {..n} \<le> x"
  using binlist_approaching_range[of x n] by (simp add: sum_binlist)

lemma sum_binseq_approx2:
  assumes "0 \<le> x" "x < 1"
  shows "sum (binseq (real_bin x)) {..<n} \<le> x"
proof (cases n)
  case 0 with assms show ?thesis by auto
next
  case (Suc n')
  with sum_binseq_approx[of x n'] assms
  show ?thesis
    by (simp add: lessThan_Suc_atMost)
qed

lemma binseq_approaches_real_bin:
  assumes "0 \<le> x" "x < 1"
  shows "(\<lambda> n. \<Sum> i<n. binseq (real_bin x) i) \<longlonglongrightarrow> x"
proof (rule LIMSEQ_I, simp)
  fix r :: real
  assume "0 < r"
  then obtain k where "1/2^k < r"
    using real_bin_lower_bound[of r] by blast
  moreover have "x - sum (binseq (real_bin x)) {..k} < 1/2^k"
    by (simp add: assms(1) assms(2) sum_binseq_diff)
  moreover have "\<And> m. m \<ge> k+1 \<Longrightarrow> sum (binseq (real_bin x)) {..<m} \<ge> sum (binseq (real_bin x)) {..k}"
    by (auto intro: sum_mono2 simp add: binseq_pos)
  ultimately have "\<And> m. m \<ge> k+1 \<Longrightarrow> x - sum (binseq (real_bin x)) {..<m} < r"
    by fastforce
  thus "\<exists>no. \<forall>n\<ge>no. \<bar>sum (binseq (real_bin x)) {..<n} - x\<bar> < r"
    by (rule_tac x="k+1" in exI, auto simp add: assms sum_binseq_approx2)
qed

lemma real_bin_inverse:
  assumes "0 \<le> x" "x < 1"
  shows "bin_real (real_bin x) = x"
  using assms
  apply (simp add: bin_real_def)
  apply (rule sym)
  apply (rule sums_unique)
  apply (simp add: sums_def binseq_approaches_real_bin)
done

lemma real_bin_inj:
  "inj_on real_bin {0..<1}"
  by (metis atLeastLessThan_iff inj_onI real_bin_inverse)

lemma sum_shift_plus_k:
  fixes f :: "nat \<Rightarrow> real"
  shows "(\<Sum> i<n. f (i + k)) = (sum f {k..<n+k})"
proof -
  have "(\<Sum> i<n. f (i + k)) = sum (\<lambda> i . f (i + k)) {0..<n}"
    by (simp add: atLeast0LessThan)
  thus ?thesis
    by (simp, subst sum.shift_bounds_nat_ivl[THEN sym], auto)
qed

lemma binseq_upper: "(\<Sum> i. binseq x (i+k)) \<le> 1/2^k"
proof (rule suminf_le_const)
  show "summable (\<lambda>i. binseq x (i + k))"
    by (simp add: summable_iff_shift binseq_summable)
next
  fix n
  have "(\<Sum>i<n. binseq x (i + k)) \<le> (\<Sum>i<n. 1 / 2 ^ (i + (k + 1)))"
  proof (rule sum_mono, unfold binseq_def)
    fix i
    assume "i \<in> {..<n}"
    thus "(of_bit (x (i + k)) / 2 ^ (i + k + 1) :: real) \<le> 1 / 2 ^ (i + (k + 1))"
      by (cases "x (i + k)", auto)
  qed
  also have "... \<le> 1/2^k"
  proof -
    have "(\<Sum>i<n. 1 / (2 :: real) ^ (i + (k + 1))) = ((\<Sum>i<n+k+1. (1 / 2) ^ i) - (\<Sum>i<k+1. (1 / 2) ^ i))"
      apply (subst sum_diff[THEN sym])
      apply (simp)
      apply (simp)
      apply (subst sum_shift_plus_k)
      apply (simp add: power_one_over)
    done
    also have "... = 1 / 2 ^ k - 1 / 2 ^ (n + k)"
      apply (subst geometric_sum)
      apply (simp)
      apply (subst geometric_sum)
      apply (simp)
      apply (simp add: power_one_over)
    done
    finally show ?thesis
      by (simp)
  qed
  finally show "(\<Sum>i<n. binseq x (i + k)) \<le> 1 / 2 ^ k" .
qed

lemma binseq_lower: "(\<Sum> i. binseq x (i+k)) \<ge> 0"
  apply (rule suminf_nonneg)
  apply (auto simp add: summable_iff_shift binseq_summable)
  apply (simp add: binseq_def)
done

lemma nonterminal_binseq_nonzero:
  assumes "nonterminal x"
  shows "(\<Sum> i. binseq x (i + k)) > 0"
proof -
  from assms obtain i where i:"x (i + k) = 1"
    by (auto simp add: terminal_def terminates_at_def, metis add.commute le_iff_add)
  thus ?thesis
  proof (rule_tac suminf_pos2[of _ i])
    show "summable (\<lambda>i. binseq x (i + k))"
      by (simp add: summable_iff_shift binseq_summable)
    show "\<And>n. 0 \<le> binseq x (n + k)"
      by (simp add: binseq_pos)
    from i show "0 < binseq x (i + k)"
      by (simp add: binseq_def)
  qed
qed

lemma list_neq_distinguish:
  assumes "xs \<noteq> ys" "length xs = length ys"
  shows "\<exists> k<length xs. (\<forall> i < k. xs!i = ys!i) \<and> xs!k \<noteq> ys!k"
using assms proof (induct xs arbitrary: ys)
  case Nil thus ?case by auto
next
  case (Cons x xs')
  note hyps = this
  then obtain y ys' where ys: "ys = y # ys'"
    by (metis length_0_conv neq_Nil_conv)
  thus ?case
  proof (cases "x = y")
    case False with hyps ys show ?thesis
      by (rule_tac x="0" in exI, simp)
  next
    case True
    with hyps ys have "xs' \<noteq> ys'"
      by (auto)
    moreover from hyps ys have "length xs' = length ys'"
      by (auto)
      thm hyps
    ultimately obtain k where "k<length xs'" "\<forall>i<k. xs' ! i = ys' ! i" "xs' ! k \<noteq> ys' ! k"
      using hyps by auto
    thus ?thesis
      using True ys less_Suc_eq_0_disj by (rule_tac x="Suc k" in exI, auto)
  qed
qed

lemma seq_neq_distinguish:
  fixes f :: "nat \<Rightarrow> 'b"
  assumes "f \<noteq> g"
  shows "\<exists> k. (\<forall> i < k. f(i) = g(i)) \<and> f(k) \<noteq> g(k)"
proof -
  from assms obtain k' where k': "f(k') \<noteq> g(k')"
    by auto
  let ?xs = "map f [0..<k'+1]"
  let ?ys = "map g [0..<k'+1]"
  from k' obtain k where k: "k < k'+1" "(\<forall> i < k. ?xs!i = ?ys!i)" "?xs!k \<noteq> ?ys!k"
    using list_neq_distinguish[of "?xs" "?ys"] by auto
  have "(\<forall>i<k. f i = g i)"
    by (auto, metis (no_types, lifting) add.left_neutral add_lessD1 diff_zero k(1) k(2) less_imp_add_positive nth_map_upt)
  moreover from k(3) have "f k \<noteq> g k"
    by (metis add.left_neutral diff_zero k(1) k(3) nth_map_upt)
  ultimately show ?thesis
    by (auto)
qed

lemma bin_real_nonterminal_inj_aux:
  assumes "nonterminal x" "nonterminal y" "x \<noteq> y"
  shows "bin_real x \<noteq> bin_real y"
proof -
  from assms(3) obtain k where k: "\<forall> i < k. x(i) = y(i)" "x(k) \<noteq> y(k)"
    using seq_neq_distinguish by blast
  have "bin_real x =
         (\<Sum>i<k. binseq x i) + of_bit (x k) / 2 ^(k+1) + (\<Sum>i. binseq x (i+(k+1)))"
    by (simp add: bin_real_def suminf_split_initial_segment[of _ "k+1"] binseq_summable)
       (simp add: binseq_def)
  moreover
  have "bin_real y =
         (\<Sum>i<k. binseq y i) + of_bit (y k) / 2 ^(k+1) + (\<Sum>i. binseq y (i+(k+1)))"
    by (simp add: bin_real_def suminf_split_initial_segment[of _ "k+1"] binseq_summable)
       (simp add: binseq_def)
  moreover
  from k(1) have "(\<Sum>i<k. binseq x i) = (\<Sum>i<k. binseq y i)"
    by (auto simp add: binseq_def)
  moreover
  have "of_bit (x k) / 2 ^(k+1) + (\<Sum>i. binseq x (i+(k+1))) \<noteq>
        of_bit (y k) / 2 ^(k+1) + (\<Sum>i. binseq y (i+(k+1)))"
  proof (cases "x k")
    case one
    moreover then have y:"y k = 0"
      using k(2) by auto
    moreover have "(\<Sum>i. binseq y (i + (k + 1))) \<le> 1/2^(k+1)"
      by (rule binseq_upper)
    moreover from assms(1) have "(\<Sum>i. binseq x (i + (k + 1))) > 0"
      by (rule nonterminal_binseq_nonzero)
    ultimately have "1 / 2^(k+1) + (\<Sum>i. binseq x (i+(k+1))) > (\<Sum>i. binseq y (i+(k+1)))"
      by simp
    with one y show ?thesis
      by simp
  next
    case zero
    moreover then have y:"y k = 1"
      using k(2) by auto
    moreover have "(\<Sum>i. binseq x (i + (k + 1))) \<le> 1/2^(k+1)"
      by (rule binseq_upper)
    moreover from assms(2) have "(\<Sum>i. binseq y (i + (k + 1))) > 0"
      by (rule nonterminal_binseq_nonzero)
    ultimately have "1 / 2^(k+1) + (\<Sum>i. binseq y (i+(k+1))) > (\<Sum>i. binseq x (i+(k+1)))"
      by simp
    with zero y show ?thesis
      by simp
  qed

  ultimately show ?thesis
    by auto
qed

text \<open> There is an injection from non-terminal infinite bit sequences to the real numbers \<close>

lemma bin_real_inj: "inj_on bin_real NonTermBitSeqs"
  using bin_real_nonterminal_inj_aux by (blast intro: inj_onI)

lemma bin_real_terminal_def:
  assumes "terminal x"
  obtains k where "bin_real x = (\<Sum>i<k. binseq x i)"
proof -
  from assms obtain k where "\<forall>i\<ge>k. x i = 0"
    by (auto simp add: terminal_def terminates_at_def)
  hence "bin_real x = (\<Sum>i<k. binseq x i)"
    unfolding bin_real_def
    by (subst suminf_finite[of "{..<k}"], auto simp add: binseq_def)
  thus ?thesis
    using that by blast
qed

lemma sum_int: "\<lbrakk> finite A; \<forall> i. f i \<in> \<int> \<rbrakk> \<Longrightarrow> sum f A \<in> \<int>"
  by (induct rule: finite_induct, simp_all)

lemma bin_real_terminal_dyadic:
  assumes "terminal x"
  shows "dyadic (bin_real x)"
proof -
  from assms obtain k where "bin_real x = (\<Sum>i<k. binseq x i)"
    using bin_real_terminal_def by blast
  also have "... = (\<Sum>i<k. (binseq x i * 2^k)) / 2^k"
    by (simp add: sum_divide_distrib)
  also have "... = (\<Sum>i<k. of_bit (x i) * 2 ^ (k - (i+1))) / 2 ^ k"
  proof -
    have "\<And>i. i \<in> {..<k} \<Longrightarrow> (of_bit (x i) :: real) / 2^(i+1) * 2^k = of_bit (x i) * 2^(k-(i+1))"
      by (simp add: power_diff)
    hence "(\<Sum>i<k. (binseq x i * 2^k)) = (\<Sum>i<k. of_bit (x i) * 2 ^ (k - (i+1)))"
      by (auto intro: sum.cong simp add: binseq_def)
    thus ?thesis by simp
  qed
  finally show ?thesis
  proof (simp)
    have "(\<Sum>i<k. of_bit (x i) * 2 ^ (k - (i + 1))) \<in> \<int>"
      by (auto intro!: sum_int)
    thus "dyadic ((\<Sum>i\<in>{..<k} \<inter> {i. x i = 1}. 2 ^ (k - Suc i)) / 2 ^ k)"
      by (auto simp add: dyadic_def)
  qed
qed

lemma terminal_rbseq_drat:
  "x \<in> {0<..<1} \<Longrightarrow> terminal (rbseq (of_drat x))"
proof (erule drat_0_1_induct, simp add: rbseq_def terminal_def terminates_at_def)
  fix a :: int and b :: nat
  assume coprime: "even a \<longrightarrow> b = 0"
  have "\<And> j. j \<ge> b \<Longrightarrow> of_int (\<lfloor>real_of_int a * (2 * 2 ^ j) / 2 ^ b\<rfloor> mod 2) = 0"
  proof -
    fix j
    assume "j \<ge> b"
    then have "real_of_int a * (2 * 2 ^ j) / 2 ^ b = real_of_int a * (2 * 2 ^ (j-b))"
      by (simp add: power_diff)
    moreover have "real_of_int a * (2 * 2 ^ (j-b)) \<in> \<int>"
      by simp
    moreover hence "\<lfloor>real_of_int a * (2 * 2 ^ (j-b))\<rfloor> mod 2 = (2 * \<lfloor>real_of_int a * 2 ^ (j - b)\<rfloor>) mod 2"
      by (metis (no_types, opaque_lifting) floor_of_int mult.left_commute of_int_mult of_int_numeral of_int_power)
    ultimately show "of_int (\<lfloor>real_of_int a * (2 * 2 ^ j) / 2 ^ b\<rfloor> mod 2) = 0"
      by simp
  qed
  with coprime show " \<exists>i. \<forall>j\<ge>i. of_int (\<lfloor>of_drat (DFract a b) * ((2::real) * 2 ^ j)\<rfloor> mod 2) = 0"
    by (rule_tac x="b" in exI, auto simp add:of_drat_DFract)
qed

lemma real_bin_dyadic_terminal:
  assumes "0 \<le> x" "x < 1" "x \<in> \<rat>\<^sub>D"
  shows "terminal (real_bin x)"
proof (cases "x = 0")
  case True thus ?thesis
    by (simp add: real_bin_eq_rbseq terminal_def terminates_at_def rbseq_def)
next
  case False
  from assms obtain n where n:"x = of_drat n"
     by (erule_tac drat_cases, auto)
  with assms False have nr: "n \<in> {0<..<1}"
    using of_drat_0_1 by force
  show ?thesis
    apply (subst real_bin_eq_rbseq)
    apply (simp_all add: assms)
    apply (simp add: n nr)
    apply (subst terminal_rbseq_drat)
    apply (simp_all only: nr)
  done
qed

lemma bin_real_terminates_binlist:
  assumes "terminates_at x k"
  shows "bin_real x = binlist (map x [0..<k])"
proof -
  from assms have "(\<Sum>n. binseq x (n + k)) = 0"
    by (simp add: suminf_eq_zero_iff binseq_summable summable_iff_shift binseq_def terminates_at_def)
  thus ?thesis
    apply (simp add: bin_real_def binlist_def)
    apply (subst suminf_split_initial_segment[of _ k])
    apply (simp add: binseq_summable)
    apply (simp add: binseq_def)
  done
qed

definition termseq_list :: "(nat \<Rightarrow> ('a::zero)) \<Rightarrow> 'a list" where
"termseq_list x = map x [0..<LEAST k. terminates_at x k]"

definition list_termseq :: "'a list \<Rightarrow> (nat \<Rightarrow> ('a::zero))" where
"list_termseq xs = (\<lambda> i. if (i < length xs) then xs!i else 0)"

definition "TermLists = {xs. xs = [] \<or> (xs \<noteq> [] \<and> last xs \<noteq> 0)}"

lemma TermLists_terminates_at:
  "xs \<in> TermLists \<Longrightarrow> terminates_at (list_termseq xs) k \<longleftrightarrow> k \<ge> length xs"
  apply (auto simp add: list_termseq_def terminates_at_def)
  apply (auto simp add: TermLists_def)
  using last_conv_nth not_less_eq_eq apply force
done

lemma terminal_list_termseq: "terminal (list_termseq xs)"
  apply (auto simp add: list_termseq_def terminal_def terminates_at_def)
  using not_le apply blast
done

lemma Least_terminates_at_list: "xs \<in> TermLists \<Longrightarrow> (LEAST k. terminates_at (list_termseq xs) k) = length xs"
  by (auto simp add: TermLists_terminates_at simp add: Least_equality)

lemma list_termseq_inverse:
  assumes "xs \<in> TermLists"
  shows "termseq_list (list_termseq xs) = xs"
proof -
  have "xs = map (\<lambda> i. xs ! i) [0..<length xs]"
    by (simp add: map_nth)
  also have "... = map (list_termseq xs) [0..<LEAST k. terminates_at (list_termseq xs) k]"
  proof -
    have "\<And>x. x < length xs \<Longrightarrow> xs ! x = list_termseq xs x"
      by (simp add: list_termseq_def)
    thus ?thesis
      by (auto simp add: Least_terminates_at_list assms)
  qed
  finally show ?thesis
    by (auto simp add: TermLists_def list_termseq_def termseq_list_def terminates_at_def)
qed

lemma termseq_list_inverse:
  assumes "x \<in> TermSeqs"
  shows "list_termseq (termseq_list x) = x"
  apply (rule ext)
  apply (auto simp add: list_termseq_def termseq_list_def)
  apply (metis (mono_tags, lifting) LeastI_ex assms le_less_linear mem_Collect_eq terminal_def terminates_at_def)
done

lemma termseq_list_inj:
  "inj_on termseq_list TermSeqs"
  by (metis inj_onI termseq_list_inverse)

lemma lenth_termseq_list:
  "length (termseq_list x) = (LEAST k. terminates_at x k)"
  by (simp add: termseq_list_def)

lemma terminal_TermLists:
  assumes "terminal x"
  shows "termseq_list x \<in> TermLists"
proof -
  let ?kx = "LEAST k. terminates_at x k"
  have tx: "terminates_at x ?kx"
    by (metis LeastI assms terminal_def)
  moreover have mt: "\<And> k. terminates_at x k \<Longrightarrow> ?kx \<le> k"
    by (auto intro: wellorder_Least_lemma)
  ultimately show ?thesis
  proof (auto simp add: TermLists_def)
    assume as: "termseq_list x \<noteq> []" "last (termseq_list x) = 0"
    hence kx_nz: "?kx > 0"
      by (metis length_greater_0_conv lenth_termseq_list)
    hence "x (?kx - 1) \<noteq> 0"
    proof -
      from kx_nz mt have nt_kxs: "\<not> terminates_at x (?kx - 1)"
        by (metis One_nat_def Suc_n_not_le_n diff_Suc_1 gr0_implies_Suc)
      show ?thesis
      proof
        assume "x (?kx - 1) = 0"
        moreover from tx have "\<forall>j\<ge>?kx. x j = 0"
          by (simp only: terminates_at_def)
        ultimately have "\<forall>j\<ge>?kx-1. x j = 0"
          by (auto, metis Suc_diff_Suc diff_zero kx_nz le_antisym not_less_eq_eq)
        hence "terminates_at x (?kx - 1)"
          by (simp only: terminates_at_def)
        with nt_kxs show False by simp
      qed
    qed

    with as show False
      by (simp add: termseq_list_def last_map)
  qed
qed

lemma termseq_list_surj:
  "termseq_list ` TermSeqs = TermLists"
  apply (auto simp add: terminal_TermLists)
  apply (auto simp add: image_Collect)
  apply (rule_tac x="list_termseq x" in exI)
  apply (simp add: list_termseq_inverse terminal_list_termseq)
done

lemma termseq_list_bij:
  "bij_betw termseq_list TermSeqs TermLists"
  by (simp add: bij_betw_def termseq_list_inj termseq_list_surj)

thm infinite_iff_countable_subset

lemma infinite_TermBitLists:
  "infinite (TermLists :: bit list set)"
proof -
  let ?f = "(\<lambda> i. replicate i 1) :: nat \<Rightarrow> bit list"
  have "inj ?f"
    by (meson injI replicate_eq_replicate)
  moreover have "range ?f \<subseteq> TermLists"
    by (auto simp add: TermLists_def)
  ultimately show ?thesis
    by (auto simp add: infinite_iff_countable_subset)
qed

instance bit :: countable
  apply (intro_classes)
  apply (rule_tac x="of_bit" in exI)
  apply (rule injI)
  apply (rename_tac x y)
  apply (case_tac x; case_tac y)
  apply (simp_all)
done

lemma countable_TermBitLists:
  "countable (TermLists :: bit list set)"
  by (fact countableI_type)

lemma card_of_TermBitLists:
  "|TermLists :: bit list set| =o |UNIV :: nat set|"
  apply (subst card_of_ordIso[THEN sym])
  using countable_TermBitLists infinite_TermBitLists to_nat_on_infinite apply blast
done

lemma card_of_TermBitSeqs:
  "|TermBitSeqs| =o |TermLists :: bit list set|"
  apply (subst card_of_ordIso[THEN sym])
using termseq_list_bij by blast

lemma card_less_TermBitSeqs_BitSeqs: "|TermBitSeqs| <o |BitSeqs|"
proof -
  have "|TermBitSeqs| =o |UNIV :: nat set|"
    using card_of_TermBitLists card_of_TermBitSeqs ordIso_transitive by blast
  moreover have "|UNIV :: nat set set| =o |BitSeqs|"
    by (simp add: card_of_bit_seq ordIso_symmetric)
  moreover have "|UNIV :: nat set| <o |UNIV :: nat set set|"
    using card_of_set_type by blast
  ultimately show ?thesis
    apply (rule_tac ordLess_ordIso_trans)
    apply (rule_tac ordIso_ordLess_trans)
    apply (assumption)
    apply (rule card_of_set_type)
    apply auto
  done
qed

lemma infinite_BitSeqs:
  "infinite BitSeqs"
  using bij_betw_finite bij_bits_to_nats infinite_UNIV by blast

lemma card_eq_NonTermBitSeqs_BitSeqs: "|NonTermBitSeqs| =o |BitSeqs|"
proof -
  have "|BitSeqs - TermBitSeqs| =o |BitSeqs|"
    apply (rule card_of_Un_diff_infinite)
    apply (simp_all add: infinite_BitSeqs card_less_TermBitSeqs_BitSeqs)
  done
  moreover have "BitSeqs - TermBitSeqs = NonTermBitSeqs"
    by (auto)
  ultimately show ?thesis
    by (simp)
qed

lemma card_le_NonTermBitSeqs_Reals: "|NonTermBitSeqs| \<le>o |UNIV :: real set|"
  using bin_real_inj card_of_ordLeqI by auto

lemma card_le_BitSeqs_Reals: "|BitSeqs| \<le>o |UNIV :: real set|"
  using card_eq_NonTermBitSeqs_BitSeqs card_le_NonTermBitSeqs_Reals ordIso_ordLess_trans ordIso_symmetric ordIso_transitive ordLeq_iff_ordLess_or_ordIso by blast

lemma card_le_PNats_Reals: "|UNIV :: nat set set| \<le>o |UNIV :: real set|"
  using card_le_BitSeqs_Reals card_of_bit_seq ordIso_iff_ordLeq ordLeq_transitive by blast

definition dcut :: "real \<Rightarrow> rat set" where
"dcut r = {q. real_of_rat q < r}"

lemma dedekind_cut_lemma:
  assumes "r1 < r2"
  shows "dcut r1 \<noteq> dcut r2"
proof -
  from assms obtain q :: rat where "r1 < of_rat q" and "of_rat q < r2"
    using of_rat_dense by auto
  hence "q \<notin> dcut r1" "q \<in> dcut r2"
    by (auto simp add: dcut_def)
  thus ?thesis
    by auto
qed

lemma dedekind_cut_inj:
  "inj dcut"
  by (simp add: dedekind_cut_lemma linorder_injI)

lemma real_nat_set: "\<exists> f :: real \<Rightarrow> nat set. inj f"
  apply (rule_tac x="\<lambda> n. to_nat ` dcut n" in exI)
  apply (simp add: dedekind_cut_lemma inj_image_eq_iff linorder_injI)
done

lemma card_le_Reals_PNats: "|UNIV :: real set| \<le>o |UNIV :: nat set set|"
proof -
  obtain f :: "real \<Rightarrow> nat set" where "inj f"
    using real_nat_set by blast
  thus ?thesis
    by (rule card_of_ordLeqI, auto)
qed

lemma card_eq_Reals_PNats: "|UNIV :: real set| =o |UNIV :: nat set set|"
  by (simp add: card_le_PNats_Reals card_le_Reals_PNats ordIso_iff_ordLeq)

definition real_nats_bij :: "real \<Rightarrow> nat set" where
"real_nats_bij = (SOME f. bij f)"

lemma real_nats_bij: "bij real_nats_bij"
proof -
  obtain f :: "real \<Rightarrow> nat set" where "bij f"
    using card_of_ordIso[of "UNIV :: real set" "UNIV :: nat set set"] card_eq_Reals_PNats
    by (auto)
  thus ?thesis
    by (simp add: real_nats_bij_def, metis someI_ex)
qed

lemma "|BitSeqs| =o |UNIV :: bit set| ^c |UNIV :: nat set|"
  by (simp add: card_of_Func_UNIV_UNIV cexp_def ordIso_symmetric)

declare [[linarith_split_limit=10]]

end