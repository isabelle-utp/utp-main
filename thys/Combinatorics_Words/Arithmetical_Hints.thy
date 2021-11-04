(*  Title:      CoW/Arithmetical_Hints.thy
    Author:     Štěpán Holub, Charles University
    Author:     Martin Raška, Charles University
    Author:     Štěpán Starosta, CTU in Prague
*)

theory Arithmetical_Hints
  imports Main
begin

section "Arithmetical hints"

text\<open>In this section we give some specific auxiliary lemmas on natural integers.\<close>

lemma zero_diff_eq: "i \<le> j \<Longrightarrow> (0::nat) = j - i  \<Longrightarrow> j = i"
  by simp

lemma zero_less_diff': "i < j \<Longrightarrow> j - i \<noteq> (0::nat)" 
   by simp

lemma nat_prod_le: "m \<noteq> (0 :: nat) \<Longrightarrow> m*n \<le> k \<Longrightarrow> n \<le> k"
  using le_trans[of n "m*n" k] by auto

lemma get_div: "(p :: nat) < a \<Longrightarrow> m = (m * a + p) div a"
  by simp

lemma get_mod: "(p :: nat) < a \<Longrightarrow> p = (m * a + p) mod a"
  by simp

lemma plus_one_between:  "(a :: nat) < b \<Longrightarrow> \<not> b < a + 1"
  by auto

lemma quotient_smaller: "a \<noteq> 0 \<Longrightarrow> a = k * b \<Longrightarrow> b \<le> (a::nat)" 
  by simp

lemma mult_cancel_le: "b \<noteq> 0 \<Longrightarrow> a*b \<le> c*b \<Longrightarrow> a \<le> (c::nat)" 
  by simp

lemma add_lessD2: assumes "k + m < (n::nat)" shows "m < n" 
  using add_lessD1[OF assms[unfolded add.commute[of k m]]].

lemma mod_offset:  assumes "M \<noteq> (0 :: nat)"
  obtains k where "n mod M = (l + k) mod M"
proof-
  have "(l + (M - l mod M)) mod M = 0"
    using mod_add_left_eq[of l M "(M - l mod M)", unfolded le_add_diff_inverse[OF mod_le_divisor[OF assms[unfolded neq0_conv]], of l] mod_self, symmetric].
  from mod_add_left_eq[of "(l + (M - l mod M))" M n, symmetric, unfolded this add.commute[of 0] add.comm_neutral]
  have "((l + (M - l mod M)) + n) mod M = n mod M".
  from that[OF this[unfolded add.assoc, symmetric]]
  show thesis.
qed

lemma assumes "q \<noteq> (0::nat)" shows "p \<le> p + q - gcd p q"
  using gcd_le2_nat[OF \<open>q \<noteq> 0\<close>, of p]
  by linarith

lemma less_mult_one: assumes "(m-1)*k < k" obtains "m = 0" | "m = (1::nat)"
  using assms by fastforce

end