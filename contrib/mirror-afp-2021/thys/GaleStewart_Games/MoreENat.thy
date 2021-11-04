subsection \<open>Theorems about the extended naturals\<close>

text \<open>Extended naturals are the natural numbers plus infinity.
      They are slightly more cumbersome to reason about, and this file contains
      some lemmas that should help with that.\<close>

theory MoreENat
  imports MoreCoinductiveList2
begin

lemma eSuc_n_not_le_n[simp]:
"(eSuc x \<le> x) \<longleftrightarrow> x = \<infinity>"
  by (metis enat_ord_simps(3) Suc_n_not_le_n antisym ile_eSuc le_add2 plus_1_eq_Suc the_enat_eSuc)

lemma mult_two_impl1[elim]:
  assumes "a * 2 = 2 * b"
  shows "(a::enat) = b" using assms by(cases a;cases b,auto simp add: mult_2 mult_2_right)

lemma mult_two_impl2[dest]:
  assumes "a * 2 = 1 + 2 * b"
  shows "(a::enat) = \<infinity> \<and> b=\<infinity>"
  apply(cases a;cases b)
  using assms Suc_double_not_eq_double[unfolded mult_2, symmetric] 
  by (auto simp add: mult_2 one_enat_def mult_2_right)

lemma mult_two_impl3[dest]:
  assumes "a * 2 = 1 + (2 * b - 1)"
  shows "(a::enat) = b \<and> a \<ge> 1"
  using assms by(cases a;cases b,auto simp add: one_enat_def mult_2 mult_2_right)

lemma mult_two_impl4[dest]:
  assumes "a * 2 = 2 * b - 1"
  shows "((a::enat) = 0 \<and> b = 0) \<or> (a = \<infinity> \<and> b=\<infinity>)"
proof(cases a;cases b)
  fix anat bnat
  assume *:"a = enat anat" "b = enat bnat"
  hence "anat + anat = bnat + bnat - Suc 0"
    using assms by (auto simp add:enat_0_iff one_enat_def mult_2 mult_2_right)
  thus ?thesis unfolding * using Suc_double_not_eq_double[unfolded mult_2, symmetric]
    by (metis Suc_pred add_gr_0 enat_0_iff(1) neq0_conv not_less0 zero_less_diff)
qed(insert assms,auto simp add:enat_0_iff one_enat_def mult_2 mult_2_right)


lemma times_two_div_two[intro]:
  assumes "enat n < x" shows "2 * enat (n div 2) < x"
proof -
  have "2 * n div 2 \<le> n" by auto
  hence "2 * enat (n div 2) \<le> enat n"
    using enat_numeral enat_ord_simps(2) linorder_not_less mult.commute times_enat_simps(1) 
  by (metis div_times_less_eq_dividend)
  with assms show ?thesis by auto
qed

lemma enat_sum_le[simp]:
  shows "enat (a + b) \<le> c \<Longrightarrow> b \<le> c"
  by (meson dual_order.trans enat_ord_simps(1) le_add2)


lemma enat_Suc_nonzero[simp]:
shows "enat (Suc n)\<noteq> 0"
 by (metis Zero_not_Suc enat.inject zero_enat_def)

end