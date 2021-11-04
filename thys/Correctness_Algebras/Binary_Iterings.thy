(* Title:      Binary Iterings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Binary Iterings\<close>

theory Binary_Iterings

imports Base

begin

class binary_itering = idempotent_left_zero_semiring + while +
  assumes while_productstar: "(x * y) \<star> z = z \<squnion> x * ((y * x) \<star> (y * z))"
  assumes while_sumstar: "(x \<squnion> y) \<star> z = (x \<star> y) \<star> (x \<star> z)"
  assumes while_left_dist_sup: "x \<star> (y \<squnion> z) = (x \<star> y) \<squnion> (x \<star> z)"
  assumes while_sub_associative: "(x \<star> y) * z \<le> x \<star> (y * z)"
  assumes while_simulate_left_plus: "x * z \<le> z * (y \<star> 1) \<squnion> w \<longrightarrow> x \<star> (z * v) \<le> z * (y \<star> v) \<squnion> (x \<star> (w * (y \<star> v)))"
  assumes while_simulate_right_plus: "z * x \<le> y * (y \<star> z) \<squnion> w \<longrightarrow> z * (x \<star> v) \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
begin

text \<open>Theorem 9.1\<close>

lemma while_zero:
  "bot \<star> x = x"
  by (metis sup_bot_right mult_left_zero while_productstar)

text \<open>Theorem 9.4\<close>

lemma while_mult_increasing:
  "x * y \<le> x \<star> y"
  by (metis le_supI2 mult.left_neutral mult_left_sub_dist_sup_left while_productstar)

text \<open>Theorem 9.2\<close>

lemma while_one_increasing:
  "x \<le> x \<star> 1"
  by (metis mult.right_neutral while_mult_increasing)

text \<open>Theorem 9.3\<close>

lemma while_increasing:
  "y \<le> x \<star> y"
  by (metis sup_left_divisibility mult_left_one while_productstar)

text \<open>Theorem 9.42\<close>

lemma while_right_isotone:
  "y \<le> z \<Longrightarrow> x \<star> y \<le> x \<star> z"
  by (metis le_iff_sup while_left_dist_sup)

text \<open>Theorem 9.41\<close>

lemma while_left_isotone:
  "x \<le> y \<Longrightarrow> x \<star> z \<le> y \<star> z"
  using sup_left_divisibility while_sumstar while_increasing by auto

lemma while_isotone:
  "w \<le> x \<Longrightarrow> y \<le> z \<Longrightarrow> w \<star> y \<le> x \<star> z"
  by (meson order_lesseq_imp while_left_isotone while_right_isotone)

text \<open>Theorem 9.17\<close>

lemma while_left_unfold:
  "x \<star> y = y \<squnion> x * (x \<star> y)"
  by (metis mult_1_left mult_1_right while_productstar)

lemma while_simulate_left_plus_1:
  "x * z \<le> z * (y \<star> 1) \<Longrightarrow> x \<star> (z * w) \<le> z * (y \<star> w) \<squnion> (x \<star> bot)"
  by (metis sup_bot_right mult_left_zero while_simulate_left_plus)

text \<open>Theorem 11.1\<close>

lemma while_simulate_absorb:
  "y * x \<le> x \<Longrightarrow> y \<star> x \<le> x \<squnion> (y \<star> bot)"
  by (metis while_simulate_left_plus_1 while_zero mult_1_right)

text \<open>Theorem 9.10\<close>

lemma while_transitive:
  "x \<star> (x \<star> y) = x \<star> y"
  by (metis order.eq_iff sup_bot_right sup_ge2 while_left_dist_sup while_increasing while_left_unfold while_simulate_absorb)

text \<open>Theorem 9.25\<close>

lemma while_slide:
  "(x * y) \<star> (x * z) = x * ((y * x) \<star> z)"
  by (metis mult_left_dist_sup while_productstar mult_assoc while_left_unfold)

text \<open>Theorem 9.21\<close>

lemma while_zero_2:
  "(x * bot) \<star> y = x * bot \<squnion> y"
  by (metis mult_left_zero sup_commute mult_assoc while_left_unfold)

text \<open>Theorem 9.5\<close>

lemma while_mult_star_exchange:
  "x * (x \<star> y) = x \<star> (x * y)"
  by (metis mult_left_one while_slide)

text \<open>Theorem 9.18\<close>

lemma while_right_unfold:
  "x \<star> y = y \<squnion> (x \<star> (x * y))"
  by (metis while_left_unfold while_mult_star_exchange)

text \<open>Theorem 9.7\<close>

lemma while_one_mult_below:
  "(x \<star> 1) * y \<le> x \<star> y"
  by (metis mult_left_one while_sub_associative)

lemma while_plus_one:
  "x \<star> y = y \<squnion> (x \<star> y)"
  by (simp add: sup.absorb2 while_increasing)

text \<open>Theorem 9.19\<close>

lemma while_rtc_2:
  "y \<squnion> x * y \<squnion> (x \<star> (x \<star> y)) = x \<star> y"
  by (simp add: sup_absorb2 while_increasing while_mult_increasing while_transitive)

text \<open>Theorem 9.6\<close>

lemma while_left_plus_below:
  "x * (x \<star> y) \<le> x \<star> y"
  by (metis sup_right_divisibility while_left_unfold)

lemma while_right_plus_below:
  "x \<star> (x * y) \<le> x \<star> y"
  using while_left_plus_below while_mult_star_exchange by auto

lemma while_right_plus_below_2:
  "(x \<star> x) * y \<le> x \<star> y"
  by (smt order_trans while_right_plus_below while_sub_associative)

text \<open>Theorem 9.47\<close>

lemma while_mult_transitive:
  "x \<le> z \<star> y \<Longrightarrow> y \<le> z \<star> w \<Longrightarrow> x \<le> z \<star> w"
  by (smt order_trans while_right_isotone while_transitive)

text \<open>Theorem 9.48\<close>

lemma while_mult_upper_bound:
  "x \<le> z \<star> 1 \<Longrightarrow> y \<le> z \<star> w \<Longrightarrow> x * y \<le> z \<star> w"
  by (metis order.trans mult_isotone while_one_mult_below while_transitive)

lemma while_one_mult_while_below:
  "(y \<star> 1) * (y \<star> v) \<le> y \<star> v"
  by (simp add: while_mult_upper_bound)

text \<open>Theorem 9.34\<close>

lemma while_sub_dist:
  "x \<star> z \<le> (x \<squnion> y) \<star> z"
  by (simp add: while_left_isotone)

lemma while_sub_dist_1:
  "x * z \<le> (x \<squnion> y) \<star> z"
  using order.trans while_mult_increasing while_sub_dist by blast

lemma while_sub_dist_2:
  "x * y * z \<le> (x \<squnion> y) \<star> z"
  by (metis sup_commute mult_assoc while_mult_transitive while_sub_dist_1)

text \<open>Theorem 9.36\<close>

lemma while_sub_dist_3:
  "x \<star> (y \<star> z) \<le> (x \<squnion> y) \<star> z"
  by (metis sup_commute while_mult_transitive while_sub_dist)

text \<open>Theorem 9.44\<close>

lemma while_absorb_2:
  "x \<le> y \<Longrightarrow> y \<star> (x \<star> z) = y \<star> z"
  using sup_left_divisibility while_sumstar while_transitive by auto

lemma while_simulate_right_plus_1:
  "z * x \<le> y * (y \<star> z) \<Longrightarrow> z * (x \<star> w) \<le> y \<star> (z * w)"
  by (metis sup_bot_right mult_left_zero while_simulate_right_plus)

text \<open>Theorem 9.39\<close>

lemma while_sumstar_1_below:
  "x \<star> ((y * (x \<star> 1)) \<star> z) \<le> ((x \<star> 1) * y) \<star> (x \<star> z)"
proof -
  have 1: "x * (((x \<star> 1) * y) \<star> (x \<star> z)) \<le> ((x \<star> 1) * y) \<star> (x \<star> z)"
    by (smt sup_mono sup_ge2 mult_assoc mult_left_dist_sup mult_right_sub_dist_sup_right while_left_unfold)
  have "x \<star> ((y * (x \<star> 1)) \<star> z) \<le> (x \<star> z) \<squnion> (x \<star> (y * (((x \<star> 1) * y) \<star> ((x \<star> 1) * z))))"
    by (metis eq_refl while_left_dist_sup while_productstar)
  also have "... \<le> (x \<star> z) \<squnion> (x \<star> ((x \<star> 1) * y * (((x \<star> 1) * y) \<star> ((x \<star> 1) * z))))"
    by (metis sup_right_isotone mult_assoc mult_left_one mult_right_sub_dist_sup_left while_left_unfold while_right_isotone)
  also have "... \<le> (x \<star> z) \<squnion> (x \<star> (((x \<star> 1) * y) \<star> ((x \<star> 1) * z)))"
    using semiring.add_left_mono while_left_plus_below while_right_isotone by blast
  also have "... \<le> x \<star> (((x \<star> 1) * y) \<star> (x \<star> z))"
    by (meson order.trans le_supI while_increasing while_one_mult_below while_right_isotone)
  also have "... \<le> (((x \<star> 1) * y) \<star> (x \<star> z)) \<squnion> (x \<star> bot)"
    using 1 while_simulate_absorb by auto
  also have "... = ((x \<star> 1) * y) \<star> (x \<star> z)"
    by (smt sup_assoc sup_commute sup_bot_left while_left_dist_sup while_left_unfold)
  finally show ?thesis
    .
qed

lemma while_sumstar_2_below:
  "((x \<star> 1) * y) \<star> (x \<star> z) \<le> (x \<star> y) \<star> (x \<star> z)"
  by (simp add: while_left_isotone while_one_mult_below)

text \<open>Theorem 9.38\<close>

lemma while_sup_1_below:
  "x \<star> ((y * (x \<star> 1)) \<star> z) \<le> (x \<squnion> y) \<star> z"
proof -
  have "((x \<star> 1) * y) \<star> ((x \<star> 1) * z) \<le> (x \<squnion> y) \<star> z"
    using while_sumstar while_isotone while_one_mult_below by auto
  hence "(y * (x \<star> 1)) \<star> z \<le> z \<squnion> y * ((x \<squnion> y) \<star> z)"
    by (metis sup_right_isotone mult_right_isotone while_productstar)
  also have "... \<le> (x \<squnion> y) \<star> z"
    by (metis sup_right_isotone sup_ge2 mult_left_isotone while_left_unfold)
  finally show ?thesis
    using while_mult_transitive while_sub_dist by blast
qed

text \<open>Theorem 9.16\<close>

lemma while_while_while:
  "((x \<star> 1) \<star> 1) \<star> y = (x \<star> 1) \<star> y"
  by (smt (z3) sup.absorb1 while_sumstar while_absorb_2 while_increasing while_one_increasing)

lemma while_one:
  "(1 \<star> 1) \<star> y = 1 \<star> y"
  by (metis while_while_while while_zero)

text \<open>Theorem 9.22\<close>

lemma while_sup_below:
  "x \<squnion> y \<le> x \<star> (y \<star> 1)"
  by (metis le_supI le_supI1 while_left_dist_sup while_left_unfold while_one_increasing)

text \<open>Theorem 9.32\<close>

lemma while_sup_2:
  "(x \<squnion> y) \<star> z \<le> (x \<star> (y \<star> 1)) \<star> z"
  using while_left_isotone while_sup_below by auto

text \<open>Theorem 9.45\<close>

lemma while_sup_one_left_unfold:
  "1 \<le> x \<Longrightarrow> x * (x \<star> y) = x \<star> y"
  by (metis order.antisym mult_1_left mult_left_isotone while_left_plus_below)

lemma while_sup_one_right_unfold:
  "1 \<le> x \<Longrightarrow> x \<star> (x * y) = x \<star> y"
  using while_mult_star_exchange while_sup_one_left_unfold by auto

text \<open>Theorem 9.30\<close>

lemma while_decompose_7:
  "(x \<squnion> y) \<star> z = x \<star> (y \<star> ((x \<squnion> y) \<star> z))"
  by (metis order.eq_iff order_trans while_increasing while_sub_dist_3 while_transitive)

text \<open>Theorem 9.31\<close>

lemma while_decompose_8:
  "(x \<squnion> y) \<star> z = (x \<squnion> y) \<star> (x \<star> (y \<star> z))"
  using while_absorb_2 by auto

text \<open>Theorem 9.27\<close>

lemma while_decompose_9:
  "(x \<star> (y \<star> 1)) \<star> z = x \<star> (y \<star> ((x \<star> (y \<star> 1)) \<star> z))"
  by (smt sup_commute le_iff_sup order_trans while_sup_below while_increasing while_sub_dist_3)

lemma while_decompose_10:
  "(x \<star> (y \<star> 1)) \<star> z = (x \<star> (y \<star> 1)) \<star> (x \<star> (y \<star> z))"
proof -
  have 1: "(x \<star> (y \<star> 1)) \<star> z \<le> (x \<star> (y \<star> 1)) \<star> (x \<star> (y \<star> z))"
    by (meson order.trans while_increasing while_right_isotone)
  have "x \<squnion> (y \<star> 1) \<le> x \<star> (y \<star> 1)"
    using while_increasing while_sup_below by auto
  hence "(x \<star> (y \<star> 1)) \<star> (x \<star> (y \<star> z)) \<le> (x \<star> (y \<star> 1)) \<star> z"
    using while_absorb_2 while_sup_below by force
  thus ?thesis
    using 1 order.antisym by blast
qed

lemma while_back_loop_fixpoint:
  "z * (y \<star> (y * x)) \<squnion> z * x = z * (y \<star> x)"
  by (metis sup_commute mult_left_dist_sup while_right_unfold)

lemma while_back_loop_prefixpoint:
  "z * (y \<star> 1) * y \<squnion> z \<le> z * (y \<star> 1)"
  by (metis le_supI le_supI2 mult_1_right mult_right_isotone mult_assoc while_increasing while_one_mult_below while_right_unfold)

text \<open>Theorem 9\<close>

lemma while_loop_is_fixpoint:
  "is_fixpoint (\<lambda>x . y * x \<squnion> z) (y \<star> z)"
  using is_fixpoint_def sup_commute while_left_unfold by auto

text \<open>Theorem 9\<close>

lemma while_back_loop_is_prefixpoint:
  "is_prefixpoint (\<lambda>x . x * y \<squnion> z) (z * (y \<star> 1))"
  using is_prefixpoint_def while_back_loop_prefixpoint by auto

text \<open>Theorem 9.20\<close>

lemma while_while_sup:
  "(1 \<squnion> x) \<star> y = (x \<star> 1) \<star> y"
  by (metis sup_commute while_decompose_10 while_sumstar while_zero)

lemma while_while_mult_sub:
  "x \<star> (1 \<star> y) \<le> (x \<star> 1) \<star> y"
  by (metis sup_commute while_sub_dist_3 while_while_sup)

text \<open>Theorem 9.11\<close>

lemma while_right_plus:
  "(x \<star> x) \<star> y = x \<star> y"
  by (metis sup_idem while_plus_one while_sumstar while_transitive)

text \<open>Theorem 9.12\<close>

lemma while_left_plus:
  "(x * (x \<star> 1)) \<star> y = x \<star> y"
  by (simp add: while_mult_star_exchange while_right_plus)

text \<open>Theorem 9.9\<close>

lemma while_below_while_one:
  "x \<star> x \<le> x \<star> 1"
  by (meson eq_refl while_mult_transitive while_one_increasing)

lemma while_below_while_one_mult:
  "x * (x \<star> x) \<le> x * (x \<star> 1)"
  by (simp add: mult_right_isotone while_below_while_one)

text \<open>Theorem 9.23\<close>

lemma while_sup_sub_sup_one:
  "x \<star> (x \<squnion> y) \<le> x \<star> (1 \<squnion> y)"
  using semiring.add_right_mono while_left_dist_sup while_below_while_one by auto

lemma while_sup_sub_sup_one_mult:
  "x * (x \<star> (x \<squnion> y)) \<le> x * (x \<star> (1 \<squnion> y))"
  by (simp add: mult_right_isotone while_sup_sub_sup_one)

lemma while_elimination:
  "x * y = bot \<Longrightarrow> x * (y \<star> z) = x * z"
  by (metis sup_bot_right mult_assoc mult_left_dist_sup mult_left_zero while_left_unfold)

text \<open>Theorem 9.8\<close>

lemma while_square:
  "(x * x) \<star> y \<le> x \<star> y"
  by (metis while_left_isotone while_mult_increasing while_right_plus)

text \<open>Theorem 9.35\<close>

lemma while_mult_sub_sup:
  "(x * y) \<star> z \<le> (x \<squnion> y) \<star> z"
  by (metis while_increasing while_isotone while_mult_increasing while_sumstar)

text \<open>Theorem 9.43\<close>

lemma while_absorb_1:
  "x \<le> y \<Longrightarrow> x \<star> (y \<star> z) = y \<star> z"
  by (metis order.antisym le_iff_sup while_increasing while_sub_dist_3)

lemma while_absorb_3:
  "x \<le> y \<Longrightarrow> x \<star> (y \<star> z) = y \<star> (x \<star> z)"
  by (simp add: while_absorb_1 while_absorb_2)

text \<open>Theorem 9.24\<close>

lemma while_square_2:
  "(x * x) \<star> ((x \<squnion> 1) * y) \<le> x \<star> y"
  by (metis le_supI while_increasing while_mult_transitive while_mult_upper_bound while_one_increasing while_square)

lemma while_separate_unfold_below:
  "(y * (x \<star> 1)) \<star> z \<le> (y \<star> z) \<squnion> (y \<star> (y * x * (x \<star> ((y * (x \<star> 1)) \<star> z))))"
proof -
  have "(y * (x \<star> 1)) \<star> z = (y \<star> (y * x * (x \<star> 1))) \<star> (y \<star> z)"
    by (metis mult_assoc mult_left_dist_sup mult_1_right while_left_unfold while_sumstar)
  hence "(y * (x \<star> 1)) \<star> z = (y \<star> z) \<squnion> (y \<star> (y * x * (x \<star> 1))) * ((y * (x \<star> 1)) \<star> z)"
    using while_left_unfold by auto
  also have "... \<le> (y \<star> z) \<squnion> (y \<star> (y * x * (x \<star> 1)) * ((y * (x \<star> 1)) \<star> z))"
    using sup_right_isotone while_sub_associative by auto
  also have "... \<le> (y \<star> z) \<squnion> (y \<star> (y * x * (x \<star> ((y * (x \<star> 1)) \<star> z))))"
    by (smt sup_right_isotone mult_assoc mult_right_isotone while_one_mult_below while_right_isotone)
  finally show ?thesis
    .
qed

text \<open>Theorem 9.33\<close>

lemma while_mult_zero_sup:
  "(x \<squnion> y * bot) \<star> z = x \<star> ((y * bot) \<star> z)"
proof -
  have "(x \<squnion> y * bot) \<star> z = (x \<star> (y * bot)) \<star> (x \<star> z)"
    by (simp add: while_sumstar)
  also have "... = (x \<star> z) \<squnion> (x \<star> (y * bot)) * ((x \<star> (y * bot)) \<star> (x \<star> z))"
    using while_left_unfold by auto
  also have "... \<le> (x \<star> z) \<squnion> (x \<star> (y * bot))"
    by (metis sup_right_isotone mult_assoc mult_left_zero while_sub_associative)
  also have "... = x \<star> ((y * bot) \<star> z)"
    by (simp add: sup_commute while_left_dist_sup while_zero_2)
  finally show ?thesis
    by (simp add: order.antisym while_sub_dist_3)
qed

lemma while_sup_mult_zero:
  "(x \<squnion> y * bot) \<star> y = x \<star> y"
  by (simp add: sup_absorb2 zero_right_mult_decreasing while_mult_zero_sup while_zero_2)

lemma while_mult_zero_sup_2:
  "(x \<squnion> y * bot) \<star> z = (x \<star> z) \<squnion> (x \<star> (y * bot))"
  by (simp add: sup_commute while_left_dist_sup while_mult_zero_sup while_zero_2)

lemma while_sup_zero_star:
  "(x \<squnion> y * bot) \<star> z = x \<star> (y * bot \<squnion> z)"
  by (simp add: while_mult_zero_sup while_zero_2)

lemma while_unfold_sum:
  "(x \<squnion> y) \<star> z = (x \<star> z) \<squnion> (x \<star> (y * ((x \<squnion> y) \<star> z)))"
  apply (rule order.antisym)
  apply (metis semiring.add_left_mono while_sub_associative while_sumstar while_left_unfold)
  by (metis le_supI while_decompose_7 while_mult_increasing while_right_isotone while_sub_dist)

lemma while_simulate_left:
  "x * z \<le> z * y \<squnion> w \<Longrightarrow> x \<star> (z * v) \<le> z * (y \<star> v) \<squnion> (x \<star> (w * (y \<star> v)))"
  by (metis sup_left_isotone mult_right_isotone order_trans while_one_increasing while_simulate_left_plus)

lemma while_simulate_right:
  assumes "z * x \<le> y * z \<squnion> w"
    shows "z * (x \<star> v) \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
proof -
  have "y * z \<squnion> w \<le> y * (y \<star> z) \<squnion> w"
    using sup_left_isotone while_increasing while_mult_star_exchange by force
  thus ?thesis
    by (meson assms order.trans while_simulate_right_plus)
qed

lemma while_simulate:
  "z * x \<le> y * z \<Longrightarrow> z * (x \<star> v) \<le> y \<star> (z * v)"
  by (metis sup_bot_right mult_left_zero while_simulate_right)

text \<open>Theorem 9.14\<close>

lemma while_while_mult:
  "1 \<star> (x \<star> y) = (x \<star> 1) \<star> y"
proof -
  have "(x \<star> 1) \<star> y \<le> (x \<star> 1) * ((x \<star> 1) \<star> y)"
    by (simp add: while_increasing while_sup_one_left_unfold)
  also have "... \<le> 1 \<star> ((x \<star> 1) * y)"
    by (simp add: while_one_mult_while_below while_simulate)
  also have "... \<le> 1 \<star> (x \<star> y)"
    by (simp add: while_isotone while_one_mult_below)
  finally show ?thesis
    by (metis order.antisym while_sub_dist_3 while_while_sup)
qed

lemma while_simulate_left_1:
  "x * z \<le> z * y \<Longrightarrow> x \<star> (z * v) \<le> z * (y \<star> v) \<squnion> (x \<star> bot)"
  by (meson order.trans mult_right_isotone while_one_increasing while_simulate_left_plus_1)

text \<open>Theorem 9.46\<close>

lemma while_associative_1:
  assumes "1 \<le> z"
  shows "x \<star> (y * z) = (x \<star> y) * z"
proof -
  have "x \<star> (y * z) \<le> x \<star> ((x \<star> y) * z)"
    by (simp add: mult_isotone while_increasing while_right_isotone)
  also have "... \<le> (x \<star> y) * (bot \<star> z) \<squnion> (x \<star> bot)"
    by (metis mult_assoc mult_right_sub_dist_sup_right while_left_unfold while_simulate_absorb while_zero)
  also have "... \<le> (x \<star> y) * z \<squnion> (x \<star> bot) * z"
    by (metis assms le_supI sup_ge1 sup_ge2 case_split_right while_plus_one while_zero)
  also have "... = (x \<star> y) * z"
    by (metis sup_bot_right mult_right_dist_sup while_left_dist_sup)
  finally show ?thesis
    by (simp add: order.antisym while_sub_associative)
qed

text \<open>Theorem 9.29\<close>

lemma while_associative_while_1:
  "x \<star> (y * (z \<star> 1)) = (x \<star> y) * (z \<star> 1)"
  by (simp add: while_associative_1 while_increasing)

text \<open>Theorem 9.13\<close>

lemma while_one_while:
  "(x \<star> 1) * (y \<star> 1) = x \<star> (y \<star> 1)"
  by (metis mult_left_one while_associative_while_1)

lemma while_decompose_5_below:
  "(x \<star> (y \<star> 1)) \<star> z \<le> (y \<star> (x \<star> 1)) \<star> z"
  by (smt (z3) while_left_dist_sup while_sumstar while_absorb_2 while_one_increasing while_plus_one while_sub_dist)

text \<open>Theorem 9.26\<close>

lemma while_decompose_5:
  "(x \<star> (y \<star> 1)) \<star> z = (y \<star> (x \<star> 1)) \<star> z"
  by (simp add: order.antisym while_decompose_5_below)

lemma while_decompose_4:
  "(x \<star> (y \<star> 1)) \<star> z = x \<star> ((y \<star> (x \<star> 1)) \<star> z)"
  using while_absorb_1 while_decompose_5 while_sup_below by auto

text \<open>Theorem 11.7\<close>

lemma while_simulate_2:
  "y * (x \<star> 1) \<le> x \<star> (y \<star> 1) \<longleftrightarrow> y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1)"
proof
  assume "y * (x \<star> 1) \<le> x \<star> (y \<star> 1)"
  hence "y * (x \<star> 1) \<le> (x \<star> 1) * (y \<star> 1)"
    by (simp add: while_one_while)
  hence "y \<star> ((x \<star> 1) * 1) \<le> (x \<star> 1) * (y \<star> 1) \<squnion> (y \<star> bot)"
    using while_simulate_left_plus_1 by blast
  hence "y \<star> (x \<star> 1) \<le> (x \<star> (y \<star> 1)) \<squnion> (y \<star> bot)"
    by (simp add: while_one_while)
  also have "... = x \<star> (y \<star> 1)"
    by (metis sup_commute le_iff_sup order_trans while_increasing while_right_isotone bot_least)
  finally show "y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1)"
    .
next
  assume "y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1)"
  thus "y * (x \<star> 1) \<le> x \<star> (y \<star> 1)"
    using order_trans while_mult_increasing by blast
qed

lemma while_simulate_1:
  "y * x \<le> x * y \<Longrightarrow> y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1)"
  by (metis order_trans while_mult_increasing while_right_isotone while_simulate while_simulate_2)

lemma while_simulate_3:
  "y * (x \<star> 1) \<le> x \<star> 1 \<Longrightarrow> y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1)"
  by (meson order.trans while_increasing while_right_isotone while_simulate_2)

text \<open>Theorem 9.28\<close>

lemma while_extra_while:
  "(y * (x \<star> 1)) \<star> z = (y * (y \<star> (x \<star> 1))) \<star> z"
proof -
  have "y * (y \<star> (x \<star> 1)) \<le> y * (x \<star> 1) * (y * (x \<star> 1) \<star> 1)"
    using while_back_loop_prefixpoint while_left_isotone while_mult_star_exchange by auto
  hence 1: "(y * (y \<star> (x \<star> 1))) \<star> z \<le> (y * (x \<star> 1)) \<star> z"
    by (metis while_simulate_right_plus_1 mult_left_one)
  have "(y * (x \<star> 1)) \<star> z \<le> (y * (y \<star> (x \<star> 1))) \<star> z"
    by (simp add: while_increasing while_left_isotone while_mult_star_exchange)
  thus ?thesis
    using 1 order.antisym by auto
qed

text \<open>Theorem 11.6\<close>

lemma while_separate_4:
  assumes "y * x \<le> x * (x \<star> (1 \<squnion> y))"
    shows "(x \<squnion> y) \<star> z = x \<star> (y \<star> z)"
proof -
  have "(1 \<squnion> y) * x \<le> x * (x \<star> (1 \<squnion> y))"
    by (smt assms sup_assoc le_supI mult_left_one mult_left_sub_dist_sup_left mult_right_dist_sup mult_1_right while_left_unfold)
  hence 1: "(1 \<squnion> y) * (x \<star> 1) \<le> x \<star> (1 \<squnion> y)"
    by (metis mult_1_right while_simulate_right_plus_1)
  have "y * x * (x \<star> 1) \<le> x * (x \<star> ((1 \<squnion> y) * (x \<star> 1)))"
    by (smt assms le_iff_sup mult_assoc mult_right_dist_sup while_associative_1 while_increasing)
  also have "... \<le> x * (x \<star> (1 \<squnion> y))"
    using 1 mult_right_isotone while_mult_transitive by blast
  also have "... \<le> x * (x \<star> 1) * (y \<star> 1)"
    by (simp add: mult_right_isotone mult_assoc while_increasing while_one_increasing while_one_while while_right_isotone)
  finally have "y \<star> (x * (x \<star> 1)) \<le> x * (x \<star> 1) * (y \<star> 1) \<squnion> (y \<star> bot)"
    by (metis mult_assoc mult_1_right while_simulate_left_plus_1)
  hence "(y \<star> 1) * (y \<star> x) \<le> x * (x \<star> y \<star> 1) \<squnion> (y \<star> bot)"
    by (smt le_iff_sup mult_assoc mult_1_right order_refl order_trans while_absorb_2 while_left_dist_sup while_mult_star_exchange while_one_mult_below while_one_while while_plus_one)
  hence "(y \<star> 1) * ((y \<star> x) \<star> (y \<star> z)) \<le> x \<star> ((y \<star> 1) * (y \<star> z) \<squnion> (y \<star> bot) * ((y \<star> x) \<star> (y \<star> z)))"
    by (simp add: while_simulate_right_plus)
  also have "... \<le> x \<star> ((y \<star> z) \<squnion> (y \<star> bot))"
    by (metis sup_mono mult_left_zero order_refl while_absorb_2 while_one_mult_below while_right_isotone while_sub_associative)
  also have "... = x \<star> y \<star> z"
    using sup.absorb_iff1 while_right_isotone by auto
  finally show ?thesis
    by (smt sup_commute le_iff_sup mult_left_one mult_right_dist_sup while_plus_one while_sub_associative while_sumstar)
qed

lemma while_separate_5:
  "y * x \<le> x * (x \<star> (x \<squnion> y)) \<Longrightarrow> (x \<squnion> y) \<star> z = x \<star> (y \<star> z)"
  using order_lesseq_imp while_separate_4 while_sup_sub_sup_one_mult by blast

lemma while_separate_6:
  "y * x \<le> x * (x \<squnion> y) \<Longrightarrow> (x \<squnion> y) \<star> z = x \<star> (y \<star> z)"
  by (smt order_trans while_increasing while_mult_star_exchange while_separate_5)

text \<open>Theorem 11.4\<close>

lemma while_separate_1:
  "y * x \<le> x * y \<Longrightarrow> (x \<squnion> y) \<star> z = x \<star> (y \<star> z)"
  using mult_left_sub_dist_sup_right order_lesseq_imp while_separate_6 by blast

text \<open>Theorem 11.2\<close>

lemma while_separate_mult_1:
  "y * x \<le> x * y \<Longrightarrow> (x * y) \<star> z \<le> x \<star> (y \<star> z)"
  by (metis while_mult_sub_sup while_separate_1)

text \<open>Theorem 11.5\<close>

lemma separation:
  assumes "y * x \<le> x * (y \<star> 1)"
    shows "(x \<squnion> y) \<star> z = x \<star> (y \<star> z)"
proof -
  have "y \<star> x \<le> x * (y \<star> 1) \<squnion> (y \<star> bot)"
    by (metis assms mult_1_right while_simulate_left_plus_1)
  also have "... \<le> x * (x \<star> y \<star> 1) \<squnion> (y \<star> bot)"
    using sup_left_isotone while_increasing while_mult_star_exchange by force
  finally have "(y \<star> 1) * (y \<star> x) \<le> x * (x \<star> y \<star> 1) \<squnion> (y \<star> bot)"
    using order.trans while_one_mult_while_below by blast
  hence "(y \<star> 1) * ((y \<star> x) \<star> (y \<star> z)) \<le> x \<star> ((y \<star> 1) * (y \<star> z) \<squnion> (y \<star> bot) * ((y \<star> x) \<star> (y \<star> z)))"
    by (simp add: while_simulate_right_plus)
  also have "... \<le> x \<star> ((y \<star> z) \<squnion> (y \<star> bot))"
    by (metis sup_mono mult_left_zero order_refl while_absorb_2 while_one_mult_below while_right_isotone while_sub_associative)
  also have "... = x \<star> y \<star> z"
    using sup.absorb_iff1 while_right_isotone by auto
  finally show ?thesis
    by (smt sup_commute le_iff_sup mult_left_one mult_right_dist_sup while_plus_one while_sub_associative while_sumstar)
qed

text \<open>Theorem 11.5\<close>

lemma while_separate_left:
  "y * x \<le> x * (y \<star> 1) \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)"
  by (metis sup_commute separation while_sub_dist_3)

text \<open>Theorem 11.6\<close>

lemma while_simulate_4:
  "y * x \<le> x * (x \<star> (1 \<squnion> y)) \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)"
  by (metis sup_commute while_separate_4 while_sub_dist_3)

lemma while_simulate_5:
  "y * x \<le> x * (x \<star> (x \<squnion> y)) \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)"
  by (smt order_trans while_sup_sub_sup_one_mult while_simulate_4)

lemma while_simulate_6:
  "y * x \<le> x * (x \<squnion> y) \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)"
  by (smt order_trans while_increasing while_mult_star_exchange while_simulate_5)

text \<open>Theorem 11.3\<close>

lemma while_simulate_7:
  "y * x \<le> x * y \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)"
  using mult_left_sub_dist_sup_right order_lesseq_imp while_simulate_6 by blast

lemma while_while_mult_1:
  "x \<star> (1 \<star> y) = 1 \<star> (x \<star> y)"
  by (metis sup_commute mult_left_one mult_1_right order_refl while_separate_1)

text \<open>Theorem 9.15\<close>

lemma while_while_mult_2:
  "x \<star> (1 \<star> y) = (x \<star> 1) \<star> y"
  by (simp add: while_while_mult while_while_mult_1)

text \<open>Theorem 11.8\<close>

lemma while_import:
  assumes "p \<le> p * p \<and> p \<le> 1 \<and> p * x \<le> x * p"
    shows "p * (x \<star> y) = p * ((p * x) \<star> y)"
proof -
  have "p * (x \<star> y) \<le> (p * x) \<star> (p * y)"
    using assms test_preserves_equation while_simulate by auto
  also have "... \<le> (p * x) \<star> y"
    by (metis assms le_iff_sup mult_left_one mult_right_dist_sup while_right_isotone)
  finally have 2: "p * (x \<star> y) \<le> p * ((p * x) \<star> y)"
    by (smt assms sup_commute le_iff_sup mult_assoc mult_left_dist_sup mult_1_right)
  have "p * ((p * x) \<star> y) \<le> p * (x \<star> y)"
    by (metis assms mult_left_isotone mult_left_one mult_right_isotone while_left_isotone)
  thus ?thesis
    using 2 order.antisym by auto
qed

text \<open>Theorem 11.8\<close>

lemma while_preserve:
  assumes "p \<le> p * p"
      and "p \<le> 1"
      and "p * x \<le> x * p"
    shows "p * (x \<star> y) = p * (x \<star> (p * y))"
proof (rule order.antisym)
  show "p * (x \<star> y) \<le> p * (x \<star> (p * y))"
    by (metis assms order.antisym coreflexive_transitive mult_right_isotone mult_assoc while_simulate)
  show "p * (x \<star> (p * y)) \<le> p * (x \<star> y)"
    by (metis assms(2) mult_left_isotone mult_left_one mult_right_isotone while_right_isotone)
qed

lemma while_plus_below_while:
  "(x \<star> 1) * x \<le> x \<star> 1"
  by (simp add: while_mult_upper_bound while_one_increasing)

text \<open>Theorem 9.40\<close>

lemma while_01:
  "(w * (x \<star> 1)) \<star> (y * z) \<le> (x \<star> w) \<star> ((x \<star> y) * z)"
proof -
  have "(w * (x \<star> 1)) \<star> (y * z) = y * z \<squnion> w * (((x \<star> 1) * w) \<star> ((x \<star> 1) * y * z))"
    by (metis mult_assoc while_productstar)
  also have "... \<le> y * z \<squnion> w * ((x \<star> w) \<star> ((x \<star> y) * z))"
    by (metis sup_right_isotone mult_left_isotone mult_right_isotone while_isotone while_one_mult_below)
  also have "... \<le> (x \<star> y) * z \<squnion> (x \<star> w) * ((x \<star> w) \<star> ((x \<star> y) * z))"
    by (meson mult_left_isotone semiring.add_mono while_increasing)
  finally show ?thesis
    using while_left_unfold by auto
qed

text \<open>Theorem 9.37\<close>

lemma while_while_sub_associative:
  "x \<star> (y \<star> z) \<le> ((x \<star> y) \<star> z) \<squnion> (x \<star> z)"
proof -
  have 1: "x * (x \<star> 1) \<le> (x \<star> 1) * ((x \<star> y) \<star> 1)"
    by (metis le_supE while_back_loop_prefixpoint while_mult_increasing while_mult_transitive while_one_while)
  have "x \<star> (y \<star> z) \<le> x \<star> ((x \<star> 1) * (y \<star> z))"
    by (metis mult_left_isotone mult_left_one while_increasing while_right_isotone)
  also have "... \<le> (x \<star> 1) * ((x \<star> y) \<star> (y \<star> z)) \<squnion> (x \<star> bot)"
    using 1 while_simulate_left_plus_1 by auto
  also have "... \<le> (x \<star> 1) * ((x \<star> y) \<star> z) \<squnion> (x \<star> z)"
    by (simp add: le_supI1 sup_commute while_absorb_2 while_increasing while_right_isotone)
  also have "... = (x \<star> 1) * z \<squnion> (x \<star> 1) * (x \<star> y) * ((x \<star> y) \<star> z) \<squnion> (x \<star> z)"
    by (metis mult_assoc mult_left_dist_sup while_left_unfold)
  also have "... = (x \<star> y) * ((x \<star> y) \<star> z) \<squnion> (x \<star> z)"
    by (smt sup_assoc sup_commute le_iff_sup mult_left_one mult_right_dist_sup order_refl while_absorb_1 while_plus_one while_sub_associative)
  also have "... \<le> ((x \<star> y) \<star> z) \<squnion> (x \<star> z)"
    using sup_left_isotone while_left_plus_below by auto
  finally show ?thesis
    .
qed

lemma while_induct:
  "x * z \<le> z \<and> y \<le> z \<and> x \<star> 1 \<le> z \<Longrightarrow> x \<star> y \<le> z"
  by (metis le_supI1 sup_commute sup_bot_left le_iff_sup while_right_isotone while_simulate_absorb)

(*
lemma while_sumstar_4_below: "(x \<star> y) \<star> ((x \<star> 1) * z) \<le> x \<star> ((y * (x \<star> 1)) \<star> z)" oops
lemma while_sumstar_2: "(x \<squnion> y) \<star> z = x \<star> ((y * (x \<star> 1)) \<star> z)" oops
lemma while_sumstar_3: "(x \<squnion> y) \<star> z = ((x \<star> 1) * y) \<star> (x \<star> z)" oops
lemma while_decompose_6: "x \<star> ((y * (x \<star> 1)) \<star> z) = y \<star> ((x * (y \<star> 1)) \<star> z)" oops
lemma while_finite_associative: "x \<star> bot = bot \<Longrightarrow> (x \<star> y) * z = x \<star> (y * z)" oops
lemma atomicity_refinement: "s = s * q \<Longrightarrow> x = q * x \<Longrightarrow> q * b = bot \<Longrightarrow> r * b \<le> b * r \<Longrightarrow> r * l \<le> l * r \<Longrightarrow> x * l \<le> l * x \<Longrightarrow> b * l \<le> l * b \<Longrightarrow> q * l \<le> l * q \<Longrightarrow> r \<star> q \<le> q * (r \<star> 1) \<Longrightarrow> q \<le> 1 \<Longrightarrow> s * ((x \<squnion> b \<squnion> r \<squnion> l) \<star> (q * z)) \<le> s * ((x * (b \<star> q) \<squnion> r \<squnion> l) \<star> z)" oops

lemma while_separate_right_plus: "y * x \<le> x * (x \<star> (1 \<squnion> y)) \<squnion> 1 \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)" oops
lemma while_square_1: "x \<star> 1 = (x * x) \<star> (x \<squnion> 1)" oops
lemma while_absorb_below_one: "y * x \<le> x \<Longrightarrow> y \<star> x \<le> 1 \<star> x" oops
lemma "y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops
lemma "y * x \<le> (1 \<squnion> x) * (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops
*)

end

class bounded_binary_itering = bounded_idempotent_left_zero_semiring + binary_itering
begin

text \<open>Theorem 9\<close>

lemma while_right_top:
  "x \<star> top = top"
  by (metis sup_left_top while_left_unfold)

text \<open>Theorem 9\<close>

lemma while_left_top:
  "top * (x \<star> 1) = top"
  by (meson order.antisym le_supE top_greatest while_back_loop_prefixpoint)

end

class extended_binary_itering = binary_itering +
  assumes while_denest_0: "w * (x \<star> (y * z)) \<le> (w * (x \<star> y)) \<star> (w * (x \<star> y) * z)"
begin

text \<open>Theorem 10.2\<close>

lemma while_denest_1:
  "w * (x \<star> (y * z)) \<le> (w * (x \<star> y)) \<star> z"
  using while_denest_0 while_mult_increasing while_mult_transitive by blast

lemma while_mult_sub_while_while:
  "x \<star> (y * z) \<le> (x \<star> y) \<star> z"
  by (metis mult_left_one while_denest_1)

lemma while_zero_zero:
  "(x \<star> bot) \<star> bot = x \<star> bot"
  by (metis order.antisym mult_left_zero sup_bot_left while_left_unfold while_sub_associative while_mult_sub_while_while)

text \<open>Theorem 10.11\<close>

lemma while_mult_zero_zero:
  "(x * (y \<star> bot)) \<star> bot = x * (y \<star> bot)"
  apply (rule order.antisym)
  apply (metis sup_bot_left while_left_unfold mult_assoc le_supI1 mult_left_zero mult_right_isotone while_left_dist_sup while_sub_associative)
  by (metis mult_left_zero while_denest_1)

text \<open>Theorem 10.3\<close>

lemma while_denest_2:
  "w * ((x \<star> (y * w)) \<star> z) = w * (((x \<star> y) * w) \<star> z)"
  apply (rule order.antisym)
  apply (metis mult_assoc while_denest_0 while_simulate_right_plus_1 while_slide)
  by (simp add: mult_isotone while_left_isotone while_sub_associative)

text \<open>Theorem 10.12\<close>

lemma while_denest_3:
  "(x \<star> w) \<star> (x \<star> bot) = (x \<star> w) \<star> bot"
  by (metis while_absorb_2 while_right_isotone while_zero_zero bot_least)

text \<open>Theorem 10.15\<close>

lemma while_02:
  "x \<star> ((x \<star> w) \<star> ((x \<star> y) * z)) = (x \<star> w) \<star> ((x \<star> y) * z)"
proof -
  have "x * ((x \<star> w) \<star> ((x \<star> y) * z)) = x * (x \<star> y) * z \<squnion> x * (x \<star> w) * ((x \<star> w) \<star> ((x \<star> y) * z))"
    by (metis mult_assoc mult_left_dist_sup while_left_unfold)
  also have "... \<le> (x \<star> w) \<star> ((x \<star> y) * z)"
    by (metis sup_mono mult_right_sub_dist_sup_right while_left_unfold)
  finally have "x \<star> ((x \<star> w) \<star> ((x \<star> y) * z)) \<le> ((x \<star> w) \<star> ((x \<star> y) * z)) \<squnion> (x \<star> bot)"
    using while_simulate_absorb by auto
  also have "... = (x \<star> w) \<star> ((x \<star> y) * z)"
    by (metis sup_commute le_iff_sup order_trans while_mult_sub_while_while while_right_isotone bot_least)
  finally show ?thesis
    by (simp add: order.antisym while_increasing)
qed

lemma while_sumstar_3_below:
  "(x \<star> y) \<star> (x \<star> z) \<le> (x \<star> y) \<star> ((x \<star> 1) * z)"
proof -
  have "(x \<star> y) \<star> (x \<star> z) = (x \<star> z) \<squnion> ((x \<star> y) \<star> ((x \<star> y) * (x \<star> z)))"
    using while_right_unfold by blast
  also have "... \<le> (x \<star> z) \<squnion> ((x \<star> y) \<star> (x \<star> (y * (x \<star> z))))"
    by (meson sup_right_isotone while_right_isotone while_sub_associative)
  also have "... \<le> (x \<star> z) \<squnion> ((x \<star> y) \<star> (x \<star> ((x \<star> y) \<star> (x \<star> z))))"
    by (smt sup_right_isotone order_trans while_increasing while_mult_upper_bound while_one_increasing while_right_isotone)
  also have "... \<le> (x \<star> z) \<squnion> ((x \<star> y) \<star> (x \<star> ((x \<star> y) \<star> ((x \<star> 1) * z))))"
    by (metis sup_right_isotone mult_left_isotone mult_left_one order_trans while_increasing while_right_isotone while_sumstar while_transitive)
  also have "... = (x \<star> z) \<squnion> ((x \<star> y) \<star> ((x \<star> 1) * z))"
    by (simp add: while_transitive while_02)
  also have "... = (x \<star> y) \<star> ((x \<star> 1) * z)"
    by (smt sup_assoc mult_left_one mult_right_dist_sup while_02 while_left_dist_sup while_plus_one)
  finally show ?thesis
    .
qed

lemma while_sumstar_4_below:
  "(x \<star> y) \<star> ((x \<star> 1) * z) \<le> x \<star> ((y * (x \<star> 1)) \<star> z)"
proof -
  have "(x \<star> y) \<star> ((x \<star> 1) * z) = (x \<star> 1) * z \<squnion> (x \<star> y) * ((x \<star> y) \<star> ((x \<star> 1) * z))"
    using while_left_unfold by auto
  also have "... \<le> (x \<star> z) \<squnion> (x \<star> (y * ((x \<star> y) \<star> ((x \<star> 1) * z))))"
    by (meson sup_mono while_one_mult_below while_sub_associative)
  also have "... = (x \<star> z) \<squnion> (x \<star> (y * (((x \<star> 1) * y) \<star> ((x \<star> 1) * z))))"
    by (metis mult_left_one while_denest_2)
  also have "... = x \<star> ((y * (x \<star> 1)) \<star> z)"
    by (metis while_left_dist_sup while_productstar)
  finally show ?thesis
    .
qed

text \<open>Theorem 10.10\<close>

lemma while_sumstar_1:
  "(x \<squnion> y) \<star> z = (x \<star> y) \<star> ((x \<star> 1) * z)"
  by (smt order.eq_iff order_trans while_sup_1_below while_sumstar while_sumstar_3_below while_sumstar_4_below)

text \<open>Theorem 10.8\<close>

lemma while_sumstar_2:
  "(x \<squnion> y) \<star> z = x \<star> ((y * (x \<star> 1)) \<star> z)"
  using order.antisym while_sup_1_below while_sumstar_1 while_sumstar_4_below by auto

text \<open>Theorem 10.9\<close>

lemma while_sumstar_3:
  "(x \<squnion> y) \<star> z = ((x \<star> 1) * y) \<star> (x \<star> z)"
  using order.antisym while_sumstar while_sumstar_1_below while_sumstar_2_below while_sumstar_2 by force

text \<open>Theorem 10.6\<close>

lemma while_decompose_6:
  "x \<star> ((y * (x \<star> 1)) \<star> z) = y \<star> ((x * (y \<star> 1)) \<star> z)"
  by (metis sup_commute while_sumstar_2)

text \<open>Theorem 10.4\<close>

lemma while_denest_4:
  "(x \<star> w) \<star> (x \<star> (y * z)) = (x \<star> w) \<star> ((x \<star> y) * z)"
proof -
  have "(x \<star> w) \<star> (x \<star> (y * z)) = x \<star> ((w * (x \<star> 1)) \<star> (y * z))"
    using while_sumstar while_sumstar_2 by force
  also have "... \<le> (x \<star> w) \<star> ((x \<star> y) * z)"
    by (metis while_01 while_right_isotone while_02)
  finally show ?thesis
    using order.antisym while_right_isotone while_sub_associative by auto
qed

text \<open>Theorem 10.13\<close>

lemma while_denest_5:
  "w * ((x \<star> (y * w)) \<star> (x \<star> (y * z))) = w * (((x \<star> y) * w) \<star> ((x \<star> y) * z))"
  by (simp add: while_denest_2 while_denest_4)

text \<open>Theorem 10.5\<close>

lemma while_denest_6:
  "(w * (x \<star> y)) \<star> z = z \<squnion> w * ((x \<squnion> y * w) \<star> (y * z))"
  by (metis while_denest_5 while_productstar while_sumstar)

text \<open>Theorem 10.1\<close>

lemma while_sum_below_one:
  "y * ((x \<squnion> y) \<star> z) \<le> (y * (x \<star> 1)) \<star> z"
  by (simp add: while_denest_6)

text \<open>Theorem 10.14\<close>

lemma while_separate_unfold:
  "(y * (x \<star> 1)) \<star> z = (y \<star> z) \<squnion> (y \<star> (y * x * (x \<star> ((y * (x \<star> 1)) \<star> z))))"
proof -
  have "y \<star> (y * x * (x \<star> ((y * (x \<star> 1)) \<star> z))) \<le> y \<star> (y * ((x \<squnion> y) \<star> z))"
    using mult_right_isotone while_left_plus_below while_right_isotone mult_assoc while_sumstar_2 by auto
  also have "... \<le> (y * (x \<star> 1)) \<star> z"
    by (metis sup_commute sup_ge1 while_absorb_1 while_mult_star_exchange while_sum_below_one)
  finally have "(y \<star> z) \<squnion> (y \<star> (y * x * (x \<star> ((y * (x \<star> 1)) \<star> z)))) \<le> (y * (x \<star> 1)) \<star> z"
    using sup.bounded_iff while_back_loop_prefixpoint while_left_isotone by auto
  thus ?thesis
    by (simp add: order.antisym while_separate_unfold_below)
qed

text \<open>Theorem 10.7\<close>

lemma while_finite_associative:
  "x \<star> bot = bot \<Longrightarrow> (x \<star> y) * z = x \<star> (y * z)"
  by (metis while_denest_4 while_zero)

text \<open>Theorem 12\<close>

lemma atomicity_refinement:
  assumes "s = s * q"
      and "x = q * x"
      and "q * b = bot"
      and "r * b \<le> b * r"
      and "r * l \<le> l * r"
      and "x * l \<le> l * x"
      and "b * l \<le> l * b"
      and "q * l \<le> l * q"
      and "r \<star> q \<le> q * (r \<star> 1) \<and> q \<le> 1"
    shows "s * ((x \<squnion> b \<squnion> r \<squnion> l) \<star> (q * z)) \<le> s * ((x * (b \<star> q) \<squnion> r \<squnion> l) \<star> z)"
proof -
  have 1: "(x \<squnion> b \<squnion> r) * l \<le> l * (x \<squnion> b \<squnion> r)"
    by (smt assms(5-7) mult_left_dist_sup semiring.add_mono semiring.distrib_right)
  have "q * ((x * (b \<star> r \<star> 1) * q) \<star> z) \<le> (x * (b \<star> r \<star> 1) * q) \<star> z"
    using assms(9) order_lesseq_imp while_increasing while_mult_upper_bound by blast
  also have "... \<le> (x * (b \<star> ((r \<star> 1) * q))) \<star> z"
    by (simp add: mult_right_isotone while_left_isotone while_sub_associative mult_assoc)
  also have "... \<le> (x * (b \<star> r \<star> q)) \<star> z"
    by (simp add: mult_right_isotone while_left_isotone while_one_mult_below while_right_isotone)
  also have "... \<le> (x * (b \<star> (q * (r \<star> 1)))) \<star> z"
    by (simp add: assms(9) mult_right_isotone while_left_isotone while_right_isotone)
  finally have 2: "q * ((x * (b \<star> r \<star> 1) * q) \<star> z) \<le> (x * (b \<star> q) * (r \<star> 1)) \<star> z"
    using while_associative_while_1 mult_assoc by auto
  have "s * ((x \<squnion> b \<squnion> r \<squnion> l) \<star> (q * z)) = s * (l \<star> (x \<squnion> b \<squnion> r) \<star> (q * z))"
    using 1 sup_commute while_separate_1 by fastforce
  also have "... = s * q * (l \<star> b \<star> r \<star> (q * x * (b \<star> r \<star> 1)) \<star> (q * z))"
    by (smt assms(1,2,4) sup_assoc sup_commute while_sumstar_2 while_separate_1)
  also have "... = s * q * (l \<star> b \<star> r \<star> (q * ((x * (b \<star> r \<star> 1) * q) \<star> z)))"
    by (simp add: while_slide mult_assoc)
  also have "... \<le> s * q * (l \<star> b \<star> r \<star> (x * (b \<star> q) * (r \<star> 1)) \<star> z)"
    using 2 by (meson mult_right_isotone while_right_isotone)
  also have "... \<le> s * (l \<star> q * (b \<star> r \<star> (x * (b \<star> q) * (r \<star> 1)) \<star> z))"
    by (simp add: assms(8) mult_right_isotone while_simulate mult_assoc)
  also have "... = s * (l \<star> q * (r \<star> (x * (b \<star> q) * (r \<star> 1)) \<star> z))"
    using assms(3) while_elimination by auto
  also have "... \<le> s * (l \<star> r \<star> (x * (b \<star> q) * (r \<star> 1)) \<star> z)"
    by (meson assms(9) order.trans mult_right_isotone order.refl while_increasing while_mult_upper_bound while_right_isotone)
  also have "... = s * (l \<star> (r \<squnion> x * (b \<star> q)) \<star> z)"
    by (simp add: while_sumstar_2)
  also have "... \<le> s * ((x * (b \<star> q) \<squnion> r \<squnion> l) \<star> z)"
    using mult_right_isotone sup_commute while_sub_dist_3 by auto
  finally show ?thesis
    .
qed

end

class bounded_extended_binary_itering = bounded_binary_itering + extended_binary_itering

end

