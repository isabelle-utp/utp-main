(* Title:      N-Omega Binary Iterings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>N-Omega Binary Iterings\<close>

theory N_Omega_Binary_Iterings

imports N_Omega_Algebras Binary_Iterings_Strict

begin

sublocale extended_binary_itering < left_zero_conway_semiring where circ = "(\<lambda>x . x \<star> 1)"
  apply unfold_locales
  using while_left_unfold apply force
  apply (metis mult_1_right while_one_mult_below while_slide)
  by (simp add: while_one_while while_sumstar_2)

class binary_itering_apx = bounded_binary_itering + n_algebra_apx
begin

lemma C_while_import:
  "C (x \<star> z) = C (C x \<star> z)"
proof -
  have 1: "C x * (x \<star> z) \<le> C x \<star> (C x * z)"
    using C_mult_propagate while_simulate by force
  have "C (x \<star> z) = C z \<squnion> C x * (x \<star> z)"
    by (metis inf_sup_distrib1 n_L_T_meet_mult while_left_unfold)
  also have "... \<le> C x \<star> z"
    using 1 by (metis C_decreasing sup_mono while_right_unfold)
  finally have "C (x \<star> z) \<le> C (C x \<star> z)"
    by simp
  thus ?thesis
    by (metis order.antisym inf.boundedI inf.cobounded1 inf.coboundedI2 inf.sup_monoid.add_commute while_absorb_2 while_increasing)
qed

lemma C_while_preserve:
  "C (x \<star> z) = C (x \<star> C z)"
proof -
  have "C x * (x \<star> z) \<le> C x \<star> (C x * z)"
    using C_mult_propagate while_simulate by auto
  also have "... \<le> x \<star> (x * C z)"
    using C_decreasing n_L_T_meet_mult_propagate while_isotone by blast
  finally have 1: "C x * (x \<star> z) \<le> x \<star> (x * C z)"
    .
  have "C (x \<star> z) = C z \<squnion> C x * (x \<star> z)"
    by (metis inf_sup_distrib1 n_L_T_meet_mult while_left_unfold)
  also have "... \<le> x \<star> C z"
    using 1 by (meson order.trans le_supI while_increasing while_right_plus_below)
  finally have "C (x \<star> z) \<le> C (x \<star> C z)"
    by simp
  thus ?thesis
    by (meson order.antisym inf.boundedI inf.cobounded1 inf.coboundedI2 inf.eq_refl while_isotone)
qed

lemma C_while_import_preserve:
  "C (x \<star> z) = C (C x \<star> C z)"
  using C_while_import C_while_preserve by auto

lemma while_L_L:
  "L \<star> L = L"
  by (metis n_L_top_L while_mult_star_exchange while_right_top)

lemma while_L_below_sup:
  "L \<star> x \<le> x \<squnion> L"
  by (metis while_left_unfold sup_right_isotone n_L_below_L)

lemma while_L_split:
  "x \<star> L \<le> (x \<star> y) \<squnion> L"
proof -
  have "x \<star> L \<le> (x \<star> bot) \<squnion> L"
    by (metis sup_commute sup_bot_left mult_1_right n_L_split_L while_right_unfold while_simulate_left_plus while_zero)
  thus ?thesis
    by (metis sup_commute sup_right_isotone order_trans while_right_isotone bot_least)
qed

lemma while_n_while_top_split:
  "x \<star> (n(x \<star> y) * top) \<le> (x \<star> bot) \<squnion> n(x \<star> y) * top"
proof -
  have "x * n(x \<star> y) * top \<le> x * bot \<squnion> n(x * (x \<star> y)) * top"
    by (simp add: n_n_top_split_n_top)
  also have "... \<le> n(x \<star> y) * top \<squnion> x * bot"
    by (metis sup_commute sup_right_isotone mult_left_isotone n_isotone while_left_plus_below)
  finally have "x \<star> (n(x \<star> y) * top) \<le> n(x \<star> y) * top \<squnion> (x \<star> (x * bot))"
    by (metis mult_assoc mult_1_right while_simulate_left mult_left_zero while_left_top)
  also have "... \<le> (x \<star> bot) \<squnion> n(x \<star> y) * top"
    using sup_left_isotone while_right_plus_below by auto
  finally show ?thesis
    .
qed

lemma circ_apx_right_isotone:
  assumes "x \<sqsubseteq> y"
    shows "z \<star> x \<sqsubseteq> z \<star> y"
proof -
  have 1: "x \<le> y \<squnion> L \<and> C y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  hence "z \<star> x \<le> (z \<star> y) \<squnion> (z \<star> L)"
    by (metis while_left_dist_sup while_right_isotone)
  hence 2: "z \<star> x \<le> (z \<star> y) \<squnion> L"
    by (meson le_supI order_lesseq_imp sup.cobounded1 while_L_split)
  have "z \<star> (n(z \<star> x) * top) \<le> (z \<star> bot) \<squnion> n(z \<star> x) * top"
    by (simp add: while_n_while_top_split)
  also have "... \<le> (z \<star> x) \<squnion> n(z \<star> x) * top"
    using sup_left_isotone while_right_isotone by force
  finally have 3: "z \<star> (n(x) * top) \<le> (z \<star> x) \<squnion> n(z \<star> x) * top"
    by (metis mult_left_isotone n_isotone order_trans while_increasing while_right_isotone)
  have "C (z \<star> y) \<le> z \<star> C y"
    by (metis C_while_preserve inf.cobounded2)
  also have "... \<le> (z \<star> x) \<squnion> (z \<star> (n(x) * top))"
    using 1 by (metis while_left_dist_sup while_right_isotone)
  also have "... \<le> (z \<star> x) \<squnion> n(z \<star> x) * top"
    using 3 by simp
  finally show ?thesis
    using 2 apx_def by auto
qed

end

class extended_binary_itering_apx = binary_itering_apx + bounded_extended_binary_itering +
  assumes n_below_while_zero: "n(x) \<le> n(x \<star> bot)"
begin

lemma circ_apx_right_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x \<star> z \<sqsubseteq> y \<star> z"
proof -
  have 1: "x \<le> y \<squnion> L \<and> C y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  hence "x \<star> z \<le> ((y \<star> 1) * L) \<star> (y \<star> z)"
    by (metis while_left_isotone while_sumstar_3)
  also have "... \<le> (y \<star> z) \<squnion> (y \<star> 1) * L"
    by (metis while_productstar sup_right_isotone mult_right_isotone n_L_below_L while_slide)
  also have "... \<le> (y \<star> z) \<squnion> L"
    by (meson order.trans le_supI sup.cobounded1 while_L_split while_one_mult_below)
  finally have 2: "x \<star> z \<le> (y \<star> z) \<squnion> L"
    .
  have "C (y \<star> z) \<le> C y \<star> z"
    by (metis C_while_import inf.sup_right_divisibility)
  also have "... \<le> ((x \<star> 1) * n(x) * top) \<star> (x \<star> z)"
    using 1 by (metis while_left_isotone mult_assoc while_sumstar_3)
  also have "... \<le> (x \<star> z) \<squnion> (x \<star> 1) * n(x) * top"
    by (metis while_productstar sup_left_top sup_right_isotone mult_assoc mult_left_sub_dist_sup_right while_slide)
  also have "... \<le> (x \<star> z) \<squnion> (x \<star> (n(x) * top))"
    using sup_right_isotone while_one_mult_below mult_assoc by auto
  also have "... \<le> (x \<star> z) \<squnion> (x \<star> (n(x \<star> z) * top))"
    by (metis n_below_while_zero bot_least while_right_isotone n_isotone mult_left_isotone sup_right_isotone order_trans)
  also have "... \<le> (x \<star> z) \<squnion> n(x \<star> z) * top"
    by (metis sup_assoc sup_right_isotone while_n_while_top_split sup_bot_right while_left_dist_sup)
  finally show ?thesis
    using 2 apx_def by auto
qed

(*
lemma while_top: "top \<star> x = L \<squnion> top * x" oops
lemma while_one_top: "1 \<star> x = L \<squnion> x" oops
lemma while_unfold_below_1: "x = y * x \<Longrightarrow> x \<le> y \<star> 1" oops

lemma while_square_1: "x \<star> 1 = (x * x) \<star> (x \<squnion> 1)" oops
lemma while_absorb_below_one: "y * x \<le> x \<Longrightarrow> y \<star> x \<le> 1 \<star> x" oops
lemma while_mult_L: "(x * L) \<star> z = z \<squnion> x * L" oops
lemma tarski_top_omega_below_2: "x * L \<le> (x * L) \<star> bot" oops
lemma tarski_top_omega_2: "x * L = (x * L) \<star> bot" oops
lemma while_separate_right_plus: "y * x \<le> x * (x \<star> (1 \<squnion> y)) \<squnion> 1 \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)" oops
lemma "y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops
lemma "y * x \<le> (1 \<squnion> x) * (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops
*)

end

class n_omega_algebra_binary = n_omega_algebra + while +
  assumes while_def: "x \<star> y = n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * y"
begin

lemma while_omega_inf_L_star:
  "x \<star> y = (x\<^sup>\<omega> \<sqinter> L) \<squnion> x\<^sup>\<star> * y"
  by (metis loop_semantics_kappa_mu_nu loop_semantics_kappa_mu_nu_2 while_def)

lemma while_one_mult_while_below_1:
  "(y \<star> 1) * (y \<star> v) \<le> y \<star> v"
proof -
  have "(y \<star> 1) * (y \<star> v) \<le> y \<star> (y \<star> v)"
    by (smt sup_left_isotone mult_assoc mult_right_dist_sup mult_right_isotone n_L_below_L while_def mult_left_one)
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * y\<^sup>\<star> * v"
    by (simp add: mult_left_dist_sup sup_assoc while_def mult_assoc)
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> (y\<^sup>\<star> * y\<^sup>\<star> * bot \<squnion> y\<^sup>\<star> * n(y\<^sup>\<omega>) * L) \<squnion> y\<^sup>\<star> * y\<^sup>\<star> * v"
    by (metis mult_left_dist_sup star.circ_transitive_equal sup_bot_left mult_assoc)
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> (y\<^sup>\<star> * y\<^sup>\<star> * bot \<squnion> n(y\<^sup>\<star> * y\<^sup>\<omega>) * L) \<squnion> y\<^sup>\<star> * y\<^sup>\<star> * v"
    by (simp add: n_mult_omega_L_star_zero)
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> n(y\<^sup>\<star> * y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * y\<^sup>\<star> * v"
    by (smt (z3) mult_left_dist_sup sup.left_commute sup_bot_left sup_commute)
  finally show ?thesis
    by (simp add: star.circ_transitive_equal star_mult_omega while_def)
qed

lemma star_below_while:
  "x\<^sup>\<star> * y \<le> x \<star> y"
  by (simp add: while_def)

subclass bounded_binary_itering
proof unfold_locales
  fix x y z
  have "z \<squnion> x * ((y * x) \<star> (y * z)) = x * (y * x)\<^sup>\<star> * y * z \<squnion> x * n((y * x)\<^sup>\<omega>) * L \<squnion> z"
    using mult_left_dist_sup sup_commute while_def mult_assoc by auto
  also have "... = x * (y * x)\<^sup>\<star> * y * z \<squnion> n(x * (y * x)\<^sup>\<omega>) * L \<squnion> z"
    by (metis mult_assoc mult_right_isotone bot_least n_mult_omega_L_star_zero sup_relative_same_increasing)
  also have "... = (x * y)\<^sup>\<star> * z \<squnion> n(x * (y * x)\<^sup>\<omega>) * L"
    by (smt sup_assoc sup_commute mult_assoc star.circ_loop_fixpoint star_slide)
  also have "... = (x * y) \<star> z"
    by (simp add: omega_slide sup_monoid.add_commute while_def)
  finally show "(x * y) \<star> z = z \<squnion> x * ((y * x) \<star> (y * z))"
    by simp
next
  fix x y z
  have "(x \<star> y) \<star> (x \<star> z) = n((n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> (n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x \<star> z)"
    by (simp add: while_def)
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L) * (x \<star> z)"
    using mult_L_sup_omega mult_L_sup_star by force
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * (x \<star> z) \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L * (x \<star> z)"
    by (simp add: mult_right_dist_sup n_dist_omega_star sup_assoc mult_assoc)
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * bot \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * (x \<star> z) \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L * (x \<star> z)"
    by (smt sup_assoc sup_bot_left mult_left_dist_sup)
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L * (x \<star> z) \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * (x \<star> z))"
    by (smt n_n_L_split_n_n_L_L sup_commute sup_assoc)
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * (x \<star> z))"
    by (smt mult_L_omega omega_sub_vector le_iff_sup)
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * (x \<star> z)"
    using mult_left_sub_dist_sup_left sup_absorb2 while_def mult_assoc by auto
  also have "... = (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> * z \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L"
    by (simp add: mult_left_dist_sup sup_commute while_def mult_assoc)
  also have "... = (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> * z \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L"
    by (metis sup_bot_right mult_left_dist_sup sup_assoc n_mult_omega_L_star_zero)
  also have "... = (x \<squnion> y) \<star> z"
    using n_dist_omega_star omega_decompose semiring.combine_common_factor star.circ_sup_9 sup_commute while_def by force
  finally show "(x \<squnion> y) \<star> z = (x \<star> y) \<star> (x \<star> z)"
    by simp
next
  fix x y z
  show "x \<star> (y \<squnion> z) = (x \<star> y) \<squnion> (x \<star> z)"
    using semiring.distrib_left sup_assoc sup_commute while_def by force
next
  fix x y z
  show "(x \<star> y) * z \<le> x \<star> (y * z)"
    by (smt sup_left_isotone mult_assoc mult_right_dist_sup mult_right_isotone n_L_below_L while_def)
next
  fix v w x y z
  show "x * z \<le> z * (y \<star> 1) \<squnion> w \<longrightarrow> x \<star> (z * v) \<le> z * (y \<star> v) \<squnion> (x \<star> (w * (y \<star> v)))"
  proof
    assume 1: "x * z \<le> z * (y \<star> 1) \<squnion> w"
    have "z * v \<squnion> x * (z * (y \<star> v) \<squnion> x\<^sup>\<star> * (w * (y \<star> v))) \<le> z * v \<squnion> x * z * (y \<star> v) \<squnion> x\<^sup>\<star> * (w * (y \<star> v))"
      by (metis sup_assoc sup_right_isotone mult_assoc mult_left_dist_sup mult_left_isotone star.left_plus_below_circ)
    also have "... \<le> z * v \<squnion> z * (y \<star> 1) * (y \<star> v) \<squnion> w * (y \<star> v) \<squnion> x\<^sup>\<star> * (w * (y \<star> v))"
      using 1 by (metis sup_assoc sup_left_isotone sup_right_isotone mult_left_isotone mult_right_dist_sup)
    also have "... \<le> z * v \<squnion> z * (y \<star> v) \<squnion> x\<^sup>\<star> * (w * (y \<star> v))"
      by (smt (verit, ccfv_threshold) sup_ge2 le_iff_sup mult_assoc mult_left_dist_sup star.circ_loop_fixpoint while_one_mult_while_below_1 le_supE le_supI)
    also have "... = z * (y \<star> v) \<squnion> x\<^sup>\<star> * (w * (y \<star> v))"
      by (metis le_iff_sup le_supE mult_right_isotone star.circ_loop_fixpoint star_below_while)
    finally have "x\<^sup>\<star> * z * v \<le> z * (y \<star> v) \<squnion> x\<^sup>\<star> * (w * (y \<star> v))"
      using star_left_induct mult_assoc by auto
    thus "x \<star> (z * v) \<le> z * (y \<star> v) \<squnion> (x \<star> (w * (y \<star> v)))"
      by (smt sup_assoc sup_commute sup_right_isotone mult_assoc while_def)
  qed
next
  fix v w x y z
  show "z * x \<le> y * (y \<star> z) \<squnion> w \<longrightarrow> z * (x \<star> v) \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
  proof
    assume "z * x \<le> y * (y \<star> z) \<squnion> w"
    hence 1: "z * x \<le> y * y\<^sup>\<star> * z \<squnion> (y * n(y\<^sup>\<omega>) * L \<squnion> w)"
      by (simp add: mult_left_dist_sup sup.left_commute sup_commute while_def mult_assoc)
    hence "z * x\<^sup>\<star> \<le> y\<^sup>\<star> * (z \<squnion> (y * n(y\<^sup>\<omega>) * L \<squnion> w) * x\<^sup>\<star>)"
      by (simp add: star_circ_simulate_right_plus)
    also have "... = y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * y * n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
      by (simp add: L_mult_star semiring.distrib_left semiring.distrib_right sup_left_commute sup_monoid.add_commute mult_assoc)
    also have "... = y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<star> * y * y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
      by (metis sup_relative_same_increasing mult_isotone n_mult_omega_L_star_zero star.left_plus_below_circ star.right_plus_circ bot_least)
    also have "... = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
      using omega_unfold star_mult_omega sup_commute mult_assoc by force
    finally have "z * x\<^sup>\<star> * v \<le> n(y\<^sup>\<omega>) * L * v \<squnion> y\<^sup>\<star> * z * v \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star> * v"
      by (smt le_iff_sup mult_right_dist_sup)
    also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * (z * v \<squnion> w * x\<^sup>\<star> * v)"
      by (metis n_L_below_L mult_assoc mult_right_isotone sup_left_isotone mult_left_dist_sup sup_assoc)
    also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * (z * v \<squnion> w * (x \<star> v))"
      using mult_right_isotone semiring.add_left_mono mult_assoc star_below_while by auto
    finally have 2: "z * x\<^sup>\<star> * v \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
      by (simp add: while_def)
    have 3: "y\<^sup>\<star> * y * y\<^sup>\<star> * bot \<le> y\<^sup>\<star> * w * x\<^sup>\<omega>"
      by (metis sup_commute sup_bot_left mult_assoc mult_left_sub_dist_sup_left star.circ_loop_fixpoint star.circ_transitive_equal)
    have "z * x\<^sup>\<omega> \<le> y * y\<^sup>\<star> * z * x\<^sup>\<omega> \<squnion> (y * n(y\<^sup>\<omega>) * L \<squnion> w) * x\<^sup>\<omega>"
      using 1 by (metis mult_assoc mult_left_isotone mult_right_dist_sup omega_unfold)
    hence "z * x\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * y * n(y\<^sup>\<omega>) * L * x\<^sup>\<omega> \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>"
      by (smt sup_assoc sup_commute left_plus_omega mult_assoc mult_left_dist_sup mult_right_dist_sup omega_induct star.left_plus_circ)
    also have "... \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * y * n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>"
      by (metis sup_left_isotone sup_right_isotone mult_assoc mult_right_isotone n_L_below_L)
    also have "... = y\<^sup>\<omega> \<squnion> n(y\<^sup>\<star> * y * y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>"
      using 3 by (smt sup_assoc sup_commute sup_relative_same_increasing n_mult_omega_L_star_zero)
    also have "... = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>"
      by (metis mult_assoc omega_unfold star_mult_omega sup_commute le_iff_sup n_L_decreasing)
    finally have "n(z * x\<^sup>\<omega>) * L \<le> n(y\<^sup>\<omega>) * L \<squnion> n(y\<^sup>\<star> * w * x\<^sup>\<omega>) * L"
      by (metis mult_assoc mult_left_isotone mult_right_dist_sup n_dist_omega_star n_isotone)
    also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * (w * (n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * bot))"
      by (smt sup_commute sup_right_isotone mult_assoc mult_left_dist_sup n_mult_omega_L_below_zero)
    also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * (w * (n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * v))"
      by (metis sup_right_isotone mult_right_isotone bot_least)
    also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * (z * v \<squnion> w * (n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * v))"
      using mult_left_sub_dist_sup_right sup_right_isotone by auto
    finally have 4: "n(z * x\<^sup>\<omega>) * L \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
      using while_def by auto
    have "z * (x \<star> v) = z * n(x\<^sup>\<omega>) * L \<squnion> z * x\<^sup>\<star> * v"
      by (simp add: mult_left_dist_sup while_def mult_assoc)
    also have "... = n(z * x\<^sup>\<omega>) * L \<squnion> z * x\<^sup>\<star> * v"
      by (metis sup_commute sup_relative_same_increasing mult_right_isotone n_mult_omega_L_star_zero bot_least)
    finally show "z * (x \<star> v) \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
      using 2 4 by simp
  qed
qed

lemma while_top:
  "top \<star> x = L \<squnion> top * x"
  by (metis n_top_L star.circ_top star_omega_top while_def)

lemma while_one_top:
  "1 \<star> x = L \<squnion> x"
  by (smt mult_left_one n_top_L omega_one star_one while_def)

lemma while_finite_associative:
  "x\<^sup>\<omega> = bot \<Longrightarrow> (x \<star> y) * z = x \<star> (y * z)"
  by (metis sup_bot_left mult_assoc n_zero_L_zero while_def)

lemma while_while_one:
  "y \<star> (x \<star> 1) = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * x\<^sup>\<star>"
  by (simp add: mult_left_dist_sup sup_assoc while_def mult_assoc)

text \<open>AACP Theorem 8.17\<close>

subclass bounded_extended_binary_itering
proof unfold_locales
  fix w x y z
  have "w * (x \<star> y * z) = n(w * n(x\<^sup>\<omega>) * L) * L \<squnion> w * x\<^sup>\<star> * y * z"
    by (smt sup_assoc sup_commute sup_bot_left mult_assoc mult_left_dist_sup n_n_L_split_n_n_L_L while_def)
  also have "... \<le> n((w * n(x\<^sup>\<omega>) * L)\<^sup>\<omega>) * L \<squnion> w * x\<^sup>\<star> * y * z"
    by (simp add: mult_L_omega)
  also have "... \<le> n((w * (x \<star> y))\<^sup>\<omega>) * L \<squnion> w * x\<^sup>\<star> * y * z"
    by (smt sup_left_isotone sup_ge1 mult_assoc mult_left_isotone mult_right_isotone n_isotone omega_isotone while_def)
  also have "... \<le> n((w * (x \<star> y))\<^sup>\<omega>) * L \<squnion> w * (x \<star> y) * z"
    by (metis star_below_while mult_assoc mult_left_isotone mult_right_isotone sup_right_isotone)
  also have "... \<le> n((w * (x \<star> y))\<^sup>\<omega>) * L \<squnion> (w * (x \<star> y))\<^sup>\<star> * (w * (x \<star> y) * z)"
    using sup.boundedI sup.cobounded1 while_def while_increasing by auto
  finally show "w * (x \<star> y * z) \<le> (w * (x \<star> y)) \<star> (w * (x \<star> y) * z)"
    using while_def by auto
qed

subclass extended_binary_itering_apx
  apply unfold_locales
  by (metis n_below_n_omega n_left_upper_bound n_n_L order_trans while_def)

lemma while_simulate_4_plus:
  assumes "y * x \<le> x * (x \<star> (1 \<squnion> y))"
    shows "y * x * x\<^sup>\<star> \<le> x * (x \<star> (1 \<squnion> y))"
proof -
  have "x * (x \<star> (1 \<squnion> y)) = x * n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * (1 \<squnion> y)"
    by (simp add: mult_left_dist_sup while_def mult_assoc)
  also have "... = n(x * x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * (1 \<squnion> y)"
    by (smt n_mult_omega_L_star_zero sup_relative_same_increasing sup_commute sup_bot_right mult_left_sub_dist_sup_right)
  finally have 1: "x * (x \<star> (1 \<squnion> y)) = n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    using mult_left_dist_sup omega_unfold sup_assoc by force
  hence "x * x\<^sup>\<star> * y * x \<le> x * x\<^sup>\<star> * n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * x\<^sup>\<star> * x \<squnion> x * x\<^sup>\<star> * x * x\<^sup>\<star> * y"
    by (metis assms mult_assoc mult_right_isotone mult_left_dist_sup star_plus)
  also have "... = n(x * x\<^sup>\<star> * x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * x\<^sup>\<star> * x \<squnion> x * x\<^sup>\<star> * x * x\<^sup>\<star> * y"
    by (smt (z3) sup_commute n_mult_omega_L_star omega_unfold semiring.distrib_left star_plus mult_assoc)
  also have "... = n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * x \<squnion> x * x * x\<^sup>\<star> * y"
    using omega_unfold star.circ_plus_same star.circ_transitive_equal star_mult_omega mult_assoc by auto
  also have "... \<le> n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    by (smt sup_assoc sup_ge2 le_iff_sup mult_assoc mult_right_dist_sup star.circ_increasing star.circ_plus_same star.circ_transitive_equal)
  finally have 2: "x * x\<^sup>\<star> * y * x \<le> n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    .
  have "(n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y) * x \<le> n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * x \<squnion> x * x\<^sup>\<star> * y * x"
    by (metis mult_right_dist_sup n_L_below_L mult_assoc mult_right_isotone sup_left_isotone)
  also have "... \<le> n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y * x"
    by (smt sup_commute sup_left_isotone mult_assoc mult_right_isotone star.left_plus_below_circ star_plus)
  also have "... \<le> n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    using 2 by simp
  finally show ?thesis
    using 1 assms star_right_induct by force
qed

lemma while_simulate_4_omega:
  assumes "y * x \<le> x * (x \<star> (1 \<squnion> y))"
    shows "y * x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
proof -
  have "x * (x \<star> (1 \<squnion> y)) = x * n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * (1 \<squnion> y)"
    using mult_left_dist_sup while_def mult_assoc by auto
  also have "... = n(x * x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * (1 \<squnion> y)"
    by (smt (z3) mult_1_right mult_left_sub_dist_sup_left n_mult_omega_L_star sup_commute sup_relative_same_increasing)
  finally have "x * (x \<star> (1 \<squnion> y)) = n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    using mult_left_dist_sup omega_unfold sup_assoc by force
  hence "y * x\<^sup>\<omega> \<le> n(x\<^sup>\<omega>) * L * x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> * x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> * y * x\<^sup>\<omega>"
    by (smt assms le_iff_sup mult_assoc mult_right_dist_sup omega_unfold)
  also have "... \<le> x * x\<^sup>\<star> * (y * x\<^sup>\<omega>) \<squnion> x\<^sup>\<omega>"
    by (metis sup_left_isotone mult_L_omega omega_sub_vector mult_assoc omega_unfold star_mult_omega n_L_decreasing le_iff_sup sup_commute)
  finally have "y * x\<^sup>\<omega> \<le> (x * x\<^sup>\<star>)\<^sup>\<omega> \<squnion> (x * x\<^sup>\<star>)\<^sup>\<star> * x\<^sup>\<omega>"
    by (simp add: omega_induct sup_monoid.add_commute)
  thus ?thesis
    by (metis sup_idem left_plus_omega star_mult_omega)
qed

lemma while_square_1:
  "x \<star> 1 = (x * x) \<star> (x \<squnion> 1)"
  by (metis mult_1_right omega_square star_square_2 while_def)

lemma while_absorb_below_one:
  "y * x \<le> x \<Longrightarrow> y \<star> x \<le> 1 \<star> x"
  by (metis star_left_induct_mult sup_mono n_galois n_sub_nL while_def while_one_top)

lemma while_mult_L:
  "(x * L) \<star> z = z \<squnion> x * L"
  by (metis sup_bot_right mult_left_zero while_denest_5 while_one_top while_productstar while_sumstar)

lemma tarski_top_omega_below_2:
  "x * L \<le> (x * L) \<star> bot"
  by (simp add: while_mult_L)

lemma tarski_top_omega_2:
  "x * L = (x * L) \<star> bot"
  by (simp add: while_mult_L)

(*
lemma while_sub_mult_one: "x * (1 \<star> y) \<le> 1 \<star> x" nitpick [expect=genuine,card=3] oops
lemma while_unfold_below: "x = z \<squnion> y * x \<longrightarrow> x \<le> y \<star> z" nitpick [expect=genuine,card=2] oops
lemma while_loop_is_greatest_postfixpoint: "is_greatest_postfixpoint (\<lambda>x . y * x \<squnion> z) (y \<star> z)" nitpick [expect=genuine,card=2] oops
lemma while_loop_is_greatest_fixpoint: "is_greatest_fixpoint (\<lambda>x . y * x \<squnion> z) (y \<star> z)" nitpick [expect=genuine,card=2] oops
lemma while_denest_3: "(x \<star> w) \<star> x\<^sup>\<omega> = (x \<star> w)\<^sup>\<omega>" nitpick [expect=genuine,card=2] oops
lemma while_mult_top: "(x * top) \<star> z = z \<squnion> x * top" nitpick [expect=genuine,card=2] oops
lemma tarski_below_top_omega: "x \<le> (x * L)\<^sup>\<omega>" nitpick [expect=genuine,card=2] oops
lemma tarski_mult_omega_omega: "(x * y\<^sup>\<omega>)\<^sup>\<omega> = x * y\<^sup>\<omega>" nitpick [expect=genuine,card=3] oops
lemma tarski_below_top_omega_2: "x \<le> (x * L) \<star> bot" nitpick [expect=genuine,card=2] oops
lemma "1 = (x * bot) \<star> 1" nitpick [expect=genuine,card=3] oops
lemma tarski: "x = bot \<or> top * x * top = top" nitpick [expect=genuine,card=3] oops
lemma "(x \<squnion> y) \<star> z = ((x \<star> 1) * y) \<star> ((x \<star> 1) * z)" nitpick [expect=genuine,card=2] oops
lemma while_top_2: "top \<star> z = top * z" nitpick [expect=genuine,card=2] oops
lemma while_mult_top_2: "(x * top) \<star> z = z \<squnion> x * top * z" nitpick [expect=genuine,card=2] oops
lemma while_one_mult: "(x \<star> 1) * x = x \<star> x" nitpick [expect=genuine,card=4] oops
lemma "(x \<star> 1) * y = x \<star> y" nitpick [expect=genuine,card=2] oops
lemma while_associative: "(x \<star> y) * z = x \<star> (y * z)" nitpick [expect=genuine,card=2] oops
lemma while_back_loop_is_fixpoint: "is_fixpoint (\<lambda>x . x * y \<squnion> z) (z * (y \<star> 1))" nitpick [expect=genuine,card=4] oops
lemma "1 \<squnion> x * bot = x \<star> 1" nitpick [expect=genuine,card=3] oops
lemma "x = x * (x \<star> 1)" nitpick [expect=genuine,card=3] oops
lemma "x * (x \<star> 1) = x \<star> 1" nitpick [expect=genuine,card=2] oops
lemma "x \<star> 1 = x \<star> (1 \<star> 1)" nitpick [expect=genuine,card=3] oops
lemma "(x \<squnion> y) \<star> 1 = (x \<star> (y \<star> 1)) \<star> 1" nitpick [expect=genuine,card=3] oops
lemma "z \<squnion> y * x = x \<Longrightarrow> y \<star> z \<le> x" nitpick [expect=genuine,card=2] oops
lemma "y * x = x \<Longrightarrow> y \<star> x \<le> x" nitpick [expect=genuine,card=2] oops
lemma "z \<squnion> x * y = x \<Longrightarrow> z * (y \<star> 1) \<le> x" nitpick [expect=genuine,card=3] oops
lemma "x * y = x \<Longrightarrow> x * (y \<star> 1) \<le> x" nitpick [expect=genuine,card=3] oops
lemma "x * z = z * y \<Longrightarrow> x \<star> z \<le> z * (y \<star> 1)" nitpick [expect=genuine,card=2] oops

lemma while_unfold_below_1: "x = y * x \<Longrightarrow> x \<le> y \<star> 1" nitpick [expect=genuine,card=3] oops
lemma "x\<^sup>\<omega> \<le> x\<^sup>\<omega> * x\<^sup>\<omega>" oops
lemma tarski_omega_idempotent: "x\<^sup>\<omega>\<^sup>\<omega> = x\<^sup>\<omega>" oops
*)

end

class n_omega_algebra_binary_strict = n_omega_algebra_binary + circ +
  assumes L_left_zero: "L * x = L"
  assumes circ_def: "x\<^sup>\<circ> = n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star>"
begin

subclass strict_binary_itering
  apply unfold_locales
  apply (metis while_def mult_assoc L_left_zero mult_right_dist_sup)
  by (metis circ_def while_def mult_1_right)

end

end

