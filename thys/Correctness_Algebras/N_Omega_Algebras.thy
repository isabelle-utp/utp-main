(* Title:      N-Omega-Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>N-Omega-Algebras\<close>

theory N_Omega_Algebras

imports Omega_Algebras Recursion

begin

class itering_apx = bounded_itering + n_algebra_apx
begin

lemma circ_L:
  "L\<^sup>\<circ> = L \<squnion> 1"
  by (metis sup_commute mult_top_circ n_L_top_L)

lemma C_circ_import:
  "C (x\<^sup>\<circ>) \<le> (C x)\<^sup>\<circ>"
proof -
  have 1: "C x * x\<^sup>\<circ> \<le> (C x)\<^sup>\<circ> * C x"
    using C_mult_propagate circ_simulate order.eq_iff by blast
  have "C (x\<^sup>\<circ>) = C (1 \<squnion> x * x\<^sup>\<circ>)"
    by (simp add: circ_left_unfold)
  also have "... = C 1 \<squnion> C (x * x\<^sup>\<circ>)"
    by (simp add: inf_sup_distrib1)
  also have "... \<le> 1 \<squnion> C (x * x\<^sup>\<circ>)"
    using sup_left_isotone by auto
  also have "... = 1 \<squnion> C x * x\<^sup>\<circ>"
    by (simp add: n_L_T_meet_mult)
  also have "... \<le> (C x)\<^sup>\<circ>"
    using 1 by (meson circ_reflexive order.trans le_supI right_plus_below_circ)
  finally show ?thesis
    .
qed

text \<open>AACP Theorem 4.3 and Theorem 4.4\<close>

lemma circ_apx_isotone:
  assumes "x \<sqsubseteq> y"
  shows "x\<^sup>\<circ> \<sqsubseteq> y\<^sup>\<circ>"
proof -
  have 1: "x \<le> y \<squnion> L \<and> C y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  have "C (y\<^sup>\<circ>) \<le> (C y)\<^sup>\<circ>"
    by (simp add: C_circ_import)
  also have "... \<le> x\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * n(x) * top"
    using 1 by (metis circ_isotone circ_left_top circ_unfold_sum mult_assoc)
  also have "... \<le> x\<^sup>\<circ> \<squnion> (x\<^sup>\<circ> * bot \<squnion> n(x\<^sup>\<circ> * x) * top)"
    using n_n_top_split_n_top sup_right_isotone by blast
  also have "... \<le> x\<^sup>\<circ> \<squnion> (x\<^sup>\<circ> * bot \<squnion> n(x\<^sup>\<circ>) * top)"
    using circ_plus_same left_plus_below_circ mult_left_isotone n_isotone sup_right_isotone by auto
  also have "... = x\<^sup>\<circ> \<squnion> n(x\<^sup>\<circ>) * top"
    by (meson sup.left_idem sup_relative_same_increasing zero_right_mult_decreasing)
  finally have 2: "C (y\<^sup>\<circ>) \<le> x\<^sup>\<circ> \<squnion> n(x\<^sup>\<circ>) * top"
    .
  have "x\<^sup>\<circ> \<le> y\<^sup>\<circ> * L\<^sup>\<circ>"
    using 1 by (metis circ_sup_1 circ_back_loop_fixpoint circ_isotone n_L_below_L le_iff_sup mult_assoc)
  also have "... = y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * L"
    using circ_L mult_left_dist_sup sup_commute by auto
  also have "... \<le> y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot \<squnion> L"
    using n_L_split_L semiring.add_left_mono sup_assoc by auto
  finally have "x\<^sup>\<circ> \<le> y\<^sup>\<circ> \<squnion> L"
    using sup.absorb1 zero_right_mult_decreasing by force
  thus "x\<^sup>\<circ> \<sqsubseteq> y\<^sup>\<circ>"
    using 2 by (simp add: apx_def)
qed

end

class n_omega_algebra_1 = bounded_left_zero_omega_algebra + n_algebra_apx + Omega +
  assumes Omega_def: "x\<^sup>\<Omega> = n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star>"
begin

text \<open>AACP Theorem 8.13\<close>

lemma C_omega_export:
  "C (x\<^sup>\<omega>) = (C x)\<^sup>\<omega>"
proof -
  have "C (x\<^sup>\<omega>) = C x * C (x\<^sup>\<omega>)"
    by (metis C_mult_propagate n_L_T_meet_mult omega_unfold)
  hence 1: "C (x\<^sup>\<omega>) \<le> (C x)\<^sup>\<omega>"
    using eq_refl omega_induct_mult by auto
  have "(C x)\<^sup>\<omega> = C (x * (C x)\<^sup>\<omega>)"
    using n_L_T_meet_mult omega_unfold by auto
  also have "... \<le> C (x\<^sup>\<omega>)"
    by (metis calculation C_decreasing inf_le1 le_infI omega_induct_mult)
  finally show ?thesis
    using 1 order.antisym by blast
qed  

text \<open>AACP Theorem 8.2\<close>

lemma L_mult_star:
  "L * x\<^sup>\<star> = L"
  by (metis n_L_top_L star.circ_left_top mult_assoc)

text \<open>AACP Theorem 8.3\<close>

lemma mult_L_star:
  "(x * L)\<^sup>\<star> = 1 \<squnion> x * L"
  by (metis L_mult_star star.circ_mult_1 mult_assoc)

lemma mult_L_omega_below:
  "(x * L)\<^sup>\<omega> \<le> x * L"
  by (metis mult_right_isotone n_L_below_L omega_slide)

text \<open>AACP Theorem 8.5\<close>

lemma mult_L_sup_star:
  "(x * L \<squnion> y)\<^sup>\<star> = y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
  using L_mult_star mult_1_right mult_left_dist_sup star_sup_1 sup_commute mult_L_star mult_assoc by auto

lemma mult_L_sup_omega_below:
  "(x * L \<squnion> y)\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
proof -
  have "(x * L \<squnion> y)\<^sup>\<omega> \<le> y\<^sup>\<star> * x * L \<squnion> (y\<^sup>\<star> * x * L)\<^sup>\<star> * y\<^sup>\<omega>"
    by (metis sup_commute mult_assoc omega_decompose sup_left_isotone mult_L_omega_below)
  also have "... \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
    by (smt (z3) le_iff_sup le_supI mult_left_dist_sup n_L_below_L star_left_induct sup.cobounded2 sup.left_idem sup.orderE sup_assoc sup_commute mult_assoc)
  finally show ?thesis
    .
qed

lemma n_Omega_isotone:
  "x \<le> y \<Longrightarrow> x\<^sup>\<Omega> \<le> y\<^sup>\<Omega>"
  by (metis Omega_def sup_mono mult_left_isotone n_isotone omega_isotone star_isotone)

lemma n_star_below_Omega:
  "x\<^sup>\<star> \<le> x\<^sup>\<Omega>"
  by (simp add: Omega_def)

lemma mult_L_star_mult_below:
  "(x * L)\<^sup>\<star> * y \<le> y \<squnion> x * L"
  by (metis sup_right_isotone mult_assoc mult_right_isotone n_L_below_L star_left_induct)

end

sublocale n_omega_algebra_1 < star: itering_apx where circ = star ..

class n_omega_algebra = n_omega_algebra_1 + n_algebra_apx +
  assumes n_split_omega_mult: "C (x\<^sup>\<omega>) \<le> x\<^sup>\<star> * n(x\<^sup>\<omega>) * top"
  assumes tarski: "x * L \<le> x * L * x * L"
begin

text \<open>AACP Theorem 8.4\<close>

lemma mult_L_omega:
  "(x * L)\<^sup>\<omega> = x * L"
  apply (rule order.antisym)
  apply (rule mult_L_omega_below)
  using omega_induct_mult tarski mult_assoc by auto

text \<open>AACP Theorem 8.6\<close>

lemma mult_L_sup_omega:
  "(x * L \<squnion> y)\<^sup>\<omega> = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
  apply (rule order.antisym)
  apply (rule mult_L_sup_omega_below)
  by (metis le_supI omega_isotone omega_sub_dist_2 sup.cobounded2 sup_commute mult_L_omega mult_assoc)

text \<open>AACP Theorem 8.1\<close>

lemma tarski_mult_top_idempotent:
  "x * L = x * L * x * L"
  by (metis omega_unfold mult_L_omega mult_assoc)

text \<open>AACP Theorem 8.7\<close>

lemma n_below_n_omega:
  "n(x) \<le> n(x\<^sup>\<omega>)"
proof -
  have "n(x) * L \<le> n(x) * L * n(x) * L"
    by (simp add: tarski)
  also have "... \<le> x * n(x) * L"
    by (simp add: mult_isotone n_L_decreasing)
  finally have "n(x) * L \<le> x\<^sup>\<omega>"
    by (simp add: omega_induct_mult mult_assoc)
  thus ?thesis
    by (simp add: n_galois)
qed

text \<open>AACP Theorem 8.14\<close>

lemma n_split_omega_sup_zero:
  "C (x\<^sup>\<omega>) \<le> x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top"
proof -
  have "n(x\<^sup>\<omega>) * top \<squnion> x * (x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top) = n(x\<^sup>\<omega>) * top \<squnion> x * x\<^sup>\<star> * bot \<squnion> x * n(x\<^sup>\<omega>) * top"
    by (simp add: mult_left_dist_sup sup_assoc mult_assoc)
  also have "... \<le> n(x\<^sup>\<omega>) * top \<squnion> x * x\<^sup>\<star> * bot \<squnion> x * bot \<squnion> n(x\<^sup>\<omega>) * top"
    by (metis sup_assoc sup_right_isotone n_n_top_split_n_top omega_unfold)
  also have "... = x * x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top"
    by (smt sup_assoc sup_commute sup_left_top sup_bot_right mult_assoc mult_left_dist_sup)
  also have "... \<le> x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top"
    by (metis sup_left_isotone mult_left_isotone star.left_plus_below_circ)
  finally have "x\<^sup>\<star> * n(x\<^sup>\<omega>) * top \<le> x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top"
    using star_left_induct mult_assoc by auto
  thus ?thesis
    using n_split_omega_mult order_trans by blast
qed

lemma n_split_omega_sup:
  "C (x\<^sup>\<omega>) \<le> x\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * top"
  by (metis sup_left_isotone n_split_omega_sup_zero order_trans zero_right_mult_decreasing)

text \<open>AACP Theorem 8.12\<close>

lemma n_dist_omega_star:
  "n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) = n(y\<^sup>\<omega>) \<squnion> n(y\<^sup>\<star> * z)"
proof -
  have "n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) = n(C (y\<^sup>\<omega>) \<squnion> C (y\<^sup>\<star> * z))"
    by (metis inf_sup_distrib1 n_C)
  also have "... \<le> n(C (y\<^sup>\<omega>) \<squnion> y\<^sup>\<star> * z)"
    using n_isotone semiring.add_right_mono sup_commute by auto
  also have "... \<le> n(y\<^sup>\<star> * bot \<squnion> n(y\<^sup>\<omega>) * top \<squnion> y\<^sup>\<star> * z)"
    using n_isotone semiring.add_right_mono n_split_omega_sup_zero by blast
  also have "... = n(y\<^sup>\<omega>) \<squnion> n(y\<^sup>\<star> * z)"
    by (smt sup_assoc sup_commute sup_bot_right mult_left_dist_sup n_dist_n_add)
  finally show ?thesis
    by (simp add: order.antisym n_isotone)
qed

lemma mult_L_sup_circ_below:
  "(x * L \<squnion> y)\<^sup>\<Omega> \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
proof -
  have "(x * L \<squnion> y)\<^sup>\<Omega> \<le> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L) * L \<squnion> (x * L \<squnion> y)\<^sup>\<star>"
    by (simp add: Omega_def mult_L_sup_omega)
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> n(y\<^sup>\<star> * x * L) * L \<squnion> (x * L \<squnion> y)\<^sup>\<star>"
    by (simp add: semiring.distrib_right mult_assoc n_dist_omega_star)
  also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    by (smt (z3) le_supI sup.cobounded1 sup_assoc sup_commute sup_idem sup_right_isotone mult_L_sup_star n_L_decreasing)
  finally show ?thesis
    .
qed

lemma n_mult_omega_L_below_zero:
  "n(y * x\<^sup>\<omega>) * L \<le> y * x\<^sup>\<star> * bot \<squnion> y * n(x\<^sup>\<omega>) * L"
proof -
  have "n(y * x\<^sup>\<omega>) * L \<le> C (y * x\<^sup>\<omega>) \<sqinter> L"
    by (metis n_C n_L_decreasing_meet_L)
  also have "... \<le> y * C (x\<^sup>\<omega>) \<sqinter> L"
    using inf.sup_left_isotone n_L_T_meet_mult n_L_T_meet_mult_propagate by auto
  also have "... \<le> y * (x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top) \<sqinter> L"
    using inf.sup_left_isotone mult_right_isotone n_split_omega_sup_zero by auto
  also have "... = (y * x\<^sup>\<star> * bot \<sqinter> L) \<squnion> (y * n(x\<^sup>\<omega>) * top \<sqinter> L)"
    using inf_sup_distrib2 mult_left_dist_sup mult_assoc by auto
  also have "... \<le> (y * x\<^sup>\<star> * bot \<sqinter> L) \<squnion> y * n(x\<^sup>\<omega>) * L"
    using n_vector_meet_L sup_right_isotone by auto
  also have "... \<le> y * x\<^sup>\<star> * bot \<squnion> y * n(x\<^sup>\<omega>) * L"
    using sup_left_isotone by auto
  finally show ?thesis
    .
qed

text \<open>AACP Theorem 8.10\<close>

lemma n_mult_omega_L_star_zero:
  "y * x\<^sup>\<star> * bot \<squnion> n(y * x\<^sup>\<omega>) * L = y * x\<^sup>\<star> * bot \<squnion> y * n(x\<^sup>\<omega>) * L"
  apply (rule order.antisym)
  apply (simp add: n_mult_omega_L_below_zero)
  by (smt sup_assoc sup_commute sup_bot_left sup_right_isotone mult_assoc mult_left_dist_sup n_n_L_split_n_L)

text \<open>AACP Theorem 8.11\<close>

lemma n_mult_omega_L_star:
  "y * x\<^sup>\<star> \<squnion> n(y * x\<^sup>\<omega>) * L = y * x\<^sup>\<star> \<squnion> y * n(x\<^sup>\<omega>) * L"
  by (metis zero_right_mult_decreasing n_mult_omega_L_star_zero sup_relative_same_increasing)

lemma n_mult_omega_L_below:
  "n(y * x\<^sup>\<omega>) * L \<le> y * x\<^sup>\<star> \<squnion> y * n(x\<^sup>\<omega>) * L"
  using sup_right_divisibility n_mult_omega_L_star by blast

lemma n_omega_L_below_zero:
  "n(x\<^sup>\<omega>) * L \<le> x * x\<^sup>\<star> * bot \<squnion> x * n(x\<^sup>\<omega>) * L"
  by (metis omega_unfold n_mult_omega_L_below_zero)

lemma n_omega_L_below:
  "n(x\<^sup>\<omega>) * L \<le> x\<^sup>\<star> \<squnion> x * n(x\<^sup>\<omega>) * L"
  by (metis omega_unfold n_mult_omega_L_below sup_left_isotone star.left_plus_below_circ order_trans)

lemma n_omega_L_star_zero:
  "x * x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * L = x * x\<^sup>\<star> * bot \<squnion> x * n(x\<^sup>\<omega>) * L"
  by (metis n_mult_omega_L_star_zero omega_unfold)

text \<open>AACP Theorem 8.8\<close>

lemma n_omega_L_star:
  "x\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L = x\<^sup>\<star> \<squnion> x * n(x\<^sup>\<omega>) * L"
  by (metis star.circ_mult_upper_bound star.left_plus_below_circ bot_least n_omega_L_star_zero sup_relative_same_increasing)

text \<open>AACP Theorem 8.9\<close>

lemma n_omega_L_star_zero_star:
  "x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * L = x\<^sup>\<star> * bot \<squnion> x\<^sup>\<star> * n(x\<^sup>\<omega>) * L"
  by (metis n_mult_omega_L_star_zero star_mult_omega mult_assoc star.circ_transitive_equal)

text \<open>AACP Theorem 8.8\<close>

lemma n_omega_L_star_star:
  "x\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L = x\<^sup>\<star> \<squnion> x\<^sup>\<star> * n(x\<^sup>\<omega>) * L"
  by (metis zero_right_mult_decreasing n_omega_L_star_zero_star sup_relative_same_increasing)

lemma n_Omega_left_unfold:
  "1 \<squnion> x * x\<^sup>\<Omega> = x\<^sup>\<Omega>"
  by (smt Omega_def sup_assoc sup_commute mult_assoc mult_left_dist_sup n_omega_L_star star.circ_left_unfold)

lemma n_Omega_left_slide:
  "(x * y)\<^sup>\<Omega> * x \<le> x * (y * x)\<^sup>\<Omega>"
proof -
  have "(x * y)\<^sup>\<Omega> * x \<le> x * y * n((x * y)\<^sup>\<omega>) * L \<squnion> (x * y)\<^sup>\<star> * x"
    by (smt Omega_def sup_commute sup_left_isotone mult_assoc mult_right_dist_sup mult_right_isotone n_L_below_L n_omega_L_star)
  also have "... \<le> x * (y * bot \<squnion> n(y * (x * y)\<^sup>\<omega>) * L) \<squnion> (x * y)\<^sup>\<star> * x"
    by (metis mult_right_isotone n_n_L_split_n_L sup_commute sup_right_isotone mult_assoc)
  also have "... = x * (y * x)\<^sup>\<Omega>"
    by (smt (verit, del_insts) le_supI1 star_slide Omega_def sup_assoc sup_commute le_iff_sup mult_assoc mult_isotone mult_left_dist_sup omega_slide star.circ_increasing star.circ_slide bot_least)
  finally show ?thesis
    .
qed

lemma n_Omega_sup_1:
  "(x \<squnion> y)\<^sup>\<Omega> = x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
proof -
  have 1: "(x \<squnion> y)\<^sup>\<Omega> = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star>"
    by (simp add: Omega_def omega_decompose semiring.distrib_right star.circ_sup_9 n_dist_omega_star)
  have "n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<le> (x\<^sup>\<star> * y)\<^sup>\<star> \<squnion> x\<^sup>\<star> * (y * n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L)"
    by (metis n_omega_L_below mult_assoc)
  also have "... \<le> (x\<^sup>\<star> * y)\<^sup>\<star> \<squnion> x\<^sup>\<star> * y * bot \<squnion> x\<^sup>\<star> * n((y * x\<^sup>\<star>)\<^sup>\<omega>) * L"
    by (smt sup_assoc sup_right_isotone mult_assoc mult_left_dist_sup mult_right_isotone n_n_L_split_n_L omega_slide)
  also have "... = (x\<^sup>\<star> * y)\<^sup>\<star> \<squnion> x\<^sup>\<star> * n((y * x\<^sup>\<star>)\<^sup>\<omega>) * L"
    by (metis sup_commute le_iff_sup star.circ_sub_dist_1 zero_right_mult_decreasing)
  also have "... \<le> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star> \<squnion> x\<^sup>\<star> * n((y * x\<^sup>\<star>)\<^sup>\<omega>) * L"
    by (metis star_outer_increasing star_slide star_star_absorb sup_left_isotone)
  also have "... \<le> x\<^sup>\<star> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
    by (metis Omega_def sup_commute mult_assoc mult_left_dist_sup mult_right_isotone n_Omega_isotone n_star_below_Omega)
  also have "... \<le> x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
    by (simp add: mult_left_isotone n_star_below_Omega)
  finally have 2: "n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<le> x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
    .
  have "n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L \<le> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star> \<squnion> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star> * y * n(x\<^sup>\<omega>) * L"
    by (smt sup_assoc sup_commute mult_left_one mult_right_dist_sup n_mult_omega_L_below star.circ_mult star.circ_slide)
  also have "... = n(x\<^sup>\<omega>) * L * (y * x\<^sup>\<Omega>)\<^sup>\<star> \<squnion> x\<^sup>\<star> * (y * x\<^sup>\<Omega>)\<^sup>\<star>"
    by (smt Omega_def sup_assoc mult_L_sup_star mult_assoc mult_left_dist_sup L_mult_star)
  also have "... \<le> x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
    by (simp add: Omega_def mult_isotone)
  finally have 3: "n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L \<le> x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
    .
  have "(x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<le> x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
    by (metis star_slide mult_isotone mult_right_isotone n_star_below_Omega order_trans star_isotone)
  hence 4: "(x \<squnion> y)\<^sup>\<Omega> \<le> x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
    using 1 2 3 by simp
  have 5: "x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega> \<le> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * n((y * x\<^sup>\<Omega>)\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * (y * x\<^sup>\<Omega>)\<^sup>\<star>"
    by (smt Omega_def sup_assoc sup_left_isotone mult_assoc mult_left_dist_sup mult_right_dist_sup mult_right_isotone n_L_below_L)
  have "n(x\<^sup>\<omega>) * L \<le> n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L"
    by (metis sup_commute sup_ge1 mult_left_isotone n_isotone star.circ_loop_fixpoint)
  hence 6: "n(x\<^sup>\<omega>) * L \<le> (x \<squnion> y)\<^sup>\<Omega>"
    using 1 order_lesseq_imp by fastforce
  have "x\<^sup>\<star> * n((y * x\<^sup>\<Omega>)\<^sup>\<omega>) * L \<le> x\<^sup>\<star> * n((y * x\<^sup>\<star>)\<^sup>\<omega> \<squnion> (y * x\<^sup>\<star>)\<^sup>\<star> * y * n(x\<^sup>\<omega>) * L) * L"
    by (metis Omega_def mult_L_sup_omega_below mult_assoc mult_left_dist_sup mult_left_isotone mult_right_isotone n_isotone)
  also have "... \<le> x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<star> * ((y * x\<^sup>\<star>)\<^sup>\<omega> \<squnion> (y * x\<^sup>\<star>)\<^sup>\<star> * y * n(x\<^sup>\<omega>) * L)) * L"
    by (simp add: n_n_L_split_n_L)
  also have "... \<le> x\<^sup>\<star> \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> x\<^sup>\<star> * (y * x\<^sup>\<star>)\<^sup>\<star> * y * n(x\<^sup>\<omega>) * L) * L"
    using omega_slide semiring.distrib_left sup_mono zero_right_mult_decreasing mult_assoc by fastforce
  also have "... \<le> x\<^sup>\<star> \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L) * L"
    by (smt sup_right_divisibility sup_right_isotone mult_left_isotone n_isotone star.circ_mult)
  also have "... \<le> x\<^sup>\<star> \<squnion> n((x \<squnion> y)\<^sup>\<omega>) * L"
    by (metis sup_right_isotone mult_assoc mult_left_isotone mult_right_isotone n_L_decreasing n_isotone omega_decompose)
  also have "... \<le> (x \<squnion> y)\<^sup>\<Omega>"
    by (simp add: Omega_def le_supI1 star_isotone sup_commute)
  finally have 7: "x\<^sup>\<star> * n((y * x\<^sup>\<Omega>)\<^sup>\<omega>) * L \<le> (x \<squnion> y)\<^sup>\<Omega>"
    .
  have "x\<^sup>\<star> * (y * x\<^sup>\<Omega>)\<^sup>\<star> \<le> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L"
    by (smt Omega_def sup_right_isotone mult_L_sup_star mult_assoc mult_left_dist_sup mult_left_isotone star.left_plus_below_circ star_slide)
  also have "... \<le> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L"
    by (simp add: n_mult_omega_L_star)
  also have "... \<le> (x \<squnion> y)\<^sup>\<Omega>"
    by (smt Omega_def sup_commute sup_right_isotone mult_left_isotone n_right_upper_bound omega_decompose star.circ_sup)
  finally have "n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * n((y * x\<^sup>\<Omega>)\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * (y * x\<^sup>\<Omega>)\<^sup>\<star> \<le> (x \<squnion> y)\<^sup>\<Omega>"
    using 6 7 by simp
  hence "x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega> \<le> (x \<squnion> y)\<^sup>\<Omega>"
    using 5 order.trans by blast
  thus ?thesis
    using 4 order.antisym by blast
qed

end

sublocale n_omega_algebra < nL_omega: left_zero_conway_semiring where circ = Omega
  apply unfold_locales
  apply (simp add: n_Omega_left_unfold)
  apply (simp add: n_Omega_left_slide)
  by (simp add: n_Omega_sup_1)

(* circ_plus_same does not hold in the non-strict model using Omega *)

context n_omega_algebra
begin

text \<open>AACP Theorem 8.16\<close>

lemma omega_apx_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x\<^sup>\<omega> \<sqsubseteq> y\<^sup>\<omega>"
proof -
  have 1: "x \<le> y \<squnion> L \<and> C y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  have "n(x) * top \<squnion> x * (x\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * top) \<le> n(x) * top \<squnion> x\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * top"
    by (metis le_supI n_split_top sup.cobounded1 sup_assoc mult_assoc mult_left_dist_sup sup_right_isotone omega_unfold)
  also have "... \<le> x\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * top"
    by (metis sup_commute sup_right_isotone mult_left_isotone n_below_n_omega sup_assoc sup_idem)
  finally have 2: "x\<^sup>\<star> * n(x) * top \<le> x\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * top"
    using star_left_induct mult_assoc by auto
  have "C (y\<^sup>\<omega>) = (C y)\<^sup>\<omega>"
    by (simp add: C_omega_export)
  also have "... \<le> (x \<squnion> n(x) * top)\<^sup>\<omega>"
    using 1 omega_isotone by blast
  also have "... = (x\<^sup>\<star> * n(x) * top)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * n(x) * top)\<^sup>\<star> * x\<^sup>\<omega>"
    by (simp add: omega_decompose mult_assoc)
  also have "... \<le> x\<^sup>\<star> * n(x) * top \<squnion> (x\<^sup>\<star> * n(x) * top)\<^sup>\<star> * x\<^sup>\<omega>"
    using mult_top_omega sup_left_isotone by blast
  also have "... = x\<^sup>\<star> * n(x) * top \<squnion> (1 \<squnion> x\<^sup>\<star> * n(x) * top * (x\<^sup>\<star> * n(x) * top)\<^sup>\<star>) * x\<^sup>\<omega>"
    by (simp add: star_left_unfold_equal)
  also have "... \<le> x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * n(x) * top"
    by (smt sup_mono sup_least mult_assoc mult_left_one mult_right_dist_sup mult_right_isotone order_refl top_greatest sup.cobounded2)
  also have "... \<le> x\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * top"
    using 2 by simp
  finally have 3: "C (y\<^sup>\<omega>) \<le> x\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * top"
    .
  have "x\<^sup>\<omega> \<le> (y \<squnion> L)\<^sup>\<omega>"
    using 1 omega_isotone by simp
  also have "... = (y\<^sup>\<star> * L)\<^sup>\<omega> \<squnion> (y\<^sup>\<star> * L)\<^sup>\<star> * y\<^sup>\<omega>"
    by (simp add: omega_decompose)
  also have "... = y\<^sup>\<star> * L * (y\<^sup>\<star> * L)\<^sup>\<omega> \<squnion> (y\<^sup>\<star> * L)\<^sup>\<star> * y\<^sup>\<omega>"
    using omega_unfold by auto
  also have "... \<le> y\<^sup>\<star> * L \<squnion> (y\<^sup>\<star> * L)\<^sup>\<star> * y\<^sup>\<omega>"
    by (metis sup_left_isotone n_L_below_L mult_assoc mult_right_isotone)
  also have "... = y\<^sup>\<star> * L \<squnion> (1 \<squnion> y\<^sup>\<star> * L * (y\<^sup>\<star> * L)\<^sup>\<star>) * y\<^sup>\<omega>"
    by (simp add: star_left_unfold_equal)
  also have "... \<le> y\<^sup>\<star> * L \<squnion> y\<^sup>\<omega>"
    by (simp add: mult_L_star_mult_below star_left_unfold_equal sup_commute)
  also have "... \<le> y\<^sup>\<star> * bot \<squnion> L \<squnion> y\<^sup>\<omega>"
    using n_L_split_L sup_left_isotone by auto
  finally have "x\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> L"
    by (simp add: star_bot_below_omega sup.absorb1 sup.left_commute sup_commute)
  thus "x\<^sup>\<omega> \<sqsubseteq> y\<^sup>\<omega>"
    using 3 by (simp add: apx_def)
qed

lemma combined_apx_left_isotone:
  "x \<sqsubseteq> y \<Longrightarrow> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * z \<sqsubseteq> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z"
  by (simp add: mult_apx_isotone n_L_apx_isotone star.circ_apx_isotone sup_apx_isotone omega_apx_isotone)

lemma combined_apx_left_isotone_2:
  "x \<sqsubseteq> y \<Longrightarrow> (x\<^sup>\<omega> \<sqinter> L) \<squnion> x\<^sup>\<star> * z \<sqsubseteq> (y\<^sup>\<omega> \<sqinter> L) \<squnion> y\<^sup>\<star> * z"
  by (metis sup_apx_isotone mult_apx_left_isotone omega_apx_isotone star.circ_apx_isotone meet_L_apx_isotone)

lemma combined_apx_right_isotone:
  "y \<sqsubseteq> z \<Longrightarrow> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * y \<sqsubseteq> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * z"
  by (simp add: mult_apx_isotone sup_apx_left_isotone sup_commute)

lemma combined_apx_right_isotone_2:
  "y \<sqsubseteq> z \<Longrightarrow> (x\<^sup>\<omega> \<sqinter> L) \<squnion> x\<^sup>\<star> * y \<sqsubseteq> (x\<^sup>\<omega> \<sqinter> L) \<squnion> x\<^sup>\<star> * z"
  by (simp add: mult_apx_right_isotone sup_apx_right_isotone)

lemma combined_apx_isotone:
  "x \<sqsubseteq> y \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w \<sqsubseteq> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z"
  by (simp add: mult_apx_isotone n_L_apx_isotone star.circ_apx_isotone sup_apx_isotone omega_apx_isotone)

lemma combined_apx_isotone_2:
  "x \<sqsubseteq> y \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> (x\<^sup>\<omega> \<sqinter> L) \<squnion> x\<^sup>\<star> * w \<sqsubseteq> (y\<^sup>\<omega> \<sqinter> L) \<squnion> y\<^sup>\<star> * z"
  by (meson combined_apx_left_isotone_2 combined_apx_right_isotone_2 apx.order.trans)

lemma n_split_nu_mu:
  "C (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<le> y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * top"
proof -
  have "C (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<le> C (y\<^sup>\<omega>) \<squnion> y\<^sup>\<star> * z"
    by (simp add: inf_sup_distrib1 le_supI1 sup_commute)
  also have "... \<le> y\<^sup>\<star> * bot \<squnion> n(y\<^sup>\<omega>) * top \<squnion> y\<^sup>\<star> * z"
    using n_split_omega_sup_zero sup_left_isotone by blast
  also have "... \<le> y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * top"
    using le_supI1 mult_left_isotone mult_right_isotone n_left_upper_bound sup_right_isotone by force
  finally show ?thesis
    .
qed

lemma n_split_nu_mu_2:
  "C (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<le> y\<^sup>\<star> * z \<squnion> ((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<sqinter> L) \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * top"
proof -
  have "C (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<le> C (y\<^sup>\<omega>) \<squnion> y\<^sup>\<star> * z"
    using inf.sup_left_isotone sup_inf_distrib2 by auto
  also have "... \<le> y\<^sup>\<star> * bot \<squnion> n(y\<^sup>\<omega>) * top \<squnion> y\<^sup>\<star> * z"
    using n_split_omega_sup_zero sup_left_isotone by blast
  also have "... \<le> y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * top"
    using le_supI1 mult_left_isotone mult_right_isotone n_left_upper_bound semiring.add_left_mono by auto
  finally show ?thesis
    using order_lesseq_imp semiring.add_right_mono sup.cobounded1 by blast
qed

lemma loop_exists:
  "C (\<nu> (\<lambda>x . y * x \<squnion> z)) \<le> \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> n(\<nu> (\<lambda>x . y * x \<squnion> z)) * top"
  using omega_loop_nu star_loop_mu n_split_nu_mu by auto

lemma loop_exists_2:
  "C (\<nu> (\<lambda>x . y * x \<squnion> z)) \<le> \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> (\<nu> (\<lambda>x . y * x \<squnion> z) \<sqinter> L) \<squnion> n(\<nu> (\<lambda>x . y * x \<squnion> z)) * top"
  by (simp add: omega_loop_nu star_loop_mu n_split_nu_mu_2)

lemma loop_apx_least_fixpoint:
  "apx.is_least_fixpoint (\<lambda>x . y * x \<squnion> z) (\<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> n(\<nu> (\<lambda>x . y * x \<squnion> z)) * L)"
proof -
  have "kappa_mu_nu_L (\<lambda>x . y * x \<squnion> z)"
    by (metis affine_apx_isotone loop_exists affine_has_greatest_fixpoint affine_has_least_fixpoint affine_isotone nu_below_mu_nu_L_def nu_below_mu_nu_L_kappa_mu_nu_L)
  thus ?thesis
    using apx.least_fixpoint_char kappa_mu_nu_L_def by force
qed

lemma loop_apx_least_fixpoint_2:
  "apx.is_least_fixpoint (\<lambda>x . y * x \<squnion> z) (\<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> (\<nu> (\<lambda>x . y * x \<squnion> z) \<sqinter> L))"
proof -
  have "kappa_mu_nu (\<lambda>x . y * x \<squnion> z)"
    by (metis affine_apx_isotone affine_has_greatest_fixpoint affine_has_least_fixpoint affine_isotone loop_exists_2 nu_below_mu_nu_def nu_below_mu_nu_kappa_mu_nu)
  thus ?thesis
    using apx.least_fixpoint_char kappa_mu_nu_def by force
qed

lemma loop_has_apx_least_fixpoint:
  "apx.has_least_fixpoint (\<lambda>x . y * x \<squnion> z)"
  using apx.least_fixpoint_char loop_apx_least_fixpoint by blast

lemma loop_semantics:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> n(\<nu> (\<lambda>x . y * x \<squnion> z)) * L"
  using apx.least_fixpoint_char loop_apx_least_fixpoint by force

lemma loop_semantics_2:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> (\<nu> (\<lambda>x . y * x \<squnion> z) \<sqinter> L)"
  using apx.least_fixpoint_char loop_apx_least_fixpoint_2 by force

text \<open>AACP Theorem 8.15\<close>

lemma loop_semantics_kappa_mu_nu:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z"
proof -
  have "\<kappa> (\<lambda>x . y * x \<squnion> z) = y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * L"
    using apx.least_fixpoint_char omega_loop_nu star_loop_mu loop_apx_least_fixpoint by auto
  thus ?thesis
    by (smt n_dist_omega_star sup_assoc mult_right_dist_sup sup_commute le_iff_sup n_L_decreasing)
qed

text \<open>AACP Theorem 8.15\<close>

lemma loop_semantics_kappa_mu_nu_2:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = (y\<^sup>\<omega> \<sqinter> L) \<squnion> y\<^sup>\<star> * z"
proof -
  have "\<kappa> (\<lambda>x . y * x \<squnion> z) = y\<^sup>\<star> * z \<squnion> ((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<sqinter> L)"
    using apx.least_fixpoint_char omega_loop_nu star_loop_mu loop_apx_least_fixpoint_2 by auto
  thus ?thesis
    by (metis sup_absorb2 sup_ge2 sup_inf_distrib1 sup_monoid.add_commute)
qed

text \<open>AACP Theorem 8.16\<close>

lemma loop_semantics_apx_left_isotone:
  "w \<sqsubseteq> y \<Longrightarrow> \<kappa> (\<lambda>x . w * x \<squnion> z) \<sqsubseteq> \<kappa> (\<lambda>x . y * x \<squnion> z)"
  by (metis loop_semantics_kappa_mu_nu_2 combined_apx_left_isotone_2)

text \<open>AACP Theorem 8.16\<close>

lemma loop_semantics_apx_right_isotone:
  "w \<sqsubseteq> z \<Longrightarrow> \<kappa> (\<lambda>x . y * x \<squnion> w) \<sqsubseteq> \<kappa> (\<lambda>x . y * x \<squnion> z)"
  by (metis loop_semantics_kappa_mu_nu_2 combined_apx_right_isotone_2)

lemma loop_semantics_apx_isotone:
  "v \<sqsubseteq> y \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> \<kappa> (\<lambda>x . v * x \<squnion> w) \<sqsubseteq> \<kappa> (\<lambda>x . y * x \<squnion> z)"
  using apx_transitive_2 loop_semantics_apx_left_isotone loop_semantics_apx_right_isotone by blast

end

end

