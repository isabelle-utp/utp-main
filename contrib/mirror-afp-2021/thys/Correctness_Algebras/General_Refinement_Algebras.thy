(* Title:      General Refinement Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>General Refinement Algebras\<close>

theory General_Refinement_Algebras

imports Omega_Algebras

begin

class general_refinement_algebra = left_kleene_algebra + Omega +
  assumes Omega_unfold: "y\<^sup>\<Omega> \<le> 1 \<squnion> y * y\<^sup>\<Omega>"
  assumes Omega_induct: "x \<le> z \<squnion> y * x \<longrightarrow> x \<le> y\<^sup>\<Omega> * z"
begin

lemma Omega_unfold_equal:
  "y\<^sup>\<Omega> = 1 \<squnion> y * y\<^sup>\<Omega>"
  by (smt Omega_induct Omega_unfold sup_right_isotone order.antisym mult_right_isotone mult_1_right)

lemma Omega_sup_1:
  "(x \<squnion> y)\<^sup>\<Omega> = x\<^sup>\<Omega> * (y * x\<^sup>\<Omega>)\<^sup>\<Omega>"
  apply (rule order.antisym)
  apply (smt Omega_induct Omega_unfold_equal sup_assoc sup_commute sup_right_isotone mult_assoc mult_right_dist_sup mult_right_isotone mult_1_right order_refl)
  by (smt Omega_induct Omega_unfold_equal sup_assoc sup_commute mult_assoc mult_left_one mult_right_dist_sup mult_1_right order_refl)

lemma Omega_left_slide:
  "(x * y)\<^sup>\<Omega> * x \<le> x * (y * x)\<^sup>\<Omega>"
proof -
  have "1 \<squnion> y * (x * y)\<^sup>\<Omega> * x \<le> 1 \<squnion> y * x * (1 \<squnion> (y * (x * y)\<^sup>\<Omega>) * x)"
    by (smt Omega_unfold_equal sup_right_isotone mult_assoc mult_left_one mult_left_sub_dist_sup mult_right_dist_sup mult_right_isotone mult_1_right)
  thus ?thesis
    by (smt Omega_induct Omega_unfold_equal le_sup_iff mult_assoc mult_left_one mult_right_dist_sup mult_right_isotone mult_1_right)
qed

end

text \<open>Theorem 50.3\<close>

sublocale general_refinement_algebra < Omega: left_conway_semiring where circ = Omega
  apply unfold_locales
  using Omega_unfold_equal apply simp
  apply (simp add: Omega_left_slide)
  by (simp add: Omega_sup_1)

context general_refinement_algebra
begin

lemma star_below_Omega:
  "x\<^sup>\<star> \<le> x\<^sup>\<Omega>"
  by (metis Omega_induct mult_1_right order_refl star.circ_left_unfold)

lemma star_mult_Omega:
  "x\<^sup>\<Omega> = x\<^sup>\<star> * x\<^sup>\<Omega>"
  by (metis Omega.left_plus_below_circ sup_commute sup_ge1 order.eq_iff star.circ_loop_fixpoint star_left_induct_mult_iff)

lemma Omega_one_greatest:
  "x \<le> 1\<^sup>\<Omega>"
  by (metis Omega_induct sup_bot_left mult_left_one order_refl order_trans zero_right_mult_decreasing)

lemma greatest_left_zero:
  "1\<^sup>\<Omega> * x = 1\<^sup>\<Omega>"
  by (simp add: Omega_one_greatest Omega_induct order.antisym)

(*
lemma circ_right_unfold: "1 \<squnion> x\<^sup>\<Omega> * x = x\<^sup>\<Omega>" nitpick [expect=genuine,card=8] oops
lemma circ_slide: "(x * y)\<^sup>\<Omega> * x = x * (y * x)\<^sup>\<Omega>" nitpick [expect=genuine,card=6] oops
lemma circ_simulate: "z * x \<le> y * z \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * z" nitpick [expect=genuine,card=6] oops
lemma circ_simulate_right: "z * x \<le> y * z \<squnion> w \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)" nitpick [expect=genuine,card=6] oops
lemma circ_simulate_right_1: "z * x \<le> y * z \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * z" nitpick [expect=genuine,card=6] oops
lemma circ_simulate_right_plus: "z * x \<le> y * y\<^sup>\<Omega> * z \<squnion> w \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)" nitpick [expect=genuine,card=6] oops
lemma circ_simulate_right_plus_1: "z * x \<le> y * y\<^sup>\<Omega> * z \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * z" nitpick [expect=genuine,card=6] oops
lemma circ_simulate_left_1: "x * z \<le> z * y \<Longrightarrow> x\<^sup>\<Omega> * z \<le> z * y\<^sup>\<Omega> \<squnion> x\<^sup>\<Omega> * bot" oops (* holds in LKA, counterexample exists in GRA *)
lemma circ_simulate_left_plus_1: "x * z \<le> z * y\<^sup>\<Omega> \<Longrightarrow> x\<^sup>\<Omega> * z \<le> z * y\<^sup>\<Omega> \<squnion> x\<^sup>\<Omega> * bot" oops (* holds in LKA, counterexample exists in GRA *)
lemma circ_simulate_absorb: "y * x \<le> x \<Longrightarrow> y\<^sup>\<Omega> * x \<le> x \<squnion> y\<^sup>\<Omega> * bot" nitpick [expect=genuine,card=8] oops (* holds in LKA, counterexample exists in GRA *)
*)

end

class bounded_general_refinement_algebra = general_refinement_algebra + bounded_left_kleene_algebra
begin

lemma Omega_one:
  "1\<^sup>\<Omega> = top"
  by (simp add: Omega_one_greatest order.antisym)

lemma top_left_zero:
  "top * x = top"
  using Omega_one greatest_left_zero by blast

end

sublocale bounded_general_refinement_algebra < Omega: bounded_left_conway_semiring where circ = Omega ..

class left_demonic_refinement_algebra = general_refinement_algebra +
  assumes Omega_isolate: "y\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * bot \<squnion> y\<^sup>\<star>"
begin

lemma Omega_isolate_equal:
  "y\<^sup>\<Omega> = y\<^sup>\<Omega> * bot \<squnion> y\<^sup>\<star>"
  using Omega_isolate order.antisym le_sup_iff star_below_Omega zero_right_mult_decreasing by auto

(*
lemma Omega_sum_unfold_1: "(x \<squnion> y)\<^sup>\<Omega> = y\<^sup>\<Omega> \<squnion> y\<^sup>\<star> * x * (x \<squnion> y)\<^sup>\<Omega>" oops
lemma Omega_sup_3: "(x \<squnion> y)\<^sup>\<Omega> = (x\<^sup>\<star> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>" oops
*)

end

class bounded_left_demonic_refinement_algebra = left_demonic_refinement_algebra + bounded_left_kleene_algebra
begin

(*
lemma Omega_mult: "(x * y)\<^sup>\<Omega> = 1 \<squnion> x * (y * x)\<^sup>\<Omega> * y" oops
lemma Omega_sup: "(x \<squnion> y)\<^sup>\<Omega> = (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>" oops
lemma Omega_simulate: "z * x \<le> y * z \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * z" nitpick [expect=genuine,card=6] oops
lemma Omega_separate_2: "y * x \<le> x * (x \<squnion> y) \<Longrightarrow> (x \<squnion> y)\<^sup>\<Omega> = x\<^sup>\<Omega> * y\<^sup>\<Omega>" oops
lemma Omega_circ_simulate_right_plus: "z * x \<le> y * y\<^sup>\<Omega> * z \<squnion> w \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)" nitpick [expect=genuine,card=6] oops
lemma Omega_circ_simulate_left_plus: "x * z \<le> z * y\<^sup>\<Omega> \<squnion> w \<Longrightarrow> x\<^sup>\<Omega> * z \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>" oops
*)

end

sublocale bounded_left_demonic_refinement_algebra < Omega: bounded_left_conway_semiring where circ = Omega ..

class demonic_refinement_algebra = left_zero_kleene_algebra + left_demonic_refinement_algebra
begin

lemma Omega_mult:
  "(x * y)\<^sup>\<Omega> = 1 \<squnion> x * (y * x)\<^sup>\<Omega> * y"
  by (smt (verit, del_insts) Omega.circ_left_slide Omega_induct Omega_unfold_equal order.eq_iff mult_assoc mult_left_dist_sup mult_1_right)

lemma Omega_sup:
  "(x \<squnion> y)\<^sup>\<Omega> = (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
  by (smt Omega_sup_1 Omega_mult mult_assoc mult_left_dist_sup mult_left_one mult_right_dist_sup mult_1_right)

lemma Omega_simulate:
  "z * x \<le> y * z \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * z"
  by (smt Omega_induct Omega_unfold_equal sup_right_isotone mult_assoc mult_left_dist_sup mult_left_isotone mult_1_right)

end

text \<open>Theorem 2.4\<close>

sublocale demonic_refinement_algebra < Omega1: itering_1 where circ = Omega
  apply unfold_locales
  apply (simp add: Omega_simulate mult_assoc)
  by (simp add: Omega_simulate)

sublocale demonic_refinement_algebra < Omega1: left_zero_conway_semiring_1 where circ = Omega ..

context demonic_refinement_algebra
begin

lemma Omega_sum_unfold_1:
  "(x \<squnion> y)\<^sup>\<Omega> = y\<^sup>\<Omega> \<squnion> y\<^sup>\<star> * x * (x \<squnion> y)\<^sup>\<Omega>"
  by (smt Omega1.circ_sup_9 Omega.circ_loop_fixpoint Omega_isolate_equal sup_assoc sup_commute mult_assoc mult_left_zero mult_right_dist_sup)

lemma Omega_sup_3:
  "(x \<squnion> y)\<^sup>\<Omega> = (x\<^sup>\<star> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
  apply (rule order.antisym)
  apply (metis Omega_sum_unfold_1 Omega_induct eq_refl sup_commute)
  by (simp add: Omega.circ_isotone Omega_sup mult_left_isotone star_below_Omega)

lemma Omega_separate_2:
  "y * x \<le> x * (x \<squnion> y) \<Longrightarrow> (x \<squnion> y)\<^sup>\<Omega> = x\<^sup>\<Omega> * y\<^sup>\<Omega>"
  apply (rule order.antisym)
  apply (smt (verit, del_insts) Omega_induct Omega_sum_unfold_1 sup_right_isotone mult_assoc mult_left_isotone star_mult_Omega star_simulation_left)
  by (simp add: Omega.circ_sub_dist_3)

lemma Omega_circ_simulate_right_plus:
  assumes "z * x \<le> y * y\<^sup>\<Omega> * z \<squnion> w"
    shows "z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)"
proof -
  have "z * x\<^sup>\<Omega> = z \<squnion> z * x * x\<^sup>\<Omega>"
    using Omega1.circ_back_loop_fixpoint Omega1.circ_plus_same sup_commute mult_assoc by auto
  also have "... \<le> y * y\<^sup>\<Omega> * z * x\<^sup>\<Omega> \<squnion> z \<squnion> w * x\<^sup>\<Omega>"
    by (smt assms sup_assoc sup_commute sup_right_isotone le_iff_sup mult_right_dist_sup)
  finally have "z * x\<^sup>\<Omega> \<le> (y * y\<^sup>\<Omega>)\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)"
    by (smt Omega_induct sup_assoc sup_commute mult_assoc)
  thus ?thesis
    by (simp add: Omega.left_plus_circ)
qed

lemma Omega_circ_simulate_left_plus:
  assumes "x * z \<le> z * y\<^sup>\<Omega> \<squnion> w"
    shows "x\<^sup>\<Omega> * z \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
proof -
  have "x * ((z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>) \<le> (z * y\<^sup>\<Omega> \<squnion> w \<squnion> x * x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
    by (smt assms mult_assoc mult_left_dist_sup sup_left_isotone mult_left_isotone)
  also have "... \<le> z * y\<^sup>\<Omega> * y\<^sup>\<Omega> \<squnion> w * y\<^sup>\<Omega> \<squnion> x\<^sup>\<Omega> * w * y\<^sup>\<Omega>"
    by (smt Omega.left_plus_below_circ sup_right_isotone mult_left_isotone mult_right_dist_sup)
  finally have 1: "x * ((z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>) \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
    by (metis Omega.circ_transitive_equal mult_assoc Omega.circ_reflexive sup_assoc le_iff_sup mult_left_one mult_right_dist_sup)
  have "x\<^sup>\<Omega> * z  = x\<^sup>\<Omega> * bot \<squnion> x\<^sup>\<star> * z"
    by (metis Omega_isolate_equal mult_assoc mult_left_zero mult_right_dist_sup)
  also have "... \<le> x\<^sup>\<Omega> * w * y\<^sup>\<Omega> \<squnion> x\<^sup>\<star> * (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
    by (metis Omega1.circ_back_loop_fixpoint bot_least idempotent_bot_closed le_supI2 mult_isotone mult_left_sub_dist_sup_left semiring.add_mono zero_right_mult_decreasing mult_assoc)
  also have "... \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
    using 1 by (metis le_supI mult_right_sub_dist_sup_right star_left_induct_mult mult_assoc)
  finally show ?thesis
    .
qed

lemma Omega_circ_simulate_right:
  assumes "z * x \<le> y * z \<squnion> w"
    shows "z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)"
proof -
  have "y * z \<squnion> w \<le> y * y\<^sup>\<Omega> * z \<squnion> w"
    using Omega.circ_mult_increasing mult_left_isotone sup_left_isotone by auto
  thus ?thesis
    using Omega_circ_simulate_right_plus assms order.trans by blast
qed

end

sublocale demonic_refinement_algebra < Omega: itering where circ = Omega
  apply unfold_locales
  apply (simp add: Omega_sup)
  using Omega_mult apply blast
  apply (simp add: Omega_circ_simulate_right_plus)
  using Omega_circ_simulate_left_plus by auto

class bounded_demonic_refinement_algebra = demonic_refinement_algebra + bounded_left_zero_kleene_algebra
begin

lemma Omega_one:
  "1\<^sup>\<Omega> = top"
  by (simp add: Omega_one_greatest order.antisym)

lemma top_left_zero:
  "top * x = top"
  using Omega_one greatest_left_zero by auto

end

sublocale bounded_demonic_refinement_algebra < Omega: bounded_itering where circ = Omega ..

class general_refinement_algebra_omega = left_omega_algebra + Omega +
  assumes omega_left_zero: "x\<^sup>\<omega> \<le> x\<^sup>\<omega> * y"
  assumes Omega_def: "x\<^sup>\<Omega> = x\<^sup>\<omega> \<squnion> x\<^sup>\<star>"
begin

lemma omega_left_zero_equal:
  "x\<^sup>\<omega> * y = x\<^sup>\<omega>"
  by (simp add: order.antisym omega_left_zero omega_sub_vector)

subclass left_demonic_refinement_algebra
  apply unfold_locales
  apply (metis Omega_def sup_commute eq_refl mult_1_right omega_loop_fixpoint)
  apply (metis Omega_def mult_right_dist_sup omega_induct omega_left_zero_equal)
  by (metis Omega_def mult_right_sub_dist_sup_right sup_commute sup_right_isotone omega_left_zero_equal)

end

class left_demonic_refinement_algebra_omega = bounded_left_omega_algebra + Omega +
  assumes top_left_zero: "top * x = top"
  assumes Omega_def: "x\<^sup>\<Omega> = x\<^sup>\<omega> \<squnion> x\<^sup>\<star>"
begin

subclass general_refinement_algebra_omega
  apply unfold_locales
  apply (metis mult_assoc omega_vector order_refl top_left_zero)
  by (rule Omega_def)

end

class demonic_refinement_algebra_omega = left_demonic_refinement_algebra_omega + bounded_left_zero_omega_algebra
begin

lemma Omega_mult:
  "(x * y)\<^sup>\<Omega> = 1 \<squnion> x * (y * x)\<^sup>\<Omega> * y"
  by (metis Omega_def comb1.circ_mult_1 omega_left_zero_equal omega_translate)

lemma Omega_sup:
  "(x \<squnion> y)\<^sup>\<Omega> = (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
proof -
  have "(x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega> = (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>\<^sup>\<star> * x\<^sup>\<Omega>"
    by (smt sup_commute Omega_def mult_assoc mult_right_dist_sup mult_bot_add_omega omega_left_zero_equal star.circ_sup_1)
  thus ?thesis
    using Omega_def Omega_sup_1 comb2.circ_slide_1 omega_left_zero_equal by auto
qed

lemma Omega_simulate:
  "z * x \<le> y * z \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * z"
  using Omega_def comb2.circ_simulate omega_left_zero_equal by auto

subclass demonic_refinement_algebra ..

end

(*
text hold in GRA and LKA
lemma circ_circ_mult: "1\<^sup>\<Omega> * x\<^sup>\<Omega> = x\<^sup>\<Omega>\<^sup>\<Omega>" oops
lemma sub_mult_one_circ: "x * 1\<^sup>\<Omega> \<le> 1\<^sup>\<Omega> * x" oops
lemma circ_circ_mult_1: "x\<^sup>\<Omega> * 1\<^sup>\<Omega> = x\<^sup>\<Omega>\<^sup>\<Omega>" oops
lemma "y * x \<le> x \<Longrightarrow> y\<^sup>\<circ> * x \<le> 1\<^sup>\<circ> * x" oops

text unknown
lemma circ_simulate_2: "y * x\<^sup>\<Omega> \<le> x\<^sup>\<Omega> * y\<^sup>\<Omega> \<longleftrightarrow> y\<^sup>\<Omega> * x\<^sup>\<Omega> \<le> x\<^sup>\<Omega> * y\<^sup>\<Omega>" oops (* holds in LKA *)
lemma circ_simulate_3: "y * x\<^sup>\<Omega> \<le> x\<^sup>\<Omega> \<Longrightarrow> y\<^sup>\<Omega> * x\<^sup>\<Omega> \<le> x\<^sup>\<Omega> * y\<^sup>\<Omega>" oops (* holds in LKA *)
lemma circ_separate_mult_1: "y * x \<le> x * y \<Longrightarrow> (x * y)\<^sup>\<Omega> \<le> x\<^sup>\<Omega> * y\<^sup>\<Omega>" oops
lemma "x\<^sup>\<circ> = (x * x)\<^sup>\<circ> * (x \<squnion> 1)" oops
lemma "y\<^sup>\<circ> * x\<^sup>\<circ> \<le> x\<^sup>\<circ> * y\<^sup>\<circ> \<Longrightarrow> (x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>" oops
lemma "y * x \<le> (1 \<squnion> x) * y\<^sup>\<circ> \<Longrightarrow> (x \<squnion> y)\<^sup>\<circ> = x\<^sup>\<circ> * y\<^sup>\<circ>" oops
*)

end

