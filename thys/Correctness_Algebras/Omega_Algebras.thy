(* Title:      Omega Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Omega Algebras\<close>

theory Omega_Algebras

imports Stone_Kleene_Relation_Algebras.Kleene_Algebras

begin

class omega =
  fixes omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [100] 100)

class left_omega_algebra = left_kleene_algebra + omega +
  assumes omega_unfold: "y\<^sup>\<omega> = y * y\<^sup>\<omega>"
  assumes omega_induct: "x \<le> z \<squnion> y * x \<longrightarrow> x \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z"
begin

text \<open>Many lemmas in this class are taken from Georg Struth's Isabelle theories.\<close>

lemma star_bot_below_omega:
  "x\<^sup>\<star> * bot \<le> x\<^sup>\<omega>"
  using omega_unfold star_left_induct_equal by auto

lemma star_bot_below_omega_bot:
  "x\<^sup>\<star> * bot \<le> x\<^sup>\<omega> * bot"
  by (metis omega_unfold star_left_induct_equal sup_monoid.add_0_left mult_assoc)

lemma omega_induct_mult:
  "y \<le> x * y \<Longrightarrow> y \<le> x\<^sup>\<omega>"
  by (metis bot_least omega_induct sup.absorb1 sup.absorb2 star_bot_below_omega)

lemma omega_sub_dist:
  "x\<^sup>\<omega> \<le> (x \<squnion> y)\<^sup>\<omega>"
  by (metis eq_refl mult_isotone omega_unfold sup.cobounded1 omega_induct_mult)

lemma omega_isotone:
  "x \<le> y \<Longrightarrow> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
  using sup_left_divisibility omega_sub_dist by fastforce

lemma omega_induct_equal:
  "y = z \<squnion> x * y \<Longrightarrow> y \<le> x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z"
  by (simp add: omega_induct)

lemma omega_bot:
  "bot\<^sup>\<omega> = bot"
  by (metis mult_left_zero omega_unfold)

lemma omega_one_greatest:
  "x \<le> 1\<^sup>\<omega>"
  by (simp add: omega_induct_mult)

lemma star_mult_omega:
  "x\<^sup>\<star> * x\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis order.antisym omega_unfold star.circ_loop_fixpoint star_left_induct_mult_equal sup.cobounded2)

lemma omega_sub_vector:
  "x\<^sup>\<omega> * y \<le> x\<^sup>\<omega>"
  by (metis mult_semi_associative omega_unfold omega_induct_mult)

lemma omega_simulation:
  "z * x \<le> y * z \<Longrightarrow> z * x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
  by (smt (verit, ccfv_threshold) mult_isotone omega_unfold order_lesseq_imp mult_assoc omega_induct_mult)

lemma omega_omega:
  "x\<^sup>\<omega>\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (metis omega_unfold omega_sub_vector)

lemma left_plus_omega:
  "(x * x\<^sup>\<star>)\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis order.antisym mult_assoc omega_induct_mult omega_unfold order_refl star.left_plus_circ star_mult_omega)

lemma omega_slide:
  "x * (y * x)\<^sup>\<omega> = (x * y)\<^sup>\<omega>"
  by (metis order.antisym mult_assoc mult_right_isotone omega_simulation omega_unfold order_refl)

lemma omega_simulation_2:
  "y * x \<le> x * y \<Longrightarrow> (x * y)\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (metis mult_right_isotone sup.absorb2 omega_induct_mult omega_slide omega_sub_dist)

lemma wagner:
  "(x \<squnion> y)\<^sup>\<omega> = x * (x \<squnion> y)\<^sup>\<omega> \<squnion> z \<Longrightarrow> (x \<squnion> y)\<^sup>\<omega> = x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z"
  by (smt (verit, ccfv_SIG) order.refl star_left_induct sup.absorb2 sup_assoc sup_commute omega_induct_equal omega_sub_dist)

lemma right_plus_omega:
  "(x\<^sup>\<star> * x)\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis left_plus_omega omega_slide star_mult_omega)

lemma omega_sub_dist_1:
  "(x * y\<^sup>\<star>)\<^sup>\<omega> \<le> (x \<squnion> y)\<^sup>\<omega>"
  by (metis left_plus_omega mult_isotone star.circ_sub_dist sup.cobounded1 sup_monoid.add_commute omega_isotone)

lemma omega_sub_dist_2:
  "(x\<^sup>\<star> * y)\<^sup>\<omega> \<le> (x \<squnion> y)\<^sup>\<omega>"
  by (metis mult_isotone star.circ_sub_dist sup.cobounded2 omega_isotone right_plus_omega)

lemma omega_star:
  "(x\<^sup>\<omega>)\<^sup>\<star> = 1 \<squnion> x\<^sup>\<omega>"
  by (metis antisym_conv star.circ_mult_increasing star_left_unfold_equal omega_sub_vector)

lemma omega_mult_omega_star:
  "x\<^sup>\<omega> * x\<^sup>\<omega>\<^sup>\<star> = x\<^sup>\<omega>"
  by (simp add: order.antisym star.circ_mult_increasing omega_sub_vector)

lemma omega_sum_unfold_1:
  "(x \<squnion> y)\<^sup>\<omega> = x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * (x \<squnion> y)\<^sup>\<omega>"
  by (metis mult_right_dist_sup omega_unfold mult_assoc wagner)

lemma omega_sum_unfold_2:
  "(x \<squnion> y)\<^sup>\<omega> \<le> (x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>"
  using omega_induct_equal omega_sum_unfold_1 by auto

lemma omega_sum_unfold_3:
  "(x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega> \<le> (x \<squnion> y)\<^sup>\<omega>"
  using star_left_induct_equal omega_sum_unfold_1 by auto

lemma omega_decompose:
  "(x \<squnion> y)\<^sup>\<omega> = (x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>"
  by (metis sup.absorb1 sup_same_context omega_sub_dist_2 omega_sum_unfold_2 omega_sum_unfold_3)

lemma omega_loop_fixpoint:
  "y * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<squnion> z = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z"
  apply (rule order.antisym)
  apply (smt (verit, ccfv_threshold) eq_refl mult_isotone mult_left_sub_dist_sup omega_induct omega_unfold star.circ_loop_fixpoint sup_assoc sup_commute sup_right_isotone)
  by (smt (z3) mult_left_sub_dist_sup omega_unfold star.circ_loop_fixpoint sup.left_commute sup_commute sup_right_isotone)

lemma omega_loop_greatest_fixpoint:
  "y * x \<squnion> z = x \<Longrightarrow> x \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z"
  by (simp add: sup_commute omega_induct_equal)

lemma omega_square:
  "x\<^sup>\<omega> = (x * x)\<^sup>\<omega>"
  using order.antisym omega_unfold order_refl mult_assoc omega_induct_mult omega_simulation_2 by auto

lemma mult_bot_omega:
  "(x * bot)\<^sup>\<omega> = x * bot"
  by (metis mult_left_zero omega_slide)

lemma mult_bot_add_omega:
  "(x \<squnion> y * bot)\<^sup>\<omega> = x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * bot"
  by (metis mult_left_zero sup_commute mult_assoc mult_bot_omega omega_decompose omega_loop_fixpoint)

lemma omega_mult_star:
  "x\<^sup>\<omega> * x\<^sup>\<star> = x\<^sup>\<omega>"
  by (meson antisym_conv star.circ_back_loop_prefixpoint sup.boundedE omega_sub_vector)

lemma omega_loop_is_greatest_fixpoint:
  "is_greatest_fixpoint (\<lambda>x . y * x \<squnion> z) (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z)"
  by (simp add: is_greatest_fixpoint_def omega_loop_fixpoint omega_loop_greatest_fixpoint)

lemma omega_loop_nu:
  "\<nu> (\<lambda>x . y * x \<squnion> z) = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z"
  by (metis greatest_fixpoint_same omega_loop_is_greatest_fixpoint)

lemma omega_loop_bot_is_greatest_fixpoint:
  "is_greatest_fixpoint (\<lambda>x . y * x) (y\<^sup>\<omega>)"
  using is_greatest_fixpoint_def omega_unfold omega_induct_mult by auto

lemma omega_loop_bot_nu:
  "\<nu> (\<lambda>x . y * x) = y\<^sup>\<omega>"
  by (metis greatest_fixpoint_same omega_loop_bot_is_greatest_fixpoint)

lemma affine_has_greatest_fixpoint:
  "has_greatest_fixpoint (\<lambda>x . y * x \<squnion> z)"
  using has_greatest_fixpoint_def omega_loop_is_greatest_fixpoint by blast

lemma omega_separate_unfold:
  "(x\<^sup>\<star> * y)\<^sup>\<omega> = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * (x\<^sup>\<star> * y)\<^sup>\<omega>"
  by (metis star.circ_loop_fixpoint sup_commute mult_assoc omega_slide omega_sum_unfold_1)

lemma omega_bot_left_slide:
  "(x * y)\<^sup>\<star> * ((x * y)\<^sup>\<omega> * bot \<squnion> 1) * x \<le> x * (y * x)\<^sup>\<star> * ((y * x)\<^sup>\<omega> * bot \<squnion> 1)"
proof -
  have "x \<squnion> x * (y * x) * (y * x)\<^sup>\<star> * ((y * x)\<^sup>\<omega> * bot \<squnion> 1) \<le> x * (y * x)\<^sup>\<star> * ((y * x)\<^sup>\<omega> * bot \<squnion> 1)"
    by (metis sup_commute mult_assoc mult_right_isotone star.circ_back_loop_prefixpoint star.mult_zero_sup_circ star.mult_zero_circ le_supE le_supI order.refl star.circ_increasing star.circ_mult_upper_bound)
  hence "((x * y)\<^sup>\<omega> * bot \<squnion> 1) * x \<squnion> x * y * (x * (y * x)\<^sup>\<star> * ((y * x)\<^sup>\<omega> * bot \<squnion> 1)) \<le> x * (y * x)\<^sup>\<star> * ((y * x)\<^sup>\<omega> * bot \<squnion> 1)"
    by (smt (z3) sup.absorb_iff2 sup_assoc mult_assoc mult_left_one mult_left_sub_dist_sup_left mult_left_zero mult_right_dist_sup omega_slide star_mult_omega)
  thus ?thesis
    by (simp add: star_left_induct mult_assoc)
qed

lemma omega_bot_add_1:
  "(x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1) = x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
proof (rule order.antisym)
  have 1: "(x \<squnion> y) * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1) \<le> x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    by (smt (z3) eq_refl star.circ_mult_upper_bound star.circ_sub_dist_1 star.mult_zero_circ star.mult_zero_sup_circ star_sup_1 sup_assoc sup_commute mult_assoc)
  have 2: "1 \<le> x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    using reflexive_mult_closed star.circ_reflexive sup_ge2 by auto
  have "(y * x\<^sup>\<star>)\<^sup>\<omega> * bot \<le> (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot"
    by (metis mult_1_right mult_left_isotone mult_left_sub_dist_sup_right omega_isotone)
  also have 3: "... \<le> (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    by (metis mult_isotone mult_left_one star.circ_reflexive sup_commute sup_ge2)
  finally have 4: "(x\<^sup>\<star> * y)\<^sup>\<omega> * bot \<le> x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    by (smt mult_assoc mult_right_isotone omega_slide)
  have "y * (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega> * bot \<le> y * (x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> y))\<^sup>\<star> * x\<^sup>\<star> * x\<^sup>\<omega> * bot * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot"
    using mult_isotone mult_left_sub_dist_sup_left mult_left_zero order.refl star_isotone sup_commute mult_assoc star_mult_omega by auto
  also have "... \<le> y * (x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> y))\<^sup>\<star> * (x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * y)\<^sup>\<omega> * bot"
    by (smt mult_assoc mult_left_isotone mult_left_sub_dist_sup_left omega_slide)
  also have "... = y * (x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * y)\<^sup>\<omega> * bot"
    using mult_left_one mult_left_zero mult_right_dist_sup mult_assoc star_mult_omega by auto
  finally have "x\<^sup>\<star> * y * (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega> * bot \<le> x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    using 3 by (smt mult_assoc mult_right_isotone omega_slide order_trans)
  hence "(x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega> * bot \<le> x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    by (smt (verit, ccfv_threshold) sup_assoc sup_commute le_iff_sup mult_assoc mult_isotone mult_left_one mult_1_right mult_right_sub_dist_sup_left order_trans star.circ_loop_fixpoint star.circ_reflexive star.mult_zero_circ)
  hence "(x \<squnion> y)\<^sup>\<omega> * bot \<le> x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    using 4 by (smt (z3) mult_right_dist_sup sup.orderE sup_assoc sup_right_divisibility omega_decompose)
  thus "(x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1) \<le> x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1)"
    using 1 2 star_left_induct mult_assoc by force
next
  have 5: "x\<^sup>\<omega> * bot \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    by (metis bot_least le_supI1 le_supI2 mult_isotone star.circ_loop_fixpoint sup.cobounded1 omega_isotone)
  have 6: "(y * x\<^sup>\<star>)\<^sup>\<omega> * bot \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    by (metis sup_commute mult_left_isotone omega_sub_dist_1 mult_assoc mult_left_sub_dist_sup_left order_trans star_mult_omega)
  have 7: "(y * x\<^sup>\<star>)\<^sup>\<star> \<le> (x \<squnion> y)\<^sup>\<star>"
    by (metis mult_left_one mult_right_sub_dist_sup_left star.circ_sup_1 star.circ_plus_one)
  hence "(y * x\<^sup>\<star>)\<^sup>\<star> * x\<^sup>\<omega> * bot \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    by (smt sup_assoc le_iff_sup mult_assoc mult_isotone mult_right_dist_sup omega_sub_dist)
  hence "(x\<^sup>\<omega> * bot \<squnion> y * x\<^sup>\<star>)\<^sup>\<omega> * bot \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    using 6 by (smt sup_commute sup.bounded_iff mult_assoc mult_right_dist_sup mult_bot_add_omega omega_unfold omega_bot)
  hence "(y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<le> y * x\<^sup>\<star> * (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    by (smt mult_assoc mult_left_one mult_left_zero mult_right_dist_sup mult_right_isotone omega_slide)
  also have "... \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    using 7 by (metis mult_left_isotone order_refl star.circ_mult_upper_bound star_left_induct_mult_iff)
  finally have "(y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1) \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    using 5 by (smt (z3) le_supE star.circ_mult_upper_bound star.circ_sub_dist_1 star.mult_zero_circ star.mult_zero_sup_circ star_involutive star_isotone sup_commute)
  hence "(x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1) \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    using 5 by (metis sup_commute mult_assoc star.circ_isotone star.circ_mult_upper_bound star.mult_zero_sup_circ star.mult_zero_circ star_involutive)
  thus "x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) * (y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<star> * ((y * x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))\<^sup>\<omega> * bot \<squnion> 1) \<le> (x \<squnion> y)\<^sup>\<star> * ((x \<squnion> y)\<^sup>\<omega> * bot \<squnion> 1)"
    by (smt sup_assoc sup_commute mult_assoc star.circ_mult_upper_bound star.circ_sub_dist star.mult_zero_sup_circ star.mult_zero_circ)
qed

lemma star_omega_greatest:
  "x\<^sup>\<star>\<^sup>\<omega> = 1\<^sup>\<omega>"
  by (metis sup_commute le_iff_sup omega_one_greatest omega_sub_dist star.circ_plus_one)

lemma omega_vector_greatest:
  "x\<^sup>\<omega> * 1\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis order.antisym mult_isotone omega_mult_omega_star omega_one_greatest omega_sub_vector)

lemma mult_greatest_omega:
  "(x * 1\<^sup>\<omega>)\<^sup>\<omega> \<le> x * 1\<^sup>\<omega>"
  by (metis mult_right_isotone omega_slide omega_sub_vector)

lemma omega_mult_star_2:
  "x\<^sup>\<omega> * y\<^sup>\<star> = x\<^sup>\<omega>"
  by (meson order.antisym le_supE star.circ_back_loop_prefixpoint omega_sub_vector)

lemma omega_import:
  assumes "p \<le> p * p"
      and "p * x \<le> x * p"
    shows "p * x\<^sup>\<omega> = p * (p * x)\<^sup>\<omega>"
proof -
  have "p * x\<^sup>\<omega> \<le> p * (p * x) * x\<^sup>\<omega>"
    by (metis assms(1) mult_assoc mult_left_isotone omega_unfold)
  also have "... \<le> p * x * p * x\<^sup>\<omega>"
    by (metis assms(2) mult_assoc mult_left_isotone mult_right_isotone)
  finally have "p * x\<^sup>\<omega> \<le> (p * x)\<^sup>\<omega>"
    by (simp add: mult_assoc omega_induct_mult)
  hence "p * x\<^sup>\<omega> \<le> p * (p * x)\<^sup>\<omega>"
    by (metis assms(1) mult_assoc mult_left_isotone mult_right_isotone order_trans)
  thus "p * x\<^sup>\<omega> = p * (p * x)\<^sup>\<omega>"
    by (metis assms(2) sup_left_divisibility order.antisym mult_right_isotone omega_induct_mult omega_slide omega_sub_dist)
qed

(*
lemma omega_circ_simulate_right_plus: "z * x \<le> y * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * z \<squnion> w \<longrightarrow> z * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) \<le> (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * (z \<squnion> w * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>))" nitpick [expect=genuine,card=4] oops
lemma omega_circ_simulate_left_plus: "x * z \<le> z * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) \<squnion> w \<longrightarrow> (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) * z \<le> (z \<squnion> (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) * w) * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>)" nitpick [expect=genuine,card=5] oops
*)

end

text \<open>Theorem 50.2\<close>

sublocale left_omega_algebra < comb0: left_conway_semiring where circ = "(\<lambda>x . x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))"
  apply unfold_locales
  apply (smt sup_assoc sup_commute le_iff_sup mult_assoc mult_left_sub_dist_sup_left omega_unfold star.circ_loop_fixpoint star_mult_omega)
  using omega_bot_left_slide mult_assoc apply fastforce
  using omega_bot_add_1 mult_assoc by simp

class left_zero_omega_algebra = left_zero_kleene_algebra + left_omega_algebra
begin

lemma star_omega_absorb:
  "y\<^sup>\<star> * (y\<^sup>\<star> * x)\<^sup>\<star> * y\<^sup>\<omega> = (y\<^sup>\<star> * x)\<^sup>\<star> * y\<^sup>\<omega>"
proof -
  have "y\<^sup>\<star> * (y\<^sup>\<star> * x)\<^sup>\<star> * y\<^sup>\<omega> = y\<^sup>\<star> * y\<^sup>\<star> * x * (y\<^sup>\<star> * x)\<^sup>\<star> * y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * y\<^sup>\<omega>"
    by (metis sup_commute mult_assoc mult_right_dist_sup star.circ_back_loop_fixpoint star.circ_plus_same)
  thus ?thesis
    by (metis mult_assoc star.circ_loop_fixpoint star.circ_transitive_equal star_mult_omega)
qed

lemma omega_circ_simulate_right_plus: 
  assumes "z * x \<le> y * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * z \<squnion> w"
    shows "z * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) \<le> (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * (z \<squnion> w * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>))"
proof -
  have 1: "z * x \<le> y\<^sup>\<omega> * bot \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    by (metis assms mult_assoc mult_left_dist_sup mult_left_zero mult_right_dist_sup omega_unfold)
  hence "(y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>) * x \<le> y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * (y\<^sup>\<omega> * bot \<squnion> y * y\<^sup>\<star> * z \<squnion> w) \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt sup_assoc sup_ge1 sup_ge2 le_iff_sup mult_assoc mult_left_dist_sup mult_left_zero mult_right_dist_sup star.circ_back_loop_fixpoint)
  also have "... = y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * y * y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt sup_assoc sup_ge2 le_iff_sup mult_assoc mult_left_dist_sup star.circ_back_loop_fixpoint star_mult_omega)
  also have "... \<le> y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt sup_commute sup_left_isotone mult_left_isotone star.circ_increasing star.circ_plus_same star.circ_transitive_equal)
  finally have "z \<squnion> (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>) * x \<le> y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (metis (no_types, lifting) le_supE le_supI star.circ_loop_fixpoint sup.cobounded1)
  hence 2: "z * x\<^sup>\<star> \<le> y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (simp add: star_right_induct)
  have "z * x\<^sup>\<omega> * bot \<le> (y\<^sup>\<omega> * bot \<squnion> y * y\<^sup>\<star> * z \<squnion> w) * x\<^sup>\<omega> * bot"
    using 1 by (smt sup_left_divisibility mult_assoc mult_right_sub_dist_sup_left omega_unfold)
  hence "z * x\<^sup>\<omega> * bot \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * (y\<^sup>\<omega> * bot \<squnion> w * x\<^sup>\<omega> * bot)"
    by (smt sup_assoc sup_commute left_plus_omega mult_assoc mult_left_zero mult_right_dist_sup omega_induct star.left_plus_circ)
  thus "z * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) \<le> (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * (z \<squnion> w * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>))"
    using 2 by (smt sup_assoc sup_commute le_iff_sup mult_assoc mult_left_dist_sup mult_left_zero mult_right_dist_sup omega_unfold omega_bot star_mult_omega zero_right_mult_decreasing)
qed

lemma omega_circ_simulate_left_plus:
  assumes "x * z \<le> z * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) \<squnion> w"
    shows "(x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) * z \<le> (z \<squnion> (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) * w) * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>)"
proof -
  have "x * (z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>) = x * z * y\<^sup>\<omega> * bot \<squnion> x * z * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x * x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x * x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt mult_assoc mult_left_dist_sup omega_unfold)
  also have "... \<le> x * z * y\<^sup>\<omega> * bot \<squnion> x * z * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (metis sup_mono sup_right_isotone mult_left_isotone star.left_plus_below_circ)
  also have "... \<le> (z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> \<squnion> w) * y\<^sup>\<omega> * bot \<squnion> (z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> \<squnion> w) * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (metis assms sup_left_isotone mult_assoc mult_left_dist_sup mult_left_isotone)
  also have "... = z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> * y\<^sup>\<omega> * bot \<squnion> w * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> * y\<^sup>\<star> \<squnion> w * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt sup_assoc mult_assoc mult_left_zero mult_right_dist_sup)
  also have "... = z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt (verit, ccfv_threshold) sup_assoc sup_commute sup_idem mult_assoc mult_right_dist_sup star.circ_loop_fixpoint star.circ_transitive_equal star_mult_omega)
  finally have "x\<^sup>\<star> * z \<le> z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt (z3) le_supE sup_least sup_ge1 star.circ_back_loop_fixpoint star_left_induct)
  hence "(x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) * z \<le> z * y\<^sup>\<omega> * bot \<squnion> z * y\<^sup>\<star> \<squnion> x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt (z3) sup.left_commute sup_commute sup_least sup_ge1 mult_assoc mult_left_zero mult_right_dist_sup)
  thus "(x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) * z \<le> (z \<squnion> (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) * w) * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>)"
    by (smt sup_assoc mult_assoc mult_left_dist_sup mult_left_zero mult_right_dist_sup)
qed

lemma omega_translate:
  "x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) = x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>"
  by (metis mult_assoc mult_left_dist_sup mult_1_right star_mult_omega)

lemma omega_circ_simulate_right:
  assumes "z * x \<le> y * z \<squnion> w"
    shows "z * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) \<le> (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * (z \<squnion> w * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>))"
proof -
  have "... \<le> y * (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * z \<squnion> w"
    using comb0.circ_mult_increasing mult_isotone sup_left_isotone omega_translate by auto
  thus "z * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>) \<le> (y\<^sup>\<omega> * bot \<squnion> y\<^sup>\<star>) * (z \<squnion> w * (x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>))"
    using assms order_trans omega_circ_simulate_right_plus by blast
qed

end

sublocale left_zero_omega_algebra < comb1: left_conway_semiring_1 where circ = "(\<lambda>x . x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))"
  apply unfold_locales
  by (smt order.eq_iff mult_assoc mult_left_dist_sup mult_left_zero mult_right_dist_sup mult_1_right omega_slide star_slide)

sublocale left_zero_omega_algebra < comb0: itering where circ = "(\<lambda>x . x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))"
  apply unfold_locales
  using comb1.circ_sup_9 apply blast
  using comb1.circ_mult_1 apply blast
  apply (metis omega_circ_simulate_right_plus omega_translate)
  using omega_circ_simulate_left_plus omega_translate by auto

text \<open>Theorem 2.2\<close>

sublocale left_zero_omega_algebra < comb2: itering where circ = "(\<lambda>x . x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star>)"
  apply unfold_locales
  using comb1.circ_sup_9 omega_translate apply force
  apply (metis comb1.circ_mult_1 omega_translate)
  using omega_circ_simulate_right_plus apply blast
  by (simp add: omega_circ_simulate_left_plus)

class omega_algebra = kleene_algebra + left_zero_omega_algebra

class left_omega_conway_semiring = left_omega_algebra + left_conway_semiring
begin

subclass left_kleene_conway_semiring ..

lemma circ_below_omega_star:
  "x\<^sup>\<circ> \<le> x\<^sup>\<omega> \<squnion> x\<^sup>\<star>"
  by (metis circ_left_unfold mult_1_right omega_induct order_refl)

lemma omega_mult_circ:
  "x\<^sup>\<omega> * x\<^sup>\<circ> = x\<^sup>\<omega>"
  by (metis circ_star omega_mult_star_2)

lemma circ_mult_omega:
  "x\<^sup>\<circ> * x\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis order.antisym sup_right_divisibility circ_loop_fixpoint circ_plus_sub omega_simulation)

lemma circ_omega_greatest:
  "x\<^sup>\<circ>\<^sup>\<omega> = 1\<^sup>\<omega>"
  by (metis circ_star star_omega_greatest)

lemma omega_circ:
  "x\<^sup>\<omega>\<^sup>\<circ> = 1 \<squnion> x\<^sup>\<omega>"
  by (metis order.antisym circ_left_unfold mult_left_sub_dist_sup_left mult_1_right omega_sub_vector)

end

class bounded_left_omega_algebra = bounded_left_kleene_algebra + left_omega_algebra
begin

lemma omega_one:
  "1\<^sup>\<omega> = top"
  by (simp add: order.antisym omega_one_greatest)

lemma star_omega_top:
  "x\<^sup>\<star>\<^sup>\<omega> = top"
  by (simp add: star_omega_greatest omega_one)

lemma omega_vector:
  "x\<^sup>\<omega> * top = x\<^sup>\<omega>"
  by (simp add: order.antisym omega_sub_vector top_right_mult_increasing)

lemma mult_top_omega:
  "(x * top)\<^sup>\<omega> \<le> x * top"
  using mult_greatest_omega omega_one by auto

end

sublocale bounded_left_omega_algebra < comb0: bounded_left_conway_semiring where circ = "(\<lambda>x . x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))" ..

class bounded_left_zero_omega_algebra = bounded_left_zero_kleene_algebra + left_zero_omega_algebra
begin

subclass bounded_left_omega_algebra ..

end

sublocale bounded_left_zero_omega_algebra < comb0: bounded_itering where circ = "(\<lambda>x . x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1))" ..

class bounded_omega_algebra = bounded_kleene_algebra + omega_algebra
begin

subclass bounded_left_zero_omega_algebra ..

end

class bounded_left_omega_conway_semiring = bounded_left_omega_algebra + left_omega_conway_semiring
begin

subclass left_kleene_conway_semiring ..

subclass bounded_left_conway_semiring ..

lemma circ_omega:
  "x\<^sup>\<circ>\<^sup>\<omega> = top"
  by (simp add: circ_omega_greatest omega_one)

end

class top_left_omega_algebra = bounded_left_omega_algebra +
  assumes top_left_bot: "top * x = top"
begin

lemma omega_translate_3:
  "x\<^sup>\<star> * (x\<^sup>\<omega> * bot \<squnion> 1) = x\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> 1)"
  by (metis omega_one omega_vector_greatest top_left_bot mult_assoc)

end

text \<open>Theorem 50.2\<close>

sublocale top_left_omega_algebra < comb4: left_conway_semiring where circ = "(\<lambda>x . x\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> 1))"
  apply unfold_locales
  using comb0.circ_left_unfold omega_translate_3 apply force
  using omega_bot_left_slide omega_translate_3 mult_assoc apply force
  using comb0.circ_sup_1 omega_translate_3 by auto

class top_left_bot_omega_algebra = bounded_left_zero_omega_algebra +
  assumes top_left_bot: "top * x = top"
begin

lemma omega_translate_2:
  "x\<^sup>\<omega> * bot \<squnion> x\<^sup>\<star> = x\<^sup>\<omega> \<squnion> x\<^sup>\<star>"
  by (metis mult_assoc omega_mult_star_2 star.circ_top top_left_bot)

end

text \<open>Theorem 2.3\<close>

sublocale top_left_bot_omega_algebra < comb3: itering where circ = "(\<lambda>x . x\<^sup>\<omega> \<squnion> x\<^sup>\<star>)"
  apply unfold_locales
  using comb2.circ_slide_1 comb2.circ_sup_1 omega_translate_2 apply force
  apply (metis comb2.circ_mult_1 omega_translate_2)
  using omega_circ_simulate_right_plus omega_translate_2 apply force
  using omega_circ_simulate_left_plus omega_translate_2 by auto

class Omega =
  fixes Omega :: "'a \<Rightarrow> 'a" ("_\<^sup>\<Omega>" [100] 100)

end

