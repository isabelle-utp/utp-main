(* Title:      Extended Designs
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Extended Designs\<close>

theory Extended_Designs

imports Omega_Algebras Domain

begin

class domain_semiring_L_below = left_zero_domain_semiring + L +
  assumes L_left_zero_below: "L * x \<le> L"
  assumes mult_L_split: "x * L = x * bot \<squnion> d(x) * L"
begin

lemma d_zero_mult_L:
  "d(x * bot) * L \<le> x"
  by (metis le_sup_iff mult_L_split mult_assoc mult_left_zero zero_right_mult_decreasing)

lemma mult_L:
  "x * L \<le> x * bot \<squnion> L"
  by (metis sup_right_isotone d_mult_below mult_L_split)

lemma d_mult_L:
  "d(x) * L \<le> x * L"
  by (metis sup_right_divisibility mult_L_split)

lemma d_L_split:
  "x * d(y) * L = x * bot \<squnion> d(x * y) * L"
  by (metis d_commutative d_mult_d d_zero mult_L_split mult_assoc mult_left_zero)

lemma d_mult_mult_L:
  "d(x * y) * L \<le> x * d(y) * L"
  using d_L_split by auto

lemma L_L:
  "L * L = L"
  by (metis d_restrict_equals le_iff_sup mult_L_split zero_right_mult_decreasing)

end

class antidomain_semiring_L = left_zero_antidomain_semiring + L +
  assumes d_zero_mult_L: "d(x * bot) * L \<le> x"
  assumes d_L_zero     : "d(L * bot) = 1"
  assumes mult_L       : "x * L \<le> x * bot \<squnion> L"
begin

lemma L_left_zero:
  "L * x = L"
  by (metis order.antisym d_L_zero d_zero_mult_L mult_assoc mult_left_one mult_left_zero zero_right_mult_decreasing)

subclass domain_semiring_L_below
  apply unfold_locales
  apply (simp add: L_left_zero)
  apply (rule order.antisym)
  apply (smt d_restrict_equals le_iff_sup mult_L mult_assoc mult_left_dist_sup)
  by (metis le_sup_iff d_L_zero d_mult_d d_zero_mult_L mult_assoc mult_right_isotone mult_1_right bot_least)

end

class ed_below = bounded_left_zero_omega_algebra + domain_semiring_L_below + Omega +
  assumes Omega_def: "x\<^sup>\<Omega> = d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star>"
begin

lemma Omega_isotone:
  "x \<le> y \<Longrightarrow> x\<^sup>\<Omega> \<le> y\<^sup>\<Omega>"
  by (metis Omega_def sup_mono d_isotone mult_left_isotone omega_isotone star.circ_isotone)

lemma star_below_Omega:
  "x\<^sup>\<star> \<le> x\<^sup>\<Omega>"
  using Omega_def by auto

lemma one_below_Omega:
  "1 \<le> x\<^sup>\<Omega>"
  using order_trans star.circ_reflexive star_below_Omega by blast

lemma L_left_zero_star:
  "L * x\<^sup>\<star> = L"
  by (meson L_left_zero_below order.antisym star.circ_back_loop_prefixpoint sup.boundedE)

lemma L_left_zero_Omega:
  "L * x\<^sup>\<Omega> = L"
  using L_left_zero_star L_left_zero_below Omega_def mult_left_dist_sup sup.order_iff sup_monoid.add_commute by auto

lemma mult_L_star:
  "(x * L)\<^sup>\<star> = 1 \<squnion> x * L"
  by (metis L_left_zero_star mult_assoc star.circ_left_unfold)

lemma mult_L_omega_below:
  "(x * L)\<^sup>\<omega> \<le> x * L"
  by (metis L_left_zero_below mult_right_isotone omega_slide)

lemma mult_L_sup_star:
  "(x * L \<squnion> y)\<^sup>\<star> = y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
  by (metis L_left_zero_star sup_commute mult_assoc star.circ_unfold_sum)

lemma mult_L_sup_omega_below:
  "(x * L \<squnion> y)\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
proof -
  have "(x * L \<squnion> y)\<^sup>\<omega> = (y\<^sup>\<star> * x * L)\<^sup>\<omega> \<squnion> (y\<^sup>\<star> * x * L)\<^sup>\<star> * y\<^sup>\<omega>"
    by (simp add: ils.il_inf_associative omega_decompose sup_commute)
  also have "... \<le> y\<^sup>\<star> * x * L \<squnion> (y\<^sup>\<star> * x * L)\<^sup>\<star> * y\<^sup>\<omega>"
    using sup_left_isotone mult_L_omega_below by auto
  also have "... = y\<^sup>\<star> * x * L \<squnion> y\<^sup>\<star> * x * L * y\<^sup>\<omega> \<squnion> y\<^sup>\<omega>"
    by (smt L_left_zero_star sup_assoc sup_commute mult_assoc star.circ_loop_fixpoint)
  also have "... \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
    by (metis L_left_zero_star sup_commute eq_refl mult_assoc star.circ_back_loop_fixpoint)
  finally show ?thesis
    .
qed

lemma mult_L_sup_circ:
  "(x * L \<squnion> y)\<^sup>\<Omega> = d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
proof -
  have "(x * L \<squnion> y)\<^sup>\<Omega> = d((x * L \<squnion> y)\<^sup>\<omega>) * L \<squnion> (x * L \<squnion> y)\<^sup>\<star>"
    by (simp add: Omega_def)
  also have "... \<le> d(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L) * L \<squnion> (x * L \<squnion> y)\<^sup>\<star>"
    by (metis sup_left_isotone d_isotone mult_L_sup_omega_below mult_left_isotone)
  also have "... = d(y\<^sup>\<omega>) * L \<squnion> d(y\<^sup>\<star> * x * L) * L \<squnion> (x * L \<squnion> y)\<^sup>\<star>"
    by (simp add: d_dist_sup mult_right_dist_sup)
  also have "... \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * x * L * L \<squnion> (x * L \<squnion> y)\<^sup>\<star>"
    by (meson d_mult_L order.refl sup.mono)
  also have "... = d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    by (smt L_L sup_assoc sup_commute le_iff_sup mult_L_sup_star mult_assoc order_refl)
  finally have 1: "(x * L \<squnion> y)\<^sup>\<Omega> \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    .
  have 2: "d(y\<^sup>\<omega>) * L \<le> (x * L \<squnion> y)\<^sup>\<Omega>"
    using Omega_isotone Omega_def by force
  have "y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L \<le> (x * L \<squnion> y)\<^sup>\<Omega>"
    by (metis Omega_def sup_ge2 mult_L_sup_star)
  hence "d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L \<le> (x * L \<squnion> y)\<^sup>\<Omega>"
    using 2 by simp
  thus ?thesis
    using 1 by (simp add: order.antisym)
qed

lemma circ_sup_d:
  "(x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega> = d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L)"
proof -
  have "(x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega> = ((d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star>) * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    by (simp add: Omega_def)
  also have "... = (d(x\<^sup>\<omega>) * L * y \<squnion> x\<^sup>\<star> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    by (simp add: mult_right_dist_sup)
  also have "... \<le> (d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    by (metis L_left_zero_below Omega_isotone sup_left_isotone mult_assoc mult_left_isotone mult_right_isotone)
  also have "... = (d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L) * x\<^sup>\<Omega>"
    by (simp add: mult_L_sup_circ)
  also have "... = d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L * x\<^sup>\<Omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<Omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L * x\<^sup>\<Omega>"
    using mult_right_dist_sup by auto
  also have "... = d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<Omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L"
    by (simp add: L_left_zero_Omega mult.assoc)
  also have "... = d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L)"
    by (simp add: Omega_def ils.il_inf_associative semiring.distrib_left sup_left_commute sup_monoid.add_commute)
  finally have 1: "(x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega> \<le> d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L)"
    .
  have "d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<le> (x\<^sup>\<Omega> * y)\<^sup>\<Omega>"
    using Omega_isotone Omega_def mult_left_isotone by auto
  also have "... \<le> (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    by (metis mult_right_isotone mult_1_right one_below_Omega)
  finally have 2: "d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<le> (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    .
  have 3: "(x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<le> (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    by (meson Omega_isotone order.trans mult_left_isotone mult_right_isotone star_below_Omega)
  have "(x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L \<le> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<Omega>"
    by (metis Omega_def sup_commute mult_assoc mult_left_sub_dist_sup_right)
  also have "... \<le> (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    using Omega_isotone Omega_def mult_left_isotone by force
  finally have "d((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * d(x\<^sup>\<omega>) * L) \<le> (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
    using 2 3 by (simp add: sup_assoc)
  thus ?thesis
    using 1 by (simp add: order.antisym)
qed

(*
lemma mult_L_omega: "(x * L)\<^sup>\<omega> = x * L" nitpick [expect=genuine,card=5] oops
lemma mult_L_sup_omega: "(x * L \<squnion> y)\<^sup>\<omega> = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L" nitpick [expect=genuine,card=5] oops
lemma d_Omega_circ_simulate_right_plus: "z * x \<le> y * y\<^sup>\<Omega> * z \<squnion> w \<Longrightarrow> z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)" nitpick [expect=genuine,card=4] oops
lemma d_Omega_circ_simulate_left_plus: "x * z \<le> z * y\<^sup>\<Omega> \<squnion> w \<Longrightarrow> x\<^sup>\<Omega> * z \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>" nitpick [expect=genuine,card=3] oops
*)

end

class ed = ed_below +
  assumes L_left_zero: "L * x = L"
begin

lemma mult_L_omega:
  "(x * L)\<^sup>\<omega> = x * L"
  by (metis L_left_zero omega_slide)

lemma mult_L_sup_omega:
  "(x * L \<squnion> y)\<^sup>\<omega> = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
  by (metis L_left_zero ils.il_inf_associative mult_bot_add_omega sup_commute)

lemma d_Omega_circ_simulate_right_plus:
  assumes "z * x \<le> y * y\<^sup>\<Omega> * z \<squnion> w"
    shows "z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)"
proof -
  have "z * x \<le> y * d(y\<^sup>\<omega>) * L * z \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    using assms Omega_def ils.il_inf_associative mult_right_dist_sup semiring.distrib_left by auto
  also have "... \<le> y * d(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    by (metis L_left_zero_below sup_commute sup_right_isotone mult_assoc mult_right_isotone)
  also have "... = y * bot \<squnion> d(y * y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    by (simp add: d_L_split)
  also have "... = d(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    by (smt sup_assoc sup_commute sup_bot_left mult_assoc mult_left_dist_sup omega_unfold)
  finally have 1: "z * x \<le> d(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    .
  have "(d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>) * x = d(y\<^sup>\<omega>) * L * x \<squnion> y\<^sup>\<star> * z * x \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L * x \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star> * x"
    using mult_right_dist_sup by fastforce
  also have "... \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z * x \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L * x \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star> * x"
    by (metis L_left_zero_below sup_left_isotone mult_assoc mult_right_isotone)
  also have "... \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z * x \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star> * x"
    by (metis L_left_zero_below sup_commute sup_left_isotone mult_assoc mult_right_isotone)
  also have "... \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z * x \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (meson star.circ_back_loop_prefixpoint sup.boundedE sup_right_isotone)
  also have "... \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * (d(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w) \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    using 1 by (smt sup_left_isotone sup_right_isotone le_iff_sup mult_assoc mult_left_dist_sup)
  also have "... = d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * y * y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt sup_assoc sup_commute sup_idem mult_assoc mult_left_dist_sup d_L_split star.circ_back_loop_fixpoint star_mult_omega)
  also have "... \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    using mult_isotone order_refl semiring.add_right_mono star.circ_mult_upper_bound star.right_plus_below_circ sup_right_isotone by auto
  finally have 2: "z * x\<^sup>\<star> \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt le_sup_iff sup_ge1 star.circ_loop_fixpoint star_right_induct)
  have "z * x * x\<^sup>\<omega> \<le> y * y\<^sup>\<star> * z * x\<^sup>\<omega> \<squnion> d(y\<^sup>\<omega>) * L * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<omega>"
    using 1 by (metis sup_commute mult_left_isotone mult_right_dist_sup)
  also have "... \<le> y * y\<^sup>\<star> * z * x\<^sup>\<omega> \<squnion> d(y\<^sup>\<omega>) * L \<squnion> w * x\<^sup>\<omega>"
    by (metis L_left_zero eq_refl ils.il_inf_associative)
  finally have "z * x\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>"
    by (smt sup_assoc sup_commute left_plus_omega mult_assoc mult_left_dist_sup omega_induct omega_unfold star.left_plus_circ)
  hence "z * x\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>"
    by (metis sup_commute d_mult_L le_iff_sup mult_assoc mult_right_isotone omega_sub_vector order_trans star_mult_omega)
  hence "d(z * x\<^sup>\<omega>) * L \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L"
    by (smt sup_assoc sup_commute d_L_split d_dist_sup le_iff_sup mult_right_dist_sup)
  hence "z * d(x\<^sup>\<omega>) * L \<le> z * bot \<squnion> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L"
    using d_L_split sup_assoc sup_right_isotone by force
  also have "... \<le> y\<^sup>\<star> * z \<squnion> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L"
    by (smt sup_commute sup_left_isotone sup_ge1 order_trans star.circ_loop_fixpoint zero_right_mult_decreasing)
  finally have "z * d(x\<^sup>\<omega>) * L \<le> d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * d(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (simp add: le_supI2 sup_commute)
  thus ?thesis
    using 2 by (smt L_left_zero Omega_def sup_assoc le_iff_sup mult_assoc mult_left_dist_sup mult_right_dist_sup)
qed

lemma d_Omega_circ_simulate_left_plus:
  assumes "x * z \<le> z * y\<^sup>\<Omega> \<squnion> w"
    shows "x\<^sup>\<Omega> * z \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
proof -
  have "x * (z * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * d(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>) = x * z * d(y\<^sup>\<omega>) * L \<squnion> x * z * y\<^sup>\<star> \<squnion> d(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * w * d(y\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt sup_assoc sup_commute mult_assoc mult_left_dist_sup d_L_split omega_unfold)
  also have "... \<le> (z * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w) * d(y\<^sup>\<omega>) * L \<squnion> (z * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w) * y\<^sup>\<star> \<squnion> d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * d(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt assms Omega_def sup_assoc sup_ge2 le_iff_sup mult_assoc mult_left_dist_sup mult_right_dist_sup star.circ_loop_fixpoint)
  also have "... = z * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> * d(y\<^sup>\<omega>) * L \<squnion> w * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w * y\<^sup>\<star> \<squnion> d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * d(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt L_left_zero sup_assoc sup_commute sup_idem mult_assoc mult_right_dist_sup star.circ_transitive_equal)
  also have "... = z * d(y\<^sup>\<omega>) * L \<squnion> w * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w * y\<^sup>\<star> \<squnion> d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * d(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt sup_assoc sup_commute sup_idem le_iff_sup mult_assoc d_L_split star_mult_omega zero_right_mult_decreasing)
  finally have "x * (z * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * d(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>) \<le> z * d(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> d(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * d(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt sup_assoc sup_commute sup_idem mult_assoc star.circ_loop_fixpoint)
  thus ?thesis
    by (smt (verit, del_insts) L_left_zero Omega_def sup_assoc le_sup_iff sup_ge1 mult_assoc mult_left_dist_sup mult_right_dist_sup star.circ_back_loop_fixpoint star_left_induct)
qed

end

text \<open>Theorem 2.5 and Theorem 50.4\<close>

sublocale ed < ed_omega: itering where circ = Omega
  apply unfold_locales
  apply (smt sup_assoc sup_commute sup_bot_left circ_sup_d Omega_def mult_left_dist_sup mult_right_dist_sup d_L_split d_dist_sup omega_decompose star.circ_sup_1 star.circ_slide)
  apply (smt L_left_zero sup_assoc sup_commute sup_bot_left Omega_def mult_assoc mult_left_dist_sup mult_right_dist_sup d_L_split omega_slide star.circ_mult)
  using d_Omega_circ_simulate_right_plus apply blast
  by (simp add: d_Omega_circ_simulate_left_plus)

sublocale ed < ed_star: itering where circ = star ..

class ed_2 = ed_below + antidomain_semiring_L + Omega
begin

subclass ed
  apply unfold_locales
  by (rule L_left_zero)

end

end

