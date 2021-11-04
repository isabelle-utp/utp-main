(* Title:      Domain Iterings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Domain Iterings\<close>

theory Domain_Iterings

imports Domain Lattice_Ordered_Semirings Omega_Algebras

begin

class domain_semiring_lattice = left_zero_domain_semiring + lattice_ordered_pre_left_semiring
begin

subclass bounded_idempotent_left_zero_semiring ..

lemma d_top:
  "d(top) = 1"
  by (metis sup_left_top d_dist_sup d_one d_plus_one)

lemma mult_domain_top:
  "x * d(y) * top \<le> d(x * y) * top"
  by (smt d_mult_d d_restrict_equals mult_assoc mult_right_isotone top_greatest)

lemma domain_meet_domain:
  "d(x \<sqinter> d(y) * z) \<le> d(y)"
  by (metis d_export d_isotone d_mult_greatest_lower_bound inf.cobounded2)

lemma meet_domain:
  "x \<sqinter> d(y) * z = d(y) * (x \<sqinter> z)"
  apply (rule order.antisym)
  apply (metis domain_meet_domain d_mult_below d_restrict_equals inf_mono mult_isotone)
  by (meson d_mult_below le_inf_iff mult_left_sub_dist_inf_right)

lemma meet_intro_domain:
  "x \<sqinter> y = d(y) * x \<sqinter> y"
  by (metis d_restrict_equals inf_commute meet_domain)

lemma meet_domain_top:
  "x \<sqinter> d(y) * top = d(y) * x"
  by (simp add: meet_domain)

(*
lemma "d(x) = x * top \<sqinter> 1" nitpick [expect=genuine,card=3] oops
*)

lemma d_galois:
  "d(x) \<le> d(y) \<longleftrightarrow> x \<le> d(y) * top"
  by (metis d_export d_isotone d_mult_left_absorb_sup d_plus_one d_restrict_equals d_top mult_isotone top.extremum)

lemma vector_meet:
  "x * top \<sqinter> y \<le> d(x) * y"
  by (metis d_galois d_mult_sub inf.sup_monoid.add_commute inf.sup_right_isotone meet_domain_top)

end

class domain_semiring_lattice_L = domain_semiring_lattice + L +
  assumes l1: "x * L = x * bot \<squnion> d(x) * L"
  assumes l2: "d(L) * x \<le> x * d(L)"
  assumes l3: "d(L) * top \<le> L \<squnion> d(L * bot) * top"
  assumes l4: "L * top \<le> L"
  assumes l5: "x * bot \<sqinter> L \<le> (x \<sqinter> L) * bot"
begin

lemma l8:
  "(x \<sqinter> L) * bot \<le> x * bot \<sqinter> L"
  by (meson inf.boundedE inf.boundedI mult_right_sub_dist_inf_left zero_right_mult_decreasing)

lemma l9:
  "x * bot \<sqinter> L \<le> d(x * bot) * L"
  by (metis vector_meet vector_mult_closed zero_vector)

lemma l10:
  "L * L = L"
  by (metis d_restrict_equals l1 le_iff_sup zero_right_mult_decreasing)

lemma l11:
  "d(x) * L \<le> x * L"
  by (metis l1 sup.cobounded2)

lemma l12:
  "d(x * bot) * L \<le> x * bot"
  by (metis sup_right_divisibility l1 mult_assoc mult_left_zero)

lemma l13:
  "d(x * bot) * L \<le> x"
  using l12 order_trans zero_right_mult_decreasing by blast

lemma l14:
  "x * L \<le> x * bot \<squnion> L"
  by (metis d_mult_below l1 sup_right_isotone)

lemma l15:
  "x * d(y) * L = x * bot \<squnion> d(x * y) * L"
  by (metis d_commutative d_mult_d d_zero l1 mult_assoc mult_left_zero)

lemma l16:
  "x * top \<sqinter> L \<le> x * L"
  using inf.order_lesseq_imp l11 vector_meet by blast

lemma l17:
  "d(x) * L \<le> d(x * L) * L"
  by (metis d_mult_below l11 le_infE le_infI meet_intro_domain)

lemma l18:
  "d(x) * L = d(x * L) * L"
  by (simp add: order.antisym d_mult_sub l17 mult_left_isotone)

lemma l19:
  "d(x * top * bot) * L \<le> d(x * L) * L"
  by (metis d_mult_sub l18 mult_assoc mult_left_isotone)

lemma l20:
  "x \<le> y \<longleftrightarrow> x \<le> y \<squnion> L \<and> x \<le> y \<squnion> d(y * bot) * top"
  apply (rule iffI)
  apply (simp add: le_supI1)
  by (smt sup_commute sup_inf_distrib1 l13 le_iff_sup meet_domain_top)

lemma l21:
  "d(x * bot) * L \<le> x * bot \<sqinter> L"
  by (simp add: d_mult_below l12)

lemma l22:
  "x * bot \<sqinter> L = d(x * bot) * L"
  using l21 order.antisym l9 by auto

lemma l23:
  "x * top \<sqinter> L = d(x) * L"
  apply (rule order.antisym)
  apply (simp add: vector_meet)
  by (metis d_mult_below inf.le_sup_iff inf_top.left_neutral l1 le_supE mult_left_sub_dist_inf_left)

lemma l29:
  "L * d(L) = L"
  by (metis d_preserves_equation d_restrict_equals l2)

lemma l30:
  "d(L) * x \<le> (x \<sqinter> L) \<squnion> d(L * bot) * x"
  by (metis inf.sup_right_divisibility inf_left_commute inf_sup_distrib1 l3 meet_domain_top)

lemma l31:
  "d(L) * x = (x \<sqinter> L) \<squnion> d(L * bot) * x"
  by (smt (z3) l30 d_dist_sup le_iff_sup meet_intro_domain semiring.combine_common_factor sup_commute sup_inf_absorb zero_right_mult_decreasing)

lemma l40:
  "L * x \<le> L"
  by (meson bot_least inf.order_trans l4 semiring.mult_left_mono top.extremum)

lemma l41:
  "L * top = L"
  by (simp add: l40 order.antisym top_right_mult_increasing)

lemma l50:
  "x * bot \<sqinter> L = (x \<sqinter> L) * bot"
  using order.antisym l5 l8 by force

lemma l51:
  "d(x * bot) * L = (x \<sqinter> L) * bot"
  using l22 l50 by auto

lemma l90:
  "L * top * L = L"
  by (simp add: l41 l10)

lemma l91:
  assumes "x = x * top"
    shows "d(L * bot) * x \<le> d(x * bot) * top"
proof -
  have "d(L * bot) * x \<le> d(d(L * bot) * x) * top"
    using d_galois by blast
  also have "... = d(d(L * bot) * d(x)) * top"
    using d_mult_d by auto
  also have "... = d(d(x) * L * bot) * top"
    using d_commutative d_mult_d ils.il_inf_associative by auto
  also have "... \<le> d(x * L * bot) * top"
    by (metis d_isotone l11 mult_left_isotone)
  also have "... \<le> d(x * top * bot) * top"
    by (simp add: d_isotone mult_left_isotone mult_right_isotone)
  finally show ?thesis
    using assms by auto
qed

lemma l92:
  assumes "x = x * top"
    shows "d(L * bot) * x \<le> d((x \<sqinter> L) * bot) * top"
proof -
  have "d(L * bot) * x = d(L) * d(L * bot) * x"
    using d_commutative d_mult_sub d_order by auto
  also have "... \<le> d(L) * d(x * bot) * top"
    by (metis assms order.eq_iff l91 mult_assoc mult_isotone)
  also have "... = d(d(x * bot) * L) * top"
    by (simp add: d_commutative d_export)
  also have "... \<le> d((x \<sqinter> L) * bot) * top"
    by (simp add: l51)
  finally show ?thesis
    .
qed

end

class domain_itering_lattice_L = bounded_itering + domain_semiring_lattice_L
begin

lemma mult_L_circ:
  "(x * L)\<^sup>\<circ> = 1 \<squnion> x * L"
  by (metis circ_back_loop_fixpoint circ_mult l40 le_iff_sup mult_assoc)

lemma mult_L_circ_mult_below:
  "(x * L)\<^sup>\<circ> * y \<le> y \<squnion> x * L"
  by (smt sup_right_isotone l40 mult_L_circ mult_assoc mult_left_one mult_right_dist_sup mult_right_isotone)

lemma circ_L:
  "L\<^sup>\<circ> = L \<squnion> 1"
  by (metis sup_commute l10 mult_L_circ)

lemma circ_d0_L:
  "x\<^sup>\<circ> * d(x * bot) * L = x\<^sup>\<circ> * bot"
  by (metis sup_bot_right circ_loop_fixpoint circ_plus_same d_zero l15 mult_assoc mult_left_zero)

lemma d0_circ_left_unfold:
  "d(x\<^sup>\<circ> * bot) = d(x * x\<^sup>\<circ> * bot)"
  by (metis sup_commute sup_bot_left circ_loop_fixpoint mult_assoc)

lemma d_circ_import:
  "d(y) * x \<le> x * d(y) \<Longrightarrow> d(y) * x\<^sup>\<circ> = d(y) * (d(y) * x)\<^sup>\<circ>"
  apply (rule order.antisym)
  apply (simp add: circ_import d_idempotent d_plus_one le_iff_sup)
  using circ_isotone d_mult_below mult_right_isotone by auto

end

class domain_omega_algebra_lattice_L = bounded_left_zero_omega_algebra + domain_semiring_lattice_L
begin

lemma mult_L_star:
  "(x * L)\<^sup>\<star> = 1 \<squnion> x * L"
  by (metis l40 le_iff_sup mult_assoc star.circ_back_loop_fixpoint star.circ_mult)

lemma mult_L_omega:
  "(x * L)\<^sup>\<omega> \<le> x * L"
  by (metis l40 mult_right_isotone omega_slide)

lemma mult_L_sup_star:
  "(x * L \<squnion> y)\<^sup>\<star> = y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
proof (rule order.antisym)
  have "(x * L \<squnion> y) * (y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L) = x * L * (y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L) \<squnion> y * (y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L)"
    by (simp add: mult_right_dist_sup)
  also have "... \<le> x * L \<squnion> y * (y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L)"
    by (metis sup_left_isotone l40 mult_assoc mult_right_isotone)
  also have "... \<le> x * L \<squnion> y * y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    by (smt sup_assoc sup_commute sup_ge2 mult_assoc mult_left_dist_sup star.circ_loop_fixpoint)
  also have "... \<le> x * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    by (meson order_refl star.left_plus_below_circ sup_mono)
  also have "... = y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    by (metis sup_assoc sup_commute mult_assoc star.circ_loop_fixpoint star.circ_reflexive star.circ_sup_one_right_unfold star_involutive)
  finally have "1 \<squnion> (x * L \<squnion> y) * (y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L) \<le> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    by (meson le_supI le_supI1 star.circ_reflexive)
  thus "(x * L \<squnion> y)\<^sup>\<star> \<le> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
    using star_left_induct by fastforce
next
  show "y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L \<le> (x * L \<squnion> y)\<^sup>\<star>"
    by (metis sup_commute le_sup_iff mult_assoc star.circ_increasing star.circ_mult_upper_bound star.circ_sub_dist)
qed

lemma mult_L_sup_omega:
  "(x * L \<squnion> y)\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
proof -
  have 1: "(y\<^sup>\<star> * x * L)\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
    by (simp add: le_supI2 mult_L_omega)
  have "(y\<^sup>\<star> * x * L)\<^sup>\<star> * y\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
    by (metis sup_right_isotone l40 mult_assoc mult_right_isotone star_left_induct)
  thus ?thesis
    using 1 by (simp add: ils.il_inf_associative omega_decompose sup_monoid.add_commute)
qed

end

sublocale domain_omega_algebra_lattice_L < dL_star: itering where circ = star ..

sublocale domain_omega_algebra_lattice_L < dL_star: domain_itering_lattice_L where circ = star ..

context domain_omega_algebra_lattice_L
begin

lemma d0_star_below_d0_omega:
  "d(x\<^sup>\<star> * bot) \<le> d(x\<^sup>\<omega> * bot)"
  by (simp add: d_isotone star_bot_below_omega_bot)

lemma d0_below_d0_omega:
  "d(x * bot) \<le> d(x\<^sup>\<omega> * bot)"
  by (metis d0_star_below_d0_omega d_isotone mult_left_isotone order_trans star.circ_increasing)

lemma star_L_split:
  assumes "y \<le> z"
      and "x * z * L \<le> x * bot \<squnion> z * L"
    shows "x\<^sup>\<star> * y * L \<le> x\<^sup>\<star> * bot \<squnion> z * L"
proof -
  have "x * (x\<^sup>\<star> * bot \<squnion> z * L) \<le> x\<^sup>\<star> * bot \<squnion> x * z * L"
    by (metis sup_bot_right order.eq_iff mult_assoc mult_left_dist_sup star.circ_loop_fixpoint)
  also have "... \<le> x\<^sup>\<star> * bot \<squnion> x * bot \<squnion> z * L"
    using assms(2) semiring.add_left_mono sup_monoid.add_assoc by auto
  also have "... = x\<^sup>\<star> * bot \<squnion> z * L"
    using mult_isotone star.circ_increasing sup.absorb_iff1 by force
  finally have "y * L \<squnion> x * (x\<^sup>\<star> * bot \<squnion> z * L) \<le> x\<^sup>\<star> * bot \<squnion> z * L"
    by (simp add: assms(1) le_supI1 mult_left_isotone sup_monoid.add_commute)
  thus ?thesis
    by (simp add: star_left_induct mult.assoc)
qed

lemma star_L_split_same:
  "x * y * L \<le> x * bot \<squnion> y * L \<Longrightarrow> x\<^sup>\<star> * y * L = x\<^sup>\<star> * bot \<squnion> y * L"
  apply (rule order.antisym)
  using star_L_split apply blast
  by (metis bot_least ils.il_inf_associative le_supI mult_isotone mult_left_one order_refl star.circ_reflexive)

lemma star_d_L_split_equal:
  "d(x * y) \<le> d(y) \<Longrightarrow> x\<^sup>\<star> * d(y) * L = x\<^sup>\<star> * bot \<squnion> d(y) * L"
  by (metis sup_right_isotone l15 le_iff_sup mult_right_sub_dist_sup_left star_L_split_same)

lemma d0_omega_mult:
  "d(x\<^sup>\<omega> * y * bot) = d(x\<^sup>\<omega> * bot)"
  apply (rule order.antisym)
  apply (simp add: d_isotone mult_isotone omega_sub_vector)
  by (metis d_isotone mult_assoc mult_right_isotone bot_least)

lemma d_omega_export:
  "d(y) * x \<le> x * d(y) \<Longrightarrow> d(y) * x\<^sup>\<omega> = (d(y) * x)\<^sup>\<omega>"
  apply (rule order.antisym)
  apply (simp add: d_preserves_equation omega_simulation)
  by (smt le_iff_sup mult_left_dist_sup omega_simulation_2 omega_slide)

lemma d_omega_import:
  "d(y) * x \<le> x * d(y) \<Longrightarrow> d(y) * x\<^sup>\<omega> = d(y) * (d(y) * x)\<^sup>\<omega>"
  using d_idempotent omega_import order.refl by auto

lemma star_d_omega_top:
  "x\<^sup>\<star> * d(x\<^sup>\<omega>) * top = x\<^sup>\<star> * bot \<squnion> d(x\<^sup>\<omega>) * top"
  apply (rule order.antisym)
  apply (metis le_supI2 mult_domain_top star_mult_omega)
  by (metis ils.il_inf_associative le_supI mult_left_one mult_left_sub_dist_sup_right mult_right_sub_dist_sup_left star.circ_right_unfold_1 sup_monoid.add_0_right)

lemma omega_meet_L:
  "x\<^sup>\<omega> \<sqinter> L = d(x\<^sup>\<omega>) * L"
  by (metis l23 omega_vector)

(*
lemma d_star_mult: "d(x * y) \<le> d(y) \<Longrightarrow> d(x\<^sup>\<star> * y) = d(x\<^sup>\<star> * bot) \<squnion> d(y)" oops
lemma d0_split_omega_omega: "x\<^sup>\<omega> \<le> x\<^sup>\<omega> * bot \<squnion> d(x\<^sup>\<omega> \<sqinter> L) * top" nitpick [expect=genuine,card=2] oops
*)

end

end

