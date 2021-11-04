(* Title:      Nonstrict Binary Iterings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Nonstrict Binary Iterings\<close>

theory Binary_Iterings_Nonstrict

imports Omega_Algebras Binary_Iterings

begin

class nonstrict_itering = bounded_left_zero_omega_algebra + while +
  assumes while_def: "x \<star> y = x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y"
begin

text \<open>Theorem 8.2\<close>

subclass bounded_binary_itering
proof (unfold_locales)
  fix x y z
  show "(x * y) \<star> z = z \<squnion> x * ((y * x) \<star> (y * z))"
    by (metis sup_commute mult_assoc mult_left_dist_sup omega_loop_fixpoint omega_slide star.circ_slide while_def)
next
  fix x y z
  show "(x \<squnion> y) \<star> z = (x \<star> y) \<star> (x \<star> z)"
  proof -
    have 1: "(x \<squnion> y) \<star> z = (x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z)"
      using mult_left_dist_sup omega_decompose star.circ_sup_9 sup_assoc while_def mult_assoc by auto
    hence 2: "(x \<squnion> y) \<star> z \<le> (x \<star> y) \<star> (x \<star> z)"
      by (smt sup_mono sup_ge2 le_iff_sup mult_left_isotone omega_sub_dist star.circ_sub_dist while_def)
    let ?rhs = "x\<^sup>\<star> * y * ((x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z)) \<squnion> (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z)"
    have "x\<^sup>\<omega> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega> \<le> x\<^sup>\<omega>"
      by (simp add: omega_sub_vector)
    hence "x\<^sup>\<omega> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega> \<le> ?rhs"
      by (smt sup_commute sup_mono sup_ge1 mult_left_dist_sup order_trans)
    hence 3: "(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega> \<le> ?rhs"
      by (metis mult_right_dist_sup omega_unfold)
    have "x\<^sup>\<omega> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<le> x\<^sup>\<omega>"
      by (simp add: omega_mult_star_2 omega_sub_vector)
    hence "x\<^sup>\<omega> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<squnion> x\<^sup>\<star> * y * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<le> ?rhs"
      by (smt sup_commute sup_mono sup_ge2 mult_assoc mult_left_dist_sup order_trans)
    hence "(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<le> ?rhs"
      by (smt sup_assoc sup_ge2 le_iff_sup mult_assoc mult_right_dist_sup star.circ_loop_fixpoint)
    hence "(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<le> ?rhs"
      using 3 by simp
    hence "(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<le> (x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z)"
      by (metis sup_commute omega_induct)
    thus ?thesis
      using 1 2 order.antisym while_def by force
  qed
next
  fix x y z
  show "x \<star> (y \<squnion> z) = (x \<star> y) \<squnion> (x \<star> z)"
    using mult_left_dist_sup sup_assoc sup_commute while_def by auto
next
  fix x y z
  show "(x \<star> y) * z \<le> x \<star> (y * z)"
    using mult_semi_associative omega_sub_vector semiring.add_mono semiring.distrib_right while_def by fastforce
next
  fix v w x y z
  show "x * z \<le> z * (y \<star> 1) \<squnion> w \<longrightarrow> x \<star> (z * v) \<le> z * (y \<star> v) \<squnion> (x \<star> (w * (y \<star> v)))"
  proof
    assume "x * z \<le> z * (y \<star> 1) \<squnion> w"
    hence 1: "x * z \<le> z * y\<^sup>\<omega> \<squnion> z * y\<^sup>\<star> \<squnion> w"
      by (metis mult_left_dist_sup mult_1_right while_def)
    let ?rhs = "z * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v) \<squnion> x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * w * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v)"
    have 2: "z * v \<le> ?rhs"
      by (metis le_supI1 mult_left_sub_dist_sup_right omega_loop_fixpoint)
    have "x * z * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v) \<le> ?rhs"
    proof -
      have "x * z * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v) \<le> (z * y\<^sup>\<omega> \<squnion> z * y\<^sup>\<star> \<squnion> w) * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v)"
        using 1 mult_left_isotone by auto
      also have "... = z * (y\<^sup>\<omega> * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v) \<squnion> y\<^sup>\<star> * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v)) \<squnion> w * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v)"
        by (smt mult_assoc mult_left_dist_sup mult_right_dist_sup)
      also have "... = z * (y\<^sup>\<omega> * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v) \<squnion> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v) \<squnion> w * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v)"
        by (smt sup_assoc mult_assoc mult_left_dist_sup star.circ_transitive_equal star_mult_omega)
      also have "... \<le> z * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v) \<squnion> x\<^sup>\<star> * w * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * v)"
        by (smt sup_commute sup_mono sup_left_top mult_left_dist_sup mult_left_one mult_right_dist_sup mult_right_sub_dist_sup_left omega_vector order_refl star.circ_plus_one)
      finally show ?thesis
        by (smt sup_assoc sup_commute le_iff_sup)
    qed
    hence "x * ?rhs \<le> ?rhs"
      by (smt sup_assoc sup_commute sup_ge1 le_iff_sup mult_assoc mult_left_dist_sup mult_right_dist_sup omega_unfold star.circ_increasing star.circ_transitive_equal)
    hence "z * v \<squnion> x * ?rhs \<le> ?rhs"
      using 2 le_supI by blast
    hence "x\<^sup>\<star> * z * v \<le> ?rhs"
      by (simp add: star_left_induct mult_assoc)
    hence "x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z * v \<le> ?rhs"
      by (meson order_trans sup_ge1 sup_ge2 sup_least)
    thus "x \<star> (z * v) \<le> z * (y \<star> v) \<squnion> (x \<star> (w * (y \<star> v)))"
      by (simp add: sup_assoc while_def mult_assoc)
  qed
next
  fix v w x y z
  show "z * x \<le> y * (y \<star> z) \<squnion> w \<longrightarrow> z * (x \<star> v) \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
  proof
    assume "z * x \<le> y * (y \<star> z) \<squnion> w"
    hence "z * x \<le> y * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<squnion> w"
      by (simp add: while_def)
    hence 1: "z * x \<le> y\<^sup>\<omega> \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
      using mult_left_dist_sup omega_unfold mult_assoc by auto
    let ?rhs = "y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z * v \<squnion> y\<^sup>\<star> * w * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * v)"
    have 2: "z * x\<^sup>\<omega> \<le> ?rhs"
    proof -
      have "z * x\<^sup>\<omega> \<le> y * y\<^sup>\<star> * z * x\<^sup>\<omega> \<squnion> y\<^sup>\<omega> * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<omega>"
        using 1 by (smt sup_commute le_iff_sup mult_assoc mult_right_dist_sup omega_unfold)
      also have "... \<le> y * y\<^sup>\<star> * z * x\<^sup>\<omega> \<squnion> y\<^sup>\<omega> \<squnion> w * x\<^sup>\<omega>"
        using omega_sub_vector semiring.add_mono by blast
      also have "... = y * y\<^sup>\<star> * (z * x\<^sup>\<omega>) \<squnion> (y\<^sup>\<omega> \<squnion> w * x\<^sup>\<omega>)"
        by (simp add: sup_assoc mult_assoc)
      finally have "z * x\<^sup>\<omega> \<le> (y * y\<^sup>\<star>)\<^sup>\<omega> \<squnion> (y * y\<^sup>\<star>)\<^sup>\<star> * (y\<^sup>\<omega> \<squnion> w * x\<^sup>\<omega>)"
        by (simp add: omega_induct sup_commute)
      also have "... = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>"
        by (simp add: left_plus_omega semiring.distrib_left star.left_plus_circ star_mult_omega mult_assoc)
      also have "... \<le> ?rhs"
        using mult_left_sub_dist_sup_left sup.mono sup_ge1 by blast
      finally show ?thesis
        .
    qed
    let ?rhs2 = "y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star>)"
    have "?rhs2 * x \<le> ?rhs2"
    proof -
      have 3: "y\<^sup>\<omega> * x \<le> ?rhs2"
        by (simp add: le_supI1 omega_sub_vector)
      have "y\<^sup>\<star> * z * x \<le> y\<^sup>\<star> * (y\<^sup>\<omega> \<squnion> y * y\<^sup>\<star> * z \<squnion> w)"
        using 1 mult_right_isotone mult_assoc by auto
      also have "... = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * y * y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w"
        by (simp add: semiring.distrib_left star_mult_omega mult_assoc)
      also have "... = y\<^sup>\<omega> \<squnion> y * y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w"
        by (simp add: star.circ_plus_same star.circ_transitive_equal mult_assoc)
      also have "... \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w"
        by (metis sup_left_isotone sup_right_isotone mult_left_isotone star.left_plus_below_circ)
      also have "... \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
        using semiring.add_left_mono star.circ_back_loop_prefixpoint by auto
      finally have 4: "y\<^sup>\<star> * z * x \<le> ?rhs2"
        using mult_left_sub_dist_sup_right order_lesseq_imp semiring.add_left_mono by blast
      have "(x\<^sup>\<omega> \<squnion> x\<^sup>\<star>) * x \<le> x\<^sup>\<omega> \<squnion> x\<^sup>\<star>"
        using omega_sub_vector semiring.distrib_right star.left_plus_below_circ star_plus sup_mono by fastforce
      hence "y\<^sup>\<star> * w * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star>) * x \<le> ?rhs2"
        by (simp add: le_supI2 mult_right_isotone mult_assoc)
      thus ?thesis
        using 3 4 mult_right_dist_sup by force
    qed
    hence "z \<squnion> ?rhs2 * x \<le> ?rhs2"
      by (metis omega_loop_fixpoint sup.boundedE sup_ge1 sup_least)
    hence 5: "z * x\<^sup>\<star> \<le> ?rhs2"
      using star_right_induct by blast
    have "z * x\<^sup>\<star> * v \<le> ?rhs"
    proof -
      have "z * x\<^sup>\<star> * v \<le> ?rhs2 * v"
        using 5 mult_left_isotone by auto
      also have "... = y\<^sup>\<omega> * v \<squnion> y\<^sup>\<star> * z * v \<squnion> y\<^sup>\<star> * w * (x\<^sup>\<omega> * v \<squnion> x\<^sup>\<star> * v)"
        using mult_right_dist_sup mult_assoc by auto
      also have "... \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z * v \<squnion> y\<^sup>\<star> * w * (x\<^sup>\<omega> * v \<squnion> x\<^sup>\<star> * v)"
        using omega_sub_vector semiring.add_right_mono by blast
      also have "... \<le> ?rhs"
        using mult_right_isotone omega_sub_vector semiring.add_left_mono semiring.add_right_mono by auto
      finally show ?thesis
        .
    qed
    hence "z * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * v) \<le> ?rhs"
      using 2 semiring.distrib_left mult_assoc by force
    thus "z * (x \<star> v) \<le> y \<star> (z * v \<squnion> w * (x \<star> v))"
      by (simp add: semiring.distrib_left sup_assoc while_def mult_assoc)
  qed
qed

text \<open>Theorem 13.8\<close>

lemma while_top:
  "top \<star> x = top"
  by (metis sup_left_top star.circ_top star_omega_top while_def)

text \<open>Theorem 13.7\<close>

lemma while_one_top:
  "1 \<star> x = top"
  by (simp add: omega_one while_def)

lemma while_finite_associative:
  "x\<^sup>\<omega> = bot \<Longrightarrow> (x \<star> y) * z = x \<star> (y * z)"
  by (simp add: while_def mult_assoc)

lemma star_below_while:
  "x\<^sup>\<star> * y \<le> x \<star> y"
  by (simp add: while_def)

text \<open>Theorem 13.9\<close>

lemma while_sub_mult_one:
  "x * (1 \<star> y) \<le> 1 \<star> x"
  by (simp add: omega_one while_def)

lemma while_while_one:
  "y \<star> (x \<star> 1) = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x\<^sup>\<star>"
  using mult_left_dist_sup sup_assoc while_def by auto

lemma while_simulate_4_plus:
  assumes "y * x \<le> x * (x \<star> (1 \<squnion> y))"
    shows "y * x * x\<^sup>\<star> \<le> x * (x \<star> (1 \<squnion> y))"
proof -
  have 1: "x * (x \<star> (1 \<squnion> y)) = x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    using mult_left_dist_sup omega_unfold sup_assoc while_def mult_assoc by force
  hence "y * x * x\<^sup>\<star> \<le> (x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y) * x\<^sup>\<star>"
    using assms mult_left_isotone by auto
  also have "... = x\<^sup>\<omega> * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y * x\<^sup>\<star>"
    using mult_right_dist_sup by force
  also have "... = x * x\<^sup>\<star> * (y * x * x\<^sup>\<star>) \<squnion> x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    by (smt sup_assoc sup_commute mult_assoc omega_mult_star_2 star.circ_back_loop_fixpoint star.circ_plus_same star.circ_transitive_equal)
  finally have "y * x * x\<^sup>\<star> \<le> x * x\<^sup>\<star> * (y * x * x\<^sup>\<star>) \<squnion> (x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y)"
    using sup_assoc by force
  hence "y * x * x\<^sup>\<star> \<le> (x * x\<^sup>\<star>)\<^sup>\<omega> \<squnion> (x * x\<^sup>\<star>)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y)"
    by (simp add: omega_induct sup_monoid.add_commute)
  also have "... = x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y)"
    by (simp add: left_plus_omega star.left_plus_circ)
  finally show ?thesis
    using 1 by (metis while_def while_mult_star_exchange while_transitive)
qed

lemma while_simulate_4_omega:
  assumes "y * x \<le> x * (x \<star> (1 \<squnion> y))"
    shows "y * x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
proof -
  have "x * (x \<star> (1 \<squnion> y)) = x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y"
    using mult_1_right mult_left_dist_sup omega_unfold sup_assoc while_def mult_assoc by auto
  hence "y * x\<^sup>\<omega> \<le> (x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> \<squnion> x * x\<^sup>\<star> * y) * x\<^sup>\<omega>"
    by (smt assms le_iff_sup mult_assoc mult_right_dist_sup omega_unfold)
  also have "... = x\<^sup>\<omega> * x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> * x\<^sup>\<omega> \<squnion> x * x\<^sup>\<star> * y * x\<^sup>\<omega>"
    using semiring.distrib_right by auto
  also have "... = x * x\<^sup>\<star> * (y * x\<^sup>\<omega>) \<squnion> x\<^sup>\<omega>"
    by (metis sup_commute le_iff_sup mult_assoc omega_sub_vector omega_unfold star_mult_omega)
  finally have "y * x\<^sup>\<omega> \<le> x * x\<^sup>\<star> * (y * x\<^sup>\<omega>) \<squnion> x\<^sup>\<omega>"
    .
  hence "y * x\<^sup>\<omega> \<le> (x * x\<^sup>\<star>)\<^sup>\<omega> \<squnion> (x * x\<^sup>\<star>)\<^sup>\<star> * x\<^sup>\<omega>"
    by (simp add: omega_induct sup_commute)
  thus ?thesis
    by (metis sup_idem left_plus_omega star_mult_omega)
qed

text \<open>Theorem 13.11\<close>

lemma while_unfold_below:
  "x = z \<squnion> y * x \<Longrightarrow> x \<le> y \<star> z"
  by (simp add: omega_induct while_def)

text \<open>Theorem 13.12\<close>

lemma while_unfold_below_sub:
  "x \<le> z \<squnion> y * x \<Longrightarrow> x \<le> y \<star> z"
  by (simp add: omega_induct while_def)

text \<open>Theorem 13.10\<close>

lemma while_unfold_below_1:
  "x = y * x \<Longrightarrow> x \<le> y \<star> 1"
  by (simp add: while_unfold_below_sub)

lemma while_square_1:
  "x \<star> 1 = (x * x) \<star> (x \<squnion> 1)"
  by (metis mult_1_right omega_square star_square_2 while_def)

lemma while_absorb_below_one:
  "y * x \<le> x \<Longrightarrow> y \<star> x \<le> 1 \<star> x"
  by (simp add: while_unfold_below_sub)

lemma while_loop_is_greatest_postfixpoint:
  "is_greatest_postfixpoint (\<lambda>x . y * x \<squnion> z) (y \<star> z)"
proof -
  have "(y \<star> z) \<le> (\<lambda>x . y * x \<squnion> z) (y \<star> z)"
    using sup_commute while_left_unfold by force
  thus ?thesis
    by (simp add: is_greatest_postfixpoint_def sup_commute while_unfold_below_sub)
qed

lemma while_loop_is_greatest_fixpoint:
  "is_greatest_fixpoint (\<lambda>x . y * x \<squnion> z) (y \<star> z)"
  by (simp add: omega_loop_is_greatest_fixpoint while_def)

(*
lemma while_sumstar_4_below: "(x \<star> y) \<star> ((x \<star> 1) * z) \<le> x \<star> ((y * (x \<star> 1)) \<star> z)" nitpick [expect=genuine,card=6] oops
lemma while_sumstar_2: "(x \<squnion> y) \<star> z = x \<star> ((y * (x \<star> 1)) \<star> z)" nitpick [expect=genuine,card=6] oops
lemma while_sumstar_3: "(x \<squnion> y) \<star> z = ((x \<star> 1) * y) \<star> (x \<star> z)" oops
lemma while_decompose_6: "x \<star> ((y * (x \<star> 1)) \<star> z) = y \<star> ((x * (y \<star> 1)) \<star> z)" nitpick [expect=genuine,card=6] oops
lemma while_finite_associative: "x \<star> bot = bot \<Longrightarrow> (x \<star> y) * z = x \<star> (y * z)" oops
lemma atomicity_refinement: "s = s * q \<Longrightarrow> x = q * x \<Longrightarrow> q * b = bot \<Longrightarrow> r * b \<le> b * r \<Longrightarrow> r * l \<le> l * r \<Longrightarrow> x * l \<le> l * x \<Longrightarrow> b * l \<le> l * b \<Longrightarrow> q * l \<le> l * q \<Longrightarrow> r \<star> q \<le> q * (r \<star> 1) \<Longrightarrow> q \<le> 1 \<Longrightarrow> s * ((x \<squnion> b \<squnion> r \<squnion> l) \<star> (q * z)) \<le> s * ((x * (b \<star> q) \<squnion> r \<squnion> l) \<star> z)" oops

lemma while_separate_right_plus: "y * x \<le> x * (x \<star> (1 \<squnion> y)) \<squnion> 1 \<Longrightarrow> y \<star> (x \<star> z) \<le> x \<star> (y \<star> z)" oops
lemma "y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops
lemma "y * x \<le> (1 \<squnion> x) * (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops

lemma while_mult_sub_while_while: "x \<star> (y * z) \<le> (x \<star> y) \<star> z" oops
lemma while_zero_zero: "(x \<star> bot) \<star> bot = x \<star> bot" oops
lemma while_denest_3: "(x \<star> w) \<star> (x \<star> bot) = (x \<star> w) \<star> bot" oops
lemma while_02: "x \<star> ((x \<star> w) \<star> ((x \<star> y) * z)) = (x \<star> w) \<star> ((x \<star> y) * z)" oops
lemma while_sumstar_3_below: "(x \<star> y) \<star> (x \<star> z) \<le> (x \<star> y) \<star> ((x \<star> 1) * z)" oops
lemma while_sumstar_1: "(x \<squnion> y) \<star> z = (x \<star> y) \<star> ((x \<star> 1) * z)" oops
lemma while_denest_4: "(x \<star> w) \<star> (x \<star> (y * z)) = (x \<star> w) \<star> ((x \<star> y) * z)" oops
*)

end

class nonstrict_itering_zero = nonstrict_itering +
  assumes mult_right_zero: "x * bot = bot"
begin

lemma while_finite_associative_2:
  "x \<star> bot = bot \<Longrightarrow> (x \<star> y) * z = x \<star> (y * z)"
  by (metis sup_bot_left sup_bot_right mult_assoc mult_right_zero while_def)

text \<open>Theorem 13 counterexamples\<close>

(*
lemma while_mult_top: "(x * top) \<star> z = z \<squnion> x * top" nitpick [expect=genuine,card=3] oops
lemma tarski_mult_top_idempotent: "x * top = x * top * x * top" nitpick [expect=genuine,card=3] oops

lemma while_denest_0: "w * (x \<star> (y * z)) \<le> (w * (x \<star> y)) \<star> (w * (x \<star> y) * z)" nitpick [expect=genuine,card=3] oops
lemma while_denest_1: "w * (x \<star> (y * z)) \<le> (w * (x \<star> y)) \<star> z" nitpick [expect=genuine,card=3] oops
lemma while_mult_zero_zero: "(x * (y \<star> bot)) \<star> bot = x * (y \<star> bot)" nitpick [expect=genuine,card=3] oops
lemma while_denest_2: "w * ((x \<star> (y * w)) \<star> z) = w * (((x \<star> y) * w) \<star> z)" nitpick [expect=genuine,card=3] oops
lemma while_denest_5: "w * ((x \<star> (y * w)) \<star> (x \<star> (y * z))) = w * (((x \<star> y) * w) \<star> ((x \<star> y) * z))" nitpick [expect=genuine,card=3] oops
lemma while_denest_6: "(w * (x \<star> y)) \<star> z = z \<squnion> w * ((x \<squnion> y * w) \<star> (y * z))" nitpick [expect=genuine,card=3] oops
lemma while_sum_below_one: "y * ((x \<squnion> y) \<star> z) \<le> (y * (x \<star> 1)) \<star> z" nitpick [expect=genuine,card=3] oops
lemma while_separate_unfold: "(y * (x \<star> 1)) \<star> z = (y \<star> z) \<squnion> (y \<star> (y * x * (x \<star> ((y * (x \<star> 1)) \<star> z))))" nitpick [expect=genuine,card=3] oops

lemma while_sub_while_zero: "x \<star> z \<le> (x \<star> y) \<star> z" nitpick [expect=genuine,card=4] oops
lemma while_while_sub_associative: "x \<star> (y \<star> z) \<le> (x \<star> y) \<star> z" nitpick [expect=genuine,card=4] oops
lemma tarski: "x \<le> x * top * x * top" nitpick [expect=genuine,card=3] oops
lemma tarski_top_omega_below: "x * top \<le> (x * top)\<^sup>\<omega>" nitpick [expect=genuine,card=3] oops
lemma tarski_top_omega: "x * top = (x * top)\<^sup>\<omega>" nitpick [expect=genuine,card=3] oops
lemma tarski_below_top_omega: "x \<le> (x * top)\<^sup>\<omega>" nitpick [expect=genuine,card=3] oops
lemma tarski_mult_omega_omega: "(x * y\<^sup>\<omega>)\<^sup>\<omega> = x * y\<^sup>\<omega>" nitpick [expect=genuine,card=3] oops
lemma tarski_mult_omega_omega: "(\<forall>z . z\<^sup>\<omega>\<^sup>\<omega> = z\<^sup>\<omega>) \<Longrightarrow> (x * y\<^sup>\<omega>)\<^sup>\<omega> = x * y\<^sup>\<omega>" nitpick [expect=genuine,card=3] oops
lemma tarski: "x = bot \<or> top * x * top = top" nitpick [expect=genuine,card=3] oops
*)

end

class nonstrict_itering_tarski = nonstrict_itering +
  assumes tarski: "x \<le> x * top * x * top"
begin

text \<open>Theorem 13.14\<close>

lemma tarski_mult_top_idempotent:
  "x * top = x * top * x * top"
  by (metis sup_commute le_iff_sup mult_assoc star.circ_back_loop_fixpoint star.circ_left_top tarski top_mult_top)

lemma tarski_top_omega_below:
  "x * top \<le> (x * top)\<^sup>\<omega>"
  using omega_induct_mult order.refl mult_assoc tarski_mult_top_idempotent by auto

lemma tarski_top_omega:
  "x * top = (x * top)\<^sup>\<omega>"
  by (simp add: order.eq_iff mult_top_omega tarski_top_omega_below)

lemma tarski_below_top_omega:
  "x \<le> (x * top)\<^sup>\<omega>"
  using top_right_mult_increasing tarski_top_omega by auto

lemma tarski_mult_omega_omega:
  "(x * y\<^sup>\<omega>)\<^sup>\<omega> = x * y\<^sup>\<omega>"
  by (metis mult_assoc omega_vector tarski_top_omega)

lemma tarski_omega_idempotent:
  "x\<^sup>\<omega>\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis omega_vector tarski_top_omega)

lemma while_denest_2a:
  "w * ((x \<star> (y * w)) \<star> z) = w * (((x \<star> y) * w) \<star> z)"
proof -
  have "(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<omega> = (x\<^sup>\<star> * y * w)\<^sup>\<star> * x\<^sup>\<omega> * (((x\<^sup>\<star> * y * w)\<^sup>\<star> * x\<^sup>\<omega>)\<^sup>\<omega> \<squnion> ((x\<^sup>\<star> * y * w)\<^sup>\<star> * x\<^sup>\<omega>)\<^sup>\<star> * (x\<^sup>\<star> * y * w)\<^sup>\<omega>) \<squnion> (x\<^sup>\<star> * y * w)\<^sup>\<omega>"
    by (metis sup_commute omega_decompose omega_loop_fixpoint)
  also have "... \<le> (x\<^sup>\<star> * y * w)\<^sup>\<star> * x\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y * w)\<^sup>\<omega>"
    by (metis sup_left_isotone mult_assoc mult_right_isotone omega_sub_vector)
  finally have 1: "w * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<omega> \<le> (w * x\<^sup>\<star> * y)\<^sup>\<star> * w * x\<^sup>\<omega> \<squnion> (w * x\<^sup>\<star> * y)\<^sup>\<omega>"
    by (smt sup_commute le_iff_sup mult_assoc mult_left_dist_sup while_def while_slide)
  have "(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<star> * z = (x\<^sup>\<star> * y * w)\<^sup>\<star> * x\<^sup>\<omega> * ((x\<^sup>\<star> * y * w)\<^sup>\<star> * x\<^sup>\<omega>)\<^sup>\<star> * (x\<^sup>\<star> * y * w)\<^sup>\<star> * z \<squnion> (x\<^sup>\<star> * y * w)\<^sup>\<star> * z"
    by (smt sup_commute mult_assoc star.circ_sup star.circ_loop_fixpoint)
  also have "... \<le> (x\<^sup>\<star> * y * w)\<^sup>\<star> * x\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y * w)\<^sup>\<star> * z"
    by (smt sup_commute sup_right_isotone mult_assoc mult_right_isotone omega_sub_vector)
  finally have "w * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<star> * z \<le> (w * x\<^sup>\<star> * y)\<^sup>\<star> * w * x\<^sup>\<omega> \<squnion> (w * x\<^sup>\<star> * y)\<^sup>\<star> * w * z"
    by (metis mult_assoc mult_left_dist_sup mult_right_isotone star.circ_slide)
  hence "w * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<omega> \<squnion> w * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<star> * z \<le> (w * x\<^sup>\<star> * y)\<^sup>\<star> * (w * x\<^sup>\<omega>)\<^sup>\<omega> \<squnion> (w * x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (w * x\<^sup>\<star> * y)\<^sup>\<star> * w * z"
    using 1 by (smt sup_assoc sup_commute le_iff_sup mult_assoc tarski_mult_omega_omega)
  also have "... \<le> (w * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<star> * y)\<^sup>\<star> * (w * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (w * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (w * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<star> * y)\<^sup>\<star> * w * z"
    by (metis sup_mono sup_ge1 sup_ge2 mult_isotone mult_left_isotone omega_isotone star.circ_isotone)
  also have "... = (w * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (w * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<star> * y)\<^sup>\<star> * w * z"
    by (simp add: star_mult_omega)
  finally have "w * ((x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<omega> \<squnion> (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y * w)\<^sup>\<star> * z) \<le> w * ((x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y) * w)\<^sup>\<omega> \<squnion> w * ((x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * y) * w)\<^sup>\<star> * z"
    by (smt mult_assoc mult_left_dist_sup omega_slide star.circ_slide)
  hence 2: "w * ((x \<star> (y * w)) \<star> z) \<le> w * (((x \<star> y) * w) \<star> z)"
    by (simp add: mult_left_dist_sup while_def mult_assoc)
  have "w * (((x \<star> y) * w) \<star> z) \<le> w * ((x \<star> (y * w)) \<star> z)"
    by (simp add: mult_right_isotone while_left_isotone while_sub_associative)
  thus ?thesis
    using 2 order.antisym by auto
qed

lemma while_denest_3:
  "(x \<star> w) \<star> x\<^sup>\<omega> = (x \<star> w)\<^sup>\<omega>"
proof -
  have 1: "(x \<star> w) \<star> x\<^sup>\<omega> = (x \<star> w)\<^sup>\<omega> \<squnion> (x \<star> w)\<^sup>\<star> * x\<^sup>\<omega>\<^sup>\<omega>"
    by (simp add: while_def tarski_omega_idempotent)
  also have "... \<le> (x \<star> w)\<^sup>\<omega> \<squnion> (x \<star> w)\<^sup>\<star> * (x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * w)\<^sup>\<omega>"
    using mult_right_isotone omega_sub_dist semiring.add_left_mono by blast
  also have "... = (x \<star> w)\<^sup>\<omega>"
    by (simp add: star_mult_omega while_def)
  finally show ?thesis
    using 1 by (simp add: sup.order_iff)
qed

lemma while_denest_4a:
  "(x \<star> w) \<star> (x \<star> (y * z)) = (x \<star> w) \<star> ((x \<star> y) * z)"
proof -
  have "(x \<star> w) \<star> (x \<star> (y * z)) = (x \<star> w)\<^sup>\<omega> \<squnion> ((x \<star> w) \<star> (x\<^sup>\<star> * y * z))"
    using while_def while_denest_3 while_left_dist_sup mult_assoc by auto
  also have "... \<le> (x \<star> w)\<^sup>\<omega> \<squnion> ((x \<star> w) \<star> ((x \<star> y) * z))"
    using mult_right_sub_dist_sup_right order.refl semiring.add_mono while_def while_right_isotone by auto
  finally have 1: "(x \<star> w) \<star> (x \<star> (y * z)) \<le> (x \<star> w) \<star> ((x \<star> y) * z)"
    by (simp add: while_def)
  have "(x \<star> w) \<star> ((x \<star> y) * z) \<le> (x \<star> w) \<star> (x \<star> (y * z))"
    by (simp add: while_right_isotone while_sub_associative)
  thus ?thesis
    using 1 order.antisym by auto
qed

text \<open>Theorem 8.3\<close>

subclass bounded_extended_binary_itering
  apply unfold_locales
  by (smt mult_assoc while_denest_2a while_denest_4a while_increasing while_slide)

text \<open>Theorem 13.13\<close>

lemma while_mult_top:
  "(x * top) \<star> z = z \<squnion> x * top"
proof -
  have 1: "z \<squnion> x * top \<le> (x * top) \<star> z"
    by (metis le_supI sup_ge1 while_def while_increasing tarski_top_omega)
  have "(x * top) \<star> z = z \<squnion> x * top * ((x * top) \<star> z)"
    using while_left_unfold by auto
  also have "... \<le> z \<squnion> x * top"
    using mult_right_isotone sup_right_isotone top_greatest mult_assoc by auto
  finally show ?thesis
    using 1 order.antisym by auto
qed

lemma tarski_top_omega_below_2:
  "x * top \<le> (x * top) \<star> bot"
  by (simp add: while_mult_top)

lemma tarski_top_omega_2:
  "x * top = (x * top) \<star> bot"
  by (simp add: while_mult_top)

lemma tarski_below_top_omega_2:
  "x \<le> (x * top) \<star> bot"
  using top_right_mult_increasing tarski_top_omega_2 by auto

(*
lemma "1 = (x * bot) \<star> 1" nitpick [expect=genuine,card=3] oops
*)

end

class nonstrict_itering_tarski_zero = nonstrict_itering_tarski + nonstrict_itering_zero
begin

lemma while_bot_1:
  "1 = (x * bot) \<star> 1"
  by (simp add: mult_right_zero while_zero)

text \<open>Theorem 13 counterexamples\<close>

(*
lemma while_associative: "(x \<star> y) * z = x \<star> (y * z)" nitpick [expect=genuine,card=2] oops
lemma "(x \<star> 1) * y = x \<star> y" nitpick [expect=genuine,card=2] oops
lemma while_one_mult: "(x \<star> 1) * x = x \<star> x" nitpick [expect=genuine,card=4] oops
lemma "(x \<squnion> y) \<star> z = ((x \<star> 1) * y) \<star> ((x \<star> 1) * z)" nitpick [expect=genuine,card=2] oops
lemma while_mult_top_2: "(x * top) \<star> z = z \<squnion> x * top * z" nitpick [expect=genuine,card=2] oops
lemma while_top_2: "top \<star> z = top * z" nitpick [expect=genuine,card=2] oops

lemma tarski: "x = bot \<or> top * x * top = top" nitpick [expect=genuine,card=3] oops
lemma while_back_loop_is_fixpoint: "is_fixpoint (\<lambda>x . x * y \<squnion> z) (z * (y \<star> 1))" nitpick [expect=genuine,card=4] oops
lemma "1 \<squnion> x * bot = x \<star> 1" nitpick [expect=genuine,card=3] oops
lemma "x = x * (x \<star> 1)" nitpick [expect=genuine,card=3] oops
lemma "x * (x \<star> 1) = x \<star> 1" nitpick [expect=genuine,card=2] oops
lemma "x \<star> 1 = x \<star> (1 \<star> 1)" nitpick [expect=genuine,card=3] oops
lemma "(x \<squnion> y) \<star> 1 = (x \<star> (y \<star> 1)) \<star> 1" nitpick [expect=genuine,card=3] oops
lemma "z \<squnion> y * x = x \<Longrightarrow> y \<star> z \<le> x" nitpick [expect=genuine,card=2] oops
lemma "y * x = x ==> y \<star> x \<le> x" nitpick [expect=genuine,card=2] oops
lemma "z \<squnion> x * y = x \<Longrightarrow> z * (y \<star> 1) \<le> x" nitpick [expect=genuine,card=3] oops
lemma "x * y = x \<Longrightarrow> x * (y \<star> 1) \<le> x" nitpick [expect=genuine,card=3] oops
lemma "x * z = z * y \<Longrightarrow> x \<star> z \<le> z * (y \<star> 1)" nitpick [expect=genuine,card=2] oops

lemma tarski: "x = bot \<or> top * x * top = top" nitpick [expect=genuine,card=3] oops
lemma tarski_case: assumes t1: "x = bot \<longrightarrow> P x" and t2: "top * x * top = top \<longrightarrow> P x" shows "P x" nitpick [expect=genuine,card=3] oops
*)

end

end

