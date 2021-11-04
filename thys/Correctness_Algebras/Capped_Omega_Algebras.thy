(* Title:      Capped Omega Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Capped Omega Algebras\<close>

theory Capped_Omega_Algebras

imports Omega_Algebras

begin

class capped_omega =
  fixes capped_omega :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<^sup>\<omega>\<^sub>_" [100,100] 100)

class capped_omega_algebra = bounded_left_zero_kleene_algebra + bounded_distrib_lattice + capped_omega +
  assumes capped_omega_unfold: "y\<^sup>\<omega>\<^sub>v = y * y\<^sup>\<omega>\<^sub>v \<sqinter> v"
  assumes capped_omega_induct: "x \<le> (y * x \<squnion> z) \<sqinter> v \<longrightarrow> x \<le> y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z"

text \<open>AACP Theorem 6.1\<close>

notation
  top ("\<top>")

sublocale capped_omega_algebra < capped: bounded_left_zero_omega_algebra where omega = "(\<lambda>y . y\<^sup>\<omega>\<^sub>\<top>)"
  apply unfold_locales
  apply (metis capped_omega_unfold inf_top_right)
  by (simp add: capped_omega_induct sup_commute)

context capped_omega_algebra
begin

text \<open>AACP Theorem 6.2\<close>

lemma capped_omega_below_omega:
  "y\<^sup>\<omega>\<^sub>v \<le> y\<^sup>\<omega>\<^sub>\<top>"
  using capped.omega_induct_mult capped_omega_unfold order.eq_iff by force

text \<open>AACP Theorem 6.3\<close>

lemma capped_omega_below:
  "y\<^sup>\<omega>\<^sub>v \<le> v"
  using capped_omega_unfold order.eq_iff by force

text \<open>AACP Theorem 6.4\<close>

lemma capped_omega_one:
  "1\<^sup>\<omega>\<^sub>v = v"
proof -
  have "v \<le> (1 * v \<squnion> bot) \<sqinter> v"
    by simp
  hence "v \<le> 1\<^sup>\<omega>\<^sub>v \<squnion> 1\<^sup>\<star> * bot"
    by (simp add: capped_omega_induct)
  also have "... = 1\<^sup>\<omega>\<^sub>v"
    by (simp add: star_one)
  finally show ?thesis
    by (simp add: capped_omega_below order.antisym)
qed

text \<open>AACP Theorem 6.5\<close>

lemma capped_omega_zero:
  "bot\<^sup>\<omega>\<^sub>v = bot"
  by (metis capped_omega_below_omega bot_unique capped.omega_bot)

lemma star_below_cap:
  "y \<le> u \<Longrightarrow> z \<le> v \<Longrightarrow> u * v \<le> v \<Longrightarrow> y\<^sup>\<star> * z \<le> v"
  by (metis le_sup_iff order.trans mult_left_isotone star_left_induct)

lemma capped_fix:
  assumes "y \<le> u"
      and "z \<le> v"
      and "u * v \<le> v"
    shows "(y * (y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z) \<squnion> z) \<sqinter> v = y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z"
proof -
  have "(y * (y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z) \<squnion> z) \<sqinter> v = (y * y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z) \<sqinter> v"
    by (simp add: mult_left_dist_sup star.circ_loop_fixpoint sup_assoc)
  also have "... = (y * y\<^sup>\<omega>\<^sub>v \<sqinter> v) \<squnion> (y\<^sup>\<star> * z \<sqinter> v)"
    by (simp add: inf_sup_distrib2)
  also have "... = y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z"
    using assms capped_omega_unfold le_iff_inf star_below_cap by auto
  finally show ?thesis
    .
qed

lemma capped_fixpoint:
  "y \<le> u \<Longrightarrow> z \<le> v \<Longrightarrow> u * v \<le> v \<Longrightarrow> is_fixpoint (\<lambda>x . (y * x \<squnion> z) \<sqinter> v) (y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z)"
  by (simp add: capped_fix is_fixpoint_def)

lemma capped_greatest_fixpoint:
  "y \<le> u \<Longrightarrow> z \<le> v \<Longrightarrow> u * v \<le> v \<Longrightarrow> is_greatest_fixpoint (\<lambda>x . (y * x \<squnion> z) \<sqinter> v) (y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z)"
  by (smt capped_fix order_refl capped_omega_induct is_greatest_fixpoint_def)

lemma capped_postfixpoint:
  "y \<le> u \<Longrightarrow> z \<le> v \<Longrightarrow> u * v \<le> v \<Longrightarrow> is_postfixpoint (\<lambda>x . (y * x \<squnion> z) \<sqinter> v) (y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z)"
  using capped_fix inf.eq_refl is_postfixpoint_def by auto

lemma capped_greatest_postfixpoint:
  "y \<le> u \<Longrightarrow> z \<le> v \<Longrightarrow> u * v \<le> v \<Longrightarrow> is_greatest_postfixpoint (\<lambda>x . (y * x \<squnion> z) \<sqinter> v) (y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z)"
  by (smt capped_fix order_refl capped_omega_induct is_greatest_postfixpoint_def)

text \<open>AACP Theorem 6.6\<close>

lemma capped_nu:
  "y \<le> u \<Longrightarrow> z \<le> v \<Longrightarrow> u * v \<le> v \<Longrightarrow> \<nu>(\<lambda>x . (y * x \<squnion> z) \<sqinter> v) = y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z"
  by (metis capped_greatest_fixpoint greatest_fixpoint_same)

lemma capped_pnu:
  "y \<le> u \<Longrightarrow> z \<le> v \<Longrightarrow> u * v \<le> v \<Longrightarrow> p\<nu>(\<lambda>x . (y * x \<squnion> z) \<sqinter> v) = y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z"
  by (metis capped_greatest_postfixpoint greatest_postfixpoint_same)

text \<open>AACP Theorem 6.7\<close>

lemma unfold_capped_omega:
  "y \<le> u \<Longrightarrow> u * v \<le> v \<Longrightarrow> y * y\<^sup>\<omega>\<^sub>v = y\<^sup>\<omega>\<^sub>v"
  by (smt (verit, ccfv_SIG) capped_omega_below capped_omega_unfold inf.order_lesseq_imp le_iff_inf mult_isotone)

text \<open>AACP Theorem 6.8\<close>

lemma star_mult_capped_omega:
  assumes "y \<le> u"
      and "u * v \<le> v"
    shows "y\<^sup>\<star> * y\<^sup>\<omega>\<^sub>v = y\<^sup>\<omega>\<^sub>v"
proof -
  have "y * y\<^sup>\<omega>\<^sub>v = y\<^sup>\<omega>\<^sub>v"
    using assms unfold_capped_omega by auto
  hence "y\<^sup>\<star> * y\<^sup>\<omega>\<^sub>v \<le> y\<^sup>\<omega>\<^sub>v"
    by (simp add: star_left_induct_mult)
  thus ?thesis
    by (metis sup_ge2 order.antisym star.circ_loop_fixpoint)
qed

text \<open>AACP Theorem 6.9\<close>

lemma star_zero_below_capped_omega_zero:
  assumes "y \<le> u"
      and "u * v \<le> v"
    shows "y\<^sup>\<star> * bot \<le> y\<^sup>\<omega>\<^sub>v * bot"
proof -
  have "y * y\<^sup>\<omega>\<^sub>v \<le> v"
    using assms capped_omega_below unfold_capped_omega by auto
  hence "y * y\<^sup>\<omega>\<^sub>v = y\<^sup>\<omega>\<^sub>v"
    using assms unfold_capped_omega by auto
  thus ?thesis
    by (metis bot_least eq_refl mult_assoc star_below_cap)
qed

lemma star_zero_below_capped_omega:
  "y \<le> u \<Longrightarrow> u * v \<le> v \<Longrightarrow> y\<^sup>\<star> * bot \<le> y\<^sup>\<omega>\<^sub>v"
  by (simp add: star_loop_least_fixpoint unfold_capped_omega)

lemma capped_omega_induct_meet_zero:
  "x \<le> y * x \<sqinter> v \<Longrightarrow> x \<le> y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * bot"
  by (simp add: capped_omega_induct)

text \<open>AACP Theorem 6.10\<close>

lemma capped_omega_induct_meet:
  "y \<le> u \<Longrightarrow> u * v \<le> v \<Longrightarrow> x \<le> y * x \<sqinter> v \<Longrightarrow> x \<le> y\<^sup>\<omega>\<^sub>v"
  by (metis capped_omega_induct_meet_zero sup_commute le_iff_sup star_zero_below_capped_omega)

lemma capped_omega_induct_equal:
  "x = (y * x \<squnion> z) \<sqinter> v \<Longrightarrow> x \<le> y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * z"
  using capped_omega_induct inf.le_iff_sup by auto

text \<open>AACP Theorem 6.11\<close>

lemma capped_meet_nu:
  assumes "y \<le> u"
      and "u * v \<le> v"
    shows "\<nu>(\<lambda>x . y * x \<sqinter> v) = y\<^sup>\<omega>\<^sub>v"
proof -
  have "y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * bot = y\<^sup>\<omega>\<^sub>v"
    by (smt assms star_zero_below_capped_omega le_iff_sup sup_commute)
  hence "\<nu>(\<lambda>x . (y * x \<squnion> bot) \<sqinter> v) = y\<^sup>\<omega>\<^sub>v"
    by (metis assms capped_nu bot_least)
  thus ?thesis
    by simp
qed

lemma capped_meet_pnu:
  assumes "y \<le> u"
      and "u * v \<le> v"
    shows "p\<nu>(\<lambda>x . y * x \<sqinter> v) = y\<^sup>\<omega>\<^sub>v"
proof -
  have "y\<^sup>\<omega>\<^sub>v \<squnion> y\<^sup>\<star> * bot = y\<^sup>\<omega>\<^sub>v"
    by (smt assms star_zero_below_capped_omega le_iff_sup sup_commute)
  hence "p\<nu>(\<lambda>x . (y * x \<squnion> bot) \<sqinter> v) = y\<^sup>\<omega>\<^sub>v"
    by (metis assms capped_pnu bot_least)
  thus ?thesis
    by simp
qed

text \<open>AACP Theorem 6.12\<close>

lemma capped_omega_isotone:
  "y \<le> u \<Longrightarrow> u * v \<le> v \<Longrightarrow> t \<le> y \<Longrightarrow> t\<^sup>\<omega>\<^sub>v \<le> y\<^sup>\<omega>\<^sub>v"
  by (metis capped_omega_induct_meet capped_omega_unfold le_iff_sup inf.sup_left_isotone mult_right_sub_dist_sup_left)

text \<open>AACP Theorem 6.13\<close>

lemma capped_omega_simulation:
  assumes "y \<le> u"
      and "s \<le> u"
      and "u * v \<le> v"
      and "s * t \<le> y * s"
    shows "s * t\<^sup>\<omega>\<^sub>v \<le> y\<^sup>\<omega>\<^sub>v"
proof -
  have "s * t\<^sup>\<omega>\<^sub>v \<le> s * t * t\<^sup>\<omega>\<^sub>v \<sqinter> s * v"
    by (metis capped_omega_below capped_omega_unfold inf.boundedI inf.cobounded1 mult_right_isotone mult_assoc)
  also have "... \<le> s * t * t\<^sup>\<omega>\<^sub>v \<sqinter> v"
    using assms(2,3) inf.order_lesseq_imp inf.sup_right_isotone mult_left_isotone by blast
  also have "... \<le> y * s * t\<^sup>\<omega>\<^sub>v \<sqinter> v"
    using assms(4) inf.sup_left_isotone mult_left_isotone by auto
  finally show ?thesis
    using assms(1,3) capped_omega_induct_meet mult_assoc by auto
qed

lemma capped_omega_slide_sub:
  assumes "s \<le> u"
      and "y \<le> u"
      and "u * u \<le> u"
      and "u * v \<le> v"
    shows "s * (y * s)\<^sup>\<omega>\<^sub>v \<le> (s * y)\<^sup>\<omega>\<^sub>v"
proof -
  have "s * y \<le> u"
    by (meson assms(1-3) mult_isotone order_trans)
  thus ?thesis
    using assms(1,4) capped_omega_simulation mult_assoc by auto 
qed

text \<open>AACP Theorem 6.14\<close>

lemma capped_omega_slide:
  "s \<le> u \<Longrightarrow> y \<le> u \<Longrightarrow> u * u \<le> u \<Longrightarrow> u * v \<le> v \<Longrightarrow> s * (y * s)\<^sup>\<omega>\<^sub>v = (s * y)\<^sup>\<omega>\<^sub>v"
  by (smt (verit) order.antisym mult_assoc mult_right_isotone capped_omega_unfold capped_omega_slide_sub inf.sup_ge1 order_trans)

lemma capped_omega_sub_dist:
  "s \<le> u \<Longrightarrow> y \<le> u \<Longrightarrow> u * v \<le> v \<Longrightarrow> s\<^sup>\<omega>\<^sub>v \<le> (s \<squnion> y)\<^sup>\<omega>\<^sub>v"
  by (simp add: capped_omega_isotone)

text \<open>AACP Theorem 6.15\<close>

lemma capped_omega_simulation_2:
  assumes "s \<le> u"
      and "y \<le> u"
      and "u * u \<le> u"
      and "u * v \<le> v"
      and "y * s \<le> s * y"
    shows "(s * y)\<^sup>\<omega>\<^sub>v \<le> s\<^sup>\<omega>\<^sub>v"
proof -
  have 1: "s * y \<le> u"
    using assms(1-3) inf.order_lesseq_imp mult_isotone by blast
  have 2: "s * (s * y)\<^sup>\<omega>\<^sub>v \<le> v"
    by (meson assms(1,4) capped_omega_below order.trans mult_isotone)
  have "(s * y)\<^sup>\<omega>\<^sub>v = s * (y * s)\<^sup>\<omega>\<^sub>v"
    using assms(1-4) capped_omega_slide by auto
  also have "... \<le> s * (s * y)\<^sup>\<omega>\<^sub>v"
    using 1 assms(4,5) capped_omega_isotone mult_right_isotone by blast
  also have "... = s * (s * y)\<^sup>\<omega>\<^sub>v \<sqinter> v"
    using 2 inf.order_iff by auto
  finally show ?thesis
    using assms(1,4) capped_omega_induct_meet by blast
qed

text \<open>AACP Theorem 6.16\<close>

lemma left_plus_capped_omega:
  assumes "y \<le> u"
      and "u * u \<le> u"
      and "u * v \<le> v"
    shows "(y * y\<^sup>\<star>)\<^sup>\<omega>\<^sub>v = y\<^sup>\<omega>\<^sub>v"
proof -
  have 1: "y * y\<^sup>\<star> \<le> u"
    by (metis assms(1,2) star_plus star_below_cap)
  hence "y * y\<^sup>\<star> * (y * y\<^sup>\<star>)\<^sup>\<omega>\<^sub>v \<le> v"
    using assms(3) capped_omega_below unfold_capped_omega by auto
  hence "y * y\<^sup>\<star> * (y * y\<^sup>\<star>)\<^sup>\<omega>\<^sub>v = (y * y\<^sup>\<star>)\<^sup>\<omega>\<^sub>v"
    using 1 assms(3) unfold_capped_omega by blast
  hence "(y * y\<^sup>\<star>)\<^sup>\<omega>\<^sub>v \<le> y\<^sup>\<omega>\<^sub>v"
    using 1 by (smt assms(1,3) capped_omega_simulation mult_assoc mult_semi_associative star.circ_transitive_equal star_simulation_right_equal)
  thus ?thesis
    using 1 by (meson assms(3) capped_omega_isotone order.antisym star.circ_mult_increasing)
qed

text \<open>AACP Theorem 6.17\<close>

lemma capped_omega_sub_vector:
  assumes "z \<le> v"
      and "y \<le> u"
      and "u * v \<le> v"
    shows "y\<^sup>\<omega>\<^sub>u * z \<le> y\<^sup>\<omega>\<^sub>v"
proof -
  have "y\<^sup>\<omega>\<^sub>u * z \<le> y * y\<^sup>\<omega>\<^sub>u * z \<sqinter> u * z"
    by (metis capped_omega_below capped_omega_unfold eq_refl inf.boundedI inf.cobounded1 mult_isotone)
  also have "... \<le> y * y\<^sup>\<omega>\<^sub>u * z \<sqinter> v"
    by (metis assms(1,3) inf.sup_left_isotone inf_commute mult_right_isotone order_trans)
  finally show ?thesis
    using assms(2,3) capped_omega_induct_meet mult_assoc by auto
qed

text \<open>AACP Theorem 6.18\<close>

lemma capped_omega_omega:
  "y \<le> u \<Longrightarrow> u * v \<le> v \<Longrightarrow> (y\<^sup>\<omega>\<^sub>u)\<^sup>\<omega>\<^sub>v \<le> y\<^sup>\<omega>\<^sub>v"
  by (metis capped_omega_below capped_omega_sub_vector unfold_capped_omega)

end

end

