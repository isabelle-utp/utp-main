(* Title:      Strict Recursion
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Strict Recursion\<close>

theory Recursion_Strict

imports N_Semirings Approximation

begin

class semiring_apx = n_semiring + apx +
  assumes apx_def: "x \<sqsubseteq> y \<longleftrightarrow> x \<le> y \<squnion> n(x) * L \<and> y \<le> x \<squnion> n(x) * top"
begin

lemma apx_n_order_reverse:
  "y \<sqsubseteq> x \<Longrightarrow> n(x) \<le> n(y)"
  by (metis apx_def le_iff_sup n_sup_left_absorb_mult n_dist_sup n_export)

lemma apx_n_order:
  "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> n(x) = n(y)"
  by (simp add: apx_n_order_reverse order.antisym)

lemma apx_transitive:
  assumes "x \<sqsubseteq> y"
      and "y \<sqsubseteq> z"
    shows "x \<sqsubseteq> z"
proof -
  have "n(y) * L \<le> n(x) * L"
    by (simp add: apx_n_order_reverse assms(1) mult_left_isotone)
  hence 1: "x \<le> z \<squnion> n(x) * L"
    by (smt assms sup_assoc sup_right_divisibility apx_def le_iff_sup)
  have "z \<le> x \<squnion> n(x) * top \<squnion> n(x \<squnion> n(x) * top) * top"
    by (smt (verit) assms sup_left_isotone order_refl sup_assoc sup_mono apx_def mult_left_isotone n_isotone order_trans)
  also have "... = x \<squnion> n(x) * top"
    by (simp add: n_dist_sup n_export n_sup_left_absorb_mult)
  finally show ?thesis
    using 1 by (simp add: apx_def)
qed

text \<open>Theorem 16.1\<close>

subclass apx_biorder
  apply unfold_locales
  apply (simp add: apx_def)
  apply (smt (verit) order.antisym le_sup_iff apx_def eq_refl le_iff_sup n_galois apx_n_order)
  using apx_transitive by blast

lemma sup_apx_left_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x \<squnion> z \<sqsubseteq> y \<squnion> z"
proof -
  have "x \<le> y \<squnion> n(x) * L \<and> y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  hence "z \<squnion> x \<le> z \<squnion> y \<squnion> n(z \<squnion> x) * L \<and> z \<squnion> y \<le> z \<squnion> x \<squnion> n(z \<squnion> x) * top"
    by (metis sup_assoc sup_right_isotone mult_right_sub_dist_sup_right n_dist_sup order_trans)
  thus ?thesis
    by (simp add: apx_def sup_commute)
qed

lemma mult_apx_left_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x * z \<sqsubseteq> y * z"
proof -
  have "x \<le> y \<squnion> n(x) * L"
    using assms apx_def by auto
  hence "x * z \<le> y * z \<squnion> n(x) * L"
    by (smt (verit, ccfv_threshold) L_left_zero mult_left_isotone semiring.distrib_right mult_assoc)
  hence 1: "x * z \<le> y * z \<squnion> n(x * z) * L"
    by (meson mult_left_isotone n_mult_left_upper_bound order_lesseq_imp sup_mono)
  have "y * z \<le> x * z \<squnion> n(x) * top * z"
    by (metis assms apx_def mult_left_isotone mult_right_dist_sup)
  hence "y * z \<le> x * z \<squnion> n(x * z) * top"
    using mult_isotone n_mult_left_upper_bound order.trans sup_right_isotone top_greatest mult_assoc by presburger
  thus ?thesis
    using 1 by (simp add: apx_def)
qed

lemma mult_apx_right_isotone:
  assumes "x \<sqsubseteq> y"
    shows "z * x \<sqsubseteq> z * y"
proof -
  have "x \<le> y \<squnion> n(x) * L"
    using assms apx_def by auto
  hence 1: "z * x \<le> z * y \<squnion> n(z * x) * L"
    by (smt sup_assoc sup_ge1 sup_bot_right mult_assoc mult_left_dist_sup mult_right_isotone n_L_split)
  have "y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  hence "z * y \<le> z * x \<squnion> z * n(x) * top"
    by (smt mult_assoc mult_left_dist_sup mult_right_isotone)
  also have "... \<le> z * x \<squnion> n(z * x) * top"
    by (smt (verit) sup_assoc le_supI le_sup_iff sup_ge1 sup_bot_right mult_left_dist_sup n_L_split n_top_split order_trans)
  finally show ?thesis
    using 1 by (simp add: apx_def)
qed

text \<open>Theorem 16.1 and Theorem 16.2\<close>

subclass apx_semiring
  apply unfold_locales
  apply (metis sup_right_top sup_ge2 apx_def mult_left_one n_L top_greatest)
  apply (simp add: sup_apx_left_isotone)
  apply (simp add: mult_apx_left_isotone)
  by (simp add: mult_apx_right_isotone)

text \<open>Theorem 16.2\<close>

lemma ni_apx_isotone:
  "x \<sqsubseteq> y \<Longrightarrow> ni(x) \<sqsubseteq> ni(y)"
  using apx_n_order_reverse apx_def le_supI1 n_ni ni_def ni_n_order by force

text \<open>Theorem 17\<close>

definition kappa_apx_meet :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_apx_meet f \<equiv> apx.has_least_fixpoint f \<and> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<kappa> f = \<mu> f \<triangle> \<nu> f"

definition kappa_mu_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_mu_nu f \<equiv> apx.has_least_fixpoint f \<and> \<kappa> f = \<mu> f \<squnion> n(\<nu> f) * L"

definition nu_below_mu_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "nu_below_mu_nu f \<equiv> \<nu> f \<le> \<mu> f \<squnion> n(\<nu> f) * top"

definition mu_nu_apx_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_nu f \<equiv> \<mu> f \<squnion> n(\<nu> f) * L \<sqsubseteq> \<nu> f"

definition mu_nu_apx_meet :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_meet f \<equiv> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<mu> f \<triangle> \<nu> f = \<mu> f \<squnion> n(\<nu> f) * L"

definition apx_meet_below_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "apx_meet_below_nu f \<equiv> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<mu> f \<triangle> \<nu> f \<le> \<nu> f"

lemma mu_below_l:
  "\<mu> f \<le> \<mu> f \<squnion> n(\<nu> f) * L"
  by simp

lemma l_below_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> \<mu> f \<squnion> n(\<nu> f) * L \<le> \<nu> f"
  by (simp add: mu_below_nu n_L_decreasing)

lemma n_l_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> n(\<mu> f \<squnion> n(\<nu> f) * L) = n(\<nu> f)"
  by (metis le_iff_sup mu_below_nu n_dist_sup n_n_L)

lemma l_apx_mu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> \<mu> f \<squnion> n(\<nu> f) * L \<sqsubseteq> \<mu> f"
  by (simp add: apx_def le_supI1 n_l_nu)

text \<open>Theorem 17.4 implies Theorem 17.5\<close>

lemma nu_below_mu_nu_mu_nu_apx_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> nu_below_mu_nu f \<Longrightarrow> mu_nu_apx_nu f"
  by (smt (z3) l_below_nu apx_def le_sup_iff sup.absorb2 sup_commute sup_monoid.add_assoc mu_nu_apx_nu_def n_l_nu nu_below_mu_nu_def)

text \<open>Theorem 17.5 implies Theorem 17.6\<close>

lemma mu_nu_apx_nu_mu_nu_apx_meet:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "mu_nu_apx_nu f"
    shows "mu_nu_apx_meet f"
proof -
  let ?l = "\<mu> f \<squnion> n(\<nu> f) * L"
  have "is_apx_meet (\<mu> f) (\<nu> f) ?l"
    apply (unfold is_apx_meet_def, intro conjI)
    apply (simp add: assms(1,2) l_apx_mu)
    using assms(3) mu_nu_apx_nu_def apply blast
    by (meson assms(1,2) l_below_nu apx_def order_trans sup_ge1 sup_left_isotone)
  thus ?thesis
    by (simp add: apx_meet_char mu_nu_apx_meet_def)
qed

text \<open>Theorem 17.6 implies Theorem 17.7\<close>

lemma mu_nu_apx_meet_apx_meet_below_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> mu_nu_apx_meet f \<Longrightarrow> apx_meet_below_nu f"
  using apx_meet_below_nu_def l_below_nu mu_nu_apx_meet_def by auto

text \<open>Theorem 17.7 implies Theorem 17.4\<close>

lemma apx_meet_below_nu_nu_below_mu_nu:
  assumes "apx_meet_below_nu f"
    shows "nu_below_mu_nu f"
proof -
  have "\<forall>m . m \<sqsubseteq> \<mu> f \<and> m \<sqsubseteq> \<nu> f \<and> m \<le> \<nu> f \<longrightarrow> \<nu> f \<le> \<mu> f \<squnion> n(m) * top"
    by (smt (verit) sup_assoc sup_left_isotone sup_right_top apx_def mult_left_dist_sup order_trans)
  thus ?thesis
    by (smt (verit) assms sup_right_isotone apx_greatest_lower_bound apx_meet_below_nu_def apx_reflexive mult_left_isotone n_isotone nu_below_mu_nu_def order_trans)
qed

text \<open>Theorem 17.1 implies Theorem 17.2\<close>

lemma has_apx_least_fixpoint_kappa_apx_meet:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "apx.has_least_fixpoint f"
    shows "kappa_apx_meet f"
proof -
  have "\<forall>w . w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> w \<sqsubseteq> \<kappa> f"
    by (meson assms apx_def order.trans kappa_below_nu mu_below_kappa semiring.add_right_mono)
  hence "is_apx_meet (\<mu> f) (\<nu> f) (\<kappa> f)"
    by (simp add: assms is_apx_meet_def kappa_apx_below_mu kappa_apx_below_nu)
  thus ?thesis
    by (simp add: assms(3) kappa_apx_meet_def apx_meet_char)
qed

text \<open>Theorem 17.2 implies Theorem 17.7\<close>

lemma kappa_apx_meet_apx_meet_below_nu:
  "has_greatest_fixpoint f \<Longrightarrow> kappa_apx_meet f \<Longrightarrow> apx_meet_below_nu f"
  using apx_meet_below_nu_def kappa_apx_meet_def kappa_below_nu by force

text \<open>Theorem 17.7 implies Theorem 17.3\<close>

lemma apx_meet_below_nu_kappa_mu_nu:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "isotone f"
      and "apx.isotone f"
      and "apx_meet_below_nu f"
    shows "kappa_mu_nu f"
proof -
  let ?l = "\<mu> f \<squnion> n(\<nu> f) * L"
  let ?m = "\<mu> f \<triangle> \<nu> f"
  have 1: "?l \<sqsubseteq> \<nu> f"
    using apx_meet_below_nu_nu_below_mu_nu assms(1,2,5) mu_nu_apx_nu_def nu_below_mu_nu_mu_nu_apx_nu by blast
  hence 2: "?m = ?l"
    using assms(1,2) mu_nu_apx_meet_def mu_nu_apx_nu_def mu_nu_apx_nu_mu_nu_apx_meet by blast
  have "\<mu> f \<le> f(?l)"
    by (metis assms(1,3) isotone_def mu_unfold sup_ge1)
  hence 3: "?l \<le> f(?l) \<squnion> n(?l) * L"
    using assms(1,2) semiring.add_right_mono n_l_nu by auto
  have "f(?l) \<le> f(\<nu> f)"
    using assms(1-3) l_below_nu isotone_def by blast
  also have "... \<le> ?l \<squnion> n(?l) * top"
    using 1 by (metis assms(2) apx_def nu_unfold)
  finally have 4: "?l \<sqsubseteq> f(?l)"
    using 3 apx_def by blast
  have 5: "f(?l) \<sqsubseteq> \<mu> f"
    by (metis assms(1,2,4) apx.isotone_def is_least_fixpoint_def least_fixpoint l_apx_mu)
  have "f(?l) \<sqsubseteq> \<nu> f"
    using 1 by (metis assms(2,4) apx.isotone_def greatest_fixpoint is_greatest_fixpoint_def)
  hence "f(?l) \<sqsubseteq> ?l"
    using 2 5 apx_meet_below_nu_def assms(5) apx_greatest_lower_bound by fastforce
  hence "f(?l) = ?l"
    using 4 by (simp add: apx.order.antisym)
  thus ?thesis
    using 1 by (smt (verit, del_insts) assms(1,2) sup_left_isotone apx_antisymmetric apx_def apx.least_fixpoint_char greatest_fixpoint apx.is_least_fixpoint_def is_greatest_fixpoint_def is_least_fixpoint_def least_fixpoint n_l_nu order_trans kappa_mu_nu_def)
qed

text \<open>Theorem 17.3 implies Theorem 17.1\<close>

lemma kappa_mu_nu_has_apx_least_fixpoint:
  "kappa_mu_nu f \<Longrightarrow> apx.has_least_fixpoint f"
  using kappa_mu_nu_def by auto

text \<open>Theorem 17.4 implies Theorem 17.3\<close>

lemma nu_below_mu_nu_kappa_mu_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> isotone f \<Longrightarrow> apx.isotone f \<Longrightarrow> nu_below_mu_nu f \<Longrightarrow> kappa_mu_nu f"
  using apx_meet_below_nu_kappa_mu_nu mu_nu_apx_meet_apx_meet_below_nu mu_nu_apx_nu_mu_nu_apx_meet nu_below_mu_nu_mu_nu_apx_nu by blast

text \<open>Theorem 17.3 implies Theorem 17.4\<close>

lemma kappa_mu_nu_nu_below_mu_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu f \<Longrightarrow> nu_below_mu_nu f"
  by (simp add: apx_meet_below_nu_nu_below_mu_nu has_apx_least_fixpoint_kappa_apx_meet kappa_apx_meet_apx_meet_below_nu kappa_mu_nu_def)

definition kappa_mu_nu_ni :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_mu_nu_ni f \<equiv> apx.has_least_fixpoint f \<and> \<kappa> f = \<mu> f \<squnion> ni(\<nu> f)"

lemma kappa_mu_nu_ni_kappa_mu_nu:
  "kappa_mu_nu_ni f \<longleftrightarrow> kappa_mu_nu f"
  by (simp add: kappa_mu_nu_def kappa_mu_nu_ni_def ni_def)

lemma nu_below_mu_nu_kappa_mu_nu_ni:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> isotone f \<Longrightarrow> apx.isotone f \<Longrightarrow> nu_below_mu_nu f \<Longrightarrow> kappa_mu_nu_ni f"
  by (simp add: kappa_mu_nu_ni_kappa_mu_nu nu_below_mu_nu_kappa_mu_nu)

lemma kappa_mu_nu_ni_nu_below_mu_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu_ni f \<Longrightarrow> nu_below_mu_nu f"
  using kappa_mu_nu_ni_kappa_mu_nu kappa_mu_nu_nu_below_mu_nu by blast

end

class itering_apx = n_itering + semiring_apx
begin

text \<open>Theorem 16.3\<close>

lemma circ_apx_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x\<^sup>\<circ> \<sqsubseteq> y\<^sup>\<circ>"
proof -
  have 1: "x \<le> y \<squnion> n(x) * L \<and> y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  hence "y\<^sup>\<circ> \<le> x\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * n(x) * top"
    by (metis circ_isotone circ_left_top circ_unfold_sum mult_assoc)
  also have "... \<le> x\<^sup>\<circ> \<squnion> n(x\<^sup>\<circ> * x) * top"
    by (smt le_sup_iff n_isotone n_top_split order_refl order_trans right_plus_below_circ zero_right_mult_decreasing)
  also have "... \<le> x\<^sup>\<circ> \<squnion> n(x\<^sup>\<circ>) * top"
    by (simp add: circ_plus_same n_circ_left_unfold)
  finally have 2: "y\<^sup>\<circ> \<le> x\<^sup>\<circ> \<squnion> n(x\<^sup>\<circ>) * top"
    .
  have "x\<^sup>\<circ> \<le> y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * n(x) * L"
    using 1 by (metis L_left_zero circ_isotone circ_unfold_sum mult_assoc)
  also have "... = y\<^sup>\<circ> \<squnion> n(y\<^sup>\<circ> * x) * L"
    by (metis sup_assoc sup_bot_right mult_assoc mult_zero_sup_circ_2 n_L_split n_mult_right_bot)
  also have "... \<le> y\<^sup>\<circ> \<squnion> n(x\<^sup>\<circ> * x) * L \<squnion> n(x\<^sup>\<circ>) * n(top * x) * L"
    using 2 by (metis sup_assoc sup_right_isotone mult_assoc mult_left_isotone mult_right_dist_sup n_dist_sup n_export n_isotone)
  finally have "x\<^sup>\<circ> \<le> y\<^sup>\<circ> \<squnion> n(x\<^sup>\<circ>) * L"
    by (metis sup_assoc circ_plus_same n_sup_left_absorb_mult n_circ_left_unfold n_dist_sup n_export ni_def ni_dist_sup)
  thus ?thesis
    using 2 by (simp add: apx_def)
qed

end

class omega_algebra_apx = n_omega_algebra_2 + semiring_apx

sublocale omega_algebra_apx < star: itering_apx where circ = star ..

sublocale omega_algebra_apx < nL_omega: itering_apx where circ = Omega ..

context omega_algebra_apx
begin

text \<open>Theorem 16.4\<close>

lemma omega_apx_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x\<^sup>\<omega> \<sqsubseteq> y\<^sup>\<omega>"
proof -
  have 1: "x \<le> y \<squnion> n(x) * L \<and> y \<le> x \<squnion> n(x) * top"
    using assms apx_def by auto
  hence "y\<^sup>\<omega> \<le> x\<^sup>\<star> * n(x) * top * (x\<^sup>\<star> * n(x) * top)\<^sup>\<omega> \<squnion> x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * n(x) * top * (x\<^sup>\<star> * n(x) * top)\<^sup>\<star> * x\<^sup>\<omega>"
    by (smt sup_assoc mult_assoc mult_left_one mult_right_dist_sup omega_decompose omega_isotone omega_unfold star_left_unfold_equal)
  also have "... \<le> x\<^sup>\<star> * n(x) * top \<squnion> x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * n(x) * top * (x\<^sup>\<star> * n(x) * top)\<^sup>\<star> * x\<^sup>\<omega>"
    using mult_top_omega omega_unfold sup_left_isotone by auto
  also have "... = x\<^sup>\<star> * n(x) * top \<squnion> x\<^sup>\<omega>"
    by (smt (z3) mult_left_dist_sup sup_assoc sup_commute sup_left_top mult_assoc)
  also have "... \<le> n(x\<^sup>\<star> * x) * top \<squnion> x\<^sup>\<star> * bot \<squnion> x\<^sup>\<omega>"
    using n_top_split semiring.add_left_mono sup_commute by fastforce
  also have "... \<le> n(x\<^sup>\<star> * x) * top \<squnion> x\<^sup>\<omega>"
    using semiring.add_right_mono star_bot_below_omega sup_commute by fastforce
  finally have 2: "y\<^sup>\<omega> \<le> x\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * top"
    by (metis sup_commute sup_right_isotone mult_left_isotone n_star_below_n_omega n_star_left_unfold order_trans star.circ_plus_same)
  have "x\<^sup>\<omega> \<le> (y \<squnion> n(x) * L)\<^sup>\<omega>"
    using 1 by (simp add: omega_isotone)
  also have "... = y\<^sup>\<star> * n(x) * L * (y\<^sup>\<star> * n(x) * L)\<^sup>\<omega> \<squnion> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * n(x) * L * (y\<^sup>\<star> * n(x) * L)\<^sup>\<star> * y\<^sup>\<omega>"
    by (smt sup_assoc mult_assoc mult_left_one mult_right_dist_sup omega_decompose omega_isotone omega_unfold star_left_unfold_equal)
  also have "... = y\<^sup>\<star> * n(x) * L \<squnion> y\<^sup>\<omega>"
    using L_left_zero sup_assoc sup_monoid.add_commute mult_assoc by force
  also have "... \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * bot \<squnion> n(y\<^sup>\<star> * x) * L"
    by (simp add: n_L_split sup_assoc sup_commute)
  also have "... \<le> y\<^sup>\<omega> \<squnion> n(x\<^sup>\<star> * x) * L \<squnion> n(x\<^sup>\<star>) * n(top * x) * L"
    using 1 by (metis sup_right_isotone sup_bot_right apx_def mult_assoc mult_left_dist_sup mult_left_isotone mult_right_dist_sup n_dist_sup n_export n_isotone star.circ_apx_isotone star_mult_omega sup_assoc)
  finally have "x\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> n(x\<^sup>\<omega>) * L"
    by (smt (verit, best) le_supE sup.orderE sup_commute sup_assoc sup_isotone mult_right_dist_sup n_sup_left_absorb_mult n_star_left_unfold ni_def ni_star_below_ni_omega order_refl order_trans star.circ_plus_same)
  thus ?thesis
    using 2 by (simp add: apx_def)
qed

end

class omega_algebra_apx_extra = omega_algebra_apx +
  assumes n_split_omega: "x\<^sup>\<omega> \<le> x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top"
begin

lemma omega_n_star:
  "x\<^sup>\<omega> \<squnion> n(x\<^sup>\<star>) * top \<le> x\<^sup>\<star> * n(x\<^sup>\<omega>) * top"
proof -
  have 1: "n(x\<^sup>\<star>) * top \<le> n(x\<^sup>\<omega>) * top"
    by (simp add: mult_left_isotone n_star_below_n_omega)
  have "... \<le> x\<^sup>\<star> * n(x\<^sup>\<omega>) * top"
    by (simp add: star_n_omega_top)
  thus ?thesis
    using 1 by (metis le_sup_iff n_split_omega order_trans star_n_omega_top)
qed

lemma n_omega_zero:
  "n(x\<^sup>\<omega>) = bot \<longleftrightarrow> n(x\<^sup>\<star>) = bot \<and> x\<^sup>\<omega> \<le> x\<^sup>\<star> * bot"
  by (metis sup_bot_right order.eq_iff mult_left_zero n_mult_bot n_split_omega star_bot_below_omega)

lemma n_split_nu_mu:
  "y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z \<le> y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * top"
proof -
  have "y\<^sup>\<omega> \<le> y\<^sup>\<star> * bot \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * top"
    by (smt sup_ge1 sup_right_isotone mult_left_isotone n_isotone n_split_omega order_trans)
  also have "... \<le> y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * top"
    using nL_star.star_zero_below_circ_mult sup_left_isotone by auto
  finally show ?thesis
    by simp
qed

lemma loop_exists:
  "\<nu> (\<lambda>x . y * x \<squnion> z) \<le> \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> n(\<nu> (\<lambda>x . y * x \<squnion> z)) * top"
  by (metis n_split_nu_mu omega_loop_nu star_loop_mu)

lemma loop_apx_least_fixpoint:
  "apx.is_least_fixpoint (\<lambda>x . y * x \<squnion> z) (\<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> n(\<nu> (\<lambda>x . y * x \<squnion> z)) * L)"
  using apx.least_fixpoint_char affine_apx_isotone affine_has_greatest_fixpoint affine_has_least_fixpoint affine_isotone kappa_mu_nu_def nu_below_mu_nu_def nu_below_mu_nu_kappa_mu_nu loop_exists by auto

lemma loop_has_apx_least_fixpoint:
  "apx.has_least_fixpoint (\<lambda>x . y * x \<squnion> z)"
  using affine_apx_isotone affine_has_greatest_fixpoint affine_has_least_fixpoint affine_isotone kappa_mu_nu_def nu_below_mu_nu_def nu_below_mu_nu_kappa_mu_nu loop_exists by auto

lemma loop_semantics:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> n(\<nu> (\<lambda>x . y * x \<squnion> z)) * L"
  using apx.least_fixpoint_char loop_apx_least_fixpoint by auto

lemma loop_apx_least_fixpoint_ni:
  "apx.is_least_fixpoint (\<lambda>x . y * x \<squnion> z) (\<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> ni(\<nu> (\<lambda>x . y * x \<squnion> z)))"
  using ni_def loop_apx_least_fixpoint by auto

lemma loop_semantics_ni:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> ni(\<nu> (\<lambda>x . y * x \<squnion> z))"
  using ni_def loop_semantics by auto

text \<open>Theorem 18\<close>

lemma loop_semantics_kappa_mu_nu:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z"
proof -
  have "\<kappa> (\<lambda>x . y * x \<squnion> z) = y\<^sup>\<star> * z \<squnion> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * L"
    by (metis loop_semantics omega_loop_nu star_loop_mu)
  thus ?thesis
    by (smt sup_assoc sup_commute le_iff_sup mult_right_dist_sup n_L_decreasing n_dist_sup)
qed

end

class omega_algebra_apx_extra_2 = omega_algebra_apx +
  assumes omega_n_star: "x\<^sup>\<omega> \<le> x\<^sup>\<star> * n(x\<^sup>\<omega>) * top"
begin

subclass omega_algebra_apx_extra
  apply unfold_locales
  using omega_n_star star_n_omega_top by auto

end

end

