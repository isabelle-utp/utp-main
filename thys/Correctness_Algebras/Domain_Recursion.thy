(* Title:      Domain Recursion
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Domain Recursion\<close>

theory Domain_Recursion

imports Domain_Iterings Approximation

begin

class domain_semiring_lattice_apx = domain_semiring_lattice_L + apx +
  assumes apx_def: "x \<sqsubseteq> y \<longleftrightarrow> x \<le> y \<squnion> L \<and> d(L) * y \<le> x \<squnion> d(x * bot) * top"
begin

lemma apx_transitive:
  assumes "x \<sqsubseteq> y"
      and "y \<sqsubseteq> z"
    shows "x \<sqsubseteq> z"
proof -
  have 1: "x \<le> z \<squnion> L"
    by (smt assms sup_assoc sup_commute apx_def le_iff_sup)
  have "d(d(L) * y * bot) * top \<le> d((x \<squnion> d(x * bot) * top) * bot) * top"
    by (metis assms(1) apx_def d_isotone mult_left_isotone)
  also have "... \<le> d(x * bot) * top"
    by (metis le_sup_iff d_galois mult_left_isotone mult_right_dist_sup order_refl zero_right_mult_decreasing)
  finally have 2: "d(d(L) * y * bot) * top \<le> d(x * bot) * top"
    .
  have "d(L) * z = d(L) * (d(L) * z)"
    by (simp add: d_idempotent ils.il_inf_associative)
  also have "... \<le> d(L) * y \<squnion> d(d(L) * y * bot) * top"
    by (metis assms(2) apx_def d_export mult_assoc mult_left_dist_sup mult_right_isotone)
  also have "... \<le> x \<squnion> d(x * bot) * top"
    using 2 by (meson assms(1) apx_def le_supI2 sup_least)
  finally show ?thesis
    using 1 by (simp add: apx_def)
qed

lemma apx_meet_L:
  assumes "y \<sqsubseteq> x"
    shows "x \<sqinter> L \<le> y \<sqinter> L"
proof -
  have "x \<sqinter> L = d(L) * x \<sqinter> L"
    using meet_intro_domain by auto
  also have "... \<le> (y \<squnion> d(y * bot) * top) \<sqinter> L"
    using assms apx_def inf.sup_left_isotone by blast
  also have "... \<le> y"
    by (simp add: inf.sup_monoid.add_commute inf_sup_distrib1 l13 meet_domain_top)
  finally show ?thesis
    by simp
qed

lemma sup_apx_left_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x \<squnion> z \<sqsubseteq> y \<squnion> z"
proof -
  have 1: "x \<squnion> z \<le> y \<squnion> z \<squnion> L"
    by (smt assms sup_assoc sup_commute sup_left_isotone apx_def)
  have "d(L) * (y \<squnion> z) = d(L) * y \<squnion> d(L) * z"
    by (simp add: mult_left_dist_sup)
  also have "... \<le> d(L) * y \<squnion> z"
    by (simp add: d_mult_below le_supI1 sup_commute)
  also have "... \<le> x \<squnion> d(x * bot) * top \<squnion> z"
    using assms apx_def sup_left_isotone by blast
  also have "... \<le> x \<squnion> z \<squnion> d((x \<squnion> z) * bot) * top"
    by (simp add: d_dist_sup le_iff_sup semiring.distrib_right sup.left_commute sup_monoid.add_assoc)
  finally show ?thesis
    using 1 by (simp add: apx_def)
qed

subclass apx_biorder
  apply unfold_locales
  apply (metis le_sup_iff sup_ge1 apx_def d_plus_one mult_left_one mult_right_dist_sup)
  apply (meson apx_meet_L order.antisym apx_def relative_equality sup_same_context)
  using apx_transitive by blast

lemma mult_apx_left_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x * z \<sqsubseteq> y * z"
proof -
  have "x * z \<le> y * z \<squnion> L * z"
    by (metis assms apx_def mult_left_isotone mult_right_dist_sup)
  hence 1: "x * z \<le> y * z \<squnion> L"
    using l40 order_lesseq_imp semiring.add_left_mono by blast
  have "d(L) * y * z \<le> x * z \<squnion> d(x * bot) * top * z"
    by (metis assms apx_def mult_left_isotone mult_right_dist_sup)
  also have "... \<le> x * z \<squnion> d(x * z * bot) * top"
    by (metis sup_right_isotone d_isotone mult_assoc mult_isotone mult_right_isotone top_greatest bot_least)
  finally show ?thesis
    using 1 by (simp add: apx_def mult_assoc)
qed

lemma mult_apx_right_isotone:
  assumes "x \<sqsubseteq> y"
    shows "z * x \<sqsubseteq> z * y"
proof -
  have "z * x \<le> z * y \<squnion> z * L"
    by (metis assms apx_def mult_left_dist_sup mult_right_isotone)
  also have "... \<le> z * y \<squnion> z * bot \<squnion> L"
    using l14 semiring.add_left_mono sup_monoid.add_assoc by auto
  finally have 1: "z * x \<le> z * y \<squnion> L"
    using mult_right_isotone sup.order_iff by auto
  have "d(L) * z * y \<le> z * d(L) * y"
    by (simp add: l2 mult_left_isotone)
  also have "... \<le> z * (x \<squnion> d(x * bot) * top)"
    by (metis assms apx_def mult_assoc mult_right_isotone)
  also have "... = z * x \<squnion> z * d(x * bot) * top"
    by (simp add: mult_left_dist_sup mult_assoc)
  also have "... \<le> z * x \<squnion> d(z * x * bot) * top"
    by (metis sup_right_isotone mult_assoc mult_domain_top)
  finally show ?thesis
    using 1 by (simp add: apx_def mult_assoc)
qed

subclass apx_semiring
  apply unfold_locales
  apply (metis sup_ge2 apx_def l3 mult_right_isotone order_trans top_greatest)
  apply (simp add: sup_apx_left_isotone)
  apply (simp add: mult_apx_left_isotone)
  by (simp add: mult_apx_right_isotone)

lemma meet_L_apx_isotone:
  "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> L \<sqsubseteq> y \<sqinter> L"
  by (smt (z3) inf.cobounded2 sup.coboundedI1 sup_absorb sup_commute apx_def apx_meet_L d_restrict_equals l20 inf_commute meet_domain)

definition kappa_apx_meet :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_apx_meet f \<equiv> apx.has_least_fixpoint f \<and> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<kappa> f = \<mu> f \<triangle> \<nu> f"

definition kappa_mu_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_mu_nu f \<equiv> apx.has_least_fixpoint f \<and> \<kappa> f = \<mu> f \<squnion> (\<nu> f \<sqinter> L)"

definition nu_below_mu_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "nu_below_mu_nu f \<equiv> d(L) * \<nu> f \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d(\<nu> f * bot) * top"

definition nu_below_mu_nu_2 :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "nu_below_mu_nu_2 f \<equiv> d(L) * \<nu> f \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d((\<mu> f \<squnion> (\<nu> f \<sqinter> L)) * bot) * top"

definition mu_nu_apx_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_nu f \<equiv> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<sqsubseteq> \<nu> f"

definition mu_nu_apx_meet :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_meet f \<equiv> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<mu> f \<triangle> \<nu> f = \<mu> f \<squnion> (\<nu> f \<sqinter> L)"

definition apx_meet_below_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "apx_meet_below_nu f \<equiv> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<mu> f \<triangle> \<nu> f \<le> \<nu> f"

lemma mu_below_l:
  "\<mu> f \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  by simp

lemma l_below_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<le> \<nu> f"
  by (simp add: mu_below_nu)

lemma n_l_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> (\<mu> f \<squnion> (\<nu> f \<sqinter> L)) \<sqinter> L = \<nu> f \<sqinter> L"
  by (meson l_below_nu inf.sup_same_context inf_le1 order_trans sup.cobounded2)

lemma l_apx_mu:
  "\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<sqsubseteq> \<mu> f"
  by (simp add: apx_def d_mult_below le_supI1 sup_inf_distrib1)

lemma nu_below_mu_nu_nu_below_mu_nu_2:
  assumes "nu_below_mu_nu f"
    shows "nu_below_mu_nu_2 f"
proof -
  have "d(L) * \<nu> f = d(L) * (d(L) * \<nu> f)"
    by (simp add: d_idempotent ils.il_inf_associative)
  also have "... \<le> d(L) * (\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d(\<nu> f * bot) * top)"
    using assms mult_isotone nu_below_mu_nu_def by blast
  also have "... = d(L) * (\<mu> f \<squnion> (\<nu> f \<sqinter> L)) \<squnion> d(L) * d(\<nu> f * bot) * top"
    by (simp add: ils.il_inf_associative mult_left_dist_sup)
  also have "... \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d(L) * d(\<nu> f * bot) * top"
    using d_mult_below sup_left_isotone by auto
  also have "... = \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d(d(\<nu> f * bot) * L) * top"
    by (simp add: d_commutative d_export)
  also have "... = \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d((\<nu> f \<sqinter> L) * bot) * top"
    using l51 by auto
  also have "... \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d((\<mu> f \<squnion> (\<nu> f \<sqinter> L)) * bot) * top"
    by (meson d_isotone inf.eq_refl mult_isotone semiring.add_left_mono sup.cobounded2)
  finally show ?thesis
    using nu_below_mu_nu_2_def by auto
qed

lemma nu_below_mu_nu_2_nu_below_mu_nu:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "nu_below_mu_nu_2 f"
    shows "nu_below_mu_nu f"
proof -
  have "d(L) * \<nu> f \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d((\<mu> f \<squnion> (\<nu> f \<sqinter> L)) * bot) * top"
    using assms(3) nu_below_mu_nu_2_def by blast
  also have "... \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> d(\<nu> f * bot) * top"
    by (metis assms(1,2) d_isotone inf.sup_monoid.add_commute inf.sup_right_divisibility le_supI le_supI2 mu_below_nu mult_left_isotone sup_left_divisibility)
  finally show ?thesis
    by (simp add: nu_below_mu_nu_def)
qed

lemma nu_below_mu_nu_equivalent:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> (nu_below_mu_nu f \<longleftrightarrow> nu_below_mu_nu_2 f)"
  using nu_below_mu_nu_2_nu_below_mu_nu nu_below_mu_nu_nu_below_mu_nu_2 by blast

lemma nu_below_mu_nu_2_mu_nu_apx_nu:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "nu_below_mu_nu_2 f"
    shows "mu_nu_apx_nu f"
proof -
  have "\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<le> \<nu> f \<squnion> L"
    using assms(1,2) l_below_nu le_supI1 by blast
  thus ?thesis
    using assms(3) apx_def mu_nu_apx_nu_def nu_below_mu_nu_2_def by blast
qed

lemma mu_nu_apx_nu_mu_nu_apx_meet:
  assumes "mu_nu_apx_nu f"
    shows "mu_nu_apx_meet f"
proof -
  let ?l = "\<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  have "is_apx_meet (\<mu> f) (\<nu> f) ?l"
    apply (unfold is_apx_meet_def, intro conjI)
    apply (simp add: l_apx_mu)
    using assms mu_nu_apx_nu_def apply blast
    by (metis apx_meet_L le_supI2 sup.order_iff sup_apx_left_isotone sup_inf_absorb)
  thus ?thesis
    by (smt apx_meet_char mu_nu_apx_meet_def)
qed

lemma mu_nu_apx_meet_apx_meet_below_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> mu_nu_apx_meet f \<Longrightarrow> apx_meet_below_nu f"
  using apx_meet_below_nu_def l_below_nu mu_nu_apx_meet_def by auto

lemma apx_meet_below_nu_nu_below_mu_nu_2:
  assumes "apx_meet_below_nu f"
    shows "nu_below_mu_nu_2 f"
proof -
  let ?l = "\<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  have "\<forall>m . m \<sqsubseteq> \<mu> f \<and> m \<sqsubseteq> \<nu> f \<and> m \<le> \<nu> f \<longrightarrow> d(L) * \<nu> f \<le> ?l \<squnion> d(?l * bot) * top"
  proof
    fix m
    show "m \<sqsubseteq> \<mu> f \<and> m \<sqsubseteq> \<nu> f \<and> m \<le> \<nu> f \<longrightarrow> d(L) * \<nu> f \<le> ?l \<squnion> d(?l * bot) * top"
    proof
      assume 1: "m \<sqsubseteq> \<mu> f \<and> m \<sqsubseteq> \<nu> f \<and> m \<le> \<nu> f"
      hence "m \<le> ?l"
        by (metis apx_def ils.il_associative sup.orderE sup.orderI sup_inf_distrib1 sup_inf_distrib2)
      hence "m \<squnion> d(m * bot) * top \<le> ?l \<squnion> d(?l * bot) * top"
        by (meson d_isotone order.trans le_supI le_supI2 mult_left_isotone sup.cobounded1)
      thus "d(L) * \<nu> f \<le> ?l \<squnion> d(?l * bot) * top"
        using 1 apx_def order_lesseq_imp by blast
    qed
  qed
  thus ?thesis
    by (smt (verit) assms apx_meet_below_nu_def apx_meet_same apx_meet_unique is_apx_meet_def nu_below_mu_nu_2_def)
qed

lemma has_apx_least_fixpoint_kappa_apx_meet:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "apx.has_least_fixpoint f"
    shows "kappa_apx_meet f"
proof -
  have 1: "\<forall>w . w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> d(L) * \<kappa> f \<le> w \<squnion> d(w * bot) * top"
    by (metis assms(2,3) apx_def mult_right_isotone order_trans kappa_below_nu)
  have "\<forall>w . w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> w \<le> \<kappa> f \<squnion> L"
    by (metis assms(1,3) sup_left_isotone apx_def mu_below_kappa order_trans)
  hence "\<forall>w . w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> w \<sqsubseteq> \<kappa> f"
    using 1 apx_def by blast
  hence "is_apx_meet (\<mu> f) (\<nu> f) (\<kappa> f)"
    using assms apx_meet_char is_apx_meet_def kappa_apx_below_mu kappa_apx_below_nu kappa_apx_meet_def by presburger
  thus ?thesis
    by (simp add: assms(3) kappa_apx_meet_def apx_meet_char)
qed

lemma kappa_apx_meet_apx_meet_below_nu:
  "has_greatest_fixpoint f \<Longrightarrow> kappa_apx_meet f \<Longrightarrow> apx_meet_below_nu f"
  using apx_meet_below_nu_def kappa_apx_meet_def kappa_below_nu by force

lemma apx_meet_below_nu_kappa_mu_nu:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "isotone f"
      and "apx.isotone f"
      and "apx_meet_below_nu f"
    shows "kappa_mu_nu f"
proof -
  let ?l = "\<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  let ?m = "\<mu> f \<triangle> \<nu> f"
  have 1: "?m = ?l"
    by (metis assms(1,2,5) apx_meet_below_nu_nu_below_mu_nu_2 mu_nu_apx_meet_def mu_nu_apx_nu_mu_nu_apx_meet nu_below_mu_nu_2_mu_nu_apx_nu)
  have 2: "?l \<le> f(?l) \<squnion> L"
  proof -
    have "?l \<le> \<mu> f \<squnion> L"
      using sup_right_isotone by auto
    also have "... = f(\<mu> f) \<squnion> L"
      by (simp add: assms(1) mu_unfold)
    also have "... \<le> f(?l) \<squnion> L"
      by (metis assms(3) sup_left_isotone sup_ge1 isotone_def)
    finally show ?thesis
      .
  qed
  have "d(L) * f(?l) \<le> ?l \<squnion> d(?l * bot) * top"
  proof -
    have "d(L) * f(?l) \<le> d(L) * f(\<nu> f)"
      by (metis assms(1-3) l_below_nu mult_right_isotone ord.isotone_def)
    also have "... = d(L) * \<nu> f"
      by (metis assms(2) nu_unfold)
    also have "... \<le> ?l \<squnion> d(?l * bot) * top"
      using apx_meet_below_nu_nu_below_mu_nu_2 assms(5) nu_below_mu_nu_2_def by blast
    finally show ?thesis
      .
  qed
  hence 3: "?l \<sqsubseteq> f(?l)"
    using 2 by (simp add: apx_def)
  have 4: "f(?l) \<sqsubseteq> \<mu> f"
  proof -
    have "?l \<sqsubseteq> \<mu> f"
      by (simp add: l_apx_mu)
    thus ?thesis
      by (metis assms(1,4) mu_unfold ord.isotone_def)
  qed
  have 5: "f(?l) \<sqsubseteq> \<nu> f"
  proof -
    have "?l \<sqsubseteq> \<nu> f"
      by (meson apx_meet_below_nu_nu_below_mu_nu_2 assms(1,2,5) l_below_nu apx_def le_supI1 nu_below_mu_nu_2_def)
    thus ?thesis
      by (metis assms(2,4) nu_unfold ord.isotone_def)
  qed
  hence "f(?l) \<sqsubseteq> ?l"
    using 1 4 apx_meet_below_nu_def assms(5) apx_greatest_lower_bound by fastforce
  hence 6: "f(?l) = ?l"
    using 3 apx.order.antisym by blast
  have "\<forall>y . f(y) = y \<longrightarrow> ?l \<sqsubseteq> y"
  proof
    fix y
    show "f(y) = y \<longrightarrow> ?l \<sqsubseteq> y"
    proof
      assume 7: "f(y) = y"
      hence 8: "?l \<le> y \<squnion> L"
        using assms(1) inf.cobounded2 is_least_fixpoint_def least_fixpoint semiring.add_mono by blast
      have "y \<le> \<nu> f"
        using 7 assms(2) greatest_fixpoint is_greatest_fixpoint_def by auto
      hence "d(L) * y \<le> ?l \<squnion> d(?l * bot) * top"
        using 3 5 by (smt (z3) apx.order.trans apx_def semiring.distrib_left sup.absorb_iff2 sup_assoc)
      thus "?l \<sqsubseteq> y"
        using 8 by (simp add: apx_def)
    qed
  qed
  thus ?thesis
    using 1 6 by (smt (verit) kappa_mu_nu_def apx.is_least_fixpoint_def apx.least_fixpoint_char)
qed

lemma kappa_mu_nu_has_apx_least_fixpoint:
  "kappa_mu_nu f \<Longrightarrow> apx.has_least_fixpoint f"
  by (simp add: kappa_mu_nu_def)

lemma nu_below_mu_nu_kappa_mu_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> isotone f \<Longrightarrow> apx.isotone f \<Longrightarrow> nu_below_mu_nu f \<Longrightarrow> kappa_mu_nu f"
  using apx_meet_below_nu_kappa_mu_nu mu_nu_apx_meet_apx_meet_below_nu mu_nu_apx_nu_mu_nu_apx_meet nu_below_mu_nu_2_mu_nu_apx_nu nu_below_mu_nu_nu_below_mu_nu_2 by blast

lemma kappa_mu_nu_nu_below_mu_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu f \<Longrightarrow> nu_below_mu_nu f"
  by (simp add: apx_meet_below_nu_nu_below_mu_nu_2 has_apx_least_fixpoint_kappa_apx_meet kappa_apx_meet_apx_meet_below_nu kappa_mu_nu_def nu_below_mu_nu_2_nu_below_mu_nu)

definition kappa_mu_nu_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_mu_nu_L f \<equiv> apx.has_least_fixpoint f \<and> \<kappa> f = \<mu> f \<squnion> d(\<nu> f * bot) * L"

definition nu_below_mu_nu_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "nu_below_mu_nu_L f \<equiv> d(L) * \<nu> f \<le> \<mu> f \<squnion> d(\<nu> f * bot) * top"

definition mu_nu_apx_nu_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_nu_L f \<equiv> \<mu> f \<squnion> d(\<nu> f * bot) * L \<sqsubseteq> \<nu> f"

definition mu_nu_apx_meet_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_meet_L f \<equiv> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<mu> f \<triangle> \<nu> f = \<mu> f \<squnion> d(\<nu> f * bot) * L"

lemma n_below_l:
  "x \<squnion> d(y * bot) * L \<le> x \<squnion> (y \<sqinter> L)"
  using d_mult_below l13 sup_right_isotone by auto

lemma n_equal_l:
  assumes "nu_below_mu_nu_L f"
    shows"\<mu> f \<squnion> d(\<nu> f * bot) * L = \<mu> f \<squnion> (\<nu> f \<sqinter> L)"
proof -
  have "\<nu> f \<sqinter> L \<le> (\<mu> f \<squnion> d(\<nu> f * bot) * top) \<sqinter> L"
    using assms l31 nu_below_mu_nu_L_def by force
  also have "... \<le> \<mu> f \<squnion> d(\<nu> f * bot) * L"
    using distrib(4) inf.sup_monoid.add_commute meet_domain_top sup_left_isotone by force
  finally have "\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<le> \<mu> f \<squnion> d(\<nu> f * bot) * L"
    by auto
  thus ?thesis
    by (meson order.antisym n_below_l)
qed

lemma nu_below_mu_nu_L_nu_below_mu_nu:
  "nu_below_mu_nu_L f \<Longrightarrow> nu_below_mu_nu f"
  using order_lesseq_imp sup.cobounded1 sup_left_isotone nu_below_mu_nu_L_def nu_below_mu_nu_def by blast

lemma nu_below_mu_nu_L_kappa_mu_nu_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> isotone f \<Longrightarrow> apx.isotone f \<Longrightarrow> nu_below_mu_nu_L f \<Longrightarrow> kappa_mu_nu_L f"
  using kappa_mu_nu_L_def kappa_mu_nu_def n_equal_l nu_below_mu_nu_L_nu_below_mu_nu nu_below_mu_nu_kappa_mu_nu by auto

lemma nu_below_mu_nu_L_mu_nu_apx_nu_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> nu_below_mu_nu_L f \<Longrightarrow> mu_nu_apx_nu_L f"
  using mu_nu_apx_nu_L_def mu_nu_apx_nu_def n_equal_l nu_below_mu_nu_2_mu_nu_apx_nu nu_below_mu_nu_L_nu_below_mu_nu nu_below_mu_nu_nu_below_mu_nu_2 by auto

lemma nu_below_mu_nu_L_mu_nu_apx_meet_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> nu_below_mu_nu_L f \<Longrightarrow> mu_nu_apx_meet_L f"
  using mu_nu_apx_meet_L_def mu_nu_apx_meet_def mu_nu_apx_nu_mu_nu_apx_meet n_equal_l nu_below_mu_nu_2_mu_nu_apx_nu nu_below_mu_nu_L_nu_below_mu_nu nu_below_mu_nu_nu_below_mu_nu_2 by auto

lemma mu_nu_apx_nu_L_nu_below_mu_nu_L:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "mu_nu_apx_nu_L f"
    shows "nu_below_mu_nu_L f"
proof -
  let ?n = "\<mu> f \<squnion> d(\<nu> f * bot) * L"
  let ?l = "\<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  have "d(L) * \<nu> f \<le> ?n \<squnion> d(?n * bot) * top"
    using assms(3) apx_def mu_nu_apx_nu_L_def by blast
  also have "... \<le> ?n \<squnion> d(?l * bot) * top"
    using d_isotone mult_left_isotone semiring.add_left_mono n_below_l by auto
  also have "... \<le> ?n \<squnion> d(\<nu> f * bot) * top"
    by (meson assms(1,2) l_below_nu d_isotone mult_left_isotone sup_right_isotone)
  finally show ?thesis
    by (metis sup_assoc sup_right_top mult_left_dist_sup nu_below_mu_nu_L_def)
qed

lemma kappa_mu_nu_L_mu_nu_apx_nu_L:
  "has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu_L f \<Longrightarrow> mu_nu_apx_nu_L f"
  using kappa_mu_nu_L_def kappa_apx_below_nu mu_nu_apx_nu_L_def by force

lemma mu_nu_apx_meet_L_mu_nu_apx_nu_L:
  "mu_nu_apx_meet_L f \<Longrightarrow> mu_nu_apx_nu_L f"
  using apx_greatest_lower_bound mu_nu_apx_meet_L_def mu_nu_apx_nu_L_def by fastforce

lemma kappa_mu_nu_L_nu_below_mu_nu_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu_L f \<Longrightarrow> nu_below_mu_nu_L f"
  using kappa_mu_nu_L_mu_nu_apx_nu_L mu_nu_apx_nu_L_nu_below_mu_nu_L by auto

end

class itering_apx = domain_itering_lattice_L + domain_semiring_lattice_apx
begin

lemma circ_apx_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x\<^sup>\<circ> \<sqsubseteq> y\<^sup>\<circ>"
proof -
  have 1: "x \<le> y \<squnion> L \<and> d(L) * y \<le> x \<squnion> d(x * bot) * top"
    using assms apx_def by auto
  have "d(L) * y\<^sup>\<circ> \<le> (d(L) * y)\<^sup>\<circ>"
    by (metis d_circ_import d_mult_below l2)
  also have "... \<le> x\<^sup>\<circ> * (d(x * bot) * top * x\<^sup>\<circ>)\<^sup>\<circ>"
    using 1 by (metis circ_sup_1 circ_isotone)
  also have "... = x\<^sup>\<circ> \<squnion> x\<^sup>\<circ> * d(x * bot) * top"
    by (metis circ_left_top mult_assoc mult_left_dist_sup mult_1_right mult_top_circ)
  also have "... \<le> x\<^sup>\<circ> \<squnion> d(x\<^sup>\<circ> * x * bot) * top"
    by (metis sup_right_isotone mult_assoc mult_domain_top)
  finally have 2: "d(L) * y\<^sup>\<circ> \<le> x\<^sup>\<circ> \<squnion> d(x\<^sup>\<circ> * bot) * top"
    using circ_plus_same d0_circ_left_unfold by auto
  have "x\<^sup>\<circ> \<le> y\<^sup>\<circ> * L\<^sup>\<circ>"
    using 1 by (metis circ_sup_1 circ_back_loop_fixpoint circ_isotone l40 le_iff_sup mult_assoc)
  also have "... = y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * L"
    by (simp add: circ_L mult_left_dist_sup sup_commute)
  also have "... \<le> y\<^sup>\<circ> \<squnion> y\<^sup>\<circ> * bot \<squnion> L"
    using l14 semiring.add_left_mono sup_monoid.add_assoc by auto
  finally have "x\<^sup>\<circ> \<le> y\<^sup>\<circ> \<squnion> L"
    using sup.absorb_iff1 zero_right_mult_decreasing by auto
  thus ?thesis
    using 2 by (simp add: apx_def)
qed

end

class omega_algebra_apx = domain_omega_algebra_lattice_L + domain_semiring_lattice_apx

sublocale omega_algebra_apx < star: itering_apx where circ = star ..

context omega_algebra_apx
begin

lemma omega_apx_isotone:
  assumes "x \<sqsubseteq> y"
    shows "x\<^sup>\<omega> \<sqsubseteq> y\<^sup>\<omega>"
proof -
  have 1: "x \<le> y \<squnion> L \<and> d(L) * y \<le> x \<squnion> d(x * bot) * top"
    using assms apx_def by auto
  have "d(L) * y\<^sup>\<omega> = (d(L) * y)\<^sup>\<omega>"
    by (simp add: d_omega_export l2)
  also have "... \<le> (x \<squnion> d(x * bot) * top)\<^sup>\<omega>"
    using 1 by (simp add: omega_isotone)
  also have "... = (x\<^sup>\<star> * d(x * bot) * top)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * d(x * bot) * top)\<^sup>\<star> * x\<^sup>\<omega>"
    by (simp add: ils.il_inf_associative omega_decompose)
  also have "... \<le> x\<^sup>\<star> * d(x * bot) * top \<squnion> (x\<^sup>\<star> * d(x * bot) * top)\<^sup>\<star> * x\<^sup>\<omega>"
    using mult_top_omega sup_left_isotone by blast
  also have "... = x\<^sup>\<star> * d(x * bot) * top \<squnion> (1 \<squnion> x\<^sup>\<star> * d(x * bot) * top * (x\<^sup>\<star> * d(x * bot) * top)\<^sup>\<star>) * x\<^sup>\<omega>"
    by (simp add: star_left_unfold_equal)
  also have "... \<le> x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * d(x * bot) * top"
    by (smt (verit, ccfv_threshold) sup_mono le_sup_iff mult_assoc mult_left_one mult_right_dist_sup mult_right_isotone order_refl top_greatest)
  also have "... \<le> x\<^sup>\<omega> \<squnion> d(x\<^sup>\<star> * x * bot) * top"
    by (metis sup_right_isotone mult_assoc mult_domain_top)
  also have "... \<le> x\<^sup>\<omega> \<squnion> d(x\<^sup>\<star> * bot) * top"
    by (simp add: dL_star.d0_circ_left_unfold star_plus)
  finally have 2: "d(L) * y\<^sup>\<omega> \<le> x\<^sup>\<omega> \<squnion> d(x\<^sup>\<omega> * bot) * top"
    by (meson sup_right_isotone d0_star_below_d0_omega mult_left_isotone order_trans)
  have "x\<^sup>\<omega> \<le> (y \<squnion> L)\<^sup>\<omega>"
    using 1 by (simp add: omega_isotone)
  also have "... = (y\<^sup>\<star> * L)\<^sup>\<omega> \<squnion> (y\<^sup>\<star> * L)\<^sup>\<star> * y\<^sup>\<omega>"
    by (simp add: omega_decompose)
  also have "... = y\<^sup>\<star> * L * (y\<^sup>\<star> * L)\<^sup>\<omega> \<squnion> (y\<^sup>\<star> * L)\<^sup>\<star> * y\<^sup>\<omega>"
    using omega_unfold by auto
  also have "... \<le> y\<^sup>\<star> * L \<squnion> (y\<^sup>\<star> * L)\<^sup>\<star> * y\<^sup>\<omega>"
    using mult_L_omega omega_unfold sup_left_isotone by auto
  also have "... = y\<^sup>\<star> * L \<squnion> (1 \<squnion> y\<^sup>\<star> * L * (y\<^sup>\<star> * L)\<^sup>\<star>) * y\<^sup>\<omega>"
    by (simp add: star_left_unfold_equal)
  also have "... \<le> y\<^sup>\<star> * L \<squnion> y\<^sup>\<omega>"
    by (simp add: dL_star.mult_L_circ_mult_below star_left_unfold_equal sup_commute)
  also have "... \<le> y\<^sup>\<star> * bot \<squnion> L \<squnion> y\<^sup>\<omega>"
    by (simp add: l14 le_supI1)
  finally have "x\<^sup>\<omega> \<le> y\<^sup>\<omega> \<squnion> L"
    using star_bot_below_omega sup.left_commute sup.order_iff sup_commute by auto
  thus ?thesis
    using 2 by (simp add: apx_def)
qed

lemma combined_apx_isotone:
  "x \<sqsubseteq> y \<Longrightarrow> (x\<^sup>\<omega> \<sqinter> L) \<squnion> x\<^sup>\<star> * z \<sqsubseteq> (y\<^sup>\<omega> \<sqinter> L) \<squnion> y\<^sup>\<star> * z"
  using meet_L_apx_isotone mult_apx_left_isotone star.circ_apx_isotone sup_apx_isotone omega_apx_isotone by auto

lemma d_split_nu_mu:
  "d(L) * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<le> y\<^sup>\<star> * z \<squnion> ((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<sqinter> L) \<squnion> d((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * bot) * top"
proof -
  have "d(L) * y\<^sup>\<omega> \<le> (y\<^sup>\<omega> \<sqinter> L) \<squnion> d(y\<^sup>\<omega> * bot) * top"
    using l31 l91 omega_vector sup_right_isotone by auto
  hence "d(L) * (y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<le> y\<^sup>\<star> * z \<squnion> (y\<^sup>\<omega> \<sqinter> L) \<squnion> d(y\<^sup>\<omega> * bot) * top"
    by (smt sup_assoc sup_commute sup_mono d_mult_below mult_left_dist_sup)
  also have "... \<le> y\<^sup>\<star> * z \<squnion> ((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<sqinter> L) \<squnion> d(y\<^sup>\<omega> * bot) * top"
    by (simp add: le_supI1 le_supI2)
  also have "... \<le> y\<^sup>\<star> * z \<squnion> ((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<sqinter> L) \<squnion> d((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) * bot) * top"
    by (meson d_isotone mult_left_isotone sup.cobounded1 sup_right_isotone)
  finally show ?thesis
    .
qed

lemma loop_exists:
  "d(L) * \<nu> (\<lambda>x . y * x \<squnion> z) \<le> \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> (\<nu> (\<lambda>x . y * x \<squnion> z) \<sqinter> L) \<squnion> d(\<nu> (\<lambda>x . y * x \<squnion> z) * bot) * top"
  by (simp add: d_split_nu_mu omega_loop_nu star_loop_mu)

lemma loop_apx_least_fixpoint:
  "apx.is_least_fixpoint (\<lambda>x . y * x \<squnion> z) (\<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> (\<nu> (\<lambda>x . y * x \<squnion> z) \<sqinter> L))"
  using apx.least_fixpoint_char affine_apx_isotone loop_exists affine_has_greatest_fixpoint affine_has_least_fixpoint affine_isotone nu_below_mu_nu_def nu_below_mu_nu_kappa_mu_nu kappa_mu_nu_def by auto

lemma loop_has_apx_least_fixpoint:
  "apx.has_least_fixpoint (\<lambda>x . y * x \<squnion> z)"
  by (metis apx.has_least_fixpoint_def loop_apx_least_fixpoint)

lemma loop_semantics:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = \<mu> (\<lambda>x . y * x \<squnion> z) \<squnion> (\<nu> (\<lambda>x . y * x \<squnion> z) \<sqinter> L)"
  using apx.least_fixpoint_char loop_apx_least_fixpoint by auto

lemma loop_semantics_kappa_mu_nu:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = (y\<^sup>\<omega> \<sqinter> L) \<squnion> y\<^sup>\<star> * z"
proof -
  have "\<kappa> (\<lambda>x . y * x \<squnion> z) = y\<^sup>\<star> * z \<squnion> ((y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z) \<sqinter> L)"
    by (metis loop_semantics omega_loop_nu star_loop_mu)
  thus ?thesis
    by (metis sup.absorb2 sup_commute sup_ge2 sup_inf_distrib1)
qed

lemma loop_semantics_kappa_mu_nu_domain:
  "\<kappa> (\<lambda>x . y * x \<squnion> z) = d(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z"
  by (simp add: omega_meet_L loop_semantics_kappa_mu_nu)

lemma loop_semantics_apx_isotone:
  "w \<sqsubseteq> y \<Longrightarrow> \<kappa> (\<lambda>x . w * x \<squnion> z) \<sqsubseteq> \<kappa> (\<lambda>x . y * x \<squnion> z)"
  by (metis loop_semantics_kappa_mu_nu combined_apx_isotone)

end

end

