(* Title:      Recursion
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Recursion\<close>

theory Recursion

imports Approximation N_Algebras

begin

class n_algebra_apx = n_algebra + apx +
  assumes apx_def: "x \<sqsubseteq> y \<longleftrightarrow> x \<le> y \<squnion> L \<and> C y \<le> x \<squnion> n(x) * top"
begin

lemma apx_transitive_2:
  assumes "x \<sqsubseteq> y"
      and "y \<sqsubseteq> z"
    shows "x \<sqsubseteq> z"
proof -
  have "C z \<le> C (y \<squnion> n(y) * top)"
    using assms(2) apx_def le_inf_iff by blast
  also have "... = C y \<squnion> n(y) * top"
    by (simp add: C_n_mult_closed inf_sup_distrib1)
  also have "... \<le> x \<squnion> n(x) * top \<squnion> n(y) * top"
    using assms(1) apx_def sup_left_isotone by blast
  also have "... = x \<squnion> n(x) * top \<squnion> n(C y) * top"
    by (simp add: n_C)
  also have "... \<le> x \<squnion> n(x) * top"
    by (metis assms(1) sup_assoc sup_idem sup_right_isotone apx_def mult_left_isotone n_add_n_top n_isotone)
  finally show ?thesis
    by (smt assms sup_assoc sup_commute apx_def le_iff_sup)
qed

lemma apx_meet_L:
  assumes "y \<sqsubseteq> x"
    shows "x \<sqinter> L \<le> y \<sqinter> L"
proof -
  have "x \<sqinter> L = C x \<sqinter> L"
    by (simp add: inf.left_commute inf.sup_monoid.add_assoc n_L_top_meet_L)
  also have "... \<le> (y \<squnion> n(y) * top) \<sqinter> L"
    using assms apx_def inf.sup_left_isotone by blast
  also have "... = (y \<sqinter> L) \<squnion> (n(y) * top \<sqinter> L)"
    by (simp add: inf_sup_distrib2)
  also have "... \<le> (y \<sqinter> L) \<squnion> n(y \<sqinter> L) * top"
    using n_n_meet_L sup_right_isotone by force
  finally show ?thesis
    by (metis le_iff_sup inf_le2 n_less_eq_char)
qed

text \<open>AACP Theorem 4.1\<close>

subclass apx_biorder
  apply unfold_locales
  apply (simp add: apx_def inf.coboundedI2)
  apply (metis sup_same_context order.antisym apx_def apx_meet_L relative_equality)
  using apx_transitive_2 by blast

lemma sup_apx_left_isotone_2:
  assumes "x \<sqsubseteq> y"
    shows "x \<squnion> z \<sqsubseteq> y \<squnion> z"
proof -
  have 1: "x \<squnion> z \<le> y \<squnion> z \<squnion> L"
    by (smt assms sup_assoc sup_commute sup_left_isotone apx_def)
  have "C (y \<squnion> z) \<le> x \<squnion> n(x) * top \<squnion> C z"
    using assms apx_def inf_sup_distrib1 sup_left_isotone by auto
  also have "... \<le> x \<squnion> z \<squnion> n(x) * top"
    using inf.coboundedI1 inf.sup_monoid.add_commute sup.cobounded1 sup.cobounded2 sup_assoc sup_least sup_right_isotone by auto
  also have "... \<le> x \<squnion> z \<squnion> n(x \<squnion> z) * top"
    using mult_isotone n_left_upper_bound semiring.add_left_mono by force
  finally show ?thesis
    using 1 apx_def by blast
qed

lemma mult_apx_left_isotone_2:
  assumes "x \<sqsubseteq> y"
    shows "x * z \<sqsubseteq> y * z"
proof -
  have "x * z \<le> y * z \<squnion> L * z"
    by (metis assms apx_def mult_left_isotone mult_right_dist_sup)
  hence 1: "x * z \<le> y * z \<squnion> L"
    using n_L_below_L order_lesseq_imp semiring.add_left_mono by blast
  have "C (y * z) = C y * z"
    by (simp add: n_L_T_meet_mult)
  also have "... \<le> x * z \<squnion> n(x) * top * z"
    by (metis assms apx_def mult_left_isotone mult_right_dist_sup)
  also have "... \<le> x * z \<squnion> n(x * z) * top"
    by (simp add: n_top_split)
  finally show ?thesis
    using 1 by (simp add: apx_def)
qed

lemma mult_apx_right_isotone_2:
  assumes "x \<sqsubseteq> y"
    shows "z * x \<sqsubseteq> z * y"
proof -
  have "z * x \<le> z * y \<squnion> z * L"
    by (metis assms apx_def mult_left_dist_sup mult_right_isotone)
  also have "... \<le> z * y \<squnion> z * bot \<squnion> L"
    using n_L_split_L semiring.add_left_mono sup_assoc by presburger
  finally have 1: "z * x \<le> z * y \<squnion> L"
    using mult_right_isotone sup.absorb_iff1 by auto
  have "C (z * y) \<le> z * C y"
    by (simp add: n_L_T_meet_mult n_L_T_meet_mult_propagate)
  also have "... \<le> z * (x \<squnion> n(x) * top)"
    using assms apx_def mult_right_isotone by blast
  also have "... = z * x \<squnion> z * n(x) * top"
    by (simp add: mult_left_dist_sup mult_assoc)
  also have "... \<le> z * x \<squnion> n(z * x) * top"
    by (simp add: n_split_top)
  finally show ?thesis
    using 1 apx_def by blast
qed

text \<open>AACP Theorem 4.1 and Theorem 4.2\<close>

subclass apx_semiring
  apply unfold_locales
  apply (simp add: apx_def n_L_below_nL_top sup.absorb2)
  using sup_apx_left_isotone_2 apply blast
  using mult_apx_left_isotone_2 apply blast
  by (simp add: mult_apx_right_isotone_2)

text \<open>AACP Theorem 4.2\<close>

lemma meet_L_apx_isotone:
  "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> L \<sqsubseteq> y \<sqinter> L"
  by (smt (verit) apx_meet_L apx_def inf.cobounded2 inf.left_commute n_L_top_meet_L n_less_eq_char sup.absorb2)

text \<open>AACP Theorem 4.2\<close>

lemma n_L_apx_isotone:
  assumes "x \<sqsubseteq> y"
    shows "n(x) * L \<sqsubseteq> n(y) * L"
proof -
  have "C (n(y) * L) \<le> n(C y) * L"
    by (simp add: n_C)
  also have "... \<le> n(x) * L \<squnion> n(n(x) * L) * top"
    by (metis assms apx_def n_add_n_top n_galois n_isotone n_n_L)
  finally show ?thesis
    using apx_def le_inf_iff n_L_decreasing_meet_L sup.absorb2 by auto
qed

definition kappa_apx_meet :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_apx_meet f \<equiv> apx.has_least_fixpoint f \<and> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<kappa> f = \<mu> f \<triangle> \<nu> f"

definition kappa_mu_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_mu_nu f \<equiv> apx.has_least_fixpoint f \<and> \<kappa> f = \<mu> f \<squnion> (\<nu> f \<sqinter> L)"

definition nu_below_mu_nu :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "nu_below_mu_nu f \<equiv> C (\<nu> f) \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<nu> f) * top"

definition nu_below_mu_nu_2 :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "nu_below_mu_nu_2 f \<equiv> C (\<nu> f) \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<mu> f \<squnion> (\<nu> f \<sqinter> L)) * top"

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
  by (meson l_below_nu inf.cobounded1 inf.sup_same_context order_trans sup_ge2)

lemma l_apx_mu:
  "\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<sqsubseteq> \<mu> f"
proof -
  have 1: "\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<le> \<mu> f \<squnion> L"
    using sup_right_isotone by auto
  have "C (\<mu> f) \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<mu> f \<squnion> (\<nu> f \<sqinter> L)) * top"
    by (simp add: le_supI1)
  thus ?thesis
    using 1 apx_def by blast
qed

text \<open>AACP Theorem 4.8 implies Theorem 4.9\<close>

lemma nu_below_mu_nu_nu_below_mu_nu_2:
  assumes "nu_below_mu_nu f"
    shows "nu_below_mu_nu_2 f"
proof -
  have "C (\<nu> f) = C (C (\<nu> f))"
    by auto
  also have "... \<le> C (\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<nu> f) * top)"
    using assms nu_below_mu_nu_def by auto
  also have "... = C (\<mu> f \<squnion> (\<nu> f \<sqinter> L)) \<squnion> C (n(\<nu> f) * top)"
    using inf_sup_distrib1 by auto
  also have "... = C (\<mu> f \<squnion> (\<nu> f \<sqinter> L)) \<squnion> n(\<nu> f) * top"
    by (simp add: C_n_mult_closed)
  also have "... \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<nu> f) * top"
    using inf_le2 sup_left_isotone by blast
  also have "... = \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<nu> f \<sqinter> L) * top"
    using n_n_meet_L by auto
  also have "... \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<mu> f \<squnion> (\<nu> f \<sqinter> L)) * top"
    using mult_isotone n_right_upper_bound semiring.add_left_mono by auto
  finally show ?thesis
    by (simp add: nu_below_mu_nu_2_def)
qed

text \<open>AACP Theorem 4.9 implies Theorem 4.8\<close>

lemma nu_below_mu_nu_2_nu_below_mu_nu:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "nu_below_mu_nu_2 f"
    shows "nu_below_mu_nu f"
proof -
  have "C (\<nu> f) \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<mu> f \<squnion> (\<nu> f \<sqinter> L)) * top"
    using assms(3) nu_below_mu_nu_2_def by blast
  also have "... \<le> \<mu> f \<squnion> (\<nu> f \<sqinter> L) \<squnion> n(\<nu> f) * top"
    by (metis assms(1,2) order.eq_iff n_n_meet_L n_l_nu)
  finally show ?thesis
    using nu_below_mu_nu_def by blast
qed

lemma nu_below_mu_nu_equivalent:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> (nu_below_mu_nu f \<longleftrightarrow> nu_below_mu_nu_2 f)"
  using nu_below_mu_nu_2_nu_below_mu_nu nu_below_mu_nu_nu_below_mu_nu_2 by blast

text \<open>AACP Theorem 4.9 implies Theorem 4.10\<close>

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

text \<open>AACP Theorem 4.10 implies Theorem 4.11\<close>

lemma mu_nu_apx_nu_mu_nu_apx_meet:
  assumes "mu_nu_apx_nu f"
    shows "mu_nu_apx_meet f"
proof -
  let ?l = "\<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  have "is_apx_meet (\<mu> f) (\<nu> f) ?l"
  proof (unfold is_apx_meet_def, intro conjI)
    show "?l \<sqsubseteq> \<mu> f"
      by (simp add: l_apx_mu)
    show "?l \<sqsubseteq> \<nu> f"
      using assms mu_nu_apx_nu_def by blast
    show "\<forall>w. w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> w \<sqsubseteq> ?l"
      by (metis apx_meet_L le_inf_iff sup.absorb1 sup_apx_left_isotone)
  qed
  thus ?thesis
    by (simp add: apx_meet_char mu_nu_apx_meet_def)
qed

text \<open>AACP Theorem 4.11 implies Theorem 4.12\<close>

lemma mu_nu_apx_meet_apx_meet_below_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> mu_nu_apx_meet f \<Longrightarrow> apx_meet_below_nu f"
  using apx_meet_below_nu_def l_below_nu mu_nu_apx_meet_def by auto

text \<open>AACP Theorem 4.12 implies Theorem 4.9\<close>

lemma apx_meet_below_nu_nu_below_mu_nu_2:
  assumes "apx_meet_below_nu f"
    shows "nu_below_mu_nu_2 f"
proof -
  let ?l = "\<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  have "\<forall>m . m \<sqsubseteq> \<mu> f \<and> m \<sqsubseteq> \<nu> f \<and> m \<le> \<nu> f \<longrightarrow> C (\<nu> f) \<le> ?l \<squnion> n(?l) * top"
  proof
    fix m
    show "m \<sqsubseteq> \<mu> f \<and> m \<sqsubseteq> \<nu> f \<and> m \<le> \<nu> f \<longrightarrow> C (\<nu> f) \<le> ?l \<squnion> n(?l) * top"
    proof
      assume 1: "m \<sqsubseteq> \<mu> f \<and> m \<sqsubseteq> \<nu> f \<and> m \<le> \<nu> f"
      hence "m \<le> ?l"
        by (smt (z3) apx_def sup.left_commute sup_inf_distrib1 sup_left_divisibility)
      hence "m \<squnion> n(m) * top \<le> ?l \<squnion> n(?l) * top"
        by (metis sup_mono mult_left_isotone n_isotone)
      thus "C (\<nu> f) \<le> ?l \<squnion> n(?l) * top"
        using 1 apx_def order.trans by blast
    qed
  qed
  thus ?thesis
    by (smt (verit, ccfv_threshold) assms apx_meet_below_nu_def apx_meet_same apx_meet_unique is_apx_meet_def nu_below_mu_nu_2_def)
qed

text \<open>AACP Theorem 4.5 implies Theorem 4.6\<close>

lemma has_apx_least_fixpoint_kappa_apx_meet:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "apx.has_least_fixpoint f"
    shows "kappa_apx_meet f"
proof -
  have 1: "\<forall>w . w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> C (\<kappa> f) \<le> w \<squnion> n(w) * top"
    by (metis assms(2,3) apx_def inf.sup_right_isotone order_trans kappa_below_nu)
  have "\<forall>w . w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> w \<le> \<kappa> f \<squnion> L"
    by (metis assms(1,3) sup_left_isotone apx_def mu_below_kappa order_trans)
  hence "\<forall>w . w \<sqsubseteq> \<mu> f \<and> w \<sqsubseteq> \<nu> f \<longrightarrow> w \<sqsubseteq> \<kappa> f"
    using 1 apx_def by blast
  hence "is_apx_meet (\<mu> f) (\<nu> f) (\<kappa> f)"
    by (simp add: assms is_apx_meet_def kappa_apx_below_mu kappa_apx_below_nu)
  thus ?thesis
    by (simp add: assms(3) kappa_apx_meet_def apx_meet_char)
qed

text \<open>AACP Theorem 4.6 implies Theorem 4.12\<close>

lemma kappa_apx_meet_apx_meet_below_nu:
  "has_greatest_fixpoint f \<Longrightarrow> kappa_apx_meet f \<Longrightarrow> apx_meet_below_nu f"
  using apx_meet_below_nu_def kappa_apx_meet_def kappa_below_nu by force

text \<open>AACP Theorem 4.12 implies Theorem 4.7\<close>

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
      using assms(3) isotone_def sup_ge1 sup_left_isotone by blast
    finally show "?l \<le> f(?l) \<squnion> L"
      .
  qed
  have "C (f(?l)) \<le> ?l \<squnion> n(?l) * top"
  proof -
    have "C (f(?l)) \<le> C (f(\<nu> f))"
      using assms(1-3) l_below_nu inf.sup_right_isotone isotone_def by blast
    also have "... = C (\<nu> f)"
      by (metis assms(2) nu_unfold)
    also have "... \<le> ?l \<squnion> n(?l) * top"
      by (metis assms(5) apx_meet_below_nu_nu_below_mu_nu_2 nu_below_mu_nu_2_def)
    finally show "C (f(?l)) \<le> ?l \<squnion> n(?l) * top"
      .
  qed
  hence 3: "?l \<sqsubseteq> f(?l)"
    using 2 apx_def by blast
  have 4: "f(?l) \<sqsubseteq> \<mu> f"
  proof -
    have "?l \<sqsubseteq> \<mu> f"
      by (simp add: l_apx_mu)
    thus "f(?l) \<sqsubseteq> \<mu> f"
      by (metis assms(1,4) mu_unfold ord.isotone_def)
  qed
  have "f(?l) \<sqsubseteq> \<nu> f"
  proof -
    have "?l \<sqsubseteq> \<nu> f"
      using 1
      by (metis apx_meet_below_nu_def assms(5) apx_meet is_apx_meet_def)
    thus "f(?l) \<sqsubseteq> \<nu> f"
      by (metis assms(2,4) nu_unfold ord.isotone_def)
  qed
  hence "f(?l) \<sqsubseteq> ?l"
    using 1 4 apx_meet_below_nu_def assms(5) apx_meet is_apx_meet_def by fastforce
  hence 5: "f(?l) = ?l"
    using 3 apx.order.antisym by blast
  have "\<forall>y . f(y) = y \<longrightarrow> ?l \<sqsubseteq> y"
  proof
    fix y
    show "f(y) = y \<longrightarrow> ?l \<sqsubseteq> y"
    proof
      assume 6: "f(y) = y"
      hence 7: "?l \<le> y \<squnion> L"
        using assms(1) inf.cobounded2 is_least_fixpoint_def least_fixpoint semiring.add_mono by blast
      have "y \<le> \<nu> f"
        using 6 assms(2) greatest_fixpoint is_greatest_fixpoint_def by auto
      hence "C y \<le> ?l \<squnion> n(?l) * top"
        using assms(5) apx_meet_below_nu_nu_below_mu_nu_2 inf.sup_right_isotone nu_below_mu_nu_2_def order_trans by blast
      thus "?l \<sqsubseteq> y"
        using 7 apx_def by blast
    qed
  qed
  thus ?thesis
    using 5 apx.least_fixpoint_same apx.has_least_fixpoint_def apx.is_least_fixpoint_def kappa_mu_nu_def by auto
qed

text \<open>AACP Theorem 4.7 implies Theorem 4.5\<close>

lemma kappa_mu_nu_has_apx_least_fixpoint:
  "kappa_mu_nu f \<Longrightarrow> apx.has_least_fixpoint f"
  by (simp add: kappa_mu_nu_def)

text \<open>AACP Theorem 4.8 implies Theorem 4.7\<close>

lemma nu_below_mu_nu_kappa_mu_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> isotone f \<Longrightarrow> apx.isotone f \<Longrightarrow> nu_below_mu_nu f \<Longrightarrow> kappa_mu_nu f"
  using apx_meet_below_nu_kappa_mu_nu mu_nu_apx_meet_apx_meet_below_nu mu_nu_apx_nu_mu_nu_apx_meet nu_below_mu_nu_2_mu_nu_apx_nu nu_below_mu_nu_nu_below_mu_nu_2 by blast

text \<open>AACP Theorem 4.7 implies Theorem 4.8\<close>

lemma kappa_mu_nu_nu_below_mu_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu f \<Longrightarrow> nu_below_mu_nu f"
  by (simp add: apx_meet_below_nu_nu_below_mu_nu_2 has_apx_least_fixpoint_kappa_apx_meet kappa_apx_meet_apx_meet_below_nu kappa_mu_nu_has_apx_least_fixpoint nu_below_mu_nu_2_nu_below_mu_nu)

definition kappa_mu_nu_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "kappa_mu_nu_L f \<equiv> apx.has_least_fixpoint f \<and> \<kappa> f = \<mu> f \<squnion> n(\<nu> f) * L"

definition nu_below_mu_nu_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "nu_below_mu_nu_L f \<equiv> C (\<nu> f) \<le> \<mu> f \<squnion> n(\<nu> f) * top"

definition mu_nu_apx_nu_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_nu_L f \<equiv> \<mu> f \<squnion> n(\<nu> f) * L \<sqsubseteq> \<nu> f"

definition mu_nu_apx_meet_L :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "mu_nu_apx_meet_L f \<equiv> has_apx_meet (\<mu> f) (\<nu> f) \<and> \<mu> f \<triangle> \<nu> f = \<mu> f \<squnion> n(\<nu> f) * L"

lemma n_below_l:
  "x \<squnion> n(y) * L \<le> x \<squnion> (y \<sqinter> L)"
  using n_L_decreasing_meet_L semiring.add_left_mono by auto

lemma n_equal_l:
  assumes "nu_below_mu_nu_L f"
    shows "\<mu> f \<squnion> n(\<nu> f) * L = \<mu> f \<squnion> (\<nu> f \<sqinter> L)"
proof -
  have "\<nu> f \<sqinter> L \<le> (\<mu> f \<squnion> n(\<nu> f) * top) \<sqinter> L"
    by (meson assms order.trans inf.boundedI inf.cobounded2 meet_L_below_C nu_below_mu_nu_L_def)
  also have "... \<le> \<mu> f \<squnion> (n(\<nu> f) * top \<sqinter> L)"
    by (simp add: inf.coboundedI2 inf.sup_monoid.add_commute inf_sup_distrib1)
  also have "... \<le> \<mu> f \<squnion> n(\<nu> f) * L"
    by (simp add: n_T_meet_L)
  finally have "\<mu> f \<squnion> (\<nu> f \<sqinter> L) \<le> \<mu> f \<squnion> n(\<nu> f) * L"
    by simp
  thus "\<mu> f \<squnion> n(\<nu> f) * L = \<mu> f \<squnion> (\<nu> f \<sqinter> L)"
    by (meson order.antisym n_below_l)
qed

text \<open>AACP Theorem 4.14 implies Theorem 4.8\<close>

lemma nu_below_mu_nu_L_nu_below_mu_nu:
  "nu_below_mu_nu_L f \<Longrightarrow> nu_below_mu_nu f"
  by (metis sup_assoc sup_right_top mult_left_dist_sup n_equal_l nu_below_mu_nu_L_def nu_below_mu_nu_def)

text \<open>AACP Theorem 4.14 implies Theorem 4.13\<close>

lemma nu_below_mu_nu_L_kappa_mu_nu_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> isotone f \<Longrightarrow> apx.isotone f \<Longrightarrow> nu_below_mu_nu_L f \<Longrightarrow> kappa_mu_nu_L f"
  using kappa_mu_nu_L_def kappa_mu_nu_def n_equal_l nu_below_mu_nu_L_nu_below_mu_nu nu_below_mu_nu_kappa_mu_nu by force

text \<open>AACP Theorem 4.14 implies Theorem 4.15\<close>

lemma nu_below_mu_nu_L_mu_nu_apx_nu_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> nu_below_mu_nu_L f \<Longrightarrow> mu_nu_apx_nu_L f"
  using mu_nu_apx_nu_L_def mu_nu_apx_nu_def n_equal_l nu_below_mu_nu_2_mu_nu_apx_nu nu_below_mu_nu_L_nu_below_mu_nu nu_below_mu_nu_nu_below_mu_nu_2 by auto

text \<open>AACP Theorem 4.14 implies Theorem 4.16\<close>

lemma nu_below_mu_nu_L_mu_nu_apx_meet_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> nu_below_mu_nu_L f \<Longrightarrow> mu_nu_apx_meet_L f"
  using mu_nu_apx_meet_L_def mu_nu_apx_meet_def mu_nu_apx_nu_mu_nu_apx_meet n_equal_l nu_below_mu_nu_2_mu_nu_apx_nu nu_below_mu_nu_L_nu_below_mu_nu nu_below_mu_nu_nu_below_mu_nu_2 by auto

text \<open>AACP Theorem 4.15 implies Theorem 4.14\<close>

lemma mu_nu_apx_nu_L_nu_below_mu_nu_L:
  assumes "has_least_fixpoint f"
      and "has_greatest_fixpoint f"
      and "mu_nu_apx_nu_L f"
    shows "nu_below_mu_nu_L f"
proof -
  let ?n = "\<mu> f \<squnion> n(\<nu> f) * L"
  let ?l = "\<mu> f \<squnion> (\<nu> f \<sqinter> L)"
  have "C (\<nu> f) \<le> ?n \<squnion> n(?n) * top"
    using assms(3) apx_def mu_nu_apx_nu_L_def by blast
  also have "... \<le> ?n \<squnion> n(?l) * top"
    using mult_left_isotone n_L_decreasing_meet_L n_isotone semiring.add_left_mono by auto
  also have "... \<le> ?n \<squnion> n(\<nu> f) * top"
    using assms(1,2) l_below_nu mult_left_isotone n_isotone sup_right_isotone by auto
  finally show ?thesis
    by (metis sup_assoc sup_right_top mult_left_dist_sup nu_below_mu_nu_L_def)
qed

text \<open>AACP Theorem 4.13 implies Theorem 4.15\<close>

lemma kappa_mu_nu_L_mu_nu_apx_nu_L:
  "has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu_L f \<Longrightarrow> mu_nu_apx_nu_L f"
  using kappa_mu_nu_L_def kappa_apx_below_nu mu_nu_apx_nu_L_def by fastforce

text \<open>AACP Theorem 4.16 implies Theorem 4.15\<close>

lemma mu_nu_apx_meet_L_mu_nu_apx_nu_L:
  "mu_nu_apx_meet_L f \<Longrightarrow> mu_nu_apx_nu_L f"
  using apx_meet_char is_apx_meet_def mu_nu_apx_meet_L_def mu_nu_apx_nu_L_def by fastforce

text \<open>AACP Theorem 4.13 implies Theorem 4.14\<close>

lemma kappa_mu_nu_L_nu_below_mu_nu_L:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> kappa_mu_nu_L f \<Longrightarrow> nu_below_mu_nu_L f"
  by (simp add: kappa_mu_nu_L_mu_nu_apx_nu_L mu_nu_apx_nu_L_nu_below_mu_nu_L)

(*
lemma nu_below_mu_nu_nu_below_mu_nu_L: "nu_below_mu_nu f \<longrightarrow> nu_below_mu_nu_L f" nitpick [expect=genuine,card=3] oops
*)

lemma unfold_fold_1:
  "isotone f \<Longrightarrow> has_least_prefixpoint f \<Longrightarrow> apx.has_least_fixpoint f \<Longrightarrow> f(x) \<le> x \<Longrightarrow> \<kappa> f \<le> x \<squnion> L"
  by (metis sup_left_isotone apx_def has_least_fixpoint_def is_least_prefixpoint_def least_prefixpoint_char least_prefixpoint_fixpoint order_trans pmu_mu kappa_apx_below_mu)

lemma unfold_fold_2:
  assumes "isotone f"
      and "apx.isotone f"
      and "has_least_prefixpoint f"
      and "has_greatest_fixpoint f"
      and "apx.has_least_fixpoint f"
      and "f(x) \<le> x"
      and "\<kappa> f \<sqinter> L \<le> x \<sqinter> L"
    shows "\<kappa> f \<le> x"
proof -
  have "\<kappa> f \<sqinter> L = \<nu> f \<sqinter> L"
    by (smt (z3) apx_meet_L assms(4,5) order.eq_iff inf.cobounded1 kappa_apx_below_nu kappa_below_nu le_inf_iff)
  hence "\<kappa> f = (\<kappa> f \<sqinter> L) \<squnion> \<mu> f"
    by (metis assms(1-5) apx_meet_below_nu_kappa_mu_nu has_apx_least_fixpoint_kappa_apx_meet sup_commute least_fixpoint_char least_prefixpoint_fixpoint kappa_apx_meet_apx_meet_below_nu kappa_mu_nu_def)
  thus ?thesis
    by (metis assms(1,3,6,7) sup_least is_least_prefixpoint_def least_prefixpoint le_inf_iff pmu_mu)
qed

end

class n_algebra_apx_2 = n_algebra + apx +
  assumes apx_def: "x \<sqsubseteq> y \<longleftrightarrow> x \<le> y \<squnion> L \<and> y \<le> x \<squnion> n(x) * top"
begin

lemma apx_transitive_2:
  assumes "x \<sqsubseteq> y"
      and "y \<sqsubseteq> z"
    shows "x \<sqsubseteq> z"
proof -
  have "z \<le> y \<squnion> n(y) * top"
    using assms(2) apx_def by auto
  also have "... \<le> x \<squnion> n(x) * top \<squnion> n(y) * top"
    using assms(1) apx_def sup_left_isotone by blast
  also have "... \<le> x \<squnion> n(x) * top"
    by (metis assms(1) sup_assoc sup_idem sup_right_isotone apx_def mult_left_isotone n_add_n_top n_isotone)
  finally show ?thesis
    by (smt assms sup_assoc sup_commute apx_def le_iff_sup)
qed

lemma apx_meet_L:
  assumes "y \<sqsubseteq> x"
    shows "x \<sqinter> L \<le> y \<sqinter> L"
proof -
  have "x \<sqinter> L \<le> (y \<sqinter> L) \<squnion> (n(y) * top \<sqinter> L)"
    by (metis assms apx_def inf.sup_left_isotone inf_sup_distrib2)
  also have "... \<le> (y \<sqinter> L) \<squnion> n(y \<sqinter> L) * top"
    using n_n_meet_L sup_right_isotone by force
  finally show ?thesis
    by (metis le_iff_sup inf_le2 n_less_eq_char)
qed

text \<open>AACP Theorem 4.1\<close>

subclass apx_biorder
  apply unfold_locales
  apply (simp add: apx_def)
  using apx_def order.eq_iff n_less_eq_char apply blast
  using apx_transitive_2 by blast

lemma sup_apx_left_isotone_2:
  assumes "x \<sqsubseteq> y"
    shows "x \<squnion> z \<sqsubseteq> y \<squnion> z"
proof -
  have 1: "x \<squnion> z \<le> y \<squnion> z \<squnion> L"
    by (smt assms sup_assoc sup_commute sup_left_isotone apx_def)
  have "y \<squnion> z \<le> x \<squnion> n(x) * top \<squnion> z"
    using assms apx_def sup_left_isotone by blast
  also have "... \<le> x \<squnion> z \<squnion> n(x \<squnion> z) * top"
    by (metis sup_assoc sup_commute sup_right_isotone mult_left_isotone n_right_upper_bound)
  finally show ?thesis
    using 1 apx_def by auto
qed

lemma mult_apx_left_isotone_2:
  assumes "x \<sqsubseteq> y"
    shows "x * z \<sqsubseteq> y * z"
proof -
  have "x * z \<le> y * z \<squnion> L * z"
    by (metis assms apx_def mult_left_isotone mult_right_dist_sup)
  hence 1: "x * z \<le> y * z \<squnion> L"
    using n_L_below_L order_lesseq_imp semiring.add_left_mono by blast
  have "y * z \<le> x * z \<squnion> n(x) * top * z"
    by (metis assms apx_def mult_left_isotone mult_right_dist_sup)
  also have "... \<le> x * z \<squnion> n(x * z) * top"
    by (simp add: n_top_split)
  finally show ?thesis
    using 1 by (simp add: apx_def)
qed

lemma mult_apx_right_isotone_2:
  assumes "x \<sqsubseteq> y"
    shows "z * x \<sqsubseteq> z * y"
proof -
  have "z * x \<le> z * y \<squnion> z * L"
    by (metis assms apx_def mult_left_dist_sup mult_right_isotone)
  also have "... \<le> z * y \<squnion> z * bot \<squnion> L"
    using n_L_split_L semiring.add_left_mono sup_assoc by auto
  finally have 1: "z * x \<le> z * y \<squnion> L"
    using mult_right_isotone sup.absorb_iff1 by force
  have "z * y \<le> z * (x \<squnion> n(x) * top)"
    using assms apx_def mult_right_isotone by blast
  also have "... = z * x \<squnion> z * n(x) * top"
    by (simp add: mult_left_dist_sup mult_assoc)
  also have "... \<le> z * x \<squnion> n(z * x) * top"
    by (simp add: n_split_top)
  finally show ?thesis
    using 1 by (simp add: apx_def)
qed

end

end

