(* Title:      Monotonic Boolean Transformers
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Monotonic Boolean Transformers\<close>

theory Monotonic_Boolean_Transformers

imports MonoBoolTranAlgebra.Assertion_Algebra Base

begin

no_notation inf (infixl "\<sqinter>" 70)
no_notation uminus ("- _" [81] 80)

context mbt_algebra
begin

lemma directed_left_mult:
  "directed Y \<Longrightarrow> directed ((*) x ` Y)"
  apply (unfold directed_def)
  using le_comp by blast

lemma neg_assertion:
  "neg_assert x \<in> assertion"
  by (metis bot_comp neg_assert_def wpt_def wpt_is_assertion mult_assoc)

lemma assertion_neg_assert:
  "x \<in> assertion \<longleftrightarrow> x = neg_assert (neg_assert x)"
  by (metis neg_assertion uminus_uminus)

text \<open>extend and dualise part of Viorel Preoteasa's theory\<close>

definition "assumption \<equiv> {x . 1 \<le> x \<and> (x * bot) \<squnion> (x ^ o) = x}"

definition "neg_assume (x::'a) \<equiv> (x ^ o * top) \<squnion> 1"

lemma neg_assume_assert:
  "neg_assume x = (neg_assert (x ^ o)) ^ o"
  using dual_bot dual_comp dual_dual dual_inf dual_one neg_assert_def neg_assume_def by auto

lemma assert_iff_assume:
  "x \<in> assertion \<longleftrightarrow> x ^ o \<in> assumption"
  by (smt assertion_def assumption_def dual_bot dual_comp dual_dual dual_inf dual_le dual_one mem_Collect_eq)

lemma assertion_iff_assumption_subseteq:
  "X \<subseteq> assertion \<longleftrightarrow> dual ` X \<subseteq> assumption"
  using assert_iff_assume by blast

lemma assumption_iff_assertion_subseteq:
  "X \<subseteq> assumption \<longleftrightarrow> dual ` X \<subseteq> assertion"
  using assert_iff_assume by auto

lemma assumption_prop:
  "x \<in> assumption \<Longrightarrow> (x * bot) \<squnion> 1 = x"
  by (smt assert_iff_assume assertion_prop dual_comp dual_dual dual_neg_top dual_one dual_sup dual_top)

lemma neg_assumption:
  "neg_assume x \<in> assumption"
  using assert_iff_assume neg_assertion neg_assume_assert by auto

lemma assumption_neg_assume:
  "x \<in> assumption \<longleftrightarrow> x = neg_assume (neg_assume x)"
  by (smt assert_iff_assume assertion_neg_assert dual_dual neg_assume_assert)

lemma assumption_sup_comp_eq:
  "x \<in> assumption \<Longrightarrow> y \<in> assumption \<Longrightarrow> x \<squnion> y = x * y"
  by (smt assert_iff_assume assertion_inf_comp_eq dual_comp dual_dual dual_sup)

lemma sup_uminus_assume[simp]:
  "x \<in> assumption \<Longrightarrow> x \<sqinter> neg_assume x = 1"
  by (smt assert_iff_assume dual_dual dual_one dual_sup neg_assume_assert sup_uminus)

lemma inf_uminus_assume[simp]:
  "x \<in> assumption \<Longrightarrow> x \<squnion> neg_assume x = top"
  by (smt assert_iff_assume dual_dual dual_sup dual_top inf_uminus neg_assume_assert sup_bot_right)

lemma uminus_assumption[simp]:
  "x \<in> assumption \<Longrightarrow> neg_assume x \<in> assumption"
  by (simp add: neg_assumption)

lemma uminus_uminus_assume[simp]:
  "x \<in> assumption \<Longrightarrow> neg_assume (neg_assume x) = x"
  by (simp add: assumption_neg_assume)

lemma sup_assumption[simp]:
  "x \<in> assumption \<Longrightarrow> y \<in> assumption \<Longrightarrow> x \<squnion> y \<in> assumption"
  by (smt assert_iff_assume dual_dual dual_sup inf_assertion)

lemma comp_assumption[simp]:
  "x \<in> assumption \<Longrightarrow> y \<in> assumption \<Longrightarrow> x * y \<in> assumption"
  using assumption_sup_comp_eq sup_assumption by auto

lemma inf_assumption[simp]:
  "x \<in> assumption \<Longrightarrow> y \<in> assumption \<Longrightarrow> x \<sqinter> y \<in> assumption"
  by (smt assert_iff_assume dual_dual dual_inf sup_assertion)

lemma assumption_comp_idempotent[simp]:
  "x \<in> assumption \<Longrightarrow> x * x = x"
  using assumption_sup_comp_eq by fastforce

lemma assumption_comp_idempotent_dual[simp]:
  "x \<in> assumption \<Longrightarrow> (x ^ o) * (x ^ o) = x ^ o"
  by (metis assumption_comp_idempotent dual_comp)

lemma top_assumption[simp]:
  "top \<in> assumption"
  by (simp add: assumption_def)

lemma one_assumption[simp]:
  "1 \<in> assumption"
  by (simp add: assumption_def)

lemma assert_top:
  "neg_assert (neg_assert p) ^ o * bot = neg_assert p * top"
  by (smt bot_comp dual_comp dual_dual dual_top inf_comp inf_top_right mult.assoc mult.left_neutral neg_assert_def)

lemma assume_bot:
  "neg_assume (neg_assume p) ^ o * top = neg_assume p * bot"
  by (smt assert_top dual_bot dual_comp dual_dual neg_assume_assert)

definition "wpb x \<equiv> (x * bot) \<squnion> 1"

lemma wpt_iff_wpb:
  "wpb x = wpt (x ^ o) ^ o"
  using dual_comp dual_dual dual_inf dual_one dual_top wpt_def wpb_def by auto

lemma wpb_is_assumption[simp]:
  "wpb x \<in> assumption"
  using assert_iff_assume wpt_is_assertion wpt_iff_wpb by auto

lemma wpb_comp:
  "(wpb x) * x = x"
  by (smt dual_comp dual_dual dual_neg_top dual_sup wpt_comp wpt_iff_wpb)

lemma wpb_comp_2:
  "wpb (x * y) = wpb (x * (wpb y))"
  by (simp add: sup_comp mult_assoc wpb_def)

lemma wpb_assumption[simp]:
  "x \<in> assumption \<Longrightarrow> wpb x = x"
  by (simp add: assumption_prop wpb_def)

lemma wpb_choice:
  "wpb (x \<squnion> y) = wpb x \<squnion> wpb y"
  using sup_assoc sup_commute sup_comp wpb_def by auto

lemma wpb_dual_assumption:
  "x \<in> assumption \<Longrightarrow> wpb (x ^ o) = 1"
  by (smt assert_iff_assume dual_dual dual_one wpt_dual_assertion wpt_iff_wpb)

lemma wpb_mono:
  "x \<le> y \<Longrightarrow> wpb x \<le> wpb y"
  by (metis le_iff_sup wpb_choice)

lemma assumption_disjunctive:
  "x \<in> assumption \<Longrightarrow> x \<in> disjunctive"
  by (smt assert_iff_assume assertion_conjunctive dual_comp dual_conjunctive dual_dual)

lemma assumption_conjunctive:
  "x \<in> assumption \<Longrightarrow> x \<in> conjunctive"
  by (smt assert_iff_assume assertion_disjunctive dual_comp dual_disjunctive dual_dual)

lemma wpb_le_assumption:
  "x \<in> assumption \<Longrightarrow> x * y = y \<Longrightarrow> x \<le> wpb y"
  by (metis assumption_prop bot_least le_comp sup_commute sup_right_isotone mult_assoc wpb_def)

definition dual_omega :: "'a \<Rightarrow> 'a" ("(_ ^ \<mho>)" [81] 80)
  where "(x ^ \<mho>) \<equiv> (((x ^ o) ^ \<omega>) ^ o)"

lemma dual_omega_fix:
  "x^\<mho> = (x * (x^\<mho>)) \<squnion> 1"
  by (smt dual_comp dual_dual dual_omega_def dual_one dual_sup omega_fix)

lemma dual_omega_comp_fix:
  "x^\<mho> * y = (x * (x^\<mho>) * y) \<squnion> y"
  by (metis dual_omega_fix mult_1_left sup_comp)

lemma dual_omega_greatest:
  "z \<le> (x * z) \<squnion> y \<Longrightarrow> z \<le> (x^\<mho>) * y"
  by (smt dual_comp dual_dual dual_le dual_neg_top dual_omega_def dual_sup omega_least)

end

context post_mbt_algebra
begin

lemma post_antitone:
  assumes "x \<le> y"
    shows "post y \<le> post x"
proof -
  have "post y \<le> post x * y * top \<sqinter> post y"
    by (metis assms inf_top_left post_1 inf_mono le_comp_left_right order_refl)
  thus ?thesis
    using order_lesseq_imp post_2 by blast
qed

lemma post_assumption_below_one:
  "q \<in> assumption \<Longrightarrow> post q \<le> post 1"
  by (simp add: assumption_def post_antitone)

lemma post_assumption_above_one:
  "q \<in> assumption \<Longrightarrow> post 1 \<le> post (q ^ o)"
  by (metis dual_le dual_one post_antitone sup.commute sup_ge1 wpb_assumption wpb_def)

lemma post_assumption_below_dual:
  "q \<in> assumption \<Longrightarrow> post q \<le> post (q ^ o)"
  using order_trans post_assumption_above_one post_assumption_below_one by blast

lemma assumption_assertion_absorb:
  "q \<in> assumption \<Longrightarrow> q * (q ^ o) = q"
  by (smt CollectE assumption_def assumption_prop bot_comp mult.left_neutral mult_assoc sup_comp)

lemma post_dual_below_post_one:
  assumes "q \<in> assumption"
  shows "post (q ^ o) \<le> post 1 * q"
proof -
  have "post (q ^ o) \<le> post 1 * q * (q ^ o) * top \<sqinter> post (q ^ o)"
    by (metis assms assumption_assertion_absorb gt_one_comp inf_le1 inf_top_left mult_assoc order_refl post_1 sup_uminus_assume top_unique)
  thus ?thesis
    using order_lesseq_imp post_2 by blast
qed

lemma post_below_post_one:
  "q \<in> assumption \<Longrightarrow> post q \<le> post 1 * q"
  using order.trans post_assumption_below_dual post_dual_below_post_one by blast

end

context complete_mbt_algebra
begin

lemma Inf_assumption[simp]:
  "X \<subseteq> assumption \<Longrightarrow> Inf X \<in> assumption"
  by (metis Sup_assertion assert_iff_assume assumption_iff_assertion_subseteq dual_Inf dual_dual)

definition "continuous x \<equiv> (\<forall>Y . directed Y \<longrightarrow> x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y))"

definition "Continuous \<equiv> { x . continuous x }"

lemma continuous_Continuous:
  "continuous x \<longleftrightarrow> x \<in> Continuous"
  by (simp add: Continuous_def)

text \<open>Theorem 53.1\<close>

lemma one_continuous:
  "1 \<in> Continuous"
  by (simp add: Continuous_def continuous_def image_def)

lemma continuous_dist_ascending_chain:
  assumes "x \<in> Continuous"
      and "ascending_chain f"
    shows "x * (SUP n::nat . f n) = (SUP n::nat . x * f n)"
proof -
  have "directed (range f)"
    by (simp add: assms(2) ascending_chain_directed)
  hence "x * (SUP n::nat . f n) = (SUP y\<in>range f . x * y)"
    using assms(1) continuous_Continuous continuous_def by auto
  thus ?thesis
    by (simp add: range_composition)
qed

text \<open>Theorem 53.1\<close>

lemma assertion_continuous:
  assumes "x \<in> assertion"
    shows "x \<in> Continuous"
proof -
  have 1: "x = (x * top) \<sqinter> 1"
    using assms assertion_prop by auto
  have "\<forall>Y . directed Y \<longrightarrow> x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y)"
  proof (rule allI, rule impI)
    fix Y
    assume "directed Y" (* assumption not used *)
    have "x * (SUP y\<in>Y . y) = (x * top) \<sqinter> (SUP y\<in>Y . y)"
      using 1 by (smt inf_comp mult.assoc mult.left_neutral top_comp)
    also have "... = (SUP y\<in>Y . (x * top) \<sqinter> y)"
      by (simp add: inf_Sup)
    finally show "x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y)"
      using 1 by (smt inf_comp mult.left_neutral mult.assoc top_comp SUP_cong)
  qed
  thus ?thesis
    by (simp add: continuous_def Continuous_def)
qed

text \<open>Theorem 53.1\<close>

lemma assumption_continuous:
  assumes "x \<in> assumption"
    shows "x \<in> Continuous"
proof -
  have 1: "x = (x * bot) \<squnion> 1"
    by (simp add: assms assumption_prop)
  have "\<forall>Y . directed Y \<longrightarrow> x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y)"
  proof (rule allI, rule impI)
    fix Y
    assume 2: "directed Y"
    have "x * (SUP y\<in>Y . y) = (x * bot) \<squnion> (SUP y\<in>Y . y)"
      using 1 by (smt sup_comp mult.assoc mult.left_neutral bot_comp)
    also have "... = (SUP y\<in>Y . (x * bot) \<squnion> y)"
      using 2 by (smt (verit, ccfv_threshold) sup_SUP SUP_cong directed_def)
    finally show "x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y)"
      using 1 by (metis sup_comp mult.left_neutral mult.assoc bot_comp SUP_cong)
  qed
  thus ?thesis
    by (simp add: continuous_def Continuous_def)
qed

text \<open>Theorem 53.1\<close>

lemma mult_continuous:
  assumes "x \<in> Continuous"
      and "y \<in> Continuous"
    shows "x * y \<in> Continuous"
proof -
  have "\<forall>Y. directed Y \<longrightarrow> x * y * (SUP y\<in>Y . y) = (SUP z\<in>Y . x * y * z)"
  proof (rule allI, rule impI)
    fix Y
    assume "directed Y"
    hence "x * y * (SUP w\<in>Y . w) = (SUP z\<in>Y . x * (y * z))"
      by (metis assms continuous_Continuous continuous_def directed_left_mult image_ident image_image mult_assoc)
    thus "x * y * (SUP y\<in>Y . y) = (SUP z\<in>Y . x * y * z)"
      using mult_assoc by auto
  qed
  thus ?thesis
    using Continuous_def continuous_def by blast
qed

text \<open>Theorem 53.1\<close>

lemma sup_continuous:
  "x \<in> Continuous \<Longrightarrow> y \<in> Continuous \<Longrightarrow> x \<squnion> y \<in> Continuous"
  by (smt SUP_cong SUP_sup_distrib continuous_Continuous continuous_def sup_comp)

text \<open>Theorem 53.1\<close>

lemma inf_continuous:
  assumes "x \<in> Continuous"
      and "y \<in> Continuous"
    shows "x \<sqinter> y \<in> Continuous"
proof -
  have "\<forall>Y. directed Y \<longrightarrow> (x \<sqinter> y) * (SUP y\<in>Y . y) = (SUP z\<in>Y . (x \<sqinter> y) * z)"
  proof (rule allI, rule impI)
    fix Y
    assume 1: "directed Y"
    have 2: "(SUP w\<in>Y . SUP z\<in>Y . (x * w) \<sqinter> (y * z)) \<le> (SUP z\<in>Y . (x * z) \<sqinter> (y * z))"
    proof (intro SUP_least)
      fix w z
      assume "w \<in> Y" and "z \<in> Y"
      from this obtain v where 3: "v\<in>Y \<and> w \<le> v \<and> z \<le> v"
        using 1 by (meson directed_def)
      hence "x * w \<sqinter> (y * z) \<le> (x * v) \<sqinter> (y * v)"
        by (meson inf.sup_mono le_comp)
      thus "x * w \<sqinter> (y * z) \<le> (SUP z\<in>Y . (x * z) \<sqinter> (y * z))"
        using 3 by (meson SUP_upper2)
    qed
    have "(SUP z\<in>Y . (x * z) \<sqinter> (y * z)) \<le> (SUP w\<in>Y . SUP z\<in>Y . (x * w) \<sqinter> (y * z))"
      apply (rule SUP_least)
      by (meson SUP_upper SUP_upper2)
    hence "(SUP w\<in>Y . SUP z\<in>Y . (x * w) \<sqinter> (y * z)) = (SUP z\<in>Y . (x \<sqinter> y) * z)"
      using 2 order.antisym inf_comp by auto
    thus "(x \<sqinter> y) * (SUP y\<in>Y . y) = (SUP z\<in>Y . (x \<sqinter> y) * z)"
      using 1 by (metis assms inf_comp continuous_Continuous continuous_def SUP_inf_distrib2)
  qed
  thus ?thesis
    using Continuous_def continuous_def by blast
qed

text \<open>Theorem 53.1\<close>

lemma dual_star_continuous:
  assumes "x \<in> Continuous"
    shows "x ^ \<otimes> \<in> Continuous"
proof -
  have "\<forall>Y. directed Y \<longrightarrow> (x ^ \<otimes>) * (SUP y\<in>Y . y) = (SUP z\<in>Y . (x ^ \<otimes>) * z)"
  proof (rule allI, rule impI)
    fix Y
    assume "directed Y"
    hence "directed ((*) (x ^ \<otimes>) ` Y)"
      by (simp add: directed_left_mult)
    hence "x * (SUP y\<in>Y . (x ^ \<otimes>) * y) = (SUP y\<in>Y . x * ((x ^ \<otimes>) * y))"
      by (metis assms continuous_Continuous continuous_def image_ident image_image)
    also have "... = (SUP y\<in>Y . x * (x ^ \<otimes>) * y)"
      using mult_assoc by auto
    also have "... \<le> (SUP y\<in>Y . (x ^ \<otimes>) * y)"
      apply (rule SUP_least)
      by (simp add: SUP_upper2 dual_star_comp_fix)
    finally have "x * (SUP y\<in>Y . (x ^ \<otimes>) * y) \<squnion> (SUP y\<in>Y . y) \<le> (SUP y\<in>Y . (x ^ \<otimes>) * y)"
      apply (rule sup_least)
      by (metis SUP_mono' dual_star_comp_fix sup.cobounded1 sup_commute)
    thus "(x ^ \<otimes>) * (SUP y\<in>Y . y) = (SUP z\<in>Y . (x ^ \<otimes>) * z)"
      by (meson SUP_least SUP_upper order.antisym dual_star_least le_comp)
  qed
  thus ?thesis
    using Continuous_def continuous_def by blast
qed

text \<open>Theorem 53.1\<close>

lemma omega_continuous:
  assumes "x \<in> Continuous"
    shows "x ^ \<omega> \<in> Continuous"
proof -
  have "\<forall>Y. directed Y \<longrightarrow> (x ^ \<omega>) * (SUP y\<in>Y . y) = (SUP z\<in>Y . (x ^ \<omega>) * z)"
  proof (rule allI, rule impI)
    fix Y
    assume 1: "directed Y"
    hence "directed ((*) (x ^ \<omega>) ` Y)"
      using directed_left_mult by auto
    hence "x * (SUP y\<in>Y . (x ^ \<omega>) * y) = (SUP y\<in>Y . x * ((x ^ \<omega>) * y))"
      by (metis assms continuous_Continuous continuous_def image_ident image_image)
    hence 2: "x * (SUP y\<in>Y . (x ^ \<omega>) * y) = (SUP y\<in>Y . x * (x ^ \<omega>) * y)"
      by (simp add: mult_assoc)
    have "(SUP y\<in>Y . x * (x ^ \<omega>) * y) \<sqinter> (SUP y\<in>Y . y) = (SUP w\<in>Y . SUP z\<in>Y . (x * (x ^ \<omega>) * w) \<sqinter> z)"
      using SUP_inf_distrib2 by blast
    hence "x * (SUP y\<in>Y . (x ^ \<omega>) * y) \<sqinter> (SUP y\<in>Y . y) = (SUP w\<in>Y . SUP z\<in>Y . (x * (x ^ \<omega>) * w) \<sqinter> z)"
      using 2 by auto
    also have "... \<le> (SUP y\<in>Y . (x ^ \<omega>) * y)"
    proof (intro SUP_least)
      fix w z
      assume "w \<in> Y" and "z \<in> Y"
      from this obtain v where 3: "v\<in>Y \<and> w \<le> v \<and> z \<le> v"
        using 1 by (meson directed_def)
      hence "x * x ^ \<omega> * w \<sqinter> z \<le> x ^ \<omega> * v"
        using inf.sup_mono le_comp omega_comp_fix by auto
      thus "x * x ^ \<omega> * w \<sqinter> z \<le> (SUP y\<in>Y . (x ^ \<omega>) * y)"
        using 3 by (meson SUP_upper2)
    qed
    finally show "(x ^ \<omega>) * (SUP y\<in>Y . y) = (SUP z\<in>Y . (x ^ \<omega>) * z)"
      by (meson SUP_least SUP_upper order.antisym omega_least le_comp)
  qed
  thus ?thesis
    using Continuous_def continuous_def by blast
qed

definition "co_continuous x \<equiv> (\<forall>Y . co_directed Y \<longrightarrow> x * (INF y\<in>Y . y) = (INF y\<in>Y . x * y))"

definition "Co_continuous \<equiv> { x . co_continuous x }"

lemma directed_dual:
  "directed X \<longleftrightarrow> co_directed (dual ` X)"
  by (simp add: directed_def co_directed_def dual_le[THEN sym])

lemma dual_dual_image:
  "dual ` dual ` X = X"
  by (simp add: image_comp)

lemma continuous_dual:
  "continuous x \<longleftrightarrow> co_continuous (x ^ o)"
proof (unfold continuous_def co_continuous_def, rule iffI)
  assume 1: "\<forall>Y. directed Y \<longrightarrow> x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y)"
  show "\<forall>Y. co_directed Y \<longrightarrow> x ^ o * (INF y\<in>Y . y) = (INF y\<in>Y . x ^ o * y)"
  proof (rule allI, rule impI)
    fix Y
    assume "co_directed Y"
    hence "x ^ o * (INF y\<in>Y . y) = (INF y\<in>(dual ` Y) . (x * y) ^ o)"
      using 1 by (metis dual_dual_image dual_SUP image_ident image_image dual_comp directed_dual)
    also have "... = (INF y\<in>(dual ` Y) . x ^ o * y ^ o)"
      by (meson dual_comp)
    also have "... = (INF y\<in>Y . x ^ o * y)"
      by (simp add: image_image)
    finally show "x ^ o * (INF y\<in>Y . y) = (INF y\<in>Y . x ^ o * y)"
      .
 qed
next
  assume 2: "\<forall>Y. co_directed Y \<longrightarrow> x ^ o * (INF y\<in>Y . y) = (INF y\<in>Y . x ^ o * y)"
  show "\<forall>Y. directed Y \<longrightarrow> x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y)"
  proof (rule allI, rule impI)
    fix Y
    assume "directed Y"
    hence "x * (SUP y\<in>Y . y) = (SUP y\<in>(dual ` Y) . (x ^ o * y) ^ o)"
      using 2 by (metis directed_dual dual_dual_image image_ident image_image dual_SUP dual_comp dual_dual)
    also have "... = (SUP y\<in>(dual ` Y) . x * y ^ o)"
      using dual_comp dual_dual by auto
    also have "... = (SUP y\<in>Y . x * y)"
      by (simp add: image_image)
    finally show "x * (SUP y\<in>Y . y) = (SUP y\<in>Y . x * y)"
      .
 qed
qed

lemma co_continuous_Co_continuous:
  "co_continuous x \<longleftrightarrow> x \<in> Co_continuous"
  by (simp add: Co_continuous_def)

text \<open>Theorem 53.1 and Theorem 53.2\<close>

lemma Continuous_dual:
  "x \<in> Continuous \<longleftrightarrow> x ^ o \<in> Co_continuous"
  by (simp add: Co_continuous_def Continuous_def continuous_dual)

text \<open>Theorem 53.2\<close>

lemma one_co_continuous:
  "1 \<in> Co_continuous"
  using Continuous_dual one_continuous by auto

lemma ascending_chain_dual:
  "ascending_chain f \<longleftrightarrow> descending_chain (dual o f)"
  using ascending_chain_def descending_chain_def dual_le by auto

lemma co_continuous_dist_descending_chain:
  assumes "x \<in> Co_continuous"
      and "descending_chain f"
    shows "x * (INF n::nat . f n) = (INF n::nat . x * f n)"
proof -
  have "x ^ o * (SUP n::nat . (dual o f) n) = (SUP n::nat . x ^ o * (dual o f) n)"
    by (smt assms Continuous_dual SUP_cong ascending_chain_dual continuous_dist_ascending_chain descending_chain_def dual_dual o_def)
  thus ?thesis
    by (smt INF_cong dual_SUP dual_comp dual_dual o_def)
qed

text \<open>Theorem 53.2\<close>

lemma assertion_co_continuous:
  "x \<in> assertion \<Longrightarrow> x \<in> Co_continuous"
  by (smt Continuous_dual assert_iff_assume assumption_continuous dual_dual)

text \<open>Theorem 53.2\<close>

lemma assumption_co_continuous:
  "x \<in> assumption \<Longrightarrow> x \<in> Co_continuous"
  by (smt Continuous_dual assert_iff_assume assertion_continuous dual_dual)

text \<open>Theorem 53.2\<close>

lemma mult_co_continuous:
  "x \<in> Co_continuous \<Longrightarrow> y \<in> Co_continuous \<Longrightarrow> x * y \<in> Co_continuous"
  by (smt Continuous_dual dual_comp dual_dual mult_continuous)

text \<open>Theorem 53.2\<close>

lemma sup_co_continuous:
  "x \<in> Co_continuous \<Longrightarrow> y \<in> Co_continuous \<Longrightarrow> x \<squnion> y \<in> Co_continuous"
  by (smt Continuous_dual dual_sup dual_dual inf_continuous)

text \<open>Theorem 53.2\<close>

lemma inf_co_continuous:
  "x \<in> Co_continuous \<Longrightarrow> y \<in> Co_continuous \<Longrightarrow> x \<sqinter> y \<in> Co_continuous"
  by (smt Continuous_dual dual_inf dual_dual sup_continuous)

text \<open>Theorem 53.2\<close>

lemma dual_omega_co_continuous:
  "x \<in> Co_continuous \<Longrightarrow> x ^ \<mho> \<in> Co_continuous"
  by (smt Continuous_dual dual_omega_def dual_dual omega_continuous)

text \<open>Theorem 53.2\<close>

lemma star_co_continuous:
  "x \<in> Co_continuous \<Longrightarrow> x ^ * \<in> Co_continuous"
  by (smt Continuous_dual dual_star_def dual_dual dual_star_continuous)

lemma dual_omega_iterate:
  assumes "y \<in> Co_continuous"
    shows "y ^ \<mho> * z = (INF n::nat . ((\<lambda>x . y * x \<squnion> z) ^ n) top)"
proof (rule order.antisym)
  show "y ^ \<mho> * z \<le> (INF n::nat . ((\<lambda>x . y * x \<squnion> z) ^ n) top)"
  proof (rule INF_greatest)
    fix n
    show "y ^ \<mho> * z \<le> ((\<lambda>x. y * x \<squnion> z) ^ n) top"
      apply (induct n)
      apply (metis power_zero_id id_def top_greatest)
      by (smt dual_omega_comp_fix le_comp mult_assoc order_refl sup_mono power_succ_unfold_ext)
  qed
next
  have 1: "descending_chain (\<lambda>n . ((\<lambda>x. y * x \<squnion> z) ^ n) top)"
  proof (unfold descending_chain_def, rule allI)
    fix n
    show "((\<lambda>x. y * x \<squnion> z) ^ Suc n) top \<le> ((\<lambda>x. y * x \<squnion> z) ^ n) top"
      apply (induct n)
      apply (metis power_zero_id id_def top_greatest)
      by (smt power_succ_unfold_ext sup_mono order_refl le_comp)
  qed
  have "(INF n. ((\<lambda>x. y * x \<squnion> z) ^ n) top) \<le> (INF n. ((\<lambda>x. y * x \<squnion> z) ^ Suc n) top)"
    apply (rule INF_greatest)
    apply (unfold power_succ_unfold_ext)
    by (smt power_succ_unfold_ext INF_lower UNIV_I)
  thus "(INF n. ((\<lambda>x. y * x \<squnion> z) ^ n) top) \<le> y ^ \<mho> * z"
    using 1 by (smt assms INF_cong co_continuous_dist_descending_chain power_succ_unfold_ext sup_INF sup_commute dual_omega_greatest)
qed

lemma dual_omega_iterate_one:
  "y \<in> Co_continuous \<Longrightarrow> y ^ \<mho> = (INF n::nat . ((\<lambda>x . y * x \<squnion> 1) ^ n) top)"
  by (metis dual_omega_iterate mult.right_neutral)

subclass ccpo
  apply unfold_locales
  apply (simp add: Sup_upper)
  using Sup_least by auto

end

class post_mbt_algebra_ext = post_mbt_algebra +
  assumes post_sub_fusion: "post 1 * neg_assume q \<le> post (neg_assume q ^ o)"
begin

lemma post_fusion:
  "post (neg_assume q ^ o) = post 1 * neg_assume q"
  using order.antisym neg_assumption post_dual_below_post_one post_sub_fusion by auto

lemma post_dual_post_one:
  "q \<in> assumption \<Longrightarrow> post 1 * q \<le> post (q ^ o)"
  by (metis assumption_neg_assume post_sub_fusion)

end

instance MonoTran :: (complete_boolean_algebra) post_mbt_algebra_ext
proof
  fix q :: "'a MonoTran"
  show "post 1 * neg_assume q \<le> post (neg_assume q ^ o)"
  proof (unfold neg_assume_def, transfer)
    fix f :: "'a \<Rightarrow> 'a"
    assume "mono f"
    have "\<forall>x. top \<le> -f bot \<squnion> x \<longrightarrow> \<not> f bot \<le> x \<longrightarrow> top \<le> bot"
      by (metis (no_types, lifting) double_compl inf.sup_bot_left inf_compl_bot sup.order_iff sup_bot_left sup_commute sup_inf_distrib1 top.extremum_uniqueI)
    hence "post_fun top \<circ> (dual_fun f \<circ> top) \<squnion> id \<le> post_fun (f bot)"
      by (simp add: dual_fun_def le_fun_def post_fun_def)
    thus "post_fun (id top) \<circ> (dual_fun f \<circ> top) \<squnion> id \<le> post_fun (dual_fun ((dual_fun f \<circ> top) \<squnion> id) top)"
      by simp
  qed
qed

class complete_mbt_algebra_ext = complete_mbt_algebra + post_mbt_algebra_ext

instance MonoTran :: (complete_boolean_algebra) complete_mbt_algebra_ext ..

end

