(*
  File:     More_Multivariate_Polynomial_HLW.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>Additional facts about multivariate polynomials\<close>
theory More_Multivariate_Polynomial_HLW
  imports "Power_Sum_Polynomials.Power_Sum_Polynomials_Library"
begin

subsection \<open>Miscellaneous\<close>

lemma Var_altdef: "Var i = monom (Poly_Mapping.single i 1) 1"
  by transfer' (simp add: Var\<^sub>0_def)

lemma Const_conv_monom: "Const c = monom 0 c"
  by transfer' (auto simp: Const\<^sub>0_def)

lemma smult_conv_mult_Const: "smult c p = Const c * p"
  by (simp add: smult_conv_mult Const_conv_monom)

lemma mpoly_map_vars_Var [simp]: "bij f \<Longrightarrow> mpoly_map_vars f (Var i) = Var (f i)"
  unfolding Var_altdef
  by (subst mpoly_map_vars_monom) (auto simp: permutep_single bij_imp_bij_inv inv_inv_eq)

lemma symmetric_mpoly_symmetric_prod':
  assumes "\<And>\<pi>. \<pi> permutes A \<Longrightarrow> g \<pi> permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g \<pi> x)"
  shows "symmetric_mpoly A (\<Prod>x\<in>X. f x)"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume \<pi>: "\<pi> permutes A"
  have "mpoly_map_vars \<pi> (prod f X) = (\<Prod>x\<in>X. mpoly_map_vars \<pi> (f x))"
    by simp
  also have "\<dots> = (\<Prod>x\<in>X. f (g \<pi> x))"
    by (intro prod.cong assms \<pi> refl)
  also have "\<dots> = (\<Prod>x\<in>g \<pi>`X. f x)"
    using assms(1)[OF \<pi>] by (subst prod.reindex) (auto simp: permutes_inj_on)
  also have "g \<pi> ` X = X"
    using assms(1)[OF \<pi>] by (simp add: permutes_image)
  finally show "mpoly_map_vars \<pi> (prod f X) = prod f X" .
qed



subsection \<open>Converting a univariate polynomial into a multivariate one\<close>

lift_definition mpoly_of_poly_aux :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a" is
  "\<lambda>i c m. if Poly_Mapping.keys m \<subseteq> {i} then c (Poly_Mapping.lookup m i) else 0"
proof goal_cases
  case (1 i c)
  hence fin: "finite {n. c n \<noteq> 0}"
    by (metis eventually_cofinite)
  show "finite {x. (if keys x \<subseteq> {i} then c (lookup x i) else 0) \<noteq> 0}"
  proof (rule finite_subset)
    show "finite (Poly_Mapping.single i ` {n. c n \<noteq> 0})"
      by (intro finite_imageI fin)
  next
    show "{x. (if keys x \<subseteq> {i} then c (lookup x i) else 0) \<noteq> 0} \<subseteq>
            Poly_Mapping.single i ` {n. c n \<noteq> 0}"
    proof (safe, split if_splits)
      fix x :: "(nat \<Rightarrow>\<^sub>0 nat)"
      assume x: "keys x \<subseteq> {i}" "c (lookup x i) \<noteq> 0"
      hence "x = Poly_Mapping.single i (lookup x i)"
        by (metis Diff_eq_empty_iff keys_empty_iff lookup_single_eq
                  remove_key_keys remove_key_single remove_key_sum)
      thus "x \<in> Poly_Mapping.single i ` {n. c n \<noteq> 0}"
        using x by blast
    qed auto
  qed
qed

lift_definition mpoly_of_poly :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> 'a mpoly" is
  "mpoly_of_poly_aux" .

lemma mpoly_of_poly_0 [simp]: "mpoly_of_poly i 0 = 0"
  by (transfer', transfer) auto

lemma coeff_mpoly_of_poly1 [simp]:
  "coeff (mpoly_of_poly i p) (Poly_Mapping.single i n) = poly.coeff p n"
  by (transfer', transfer') auto

lemma coeff_mpoly_of_poly2 [simp]:
  assumes "\<not>keys x \<subseteq> {i}"
  shows "coeff (mpoly_of_poly i p) x = 0"
  using assms by (transfer', transfer') auto

lemma coeff_mpoly_of_poly:
  "coeff (mpoly_of_poly i p) m =
     (poly.coeff p (Poly_Mapping.lookup m i) when keys m \<subseteq> {i})"
  by (transfer', transfer') auto

lemma poly_mapping_single_eq_0_iff [simp]: "Poly_Mapping.single i n = 0 \<longleftrightarrow> n = 0"
  by (metis lookup_single_eq single_zero)

lemma mpoly_of_poly_pCons [simp]:
  fixes p :: "'a :: semiring_1 poly"
  shows "mpoly_of_poly i (pCons c p) = Const c + Var i * mpoly_of_poly i p"
proof (rule mpoly_eqI)
  fix mon :: "nat \<Rightarrow>\<^sub>0 nat"
  define moni :: "nat \<Rightarrow>\<^sub>0 nat" where "moni = Poly_Mapping.single i 1"
  have "coeff (Var i * mpoly_of_poly i p) mon =
          (\<Sum>l. (1 when l = moni) * (\<Sum>q. coeff (mpoly_of_poly i p) q when mon = moni + q))"
    unfolding coeff_mpoly_times prod_fun_def coeff_Var moni_def
    by (rule Sum_any.cong) (auto simp: when_def)
  also have "\<dots> = (\<Sum>a. coeff (mpoly_of_poly i p) a when mon = moni + a)"
    by (subst Sum_any_left_distrib [symmetric]) simp_all
  finally have eq: "coeff (Var i * mpoly_of_poly i p) mon = \<dots>" .

  show "coeff (mpoly_of_poly i (pCons c p)) mon = coeff (Const c + Var i * mpoly_of_poly i p) mon"
  proof (cases "keys mon \<subseteq> {i}")
    case False
    hence [simp]: "mon \<noteq> 0"
      by auto
    obtain j where j: "j \<in> keys mon" "j \<noteq> i"
      using False by auto
    have "coeff (mpoly_of_poly i p) mon' = 0" if mon_eq: "mon = moni + mon'" for mon'
    proof -
      have "Poly_Mapping.lookup mon j \<noteq> 0"
        using j by (meson lookup_eq_zero_in_keys_contradict)
      also have "Poly_Mapping.lookup mon j = Poly_Mapping.lookup mon' j"
        unfolding mon_eq moni_def using j by (simp add: lookup_add lookup_single)
      finally have "j \<in> keys mon'"
        by (meson lookup_not_eq_zero_eq_in_keys)
      with j have "\<not>keys mon' \<subseteq> {i}"
        by blast
      thus ?thesis by simp
    qed
    hence "coeff (Var i * mpoly_of_poly i p) mon = 0"
      unfolding eq by (intro Sum_any_zeroI) (auto simp: when_def)
    thus ?thesis using False
      by (simp add: mpoly_coeff_Const)
  next
    case True
    define n where "n = Poly_Mapping.lookup mon i"
    have mon_eq: "mon = Poly_Mapping.single i n"
      using True unfolding n_def
      by (metis Diff_eq_empty_iff add_cancel_right_left keys_empty_iff remove_key_keys remove_key_sum)
    have eq': "mon = moni + mon' \<longleftrightarrow> n > 0 \<and> mon' = Poly_Mapping.single i (n - 1)" for mon'
    proof safe
      assume eq: "mon = moni + mon'"
      thus "n > 0" "mon' = Poly_Mapping.single i (n - 1)"
        unfolding moni_def mon_eq using gr0I by (force simp: single_diff)+
    next
      assume "n > 0" "mon' = Poly_Mapping.single i (n - 1)"
      thus "mon = moni + Poly_Mapping.single i (n - 1)"
        unfolding mon_eq moni_def by (subst single_add [symmetric]) auto
    qed
    have "coeff (Var i * mpoly_of_poly i p) mon = (poly.coeff p (n - 1) when (n > 0))"
      unfolding eq eq' by (auto simp: when_def)
    thus ?thesis
      by (auto simp: mon_eq when_def mpoly_coeff_Const coeff_pCons split: nat.splits)
  qed
qed

lemma mpoly_of_poly_1 [simp]: "mpoly_of_poly i 1 = 1"
  unfolding one_pCons mpoly_of_poly_pCons mpoly_of_poly_0 by simp

lemma mpoly_of_poly_uminus [simp]: "mpoly_of_poly i (-p) = -mpoly_of_poly i p"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_add [simp]: "mpoly_of_poly i (p + q) = mpoly_of_poly i p + mpoly_of_poly i q"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_diff [simp]: "mpoly_of_poly i (p - q) = mpoly_of_poly i p - mpoly_of_poly i q"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_smult [simp]:
  "mpoly_of_poly i (Polynomial.smult c p) = smult c (mpoly_of_poly i p)"
  by (rule mpoly_eqI) (auto simp: coeff_mpoly_of_poly when_def)

lemma mpoly_of_poly_mult [simp]:
  fixes p q :: "'a :: comm_semiring_1 poly"
  shows "mpoly_of_poly i (p * q) = mpoly_of_poly i p * mpoly_of_poly i q"
  by (induction p) (auto simp: algebra_simps smult_conv_mult_Const)

lemma insertion_mpoly_of_poly [simp]: "insertion f (mpoly_of_poly i p) = poly p (f i)"
  by (induction p) (auto simp: insertion_add insertion_mult)

lemma mapping_of_mpoly_of_poly [simp]: "mapping_of (mpoly_of_poly i p) = mpoly_of_poly_aux i p"
  by transfer' simp

lemma vars_mpoly_of_poly: "vars (mpoly_of_poly i p) \<subseteq> {i}"
proof -
  have "x = i" if "xa \<in> keys (mpoly_of_poly_aux i p)" "x \<in> keys xa" for x xa
    using that
    by (meson in_mono lookup_eq_zero_in_keys_contradict mpoly_of_poly_aux.rep_eq singletonD)
  thus ?thesis
    by (auto simp: vars_def)
qed

lemma mpoly_map_vars_mpoly_of_poly [simp]:
  assumes "bij f"
  shows   "mpoly_map_vars f (mpoly_of_poly i p) = mpoly_of_poly (f i) p"
proof (rule mpoly_eqI, goal_cases)
  case (1 mon)
  have "f -` keys mon \<subseteq> {i} \<longleftrightarrow> keys mon \<subseteq> {f i}"
    using assms by (simp add: vimage_subset_eq)
  thus ?case using assms
    by (simp add: coeff_mpoly_map_vars coeff_mpoly_of_poly lookup_permutep keys_permutep when_def)
qed

end