(*
  File:     Misc_HLW.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>Miscellaneous facts\<close>
theory Misc_HLW
imports
  Complex_Main
  "HOL-Library.Multiset"
  "HOL-Library.Permutations"
  "HOL-Library.FuncSet"
  "HOL-Library.Groups_Big_Fun"
  "HOL-Library.Poly_Mapping"
  "HOL-Library.Landau_Symbols"
  "HOL-Computational_Algebra.Computational_Algebra"
begin

lemma set_mset_subset_singletonD:
  assumes "set_mset A \<subseteq> {x}"
  shows   "A = replicate_mset (size A) x"
  using assms by (induction A) auto
  
lemma image_mset_eq_replicate_msetD:
  assumes "image_mset f A = replicate_mset n y"
  shows   "\<forall>x\<in>#A. f x = y"
proof -
  have "f ` set_mset A = set_mset (image_mset f A)"
    by simp
  also note assms
  finally show ?thesis by (auto split: if_splits)
qed

lemma bij_betw_permutes_compose_left:
  assumes "\<pi> permutes A"
  shows   "bij_betw (\<lambda>\<sigma>. \<pi> \<circ> \<sigma>) {\<sigma>. \<sigma> permutes A} {\<sigma>. \<sigma> permutes A}"
proof (rule bij_betwI)
  show "(\<circ>) \<pi> \<in> {\<sigma>. \<sigma> permutes A} \<rightarrow> {\<sigma>. \<sigma> permutes A}"
    by (auto intro: permutes_compose assms)
  show "(\<circ>) (inv_into UNIV \<pi>) \<in> {\<sigma>. \<sigma> permutes A} \<rightarrow> {\<sigma>. \<sigma> permutes A}"
    by (auto intro: permutes_compose assms permutes_inv)
qed (use permutes_inverses[OF assms] in auto)

lemma bij_betw_compose_left_perm_Pi:
  assumes "\<pi> permutes B"
  shows   "bij_betw (\<lambda>f. (\<pi> \<circ> f)) (A \<rightarrow> B) (A \<rightarrow> B)"
proof (rule bij_betwI)
  have *: "(\<lambda>f. (\<pi> \<circ> f)) \<in> (A \<rightarrow> B) \<rightarrow> A \<rightarrow> B" if \<pi>: "\<pi> permutes B" for \<pi>
    by (auto simp: permutes_in_image[OF \<pi>])
  show "(\<lambda>f. (\<pi> \<circ> f)) \<in> (A \<rightarrow> B) \<rightarrow> A \<rightarrow> B"
    by (rule *) fact
  show "(\<lambda>f. (inv_into UNIV \<pi> \<circ> f)) \<in> (A \<rightarrow> B) \<rightarrow> A \<rightarrow> B"
    by (intro * permutes_inv) fact
qed (auto simp: permutes_inverses[OF assms] fun_eq_iff)

lemma bij_betw_compose_left_perm_PiE:
  assumes "\<pi> permutes B"
  shows   "bij_betw (\<lambda>f. restrict (\<pi> \<circ> f) A) (A \<rightarrow>\<^sub>E B) (A \<rightarrow>\<^sub>E B)"
proof (rule bij_betwI)
  have *: "(\<lambda>f. restrict (\<pi> \<circ> f) A) \<in> (A \<rightarrow>\<^sub>E B) \<rightarrow> A \<rightarrow>\<^sub>E B" if \<pi>: "\<pi> permutes B" for \<pi>
    by (auto simp: permutes_in_image[OF \<pi>])
  show "(\<lambda>f. restrict (\<pi> \<circ> f) A) \<in> (A \<rightarrow>\<^sub>E B) \<rightarrow> A \<rightarrow>\<^sub>E B"
    by (rule *) fact
  show "(\<lambda>f. restrict (inv_into UNIV \<pi> \<circ> f) A) \<in> (A \<rightarrow>\<^sub>E B) \<rightarrow> A \<rightarrow>\<^sub>E B"
    by (intro * permutes_inv) fact
qed (auto simp: permutes_inverses[OF assms] fun_eq_iff)

lemma bij_betw_image_mset_set:
  assumes "bij_betw f A B"
  shows   "image_mset f (mset_set A) = mset_set B"
  using assms by (simp add: bij_betw_def image_mset_mset_set)

lemma finite_multisets_of_size:
  assumes "finite A"
  shows   "finite {X. set_mset X \<subseteq> A \<and> size X = n}"
proof (rule finite_subset)
  show "{X. set_mset X \<subseteq> A \<and> size X = n} \<subseteq> mset ` {xs. set xs \<subseteq> A \<and> length xs = n}"
  proof
    fix X assume X: "X \<in> {X. set_mset X \<subseteq> A \<and> size X = n}"
    obtain xs where [simp]: "X = mset xs"
      by (metis ex_mset)
    thus "X \<in> mset ` {xs. set xs \<subseteq> A \<and> length xs = n}"
      using X by auto
  qed
next
  show "finite (mset ` {xs. set xs \<subseteq> A \<and> length xs = n})"
    by (intro finite_imageI finite_lists_length_eq assms)
qed

lemma sum_mset_image_mset_sum_mset_image_mset:
   "sum_mset (image_mset g (sum_mset (image_mset f A))) =
    sum_mset (image_mset (\<lambda>x. sum_mset (image_mset g (f x))) A)"
  by (induction A) auto

lemma sum_mset_image_mset_singleton: "sum_mset (image_mset (\<lambda>x. {#f x#}) A) = image_mset f A"
  by (induction A) auto

lemma sum_mset_conv_sum:
  "sum_mset (image_mset f A) = (\<Sum>x\<in>set_mset A. of_nat (count A x) * f x)"
proof (induction A rule: full_multiset_induct)
  case (less A)
  show ?case
  proof (cases "A = {#}")
    case False
    then obtain x where x: "x \<in># A"
      by auto
    define n where "n = count A x"
    define A' where "A' = filter_mset (\<lambda>y. y \<noteq> x) A"
    have A_eq: "A = replicate_mset n x + A'"
      by (intro multiset_eqI) (auto simp: A'_def n_def)
    have [simp]: "x \<notin># A'" "count A' x = 0"
      by (auto simp: A'_def)
    have "n \<noteq> 0"
      using x by (auto simp: n_def)
    
    have "sum_mset (image_mset f A) = of_nat n * f x + sum_mset (image_mset f A')"
      by (simp add: A_eq)
    also have "A' \<subset># A"
      unfolding A'_def using x by (simp add: filter_mset_eq_conv subset_mset_def)
    with less.IH have "sum_mset (image_mset f A') = (\<Sum>x\<in>set_mset A'. of_nat (count A' x) * f x)"
      by simp
    also have "\<dots> = (\<Sum>x\<in>set_mset A'. of_nat (count A x) * f x)"
      by (intro sum.cong) (auto simp: A_eq)
    also have "of_nat n * f x + \<dots> = (\<Sum>x\<in>insert x (set_mset A'). of_nat (count A x) * f x)"
      by (subst sum.insert) (auto simp: A_eq)
    also from \<open>n \<noteq> 0\<close> have "insert x (set_mset A') = set_mset A"
      by (auto simp: A_eq)
    finally show ?thesis .
  qed auto
qed

lemma sum_mset_conv_Sum_any:
  "sum_mset (image_mset f A) = Sum_any (\<lambda>x. of_nat (count A x) * f x)"
proof -
  have "sum_mset (image_mset f A) = (\<Sum>x\<in>set_mset A. of_nat (count A x) * f x)"
    by (rule sum_mset_conv_sum)
  also have "\<dots> = Sum_any (\<lambda>x. of_nat (count A x) * f x)"
  proof (rule Sum_any.expand_superset [symmetric])
    show "{x. of_nat (count A x) * f x \<noteq> 0} \<subseteq> set_mset A"
    proof
      fix x assume "x \<in> {x. of_nat (count A x) * f x \<noteq> 0}"
      hence "count A x \<noteq> 0"
        by (intro notI) auto
      thus "x \<in># A"
        by auto
    qed
  qed auto
  finally show ?thesis .
qed

lemma Sum_any_sum_swap:
  assumes "finite A" "\<And>y. finite {x. f x y \<noteq> 0}"
  shows   "Sum_any (\<lambda>x. sum (f x) A) = (\<Sum>y\<in>A. Sum_any (\<lambda>x. f x y))"
proof -
  have "Sum_any (\<lambda>x. sum (f x) A) = Sum_any (\<lambda>x. Sum_any (\<lambda>y. f x y when y \<in> A))"
    unfolding when_def by (subst Sum_any.conditionalize) (use assms in simp_all)
  also have "\<dots> = Sum_any (\<lambda>y. Sum_any (\<lambda>x. f x y when y \<in> A))"
    by (intro Sum_any.swap[of "(\<Union>y\<in>A. {x. f x y \<noteq> 0}) \<times> A"] finite_SigmaI finite_UN_I assms) auto
  also have "(\<lambda>y. Sum_any (\<lambda>x. f x y when y \<in> A)) = (\<lambda>y. Sum_any (\<lambda>x. f x y) when y \<in> A)"
    by (auto simp: when_def)
  also have "Sum_any \<dots> = (\<Sum>y\<in>A. Sum_any (\<lambda>x. f x y))"
    unfolding when_def by (subst Sum_any.conditionalize) (use assms in simp_all)
  finally show ?thesis .
qed

lemma (in landau_pair) big_power:
  assumes "f \<in> L F g"
  shows   "(\<lambda>x. f x ^ n) \<in> L F (\<lambda>x. g x ^ n)"
  using big_prod[of "{..<n}" "\<lambda>_. f" F "\<lambda>_. g"] assms by simp

lemma (in landau_pair) small_power:
  assumes "f \<in> l F g" "n > 0"
  shows   "(\<lambda>x. f x ^ n) \<in> l F (\<lambda>x. g x ^ n)"
  using assms(2,1)
  by (induction rule: nat_induct_non_zero) (auto intro!: small.mult)

lemma pairwise_imp_disjoint_family_on:
  assumes "pairwise R A"
  assumes "\<And>m n. m \<in> A \<Longrightarrow> n \<in> A \<Longrightarrow> R m n \<Longrightarrow> f m \<inter> f n = {}"
  shows   "disjoint_family_on f A"
  using assms
  unfolding disjoint_family_on_def pairwise_def by blast

lemma (in comm_monoid_set) If_eq:
  assumes "y \<in> A" "finite A"
  shows   "F (\<lambda>x. g x (if x = y then h1 x else h2 x)) A = f (g y (h1 y)) (F (\<lambda>x. g x (h2 x)) (A-{y}))"
proof -
  have "F (\<lambda>x. g x (if x = y then h1 x else h2 x)) A =
          f (g y (h1 y)) (F (\<lambda>x. g x (if x = y then h1 x else h2 x)) (A-{y}))"
    using assms by (subst remove[of _ y]) auto
  also have "F (\<lambda>x. g x (if x = y then h1 x else h2 x)) (A-{y}) = F (\<lambda>x. g x (h2 x)) (A-{y})"
    by (intro cong) auto
  finally show ?thesis by simp
qed

lemma prod_nonzeroI:
  fixes f :: "'a \<Rightarrow> 'b :: {semiring_no_zero_divisors, comm_semiring_1}"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows "prod f A \<noteq> 0"
  using assms by (induction rule: infinite_finite_induct) auto

lemma frequently_prime_cofinite: "frequently (prime :: nat \<Rightarrow> bool) cofinite"
  unfolding INFM_nat_le by (meson bigger_prime less_imp_le)

lemma frequently_eventually_mono:
  assumes "frequently Q F" "eventually P F" "\<And>x. P x \<Longrightarrow> Q x \<Longrightarrow> R x"
  shows   "frequently R F"
proof (rule frequently_mp[OF _ assms(1)])
  show "eventually (\<lambda>x. Q x \<longrightarrow> R x) F"
    using assms(2) by eventually_elim (use assms(3) in blast)
qed

lemma bij_betw_Diff:
  assumes "bij_betw f A B" "bij_betw f A' B'" "A' \<subseteq> A" "B' \<subseteq> B"
  shows   "bij_betw f (A - A') (B - B')"
  unfolding bij_betw_def
proof
  have "inj_on f A"
    using assms(1) by (auto simp: bij_betw_def)
  thus "inj_on f (A - A')"
    by (rule inj_on_subset) auto
  have "f ` (A - A') = f ` A - f ` A'"
    by (intro inj_on_image_set_diff[OF \<open>inj_on f A\<close>]) (use \<open>A' \<subseteq> A\<close> in auto)
  also have "\<dots> = B - B'"
    using assms(1,2) by (auto simp: bij_betw_def)
  finally show "f` (A - A') = B - B'" .
qed
    
lemma bij_betw_singleton: "bij_betw f {x} {y} \<longleftrightarrow> f x = y"
  by (auto simp: bij_betw_def)

end