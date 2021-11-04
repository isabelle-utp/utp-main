(*
    File:     General_Auxiliary.thy
    Author:   Joseph Thommes, TU München; Manuel Eberl, TU München
*)
section \<open>Auxiliary lemmas\<close>

theory General_Auxiliary
  imports "HOL-Algebra.Algebra"
begin

lemma inter_imp_subset: "A \<inter> B = A \<Longrightarrow> A \<subseteq> B"
  by blast

lemma card_inter_eq:
  assumes "finite A" "card (A \<inter> B) = card A"
  shows "A \<subseteq> B"
proof -
  have "A \<inter> B \<subseteq> A" by blast
  with assms have "A \<inter> B = A" using card_subset_eq by blast
  thus ?thesis by blast
qed

lemma coprime_eq_empty_prime_inter:
  assumes "(n::nat) \<noteq> 0" "m \<noteq> 0"
  shows "coprime n m \<longleftrightarrow> (prime_factors n) \<inter> (prime_factors m) = {}"
proof
  show "coprime n m \<Longrightarrow> prime_factors n \<inter> prime_factors m = {}"
  proof (rule ccontr)
    assume cp: "coprime n m"
    assume pf: "prime_factors n \<inter> prime_factors m \<noteq> {}"
    then obtain p where p: "p \<in> prime_factors n" "p \<in> prime_factors m" by blast
    then have p_dvd: "p dvd n" "p dvd m" by blast+
    moreover have "\<not>is_unit p" using p using not_prime_unit by blast
    ultimately show "False" using cp unfolding coprime_def by simp
  qed
  assume assm: "prime_factors n \<inter> prime_factors m = {}"
  show "coprime n m" unfolding coprime_def
  proof
    fix c
    show "c dvd n \<longrightarrow> c dvd m \<longrightarrow> is_unit c"
    proof(rule; rule)
      assume c: "c dvd n" "c dvd m"
      then have "prime_factors c \<subseteq> prime_factors n" "prime_factors c \<subseteq> prime_factors m"
        using assms dvd_prime_factors by blast+
      then have "prime_factors c = {}" using assm by blast
      thus "is_unit c" using assms c
        by (metis dvd_0_left_iff prime_factorization_empty_iff set_mset_eq_empty_iff)
    qed
  qed
qed

lemma prime_factors_Prod:
  assumes "finite S" "\<And>a. a \<in> S \<Longrightarrow> f a \<noteq> 0"
  shows "prime_factors (prod f S) = \<Union>(prime_factors ` f ` S)"
  using assms
proof(induction S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case i: (insert x F)
  from i have x: "f x \<noteq> 0" by blast
  from i have F: "prod f F \<noteq> 0" by simp
  from i have "prime_factors(prod f F) = \<Union> (prime_factors ` f ` F)" by blast
  moreover have "prod f (insert x F) = (prod f F) * f x" using i mult.commute by force
  ultimately
  have "prime_factors (prod f (insert x F)) = (\<Union>(prime_factors ` f ` F)) \<union> prime_factors (f x)"
    using prime_factors_product[OF F x] by argo
  thus ?case by force
qed

lemma lcm_is_Min_multiple_nat:
  assumes "c \<noteq> 0" "(a::nat) dvd c" "(b::nat) dvd c"
  shows "c \<ge> lcm a b"
  using lcm_least[of a c b] assms by fastforce

lemma diff_prime_power_imp_coprime:
  assumes "p \<noteq> q" "Factorial_Ring.prime (p::nat)" "Factorial_Ring.prime q"
  shows "coprime (p ^ (n::nat)) (q ^ m)"
  using assms
  by (metis power_0 power_one_right prime_dvd_power prime_imp_power_coprime_nat
            prime_nat_iff prime_power_inj'')

lemma "finite (prime_factors x)"
  using finite_set_mset by blast

lemma card_ge_1_two_diff:
  assumes "card A > 1"
  obtains x y where "x \<in> A" "y \<in> A" "x \<noteq> y"
proof -
  have fA: "finite A" using assms by (metis card.infinite not_one_less_zero)
  from assms obtain x where x: "x \<in> A" by fastforce
  with assms fA have "card (A - {x}) > 0" by simp
  then obtain y where y: "y \<in> (A - {x})" by (metis card_gt_0_iff ex_in_conv)
  thus ?thesis using that[of x y] x by blast
qed

lemma infinite_two_diff:
  assumes "infinite A"
  obtains x y where "x \<in> A" "y \<in> A" "x \<noteq> y"
proof -
  from assms obtain x where x: "x \<in> A" by fastforce
  from assms have "infinite (A - {x})" by simp
  then obtain y where y: "y \<in> (A - {x})"
    by (metis ex_in_conv finite.emptyI)
  show ?thesis using that[of x y] using x y by blast
qed

lemma Inf_le:
  "Inf A \<le> x" if "x \<in> (A::nat set)" for x
proof (cases "A = {}")
  case True
  then show ?thesis using that by simp
next
  case False
  hence "Inf A \<le> Inf {x}" using that by (simp add: cInf_lower)
  also have "\<dots> = x" by simp
  finally show "Inf A \<le> x" by blast
qed

lemma switch_elem_card_le:
  assumes "a \<in> A"
  shows "card (A - {a} \<union> {b}) \<le> card A"
  using assms
  by (metis Diff_insert_absorb Set.set_insert Un_commute card.infinite card_insert_disjoint
            card_mono finite_insert insert_is_Un insert_subset order_refl)

lemma pairwise_coprime_dvd:
  assumes "finite A" "pairwise coprime A" "(n::nat) = prod id A" "\<forall>a\<in>A. a dvd j"
  shows "n dvd j"
  using assms
proof (induction A arbitrary: n)
  case i: (insert x F)
  have "prod id F dvd j" "x dvd j" using i unfolding pairwise_def by auto
  moreover have "coprime (prod id F) x"
    by (metis i(2, 4) id_apply pairwise_insert prod_coprime_left)
  ultimately show ?case using i(1, 2, 5) by (simp add: coprime_commute divides_mult)
qed simp

lemma pairwise_coprime_dvd':
  assumes "finite A" "\<And>i j. \<lbrakk>i \<in> A; j \<in> A; i \<noteq> j\<rbrakk> \<Longrightarrow> coprime (f i) (f j)"
          "(n::nat) = prod f A" "\<forall>a\<in>A. f a dvd j"
  shows "n dvd j"
  using assms
proof (induction A arbitrary: n)
  case i: (insert x F)
  have "prod f F dvd j" "f x dvd j" using i unfolding pairwise_def by auto
  moreover have "coprime (prod f F) (f x)" by(intro prod_coprime_left, use i in blast)
  ultimately show ?case using i by (simp add: coprime_commute divides_mult)
qed simp

lemma transp_successively_remove1:
  assumes "transp f" "successively f l"
  shows "successively f (remove1 a l)" using assms(2)
proof(induction l rule: induct_list012)
  case (3 x y zs)
  from 3(3)[unfolded successively.simps] have fs: "f x y" "successively f (y # zs)" by auto
  moreover from this(2) successively.simps have s: "successively f zs" by(cases zs, auto)
  ultimately have s2: "successively f (remove1 a zs)" "successively f (remove1 a (y # zs))"
    using 3 by auto
  consider (x) "x = a" | (y) "y = a \<and> x \<noteq> a" | (zs) "a \<noteq> x \<and> a \<noteq> y" by blast
  thus ?case
  proof (cases)
    case x
    then show ?thesis using 3 by simp
  next
    case y
    then show ?thesis
    proof (cases zs)
      case Nil
      then show ?thesis using fs by simp
    next
      case (Cons a list)
      hence "f y a" using fs by simp
      hence "f x a" using fs(1) assms(1)[unfolded transp_def] by blast
      then show ?thesis using Cons y s by auto
    qed
  next
    case zs
    then show ?thesis using s2 fs by auto
  qed
qed auto


lemma exp_one_2pi_iff:
  fixes x::real shows "exp (2 * of_real pi * \<i> * x) = 1 \<longleftrightarrow> x \<in> \<int>"
proof -
  have c: "cis (2 * x * pi) = 1 \<longleftrightarrow> x \<in> \<int>"
    by (auto simp: complex_eq_iff sin_times_pi_eq_0 cos_one_2pi_int, meson Ints_cases)
  have "exp (2 * of_real pi * \<i> * x) = exp (\<i> * complex_of_real (2 * x * pi))"
  proof -
    have "2 * of_real pi * \<i> * x = \<i> * complex_of_real (2 * x * pi)" by simp
    thus ?thesis by argo
  qed
  also from cis_conv_exp have "\<dots> = cis (2 * x * pi)" by simp
  finally show ?thesis using c by simp
qed

(* Manuel Eberl *)
lemma of_int_divide_in_Ints_iff:
  assumes "b \<noteq> 0"
  shows   "(of_int a / of_int b :: 'a :: field_char_0) \<in> \<int> \<longleftrightarrow> b dvd a"
proof
  assume *: "(of_int a / of_int b :: 'a :: field_char_0) \<in> \<int>"
  from * obtain n where "of_int a / of_int b = (of_int n :: 'a)"
    by (elim Ints_cases)
  hence "of_int (b * n) = (of_int a :: 'a)"
    using assms by (subst of_int_mult) (auto simp: field_simps)
  hence "b * n = a"
    by (subst (asm) of_int_eq_iff)
  thus "b dvd a" by auto
qed auto

(* Manuel Eberl *)
lemma of_nat_divide_in_Ints_iff:
  assumes "b \<noteq> 0"
  shows   "(of_nat a / of_nat b :: 'a :: field_char_0) \<in> \<int> \<longleftrightarrow> b dvd a"
  using of_int_divide_in_Ints_iff[of "int b" "int a"] assms by simp

lemma true_nth_unity_root:
  fixes n::nat
  obtains x::complex where "x ^ n = 1" "\<And>m. \<lbrakk>0<m; m<n\<rbrakk> \<Longrightarrow> x ^ m \<noteq> 1"
proof(cases "n = 0")
  case False
  show ?thesis
  proof (rule that)
    show "cis (2 * pi / n) ^ n = 1"
      by (simp add: DeMoivre)
  next
    fix m assume m: "m > 0" "m < n"
    have "cis (2 * pi / n) ^ m = cis (2 * pi * m / n)"
      by (simp add: DeMoivre algebra_simps)
    also have "\<dots> = 1 \<longleftrightarrow> real m / real n \<in> \<int>"
      using exp_one_2pi_iff[of "m / n"] by (simp add: cis_conv_exp algebra_simps)
    also have "\<dots> \<longleftrightarrow> n dvd m"
      using m by (subst of_nat_divide_in_Ints_iff) auto
    also have "\<not>n dvd m"
      using m by auto
    finally show "cis (2 * pi / real n) ^ m \<noteq> 1" .
  qed
qed simp

lemma finite_bij_betwI:
  assumes "finite A" "finite B" "inj_on f A" "f \<in> A \<rightarrow> B" "card A = card B"
  shows "bij_betw f A B"
proof (intro bij_betw_imageI)
  show "inj_on f A" by fact
  show "f ` A = B"
  proof -
    have "card (f ` A) = card B" using assms by (simp add: card_image)
    moreover have "f ` A \<subseteq> B" using assms by blast
    ultimately show ?thesis using assms by (meson card_subset_eq)
  qed
qed

lemma powi_mod:
  "x powi m = x powi (m mod n)" if "x ^ n = 1" "n > 0" for x::complex and m::int
proof -
  have xnz: "x \<noteq> 0" using that by (metis zero_neq_one zero_power)
  obtain k::int where k: "m = k*n + (m mod n)" using div_mod_decomp_int by blast
  have "x powi m = x powi (k*n) * x powi (m mod n)" by (subst k, intro power_int_add, use xnz in auto)
  moreover have "x powi (k*n) = 1" using that
    by (metis mult.commute power_int_1_left power_int_mult power_int_of_nat)
  ultimately show ?thesis by force
qed

(* Manuel Eberl *)
lemma Sigma_insert: "Sigma (insert x A) B = (\<lambda>y. (x, y)) ` B x \<union> Sigma A B"
  by auto

end