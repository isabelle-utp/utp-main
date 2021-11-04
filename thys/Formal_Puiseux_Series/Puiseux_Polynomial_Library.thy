(*
  File:    Puiseux_Polynomial_Library.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Auxiliary material\<close>
subsection \<open>Facts about polynomials\<close>
theory Puiseux_Polynomial_Library
  imports "HOL-Computational_Algebra.Computational_Algebra" "Polynomial_Interpolation.Ring_Hom_Poly"
begin

(* TODO: move a lot of this *)

lemma poly_sum_mset: "poly (\<Sum>x\<in>#A. p x) y = (\<Sum>x\<in>#A. poly (p x) y)"
  by (induction A) auto

lemma poly_prod_mset: "poly (\<Prod>x\<in>#A. p x) y = (\<Prod>x\<in>#A. poly (p x) y)"
  by (induction A) auto

lemma set_mset_subset_singletonD:
  assumes "set_mset A \<subseteq> {x}"
  shows   "A = replicate_mset (size A) x"
  using assms by (induction A) auto

lemma inj_idom_hom_compose [intro]:
  assumes "inj_idom_hom f" "inj_idom_hom g"
  shows   "inj_idom_hom (f \<circ> g)"
proof -
  interpret f: inj_idom_hom f by fact
  interpret g: inj_idom_hom g by fact
  show ?thesis
    by unfold_locales (auto simp: f.hom_add g.hom_add f.hom_mult g.hom_mult)
qed

lemma coeff_pcompose_linear:
  "coeff (pcompose p [:0, a :: 'a :: comm_semiring_1:]) i = a ^ i * coeff p i"
  by (induction p arbitrary: i) (auto simp: pcompose_pCons coeff_pCons mult_ac split: nat.splits)

lemma degree_cong:
  assumes "\<And>i. coeff p i = 0 \<longleftrightarrow> coeff q i = 0"
  shows   "degree p = degree q"
proof -
  have "(\<lambda>n. \<forall>i>n. poly.coeff p i = 0) = (\<lambda>n. \<forall>i>n. poly.coeff q i = 0)"
    using assms by (auto simp: fun_eq_iff)
  thus ?thesis
    by (simp only: degree_def)
qed

lemma coeff_Abs_poly_If_le:
  "coeff (Abs_poly (\<lambda>i. if i \<le> n then f i else 0)) = (\<lambda>i. if i \<le> n then f i else 0)"
proof (rule Abs_poly_inverse, clarify)
  have "eventually (\<lambda>i. i > n) cofinite"
    by (auto simp: MOST_nat)
  thus "eventually (\<lambda>i. (if i \<le> n then f i else 0) = 0) cofinite"
    by eventually_elim auto
qed

lemma coeff_Abs_poly:
  assumes "\<And>i. i > n \<Longrightarrow> f i = 0"
  shows   "coeff (Abs_poly f) = f"
proof (rule Abs_poly_inverse, clarify)
  have "eventually (\<lambda>i. i > n) cofinite"
    by (auto simp: MOST_nat)
  thus "eventually (\<lambda>i. f i = 0) cofinite"
    by eventually_elim (use assms in auto)
qed

lemma (in inj_idom_hom) inj_idom_hom_map_poly [intro]: "inj_idom_hom (map_poly hom)"
proof -
  interpret map_poly_inj_idom_hom hom by unfold_locales
  show ?thesis 
    by (simp add: inj_idom_hom_axioms)
qed

lemma inj_idom_hom_pcompose [intro]:
  assumes [simp]: "degree (p :: 'a :: idom poly) \<noteq> 0"
  shows "inj_idom_hom (\<lambda>q. pcompose q p)"
  by unfold_locales (simp_all add: pcompose_eq_0)

lemma degree_sum_less:
  assumes "\<And>x. x \<in> A \<Longrightarrow> degree (f x) < n" "n > 0"
  shows   "degree (sum f A) < n"
  using assms by (induction rule: infinite_finite_induct) (auto intro!: degree_add_less)

lemma degree_lessI:
  assumes "p \<noteq> 0 \<or> n > 0" "\<forall>k\<ge>n. coeff p k = 0"
  shows   "degree p < n"
proof (cases "p = 0")
  case False
  show ?thesis
  proof (rule ccontr)
    assume *: "\<not>(degree p < n)"
    define d where "d = degree p"
    from \<open>p \<noteq> 0\<close> have "coeff p d \<noteq> 0"
      by (auto simp: d_def)
    moreover have "coeff p d = 0"
      using assms(2) * by (auto simp: not_less)
    ultimately show False by contradiction
  qed
qed (use assms in auto)

lemma coeff_linear_poly_power:
  fixes c :: "'a :: semiring_1"
  assumes "i \<le> n"
  shows   "coeff ([:a, b:] ^ n) i = of_nat (n choose i) * b ^ i * a ^ (n - i)"
proof -
  have "[:a, b:] = monom b 1 + [:a:]"
    by (simp add: monom_altdef)
  also have "coeff (\<dots> ^ n) i = (\<Sum>k\<le>n. a^(n-k) * of_nat (n choose k) * (if k = i then b ^ k else 0))"
    by (subst binomial_ring) (simp add: coeff_sum of_nat_poly monom_power poly_const_pow mult_ac)
  also have "\<dots> = (\<Sum>k\<in>{i}. a ^ (n - i) * b ^ i * of_nat (n choose k))"
    using assms by (intro sum.mono_neutral_cong_right) (auto simp: mult_ac)
  finally show *: ?thesis by (simp add: mult_ac)
qed

lemma pcompose_altdef: "pcompose p q = poly (map_poly (\<lambda>x. [:x:]) p) q"
  by (induction p) simp_all

lemma coeff_mult_0: "coeff (p * q) 0 = coeff p 0 * coeff q 0"
  by (simp add: coeff_mult)

lemma coeff_pcompose_0 [simp]:
  "coeff (pcompose p q) 0 = poly p (coeff q 0)"
  by (induction p) (simp_all add: coeff_mult_0)

lemma reducible_polyI:
  fixes p :: "'a :: field poly"
  assumes "p = q * r" "degree q > 0" "degree r > 0"
  shows   "\<not>irreducible p"
  using assms by (auto simp: irreducible_def)

lemma root_imp_reducible_poly:
  fixes x :: "'a :: field"
  assumes "poly p x = 0" and "degree p > 1"
  shows   "\<not>irreducible p"
proof -
  from assms have "p \<noteq> 0"
    by auto
  define q where "q = [:-x, 1:]"
  have "q dvd p"
    using assms by (simp add: poly_eq_0_iff_dvd q_def)
  then obtain r where p_eq: "p = q * r"
    by (elim dvdE)
  have [simp]: "q \<noteq> 0" "r \<noteq> 0"
    using \<open>p \<noteq> 0\<close> by (auto simp: p_eq)
  have "degree p = Suc (degree r)"
    unfolding p_eq by (subst degree_mult_eq) (auto simp: q_def)
  with assms(2) have "degree r > 0"
    by auto
  hence "\<not>is_unit r"
    by auto
  moreover have "\<not>is_unit q"
    by (auto simp: q_def)
  ultimately show ?thesis using p_eq
    by (auto simp: irreducible_def)
qed


subsection \<open>A typeclass for algebraically closed fields\<close>

(* TODO: Move! *)

text \<open>
  Since the required sort constraints are not available inside the class, we have to resort
  to a somewhat awkward way of writing the definition of algebraically closed fields:
\<close>
class alg_closed_field = field +
  assumes alg_closed: "n > 0 \<Longrightarrow> f n \<noteq> 0 \<Longrightarrow> \<exists>x. (\<Sum>k\<le>n. f k * x ^ k) = 0"

text \<open>
  We can then however easily show the equivalence to the proper definition:
\<close>
lemma alg_closed_imp_poly_has_root:
  assumes "degree (p :: 'a :: alg_closed_field poly) > 0"
  shows   "\<exists>x. poly p x = 0"
proof -
  have "\<exists>x. (\<Sum>k\<le>degree p. coeff p k * x ^ k) = 0"
    using assms by (intro alg_closed) auto
  thus ?thesis
    by (simp add: poly_altdef)
qed

lemma alg_closedI [Pure.intro]:
  assumes "\<And>p :: 'a poly. degree p > 0 \<Longrightarrow> lead_coeff p = 1 \<Longrightarrow> \<exists>x. poly p x = 0"
  shows   "OFCLASS('a :: field, alg_closed_field_class)"
proof
  fix n :: nat and f :: "nat \<Rightarrow> 'a"
  assume n: "n > 0" "f n \<noteq> 0"
  define p where "p = Abs_poly (\<lambda>k. if k \<le> n then f k else 0)"
  have coeff_p: "coeff p k = (if k \<le> n then f k else 0)" for k
  proof -
    have "eventually (\<lambda>k. k > n) cofinite"
      by (auto simp: MOST_nat)
    hence "eventually (\<lambda>k. (if k \<le> n then f k else 0) = 0) cofinite"
      by eventually_elim auto
    thus ?thesis
      unfolding p_def by (subst Abs_poly_inverse) auto
  qed

  from n have "degree p \<ge> n"
    by (intro le_degree) (auto simp: coeff_p)
  moreover have "degree p \<le> n"
    by (intro degree_le) (auto simp: coeff_p)
  ultimately have deg_p: "degree p = n"
    by linarith
  from deg_p and n have [simp]: "p \<noteq> 0"
    by auto

  define p' where "p' = smult (inverse (lead_coeff p)) p"
  have deg_p': "degree p' = degree p"
    by (auto simp: p'_def)
  have lead_coeff_p' [simp]: "lead_coeff p' = 1"
    by (auto simp: p'_def)

  from deg_p and deg_p' and n have "degree p' > 0"
    by simp
  from assms[OF this] obtain x where "poly p' x = 0"
    by auto
  hence "poly p x = 0"
    by (simp add: p'_def)
  also have "poly p x = (\<Sum>k\<le>n. f k * x ^ k)"
    unfolding poly_altdef by (intro sum.cong) (auto simp: deg_p coeff_p)
  finally show "\<exists>x. (\<Sum>k\<le>n. f k * x ^ k) = 0" ..
qed


text \<open>
  We can now prove by induction that every polynomial of degree \<open>n\<close> splits into a product of
  \<open>n\<close> linear factors:
\<close>
lemma alg_closed_imp_factorization:
  fixes p :: "'a :: alg_closed_field poly"
  assumes "p \<noteq> 0"
  shows "\<exists>A. size A = degree p \<and> p = smult (lead_coeff p) (\<Prod>x\<in>#A. [:-x, 1:])"
  using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "degree p = 0")
    case True
    thus ?thesis
      by (intro exI[of _ "{#}"]) (auto elim!: degree_eq_zeroE)
  next
    case False
    then obtain x where x: "poly p x = 0"
      using alg_closed_imp_poly_has_root by blast
    hence "[:-x, 1:] dvd p"
      using poly_eq_0_iff_dvd by blast
    then obtain q where p_eq: "p = [:-x, 1:] * q"
      by (elim dvdE)
    have "q \<noteq> 0"
      using less.prems p_eq by auto
    moreover from this have deg: "degree p = Suc (degree q)"
      unfolding p_eq by (subst degree_mult_eq) auto
    ultimately obtain A where A: "size A = degree q" "q = smult (lead_coeff q) (\<Prod>x\<in>#A. [:-x, 1:])"
      using less.hyps[of q] by auto
    have "smult (lead_coeff p) (\<Prod>y\<in>#add_mset x A. [:- y, 1:]) =
          [:- x, 1:] * smult (lead_coeff q) (\<Prod>y\<in>#A. [:- y, 1:])"
      unfolding p_eq lead_coeff_mult by simp
    also note A(2) [symmetric]
    also note p_eq [symmetric]
    finally show ?thesis using A(1)
      by (intro exI[of _ "add_mset x A"]) (auto simp: deg)
  qed
qed

text \<open>
  As an alternative characterisation of algebraic closure, one can also say that any
  polynomial of degree at least 2 splits into non-constant factors:
\<close>
lemma alg_closed_imp_reducible:
  assumes "degree (p :: 'a :: alg_closed_field poly) > 1"
  shows   "\<not>irreducible p"
proof -
  have "degree p > 0"
    using assms by auto
  then obtain z where z: "poly p z = 0"
    using alg_closed_imp_poly_has_root[of p] by blast
  then have dvd: "[:-z, 1:] dvd p"
    by (subst dvd_iff_poly_eq_0) auto
  then obtain q where q: "p = [:-z, 1:] * q"
    by (erule dvdE)
  have [simp]: "q \<noteq> 0"
    using assms q by auto

  show ?thesis
  proof (rule reducible_polyI)
    show "p = [:-z, 1:] * q"
      by fact
  next
    have "degree p = degree ([:-z, 1:] * q)"
      by (simp only: q)
    also have "\<dots> = degree q + 1"
      by (subst degree_mult_eq) auto
    finally show "degree q > 0"
      using assms by linarith
  qed auto
qed

text \<open>
  When proving algebraic closure through reducibility, we can assume w.l.o.g. that the polynomial
  is monic and has a non-zero constant coefficient:
\<close>
lemma alg_closedI_reducible:
  assumes "\<And>p :: 'a poly. degree p > 1 \<Longrightarrow> lead_coeff p = 1 \<Longrightarrow> coeff p 0 \<noteq> 0 \<Longrightarrow>
              \<not>irreducible p"
  shows   "OFCLASS('a :: field, alg_closed_field_class)"
proof
  fix p :: "'a poly" assume p: "degree p > 0" "lead_coeff p = 1"
  show "\<exists>x. poly p x = 0"
  proof (cases "coeff p 0 = 0")
    case True
    hence "poly p 0 = 0"
      by (simp add: poly_0_coeff_0)
    thus ?thesis by blast
  next
    case False
    from p and this show ?thesis
    proof (induction "degree p" arbitrary: p rule: less_induct)
      case (less p)
      show ?case
      proof (cases "degree p = 1")
        case True
        then obtain a b where p: "p = [:a, b:]"
          by (cases p) (auto split: if_splits elim!: degree_eq_zeroE)
        from True have [simp]: "b \<noteq> 0"
          by (auto simp: p)
        have "poly p (-a/b) = 0"
          by (auto simp: p)
        thus ?thesis by blast
      next
        case False
        hence "degree p > 1"
          using less.prems by auto
        from assms[OF \<open>degree p > 1\<close> \<open>lead_coeff p = 1\<close> \<open>coeff p 0 \<noteq> 0\<close>]
        have "\<not>irreducible p" by auto
        then obtain r s where rs: "degree r > 0" "degree s > 0" "p = r * s"
          using less.prems by (auto simp: irreducible_def)
        hence "coeff r 0 \<noteq> 0"
          using \<open>coeff p 0 \<noteq> 0\<close> by (auto simp: coeff_mult_0)

        define r' where "r' = smult (inverse (lead_coeff r)) r"
        have [simp]: "degree r' = degree r"
          by (simp add: r'_def)
        have lc: "lead_coeff r' = 1"
          using rs by (auto simp: r'_def)
        have nz: "coeff r' 0 \<noteq> 0"
          using \<open>coeff r 0 \<noteq> 0\<close> by (auto simp: r'_def)
  
        have "degree r < degree r + degree s"
          using rs by linarith
        also have "\<dots> = degree (r * s)"
          using rs(3) less.prems by (subst degree_mult_eq) auto
        also have "r * s = p"
          using rs(3) by simp
        finally have "\<exists>x. poly r' x = 0"
          by (intro less) (use lc rs nz in auto)
        thus ?thesis
          using rs(3) by (auto simp: r'_def)
      qed
    qed
  qed
qed

text \<open>
  Using a clever Tschirnhausen transformation mentioned e.g. in the article by
  Nowak~\cite{nowak2000}, we can also assume w.l.o.g. that the coefficient $a_{n-1}$ is zero.
\<close>
lemma alg_closedI_reducible_coeff_deg_minus_one_eq_0:
  assumes "\<And>p :: 'a poly. degree p > 1 \<Longrightarrow> lead_coeff p = 1 \<Longrightarrow> coeff p (degree p - 1) = 0 \<Longrightarrow>
              coeff p 0 \<noteq> 0 \<Longrightarrow> \<not>irreducible p"
  shows   "OFCLASS('a :: field_char_0, alg_closed_field_class)"
proof (rule alg_closedI_reducible, goal_cases)
  case (1 p)
  define n where [simp]: "n = degree p"
  define a where "a = coeff p (n - 1)"
  define r where "r = [: -a / of_nat n, 1 :]"
  define s where "s = [: a / of_nat n, 1 :]"
  define q where "q = pcompose p r"

  have "n > 0"
    using 1 by simp
  have r_altdef: "r = monom 1 1 + [:-a / of_nat n:]"
    by (simp add: r_def monom_altdef)
  have deg_q: "degree q = n"
    by (simp add: q_def r_def)
  have lc_q: "lead_coeff q = 1"
    unfolding q_def using 1 by (subst lead_coeff_comp) (simp_all add: r_def)
  have "q \<noteq> 0"
    using 1 deg_q by auto
  
  have "coeff q (n - 1) =
          (\<Sum>i\<le>n. \<Sum>k\<le>i. coeff p i * (of_nat (i choose k) *
            ((-a / of_nat n) ^ (i - k) * (if k = n - 1 then 1 else 0))))"
    unfolding q_def pcompose_altdef poly_altdef r_altdef
    by (simp_all add: degree_map_poly coeff_map_poly coeff_sum binomial_ring sum_distrib_left poly_const_pow
                  sum_distrib_right mult_ac monom_power coeff_monom_mult of_nat_poly cong: if_cong)
  also have "\<dots> = (\<Sum>i\<le>n. \<Sum>k\<in>(if i \<ge> n - 1 then {n-1} else {}).
                     coeff p i * (of_nat (i choose k) * (-a / of_nat n) ^ (i - k)))"
    by (rule sum.cong [OF refl], rule sum.mono_neutral_cong_right) (auto split: if_splits)
  also have "\<dots> = (\<Sum>i\<in>{n-1,n}. \<Sum>k\<in>(if i \<ge> n - 1 then {n-1} else {}).
                     coeff p i * (of_nat (i choose k) * (-a / of_nat n) ^ (i - k)))"
    by (rule sum.mono_neutral_right) auto
  also have "\<dots> = a - of_nat (n choose (n - 1)) * a / of_nat n"
    using 1 by (simp add: a_def)
  also have "n choose (n - 1) = n"
    using \<open>n > 0\<close> by (subst binomial_symmetric) auto
  also have "a - of_nat n * a / of_nat n = 0"
    using \<open>n > 0\<close> by simp
  finally have "coeff q (n - 1) = 0" .

  show ?case
  proof (cases "coeff q 0 = 0")
    case True
    hence "poly p (- (a / of_nat (degree p))) = 0"
      by (auto simp: q_def r_def)
    thus ?thesis
      by (rule root_imp_reducible_poly) (use 1 in auto)
  next
    case False
    hence "\<not>irreducible q"
      using assms[of q] and lc_q and 1 and \<open>coeff q (n - 1) = 0\<close>
      by (auto simp: deg_q)
    then obtain u v where uv: "degree u > 0" "degree v > 0" "q = u * v"
      using \<open>q \<noteq> 0\<close> 1 deg_q by (auto simp: irreducible_def)

    have "p = pcompose q s"
      by (simp add: q_def r_def s_def flip: pcompose_assoc)
    also have "q = u * v"
      by fact
    finally have "p = pcompose u s * pcompose v s"
      by (simp add: pcompose_mult)
    moreover have "degree (pcompose u s) > 0" "degree (pcompose v s) > 0"
      using uv by (simp_all add: s_def)
    ultimately show "\<not>irreducible p"
      using 1 by (intro reducible_polyI)
  qed
qed

text \<open>
  As a consequence of the full factorisation lemma proven above, we can also show that any
  polynomial with at least two different roots splits into two non-constant coprime factors:
\<close>
lemma alg_closed_imp_poly_splits_coprime:
  assumes "degree (p :: 'a :: {alg_closed_field} poly) > 1"
  assumes "poly p x = 0" "poly p y = 0" "x \<noteq> y"
  obtains r s where "degree r > 0" "degree s > 0" "coprime r s" "p = r * s"
proof -
  define n where "n = order x p"
  have "n > 0"
    using assms by (metis degree_0 gr0I n_def not_one_less_zero order_root)
  have "[:-x, 1:] ^ n dvd p"
    unfolding n_def by (simp add: order_1)
  then obtain q where p_eq: "p = [:-x, 1:] ^ n * q"
    by (elim dvdE)
  from assms have [simp]: "q \<noteq> 0"
    by (auto simp: p_eq)
  have "order x p = n + Polynomial.order x q"
    unfolding p_eq by (subst order_mult) (auto simp: order_power_n_n)
  hence "Polynomial.order x q = 0"
    by (simp add: n_def)
  hence "poly q x \<noteq> 0"
    by (simp add: order_root)

  show ?thesis
  proof (rule that)
    show "coprime ([:-x, 1:] ^ n) q"
    proof (rule coprimeI)
      fix d
      assume d: "d dvd [:-x, 1:] ^ n" "d dvd q"
      have "degree d = 0"
      proof (rule ccontr)
        assume "\<not>(degree d = 0)"
        then obtain z where z: "poly d z = 0"
          using alg_closed_imp_poly_has_root by blast
        moreover from this and d(1) have "poly ([:-x, 1:] ^ n) z = 0"
          using dvd_trans poly_eq_0_iff_dvd by blast
        ultimately have "poly d x = 0"
          by auto
        with d(2) have "poly q x = 0"
          using dvd_trans poly_eq_0_iff_dvd by blast
        with \<open>poly q x \<noteq> 0\<close> show False by contradiction
      qed
      thus "is_unit d" using d
        by auto
    qed
  next
    have "poly q y = 0"
      using \<open>poly p y = 0\<close> \<open>x \<noteq> y\<close> by (auto simp: p_eq)
    with \<open>q \<noteq> 0\<close> show "degree q > 0"
      using poly_zero by blast
  qed (use \<open>n > 0\<close> in \<open>simp_all add: p_eq degree_power_eq\<close>)
qed

instance complex :: alg_closed_field
  by standard (use constant_degree fundamental_theorem_of_algebra neq0_conv in blast)

end