(*
  File:     More_Polynomial_HLW.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>Auxiliary facts about univariate polynomials\<close>
theory More_Polynomial_HLW
imports
  "HOL-Computational_Algebra.Computational_Algebra"
  "Polynomial_Factorization.Gauss_Lemma"
  "Power_Sum_Polynomials.Power_Sum_Polynomials_Library"
  "Algebraic_Numbers.Algebraic_Numbers"
begin

instance poly :: ("{idom_divide,normalization_semidom_multiplicative,factorial_ring_gcd,
                    semiring_gcd_mult_normalize}") factorial_semiring_multiplicative ..

lemma lead_coeff_prod_mset:
  fixes A :: "'a::{comm_semiring_1, semiring_no_zero_divisors} poly multiset"
  shows "Polynomial.lead_coeff (prod_mset A) = prod_mset (image_mset Polynomial.lead_coeff A)"
  by (induction A) (auto simp: Polynomial.lead_coeff_mult)

lemma content_normalize [simp]:
  fixes p :: "'a :: {factorial_semiring, idom_divide, semiring_gcd, normalization_semidom_multiplicative} poly"
  shows "content (normalize p) = content p"
proof (cases "p = 0")
  case [simp]: False
  have "content p = content (unit_factor p * normalize p)"
    by simp
  also have "\<dots> = content (unit_factor p) * content (normalize p)"
    by (rule content_mult)
  also have "content (unit_factor p) = 1"
    by (auto simp: unit_factor_poly_def)
  finally show ?thesis by simp
qed auto

lemma rat_to_normalized_int_poly_exists:
  fixes p :: "rat poly"
  assumes "p \<noteq> 0"
  obtains q lc where "p = Polynomial.smult lc (of_int_poly q)" "lc > 0" "content q = 1"
proof -
  define lc where "lc = fst (rat_to_normalized_int_poly p)"
  define q where "q = snd (rat_to_normalized_int_poly p)"
  have eq: "rat_to_normalized_int_poly p = (lc, q)"
    by (simp add: lc_def q_def)
  show ?thesis
    using rat_to_normalized_int_poly[OF eq] assms
    by (intro that[of lc q]) auto
qed

lemma irreducible_imp_squarefree:
  assumes "irreducible p"
  shows   "squarefree p"
proof (rule squarefreeI)
  fix q assume "q ^ 2 dvd p"
  then obtain r where qr: "p = q ^ 2 * r"
    by (elim dvdE)
  have "q dvd 1 \<or> q * r dvd 1"
    by (intro irreducibleD[OF assms]) (use qr in \<open>simp_all add: power2_eq_square mult_ac\<close>)
  thus "q dvd 1"
    by (meson dvd_mult_left)
qed

lemma squarefree_imp_rsquarefree:
  fixes p :: "'a :: idom poly"
  assumes "squarefree p"
  shows   "rsquarefree p"
  unfolding rsquarefree_def
proof (intro conjI allI)
  fix x :: 'a
  have "Polynomial.order x p < 2"
  proof (rule ccontr)
    assume "\<not>(Polynomial.order x p < 2)"
    hence "[:-x, 1:] ^ 2 dvd p"
      by (subst order_divides) auto
    from assms and this have "[:-x, 1:] dvd 1"
      by (rule squarefreeD)
    hence "Polynomial.degree [:-x, 1:] \<le> Polynomial.degree (1 :: 'a poly)"
      by (rule dvd_imp_degree_le) auto
    thus False by simp
  qed
  thus "Polynomial.order x p = 0 \<or> Polynomial.order x p = 1"
    by linarith
qed (use assms in auto)

lemma squarefree_imp_coprime_pderiv:
  fixes p :: "'a :: {factorial_ring_gcd,semiring_gcd_mult_normalize,semiring_char_0} poly"
  assumes "squarefree p" and "content p = 1"
  shows   "Rings.coprime p (pderiv p)"
proof (rule coprimeI_primes)
  fix d assume d: "prime d" "d dvd p" "d dvd pderiv p"
  show False
  proof (cases "Polynomial.degree d = 0")
    case deg: False
    obtain q where dq: "p = d * q"
      using d by (elim dvdE)
    have \<open>d dvd q * pderiv d\<close>
      using d by (simp add: dq pderiv_mult dvd_add_right_iff)
    moreover have "\<not>d dvd pderiv d"
    proof
      assume "d dvd pderiv d"
      hence "Polynomial.degree d \<le> Polynomial.degree (pderiv d)"
        using d deg by (intro dvd_imp_degree_le) (auto simp: pderiv_eq_0_iff)
      hence "Polynomial.degree d = 0"
        by (subst (asm) degree_pderiv) auto
      thus False using deg by contradiction
    qed
    ultimately have "d dvd q"
      using d(1) by (simp add: prime_dvd_mult_iff)
    hence "d ^ 2 dvd p"
      by (auto simp: dq power2_eq_square)
    from assms(1) and this have "is_unit d"
      by (rule squarefreeD)
    thus False using \<open>prime d\<close> by auto
  next
    case True
    then obtain d' where [simp]: "d = [:d':]"
      by (elim degree_eq_zeroE)
    from d have "d' dvd content p"
      by (simp add: const_poly_dvd_iff_dvd_content)
    with assms and prime_imp_prime_elem[OF \<open>prime d\<close>] show False
      by (auto simp: prime_elem_const_poly_iff)
  qed
qed (use assms in auto)

lemma irreducible_imp_coprime_pderiv:
  fixes p :: "'a :: {idom_divide,semiring_char_0} poly"
  assumes "irreducible p" "Polynomial.degree p \<noteq> 0"
  shows   "Rings.coprime p (pderiv p)"
proof (rule Rings.coprimeI)
  fix d assume d: "d dvd p" "d dvd pderiv p"
  obtain q where dq: "p = d * q"
    using d by (elim dvdE)
  have "is_unit d \<or> is_unit q"
    using assms dq by (auto simp: irreducible_def)
  thus "is_unit d"
  proof
    assume unit: "is_unit q"
    with d have "p dvd pderiv p"
      using algebraic_semidom_class.mult_unit_dvd_iff dq by blast
    hence "Polynomial.degree p = 0"
      by (meson not_dvd_pderiv)
    with assms(2) show ?thesis by contradiction
  qed
qed

lemma poly_gcd_eq_0I:
  assumes "poly p x = 0" "poly q x = 0"
  shows   "poly (gcd p q) x = 0"
  using assms by (simp add: poly_eq_0_iff_dvd)

lemma poly_eq_0_coprime:
  assumes "Rings.coprime p q" "p \<noteq> 0" "q \<noteq> 0"
  shows   "poly p x \<noteq> 0 \<or> poly q x \<noteq> 0"
proof -
  have False if "poly p x = 0" "poly q x = 0"
  proof -
    have "[:-x, 1:] dvd p" "[:-x, 1:] dvd q"
      using that by (simp_all add: poly_eq_0_iff_dvd)
    hence "[:-x, 1:] dvd 1"
      using \<open>Rings.coprime p q\<close> by (meson not_coprimeI)
    thus False
      by (simp add: is_unit_poly_iff)
  qed
  thus ?thesis
    by blast
qed

lemma coprime_of_int_polyI:
  assumes "Rings.coprime p q"
  shows   "Rings.coprime (of_int_poly p) (of_int_poly q :: 'a :: {field_char_0,field_gcd} poly)"
  using assms gcd_of_int_poly[of p q, where ?'a = 'a] unfolding coprime_iff_gcd_eq_1 by simp

lemma irreducible_imp_rsquarefree_of_int_poly:
  fixes p :: "int poly"
  assumes "irreducible p" and "Polynomial.degree p > 0"
  shows   "rsquarefree (of_int_poly p :: 'a :: {field_gcd, field_char_0} poly)"
proof -
  {
    fix x :: 'a
    assume x: "poly (of_int_poly p) x = 0" "poly (pderiv (of_int_poly p)) x = 0"
    define d where "d = gcd (of_int_poly p) (pderiv (of_int_poly p) :: 'a poly)"
    have "poly d x = 0"
      using x unfolding d_def by (intro poly_gcd_eq_0I) auto
    moreover have "d \<noteq> 0"
      using assms by (auto simp: d_def)
    ultimately have "0 < Polynomial.degree d"
      by (intro Nat.gr0I) (auto elim!: degree_eq_zeroE)
    also have "Polynomial.degree d = Polynomial.degree (gcd p (pderiv p))"
      unfolding d_def of_int_hom.map_poly_pderiv[symmetric] gcd_of_int_poly by simp
    finally have deg: "\<dots> > 0" .
  
    have "gcd p (pderiv p) dvd p"
      by auto
    from irreducibleD'[OF assms(1) this] and deg have "p dvd gcd p (pderiv p)"
      by auto
    also have "\<dots> dvd pderiv p"
      by auto
    finally have "Polynomial.degree p = 0"
      by auto
    with assms have False by simp
  }
  thus ?thesis by (auto simp: rsquarefree_roots)
qed

lemma squarefree_of_int_polyI:
  assumes "squarefree p" "content p = 1"
  shows   "squarefree (of_int_poly p :: 'a :: {field_char_0,field_gcd} poly)"
proof -
  have "Rings.coprime p (pderiv p)"
    by (rule squarefree_imp_coprime_pderiv) fact+
  hence "Rings.coprime (of_int_poly p :: 'a poly) (of_int_poly (pderiv p))"
    by (rule coprime_of_int_polyI)
  also have "of_int_poly (pderiv p) = pderiv (of_int_poly p :: 'a poly)"
    by (simp add: of_int_hom.map_poly_pderiv)
  finally show ?thesis
    using coprime_pderiv_imp_squarefree by blast
qed

lemma higher_pderiv_pcompose_linear:
   "(pderiv ^^ n) (pcompose p [:0, c:]) =
    Polynomial.smult (c ^ n) (pcompose ((pderiv ^^ n) p) [:0, c:])"
  by (induction n)  (simp_all add: pderiv_pcompose pderiv_smult pderiv_pCons pcompose_smult mult_ac)

lemma poly_poly_eq:
  "poly (poly p [:x:]) y = poly (eval_poly (\<lambda>p. [:poly p y:]) p [:0, 1:]) x"
  by (induction p) (auto simp: eval_poly_def)

lemma poly_poly_poly_y_x [simp]:
  fixes p :: "'a :: idom poly poly"
  shows "poly (poly (poly_y_x p) [:y:]) x = poly (poly p [:x:]) y"
proof (induction p)
  case (pCons a p)
  have "poly (poly (poly_y_x (pCons a p)) [:y:]) x = 
          poly a y + poly (poly (map_poly (pCons 0) (poly_y_x p)) [:y:]) x"
    by (simp add: poly_y_x_pCons eval_poly_def)
  also have "pCons 0 = (\<lambda>p::'a poly. Polynomial.monom 1 1 * p)"
    by (simp add: Polynomial.monom_altdef)
  also have "map_poly \<dots> (poly_y_x p) = Polynomial.smult (Polynomial.monom 1 1) (poly_y_x p)"
    by (simp add: smult_conv_map_poly)
  also have "poly \<dots> [:y:] = Polynomial.monom 1 1 * poly (poly_y_x p) [:y:]"
    by simp
  also have "poly a y + poly \<dots> x = poly (poly (pCons a p) [:x:]) y"
    by (simp add: pCons poly_monom)
  finally show ?case .
qed auto

lemma (in idom_hom) map_poly_higher_pderiv [hom_distribs]:
  "map_poly hom ((pderiv ^^ n) p) = (pderiv ^^ n) (map_poly hom p)"
  by (induction n) (simp_all add: map_poly_pderiv)

lemma coeff_prod_linear_factors:
  fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1"
  assumes [intro]: "finite A"
  shows "Polynomial.coeff (\<Prod>x\<in>A. [:-f x, 1:] ^ e x) i =
           (\<Sum>X | X \<in> Pow (SIGMA x:A. {..<e x}) \<and> i = sum e A - card X.
             (-1) ^ card X * (\<Prod>x\<in>X. f (fst x)))"
proof -
  define poly_X where "poly_X = (Polynomial.monom 1 1 :: 'b poly)"
  have [simp]: "(- 1) ^ n = [:(- 1) ^ n :: 'b:]" for n :: nat
    by (simp flip: pCons_one add: poly_const_pow)
  have "(\<Prod>x\<in>A. [:-f x, 1:] ^ e x) = (\<Prod>(x,_)\<in>Sigma A (\<lambda>x. {..<e x}). [:-f x, 1:])"
    by (subst prod.Sigma [symmetric]) auto
  also have "\<dots> = (\<Prod>(x,_)\<in>Sigma A (\<lambda>x. {..<e x}). poly_X - [:f x:])"
    by (intro prod.cong) (auto simp: poly_X_def monom_altdef)
  also have "\<dots> = (\<Sum>X\<in>Pow (SIGMA x:A. {..<e x}).
                    Polynomial.smult ((-1) ^ card X * (\<Prod>x\<in>X. f (fst x)))
                    (poly_X ^ card ((SIGMA x:A. {..<e x}) - X)))"
    unfolding case_prod_unfold 
    by (subst prod_diff1) (auto simp: mult_ac simp flip: coeff_lift_hom.hom_prod)
  also have "\<dots> = (\<Sum>X\<in>Pow (SIGMA x:A. {..<e x}).
       Polynomial.monom ((- 1) ^ card X * (\<Prod>x\<in>X. f (fst x))) (card ((SIGMA x:A. {..<e x}) - X)))"
    unfolding poly_X_def monom_power Polynomial.smult_monom by simp
  also have "Polynomial.coeff \<dots> i = (\<Sum>X\<in>{X\<in>Pow (SIGMA x:A. {..<e x}). i =
               sum e A - card X}. (- 1) ^ card X * (\<Prod>x\<in>X. f (fst x)))"
    unfolding Polynomial.coeff_sum
  proof (intro sum.mono_neutral_cong_right ballI, goal_cases)
    case (3 X)
    hence X: "X \<subseteq> (SIGMA x:A. {..<e x})"
      by auto
    have card_le: "card X \<le> card (SIGMA x:A. {..<e x})"
      using X by (intro card_mono) auto
    have "finite X"
      by (rule finite_subset[OF X]) auto
    hence "card ((SIGMA x:A. {..<e x}) - X) = card (SIGMA x:A. {..<e x}) - card X"
      using 3 by (intro card_Diff_subset) auto
    also have card_eq: "card (SIGMA x:A. {..<e x}) = sum e A"
      by (subst card_SigmaI) auto
    finally show ?case
      using 3 card_le card_eq by (auto simp: algebra_simps)
  next
    case (4 X)
    hence X: "X \<subseteq> (SIGMA x:A. {..<e x})"
      by auto
    have "finite X"
      by (rule finite_subset[OF X]) auto
    hence "card ((SIGMA x:A. {..<e x}) - X) = card (SIGMA x:A. {..<e x}) - card X"
      using 4 by (intro card_Diff_subset) auto
    also have card_eq: "card (SIGMA x:A. {..<e x}) = sum e A"
      by (subst card_SigmaI) auto
    finally show ?case
      using 4 card_eq by (auto simp: algebra_simps)
  qed auto
  finally show ?thesis .
qed

lemma (in comm_ring_hom) synthetic_div_hom:
  "synthetic_div (map_poly hom p) (hom x) = map_poly hom (synthetic_div p x)"
  by (induction p) (auto simp: map_poly_pCons_hom)

lemma synthetic_div_altdef:
  fixes p :: "'a :: field poly"
  shows "synthetic_div p c = p div [:-c, 1:]"
proof -
  define q where "q = p div [:- c, 1:]"
  have "Polynomial.degree (p mod [:-c, 1:]) = 0"
  proof (cases "p mod [:-c, 1:] = 0")
    case False
    hence "Polynomial.degree (p mod [:-c, 1:]) < Polynomial.degree [:-c, 1:]"
      by (intro degree_mod_less') auto
    thus ?thesis by simp
  qed auto
  then obtain d where d: "p mod [:-c, 1:] = [:d:]"
    by (elim degree_eq_zeroE)

  have p_eq: "p = q * [:-c, 1:] + [:d:]"
    unfolding q_def d [symmetric] by presburger
  have [simp]: "poly p c = d"
    by (simp add: p_eq)
  have "p + Polynomial.smult c q = pCons (poly p c) q"
    by (subst p_eq) auto
  from synthetic_div_unique[OF this] show ?thesis
    by (auto simp: q_def)
qed

lemma (in ring_closed) poly_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A" "x \<in> A"
  shows   "poly p x \<in> A"
  unfolding poly_altdef by (intro sum_closed mult_closed power_closed assms)

lemma (in ring_closed) coeff_pCons_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A" "x \<in> A"
  shows   "poly.coeff (pCons x p) i \<in> A"
  unfolding poly_altdef using assms by (auto simp: coeff_pCons split: nat.splits)

lemma (in ring_closed) coeff_poly_mult_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A" "\<And>i. poly.coeff q i \<in> A"
  shows   "poly.coeff (p * q) i \<in> A"
  unfolding coeff_mult using assms by auto

lemma (in ring_closed) coeff_poly_prod_closed [intro]:
  assumes "\<And>x i. x \<in> X \<Longrightarrow> poly.coeff (f x) i \<in> A"
  shows   "poly.coeff (prod f X) i \<in> A"
  using assms by (induction X arbitrary: i rule: infinite_finite_induct) auto

lemma (in ring_closed) coeff_poly_power_closed [intro]:
  assumes "\<And>i. poly.coeff p i \<in> A"
  shows   "poly.coeff (p ^ n) i \<in> A"
  using coeff_poly_prod_closed[of "{..<n}" "\<lambda>_. p" i] assms by simp

lemma (in ring_closed) synthetic_div_closed:
  assumes "\<And>i. poly.coeff p i \<in> A" "x \<in> A"
  shows   "poly.coeff (synthetic_div p x) i \<in> A"
proof -
  from assms(1) have "\<forall>i. poly.coeff p i \<in> A"
    by blast
  from this and assms(2) show ?thesis
    by (induction p arbitrary: i) (auto simp: coeff_pCons split: nat.splits)
qed

lemma pcompose_monom: "pcompose (Polynomial.monom c n) p = Polynomial.smult c (p ^ n)"
  by (simp add: monom_altdef pcompose_hom.hom_power pcompose_smult)

lemma poly_roots_uminus [simp]: "poly_roots (-p) = poly_roots p"
  using poly_roots_smult[of "-1" p] by (simp del: poly_roots_smult)

lemma poly_roots_normalize [simp]:
  fixes p :: "'a :: {normalization_semidom, idom_divide} poly"
  shows "poly_roots (normalize p) = poly_roots p"
proof (cases "p = 0")
  case [simp]: False
  have "poly_roots p = poly_roots (unit_factor p * normalize p)"
    by simp
  also have "\<dots> = poly_roots (normalize p)"
    unfolding unit_factor_poly_def by simp
  finally show ?thesis ..
qed auto


lemma poly_roots_of_int_normalize [simp]:
  "poly_roots (of_int_poly (normalize p) :: 'a :: {idom, ring_char_0} poly) =
   poly_roots (of_int_poly p)"
proof (cases "p = 0")
  case [simp]: False
  have "poly_roots (of_int_poly p :: 'a poly) = poly_roots (of_int_poly (unit_factor p * normalize p))"
    by simp
  also have "\<dots> = poly_roots (Polynomial.smult (of_int (sgn (Polynomial.lead_coeff p)))
                    (of_int_poly (normalize p)))"
    by (simp add: unit_factor_poly_def of_int_hom.map_poly_hom_smult)
  also have "\<dots> = poly_roots (Ring_Hom_Poly.of_int_poly (normalize p) :: 'a poly)"
    by (intro poly_roots_smult) (auto simp: sgn_if)
  finally show ?thesis ..
qed auto

lemma poly_roots_power [simp]: "poly_roots (p ^ n) = repeat_mset n (poly_roots p)"
proof (cases "p = 0")
  case True
  thus ?thesis by (cases n) auto
next
  case False
  thus ?thesis by (induction n) (auto simp: poly_roots_mult)
qed

lemma poly_roots_conv_sum_prime_factors:
  "poly_roots q = (\<Sum>p\<in>#prime_factorization q. poly_roots p)"
proof (cases "q = 0")
  case [simp]: False

  have "(\<Sum>p\<in>#prime_factorization q. poly_roots p) =
        poly_roots (prod_mset (prime_factorization q))"
    by (rule poly_roots_prod_mset [symmetric]) auto
  also have "\<dots> = poly_roots (normalize (prod_mset (prime_factorization q)))"
    by simp
  also have "normalize (prod_mset (prime_factorization q)) = normalize q"
    by (rule prod_mset_prime_factorization_weak) auto
  also have "poly_roots \<dots> = poly_roots q"
    by simp
  finally show ?thesis ..
qed auto

lemma poly_roots_of_int_conv_sum_prime_factors:
  "poly_roots (of_int_poly q :: 'a :: {idom, ring_char_0} poly) =
   (\<Sum>p\<in>#prime_factorization q. poly_roots (of_int_poly p))"
proof (cases "q = 0")
  case [simp]: False

  have "(\<Sum>p\<in>#prime_factorization q. poly_roots (of_int_poly p :: 'a poly)) =
        poly_roots (\<Prod>p\<in>#prime_factorization q. of_int_poly p)"
    by (subst poly_roots_prod_mset) (auto simp: multiset.map_comp o_def)
  also have "(\<Prod>p\<in>#prime_factorization q. of_int_poly p :: 'a poly) =
               of_int_poly (prod_mset (prime_factorization q))"
    by simp
  also have "poly_roots \<dots> = poly_roots (of_int_poly (normalize (prod_mset (prime_factorization q))))"
    by (rule poly_roots_of_int_normalize [symmetric])
  also have "normalize (prod_mset (prime_factorization q)) = normalize q"
    by (rule prod_mset_prime_factorization_weak) auto
  also have "poly_roots (of_int_poly \<dots> :: 'a poly) = poly_roots (of_int_poly q)"
    by simp
  finally show ?thesis ..
qed auto

lemma dvd_imp_poly_roots_subset:
  assumes "q \<noteq> 0" "p dvd q"
  shows   "poly_roots p \<subseteq># poly_roots q"
proof -
  from assms have "p \<noteq> 0"
    by auto
  thus ?thesis
    using assms by (intro mset_subset_eqI) (auto intro: dvd_imp_order_le)
qed

lemma abs_prod_mset: "\<bar>prod_mset (A :: 'a :: idom_abs_sgn multiset)\<bar> = prod_mset (image_mset abs A)"
  by (induction A) (auto simp: abs_mult)

lemma content_1_imp_nonconstant_prime_factors:
  assumes "content (p :: int poly) = 1" and "q \<in> prime_factors p"
  shows   "Polynomial.degree q > 0"
proof -
  let ?d = "Polynomial.degree :: int poly \<Rightarrow> nat"
  let ?lc = "Polynomial.lead_coeff :: int poly \<Rightarrow> int"
  define P where "P = prime_factorization p"
  define P1 where "P1 = filter_mset (\<lambda>p. ?d p = 0) P"
  define P2 where "P2 = filter_mset (\<lambda>p. ?d p > 0) P"
  have [simp]: "p \<noteq> 0"
    using assms by auto
  have "1 = content (normalize p)"
    using assms by simp
  also have "normalize p = prod_mset P"
    unfolding P_def by (rule prod_mset_prime_factorization [symmetric]) auto
  also have "P = filter_mset (\<lambda>p. ?d p = 0) P + filter_mset (\<lambda>p. ?d p > 0) P"
    by (induction P) auto
  also have "prod_mset \<dots> = prod_mset P1 * prod_mset P2"
    unfolding P1_def P2_def by (subst prod_mset.union) auto
  also have "content \<dots> = content (prod_mset P1) * content (prod_mset P2)"
    unfolding content_mult ..
  also have "image_mset id P1 = image_mset (\<lambda>q. [:?lc q:]) P1"
    by (intro image_mset_cong) (auto simp: P1_def elim!: degree_eq_zeroE)
  hence "P1 = image_mset (\<lambda>q. [:?lc q:]) P1"
    by simp
  also have "content (prod_mset \<dots>) = \<bar>(\<Prod>q\<in>#P1. ?lc q)\<bar>"
    by (simp add: content_prod_mset multiset.map_comp o_def abs_prod_mset)
  finally have "\<bar>(\<Prod>q\<in>#P1. ?lc q)\<bar> * content (prod_mset P2) = 1" ..
  hence "\<bar>(\<Prod>q\<in>#P1. ?lc q)\<bar> dvd 1"
    unfolding dvd_def by metis

  have "set_mset P1 = {}"
  proof (rule ccontr)
    assume "set_mset P1 \<noteq> {}"
    then obtain q where q: "q \<in># P1"
      by blast
    have "\<bar>?lc q\<bar> dvd (\<Prod>q\<in>#P1. \<bar>?lc q\<bar>)"
      by (rule dvd_prod_mset) (use q in auto)
    also have "\<dots> = \<bar>(\<Prod>q\<in>#P1. ?lc q)\<bar>"
      by (simp add: abs_prod_mset multiset.map_comp o_def)
    also have "\<dots> dvd 1"
      by fact
    finally have "is_unit (?lc q)"
      by simp
    hence "is_unit q"
      using q unfolding P1_def by (auto elim!: degree_eq_zeroE)
    moreover have "prime q"
      using q unfolding P1_def P_def by auto
    ultimately show False by auto
  qed
  with assms show ?thesis
    by (auto simp: P1_def P_def)
qed

end