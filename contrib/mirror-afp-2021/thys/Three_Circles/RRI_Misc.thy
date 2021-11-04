section \<open>Misc results about polynomials\<close>

theory RRI_Misc imports 
  "HOL-Computational_Algebra.Computational_Algebra" 
  "Budan_Fourier.BF_Misc"
  "Polynomial_Interpolation.Ring_Hom_Poly"
begin

subsection \<open>Misc\<close>

declare pcompose_pCons[simp del]

lemma Setcompr_subset: "\<And>f P S. {f x | x. P x} \<subseteq> S = (\<forall> x. P x \<longrightarrow> f x \<in> S)" 
  by blast

lemma map_cong':
  assumes "xs = map h ys" and "\<And>y. y \<in> set ys \<Longrightarrow> f (h y) = g y"
  shows "map f xs = map g ys"
  using assms map_replicate_trivial by simp

lemma nth_default_replicate_eq: 
    "nth_default dflt (replicate n x) i = (if i < n then x else dflt)"
  by (auto simp: nth_default_def)

lemma square_bounded_less: 
  fixes a b::"'a :: linordered_ring_strict"
  shows "-a < b \<and> b < a \<Longrightarrow> b*b < a*a"
  by (metis (no_types, lifting) leD leI minus_less_iff minus_mult_minus mult_strict_mono'
      neg_less_eq_nonneg neg_less_pos verit_minus_simplify(4) zero_le_mult_iff zero_le_square)

lemma square_bounded_le: 
  fixes a b::"'a :: linordered_ring_strict"
  shows "-a \<le> b \<and> b \<le> a \<Longrightarrow> b*b \<le> a*a"
  by (metis le_less minus_mult_minus square_bounded_less)

context vector_space
begin

lemma card_le_dim_spanning:
  assumes BV: "B \<subseteq> V"
    and VB: "V \<subseteq> span B"
    and fB: "finite B"
    and dVB: "dim V \<ge> card B"
  shows "independent B"
proof -
  {
    fix a
    assume a: "a \<in> B" "a \<in> span (B - {a})"
    from a fB have c0: "card B \<noteq> 0"
      by auto
    from a fB have cb: "card (B - {a}) = card B - 1"
      by auto
    {
      fix x
      assume x: "x \<in> V"
      from a have eq: "insert a (B - {a}) = B"
        by blast
      from x VB have x': "x \<in> span B"
        by blast
      from span_trans[OF a(2), unfolded eq, OF x']
      have "x \<in> span (B - {a})" .
    }
    then have th1: "V \<subseteq> span (B - {a})"
      by blast
    have th2: "finite (B - {a})"
      using fB by auto
    from dim_le_card[OF th1 th2]
    have c: "dim V \<le> card (B - {a})" .
    from c c0 dVB cb have False by simp
  }
  then show ?thesis
    unfolding dependent_def by blast
qed

end

subsection \<open>Misc results about polynomials\<close>

lemma smult_power: "smult (x^n) (p^n) = smult x p ^ n"
  apply (induction n)
  subgoal by fastforce
  by (metis (no_types, hide_lams) mult_smult_left mult_smult_right 
      power_Suc smult_smult)

lemma reflect_poly_monom: "reflect_poly (monom n i) = monom n 0"
  apply (induction i)
  by (auto simp: coeffs_eq_iff coeffs_monom coeffs_reflect_poly)

lemma poly_eq_by_eval: 
  fixes P Q :: "'a::{comm_ring_1,ring_no_zero_divisors,ring_char_0} poly"
  assumes h: "\<And>x. poly P x = poly Q x" shows "P = Q"
proof -
  have "poly P = poly Q" using h by fast
  thus ?thesis by (auto simp: poly_eq_poly_eq_iff)
qed

lemma poly_binomial: 
  "[:(1::'a::comm_ring_1), 1:]^n = (\<Sum>k\<le>n. monom (of_nat (n choose k)) k)"
proof -
  have "[:(1::'a::comm_ring_1), 1:]^n = (monom 1 1 + 1)^n"
    by (metis (no_types, lifting) add.left_neutral add.right_neutral add_pCons
        monom_altdef pCons_one power_one_right smult_1_left)
  also have "... = (\<Sum>k\<le>n. of_nat (n choose k) * monom 1 1 ^ k)"
    apply (subst binomial_ring)
    by force
  also have "... = (\<Sum>k\<le>n. monom (of_nat (n choose k)) k)"
    by (auto simp: monom_altdef of_nat_poly)
  finally show ?thesis .
qed

lemma degree_0_iff: "degree P = 0 \<longleftrightarrow> (\<exists>a. P = [:a:])"
  by (meson degree_eq_zeroE degree_pCons_0)

interpretation poly_vs: vector_space smult
  by (simp add: vector_space_def smult_add_right smult_add_left)

lemma degree_subspace: "poly_vs.subspace {x. degree x \<le> n}"
  by (auto simp: poly_vs.subspace_def degree_add_le)

lemma monom_span: 
  "poly_vs.span {monom 1 x | x. x \<le> p} = {(x::'a::field poly). degree x \<le> p}"
(is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix x assume "x \<in> ?L"
    moreover have hfin: "finite {P. \<exists>x \<in> {..p}. P = monom 1 x}"
      by auto
    ultimately have 
      "x \<in> range (\<lambda>u. \<Sum>v\<in>{monom 1 x | x. x \<in> {..p}}. smult (u v) v)"
      by (simp add: poly_vs.span_finite)
    hence "\<exists> u. x = (\<Sum>v\<in>{monom 1 x | x. x \<in> {..p}}. smult (u v) v)"
      by (auto simp: image_iff)
    then obtain u 
      where p': "x = (\<Sum>v\<in>{monom 1 x | x. x \<in> {..p}}. smult (u v) v)"
      by blast
    have "\<And>v. v \<in> {monom 1 x | x. x \<in> {..p}} \<Longrightarrow> degree (smult (u v) v) \<le> p"
      by (auto simp add: degree_monom_eq)
    hence "degree x \<le> p" using hfin
      apply (subst p')
      apply (rule degree_sum_le)
      by auto
    thus "x \<in> {x. degree x \<le> p}" by force
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix x assume "x \<in> ?R"
    hence "degree x \<le> p" by force
    hence "x = (\<Sum>i\<le>p. monom (coeff x i) i)"
      by (simp add: poly_as_sum_of_monoms')
    also have
      "... = (\<Sum>i\<le>p. smult (coeff x (degree (monom (1::'a) i))) (monom 1 i))"
      by (auto simp add: smult_monom degree_monom_eq)
    also have
      "... = (\<Sum>v\<in>{monom 1 x | x. x \<in> {..p}}. smult ((\<lambda>v. coeff x (degree v)) v) v)"
    proof (rule sum.reindex_cong)
      show "inj_on degree {monom (1::'a) x |x. x \<in> {..p}}"
      proof
        fix x 
        assume "x \<in> {monom (1::'a) x |x. x \<in> {..p}}" 
        hence "\<exists> a. x = monom 1 a" by blast
        then obtain a where hx: "x = monom 1 a" by blast
        fix y 
        assume "y \<in> {monom (1::'a) x |x. x \<in> {..p}}" 
        hence "\<exists> b. y = monom 1 b" by blast
        then obtain b where hy: "y = monom 1 b" by blast
        assume "degree x = degree y"
        thus "x = y" using hx hy by (simp add: degree_monom_eq)
      qed
      show "{..p} = degree ` {monom (1::'a) x |x. x \<in> {..p}}"
      proof
        show "{..p} \<subseteq> degree ` {monom (1::'a) x |x. x \<in> {..p}}"
        proof
          fix x assume "x \<in> {..p}"
          hence "monom (1::'a) x \<in> {monom 1 x |x. x \<in> {..p}}" by force
          moreover have "degree (monom (1::'a) x) = x"
            by (simp add: degree_monom_eq)
          ultimately show "x \<in> degree ` {monom (1::'a) x |x. x \<in> {..p}}" by auto
        qed
        show "degree ` {monom (1::'a) x |x. x \<in> {..p}} \<subseteq> {..p}"
          by (auto simp add: degree_monom_eq)
      qed
    next
      fix y assume "y \<in> {monom (1::'a) x |x. x \<in> {..p}}"
      hence "\<exists>z \<in> {..p}. y = monom (1::'a) z" by blast
      then obtain z where "y = monom (1::'a) z" by blast
      thus 
        "smult (coeff x (degree (monom (1::'a) (degree y)))) (monom (1::'a) (degree y)) =
         smult (coeff x (degree y)) y"
        by (simp add: smult_monom degree_monom_eq)
    qed
    finally have "x = (\<Sum>v\<in>{monom 1 x | x. x \<in> {..p}}. 
                      smult ((\<lambda>v. coeff x (degree v)) v) v)" .
    thus "x \<in> ?L" by (auto simp add: poly_vs.span_finite)
  qed
qed

lemma monom_independent: 
  "poly_vs.independent {monom (1::'a::field) x | x. x \<le> p}"
proof (rule poly_vs.independent_if_scalars_zero)
  fix f::"'a poly \<Rightarrow> 'a"
  assume h: "(\<Sum>x\<in>{monom 1 x |x. x \<le> p}. smult (f x) x) = 0"
  have h': "(\<Sum>i\<le>p. monom (f (monom (1::'a) i)) i) = 
            (\<Sum>x\<in>{monom (1::'a) x |x. x \<le> p}. smult (f x) x)"
  proof (rule sum.reindex_cong)
    show "inj_on degree {monom (1::'a) x |x. x \<le> p}"
      by (smt (verit) degree_monom_eq inj_on_def mem_Collect_eq zero_neq_one)
    show "{..p} = degree ` {monom (1::'a) x |x. x \<le> p}"
    proof
      show "{..p} \<subseteq> degree ` {monom (1::'a) x |x. x \<le> p}"
      proof
        fix x assume "x \<in> {..p}"
        then have "x = degree (monom (1::'a) x) \<and> x \<le> p"
          by (auto simp: degree_monom_eq)
        thus "x \<in> degree ` {monom (1::'a) x |x. x \<le> p}" 
          by blast
      qed
      show "degree ` {monom (1::'a) x |x. x \<le> p} \<subseteq> {..p}"
        by (force simp: degree_monom_eq)
    qed
  qed (auto simp: degree_monom_eq smult_monom)

  fix x::"'a poly"
  assume "x \<in> {monom 1 x |x. x \<le> p}"
  then obtain y where "y \<le> p" and "x = monom 1 y" by blast
  hence "f x = coeff (\<Sum>x\<in>{monom 1 x |x. x \<le> p}. smult (f x) x) y"
    by (auto simp: coeff_sum h'[symmetric])
  thus "f x = 0"
    using h by auto
qed force

lemma dim_degree: "poly_vs.dim {x. degree x \<le> n} = n + 1"
  using poly_vs.dim_eq_card_independent[OF monom_independent]
  by (auto simp: monom_span[symmetric] card_image image_Collect[symmetric]
      inj_on_def monom_eq_iff')

lemma degree_div: 
  fixes p q::"('a::idom_divide) poly" 
  assumes "q dvd p"
  shows "degree (p div q) = degree p - degree q" using assms
  by (metis (no_types, lifting) add_diff_cancel_left' degree_0 degree_mult_eq 
      diff_add_zero diff_zero div_by_0 dvd_div_eq_0_iff dvd_mult_div_cancel)

lemma lead_coeff_div: 
  fixes p q::"('a::{idom_divide, inverse}) poly" 
  assumes "q dvd p"
  shows "lead_coeff (p div q) = lead_coeff p / lead_coeff q" using assms
  by (smt (z3) div_by_0 dvd_div_mult_self lead_coeff_mult leading_coeff_0_iff
      nonzero_mult_div_cancel_right)

lemma complex_poly_eq: 
  "r = map_poly of_real (map_poly Re r) + smult \<i> (map_poly of_real (map_poly Im r))"
  by (auto simp: poly_eq_iff coeff_map_poly complex_eq)

lemma complex_poly_cong: 
  "(map_poly Re p = map_poly Re q \<and> map_poly Im p = map_poly Im q) = (p = q)" 
  by (metis complex_poly_eq)

lemma map_poly_Im_of_real: "map_poly Im (map_poly of_real p) = 0"
  by (auto simp: poly_eq_iff coeff_map_poly)

lemma mult_map_poly_imp_map_poly: 
  assumes "map_poly complex_of_real q = r * map_poly complex_of_real p" 
          "p \<noteq> 0"
  shows "r = map_poly complex_of_real (map_poly Re r)"
proof -
  have h: "Im \<circ> (*) \<i> \<circ> complex_of_real = id" by fastforce
  have "map_poly complex_of_real q = r * map_poly complex_of_real p" 
    using assms by blast
  also have "... = (map_poly of_real (map_poly Re r) + 
                    smult \<i> (map_poly of_real (map_poly Im r))) *
                   map_poly complex_of_real p"
    using complex_poly_eq by fastforce
  also have "... = map_poly of_real (map_poly Re r * p) + 
                   smult \<i> (map_poly of_real (map_poly Im r * p))"
    by (simp add: mult_poly_add_left)
  finally have "map_poly complex_of_real q = 
                map_poly of_real (map_poly Re r * p) + 
                smult \<i> (map_poly of_real (map_poly Im r * p))" .
  hence "0 = map_poly Im (map_poly of_real (map_poly Re r * p) + 
             smult \<i> (map_poly of_real (map_poly Im r * p)))"
    by (auto simp: complex_poly_cong[symmetric] map_poly_Im_of_real)
  also have "... = map_poly of_real (map_poly Im r * p)"
    apply (rule poly_eqI)
    by (auto simp: coeff_map_poly coeff_mult)
  finally have "0 = map_poly complex_of_real (map_poly Im r) *
                    map_poly complex_of_real p" 
    by auto
  hence "map_poly complex_of_real (map_poly Im r) = 0" using assms by fastforce
  thus ?thesis apply (subst complex_poly_eq) by auto
qed

lemma map_poly_dvd: 
  fixes p q::"real poly"
  assumes hdvd: "map_poly complex_of_real p dvd 
                    map_poly complex_of_real q" "q \<noteq> 0"
  shows "p dvd q" 
proof -
  from hdvd obtain r 
    where h:"map_poly complex_of_real q = r * map_poly complex_of_real p"
    by fastforce
  hence "r = map_poly complex_of_real (map_poly Re r)" 
    using mult_map_poly_imp_map_poly assms by force
  hence "map_poly complex_of_real q = map_poly complex_of_real (p * map_poly Re r)" 
    using h by auto
  hence "q = p * map_poly Re r" using of_real_poly_eq_iff by blast
  thus "p dvd q" by force
qed

lemma div_poly_eq_0: 
  fixes p q::"('a::idom_divide) poly" 
  assumes "q dvd p" "poly (p div q) x = 0" "q \<noteq> 0"
  shows "poly p x = 0"
  using assms by fastforce

lemma poly_map_poly_of_real_cnj: 
    "poly (map_poly of_real p) (cnj z) = cnj (poly (map_poly of_real p) z)"
  apply (induction p)
  by auto

text \<open>
An induction rule on real polynomials, if $P \neq 0$ then either $(X-x)|P$ or 
$(X-z)(X-cnj z)|P$, we induct by dividing by these polynomials.
\<close>
lemma real_poly_roots_induct: 
  fixes P::"real poly \<Rightarrow> bool" and p::"real poly"
  assumes IH_real: "\<And>p x. P p \<Longrightarrow> P (p * [:-x, 1:])"
      and IH_complex: "\<And>p a b. b \<noteq> 0 \<Longrightarrow> P p 
              \<Longrightarrow> P (p * [: a*a + b*b, -2*a, 1 :])"
      and H0: "\<And>a. P [:a:]"
  defines "d \<equiv> degree p"
  shows "P p"
  using d_def
proof (induction d arbitrary: p rule: less_induct)
  fix p::"real poly"
  assume IH: "(\<And>q. degree q < degree p \<Longrightarrow> P q)"
  show "P p"
  proof (cases "0 = degree p")
    fix p::"real poly" assume "0 = degree p"
    hence "\<exists> a. p = [:a:]"
      by (simp add: degree_0_iff)
    thus "P p" using H0 by blast
  next
    assume hdeg: "0 \<noteq> degree p" 
    hence "\<not> constant (poly (map_poly of_real p))"
      by (metis (no_types, hide_lams) constant_def constant_degree
          of_real_eq_iff of_real_poly_map_poly)
    then obtain z::complex where h: "poly (map_poly of_real p) z = 0" 
      using fundamental_theorem_of_algebra by blast
    show "P p"
    proof cases
      assume "Im z = 0"
      hence "z = Re z" by (simp add: complex_is_Real_iff)
      moreover have "[:-z, 1:] dvd map_poly of_real p" 
        using h poly_eq_0_iff_dvd by blast
      ultimately have "[:-(Re z), 1:] dvd p"
        by (smt (z3) dvd_iff_poly_eq_0 h of_real_0 of_real_eq_iff of_real_poly_map_poly)
      hence 2:"P (p div [:-Re z, 1:])"
        apply (subst IH)
        using hdeg by (auto simp: degree_div)
      moreover have 1:"p = (p div [:- Re z, 1:]) * [:-Re z, 1:]"
        by (metis \<open>[:- Re z, 1:] dvd p\<close> dvd_div_mult_self)
      ultimately show "P p"
        apply (subst 1)
        by (rule IH_real[OF 2])
    next
      assume "Im z \<noteq> 0"
      hence hcnj: "cnj z \<noteq> z" by (metis cnj.simps(2) neg_equal_zero)
      have h2: "poly (map_poly of_real p) (cnj z) = 0" 
        using h poly_map_poly_of_real_cnj by force
      have "[:-z, 1:] * [:-cnj z, 1:] dvd map_poly of_real p"
      proof (rule divides_mult)
        have "\<And>c. c dvd [:-z, 1:] \<Longrightarrow> c dvd [:- cnj z, 1:] \<Longrightarrow> is_unit c"
        proof -
          fix c
          assume h:"c dvd [:-z, 1:]" hence "degree c \<le> 1" using divides_degree by fastforce
          hence "degree c = 0 \<or> degree c = 1" by linarith
          thus "c dvd [:- cnj z, 1:] \<Longrightarrow> is_unit c"
          proof
            assume "degree c = 0"
            moreover have "c \<noteq> 0" using h by fastforce
            ultimately show "is_unit c" by (simp add: is_unit_iff_degree)
          next
            assume hdeg: "degree c = 1"
            then obtain x where 1:"[:-z, 1:] = x*c" using h by fastforce
            hence "degree [:-z, 1:] = degree x + degree c"
              by (metis add.inverse_neutral degree_mult_eq mult_cancel_right
                  mult_poly_0_left pCons_eq_0_iff zero_neq_neg_one)
            hence "degree x = 0" using hdeg by auto
            then obtain x' where 2: "x = [:x':]" using degree_0_iff by auto
            assume "c dvd [:-cnj z, 1:]"
            then obtain y where 3: "[:-cnj z, 1:] = y*c" by fastforce
            hence "degree [:-cnj z, 1:] = degree y + degree c"
              by (metis add.inverse_neutral degree_mult_eq mult_cancel_right
                  mult_poly_0_left pCons_eq_0_iff zero_neq_neg_one)
            hence "degree y = 0" using hdeg by auto
            then obtain y' where 4: "y = [:y':]" using degree_0_iff by auto
            moreover from hdeg obtain a b where 5:"c = [:a, b:]" and 6: "b \<noteq> 0"
              by (meson degree_eq_oneE)
            from 1 2 5 6 have "x' = inverse b" by (auto simp: field_simps)
            moreover from 3 4 5 6 have "y' = inverse b" by (auto simp: field_simps)
            ultimately have "x = y" using 2 4 by presburger
            then have "z = cnj z" using 1 3 by (metis neg_equal_iff_equal pCons_eq_iff)
            thus "is_unit c" using hcnj by argo
          qed
        qed
        thus "coprime [:- z, 1:] [:- cnj z, 1:]" by (meson not_coprimeE)
        show "[:- z, 1:] dvd map_poly complex_of_real p"
          using h poly_eq_0_iff_dvd by auto
        show "[:- cnj z, 1:] dvd map_poly complex_of_real p"
          using h2 poly_eq_0_iff_dvd by blast
      qed
      moreover have "[:- z, 1:] * [:- cnj z, 1:] = 
                     map_poly of_real [:Re z*Re z + Im z*Im z, -2*Re z, 1:]"
        by (auto simp: complex_eqI)
      ultimately have hdvd: 
        "map_poly complex_of_real [:Re z*Re z + Im z*Im z, -2*Re z, 1:] dvd
         map_poly complex_of_real p"
        by force
      hence "[:Re z*Re z + Im z*Im z, -2*Re z, 1:] dvd p" using map_poly_dvd 
        by blast
      hence 2:"P (p div [:Re z*Re z + Im z*Im z, -2*Re z, 1:])"
        apply (subst IH)
        using hdeg by (auto simp: degree_div)
      moreover have 1:
        "p = (p div [:Re z*Re z + Im z*Im z, -2*Re z, 1:]) * 
                    [:Re z*Re z + Im z*Im z, -2*Re z, 1:]"
        apply (subst dvd_div_mult_self) 
        using \<open>[:Re z*Re z + Im z*Im z, -2*Re z, 1:] dvd p\<close> by auto
      ultimately show "P p"
        apply (subst 1)
        apply (rule IH_complex[of  "Im z" _ "Re z"])
        apply (meson \<open>Im z \<noteq> 0\<close>)
        by blast
    qed
  qed
qed

subsection \<open>The reciprocal polynomial\<close>

definition reciprocal_poly :: "nat \<Rightarrow> 'a::zero poly \<Rightarrow> 'a poly"
  where "reciprocal_poly p P = 
          Poly (rev ((coeffs P) @ (replicate (p - degree P) 0)))"

lemma reciprocal_0: "reciprocal_poly p 0 = 0" by (simp add: reciprocal_poly_def)

lemma reciprocal_1: "reciprocal_poly p 1 = monom 1 p"
  by (simp add: reciprocal_poly_def monom_altdef Poly_append)

lemma coeff_reciprocal: 
  assumes hi: "i \<le> p" and hP: "degree P \<le> p"
  shows "coeff (reciprocal_poly p P) i = coeff P (p - i)"
proof cases
  assume "i < p - degree P"
  hence "degree P < p - i" using hP by linarith
  thus "coeff (reciprocal_poly p P) i = coeff P (p - i)"
    by (auto simp: reciprocal_poly_def nth_default_append coeff_eq_0)
next
  assume h: "\<not>i < p - degree P"
  show "coeff (reciprocal_poly p P) i = coeff P (p - i)"
  proof cases
    assume "P = 0"
    thus "coeff (reciprocal_poly p P) i = coeff P (p - i)" 
      by (simp add: reciprocal_0)
  next
    assume hP': "P \<noteq> 0"
    have "degree P \<ge> p - i" using h hP by linarith
    moreover hence "(i - (p - degree P)) < length (rev (coeffs P))" 
      using hP' hP hi by (auto simp: length_coeffs)
    thus "coeff (reciprocal_poly p P) i = coeff P (p - i)"
      by (auto simp: reciprocal_poly_def nth_default_append coeff_eq_0 hP hP' 
          nth_default_nth rev_nth calculation coeffs_nth length_coeffs_degree)
  qed
qed

lemma coeff_reciprocal_less: 
  assumes hn: "p < i" and hP: "degree P \<le> p"
  shows "coeff (reciprocal_poly p P) i = 0"
proof cases
  assume "P = 0"
  thus ?thesis by (auto simp: reciprocal_0)
next
  assume "P \<noteq> 0"
  thus ?thesis
    using hn 
    by (auto simp: reciprocal_poly_def nth_default_append 
        nth_default_eq_dflt_iff hP length_coeffs)
qed

lemma reciprocal_monom: 
  assumes "n \<le> p"
  shows "reciprocal_poly p (monom a n) = monom a (p-n)"
proof (cases "a=0")
  case True
  then show ?thesis by (simp add: reciprocal_0)
next
  case False
  with \<open>n\<le>p\<close> show ?thesis 
    apply (rule_tac poly_eqI)
    by (metis coeff_monom coeff_reciprocal coeff_reciprocal_less 
        diff_diff_cancel diff_le_self lead_coeff_monom not_le_imp_less)
qed

lemma reciprocal_degree: "reciprocal_poly (degree P) P = reflect_poly P"
  by (auto simp add: reciprocal_poly_def reflect_poly_def)

lemma degree_reciprocal:
  fixes P :: "('a::zero) poly" 
  assumes hP: "degree P \<le> p"
  shows "degree (reciprocal_poly p P) \<le> p"
proof (auto simp add: reciprocal_poly_def)
  have "degree (reciprocal_poly p P) \<le> 
        length (replicate (p - degree P) (0::'a) @ rev (coeffs P))"
    by (metis degree_Poly reciprocal_poly_def rev_append rev_replicate)
  thus "degree (Poly (replicate (p - degree P) 0 @ rev (coeffs P))) \<le> p" 
    by (smt Suc_le_mono add_Suc_right coeffs_Poly degree_0 hP le_SucE le_SucI 
        le_add_diff_inverse2 le_zero_eq length_append length_coeffs_degree
        length_replicate length_rev length_strip_while_le reciprocal_0
        reciprocal_poly_def rev_append rev_replicate)
qed

lemma reciprocal_0_iff: 
  assumes hP: "degree P \<le> p" 
  shows "(reciprocal_poly p P = 0) = (P = 0)"
proof
  assume h: "reciprocal_poly p P = 0"
  show "P = 0"
  proof (rule poly_eqI)
    fix n
    show "coeff P n = coeff 0 n"
    proof cases
      assume hn: "n \<le> p"
      hence "p - n \<le> p" by auto
      hence "coeff (reciprocal_poly p P) (p - n) = coeff P n" 
        using hP hn by (auto simp: coeff_reciprocal)
      thus ?thesis using h by auto
    next
      assume hn: "\<not> n \<le> p"
      thus ?thesis using hP by (metis coeff_0 dual_order.trans le_degree)
    qed
  qed
next
  assume "P = 0"
  thus "reciprocal_poly p P = 0" using reciprocal_0 by fast
qed

lemma poly_reciprocal: 
  fixes P::"'a::field poly"
  assumes hp: "degree P \<le> p" and hx: "x \<noteq> 0"
  shows "poly (reciprocal_poly p P) x = x^p * (poly P (inverse x))"
proof -
  have "poly (reciprocal_poly p P) x
      = poly ((Poly ((replicate (p - degree P) 0) @ rev (coeffs P)))) x"
    by (auto simp add: hx reflect_poly_def reciprocal_poly_def)
  also have "... = poly ((monom 1 (p - degree P)) * (reflect_poly P)) x"
    by (auto simp add: reflect_poly_def Poly_append)
  also have "... = x^(p - degree P) *  x ^ degree P * poly P (inverse x)"
    by (auto simp add: poly_reflect_poly_nz poly_monom hx)
  also have "... = x^p * poly P (inverse x)"
    by (auto simp add: hp power_add[symmetric])
  finally show ?thesis .
qed

lemma reciprocal_fcompose: 
  fixes P::"('a::{ring_char_0,field}) poly" 
  assumes hP: "degree P \<le> p"
  shows "reciprocal_poly p P = monom 1 (p - degree P) * fcompose P 1 [:0, 1:]"
proof (rule poly_eq_by_eval, cases)
  fix x::'a
  assume hx: "x = 0"
  hence "poly (reciprocal_poly p P) x = coeff P p"
    using hP by (auto simp: poly_0_coeff_0 coeff_reciprocal)
  moreover have "poly (monom 1 (p - degree P) 
    * fcompose P 1 [:0, 1:]) x = coeff P p"
  proof cases
    assume "degree P = p"
    thus ?thesis
      apply (induction P arbitrary: p)
      using hx by (auto simp: poly_monom degree_0_iff fcompose_pCons)
  next
    assume "degree P \<noteq> p"
    hence "degree P < p" using hP by auto
    thus ?thesis
      using hx by (auto simp: poly_monom coeff_eq_0)
  qed
  ultimately show "poly (reciprocal_poly p P) x = poly (monom 1 (p - degree P) * fcompose P 1 [:0, 1:]) x"
    by presburger
next
  fix x::'a assume "x \<noteq> 0"
  thus "poly (reciprocal_poly p P) x = 
        poly (monom 1 (p - degree P) * fcompose P 1 [:0, 1:]) x"
    using hP 
    by (auto simp: poly_reciprocal poly_fcompose inverse_eq_divide
        poly_monom power_diff)
qed

lemma reciprocal_reciprocal: 
  fixes P :: "'a::{field,ring_char_0} poly"
  assumes hP: "degree P \<le> p"
  shows "reciprocal_poly p (reciprocal_poly p P) = P"
proof (rule poly_eq_by_eval)
  fix x
  show "poly (reciprocal_poly p (reciprocal_poly p P)) x = poly P x"
  proof cases
    assume "x = 0"
    thus "poly (reciprocal_poly p (reciprocal_poly p P)) x = poly P x" 
      using hP
      by (auto simp: poly_0_coeff_0 coeff_reciprocal degree_reciprocal)
  next
    assume hx: "x \<noteq> 0"
    hence "poly (reciprocal_poly p (reciprocal_poly p P)) x 
        = x ^ p * (inverse x ^ p * poly P x)" using hP
      by (auto simp: poly_reciprocal degree_reciprocal)
    thus "poly (reciprocal_poly p (reciprocal_poly p P)) x = poly P x" 
      using hP hx left_right_inverse_power right_inverse by auto
  qed
qed

lemma reciprocal_smult: 
  fixes P :: "'a::idom poly" 
  assumes h: "degree P \<le> p"
  shows "reciprocal_poly p (smult n P) = smult n (reciprocal_poly p P)"
proof cases
  assume "n = 0"
  thus ?thesis by (auto simp add: reciprocal_poly_def)
next
  assume "n \<noteq> 0"
  thus ?thesis 
    by (auto simp add: reciprocal_poly_def smult_Poly coeffs_smult 
        rev_map[symmetric])
qed

lemma reciprocal_add: 
  fixes P Q :: "'a::comm_semiring_0 poly"
  assumes "degree P \<le> p" and "degree Q \<le> p" 
  shows "reciprocal_poly p (P + Q) = reciprocal_poly p P + reciprocal_poly p Q" 
(is "?L = ?R")
proof (rule poly_eqI, cases)
  fix n
  assume "n \<le> p"
  then show "coeff ?L n = coeff ?R n"
    using assms by (auto simp: degree_add_le coeff_reciprocal)
next
  fix n assume "\<not>n \<le> p"
  then show "coeff ?L n = coeff ?R n"
    using assms by (auto simp: degree_add_le coeff_reciprocal_less)
qed 

lemma reciprocal_diff: 
  fixes P Q :: "'a::comm_ring poly"
  assumes "degree P \<le> p" and "degree Q \<le> p" 
  shows "reciprocal_poly p (P - Q) = reciprocal_poly p P - reciprocal_poly p Q"
  by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus assms
      add_diff_cancel degree_add_le degree_minus diff_add_cancel reciprocal_add)

lemma reciprocal_sum: 
  fixes P :: "'a \<Rightarrow> 'b::comm_semiring_0 poly" 
  assumes hP: "\<And>k. degree (P k) \<le> p"
  shows "reciprocal_poly p (\<Sum>k\<in>A. P k) = (\<Sum>k\<in>A. reciprocal_poly p (P k))"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by (simp add: reciprocal_0)
next
  case empty
  then show ?case by (simp add: reciprocal_0)
next
  case (insert x F)
  assume "x \<notin> F"
     and "reciprocal_poly p (sum P F) = (\<Sum>k\<in>F. reciprocal_poly p (P k))"
     and "finite F"
  moreover hence "reciprocal_poly p (sum P (insert x F)) 
      = reciprocal_poly p (P x) + reciprocal_poly p (sum P F)"
    by (auto simp add: reciprocal_add hP degree_sum_le)
  ultimately show "reciprocal_poly p (sum P (insert x F)) 
      = (\<Sum>k\<in>insert x F. reciprocal_poly p (P k))"
    by (auto simp: Groups_Big.comm_monoid_add_class.sum.insert_if)
qed

lemma reciprocal_mult: 
  fixes P Q::"'a::{ring_char_0,field} poly" 
  assumes "degree (P * Q) \<le> p"
    and "degree P \<le> p" and "degree Q \<le> p"
  shows "monom 1 p * reciprocal_poly p (P * Q) = 
         reciprocal_poly p P * reciprocal_poly p Q"
proof (cases "P=0 \<or> Q=0")
  case True
  then show ?thesis using assms(1) 
    by (auto simp: reciprocal_fcompose fcompose_mult)
next
  case False
  then show ?thesis  
    using assms
    by (auto simp: degree_mult_eq mult_monom reciprocal_fcompose fcompose_mult)
qed

lemma reciprocal_reflect_poly: 
  fixes P::"'a::{ring_char_0,field} poly" 
  assumes hP: "degree P \<le> p"
  shows "reciprocal_poly p P = monom 1 (p - degree P) * reflect_poly P"
proof (rule poly_eqI)
  fix n
  show "coeff (reciprocal_poly p P) n = 
    coeff (monom 1 (p - degree P) * reflect_poly P) n"
  proof cases
    assume "n \<le> p" 
    thus ?thesis using hP
      by (auto simp: coeff_reciprocal coeff_monom_mult coeff_reflect_poly coeff_eq_0)
  next
    assume "\<not> n \<le> p"
    thus ?thesis using hP
      by (auto simp: coeff_reciprocal_less coeff_monom_mult coeff_reflect_poly)
  qed
qed

lemma map_poly_reciprocal: 
  assumes "degree P \<le> p" and "f 0 = 0" 
  shows "map_poly f (reciprocal_poly p P)  = reciprocal_poly p (map_poly f P)"
proof (rule poly_eqI)
  fix n 
  show "coeff (map_poly f (reciprocal_poly p P)) n =
         coeff (reciprocal_poly p (map_poly f P)) n"
  proof (cases "n\<le>p")
    case True
    then show ?thesis 
      apply (subst coeff_reciprocal[OF True])
      subgoal by (meson assms(1) assms(2) degree_map_poly_le le_trans)
      by (simp add: assms(1) assms(2) coeff_map_poly coeff_reciprocal)
  next
    case False
    then show ?thesis 
      by (metis assms(1) assms(2) coeff_map_poly coeff_reciprocal_less 
          degree_map_poly_le dual_order.trans leI)
  qed
qed

subsection \<open>More about @{term proots_count}\<close>

lemma proots_count_monom: 
  assumes "0 \<notin> A" 
  shows "proots_count (monom 1 d) A = 0"
  using assms by (auto simp: proots_count_def poly_monom)

lemma proots_count_reciprocal: 
  fixes P::"'a::{ring_char_0,field} poly"
  assumes hP: "degree P \<le> p" and h0: "P \<noteq> 0" and h0': "0 \<notin> A"
  shows "proots_count (reciprocal_poly p P) A = proots_count P {x. inverse x \<in> A}"
proof -
  have "proots_count (reciprocal_poly p P) A = 
        proots_count (fcompose P 1 [:0, 1:]) A"
    apply (subst reciprocal_fcompose[OF hP], subst proots_count_times)
    subgoal using h0 by (metis hP reciprocal_0_iff reciprocal_fcompose)
    subgoal using h0' by (auto simp: proots_count_monom)
    done

  also have "... = proots_count P {x. inverse x \<in> A}"
  proof (rule proots_fcompose_bij_eq[symmetric])
    show "bij_betw (\<lambda>x. poly 1 x / poly [:0, 1:] x) A {x. inverse x \<in> A}"
    proof (rule bij_betw_imageI)
      show "inj_on (\<lambda>x. poly 1 x / poly [:0, 1:] x) A"
        by (simp add: inj_on_def)

      show "(\<lambda>x. poly 1 x / poly [:0, 1:] x) ` A = {x. inverse x \<in> A}"
      proof
        show "(\<lambda>x. poly 1 x / poly [:0, 1:] x) ` A \<subseteq> {x. inverse x \<in> A}"
          by force
        show "{x. inverse x \<in> A} \<subseteq> (\<lambda>x. poly 1 x / poly [:0, 1:] x) ` A"
        proof
          fix x assume "x \<in> {x::'a. inverse x \<in> A}"
          hence "x = poly 1 (inverse x) / poly [:0, 1:] (inverse x) \<and> inverse x \<in> A"
            by (auto simp: inverse_eq_divide)
          thus "x \<in> (\<lambda>x. poly 1 x / poly [:0, 1:] x) ` A" by blast
        qed
      qed
    qed
  next
    show "\<forall>c. 1 \<noteq> smult c [:0, 1:]" 
      by (metis coeff_pCons_0 degree_1 lead_coeff_1 pCons_0_0 pcompose_0'
          pcompose_smult smult_0_right zero_neq_one)
  qed (auto simp: assms infinite_UNIV_char_0)
  finally show ?thesis by linarith
qed

lemma proots_count_reciprocal': 
  fixes P::"real poly"
  assumes hP: "degree P \<le> p" and h0: "P \<noteq> 0"
  shows "proots_count P {x. 0 < x \<and> x < 1} = 
         proots_count (reciprocal_poly p P) {x. 1 < x}"
proof (subst proots_count_reciprocal)
  show "proots_count P {x. 0 < x \<and> x < 1} =
      proots_count P {x. inverse x \<in> Collect ((<) 1)}"
    apply (rule arg_cong[of _ _ "proots_count P"])
    using one_less_inverse_iff by fastforce
qed (use assms in auto)

lemma proots_count_pos: 
  assumes "proots_count P S > 0" 
  shows "\<exists>x \<in> S. poly P x = 0"
proof (rule ccontr)
  assume "\<not> (\<exists>x\<in>S. poly P x = 0)"
  hence "\<And>x. x \<in> S \<Longrightarrow> poly P x \<noteq> 0" by blast
  hence "\<And>x. x \<in> S \<Longrightarrow> order x P = 0" using order_0I by blast
  hence "proots_count P S = 0" by (force simp: proots_count_def)
  thus False using assms by presburger
qed

lemma proots_count_of_root_set: 
  assumes "P \<noteq> 0" "R \<subseteq> S" and "\<And>x. x\<in>R \<Longrightarrow> poly P x = 0"
  shows "proots_count P S \<ge> card R"
proof -
  have "card R \<le> card (proots_within P S)"
    apply (rule card_mono)
    subgoal using assms by auto
    subgoal using assms(2) assms(3) by (auto simp: proots_within_def)
    done
  also have "... \<le> proots_count P S"
    by (rule card_proots_within_leq[OF assms(1)])
  finally show ?thesis .
qed

lemma proots_count_of_root: assumes "P \<noteq> 0" "x\<in>S" "poly P x = 0"
  shows "proots_count P S > 0"
  using proots_count_of_root_set[of P "{x}" S] assms by force

subsection \<open>More about @{term changes}\<close>

lemma changes_nonneg: "0 \<le> changes xs"
  apply (induction xs rule: changes.induct)
  by simp_all

lemma changes_replicate_0: shows "changes (replicate n 0) = 0"
  apply (induction n)
  by auto

lemma changes_append_replicate_0: "changes (xs @ replicate n 0) = changes xs"
proof (induction xs rule: changes.induct)
  case (2 uu)
  then show ?case
    apply (induction n)
    by auto
qed (auto simp: changes_replicate_0)

lemma changes_scale_Cons: 
  fixes xs:: "real list" assumes hs: "s > 0"
  shows "changes (s * x # xs) = changes (x # xs)"
  apply (induction xs rule: changes.induct)
  using assms by (auto simp: mult_less_0_iff zero_less_mult_iff)

lemma changes_scale: 
  fixes xs::"('a::linordered_idom) list"
  assumes hs: "\<And>i. i < n \<Longrightarrow> s i > 0" and hn: "length xs \<le> n"
  shows "changes [s i * (nth_default 0 xs i). i \<leftarrow> [0..<n]] = changes xs"
using assms
proof (induction xs arbitrary: s n rule: changes.induct)
  case 1
  show ?case by (auto simp: map_replicate_const changes_replicate_0)
next
  case (2 uu)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by force
  next
    case (Suc m)
    hence "map (\<lambda>i. s i * nth_default 0 [uu] i) [0..<n] = [s 0 * uu] @ replicate m 0"
    proof (induction m arbitrary: n)
      case (Suc m n)
      from Suc have "map (\<lambda>i. s i * nth_default 0 [uu] i) [0..<Suc m] = 
                     [s 0 * uu] @ replicate m 0"
        by meson
      hence "map (\<lambda>i. s i * nth_default 0 [uu] i) [0..<n] =
             [s 0 * uu] @ replicate m 0 @ [0]"
        using Suc by auto
      also have "... = [s 0 * uu] @ replicate (Suc m) 0"
        by (simp add: replicate_append_same)
      finally show ?case .
    qed fastforce
    then show ?thesis
      by (metis changes.simps(2) changes_append_replicate_0)
  qed
next
  case (3 a b xs s n)
  obtain m where hn: "n = m + 2"
    using 3(5)
    by (metis add_2_eq_Suc' diff_diff_cancel diff_le_self length_Suc_conv 
        nat_arith.suc1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  hence h: 
    "map (\<lambda>i. s i * nth_default 0 (a # b # xs) i) [0..<n] = 
      s 0 * a # s 1 * b # map (\<lambda>i. 
      (\<lambda> i. s (i+2)) i * nth_default 0 (xs) i) [0..<m]"
    apply (induction m arbitrary: n)
    by auto
  consider (neg)"a*b<0" | (nil)"b=0" | (pos)"\<not>a*b<0 \<and> \<not>b=0" by linarith
  then show ?case
  proof (cases)
    case neg
    hence 
      "changes (map (\<lambda>i. s i * nth_default 0 (a # b # xs) i) [0..<n]) =
        1 + changes (s 1 * b # map (\<lambda>i. (\<lambda> i. s (i+2)) i 
                                        * nth_default 0 (xs) i) [0..<m])"
      apply (subst h)
      using 3(4)[of 0] 3(4)[of 1] hn
      by (metis (no_types, lifting) changes.simps(3) mult_less_0_iff pos2
          mult_pos_pos one_less_numeral_iff semiring_norm(76) trans_less_add2)
    also have 
      "... = 1 + changes (map (\<lambda>i. s (Suc i) * nth_default 0 (b # xs) i) [0..<Suc m])"
      apply (rule arg_cong[of _ _ "\<lambda> x. 1 + changes x"])
      apply (induction m)
      by auto
    also have "... = changes (a # b # xs)"
      apply (subst 3(1)[OF neg])
      using 3 neg hn by auto
    finally show ?thesis .
  next
    case nil
    hence "changes (map (\<lambda>i. s i * nth_default 0 (a # b # xs) i) [0..<n]) =
           changes (s 0 * a # map (\<lambda>i. (\<lambda> i. s (i+2)) i * nth_default 0 (xs) i) [0..<m])"
      apply (subst h)
      using 3(4)[of 0] 3(4)[of 1] hn
      by auto
    also have 
      "... = changes (map 
               (\<lambda>i. s (if i = 0 then 0 else Suc i) * nth_default 0 (a # xs) i) 
              [0..<Suc m])"
      apply (rule arg_cong[of _ _ "\<lambda> x. changes x"])
      apply (induction m)
      by auto
    also have "... = changes (a # b # xs)"
      apply (subst 3(2))
      using 3 nil hn by auto
    finally show ?thesis .
  next
    case pos
    hence "changes (map (\<lambda>i. s i * nth_default 0 (a # b # xs) i) [0..<n]) =
           changes (s 1 * b # map (\<lambda>i. (\<lambda> i. s (i+2)) i * nth_default 0 (xs) i) [0..<m])"
      apply (subst h)
      using 3(4)[of 0] 3(4)[of 1] hn
      by (metis (no_types, lifting) changes.simps(3) divisors_zero 
          mult_less_0_iff nat_1_add_1 not_square_less_zero one_less_numeral_iff
          semiring_norm(76) trans_less_add2 zero_less_mult_pos zero_less_two)
    also have
      "... = changes (map (\<lambda>i. s (Suc i) * nth_default 0 (b # xs) i) [0..<Suc m])"
      apply (rule arg_cong[of _ _ "\<lambda> x. changes x"])
      apply (induction m)
      by auto
    also have "... = changes (a # b # xs)"
      apply (subst 3(3))
      using 3 pos hn by auto
    finally show ?thesis .
  qed
qed

lemma changes_scale_const: fixes xs::"'a::linordered_idom list" 
  assumes hs: "s \<noteq> 0"
  shows "changes (map ((*) s) xs) = changes xs"
  apply (induction xs rule: changes.induct)
    apply (simp, force)
  using hs by (auto simp: mult_less_0_iff zero_less_mult_iff)

lemma changes_snoc: fixes xs::"'a::linordered_idom list" 
  shows "changes (xs @ [b, a]) = (if a * b < 0 then 1 + changes (xs @ [b])
         else if b = 0 then changes (xs @ [a]) else changes (xs @ [b]))"
  apply (induction xs rule: changes.induct)
  subgoal by (force simp: mult_less_0_iff)
  subgoal by (force simp: mult_less_0_iff)
  subgoal by force
  done

lemma changes_rev: fixes xs:: "'a::linordered_idom list" 
  shows "changes (rev xs) = changes xs"
  apply (induction xs rule: changes.induct)
  by (auto simp: changes_snoc)

lemma changes_rev_about: fixes xs:: "'a::linordered_idom list" 
  shows "changes (replicate (p - length xs) 0 @ rev xs) = changes xs"
proof (induction p)
  case (Suc p)
  then show ?case
  proof cases
    assume "\<not>Suc p \<le> length xs"
    hence "Suc p - length xs = Suc (p - length xs)" by linarith
    thus ?case using Suc.IH changes_rev by auto
  qed (auto simp: changes_rev)
qed (auto simp: changes_rev)

lemma changes_add_between: 
  assumes "a \<le> x" and "x \<le> b"
  shows "changes (as @ [a, b] @ bs) = changes (as @ [a, x, b] @ bs)"
proof (induction as rule: changes.induct)
  case 1
  then show ?case using assms 
    apply (induction bs)
    by (auto simp: mult_less_0_iff)
next
  case (2 c)
  then show ?case 
    apply (induction bs)
    using assms by (auto simp: mult_less_0_iff)
next
  case (3 y z as)
  then show ?case
    using assms by (auto simp: mult_less_0_iff)
qed

lemma changes_all_nonneg: assumes "\<And>i. nth_default 0 xs i \<ge> 0" shows "changes xs = 0"
  using assms
proof (induction xs rule: changes.induct)
  case (3 x1 x2 xs)
  moreover assume "(\<And>i. 0 \<le> nth_default 0 (x1 # x2 # xs) i)"
  moreover hence "(\<And>i. 0 \<le> nth_default 0 (x1 # xs) i)" 
    and "(\<And>i. 0 \<le> nth_default 0 (x2 # xs) i)"
    and "x1 * x2 \<ge> 0"
  proof -
    fix i
    assume h:"(\<And>i. 0 \<le> nth_default 0 (x1 # x2 # xs) i)"
    show "0 \<le> nth_default 0 (x1 # xs) i"
    proof (cases i)
      case 0
      then show ?thesis using h[of 0] by force
    next
      case (Suc nat)
      then show ?thesis using h[of "Suc (Suc nat)"] by force
    qed
    show "0 \<le> nth_default 0 (x2 # xs) i" using h[of "Suc i"] by simp
    show "x1*x2 \<ge> 0" using h[of 0] h[of 1] by simp
  qed
  ultimately show ?case by auto
qed auto

lemma changes_pCons: "changes (coeffs (pCons 0 f)) = changes (coeffs f)"
  by (auto simp: cCons_def)

lemma changes_increasing: 
  assumes "\<And>i. i < length xs - 1 \<Longrightarrow> xs ! (i + 1) \<ge> xs ! i" 
    and "length xs > 1"
    and "hd xs < 0" 
    and "last xs > 0"
  shows "changes xs = 1"
  using assms
proof (induction xs rule:changes.induct)
  case (3 x y xs)
  consider (neg)"x*y<0" | (nil)"y=0" | (pos)"\<not>x*y<0 \<and> \<not>y=0" by linarith
  then show ?case
  proof cases
    case neg
    have "changes (y # xs) = 0"
    proof (rule changes_all_nonneg)
      fix i
      show "0 \<le> nth_default 0 (y # xs) i"
      proof (cases "i < length (y # xs)")
        case True
        then show ?thesis using 3(4)[of i] 
          apply (induction i)
          subgoal using 3(6) neg by (fastforce simp: mult_less_0_iff)
          subgoal using 3(4) by (auto simp: nth_default_def)
          done
      next
        case False
        then show ?thesis by (simp add: nth_default_def)
      qed
    qed
    thus "changes (x # y # xs) = 1"
      using neg by force
  next
    case nil
    hence "xs \<noteq> []" using 3(7) by force
    have h: "\<And>i. i < length (x # xs) - 1 \<Longrightarrow> (x # xs) ! i \<le> (x # xs) ! (i + 1)"
    proof -
      fix i assume "i < length (x # xs) - 1"
      thus "(x # xs) ! i \<le> (x # xs) ! (i + 1)"
        apply (cases "i = 0")
        subgoal using 3(4)[of 0] 3(4)[of 1] \<open>xs \<noteq> []\<close> by force
        using 3(4)[of "i+1"] by simp
    qed
    have "changes (x # xs) = 1"
      apply (rule 3(2))
      using nil h \<open>xs \<noteq> []\<close> 3(6) 3(7) by auto
    thus ?thesis
      using nil by force
  next
    case pos
    hence "xs \<noteq> []" using 3(6) 3(7) by (fastforce simp: mult_less_0_iff)
    have "changes (y # xs) = 1"
    proof (rule 3(3))
      show "\<not> x * y < 0" "y \<noteq> 0"
        using pos by auto
      show "\<And>i. i < length (y # xs) - 1 
        \<Longrightarrow> (y # xs) ! i \<le> (y # xs) ! (i + 1)"
        using 3(4) by force
      show "1 < length (y # xs)"
        using \<open>xs \<noteq> []\<close> by force
      show "hd (y # xs) < 0"
        using 3(6) pos by (force simp: mult_less_0_iff)
      show "0 < last (y # xs)"
        using 3(7) by force
    qed
    thus ?thesis using pos by auto
  qed
qed auto

end