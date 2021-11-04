(*
  File:     Hermite_Lindemann.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>The Hermite--Lindemann--Weierstraß Transcendence Theorem\<close>
theory Hermite_Lindemann
imports 
  Pi_Transcendental.Pi_Transcendental
  Algebraic_Numbers.Algebraic_Numbers
  Algebraic_Integer_Divisibility
  Min_Int_Poly
  Complex_Lexorder
  More_Polynomial_HLW
  More_Multivariate_Polynomial_HLW
  More_Algebraic_Numbers_HLW
  Misc_HLW
begin

text \<open>
  The Hermite--Lindemann--Weierstraß theorem answers questions about the transcendence of
  the exponential function and other related complex functions. It proves that a large number of
  combinations of exponentials is always transcendental.

  A first (much weaker) version of the theorem was proven by Hermite. Lindemann and Weierstraß then
  successively generalised it shortly afterwards, and finally Baker gave another, arguably more
  elegant formulation (which is the one that we will prove, and then derive the traditional version
  from it).

  To honour the contributions of all three of these 19th-century mathematicians, I refer to the
  theorem as the Hermite--Lindemann--Weierstraß theorem, even though in other literature it is
  often called Hermite--Lindemann or Lindemann--Weierstraß. To keep things short, the Isabelle
  name of the theorem, however, will omit Weierstraß's name.
\<close>

subsection \<open>Main proof\<close>

text \<open>
  Following Baker, We first prove the following special form of the theorem:
  Let $m > 0$ and $q_1, \ldots, q_m \in\mathbb{Z}[X]$ be irreducible, non-constant,
  and pairwise coprime polynomials. Let $\beta_1, \ldots, \beta_m$ be non-zero integers. Then
  \[\sum_{i=1}^m \beta_i \sum_{q_i(\alpha) = 0} e^\alpha \neq 0\]

  The difference to the final theorem is that

    \<^enum> The coefficients $\beta_i$ are non-zero integers (as opposed to arbitrary algebraic numbers)

    \<^enum> The exponents $\alpha_i$ occur in full sets of conjugates, and each set has the same
      coefficient.

  In a similar fashion to the proofs of the transcendence of \<open>e\<close> and \<open>\<pi>\<close>, we define some number
  $J$ depending on the $\alpha_i$ and $\beta_i$ and an arbitrary sufficiently large prime \<open>p\<close>. We
  then show that, on one hand, $J$ is an integer multiple of $(p-1)!$, but on the other hand it
  is bounded from above by a term of the form $C_1 \cdot C_2^p$. This is then clearly a
  contradiction if \<open>p\<close> is chosen large enough.
\<close>

lemma Hermite_Lindemann_aux1:
  fixes P :: "int poly set" and \<beta> :: "int poly \<Rightarrow> int"
  assumes "finite P" and "P \<noteq> {}"
  assumes distinct: "pairwise Rings.coprime P"
  assumes irred: "\<And>p. p \<in> P \<Longrightarrow> irreducible p"
  assumes nonconstant: "\<And>p. p \<in> P \<Longrightarrow> Polynomial.degree p > 0"
  assumes \<beta>_nz: "\<And>p. p \<in> P \<Longrightarrow> \<beta> p \<noteq> 0"
  defines "Roots \<equiv> (\<lambda>p. {\<alpha>::complex. poly (of_int_poly p) \<alpha> = 0})"
  shows   "(\<Sum>p\<in>P. of_int (\<beta> p) * (\<Sum>\<alpha>\<in>Roots p. exp \<alpha>)) \<noteq> 0"
proof
  note [intro] = \<open>finite P\<close>
  assume sum_eq_0: "(\<Sum>p\<in>P. of_int (\<beta> p) * (\<Sum>\<alpha>\<in>Roots p. exp \<alpha>)) = 0"

  define Roots' where "Roots' = (\<Union>p\<in>P. Roots p)"
  have finite_Roots [intro]: "finite (Roots p)" if "p \<in> P" for p
    using nonconstant[of p] that by (auto intro: poly_roots_finite simp: Roots_def)
  have [intro]: "finite Roots'"
    by (auto simp: Roots'_def)
  have [simp]: "0 \<notin> P"
    using nonconstant[of 0] by auto
  have [simp]: "p \<noteq> 0" if "p \<in> P" for p
    using that by auto

  text \<open>
    The polynomials in \<^term>\<open>P\<close> do not have multiple roots:
  \<close>
  have rsquarefree: "rsquarefree (of_int_poly q :: complex poly)" if "q \<in> P" for q
    by (rule irreducible_imp_rsquarefree_of_int_poly) (use that in \<open>auto intro: irred nonconstant\<close>)

  text \<open>
    No two different polynomials in \<^term>\<open>P\<close> have roots in common:
  \<close>
  have disjoint: "disjoint_family_on Roots P"
    using distinct
  proof (rule pairwise_imp_disjoint_family_on)
    fix p q assume P: "p \<in> P" "q \<in> P" and "Rings.coprime p q"
    hence "Rings.coprime (of_int_poly p :: complex poly) (of_int_poly q)"
      by (intro coprime_of_int_polyI)
    thus "Roots p \<inter> Roots q = {}"
      using poly_eq_0_coprime[of "of_int_poly p" "of_int_poly q :: complex poly"] P
      by (auto simp: Roots_def)
  qed

  define n_roots :: "int poly \<Rightarrow> nat" ("\<sharp>_")
    where "n_roots = (\<lambda>p. card (Roots p))"
  define n where "n = (\<Sum>p\<in>P. \<sharp>p)"
  have n_altdef: "n = card Roots'"
    unfolding n_def Roots'_def n_roots_def using disjoint
    by (subst card_UN_disjoint) (auto simp: disjoint_family_on_def)
  have Roots_nonempty: "Roots p \<noteq> {}" if "p \<in> P" for p
    using nonconstant[OF that] by (auto simp: Roots_def fundamental_theorem_of_algebra constant_degree)
  have "Roots' \<noteq> {}"
    using Roots_nonempty \<open>P \<noteq> {}\<close> by (auto simp: Roots'_def)
  have "n > 0"
    using \<open>Roots' \<noteq> {}\<close> \<open>finite Roots'\<close> by (auto simp: n_altdef)

  text \<open>
    We can split each polynomial in \<open>P\<close> into a product of linear factors:
  \<close>
  have of_int_poly_P:
     "of_int_poly q = Polynomial.smult (Polynomial.lead_coeff q) (\<Prod>x\<in>Roots q. [:-x, 1:])"
     if "q \<in> P" for q
    using complex_poly_decompose_rsquarefree[OF rsquarefree[OF that]] by (simp add: Roots_def)

  text \<open>
    We let \<open>l\<close> be an integer such that $l\alpha$ is an algebraic integer for all our roots \<open>\<alpha>\<close>:
  \<close>
  define l where "l = (LCM q\<in>P. Polynomial.lead_coeff q)"
  have alg_int: "algebraic_int (of_int l * x)" if "x \<in> Roots'" for x
  proof -
    from that obtain q where q: "q \<in> P" "ipoly q x = 0"
      by (auto simp: Roots'_def Roots_def)
    show ?thesis
      by (rule algebraic_imp_algebraic_int'[of q]) (use q in \<open>auto simp: l_def\<close>)
  qed
  have "l \<noteq> 0"
    using \<open>finite P\<close> by (auto simp: l_def Lcm_0_iff)
  moreover have "l \<ge> 0"
    unfolding l_def by (rule Lcm_int_greater_eq_0)
  ultimately have "l > 0" by linarith

  text \<open>
    We can split the product of all the polynomials in \<open>P\<close> into linear factors:
  \<close>
  define lc_factor where "lc_factor = (\<Prod>q\<in>P. l ^ Polynomial.degree q div Polynomial.lead_coeff q)"
  have lc_factor: "Polynomial.smult (of_int l ^ n) (\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:]) =
                      of_int_poly (Polynomial.smult lc_factor (\<Prod>P))"
  proof -
    define lc where "lc = (\<lambda>q. Polynomial.lead_coeff q :: int)"
    define d where "d = (Polynomial.degree :: int poly \<Rightarrow> nat)"
    have "(\<Prod>q\<in>P. of_int_poly q) =
          (\<Prod>q\<in>P. Polynomial.smult (lc q) (\<Prod>x\<in>Roots q. [:-x, 1:]) :: complex poly)"
      unfolding lc_def by (intro prod.cong of_int_poly_P refl)
    also have "\<dots> = Polynomial.smult (\<Prod>q\<in>P. lc q) (\<Prod>q\<in>P. (\<Prod>x\<in>Roots q. [:-x, 1:]))"
      by (simp add: prod_smult)
    also have "(\<Prod>q\<in>P. (\<Prod>x\<in>Roots q. [:-x, 1:])) = (\<Prod>x\<in>Roots'. [:-x, 1:])"
      unfolding Roots'_def using disjoint
      by (intro prod.UNION_disjoint [symmetric]) (auto simp: disjoint_family_on_def)
    also have "Polynomial.smult (of_int lc_factor) (Polynomial.smult (\<Prod>q\<in>P. lc q) \<dots>) =
               Polynomial.smult (\<Prod>q\<in>P. of_int (l ^ d q div lc q * lc q)) (\<Prod>x\<in>Roots'. pCons (- x) 1)"
      by (simp add: lc_factor_def prod.distrib lc_def d_def)
    also have "(\<Prod>q\<in>P. of_int (l ^ d q div lc q * lc q)) = (\<Prod>q\<in>P. of_int l ^ d q :: complex)"
    proof (intro prod.cong, goal_cases)
      case (2 q)
      have "lc q dvd l"
        unfolding l_def lc_def using 2 by auto
      also have "\<dots> dvd l ^ d q"
        using 2 nonconstant[of q] by (intro dvd_power) (auto simp: d_def)
      finally show ?case by simp
    qed auto
    also have "\<dots> = l ^ (\<Sum>q\<in>P. d q)"
      by (simp add: power_sum)
    also have "(\<Sum>q\<in>P. d q) = (\<Sum>q\<in>P. n_roots q)"
    proof (intro sum.cong, goal_cases)
      case (2 q)
      thus ?case using rsquarefree[OF 2]
        by (subst (asm) rsquarefree_card_degree) (auto simp: d_def n_roots_def Roots_def)
    qed auto
    also have "\<dots> = n"
      by (simp add: n_def)
    finally show ?thesis
      by (simp add: of_int_hom.map_poly_hom_smult of_int_poly_hom.hom_prod)
  qed

  text \<open>
    We define \<open>R\<close> to be the radius of the smallest circle around the origin in which all our
    roots lie:
  \<close>
  define R :: real where "R = Max (norm ` Roots')"
  have R_ge: "R \<ge> norm \<alpha>" if "\<alpha> \<in> Roots'" for \<alpha>
    unfolding R_def using that by (intro Max_ge) auto
  have "R \<ge> 0"
  proof -
    from \<open>Roots' \<noteq> {}\<close> obtain \<alpha> where "\<alpha> \<in> Roots'"
      by auto
    have "0 \<le> norm \<alpha>"
      by simp
    also have "\<dots> \<le> R"
      by (intro R_ge) fact
    finally show "R \<ge> 0"
      by simp
  qed

  text \<open>
    Now the main part of the proof: for any sufficiently large prime \<open>p\<close>, our assumptions
    imply $(p-1)! ^ n \leq C' l^{np} (2R)^{np-1}$ for some constant $C'$:    
  \<close>
  define C :: "nat \<Rightarrow> real" where "C = (\<lambda>p. l ^ (n * p) * (2*R) ^ (n * p - 1))"
  define C' where
    "C' = (\<Prod>x\<in>Roots'. \<Sum>q\<in>P. real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. cmod \<alpha> * exp (cmod \<alpha>)))"

  text \<open>
    We commence with the proof of the main inequality.
  \<close>
  have ineq: "fact (p - 1) ^ n \<le> C' * C p ^ n"
    if p: "prime p" 
    and p_ineqs: "\<forall>q\<in>P. p > \<bar>\<beta> q\<bar>"
                 "real p > norm (\<Prod>\<alpha>\<in>Roots'. of_int (l^n) * (\<Prod>x\<in>Roots'-{\<alpha>}. \<alpha> - x))"
    for p :: nat
  proof -
    have "p > 1"
      using prime_gt_1_nat[OF p] .

    text \<open>
      We define the polynomial function
        \[f_i(X) = l^{np} \frac{\prod_\alpha (X-\alpha)^p}{X - \alpha_i}\]
      where the product runs over all roots $\alpha$.
    \<close>
    define f_poly :: "complex \<Rightarrow> complex poly" where
      "f_poly = (\<lambda>\<alpha>. Polynomial.smult (l^(n*p)) ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:]^p) div [:-\<alpha>, 1:]))"
    have f_poly_altdef: "f_poly \<alpha> = Polynomial.smult (l^(n*p))
                           ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:]^(if \<alpha>' = \<alpha> then p - 1 else p)))"
      if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      have "(\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:] ^ (if \<alpha>'=\<alpha> then p-1 else p)) * [:-\<alpha>, 1:] =
            [:- \<alpha>, 1:] ^ (p - 1) * (\<Prod>x\<in>Roots' - {\<alpha>}. [:- x, 1:] ^ p) * [:- \<alpha>, 1:]"
        using that by (subst prod.If_eq) (auto simp: algebra_simps)
      also have "\<dots> = (\<Prod>x\<in>Roots' - {\<alpha>}. [:- x, 1:] ^ p) * [:- \<alpha>, 1:] ^ Suc (p - 1)"
        by (simp only: power_Suc mult_ac)
      also have "Suc (p - 1) = p"
        using \<open>p > 1\<close> by auto
      also have "(\<Prod>x\<in>Roots' - {\<alpha>}. [:- x, 1:] ^ p) * [:- \<alpha>, 1:] ^ p = (\<Prod>x\<in>Roots'. [:- x, 1:] ^ p)"
        using that by (subst prod.remove[of _ \<alpha>]) auto
      finally have eq: "(\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>', 1:] ^ (if \<alpha>'=\<alpha> then p-1 else p)) * [:-\<alpha>, 1:] =
                        (\<Prod>x\<in>Roots'. [:- x, 1:] ^ p)" .
      show ?thesis
        unfolding f_poly_def eq[symmetric] by (subst nonzero_mult_div_cancel_right) auto
    qed
  
    define f :: "complex \<Rightarrow> complex \<Rightarrow> complex"
      where "f = (\<lambda>\<alpha> x. l^(n*p) * (\<Prod>\<alpha>'\<in>Roots'. (x - \<alpha>')^(if \<alpha>' = \<alpha> then p - 1 else p)))"
    have eval_f: "poly (f_poly \<alpha>) x = f \<alpha> x" if "\<alpha> \<in> Roots'" for \<alpha> x
      using that by (simp add: f_poly_altdef poly_prod f_def)
    have deg_f: "Polynomial.degree (f_poly \<alpha>) = n * p - 1" if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      have "Polynomial.degree (f_poly \<alpha>) = p - 1 + (n - 1) * p"
        unfolding f_poly_altdef[OF that] using that \<open>l > 0\<close> \<open>finite Roots'\<close>
        by (subst prod.If_eq) (auto simp: degree_prod_eq degree_power_eq degree_mult_eq n_altdef)
      also have "p - 1 + (n - 1) * p = n * p - 1"
        using \<open>n > 0\<close> \<open>p > 1\<close> by (cases n) auto
      finally show ?thesis .
    qed

    text \<open>
      Next, we define the function $I_i(z) = \int_0^z e^{z-t} f_i(t) \text{d}t$, and,
      based on that, the numbers $J_i = \sum_{i=1}^m \beta_i \sum_{q_i(x) = 0} I_i(x)$,
      and the number $J$, which is the product of all the $J_i$:
    \<close>
    define I :: "complex \<Rightarrow> complex \<Rightarrow> complex"
      where "I = (\<lambda>\<alpha> x. lindemann_weierstrass_aux.I (f_poly \<alpha>) x)"
    define J :: "complex \<Rightarrow> complex"
      where "J = (\<lambda>\<alpha>. \<Sum>q\<in>P. \<beta> q * (\<Sum>x\<in>Roots q. I \<alpha> x))"

    define J' :: complex
      where "J' = (\<Prod>\<alpha>\<in>Roots'. J \<alpha>)"

    text \<open>
      Reusing some of the machinery from the proof that \<open>e\<close> is transcendental,
      we find the following equality for $J_i$:
    \<close>
    have J_eq: "J \<alpha> = -(\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
      if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      have "n * p \<ge> 1 * 2"
        using \<open>n > 0\<close> \<open>p > 1\<close> by (intro mult_mono) auto
      hence [simp]: "{..n*p-Suc 0} = {..<n*p}"
        by auto
      have "J \<alpha> = (\<Sum>q\<in>P. \<beta> q * (\<Sum>x\<in>Roots q. I \<alpha> x))"
        unfolding J_def ..
      also have "\<dots> = (\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. exp x * (\<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) 0))) -
                      (\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
        unfolding I_def lindemann_weierstrass_aux.I_def
        by (simp add: deg_f that ring_distribs sum_subtractf sum_distrib_left sum_distrib_right mult_ac)
      also have "\<dots> = -(\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n*p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
        unfolding sum_distrib_right [symmetric] mult.assoc [symmetric] sum_eq_0 by simp
      finally show ?thesis .
    qed

    text \<open>
      The next big step is to show that $(p-1)! \mid J_i$ as an algebraic integer (i.e.
      $J_i / (p-1)!$ is an algebraic integer), but $p \not\mid J_i$. This is done by brute force:
      We show that every summand in the above sum has $p!$ as a factor, except for
      the one corresponding to $x = \alpha_i$, $j = p - 1$, which has $(p-1)!$ as a factor but
      not \<open>p\<close>.
    \<close>
    have J: "fact (p - 1) alg_dvd J \<alpha>" "\<not>of_nat p alg_dvd J \<alpha>" if \<alpha>: "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      define h where "h = (\<lambda>\<alpha>' j. poly ((pderiv ^^ j) (f_poly \<alpha>)) \<alpha>')"
      from \<alpha> obtain q where q: "q \<in> P" "\<alpha> \<in> Roots q"
        by (auto simp: Roots'_def)
  
      have "J \<alpha> = -(\<Sum>(q, \<alpha>')\<in>Sigma P Roots. \<Sum>j<n*p. of_int (\<beta> q) * h \<alpha>' j)"
        unfolding J_eq[OF \<alpha>] h_def sum_distrib_left by (subst (2) sum.Sigma) auto
      also have "\<dots> = -(\<Sum>((q,\<alpha>'),i)\<in>Sigma P Roots\<times>{..<n*p}. of_int (\<beta> q) * h \<alpha>' i)"
        by (subst (2) sum.Sigma [symmetric]) (auto simp: case_prod_unfold)
      finally have J_eq': "J \<alpha> = - (\<Sum>((q, \<alpha>'), i)\<in>Sigma P Roots \<times> {..<n * p}. of_int (\<beta> q) * h \<alpha>' i)" .
  
      have h_\<alpha>_pm1_eq: "h \<alpha> (p-1) = of_int (l^(n*p)) * fact (p-1) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)"
      proof -
        have "h \<alpha> (p - 1) = of_int (l ^ (n * p)) *
                poly ((pderiv ^^ (p-1)) (\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:] ^ (if \<alpha>' = \<alpha> then p - 1 else p))) \<alpha>"
          unfolding h_def f_poly_altdef[OF \<alpha>] higher_pderiv_smult poly_smult ..
        also have "(\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:] ^ (if \<alpha>' = \<alpha> then p - 1 else p)) =
                    [:-\<alpha>,1:]^(p-1) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. [:-\<alpha>',1:]^p)"
          using \<alpha> by (subst prod.If_eq) auto
        also have "poly ((pderiv ^^ (p-1)) \<dots>) \<alpha> = fact (p - 1) * (\<Prod>\<alpha>'\<in>Roots' - {\<alpha>}. (\<alpha> - \<alpha>') ^ p)"
          by (subst poly_higher_pderiv_aux2) (simp_all add: poly_prod)
        finally show ?thesis by (simp only: mult.assoc)
      qed
  
      have "fact (p-1) alg_dvd h \<alpha> (p-1)"
      proof -
        have "fact (p-1) alg_dvd fact (p-1) * (of_int (l^p) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (l*\<alpha>-l*\<alpha>')^p))"
          by (intro alg_dvd_triv_left algebraic_int_times[of "of_int (l^p)"]
                    algebraic_int_prod algebraic_int_power algebraic_int_diff
                    alg_int \<alpha> algebraic_int_of_int) auto
        also have "(\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (l*\<alpha>-l*\<alpha>')^p) = (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. of_int l^p * (\<alpha>-\<alpha>')^p)"
          by (subst power_mult_distrib [symmetric]) (simp_all add: algebra_simps)
        also have "\<dots> = of_int (l ^ (p * (n-1))) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)"
          using \<alpha> by (subst prod.distrib) (auto simp: card_Diff_subset n_altdef simp flip: power_mult)
        also have "of_int (l^p) * \<dots> = of_int (l^(p+p*(n-1))) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)"
          unfolding mult.assoc [symmetric] power_add [symmetric] of_int_power ..
        also have "p + p * (n - 1) = n * p"
          using \<open>n > 0\<close> by (cases n) (auto simp: mult_ac)
        also have "fact (p - 1) * (of_int (l^(n*p)) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')^p)) = h \<alpha> (p-1)"
          unfolding h_\<alpha>_pm1_eq by (simp add: mult_ac)
        finally show ?thesis .
      qed
 
      have "\<not>of_nat p alg_dvd of_int (\<beta> q) * h \<alpha> (p-1)"
        unfolding h_\<alpha>_pm1_eq mult.assoc [symmetric] of_int_mult [symmetric]
      proof
        define r where "r = (\<lambda>\<alpha>. of_int (l^n) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. \<alpha>-\<alpha>'))"
        have alg_int_r: "algebraic_int (r \<alpha>)" if "\<alpha> \<in> Roots'" for \<alpha>
        proof -
          have "algebraic_int (of_int l * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. of_int l * \<alpha> - of_int l * \<alpha>'))"
            by (intro algebraic_int_times[OF algebraic_int_of_int] algebraic_int_prod 
                      algebraic_int_power algebraic_int_diff alg_int that) auto
          also have "\<dots> = of_int l * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. of_int l * (\<alpha> - \<alpha>'))"
            by (simp add: algebra_simps flip: power_mult_distrib)
          also have "\<dots> = of_int (l^(1 + (n-1))) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. \<alpha> - \<alpha>')"
            using that by (simp add: r_def prod.distrib card_Diff_subset
                                     n_altdef power_add mult_ac flip: power_mult)
          also have "1 + (n - 1) = n"
            using \<open>n > 0\<close> by auto
          finally show "algebraic_int (r \<alpha>)"
            unfolding r_def .
        qed

        have "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<in> \<rat>"
        proof -
          obtain Root where Root_bij: "bij_betw Root {..<n} Roots'"
            using ex_bij_betw_nat_finite[OF \<open>finite Roots'\<close>] unfolding n_altdef atLeast0LessThan by metis
          have Root_in_Roots': "Root i \<in> Roots'" if "i < n" for i
            using Root_bij that by (auto simp: bij_betw_def)

          define R :: "complex mpoly" where
            "R = (\<Prod>i<n. Const (of_int (l^n)) * (\<Prod>j\<in>{..<n}-{i}. Var i - Var j))"
          have "insertion Root R \<in> \<rat>"
          proof (rule symmetric_poly_of_roots_in_subring)
            show "symmetric_mpoly {..<n} R"
              unfolding R_def
            proof (rule symmetric_mpoly_symmetric_prod'[of _ "\<lambda>\<pi>. \<pi>"], goal_cases)
              case (2 i \<pi>)
              from \<open>\<pi> permutes {..<n}\<close> have [simp]: "bij \<pi>"
                by (rule permutes_bij)
              have "mpoly_map_vars \<pi> (Const (of_int (l ^ n)) *
                      (\<Prod>j\<in>{..<n} - {i}. Var i - Var j):: complex mpoly) =
                    Const (of_int l ^ n) * (\<Prod>j\<in>{..<n} - {i}. Var (\<pi> i) - Var (\<pi> j))"
                by simp
              also have "(\<Prod>j\<in>{..<n} - {i}. Var (\<pi> i) - Var (\<pi> j)) =
                         (\<Prod>j\<in>{..<n} - {\<pi> i}. Var (\<pi> i) - Var j)"
                using 2 permutes_in_image[OF 2(2), of i]
                by (intro prod.reindex_bij_betw bij_betw_Diff permutes_imp_bij[OF 2(2)])
                   (auto simp: bij_betw_singleton)
              finally show ?case by simp
            qed
          next
            show "vars R \<subseteq> {..<n}" unfolding R_def
              by (intro order.trans[OF vars_prod] UN_least order.trans[OF vars_mult]
                        Un_least order.trans[OF vars_power] order.trans[OF vars_diff])
                 (auto simp: vars_Var)
          next
            show "ring_closed (\<rat> :: complex set)"
              by unfold_locales auto
            then interpret ring_closed "\<rat> :: complex set" .              
            show "\<forall>m. MPoly_Type.coeff R m \<in> \<rat>"
              unfolding R_def
              by (intro allI coeff_prod_closed coeff_mult_closed coeff_power_closed)
                 (auto simp: mpoly_coeff_Const coeff_Var when_def)
          next
            let ?lc = "of_int (\<Prod>p\<in>P. Polynomial.lead_coeff p) :: complex"
            have "(\<Prod>q\<in>P. of_int_poly q) = (\<Prod>q\<in>P. Polynomial.smult
                    (of_int (Polynomial.lead_coeff q)) (\<Prod>x\<in>Roots q. [:-x, 1:]))"
              by (intro prod.cong of_int_poly_P refl)
            also have "\<dots> = Polynomial.smult ?lc (\<Prod>q\<in>P. \<Prod>x\<in>Roots q. [:-x, 1:])"
              by (simp add: prod_smult)
            also have "(\<Prod>q\<in>P. \<Prod>x\<in>Roots q. [:-x, 1:]) = (\<Prod>x\<in>Roots'. [:-x, 1:])"
              unfolding Roots'_def using disjoint
              by (intro prod.UNION_disjoint [symmetric]) (auto simp: disjoint_family_on_def)
            also have "\<dots> = (\<Prod>i<n. [:- Root i, 1:])"
              by (intro prod.reindex_bij_betw [symmetric] Root_bij)
            finally show "of_int_poly (\<Prod>P) = Polynomial.smult ?lc (\<Prod>i<n. [:- Root i, 1:])"
              by (simp add: of_int_poly_hom.hom_prod)
            have "prod Polynomial.lead_coeff P \<noteq> 0"
              by (intro prod_nonzeroI) auto
            thus "inverse ?lc * ?lc = 1" "inverse ?lc \<in> \<rat>"
              by (auto simp: field_simps simp flip: of_int_prod)
          qed auto
          also have "insertion Root R = (\<Prod>i<n. of_int (l^n) * (\<Prod>j\<in>{..<n}-{i}. Root i - Root j))"
            by (simp add: R_def insertion_prod insertion_mult insertion_power insertion_diff)
          also have "\<dots> = (\<Prod>i<n. of_int (l^n) * (\<Prod>\<alpha>'\<in>Roots'-{Root i}. Root i - \<alpha>'))"
          proof (intro prod.cong, goal_cases)
            case (2 i)
            hence "(\<Prod>j\<in>{..<n}-{i}. Root i - Root j) = (\<Prod>\<alpha>'\<in>Roots'-{Root i}. Root i - \<alpha>')"
              by (intro prod.reindex_bij_betw bij_betw_Diff Root_bij)
                 (auto intro: Root_in_Roots' simp: bij_betw_singleton)
            thus ?case by simp
          qed auto
          also have "\<dots> = (\<Prod>\<alpha>'\<in>Roots'. r \<alpha>')"
            unfolding r_def by (intro prod.reindex_bij_betw Root_bij)
          finally show "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<in> \<rat>" .
        qed
        moreover have "algebraic_int (\<Prod>\<alpha>'\<in>Roots'. r \<alpha>')"
          by (intro algebraic_int_prod alg_int_r)
        ultimately have is_int: "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<in> \<int>"
          using rational_algebraic_int_is_int by blast
        then obtain R' where R': "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') = of_int R'"
          by (elim Ints_cases)
        have "(\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') \<noteq> 0"
          using \<open>l > 0\<close> by (intro prod_nonzeroI) (auto simp: r_def \<open>finite Roots'\<close>)
        with R' have [simp]: "R' \<noteq> 0"
          by auto

        assume "of_nat p alg_dvd of_int (\<beta> q * l^(n*p)) * fact (p-1) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>') ^ p)"
        also have "\<dots> = of_int (\<beta> q) * fact (p-1) * r \<alpha> ^ p"
          by (simp add: r_def mult_ac power_mult_distrib power_mult prod_power_distrib)
        also have "\<dots> alg_dvd of_int (\<beta> q) * fact (p-1) * r \<alpha> ^ p * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. r \<alpha>') ^ p"
          by (intro alg_dvd_triv_left algebraic_int_prod alg_int_r algebraic_int_power) auto
        also have "\<dots> = of_int (\<beta> q) * fact (p-1) * (\<Prod>\<alpha>'\<in>Roots'. r \<alpha>') ^ p"
          using \<alpha> by (subst (2) prod.remove[of _ "\<alpha>"]) (auto simp: mult_ac power_mult_distrib)
        also have "\<dots> = of_int (\<beta> q * fact (p - 1) * R' ^ p)"
          by (simp add: R')
        also have "of_nat p = of_int (int p)"
          by simp
        finally have "int p dvd \<beta> q * fact (p - 1) * R' ^ p" 
          by (subst (asm) alg_dvd_of_int_iff)
        moreover have "prime (int p)"
          using \<open>prime p\<close> by auto
        ultimately have "int p dvd \<beta> q \<or> int p dvd fact (p - 1) \<or> int p dvd R' ^ p"
          by (simp add: prime_dvd_mult_iff)
        moreover have "\<not>int p dvd \<beta> q"
        proof
          assume "int p dvd \<beta> q"
          hence "int p \<le> \<bar>\<beta> q\<bar>"
            using \<beta>_nz[of q] dvd_imp_le_int[of "\<beta> q" "int p"] q by auto
          with p_ineqs(1) q show False by auto
        qed
        moreover have "\<not>int p dvd fact (p - 1)"
        proof -
          have "\<not>p dvd fact (p - 1)"
            using \<open>p > 1\<close> p by (subst prime_dvd_fact_iff) auto
          hence "\<not>int p dvd int (fact (p - 1))"
            by (subst int_dvd_int_iff)
          thus ?thesis unfolding of_nat_fact .
        qed
        moreover have "\<not>int p dvd R' ^ p"
        proof
          assume "int p dvd R' ^ p"
          hence "int p dvd R'"
            using \<open>prime (int p)\<close> prime_dvd_power by metis
          hence "int p \<le> \<bar>R'\<bar>"
            using \<beta>_nz[of q] dvd_imp_le_int[of R' "int p"] q by auto
          hence "real p \<le> real_of_int \<bar>R'\<bar>"
            by linarith
          also have "\<dots> = norm (\<Prod>\<alpha>\<in>Roots'. r \<alpha>)"
            unfolding R' by simp
          finally show False unfolding r_def using p_ineqs(2)
            by linarith
        qed
        ultimately show False
          by blast
      qed
  
      have fact_p_dvd: "fact p alg_dvd h \<alpha>' j" if "\<alpha>' \<in> Roots'" "\<alpha>' \<noteq> \<alpha> \<or> j \<noteq> p - 1" for \<alpha>' j
      proof (cases "j \<ge> p")
        case False
        with that have j: "j < (if \<alpha>' = \<alpha> then p - 1 else p)"
          by auto
        have "h \<alpha>' j = 0"
          unfolding h_def f_poly_altdef[OF \<alpha>]
          by (intro poly_higher_pderiv_aux1'[OF j] dvd_smult dvd_prodI that) auto
        thus ?thesis by simp
      next
        case True
        define e where "e = (\<lambda>x. if x = \<alpha> then p - 1 else p)"
        define Q where "Q = (\<Prod>x\<in>Roots'. [:-x, 1:] ^ e x)"
        define Q' where "Q' = Polynomial.smult (of_int (l^(n*p+j))) (pcompose Q [:0, 1 / of_int l:])"
        have "poly ((pderiv ^^ j) Q) \<alpha>' / l ^ j =
                poly ((pderiv ^^ j) (pcompose Q [:0, 1 / of_int l:])) (l * \<alpha>')"
          using \<open>l > 0\<close> by (simp add: higher_pderiv_pcompose_linear poly_pcompose field_simps)

        have "sum e Roots' = (n - 1) * p + (p - 1)"
          unfolding e_def using \<alpha>
          by (subst sum.If_eq) (auto simp: card_Diff_subset n_altdef algebra_simps)
        also have "\<dots> = n * p - 1"
          using \<open>n > 0\<close> \<open>p > 1\<close> by (cases n) auto
        finally have [simp]: "sum e Roots' = n * p - 1" .

        have "h \<alpha>' j = of_int (l^(n*p)) * poly ((pderiv ^^ j) Q) \<alpha>'"
          unfolding h_def f_poly_altdef[OF \<alpha>] higher_pderiv_smult poly_smult e_def Q_def ..
        also have "poly ((pderiv ^^ j) Q) \<alpha>' =
                     of_int l ^ j * poly ((pderiv ^^ j) (pcompose Q [:0, 1 / of_int l:])) (l * \<alpha>')"
          using \<open>l > 0\<close> by (simp add: higher_pderiv_pcompose_linear poly_pcompose field_simps)
        also have "of_int (l ^ (n * p)) * \<dots> = poly ((pderiv ^^ j) Q') (l * \<alpha>')"
          by (simp add: Q'_def higher_pderiv_smult power_add)
        also have "fact p alg_dvd \<dots>"
        proof (rule fact_alg_dvd_poly_higher_pderiv)
          show "j \<ge> p" by fact
          show "algebraic_int (of_int l * \<alpha>')"
            by (rule alg_int) fact
          interpret alg_int: ring_closed "{x::complex. algebraic_int x}"
            by standard auto
          show "algebraic_int (poly.coeff Q' i)" for i
          proof (cases "i \<le> Polynomial.degree Q'")
            case False
            thus ?thesis
              by (simp add: coeff_eq_0)
          next
            case True
            hence "i \<le> n * p - 1" using \<open>l > 0\<close>
              by (simp add: Q'_def degree_prod_eq Q_def degree_power_eq)
            also have "n * p > 0"
              using \<open>n > 0\<close> \<open>p > 1\<close> by auto
            hence "n * p - 1 < n * p"
              by simp
            finally have i: "i < n * p" .

            have "poly.coeff Q' i = of_int l ^ (n * p + j) / of_int l ^ i * poly.coeff Q i"
              by (simp add: Q'_def coeff_pcompose_linear field_simps)
            also have "of_int l ^ (n * p + j) = (of_int l ^ (n * p + j - i) :: complex) * of_int l ^ i"
              unfolding power_add [symmetric] using i by simp
            hence "of_int l ^ (n * p + j) / of_int l ^ i = (of_int l ^ (n * p + j - i) :: complex)"
              using \<open>l > 0\<close> by (simp add: field_simps)
            also have "\<dots> * poly.coeff Q i =
                (\<Sum>X\<in>{X. X \<subseteq> (SIGMA x:Roots'. {..<e x}) \<and> i = n * p - Suc (card X)}.
                of_int l ^ (n * p + j - (n * p - Suc (card X))) * ((- 1) ^ card X * prod fst X))"
              unfolding Q_def by (subst coeff_prod_linear_factors) (auto simp: sum_distrib_left)
            also have "algebraic_int \<dots>"
            proof (intro algebraic_int_sum, goal_cases)
              case (1 X)
              hence X: "X \<subseteq> (SIGMA x:Roots'. {..<e x})"
                by auto
              have card_eq: "card (SIGMA x:Roots'. {..<e x}) = n * p - 1"
                by (subst card_SigmaI) auto
              from X have "card X \<le> card (SIGMA x:Roots'. {..<e x})"
                by (intro card_mono) auto
              hence "card X \<le> n * p - 1"
                using card_eq by auto
              also have "\<dots> < n * p"
                using  \<open>n * p > 0\<close> by simp
              finally have card_less: "card X < n * p" .
              have "algebraic_int ((-1) ^ card X * of_int l ^ (j + 1) * (\<Prod>x\<in>X. of_int l * fst x))"
                using X by (intro algebraic_int_times algebraic_int_prod alg_int) auto
              thus ?case
                using card_less by (simp add: power_add prod.distrib mult_ac)
            qed
            finally show ?thesis .
          qed
        qed
        finally show ?thesis .
      qed
  
      have p_dvd: "of_nat p alg_dvd h \<alpha>' j" if "\<alpha>' \<in> Roots'" "\<alpha>' \<noteq> \<alpha> \<or> j \<noteq> p - 1" for \<alpha>' j
      proof -
        have "of_nat p alg_dvd (of_nat (fact p) :: complex)"
          by (intro alg_dvd_of_nat dvd_fact) (use \<open>p > 1\<close> in auto)
        hence "of_nat p alg_dvd (fact p :: complex)"
          by simp
        also have "\<dots> alg_dvd h \<alpha>' j"
          using that by (intro fact_p_dvd)
        finally show ?thesis .
      qed
  
      show "fact (p - 1) alg_dvd J \<alpha>"
        unfolding J_eq'
      proof (intro alg_dvd_uminus_right alg_dvd_sum, safe intro!: alg_dvd_mult algebraic_int_of_int)
        fix q \<alpha>' j
        assume "q \<in> P" "\<alpha>' \<in> Roots q" "j < n * p"
        hence "\<alpha>' \<in> Roots'"
          by (auto simp: Roots'_def)
        show "fact (p - 1) alg_dvd h \<alpha>' j"
        proof (cases "\<alpha>' = \<alpha> \<and> j = p - 1")
          case True
          thus ?thesis using \<open>fact (p - 1) alg_dvd h \<alpha> (p - 1)\<close>
            by simp
        next
          case False
          have "of_int (fact (p - 1)) alg_dvd (of_int (fact p) :: complex)"
            by (intro alg_dvd_of_int fact_dvd) auto
          hence "fact (p - 1) alg_dvd (fact p :: complex)"
            by simp
          also have "\<dots> alg_dvd h \<alpha>' j"
            using False \<open>\<alpha>' \<in> Roots'\<close> by (intro fact_p_dvd) auto
          finally show ?thesis .
        qed
      qed
  
      show "\<not>of_nat p alg_dvd J \<alpha>"
        unfolding J_eq' alg_dvd_uminus_right_iff
      proof (rule not_alg_dvd_sum)
        have "p - 1 < 1 * p"
          using \<open>p > 1\<close> by simp
        also have "1 * p \<le> n * p"
          using \<open>n > 0\<close> by (intro mult_right_mono) auto
        finally show "((q, \<alpha>), p - 1) \<in> Sigma P Roots \<times> {..<n*p}"
          using q \<open>n > 0\<close> by auto
      next
        fix z assume z: "z \<in> Sigma P Roots \<times> {..<n*p}-{((q,\<alpha>),p-1)}"
        from z have "snd (fst z) \<in> Roots'"
          by (auto simp: Roots'_def)
        moreover have "fst (fst z) = q" if "\<alpha> \<in> Roots (fst (fst z))"
        proof -
          have "\<alpha> \<in> Roots (fst (fst z)) \<inter> Roots q" "q \<in> P" "fst (fst z) \<in> P"
            using that q z by auto
          with disjoint show ?thesis
            unfolding disjoint_family_on_def by blast
        qed
        ultimately have "of_nat p alg_dvd h (snd (fst z)) (snd z)"
          using z by (intro p_dvd) auto
        thus  "of_nat p alg_dvd (case z of (x, xa) \<Rightarrow> (case x of (q, \<alpha>') \<Rightarrow> \<lambda>i. of_int (\<beta> q) * h \<alpha>' i) xa)"
          using z by auto
      qed (use \<open>\<not>of_nat p alg_dvd of_int (\<beta> q) * h \<alpha> (p-1)\<close> in auto)
    qed

    text \<open>
      Our next goal is to show that $J$ is rational. This is done by repeated applications
      of the fundamental theorem of symmetric polynomials, exploiting the fact that $J$ is
      symmetric in all the $\alpha_i$ for each set of conjugates.
    \<close>
    define g :: "int poly poly"
      where "g = synthetic_div (map_poly (\<lambda>x. [:x:])
                   ((Polynomial.smult lc_factor (\<Prod>P)) ^ p)) [:0, 1:]"
    have g: "map_poly (\<lambda>p. ipoly p \<alpha>) g = f_poly \<alpha>" if \<alpha>: "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      interpret \<alpha>: comm_ring_hom "\<lambda>p. ipoly p \<alpha>"
        by standard (auto simp: of_int_hom.poly_map_poly_eval_poly of_int_poly_hom.hom_mult)
      define Q :: "int poly" where "Q = (Polynomial.smult lc_factor (\<Prod>P)) ^ p"
      have "f_poly \<alpha> = Polynomial.smult (of_int (l^(n*p))) ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:])^p) div [:-\<alpha>,1:]"
        unfolding f_poly_def div_smult_left [symmetric] prod_power_distrib[symmetric] ..
      also have "of_int (l^(n*p)) = (of_int l^n)^p"
        by (simp add: power_mult)
      also have "Polynomial.smult \<dots> ((\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:])^p) =
                   (Polynomial.smult (of_int l ^ n) (\<Prod>\<alpha>'\<in>Roots'. [:-\<alpha>',1:])) ^ p"
        by (simp only: smult_power)
      also have "\<dots> = of_int_poly Q"
        by (subst lc_factor) (simp_all add: Q_def of_int_poly_hom.hom_power)
      also have "\<dots> div [:-\<alpha>, 1:] = synthetic_div (of_int_poly Q) \<alpha>"
        unfolding synthetic_div_altdef ..
      also have "\<dots> = synthetic_div (map_poly (\<lambda>p. ipoly p \<alpha>) (map_poly (\<lambda>x. [:x:]) Q)) (ipoly [:0, 1:] \<alpha>)"
        by (simp add: map_poly_map_poly o_def)
      also have "\<dots> = map_poly (\<lambda>p. ipoly p \<alpha>) g"
        unfolding g_def Q_def by (rule \<alpha>.synthetic_div_hom)
      finally show ?thesis ..
    qed

    obtain Q where Q: "J \<alpha> = -(\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q q) \<alpha>)"
      if "\<alpha> \<in> Roots'" for \<alpha>
    proof -
      define g' :: "nat \<Rightarrow> complex poly poly"
        where "g' = (\<lambda>j.  (map_poly of_int_poly ((pderiv ^^ j) g)))"
      obtain root :: "int poly \<Rightarrow> nat \<Rightarrow> complex"
        where root: "\<And>q. q \<in> P \<Longrightarrow> bij_betw (root q) {..<\<sharp>q} (Roots q)"
        using ex_bij_betw_nat_finite[OF finite_Roots] unfolding n_roots_def atLeast0LessThan
        by metis
      have "\<exists>Q'. map_poly of_rat Q' = (\<Sum>x\<in>Roots q. poly (g' j) [:x:])" if q: "q \<in> P" for q j
      proof -
        define Q :: "nat \<Rightarrow> complex poly mpoly"
          where "Q = (\<lambda>j. (\<Sum>i<\<sharp>q. mpoly_of_poly i (g' j)))"
        define ratpolys :: "complex poly set" where "ratpolys = {p. \<forall>i. poly.coeff p i \<in> \<rat>}"
        have "insertion ((\<lambda>x. [:x:]) \<circ> root q) (Q j) \<in> ratpolys"
        proof (rule symmetric_poly_of_roots_in_subring)
          show "ring_closed ratpolys"
            by standard (auto simp: ratpolys_def intro!: coeff_mult_semiring_closed)
          show "\<forall>m. MPoly_Type.coeff (Q j) m \<in> ratpolys"
            by (auto simp: Q_def ratpolys_def Polynomial.coeff_sum coeff_mpoly_of_poly when_def g'_def
                     intro!: sum_in_Rats)
          show "vars (Q j) \<subseteq> {..<\<sharp>q}" unfolding Q_def
            by (intro order.trans[OF vars_sum] UN_least order.trans[OF vars_mpoly_of_poly]) auto
          show "symmetric_mpoly {..<\<sharp>q} (Q j)" unfolding Q_def
            by (rule symmetric_mpoly_symmetric_sum[of _ id]) (auto simp: permutes_bij)
          interpret coeff_lift_hom: map_poly_idom_hom "\<lambda>x. [:x:]"
            by standard
          define lc :: complex where "lc = of_int (Polynomial.lead_coeff q)"
          have "of_int_poly q = Polynomial.smult (Polynomial.lead_coeff q) (\<Prod>x\<in>Roots q. [:-x, 1:])"
            by (rule of_int_poly_P) fact
          also have "poly_lift \<dots> = Polynomial.smult [:lc:] (\<Prod>a\<in>Roots q. [:-[:a:], 1:])"
            by (simp add: poly_lift_def map_poly_smult coeff_lift_hom.hom_prod lc_def)
          also have "(\<Prod>a\<in>Roots q. [:-[:a:], 1:]) = (\<Prod>i<\<sharp>q. [:-[:root q i:], 1:])"
            by (intro prod.reindex_bij_betw [symmetric] root q)
          also have "\<dots> = (\<Prod>i<\<sharp>q. [:- ((\<lambda>x. [:x:]) \<circ> root q) i, 1:])"
            by simp
          finally show "poly_lift (Ring_Hom_Poly.of_int_poly q) = Polynomial.smult [:lc:] \<dots>" .
          have "lc \<noteq> 0"
            using q by (auto simp: lc_def)
          thus "[:inverse lc:] * [:lc:] = 1"
            by (simp add: field_simps)
        qed (auto simp: ratpolys_def coeff_pCons split: nat.splits)

        also have "insertion ((\<lambda>x. [:x:]) \<circ> root q) (Q j) = (\<Sum>i<\<sharp>q. poly (g' j) [:root q i:])"
          by (simp add: Q_def insertion_sum poly_sum)
        also have "\<dots> = (\<Sum>x\<in>Roots q. poly (g' j) [:x:])"
          by (intro sum.reindex_bij_betw root q)
        finally have "\<forall>i. poly.coeff (\<Sum>x\<in>Roots q. poly (g' j) [:x:]) i \<in> \<rat>"
          by (auto simp: ratpolys_def)
        thus ?thesis
          using ratpolyE by metis
      qed
      then obtain Q where Q: "\<And>q j. q \<in> P \<Longrightarrow> map_poly of_rat (Q q j) = (\<Sum>x\<in>Roots q. poly (g' j) [:x:])"
        by metis
      define Q' where "Q' = (\<lambda>q. \<Sum>j<n*p. Q q j)"

      have "J \<alpha> = - (\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q' q) \<alpha>)" if \<alpha>: "\<alpha> \<in> Roots'" for \<alpha>
      proof -
        have "J \<alpha> = -(\<Sum>q\<in>P. of_int (\<beta> q) * (\<Sum>x\<in>Roots q. \<Sum>j<n * p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x))"
          (is "_ = -?S") unfolding J_eq[OF \<alpha>] ..
        also have "?S = (\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q' q) \<alpha>)"
        proof (rule sum.cong, goal_cases)
          case q: (2 q)
          interpret \<alpha>: idom_hom "\<lambda>p. ipoly p \<alpha>"
            by standard (auto simp: of_int_hom.poly_map_poly_eval_poly of_int_poly_hom.hom_mult)
  
          have "(\<Sum>x\<in>Roots q. \<Sum>j<n * p. poly ((pderiv ^^ j) (f_poly \<alpha>)) x) =
                (\<Sum>j<n * p. \<Sum>x\<in>Roots q. poly ((pderiv ^^ j) (f_poly \<alpha>)) x)"
            by (rule sum.swap)
          also have "\<dots> = (\<Sum>j<n * p. eval_poly of_rat (Q q j) \<alpha>)"
          proof (rule sum.cong, goal_cases)
            case j: (2 j)
            have "(\<Sum>x\<in>Roots q. poly ((pderiv ^^ j) (f_poly \<alpha>)) x) =
                  (\<Sum>x\<in>Roots q. poly (poly (g' j) [:x:]) \<alpha>)"
            proof (rule sum.cong, goal_cases)
              case (2 x)
              have "poly ((pderiv ^^ j) (f_poly \<alpha>)) x =
                    poly ((pderiv ^^ j) (map_poly (\<lambda>p. ipoly p \<alpha>) g)) x"
                by (subst g[OF \<alpha>, symmetric]) (rule refl)
              also have "\<dots> = poly (eval_poly ((\<lambda>p. [:poly p \<alpha>:]) \<circ> of_int_poly) ((pderiv ^^ j) g) [:0, 1:]) x"
                unfolding o_def \<alpha>.map_poly_higher_pderiv [symmetric]
                by (simp only: \<alpha>.map_poly_eval_poly)
              also have "\<dots> = poly (eval_poly (\<lambda>p. [:poly p \<alpha>:])
                                (map_poly of_int_poly ((pderiv ^^ j) g)) [:0, 1:]) x"
                unfolding eval_poly_def by (subst map_poly_map_poly) auto
              also have "\<dots> = poly (poly (map_poly of_int_poly ((pderiv ^^ j) g)) [:x:]) \<alpha>"
                by (rule poly_poly_eq [symmetric])
              also have "\<dots> = poly (poly (g' j) [:x:]) \<alpha>"
                by (simp add: g'_def)
              finally show ?case .
            qed auto
            also have "\<dots> = poly (\<Sum>x\<in>Roots q. poly (g' j) [:x:]) \<alpha>"
              by (simp add: poly_sum)
            also have "\<dots> = eval_poly of_rat (Q q j) \<alpha>"
              using q by (simp add: Q eval_poly_def)
            finally show ?case .
          qed auto
          also have "\<dots> = eval_poly of_rat (Q' q) \<alpha>"
            by (simp add: Q'_def of_rat_hom.eval_poly_sum)
          finally show ?case by simp
        qed auto
        finally show "J \<alpha> = - (\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q' q) \<alpha>)" .
      qed
      thus ?thesis using that[of Q'] by metis
    qed

    have "J' \<in> \<rat>"
    proof -
      have "(\<Prod>\<alpha>\<in>Roots q. J \<alpha>) \<in> \<rat>" if q: "q \<in> P" for q
      proof -
        obtain root where root: "bij_betw root {..<\<sharp>q} (Roots q)"
          using ex_bij_betw_nat_finite[OF finite_Roots[OF q]]
          unfolding atLeast0LessThan n_roots_def by metis
        define Q' :: "complex poly"
          where "Q' = -(\<Sum>q\<in>P. Polynomial.smult (of_int (\<beta> q)) (map_poly of_rat (Q q)))"

        have "(\<Prod>\<alpha>\<in>Roots q. J \<alpha>) = (\<Prod>\<alpha>\<in>Roots q. -(\<Sum>q\<in>P. of_int (\<beta> q) * eval_poly of_rat (Q q) \<alpha>))"
          by (intro prod.cong refl Q) (auto simp: Roots'_def q)
        also have "\<dots> = (\<Prod>\<alpha>\<in>Roots q. poly Q' \<alpha>)"
          by (simp add: Q'_def poly_sum eval_poly_def)
        also have "\<dots> = (\<Prod>i<\<sharp>q. poly Q' (root i))"
          by (intro prod.reindex_bij_betw [symmetric] root)
        also have "\<dots> = insertion root (\<Prod>i<\<sharp>q. mpoly_of_poly i Q')"
          by (simp add: insertion_prod)
        also have "\<dots> \<in> \<rat>"
        proof (rule symmetric_poly_of_roots_in_subring)
          show "ring_closed (\<rat> :: complex set)"
            by standard auto
          then interpret Q: ring_closed "\<rat> :: complex set" .
          show "\<forall>m. MPoly_Type.coeff (\<Prod>i<\<sharp>q. mpoly_of_poly i Q') m \<in> \<rat>"
            by (auto intro!: Q.coeff_prod_closed sum_in_Rats
                     simp: coeff_mpoly_of_poly when_def Q'_def Polynomial.coeff_sum)
          show "symmetric_mpoly {..<\<sharp>q} (\<Prod>i<\<sharp>q. mpoly_of_poly i Q')"
            by (intro symmetric_mpoly_symmetric_prod'[of _ id]) (auto simp: permutes_bij)
          show "vars (\<Prod>i<\<sharp>q. mpoly_of_poly i Q') \<subseteq> {..<\<sharp>q}"
            by (intro order.trans[OF vars_prod] order.trans[OF vars_mpoly_of_poly] UN_least) auto
          define lc where "lc = (of_int (Polynomial.lead_coeff q) :: complex)"
          have "of_int_poly q = Polynomial.smult lc (\<Prod>x\<in>Roots q. [:- x, 1:])"
            unfolding lc_def by (rule of_int_poly_P) fact
          also have "(\<Prod>x\<in>Roots q. [:- x, 1:]) = (\<Prod>i<\<sharp>q. [:- root i, 1:])"
            by (intro prod.reindex_bij_betw [symmetric] root)
          finally show "of_int_poly q = Polynomial.smult lc (\<Prod>i<\<sharp>q. [:- root i, 1:])" .
          have "lc \<noteq> 0"
            using q by (auto simp: lc_def)
          thus "inverse lc * lc = 1" "inverse lc \<in> \<rat>"
            by (auto simp: lc_def)
        qed auto
        finally show ?thesis .
      qed
      hence "(\<Prod>q\<in>P. \<Prod>\<alpha>\<in>Roots q. J \<alpha>) \<in> \<rat>"
        by (rule prod_in_Rats)
      also have "(\<Prod>q\<in>P. \<Prod>\<alpha>\<in>Roots q. J \<alpha>) = J'"
        unfolding Roots'_def J'_def using disjoint
        by (intro prod.UNION_disjoint [symmetric]) (auto simp: disjoint_family_on_def)
      finally show "J' \<in> \<rat>" .
    qed

    text \<open>
      Since \<open>J'\<close> is clearly an algebraic integer, we now know that it is in fact an integer.
    \<close>
    moreover have "algebraic_int J'"
      unfolding J'_def 
    proof (intro algebraic_int_prod)
      fix x assume "x \<in> Roots'"
      hence "fact (p - 1) alg_dvd J x"
        by (intro J)
      thus "algebraic_int (J x)"
        by (rule alg_dvd_imp_algebraic_int) auto
    qed
    ultimately have "J' \<in> \<int>"
      using rational_algebraic_int_is_int by blast

    text \<open>
      It is also non-zero, as none of the $J_i$ have $p$ as a factor and such cannot be zero.
    \<close>
    have "J' \<noteq> 0"
      unfolding J'_def
    proof (intro prod_nonzeroI)
      fix \<alpha> assume "\<alpha> \<in> Roots'"
      hence "\<not>of_nat p alg_dvd J \<alpha>"
        using J(2)[of \<alpha>] by auto
      thus "J \<alpha> \<noteq> 0"
        by auto
    qed

    text \<open>
      It then clearly follows that $(p-1)!^n \leq J$:
    \<close>
    have "fact (p - 1) ^ n alg_dvd J'"
    proof -
      have "fact (p - 1) ^ n = (\<Prod>\<alpha>\<in>Roots'. fact (p - 1))"
        by (simp add: n_altdef)
      also have "\<dots> alg_dvd J'"
        unfolding J'_def by (intro prod_alg_dvd_prod J(1))
      finally show ?thesis .
    qed
  
    have "fact (p - 1) ^ n \<le> norm J'"
    proof -
      from \<open>J' \<in> \<int>\<close> obtain J'' where [simp]: "J' = of_int J''"
        by (elim Ints_cases)
      have "of_int (fact (p - 1) ^ n) = (fact (p - 1) ^ n :: complex)"
        by simp
      also have "\<dots> alg_dvd J'"
        by fact
      also have "J' = of_int J''"
        by fact
      finally have "fact (p - 1) ^ n dvd J''"
        by (subst (asm) alg_dvd_of_int_iff)
      moreover from \<open>J' \<noteq> 0\<close> have "J'' \<noteq> 0"
        by auto
      ultimately have "\<bar>J''\<bar> \<ge> \<bar>fact (p - 1) ^ n\<bar>"
        by (intro dvd_imp_le_int)
      hence "real_of_int \<bar>J''\<bar> \<ge> real_of_int \<bar>fact (p - 1) ^ n\<bar>"
        by linarith
      also have "real_of_int \<bar>J''\<bar> = norm J'"
        by simp
      finally show ?thesis
        by simp
    qed

    text \<open>The standard M-L bound for $I_i(x)$ shows the following inequality:\<close>
    also have "norm J' \<le> C' * C p ^ n"
    proof -
      have "norm J' = (\<Prod>x\<in>Roots'. norm (J x))"
        unfolding J'_def prod_norm [symmetric] ..
      also have "\<dots> \<le> (\<Prod>x\<in>Roots'. \<Sum>q\<in>P. real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. cmod \<alpha> * exp (cmod \<alpha>) * C p))"
      proof (intro prod_mono conjI)
        fix x assume x: "x \<in> Roots'"
        show "norm (J x) \<le> (\<Sum>q\<in>P. real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. norm \<alpha> * exp (norm \<alpha>) * C p))"
          unfolding J_def
        proof (intro sum_norm_le)
          fix q assume "q \<in> P"
          show "norm (of_int (\<beta> q) * sum (I x) (Roots q)) \<le>
                  real_of_int \<bar>\<beta> q\<bar> * (\<Sum>\<alpha>\<in>Roots q. norm \<alpha> * exp (norm \<alpha>) * C p)"
            unfolding norm_mult norm_of_int of_int_abs
          proof (intro mult_left_mono sum_norm_le)
            fix \<alpha> assume "\<alpha> \<in> Roots q"
            hence \<alpha>: "\<alpha> \<in> Roots'"
              using \<open>q \<in> P\<close> by (auto simp: Roots'_def)
            show "norm (I x \<alpha>) \<le> norm \<alpha> * exp (norm \<alpha>) * C p"
              unfolding I_def
            proof (intro lindemann_weierstrass_aux.lindemann_weierstrass_integral_bound)
              fix t assume "t \<in> closed_segment 0 \<alpha>"
              also have "closed_segment 0 \<alpha> \<subseteq> cball 0 R"
                using \<open>R \<ge> 0\<close> R_ge[OF \<alpha>] by (intro closed_segment_subset) auto
              finally have "norm t \<le> R" by simp
  
              have norm_diff_le: "norm (t - y) \<le> 2 * R" if "y \<in> Roots'" for y
              proof -
                have "norm (t - y) \<le> norm t + norm y"
                  by (meson norm_triangle_ineq4)
                also have "\<dots> \<le> R + R"
                  by (intro add_mono[OF \<open>norm t \<le> R\<close> R_ge] that)
                finally show ?thesis by simp
              qed
  
              have "norm (poly (f_poly x) t) =
                      \<bar>real_of_int l\<bar> ^ (n * p) * (\<Prod>y\<in>Roots'. cmod (t - y) ^ (if y = x then p - 1 else p))"
                by (simp add: eval_f x f_def norm_mult norm_power flip: prod_norm)
              also have "\<dots> \<le> \<bar>real_of_int l\<bar> ^ (n * p) * (\<Prod>y\<in>Roots'. (2*R) ^ (if y = x then p - 1 else p))"
                by (intro mult_left_mono prod_mono conjI power_mono norm_diff_le) auto
              also have "\<dots> = \<bar>real_of_int l\<bar>^(n*p) * (2^(p-1) * R^(p-1) * (2^p*R^p)^(n-1))"
                using x by (subst prod.If_eq) (auto simp: card_Diff_subset n_altdef)
              also have "2^(p-1) * R^(p-1) * (2^p*R^p)^(n-1) = (2^((p-1)+p*(n-1))) * (R^((p-1)+p*(n-1)))"
                unfolding power_mult power_mult_distrib power_add by (simp add: mult_ac)
              also have "(p-1)+p*(n-1) = p*n - 1"
                using \<open>n > 0\<close> \<open>p > 1\<close> by (cases n) (auto simp: algebra_simps)
              also have "2 ^ (p * n - 1) * R ^ (p * n - 1) = (2*R)^(n * p-1)"
                unfolding power_mult_distrib by (simp add: mult_ac)
              finally show "norm (poly (f_poly x) t) \<le> C p"
                unfolding C_def using \<open>l > 0\<close> by simp
            qed (use \<open>R \<ge> 0\<close> \<open>l > 0\<close> in \<open>auto simp: C_def\<close>)
          qed auto
        qed
      qed auto
      also have "\<dots> = C' * C p ^ n"
        by (simp add: C'_def power_mult_distrib n_altdef flip: sum_distrib_right mult.assoc)
      finally show ?thesis .
    qed

    text \<open>And with that, we have our inequality:\<close>
    finally show "fact (p - 1) ^ n \<le> C' * C p ^ n" .
  qed

  text \<open>
    Some simple asymptotic estimates show that this is clearly a contradiction, since
    the left-hand side grows much faster than the right-hand side and there are infinitely many
    sufficiently large primes:
  \<close>
  have freq: "frequently prime sequentially"
    using frequently_prime_cofinite unfolding cofinite_eq_sequentially .
  have ev: "eventually (\<lambda>p. (\<forall>q\<in>P.  int p > \<bar>\<beta> q\<bar>) \<and>
              real p > norm (\<Prod>\<alpha>\<in>Roots'. of_int (l^n) * (\<Prod>\<alpha>'\<in>Roots'-{\<alpha>}. (\<alpha>-\<alpha>')))) sequentially"
    by (intro eventually_ball_finite \<open>finite P\<close> ballI eventually_conj filterlim_real_sequentially
          eventually_compose_filterlim[OF eventually_gt_at_top] filterlim_int_sequentially)

  have "frequently (\<lambda>p. fact (p - 1) ^ n \<le> C' * C p ^ n) sequentially"
    by (rule frequently_eventually_mono[OF freq ev]) (use ineq in blast)
  moreover have "eventually (\<lambda>p. fact (p - 1) ^ n > C' * C p ^ n) sequentially"
  proof (cases "R = 0")
    case True
    have "eventually (\<lambda>p. p * n > 1) at_top" using \<open>n > 0\<close>
      by (intro eventually_compose_filterlim[OF eventually_gt_at_top] mult_nat_right_at_top)
    thus ?thesis 
      by eventually_elim (use \<open>n > 0\<close> True in \<open>auto simp: C_def power_0_left mult_ac\<close>)
  next
    case False
    hence "R > 0"
      using \<open>R \<ge> 0\<close> by auto
    define D :: real where "D = (2 * R * \<bar>real_of_int l\<bar>) ^ n" 
    have "D > 0"
      using \<open>R > 0\<close> \<open>l > 0\<close> unfolding D_def by (intro zero_less_power) auto

    have "(\<lambda>p. C' * C p ^ n) \<in> O(\<lambda>p. C p ^ n)"
      by simp
    also have "(\<lambda>p. C p ^ n) \<in> O(\<lambda>p. ((2 * R * l) ^ (n * p)) ^ n)"
    proof (rule landau_o.big_power[OF bigthetaD1])
      have np: "eventually (\<lambda>p. p * n > 0) at_top" using \<open>n > 0\<close>
        by (intro eventually_compose_filterlim[OF eventually_gt_at_top] mult_nat_right_at_top)
      have "eventually (\<lambda>p. (2 * R) * C p = (2 * R * l) ^ (n * p)) at_top"
        using np
      proof eventually_elim
        case (elim p)
        have "2 * R * C p = l ^ (n * p) * (2 * R) ^ (Suc (n * p - 1))"
          by (simp add: C_def algebra_simps)
        also have "Suc (n * p - 1) = n * p"
          using elim by auto
        finally show ?case
          by (simp add: algebra_simps)
      qed
      hence "(\<lambda>p. (2 * R) * C p) \<in> \<Theta>(\<lambda>p. (2 * R * l) ^ (n * p))"
        by (intro bigthetaI_cong)
      thus "C \<in> \<Theta>(\<lambda>p. (2 * R * l) ^ (n * p))"
        using \<open>R > 0\<close> by simp
    qed
    also have "\<dots> = O(\<lambda>p. (D ^ p) ^ n)"
      using \<open>l > 0\<close> by (simp flip: power_mult add: power2_eq_square mult_ac D_def)
    also have "(\<lambda>p. (D ^ p) ^ n) \<in> o(\<lambda>p. fact (p - 1) ^ n)"
    proof (intro landau_o.small_power)
      have "eventually (\<lambda>p. D ^ p = D * D ^ (p - 1)) at_top"
        using eventually_gt_at_top[of 0]
        by eventually_elim (use \<open>D > 0\<close> in \<open>auto simp flip: power_Suc\<close>)
      hence "(\<lambda>p. D ^ p) \<in> \<Theta>(\<lambda>p. D * D ^ (p - 1))"
        by (intro bigthetaI_cong)
      hence "(\<lambda>p. D ^ p) \<in> \<Theta>(\<lambda>p. D ^ (p - 1))"
        using \<open>D > 0\<close> by simp
      also have "(\<lambda>p. D ^ (p - 1)) \<in> o(\<lambda>p. fact (p - 1))"
        by (intro smalloI_tendsto[OF filterlim_compose[OF power_over_fact_tendsto_0]]
                  filterlim_minus_nat_at_top) auto
      finally show "(\<lambda>p. D ^ p) \<in> o(\<lambda>x. fact (x - 1))" .
    qed fact+
    finally have smallo: "(\<lambda>p. C' * C p ^ n) \<in> o(\<lambda>p. fact (p - 1) ^ n)" .
    have "eventually (\<lambda>p. \<bar>C' * C p ^ n\<bar> \<le> 1/2 * fact (p - 1) ^ n) at_top"
      using landau_o.smallD[OF smallo, of "1/2"] by simp
    thus "eventually (\<lambda>p. C' * C p ^ n < fact (p - 1) ^ n) at_top"
    proof eventually_elim
      case (elim p)
      have "C' * C p ^ n \<le> \<bar>C' * C p ^ n\<bar>"
        by simp
      also have "\<dots> \<le> 1/2 * fact (p - 1) ^ n"
        by fact
      also have "\<dots> < fact (p - 1) ^ n"
        by simp
      finally show ?case .
    qed
  qed
  ultimately have "frequently (\<lambda>p::nat. False) sequentially"
    by (rule frequently_eventually_mono) auto
  thus False
    by simp
qed


subsection \<open>Removing the restriction of full sets of conjugates\<close>

text \<open>
  We will now remove the restriction that the $\alpha_i$ must occur in full sets of conjugates
  by multiplying the equality with all permutations of roots.
\<close>
lemma Hermite_Lindemann_aux2:
  fixes X :: "complex set" and \<beta> :: "complex \<Rightarrow> int"
  assumes "finite X"
  assumes nz:   "\<And>x. x \<in> X \<Longrightarrow> \<beta> x \<noteq> 0"
  assumes alg:  "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes sum0: "(\<Sum>x\<in>X. of_int (\<beta> x) * exp x) = 0"
  shows   "X = {}"
proof (rule ccontr)
  assume "X \<noteq> {}"
  note [intro] = \<open>finite X\<close>

  text \<open>
    Let \<open>P\<close> be the smallest integer polynomial whose roots are a superset of \<open>X\<close>:
  \<close>
  define P :: "int poly" where "P = \<Prod>(min_int_poly ` X)"
  define Roots :: "complex set" where "Roots = {x. ipoly P x = 0}"
  have [simp]: "P \<noteq> 0"
    using \<open>finite X\<close> by (auto simp: P_def)
  have [intro]: "finite Roots"
    unfolding Roots_def by (intro poly_roots_finite) auto

  have "X \<subseteq> Roots"
  proof safe
    fix x assume "x \<in> X"
    hence "ipoly (min_int_poly x) x = 0"
      by (intro ipoly_min_int_poly alg)
    thus "x \<in> Roots"
      using \<open>finite X\<close> \<open>x \<in> X\<close>
      by (auto simp: Roots_def P_def of_int_poly_hom.hom_prod poly_prod)
  qed

  have "squarefree (of_int_poly P :: complex poly)"
    unfolding P_def of_int_poly_hom.hom_prod
  proof (rule squarefree_prod_coprime; safe)
    fix x assume "x \<in> X"
    thus "squarefree (of_int_poly (min_int_poly x) :: complex poly)"
      by (intro squarefree_of_int_polyI) auto
  next
    fix x y assume xy: "x \<in> X" "y \<in> X" "min_int_poly x \<noteq> min_int_poly y"
    thus "Rings.coprime (of_int_poly (min_int_poly x)) (of_int_poly (min_int_poly y) :: complex poly)"
      by (intro coprime_of_int_polyI[OF primes_coprime]) auto
  qed

  text \<open>
    Since we will need a numbering of these roots, we obtain one:
  \<close>
  define n where "n = card Roots"
  obtain Root where Root: "bij_betw Root {..<n} Roots"
    using ex_bij_betw_nat_finite[OF \<open>finite Roots\<close>] unfolding n_def atLeast0LessThan by metis
  define unRoot :: "complex \<Rightarrow> nat" where "unRoot = inv_into {..<n} Root"
  have unRoot: "bij_betw unRoot Roots {..<n}"
    unfolding unRoot_def by (intro bij_betw_inv_into Root)
  have unRoot_Root [simp]: "unRoot (Root i) = i" if "i < n" for i
    unfolding unRoot_def using Root that by (subst inv_into_f_f) (auto simp: bij_betw_def)
  have Root_unRoot [simp]: "Root (unRoot x) = x" if "x \<in> Roots" for x
    unfolding unRoot_def using Root that by (subst f_inv_into_f) (auto simp: bij_betw_def)
  have [simp, intro]: "Root i \<in> Roots" if "i < n" for i
    using Root that by (auto simp: bij_betw_def)
  have [simp, intro]: "unRoot x < n" if "x \<in> Roots" for x
    using unRoot that by (auto simp: bij_betw_def)

  text \<open>
    We will also need to convert between permutations of natural numbers less than \<open>n\<close> and
    permutations of the roots:
  \<close>
  define convert_perm :: "(nat \<Rightarrow> nat) \<Rightarrow> (complex \<Rightarrow> complex)" where
    "convert_perm = (\<lambda>\<sigma> x. if x \<in> Roots then Root (\<sigma> (unRoot x)) else x)"
  have bij_convert: "bij_betw convert_perm {\<sigma>. \<sigma> permutes {..<n}} {\<sigma>. \<sigma> permutes Roots}"
    using bij_betw_permutations[OF Root] unfolding convert_perm_def unRoot_def .
  have permutes_convert_perm [intro]: "convert_perm \<sigma> permutes Roots" if "\<sigma> permutes {..<n}" for \<sigma>
    using that bij_convert unfolding bij_betw_def by blast
  have convert_perm_compose: "convert_perm (\<pi> \<circ> \<sigma>) = convert_perm \<pi> \<circ> convert_perm \<sigma>"
    if "\<pi> permutes {..<n}" "\<sigma> permutes {..<n}" for \<sigma> \<pi>
  proof (intro ext)
    fix x show "convert_perm (\<pi> \<circ> \<sigma>) x = (convert_perm \<pi> \<circ> convert_perm \<sigma>) x"
    proof (cases "x \<in> Roots")
      case True
      thus ?thesis
        using permutes_in_image[OF that(2), of "unRoot x"]
        by (auto simp: convert_perm_def bij_betw_def)
    qed (auto simp: convert_perm_def)
  qed

  text \<open>
    We extend the coefficient vector to the new roots by setting their coefficients to 0:
  \<close>
  define \<beta>' where "\<beta>' = (\<lambda>x. if x \<in> X then \<beta> x else 0)"

  text \<open>
    We now define the set of all permutations of our roots:
  \<close>
  define perms where "perms = {\<pi>. \<pi> permutes Roots}"
  have [intro]: "finite perms"
    unfolding perms_def by (rule finite_permutations) auto
  have [simp]: "card perms = fact n"
    unfolding perms_def n_def by (intro card_permutations) auto

  text \<open>
    The following is the set of all \<open>n!\<close>-tuples of roots, disregarding permutation of components.
    In other words: all multisets of roots with size \<open>n!\<close>.
  \<close>
  define Roots_ms :: "complex multiset set" where
    "Roots_ms = {X. set_mset X \<subseteq> Roots \<and> size X = fact n}"
  have [intro]: "finite Roots_ms"
    unfolding Roots_ms_def by (rule finite_multisets_of_size) auto

  text \<open>
    Next, the following is the set of \<open>n!\<close>-tuples whose entries are precisely the multiset \<open>X\<close>:
  \<close>
  define tuples :: "complex multiset \<Rightarrow> ((complex \<Rightarrow> complex) \<Rightarrow> complex) set" where
    "tuples = (\<lambda>X. {f\<in>perms \<rightarrow>\<^sub>E Roots. image_mset f (mset_set perms) = X})"
  have fin_tuples [intro]: "finite (tuples X)" for X
    unfolding tuples_def by (rule finite_subset[of _ "perms \<rightarrow>\<^sub>E Roots", OF _ finite_PiE]) auto
  define tuples' :: "(complex multiset \<times> ((complex \<Rightarrow> complex) \<Rightarrow> complex)) set" where
    "tuples' = (SIGMA X:Roots_ms. tuples X)"

  text \<open>
    The following shows that our \<^term>\<open>tuples\<close> definition is stable under permutation of
    the roots.
  \<close>
  have bij_convert': "bij_betw (\<lambda>f. f \<circ> (\<lambda>g. \<sigma> \<circ> g)) (tuples X) (tuples X)"
    if \<sigma>: "\<sigma> permutes Roots" for \<sigma> X
  proof (rule bij_betwI)
    have *: "(\<lambda>f. f \<circ> (\<circ>) \<sigma>) \<in> tuples X \<rightarrow> tuples X" if \<sigma>: "\<sigma> permutes Roots" for \<sigma>
    proof
      fix f assume f: "f \<in> tuples X"
      show "f \<circ> (\<circ>) \<sigma> \<in> tuples X"
        unfolding tuples_def
      proof safe
        fix \<sigma>'
        assume \<sigma>': "\<sigma>' \<in> perms"
        show "(f \<circ> (\<circ>) \<sigma>) \<sigma>' \<in> Roots"
          using permutes_compose[OF _ \<sigma>, of \<sigma>'] \<sigma> \<sigma>' f by (auto simp: perms_def tuples_def)
      next
        fix \<sigma>'
        assume \<sigma>': "\<sigma>' \<notin> perms"
        have "\<not>(\<sigma> \<circ> \<sigma>') permutes Roots"
        proof
          assume "(\<sigma> \<circ> \<sigma>') permutes Roots"
          hence "inv_into UNIV \<sigma> \<circ> (\<sigma> \<circ> \<sigma>') permutes Roots"
            by (rule permutes_compose) (use permutes_inv[OF \<sigma>] in simp_all)
          also have "inv_into UNIV \<sigma> \<circ> (\<sigma> \<circ> \<sigma>') = \<sigma>'"
            by (auto simp: fun_eq_iff permutes_inverses[OF \<sigma>])
          finally show False using \<sigma>' by (simp add: perms_def)
        qed
        thus "(f \<circ> (\<circ>) \<sigma>) \<sigma>' = undefined"
          using f by (auto simp: perms_def tuples_def)
      next
        have "image_mset (f \<circ> (\<circ>) \<sigma>) (mset_set perms) =
              image_mset f (image_mset ((\<circ>) \<sigma>) (mset_set perms))"
          by (rule multiset.map_comp [symmetric])
        also have "image_mset ((\<circ>) \<sigma>) (mset_set perms) = mset_set perms"
          using bij_betw_permutes_compose_left[OF \<sigma>]
          by (subst image_mset_mset_set) (auto simp: bij_betw_def perms_def)
        also have "image_mset f \<dots> = X"
          using f by (auto simp: tuples_def)
        finally show "image_mset (f \<circ> (\<circ>) \<sigma>) (mset_set perms) = X" .
      qed
    qed

    show "(\<lambda>f. f \<circ> (\<circ>) \<sigma>) \<in> tuples X \<rightarrow> tuples X"
      by (rule *) fact
    show "(\<lambda>f. f \<circ> (\<circ>) (inv_into UNIV \<sigma>)) \<in> tuples X \<rightarrow> tuples X"
      by (intro * permutes_inv) fact
    show "f \<circ> (\<circ>) \<sigma> \<circ> (\<circ>) (inv_into UNIV \<sigma>) = f" if "f \<in> tuples X" for f
      by (auto simp: fun_eq_iff o_def permutes_inverses[OF \<sigma>])
    show "f \<circ> (\<circ>) (inv_into UNIV \<sigma>) \<circ> (\<circ>) \<sigma> = f" if "f \<in> tuples X" for f
      by (auto simp: fun_eq_iff o_def permutes_inverses[OF \<sigma>])
  qed

  text \<open>
    Next, we define the multiset of of possible exponents that we can get for a given
    \<open>n!\<close>-multiset of roots,
  \<close>
  define R :: "complex multiset \<Rightarrow> complex multiset" where
    "R = (\<lambda>X. image_mset (\<lambda>f. \<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)) (mset_set (tuples X)))"

  text \<open>
    We show that, for each such multiset, there is a content-free integer polynomial that has
    exactly these exponents as roots. This shows that they form a full set of conjugates (but
    note this polynomial is not necessarily squarefree).

    The proof is yet another application of the fundamental theorem of symmetric polynomials.
  \<close>
  obtain Q :: "complex multiset \<Rightarrow> int poly"
    where Q: "\<And>X. X \<in> Roots_ms \<Longrightarrow> poly_roots (of_int_poly (Q X)) = R X"
             "\<And>X. X \<in> Roots_ms \<Longrightarrow> content (Q X) = 1"
  proof -
    {
      fix X :: "complex multiset"
      assume X: "X \<in> Roots_ms"
      define Q :: "complex poly mpoly" where
        "Q = (\<Prod>f\<in>tuples X. Const [:0, 1:] -
                 (\<Sum>\<sigma> | \<sigma> permutes {..<n}. Var (\<sigma> (unRoot (f (convert_perm \<sigma>))))))"
      define Q1 where "Q1 = (\<Prod>f\<in>tuples X. [:- (\<Sum>\<sigma> | \<sigma> permutes Roots. \<sigma> (f \<sigma>)), 1:])"
      define ratpolys :: "complex poly set" where "ratpolys = {p. \<forall>i. poly.coeff p i \<in> \<rat>}"

      have "insertion (\<lambda>x. [:Root x:]) Q \<in> ratpolys"
      proof (rule symmetric_poly_of_roots_in_subring[where l = "\<lambda>x. [:x:]"])
        show "ring_closed ratpolys"
          unfolding ratpolys_def by standard (auto intro: coeff_mult_semiring_closed)
        then interpret ratpolys: ring_closed ratpolys .
        have "pCons 0 1 \<in> ratpolys "
          by (auto simp: ratpolys_def coeff_pCons split: nat.splits)
        thus "\<forall>m. MPoly_Type.coeff Q m \<in> ratpolys"
          unfolding Q_def
          by (intro allI ratpolys.coeff_prod_closed)
             (auto intro!: ratpolys.minus_closed ratpolys.sum_closed ratpolys.uminus_closed simp: coeff_Var mpoly_coeff_Const when_def)
      next
        show "ring_homomorphism (\<lambda>x::complex. [:x:])" ..
      next
        have "\<sigma> (unRoot (f (convert_perm \<sigma>))) < n" if "f \<in> tuples X" "\<sigma> permutes {..<n}" for f \<sigma>
        proof -
          have "convert_perm \<sigma> \<in> perms"
            using bij_convert that(2) by (auto simp: bij_betw_def perms_def)
          hence "f (convert_perm \<sigma>) \<in> Roots"
            using that by (auto simp: tuples_def)
          thus ?thesis
            using permutes_in_image[OF that(2)] by simp
        qed
        thus "vars Q \<subseteq> {..<n}"
          unfolding Q_def
          by (intro order.trans[OF vars_prod] UN_least order.trans[OF vars_sum]
                order.trans[OF vars_diff] Un_least) (auto simp: vars_Var)
      next
        define lc :: complex where "lc = of_int (Polynomial.lead_coeff P)"
        show "[:inverse lc:] \<in> ratpolys"
          by (auto simp: ratpolys_def coeff_pCons lc_def split: nat.splits)
        show "\<forall>i. [:poly.coeff (of_int_poly P) i:] \<in> ratpolys"
          by (auto simp: ratpolys_def coeff_pCons split: nat.splits)
        have "lc \<noteq> 0"
          by (auto simp: lc_def)
        thus "[:inverse lc:] * [:lc:] = 1"
          by auto
        have "rsquarefree (of_int_poly P :: complex poly)"
          using \<open>squarefree (of_int_poly P :: complex poly)\<close> by (intro squarefree_imp_rsquarefree)
        hence "of_int_poly P = Polynomial.smult lc (\<Prod>x\<in>Roots. [:-x, 1:])"
          unfolding lc_def Roots_def of_int_hom.hom_lead_coeff[symmetric]
          by (rule complex_poly_decompose_rsquarefree [symmetric])
        also have "(\<Prod>x\<in>Roots. [:-x, 1:]) = (\<Prod>i<n. [:-Root i, 1:])"
          by (rule prod.reindex_bij_betw[OF Root, symmetric])
        finally show "of_int_poly P = Polynomial.smult lc (\<Prod>i<n. [:- Root i, 1:])" .
      next
        show "symmetric_mpoly {..<n} Q"
          unfolding symmetric_mpoly_def
        proof safe
          fix \<pi> assume \<pi>: "\<pi> permutes {..<n}"
          have "mpoly_map_vars \<pi> Q = (\<Prod>f\<in>tuples X. Const (pCons 0 1) - (\<Sum> \<sigma> | \<sigma> permutes {..<n}.
                  Var ((\<pi> \<circ> \<sigma>) (unRoot (f (convert_perm \<sigma>))))))"
            by (simp add: Q_def permutes_bij[OF \<pi>])
          also have "\<dots> = (\<Prod>f\<in>tuples X. Const (pCons 0 1) - (\<Sum> \<sigma> | \<sigma> permutes {..<n}.
                  Var ((\<pi> \<circ> \<sigma>) (unRoot ((f \<circ> (\<lambda>\<sigma>. convert_perm \<pi> \<circ> \<sigma>)) (convert_perm \<sigma>))))))"
            using \<pi> by (intro prod.reindex_bij_betw [OF bij_convert', symmetric]) auto
          also have "\<dots> = Q"
            unfolding Q_def
          proof (rule prod.cong, goal_cases)
            case (2 f)
            have "(\<Sum> \<sigma> | \<sigma> permutes {..<n}. Var ((\<pi> \<circ> \<sigma>) (unRoot ((f \<circ> (\<lambda>\<sigma>. convert_perm \<pi> \<circ> \<sigma>)) (convert_perm \<sigma>))))) =
                  (\<Sum> \<sigma> | \<sigma> permutes {..<n}. Var ((\<pi> \<circ> \<sigma>) (unRoot (f (convert_perm (\<pi> \<circ> \<sigma>))))))"
              using \<pi> by (intro sum.cong refl, subst convert_perm_compose) simp_all
            also have "\<dots> = (\<Sum> \<sigma> | \<sigma> permutes {..<n}. Var (\<sigma> (unRoot (f (convert_perm \<sigma>)))))"
              using \<pi> by (rule setum_permutations_compose_left [symmetric])
            finally show ?case by simp
          qed auto
          finally show "mpoly_map_vars \<pi> Q = Q" .
        qed
      qed auto
      also have "insertion (\<lambda>x. [:Root x:]) Q = Q1"
        unfolding Q_def Q1_def insertion_prod insertion_sum insertion_diff insertion_Const insertion_Var
      proof (intro prod.cong, goal_cases)
        case f: (2 f)
        have "(\<Sum>\<sigma> | \<sigma> permutes {..<n}. [:Root (\<sigma> (unRoot (f (convert_perm \<sigma>)))):]) =
              (\<Sum>\<sigma> | \<sigma> permutes {..<n}. [:convert_perm \<sigma> (f (convert_perm \<sigma>)):])"
        proof (rule sum.cong, goal_cases)
          case (2 \<sigma>)
          have "convert_perm \<sigma> permutes Roots"
            using bij_convert 2 by (auto simp: bij_betw_def)
          hence "f (convert_perm \<sigma>) \<in> Roots"
            using f by (auto simp: tuples_def perms_def)
          thus ?case by (simp add: convert_perm_def)
        qed simp_all
        also have "\<dots> = (\<Sum>\<sigma> | \<sigma> permutes Roots. [:\<sigma> (f \<sigma>):])"
          by (rule sum.reindex_bij_betw[OF bij_convert])
        finally show ?case
          by (simp flip: pCons_one coeff_lift_hom.hom_sum)
      qed simp_all
      finally have "Q1 \<in> ratpolys"
        by auto
      then obtain Q2 :: "rat poly" where Q2: "Q1 = map_poly of_rat Q2"
        unfolding ratpolys_def using ratpolyE[of Q1] by blast

      have "Q1 \<noteq> 0"
        unfolding Q1_def using fin_tuples[of X] by auto
      with Q2 have "Q2 \<noteq> 0"
        by auto
      obtain Q3 :: "int poly" and lc :: rat
        where Q3: "Q2 = Polynomial.smult lc (of_int_poly Q3)" and "lc > 0" and "content Q3 = 1"
        using rat_to_normalized_int_poly_exists[OF \<open>Q2 \<noteq> 0\<close>] by metis

      have "poly_roots (of_int_poly Q3) = poly_roots (map_poly (of_rat \<circ> of_int) Q3)"
        by simp
      also have "map_poly (of_rat \<circ> of_int) Q3 = map_poly of_rat (map_poly of_int Q3)"
        by (subst map_poly_map_poly) auto
      also have "poly_roots \<dots> = poly_roots (Polynomial.smult (of_rat lc) \<dots>)"
        using \<open>lc > 0\<close> by simp
      also have "Polynomial.smult (of_rat lc) (map_poly of_rat (map_poly of_int Q3)) =
                 map_poly of_rat (Polynomial.smult lc (map_poly of_int Q3))"
        by (simp add: of_rat_hom.map_poly_hom_smult)
      also have "\<dots> = Q1"
        by (simp only: Q3 [symmetric] Q2 [symmetric])
      also have "poly_roots Q1 = R X"
        unfolding Q1_def
        by (subst poly_roots_prod, force, subst poly_roots_linear)
           (auto simp: R_def perms_def sum_mset_image_mset_singleton sum_unfold_sum_mset)
      finally have "\<exists>Q. poly_roots (of_int_poly Q) = R X \<and> content Q = 1"
        using \<open>content Q3 = 1\<close> by metis
    }
    hence "\<exists>Q. \<forall>X\<in>Roots_ms. poly_roots (of_int_poly (Q X)) = R X \<and> content (Q X) = 1"
      by metis
    thus ?thesis using that by metis
  qed

  text \<open>
    We can now collect all the $e^{\sum \alpha_i}$ that happen to be equal and let the following
    be their coefficients:
  \<close>
  define \<beta>'' :: "int poly \<Rightarrow> int"
    where "\<beta>'' = (\<lambda>q. \<Sum>X\<in>Roots_ms. int (count (prime_factorization (Q X)) q) * (\<Prod>x\<in>#X. \<beta>' x))"
  have supp_\<beta>'': "{q. \<beta>'' q \<noteq> 0} \<subseteq> (\<Union>X\<in>Roots_ms. prime_factors (Q X))"
    unfolding \<beta>''_def using sum.not_neutral_contains_not_neutral by fastforce

  text \<open>
    We have to prove that \<open>\<beta>''\<close> is not zero everywhere. We do this by selecting the nonzero term
    with the maximal exponent (w.r.t. the lexicographic ordering on the complex numbers) in every
    factor of the product and show that there is no other summand corresponding to these, so
    that their non-zero coefficient cannot get cancelled.
  \<close>
  have "{q. \<beta>'' q \<noteq> 0} \<noteq> {}"
  proof -
    define f where "f = restrict (\<lambda>\<sigma>. inv_into UNIV \<sigma> (complex_lex.Max (\<sigma> ` X))) perms"
    have f: "f \<in> perms \<rightarrow> X"
    proof
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> perms"
      have "complex_lex.Max (\<sigma> ` X) \<in> \<sigma> ` X"
        using \<open>X \<noteq> {}\<close> by (intro complex_lex.Max_in finite_imageI) auto
      thus "f \<sigma> \<in> X"
        using \<sigma> by (auto simp: f_def permutes_inverses[of \<sigma> Roots] perms_def)
    qed
    hence f': "f \<in> perms \<rightarrow>\<^sub>E Roots"
      using \<open>X \<subseteq> Roots\<close> by (auto simp: f_def PiE_def)

    define Y where "Y = image_mset f (mset_set perms)"
    have "Y \<in> Roots_ms" using f' \<open>finite perms\<close>
      by (auto simp: Roots_ms_def Y_def)

    have "(\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)) \<in># R Y"
    proof -
      from f' have "f \<in> tuples Y"
        unfolding tuples_def Y_def by simp
      thus ?thesis
        unfolding R_def using fin_tuples[of Y] by auto
    qed
    also have "R Y = poly_roots (of_int_poly (Q Y))"
      by (rule Q(1) [symmetric]) fact
    also have "\<dots> = (\<Sum>p\<in>#prime_factorization (Q Y). poly_roots (of_int_poly p))"
      by (rule poly_roots_of_int_conv_sum_prime_factors)
    finally obtain q where q: "q \<in> prime_factors (Q Y)" "(\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)) \<in># poly_roots (of_int_poly q)"
      by auto

    have "\<beta>'' q = (\<Sum>X\<in>{Y}. int (count (prime_factorization (Q X)) q) * prod_mset (image_mset \<beta>' X))"
      unfolding \<beta>''_def
    proof (intro sum.mono_neutral_right ballI)
      fix Y' assume Y': "Y' \<in> Roots_ms - {Y}"
      show "int (count (prime_factorization (Q Y')) q) * \<Prod>\<^sub># (image_mset \<beta>' Y') = 0"
      proof (cases "set_mset Y' \<subseteq> X")
        case Y'_subset: True
        have "q \<notin> prime_factors (Q Y')"
        proof
          assume q': "q \<in> prime_factors (Q Y')"
          have "poly_roots (of_int_poly q :: complex poly) \<subseteq>#
                         poly_roots (of_int_poly (Q Y'))"
            using q' by (intro dvd_imp_poly_roots_subset of_int_poly_hom.hom_dvd) auto
          with q(2) have "(\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)) \<in># poly_roots (of_int_poly (Q Y'))"
            by (meson mset_subset_eqD)
          also have "poly_roots (of_int_poly (Q Y')) = R Y'"
            using Q(1)[of Y'] Y' by auto
          finally obtain g where g: "g \<in> tuples Y'" "(\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)) = (\<Sum>\<sigma>\<in>perms. \<sigma> (g \<sigma>))"
            unfolding R_def using fin_tuples[of Y'] by auto

          moreover have "(\<Sum>\<sigma>\<in>perms. \<sigma> (g \<sigma>)) <\<^sub>\<complex> (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>))"
          proof (rule sum_strict_mono_ex1_complex_lex)
            show le: "\<forall>\<sigma>\<in>perms. \<sigma> (g \<sigma>) \<le>\<^sub>\<complex> \<sigma> (f \<sigma>)"
            proof
              fix \<sigma> assume \<sigma>: "\<sigma> \<in> perms"
              hence \<sigma>': "\<sigma> permutes Roots"
                by (auto simp: perms_def)
              have "image_mset g (mset_set perms) = Y'"
                using g by (auto simp: tuples_def)
              also have "set_mset \<dots> \<subseteq> X"
                by fact
              finally have "g ` perms \<subseteq> X"
                using \<open>finite perms\<close> by auto
              hence "\<sigma> (g \<sigma>) \<le>\<^sub>\<complex> complex_lex.Max (\<sigma> ` X)"
                using \<open>finite perms\<close> \<sigma>
                by (intro complex_lex.Max.coboundedI finite_imageI imageI)
                   (auto simp: tuples_def)
              also have "\<dots> = \<sigma> (f \<sigma>)"
                using \<sigma> by (simp add: f_def permutes_inverses[OF \<sigma>'])
              finally show "\<sigma> (g \<sigma>) \<le>\<^sub>\<complex> \<sigma> (f \<sigma>)" .
            qed

            have "image_mset g (mset_set perms) \<noteq> image_mset f (mset_set perms)"
              using Y' g by (auto simp: tuples_def Y_def)
            then obtain \<sigma> where \<sigma>: "\<sigma> \<in># mset_set perms" "g \<sigma> \<noteq> f \<sigma>"
              by (meson multiset.map_cong)
            have "\<sigma> permutes Roots"
              using \<sigma> \<open>finite perms\<close> by (auto simp: perms_def)
            have "\<sigma> (g \<sigma>) \<noteq> \<sigma> (f \<sigma>)"
              using permutes_inj[OF \<open>\<sigma> permutes Roots\<close>] \<sigma> by (auto simp: inj_def)
            moreover have "\<sigma> (g \<sigma>) \<le>\<^sub>\<complex> \<sigma> (f \<sigma>)"
              using le \<sigma> \<open>finite perms\<close> by auto
            ultimately have "\<sigma> (g \<sigma>) <\<^sub>\<complex> \<sigma> (f \<sigma>)"
              by simp
            thus "\<exists>\<sigma>\<in>perms. \<sigma> (g \<sigma>) <\<^sub>\<complex> \<sigma> (f \<sigma>)"
              using \<sigma> \<open>finite perms\<close> by auto
          qed (use \<open>finite perms\<close> in simp_all)
          ultimately show False by simp
        qed
        thus ?thesis by auto
      qed (auto simp: \<beta>'_def)
    qed (use \<open>Y \<in> Roots_ms\<close> in auto)
    also have "\<dots> = int (count (prime_factorization (Q Y)) q) * prod_mset (image_mset \<beta>' Y)"
      by simp
    also have "\<dots> \<noteq> 0"
      using q nz \<open>finite X\<close> \<open>X \<noteq> {}\<close> \<open>finite perms\<close> f by (auto simp: \<beta>'_def Y_def)
    finally show "{q. \<beta>'' q \<noteq> 0} \<noteq> {}"
      by auto
  qed

  text \<open>
    We are now ready for the final push: we start with the original sum that we know to be zero,
    multiply it with the other permutations, and then multiply out the sum.
  \<close>
  have "0 = (\<Sum>x\<in>X. \<beta> x * exp x)"
    using sum0 ..
  also have "\<dots> = (\<Sum>x\<in>Roots. \<beta>' x * exp x)"
    by (intro sum.mono_neutral_cong_left \<open>X \<subseteq> Roots\<close>) (auto simp: \<beta>'_def)
  also have "\<dots> dvd (\<Prod>\<sigma>\<in>perms. \<Sum>x\<in>Roots. \<beta>' x * exp (\<sigma> x))"
    by (rule dvd_prodI[OF \<open>finite perms\<close>])
       (use permutes_id[of Roots] in \<open>simp_all add: id_def perms_def\<close>)
  also have "\<dots> = (\<Sum>f\<in>perms \<rightarrow>\<^sub>E Roots. \<Prod>\<sigma>\<in>perms. \<beta>' (f \<sigma>) * exp (\<sigma> (f \<sigma>)))"
    by (rule prod_sum_PiE) auto
  also have "\<dots> = (\<Sum>f\<in>perms \<rightarrow>\<^sub>E Roots. (\<Prod>\<sigma>\<in>perms. \<beta>' (f \<sigma>)) * exp (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)))"
    using \<open>finite perms\<close> by (simp add: prod.distrib exp_sum)
  also have "\<dots> = (\<Sum>(X,f)\<in>tuples'. (\<Prod>\<sigma>\<in>perms. \<beta>' (f \<sigma>)) * exp (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)))"
    using \<open>finite perms\<close>
    by (intro sum.reindex_bij_witness[of _ snd "\<lambda>f. (image_mset f (mset_set perms), f)"])
       (auto simp: tuples'_def tuples_def Roots_ms_def PiE_def Pi_def)
  also have "\<dots> = (\<Sum>(X,f)\<in>tuples'. (\<Prod>x\<in>#X. \<beta>' x) * exp (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)))"
  proof (safe intro!: sum.cong)
    fix X :: "complex multiset" and f :: "(complex \<Rightarrow> complex) \<Rightarrow> complex"
    assume "(X, f) \<in> tuples'"
    hence X: "X \<in> Roots_ms" "X = image_mset f (mset_set perms)" and f: "f \<in> perms \<rightarrow>\<^sub>E Roots"
      by (auto simp: tuples'_def tuples_def)
    have "(\<Prod>\<sigma>\<in>perms. \<beta>' (f \<sigma>)) = (\<Prod>\<sigma>\<in>#mset_set perms. \<beta>' (f \<sigma>))"
      by (meson prod_unfold_prod_mset)
    also have "\<dots> = (\<Prod>x\<in>#X. \<beta>' x)"
      unfolding X(2) by (simp add: multiset.map_comp o_def)
    finally show "(\<Prod>\<sigma>\<in>perms. \<beta>' (f \<sigma>)) * exp (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)) =
                  (\<Prod>x\<in>#X. \<beta>' x) * exp (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>))" by simp
  qed
  also have "\<dots> = (\<Sum>X\<in>Roots_ms. \<Sum>f\<in>tuples X. (\<Prod>x\<in>#X. \<beta>' x) * exp (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>)))"
    unfolding tuples'_def by (intro sum.Sigma [symmetric]) auto
  also have "\<dots> = (\<Sum>X\<in>Roots_ms. of_int (\<Prod>x\<in>#X. \<beta>' x) * (\<Sum>f\<in>tuples X. exp (\<Sum>\<sigma>\<in>perms. \<sigma> (f \<sigma>))))"
    by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>X\<in>Roots_ms. of_int (\<Prod>x\<in>#X. \<beta>' x) * (\<Sum>x\<in>#R X. exp x))"
    by (simp only: R_def multiset.map_comp o_def sum_unfold_sum_mset)
  also have "\<dots> = (\<Sum>X\<in>Roots_ms. of_int (\<Prod>x\<in>#X. \<beta>' x) * (\<Sum>x\<in>#poly_roots (of_int_poly (Q X)). exp x))"
    by (intro sum.cong) (simp_all flip: Q)

  text \<open>
    Our problem now is that the polynomials \<open>Q X\<close> can still contain multiple roots and that their
    roots might not be disjoint. We therefore split them all into irreducible factors and collect
    equal terms.
  \<close>
  also have "\<dots> = (\<Sum>X\<in>Roots_ms. (\<Sum>p. of_int (int (count (prime_factorization (Q X)) p) *
                      (\<Prod>x\<in>#X. \<beta>' x)) * (\<Sum>x | ipoly p x = 0. exp x)))"
  proof (rule sum.cong, goal_cases)
    case (2 X)
    have "(\<Sum>x\<in>#poly_roots (of_int_poly (Q X) :: complex poly). exp x) =
          (\<Sum>x \<in># (\<Sum>p\<in>#prime_factorization (Q X). poly_roots (of_int_poly p)). exp x)"
      by (subst poly_roots_of_int_conv_sum_prime_factors) (rule refl)
    also have "\<dots> = (\<Sum>p\<in>#prime_factorization (Q X). \<Sum>x\<in>#poly_roots (of_int_poly p). exp x)"
      by (rule sum_mset_image_mset_sum_mset_image_mset)
    also have "rsquarefree (of_int_poly p :: complex poly)" if "p \<in> prime_factors (Q X)" for p
    proof (rule irreducible_imp_rsquarefree_of_int_poly)
      have "prime p"
        using that by auto
      thus "irreducible p"
        by blast
    next
      show "Polynomial.degree p > 0"
        by (intro content_1_imp_nonconstant_prime_factors[OF Q(2) that] 2)
    qed
    hence "(\<Sum>p\<in>#prime_factorization (Q X). \<Sum>x\<in>#poly_roots (of_int_poly p). exp x) =
           (\<Sum>p\<in>#prime_factorization (Q X). \<Sum>x | ipoly p x = 0. exp (x :: complex))"
      unfolding sum_unfold_sum_mset
      by (intro arg_cong[of _ _ sum_mset] image_mset_cong sum.cong refl,
          subst rsquarefree_poly_roots_eq) auto
    also have "\<dots> = (\<Sum>p. count (prime_factorization (Q X)) p * (\<Sum>x | ipoly p x = 0. exp (x :: complex)))"
      by (rule sum_mset_conv_Sum_any)
    also have "of_int (\<Prod>x\<in>#X. \<beta>' x) * \<dots> =
               (\<Sum>p. of_int (int (count (prime_factorization (Q X)) p) * (\<Prod>x\<in>#X. \<beta>' x)) * (\<Sum>x | ipoly p x = 0. exp x))"
      by (subst Sum_any_right_distrib) (auto simp: mult_ac)
    finally show ?case by simp
  qed auto
  also have "\<dots> = (\<Sum>q. of_int (\<beta>'' q) * (\<Sum>x | ipoly q x = 0. exp x))"
    unfolding \<beta>''_def of_int_sum
    by (subst Sum_any_sum_swap [symmetric]) (auto simp: sum_distrib_right)
  also have "\<dots> = (\<Sum>q | \<beta>'' q \<noteq> 0. of_int (\<beta>'' q) * (\<Sum>x | ipoly q x = 0. exp x))"
    by (intro Sum_any.expand_superset finite_subset[OF supp_\<beta>'']) auto
  finally have "(\<Sum>q | \<beta>'' q \<noteq> 0. of_int (\<beta>'' q) * (\<Sum>x | ipoly q x = 0. exp (x :: complex))) = 0"
    by simp

  text \<open>
    We are now in the situation of our the specialised Hermite--Lindemann Theorem we proved
    earlier and can easily derive a contradiction.
  \<close>
  moreover have "(\<Sum>q | \<beta>'' q \<noteq> 0. of_int (\<beta>'' q) * (\<Sum>x | ipoly q x = 0. exp (x :: complex))) \<noteq> 0"
  proof (rule Hermite_Lindemann_aux1)
    show "finite {q. \<beta>'' q \<noteq> 0}"
      by (rule finite_subset[OF supp_\<beta>'']) auto
  next
    show "pairwise Rings.coprime {q. \<beta>'' q \<noteq> 0}"
    proof (rule pairwiseI, clarify)
      fix p q assume pq: "p \<noteq> q" "\<beta>'' p \<noteq> 0" "\<beta>'' q \<noteq> 0"
      hence "prime p" "prime q"
        using supp_\<beta>'' Q(2) by auto
      with pq show "Rings.coprime p q"
        by (simp add: primes_coprime)
    qed
  next
    fix q :: "int poly"
    assume q: "q \<in> {q. \<beta>'' q \<noteq> 0}"
    also note supp_\<beta>''
    finally obtain X where X: "X \<in> Roots_ms" "q \<in> prime_factors (Q X)"
      by blast
    show "irreducible q"
      using X by (intro prime_elem_imp_irreducible prime_imp_prime_elem) auto
    show "Polynomial.degree q > 0" using X
      by (intro content_1_imp_nonconstant_prime_factors[OF Q(2)[of X]])
  qed (use \<open>{x. \<beta>'' x \<noteq> 0} \<noteq> {}\<close> in auto)

  ultimately show False by contradiction
qed


subsection \<open>Removing the restriction to integer coefficients\<close>

text \<open>
  Next, we weaken the restriction that the $\beta_i$ must be integers to the restriction
  that they must be rationals. This is done simply by multiplying with the least common multiple
  of the demoninators.
\<close>
lemma Hermite_Lindemann_aux3:
  fixes X :: "complex set" and \<beta> :: "complex \<Rightarrow> rat"
  assumes "finite X"
  assumes nz:   "\<And>x. x \<in> X \<Longrightarrow> \<beta> x \<noteq> 0"
  assumes alg:  "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes sum0: "(\<Sum>x\<in>X. of_rat (\<beta> x) * exp x) = 0"
  shows   "X = {}"
proof -
  define l :: int where "l = Lcm ((snd \<circ> quotient_of \<circ> \<beta>) ` X)"
  have [simp]: "snd (quotient_of r) \<noteq> 0" for r
    using quotient_of_denom_pos'[of r] by simp
  have [simp]: "l \<noteq> 0"
    using \<open>finite X\<close> by (auto simp: l_def Lcm_0_iff)

  have "of_int l * \<beta> x \<in> \<int>" if "x \<in> X" for x
  proof -
    define a b where "a = fst (quotient_of (\<beta> x))" and "b = snd (quotient_of (\<beta> x))"
    have "b > 0"
      using quotient_of_denom_pos'[of "\<beta> x"] by (auto simp: b_def)
    have "\<beta> x = of_int a / of_int b"
      by (intro quotient_of_div) (auto simp: a_def b_def)
    also have "of_int l * \<dots> = of_int (l * a) / of_int b"
      using \<open>b > 0\<close> by (simp add: field_simps)
    also have "\<dots> \<in> \<int>" using that
      by (intro of_int_divide_in_Ints) (auto simp: l_def b_def)
    finally show ?thesis .
  qed
  hence "\<forall>x\<in>X. \<exists>n. of_int n = of_int l * \<beta> x"
    using Ints_cases by metis
  then obtain \<beta>' where \<beta>': "of_int (\<beta>' x) = of_int l * \<beta> x" if "x \<in> X" for x
    by metis

  show ?thesis
  proof (rule Hermite_Lindemann_aux2)
    have "0 = of_int l * (\<Sum>x\<in>X. of_rat (\<beta> x) * exp x :: complex)"
      by (simp add: sum0)
    also have "\<dots> = (\<Sum>x\<in>X. of_int (\<beta>' x) * exp x)"
      unfolding sum_distrib_left
    proof (rule sum.cong, goal_cases)
      case (2 x)
      have "of_int l * of_rat (\<beta> x) = of_rat (of_int l * \<beta> x)"
        by (simp add: of_rat_mult)
      also have "of_int l * \<beta> x = of_int (\<beta>' x)"
        using 2 by (rule \<beta>' [symmetric])
      finally show ?case by (simp add: mult_ac)
    qed simp_all
    finally show "\<dots> = 0" ..
  next
    fix x assume "x \<in> X"
    hence "of_int (\<beta>' x) \<noteq> (0 :: rat)" using nz
      by (subst \<beta>') auto
    thus "\<beta>' x \<noteq> 0"
      by auto
  qed (use alg \<open>finite X\<close> in auto)
qed

text \<open>
  Next, we weaken the restriction that the $\beta_i$ must be rational to them being algebraic.
  Similarly to before, this is done by multiplying over all possible permutations of the $\beta_i$
  (in some sense) to introduce more symmetry, from which it then follows by the fundamental theorem
  of symmetric polynomials that the resulting coefficients are rational.
\<close>
lemma Hermite_Lindemann_aux4:
  fixes \<beta> :: "complex \<Rightarrow> complex"
  assumes [intro]: "finite X"
  assumes alg1: "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes alg2: "\<And>x. x \<in> X \<Longrightarrow> algebraic (\<beta> x)"
  assumes nz:   "\<And>x. x \<in> X \<Longrightarrow> \<beta> x \<noteq> 0"
  assumes sum0: "(\<Sum>x\<in>X. \<beta> x * exp x) = 0"
  shows   "X = {}"
proof (rule ccontr)
  assume X: "X \<noteq> {}"
  note [intro!] = finite_PiE

  text \<open>
    We now take more or less the same approach as before, except that now we find a polynomial
    that has all of the conjugates of the coefficients \<open>\<beta>\<close> as roots. Note that this is a slight
    deviation from Baker's proof, who picks one polynomial for each \<open>\<beta>\<close> independently. I did it
    this way because, as Bernard~\cite{bernard} observed, it makes the proof a bit easier.
  \<close>
  define P :: "int poly" where "P = \<Prod>((min_int_poly \<circ> \<beta>) ` X)"
  define Roots :: "complex set" where "Roots = {x. ipoly P x = 0}"
  have "0 \<notin> Roots" using \<open>finite X\<close> alg2 nz
    by (auto simp: Roots_def P_def poly_prod)
  have [simp]: "P \<noteq> 0"
    using \<open>finite X\<close> by (auto simp: P_def)
  have [intro]: "finite Roots"
    unfolding Roots_def by (intro poly_roots_finite) auto

  have "\<beta> ` X \<subseteq> Roots"
  proof safe
    fix x assume "x \<in> X"
    hence "ipoly (min_int_poly (\<beta> x)) (\<beta> x) = 0"
      by (intro ipoly_min_int_poly alg2)
    thus "\<beta> x \<in> Roots"
      using \<open>finite X\<close> \<open>x \<in> X\<close>
      by (auto simp: Roots_def P_def of_int_poly_hom.hom_prod poly_prod)
  qed

  have "squarefree (of_int_poly P :: complex poly)"
    unfolding P_def of_int_poly_hom.hom_prod o_def
  proof (rule squarefree_prod_coprime; safe)
    fix x assume "x \<in> X"
    thus "squarefree (of_int_poly (min_int_poly (\<beta> x)) :: complex poly)"
      by (intro squarefree_of_int_polyI) auto
  next
    fix x y assume xy: "x \<in> X" "y \<in> X" "min_int_poly (\<beta> x) \<noteq> min_int_poly (\<beta> y)"
    thus "Rings.coprime (of_int_poly (min_int_poly (\<beta> x)))
            (of_int_poly (min_int_poly (\<beta> y)) :: complex poly)"
      by (intro coprime_of_int_polyI[OF primes_coprime]) auto
  qed

  define n where "n = card Roots"
  define m where "m = card X"
  have "Roots \<noteq> {}"
    using \<open>\<beta> ` X \<subseteq> Roots\<close> \<open>X \<noteq> {}\<close> by auto
  hence "n > 0" "m > 0"
    using \<open>finite Roots\<close> \<open>finite X\<close> \<open>X \<noteq> {}\<close> by (auto simp: n_def m_def)
  have fin1 [simp]: "finite (X \<rightarrow>\<^sub>E Roots)"
    by auto
  have [simp]: "card (X \<rightarrow>\<^sub>E Roots) = n ^ m"
    by (subst card_PiE) (auto simp: m_def n_def)

  text \<open>
    We again find a bijection between the roots and the natural numbers less than \<open>n\<close>:
  \<close>
  obtain Root where Root: "bij_betw Root {..<n} Roots"
    using ex_bij_betw_nat_finite[OF \<open>finite Roots\<close>] unfolding n_def atLeast0LessThan by metis
  define unRoot :: "complex \<Rightarrow> nat" where "unRoot = inv_into {..<n} Root"
  have unRoot: "bij_betw unRoot Roots {..<n}"
    unfolding unRoot_def by (intro bij_betw_inv_into Root)
  have unRoot_Root [simp]: "unRoot (Root i) = i" if "i < n" for i
    unfolding unRoot_def using Root that by (subst inv_into_f_f) (auto simp: bij_betw_def)
  have Root_unRoot [simp]: "Root (unRoot x) = x" if "x \<in> Roots" for x
    unfolding unRoot_def using Root that by (subst f_inv_into_f) (auto simp: bij_betw_def)
  have [simp, intro]: "Root i \<in> Roots" if "i < n" for i
    using Root that by (auto simp: bij_betw_def)
  have [simp, intro]: "unRoot x < n" if "x \<in> Roots" for x
    using unRoot that by (auto simp: bij_betw_def)

  text \<open>
    And we again define the set of multisets and tuples that we will get in the expanded product.
  \<close>
  define Roots_ms :: "complex multiset set" where
    "Roots_ms = {Y. set_mset Y \<subseteq> X \<and> size Y = n ^ m}"
  have [intro]: "finite Roots_ms"
    unfolding Roots_ms_def by (rule finite_multisets_of_size) auto
  define tuples :: "complex multiset \<Rightarrow> ((complex \<Rightarrow> complex) \<Rightarrow> complex) set"
    where "tuples = (\<lambda>Y. {f\<in>(X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X. image_mset f (mset_set (X \<rightarrow>\<^sub>E Roots)) = Y})"
  have [intro]: "finite (tuples Y)" for Y
    unfolding tuples_def by (rule finite_subset[of _ "(X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X"]) auto

  text \<open>
    We will also need to convert permutations over the natural and over the roots again.
  \<close>
  define convert_perm :: "(nat \<Rightarrow> nat) \<Rightarrow> (complex \<Rightarrow> complex)" where
    "convert_perm = (\<lambda>\<sigma> x. if x \<in> Roots then Root (\<sigma> (unRoot x)) else x)"
  have bij_convert: "bij_betw convert_perm {\<sigma>. \<sigma> permutes {..<n}} {\<sigma>. \<sigma> permutes Roots}"
    using bij_betw_permutations[OF Root] unfolding convert_perm_def unRoot_def .
  have permutes_convert_perm [intro]: "convert_perm \<sigma> permutes Roots" if "\<sigma> permutes {..<n}" for \<sigma>
    using that bij_convert unfolding bij_betw_def by blast

  text \<open>
    We also need a small lemma showing that our tuples are stable under permutation of the roots.
  \<close>
  have bij_betw_compose_perm: 
    "bij_betw (\<lambda>f. restrict (\<lambda>g. f (restrict (\<pi> \<circ> g) X)) (X \<rightarrow>\<^sub>E Roots)) (tuples Y) (tuples Y)"
    if \<pi>: "\<pi> permutes Roots" and "Y \<in> Roots_ms" for \<pi> Y
  proof (rule bij_betwI)
    have *: "(\<lambda>f. restrict (\<lambda>g. f (restrict (\<pi> \<circ> g) X)) (X \<rightarrow>\<^sub>E Roots)) \<in> tuples Y \<rightarrow> tuples Y"
      if \<pi>: "\<pi> permutes Roots" for \<pi>
    proof
      fix f assume f: "f \<in> tuples Y"
      hence f': "f \<in> (X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X"
        by (auto simp: tuples_def)
      define f' where "f' = (\<lambda>g. f (restrict (\<pi> \<circ> g) X))"
      have "f' \<in> (X \<rightarrow>\<^sub>E Roots) \<rightarrow> X" unfolding f'_def
        using f' bij_betw_apply[OF bij_betw_compose_left_perm_PiE[OF \<pi>, of X]] by blast
      hence "restrict f' (X \<rightarrow>\<^sub>E Roots) \<in> (X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X"
        by simp
      moreover have "image_mset (restrict f' (X \<rightarrow>\<^sub>E Roots)) (mset_set (X \<rightarrow>\<^sub>E Roots)) = Y"
      proof -
        have "image_mset (restrict f' (X \<rightarrow>\<^sub>E Roots)) (mset_set (X \<rightarrow>\<^sub>E Roots)) =
              image_mset f' (mset_set (X \<rightarrow>\<^sub>E Roots))"
          by (intro image_mset_cong) auto
        also have "\<dots> = image_mset f (image_mset (\<lambda>g. restrict (\<pi> \<circ> g) X) (mset_set (X \<rightarrow>\<^sub>E Roots)))"
          unfolding f'_def o_def multiset.map_comp by (simp add: o_def)
        also have "image_mset (\<lambda>g. restrict (\<pi> \<circ> g) X) (mset_set (X \<rightarrow>\<^sub>E Roots)) =
                   mset_set (X \<rightarrow>\<^sub>E Roots)"
          by (intro bij_betw_image_mset_set bij_betw_compose_left_perm_PiE \<pi>)
        also have "image_mset f \<dots> = Y"
          using f by (simp add: tuples_def)
        finally show ?thesis .
      qed
      ultimately show "restrict f' (X \<rightarrow>\<^sub>E Roots) \<in> tuples Y"
        by (auto simp: tuples_def)
    qed
    show "(\<lambda>f. restrict (\<lambda>g. f (restrict (\<pi> \<circ> g) X)) (X \<rightarrow>\<^sub>E Roots)) \<in> tuples Y \<rightarrow> tuples Y"
      by (intro * \<pi>)
    show "(\<lambda>f. restrict (\<lambda>g. f (restrict (inv_into UNIV \<pi> \<circ> g) X)) (X \<rightarrow>\<^sub>E Roots)) \<in> tuples Y \<rightarrow> tuples Y"
      by (intro * permutes_inv \<pi>)
  next
    have *: "(\<lambda>g\<in>X \<rightarrow>\<^sub>E Roots. (\<lambda>g\<in>X \<rightarrow>\<^sub>E Roots. f (restrict (\<pi> \<circ> g) X))
                (restrict (inv_into UNIV \<pi> \<circ> g) X)) = f" (is "?lhs = _")
      if f: "f \<in> tuples Y" and \<pi>: "\<pi> permutes Roots" for f \<pi>
    proof
      fix g show "?lhs g = f g"
      proof (cases "g \<in> X \<rightarrow>\<^sub>E Roots")
        case True
        have "restrict (\<pi> \<circ> restrict (inv_into UNIV \<pi> \<circ> g) X) X = g"
          using True
          by (intro ext) (auto simp: permutes_inverses[OF \<pi>])
        thus ?thesis using True
          by (auto simp: permutes_in_image[OF permutes_inv[OF \<pi>]])
      qed (use f in \<open>auto simp: tuples_def\<close>)
    qed
    show "(\<lambda>g\<in>X \<rightarrow>\<^sub>E Roots. (\<lambda>g\<in>X \<rightarrow>\<^sub>E Roots. f (restrict (\<pi> \<circ> g) X))
                (restrict (inv_into UNIV \<pi> \<circ> g) X)) = f" if "f \<in> tuples Y" for f
      using *[OF that \<pi>] .
    show "(\<lambda>g\<in>X \<rightarrow>\<^sub>E Roots. (\<lambda>g\<in>X \<rightarrow>\<^sub>E Roots. f (restrict (inv_into UNIV \<pi> \<circ> g) X))
                (restrict (\<pi> \<circ> g) X)) = f" if "f \<in> tuples Y" for f
      using *[OF that permutes_inv[OF \<pi>]] permutes_inv_inv[OF \<pi>] by simp
  qed

  text \<open>
    We show that the coefficients in the expanded new sum are rational -- again using the 
    fundamental theorem of symmetric polynomials.
  \<close>
  define \<beta>' :: "complex multiset \<Rightarrow> complex"
    where "\<beta>' = (\<lambda>Y. \<Sum>f\<in>tuples Y. \<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. g (f g))"

  have "\<beta>' Y \<in> \<rat>" if Y: "Y \<in> Roots_ms" for Y
  proof -
    define Q :: "complex mpoly"
      where "Q = (\<Sum>f\<in>tuples Y. \<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Var (unRoot (g (f g))))"

    have "insertion Root Q \<in> \<rat>"
    proof (rule symmetric_poly_of_roots_in_subring)
      show "ring_closed (\<rat> :: complex set)"
        by standard auto
      then interpret ring_closed "\<rat> :: complex set" .
      show "\<forall>m. coeff Q m \<in> \<rat>"
        by (auto simp: Q_def coeff_Var when_def intro!: sum_in_Rats coeff_prod_closed)
    next
      show "symmetric_mpoly {..<n} Q"
        unfolding symmetric_mpoly_def
      proof safe
        fix \<pi> assume \<pi>: "\<pi> permutes {..<n}"
        define \<pi>' where "\<pi>' = convert_perm (inv_into UNIV \<pi>)"
        have \<pi>': "\<pi>' permutes Roots"
          unfolding \<pi>'_def by (intro permutes_convert_perm permutes_inv \<pi>)
        have "mpoly_map_vars \<pi> Q = (\<Sum>f\<in>tuples Y. \<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Var (\<pi> (unRoot (g (f g)))))"
          unfolding Q_def by (simp add: permutes_bij[OF \<pi>])
        also have "\<dots> = (\<Sum>f\<in>tuples Y. \<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Var (unRoot (g (f (restrict (\<pi>' \<circ> g) X)))))"
        proof (rule sum.cong, goal_cases)
          case (2 f)
          have f: "f \<in> (X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X"
            using 2 by (auto simp: tuples_def)
          have "(\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Var (\<pi> (unRoot (g (f g))))) =
                (\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Var (\<pi> (unRoot (restrict (\<pi>' \<circ> g) X (f (restrict (\<pi>' \<circ> g) X))))))"
            using \<pi>' by (intro prod.reindex_bij_betw [symmetric] bij_betw_compose_left_perm_PiE)
          also have "\<dots> = (\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Var (unRoot (g (f (restrict (\<pi>' \<circ> g) X)))))"
          proof (intro prod.cong refl arg_cong[of _ _ Var])
            fix g assume g: "g \<in> X \<rightarrow>\<^sub>E Roots"
            have "restrict (\<pi>' \<circ> g) X \<in> X \<rightarrow>\<^sub>E Roots"
              using bij_betw_compose_left_perm_PiE[OF \<pi>', of X] g unfolding bij_betw_def by blast
            hence *: "f (restrict (\<pi>' \<circ> g) X) \<in> X"
              by (rule PiE_mem[OF f])
            hence **: "g (f (restrict (\<pi>' \<circ> g) X)) \<in> Roots"
              by (rule PiE_mem[OF g])

            have "unRoot (restrict (\<pi>' \<circ> g) X (f (restrict (\<pi>' \<circ> g) X))) =
                   unRoot (Root (inv_into UNIV \<pi> (unRoot (g (f (restrict (\<pi>' \<circ> g) X))))))"
              using * ** by (subst \<pi>'_def) (auto simp: convert_perm_def)
            also have "inv_into UNIV \<pi> (unRoot (g (f (restrict (\<pi>' \<circ> g) X)))) \<in> {..<n}"
              using ** by (subst permutes_in_image[OF permutes_inv[OF \<pi>]]) auto
            hence "unRoot (Root (inv_into UNIV \<pi> (unRoot (g (f (restrict (\<pi>' \<circ> g) X)))))) =
                   inv_into UNIV \<pi> (unRoot (g (f (restrict (\<pi>' \<circ> g) X))))"
              by (intro unRoot_Root) auto
            also have "\<pi> \<dots> = unRoot (g (f (restrict (\<pi>' \<circ> g) X)))"
              by (rule permutes_inverses[OF \<pi>])
            finally show "\<pi> (unRoot (restrict (\<pi>' \<circ> g) X (f (restrict (\<pi>' \<circ> g) X)))) =
                          unRoot (g (f (restrict (\<pi>' \<circ> g) X)))" .
          qed
          finally show ?case .
        qed simp_all
        also have "\<dots> = (\<Sum>x\<in>tuples Y. \<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Var (unRoot (g ((\<lambda>g\<in>X \<rightarrow>\<^sub>E Roots. x (restrict (\<pi>' \<circ> g) X)) g))))"
          by (intro sum.cong prod.cong refl) auto
        also have "\<dots> = Q"
          unfolding Q_def
          by (rule sum.reindex_bij_betw[OF bij_betw_compose_perm]) (use \<pi>' Y in simp_all)
        finally show "mpoly_map_vars \<pi> Q = Q" .
      qed
    next
      show "vars Q \<subseteq> {..<n}"
        unfolding Q_def
        by (intro order.trans[OF vars_sum] UN_least order.trans[OF vars_prod])
           (auto simp: vars_Var tuples_def)
    next
      define lc where "lc = Polynomial.lead_coeff P"
      have "lc \<noteq> 0"
        unfolding lc_def by auto
      thus "inverse (of_int lc) * (of_int lc :: complex) = 1" and "inverse (of_int lc) \<in> \<rat>"
        by auto
      have "rsquarefree (of_int_poly P :: complex poly)"
        using \<open>squarefree (of_int_poly P :: complex poly)\<close> by (intro squarefree_imp_rsquarefree)
      hence "of_int_poly P = Polynomial.smult (of_int lc) (\<Prod>x\<in>Roots. [:-x, 1:])"
        unfolding lc_def of_int_hom.hom_lead_coeff[symmetric] Roots_def
        by (rule complex_poly_decompose_rsquarefree [symmetric])
      also have "(\<Prod>x\<in>Roots. [:-x, 1:]) = (\<Prod>i<n. [:-Root i, 1:])"
        by (rule prod.reindex_bij_betw[OF Root, symmetric])
      finally show "of_int_poly P = Polynomial.smult (of_int lc) (\<Prod>i<n. [:- Root i, 1:])" .
    qed auto
    also have "insertion Root Q = (\<Sum>f\<in>tuples Y. \<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. Root (unRoot (g (f g))))"
      by (simp add: Q_def insertion_sum insertion_prod)
    also have "\<dots> = \<beta>' Y"
      unfolding \<beta>'_def by (intro sum.cong prod.cong refl Root_unRoot) (auto simp: tuples_def)
    finally show ?thesis .
  qed
  hence "\<forall>Y\<in>Roots_ms. \<exists>x. \<beta>' Y = of_rat x"
    by (auto elim!: Rats_cases)
  then obtain \<beta>'' :: "complex multiset \<Rightarrow> rat"
    where \<beta>'': "\<And>Y. Y \<in> Roots_ms \<Longrightarrow> \<beta>' Y = of_rat (\<beta>'' Y)"
    by metis

  text \<open>
    We again collect all the terms that happen to have equal exponents and call their
    coefficients \<open>\<beta>''\<close>:
  \<close>
  define \<beta>''' :: "complex \<Rightarrow> rat" where "\<beta>''' = (\<lambda>\<alpha>. \<Sum>Y\<in>Roots_ms. (\<beta>'' Y when \<Sum>\<^sub>#Y = \<alpha>))"
  have supp_\<beta>''': "{x. \<beta>''' x \<noteq> 0} \<subseteq> sum_mset ` Roots_ms"
    by (auto simp: \<beta>'''_def when_def elim!: sum.not_neutral_contains_not_neutral split: if_splits)

  text \<open>
    We again start with the sum that we now to be zero and multiply it with all the sums that can
    be obtained with different choices for the roots.
  \<close>
  have "0 = (\<Sum>x\<in>X. \<beta> x * exp x)"
    using sum0 ..
  also have "\<dots> = (\<Sum>x\<in>X. restrict \<beta> X x * exp x)"
    by (intro sum.cong) auto
  also have "\<dots> dvd (\<Prod>f \<in> X \<rightarrow>\<^sub>E Roots. \<Sum>x\<in>X. f x * exp x)"
    by (rule dvd_prodI) (use \<open>\<beta> ` X \<subseteq> Roots\<close> in \<open>auto simp: id_def\<close>)
  also have "\<dots> = (\<Sum>f\<in>(X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X. \<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. g (f g) * exp (f g))"
    by (rule prod_sum_PiE) auto
  also have "\<dots> = (\<Sum>f\<in>(X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X. (\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. g (f g)) * exp (\<Sum>g\<in>X \<rightarrow>\<^sub>E Roots. f g))"
    by (simp add: prod.distrib exp_sum)
  also have "\<dots> = (\<Sum>(Y,f)\<in>Sigma Roots_ms tuples.
                    (\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. g (f g)) * exp (\<Sum>g\<in>X \<rightarrow>\<^sub>E Roots. f g))"
    by (intro sum.reindex_bij_witness[of _ snd "\<lambda>f. (image_mset f (mset_set (X \<rightarrow>\<^sub>E Roots)), f)"])
       (auto simp: Roots_ms_def tuples_def)
  also have "\<dots> = (\<Sum>(Y,f)\<in>Sigma Roots_ms tuples. (\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. g (f g)) * exp (\<Sum>\<^sub>#Y))"
    by (intro sum.cong) (auto simp: tuples_def sum_unfold_sum_mset)
  also have "\<dots> = (\<Sum>Y\<in>Roots_ms. \<beta>' Y * exp (\<Sum>\<^sub>#Y))"
    unfolding \<beta>'_def sum_distrib_right by (rule sum.Sigma [symmetric]) auto
  also have "\<dots> = (\<Sum>Y\<in>Roots_ms. of_rat (\<beta>'' Y) * exp (\<Sum>\<^sub>#Y))"
    by (intro sum.cong) (auto simp: \<beta>'')
  also have "\<dots> = (\<Sum>Y\<in>Roots_ms. Sum_any (\<lambda>\<alpha>. of_rat (\<beta>'' Y when \<Sum>\<^sub># Y = \<alpha>) * exp \<alpha>))"
  proof (rule sum.cong, goal_cases)
    case (2 Y)
    have "Sum_any (\<lambda>\<alpha>. of_rat (\<beta>'' Y when \<Sum>\<^sub># Y = \<alpha>) * exp \<alpha>) =
          (\<Sum>\<alpha>\<in>{\<Sum>\<^sub># Y}. of_rat (\<beta>'' Y when \<Sum>\<^sub># Y = \<alpha>) * exp \<alpha>)"
      by (intro Sum_any.expand_superset) auto
    thus ?case by simp
  qed auto
  also have "\<dots> = Sum_any (\<lambda>\<alpha>. of_rat (\<beta>''' \<alpha>) * exp \<alpha>)"
    unfolding \<beta>'''_def of_rat_sum sum_distrib_right by (subst Sum_any_sum_swap) auto
  also have "\<dots> = (\<Sum>\<alpha> | \<beta>''' \<alpha> \<noteq> 0. of_rat (\<beta>''' \<alpha>) * exp \<alpha>)"
    by (intro Sum_any.expand_superset finite_subset[OF supp_\<beta>''']) auto
  finally have "(\<Sum>\<alpha> | \<beta>''' \<alpha> \<noteq> 0. of_rat (\<beta>''' \<alpha>) * exp \<alpha>) = 0"
    by auto

  text \<open>
    We are now in the situation of our previous version of the theorem and can apply it to find
    that all the coefficients are zero.
  \<close>
  have "{\<alpha>. \<beta>''' \<alpha> \<noteq> 0} = {}"
  proof (rule Hermite_Lindemann_aux3)
    show "finite {\<alpha>. \<beta>''' \<alpha> \<noteq> 0}"
      by (rule finite_subset[OF supp_\<beta>''']) auto
  next
    show "(\<Sum>\<alpha> | \<beta>''' \<alpha> \<noteq> 0. of_rat (\<beta>''' \<alpha>) * exp \<alpha>) = 0"
    by fact
  next
    fix \<alpha> assume \<alpha>: "\<alpha> \<in> {\<alpha>. \<beta>''' \<alpha> \<noteq> 0}"
    then obtain Y where Y: "Y \<in> Roots_ms" "\<alpha> = sum_mset Y"
      using supp_\<beta>''' by auto
    thus "algebraic \<alpha>" using alg1
      by (auto simp: Roots_ms_def)
  qed auto

  text \<open>
    However, similarly to before, we can show that the coefficient corresponding to the
    term with the lexicographically greatest exponent (which is obtained by picking the
    term with the lexicographically greatest term in each of the factors of our big product)
    is non-zero.
  \<close>
  moreover have "\<exists>\<alpha>. \<beta>''' \<alpha> \<noteq> 0"
  proof -
    define \<alpha>_max where "\<alpha>_max = complex_lex.Max X"
    have [simp]: "\<alpha>_max \<in> X"
      unfolding \<alpha>_max_def using \<open>X \<noteq> {}\<close> by (intro complex_lex.Max_in) auto
    define Y_max :: "complex multiset" where "Y_max = replicate_mset (n ^ m) \<alpha>_max"
    define f_max where "f_max = restrict (\<lambda>_. \<alpha>_max) (X \<rightarrow>\<^sub>E Roots)"
    have [simp]: "Y_max \<in> Roots_ms"
      by (auto simp: Y_max_def Roots_ms_def)
    have "tuples Y_max = {f_max}"
    proof safe
      have "image_mset (\<lambda>_\<in>X \<rightarrow>\<^sub>E Roots. \<alpha>_max) (mset_set (X \<rightarrow>\<^sub>E Roots)) =
            image_mset (\<lambda>_. \<alpha>_max) (mset_set (X \<rightarrow>\<^sub>E Roots))"
        by (intro image_mset_cong) auto
      thus "f_max \<in> tuples Y_max"
        by (auto simp: f_max_def tuples_def Y_max_def image_mset_const_eq)
    next
      fix f assume "f \<in> tuples Y_max"
      hence f: "f \<in> (X \<rightarrow>\<^sub>E Roots) \<rightarrow>\<^sub>E X" "image_mset f (mset_set (X \<rightarrow>\<^sub>E Roots)) = Y_max"
        by (auto simp: tuples_def)
      hence "\<forall>g \<in># mset_set (X \<rightarrow>\<^sub>E Roots). f g = \<alpha>_max"
        by (intro image_mset_eq_replicate_msetD[where n = "n ^ m"]) (auto simp: Y_max_def)
      thus "f = f_max"
        using f by (auto simp: Y_max_def fun_eq_iff f_max_def)
    qed

    have "\<beta>''' (of_nat (n ^ m) * \<alpha>_max) = (\<Sum>Y\<in>Roots_ms. \<beta>'' Y when \<Sum>\<^sub># Y = of_nat (n ^ m) * \<alpha>_max)"
      unfolding \<beta>'''_def Roots_ms_def ..
    also have "\<Sum>\<^sub># Y \<noteq> of_nat n ^ m * \<alpha>_max" if "Y \<in> Roots_ms" "Y \<noteq> Y_max" for Y
    proof -
      have "\<not>set_mset Y \<subseteq> {\<alpha>_max}"
        using set_mset_subset_singletonD[of Y "\<alpha>_max"] that
        by (auto simp: Roots_ms_def Y_max_def split: if_splits)
      then obtain y where y: "y \<in># Y" "y \<noteq> \<alpha>_max"
        by auto
      have "y \<in> X" "set_mset (Y - {#y#}) \<subseteq> X"
        using y that by (auto simp: Roots_ms_def dest: in_diffD)
      hence "y \<le>\<^sub>\<complex> \<alpha>_max"
        using y unfolding \<alpha>_max_def by (intro complex_lex.Max_ge) auto
      with y have "y <\<^sub>\<complex> \<alpha>_max"
        by auto
      have *: "Y = {#y#} + (Y - {#y#})"
        using y by simp
      have "sum_mset Y = y + sum_mset (Y - {#y#})"
        by (subst *) auto
      also have "\<dots> <\<^sub>\<complex> \<alpha>_max + sum_mset (Y - {#y#})"
        by (intro complex_lex.add_strict_right_mono) fact
      also have "\<dots> \<le>\<^sub>\<complex> \<alpha>_max + sum_mset (replicate_mset (n ^ m - 1) \<alpha>_max)"
        unfolding \<alpha>_max_def using that y \<open>set_mset (Y - {#y#}) \<subseteq> X\<close>
        by (intro complex_lex.add_left_mono sum_mset_mono_complex_lex
                  rel_mset_replicate_mset_right complex_lex.Max_ge)
           (auto simp: Roots_ms_def size_Diff_singleton)
      also have "\<dots> = of_nat (Suc (n ^ m - 1)) * \<alpha>_max"
        by (simp add: algebra_simps)
      also have "Suc (n ^ m - 1) = n ^ m"
        using \<open>n > 0\<close> by simp
      finally show ?thesis by simp
    qed
    hence "(\<Sum>Y\<in>Roots_ms. \<beta>'' Y when \<Sum>\<^sub># Y = of_nat (n ^ m) * \<alpha>_max) = (\<Sum>Y\<in>{Y_max}. \<beta>'' Y when \<Sum>\<^sub># Y = of_nat (n ^ m) * \<alpha>_max)"
      by (intro sum.mono_neutral_right ballI) auto
    also have "\<dots> = \<beta>'' Y_max"
      by (auto simp: when_def Y_max_def)
    also have "of_rat \<dots> = \<beta>' Y_max"
      using \<beta>''[of Y_max] by auto
    also have "\<dots> = (\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. g (f_max g))"
      by (auto simp: \<beta>'_def \<open>tuples Y_max = {f_max}\<close>)
    also have "\<dots> = (\<Prod>g\<in>X \<rightarrow>\<^sub>E Roots. g \<alpha>_max)"
      by (intro prod.cong) (auto simp: f_max_def)
    also have "\<dots> \<noteq> 0"
      using \<open>0 \<notin> Roots\<close> \<open>\<alpha>_max \<in> X\<close> by (intro prod_nonzeroI) (metis PiE_mem)
    finally show ?thesis by blast
  qed

  ultimately show False by blast
qed


subsection \<open>The final theorem\<close>

text \<open>
  We now additionally allow some of the $\beta_i$ to be zero:
\<close>
lemma Hermite_Lindemann':
  fixes \<beta> :: "complex \<Rightarrow> complex"
  assumes "finite X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes "\<And>x. x \<in> X \<Longrightarrow> algebraic (\<beta> x)"
  assumes "(\<Sum>x\<in>X. \<beta> x * exp x) = 0"
  shows   "\<forall>x\<in>X. \<beta> x = 0"
proof -
  have "{x\<in>X. \<beta> x \<noteq> 0} = {}"
  proof (rule Hermite_Lindemann_aux4)
    have "(\<Sum>x | x \<in> X \<and> \<beta> x \<noteq> 0. \<beta> x * exp x) = (\<Sum>x\<in>X. \<beta> x * exp x)"
      by (intro sum.mono_neutral_left assms(1)) auto
    also have "\<dots> = 0"
      by fact
    finally show "(\<Sum>x | x \<in> X \<and> \<beta> x \<noteq> 0. \<beta> x * exp x) = 0" .
  qed (use assms in auto)
  thus ?thesis by blast
qed

text \<open>
  Lastly, we switch to indexed summation in order to obtain a version of the theorem that
  is somewhat nicer to use:
\<close>
theorem Hermite_Lindemann:
  fixes \<alpha> \<beta> :: "'a \<Rightarrow> complex"
  assumes "finite I"
  assumes "\<And>x. x \<in> I \<Longrightarrow> algebraic (\<alpha> x)"
  assumes "\<And>x. x \<in> I \<Longrightarrow> algebraic (\<beta> x)"
  assumes "inj_on \<alpha> I"
  assumes "(\<Sum>x\<in>I. \<beta> x * exp (\<alpha> x)) = 0"
  shows   "\<forall>x\<in>I. \<beta> x = 0"
proof -
  define f where "f = inv_into I \<alpha>"
  have [simp]: "f (\<alpha> x) = x" if "x \<in> I" for x
    using that by (auto simp: f_def inv_into_f_f[OF assms(4)])
  have "\<forall>x\<in>\<alpha>`I. (\<beta> \<circ> f) x = 0"
  proof (rule Hermite_Lindemann')
    have "0 = (\<Sum>x\<in>I. \<beta> x * exp (\<alpha> x))"
      using assms(5) ..
    also have "\<dots> = (\<Sum>x\<in>I. (\<beta> \<circ> f) (\<alpha> x) * exp (\<alpha> x))"
      by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>x\<in>\<alpha>`I. (\<beta> \<circ> f) x * exp x)"
      using assms(4) by (subst sum.reindex) auto
    finally show "(\<Sum>x\<in>\<alpha> ` I. (\<beta> \<circ> f) x * exp x) = 0" ..
  qed (use assms in auto)
  thus ?thesis by auto
qed

text \<open>
  The following version using lists instead of sequences is even more convenient to use
  in practice:
\<close>
corollary Hermite_Lindemann_list:
  fixes xs :: "(complex \<times> complex) list"
  assumes alg:      "\<forall>(x,y)\<in>set xs. algebraic x \<and> algebraic y"
  assumes distinct: "distinct (map snd xs)"
  assumes sum0:     "(\<Sum>(c,\<alpha>)\<leftarrow>xs. c * exp \<alpha>) = 0"
  shows   "\<forall>c\<in>(fst ` set xs). c = 0"
proof -
  define n where "n = length xs"
  have *: "\<forall>i\<in>{..<n}. fst (xs ! i) = 0"
  proof (rule Hermite_Lindemann)
    from distinct have "inj_on (\<lambda>i. map snd xs ! i) {..<n}"
      by (intro inj_on_nth) (auto simp: n_def)
    also have "?this \<longleftrightarrow> inj_on (\<lambda>i. snd (xs ! i)) {..<n}"
      by (intro inj_on_cong) (auto simp: n_def)
    finally show "inj_on (\<lambda>i. snd (xs ! i)) {..<n}" .
  next
    have "0 = (\<Sum>(c,\<alpha>)\<leftarrow>xs. c * exp \<alpha>)"
      using sum0 ..
    also have "\<dots> = (\<Sum>i<n. fst (xs ! i) * exp (snd (xs ! i)))"
      unfolding sum_list_sum_nth
      by (intro sum.cong) (auto simp: n_def case_prod_unfold)
    finally show "\<dots> = 0" ..
  next
    fix i assume i: "i \<in> {..<n}"
    hence "(fst (xs ! i), snd (xs ! i)) \<in> set xs"
      by (auto simp: n_def)
    with alg show "algebraic (fst (xs ! i))" "algebraic (snd (xs ! i))"
      by blast+
  qed auto

  show ?thesis
  proof (intro ballI, elim imageE)
    fix c x assume cx: "c = fst x" "x \<in> set xs"
    then obtain i where "i \<in> {..<n}" "x = xs ! i"
      by (auto simp: set_conv_nth n_def)
    with * cx show "c = 0" by blast
  qed
qed


subsection \<open>The traditional formulation of the theorem\<close>

text \<open>
  What we proved above was actually Baker's reformulation of the theorem. Thus, we now also derive
  the original one, which uses linear independence and algebraic independence.

  It states that if $\alpha_1, \ldots, \alpha_n$ are algebraic numbers that are linearly
  independent over \<open>\<int>\<close>, then $e^{\alpha_1}, \ldots, e^{\alpha_n}$ are algebraically independent
  over \<open>\<rat>\<close>.
\<close>

text \<open>
  Linear independence over the integers is just independence of a set of complex numbers when
  viewing the complex numbers as a \<open>\<int>\<close>-module.
\<close>
definition linearly_independent_over_int :: "'a :: field_char_0 set \<Rightarrow> bool" where
  "linearly_independent_over_int = module.independent (\<lambda>r x. of_int r * x)"

text \<open>
  Algebraic independence over the rationals means that the given set \<open>X\<close> of numbers fulfils
  no non-trivial polynomial equation with rational coefficients, i.e. there is no non-zero
  multivariate polynomial with rational coefficients that, when inserting the numbers from \<open>X\<close>,
  becomes zero.

  Note that we could easily replace `rational coefficients' with `algebraic coefficients' here
  and the proof would still go through without any modifications.
\<close>
definition algebraically_independent_over_rat :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: field_char_0) \<Rightarrow> bool" where
  "algebraically_independent_over_rat n a \<longleftrightarrow>
     (\<forall>p. vars p \<subseteq> {..<n} \<and> (\<forall>m. coeff p m \<in> \<rat>) \<and> insertion a p = 0 \<longrightarrow> p = 0)"

corollary Hermite_Lindemann_original:
  fixes n :: nat and \<alpha> :: "nat \<Rightarrow> complex"
  assumes "inj_on \<alpha> {..<n}"
  assumes "\<And>i. i < n \<Longrightarrow> algebraic (\<alpha> i)"
  assumes "linearly_independent_over_int (\<alpha> ` {..<n})"
  shows   "algebraically_independent_over_rat n (\<lambda>i. exp (\<alpha> i))"
  unfolding algebraically_independent_over_rat_def
proof safe
  fix p assume p: "vars p \<subseteq> {..<n}" "\<forall>m. coeff p m \<in> \<rat>" "insertion (\<lambda>i. exp (\<alpha> i)) p = 0"
  define \<alpha>' where "\<alpha>' = (\<lambda>m. \<Sum>i<n. of_nat (lookup m i) * \<alpha> i)"
  define I where "I = {m. coeff p m \<noteq> 0}"

  have lookup_eq_0: "lookup m i = 0" if "m \<in> I" "i \<notin> {..<n}" for i m
  proof -
    have "keys m \<subseteq> vars p"
      using that coeff_notin_vars[of m p] by (auto simp: I_def)
    thus "lookup m i = 0"
      using in_keys_iff[of i m] that p(1) by blast
  qed

  have "\<forall>x\<in>I. coeff p x = 0"
  proof (rule Hermite_Lindemann)
    show "finite I"
      by (auto simp: I_def)
  next
    show "algebraic (\<alpha>' m)" if "m \<in> I" for m
      unfolding \<alpha>'_def using assms(2) by fastforce
  next
    show "algebraic (coeff p m)" if "m \<in> I" for m
      unfolding \<alpha>'_def using p(2) by blast
  next
    show "inj_on \<alpha>' I"
    proof
      fix m1 m2 assume m12: "m1 \<in> I" "m2 \<in> I" "\<alpha>' m1 = \<alpha>' m2"
      define lu :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat \<Rightarrow> int" where "lu = (\<lambda>m i. int (lookup m i))"
      interpret int: Modules.module "\<lambda>r x. of_int r * (x :: complex)"
        by standard (auto simp: algebra_simps of_rat_mult of_rat_add)
      define idx where "idx = inv_into {..<n} \<alpha>"

      have "lu m1 i = lu m2 i" if "i < n" for i
      proof -
        have "lu m1 (idx (\<alpha> i)) - lu m2 (idx (\<alpha> i)) = 0"
        proof (rule int.independentD)
          show "int.independent (\<alpha> ` {..<n})"
            using assms(3) by (simp add: linearly_independent_over_int_def)
        next
          have "(\<Sum>x\<in>\<alpha>`{..<n}. of_int (lu m1 (idx x) - lu m2 (idx x)) * x) =
                (\<Sum>i<n. of_int (lu m1 (idx (\<alpha> i)) - lu m2 (idx (\<alpha> i))) * \<alpha> i)"
            using assms(1) by (subst sum.reindex) auto
          also have "\<dots> = (\<Sum>i<n. of_int (lu m1 i - lu m2 i) * \<alpha> i)"
            by (intro sum.cong) (auto simp: idx_def inv_into_f_f[OF assms(1)])
          also have "\<dots> = 0"
            using m12 by (simp add: \<alpha>'_def ring_distribs of_rat_diff sum_subtractf lu_def)
          finally show "(\<Sum>x\<in>\<alpha>`{..<n}. of_int (lu m1 (idx x) - lu m2 (idx x)) * x) = 0"
            by (simp add: \<alpha>'_def ring_distribs of_rat_diff sum_subtractf lu_def)
        qed (use that in auto)
        thus ?thesis
          using that by (auto simp: idx_def inv_into_f_f[OF assms(1)])
      qed
      hence "lookup m1 i = lookup m2 i" for i
        using m12 by (cases "i < n") (auto simp: lu_def lookup_eq_0)
      thus "m1 = m2"
        by (rule poly_mapping_eqI)
    qed
  next
    have "0 = insertion (\<lambda>i. exp (\<alpha> i)) p"
      using p(3) ..
    also have "\<dots> = (\<Sum>m\<in>I. coeff p m * Prod_any (\<lambda>i. exp (\<alpha> i) ^ lookup m i))"
      unfolding insertion_altdef by (rule Sum_any.expand_superset) (auto simp: I_def)
    also have "\<dots> = (\<Sum>m\<in>I. coeff p m * exp (\<alpha>' m))"
    proof (intro sum.cong, goal_cases)
      case (2 m)
      have "Prod_any (\<lambda>i. exp (\<alpha> i) ^ lookup m i) = (\<Prod>i<n. exp (\<alpha> i) ^ lookup m i)"
        using 2 lookup_eq_0[of m] by (intro Prod_any.expand_superset; force)
      also have "\<dots> = exp (\<alpha>' m)"
        by (simp add: exp_sum exp_of_nat_mult \<alpha>'_def)
      finally show ?case by simp
    qed simp_all
    finally show "(\<Sum>m\<in>I. coeff p m * exp (\<alpha>' m)) = 0" ..
  qed
  thus "p = 0"
    by (intro mpoly_eqI) (auto simp: I_def)
qed


subsection \<open>Simple corollaries\<close>

text \<open>
  Now, we derive all the usual obvious corollaries of the theorem in the obvious way.

  First, the exponential of a non-zero algebraic number is transcendental.
\<close>
corollary algebraic_exp_complex_iff:
  assumes "algebraic x"
  shows   "algebraic (exp x :: complex) \<longleftrightarrow> x = 0"
  using Hermite_Lindemann_list[of "[(1, x), (-exp x, 0)]"] assms by auto

text \<open>
  More generally, any sum of exponentials with algebraic coefficients and exponents is
  transcendental if the exponents are all distinct and non-zero and at least one coefficient
  is non-zero.
\<close>
corollary sum_of_exp_transcendentalI:
  fixes xs :: "(complex \<times> complex) list"
  assumes "\<forall>(x,y)\<in>set xs. algebraic x \<and> algebraic y \<and> y \<noteq> 0"
  assumes "\<exists>x\<in>fst`set xs. x \<noteq> 0"
  assumes distinct: "distinct (map snd xs)"
  shows   "\<not>algebraic (\<Sum>(c,\<alpha>)\<leftarrow>xs. c * exp \<alpha>)"
proof
  define S where "S = (\<Sum>(c,\<alpha>)\<leftarrow>xs. c * exp \<alpha>)"
  assume S: "algebraic S"
  have "\<forall>c\<in>fst`set ((-S,0) # xs). c = 0"
  proof (rule Hermite_Lindemann_list)
    show "(\<Sum>(c, \<alpha>)\<leftarrow>(- S, 0) # xs. c * exp \<alpha>) = 0"
      by (auto simp: S_def)
  qed (use S assms in auto)
  with assms(2) show False
    by auto
qed

text \<open>
  Any complex logarithm of an algebraic number other than 1 is transcendental
  (no matter which branch cut).
\<close>
corollary transcendental_complex_logarithm:
  assumes "algebraic x" "exp y = (x :: complex)" "x \<noteq> 1"
  shows   "\<not>algebraic y"
  using algebraic_exp_complex_iff[of y] assms by auto

text \<open>
  In particular, this holds for the standard branch of the logarithm.
\<close>
corollary transcendental_Ln:
  assumes "algebraic x" "x \<noteq> 0" "x \<noteq> 1"
  shows   "\<not>algebraic (Ln x)"
  by (rule transcendental_complex_logarithm) (use assms in auto)

text \<open>
  The transcendence of \<open>e\<close> and \<open>\<pi>\<close>, which I have already formalised directly in other AFP
  entries, now follows as a simple corollary.
\<close>
corollary exp_1_complex_transcendental: "\<not>algebraic (exp 1 :: complex)"
  by (subst algebraic_exp_complex_iff) auto

corollary pi_transcendental: "\<not>algebraic pi"
proof -
  have "\<not>algebraic (\<i> * pi)"
    by (rule transcendental_complex_logarithm[of "-1"]) auto
  thus ?thesis by simp
qed


subsection \<open>Transcendence of the trigonometric and hyperbolic functions\<close>

text \<open>
  In a similar fashion, we can also prove the transcendence of all the trigonometric and
  hyperbolic functions such as $\sin$, $\tan$, $\sinh$, $\arcsin$, etc.
\<close>

lemma transcendental_sinh:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (sinh z :: complex)"
proof -
  have "\<not>algebraic (\<Sum>(a,b)\<leftarrow>[(1/2, z), (-1/2, -z)]. a * exp b)"
    using assms by (intro sum_of_exp_transcendentalI) auto
  also have "(\<Sum>(a,b)\<leftarrow>[(1/2, z), (-1/2, -z)]. a * exp b) = sinh z"
    by (simp add: sinh_def field_simps scaleR_conv_of_real)
  finally show ?thesis .
qed

lemma transcendental_cosh:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (cosh z :: complex)"
proof -
  have "\<not>algebraic (\<Sum>(a,b)\<leftarrow>[(1/2, z), (1/2, -z)]. a * exp b)"
    using assms by (intro sum_of_exp_transcendentalI) auto
  also have "(\<Sum>(a,b)\<leftarrow>[(1/2, z), (1/2, -z)]. a * exp b) = cosh z"
    by (simp add: cosh_def field_simps scaleR_conv_of_real)
  finally show ?thesis .
qed

lemma transcendental_sin:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (sin z :: complex)"
  unfolding sin_conv_sinh using transcendental_sinh[of "\<i> * z"] assms by simp

lemma transcendental_cos:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (cos z :: complex)"
  unfolding cos_conv_cosh using transcendental_cosh[of "\<i> * z"] assms by simp

(* TODO: Move? *)
lemma tan_square_neq_neg1: "tan (z :: complex) ^ 2 \<noteq> -1"
proof
  assume "tan z ^ 2 = -1"
  hence "sin z ^ 2 = -(cos z ^ 2)"
    by (auto simp: tan_def divide_simps split: if_splits)
  also have "cos z ^ 2 = 1 - sin z ^ 2"
    by (simp add: cos_squared_eq)
  finally show False
    by simp
qed

lemma transcendental_tan:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (tan z :: complex)"
proof
  assume "algebraic (tan z)"

  have nz1: "real_of_int n + 1 / 2 \<noteq> 0" for n
  proof -
    have "real_of_int (2 * n + 1) / real_of_int 2 \<notin> \<int>"
      by (intro fraction_not_in_ints) auto
    also have "real_of_int (2 * n + 1) / real_of_int 2 = real_of_int n + 1 / 2"
      by simp
    finally show "\<dots> \<noteq> 0"
      by auto
  qed

  have nz2: "1 + tan z ^ 2 \<noteq> 0"
    using tan_square_neq_neg1[of z] by (subst add_eq_0_iff) 

  have nz3: "cos z \<noteq> 0"
  proof
    assume "cos z = 0"
    then obtain n where "z = complex_of_real (real_of_int n * pi) + complex_of_real pi / 2"
      by (subst (asm) cos_eq_0) blast
    also have "\<dots> = complex_of_real ((real_of_int n + 1 / 2) * pi)"
      by (simp add: ring_distribs)
    also have "algebraic \<dots> \<longleftrightarrow> algebraic ((real_of_int n + 1 / 2) * pi)"
      by (rule algebraic_of_real_iff)
    also have "\<not>algebraic ((real_of_int n + 1 / 2) * pi)"
      using nz1[of n] transcendental_pi by simp
    finally show False using assms(1) by contradiction
  qed

  from nz3 have *: "sin z ^ 2 = tan z ^ 2 * cos z ^ 2"
    by (simp add: tan_def field_simps)
  also have "cos z ^ 2 = 1 - sin z ^ 2"
    by (simp add: cos_squared_eq)
  finally have "sin z ^ 2 * (1 + tan z ^ 2) = tan z ^ 2"
    by (simp add: algebra_simps)
  hence "sin z ^ 2 = tan z ^ 2 / (1 + tan z ^ 2)"
    using nz2 by (simp add: field_simps)
  also have "algebraic (tan z ^ 2 / (1 + tan z ^ 2))"
    using \<open>algebraic (tan z)\<close> by auto
  finally have "algebraic (sin z ^ 2)" .
  hence "algebraic (sin z)"
    by simp
  thus False
    using transcendental_sin[OF \<open>algebraic z\<close> \<open>z \<noteq> 0\<close>] by contradiction
qed

lemma transcendental_cot:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (cot z :: complex)"
proof -
  have "\<not>algebraic (tan z)"
    by (rule transcendental_tan) fact+
  also have "algebraic (tan z) \<longleftrightarrow> algebraic (inverse (tan z))"
    by simp
  also have "inverse (tan z) = cot z"
    by (simp add: cot_def tan_def)
  finally show ?thesis .
qed

lemma transcendental_tanh:
  assumes "algebraic z" "z \<noteq> 0" "cosh z \<noteq> 0"
  shows   "\<not>algebraic (tanh z :: complex)"
  using transcendental_tan[of "\<i> * z"] assms unfolding tanh_conv_tan by simp

lemma transcendental_Arcsin:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (Arcsin z)"
proof -
  have "\<i> * z + csqrt (1 - z\<^sup>2) \<noteq> 0"
    using Arcsin_body_lemma by blast
  moreover have "\<i> * z + csqrt (1 - z\<^sup>2) \<noteq> 1"
  proof
    assume "\<i> * z + csqrt (1 - z\<^sup>2) = 1"
    hence "Arcsin z = 0"
      by (simp add: Arcsin_def)
    hence "sin (Arcsin z) = 0"
      by (simp only: sin_zero)
    also have "sin (Arcsin z) = z"
      by simp
    finally show False using \<open>z \<noteq> 0\<close> by simp
  qed
  ultimately have "\<not> algebraic (Ln (\<i> * z + csqrt (1 - z\<^sup>2)))"
    using assms by (intro transcendental_Ln) auto
  thus ?thesis
    by (simp add: Arcsin_def)
qed

lemma transcendental_Arccos:
  assumes "algebraic z" "z \<noteq> 1"
  shows   "\<not>algebraic (Arccos z)"
proof -
  have "z + \<i> * csqrt (1 - z\<^sup>2) \<noteq> 0"
    using Arccos_body_lemma by blast
  moreover have "z + \<i> * csqrt (1 - z\<^sup>2) \<noteq> 1"
  proof
    assume "z + \<i> * csqrt (1 - z\<^sup>2) = 1"
    hence "Arccos z = 0"
      by (simp add: Arccos_def)
    hence "cos (Arccos z) = 1"
      by (simp only: cos_zero)
    also have "cos (Arccos z) = z"
      by simp
    finally show False using \<open>z \<noteq> 1\<close> by simp
  qed
  ultimately have "\<not> algebraic (Ln (z + \<i> * csqrt (1 - z\<^sup>2)))"
    using assms by (intro transcendental_Ln) auto
  thus ?thesis
    by (simp add: Arccos_def)
qed

lemma transcendental_Arctan:
  assumes "algebraic z" "z \<notin> {0, \<i>, -\<i>}"
  shows   "\<not>algebraic (Arctan z)"
proof -
  have "\<i> * z \<noteq> 1" "1 + \<i> * z \<noteq> 0"
    using assms(2) by (auto simp: complex_eq_iff)
  hence "\<not> algebraic (Ln ((1 - \<i> * z) / (1 + \<i> * z)))"
    using assms by (intro transcendental_Ln) auto
  thus ?thesis
    by (simp add: Arctan_def)
qed

end