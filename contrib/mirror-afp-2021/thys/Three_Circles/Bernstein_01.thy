section \<open>Bernstein Polynomials over the interval [0, 1]\<close>

theory Bernstein_01
  imports "HOL-Computational_Algebra.Computational_Algebra" 
    "Budan_Fourier.Budan_Fourier"
    "RRI_Misc"
begin

text \<open>
The theorem of three circles is a statement about the Bernstein coefficients of a polynomial, the
coefficients when a polynomial is expressed as a sum of Bernstein polynomials. These coefficients
behave nicely under translations and rescaling and are the coefficients of a particular polynomial
in the [0, 1] case. We shall define the [0, 1] case now and consider the general case later,
deriving all the results by rescaling.
\<close>

subsection \<open>Definition and basic results\<close>

definition Bernstein_Poly_01 :: "nat \<Rightarrow> nat \<Rightarrow> real poly" where
  "Bernstein_Poly_01 j p = (monom (p choose j) j) 
                              * (monom 1 (p-j) \<circ>\<^sub>p [:1, -1:])"

lemma degree_Bernstein: 
  assumes hb: "j \<le> p" 
  shows "degree (Bernstein_Poly_01 j p) = p"
proof -
  have ha: "monom (p choose j) j \<noteq> (0::real poly)" using hb by force
  have hb: "monom 1 (p-j) \<circ>\<^sub>p [:1, -1:] \<noteq> (0::real poly)"
  proof
    assume "monom 1 (p-j) \<circ>\<^sub>p [:1, -1:] = (0::real poly)"
    hence "lead_coeff (monom 1 (p - j) \<circ>\<^sub>p [:1, -1:]) = (0::real)"
      apply (subst leading_coeff_0_iff)
      by simp
    moreover have "lead_coeff (monom (1::real) (p - j) 
        \<circ>\<^sub>p [:1, -1:]) = (((- 1) ^ (p - j))::real)"
      by (subst lead_coeff_comp, auto simp: degree_monom_eq)
    ultimately show "False" by auto
  qed
  from ha hb show ?thesis
    by (auto simp add: Bernstein_Poly_01_def degree_mult_eq 
          degree_monom_eq degree_pcompose)
qed

lemma coeff_gt: 
  assumes hb: "j > p" 
  shows "Bernstein_Poly_01 j p = 0"
  by (simp add: hb Bernstein_Poly_01_def)

lemma degree_Bernstein_le: "degree (Bernstein_Poly_01 j p) \<le> p"
  apply (cases "j \<le> p")
  by (simp_all add: degree_Bernstein coeff_gt)

lemma poly_Bernstein_nonneg: 
  assumes "x \<ge> 0" and "1 \<ge> x" 
  shows "poly (Bernstein_Poly_01 j p) x \<ge> 0"
  using assms by (simp add: poly_monom poly_pcompose Bernstein_Poly_01_def)

lemma Bernstein_symmetry: 
  assumes "j \<le> p"
  shows "(Bernstein_Poly_01 j p) \<circ>\<^sub>p [:1, -1:] = Bernstein_Poly_01 (p-j) p"
proof -
  have "(Bernstein_Poly_01 j p) \<circ>\<^sub>p [:1, -1:]
         = ((monom (p choose j) j) * (monom 1 (p-j) \<circ>\<^sub>p [:1, -1:])) \<circ>\<^sub>p [:1, -1:]"
    by (simp add: Bernstein_Poly_01_def)
  also have "... = (monom (p choose (p-j)) j * 
                    (monom 1 (p-j) \<circ>\<^sub>p [:1, -1:])) \<circ>\<^sub>p [:1, -1:]" 
    by (fastforce simp: binomial_symmetric[OF assms])
  also have "... = monom (p choose (p-j)) j \<circ>\<^sub>p [:1, -1:] * 
                   (monom 1 (p-j)) \<circ>\<^sub>p ([:1, -1:] \<circ>\<^sub>p [:1, -1:])"
    by (force simp: pcompose_mult pcompose_assoc)
  also have "... = (monom (p choose (p-j)) j \<circ>\<^sub>p [:1, -1:]) * monom 1 (p-j)"
    by (force simp: pcompose_pCons)
  also have "... = smult (p choose (p-j)) (monom 1 j \<circ>\<^sub>p [:1, -1:]) 
                    * monom 1 (p-j)" 
    by (simp add: assms smult_monom pcompose_smult[symmetric])
  also have "... = (monom 1 j \<circ>\<^sub>p [:1, -1:]) * monom (p choose (p-j)) (p-j)"
    apply (subst mult_smult_left)
    apply (subst mult_smult_right[symmetric])
    apply (subst smult_monom)
    by force
  also have "... = Bernstein_Poly_01 (p-j) p" using assms
    by (auto simp: Bernstein_Poly_01_def)
  finally show ?thesis .
qed

subsection \<open>@{term Bernstein_Poly_01} and @{term reciprocal_poly}\<close>

lemma Bernstein_reciprocal: 
  "reciprocal_poly p (Bernstein_Poly_01 i p) 
    = smult (p choose i) ([:-1, 1:]^(p-i))"
proof cases
  assume "i \<le> p"
  hence "reciprocal_poly p (Bernstein_Poly_01 i p) = 
         reciprocal_poly (degree (Bernstein_Poly_01 i p)) (Bernstein_Poly_01 i p)"
    by (auto simp: degree_Bernstein)
  also have "... = reflect_poly (Bernstein_Poly_01 i p)"
    by (rule reciprocal_degree)
  also have "... = smult (p choose i) ([:-1, 1:]^(p-i))"
    by (auto simp: Bernstein_Poly_01_def reflect_poly_simps monom_altdef
         pcompose_pCons reflect_poly_pCons' hom_distribs)
  finally show ?thesis .
next
  assume h:"\<not> i \<le> p"
  hence "reciprocal_poly p (Bernstein_Poly_01 i p) = (0::real poly)"
    by (auto simp: coeff_gt reciprocal_poly_def)
  also have "... = smult (p choose i) ([:-1, 1:]^(p - i))" using h
    by fastforce
  finally show ?thesis .
qed

lemma Bernstein_reciprocal_translate: 
  "reciprocal_poly p (Bernstein_Poly_01 i p) \<circ>\<^sub>p [:1, 1:] = 
   monom (p choose i) (p - i)"
  by (auto simp: Bernstein_reciprocal pcompose_smult pcompose_pCons monom_altdef hom_distribs)

lemma coeff_Bernstein_sum_01: fixes b::"nat \<Rightarrow> real" assumes hi: "p \<ge> i"
  shows 
    "coeff (reciprocal_poly p 
            (\<Sum>x = 0..p. smult (b x) (Bernstein_Poly_01 x p)) \<circ>\<^sub>p [:1, 1:]) 
      (p - i) = (p choose i) * (b i)" (is "?L = ?R")
proof -
  define P where "P \<equiv> (\<Sum>x = 0..p. (smult (b x) (Bernstein_Poly_01 x p)))"

  have "\<And>x. degree (smult (b x) (Bernstein_Poly_01 x p)) \<le> p"
  proof -
    fix x
    show "degree (smult (b x) (Bernstein_Poly_01 x p)) \<le> p"
      apply (cases "x \<le> p")
      by (auto simp: degree_Bernstein coeff_gt)
  qed
  hence "reciprocal_poly p P = 
         (\<Sum>x = 0..p. reciprocal_poly p (smult (b x) (Bernstein_Poly_01 x p)))"
    apply (subst P_def)
    apply (rule reciprocal_sum)
    by presburger
  also have
    "... = (\<Sum>x = 0..p. (smult (b x * (p choose x)) ([:-1, 1:]^(p-x))))"
  proof (rule sum.cong)
    fix x assume "x \<in> {0..p}"
    hence "x \<le> p" by simp
    thus "reciprocal_poly p (smult (b x) (Bernstein_Poly_01 x p)) =
          smult ((b x) * (p choose x)) ([:-1, 1:]^(p-x))"
      by (auto simp add: reciprocal_smult degree_Bernstein Bernstein_reciprocal)
  qed (simp)
  finally have 
    "reciprocal_poly p P = 
     (\<Sum>x = 0..p. (smult ((b x) * (p choose x)) ([:-1, 1:]^(p-x))))" .
  hence 
    "(reciprocal_poly p P) \<circ>\<^sub>p [:1, 1:] = 
     (\<Sum>x = 0..p. (smult ((b x) * (p choose x)) ([:-1, 1:]^(p-x))) \<circ>\<^sub>p [:1, 1:])"
    by (simp add: pcompose_sum pcompose_add)
  also have "... = (\<Sum>x = 0..p. (monom ((b x) * (p choose x)) (p - x)))"
  proof (rule sum.cong)
    fix x assume "x \<in> {0..p}"
    hence "x \<le> p" by simp
    thus "smult (b x * (p choose x)) ([:- 1, 1:] ^ (p - x)) \<circ>\<^sub>p [:1, 1:] =
          monom (b x * (p choose x)) (p - x)"
      by (simp add: hom_distribs pcompose_smult pcompose_pCons monom_altdef)
  qed (simp)
  finally have "(reciprocal_poly p P) \<circ>\<^sub>p [:1, 1:] = 
                (\<Sum>x = 0..p. (monom ((b x) * (p choose x)) (p - x)))" .
  hence "?L = (\<Sum>x = 0..p. if p - x = p - i then b x * real (p choose x) else 0)"
    by (auto simp add: P_def coeff_sum)
  also have "... = (\<Sum>x = 0..p. if x = i then b x * real (p choose x) else 0)"
  proof (rule sum.cong)
    fix x assume "x \<in> {0..p}"
    hence "x \<le> p" by simp
    thus "(if p - x = p - i then b x * real (p choose x) else 0) =
          (if x = i then b x * real (p choose x) else 0)" using hi
      by (auto simp add: leI)
  qed (simp)
  also have "... = ?R" by simp
  finally show ?thesis .
qed

lemma Bernstein_sum_01: assumes hP: "degree P \<le> p"
  shows 
  "P = (\<Sum>j = 0..p. smult 
     (inverse (real (p choose j)) * 
      coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j))
   (Bernstein_Poly_01 j p))"
proof -
  define Q where "Q \<equiv> reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]"
  from hP Q_def have hQ: "degree Q \<le> p" 
    by (auto simp: degree_reciprocal degree_pcompose)
  have "reciprocal_poly p (\<Sum>j = 0..p. 
        smult (inverse (real (p choose j)) * coeff Q (p-j)) 
        (Bernstein_Poly_01 j p)) \<circ>\<^sub>p [:1, 1:] = Q"
  proof (rule poly_eqI)
    fix n
    show "coeff (reciprocal_poly p (\<Sum>j = 0..p. 
          smult (inverse (real (p choose j)) * coeff Q (p-j))
          (Bernstein_Poly_01 j p)) \<circ>\<^sub>p [:1, 1:]) n = coeff Q n" 
      (is "?L = ?R")
    proof cases
      assume hn: "n \<le> p"
      hence "?L = coeff (reciprocal_poly p (\<Sum>j = 0..p. 
             smult (inverse (real (p choose j)) * coeff Q (p-j)) 
             (Bernstein_Poly_01 j p)) \<circ>\<^sub>p [:1, 1:]) (p - (p - n))"
        by force
      also have "... = (p choose (p-n)) * 
                       (inverse (real (p choose (p-n))) * 
                        coeff Q (p-(p-n)))"
        apply (subst coeff_Bernstein_sum_01)
        by auto
      also have "... = ?R" using hn
        by fastforce
      finally show "?L = ?R" .
    next
      assume hn: "\<not> n \<le> p"
      have "degree (\<Sum>j = 0..p.
            smult (inverse (real (p choose j)) * coeff Q (p - j))
            (Bernstein_Poly_01 j p)) \<le> p"
      proof (rule degree_sum_le)
        fix q assume "q \<in> {0..p}"
        hence "q \<le> p" by fastforce
        thus "degree (smult (inverse (real (p choose q)) * 
              coeff Q (p - q)) (Bernstein_Poly_01 q p)) \<le> p"
          by (auto simp add: degree_Bernstein degree_smult_le)
      qed simp
      hence "degree (reciprocal_poly p (\<Sum>j = 0..p.
            smult (inverse (real (p choose j)) * coeff Q (p - j)) 
            (Bernstein_Poly_01 j p)) \<circ>\<^sub>p [:1, 1:]) \<le> p"
        by (auto simp add: degree_pcompose degree_reciprocal)
      hence "?L = 0" using hn by (auto simp add: coeff_eq_0)
      thus "?L = ?R" using hQ hn by (simp add: coeff_eq_0)
    qed
  qed
  hence "reciprocal_poly p P \<circ>\<^sub>p [:1, 1:] = 
         reciprocal_poly p (\<Sum>j = 0..p. 
         smult (inverse (real (p choose j)) *
         coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j))
         (Bernstein_Poly_01 j p)) \<circ>\<^sub>p [:1, 1:]" 
    by (auto simp: degree_reciprocal degree_pcompose Q_def)
  hence "reciprocal_poly p P \<circ>\<^sub>p ([:1, 1:] \<circ>\<^sub>p [:-1, 1:]) =
         reciprocal_poly p (\<Sum>j = 0..p. smult (inverse (real (p choose j)) * 
         coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j)) 
         (Bernstein_Poly_01 j p)) \<circ>\<^sub>p ([:1, 1:] \<circ>\<^sub>p [:-1, 1:])"
    by (auto simp: pcompose_assoc)
  hence "reciprocal_poly p P = reciprocal_poly p (\<Sum>j = 0..p. 
         smult (inverse (real (p choose j)) *
         coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j)) (Bernstein_Poly_01 j p))" 
    by (auto simp: pcompose_pCons)
  hence "reciprocal_poly p (reciprocal_poly p P) = 
         reciprocal_poly p (reciprocal_poly p (\<Sum>j = 0..p. 
         smult (inverse (real (p choose j)) *
         coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j)) (Bernstein_Poly_01 j p)))"
    by argo
  thus "P = (\<Sum>j = 0..p. smult (inverse (real (p choose j)) * 
        coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j)) (Bernstein_Poly_01 j p))"
    using hP by (auto simp: reciprocal_reciprocal degree_sum_le degree_smult_le 
                 degree_Bernstein degree_add_le)
qed

lemma Bernstein_Poly_01_span1: 
  assumes hP: "degree P \<le> p"
  shows "P \<in> poly_vs.span {Bernstein_Poly_01 x p | x. x \<le> p}"
proof -
  have "Bernstein_Poly_01 x p
         \<in> poly_vs.span {Bernstein_Poly_01 x p |x. x \<le> p}"
    if "x \<in> {0..p}" for x
  proof -
    have "\<exists>n. Bernstein_Poly_01 x p = Bernstein_Poly_01 n p \<and> n \<le> p"
      using that by force
    then show 
      "Bernstein_Poly_01 x p \<in> poly_vs.span {Bernstein_Poly_01 n p |n. n \<le> p}"
      by (simp add: poly_vs.span_base)
  qed
  thus ?thesis
    apply (subst Bernstein_sum_01[OF hP])
    apply (rule poly_vs.span_sum)
    apply (rule poly_vs.span_scale)
    by blast
qed

lemma Bernstein_Poly_01_span:
  "poly_vs.span {Bernstein_Poly_01 x p | x. x \<le> p} 
      = {x. degree x \<le> p}"
  apply (subst monom_span[symmetric])
  apply (subst poly_vs.span_eq)
  by (auto simp: monom_span degree_Bernstein_le
      Bernstein_Poly_01_span1 degree_monom_eq)

subsection \<open>Bernstein coefficients and changes\<close>

definition Bernstein_coeffs_01 :: "nat \<Rightarrow> real poly \<Rightarrow> real list" where 
  "Bernstein_coeffs_01 p P = 
   [(inverse (real (p choose j)) * 
    coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j)). j \<leftarrow> [0..<(p+1)]]"

lemma length_Bernstein_coeffs_01: "length (Bernstein_coeffs_01 p P) = p + 1"
  by (auto simp: Bernstein_coeffs_01_def)

lemma nth_default_Bernstein_coeffs_01: assumes "degree P \<le> p"
  shows "nth_default 0 (Bernstein_coeffs_01 p P) i = 
         inverse (p choose i) * coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-i)"
  apply (cases "p = i")
  using assms by (auto simp: Bernstein_coeffs_01_def nth_default_append
                  nth_default_Cons Nitpick.case_nat_unfold binomial_eq_0)

lemma Bernstein_coeffs_01_sum: assumes "degree P \<le> p"
  shows "P = (\<Sum>j = 0..p. smult (nth_default 0 (Bernstein_coeffs_01 p P) j) 
             (Bernstein_Poly_01 j p))"
  apply (subst nth_default_Bernstein_coeffs_01[OF assms])
  apply (subst Bernstein_sum_01[OF assms])
  by argo

definition Bernstein_changes_01 :: "nat \<Rightarrow> real poly \<Rightarrow> int" where
  "Bernstein_changes_01 p P = nat (changes (Bernstein_coeffs_01 p P))"

lemma Bernstein_changes_01_def': 
  "Bernstein_changes_01 p P = nat (changes [(inverse (real (p choose j)) * 
     coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p-j)). j \<leftarrow> [0..<p + 1]])"
  by (simp add: Bernstein_changes_01_def Bernstein_coeffs_01_def)

lemma Bernstein_changes_01_eq_changes: 
  assumes hP: "degree P \<le> p"
  shows "Bernstein_changes_01 p P = 
         changes (coeffs ((reciprocal_poly p P) \<circ>\<^sub>p [:1, 1:]))"
proof (subst Bernstein_changes_01_def')
  have h: 
    "map (\<lambda>j. inverse (real (p choose j)) * 
     coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p - j)) [0..<p + 1] = 
     map (\<lambda>j. inverse (real (p choose j)) * 
     nth_default 0 [nth_default 0 (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))
                    (p - j). j \<leftarrow> [0..<p + 1]] j) [0..<p + 1]"
  proof (rule map_cong)
    fix x
    assume "x \<in> set [0..<p+1]"
    hence hx: "x \<le> p" by fastforce
    moreover have 1:
      "length (map (\<lambda>j. nth_default 0 
       (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) (p - j)) [0..<p + 1]) \<le> Suc p"
      by force
    moreover have "length (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) \<le> Suc p"
    proof (cases "P=0")
      case False
      then have "reciprocal_poly p P \<circ>\<^sub>p [:1, 1:] \<noteq> 0" 
        using hP by (simp add: Missing_Polynomial.pcompose_eq_0 reciprocal_0_iff)
      moreover have "Suc (degree (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) \<le> Suc p"
        using hP by (auto simp: degree_pcompose degree_reciprocal)
      ultimately show ?thesis 
        using length_coeffs_degree by force
    qed (auto simp: reciprocal_0)
    ultimately have h: 
      "nth_default 0 (map (\<lambda>j. nth_default 0 (coeffs 
       (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) (p - j)) [0..<p + 1]) x =
       nth_default 0 (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) (p - x)"
      (is "?L = ?R")
    proof -
      have "?L = (map (\<lambda>j. nth_default 0 (coeffs
            (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) (p - j)) [0..<p + 1]) ! x"
        using hx by (auto simp: nth_default_nth)
      also have "... =  nth_default 0 
          (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) (p - [0..<p + 1] ! x)"
        apply (subst nth_map)
        using hx by auto
      also have "... = ?R"
        apply (subst nth_upt)
        using hx by auto
      finally show ?thesis .
    qed
    show "inverse (real (p choose x)) *
          coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p - x) =
          inverse (real (p choose x)) *
          nth_default 0 (map (\<lambda>j. nth_default 0 
          (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) (p - j)) [0..<p + 1]) x"
      apply (subst h)
      apply (subst nth_default_coeffs_eq)
      by blast
  qed auto

  have 1: 
    "rev (map (\<lambda>j. nth_default 0 (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) 
     (p - j)) [0..<p + 1]) = map (\<lambda>j. nth_default 0 (coeffs 
     (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) j) [0..<p + 1]"
  proof (subst rev_map, rule map_cong')
    have "\<And>q. (q \<ge> p \<longrightarrow> rev [q-p..<q+1] = map ((-) q) [0..<p+1])"
    proof (induction p)
      case 0
      then show ?case by simp
    next
      case (Suc p)
      have IH: "\<And>q. (q \<ge> p \<longrightarrow> rev [q-p..<q+1] = map ((-) q) [0..<p+1])"
        using Suc.IH by blast
      show ?case
      proof
        assume hq: "Suc p \<le> q"
        then have h: "rev [q - p..<q + 1] = map ((-) (q)) [0..<p + 1]"
          apply (subst IH)
          using hq by auto
        have "[q - Suc p..<q + 1] = (q - Suc p) # [q - p..<q + 1]"
          by (simp add: Suc_diff_Suc Suc_le_lessD hq upt_conv_Cons)
        hence "rev [q - Suc p..<q + 1] = rev [q - p..<q + 1] @ [q - Suc p]"
          by force
        also have "... = map ((-) (q)) [0..<p + 1] @ [q - Suc p]"
          using h by blast
        also have "... = map ((-) q) [0..<Suc p + 1]"
          by force
        finally show "rev [q - Suc p..<q + 1] = map ((-) q) [0..<Suc p + 1]" .
      qed
    qed
    thus "rev [0..<p + 1] = map ((-) p) [0..<p + 1]"
      by force
  next
    fix y
    assume "y \<in> set [0..<p + 1]"
    hence "y \<le> p" by fastforce
    thus "nth_default 0 (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) (p - (p - y)) =
          nth_default 0 (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) y"
      by fastforce
  qed

  have 2: "\<And> f. f \<noteq> 0 \<longrightarrow> degree f \<le> p \<longrightarrow>
           map (nth_default 0 (coeffs f)) [0..<p + 1] = 
           coeffs f @ replicate (p - degree f) 0"
  proof (induction p)
    case 0
    then show ?case by (auto simp: degree_0_iff)
  next
    fix f
    case (Suc p)
    hence IH: "(f \<noteq> 0 \<longrightarrow>
                degree f \<le> p \<longrightarrow>
                map (nth_default 0 (coeffs f)) [0..<p + 1] =
                coeffs f @ replicate (p - degree f) 0)" by blast
    then show ?case
    proof (cases)
      assume h': "Suc p = degree f"
      hence h: "[0..<Suc p + 1] = [0..<length (coeffs f)]" 
        by (metis add_is_0 degree_0 length_coeffs plus_1_eq_Suc zero_neq_one)
      thus ?thesis
        apply (subst h)
        apply (subst map_nth_default)
        using h' by fastforce
    next
      assume h': "Suc p \<noteq> degree f"
      show ?thesis
      proof
        assume hf: "f \<noteq> 0"
        show "degree f \<le> Suc p \<longrightarrow>
            map (nth_default 0 (coeffs f)) [0..<Suc p + 1] =
            coeffs f @ replicate (Suc p - degree f) 0"
        proof
          assume "degree f \<le> Suc p"
          hence 1: "degree f \<le> p" using h' by fastforce
          hence 2: "map (nth_default 0 (coeffs f)) [0..<p + 1] =
                  coeffs f @ replicate (p - degree f) 0" using IH hf by blast
          have "map (nth_default 0 (coeffs f)) [0..<Suc p + 1] = 
                map (nth_default 0 (coeffs f)) [0..<p + 1] @
                     [nth_default 0 (coeffs f) (Suc p)]"
            by fastforce
          also have
            "... = coeffs f @ replicate (p - degree f) 0 @ [coeff f (Suc p)]"
            using 2 
            by (auto simp: nth_default_coeffs_eq)
          also have "... = coeffs f @ replicate (p - degree f) 0 @ [0]"
            using \<open>degree f \<le> Suc p\<close> h' le_antisym le_degree by blast
          also have "... = coeffs f @ replicate (Suc p - degree f) 0" using 1
            by (simp add: Suc_diff_le replicate_app_Cons_same)
          finally show "map (nth_default 0 (coeffs f)) [0..<Suc p + 1] =
                coeffs f @ replicate (Suc p - degree f) 0" .
        qed
      qed
    qed
  qed
  
  thus "int (nat (changes (map (\<lambda>j. inverse (real (p choose j)) *
        coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p - j)) [0..<p + 1]))) =
        changes (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))"
  proof cases
    assume hP: "P = 0"
    show "int (nat (changes (map (\<lambda>j. inverse (real (p choose j)) *
          coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]) (p - j)) [0..<p + 1]))) =
          changes (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))" (is "?L = ?R")
    proof -
      have "?L = int (nat (changes (map (\<lambda>j. 0::real) [0..<p+1])))"
        using hP by (auto simp: reciprocal_0 changes_nonneg)
      also have "... = 0"
        apply (induction p)
        by (auto simp: map_replicate_trivial changes_nonneg
            replicate_app_Cons_same)
      also have "0 = changes ([]::real list)" by simp
      also have "... = ?R" using hP by (auto simp: reciprocal_0)
      finally show ?thesis .
    qed
  next
    assume hP': "P \<noteq> 0"
    thus ?thesis
      apply (subst h)
      apply (subst changes_scale)
        apply auto[2]
      apply (subst changes_rev[symmetric])
      apply (subst 1)
      apply (subst 2)
      apply (simp add: pcompose_eq_0 hP reciprocal_0_iff)
      using assms apply (auto simp: degree_reciprocal)[1]
      by (auto simp: changes_append_replicate_0 changes_nonneg)
  qed
qed

lemma Bernstein_changes_01_test: fixes P::"real poly"
  assumes hP: "degree P \<le> p" and h0: "P \<noteq> 0"
  shows "proots_count P {x. 0 < x \<and> x < 1} \<le> Bernstein_changes_01 p P \<and>
        even (Bernstein_changes_01 p P - proots_count P {x. 0 < x \<and> x < 1})"
proof -
  let ?Q = "(reciprocal_poly p P) \<circ>\<^sub>p [:1, 1:]"

  have 1: "changes (coeffs ?Q) \<ge> proots_count ?Q {x. 0 < x} \<and> 
        even (changes (coeffs ?Q) - proots_count ?Q {x. 0 < x})"
    apply (rule descartes_sign)
    by (simp add: Missing_Polynomial.pcompose_eq_0 h0 hP reciprocal_0_iff)
  
  have "((+) (1::real) ` Collect ((<) (0::real))) = {x. (1::real)<x}"
  proof
    show "{x::real. 1 < x} \<subseteq> (+) 1 ` Collect ((<) 0)"
    proof
      fix x::real assume "x \<in> {x. 1 < x}"
      hence "1 < x" by simp
      hence "-1 + x \<in> Collect ((<) 0)" by auto
      hence "1 + (-1 + x) \<in> (+) 1 ` Collect ((<) 0)" by blast
      thus "x \<in> (+) 1 ` Collect ((<) 0)" by argo
    qed
  qed auto
  hence 2:  "proots_count P {x. 0 < x \<and> x < 1} = proots_count ?Q {x. 0 < x}"
    using assms
    by (auto simp: proots_pcompose reciprocal_0_iff proots_count_reciprocal')
  
  show ?thesis
    apply (subst Bernstein_changes_01_eq_changes[OF hP])
    apply (subst Bernstein_changes_01_eq_changes[OF hP])
    apply (subst 2)
    apply (subst 2)
    by (rule 1)
qed

subsection \<open>Expression as a Bernstein sum\<close>

lemma Bernstein_coeffs_01_0: "Bernstein_coeffs_01 p 0 = replicate (p+1) 0"
  by (auto simp: Bernstein_coeffs_01_def reciprocal_0 map_replicate_trivial
      replicate_append_same)

lemma Bernstein_coeffs_01_1: "Bernstein_coeffs_01 p 1 = replicate (p+1) 1"
proof -
  have "Bernstein_coeffs_01 p 1 =
     map (\<lambda>j. inverse (real (p choose j)) *
     coeff (\<Sum>k\<le>p. smult (real (p choose k)) ([:0, 1:] ^ k)) (p - j)) [0..<(p+1)]"
    by (auto simp: Bernstein_coeffs_01_def reciprocal_1 monom_altdef
        hom_distribs pcompose_pCons poly_0_coeff_0[symmetric] poly_binomial)
  also have "... = map (\<lambda>j. inverse (real (p choose j)) * 
             real (p choose (p - j))) [0..<(p+1)]"
    by (auto simp: monom_altdef[symmetric] coeff_sum binomial)
  also have "... = map (\<lambda>j. 1) [0..<(p+1)]"
    apply (rule map_cong)
    subgoal by argo
    subgoal apply (subst binomial_symmetric)
      by auto
    done
  also have "... = replicate (p+1) 1"
    by (auto simp: map_replicate_trivial replicate_append_same)
  finally show ?thesis .
qed

lemma Bernstein_coeffs_01_x: assumes "p \<noteq> 0"
  shows "Bernstein_coeffs_01 p (monom 1 1) = [i/p. i \<leftarrow> [0..<(p+1)]]"
proof -
  have 
    "Bernstein_coeffs_01 p (monom 1 1) = map (\<lambda>j. inverse (real (p choose j)) *
     coeff (monom 1 (p - Suc 0) \<circ>\<^sub>p [:1, 1:]) (p - j)) [0..<(p+1)]"
    using assms by (auto simp: Bernstein_coeffs_01_def reciprocal_monom)
  also have 
    "... = map (\<lambda>j. inverse (real (p choose j)) *
     (\<Sum>k\<le>p - Suc 0. coeff (monom (real (p -  1 choose k)) k) (p - j))) [0..<(p+1)]"
    by (auto simp: monom_altdef hom_distribs pcompose_pCons poly_binomial coeff_sum)
  also have"... = map (\<lambda>j. inverse (real (p choose j)) *
            real (p -  1 choose (p - j))) [0..<(p+1)]"
    by auto
  also have "... = map (\<lambda>j. j/p) [0..<(p+1)]"
  proof (rule map_cong)
    fix x assume "x \<in> set [0..<(p+1)]"
    hence "x \<le> p" by force
    thus "inverse (real (p choose x)) * real (p - 1 choose (p - x)) =
          real x / real p"
    proof (cases "x = 0")
      show "x = 0 \<Longrightarrow> ?thesis"
        using assms by fastforce
      assume 1: "x \<le> p" and 2: "x \<noteq> 0"
      hence "p - x \<le> p - 1" by force
      hence "(p - 1 choose (p - x)) = (p - 1 choose (x - 1))"
        apply (subst binomial_symmetric)
        using 1 2 by auto
      hence "x * (p choose x) = p * (p - 1 choose (p - x))"
         using 2 times_binomial_minus1_eq by simp
       hence "real x * real (p choose x) = real p * real (p - 1 choose (p - x))"
         by (metis of_nat_mult)
       thus ?thesis using 1 2
         by (auto simp: divide_simps)
    qed
  qed blast
  finally show ?thesis .
qed

lemma Bernstein_coeffs_01_add: 
  assumes "degree P \<le> p" and "degree Q \<le> p"
  shows "nth_default 0 (Bernstein_coeffs_01 p (P + Q)) i = 
    nth_default 0 (Bernstein_coeffs_01 p P) i +
    nth_default 0 (Bernstein_coeffs_01 p Q) i"
  using assms by (auto simp: nth_default_Bernstein_coeffs_01 degree_add_le
                    reciprocal_add pcompose_add algebra_simps)

lemma Bernstein_coeffs_01_smult: 
  assumes "degree P \<le> p"
  shows "nth_default 0 (Bernstein_coeffs_01 p (smult a P)) i =
          a * nth_default 0 (Bernstein_coeffs_01 p P) i"
  using assms
  by (auto simp: nth_default_Bernstein_coeffs_01 reciprocal_smult
      pcompose_smult)

end
