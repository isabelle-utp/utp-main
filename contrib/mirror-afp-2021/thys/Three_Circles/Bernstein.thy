section \<open>Bernstein Polynomials over any finite interval\<close>

theory Bernstein
  imports "Bernstein_01"
begin

subsection \<open>Definition and relation to Bernstein Polynomials over [0, 1]\<close>

definition Bernstein_Poly :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real poly" where
  "Bernstein_Poly j p c d = smult ((p choose j)/(d - c)^p)
      (((monom 1 j) \<circ>\<^sub>p [:-c, 1:]) * (monom 1 (p-j) \<circ>\<^sub>p [:d, -1:]))"

lemma Bernstein_Poly_altdef: 
  assumes "c \<noteq> d" and "j \<le> p"
  shows "Bernstein_Poly j p c d = smult (p choose j) 
            ([:-c/(d-c), 1/(d-c):]^j * [:d/(d-c), -1/(d-c):]^(p-j))" 
    (is "?L = ?R")
proof -
  have "?L = smult (p choose j) (smult ((1/(d - c))^j)
        (smult ((1/(d - c))^(p-j)) ([:-c, 1:]^j * [:d, -1:]^(p-j))))"
    using assms by (auto simp: Bernstein_Poly_def monom_altdef hom_distribs
                    pcompose_pCons smult_eq_iff field_simps power_add[symmetric])
  also have "... = ?R"
    apply (subst mult_smult_right[symmetric])
    apply (subst mult_smult_left[symmetric])
    apply (subst smult_power)
    apply (subst smult_power)
    by auto
  finally show ?thesis .
qed

lemma Bernstein_Poly_nonneg: 
  assumes "c \<le> x" and "x \<le> d"
  shows "poly (Bernstein_Poly j p c d) x \<ge> 0"
  using assms by (auto simp: Bernstein_Poly_def poly_pcompose poly_monom)

lemma Bernstein_Poly_01: "Bernstein_Poly j p 0 1 = Bernstein_Poly_01 j p"
  by (auto simp: Bernstein_Poly_def Bernstein_Poly_01_def monom_altdef)

lemma Bernstein_Poly_rescale: 
  assumes "a \<noteq> b"
  shows "Bernstein_Poly j p c d \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b-a:] 
            = Bernstein_Poly j p ((c-a)/(b-a)) ((d-a)/(b-a))"
  (is "?L = ?R")
proof -
  have "?R = smult (real (p choose j) 
      / ((d - a) / (b - a) - (c - a) / (b - a)) ^ p)
      ([:- ((c - a) / (b - a)), 1:] ^ j 
      * [:(d - a) / (b - a), - 1:] ^ (p - j))"
    by (auto simp: Bernstein_Poly_def monom_altdef hom_distribs 
        pcompose_pCons) 
  also have "... = smult (real (p choose j) / ((d - c) / (b - a)) ^ p)
              ([:- ((c - a) / (b - a)), 1:] ^ j * [:(d - a) / (b - a), - 1:] 
            ^ (p - j))"
    by argo
  also have "... = smult (real (p choose j) / (d - c) ^ p) 
      (smult ((b - a) ^ (p - j)) (smult ((b - a) ^ j)
      ([:- ((c - a) / (b - a)), 1:] ^ j * [:(d - a) / (b - a), - 1:] 
      ^ (p - j))))"
    by (auto simp: power_add[symmetric] power_divide)
  also have "... = smult (real (p choose j) / (d - c) ^ p)
              ([:- (c - a), b - a:] ^ j * [:d - a, -(b - a):] ^ (p - j))"
    apply (subst mult_smult_left[symmetric])
    apply (subst mult_smult_right[symmetric])
    using assms by (auto simp: smult_power)
  also have "... = ?L"
    using assms 
    by (auto simp: Bernstein_Poly_def monom_altdef pcompose_mult 
        pcompose_smult hom_distribs pcompose_pCons)
  finally show ?thesis by presburger
qed

lemma Bernstein_Poly_rescale_01: 
  assumes "c \<noteq> d"
  shows "Bernstein_Poly j p c d \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d-c:] 
          = Bernstein_Poly_01 j p"
  apply (subst Bernstein_Poly_rescale)
  using assms by (auto simp: Bernstein_Poly_01)

lemma Bernstein_Poly_eq_rescale_01: 
  assumes "c \<noteq> d"
  shows "Bernstein_Poly j p c d = Bernstein_Poly_01 j p 
            \<circ>\<^sub>p [:0, 1/(d-c):] \<circ>\<^sub>p [:-c, 1:]"
  apply (subst Bernstein_Poly_rescale_01[symmetric])
  using assms by (auto simp: pcompose_pCons pcompose_assoc[symmetric])

lemma coeff_Bernstein_sum: 
  fixes b::"nat \<Rightarrow> real" and p::nat and c d::real
  defines "P \<equiv> (\<Sum>j = 0..p. (smult (b j) (Bernstein_Poly j p c d)))"
  assumes "i \<le> p" and "c \<noteq> d"
  shows "coeff ((reciprocal_poly p (P \<circ>\<^sub>p [:c, 1:] 
      \<circ>\<^sub>p [:0, d-c:])) \<circ>\<^sub>p [:1, 1:]) (p - i) = (p choose i) * (b i)"
proof -
  have h: "P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d-c:] 
      = (\<Sum>j = 0..p. (smult (b j) (Bernstein_Poly_01 j p)))"
    using assms 
    by (auto simp: P_def pcompose_sum pcompose_smult 
          pcompose_add Bernstein_Poly_rescale_01)
  then show ?thesis
    using coeff_Bernstein_sum_01 assms by simp
qed

lemma Bernstein_sum: 
  assumes "c \<noteq> d" and "degree P \<le> p"
  shows "P = (\<Sum>j = 0..p. smult (inverse (real (p choose j))
     * coeff (reciprocal_poly p (P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d-c:]) 
      \<circ>\<^sub>p [:1, 1:]) (p-j)) (Bernstein_Poly j p c d))"
  apply (subst Bernstein_Poly_eq_rescale_01)
  subgoal using assms by blast
  subgoal 
    apply (subst pcompose_smult[symmetric])
    apply (subst pcompose_sum[symmetric])
    apply (subst pcompose_smult[symmetric])
    apply (subst pcompose_sum[symmetric])
    apply (subst Bernstein_sum_01[symmetric])
    using assms by (auto simp: degree_pcompose pcompose_assoc[symmetric] 
        pcompose_pCons)
  done

lemma Bernstein_Poly_span1: 
  assumes "c \<noteq> d" and "degree P \<le> p"
  shows "P \<in> poly_vs.span {Bernstein_Poly x p c d | x. x \<le> p}"
proof (subst Bernstein_sum[OF assms], rule poly_vs.span_sum)
  fix x :: nat
  assume "x \<in> {0..p}"
  then have "\<exists>n. Bernstein_Poly x p c d = Bernstein_Poly n p c d \<and> n \<le> p"
    by auto
  then have 
    "Bernstein_Poly x p c d \<in> poly_vs.span {Bernstein_Poly n p c d |n. n \<le> p}"
    by (simp add: poly_vs.span_base)
  thus "smult (inverse (real (p choose x)) *
        coeff (reciprocal_poly p (P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d - c:]) \<circ>\<^sub>p [:1, 1:])
        (p - x)) (Bernstein_Poly x p c d)
         \<in> poly_vs.span {Bernstein_Poly x p c d |x. x \<le> p}"
    by (rule poly_vs.span_scale)
qed

lemma Bernstein_Poly_span: 
  assumes "c \<noteq> d" 
  shows "poly_vs.span {Bernstein_Poly x p c d | x. x \<le> p} = {x. degree x \<le> p}"
proof (subst Bernstein_Poly_01_span[symmetric], subst poly_vs.span_eq, rule conjI)
  show "{Bernstein_Poly x p c d |x. x \<le> p}
      \<subseteq> poly_vs.span {Bernstein_Poly_01 x p |x. x \<le> p}"
    apply (subst Setcompr_subset)
    apply (rule allI, rule impI)
    apply (rule Bernstein_Poly_01_span1)
    using assms by (auto simp: degree_Bernstein_le Bernstein_Poly_eq_rescale_01
                    degree_pcompose)

  show "{Bernstein_Poly_01 x p |x. x \<le> p}
      \<subseteq> poly_vs.span {Bernstein_Poly x p c d |x. x \<le> p}"
    apply (subst Setcompr_subset)
    apply (rule allI, rule impI)
    apply (rule Bernstein_Poly_span1)
    using assms by (auto simp: degree_Bernstein_le)
qed

lemma Bernstein_Poly_independent: assumes "c \<noteq> d" 
  shows "poly_vs.independent {Bernstein_Poly x p c d | x. x \<in> {..p}}"
proof (rule poly_vs.card_le_dim_spanning)
  show "{Bernstein_Poly x p c d |x. x \<in> {.. p}} \<subseteq> {x. degree x \<le> p}"
    using assms 
    by (auto simp: degree_Bernstein Bernstein_Poly_eq_rescale_01 degree_pcompose)
  show "{x. degree x \<le> p} \<subseteq> poly_vs.span {Bernstein_Poly x p c d |x. x \<in> {..p}}"
    using assms by (auto simp: Bernstein_Poly_span1)
  show "finite {Bernstein_Poly x p c d |x. x \<in> {..p}}" by fastforce
  show "card {Bernstein_Poly x p c d |x. x \<in> {..p}} \<le> poly_vs.dim {x. degree x \<le> p}"
    apply (rule le_trans)
     apply (subst image_Collect[symmetric], rule card_image_le, force)
    by (force simp: dim_degree)
qed

subsection \<open>Bernstein coefficients and changes over any interval\<close>

definition Bernstein_coeffs ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> real list" where 
  "Bernstein_coeffs p c d P = 
    [(inverse (real (p choose j)) * 
      coeff (reciprocal_poly p (P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d-c:]) \<circ>\<^sub>p [:1, 1:]) (p-j)). 
     j \<leftarrow> [0..<(p+1)]]"

lemma Bernstein_coeffs_eq_rescale: assumes "c \<noteq> d"
  shows "Bernstein_coeffs p c d P = Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d-c:])"
  using assms by (auto simp: pcompose_pCons pcompose_assoc[symmetric]
                  Bernstein_coeffs_def Bernstein_coeffs_01_def)

lemma nth_default_Bernstein_coeffs: assumes "degree P \<le> p"
  shows "nth_default 0 (Bernstein_coeffs p c d P) i =
         inverse (p choose i) * coeff
         (reciprocal_poly p (P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d-c:]) \<circ>\<^sub>p [:1, 1:]) (p-i)"
  apply (cases "p = i")
  using assms by (auto simp: Bernstein_coeffs_def nth_default_append
                  nth_default_Cons Nitpick.case_nat_unfold binomial_eq_0)

lemma Bernstein_coeffs_sum: assumes "c \<noteq> d" and hP: "degree P \<le> p"
  shows "P = (\<Sum>j = 0..p. smult (nth_default 0 (Bernstein_coeffs p c d P) j)
         (Bernstein_Poly j p c d))"
  apply (subst nth_default_Bernstein_coeffs[OF hP])
  apply (subst Bernstein_sum[OF assms])
  by argo

definition Bernstein_changes :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> int" where
  "Bernstein_changes p c d P = nat (changes (Bernstein_coeffs p c d P))"

lemma Bernstein_changes_eq_rescale: assumes "c \<noteq> d" and "degree P \<le> p"
  shows "Bernstein_changes p c d P =
         Bernstein_changes_01 p (P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d-c:])"
  using assms by (auto simp: Bernstein_coeffs_eq_rescale Bernstein_changes_def
                  Bernstein_changes_01_def)

text \<open>This is related and mostly equivalent to previous Descartes test \cite{li2019counting}\<close>
lemma Bernstein_changes_test: 
  fixes P::"real poly"
  assumes "degree P \<le> p" and "P \<noteq> 0" and "c < d"
  shows "proots_count P {x. c < x \<and> x < d} \<le> Bernstein_changes p c d P \<and>
        even (Bernstein_changes p c d P - proots_count P {x. c < x \<and> x < d})"
proof -
  define Q where "Q=P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d - c:]"

  have "int (proots_count Q {x. 0 < x \<and> x < 1}) 
          \<le> Bernstein_changes_01 p Q \<and>
              even (Bernstein_changes_01 p Q - 
                  int (proots_count Q {x. 0 < x \<and> x < 1}))"
    unfolding Q_def
    apply (rule Bernstein_changes_01_test)
    subgoal using assms by fastforce
    subgoal using assms by (auto simp: pcompose_eq_0)
    done
  moreover have "proots_count P {x. c < x \<and> x < d} =
            proots_count Q {x. 0 < x \<and> x < 1}"
    unfolding Q_def
  proof (subst proots_pcompose)
    have "poly [:c, 1:] ` poly [:0, d - c:] ` {x. 0 < x \<and> x < 1} =
        {x. c < x \<and> x < d}" (is "?L = ?R")
    proof
      have "c + x * (d - c) < d" if "x < 1" for x
      proof - 
        have "x * (d - c) < 1 * (d - c)"
          using \<open>c < d\<close> that by force
        then show ?thesis by fastforce
      qed
      then show "?L \<subseteq> ?R"
        using assms by auto
    next
      show "?R \<subseteq> ?L"
      proof
        fix x::real assume "x \<in> ?R"
        hence "c < x" and "x < d" by auto
        thus "x \<in> ?L"
        proof (subst image_eqI)
          show "x = poly [:c, 1:] (x - c)" by force
          assume "c < x" and "x < d"
          thus "x - c \<in> poly [:0, d - c:] ` {x. 0 < x \<and> x < 1}"
          proof (subst image_eqI)
            show "x - c = poly [:0, d - c:] ((x - c)/(d - c))"
              using assms by fastforce
            assume "c < x" and "x < d"
            thus "(x - c) / (d - c) \<in> {x. 0 < x \<and> x < 1}"
              by auto
          qed fast
        qed fast
      qed
    qed
    then show "proots_count P {x. c < x \<and> x < d} =
        proots_count (P \<circ>\<^sub>p [:c, 1:]) 
        (poly [:0, d - c:] ` {x. 0 < x \<and> x < 1})"
      using assms by (auto simp:proots_pcompose)
    show "P \<circ>\<^sub>p [:c, 1:] \<noteq> 0"
      by (simp add: pcompose_eq_0 assms(2))
    show "degree [:0, d - c:] = 1"
      using assms by auto
  qed
  moreover have " Bernstein_changes p c d P = Bernstein_changes_01 p Q"
    unfolding Q_def
    apply (rule Bernstein_changes_eq_rescale)
    using assms by auto
  ultimately show ?thesis by auto
qed

subsection \<open>The control polygon of a polynomial\<close>

definition control_points ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "control_points p c d P = 
   [(((real i)*d + (real (p - i))*c)/p, 
      nth_default 0 (Bernstein_coeffs p c d P) i).
      i \<leftarrow> [0..<(p+1)]]"

lemma line_above: 
  fixes a b c d :: real and p :: nat and P :: "real poly"
  assumes hline: "\<And>i. i \<le> p \<Longrightarrow> a * (((real i)*d + (real (p - i))*c)/p) + b \<ge>
                  nth_default 0 (Bernstein_coeffs p c d P) i"
  and hp: "p \<noteq> 0" and hcd: "c \<noteq> d" and hP: "degree P \<le> p"
  shows "\<And>x. c \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> a*x + b \<ge> poly P x"
proof -
  fix x
  assume hc: "c \<le> x" and  hd: "x \<le> d"

  have bern_eq:"Bernstein_coeffs p c d [:b, a:] =
           [a*(real i * d + real (p - i) * c)/p + b. i \<leftarrow> [0..<(p+1)]]"
  proof -
    have "Bernstein_coeffs p c d [:b, a:] = map (nth_default 0
          (Bernstein_coeffs_01 p ([:b, a:] \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d - c:])))
         [0..<p+1]"
      apply (subst Bernstein_coeffs_eq_rescale["OF" hcd])
      apply (subst map_nth_default[symmetric])
      apply (subst length_Bernstein_coeffs_01)
      by blast
    also have 
      "... = map (\<lambda>i. a * (real i * d + real (p - i) * c) / real p + b) [0..<p + 1]"
    proof (rule map_cong)
      fix x assume hx: "x \<in> set [0..<p + 1]"
      have "nth_default 0 (Bernstein_coeffs_01 p
            ([:b, a:] \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d - c:])) x =
            nth_default 0 (Bernstein_coeffs_01 p
            (smult (b + a*c) 1 + smult (a*(d - c)) (monom 1 1))) x"
      proof-
        have "[:b, a:] \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d - c:] =
                  smult (b + a*c) 1 + smult (a*(d - c)) (monom 1 1)"
          by (simp add: monom_altdef pcompose_pCons)
        then show ?thesis by auto
      qed
      also have "... = 
          nth_default 0 (Bernstein_coeffs_01 p (smult (b + a * c) 1)) x +
          nth_default 0 (Bernstein_coeffs_01 p (smult (a * (d - c)) (monom 1 1))) x"
        apply (subst Bernstein_coeffs_01_add)
        using hp by (auto simp: degree_monom_eq)
      also have "...  =
            (b + a*c) * nth_default 0 (Bernstein_coeffs_01 p 1) x +
            (a*(d - c)) * nth_default 0 (Bernstein_coeffs_01 p (monom 1 1)) x"
        apply (subst Bernstein_coeffs_01_smult)
        using hp by (auto simp: Bernstein_coeffs_01_smult degree_monom_eq)
      also have "... =
          (b + a * c) * (if x < p + 1 then 1 else 0) +
           a * (d - c) * (real (nth_default 0 [0..<p + 1] x) / real p)" 
        apply (subst Bernstein_coeffs_01_1, subst Bernstein_coeffs_01_x[OF hp])
        apply (subst nth_default_replicate_eq, subst nth_default_map_eq[of _ 0])
        by auto
      also have "... =
              (b + a * c) * (if x < p + 1 then 1 else 0) +
              a * (d - c) * (real ([0..<p + 1] ! x) / real p)"
        apply (subst nth_default_nth)
        using hx by auto
      also have "... = (b + a * c) * (if x < p + 1 then 1 else 0) +
              a * (d - c) * (real (0 + x) / real p)"
        apply (subst nth_upt)
        using hx by auto
      also have "... = a * (real x * d + real (p - x) * c) / real p + b"
        apply (subst of_nat_diff)
        using hx hp by (auto simp: field_simps)
      finally show "nth_default 0 (Bernstein_coeffs_01 p
                    ([:b, a:] \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, d - c:])) x =
                    a * (real x * d + real (p - x) * c) / real p + b" .
    qed blast
    finally show ?thesis .
  qed

  have nth_default_geq:"nth_default 0 (Bernstein_coeffs p c d [:b, a:]) i \<ge>
           nth_default 0 (Bernstein_coeffs p c d P) i" for i
  proof -
    show "nth_default 0 (Bernstein_coeffs p c d [:b, a:]) i \<ge>
          nth_default 0 (Bernstein_coeffs p c d P) i"
    proof cases
      define p1 where "p1 \<equiv> p+1"
      assume h: "i \<le> p"
      hence "nth_default 0 (Bernstein_coeffs p c d P) i \<le>
             a * (((real i)*d + (real (p - i))*c)/p) + b"
        by (rule hline)
      also have "... = nth_default 0 (map (\<lambda>i. a * (real i * d 
          + real (p - i) * c) / real p + b) [0..<p + 1]) i"
        apply (subst p1_def[symmetric])
        using h apply (auto simp: nth_default_def)
        by (auto simp: p1_def)
      also have "... = nth_default 0 (Bernstein_coeffs p c d [:b, a:]) i"
        using bern_eq by simp
      finally show ?thesis .
    next
      assume h: "\<not>i \<le> p"
      thus ?thesis
        using assms 
        by (auto simp: nth_default_def Bernstein_coeffs_eq_rescale
                        length_Bernstein_coeffs_01)
    qed
  qed
  
  have "poly P x = (\<Sum>k = 0..p.
        poly (smult (nth_default 0 (Bernstein_coeffs p c d P) k)
        (Bernstein_Poly k p c d)) x)"
    apply (subst Bernstein_coeffs_sum[OF hcd hP])
    by (rule poly_sum)
  also have "... \<le> (\<Sum>k = 0..p.
      poly (smult (nth_default 0 (Bernstein_coeffs p c d [:b, a:]) k)
        (Bernstein_Poly k p c d)) x)"
    apply (rule sum_mono)
    using mult_right_mono[OF nth_default_geq] Bernstein_Poly_nonneg[OF hc hd]
    by auto
  also have "... = poly [:b, a:] x"
    apply (subst(2) Bernstein_coeffs_sum[of c d "[:b, a:]" p])
    using assms apply auto[2]
    by (rule poly_sum[symmetric])
  also have "... = a*x + b" by force
  finally show "poly P x \<le> a*x + b" .
qed

end