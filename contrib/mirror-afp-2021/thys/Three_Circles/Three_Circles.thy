section \<open>Proof of the theorem of three circles\<close>

theory Three_Circles
  imports "Bernstein" "Normal_Poly"
begin

text \<open>
The theorem of three circles is a result in real algebraic geometry about the number of real roots
in an interval. It says if the number of roots in certain circles in the complex plane are zero or 
one then the number of roots in the circles is equal to the sign changes of the Bernstein
coefficients on that interval for which the circles intersect the real line. This can then be used
to determine if an interval has a real root in the bisection procedure, which is more efficient than
Descartes' rule of signs.

The proof here follows Theorem 10.50 in
  Basu, S., Pollack, R., Roy, M.-F.: Algorithms in Real Algebraic Geometry. 
  Springer Berlin Heidelberg, Berlin, Heidelberg (2016).

This theorem has also been fomalised in Coq \cite{zsido2014theorem}. The relationship
between this theorem and root isolation has been elaborated in Eigenwillig's PhD
thesis \cite{eigenwillig2008real}.
\<close>

subsection \<open>No sign changes case\<close>

declare degree_pcompose[simp del]

corollary descartes_sign_zero:
  fixes p::"real poly"
  assumes "\<And>x::complex. poly (map_poly of_real p) x = 0 \<Longrightarrow> Re x \<le> 0" 
    and "lead_coeff p = 1"
  shows "coeff p i \<ge> 0"
  using assms
proof (induction p arbitrary: i rule: real_poly_roots_induct)
  case (1 p x)
  interpret map_poly_idom_hom complex_of_real ..
  have h: "\<And> i. 0 \<le> coeff p i"
    apply (rule 1(1))
    using 1(2) apply (metis lambda_zero of_real_poly_map_mult poly_mult)
    using 1(3) apply (metis lead_coeff_1 lead_coeff_mult lead_coeff_pCons(1)
                      mult_cancel_right2 pCons_one zero_neq_one)
    done
  have "x \<le> 0"
    apply (subst Re_complex_of_real[symmetric])
    apply (rule 1(2))
    apply (subst hom_mult)
    by (auto)
  thus ?case
    apply (cases i)
    subgoal using h[of i] h[of "i-1"]
      by (fastforce simp: coeff_pCons mult_nonneg_nonpos2)
    subgoal using h[of i] h[of "i-1"] mult_left_mono_neg
      by (fastforce simp: coeff_pCons)
    done
next
  case (2 p a b)
  interpret map_poly_idom_hom complex_of_real ..
  have h: "\<And> i. 0 \<le> coeff p i"
    apply (rule 2(2))
    using 2(3) apply (metis lambda_zero of_real_poly_map_mult poly_mult)
    using 2(4) apply (metis lead_coeff_1 lead_coeff_mult lead_coeff_pCons(1)
                      mult_cancel_right2 pCons_one zero_neq_one)
    done
  have "Re (a + b * \<i>) \<le> 0"
    apply (rule 2(3))
    apply (subst hom_mult)
    by (auto simp: algebra_simps)
  hence 1: "0 \<le> - 2 * a" by fastforce
  have 2: "0 \<le> a * a + b * b" by fastforce
  have "\<And> x. 0 \<le> coeff [:a * a + b * b, - 2 * a, 1:] x"
  proof -
    fix x
    show "0 \<le> coeff [:a * a + b * b, - 2 * a, 1:] x"
      using 2 apply (cases "x = 0", fastforce)
      using 1 apply (cases "x = 1", fastforce)
      apply (cases "x = 2", fastforce simp: coeff_pCons)
      by (auto simp: coeff_eq_0)
  qed
  thus ?case
    apply (subst mult.commute, subst coeff_mult)
    apply (rule sum_nonneg, rule mult_nonneg_nonneg[OF _ h])
    by auto
next
  case (3 a)
  then show ?case
    by (smt (z3) bot_nat_0.extremum_uniqueI degree_1 le_degree
        lead_coeff_pCons(2) pCons_one)
qed

definition circle_01_diam :: "complex set" where
"circle_01_diam =
 {x. cmod (x - (of_nat 1 :: complex)/(of_nat 2)) < (real 1)/(real 2)}"

lemma pos_real_map:
  "{x::complex. 1 / x \<in> (\<lambda>x. x + 1) ` {x. 0 < Re x}} = circle_01_diam"
proof
  show "{x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. 0 < Re x}} \<subseteq> circle_01_diam"
  proof
    fix x assume "x \<in> {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. 0 < Re x}}"
    then obtain y where h: "1 / x = y + 1" and hy: "0 < Re y" by blast
    hence hy': "y = 1 / x - 1" by fastforce
    hence hy'': "y + 1 \<noteq> 0" using h hy by fastforce
    hence "x = 1 / (y + 1)" using h
      by (metis div_by_1 divide_divide_eq_right mult.left_neutral)
    have "\<bar>Re y - 1\<bar> < \<bar>Re y + 1\<bar>" using hy by simp
    hence "cmod (y - 1) < cmod (y + 1)"
      by (smt (z3) cmod_Re_le_iff minus_complex.simps(1) minus_complex.simps(2)
          one_complex.simps plus_complex.simps(1) plus_complex.simps(2))
    hence "cmod ((y - 1)/(y + 1)) < 1"
      by (smt (verit) divide_less_eq_1_pos nonzero_norm_divide zero_less_norm_iff)
    thus "x \<in> circle_01_diam" using hy' hy''
      by (auto simp: field_simps norm_minus_commute circle_01_diam_def)
  qed
  show "circle_01_diam \<subseteq> {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. 0 < Re x}}"
  proof
    fix x assume "x \<in> circle_01_diam"
    hence "cmod (x - 1 / 2) * 2 < 1" by (auto simp: circle_01_diam_def)
    hence h: "x \<noteq> 0" and "cmod (x - 1 / 2) * cmod 2 < 1" by auto
    hence "cmod (2*x - 1) < 1" 
      by (smt (verit) dbl_simps(3) dbl_simps(5) div_self times_divide_eq_left
          left_diff_distrib_numeral mult.commute mult_numeral_1
          norm_eq_zero norm_mult norm_numeral norm_one numeral_One)
    hence "cmod (((1/x - 1) -  1)/((1/x - 1) + 1)) < 1"
      by (auto simp: divide_simps norm_minus_commute)
    hence "cmod (((1/x - 1) -  1)/ cmod ((1/x - 1) + 1)) < 1"
      by (metis (no_types, lifting) abs_norm_cancel norm_divide norm_of_real)
    hence "cmod ((1/x - 1) - 1) < cmod ((1/x - 1) + 1)" using h
      by (smt (verit) diff_add_cancel divide_eq_0_iff divide_less_eq_1_pos
          norm_divide norm_of_real zero_less_norm_iff zero_neq_one)
    hence "\<bar>Re (1/x - 1) - 1\<bar> < \<bar>Re (1/x - 1) + 1\<bar>"
      by (smt (z3) cmod_Re_le_iff minus_complex.simps(1) minus_complex.simps(2)
          one_complex.simps plus_complex.simps(1) plus_complex.simps(2))
    hence "0 < Re (1/x - 1)" by linarith
    moreover have "1 / x = (1/x - 1) + 1" by simp
    ultimately have "0 < Re (1/x - 1) \<and> 1 / x = (1/x - 1) + 1" by blast
    hence "\<exists>xa. 0 < Re xa \<and> 1 / x = xa + 1" by blast
    thus "x \<in> {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. 0 < Re x}}" by blast
  qed
qed

lemma one_circle_01: fixes P::"real poly" assumes hP: "degree P \<le> p" and "P \<noteq> 0"
  and "proots_count (map_poly of_real P) circle_01_diam = 0"
shows "Bernstein_changes_01 p P = 0"
proof -
  let ?Q = "(reciprocal_poly p P) \<circ>\<^sub>p [:1, 1:]"
  have hQ: "?Q \<noteq> 0" 
    using assms 
    by (simp add: Missing_Polynomial.pcompose_eq_0 reciprocal_0_iff)

  hence 1: "changes (coeffs ?Q) \<ge> proots_count ?Q {x. 0 < x} \<and> 
        even (changes (coeffs ?Q) - proots_count ?Q {x. 0 < x})"
    by (rule descartes_sign)
    
  have hdeg: "degree (map_poly complex_of_real P) \<le> p"
    by (rule le_trans, rule degree_map_poly_le, auto simp: assms)
  have hx: "\<And>x. 1 + x = 0 \<Longrightarrow> 0 < Re x \<Longrightarrow> False"
  proof -
    fix x::complex assume "1 + x = 0"
    hence "x = -1" by algebra
    thus "0 < Re x \<Longrightarrow> False" by auto
  qed

  have 2: "proots_count (map_poly of_real P) circle_01_diam =
           proots_count (map_poly of_real ?Q) {x. 0 < Re x}"
    apply (subst pos_real_map[symmetric])
    apply (subst of_real_hom.map_poly_pcompose)
    apply (subst map_poly_reciprocal) using assms apply auto[2]
    apply (subst proots_pcompose)
    using assms apply (auto simp: reciprocal_0_iff degree_map_poly)[2]
    apply (subst proots_count_reciprocal)
    using assms apply (auto simp: degree_map_poly inverse_eq_divide)[2]
    using hx apply fastforce
    by (auto simp: inverse_eq_divide algebra_simps)

  hence 3:"proots_count (map_poly of_real ?Q) {x. 0 < Re x} = 0"
    using assms(3) by presburger

  hence "\<And>x::complex.
         poly (map_poly of_real (smult (inverse (lead_coeff ?Q)) ?Q)) x = 0 \<Longrightarrow>
         Re x \<le> 0"
  proof cases
    fix x::complex show "Re x \<le> 0 \<Longrightarrow> Re x \<le> 0" by fast 
    assume "\<not>Re x \<le> 0" hence h:"0 < Re x" by simp
    assume "poly (map_poly of_real (smult (inverse (lead_coeff ?Q)) ?Q)) x = 0"
    hence h2:"poly (map_poly of_real ?Q) x = 0" by fastforce 
    hence "order x (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) > 0" 
      using assms by (fastforce simp: order_root pcompose_eq_0 reciprocal_0_iff)
    hence "proots_count (map_poly of_real ?Q) {x. 0 < Re x} \<noteq> 0"
    proof -
      have h3: "finite {x. poly (map_poly complex_of_real 
                (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) x = 0}" 
        apply (rule poly_roots_finite)
        using assms by (fastforce simp: order_root pcompose_eq_0 reciprocal_0_iff)
      have "0 < order x (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))"
        using h2 assms by (fastforce simp: order_root pcompose_eq_0 reciprocal_0_iff)
      also have "... \<le> (\<Sum>r\<in>{x. 0 < Re x \<and>
                  poly (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) x =
                  0}.
           order r (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])))" 
        apply (rule member_le_sum) using h h2 h3 by auto
      finally have 
        "0 < (\<Sum>r\<in>{x. 0 < Re x \<and>
         poly (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) x = 0}.
         order r (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])))" .
      thus 
        "0 < order x (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) \<Longrightarrow>
         proots_count (map_poly complex_of_real (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))
         {x. 0 < Re x} \<noteq> 0 "
        by (auto simp: proots_count_def proots_within_def)
    qed
    thus "Re x \<le> 0" using 3 by blast
  qed
  hence "\<And>i. coeff (smult (inverse (lead_coeff ?Q)) ?Q) i \<ge> 0"
    apply (frule descartes_sign_zero)
    using assms by (fastforce simp: pcompose_eq_0 reciprocal_0_iff)
  hence "changes (coeffs (smult (inverse (lead_coeff ?Q)) ?Q)) = 0"
    by (subst changes_all_nonneg, auto simp: nth_default_coeffs_eq)
  hence "changes (coeffs ?Q) = 0"
    using hQ by (auto simp: coeffs_smult changes_scale_const)

  thus ?thesis
    apply (subst Bernstein_changes_01_eq_changes["OF" hP]) 
    by blast
qed

definition circle_diam :: "real \<Rightarrow> real \<Rightarrow> complex set" where
"circle_diam l r = {x. cmod ((x - l) - (r - l)/2) < (r - l)/2}"

lemma circle_diam_rescale: assumes "l < r"
  shows "circle_diam l r = (\<lambda> x . (x*(r - l) + l)) ` circle_01_diam"
proof
  show "circle_diam l r \<subseteq> (\<lambda>x. x * (complex_of_real r - complex_of_real l) +
        complex_of_real l) ` circle_01_diam"
  proof
    fix x assume "x \<in> circle_diam l r"
    hence "cmod ((x - l) - (r - l)/2) < (r - l)/2" by (auto simp: circle_diam_def)
    hence "cmod ((r - l) * ((x - l)/(r - l) - 1/2)) < (r - l)/2" using assms
      by (subst right_diff_distrib, fastforce)
    hence "(r - l) * cmod ((x - l)/(r - l) - 1/2) < (r - l) * 1/2"
      apply (subst(2) abs_of_pos[symmetric])
      subgoal using assms by argo
      subgoal 
        apply (subst norm_scaleR[symmetric])
        by (simp add: scaleR_conv_of_real)
      done
    hence "cmod ((x - l)/(r - l) - 1/2) < 1/2"
      apply (subst mult_less_cancel_left_pos[of "r-l",symmetric])
      using assms by auto
    hence
      "cmod ((x-l)/(r-l) - 1 / 2) * 2 < 1 \<and>
       x = (x-l)/(r-l) * (complex_of_real r - complex_of_real l) + complex_of_real l"
      by force
    thus "x \<in> (\<lambda>x. x * (complex_of_real r - complex_of_real l) + complex_of_real l) `
          circle_01_diam"
      by (force simp: circle_01_diam_def)
  qed
  show "(\<lambda>x. x * (complex_of_real r - complex_of_real l) + complex_of_real l) `
        circle_01_diam \<subseteq> circle_diam l r"
  proof
    fix x::complex
    assume
      "x \<in> (\<lambda>x. x * (complex_of_real r - complex_of_real l) + complex_of_real l) `
       circle_01_diam"
    then obtain y::complex where "x = y * (r - l) + l" "cmod (y - 1/2) < 1/2"
      by (fastforce simp: circle_01_diam_def)
    moreover hence "y = (x - l) / (r - l)" using assms by force
    ultimately have "cmod ((x - l) / (r - l) - 1/2) < 1/2" by presburger
    hence "(r - l) * (cmod ((x - l) / (r - l) - 1/2)) < (r - l) * (1/2)"
      apply (subst mult_less_cancel_left_pos)
      using assms by auto
    hence "cmod ((x - l) - (r - l)/2) < (r - l)/2"
      apply (subst(asm) (2) abs_of_pos[symmetric])
      using assms apply argo
      apply (subst(asm) norm_scaleR[symmetric])
      by (smt (verit, del_insts)
          \<open>x = y * complex_of_real (r - l) + complex_of_real l\<close>
          \<open>y = (x - complex_of_real l) / complex_of_real (r - l)\<close>
          add_diff_cancel divide_divide_eq_right divide_numeral_1 mult.commute
          of_real_1 of_real_add of_real_divide one_add_one scaleR_conv_of_real
          scale_right_diff_distrib times_divide_eq_right)
    thus "x \<in> circle_diam l r"
      by (force simp: circle_diam_def)
  qed
qed

lemma one_circle: fixes P::"real poly" assumes "l < r"
  and "proots_count (map_poly of_real P) (circle_diam l r) = 0"
  and "P \<noteq> 0"
  and "degree P \<le> p"
shows "Bernstein_changes p l r P = 0"
proof (subst Bernstein_changes_eq_rescale)
  show "l \<noteq> r" using assms(1) by force
  show "degree P \<le> p" using assms(4) by blast
  show "Bernstein_changes_01 p (P \<circ>\<^sub>p [:l, 1:] \<circ>\<^sub>p [:0, r - l:]) = 0"
  proof (rule one_circle_01)
    show "degree (P \<circ>\<^sub>p [:l, 1:] \<circ>\<^sub>p [:0, r - l:]) \<le> p"
      using assms(4) by (force simp: degree_pcompose)
    show "P \<circ>\<^sub>p [:l, 1:] \<circ>\<^sub>p [:0, r - l:] \<noteq> 0"
      using assms by (smt (z3) degree_0_iff gr_zeroI pCons_eq_0_iff pCons_eq_iff
                      pcompose_eq_0)

    have "proots_count (map_poly of_real P) (circle_diam l r) = 
          proots_count (map_poly complex_of_real (P \<circ>\<^sub>p [:l, 1:] \<circ>\<^sub>p [:0, r - l:]))
          circle_01_diam"
      apply (subst of_real_hom.map_poly_pcompose)
      apply (subst proots_pcompose)
        apply (metis assms(3) degree_eq_zeroE of_real_poly_eq_0_iff
          pCons_eq_iff pCons_one pcompose_eq_0 zero_neq_one)
      using assms(1) apply fastforce
      apply (subst of_real_hom.map_poly_pcompose)
      apply (subst proots_pcompose)
        apply (auto simp: assms(3))[2]
      apply (subst circle_diam_rescale[OF assms(1)])
      apply (rule arg_cong[of _ _ "proots_count (map_poly complex_of_real P)"])
      by fastforce

    thus "proots_count (map_poly complex_of_real (P \<circ>\<^sub>p [:l, 1:] \<circ>\<^sub>p [:0, r - l:]))
          circle_01_diam = 0"
      using assms(2) by presburger
  qed
qed

subsection \<open>One sign change case\<close>

definition upper_circle_01 :: "complex set" where
"upper_circle_01 = {x. cmod (x - (1/2 + sqrt(3)/6 * \<i>)) < sqrt 3 / 3}"

lemma upper_circle_map:
  "{x::complex. 1 / x \<in> (\<lambda>x. x + 1) ` {x. Im x < sqrt 3 * Re x}} = upper_circle_01"
proof
  show "{x::complex. 1 / x \<in> (\<lambda>x. x + 1) ` {x. Im x < sqrt 3 * Re x}} \<subseteq> upper_circle_01"
  proof
    fix x
    assume "x \<in> {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. Im x < sqrt 3 * Re x}}"
    then obtain y where "1 / x = y + 1" and h: "Im y < sqrt 3 * Re y" by fastforce
    hence hy: "y = 1/x - 1" by simp
    hence hx: "x = 1/(y+1)" by auto
    from h have hy1: "y \<noteq> -1" by fastforce
    hence hx0: "x \<noteq> 0" using hy by fastforce
    from h have "0 < Re ((\<i> + sqrt 3) * y)" by fastforce
    hence "cmod ((\<i> + sqrt 3) * y - 1) < cmod ((\<i> + sqrt 3) * y + 1)"
      by (auto simp: cmod_def power2_eq_square algebra_simps)
    hence 1: "cmod (((\<i> + sqrt 3) * y - 1)/((\<i> + sqrt 3) * y + 1)) < 1"
      by (auto simp: norm_divide divide_simps)
    also have "cmod (((\<i> + sqrt 3) * y - 1)/((\<i> + sqrt 3) * y + 1)) =
               cmod (((\<i> + sqrt 3) * y * x - x)/((\<i> + sqrt 3) * y * x + x))"
      apply (subst mult_divide_mult_cancel_right[symmetric, OF hx0])
      apply (subst ring_distribs(2)[of _ _ x])
      apply (subst left_diff_distrib[of _ _ x])
      by simp
    also have "... = cmod
       (((-1 - complex_of_real (sqrt 3) - \<i>) * x + (complex_of_real (sqrt 3) + \<i>)) /
       (( 1 - complex_of_real (sqrt 3) - \<i>) * x + (complex_of_real (sqrt 3) + \<i>)))"
      by (auto simp: hy algebra_simps hx0)

    also have 
      "... = cmod ((-1 - complex_of_real (sqrt 3) - \<i>) * x +
                   (complex_of_real (sqrt 3) + \<i>)) /
             cmod (( 1 - complex_of_real (sqrt 3) - \<i>) * x +
                   (complex_of_real (sqrt 3) + \<i>))"
      by (auto simp: norm_divide)
    
    finally have 
      "cmod ((-1 - complex_of_real (sqrt 3) - \<i>) * x + (complex_of_real (sqrt 3) + \<i>))
       < cmod ((1 - complex_of_real (sqrt 3) - \<i>) * x + (complex_of_real (sqrt 3) + \<i>))"
    proof (subst divide_less_eq_1_pos[symmetric], subst zero_less_norm_iff)
      show "(1 - complex_of_real (sqrt 3) - \<i>) * x + (complex_of_real (sqrt 3) + \<i>) \<noteq> 0"
      proof
        have "-\<i> + 1 \<noteq> complex_of_real (sqrt 3)" by (auto simp: complex_eq_iff)
        moreover assume
          "(1 - complex_of_real (sqrt 3) - \<i>) * x + (complex_of_real (sqrt 3) + \<i>) = 0"
        ultimately have
          "x = (-complex_of_real (sqrt 3) - \<i>)/(1 - complex_of_real (sqrt 3) - \<i>)"
          by (auto simp: divide_simps algebra_simps)
        thus False
          using h by (auto simp: hy field_simps Im_divide Re_divide)
      qed
    qed

    hence "cmod (x - (1/2 + sqrt(3)/6 * \<i>)) < sqrt 3 / 3"
      apply (subst(3) abs_of_pos[symmetric, of 3]) apply auto[1]
      apply (subst real_sqrt_abs2[symmetric], subst real_sqrt_divide[symmetric])
      apply (subst cmod_def, subst real_sqrt_less_iff)
      apply (rule mult_right_less_imp_less[of _ "sqrt 3 /3"])
      by (auto simp: cmod_def power2_eq_square algebra_simps)

    thus "x \<in> upper_circle_01"
      by (auto simp: upper_circle_01_def)
  qed

  show "upper_circle_01 \<subseteq> {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. sqrt 3 * Re x > Im x}}"
  proof
    fix x assume "x \<in> upper_circle_01"
    hence "cmod (x - (1/2 + sqrt(3)/6 * \<i>)) < sqrt 3 / 3"
      by (force simp: upper_circle_01_def)
    hence "sqrt ((Re x - 1/2)^2 + (Im x - sqrt(3)/6)^2) < sqrt (1/3)"
      by (auto simp: cmod_def sqrt_divide_self_eq real_sqrt_inverse[symmetric])
    hence 1: "- Im x * sqrt 3 + (Im x * (Im x * 3) + Re x * (Re x * 3)) < Re x * 3"
      by (auto simp: power2_eq_square algebra_simps)
    have 2: "- Im x + (Im x * (Im x * sqrt 3) + Re x * (Re x * sqrt 3)) < Re x * sqrt 3"
      apply (rule mult_right_less_imp_less[of _ "sqrt 3"])
       apply (subst mult.assoc[of _ "sqrt 3"], subst real_sqrt_mult_self)
      using 1 by (auto simp: algebra_simps)
    have "sqrt 3 + (-Im x) / (Im x * Im x + Re x * Re x) <
          Re x * sqrt 3 / (Im x * Im x + Re x * Re x)"
      apply (rule mult_right_less_imp_less[of _ "(Im x * Im x + Re x * Re x)"])
       apply (rule subst, rule arg_cong2[of _ _ _ _ "(<)"])
         prefer 3 apply (rule 2)
        apply (subst distrib_right)
      using 2 apply auto
      by (auto simp: algebra_simps)

    hence "0 < - Im (1/x-1) + sqrt 3 * Re (1/x-1)"
      by (auto simp: power2_eq_square algebra_simps Re_divide Im_divide)
    hence "sqrt 3 * Re (1/x-1) > Im (1/x-1)"
      by argo
    hence "(1/x-1) \<in> {x. sqrt 3 * Re x > Im x}" by fast
    moreover have "1/x = (1/x-1) + 1" by simp
    ultimately show "x \<in> {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. sqrt 3 * Re x > Im x}}"
      by blast
  qed
qed

definition lower_circle_01 :: "complex set" where
"lower_circle_01 = {x. cmod (x - (1/2 - sqrt(3)/6 * \<i>)) < sqrt 3 / 3}"

lemma cnj_upper_circle_01: "cnj ` upper_circle_01 = lower_circle_01"
proof
  show "cnj ` upper_circle_01 \<subseteq> lower_circle_01"
  proof
    fix x assume "x \<in> cnj ` upper_circle_01"
    then obtain y where "y \<in> upper_circle_01" and "x = cnj y" by blast
    thus "x \<in> lower_circle_01"
      apply (subst lower_circle_01_def, subst complex_mod_cnj[symmetric])
      by (auto simp add: upper_circle_01_def del: complex_mod_cnj)
  qed
  show "lower_circle_01 \<subseteq> cnj ` upper_circle_01"
  proof
    fix x assume "x \<in> lower_circle_01"
    hence "cnj x \<in> upper_circle_01" and "x = cnj (cnj x)"
      apply (subst upper_circle_01_def, subst complex_mod_cnj[symmetric])
      by (auto simp add: lower_circle_01_def del: complex_mod_cnj)
    thus "x \<in> cnj ` upper_circle_01"
      by blast
  qed
qed

lemma lower_circle_map:
  "{x::complex. 1 / x \<in> (\<lambda>x. x + 1) ` {x. Im x > - sqrt 3 * Re x}} = lower_circle_01"
proof (subst cnj_upper_circle_01[symmetric], subst upper_circle_map[symmetric])
  have "{x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. - sqrt 3 * Re x < Im x}} = 
        {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. sqrt 3 * Re (cnj x) > Im (cnj x)}}"
    by auto
  also have "... = {x. 1 / x \<in> (\<lambda>x. x + 1) ` cnj ` {x. sqrt 3 * Re x > Im x}}"
    apply (subst(2) bij_image_Collect_eq)
     apply (metis bijI' complex_cnj_cnj)
    by (auto simp: inj_def inj_imp_inv_eq[of _ cnj])
  also have "... = {x. 1 / x \<in> cnj ` (\<lambda>x. x + 1) ` {x. sqrt 3 * Re x > Im x}}"
    by (auto simp: image_image)
  also have "... = {x. cnj (1 / x) \<in> (\<lambda>x. x + 1) ` {x. sqrt 3 * Re x > Im x}}"
    by (metis (no_types, lifting) complex_cnj_cnj image_iff)
  also have "... = cnj ` {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. sqrt 3 * Re x > Im x}}"
    apply (subst(2) bij_image_Collect_eq)
     apply (metis bijI' complex_cnj_cnj)
    by (auto simp: inj_def inj_imp_inv_eq[of _ cnj])
  finally show "{x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. - sqrt 3 * Re x < Im x}} =
          cnj ` {x. 1 / x \<in> (\<lambda>x. x + 1) ` {x. Im x < sqrt 3 * Re x}}" .
qed

lemma two_circles_01: 
  fixes P::"real poly" 
  assumes hP: "degree P \<le> p" and hP0: "P \<noteq> 0" and hp0: "p \<noteq> 0"
  and h: "proots_count (map_poly of_real P) 
          (upper_circle_01 \<union> lower_circle_01) = 1"
shows "Bernstein_changes_01 p P = 1"
proof (subst Bernstein_changes_01_eq_changes[OF hP])
  let ?Q = "reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]"
  have hQ0: "?Q \<noteq> 0" using hP0
    by (simp add: pcompose_eq_0 hP reciprocal_0_iff)

  from h obtain x' where hroot': "poly (map_poly of_real P) x' = 0"
    and hx':"x' \<in> upper_circle_01 \<union> lower_circle_01"
    using proots_count_pos by (metis less_numeral_extra(1))

  obtain x where hxx': "x' = complex_of_real x"
  proof (cases "Im x' = 0")
    assume "Im x' = 0" and h: "\<And>x. x' = complex_of_real x \<Longrightarrow> thesis"
    then show thesis using h[of "Re x'"] by (simp add: complex_is_Real_iff)
  next
    assume hx'': "Im x' \<noteq> 0"
    have 1: "card {x', cnj x'} = 2"
    proof (subst card_2_iff)
      from hx'' have "x' \<noteq> cnj x'" and "{x', cnj x'} = {x', cnj x'}" 
        by (metis cnj.simps(2) neg_equal_zero, argo)
      thus "\<exists>x y. {x', cnj x'} = {x, y} \<and> x \<noteq> y" by blast
    qed
    moreover have "{x', cnj x'} \<subseteq> upper_circle_01 \<union> lower_circle_01" using hx'
      apply (rule UnE)
      by (auto simp: cnj_upper_circle_01[symmetric])
    moreover have "\<And>x. x \<in> {x', cnj x'} \<Longrightarrow> poly (map_poly of_real P) x = 0"
      using hroot' poly_map_poly_of_real_cnj by auto
    ultimately have
      "proots_count (map_poly of_real P) (upper_circle_01 \<union> lower_circle_01) \<ge> 2"
      apply (subst 1[symmetric])
      apply (rule proots_count_of_root_set)
      using assms(2) of_real_poly_eq_0_iff by (blast, blast, blast)
    thus thesis using assms(4) by linarith
  qed
  hence hroot: "poly P x = 0"
    using hroot' by (metis of_real_0 of_real_eq_iff of_real_poly_map_poly)
  have that: "3 * sqrt (x * x + 1 / 3 - x) < sqrt 3" using hx'
    apply (rule UnE) 
    by (auto simp: cmod_def power2_eq_square algebra_simps upper_circle_01_def
        lower_circle_01_def hxx')
  have hx: "0 < x \<and> x < 1"
  proof -
    have "3 * sqrt (x * x + 1 / 3 - x) = sqrt (9 * (x * x + 1 / 3 - x))"
      by (subst real_sqrt_mult, simp)
    hence "9 * (x * x + 1 / 3 - x) < 3" using that real_sqrt_less_iff by metis
    hence "x*x - x < 0" by auto
    thus "0 < x \<and> x < 1"
      using mult_eq_0_iff mult_less_cancel_right_disj by fastforce
  qed

  let ?y = "1/x - 1"
  from hroot hx assms have "poly ?Q ?y = 0"
    by (auto simp: poly_pcompose poly_reciprocal)
  hence "[:-?y, 1:] dvd ?Q" using poly_eq_0_iff_dvd by blast
  then obtain R where hR: "?Q = R * [:-?y, 1:]" by auto
  hence hR0: "R \<noteq> 0" using hQ0 by force
  interpret map_poly_idom_hom complex_of_real ..


  have "normal_poly (smult (inverse (lead_coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))) R)"
  proof (rule normal_poly_of_roots)
    show "\<And>z. poly (map_poly complex_of_real
          (smult (inverse (lead_coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))) R)) z = 0 \<Longrightarrow>
          Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2"
    proof -
      fix z
      assume
        "poly (map_poly complex_of_real
         (smult (inverse (lead_coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))) R)) z = 0"
      hence hroot2: "poly (map_poly complex_of_real R) z = 0"
        by (auto simp: map_poly_smult hQ0)
      show "Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2"
      proof (rule ccontr)
        assume "\<not> (Re z \<le> 0 \<and> (cmod z)\<^sup>2 \<le> 4 * (Re z)\<^sup>2)"
        hence 1: "0 < Re z \<or> 4 * (Re z)\<^sup>2 < (cmod z)\<^sup>2" by linarith
        hence hz: "z \<noteq> -1" by force
        have "Im z > - sqrt 3 * Re z \<or> sqrt 3 * Re z > Im z"
        proof (cases "Im z \<ge> sqrt 3 * Re z", cases "- sqrt 3 * Re z \<ge> Im z")
          assume 2: "sqrt 3 * Re z \<le> Im z" "Im z \<le> - sqrt 3 * Re z"
          hence "sqrt 3 * Re z \<le> sqrt 3 * - Re z" by force
          hence "Re z \<le> - Re z"
            apply (rule mult_left_le_imp_le)
            by fastforce
          hence "Re z \<le> 0" by simp
          moreover have "(Im z)^2 \<le> (-sqrt 3 * Re z)^2"
            apply (subst power2_eq_square, subst power2_eq_square)
            apply (rule square_bounded_le)
            using 2 by auto
          ultimately have False using 1 
            by (auto simp: power2_eq_square cmod_def algebra_simps)
          thus ?thesis by fast
        qed auto

        hence "z \<in> {z. - sqrt 3 * Re z < Im z} \<union> {z. Im z < sqrt 3 * Re z}"
          by blast

        hence 1: "inverse (1 + z) \<in> upper_circle_01 \<union> lower_circle_01"
          by (force simp: inverse_eq_divide upper_circle_map[symmetric]
              lower_circle_map[symmetric])
        
        have hRdeg': "degree R < p"
          apply (rule less_le_trans[of "degree R" "degree ?Q"])
           apply (subst hR, subst degree_mult_eq[OF hR0], fastforce, fastforce)
          by (auto simp: degree_pcompose degree_reciprocal hP)
        hence hRdeg: "degree R \<le> p" by fastforce
        have 2: "map_poly complex_of_real (reciprocal_poly p (R \<circ>\<^sub>p [:-1, 1:])) \<noteq> 0"
          apply (subst of_real_poly_eq_0_iff, subst reciprocal_0_iff)
           apply (force simp: hRdeg degree_pcompose)
          using hR0 pcompose_eq_0
          by (metis degree_eq_zeroE gr_zeroI pCons_eq_iff pCons_one zero_neq_one)
        have 3: 
          "poly (map_poly complex_of_real (reciprocal_poly p (R \<circ>\<^sub>p [:-1, 1:])))
                 (inverse (1 + z)) = 0"
          apply (subst map_poly_reciprocal)
          using hRdeg apply (force simp: degree_pcompose)
           apply auto[1]
          apply (subst poly_reciprocal)
          using hRdeg apply (force simp: degree_map_poly degree_pcompose)
          using hz apply (metis inverse_nonzero_iff_nonzero neg_eq_iff_add_eq_0)
          by (auto simp: of_real_hom.map_poly_pcompose poly_pcompose hroot2)
        
        have "proots_count (map_poly of_real (reciprocal_poly p (R \<circ>\<^sub>p [:-1, 1:])))
               (upper_circle_01 \<union> lower_circle_01) > 0"
          by (rule proots_count_of_root[OF 2 1 3])
        moreover have "proots_count
                     (map_poly complex_of_real
                     (reciprocal_poly p ([:1 - 1 / x, 1:] \<circ>\<^sub>p [:- 1, 1:])))
                     (upper_circle_01 \<union> lower_circle_01) > 0"
          apply (subst map_poly_reciprocal)
            using hp0 less_eq_Suc_le apply (simp add: degree_pcompose)
           apply simp
            apply (subst proots_count_reciprocal)
            using hp0 less_eq_Suc_le
               apply (simp add: degree_pcompose degree_map_poly)
              apply (auto simp: pcompose_pCons)[1]
             apply (auto simp: cmod_def power2_eq_square real_sqrt_divide
                    real_div_sqrt upper_circle_01_def lower_circle_01_def)[1]
            apply (subst of_real_hom.map_poly_pcompose)
            apply (subst proots_pcompose, fastforce, force)
            apply (subst lower_circle_map[symmetric])
            apply (subst upper_circle_map[symmetric])
            apply (rule proots_count_of_root[of _ "of_real (1/x - 1)"])
              apply simp
             apply (auto simp: bij_image_Collect_eq bij_def inj_def image_iff
                    inverse_eq_divide inj_imp_inv_eq[of _ "\<lambda> x. x+1"] hx)[1]
            by force

          ultimately have "proots_count
                 (map_poly complex_of_real (reciprocal_poly p (R \<circ>\<^sub>p [:- 1, 1:])))
                 (upper_circle_01 \<union> lower_circle_01) +
            proots_count
             (map_poly complex_of_real
               (reciprocal_poly p ([:1 - 1 / x, 1:] \<circ>\<^sub>p [:- 1, 1:])))
             (upper_circle_01 \<union> lower_circle_01) > 1"
          by fastforce
        also have "... = proots_count (map_poly complex_of_real
                   (monom 1 p * reciprocal_poly p (?Q \<circ>\<^sub>p [:- 1, 1:])))
           (upper_circle_01 \<union> lower_circle_01)"
          apply (subst eq_commute, subst hR, subst pcompose_mult)
          apply (subst reciprocal_mult, subst degree_mult_eq)
          using hR0 apply (fastforce simp: pcompose_eq_0)
              apply (fastforce simp: pcompose_pCons)
          using hRdeg' apply (simp add: degree_pcompose)
          using hRdeg apply (simp add: degree_pcompose)
          using hp0 apply (auto simp: degree_pcompose)[1]
          apply (subst hom_mult)
          apply (subst proots_count_times)
          using hp0 hRdeg' hR0
          apply (fastforce simp: reciprocal_0_iff degree_pcompose pcompose_eq_0
                 pcompose_pCons)
          by simp
        also have "... = proots_count
           (map_poly complex_of_real
             (reciprocal_poly p (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:] \<circ>\<^sub>p [:- 1, 1:])))
           (upper_circle_01 \<union> lower_circle_01)"
          apply (subst hom_mult)
          apply (subst proots_count_times)
          using hp0 hP hP0 
           apply (auto simp: map_poly_reciprocal degree_pcompose
                  degree_reciprocal of_real_hom.map_poly_pcompose
                  reciprocal_0_iff degree_map_poly pcompose_eq_0)[1]
          apply (subst map_poly_monom, fastforce) 
          apply (subst of_real_1, subst proots_count_monom)
           apply (auto simp: cmod_def power2_eq_square real_sqrt_divide
                  real_div_sqrt upper_circle_01_def lower_circle_01_def)[1]
          by presburger
        also have "... = 1"
          by (auto simp: pcompose_assoc["symmetric"] pcompose_pCons
              reciprocal_reciprocal hP h)
        finally show False by blast
      qed
    qed
   show "lead_coeff
         (smult (inverse (lead_coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]))) R) = 1"
      by (auto simp: hR degree_add_eq_right hR0 coeff_eq_0)
  qed

  hence "changes (coeffs (smult (inverse (lead_coeff ?Q)) ?Q)) = 1"
    apply (subst hR, subst mult_smult_left[symmetric], rule normal_changes)
    by (auto simp: hx)
  
  moreover have "changes (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) =
      changes (coeffs (smult (inverse (lead_coeff (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])))
        (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])))"
    by (auto simp: pcompose_eq_0 reciprocal_0_iff hP hP0 coeffs_smult
        changes_scale_const[symmetric])

  ultimately show "changes (coeffs (reciprocal_poly p P \<circ>\<^sub>p [:1, 1:])) = 1" by argo
qed

definition upper_circle :: "real \<Rightarrow> real \<Rightarrow> complex set" where
"upper_circle l r = {x::complex.
  cmod ((x-of_real l)/(of_real (r-l)) - (1/2 + of_real (sqrt(3))/6 * \<i>)) < sqrt 3 / 3}"

lemma upper_circle_rescale: assumes "l < r"
  shows "upper_circle l r = (\<lambda> x . (x*(r - l) + l)) ` upper_circle_01"
proof
  show "upper_circle l r \<subseteq>
        (\<lambda>x. x * (of_real r - of_real l) + of_real l) ` upper_circle_01"
    apply (rule subsetI)
    apply (rule image_eqI[of _ _ "(_ - of_real l)/(of_real r - of_real l)"])
    using assms apply (auto simp: divide_simps)[1]
    by (auto simp: upper_circle_01_def upper_circle_def)
  show "(\<lambda>x. x * (of_real r - of_real l) + of_real l) ` upper_circle_01 \<subseteq>
        upper_circle l r"
    apply (rule subsetI, subst(asm) image_iff)
    using assms by (auto simp: upper_circle_01_def upper_circle_def)
qed

definition lower_circle :: "real \<Rightarrow> real \<Rightarrow> complex set" where
"lower_circle l r = {x::complex.
 cmod ((x-of_real l)/(of_real (r-l)) - (1/2 - of_real (sqrt(3))/6 * \<i>)) < sqrt 3 / 3}"

lemma lower_circle_rescale: 
  assumes "l < r"
  shows "lower_circle l r = (\<lambda> x . (x*(r - l) + l)) ` lower_circle_01"
proof
  show "lower_circle l r \<subseteq> (\<lambda>x. x * (of_real r - of_real l) + of_real l) `
        lower_circle_01"
    apply (rule subsetI)
    apply (rule image_eqI[of _ _ "(_ - of_real l)/(of_real r - of_real l)"])
    using assms apply (auto simp: divide_simps)[1]
    by (auto simp: lower_circle_01_def lower_circle_def)
  show "(\<lambda>x. x * (of_real r - of_real l) + of_real l) ` lower_circle_01 \<subseteq>
        lower_circle l r"
    apply (rule subsetI, subst(asm) image_iff)
    using assms by (auto simp: lower_circle_01_def lower_circle_def)
qed

lemma two_circles: 
  fixes P::"real poly" and l r::real 
  assumes hlr: "l < r"
  and hP: "degree P \<le> p" 
  and hP0: "P \<noteq> 0" 
  and hp0: "p \<noteq> 0"
  and h: "proots_count (map_poly of_real P) 
       (upper_circle l r \<union> lower_circle l r) = 1"
shows "Bernstein_changes p l r P = 1"
proof -
  have 1: "Bernstein_changes p l r P =
           Bernstein_changes_01 p (P \<circ>\<^sub>p [:l, 1:] \<circ>\<^sub>p [:0, r - l:])"
    using assms by (force simp: Bernstein_changes_eq_rescale)
  have "proots_count (map_poly complex_of_real (P \<circ>\<^sub>p [:l, 1:] \<circ>\<^sub>p [:0, r - l:]))
     (upper_circle_01 \<union> lower_circle_01) = 1"
    using assms
    by (auto simp: upper_circle_rescale lower_circle_rescale proots_pcompose image_Un
        of_real_hom.map_poly_pcompose pcompose_eq_0 image_image algebra_simps)
  thus ?thesis
    apply (subst 1)
    apply (rule two_circles_01)
    using hP apply (force simp: degree_pcompose)
    using hP0 hlr apply (fastforce simp: pcompose_eq_0)
    using hp0 apply blast
    by blast
qed

subsection \<open>The theorem of three circles\<close>

theorem three_circles: 
  fixes P::"real poly" and l r::real
  assumes "l < r"
  and hP: "degree P \<le> p" 
  and hP0: "P \<noteq> 0" 
  and hp0: "p \<noteq> 0"
shows "proots_count (map_poly of_real P) (circle_diam l r) = 0 \<Longrightarrow>
       Bernstein_changes p l r P = 0"
  and "proots_count (map_poly of_real P) 
       (upper_circle l r \<union> lower_circle l r) = 1 \<Longrightarrow>
       Bernstein_changes p l r P = 1"
  apply (rule one_circle)
  using assms apply auto[4]
  apply (rule two_circles)
  using assms by auto

end