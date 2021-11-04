section \<open>Algorithms to compute all complex and real roots of a quartic polynomial\<close>

theory Quartic_Polynomials
  imports 
    Ferraris_Formula
    Cubic_Polynomials
begin

text \<open>The complex case is straight-forward\<close>

definition solve_depressed_quartic_complex :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex list" where
  "solve_depressed_quartic_complex p q r = remdups (if q = 0 then 
     (concat (map (\<lambda> z. let y = csqrt z in [y,-y]) (croots2 [:r,p,1:]))) else
     let cubics = croots3 [: - (q^2), 2 * p^2 - 8 * r, 8 * p, 8:];
         m = hd cubics; \<comment> \<open>select any root of the cubic polynomial\<close>
         a = csqrt (2 * m);
         p2m = p / 2 + m;
         q2a = q / (2 * a);
         b1 = p2m - q2a;
         b2 = p2m + q2a
       in (croots2 [:b1,a,1:] @ croots2 [:b2,-a,1:]))" 

lemma solve_depressed_quartic_complex: "x \<in> set (solve_depressed_quartic_complex p q r) 
  \<longleftrightarrow> (x^4 + p * x^2 + q * x + r = 0)"
proof -
  note powers = field_simps power4_eq_xxxx power3_eq_cube power2_eq_square
  show ?thesis
  proof (cases "q = 0")
    case True
    have csqrt: "z = x^2 \<longleftrightarrow> (x = csqrt z \<or> x = - csqrt z)" for z 
      by (metis power2_csqrt power2_eq_iff)
    have "(x ^ 4 + p * x\<^sup>2 + q * x + r = 0) \<longleftrightarrow> (x ^ 4 + p * x\<^sup>2 + r = 0)" 
      unfolding True by simp
    also have "\<dots> \<longleftrightarrow> (\<exists>z. z\<^sup>2 + p * z + r = 0 \<and> z = x\<^sup>2)" unfolding biquadratic_solution by simp
    also have "\<dots> \<longleftrightarrow> (\<exists> z. poly [:r,p,1:] z = 0 \<and> z = x^2)" 
      by (simp add: powers)
    also have "\<dots> \<longleftrightarrow> (\<exists> z \<in> set (croots2 [:r,p,1:]). z = x^2)" 
      by (subst croots2[symmetric], auto)
    also have "\<dots> \<longleftrightarrow> (\<exists> z \<in> set (croots2 [:r,p,1:]). x = csqrt z \<or> x = - csqrt z)" 
      unfolding csqrt ..
    also have "\<dots> \<longleftrightarrow> (x \<in> set (solve_depressed_quartic_complex p q r))" 
      unfolding solve_depressed_quartic_complex_def id unfolding True Let_def by auto
    finally show ?thesis ..
  next
    case q0: False
    hence id: "(if q = 0 then x else y) = y" for x y :: "complex list" by auto
    note powers = field_simps power4_eq_xxxx power3_eq_cube power2_eq_square
    let ?poly = "[:- q\<^sup>2, 2 * p\<^sup>2 - 8 * r, 8 * p, 8:]" 
    from croots3[of ?poly] have croots: "set (croots3 ?poly) = {x. poly ?poly x = 0}" by auto
    from fundamental_theorem_of_algebra_alt[of ?poly] 
    have "{x. poly ?poly x = 0} \<noteq> {}" by auto
    with croots have "croots3 ?poly \<noteq> []" by auto
    then obtain m rest where rts: "croots3 ?poly = m # rest" by (cases "croots3 ?poly", auto)
    hence hd: "hd (croots3 ?poly) = m" by auto
    from croots[unfolded rts] have "poly ?poly m = 0" by auto
    hence mrt: "8*m^3 + (8 * p) * m^2 + (2 * p^2 - 8 * r) * m - q^2 = 0" 
      and m0: "m \<noteq> 0" using q0
      by (auto simp: powers)  
    define b1 where "b1 = p / 2 + m - q / (2 * csqrt (2 * m))" 
    define b2 where "b2 = p / 2 + m + q / (2 * csqrt (2 * m))" 
    have csqrt: "csqrt x * csqrt x = x" for x by (metis power2_csqrt power2_eq_square)
    show ?thesis unfolding solve_depressed_quartic_complex_def id Let_def set_remdups set_append hd
      unfolding b1_def[symmetric] b2_def[symmetric]
      apply (subst depressed_quartic_Ferrari[OF mrt q0 csqrt b1_def b2_def])
      apply (subst (1 2) croots2[symmetric], auto)
      done
  qed
qed
  
text \<open>The main difference in the real case is that a specific cubic root has to be used, namely
  a positive one. In the soundness proof we show that such a cubic root always exists.\<close>

definition solve_depressed_quartic_real :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real list" where
  "solve_depressed_quartic_real p q r = remdups (if q = 0 then 
     (concat (map (\<lambda> z. rroots2 [:-z,0,1:]) (rroots2 [:r,p,1:]))) else
     let cubics = rroots3 [: - (q^2), 2 * p^2 - 8 * r, 8 * p, 8:];
         m = the (find (\<lambda> m. m > 0) cubics);  \<comment> \<open>select any positive root of the cubic polynomial\<close>
         a = sqrt (2 * m); 
         p2m = p / 2 + m;
         q2a = q / (2 * a);
         b1 = p2m - q2a;
         b2 = p2m + q2a
       in (rroots2 [:b1,a,1:] @ rroots2 [:b2,-a,1:]))" 

lemma solve_depressed_quartic_real: "x \<in> set (solve_depressed_quartic_real p q r) 
  \<longleftrightarrow> (x^4 + p * x^2 + q * x + r = 0)"
proof -
  note powers = field_simps power4_eq_xxxx power3_eq_cube power2_eq_square
  show ?thesis
  proof (cases "q = 0")
    case True
    have sqrt: "z = x^2 \<longleftrightarrow> (x \<in> set (rroots2 [:-z,0,1:]))" for z 
      by (subst rroots2[symmetric], auto simp: powers)
    have "(x ^ 4 + p * x\<^sup>2 + q * x + r = 0) \<longleftrightarrow> (x ^ 4 + p * x\<^sup>2 + r = 0)" 
      unfolding True by simp
    also have "\<dots> \<longleftrightarrow> (\<exists>z. z\<^sup>2 + p * z + r = 0 \<and> z = x\<^sup>2)" unfolding biquadratic_solution by simp
    also have "\<dots> \<longleftrightarrow> (\<exists> z. poly [:r,p,1:] z = 0 \<and> z = x^2)" 
      by (simp add: powers)
    also have "\<dots> \<longleftrightarrow> (\<exists> z \<in> set (rroots2 [:r,p,1:]). z = x^2)" 
      by (subst rroots2[symmetric], auto)
    also have "\<dots> \<longleftrightarrow> (\<exists> z \<in> set (rroots2 [:r,p,1:]). x \<in> set (rroots2 [:-z,0,1:]))" 
      unfolding sqrt ..
    also have "\<dots> \<longleftrightarrow> (x \<in> set (solve_depressed_quartic_real p q r))" 
      unfolding solve_depressed_quartic_real_def id unfolding True Let_def by auto
    finally show ?thesis ..
  next
    case q0: False
    hence id: "(if q = 0 then x else y) = y" for x y :: "real list" by auto
    note powers = field_simps power4_eq_xxxx power3_eq_cube power2_eq_square
    let ?poly = "[:- q\<^sup>2, 2 * p\<^sup>2 - 8 * r, 8 * p, 8:]" 
    
    define cubics where "cubics = rroots3 ?poly" 
    from rroots3[of ?poly, folded cubics_def] 
    have rroots: "set cubics = {x. poly ?poly x = 0}" by auto
    from odd_degree_imp_real_root[of ?poly] 
    have "{x. poly ?poly x = 0} \<noteq> {}" by auto
    with rroots have "cubics \<noteq> []" by auto
    have "\<exists> m. m \<in> set cubics \<and> m > 0"
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      from this[unfolded rroots] have rt: "poly ?poly m = 0 \<Longrightarrow> m \<le> 0" for m by auto
      have "poly ?poly 0 = - (q^2)" by simp
      also have "\<dots> < 0" using q0 by auto
      finally have lt: "poly ?poly 0 \<le> 0" by simp
      from poly_pinfty_gt_lc[of ?poly] obtain n0 where "\<And> n. n \<ge> n0 \<Longrightarrow> 8 \<le> poly ?poly n" by auto
      from this[of "max n0 0"] have "poly ?poly (max n0 0) \<ge> 0" by auto
      from IVT[of "poly ?poly", OF lt this] obtain m where "m \<ge> 0" and poly: "poly ?poly m = 0" by auto
      from rt[OF this(2)] this(1) have "m = 0" by auto
      thus False using poly q0 by simp
    qed
    hence "find (\<lambda> m. m > 0) cubics \<noteq> None" unfolding find_None_iff by auto
    then obtain m where find: "find (\<lambda> m. m > 0) cubics = Some m" by auto
    from find_Some_D[OF this] have m: "m \<in> set cubics" and m_0: "m > 0" by auto
    with rroots have "poly ?poly m = 0" by auto
    hence mrt: "8*m^3 + (8 * p) * m^2 + (2 * p^2 - 8 * r) * m - q^2 = 0" 
      by (auto simp: powers)  
    from m_0 have sqrt: "sqrt (2 * m) * sqrt (2 * m) = 2 * m" by simp
    define b1 where "b1 = p / 2 + m - q / (2 * sqrt (2 * m))" 
    define b2 where "b2 = p / 2 + m + q / (2 * sqrt (2 * m))" 
    show ?thesis unfolding solve_depressed_quartic_real_def id Let_def set_remdups set_append 
        cubics_def[symmetric] find option.sel
      unfolding b1_def[symmetric] b2_def[symmetric]
      apply (subst depressed_quartic_Ferrari[OF mrt q0 sqrt b1_def b2_def])
      apply (subst (1 2) rroots2[symmetric], auto)
      done
  qed
qed

text \<open>Combining the various algorithms\<close>

lemma numeral_4_eq_4: "4 = Suc (Suc (Suc (Suc 0)))"
  by (simp add: eval_nat_numeral)

lemma degree4_coeffs: "degree p = 4 \<Longrightarrow>
  \<exists> a b c d e. p = [: e, d, c, b, a :] \<and> a \<noteq> 0" 
  using degree3_coeffs degree_pCons_eq_if nat.inject numeral_3_eq_3 numeral_4_eq_4 pCons_cases zero_neq_numeral
  by metis

definition roots4_generic :: "('a :: field_char_0 \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow> 'a poly \<Rightarrow> 'a list" where
  "roots4_generic depressed_solver p = (let 
     cs = coeffs p; 
     cs = coeffs p; 
     a4 = cs ! 4; a3 = cs ! 3; a2 = cs ! 2; a1 = cs ! 1; a0 = cs ! 0;
     b = a3 / a4;
     c = a2 / a4;
     d = a1 / a4;
     e = a0 / a4;
     b2 = b * b;
     b3 = b2 * b;
     b4 = b3 * b;
     b4' = b / 4;
     p = c - 3/8 * b2;
     q = (b3 - 4*b*c + 8 * d) / 8;
     r = ( -3 * b4 + 256 * e - 64 * b * d + 16 * b2 * c) / 256;
     roots = depressed_solver p q r
     in map (\<lambda> y. y - b4') roots)" 

lemma roots4_generic: assumes deg: "degree p = 4" 
  and solver: "\<And> p q r y. y \<in> set (depressed_solver p q r) \<longleftrightarrow> y^4 + p * y^2 + q * y + r = 0" 
  shows "set (roots4_generic depressed_solver p) = {x. poly p x = 0}" 
proof -
  note powers = field_simps power4_eq_xxxx power3_eq_cube power2_eq_square
  from degree4_coeffs[OF deg] obtain a4 a3 a2 a1 a0 where
    p: "p = [:a0,a1,a2,a3,a4:]" and a4: "a4 \<noteq> 0" by auto
  have coeffs: "coeffs p ! 4 = a4" "coeffs p ! 3 = a3" "coeffs p ! 2 = a2" "coeffs p ! 1 = a1" "coeffs p ! 0 = a0" 
    unfolding p using a4 by auto
  define b where "b = a3 / a4" 
  define c where "c = a2 / a4" 
  define d where "d = a1 / a4" 
  define e where "e = a0 / a4" 
  note def = roots4_generic_def[of depressed_solver p, unfolded Let_def coeffs, folded b_def c_def d_def e_def,
      folded power4_eq_xxxx, folded power3_eq_cube, folded power2_eq_square]
  let ?p = p
  {
    fix x
    define y where "y = x + b / 4" 
    define p where "p = c - (3/8) * b^2" 
    define q where "q = (b^3 - 4*b*c + 8 * d) / 8" 
    define r where "r = ( -3 * b^4 + 256 * e - 64 * b * d + 16 * b^2 * c) / 256" 
    note def = def[folded p_def q_def r_def]
    have xy: "x = y - b / 4" unfolding y_def by auto
    have "poly ?p x = 0 \<longleftrightarrow> a4 * x^4 + a3 * x^3 + a2 * x^2 + a1 * x + a0 = 0" unfolding p
      by (simp add: powers)
    also have "\<dots> \<longleftrightarrow> (y ^ 4 + p * y\<^sup>2 + q * y + r = 0)" 
      unfolding to_depressed_quartic[OF a4 b_def c_def d_def e_def p_def q_def r_def xy] ..
    also have "\<dots> \<longleftrightarrow> y \<in> set (depressed_solver p q r)" 
      unfolding solver ..
    also have "\<dots> \<longleftrightarrow> x \<in> set (roots4_generic depressed_solver ?p)" unfolding xy def by auto
    finally have "poly ?p x = 0 \<longleftrightarrow> x \<in> set (roots4_generic depressed_solver ?p)" by auto
  }
  thus ?thesis by simp
qed

definition croots4 :: "complex poly \<Rightarrow> complex list" where
  "croots4 = roots4_generic solve_depressed_quartic_complex"

lemma croots4: assumes deg: "degree p = 4" 
  shows "set (croots4 p) = { x. poly p x = 0}" 
  unfolding croots4_def by (rule roots4_generic[OF deg solve_depressed_quartic_complex])

definition rroots4 :: "real poly \<Rightarrow> real list" where
  "rroots4 = roots4_generic solve_depressed_quartic_real"

lemma rroots4: assumes deg: "degree p = 4" 
  shows "set (rroots4 p) = { x. poly p x = 0}" 
  unfolding rroots4_def by (rule roots4_generic[OF deg solve_depressed_quartic_real])


end