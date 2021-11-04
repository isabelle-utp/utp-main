section \<open>Cardano's formula for solving cubic equations\<close>

theory Cardanos_Formula
  imports 
    Polynomial_Factorization.Explicit_Roots
    Polynomial_Interpolation.Ring_Hom_Poly
    Complex_Geometry.More_Complex
    Algebraic_Numbers.Complex_Roots_Real_Poly
begin

subsection \<open>Translation to depressed case\<close>

text \<open>Solving an arbitrary cubic equation can easily be turned into the depressed case, i.e., where
  there is no quadratic part.\<close>

lemma to_depressed_cubic: fixes a :: "'a :: field_char_0"
  assumes a: "a \<noteq> 0" 
  and xy: "x = y - b / (3 * a)" 
  and e: "e = (c - b^2 / (3 * a)) / a" 
  and f: "f = (d + 2 * b^3 / (27 * a^2) - b * c / (3 * a)) / a" 
shows "(a * x ^ 3 + b * x\<^sup>2 + c * x + d = 0) \<longleftrightarrow> y^3 + e * y + f = 0" 
proof -
  let ?yexp = "y^3 + e * y + f" 
  have "a * x^3 + b * x^2 + c * x + d = 0 \<longleftrightarrow> (a * x^3 + b * x^2 + c * x + d) / a = 0" 
    using a by auto
  also have "(a * x^3 + b * x^2 + c * x + d) / a = ?yexp" unfolding xy e f power3_eq_cube power2_eq_square using a
    by (simp add: field_simps)
  finally show ?thesis .
qed

subsection \<open>Solving the depressed case in arbitrary fields\<close>

lemma cubic_depressed: fixes e :: "'a :: field_char_0" 
  assumes yz: "e \<noteq> 0 \<Longrightarrow> z^2 - y * z - e / 3 = 0" 
  and u: "e \<noteq> 0 \<Longrightarrow> u = z^3" 
  and v: "v = - (e ^ 3 / 27)" 
shows "y^3 + e * y + f = 0 \<longleftrightarrow> (if e = 0 then y^3 = -f else u\<^sup>2 + f * u + v = 0)" 
proof - 
  let ?yexp = "y^3 + e * y + f" 
  show ?thesis
  proof (cases "e = 0")
    case False
    note yz = yz[OF False]
    from yz have eyz: "e = 3 * (z^2 - y * z)" by auto
    from yz False have z0: "z \<noteq> 0" by auto
    have "?yexp = 0 \<longleftrightarrow> z^3 * ?yexp = 0" using z0 by simp
    also have "z^3 * ?yexp = z^6 + f * z^3 - e^3/27" unfolding eyz by algebra
    also have "\<dots> = u^2 + f * u + v" unfolding u[OF False] v by algebra  
    finally show ?thesis using False by auto 
  next
    case True
    show ?thesis unfolding True by (auto, algebra)
  qed
qed

subsection \<open>Solving the depressed case for complex numbers\<close>

text \<open>In the complex-numbers-case, the quadratic equation for u is always solvable,
  and the main challenge here is prove that it does not matter which solution of 
  the quadratic equation is considered (this is the diff:False case in the proof below.)\<close>
lemma solve_cubic_depressed_Cardano_complex: fixes e :: complex 
  assumes e0: "e \<noteq> 0" 
  and v: "v = - (e ^ 3 / 27)" 
  and u: "u^2 + f * u + v = 0" 
shows "y^3 + e * y + f = 0 \<longleftrightarrow> (\<exists> z. z^3 = u \<and> y = z - e / (3 * z))" 
proof -
  from v e0 have v0: "v \<noteq> 0" by auto
  from e0 have "(if e = 0 then x else y) = y" for x y :: bool by auto
  note main = cubic_depressed[OF _ _ v, unfolded this]
  show ?thesis (is "?l = ?r")
  proof
    assume ?r
    then obtain z where z: "z^3 = u" and y: "y = z - e / (3 * z)" by auto
    from u v0 have u0: "u \<noteq> 0" by auto
    from z u0 have z0: "z \<noteq> 0" by auto
    show ?l
    proof (subst main)
      show "u\<^sup>2 + f * u + v = 0" by fact
      show "u = z^3" unfolding z by simp
      show "z\<^sup>2 - y * z - e / 3 = 0" unfolding y using z0
        by (auto simp: field_simps power2_eq_square)
    qed
  next
    assume ?l
    let ?yexp = "y^3 + e * y + f" 
    have y0: "?yexp = 0" using \<open>?l\<close> by auto
    define p where "p = [: -e/3, -y, 1:]" 
    have deg: "degree p = 2" unfolding p_def by auto
    define z where "z = hd (croots2 p)"  
    have "z \<in> set (croots2 p)" unfolding croots2_def Let_def z_def by auto
    with croots2[OF deg] have pz: "poly p z = 0" by auto
    from pz e0 have z0: "z \<noteq> 0" unfolding p_def by auto
    from pz have yz: "y * z = z * z - e / 3" unfolding p_def by (auto simp: field_simps)
    from arg_cong[OF this, of "\<lambda> x. x / z"] z0 have "y = z - e / (3 * z)"
      by (auto simp: field_simps)
    have "\<exists> u z. u\<^sup>2 + f * u + v = 0 \<and> z^3 = u \<and> y = z - e / (3 * z)" 
    proof (intro exI conjI)
      show "y = z - e / (3 * z)" by fact
      from y0 have "0 = ?yexp * z^3" by auto
      also have "\<dots> = (y * z)^3 + e * (y * z) * z^2 + f * z^3" by algebra
      also have "\<dots> = (z^3)^2 + f * (z^3) + v" unfolding yz v by algebra
      finally show "(z^3)^2 + f * (z^3) + v = 0" by simp 
    qed simp
    then obtain uu z where
       *: "uu\<^sup>2 + f * uu + v = 0" "z ^ 3 = uu" "y = z - e / (3 * z)" by blast
        show ?r
    proof (cases "uu = u")
      case True
      thus ?thesis using * by auto
    next
      case diff: False
      define p where "p = [:v,f,1:]" 
      have p2: "degree p = 2" unfolding p_def by auto
      have poly: "poly p u = 0" "poly p uu = 0" using u *(1) unfolding p_def
        by (auto simp: field_simps power2_eq_square)
      have u0: "u \<noteq> 0" "uu \<noteq> 0" using poly v0 unfolding p_def by auto
      {
        from poly(1) have "[:-u,1:] dvd p" by (meson poly_eq_0_iff_dvd)
        then obtain q where pq: "p = q * [:-u,1:]" by auto
        from poly(2)[unfolded pq poly_mult] diff have "poly q uu = 0" by auto
        hence "[:-uu,1:] dvd q" by (meson poly_eq_0_iff_dvd)      
        then obtain q' where qq': "q = q' * [:-uu,1:]" by auto
        with pq have pq: "p = q' * [:-uu,1:] * [:-u,1:]" by auto
        from pq[unfolded p_def] have q': "q' \<noteq> 0" by auto
        from arg_cong[OF pq, of degree, unfolded p2]
        have "2 = degree (q' * [:- uu, 1:] * [:- u, 1:])" .
        also have "\<dots> = degree q' + degree [:- uu, 1:] + degree [:- u, 1:]" 
          apply (subst degree_mult_eq)
          subgoal using q' by (metis mult_eq_0_iff pCons_eq_0_iff zero_neq_one)
          subgoal by force
          by (subst degree_mult_eq[OF q'], auto)
        also have "\<dots> = degree q' + 2" by simp
        finally have dq: "degree q' = 0" by simp
        from dq obtain c where q': "q' = [: c:]" by (metis degree_eq_zeroE)
        from pq[unfolded q' p_def] have "c = 1" by auto
        with q' have "q' = 1" by simp
        with pq have "[: -u, 1:] * [: -uu, 1 :] = p" by simp
      }
      from this[unfolded p_def, simplified] have prod: "uu * u = v" by simp
      hence uu: "u = v / uu" using u0 by (simp add: field_simps)
      define zz where "zz = - e / (3 * z)" 
      show ?r using *(2-) uu unfolding v using u0
        by (intro exI[of _ zz], auto simp: zz_def field_simps)
    qed
  qed
qed

subsection \<open>Solving the depressed case for real numbers\<close>

definition discriminant_cubic_depressed :: "'a :: comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a" where 
  "discriminant_cubic_depressed e f = - (4 * e^3 + 27 * f^2)"

lemma discriminant_cubic_depressed: assumes "[:-x,1:] * [:-y,1:] * [:-z,1:] = [:f,e,0,1:]" 
  shows "discriminant_cubic_depressed e f = (x-y)^2 * (x - z)^2 * (y - z)^2" 
proof -
  from assms have f: "f = - (z * (y * x))" and e: "e = y * x - z * (- y - x)" and 
      z: "z = - y - x" by auto
  show ?thesis unfolding discriminant_cubic_depressed_def e f z
    by (simp add: power2_eq_square power3_eq_cube field_simps)
qed

text \<open>If the discriminant is negative, then there is exactly one real root\<close>

lemma solve_cubic_depressed_Cardano_real: fixes e f v u :: real 
  defines "y1 \<equiv> root 3 u - e / (3 * root 3 u)" 
    and "\<Delta> \<equiv> discriminant_cubic_depressed e f" 
  assumes e0: "e \<noteq> 0" 
  and v: "v = - (e ^ 3 / 27)" 
  and u: "u\<^sup>2 + f * u + v = 0" (* this implies \<Delta> \<le> 0 *)
shows "y1^3 + e * y1 + f = 0"
  "\<Delta> \<noteq> 0 \<Longrightarrow> y^3 + e * y + f = 0 \<Longrightarrow> y = y1" (* this is the case \<Delta> < 0 *)
proof -
  let ?c = complex_of_real
  let ?y = "?c y" 
  let ?e = "?c e"
  let ?u = "?c u" 
  let ?v = "?c v" 
  let ?f = "?c f" 
  {
    fix y :: real
    let ?y = "?c y" 
    have "y^3 + e * y + f = 0 \<longleftrightarrow> ?c (y^3 + e * y + f) = ?c 0" 
      using of_real_eq_iff by blast
    also have "\<dots> \<longleftrightarrow> ?y^3 + ?e * ?y + ?f = 0" by simp
    also have "\<dots> \<longleftrightarrow> (\<exists> z. z^3 = ?u \<and> ?y = z - ?e / (3 * z))" 
    proof (rule solve_cubic_depressed_Cardano_complex)
      show "?e \<noteq> 0" using e0 by auto
      show "?v = - (?e ^ 3 / 27)" unfolding v by simp
      show "?u\<^sup>2 + ?f * ?u + ?v = 0" using arg_cong[OF u, of ?c] by simp
    qed
    finally have "y^3 + e * y + f = 0 \<longleftrightarrow> (\<exists> z. z^3 = ?u \<and> ?y = z - ?e / (3 * z))" .
  } note pre = this
  show y1: "y1^3 + e * y1 + f = 0" unfolding pre y1_def
    by (intro exI[of _ "?c (root 3 u)"], simp only: of_real_power[symmetric],
        simp del: of_real_power add: odd_real_root_pow)
  from u have "{z. poly [:v,f,1:] z = 0} \<noteq> {}" 
    by (auto simp add: field_simps power2_eq_square)
  hence "set (rroots2 [:v,f,1:]) \<noteq> {}" 
    by (subst rroots2[symmetric], auto)
  hence "rroots2 [:v,f,1:] \<noteq> []" by simp
  from this[unfolded rroots2_def Let_def, simplified]
  have "f^2 - 4 * v \<ge> 0"
    by (auto split: if_splits simp: numeral_2_eq_2 field_simps power2_eq_square)
  hence delta_le_0: "\<Delta> \<le> 0" unfolding \<Delta>_def discriminant_cubic_depressed_def v by auto

  assume Delta_non_0: "\<Delta> \<noteq> 0" 
  with delta_le_0 have delta_neg: "\<Delta> < 0" by simp
  let ?p = "[:f,e,0,1:]" 
  have poly: "poly ?p y = 0 \<longleftrightarrow> y^3 + e * y + f = 0" for y
    by (simp add: field_simps power2_eq_square power3_eq_cube)
  from y1 have "poly ?p y1 = 0" unfolding poly .
  hence "[:-y1,1:] dvd ?p" using poly_eq_0_iff_dvd by blast
  then obtain q where pq: "?p = [:-y1,1:] * q" by blast
  {
    fix y2 
    assume "poly ?p y2 = 0" "y2 \<noteq> y1" 
    from this[unfolded pq] poly_mult have "poly q y2 = 0" by auto
    from this[unfolded poly_eq_0_iff_dvd] obtain r where qr: "q = [:-y2,1:] * r" by blast
    {
      have r0: "r \<noteq> 0" using pq unfolding qr poly_mult by auto
      have "3 = degree ?p" by simp
      also have "\<dots> = 2 + degree r" unfolding pq qr
        apply (subst degree_mult_eq, force)
        subgoal using r0 pq qr by force
        by (subst degree_mult_eq[OF _ r0], auto)
      finally have "degree r = 1" by simp
      from degree1_coeffs[OF this] obtain yy a where r: "r = [:yy,a:]" by auto
      define y3 where "y3 = -yy" 
      with r have r: "r = [:-y3,a:]" by auto
      from pq[unfolded qr r] have "a = 1" by auto
      with r have "\<exists> y3. r = [:-y3,1:]" by auto
    }
    then obtain y3 where r: "r = [:-y3,1:]" by auto
    have py: "?p = [:-y1,1:] * [:-y2,1:] * [:-y3,1:]" unfolding pq qr r by algebra
    from discriminant_cubic_depressed[OF this[symmetric], folded \<Delta>_def]
    have delta: "\<Delta> = (y1 - y2)\<^sup>2 * (y1 - y3)\<^sup>2 * (y2 - y3)\<^sup>2" .
    have d0: "\<Delta> \<ge> 0" unfolding delta by auto
    with delta_neg have False by auto
  }
  with y1 show "y^3 + e * y + f = 0 \<Longrightarrow> y = y1" unfolding poly by auto
qed

text \<open>If the discriminant is non-negative, then all roots are real\<close>

lemma solve_cubic_depressed_Cardano_all_real_roots: fixes e f v :: real and y :: complex
  defines "\<Delta> \<equiv> discriminant_cubic_depressed e f" 
  assumes Delta: "\<Delta> \<ge> 0" 
  and rt: "y^3 + e * y + f = 0"
shows "y \<in> \<real>" 
proof -
  note powers = field_simps power3_eq_cube power2_eq_square
  let ?c = complex_of_real
  let ?e = "?c e" 
  let ?f = "?c f" 
  let ?cp = "[:?f,?e,0,1:]" 
  let ?p = "[:f,e,0,1:]" 
  from odd_degree_imp_real_root[of ?p] obtain x1 where "poly ?p x1 = 0" by auto
  hence "[:-x1,1:] dvd ?p" using poly_eq_0_iff_dvd by blast
  then obtain q where pq: "?p = [:-x1,1:] * q" by auto
  from arg_cong[OF pq, of degree]
  have "3 = degree ([:-x1,1:] * q)" by simp
  also have "\<dots> = 1 + degree q" 
    by (subst degree_mult_eq, insert pq, auto)
  finally have dq: "degree q = 2" by auto
  let ?cc = "map_poly ?c" 
  let ?q = "?cc q" 
  have cpq: "?cc ?p = ?cc [:-x1,1:] * ?q" unfolding pq hom_distribs by simp
  let ?x1 = "?c x1" 
  have dq': "degree ?q = 2" using dq by simp
  have "\<not> constant (poly ?q)" using dq by (simp add: constant_degree)
  from fundamental_theorem_of_algebra[OF this] obtain x2 where x2: "poly ?q x2 = 0" by blast
  have "x2 \<in> \<real>" 
  proof (rule ccontr)
    assume x2r: "x2 \<notin> \<real>" 
    define x3 where "x3 = cnj x2" 
    from x2r have x23: "x2 \<noteq> x3" unfolding x3_def using Reals_cnj_iff by force
    have x3: "poly ?q x3 = 0" unfolding x3_def
      by (rule complex_conjugate_root[OF _ x2], auto)
    from x2[unfolded poly_eq_0_iff_dvd] obtain r where qr: "?q = [:-x2,1:] * r" by auto
    from arg_cong[OF this[symmetric], of "\<lambda> x. poly x x3", unfolded poly_mult x3 mult_eq_0_iff] x23
    have x3: "poly r x3 = 0" by auto
    from arg_cong[OF qr, of degree]
    have "2 = degree ([:-x2,1:] * r)" using dq' by simp
    also have "\<dots> = 1 + degree r" by (subst degree_mult_eq, insert pq qr, auto)
    finally have "degree r = 1" by simp
    from degree1_coeffs[OF this] obtain a b where r: "r = [:a,b:]" by auto
    from cpq[unfolded qr r] have b1: "b = 1" by simp
    with x3 r have "a + x3 = 0" by simp
    hence "a = - x3" by algebra
    with b1 r have r: "r = [:-x3,1:]" by auto
    have "?cc ?p = ?cc [:-x1,1:] * [:-x2,1:] * [:-x3,1:]" unfolding cpq qr r by algebra
    also have "?cc [:-x1,1:] = [:-?x1,1:]" by simp
    also have "?cc ?p = ?cp" by simp
    finally have id: "[:-?x1,1:] * [:-x2,1:] * [:-x3,1:] = ?cp" by simp
    define x23 where "x23 = - 4 * (Im x2)^2" 
    define x12c where "x12c = ?x1 - x2" 
    define x12 where "x12 = (Re x12c) ^ 2 + (Im x12c)^2" 
    have x23_0: "x23 < 0" unfolding x23_def using x2r using complex_is_Real_iff by force
    have "Im x12c \<noteq> 0" unfolding x12c_def using x2r using complex_is_Real_iff by force
    hence "(Im x12c)^2 > 0" by simp
    hence x12: "x12 > 0" unfolding x12_def using sum_power2_gt_zero_iff by auto
    from discriminant_cubic_depressed[OF id]
    have "?c \<Delta> = ((?x1 - x2)\<^sup>2 * (?x1 - x3)\<^sup>2) * (x2 - x3)\<^sup>2" 
      unfolding \<Delta>_def discriminant_cubic_depressed_def by simp
    also have "(x2 - x3)^2 = ?c x23" unfolding x3_def x23_def by (simp add: complex_eq_iff power2_eq_square)
    also have "(?x1 - x2)\<^sup>2 * (?x1 - x3)\<^sup>2 = ((?x1 - x2) * (?x1 - x3))^2" 
      by (simp add: power2_eq_square)
    also have "?x1 - x3 = cnj (?x1 - x2)" unfolding x3_def by simp
    also have "(?x1 - x2) = x12c" unfolding x12c_def ..
    also have "x12c * cnj x12c = ?c x12" by (simp add: x12_def complex_eq_iff power2_eq_square)
    finally have "?c \<Delta> = ?c (x12^2 * x23)" by simp
    hence "\<Delta> = x12^2 * x23" by (rule of_real_hom.injectivity)
    also have "\<dots> < 0" using x12 x23_0 by (meson mult_pos_neg zero_less_power)
    finally show False using Delta by simp
  qed
  with x2 obtain x2 where "poly ?q (?c x2) = 0" unfolding Reals_def by auto
  hence x2: "poly q x2 = 0" by simp
  from x2[unfolded poly_eq_0_iff_dvd] obtain r where qr: "q = [:-x2,1:] * r" by auto
  from arg_cong[OF qr, of degree]
  have "2 = degree ([:-x2,1:] * r)" using dq' by simp
  also have "\<dots> = 1 + degree r" by (subst degree_mult_eq, insert pq qr, auto)
  finally have "degree r = 1" by simp
  from degree1_coeffs[OF this] obtain a b where r: "r = [:a,b:]" by auto
  from pq[unfolded qr r] have b1: "b = 1" by simp
  define x3 where "x3 = -a" 
  have r: "r = [:-x3,1:]" unfolding r b1 x3_def by simp
  let ?pp = "[:-x1,1:] * [:-x2,1:] * [:-x3,1:]" 
  have id: "?p = ?pp" unfolding pq qr r by linarith
  have "True \<longleftrightarrow> y^3 + e * y + f = 0" using rt by auto
  also have "y^3 + e * y + f = poly (?cc ?p) y" by (simp add: powers)
  also have "\<dots> = poly (?cc ?pp) y" unfolding id by simp
  also have "?cc ?pp = [:-?c x1, 1:] * [:-?c x2, 1:] * [:- ?c x3, 1:]" 
    by simp
  also have "poly \<dots> y = 0 \<longleftrightarrow> y = ?c x1 \<or> y = ?c x2 \<or> y = ?c x3" 
    unfolding poly_mult mult_eq_0_iff by auto
  finally show "y \<in> \<real>" by auto
qed

end