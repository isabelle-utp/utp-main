section \<open>$n$-th roots of complex numbers\<close>

theory Complex_Roots
  imports 
    Complex_Geometry.More_Complex
    Min_Int_Poly_Impl
    "HOL-Library.Product_Lexorder"
begin

subsection \<open>An algorithm to compute all complex roots of (algebraic) complex numbers\<close>

text \<open>TODO: The filter instruction might be tuned by using interval arithmetic instead.\<close>
definition all_croots :: "nat \<Rightarrow> complex \<Rightarrow> complex list" where
  "all_croots n x = (if n = 0 then [] else
     if algebraic x then
       (let p = min_int_poly x;
         q = poly_nth_root n p;
         xs = complex_roots_of_int_poly q
         in filter (\<lambda> y. y^n = x) xs)
     else (SOME ys. set ys = {y. y^n = x}))" 

lemma all_croots_code[code]:
  "all_croots n x = (if n = 0 then [] else
     if algebraic x then
       (let p = min_int_poly x;
         q = poly_nth_root n p;
         xs = complex_roots_of_int_poly q
         in filter (\<lambda> y. y^n = x) xs)
     else Code.abort (STR ''all_croots invoked on non-algebraic number'') (\<lambda> _. all_croots n x))" 
  by (auto simp: all_croots_def)

lemma all_croots: assumes n0: "n \<noteq> 0" shows "set (all_croots n x) = {y. y^n = x}" 
proof (cases "algebraic x")
  case True
  hence id: "(if n = 0 then y else if algebraic x then z else u) = z" 
    for y z u :: "complex list" using n0 by auto
  define p where "p = poly_nth_root n (min_int_poly x)" 
  show ?thesis unfolding Let_def p_def[symmetric] all_croots_def id
  proof (standard, force, standard, simp)
    fix y
    assume y: "y ^n  = x"     
    have "min_int_poly x represents x" using True by auto
    from represents_nth_root[OF n0 y this]
    have "p represents y" unfolding p_def by auto
    thus "y \<in> set (complex_roots_of_int_poly p)" 
      by (subst complex_roots_of_int_poly, auto)
  qed
next
  case False
  hence id: "(if n = 0 then y else if algebraic x then z else u) = u" 
    for y z u :: "complex list" using n0 by auto
  show ?thesis unfolding Let_def all_croots_def id
    by (rule someI_ex, rule finite_list, insert n0, blast)
qed

subsection \<open>A definition of \emph{the} complex root of a complex number\<close>

text \<open>While the definition of the complex root is quite natural and easy,
  the main task is a criterion to determine which of all possible roots of a
  complex number is the chosen one.\<close>

definition croot :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "croot n x = (rcis (root n (cmod x)) (arg x / of_nat n))" 

lemma croot_0[simp]: "croot n 0 = 0" "croot 0 x = 0"
  unfolding croot_def by auto

lemma croot_power: assumes n: "n \<noteq> 0" 
  shows "(croot n x) ^ n = x" 
  unfolding croot_def DeMoivre2
  by (subst real_root_pow_pos2, insert n, auto simp: rcis_cmod_arg)

lemma arg_of_real: "arg (of_real x) = 
  (if x < 0 then pi else 0)"
proof (cases "x = 0")
  case False
  hence "x < 0 \<or> x > 0" by auto
  thus ?thesis by (intro arg_unique, auto
      simp: complex_sgn_def scaleR_complex.ctr complex_eq_iff)
qed (auto simp: arg_def)


lemma arg_rcis_cis[simp]: assumes "x > 0" 
  shows "arg (rcis x y) = arg (cis y)" 
  using assms unfolding rcis_def by simp

lemma cis_arg_1[simp]: "cis (arg 1) = 1" 
  using arg_of_real[of 1] by simp

lemma cis_arg_power[simp]: assumes "x \<noteq> 0" 
  shows "cis (arg (x ^ n)) = cis (arg x * real n)" 
proof (induct n)
  case (Suc n)
  show ?case unfolding power.simps
  proof (subst cis_arg_mult)    
    show "cis (arg x + arg (x ^ n)) = cis (arg x * real (Suc n))" 
      unfolding mult.commute[of "arg x"] DeMoivre[symmetric]
      unfolding power.simps using Suc
      by (metis DeMoivre cis_mult mult.commute)
    show "x * x ^ n \<noteq> 0" using assms by auto
  qed
qed simp

lemma arg_croot[simp]: "arg (croot n x) = arg x / real n" 
proof (cases "n = 0 \<or> x = 0")
  case True
  thus ?thesis by (auto simp: arg_def)
next
  case False
  hence n: "n \<noteq> 0" and x: "x \<noteq> 0" by auto
  let ?root = "croot n x" 
  from n have n1: "real n \<ge> 1" "real n > 0" "real n \<noteq> 0" by auto
  have bounded: "- pi < arg x / real n \<and> arg x / real n \<le> pi" 
  proof (cases "arg x < 0")
    case True
    from arg_bounded[of x] have "- pi < arg x" by auto
    also have "\<dots> \<le> arg x / real n" using n1 True
      by (smt (z3) div_by_1 divide_minus_left frac_le)
    finally have one: "- pi < arg x / real n" .
    have "arg x / real n \<le> 0" using True n1 
      by (smt (verit) divide_less_0_iff)
    also have "\<dots> \<le> pi" by simp
    finally show ?thesis using one by auto
  next
    case False
    hence ax: "arg x \<ge> 0" by auto
    have "arg x / real n \<le> arg x" using n1 ax
      by (smt (verit) div_by_1 frac_le)
    also have "\<dots> \<le> pi" using arg_bounded[of x] by simp
    finally have one: "arg x / real n \<le> pi" .
    have "-pi < 0" by simp
    also have "\<dots> \<le> arg x / real n" using ax n1 by simp
    finally show ?thesis using one by auto
  qed
  have "arg ?root = arg (cis (arg x / real n))" 
    unfolding croot_def using x n by simp 
  also have "\<dots> = arg x / real n" 
    by (rule arg_unique, force, insert bounded, auto)
  finally show ?thesis .
qed

lemma cos_abs[simp]: "cos (abs x :: real) = cos x" 
proof (cases "x < 0")
  case True
  hence abs: "abs x = - x" by simp
  show ?thesis unfolding abs by simp
qed simp

lemma cos_mono_le: assumes "abs x \<le> pi" 
  and "abs y \<le> pi" 
shows "cos x \<le> cos y \<longleftrightarrow> abs y \<le> abs x" 
proof -
  have "cos x \<le> cos y \<longleftrightarrow> cos (abs x) \<le> cos (abs y)" by simp
  also have "\<dots> \<longleftrightarrow> abs y \<le> abs x" 
    by (subst cos_mono_le_eq, insert assms, auto)
  finally show ?thesis .
qed

lemma abs_add_2_mult_bound: fixes x :: "'a :: linordered_idom" 
  assumes xy: "\<bar>x\<bar> \<le> y" 
  shows "\<bar>x\<bar> \<le> \<bar>x + 2 * of_int i * y\<bar>" 
proof (cases "i = 0")
  case i: False
  let ?oi = "of_int :: int \<Rightarrow> 'a" 
  from xy have y: "y \<ge> 0" by auto
  consider (pp) "x \<ge> 0" "i \<ge> 0" 
    | (nn) "x \<le> 0" "i \<le> 0" 
    | (pn) "x \<ge> 0" "i \<le> 0" 
    | (np) "x \<le> 0" "i \<ge> 0" 
    by linarith
  thus ?thesis
  proof cases
    case pp
    thus ?thesis using y by simp
  next
    case nn 
    have "x \<ge> x + 2 * ?oi i * y" 
      using nn y by (simp add: mult_nonneg_nonpos2)
    with nn show ?thesis by linarith
  next
    case pn
    with i have "0 \<le> x" "i < 0" by auto
    define j where "j = nat (-i) - 1" 
    define z where "z = x - 2 * y" 
    define u where "u = 2 * ?oi (nat j) * y" 
    have u: "u \<ge> 0" unfolding u_def using y by auto 
    have i: "i = - int (Suc j)" 
      using \<open>i < 0\<close> unfolding j_def by simp
    have id: "x + 2 * ?oi i * y = z - u" 
      unfolding i z_def u_def by (simp add: field_simps)
    have z: "z \<le> 0" "abs z \<ge> x" using xy y pn(1)
      unfolding z_def by auto
    show ?thesis unfolding id using pn(1) z u by simp
  next
    case np
    with i have "0 \<ge> x" "i > 0" by auto
    define j where "j = nat i - 1" 
    have i: "i = int (Suc j)" 
      using \<open>i > 0\<close> unfolding j_def by simp
    define u where "u = 2 * ?oi (nat j) * y" 
    have u: "u \<ge> 0" unfolding u_def using y by auto 
    define z where "z = - x - 2 * y" 
    have id: "x + 2 * ?oi i * y = - z + u" 
      unfolding i z_def u_def by (simp add: field_simps)
    have z: "z \<le> 0" "abs z \<ge> - x" using xy y np(1)
      unfolding z_def by auto
    show ?thesis unfolding id using np(1) z u by simp
  qed
qed simp

lemma abs_eq_add_2_mult: fixes y :: "'a :: linordered_idom" 
  assumes abs_id: "\<bar>x\<bar> = \<bar>x + 2 * of_int i * y\<bar>" 
  and xy: "- y < x" "x \<le> y" 
  and i: "i \<noteq> 0" 
shows "x = y \<and> i = -1" 
proof -  
  let ?oi = "of_int :: int \<Rightarrow> 'a" 
  from xy have y: "y > 0" by auto
  consider (pp) "x \<ge> 0" "i \<ge> 0" 
    | (nn) "x < 0" "i \<le> 0" 
    | (pn) "x \<ge> 0" "i \<le> 0" 
    | (np) "x < 0" "i \<ge> 0" 
    by linarith
  hence "?thesis \<or> x = ?oi (- i) * y" 
  proof cases
    case pp
    thus ?thesis using y abs_id xy i by simp
  next
    case nn
    hence "\<bar>x + 2 * ?oi i * y\<bar> = 
      - (x + 2 * ?oi i * y)"
      using y nn
      by (intro abs_of_nonpos add_nonpos_nonpos, 
          force, simp, intro mult_nonneg_nonpos, auto)
    thus ?thesis using y abs_id xy i nn
      by auto
  next
    case pn
    with i have "0 \<le> x" "i < 0" by auto
    define j where "j = nat (-i) - 1" 
    define z where "z = x - 2 * y" 
    define u where "u = 2 * ?oi (nat j) * y" 
    have u: "u \<ge> 0" unfolding u_def using y by auto 
    have i: "i = - int (Suc j)" 
      using \<open>i < 0\<close> unfolding j_def by simp
    have id: "x + 2 * ?oi i * y = z - u" 
      unfolding i z_def u_def by (simp add: field_simps)
    have z: "z \<le> 0" "abs z \<ge> x" using xy y pn(1)
      unfolding z_def by auto
    from abs_id[unfolded id] have "z - u = -x " 
      using z u pn by auto
    from this[folded id] have "x = of_int (-i) * y" 
      by auto
    thus ?thesis by auto
  next
    case np
    with i have "0 \<ge> x" "i > 0" by auto
    define j where "j = nat i - 1" 
    have i: "i = int (Suc j)" 
      using \<open>i > 0\<close> unfolding j_def by simp
    define u where "u = 2 * ?oi (nat j) * y" 
    have u: "u \<ge> 0" unfolding u_def using y by auto 
    define z where "z = - x - 2 * y" 
    have id: "x + 2 * ?oi i * y = - z + u" 
      unfolding i z_def u_def by (simp add: field_simps)
    have z: "z \<le> 0" 
      using xy y np(1) unfolding z_def by auto
    from abs_id[unfolded id] have "- z + u = - x" 
      using u z np by auto
    from this[folded id] have "x = of_int (- i) * y" 
      by auto
    thus ?thesis by auto
  qed
  thus ?thesis
  proof
    assume "x = ?oi (- i) * y" 
    with xy i y
    show ?thesis
      by (smt (verit, ccfv_SIG) less_le minus_less_iff mult_le_cancel_right2 mult_minus1_right mult_minus_left mult_of_int_commute of_int_hom.hom_one of_int_le_1_iff of_int_minus)
  qed
qed

text \<open>This is the core lemma. It tells us that @{const croot} will choose the 
  principal root, i.e. the root with
  largest real part and if there are two roots with identical real part, then the largest imaginary part.
  This criterion will be crucial for implementing @{const croot}.\<close>

lemma croot_principal: assumes n: "n \<noteq> 0"
  and y: "y ^ n = x"
  and neq: "y \<noteq> croot n x"
shows "Re y < Re (croot n x) \<or> Re y = Re (croot n x) \<and> Im y < Im (croot n x)" 
proof (cases "x = 0")
  case True
  with neq y have False by auto
  thus ?thesis ..
next
  case x: False
  let ?root = "croot n x" 
  from n have n1: "real n \<ge> 1" "real n > 0" "real n \<noteq> 0" by auto
  from x y n have y0: "y \<noteq> 0" by auto
  from croot_power[OF n, of x] y
  have id: "?root ^ n = y ^ n" by simp
  hence "cmod (?root ^ n) = cmod (y ^ n)" by simp
  hence norm_eq: "cmod ?root = cmod y" using n unfolding norm_power
    by (meson gr_zeroI norm_ge_zero power_eq_imp_eq_base)
  have "cis (arg y * real n) = cis (arg (y^n))" by (subst cis_arg_power[OF y0], simp) 
  also have "\<dots> = cis (arg x)" using y by simp
  finally have ciseq: "cis (arg y * real n) = cis (arg x)" by simp
  from cis_eq[OF ciseq] obtain i where
    "arg y * real n - arg x = 2 * real_of_int i * pi" 
    by auto
  hence "arg y * real n = arg x + 2 * real_of_int i * pi" by auto
  from arg_cong[OF this, of "\<lambda> x. x / real n"] n1
  have argy: "arg y = arg ?root + 2 * real_of_int i * pi / real n" 
    by (auto simp: field_simps)
  have i0: "i \<noteq> 0" 
  proof
    assume "i = 0" 
    hence "arg y = arg ?root" unfolding argy by simp
    with norm_eq have "?root = y" by (metis rcis_cmod_arg)
    with neq show False by simp
  qed
  from y0 have cy0: "cmod y > 0" by auto
  from arg_bounded[of x] have abs_pi: "abs (arg x) \<le> pi" by auto
  have "Re y \<le> Re ?root \<longleftrightarrow> Re y / cmod y \<le> Re ?root / cmod y"
    using cy0 unfolding divide_le_cancel by simp
  also have cosy: "Re y / cmod y = cos (arg y)" unfolding cos_arg[OF y0] ..
  also have cosrt: "Re ?root / cmod y = cos (arg ?root)" 
    unfolding norm_eq[symmetric] by (subst cos_arg, insert norm_eq cy0, auto)
  also have "cos (arg y) \<le> cos (arg ?root) \<longleftrightarrow> abs (arg ?root) \<le> abs (arg y)" 
    by (rule cos_mono_le, insert arg_bounded[of y] arg_bounded[of ?root], auto)
  also have "\<dots> \<longleftrightarrow> abs (arg ?root) * real n \<le> abs (arg y) * real n" 
    unfolding mult_le_cancel_right using n1 by simp
  also have "\<dots> \<longleftrightarrow> abs (arg x) \<le> \<bar>arg x + 2 * real_of_int i * pi\<bar>" 
    unfolding argy using n1 by (simp add: field_simps)
  also have "\<dots>" using abs_pi
    by (rule abs_add_2_mult_bound)
  finally have le: "Re y \<le> Re (croot n x)" .
  show ?thesis
  proof (cases "Re y = Re (croot n x)")
    case False
    with le show ?thesis by auto
  next
    case True
    hence "Re y / cmod y = Re ?root / cmod y" by simp
    hence "cos (arg y) = cos (arg ?root)" unfolding cosy cosrt .
    hence "cos (abs (arg y)) = cos (abs (arg ?root))" unfolding cos_abs .
    from cos_inj_pi[OF _ _ _ _ this]
    have "abs (arg y) = abs (arg ?root)" 
      using arg_bounded[of y] arg_bounded[of ?root] by auto
    hence "abs (arg y) * real n = abs (arg ?root) * real n" by simp
    hence "abs (arg x) = \<bar>arg x + 2 * real_of_int i * pi\<bar>" unfolding argy 
      using n1 by (simp add: field_simps)
    from abs_eq_add_2_mult[OF this _ _ \<open>i \<noteq> 0\<close>] arg_bounded[of x]  
    have argx: "arg x = pi" and i: "i = -1" by auto
    have argy: "arg y = -pi / real n" 
      unfolding argy arg_croot i argx by simp
    have "Im ?root > Im y \<longleftrightarrow> Im ?root / cmod ?root > Im y / cmod y"
      unfolding norm_eq using cy0
      by (meson divide_less_cancel divide_strict_right_mono) 
    also have "\<dots> \<longleftrightarrow> sin (arg ?root) > sin (arg y)" 
      by (subst (1 2) sin_arg, insert y0 norm_eq, auto)
    also have "\<dots> \<longleftrightarrow> sin (- pi / real n) < sin (pi / real n)" 
      unfolding argy arg_croot argx by simp
    also have \<dots>
    proof -
      have "sin (- pi / real n) < 0" 
        using n1 by (smt (verit) arg_bounded argy divide_neg_pos sin_gt_zero sin_minus)
      also have "\<dots> < sin (pi / real n)" 
        using n1 calculation by fastforce
      finally show ?thesis .
    qed
    finally show ?thesis using le by auto
  qed
qed

lemma croot_unique: assumes n: "n \<noteq> 0"
  and y: "y ^ n = x"
  and y_max_Re_Im: "\<And> z. z ^ n = x \<Longrightarrow>
      Re z < Re y \<or> Re z = Re y \<and> Im z \<le> Im y" 
shows "croot n x = y" 
proof (rule ccontr)
  assume "croot n x \<noteq> y" 
  from croot_principal[OF n y this[symmetric]]
  have "Re y < Re (croot n x) \<or>
    Re y = Re (croot n x) \<and> Im y < Im (croot n x)" .
  with y_max_Re_Im[OF croot_power[OF n]]
  show False by auto
qed

lemma csqrt_is_croot_2: "csqrt = croot 2" 
proof
  fix x
  show "csqrt x = croot 2 x" 
  proof (rule sym, rule croot_unique, force, force)
    let ?p = "[:-x,0,1:]" 
    let ?cx = "csqrt x" 
    have p: "?p = [:?cx,1:] * [:-?cx,1:]" 
      by (simp add: power2_eq_square[symmetric])
    fix y
    assume "y^2 = x" 
    hence "True \<longleftrightarrow> poly ?p y = 0" 
      by (auto simp: power2_eq_square)
    also have "\<dots> \<longleftrightarrow> y = - ?cx \<or> y = ?cx" 
      unfolding p poly_mult mult_eq_0_iff poly_root_factor by auto
    finally have "y = - ?cx \<or> y = ?cx" by simp
    thus "Re y < Re ?cx \<or> Re y = Re ?cx \<and> Im y \<le> Im ?cx"
    proof
      assume y: "y = - ?cx"
      show ?thesis
      proof (cases "Re ?cx = 0")
        case False
        with csqrt_principal[of x] have "Re ?cx > 0" by simp
        thus ?thesis unfolding y by simp
      next
        case True
        with csqrt_principal[of x] have "Im ?cx \<ge> 0" by simp
        thus ?thesis unfolding y using True by auto
      qed
    qed auto
  qed
qed

lemma croot_via_root_selection: assumes roots: "set ys = { y. y^n = x}" 
  and n: "n \<noteq> 0" 
shows "croot n x = arg_min_list (\<lambda> y. (- Re y, - Im y)) ys" 
  (is "_ = arg_min_list ?f ys")
proof (rule croot_unique[OF n])
  let ?y = "arg_min_list ?f ys" 
  have rt: "croot n x ^ n = x" using n by (rule croot_power)
  hence "croot n x \<in> set ys" unfolding roots by auto
  hence ys: "ys \<noteq> []" by auto
  from arg_min_list_in[OF this] have "?y \<in> set ys" by auto
  from this[unfolded roots] 
  show "?y^n = x" by auto
  fix z
  assume "z^n = x"
  hence z: "z \<in> set ys" unfolding roots by auto
  from f_arg_min_list_f[OF ys, of ?f] z 
  have "?f ?y \<le> ?f z" by simp
  thus "Re z < Re ?y \<or> Re z = Re ?y \<and> Im z \<le> Im ?y" by auto
qed

lemma croot_impl[code]: "croot n x = (if n = 0 then 0 else 
  arg_min_list (\<lambda> y. (- Re y, - Im y)) (all_croots n x))" 
proof (cases "n = 0")
  case n0: False
  hence id: "(if n = 0 then y else z) = z" 
    for y z u :: complex by auto
  show ?thesis unfolding id Let_def 
    by (rule croot_via_root_selection[OF _ n0], rule all_croots[OF n0])
qed auto

end