section \<open>Getting Small Representative Polynomials via Factorization\<close>

text \<open>In this theory we import a factorization algorithm for 
  integer polynomials to turn a representing polynomial of some algebraic number into
  a list of irreducible polynomials where exactly one list element
  represents the same number. Moreover, we prove
  that the certain polynomial operations preserve irreducibility, so that
  no factorization is required.\<close>

theory Factors_of_Int_Poly
  imports
  Berlekamp_Zassenhaus.Factorize_Int_Poly
  Algebraic_Numbers_Prelim
begin

lemma degree_of_gcd: "degree (gcd q r) \<noteq> 0 \<longleftrightarrow>
 degree (gcd (of_int_poly q :: 'a :: {field_char_0, field_gcd} poly) (of_int_poly r)) \<noteq> 0"
proof -
  let ?r = "of_rat :: rat \<Rightarrow> 'a"
  interpret rpoly: field_hom' ?r
    by (unfold_locales, auto simp: of_rat_add of_rat_mult)
  {
    fix p
    have "of_int_poly p = map_poly (?r o of_int) p" unfolding o_def
      by auto
    also have "\<dots> = map_poly ?r (map_poly of_int p)"
      by (subst map_poly_map_poly, auto)
    finally have "of_int_poly p = map_poly ?r (map_poly of_int p)" .
  } note id = this
  show ?thesis unfolding id by (fold hom_distribs, simp add: gcd_rat_to_gcd_int)
qed

definition factors_of_int_poly :: "int poly \<Rightarrow> int poly list" where
  "factors_of_int_poly p = map (abs_int_poly o fst) (snd (factorize_int_poly p))"

lemma factors_of_int_poly_const: assumes "degree p = 0"
  shows "factors_of_int_poly p = []"
proof -
  from degree0_coeffs[OF assms] obtain a where p: "p = [: a :]" by auto
  show ?thesis unfolding p factors_of_int_poly_def
    factorize_int_poly_generic_def x_split_def
    by (cases "a = 0", auto simp add: Let_def factorize_int_last_nz_poly_def)
qed

lemma factors_of_int_poly:
  defines "rp \<equiv> ipoly :: int poly \<Rightarrow> 'a :: {field_gcd,field_char_0} \<Rightarrow> 'a"
  assumes "factors_of_int_poly p = qs"
  shows "\<And> q. q \<in> set qs \<Longrightarrow> irreducible q \<and> lead_coeff q > 0 \<and> degree q \<le> degree p \<and> degree q \<noteq> 0"
  "p \<noteq> 0 \<Longrightarrow> rp p x = 0 \<longleftrightarrow> (\<exists> q \<in> set qs. rp q x = 0)"
  "p \<noteq> 0 \<Longrightarrow> rp p x = 0 \<Longrightarrow> \<exists>! q \<in> set qs. rp q x = 0"
  "distinct qs"
proof -
  obtain c qis where factt: "factorize_int_poly p = (c,qis)" by force
  from assms[unfolded factors_of_int_poly_def factt]
  have qs: "qs = map (abs_int_poly \<circ> fst) (snd (c, qis))" by auto
  note fact = factorize_int_poly(1)[OF factt]
  note fact_mem = factorize_int_poly(2,3)[OF factt]
  have sqf: "square_free_factorization p (c, qis)" by (rule fact(1))
  note sff = square_free_factorizationD[OF sqf]
  have sff': "p = Polynomial.smult c (\<Prod>(a, i)\<leftarrow> qis. a ^ Suc i)"
    unfolding sff(1) prod.distinct_set_conv_list[OF sff(5)] ..
  {
    fix q
    assume q: "q \<in> set qs"
    then obtain r i where qi: "(r,i) \<in> set qis" and qr: "q = abs_int_poly r" unfolding qs by auto
    from split_list[OF qi] obtain qis1 qis2 where qis: "qis = qis1 @ (r,i) # qis2" by auto
    have dvd: "r dvd p" unfolding sff' qis dvd_def
      by (intro exI[of _ "smult c (r ^ i * (\<Prod>(a, i)\<leftarrow>qis1 @  qis2. a ^ Suc i))"], auto)
    from fact_mem[OF qi] have r0: "r \<noteq> 0" by auto
    from qi factt have p: "p \<noteq> 0" by (cases p, auto)
    with dvd have deg: "degree r \<le> degree p" by (metis dvd_imp_degree_le)
    with fact_mem[OF qi] r0
    show "irreducible q \<and> lead_coeff q > 0 \<and> degree q \<le> degree p \<and> degree q \<noteq> 0"
      unfolding qr lead_coeff_abs_int_poly by auto
  } note * = this
  show "distinct qs" unfolding distinct_conv_nth
  proof (intro allI impI)
    fix i j
    assume "i < length qs" "j < length qs" and diff: "i \<noteq> j"
    hence ij: "i < length qis" "j < length qis"
      and id: "qs ! i = abs_int_poly (fst (qis ! i))" "qs ! j = abs_int_poly (fst (qis ! j))" unfolding qs by auto
    obtain qi I where qi: "qis ! i = (qi, I)" by force
    obtain qj J where qj: "qis ! j = (qj, J)" by force
    from sff(5)[unfolded distinct_conv_nth, rule_format, OF ij diff] qi qj
    have diff: "(qi, I) \<noteq> (qj, J)" by auto
    from ij qi qj have "(qi, I) \<in> set qis" "(qj, J) \<in> set qis" unfolding set_conv_nth by force+
    from sff(3)[OF this diff] sff(2) this
    have cop: "coprime qi qj" "degree qi \<noteq> 0" "degree qj \<noteq> 0" by auto
    note i = cf_pos_poly_main[of qi, unfolded smult_prod monom_0]
    note j = cf_pos_poly_main[of qj, unfolded smult_prod monom_0]
    from cop(2) i have deg: "degree (qs ! i) \<noteq> 0" by (auto simp: id qi)
    have cop: "coprime (qs ! i) (qs ! j)"
      unfolding id qi qj fst_conv
      apply (rule coprime_prod[of "[:sgn (lead_coeff qi):]" "[:sgn (lead_coeff qj):]"])
      using cop
      unfolding i j by (auto simp: sgn_eq_0_iff)
    show "qs ! i \<noteq> qs ! j"
    proof
      assume id: "qs ! i = qs ! j"
      have "degree (gcd (qs ! i) (qs ! j)) = degree (qs ! i)"  unfolding id by simp
      also have "\<dots> \<noteq> 0" using deg by simp
      finally show False using cop by simp
    qed
  qed
  assume p: "p \<noteq> 0"
  from fact(1) p have c: "c \<noteq> 0" using sff(1) by auto
  let ?r = "of_int :: int \<Rightarrow> 'a"
  let ?rp = "map_poly ?r"
  have rp: "\<And> x p. rp p x = 0 \<longleftrightarrow> poly (?rp p) x = 0" unfolding rp_def ..
  have "rp p x = 0 \<longleftrightarrow> rp (\<Prod>(x, y)\<leftarrow>qis. x ^ Suc y) x = 0" unfolding sff'(1)
    unfolding rp hom_distribs using c by simp
  also have "\<dots> = (\<exists> (q,i) \<in>set qis. poly (?rp (q ^ Suc i)) x = 0)"
    unfolding qs rp of_int_poly_hom.hom_prod_list poly_prod_list_zero_iff set_map by fastforce
  also have "\<dots> = (\<exists> (q,i) \<in>set qis. poly (?rp q) x = 0)"
    unfolding of_int_poly_hom.hom_power poly_power_zero_iff by auto
  also have "\<dots> = (\<exists> q \<in> fst ` set qis. poly (?rp q) x = 0)" by force
  also have "\<dots> = (\<exists> q \<in> set qs. rp q x = 0)" unfolding rp qs snd_conv o_def bex_simps set_map
    by simp
  finally show iff: "rp p x = 0 \<longleftrightarrow> (\<exists> q \<in> set qs. rp q x = 0)" by auto
  assume "rp p x = 0"
  with iff obtain q where q: "q \<in> set qs" and rtq: "rp q x = 0" by auto
  then obtain i q' where qi: "(q',i) \<in> set qis" and qq': "q = abs_int_poly q'" unfolding qs by auto
  show "\<exists>! q \<in> set qs. rp q x = 0"
  proof (intro ex1I, intro conjI, rule q, rule rtq, clarify)
    fix r
    assume "r \<in> set qs" and rtr: "rp r x = 0"
    then obtain j r' where rj: "(r',j) \<in> set qis" and rr': "r = abs_int_poly r'" unfolding qs by auto
    from rtr rtq have rtr: "rp r' x = 0" and rtq: "rp q' x = 0"
      unfolding rp rr' qq' by auto
    from rtr rtq have "[:-x,1:] dvd ?rp q'" "[:-x,1:] dvd ?rp r'" unfolding rp
      by (auto simp: poly_eq_0_iff_dvd)
    hence "[:-x,1:] dvd gcd (?rp q') (?rp r')" by simp
    hence "gcd (?rp q') (?rp r') = 0 \<or> degree (gcd (?rp q') (?rp r')) \<noteq> 0"
      by (metis is_unit_gcd_iff is_unit_iff_degree is_unit_pCons_iff one_poly_eq_simps(1))
    hence "gcd q' r' = 0 \<or> degree (gcd q' r') \<noteq> 0"
      unfolding gcd_eq_0_iff degree_of_gcd[of q' r',symmetric] by auto
    hence "\<not> coprime q' r'" by auto
    with sff(3)[OF qi rj] have "q' = r'" by auto
    thus "r = q" unfolding rr' qq' by simp
  qed
qed

lemma factors_int_poly_represents:
  fixes x :: "'a :: {field_char_0,field_gcd}"
  assumes p: "p represents x"
  shows "\<exists> q \<in> set (factors_of_int_poly p).
    q represents x \<and> irreducible q \<and> lead_coeff q > 0  \<and> degree q \<le> degree p"
proof -
  from representsD[OF p] have p: "p \<noteq> 0" and rt: "ipoly p x = 0" by auto
  note fact = factors_of_int_poly[OF refl]
  from fact(2)[OF p, of x] rt obtain q where q: "q \<in> set (factors_of_int_poly p)" and
    rt: "ipoly q x = 0" by auto
  from fact(1)[OF q] rt show ?thesis
    by (intro bexI[OF _ q], auto simp: represents_def irreducible_def)
qed

corollary irreducible_represents_imp_degree:
  fixes x :: "'a :: {field_char_0,field_gcd}"
  assumes "irreducible f" and "f represents x" and "g represents x"
  shows "degree f \<le> degree g"
proof -
  from factors_of_int_poly(1)[OF refl, of _ g] factors_of_int_poly(3)[OF refl, of g x]
     assms(3) obtain h where *: "h represents x" "degree h \<le> degree g" "irreducible h"
    by blast
  let ?af = "abs_int_poly f"
  let ?ah = "abs_int_poly h"
  from assms have af: "irreducible ?af" "?af represents x" "lead_coeff ?af > 0" by fastforce+
  from * have ah: "irreducible ?ah" "?ah represents x" "lead_coeff ?ah > 0" by fastforce+
  from algebraic_imp_represents_unique[of x] af ah have id: "?af = ?ah"
    unfolding algebraic_iff_represents by blast
  show ?thesis using arg_cong[OF id, of degree] \<open>degree h \<le> degree g\<close> by simp
qed

lemma irreducible_preservation:
  fixes x :: "'a :: {field_char_0,field_gcd}"
  assumes irr: "irreducible p"
  and x: "p represents x"
  and y: "q represents y"
  and deg: "degree p \<ge> degree q"
  and f: "\<And> q. q represents y \<Longrightarrow> (f q) represents x \<and> degree (f q) \<le> degree q"
  and pr: "primitive q"
  shows "irreducible q"
proof (rule ccontr)
  define pp where "pp = abs_int_poly p"
  have dp: "degree p \<noteq> 0" using x by (rule represents_degree)
  have dq: "degree q \<noteq> 0" using y by (rule represents_degree)
  from dp have p0: "p \<noteq> 0" by auto
  from x deg irr p0
  have irr: "irreducible pp" and x: "pp represents x" and
    deg: "degree pp \<ge> degree q" and cf_pos: "lead_coeff pp > 0"
    unfolding pp_def lead_coeff_abs_int_poly by (auto intro!: representsI)
  from x have ax: "algebraic x" unfolding algebraic_altdef_ipoly represents_def by blast
  assume "\<not> ?thesis"
  from this irreducible_connect_int[of q] pr have "\<not> irreducible\<^sub>d q" by auto
  from this dq obtain r where
    r: "degree r \<noteq> 0" "degree r < degree q" and "r dvd q" by auto
  then obtain rr where q: "q = r * rr" unfolding dvd_def by auto
  have "degree q = degree r + degree rr" using dq unfolding q
    by (subst degree_mult_eq, auto)
  with r have rr: "degree rr \<noteq> 0" "degree rr < degree q" by auto
  from representsD(2)[OF y, unfolded q hom_distribs]
  have "ipoly r y = 0 \<or> ipoly rr y = 0" by auto
  with r rr have "r represents y \<or> rr represents y" unfolding represents_def by auto
  with r rr obtain r where r: "r represents y" "degree r < degree q" by blast
  from f[OF r(1)] deg r(2) obtain r where r: "r represents x" "degree r < degree pp" by auto
  from factors_int_poly_represents[OF r(1)] r(2) obtain r where
    r: "r represents x" "irreducible r" "lead_coeff r > 0" and deg: "degree r < degree pp" by force
  from algebraic_imp_represents_unique[OF ax] r irr cf_pos x have "r = pp" by auto
  with deg show False by auto
qed

declare irreducible_const_poly_iff [simp]

lemma poly_uminus_irreducible:
  assumes p: "irreducible (p :: int poly)" and deg: "degree p \<noteq> 0"
  shows "irreducible (poly_uminus p)"
proof-
  from deg_nonzero_represents[OF deg] obtain x :: complex where x: "p represents x" by auto
  from represents_uminus[OF x]
  have y: "poly_uminus p represents (- x)" .
  show ?thesis
  proof (rule irreducible_preservation[OF p x y], force)
    from deg irreducible_imp_primitive[OF p] have "primitive p" by auto
    then show "primitive (poly_uminus p)" by simp
    fix q
    assume "q represents (- x)"
    from represents_uminus[OF this] have "(poly_uminus q) represents x" by simp
    thus "(poly_uminus q) represents x \<and> degree (poly_uminus q) \<le> degree q" by auto
  qed
qed

lemma reflect_poly_irreducible:
  fixes x :: "'a :: {field_char_0,field_gcd}"
  assumes p: "irreducible p" and x: "p represents x" and x0: "x \<noteq> 0"
  shows "irreducible (reflect_poly p)"
proof -
  from represents_inverse[OF x0 x]
  have y: "(reflect_poly p) represents (inverse x)" by simp
  from x0 have ix0: "inverse x \<noteq> 0" by auto
  show ?thesis
  proof (rule irreducible_preservation[OF p x y])
    from x irreducible_imp_primitive[OF p]
    show "primitive (reflect_poly p)" by (auto simp: content_reflect_poly)
    fix q
    assume "q represents (inverse x)"
    from represents_inverse[OF ix0 this] have "(reflect_poly q) represents x" by simp
    with degree_reflect_poly_le
    show "(reflect_poly q) represents x \<and> degree (reflect_poly q) \<le> degree q" by auto
  qed (insert p, auto simp: degree_reflect_poly_le)
qed

lemma poly_add_rat_irreducible:
  assumes p: "irreducible p" and deg: "degree p \<noteq> 0"
  shows "irreducible (cf_pos_poly (poly_add_rat r p))"
proof -
  from deg_nonzero_represents[OF deg] obtain x :: complex where x: "p represents x" by auto
  from represents_add_rat[OF x]
  have y: "cf_pos_poly (poly_add_rat r p) represents (of_rat r + x)" by simp
  show ?thesis
  proof (rule irreducible_preservation[OF p x y], force)
    fix q
    assume "q represents (of_rat r + x)"
    from represents_add_rat[OF this, of "- r"] have "(poly_add_rat (- r) q) represents x" by (simp add: of_rat_minus)
    thus "(poly_add_rat (- r) q) represents x \<and> degree (poly_add_rat (- r) q) \<le> degree q" by auto
  qed (insert p, auto)
qed

lemma poly_mult_rat_irreducible:
  assumes p: "irreducible p" and deg: "degree p \<noteq> 0" and r: "r \<noteq> 0"
  shows "irreducible (cf_pos_poly (poly_mult_rat r p))"
proof -
  from deg_nonzero_represents[OF deg] obtain x :: complex where x: "p represents x" by auto
  from represents_mult_rat[OF r x]
  have y: "cf_pos_poly (poly_mult_rat r p) represents (of_rat r * x)" by simp
  show ?thesis
  proof (rule irreducible_preservation[OF p x y], force simp: r)
    fix q
    from r have r': "inverse r \<noteq> 0" by simp
    assume "q represents (of_rat r * x)"
    from represents_mult_rat[OF r' this] have "(poly_mult_rat (inverse r) q) represents x" using r
      by (simp add: of_rat_divide field_simps)
    thus "(poly_mult_rat (inverse r) q) represents x \<and> degree (poly_mult_rat (inverse r) q) \<le> degree q"
      using r by auto
  qed (insert p r, auto)
qed

interpretation coeff_lift_hom:
  factor_preserving_hom "coeff_lift :: 'a :: {comm_semiring_1,semiring_no_zero_divisors} \<Rightarrow> _"
  by (unfold_locales, auto)



end