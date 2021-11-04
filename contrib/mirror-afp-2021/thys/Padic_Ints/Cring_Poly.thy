theory Cring_Poly
  imports "HOL-Algebra.UnivPoly" "HOL-Algebra.Subrings" Function_Ring
begin

text\<open>
  This theory extends the material in \<^theory>\<open>HOL-Algebra.UnivPoly\<close>. The main additions are 
  material on Taylor expansions of polynomials and polynomial derivatives, and various applications
  of the universal property of polynomial evaluation. These include construing polynomials as 
  functions from the base ring to itself, composing one polynomial with another, and extending
  homomorphisms between rings to homomoprhisms of their polynomial rings. These formalizations 
  are necessary components of the proof of Hensel's lemma for $p$-adic integers, and for the 
  proof of $p$-adic quantifier elimination. \<close>

lemma(in ring) ring_hom_finsum:
  assumes "h \<in> ring_hom R S"
  assumes "ring S"
  assumes "finite I"
  assumes "F \<in> I \<rightarrow> carrier R"
  shows "h (finsum R F I) = finsum S (h \<circ> F) I"
proof- 
  have I: "(h \<in> ring_hom R S \<and> F \<in> I \<rightarrow> carrier R) \<longrightarrow> h (finsum R F I) = finsum S (h \<circ> F) I"
    apply(rule finite_induct, rule assms)
    using assms ring_hom_zero[of h R S] 
    apply (metis abelian_group_def abelian_monoid.finsum_empty is_ring ring_def)
  proof(rule)
    fix A a 
    assume A: "finite A" "a \<notin> A" "h \<in> ring_hom R S \<and> F \<in> A \<rightarrow> carrier R \<longrightarrow>
           h (finsum R F A) = finsum S (h \<circ> F) A" "h \<in> ring_hom R S \<and> F \<in> insert a A \<rightarrow> carrier R"
    have 0: "h \<in> ring_hom R S \<and> F \<in> A \<rightarrow> carrier R "
      using A by auto 
    have 1: "h (finsum R F A) = finsum S (h \<circ> F) A"
      using A 0 by auto 
    have 2: "abelian_monoid S"
      using assms ring_def abelian_group_def by auto
    have 3: "h (F a \<oplus> finsum R F A) = h (F a) \<oplus>\<^bsub>S\<^esub> (finsum S (h \<circ> F) A) "
      using ring_hom_add assms finsum_closed 1 A(4) by fastforce
    have 4: "finsum R F (insert a A) = F a \<oplus> finsum R F A"
      using finsum_insert[of A a F] A assms by auto 
    have 5: "finsum S (h \<circ> F) (insert a A) = (h \<circ> F) a \<oplus>\<^bsub>S\<^esub> finsum S (h \<circ> F) A"
      apply(rule abelian_monoid.finsum_insert[of S A a "h \<circ> F"])
          apply (simp add: "2")
         apply(rule A)
        apply(rule A)
      using ring_hom_closed A  "0" apply fastforce
      using A ring_hom_closed by auto 
    show "h (finsum R F (insert a A)) =
           finsum S (h \<circ> F) (insert a A)"
      unfolding 4 5 3 by auto 
  qed
  thus ?thesis using assms by blast 
qed

lemma(in ring) ring_hom_a_inv:
  assumes "ring S"
  assumes "h \<in> ring_hom R S"
  assumes "b \<in> carrier R"
  shows "h (\<ominus> b) =  \<ominus>\<^bsub>S\<^esub> h b"
proof-
  have "h b \<oplus>\<^bsub>S\<^esub> h (\<ominus> b) = \<zero>\<^bsub>S\<^esub>"
    by (metis (no_types, hide_lams) abelian_group.a_inv_closed assms(1) assms(2) assms(3) 
        is_abelian_group local.ring_axioms r_neg ring_hom_add ring_hom_zero)        
  then show ?thesis 
    by (metis (no_types, lifting) abelian_group.minus_equality add.inv_closed assms(1) 
        assms(2) assms(3) ring.is_abelian_group ring.ring_simprules(10) ring_hom_closed)
qed

lemma(in ring) ring_hom_minus:
  assumes "ring S"
  assumes "h \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "h (a \<ominus> b) = h a \<ominus>\<^bsub>S\<^esub> h b" 
  using assms ring_hom_add[of h R S a "\<ominus>\<^bsub>R\<^esub> b"]
  unfolding a_minus_def 
  using ring_hom_a_inv[of S h b] by auto 

lemma ring_hom_nat_pow:
  assumes "ring R"
  assumes "ring S"
  assumes "h \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  shows "h (a[^]\<^bsub>R\<^esub>(n::nat)) = (h a)[^]\<^bsub>S\<^esub>(n::nat)"
  using assms by (simp add: ring_hom_ring.hom_nat_pow ring_hom_ringI2)

lemma (in ring) Units_not_right_zero_divisor:
  assumes "a \<in> Units R"
  assumes "b \<in> carrier R"
  assumes "a \<otimes> b = \<zero>"
  shows  "b = \<zero>"
proof- 
  have "inv a \<otimes> a \<otimes> b = \<zero> "
    using assms Units_closed Units_inv_closed r_null m_assoc[of "inv a" a b] by presburger
  thus ?thesis using assms 
    by (metis Units_l_inv l_one)    
qed

lemma (in ring) Units_not_left_zero_divisor:
  assumes "a \<in> Units R"
  assumes "b \<in> carrier R"
  assumes "b \<otimes> a = \<zero>"
  shows  "b = \<zero>"
proof- 
  have "b \<otimes> (a \<otimes> inv a) = \<zero> "
    using assms Units_closed Units_inv_closed l_null m_assoc[of b a"inv a"] by presburger
  thus ?thesis using assms 
    by (metis Units_r_inv r_one)    
qed

lemma (in cring) finsum_remove:
  assumes "\<And>i. i \<in> Y \<Longrightarrow> f i \<in> carrier R"
  assumes "finite Y"
  assumes "i \<in> Y"
  shows "finsum R f Y = f i \<oplus> finsum R f (Y - {i})"
proof- 
  have "finsum R f (insert i (Y - {i})) = f i \<oplus> finsum R f (Y - {i})"
    apply(rule finsum_insert)
    using assms apply blast apply blast using assms apply blast
    using assms by blast 
  thus ?thesis using assms 
    by (metis insert_Diff)
qed


type_synonym degree = nat
text\<open>The composition of two ring homomorphisms is a ring homomorphism\<close>
lemma ring_hom_compose:                                                                                                           
  assumes "ring R"
  assumes "ring S"
  assumes "ring T"
  assumes "h \<in> ring_hom R S"
  assumes "g \<in> ring_hom S T"
  assumes "\<And>c. c \<in> carrier R \<Longrightarrow> f c = g (h c)"
  shows "f \<in>  ring_hom R T"
proof(rule ring_hom_memI)
  show "\<And>x. x \<in> carrier R \<Longrightarrow> f x \<in> carrier T"
    using assms  by (metis ring_hom_closed)
  show " \<And>x y. x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> f (x \<otimes>\<^bsub>R\<^esub> y) = f x \<otimes>\<^bsub>T\<^esub> f y"
  proof-
    fix x y
    assume A: "x \<in>  carrier R" "y \<in>  carrier R"
    show "f (x \<otimes>\<^bsub>R\<^esub> y) = f x \<otimes>\<^bsub>T\<^esub> f y"
    proof-
      have  "f (x \<otimes>\<^bsub>R\<^esub> y) = g (h (x \<otimes>\<^bsub>R\<^esub> y))"
        by (simp add: A(1) A(2) assms(1) assms(6) ring.ring_simprules(5))
      then have  "f (x \<otimes>\<^bsub>R\<^esub> y) = g ((h x) \<otimes>\<^bsub>S\<^esub> (h y))"
        using A(1) A(2) assms(4) ring_hom_mult by fastforce
      then have  "f (x \<otimes>\<^bsub>R\<^esub> y) = g (h x) \<otimes>\<^bsub>T\<^esub> g (h y)"
        using A(1) A(2) assms(4) assms(5) ring_hom_closed ring_hom_mult by fastforce
      then show ?thesis 
        by (simp add: A(1) A(2) assms(6))
    qed
  qed
  show "\<And>x y. x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> f (x \<oplus>\<^bsub>R\<^esub> y) = f x \<oplus>\<^bsub>T\<^esub> f y"
  proof-
    fix x y
    assume A: "x \<in>  carrier R" "y \<in>  carrier R"
    show "f (x \<oplus>\<^bsub>R\<^esub> y) = f x \<oplus>\<^bsub>T\<^esub> f y"
    proof-
      have  "f (x \<oplus>\<^bsub>R\<^esub> y) = g (h (x \<oplus>\<^bsub>R\<^esub> y))"
        by (simp add: A(1) A(2) assms(1) assms(6) ring.ring_simprules(1))
      then have  "f (x \<oplus>\<^bsub>R\<^esub> y) = g ((h x) \<oplus>\<^bsub>S\<^esub> (h y))"
        using A(1) A(2) assms(4) ring_hom_add by fastforce
      then have  "f (x \<oplus>\<^bsub>R\<^esub> y) = g (h x) \<oplus>\<^bsub>T\<^esub> g (h y)"
        by (metis (no_types, hide_lams) A(1) A(2) assms(4) assms(5) ring_hom_add ring_hom_closed)
      then show ?thesis
        by (simp add: A(1) A(2) assms(6))
    qed
  qed
  show "f \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>T\<^esub>" 
    by (metis assms(1) assms(4) assms(5) assms(6) ring.ring_simprules(6) ring_hom_one)
qed


(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Basic Notions about Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)
context UP_ring
begin


text\<open>rings are closed under monomial terms\<close>
lemma monom_term_car:
  assumes "c \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "c \<otimes> x[^](n::nat) \<in> carrier R"
  using assms monoid.nat_pow_closed 
  by blast

text\<open>Univariate polynomial ring over R\<close>

lemma P_is_UP_ring:
"UP_ring R"
  by (simp add: UP_ring_axioms)

text\<open>Degree function\<close>
abbreviation(input) degree  where
"degree f \<equiv>  deg R f"

lemma UP_car_memI:
  assumes "\<And>n. n > k \<Longrightarrow> p n = \<zero>"
  assumes "\<And>n. p n \<in> carrier R"
  shows "p \<in> carrier P"
proof-
  have "bound \<zero> k p"
    by (simp add: assms(1) bound.intro)
  then show ?thesis 
    by (metis (no_types, lifting) P_def UP_def assms(2) mem_upI partial_object.select_convs(1))
qed

lemma(in UP_cring) UP_car_memI':
  assumes "\<And>x. g x \<in> carrier R"
  assumes "\<And>x. x > k \<Longrightarrow> g x = \<zero>"
  shows "g \<in> carrier (UP R)"
proof-
  have "bound \<zero> k g"
    using assms unfolding bound_def by blast 
  then show ?thesis 
    using P_def UP_car_memI assms(1) by blast
qed

lemma(in UP_cring) UP_car_memE:
  assumes "g \<in> carrier (UP R)"
  shows "\<And>x. g x \<in> carrier R"
        "\<And>x. x > (deg R g) \<Longrightarrow> g x = \<zero>"
  using P_def assms UP_def[of R] apply (simp add: mem_upD)
  using assms UP_def[of R] up_def[of R] 
  by (smt R.ring_axioms UP_ring.deg_aboveD UP_ring.intro partial_object.select_convs(1) restrict_apply up_ring.simps(2))
  
end

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Lemmas About Coefficients\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

context UP_ring
begin
text\<open>The goal here is to reduce dependence on the function coeff from Univ\_Poly, in favour of using
a polynomial itself as its coefficient function.\<close>

lemma coeff_simp:
  assumes "f \<in> carrier P"
  shows "coeff (UP R)  f = f "
proof fix x show "coeff (UP R) f x = f x" 
    using assms P_def UP_def[of R] by auto 
qed

text\<open>Coefficients are in R\<close>

lemma cfs_closed:
  assumes "f \<in> carrier P"
  shows "f n \<in> carrier R"
  using assms coeff_simp[of f]  P_def coeff_closed 
  by fastforce

lemma cfs_monom:
  "a \<in> carrier R ==> (monom P a m) n = (if m=n then a else \<zero>)"
using coeff_simp  P_def coeff_monom monom_closed by auto

lemma cfs_zero [simp]: "\<zero>\<^bsub>P\<^esub> n = \<zero>" 
  using P_def UP_zero_closed coeff_simp coeff_zero by auto

lemma cfs_one [simp]: "\<one>\<^bsub>P\<^esub> n = (if n=0 then \<one> else \<zero>)"
  by (metis P_def R.one_closed UP_ring.cfs_monom UP_ring_axioms monom_one)

lemma cfs_smult [simp]:
  "[| a \<in> carrier R; p \<in> carrier P |] ==> (a \<odot>\<^bsub>P\<^esub> p) n = a \<otimes> p n"
  using P_def UP_ring.coeff_simp UP_ring_axioms UP_smult_closed coeff_smult by fastforce
  
lemma cfs_add [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> (p \<oplus>\<^bsub>P\<^esub> q) n = p n \<oplus> q n"
  by (metis P.add.m_closed P_def UP_ring.coeff_add UP_ring.coeff_simp UP_ring_axioms)

lemma cfs_a_inv [simp]:
  assumes R: "p \<in> carrier P"
  shows "(\<ominus>\<^bsub>P\<^esub> p) n = \<ominus> (p n)"
  using P.add.inv_closed P_def UP_ring.coeff_a_inv UP_ring.coeff_simp UP_ring_axioms assms 
  by fastforce

lemma cfs_minus [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> (p \<ominus>\<^bsub>P\<^esub> q) n = p n \<ominus> q n"
  using P.minus_closed P_def coeff_minus coeff_simp by auto

lemma cfs_monom_mult_r:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(monom P a n \<otimes>\<^bsub>P\<^esub> p) (k + n) = a \<otimes> p k"
  using coeff_monom_mult assms P.m_closed P_def coeff_simp monom_closed by auto

lemma(in UP_cring) cfs_monom_mult_l:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(p \<otimes>\<^bsub>P\<^esub> monom P a n) (k + n) = a \<otimes> p k"
  using UP_m_comm assms(1) assms(2) cfs_monom_mult_r by auto

lemma(in UP_cring) cfs_monom_mult_l':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "m \<ge> n"
  shows "(f \<otimes>\<^bsub>P\<^esub> (monom P a n)) m = a \<otimes> (f (m - n))"
  using cfs_monom_mult_l[of f a n "m-n"] assms 
  by simp

lemma(in UP_cring) cfs_monom_mult_r':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "m \<ge> n"
  shows "((monom P a n) \<otimes>\<^bsub>P\<^esub> f) m = a \<otimes> (f (m - n))"
  using cfs_monom_mult_r[of f a n "m-n"] assms 
  by simp 
end
  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Degree Bound Lemmas\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

context UP_ring
begin

lemma bound_deg_sum:
  assumes " f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree f  \<le> n"
  assumes "degree g \<le> n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) \<le> n"
  using P_def UP_ring_axioms assms(1) assms(2) assms(3) assms(4) 
  by (meson deg_add max.boundedI order_trans)

lemma bound_deg_sum':
  assumes " f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree f < n"
  assumes "degree g < n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) < n"
  using P_def UP_ring_axioms assms(1) assms(2) 
        assms(3) assms(4) 
  by (metis bound_deg_sum le_neq_implies_less less_imp_le_nat not_less)        

lemma equal_deg_sum:
  assumes " f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree f < n"
  assumes "degree g = n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) = n"
proof-
  have 0: "degree (f \<oplus>\<^bsub>P\<^esub> g) \<le>n"
    using assms bound_deg_sum 
          P_def UP_ring_axioms by auto
  show "degree (f \<oplus>\<^bsub>P\<^esub> g) = n"
  proof(rule ccontr)
    assume "degree (f \<oplus>\<^bsub>P\<^esub> g) \<noteq> n "
    then have 1: "degree (f \<oplus>\<^bsub>P\<^esub> g) < n"
      using 0 by auto 
    have 2: "degree (\<ominus>\<^bsub>P\<^esub> f) < n"
      using assms by simp
    have 3: "g = (f \<oplus>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> f)"
      using assms 
      by (simp add: P.add.m_comm P.r_neg1)
    then show False using 1 2 3 assms 
      by (metis UP_a_closed UP_a_inv_closed deg_add leD le_max_iff_disj)
  qed
qed

lemma equal_deg_sum':
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "degree g < n"
  assumes "degree f = n"
  shows "degree (f \<oplus>\<^bsub>P\<^esub> g) = n"
  using P_def UP_a_comm UP_ring.equal_deg_sum UP_ring_axioms assms(1) assms(2) assms(3) assms(4)
  by fastforce

lemma degree_of_sum_diff_degree:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "degree (p \<oplus>\<^bsub>P\<^esub> q) = degree p" 
  by(rule equal_deg_sum', auto simp: assms)

lemma degree_of_difference_diff_degree:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "degree (p \<ominus>\<^bsub>P\<^esub> q) = degree p" 
proof-
  have A: "(p \<ominus>\<^bsub>P\<^esub> q) = p \<oplus>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> q)" 
    by (simp add: P.minus_eq)
  have "degree (\<ominus>\<^bsub>P\<^esub> q) = degree q " 
    by (simp add: assms(2))
  then show ?thesis 
    using assms A 
    by (simp add: degree_of_sum_diff_degree)
qed

lemma (in UP_ring) deg_diff_by_const:
  assumes "g \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  assumes "h = g \<oplus>\<^bsub>UP R\<^esub> up_ring.monom (UP R) a 0"
  shows "deg R g = deg R h"
  unfolding assms using assms 
  by (metis P_def UP_ring.bound_deg_sum UP_ring.deg_monom_le UP_ring.monom_closed UP_ring_axioms degree_of_sum_diff_degree gr_zeroI not_less)

lemma (in UP_ring) deg_diff_by_const':
  assumes "g \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  assumes "h = g \<ominus>\<^bsub>UP R\<^esub> up_ring.monom (UP R) a 0"
  shows "deg R g = deg R h"
  apply(rule deg_diff_by_const[of _  "\<ominus> a"])
  using assms apply blast 
  using assms apply blast
  by (metis P.minus_eq P_def assms(2) assms(3) monom_a_inv)

lemma(in UP_ring) deg_gtE:
  assumes "p \<in> carrier P"
  assumes "i > deg R p"
  shows "p i = \<zero>"
  using assms  P_def coeff_simp deg_aboveD by metis
end

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Leading Term Function\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

definition leading_term where 
"leading_term R f = monom (UP R) (f (deg R f)) (deg R f)"

context UP_ring
begin

abbreviation(input) ltrm  where
"ltrm f \<equiv> monom P (f (deg R f)) (deg R f)"

text\<open>leading term is a polynomial\<close>
lemma ltrm_closed:
  assumes "f \<in> carrier P"
  shows "ltrm f \<in> carrier P"
  using assms 
  by (simp add: cfs_closed)  
  
text\<open>Simplified coefficient function description for leading term\<close>
lemma ltrm_coeff:
  assumes "f \<in> carrier P"
  shows "coeff P (ltrm f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
    using assms 
    by (simp add: cfs_closed)

lemma ltrm_cfs:
  assumes "f \<in> carrier P"
  shows "(ltrm f) n  = (if (n = degree f) then (f (degree f)) else \<zero>)"
  using assms 
  by (simp add: cfs_closed cfs_monom)

lemma ltrm_cfs_above_deg:
  assumes "f \<in> carrier P"
  assumes "n > degree f"
  shows "ltrm f n = \<zero>"
  using assms 
  by (simp add: ltrm_cfs)

text\<open>The leading term of f has the same degree as f\<close>

lemma deg_ltrm:
  assumes "f \<in> carrier P"
  shows "degree (ltrm f) = degree f"
  using assms 
  by (metis P_def UP_ring.lcoeff_nonzero_deg UP_ring_axioms cfs_closed coeff_simp deg_const deg_monom)

text\<open>Subtracting the leading term yields a drop in degree\<close>

lemma minus_ltrm_degree_drop:
  assumes "f \<in> carrier P"
  assumes "degree f = Suc n"
  shows "degree (f \<ominus>\<^bsub>P\<^esub> (ltrm f)) \<le> n"
proof(rule UP_ring.deg_aboveI)
  show C0: "UP_ring R" 
    by (simp add: UP_ring_axioms)    
  show C1: "f \<ominus>\<^bsub>P\<^esub> ltrm f \<in> carrier (UP R)"
    using assms ltrm_closed P.minus_closed P_def 
    by blast     
  show C2: "\<And>m. n < m \<Longrightarrow> coeff (UP R) (f \<ominus>\<^bsub>P\<^esub> ltrm f) m = \<zero>"
  proof-
    fix m
    assume A: "n<m"
    show "coeff (UP R) (f \<ominus>\<^bsub>P\<^esub> ltrm f) m = \<zero>"
    proof(cases " m = Suc n")
      case True
      have B: "f m \<in> carrier R" 
        using UP.coeff_closed P_def assms(1) cfs_closed by blast       
      have "m = degree f"
        using True by (simp add: assms(2))
      then have "f m = (ltrm f) m" 
        using ltrm_cfs assms(1) by auto 
      then have "(f m) \<ominus>\<^bsub>R\<^esub>( ltrm f) m = \<zero>"
        using B UP_ring_def P_is_UP_ring 
          B R.add.r_inv R.is_abelian_group abelian_group.minus_eq by fastforce
      then have "(f \<ominus>\<^bsub>UP R\<^esub> ltrm f) m = \<zero>"
        by (metis C1 ltrm_closed P_def assms(1) coeff_minus coeff_simp)        
      then show ?thesis 
        using C1 P_def UP_ring.coeff_simp UP_ring_axioms by fastforce
    next
      case False
      have D0: "m > degree f" using False 
        using A assms(2) by linarith
       have B: "f m \<in> carrier R" 
         using UP.coeff_closed P_def assms(1) cfs_closed 
         by blast
       have "f m = (ltrm f) m" 
         using D0 ltrm_cfs_above_deg P_def assms(1) coeff_simp deg_aboveD 
         by auto 
      then show ?thesis 
        by (metis B ltrm_closed P_def R.r_neg UP_ring.coeff_simp UP_ring_axioms a_minus_def assms(1) coeff_minus)       
    qed
  qed
qed

lemma ltrm_decomp:
  assumes "f \<in> carrier P"
  assumes "degree f >(0::nat)"
  obtains g where "g \<in> carrier P \<and> f = g \<oplus>\<^bsub>P\<^esub> (ltrm f) \<and> degree g < degree f"
proof-
  have 0: "f \<ominus>\<^bsub>P\<^esub> (ltrm f) \<in> carrier P"
    using ltrm_closed assms(1) by blast    
  have 1: "f = (f \<ominus>\<^bsub>P\<^esub> (ltrm f)) \<oplus>\<^bsub>P\<^esub> (ltrm f)"
    using assms 
    by (metis "0" ltrm_closed P.add.inv_solve_right P.minus_eq)
  show ?thesis using assms 0 1 minus_ltrm_degree_drop[of f]
    by (metis ltrm_closed Suc_diff_1 Suc_n_not_le_n deg_ltrm equal_deg_sum' linorder_neqE_nat that)
qed

text\<open>leading term of a sum\<close>
lemma coeff_of_sum_diff_degree0:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < n"
  shows "(p \<oplus>\<^bsub>P\<^esub> q) n = p n"
  using assms P_def UP_ring.deg_aboveD UP_ring_axioms cfs_add coeff_simp cfs_closed deg_aboveD 
  by auto

lemma coeff_of_sum_diff_degree1:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "(p \<oplus>\<^bsub>P\<^esub> q) (degree p) = p (degree p)"
  using assms(1) assms(2) assms(3) coeff_of_sum_diff_degree0 by blast



lemma ltrm_of_sum_diff_degree:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree p > degree q"
  shows "ltrm (p \<oplus>\<^bsub>P\<^esub> q) = ltrm p" 
  unfolding leading_term_def 
  using assms(1) assms(2) assms(3) coeff_of_sum_diff_degree1 degree_of_sum_diff_degree 
  by presburger

text\<open>leading term of a monomial\<close>

lemma ltrm_monom:
  assumes "a \<in> carrier R"
  assumes "f = monom P a n"
  shows "ltrm f = f"
  unfolding leading_term_def
  by (metis P_def UP_ring.cfs_monom UP_ring.monom_zero UP_ring_axioms assms(1) assms(2) deg_monom)  

lemma ltrm_monom_simp:
  assumes "a \<in> carrier R"
  shows "ltrm (monom P a n) = monom P a n"
  using assms ltrm_monom by auto

lemma ltrm_inv_simp[simp]:
  assumes "f \<in> carrier P"
  shows "ltrm (ltrm f) = ltrm f"
  by (metis assms deg_ltrm ltrm_cfs)

lemma ltrm_deg_0:
  assumes "p \<in> carrier P"
  assumes "degree p = 0"
  shows "ltrm p = p"
  using ltrm_monom assms P_def UP_ring.deg_zero_impl_monom UP_ring_axioms coeff_simp
  by fastforce

lemma ltrm_prod_ltrm:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "ltrm ((ltrm p) \<otimes>\<^bsub>P\<^esub> (ltrm q)) = (ltrm p) \<otimes>\<^bsub>P\<^esub> (ltrm q)"
  using ltrm_monom R.m_closed assms(1) assms(2) cfs_closed monom_mult
  by metis 

text\<open>lead coefficient function\<close>

abbreviation(input) lcf where
"lcf p \<equiv> p (deg R p)"

lemma(in UP_ring) lcf_ltrm:
"ltrm p = monom P (lcf p) (degree p)"
  by auto

lemma lcf_closed:
  assumes "f \<in> carrier P"
  shows "lcf f \<in> carrier R"
  by (simp add: assms cfs_closed)

lemma(in UP_cring) lcf_monom:
  assumes "a \<in> carrier R"
  shows "lcf (monom P a n) = a" "lcf (monom (UP R) a n) = a"
  using assms deg_monom cfs_monom apply fastforce
  by (metis UP_ring.cfs_monom UP_ring.deg_monom UP_ring_axioms assms)


end 

text\<open>Function which truncates a polynomial by removing the leading term\<close>

definition truncate where
"truncate R f = f \<ominus>\<^bsub>(UP R)\<^esub> (leading_term R f)"

context UP_ring
begin 

abbreviation(input) trunc where
"trunc \<equiv> truncate R"

lemma trunc_closed:
  assumes "f \<in> carrier P"
  shows "trunc f \<in> carrier P"
  using assms unfolding truncate_def 
  by (metis ltrm_closed P_def UP_ring.UP_ring UP_ring_axioms leading_term_def ring.ring_simprules(4))

lemma trunc_simps:
  assumes "f \<in> carrier P"
  shows "f = (trunc f) \<oplus>\<^bsub>P\<^esub> (ltrm f)"
        "f \<ominus>\<^bsub>P\<^esub> (trunc f) = ltrm f"   
  apply (metis ltrm_closed P.add.inv_solve_right P.minus_closed P_def a_minus_def assms Cring_Poly.truncate_def leading_term_def)
  using trunc_closed[of f] ltrm_closed[of f] P_def P.add.inv_solve_right[of "ltrm f" f "trunc f"]
        assms  unfolding UP_cring_def
  by (metis P.add.inv_closed P.add.m_lcomm P.add.r_inv_ex P.minus_eq P.minus_minus
      P.r_neg2 P.r_zero Cring_Poly.truncate_def leading_term_def)

lemma trunc_zero:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "trunc f = \<zero>\<^bsub>P\<^esub>"
  unfolding truncate_def 
  using assms ltrm_deg_0[of f] 
  by (metis P.r_neg P_def a_minus_def leading_term_def)

lemma trunc_degree:
  assumes "f \<in> carrier P"
  assumes "degree f > 0"
  shows "degree (trunc f) < degree f"
  unfolding truncate_def using assms 
  by (metis ltrm_closed ltrm_decomp P.add.right_cancel Cring_Poly.truncate_def trunc_closed trunc_simps(1))

text\<open>The coefficients of trunc agree with f for small degree\<close>

lemma trunc_cfs:
  assumes "p \<in> carrier P"
  assumes "n < degree p"
  shows " (trunc p) n = p n"
  using P_def assms(1) assms(2) unfolding truncate_def 
  by (smt ltrm_closed ltrm_cfs R.minus_zero R.ring_axioms UP_ring.cfs_minus
      UP_ring_axioms a_minus_def cfs_closed leading_term_def nat_neq_iff ring.ring_simprules(15))

text\<open>monomial predicate\<close>

definition is_UP_monom where
"is_UP_monom = (\<lambda>f. f \<in> carrier (UP R) \<and> f = ltrm f)"

lemma is_UP_monomI:
  assumes "a \<in> carrier R"
  assumes "p = monom P a n"
  shows "is_UP_monom p"
  using assms(1) assms(2) is_UP_monom_def ltrm_monom P_def monom_closed 
  by auto
  
lemma is_UP_monomI':
  assumes "f \<in> carrier (UP R)"
  assumes "f = ltrm f"
  shows "is_UP_monom f"
  using assms P_def unfolding is_UP_monom_def by blast 

lemma monom_is_UP_monom:
  assumes "a \<in> carrier R"
  shows "is_UP_monom (monom P a n)" "is_UP_monom (monom (UP R) a n)"
  using assms P_def ltrm_monom_simp monom_closed
  unfolding is_UP_monom_def  
  by auto

lemma is_UP_monomE:
  assumes "is_UP_monom f"
  shows "f \<in> carrier P" "f = monom P (lcf f) (degree f)"  "f = monom (UP R) (lcf f) (degree f)"
  using assms unfolding is_UP_monom_def 
  by(auto simp: P_def ) 

lemma ltrm_is_UP_monom:
  assumes "p \<in> carrier P"
  shows "is_UP_monom (ltrm p)"
  using assms 
  by (simp add: cfs_closed monom_is_UP_monom(1))

lemma is_UP_monom_mult:
  assumes "is_UP_monom p"
  assumes "is_UP_monom q"
  shows "is_UP_monom (p \<otimes>\<^bsub>P\<^esub> q)"
  apply(rule is_UP_monomI')
  using assms is_UP_monomE P_def UP_mult_closed 
  apply simp  
  using assms is_UP_monomE[of p] is_UP_monomE[of q] 
        P_def monom_mult 
  by (metis lcf_closed ltrm_monom R.m_closed)
end 

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Properties of Leading Terms and Leading Coefficients in Commutative Rings and Domains\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

context UP_cring
begin

lemma cring_deg_mult:
  assumes "q \<in> carrier P"
  assumes "p \<in> carrier P"
  assumes "lcf q \<otimes> lcf p \<noteq>\<zero>"
  shows "degree (q \<otimes>\<^bsub>P\<^esub> p) = degree p + degree q"
proof-
  have "q \<otimes>\<^bsub>P\<^esub> p = (trunc q \<oplus>\<^bsub>P\<^esub> ltrm q) \<otimes>\<^bsub>P\<^esub> (trunc p \<oplus>\<^bsub>P\<^esub> ltrm p)"
    using assms(1) assms(2) trunc_simps(1) by auto
  then have "q \<otimes>\<^bsub>P\<^esub> p = (trunc q \<oplus>\<^bsub>P\<^esub> ltrm q) \<otimes>\<^bsub>P\<^esub> (trunc p \<oplus>\<^bsub>P\<^esub> ltrm p)"
    by linarith
  then have 0: "q \<otimes>\<^bsub>P\<^esub> p = (trunc q  \<otimes>\<^bsub>P\<^esub> (trunc p \<oplus>\<^bsub>P\<^esub> ltrm p)) \<oplus>\<^bsub>P\<^esub> ( ltrm q \<otimes>\<^bsub>P\<^esub> (trunc p \<oplus>\<^bsub>P\<^esub> ltrm p))"
    by (simp add: P.l_distr assms(1) assms(2) ltrm_closed trunc_closed)
  have 1: "(trunc q  \<otimes>\<^bsub>P\<^esub> (trunc p \<oplus>\<^bsub>P\<^esub> ltrm p)) (degree p + degree q) = \<zero>"
  proof(cases "degree q = 0")
    case True
    then show ?thesis 
      using assms(1) assms(2) trunc_simps(1) trunc_zero by auto           
  next
    case False
    have "degree ((trunc q)  \<otimes>\<^bsub>P\<^esub> p) \<le> degree (trunc q) + degree p"
      using assms trunc_simps[of q]  deg_mult_ring[of "trunc q" p]  trunc_closed 
      by blast      
    then have "degree (trunc q  \<otimes>\<^bsub>P\<^esub> (trunc p \<oplus>\<^bsub>P\<^esub> ltrm p)) < degree q + degree p"
      using False assms(1) assms(2) trunc_degree trunc_simps(1) by fastforce
    then show ?thesis 
      by (metis P_def UP_mult_closed UP_ring.coeff_simp UP_ring_axioms
          add.commute assms(1) assms(2) deg_belowI not_less trunc_closed trunc_simps(1))      
  qed
  have 2: "(q \<otimes>\<^bsub>P\<^esub> p) (degree p + degree q) = 
                   ( ltrm q \<otimes>\<^bsub>P\<^esub> (trunc p \<oplus>\<^bsub>P\<^esub> ltrm p)) (degree p + degree q)"
    using 0 1 assms cfs_closed trunc_closed by auto       
  have 3: "(q \<otimes>\<^bsub>P\<^esub> p) (degree p + degree q) = 
                   ( ltrm q \<otimes>\<^bsub>P\<^esub> trunc p) (degree p + degree q) \<oplus> ( ltrm q \<otimes>\<^bsub>P\<^esub> ltrm p) (degree p + degree q)"
    by (simp add: "2" ltrm_closed UP_r_distr assms(1) assms(2) trunc_closed)   
  have 4: "( ltrm q \<otimes>\<^bsub>P\<^esub> trunc p) (degree p + degree q) = \<zero>"
  proof(cases "degree p = 0")
    case True
    then show ?thesis 
      using "2" "3" assms(1) assms(2) cfs_closed ltrm_closed trunc_zero by auto            
  next
    case False
    have "degree ( ltrm q \<otimes>\<^bsub>P\<^esub> trunc p) \<le> degree (ltrm q) + degree (trunc p)"
      using assms trunc_simps deg_mult_ring ltrm_closed trunc_closed by presburger              
    then have "degree ( ltrm q \<otimes>\<^bsub>P\<^esub> trunc p) < degree q + degree p"
      using False assms(1) assms(2) trunc_degree trunc_simps(1) deg_ltrm by fastforce 
    then show ?thesis 
      by (metis ltrm_closed P_def UP_mult_closed UP_ring.coeff_simp UP_ring_axioms add.commute assms(1) assms(2) deg_belowI not_less trunc_closed)          
  qed
  have 5: "(q \<otimes>\<^bsub>P\<^esub> p) (degree p + degree q) = ( ltrm q \<otimes>\<^bsub>P\<^esub> ltrm p) (degree p + degree q)"
    by (simp add: "3" "4" assms(1) assms(2) cfs_closed)   
  have 6: "ltrm q \<otimes>\<^bsub>P\<^esub> ltrm p = monom P (lcf q \<otimes> lcf p) (degree p + degree q)"
    unfolding  leading_term_def 
    by (metis P_def UP_ring.monom_mult UP_ring_axioms add.commute assms(1) assms(2) cfs_closed)
  have 7: "( ltrm q \<otimes>\<^bsub>P\<^esub> ltrm p) (degree p + degree q) \<noteq>\<zero>"
    using 5  6 assms 
    by (metis R.m_closed cfs_closed cfs_monom)   
  have 8: "degree (q \<otimes>\<^bsub>P\<^esub> p) \<ge>degree p + degree q"
    using 5 6 7 P_def UP_mult_closed assms(1) assms(2) 
    by (simp add: UP_ring.coeff_simp UP_ring_axioms deg_belowI)    
  then show ?thesis 
    using assms(1) assms(2) deg_mult_ring by fastforce
qed

text\<open>leading term is multiplicative\<close>

lemma ltrm_of_sum_diff_deg:
  assumes "q \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  assumes "degree q < n"
  assumes "p = q \<oplus>\<^bsub>P\<^esub> (monom P a n)"
  shows "ltrm p =  (monom P a n)"
proof-
  have 0: "degree  (monom P a n) = n" 
    by (simp add: assms(2) assms(3))
  have 1: "(monom P a n) \<in> carrier P"
    using assms(2) by auto
  have 2: "ltrm ((monom P a n) \<oplus>\<^bsub>P\<^esub> q) = ltrm (monom P a n)"
    using assms ltrm_of_sum_diff_degree[of "(monom P a n)" q] 1  "0" by linarith
  then show ?thesis 
    using UP_a_comm assms(1) assms(2) assms(5) ltrm_monom by auto
qed

lemma(in UP_cring) ltrm_smult_cring:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "lcf p \<otimes> a \<noteq> \<zero>"
  shows "ltrm (a \<odot>\<^bsub>P\<^esub>p) = a\<odot>\<^bsub>P\<^esub>(ltrm p)"
  using assms 
  by (smt lcf_monom(1) P_def R.m_closed R.m_comm cfs_closed cfs_smult coeff_simp
      cring_deg_mult deg_monom deg_ltrm monom_closed monom_mult_is_smult monom_mult_smult) 

lemma(in UP_cring) deg_zero_ltrm_smult_cring:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "degree p = 0"
  shows "ltrm (a \<odot>\<^bsub>P\<^esub>p) = a\<odot>\<^bsub>P\<^esub>(ltrm p)"
  by (metis ltrm_deg_0 assms(1) assms(2) assms(3) deg_smult_decr le_0_eq module.smult_closed module_axioms)

lemma(in UP_domain) ltrm_smult:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "ltrm (a \<odot>\<^bsub>P\<^esub>p) = a\<odot>\<^bsub>P\<^esub>(ltrm p)"
  by (metis lcf_closed ltrm_closed ltrm_smult_cring P_def R.integral_iff UP_ring.deg_ltrm 
      UP_ring_axioms UP_smult_zero assms(1) assms(2) cfs_zero deg_nzero_nzero deg_zero_ltrm_smult_cring monom_zero)

lemma(in UP_cring) cring_ltrm_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "lcf p \<otimes> lcf q \<noteq> \<zero>"
  shows "ltrm (p \<otimes>\<^bsub>P\<^esub> q) = (ltrm p) \<otimes>\<^bsub>P\<^esub> (ltrm q)"
proof(cases "degree p = 0 \<or> degree q = 0")
  case True
  then show ?thesis 
    by (smt ltrm_closed ltrm_deg_0 ltrm_smult_cring R.m_comm UP_m_comm assms(1) assms(2) assms(3) cfs_closed monom_mult_is_smult)
next
  case False
    obtain q0 where q0_def: "q0 = trunc q" 
      by simp
    obtain p0 where p0_def: "p0 = trunc p" 
      by simp
    have Pq: "degree q0 < degree q"
      using False P_def assms(2) q0_def trunc_degree by blast          
    have Pp: "degree p0 < degree p"
      using False P_def assms(1) p0_def trunc_degree by blast
    have "p \<otimes>\<^bsub>P\<^esub> q = (p0 \<oplus>\<^bsub>P\<^esub> ltrm(p)) \<otimes>\<^bsub>P \<^esub>(q0 \<oplus>\<^bsub>P\<^esub> ltrm(q))"
      using assms(1) assms(2) p0_def q0_def trunc_simps(1) by auto
    then have P0: "p \<otimes>\<^bsub>P\<^esub> q = ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p)) \<otimes>\<^bsub>P \<^esub>q0) \<oplus>\<^bsub>P\<^esub> ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q))"
      by (simp add: P.r_distr assms(1) assms(2) ltrm_closed p0_def q0_def trunc_closed)
    have P1: "degree ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p)) \<otimes>\<^bsub>P \<^esub>q0) < degree ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q))"
    proof-
      have LHS: "degree ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p)) \<otimes>\<^bsub>P \<^esub>q0) \<le> degree p + degree q0 "
      proof(cases "q0 = \<zero>\<^bsub>P\<^esub>")
        case True
        then show ?thesis 
          using assms(1) p0_def trunc_simps(1) by auto
      next
        case False
        then show ?thesis 
          using assms(1) assms(2) deg_mult_ring  p0_def 
            q0_def trunc_simps(1) trunc_closed by auto
      qed
      have RHS: "degree ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q)) = degree p + degree q"
        using assms(1) assms(2) deg_mult_ring ltrm_closed p0_def trunc_simps(1) 
        by (smt P_def UP_cring.lcf_monom(1) UP_cring.cring_deg_mult UP_cring_axioms add.commute assms(3) cfs_closed deg_ltrm)                    
        then show ?thesis 
          using RHS LHS  Pq 
          by linarith    
    qed
    then have P2: "ltrm (p \<otimes>\<^bsub>P\<^esub> q) = ltrm ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q))"
      using P0 P1  
      by (metis (no_types, lifting) ltrm_closed ltrm_of_sum_diff_degree P.add.m_comm 
          UP_mult_closed assms(1) assms(2) p0_def q0_def trunc_closed trunc_simps(1))      
    have P3: " ltrm ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q)) = ltrm p \<otimes>\<^bsub>P\<^esub> ltrm q"
    proof-
      have Q0: "((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q)) = (p0 \<otimes>\<^bsub>P \<^esub>ltrm(q)) \<oplus>\<^bsub>P\<^esub>  (ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q)"
        by (simp add: P.l_distr assms(1) assms(2) ltrm_closed p0_def trunc_closed)
      have Q1: "degree ((p0 \<otimes>\<^bsub>P \<^esub>ltrm(q)) ) < degree ((ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q))"
      proof(cases "p0 = \<zero>\<^bsub>P\<^esub>")
        case True
        then show ?thesis 
          using P1 assms(1) assms(2)  ltrm_closed by auto
      next
        case F: False
        then show ?thesis
          proof-
            have LHS: "degree ((p0 \<otimes>\<^bsub>P \<^esub>ltrm(q))) < degree p + degree q"
              using False F  Pp assms(1) assms(2) deg_nzero_nzero 
                 deg_ltrm ltrm_closed p0_def trunc_closed 
              by (smt add_le_cancel_right deg_mult_ring le_trans not_less)   
            have RHS: "degree ((ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q)) = degree p + degree q" 
              using cring_deg_mult[of "ltrm p" "ltrm q"] assms 
              by (simp add: ltrm_closed ltrm_cfs deg_ltrm)                      
            then show ?thesis using LHS RHS by auto 
        qed
      qed
      have Q2: "ltrm ((p0 \<oplus>\<^bsub>P\<^esub> ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q)) = ltrm ((ltrm(p))\<otimes>\<^bsub>P \<^esub>ltrm(q))" 
        using Q0 Q1 
        by (metis (no_types, lifting) ltrm_closed ltrm_of_sum_diff_degree P.add.m_comm 
            UP_mult_closed assms(1) assms(2) p0_def trunc_closed)        
      show ?thesis using ltrm_prod_ltrm Q0 Q1 Q2 
        by (simp add: assms(1) assms(2))
    qed
    then show ?thesis 
      by (simp add: P2)
qed

lemma(in UP_domain) ltrm_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "ltrm (p \<otimes>\<^bsub>P\<^esub> q) = (ltrm p) \<otimes>\<^bsub>P\<^esub> (ltrm q)"
  using cring_ltrm_mult assms 
  by (smt ltrm_closed ltrm_deg_0 cfs_closed deg_nzero_nzero deg_ltrm local.integral_iff monom_mult monom_zero)

lemma lcf_deg_0:
  assumes "degree p = 0"
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "(p \<otimes>\<^bsub>P\<^esub> q) = (lcf p)\<odot>\<^bsub>P\<^esub>q" 
  using P_def assms(1) assms(2) assms(3) 
  by (metis ltrm_deg_0 cfs_closed monom_mult_is_smult)
  
text\<open>leading term powers\<close>

lemma (in domain) nonzero_pow_nonzero:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  shows "a[^](n::nat) \<noteq> \<zero>"  
proof(induction n)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  fix n::nat
  assume IH: "a[^] n \<noteq> \<zero>" 
  show "a[^] (Suc n) \<noteq> \<zero>" 
  proof-
    have "a[^] (Suc n) = a[^] n \<otimes> a"
      by simp
    then show ?thesis using assms IH 
      using IH assms(1) assms(2) local.integral by auto
  qed
qed

lemma (in UP_cring) cring_monom_degree:
  assumes "a \<in> (carrier R)"
  assumes "p = monom P a m"
  assumes "a[^]n \<noteq> \<zero>"
  shows "degree (p[^]\<^bsub>P\<^esub> n) = n*m"
  by (simp add: assms(1) assms(2) assms(3) monom_pow)
  
lemma (in UP_domain) monom_degree:
  assumes "a \<noteq>\<zero>"
  assumes "a \<in> (carrier R)"
  assumes "p = monom P a m"
  shows "degree (p[^]\<^bsub>P\<^esub> n) = n*m"
  by (simp add: R.domain_axioms assms(1) assms(2) assms(3) domain.nonzero_pow_nonzero monom_pow)
  
lemma(in UP_cring)  cring_pow_ltrm:
  assumes "p \<in> carrier P" 
  assumes "lcf p [^]n \<noteq> \<zero>"
  shows "ltrm (p[^]\<^bsub>P\<^esub>(n::nat)) = (ltrm p)[^]\<^bsub>P\<^esub>n"
proof-
  have "lcf p [^]n \<noteq> \<zero> \<Longrightarrow> ltrm (p[^]\<^bsub>P\<^esub>(n::nat)) = (ltrm p)[^]\<^bsub>P\<^esub>n"
  proof(induction n)
    case 0
    then show ?case 
      using P.ring_simprules(6) P.nat_pow_0 cfs_one deg_one monom_one by presburger
  next
    case (Suc n) fix n::nat
    assume IH : "(lcf p [^] n \<noteq> \<zero> \<Longrightarrow> ltrm (p [^]\<^bsub>P\<^esub> n) = ltrm p [^]\<^bsub>P\<^esub> n)"
    assume A: "lcf p [^] Suc n \<noteq> \<zero>"
    have a: "ltrm (p [^]\<^bsub>P\<^esub> n) = ltrm p [^]\<^bsub>P\<^esub> n"
      apply(cases "lcf p [^] n = \<zero>")
      using A lcf_closed assms(1) apply auto[1]
      by(rule IH)
    have 0: "lcf (ltrm (p [^]\<^bsub>P\<^esub> n)) = lcf p [^] n"
      unfolding a 
      by (simp add: lcf_monom(1) assms(1) cfs_closed monom_pow)
    then have 1: "lcf (ltrm (p [^]\<^bsub>P\<^esub> n)) \<otimes> lcf p \<noteq> \<zero>"
      using assms A R.nat_pow_Suc IH  by metis   
    then show "ltrm (p [^]\<^bsub>P\<^esub> Suc n) = ltrm p [^]\<^bsub>P\<^esub> Suc n"
      using IH 0 assms(1) cring_ltrm_mult cfs_closed 
      by (smt A lcf_monom(1) ltrm_closed P.nat_pow_Suc2 P.nat_pow_closed R.nat_pow_Suc2 a)    
  qed
  then show ?thesis 
    using assms(2) by blast
qed

lemma(in UP_cring)  cring_pow_deg:
  assumes "p \<in> carrier P" 
  assumes "lcf p [^]n \<noteq> \<zero>"
  shows "degree (p[^]\<^bsub>P\<^esub>(n::nat)) = n*degree p"
proof-
  have "degree ( (ltrm p)[^]\<^bsub>P\<^esub>n) = n*degree p"
    using assms(1) assms(2) cring_monom_degree lcf_closed lcf_ltrm by auto
  then show ?thesis 
    using assms cring_pow_ltrm 
    by (metis P.nat_pow_closed P_def UP_ring.deg_ltrm UP_ring_axioms)
qed

lemma(in UP_cring)  cring_pow_deg_bound:
  assumes "p \<in> carrier P" 
  shows "degree (p[^]\<^bsub>P\<^esub>(n::nat)) \<le> n*degree p"
  apply(induction n)
   apply (metis Group.nat_pow_0 deg_one le_zero_eq mult_is_0)  
  using deg_mult_ring[of _ p]
  by (smt P.nat_pow_Suc2 P.nat_pow_closed ab_semigroup_add_class.add_ac(1) assms deg_mult_ring le_iff_add mult_Suc)  

lemma(in UP_cring) deg_smult:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier (UP R)"
  assumes "a \<otimes> lcf f \<noteq> \<zero>"
  shows "deg R (a \<odot>\<^bsub>UP R\<^esub> f) = deg R  f"
  using assms  P_def cfs_smult deg_eqI deg_smult_decr smult_closed 
  by (metis deg_gtE le_neq_implies_less)
 
lemma(in UP_cring) deg_smult':
  assumes "a \<in> Units R"
  assumes "f \<in> carrier (UP R)"
  shows "deg R (a \<odot>\<^bsub>UP R\<^esub> f) = deg R  f"
  apply(cases "deg R f = 0")
  apply (metis P_def R.Units_closed assms(1) assms(2) deg_smult_decr le_zero_eq)
  apply(rule deg_smult) 
  using assms apply blast
  using assms apply blast
proof
  assume A: "deg R f \<noteq> 0" "a \<otimes> f (deg R f) = \<zero>"
  have 0: "f (deg R f) = \<zero>"
    using A assms R.Units_not_right_zero_divisor[of a "f (deg R f)"] UP_car_memE(1) by blast
  then show False  using assms A 
    by (metis P_def deg_zero deg_ltrm monom_zero)
qed

lemma(in UP_domain)  pow_sum0:
"\<And> p q. p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n"
proof(induction n)
  case 0
  then show ?case 
    by (metis Group.nat_pow_0 deg_one mult_is_0)
next
    case (Suc n)
    fix n
    assume IH: "\<And> p q. p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow> 
              degree q < degree p \<Longrightarrow> degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n"
    then show "\<And> p q. p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow> 
             degree q < degree p \<Longrightarrow> degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n)) = (degree p)*(Suc n)"
    proof-
      fix p q
      assume A0: "p \<in> carrier P" and 
           A1: "q \<in> carrier P" and 
           A2:  "degree q < degree p"
      show "degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n)) = (degree p)*(Suc n)"
      proof(cases "q = \<zero>\<^bsub>P\<^esub>")
        case True
        then show ?thesis 
        by (metis A0 A1 A2 IH P.nat_pow_Suc2 P.nat_pow_closed P.r_zero deg_mult 
            domain.nonzero_pow_nonzero local.domain_axioms mult_Suc_right nat_neq_iff)
      next
        case False
        then show ?thesis 
        proof-
          have P0: "degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n" 
          using A0 A1 A2 IH by auto 
          have P1: "(p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n) = ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q )"
            by simp
          then have P2: "(p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>(Suc n) = (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> p) \<oplus>\<^bsub>P\<^esub> (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> q)"
            by (simp add: A0 A1 UP_r_distr)
          have P3: "degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> p) = (degree p)*n + (degree p)" 
            using P0 A0 A1 A2 deg_nzero_nzero  degree_of_sum_diff_degree local.nonzero_pow_nonzero by auto
          have P4: "degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> q) = (degree p)*n + (degree q)" 
            using P0 A0 A1 A2 deg_nzero_nzero  degree_of_sum_diff_degree local.nonzero_pow_nonzero False deg_mult 
            by simp
          have P5: "degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> p) > degree (((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub> q)"
            using P3 P4 A2 by auto 
          then show ?thesis using P5 P3 P2 
            by (simp add: A0 A1 degree_of_sum_diff_degree)
        qed
      qed
    qed
qed

lemma(in UP_domain)  pow_sum:
  assumes "p \<in> carrier P" 
  assumes "q \<in> carrier P"
  assumes "degree q < degree p"
  shows "degree ((p \<oplus>\<^bsub>P\<^esub> q )[^]\<^bsub>P\<^esub>n) = (degree p)*n"
  using assms(1) assms(2) assms(3) pow_sum0 by blast

lemma(in UP_domain)  deg_pow0:
 "\<And> p. p \<in> carrier P \<Longrightarrow> n \<ge> degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"
proof(induction n)
  case 0
  show "p \<in> carrier P \<Longrightarrow> 0 \<ge> degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"
  proof-
    assume B0:"p \<in> carrier P"
    assume B1: "0 \<ge> degree p"
    then obtain a where a_def: "a \<in> carrier R \<and> p = monom P a 0"
      using B0 deg_zero_impl_monom  by fastforce
    show "degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"  using UP_cring.monom_pow 
      by (metis P_def R.nat_pow_closed UP_cring_axioms a_def deg_const  
        mult_0_right mult_zero_left)
  qed
next
  case (Suc n)
  fix n
  assume IH: "\<And>p. (p \<in> carrier P \<Longrightarrow> n \<ge>degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m * (degree p))"
  show "p \<in> carrier P \<Longrightarrow> Suc n \<ge> degree p \<Longrightarrow> degree (p [^]\<^bsub>P\<^esub> m) = m * (degree p)"
  proof-
    assume A0: "p \<in> carrier P"
    assume A1: "Suc n \<ge> degree p"
    show "degree (p [^]\<^bsub>P\<^esub> m) = m * (degree p)"
    proof(cases "Suc n > degree p")
      case True
      then show ?thesis using IH A0 by simp
    next
      case False
      then show ?thesis 
      proof-
        obtain q where q_def: "q = trunc p"
          by simp
        obtain k where k_def: "k = degree q"
          by simp
        have q_is_poly: "q \<in> carrier P" 
          by (simp add: A0 q_def trunc_closed)
        have k_bound0: "k <degree p" 
          using k_def q_def trunc_degree[of p] A0 False by auto
        have k_bound1: "k \<le> n" 
          using k_bound0 A0 A1 by auto  
        have P_q:"degree (q [^]\<^bsub>P\<^esub> m) = m * k" 
          using IH[of "q"] k_bound1 k_def q_is_poly by auto  
        have P_ltrm: "degree ((ltrm p) [^]\<^bsub>P\<^esub> m) = m*(degree p)"
        proof-
          have "degree p = degree (ltrm p)" 
            by (simp add: A0 deg_ltrm)            
          then show ?thesis using monom_degree 
            by (metis A0 P.r_zero P_def cfs_closed coeff_simp equal_deg_sum k_bound0 k_def lcoeff_nonzero2 nat_neq_iff q_is_poly)            
        qed
        have "p = q \<oplus>\<^bsub>P\<^esub> (ltrm p)" 
          by (simp add: A0 q_def trunc_simps(1))
        then show ?thesis 
          using P_q pow_sum[of "(ltrm p)" q m] A0 UP_a_comm 
            deg_ltrm k_bound0 k_def ltrm_closed q_is_poly by auto
      qed
    qed
  qed
qed

lemma(in UP_domain)  deg_pow:
  assumes "p \<in> carrier P"
  shows "degree (p [^]\<^bsub>P\<^esub> m) = m*(degree p)"
  using deg_pow0 assms by blast

lemma(in UP_domain)  ltrm_pow0:
"\<And>f. f \<in> carrier P \<Longrightarrow> ltrm (f [^]\<^bsub>P\<^esub> (n::nat)) = (ltrm f) [^]\<^bsub>P\<^esub> n"
proof(induction n)
  case 0
  then show ?case 
    using ltrm_deg_0 P.nat_pow_0 P.ring_simprules(6) deg_one by presburger  
next
  case (Suc n)
  fix n::nat
  assume IH: "\<And>f. f \<in> carrier P \<Longrightarrow> ltrm (f [^]\<^bsub>P\<^esub> n) = (ltrm f) [^]\<^bsub>P\<^esub> n"
  then show "\<And>f. f \<in> carrier P \<Longrightarrow> ltrm (f [^]\<^bsub>P\<^esub> (Suc n)) = (ltrm f) [^]\<^bsub>P\<^esub> (Suc n)"
  proof-
    fix f
    assume A: "f \<in> carrier P"
    show " ltrm (f [^]\<^bsub>P\<^esub> (Suc n)) = (ltrm f) [^]\<^bsub>P\<^esub> (Suc n)"
    proof-
      have 0: "ltrm (f [^]\<^bsub>P\<^esub> n) = (ltrm f) [^]\<^bsub>P\<^esub> n" 
        using A IH  by blast
      have 1: "ltrm (f [^]\<^bsub>P\<^esub> (Suc n)) = ltrm ((f [^]\<^bsub>P\<^esub> n)\<otimes>\<^bsub>P\<^esub> f)" 
        by auto then 
      show ?thesis using ltrm_mult 0 1 
        by (simp add: A)
    qed
  qed
qed

lemma(in UP_domain)  ltrm_pow:
  assumes "f \<in> carrier P"
  shows " ltrm (f [^]\<^bsub>P\<^esub> (n::nat)) = (ltrm f) [^]\<^bsub>P\<^esub> n"
  using assms ltrm_pow0 by blast

text\<open>lemma on the leading coefficient\<close>

lemma lcf_eq:
  assumes "f \<in> carrier P"
  shows "lcf f = lcf (ltrm f)"
  using ltrm_deg_0 
  by (simp add: ltrm_cfs assms deg_ltrm)
  
lemma lcf_eq_deg_eq_imp_ltrm_eq:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree p > 0"
  assumes "degree p = degree q"
  assumes "lcf p = lcf q"
  shows "ltrm p = ltrm q"
  using assms(4) assms(5) 
  by (simp add: leading_term_def)
  
lemma ltrm_eq_imp_lcf_eq:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "ltrm p = ltrm q"
  shows "lcf p = lcf q"
  using assms 
  by (metis lcf_eq)

lemma ltrm_eq_imp_deg_drop:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "ltrm p = ltrm q"
  assumes "degree p >0"
  shows "degree (p \<ominus>\<^bsub>P\<^esub> q) < degree p"
proof-
  have P0: "degree p = degree q"
    by (metis assms(1) assms(2) assms(3) deg_ltrm)
  then have P1: "degree (p \<ominus>\<^bsub>P\<^esub> q) \<le> degree p"
    by (metis P.add.inv_solve_right P.minus_closed P.minus_eq assms(1)
        assms(2) degree_of_sum_diff_degree neqE order.strict_implies_order order_refl)
  have "degree (p \<ominus>\<^bsub>P\<^esub> q) \<noteq> degree p"
  proof
    assume A: "degree (p \<ominus>\<^bsub>P\<^esub> q) = degree p"
    have Q0: "p \<ominus>\<^bsub>P\<^esub> q = ((trunc p) \<oplus>\<^bsub>P\<^esub> (ltrm p)) \<ominus>\<^bsub>P\<^esub> ((trunc q) \<oplus>\<^bsub>P\<^esub> (ltrm p))"
      using assms(1) assms(2) assms(3) trunc_simps(1) by force
    have Q1: "p \<ominus>\<^bsub>P\<^esub> q = (trunc p)  \<ominus>\<^bsub>P\<^esub> (trunc q)" 
    proof-
      have "p \<ominus>\<^bsub>P\<^esub> q = ((trunc p) \<oplus>\<^bsub>P\<^esub> (ltrm p)) \<ominus>\<^bsub>P\<^esub> (trunc q) \<ominus> \<^bsub>P\<^esub> (ltrm p)"
        using Q0 
        by (simp add: P.minus_add P.minus_eq UP_a_assoc assms(1) assms(2) ltrm_closed trunc_closed)
      then show ?thesis 
        by (metis (no_types, lifting) ltrm_closed P.add.inv_mult_group P.minus_eq 
            P.r_neg2 UP_a_assoc assms(1) assms(2) assms(3) carrier_is_submodule submoduleE(6) trunc_closed trunc_simps(1))        
    qed
    have Q2: "degree (trunc p) < degree p" 
      by (simp add: assms(1) assms(4) trunc_degree)
    have Q3: "degree (trunc q) < degree q" 
      using P0 assms(2) assms(4) trunc_degree by auto
    then show False  using A Q1 Q2 Q3 by (simp add: P.add.inv_solve_right
          P.minus_eq P0 assms(1) assms(2) degree_of_sum_diff_degree trunc_closed)
  qed
  then show ?thesis 
    using P1 by auto
qed

lemma(in UP_cring) cring_lcf_scalar_mult:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "a \<otimes> (lcf p) \<noteq>\<zero>"
  shows "lcf (a \<odot>\<^bsub>P\<^esub> p) = a \<otimes> (lcf p)"
proof-
  have 0: "lcf (a \<odot>\<^bsub>P\<^esub> p) = lcf (ltrm (a \<odot>\<^bsub>P\<^esub> p))"
    using assms  lcf_eq smult_closed by blast
  have 1: "degree (a \<odot>\<^bsub>P\<^esub> p) = degree p"
    by (smt lcf_monom(1) P_def R.one_closed R.r_null UP_ring.coeff_smult UP_ring_axioms  
        assms(1) assms(2) assms(3) coeff_simp cring_deg_mult deg_const monom_closed monom_mult_is_smult smult_one)
  then have "lcf (a \<odot>\<^bsub>P\<^esub> p) = lcf (a \<odot>\<^bsub>P\<^esub> (ltrm p))"
    using lcf_eq[of "a \<odot>\<^bsub>P\<^esub> p"] smult_closed  assms 0 
    by (metis cfs_closed cfs_smult monom_mult_smult)     
  then show ?thesis 
    unfolding leading_term_def 
    by (metis P_def R.m_closed UP_cring.lcf_monom UP_cring_axioms assms(1) assms(2) cfs_closed monom_mult_smult)   
qed

lemma(in UP_domain) lcf_scalar_mult:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "lcf (a \<odot>\<^bsub>P\<^esub> p) = a \<otimes> (lcf p)"
proof-
  have "lcf (a \<odot>\<^bsub>P\<^esub> p) = lcf (ltrm (a \<odot>\<^bsub>P\<^esub> p))"
    using lcf_eq UP_smult_closed assms(1) assms(2) by blast 
  then have "lcf (a \<odot>\<^bsub>P\<^esub> p) = lcf (a \<odot>\<^bsub>P\<^esub> (ltrm p))"
    using ltrm_smult assms(1) assms(2) by metis   
  then show ?thesis 
    by (metis (full_types) UP_smult_zero assms(1) assms(2) cfs_smult cfs_zero deg_smult)    
qed

lemma(in UP_cring)  cring_lcf_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "(lcf p) \<otimes> (lcf q) \<noteq>\<zero>"
  shows "lcf (p \<otimes>\<^bsub>P\<^esub> q) = (lcf p) \<otimes> (lcf q)"
  using assms cring_ltrm_mult 
  by (smt lcf_monom(1) P.m_closed R.m_closed cfs_closed monom_mult)

lemma(in UP_domain)  lcf_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "lcf (p \<otimes>\<^bsub>P\<^esub> q) = (lcf p) \<otimes> (lcf q)"
  by (smt ltrm_deg_0 R.integral_iff assms(1) assms(2) cfs_closed cring_lcf_mult deg_zero deg_ltrm local.integral_iff monom_zero)

lemma(in UP_cring)  cring_lcf_pow:
  assumes "p \<in> carrier P"
  assumes "(lcf p)[^]n \<noteq>\<zero>"
  shows "lcf (p[^]\<^bsub>P\<^esub>(n::nat)) = (lcf p)[^]n"
  by (smt P.nat_pow_closed R.nat_pow_closed assms(1) assms(2) cring_pow_ltrm lcf_closed lcf_ltrm lcf_monom monom_pow)

lemma(in UP_domain)  lcf_pow:
  assumes "p \<in> carrier P"
  shows "lcf (p[^]\<^bsub>P\<^esub>(n::nat)) = (lcf p)[^]n"
proof-
  show ?thesis 
  proof(induction n)
    case 0
    then show ?case 
      by (metis Group.nat_pow_0 P_def R.one_closed UP_cring.lcf_monom UP_cring_axioms monom_one)    
  next
    case (Suc n)
    fix n
    assume IH: "lcf (p[^]\<^bsub>P\<^esub>(n::nat)) = (lcf p)[^]n"
    show "lcf (p[^]\<^bsub>P\<^esub>(Suc n)) = (lcf p)[^](Suc n)"
    proof-
      have "lcf (p[^]\<^bsub>P\<^esub>(Suc n)) = lcf ((p[^]\<^bsub>P\<^esub>n) \<otimes>\<^bsub>P\<^esub>p)"
        by simp
      then have "lcf (p[^]\<^bsub>P\<^esub>(Suc n)) = (lcf p)[^]n \<otimes> (lcf p)"
        by (simp add: IH assms lcf_mult)
      then show ?thesis by auto 
    qed
  qed
qed
end

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Constant Terms and Constant Coefficients\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

text\<open>Constant term  and coefficient function\<close>

definition zcf where
"zcf f = (f 0)"

abbreviation(in UP_cring)(input) ctrm where
"ctrm f \<equiv> monom P (f 0) 0"

context UP_cring
begin

lemma ctrm_is_poly:
  assumes "p \<in> carrier P"
  shows "ctrm p \<in> carrier P"
  by (simp add: assms cfs_closed)

lemma ctrm_degree:
  assumes "p \<in> carrier P"
  shows "degree (ctrm p) = 0"
  by (simp add: assms cfs_closed) 
  
lemma ctrm_zcf:
assumes "f \<in> carrier P"
assumes "zcf f = \<zero>"
shows "ctrm f = \<zero>\<^bsub>P\<^esub>"
  by (metis P_def UP_ring.monom_zero UP_ring_axioms zcf_def assms(2))

lemma zcf_degree_zero:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "lcf f = zcf f"
  by (simp add: zcf_def assms(2))
  
lemma zcf_zero_degree_zero:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  assumes "zcf f = \<zero>"
  shows "f = \<zero>\<^bsub>P\<^esub>"
  using zcf_degree_zero[of f] assms ltrm_deg_0[of f] 
  by simp

lemma zcf_ctrm:
  assumes "p \<in> carrier P"
  shows "zcf (ctrm p) = zcf p"
  unfolding zcf_def 
  using P_def UP_ring.cfs_monom UP_ring_axioms assms cfs_closed by fastforce
 
lemma ctrm_trunc:
  assumes "p \<in> carrier P"
  assumes "degree p >0"
  shows "zcf(trunc p) = zcf p"
  by (simp add: zcf_def assms(1) assms(2) trunc_cfs)

text\<open>Constant coefficient function is a ring homomorphism\<close>


lemma zcf_add:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "zcf(p \<oplus>\<^bsub>P\<^esub> q) = (zcf p) \<oplus> (zcf q)"
  by (simp add: zcf_def assms(1) assms(2))

lemma coeff_ltrm[simp]:
  assumes "p \<in> carrier P"
  assumes "degree p > 0"
  shows "zcf(ltrm p) = \<zero>"
  by (metis ltrm_cfs_above_deg ltrm_cfs zcf_def assms(1) assms(2))

lemma zcf_zero[simp]:
"zcf \<zero>\<^bsub>P\<^esub> = \<zero>"
  using zcf_degree_zero by auto

lemma zcf_one[simp]:
"zcf \<one>\<^bsub>P\<^esub> = \<one>"
  by (simp add: zcf_def)

lemma ctrm_smult:
  assumes "f \<in> carrier P"
  assumes "a \<in>  carrier R"
  shows "ctrm (a \<odot>\<^bsub>P\<^esub> f) = a \<odot>\<^bsub>P\<^esub>(ctrm f)"
  using P_def UP_ring.monom_mult_smult UP_ring_axioms assms(1) assms(2) cfs_smult coeff_simp 
  by (simp add: UP_ring.monom_mult_smult cfs_closed)

lemma ctrm_monom[simp]:
  assumes "a \<in> carrier R"
  shows "ctrm (monom P a (Suc k)) = \<zero>\<^bsub>P\<^esub>"
  by (simp add: assms cfs_monom)
end
  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>Polynomial Induction Rules\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

context UP_ring
begin

text\<open>Rule for strong induction on polynomial degree\<close>

lemma poly_induct:
  assumes "p \<in> carrier P"
  assumes Deg_0: "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> Q p"
  assumes IH: "\<And>p. (\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q) \<Longrightarrow> p \<in> carrier P \<Longrightarrow> degree p > 0 \<Longrightarrow> Q p"
  shows "Q p"
proof-
  have "\<And>n. \<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> Q p"
  proof-
    fix n
    show "\<And>p. p \<in> carrier P \<Longrightarrow>  degree p \<le> n \<Longrightarrow> Q p"
    proof(induction n)
      case 0
      then show ?case 
        using Deg_0  by simp
    next
      case (Suc n)
      fix n 
      assume I:  "\<And>p. p \<in> carrier P \<Longrightarrow>  degree p \<le> n \<Longrightarrow> Q p"
      show  "\<And>p. p \<in> carrier P \<Longrightarrow>  degree p \<le> (Suc n) \<Longrightarrow> Q p"
      proof-
        fix p
        assume A0: " p \<in> carrier P "
        assume A1: "degree p \<le>Suc n"
        show "Q p"
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis 
            using I  A0 by auto
        next
          case False
          then have D: "degree p = Suc n" 
            by (simp add: A1 nat_less_le)
          then  have "(\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q)" 
              using I   by simp
            then show "Q p" 
                  using IH D A0 A1 Deg_0 by blast
        qed
      qed
    qed
  qed
  then show ?thesis using assms by blast 
qed

text\<open>Variant on induction on degree\<close>

lemma poly_induct2:
  assumes "p \<in> carrier P"
  assumes Deg_0: "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> Q p"
  assumes IH: "\<And>p. degree p > 0  \<Longrightarrow> p \<in> carrier P \<Longrightarrow> Q (trunc p)  \<Longrightarrow> Q p"
  shows "Q p"
proof(rule poly_induct)
  show "p \<in> carrier P" 
    by (simp add: assms(1))
  show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> Q p" 
      by (simp add: Deg_0)
    show "\<And>p. (\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q) \<Longrightarrow> p \<in> carrier P \<Longrightarrow> 0 < degree p \<Longrightarrow> Q p"
    proof-
      fix p
      assume A0: "(\<And>q. q \<in> carrier P \<Longrightarrow> degree q < degree p \<Longrightarrow> Q q)"
      assume A1: " p \<in> carrier P"
      assume A2: "0 < degree p" 
      show "Q p"
      proof-
        have "degree (trunc p) < degree p"
          by (simp add: A1 A2 trunc_degree)
        have "Q (trunc p)"
          by (simp add: A0 A1 \<open>degree (trunc p) < degree p\<close> trunc_closed)
        then show ?thesis 
          by (simp add: A1 A2 IH)
      qed
    qed
qed

text\<open>Additive properties which are true for all monomials are true for all polynomials \<close>

lemma poly_induct3:
  assumes "p \<in> carrier P"
  assumes add: "\<And>p q. q \<in> carrier P \<Longrightarrow> p \<in> carrier P \<Longrightarrow> Q p \<Longrightarrow> Q q  \<Longrightarrow> Q (p \<oplus>\<^bsub>P\<^esub> q)"
  assumes monom: "\<And>a n. a \<in> carrier R \<Longrightarrow> Q (monom P a n)"
  shows "Q p"
  apply(rule poly_induct2)
  apply (simp add: assms(1))
  apply (metis lcf_closed P_def coeff_simp deg_zero_impl_monom monom)
  by (metis lcf_closed ltrm_closed add monom trunc_closed trunc_simps(1))

lemma poly_induct4:
  assumes "p \<in> carrier P"
  assumes add: "\<And>p q. q \<in> carrier P \<Longrightarrow> p \<in> carrier P \<Longrightarrow> Q p \<Longrightarrow> Q q  \<Longrightarrow> Q (p \<oplus>\<^bsub>P\<^esub> q)"
  assumes monom_zero: "\<And>a. a \<in> carrier R \<Longrightarrow> Q (monom P a 0)"
  assumes monom_Suc: "\<And>a n. a \<in> carrier R \<Longrightarrow> Q (monom P a (Suc n))"
  shows "Q p"
  apply(rule poly_induct3)
  using assms(1) apply auto[1]
  using add apply blast
  using monom_zero monom_Suc 
  by (metis P_def UP_ring.monom_zero UP_ring_axioms deg_monom deg_monom_le le_0_eq le_SucE zero_induct)

lemma monic_monom_smult:
  assumes "a \<in> carrier R"
  shows "a \<odot>\<^bsub>P\<^esub> monom P \<one> n = monom P a n"
  using assms 
  by (metis R.one_closed R.r_one monom_mult_smult)

lemma poly_induct5:
  assumes "p \<in> carrier P"
  assumes add: "\<And>p q. q \<in> carrier P \<Longrightarrow> p \<in> carrier P \<Longrightarrow> Q p \<Longrightarrow> Q q  \<Longrightarrow> Q (p \<oplus>\<^bsub>P\<^esub> q)"
  assumes monic_monom: "\<And>n. Q (monom P \<one> n)"
  assumes smult: "\<And>p a . a \<in> carrier R \<Longrightarrow> p \<in> carrier P \<Longrightarrow> Q p \<Longrightarrow> Q (a \<odot>\<^bsub>P\<^esub> p)"
  shows "Q p"
  apply(rule poly_induct3)
  apply (simp add: assms(1))
  using add apply blast
proof-
  fix a n assume A: "a \<in> carrier R" show "Q (monom P a n)"
    using monic_monom[of n] smult[of a "monom P \<one> n"] monom_mult_smult[of a \<one> n]
  by (simp add: A)
qed

lemma poly_induct6:
  assumes "p \<in> carrier P"
  assumes monom: "\<And>a n. a \<in> carrier R \<Longrightarrow> Q (monom P a 0)"
  assumes plus_monom: "\<And>a n p. a \<in> carrier R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> p \<in> carrier P \<Longrightarrow> degree p < n \<Longrightarrow> Q p \<Longrightarrow>
                                Q(p \<oplus>\<^bsub>P\<^esub> monom P a n)"
  shows "Q p"
  apply(rule poly_induct2)
  using assms(1) apply auto[1]
  apply (metis lcf_closed P_def coeff_simp deg_zero_impl_monom monom)
  using plus_monom 
  by (metis lcf_closed P_def coeff_simp lcoeff_nonzero_deg nat_less_le trunc_closed trunc_degree trunc_simps(1))
  

end

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Mapping a Polynomial to its Associated Ring Function\<close>
(**************************************************************************************************)
(**************************************************************************************************)


text\<open>Turning a polynomial into a function on R:\<close>
definition to_function  where
"to_function S f  = (\<lambda>s \<in> carrier S. eval S S (\<lambda>x. x) s f)"

context UP_cring
begin

definition to_fun where
"to_fun f \<equiv> to_function R f"

text\<open>Explicit formula for evaluating a polynomial function:\<close>

lemma to_fun_eval:
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "to_fun f x  = eval R R (\<lambda>x. x) x f"
  using assms unfolding to_function_def to_fun_def 
  by auto 

lemma to_fun_formula:
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "to_fun f x = (\<Oplus>i \<in> {..degree f}. (f i) \<otimes> x [^] i)"
proof-
  have "f \<in> carrier (UP R)"
    using assms P_def by auto 
  then  have "eval R R (\<lambda>x. x) x f =  (\<Oplus>\<^bsub>R\<^esub>i\<in>{..deg R f}. (\<lambda>x. x) (coeff (UP R) f i) \<otimes>\<^bsub>R\<^esub> x [^]\<^bsub>R\<^esub> i)"
    apply(simp add:UnivPoly.eval_def) done
  then have "to_fun f x = (\<Oplus>\<^bsub>R\<^esub>i\<in>{..deg R f}. (\<lambda>x. x) (coeff (UP R) f i) \<otimes>\<^bsub>R\<^esub> x [^]\<^bsub>R\<^esub> i)"
    using to_function_def assms unfolding to_fun_def  
    by (simp add: to_function_def)
  then show ?thesis  
    by(simp add: assms coeff_simp) 
qed

lemma eval_ring_hom:
  assumes "a \<in> carrier R"
  shows "eval R R (\<lambda>x. x) a \<in> ring_hom P R"
proof-
  have "(\<lambda>x. x) \<in> ring_hom R R"
    apply(rule ring_hom_memI)
    apply auto done
  then have "UP_pre_univ_prop R R (\<lambda>x. x)"
    using R_cring UP_pre_univ_propI by blast
  then show ?thesis 
    by (simp add: P_def UP_pre_univ_prop.eval_ring_hom assms)
qed

lemma to_fun_closed:
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "to_fun f x  \<in> carrier R"
  using assms to_fun_eval[of f x] eval_ring_hom[of x]
  ring_hom_closed 
  by fastforce
  
lemma to_fun_plus:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "to_fun (f \<oplus>\<^bsub>P\<^esub> g) x = (to_fun f x) \<oplus> (to_fun g x)"
  using assms to_fun_eval[of ] eval_ring_hom[of x]
  by (simp add: ring_hom_add)
  
lemma to_fun_mult:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "to_fun (f \<otimes>\<^bsub>P\<^esub> g) x = (to_fun f x) \<otimes> (to_fun g x)"
  using assms to_fun_eval[of ] eval_ring_hom[of x]
  by (simp add: ring_hom_mult)

lemma to_fun_ring_hom:
  assumes "a \<in> carrier R"
  shows "(\<lambda>p. to_fun p a) \<in> ring_hom P R"
  apply(rule ring_hom_memI)
  apply (simp add: assms to_fun_closed)
    apply (simp add: assms to_fun_mult)
      apply (simp add: assms to_fun_plus)
        using to_fun_eval[of "\<one>\<^bsub>P\<^esub>" a] eval_ring_hom[of a] 
              ring_hom_closed 
        by (simp add: assms ring_hom_one)

lemma ring_hom_uminus:
  assumes "ring S"
  assumes "f \<in> (ring_hom S R)"
  assumes "a \<in> carrier S"
  shows "f (\<ominus>\<^bsub>S\<^esub> a) = \<ominus> (f a)"
proof-
  have "f (a \<ominus>\<^bsub>S\<^esub> a) = (f a) \<oplus> f (\<ominus>\<^bsub>S\<^esub> a)"
    unfolding a_minus_def 
    by (simp add: assms(1) assms(2) assms(3) ring.ring_simprules(3) ring_hom_add)
  then have "(f a) \<oplus> f (\<ominus>\<^bsub>S\<^esub> a) = \<zero> "
    by (metis R.ring_axioms a_minus_def assms(1) assms(2) assms(3) 
        ring.ring_simprules(16) ring_hom_zero)
  then show ?thesis 
    by (metis (no_types, lifting) R.add.m_comm R.minus_equality assms(1)
        assms(2) assms(3) ring.ring_simprules(3) ring_hom_closed)
qed

lemma to_fun_minus:
  assumes "f \<in> carrier P"
  assumes "x \<in> carrier R"
  shows "to_fun (\<ominus>\<^bsub>P\<^esub>f) x = \<ominus> (to_fun f x)"
  unfolding to_function_def to_fun_def 
  using  eval_ring_hom[of x] assms  
  by (simp add: UP_ring ring_hom_uminus)

lemma id_is_hom:
"ring_hom_cring R R (\<lambda>x. x)"
proof(rule ring_hom_cringI)
  show "cring R" 
    by (simp add: R_cring )
  show "cring R" 
    by (simp add: R_cring ) 
  show "(\<lambda>x. x) \<in> ring_hom R R"
    unfolding ring_hom_def
    apply(auto)
    done
qed

lemma UP_pre_univ_prop_fact:
"UP_pre_univ_prop R R (\<lambda>x. x)"
  unfolding UP_pre_univ_prop_def
  by (simp add: UP_cring_def R_cring  id_is_hom)

end

  (**************************************************************************************************)
  (**************************************************************************************************)
  subsection\<open>to-fun is a Ring Homomorphism from Polynomials to Functions\<close>
  (**************************************************************************************************)
  (**************************************************************************************************)

context UP_cring
begin

lemma to_fun_is_Fun:
  assumes "x \<in> carrier P"
  shows "to_fun x \<in> carrier (Fun R)"
  apply(rule ring_functions.function_ring_car_memI)
  unfolding ring_functions_def apply(simp add: R.ring_axioms)
  using to_fun_closed assms apply auto[1]
  unfolding to_function_def to_fun_def  by auto 

lemma to_fun_Fun_mult:
  assumes "x \<in> carrier P"
  assumes "y \<in> carrier P"
  shows "to_fun (x \<otimes>\<^bsub>P\<^esub> y) = to_fun x \<otimes>\<^bsub>function_ring (carrier R) R\<^esub> to_fun y"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "carrier R"])
  apply (simp add: R.ring_axioms ring_functions_def)
    apply (simp add: assms(1) assms(2) to_fun_is_Fun)
      apply (simp add: R.ring_axioms assms(1) assms(2) ring_functions.fun_mult_closed ring_functions.intro to_fun_is_Fun)
        by (simp add: R.ring_axioms assms(1) assms(2) ring_functions.function_mult_eval_car ring_functions.intro to_fun_is_Fun to_fun_mult)

lemma to_fun_Fun_add:
  assumes "x \<in> carrier P"
  assumes "y \<in> carrier P"
  shows "to_fun (x \<oplus>\<^bsub>P\<^esub> y) = to_fun x \<oplus>\<^bsub>function_ring (carrier R) R\<^esub> to_fun y"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "carrier R"])
  apply (simp add: R.ring_axioms ring_functions_def)
    apply (simp add: assms(1) assms(2) to_fun_is_Fun)
      apply (simp add: R.ring_axioms assms(1) assms(2) ring_functions.fun_add_closed ring_functions.intro to_fun_is_Fun)
        by (simp add: R.ring_axioms assms(1) assms(2) ring_functions.fun_add_eval_car ring_functions.intro to_fun_is_Fun to_fun_plus)

lemma to_fun_Fun_one:
"to_fun \<one>\<^bsub>P\<^esub> = \<one>\<^bsub>Fun R\<^esub>"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "carrier R"])
  apply (simp add: R.ring_axioms ring_functions_def)
    apply (simp add: to_fun_is_Fun)
      apply (simp add: R.ring_axioms ring_functions.function_one_closed ring_functions_def)
        using P_def R.ring_axioms UP_cring.eval_ring_hom UP_cring.to_fun_eval UP_cring_axioms UP_one_closed ring_functions.function_one_eval ring_functions.intro ring_hom_one 
          by fastforce

lemma to_fun_Fun_zero:
"to_fun \<zero>\<^bsub>P\<^esub> = \<zero>\<^bsub>Fun R\<^esub>"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "carrier R"])
  apply (simp add: R.ring_axioms ring_functions_def)
    apply (simp add: to_fun_is_Fun)
      apply (simp add: R.ring_axioms ring_functions.function_zero_closed ring_functions_def)
        using P_def R.ring_axioms UP_cring.eval_ring_hom UP_cring.to_fun_eval UP_cring_axioms UP_zero_closed ring_functions.function_zero_eval ring_functions.intro ring_hom_zero 
        by (metis UP_ring eval_ring_hom)

lemma to_fun_function_ring_hom:
"to_fun \<in> ring_hom P (Fun R)"
  apply(rule ring_hom_memI)
    using to_fun_is_Fun apply auto[1]
      apply (simp add: to_fun_Fun_mult)
        apply (simp add: to_fun_Fun_add)
          by (simp add: to_fun_Fun_one)

lemma(in UP_cring) to_fun_one:
  assumes "a \<in> carrier R"
  shows "to_fun \<one>\<^bsub>P\<^esub> a = \<one>"
  using assms to_fun_Fun_one 
  by (metis P_def UP_cring.to_fun_eval UP_cring_axioms UP_one_closed eval_ring_hom ring_hom_one) 

lemma(in UP_cring) to_fun_zero:
  assumes "a \<in> carrier R"
  shows "to_fun \<zero>\<^bsub>P\<^esub> a = \<zero>"
  by (simp add: assms R.ring_axioms ring_functions.function_zero_eval ring_functions.intro to_fun_Fun_zero) 

lemma(in UP_cring) to_fun_nat_pow:
  assumes "h \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "to_fun (h[^]\<^bsub>UP R\<^esub>(n::nat)) a = (to_fun h a)[^]n"
  apply(induction n)
  using assms to_fun_one 
  apply (metis P.nat_pow_0 P_def R.nat_pow_0)
  using assms to_fun_mult  P.nat_pow_closed P_def by auto

lemma(in UP_cring) to_fun_finsum: 
  assumes "finite (Y::'d set)"
  assumes "f \<in> UNIV \<rightarrow> carrier (UP R)"
  assumes "t \<in> carrier R"
  shows "to_fun (finsum (UP R) f Y) t = finsum R (\<lambda>i. (to_fun (f i) t)) Y"
proof(rule finite.induct[of Y])
  show "finite Y"
    using assms by blast 
  show "to_fun (finsum (UP R) f {}) t = (\<Oplus>i\<in>{}. to_fun (f i) t)"
    using P.finsum_empty[of f] assms unfolding P_def R.finsum_empty 
    using P_def to_fun_zero by presburger
  show  "\<And>A a. finite A \<Longrightarrow>
           to_fun (finsum (UP R) f A) t = (\<Oplus>i\<in>A. to_fun (f i) t) \<Longrightarrow> to_fun (finsum (UP R) f (insert a A)) t = (\<Oplus>i\<in>insert a A. to_fun (f i) t)"
  proof-     
    fix A :: "'d set" fix a
    assume A: "finite A" "to_fun (finsum (UP R) f A) t = (\<Oplus>i\<in>A. to_fun (f i) t)"
    show "to_fun (finsum (UP R) f (insert a A)) t = (\<Oplus>i\<in>insert a A. to_fun (f i) t)"
    proof(cases "a \<in> A")
      case True
      then show ?thesis using A 
        by (metis insert_absorb)
    next
      case False
      have 0: "finsum (UP R) f (insert a A) = f a \<oplus>\<^bsub>UP R\<^esub> finsum (UP R) f A"
        using A False finsum_insert[of A a f] assms unfolding P_def  by blast
      have 1: "to_fun (f a \<oplus>\<^bsub>P\<^esub>finsum (UP R) f A ) t =  to_fun (f a) t \<oplus> to_fun (finsum (UP R) f A) t"
        apply(rule to_fun_plus[of  "finsum (UP R) f A" "f a" t])
        using assms(2) finsum_closed[of f A] A unfolding P_def apply blast
        using P_def assms apply blast
        using assms by blast
      have 2: "to_fun (f a \<oplus>\<^bsub>P\<^esub>finsum (UP R) f A ) t =  to_fun (f a) t \<oplus> (\<Oplus>i\<in>A. to_fun (f i) t)"
        unfolding  1 A by blast 
      have 3: "(\<Oplus>i\<in>insert a A. to_fun (f i) t) = to_fun (f a) t \<oplus> (\<Oplus>i\<in>A. to_fun (f i) t)"
        apply(rule  R.finsum_insert, rule A, rule False)
        using to_fun_closed assms unfolding P_def apply blast
        apply(rule to_fun_closed) using assms unfolding P_def apply blast using assms by blast 
      show ?thesis 
        unfolding 0 unfolding 3 using 2 unfolding P_def by blast 
    qed
  qed
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Inclusion of a Ring into its Polynomials Ring via Constants\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition to_polynomial where
"to_polynomial R = (\<lambda>a. monom (UP R) a 0)"

context UP_cring
begin

abbreviation(input) to_poly where
"to_poly  \<equiv> to_polynomial R"

lemma to_poly_mult_simp:
  assumes "b \<in> carrier R"
  assumes "f \<in> carrier (UP R)"
  shows "(to_polynomial R b) \<otimes>\<^bsub>UP R\<^esub> f = b \<odot>\<^bsub>UP R\<^esub> f"
        "f  \<otimes>\<^bsub>UP R\<^esub> (to_polynomial R b) = b \<odot>\<^bsub>UP R\<^esub> f"   
  unfolding to_polynomial_def
  using assms  P_def monom_mult_is_smult apply auto[1]
  using UP_cring.UP_m_comm UP_cring_axioms UP_ring.monom_closed 
        UP_ring.monom_mult_is_smult UP_ring_axioms assms(1) assms(2) 
  by fastforce  

lemma to_fun_to_poly:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_fun (to_poly a) b = a"
  unfolding to_function_def to_fun_def to_polynomial_def 
  by (simp add: UP_pre_univ_prop.eval_const UP_pre_univ_prop_fact assms(1) assms(2))
  
lemma to_poly_inverse:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "f = to_poly (f 0)"
  using P_def assms(1) assms(2) 
  by (metis ltrm_deg_0 to_polynomial_def) 

lemma to_poly_closed:
  assumes "a \<in> carrier R"
  shows "to_poly a \<in> carrier P"
  by (metis P_def assms monom_closed to_polynomial_def)

lemma degree_to_poly[simp]:
  assumes "a \<in> carrier R"
  shows "degree (to_poly a) = 0"
  by (metis P_def assms deg_const to_polynomial_def)

lemma to_poly_is_ring_hom:
"to_poly \<in> ring_hom R P"
  unfolding to_polynomial_def
  unfolding P_def
  using UP_ring.const_ring_hom[of R]
  UP_ring_axioms by simp 

lemma to_poly_add:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<oplus> b) = to_poly a \<oplus>\<^bsub>P\<^esub> to_poly b"
  by (simp add: assms(1) assms(2) ring_hom_add to_poly_is_ring_hom)

lemma to_poly_mult:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<otimes> b) = to_poly a \<otimes>\<^bsub>P\<^esub> to_poly b"
  by (simp add: assms(1) assms(2) ring_hom_mult to_poly_is_ring_hom)

lemma to_poly_minus:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_poly (a \<ominus> b) = to_poly a \<ominus>\<^bsub>P\<^esub> to_poly b"
  by (metis P.minus_eq P_def R.add.inv_closed R.ring_axioms UP_ring.monom_add 
      UP_ring_axioms assms(1) assms(2) monom_a_inv ring.ring_simprules(14) to_polynomial_def)

lemma to_poly_a_inv:
  assumes "a \<in> carrier R"
  shows "to_poly (\<ominus> a) =  \<ominus>\<^bsub>P\<^esub> to_poly a"
  by (metis P_def assms monom_a_inv to_polynomial_def)

lemma to_poly_nat_pow:
  assumes "a \<in> carrier R"
  shows "(to_poly a) [^]\<^bsub>P\<^esub> (n::nat)= to_poly (a[^]n)"
  using assms UP_cring UP_cring_axioms UP_cring_def UnivPoly.ring_hom_cringI ring_hom_cring.hom_pow to_poly_is_ring_hom 
  by fastforce


end

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Polynomial Substitution\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition compose where
"compose R f g = eval R (UP R) (to_polynomial R) g f"

abbreviation(in UP_cring)(input) sub  (infixl "of" 70) where
"sub f g \<equiv> compose R f g"

definition rev_compose  where
"rev_compose R = eval R (UP R) (to_polynomial R)"

abbreviation(in UP_cring)(input) rev_sub  where
"rev_sub \<equiv> rev_compose R"

context UP_cring
begin

lemma  sub_rev_sub:
"sub f g = rev_sub g f"
  unfolding compose_def rev_compose_def 
  by simp  

lemma(in UP_cring) to_poly_UP_pre_univ_prop:
"UP_pre_univ_prop R P to_poly"
proof 
  show "to_poly \<in> ring_hom R P" 
    by (simp add: to_poly_is_ring_hom)
qed

lemma rev_sub_is_hom:
  assumes "g \<in> carrier P"
  shows "rev_sub g \<in> ring_hom P P"
  unfolding rev_compose_def
  using to_poly_UP_pre_univ_prop assms(1) UP_pre_univ_prop.eval_ring_hom[of R P to_poly g] 
  unfolding P_def apply auto 
  done

lemma rev_sub_closed:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "rev_sub q p \<in> carrier P"
  using rev_sub_is_hom[of q] assms ring_hom_closed[of "rev_sub q" P P p] by auto  

lemma sub_closed:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "sub q p \<in> carrier P"
  by (simp add: assms(1) assms(2) rev_sub_closed sub_rev_sub)

lemma rev_sub_add:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "rev_sub g (f \<oplus>\<^bsub>P\<^esub> h) = (rev_sub g f) \<oplus>\<^bsub>P\<^esub> (rev_sub g h)"
  using rev_sub_is_hom assms ring_hom_add by fastforce

lemma sub_add: 
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "((f \<oplus>\<^bsub>P\<^esub> h) of g) = ((f of g) \<oplus>\<^bsub>P\<^esub> (h of g))"
  by (simp add: assms(1) assms(2) assms(3) rev_sub_add sub_rev_sub)

lemma rev_sub_mult:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "rev_sub g (f \<otimes>\<^bsub>P\<^esub> h) = (rev_sub g f) \<otimes>\<^bsub>P\<^esub> (rev_sub g h)"
  using rev_sub_is_hom assms ring_hom_mult  by fastforce

lemma sub_mult: 
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "h \<in>carrier P"
  shows "((f \<otimes>\<^bsub>P\<^esub> h) of g) = ((f of g) \<otimes>\<^bsub>P\<^esub> (h of g))"
  by (simp add: assms(1) assms(2) assms(3) rev_sub_mult sub_rev_sub)

lemma sub_monom:
  assumes "g \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "sub (monom (UP R) a n) g = to_poly a  \<otimes>\<^bsub>UP R\<^esub> (g[^]\<^bsub>UP R\<^esub> (n::nat))" 
        "sub (monom (UP R) a n) g = a \<odot>\<^bsub>UP R\<^esub> (g[^]\<^bsub>UP R\<^esub> (n::nat))" 
   apply (simp add: UP_cring.to_poly_UP_pre_univ_prop UP_cring_axioms 
          UP_pre_univ_prop.eval_monom assms(1) assms(2) Cring_Poly.compose_def)
  by (metis P_def UP_cring.to_poly_mult_simp(1) UP_cring_axioms UP_pre_univ_prop.eval_monom 
      UP_ring assms(1) assms(2) Cring_Poly.compose_def monoid.nat_pow_closed ring_def to_poly_UP_pre_univ_prop) 
 
text\<open>Subbing into a constant does nothing\<close>

lemma rev_sub_to_poly:
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "rev_sub g (to_poly a) = to_poly a"
  unfolding to_polynomial_def rev_compose_def
  using to_poly_UP_pre_univ_prop 
  unfolding to_polynomial_def 
     using P_def UP_pre_univ_prop.eval_const assms(1) assms(2) by fastforce

lemma sub_to_poly:
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(to_poly a) of g  = to_poly a"
  by (simp add: assms(1) assms(2) rev_sub_to_poly sub_rev_sub)

lemma sub_const:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "f of g = f"
  by (metis lcf_closed assms(1) assms(2) assms(3) sub_to_poly to_poly_inverse)

text\<open>Substitution into a monomial\<close>

lemma monom_sub:
  assumes "a \<in> carrier R"
  assumes "g \<in> carrier P"
  shows "(monom P a n) of g = a \<odot>\<^bsub>P\<^esub> g[^]\<^bsub>P\<^esub> n"
    unfolding compose_def
    using assms UP_pre_univ_prop.eval_monom[of R P to_poly a g n] to_poly_UP_pre_univ_prop 
    unfolding P_def  
    using P.nat_pow_closed P_def  to_poly_mult_simp(1) 
    by (simp add: to_poly_mult_simp(1) UP_cring_axioms)
    
lemma(in UP_cring)  cring_sub_monom_bound:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  assumes "f = monom P a n"
  assumes "g \<in> carrier P"
  shows "degree (f of g) \<le> n*(degree g)"
proof-
  have "f of g = (to_poly a) \<otimes>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
    unfolding compose_def
    using assms UP_pre_univ_prop.eval_monom[of R P to_poly a g] to_poly_UP_pre_univ_prop 
    unfolding P_def  
    by blast
  then show ?thesis 
    by (smt P.nat_pow_closed assms(1) assms(4) cring_pow_deg_bound deg_mult_ring
        degree_to_poly le_trans plus_nat.add_0 to_poly_closed)
qed

lemma(in UP_cring)  cring_sub_monom:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  assumes "f = monom P a n"
  assumes "g \<in> carrier P"
  assumes "a \<otimes> (lcf g [^] n) \<noteq> \<zero>"
  shows "degree (f of g) = n*(degree g)"
proof-
  have 0: "f of g = (to_poly a) \<otimes>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
    unfolding compose_def
    using assms UP_pre_univ_prop.eval_monom[of R P to_poly a g] to_poly_UP_pre_univ_prop 
    unfolding P_def  
    by blast
  have 1: "lcf (to_poly a) \<otimes> lcf (g [^]\<^bsub>P\<^esub> n) \<noteq> \<zero>" 
    using assms 
    by (smt P.nat_pow_closed P_def R.nat_pow_closed R.r_null cring_pow_ltrm lcf_closed lcf_ltrm lcf_monom monom_pow to_polynomial_def)
  then show ?thesis 
    using 0 1 assms cring_pow_deg[of g n] cring_deg_mult[of "to_poly a" "g[^]\<^bsub>P\<^esub>n"]
    by (metis P.nat_pow_closed R.r_null add.right_neutral degree_to_poly to_poly_closed)
qed
    
lemma(in UP_domain)  sub_monom:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  assumes "f = monom P a n"
  assumes "g \<in> carrier P"
  shows "degree (f of g) = n*(degree g)"
proof-
  have "f of g = (to_poly a) \<otimes>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
    unfolding compose_def
    using assms UP_pre_univ_prop.eval_monom[of R P to_poly a g] to_poly_UP_pre_univ_prop 
    unfolding P_def  
    by blast
  then show ?thesis using deg_pow deg_mult 
    by (metis P.nat_pow_closed P_def assms(1) assms(2) 
        assms(4) deg_smult monom_mult_is_smult to_polynomial_def)
qed

text\<open>Subbing a constant into a polynomial yields a constant\<close>
lemma sub_in_const:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree g = 0"
  shows "degree (f of g) = 0"
proof-
  have "\<And>n. (\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = 0)"
  proof-
    fix n
    show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = 0"
    proof(induction n)
      case 0
      then show ?case 
        by (simp add: assms(1) sub_const)       
    next
      case (Suc n)
      fix n
      assume IH: "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = 0"
      show  "\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> (Suc n) \<Longrightarrow> degree (p of g) = 0"
      proof-
        fix p
        assume A0: "p \<in> carrier P"
        assume A1: "degree p \<le> (Suc n)"
        show "degree (p of g) = 0"
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis using IH 
            using A0 by auto
        next
          case False
          then have D: "degree p = Suc n" 
            by (simp add: A1 nat_less_le)
          show ?thesis
          proof-
            have P0: "degree ((trunc p) of g) = 0" using IH 
              by (metis A0 D less_Suc_eq_le trunc_degree trunc_closed zero_less_Suc)
            have P1: "degree ((ltrm p) of g) = 0" 
            proof-
              obtain a n where an_def: "ltrm p = monom P a n \<and> a \<in> carrier R"
                unfolding leading_term_def 
                using A0 P_def cfs_closed by blast
              obtain b where b_def: "g = monom P b 0 \<and> b \<in> carrier R"
                using assms deg_zero_impl_monom  coeff_closed 
                by blast               
              have 0: " monom P b 0 [^]\<^bsub>P\<^esub> n = monom P (b[^]n) 0"
                apply(induction n)
                 apply fastforce[1]
              proof- fix n::nat assume IH: "monom P b 0 [^]\<^bsub>P\<^esub> n = monom P (b [^] n) 0"
                have "monom P b 0 [^]\<^bsub>P\<^esub> Suc n = (monom P (b[^]n) 0) \<otimes>\<^bsub>P\<^esub> monom P b 0"
                  using IH by simp
                then have "monom P b 0 [^]\<^bsub>P\<^esub> Suc n = (monom P ((b[^]n)\<otimes>b) 0)"
                  using b_def  
                  by (simp add: monom_mult_is_smult monom_mult_smult)
                then show "monom P b 0 [^]\<^bsub>P\<^esub> Suc n = monom P (b [^] Suc n) 0 "
                  by simp 
              qed
                   
              then have 0: "a \<odot>\<^bsub>P\<^esub> monom P b 0 [^]\<^bsub>P\<^esub> n = monom P (a \<otimes> b[^]n) 0"
                by (simp add: an_def b_def monom_mult_smult)


              then show ?thesis using monom_sub[of a "monom P b 0" n] assms an_def 
                by (simp add: \<open>\<lbrakk>a \<in> carrier R; monom P b 0 \<in> carrier P\<rbrakk> \<Longrightarrow> monom P a n of monom P b 0 = a \<odot>\<^bsub>P\<^esub> monom P b 0 [^]\<^bsub>P\<^esub> n\<close> b_def)
            qed
            have P2: "p of g = (trunc p of g) \<oplus>\<^bsub>P\<^esub> ((ltrm p) of g)"
              by (metis A0 assms(1) ltrm_closed sub_add trunc_simps(1) trunc_closed)
            then show ?thesis 
              using P0 P1 P2 deg_add[of "trunc p of g" "ltrm p of g"] 
              by (metis A0 assms(1) le_0_eq ltrm_closed max_0R sub_closed trunc_closed)              
          qed
        qed
      qed
    qed
  qed
  then show ?thesis 
    using assms(2) by blast
qed

lemma (in UP_cring)  cring_sub_deg_bound:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  shows "degree (f of g) \<le> degree f * degree g"
proof-
  have "\<And>n. \<And> p. p \<in> carrier P \<Longrightarrow> (degree p) \<le> n \<Longrightarrow> degree (p of g) \<le> degree p * degree g"
  proof-
    fix n::nat
    show "\<And> p. p \<in> carrier P \<Longrightarrow> (degree p) \<le> n \<Longrightarrow> degree (p of g) \<le> degree p * degree g"
    proof(induction n)
      case 0
      then have B0: "degree p = 0" by auto 
      then show ?case using sub_const[of g p] 
        by (simp add: "0.prems"(1) assms(1))
    next
      case (Suc n)
      fix n
      assume IH: "(\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) \<le> degree p * degree g)"
      show " p \<in> carrier P \<Longrightarrow> degree p \<le> Suc n \<Longrightarrow> degree (p of g) \<le>  degree p * degree g"
      proof-
        assume A0: "p \<in> carrier P"
        assume A1: "degree p \<le> Suc n"
        show ?thesis 
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis using IH 
            by (simp add: A0)
        next
          case False
          then have D: "degree p = Suc n" 
            using A1 by auto  
          have P0: "(p of g) = ((trunc p) of g) \<oplus>\<^bsub>P\<^esub> ((ltrm p) of g)"
            by (metis A0 assms(1) ltrm_closed sub_add trunc_simps(1) trunc_closed)
          have P1: "degree ((trunc p) of g) \<le> (degree (trunc p))*(degree g)"
            using IH  by (metis A0 D less_Suc_eq_le trunc_degree trunc_closed zero_less_Suc)
          have P2: "degree ((ltrm p) of g) \<le> (degree p) * degree g"
            using A0 D P_def  UP_cring_axioms assms(1) 
            by (metis False cfs_closed coeff_simp cring_sub_monom_bound deg_zero lcoeff_nonzero2 less_Suc_eq_0_disj)                              
          then show ?thesis
            proof(cases "degree g = 0")
              case True
              then show ?thesis 
                by (simp add: Suc(2) assms(1) sub_in_const)
            next
              case F: False
              then show ?thesis 
              proof-
                have P3: "degree ((trunc p) of g) \<le> n*degree g"
                  using A0 False D  P1 P2  IH[of "trunc p"] trunc_degree[of p]
                proof -
                  { assume "degree (trunc p) < degree p"
                    then have "degree (trunc p) \<le> n"
                      using D by auto
                    then have ?thesis
                      by (meson P1 le_trans mult_le_cancel2) }
                  then show ?thesis
                    by (metis (full_types) A0 D Suc_mult_le_cancel1 nat_mult_le_cancel_disj trunc_degree)
                qed      
                then have P3': "degree ((trunc p) of g) < (degree p)*degree g"
                  using F D by auto 
                have P4: "degree (ltrm p of g) \<le> (degree p)*degree g"
                  using cring_sub_monom_bound  D P2 
                  by auto
                then show ?thesis 
                  using D  P0 P1 P3 P4 A0 P3' assms(1) bound_deg_sum less_imp_le_nat
                    ltrm_closed sub_closed trunc_closed 
                  by metis                   
              qed
            qed
          qed
        qed
      qed
  qed
  then show ?thesis 
    using assms(2) by blast
qed

lemma (in UP_cring)  cring_sub_deg:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "lcf f \<otimes> (lcf g [^] (degree f)) \<noteq> \<zero>"
  shows "degree (f of g) = degree f * degree g"
proof-
  have 0: "f of g = (trunc f of g) \<oplus>\<^bsub>P\<^esub> ((ltrm f) of g)"
    by (metis assms(1) assms(2) ltrm_closed rev_sub_add sub_rev_sub trunc_simps(1) trunc_closed)
  have 1: "lcf f \<noteq> \<zero>"
    using assms  cring.cring_simprules(26) lcf_closed 
    by auto
  have 2: "degree ((ltrm f) of g) = degree f * degree g"
    using 0 1 assms cring_sub_monom[of "lcf f" "ltrm f" "degree f" g] lcf_closed lcf_ltrm 
    by blast
  show ?thesis
    apply(cases "degree f = 0")
     apply (simp add: assms(1) assms(2))
    apply(cases "degree g = 0")
     apply (simp add: assms(1) assms(2) sub_in_const)
    using 0 1 assms cring_sub_deg_bound[of g "trunc f"] trunc_degree[of f]   
    using sub_const apply auto[1]
    apply(cases "degree g = 0")
    using 0 1 assms cring_sub_deg_bound[of g "trunc f"] trunc_degree[of f]   
    using sub_in_const apply fastforce
    unfolding 0 using 1 2 
    by (smt "0" ltrm_closed \<open>\<lbrakk>f \<in> carrier P; 0 < deg R f\<rbrakk> \<Longrightarrow> deg R (Cring_Poly.truncate R f) < deg R f\<close>
        assms(1) assms(2) cring_sub_deg_bound degree_of_sum_diff_degree equal_deg_sum
        le_eq_less_or_eq mult_less_cancel2 nat_neq_iff neq0_conv sub_closed trunc_closed)    
qed

lemma (in UP_domain)  sub_deg0:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes "f \<noteq> \<zero>\<^bsub>P\<^esub>"
  shows "degree (f of g) = degree f * degree g"
proof-
  have "\<And>n. \<And> p. p \<in> carrier P \<Longrightarrow> (degree p) \<le> n \<Longrightarrow> degree (p of g) = degree p * degree g"
  proof-
    fix n::nat
    show "\<And> p. p \<in> carrier P \<Longrightarrow> (degree p) \<le> n \<Longrightarrow> degree (p of g) = degree p * degree g"
    proof(induction n)
      case 0
      then have B0: "degree p = 0" by auto 
      then show ?case using sub_const[of g p] 
        by (simp add: "0.prems"(1) assms(1))
    next
      case (Suc n)
      fix n
      assume IH: "(\<And>p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> degree (p of g) = degree p * degree g)"
      show " p \<in> carrier P \<Longrightarrow> degree p \<le> Suc n \<Longrightarrow> degree (p of g) = degree p * degree g"
      proof-
        assume A0: "p \<in> carrier P"
        assume A1: "degree p \<le> Suc n"
        show ?thesis 
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis using IH 
            by (simp add: A0)
        next
          case False
          then have D: "degree p = Suc n" 
            using A1 by auto  
          have P0: "(p of g) = ((trunc p) of g) \<oplus>\<^bsub>P\<^esub> ((ltrm p) of g)"
            by (metis A0 assms(1) ltrm_closed sub_add trunc_simps(1) trunc_closed)
          have P1: "degree ((trunc p) of g) = (degree (trunc p))*(degree g)"
            using IH  by (metis A0 D less_Suc_eq_le trunc_degree trunc_closed zero_less_Suc)
          have P2: "degree ((ltrm p) of g) = (degree p) * degree g"
            using A0 D P_def UP_domain.sub_monom UP_cring_axioms assms(1) 
            by (metis False UP_domain_axioms UP_ring.coeff_simp UP_ring.lcoeff_nonzero2 UP_ring_axioms cfs_closed deg_nzero_nzero less_Suc_eq_0_disj)
                     
          then show ?thesis
            proof(cases "degree g = 0")
              case True
              then show ?thesis 
                by (simp add: Suc(2) assms(1) sub_in_const)
            next
              case False
              then show ?thesis 
              proof-
                have P3: "degree ((trunc p) of g) < degree ((ltrm p) of g)"
                  using False D  P1 P2  
                  by (metis (no_types, lifting) A0 mult.commute mult_right_cancel 
                      nat_less_le nat_mult_le_cancel_disj trunc_degree zero_less_Suc)
                then show ?thesis 
                 by (simp add: A0 ltrm_closed P0 P2 assms(1) equal_deg_sum sub_closed trunc_closed)                 
              qed
            qed
          qed
        qed
      qed
  qed
  then show ?thesis 
      using assms(2) by blast
qed

lemma(in UP_domain)  sub_deg:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  shows "degree (f of g) = degree f * degree g"
proof(cases "f = \<zero>\<^bsub>P\<^esub>")
  case True
  then show ?thesis 
    using assms(1)  sub_const by auto
next
  case False
  then show ?thesis 
    by (simp add: assms(1) assms(2) assms(3) sub_deg0)
qed

lemma(in UP_cring)  cring_ltrm_sub:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree g > 0"
  assumes "lcf f \<otimes> (lcf g [^] (degree f)) \<noteq> \<zero>"
  shows "ltrm (f of g) = ltrm ((ltrm f) of g)"
proof-
  have P0: "degree (f of g) = degree ((ltrm f) of g)"
    using assms(1) assms(2) assms(4) cring_sub_deg lcf_eq ltrm_closed deg_ltrm 
    by auto               
  have P1: "f of g = ((trunc f) of g) \<oplus>\<^bsub>P\<^esub>((ltrm f) of g)"
    by (metis assms(1) assms(2) ltrm_closed rev_sub_add sub_rev_sub trunc_simps(1) trunc_closed)
  then show ?thesis
  proof(cases "degree f = 0")
    case True
    then show ?thesis 
      using ltrm_deg_0 assms(2) by auto     
  next
    case False
    have P2: "degree (f of g) = degree f * degree g"
      by (simp add: assms(1) assms(2) assms(4) cring_sub_deg)      
    then have P3: "degree ((trunc f) of g) < degree ((ltrm f) of g)"
      using False P0 P1 P_def UP_cring.sub_closed trunc_closed UP_cring_axioms
          UP_ring.degree_of_sum_diff_degree UP_ring.ltrm_closed UP_ring_axioms assms(1) 
          assms(2) assms(4) cring_sub_deg_bound le_antisym less_imp_le_nat less_nat_zero_code
          mult_right_le_imp_le nat_neq_iff trunc_degree
      by (smt assms(3))
    then show ?thesis using P0 P1 P2 
      by (metis (no_types, lifting) ltrm_closed ltrm_of_sum_diff_degree P.add.m_comm assms(1) assms(2) sub_closed trunc_closed)      
  qed
qed

lemma(in UP_domain)  ltrm_sub:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree g > 0"
  shows "ltrm (f of g) = ltrm ((ltrm f) of g)"
proof-
  have P0: "degree (f of g) = degree ((ltrm f) of g)"
    using sub_deg 
    by (metis ltrm_closed assms(1) assms(2) assms(3) deg_zero deg_ltrm nat_neq_iff)       
  have P1: "f of g = ((trunc f) of g) \<oplus>\<^bsub>P\<^esub>((ltrm f) of g)"
    by (metis assms(1) assms(2) ltrm_closed rev_sub_add sub_rev_sub trunc_simps(1) trunc_closed)
  then show ?thesis
  proof(cases "degree f = 0")
    case True
    then show ?thesis 
      using ltrm_deg_0 assms(2) by auto    
  next
    case False
    then have P2: "degree ((trunc f) of g) < degree ((ltrm f) of g)"
      using sub_deg 
      by (metis (no_types, lifting) ltrm_closed assms(1) assms(2) assms(3) deg_zero
          deg_ltrm mult_less_cancel2 neq0_conv trunc_closed trunc_degree)      
    then show ?thesis 
      using P0 P1 P2 
      by (metis (no_types, lifting) ltrm_closed ltrm_of_sum_diff_degree P.add.m_comm assms(1) assms(2) sub_closed trunc_closed)
  qed
qed

lemma(in UP_cring)  cring_lcf_of_sub_in_ltrm:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "degree g > 0"
  assumes "(lcf f) \<otimes> ((lcf g)[^]n) \<noteq>\<zero>"
  shows "lcf ((ltrm f) of g) = (lcf f) \<otimes> ((lcf g)[^]n)"
  by (metis (no_types, lifting) P.nat_pow_closed P_def R.r_null UP_cring.monom_sub UP_cring_axioms 
      assms(1) assms(2) assms(3) assms(5) cfs_closed cring_lcf_pow cring_lcf_scalar_mult)

lemma(in UP_domain)  lcf_of_sub_in_ltrm:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "degree g > 0"
  shows "lcf ((ltrm f) of g) = (lcf f) \<otimes> ((lcf g)[^]n)"
proof(cases "degree f = 0")
  case True
  then show ?thesis 
    using ltrm_deg_0 assms(1) assms(2) assms(3) cfs_closed 
    by (simp add: sub_const)       
next
  case False
  then show ?thesis 
  proof-
    have P0: "(ltrm f) of g = (to_poly (lcf f)) \<otimes>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
      unfolding compose_def
      using assms UP_pre_univ_prop.eval_monom[of R P to_poly "(lcf f)" g n] to_poly_UP_pre_univ_prop 
      unfolding P_def  
      using P_def cfs_closed by blast        
    have P1: "(ltrm f) of g = (lcf f) \<odot>\<^bsub>P\<^esub>(g[^]\<^bsub>P\<^esub>n)"
      using P0 P.nat_pow_closed 
      by (simp add: assms(1) assms(2) assms(3) cfs_closed monom_sub)          
    have P2: "ltrm ((ltrm f) of g) = (ltrm (to_poly (lcf f))) \<otimes>\<^bsub>P\<^esub> (ltrm (g[^]\<^bsub>P\<^esub>n))"
      using P0 ltrm_mult P.nat_pow_closed P_def assms(1) assms(2) 
         to_poly_closed 
      by (simp add: cfs_closed)                  
    have P3: "ltrm ((ltrm f) of g) =  (to_poly (lcf f)) \<otimes>\<^bsub>P\<^esub> (ltrm (g[^]\<^bsub>P\<^esub>n))"
      using P2  ltrm_deg_0 assms(2) to_poly_closed 
      by (simp add: cfs_closed)           
    have P4: "ltrm ((ltrm f) of g) = (lcf f) \<odot>\<^bsub>P\<^esub> ((ltrm g)[^]\<^bsub>P\<^esub>n)"
      using P.nat_pow_closed P1 P_def assms(1) assms(2) ltrm_pow0 ltrm_smult 
      by (simp add: cfs_closed)
    have P5: "lcf ((ltrm f) of g) = (lcf f) \<otimes> (lcf ((ltrm g)[^]\<^bsub>P\<^esub>n))"
      using lcf_scalar_mult P4  by (metis P.nat_pow_closed P1 cfs_closed 
          UP_smult_closed assms(1) assms(2) assms(3) lcf_eq ltrm_closed sub_rev_sub)
    show ?thesis
      using P5 ltrm_pow lcf_pow assms(1) lcf_eq ltrm_closed by presburger
  qed
qed

lemma(in UP_cring)  cring_ltrm_of_sub_in_ltrm:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "degree g > 0"
  assumes "(lcf f) \<otimes> ((lcf g)[^]n) \<noteq>\<zero>"
  shows "ltrm ((ltrm f) of g) = (lcf f) \<odot>\<^bsub>P\<^esub> ((ltrm g)[^]\<^bsub>P\<^esub>n)"
  by (smt lcf_eq ltrm_closed R.nat_pow_closed R.r_null assms(1) assms(2) assms(3) 
      assms(4) assms(5) cfs_closed cring_lcf_of_sub_in_ltrm cring_lcf_pow cring_pow_ltrm
      cring_pow_deg cring_sub_deg deg_zero deg_ltrm monom_mult_smult neq0_conv)
  
lemma(in UP_domain)  ltrm_of_sub_in_ltrm:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "degree g > 0"
  shows "ltrm ((ltrm f) of g) = (lcf f) \<odot>\<^bsub>P\<^esub> ((ltrm g)[^]\<^bsub>P\<^esub>n)"
  by (smt Group.nat_pow_0 lcf_of_sub_in_ltrm lcf_pow lcf_scalar_mult ltrm_closed 
      ltrm_pow0 ltrm_smult P.nat_pow_closed P_def UP_ring.monom_one UP_ring_axioms assms(1) 
      assms(2) assms(3) assms(4) cfs_closed coeff_simp deg_const deg_nzero_nzero deg_pow 
      deg_smult deg_ltrm lcoeff_nonzero2 nat_less_le sub_deg)

text\<open>formula for the leading term of a composition \<close>

lemma(in UP_domain)  cring_ltrm_of_sub:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "degree g > 0"
  assumes "(lcf f) \<otimes> ((lcf g)[^]n) \<noteq>\<zero>"
  shows "ltrm (f of g) = (lcf f) \<odot>\<^bsub>P\<^esub> ((ltrm g)[^]\<^bsub>P\<^esub>n)"
  using ltrm_of_sub_in_ltrm ltrm_sub assms(1) assms(2) assms(3) assms(4) by presburger
    
lemma(in UP_domain)  ltrm_of_sub:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "degree f = n"
  assumes "degree g > 0"
  shows "ltrm (f of g) = (lcf f) \<odot>\<^bsub>P\<^esub> ((ltrm g)[^]\<^bsub>P\<^esub>n)"
  using ltrm_of_sub_in_ltrm ltrm_sub assms(1) assms(2) assms(3) assms(4) by presburger
   
text\<open>subtitution is associative\<close>

lemma  sub_assoc_monom:
  assumes "f \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "r \<in> carrier P"
  shows "(ltrm f) of (q of r) = ((ltrm f) of q) of r"
proof-
  obtain n where n_def: "n = degree f"
    by simp
  obtain a where a_def: "a \<in> carrier R \<and> (ltrm f) = monom P a n"
    using assms(1) cfs_closed n_def by blast         
  have LHS: "(ltrm f) of (q of r) = a \<odot>\<^bsub>P\<^esub> (q of r)[^]\<^bsub>P\<^esub> n"
    by (metis P.nat_pow_closed P_def UP_pre_univ_prop.eval_monom a_def assms(2)
        assms(3) compose_def monom_mult_is_smult sub_closed to_poly_UP_pre_univ_prop to_polynomial_def)
  have RHS0: "((ltrm f) of q) of r = (a \<odot>\<^bsub>P\<^esub> q[^]\<^bsub>P\<^esub> n)of r"
    by (metis P.nat_pow_closed P_def UP_pre_univ_prop.eval_monom a_def 
        assms(2) compose_def monom_mult_is_smult to_poly_UP_pre_univ_prop to_polynomial_def)
  have RHS1: "((ltrm f) of q) of r = ((to_poly a) \<otimes>\<^bsub>P\<^esub> q[^]\<^bsub>P\<^esub> n)of r"
    using RHS0  by (metis P.nat_pow_closed P_def a_def 
        assms(2) monom_mult_is_smult to_polynomial_def)
  have RHS2: "((ltrm f) of q) of r = ((to_poly a) of r) \<otimes>\<^bsub>P\<^esub> (q[^]\<^bsub>P\<^esub> n of r)"
    using RHS1 a_def assms(2) assms(3) sub_mult to_poly_closed by auto
  have RHS3: "((ltrm f) of q) of r = (to_poly a) \<otimes>\<^bsub>P\<^esub> (q[^]\<^bsub>P\<^esub> n of r)"
    using RHS2 a_def assms(3) sub_to_poly by auto
  have RHS4: "((ltrm f) of q) of r = a \<odot>\<^bsub>P\<^esub> ((q[^]\<^bsub>P\<^esub> n)of r)"
    using RHS3 
    by (metis P.nat_pow_closed P_def a_def assms(2) assms(3) 
        monom_mult_is_smult sub_closed to_polynomial_def)
  have "(q of r)[^]\<^bsub>P\<^esub> n = ((q[^]\<^bsub>P\<^esub> n)of r)" 
    apply(induction n) 
    apply (metis Group.nat_pow_0 P.ring_simprules(6) assms(3) deg_one sub_const)
    by (simp add: assms(2) assms(3) sub_mult)    
  then show ?thesis using RHS4 LHS by simp
qed

lemma sub_assoc:
  assumes "f \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "r \<in> carrier P"
  shows "f of (q of r) = (f of q) of r"
proof-
  have "\<And> n. \<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> p of (q of r) = (p of q) of r"
  proof-
    fix n
    show "\<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> p of (q of r) = (p of q) of r"
    proof(induction n)
      case 0
      then have deg_p: "degree p = 0"
        by blast
      then have B0: "p of (q of r) = p"
        using sub_const[of "q of r" p] assms  "0.prems"(1) sub_closed by blast
      have B1: "(p of q) of r = p"
      proof-
        have p0: "p of q = p"
          using deg_p 0 assms(2) 
          by (simp add: P_def UP_cring.sub_const UP_cring_axioms)                             
        show ?thesis 
          unfolding p0 using deg_p 0 assms(3) 
          by (simp add: P_def UP_cring.sub_const UP_cring_axioms)                             
      qed
      then show "p of (q of r) = (p of q) of r" using B0 B1 by auto 
    next
      case (Suc n)
      fix n
      assume IH: "\<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> n \<Longrightarrow> p of (q of r) = (p of q) of r"
      then show "\<And> p. p \<in> carrier P \<Longrightarrow> degree p \<le> Suc n \<Longrightarrow> p of (q of r) = (p of q) of r"
      proof-
        fix p
        assume A0: " p \<in> carrier P "
        assume A1: "degree p \<le> Suc n"
        show "p of (q of r) = (p of q) of r"
        proof(cases "degree p < Suc n")
          case True
          then show ?thesis using A0 A1 IH by auto 
        next
          case False
          then have "degree p = Suc n"
            using A1 by auto 
          have I0: "p of (q of r) = ((trunc p) \<oplus>\<^bsub>P\<^esub> (ltrm p)) of (q of r)"
            using A0 trunc_simps(1) by auto
          have I1: "p of (q of r) = ((trunc p)  of (q of r)) \<oplus>\<^bsub>P\<^esub> ((ltrm p)  of (q of r))"
            using I0 sub_add 
            by (simp add: A0 assms(2) assms(3) ltrm_closed rev_sub_closed sub_rev_sub trunc_closed)
          have I2: "p of (q of r) = (((trunc p)  of q) of r) \<oplus>\<^bsub>P\<^esub> (((ltrm p)  of q) of r)"
            using IH[of "trunc p"] sub_assoc_monom[of p q r] 
            by (metis A0 I1 \<open>degree p = Suc n\<close> assms(2) assms(3) 
                less_Suc_eq_le trunc_degree trunc_closed zero_less_Suc)
          have I3: "p of (q of r) = (((trunc p)  of q) \<oplus>\<^bsub>P\<^esub> ((ltrm p)  of q)) of r"
            using sub_add trunc_simps(1) assms   
            by (simp add: A0 I2 ltrm_closed sub_closed trunc_closed)
          have I4: "p of (q of r) = (((trunc p)\<oplus>\<^bsub>P\<^esub>(ltrm p))   of q)  of r"
            using sub_add trunc_simps(1) assms   
            by (simp add: trunc_simps(1) A0 I3 ltrm_closed trunc_closed)
          then show ?thesis 
            using A0 trunc_simps(1) by auto
        qed
      qed
    qed
  qed
  then show ?thesis 
    using assms(1) by blast
qed

lemma sub_smult:
  assumes "f \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(a\<odot>\<^bsub>P\<^esub>f ) of q = a\<odot>\<^bsub>P\<^esub>(f of q)"
proof-
  have "(a\<odot>\<^bsub>P\<^esub>f ) of q = ((to_poly a) \<otimes>\<^bsub>P\<^esub>f) of q"
    using assms  by (metis P_def monom_mult_is_smult to_polynomial_def)
  then have "(a\<odot>\<^bsub>P\<^esub>f ) of q = ((to_poly a) of q) \<otimes>\<^bsub>P\<^esub>(f of q)"
    by (simp add: assms(1) assms(2) assms(3) sub_mult to_poly_closed)
  then have "(a\<odot>\<^bsub>P\<^esub>f ) of q = (to_poly a) \<otimes>\<^bsub>P\<^esub>(f of q)"
    by (simp add: assms(2) assms(3) sub_to_poly)
  then show ?thesis 
    by (metis P_def assms(1) assms(2) assms(3) 
        monom_mult_is_smult sub_closed to_polynomial_def)
qed

lemma to_fun_sub_monom:
  assumes "is_UP_monom f"
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "to_fun (f of g) a = to_fun f (to_fun g a)"   
proof-
  obtain b n where b_def: "b \<in> carrier R \<and> f = monom P b n"
    using assms unfolding is_UP_monom_def 
     using P_def cfs_closed by blast     
  then have P0: "f of g = b \<odot>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n)"
    using b_def assms(2) monom_sub by blast
  have P1: "UP_pre_univ_prop R R (\<lambda>x. x)" 
    by (simp add: UP_pre_univ_prop_fact)
  then have P2: "to_fun f (to_fun g a) = b \<otimes>((to_fun g a)[^]n)"
    using P1 to_fun_eval[of f "to_fun g a"] P_def UP_pre_univ_prop.eval_monom assms(1)
          assms(2) assms(3) b_def is_UP_monomE(1) to_fun_closed 
    by force
  have P3: "to_fun (monom P b n of g) a =  b \<otimes>((to_fun g a)[^]n)"
  proof-
    have 0: "to_fun (monom P b n of g) a = eval R R (\<lambda>x. x) a  (b \<odot>\<^bsub>P\<^esub> (g[^]\<^bsub>P\<^esub>n) )"

      using UP_pre_univ_prop.eval_monom[of R "(UP R)" to_poly b g n]
            P_def assms(2) b_def to_poly_UP_pre_univ_prop to_fun_eval P0
      by (metis assms(3) monom_closed sub_closed)      
    have 1: "to_fun (monom P b n of g) a = (eval R R (\<lambda>x. x) a  (to_poly b)) \<otimes> ( eval R R (\<lambda>x. x) a ( g [^]\<^bsub>UP R\<^esub> n ))"
      using 0 eval_ring_hom 
      by (metis P.nat_pow_closed P0 P_def assms(2) assms(3) b_def monom_mult_is_smult to_fun_eval to_fun_mult to_poly_closed to_polynomial_def)                
    have 2: "to_fun (monom P b n of g) a = b \<otimes> ( eval R R (\<lambda>x. x) a ( g [^]\<^bsub>UP R\<^esub> n ))"
      using 1 assms(3) b_def to_fun_eval to_fun_to_poly to_poly_closed by auto              
    then show ?thesis 
      unfolding to_function_def to_fun_def 
      using eval_ring_hom P_def UP_pre_univ_prop.ring_homD UP_pre_univ_prop_fact 
            assms(2) assms(3) ring_hom_cring.hom_pow by fastforce
  qed
  then show ?thesis 
    using b_def P2 by auto
qed

lemma to_fun_sub:
  assumes "g \<in> carrier P"
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "to_fun (f of  g) a = (to_fun f) (to_fun g a)"
proof(rule poly_induct2[of f])
  show "f \<in> carrier P" 
    using assms by auto 
  show "\<And>p. p \<in> carrier P \<Longrightarrow> degree p = 0 \<Longrightarrow> to_fun (p of g) a = to_fun p (to_fun g a)"
  proof-
    fix p
    assume A0: "p \<in> carrier P"
    assume A1: "degree p = 0"
    then have P0: "degree (p of g) = 0"
      by (simp add: A0 assms(1) sub_const)    
    then obtain b where b_def: "p of g = to_poly b \<and> b \<in> carrier R"
      using A0 A1 cfs_closed assms(1) to_poly_inverse 
      by (meson sub_closed)
    then have "to_fun (p of g) a = b" 
      by (simp add: assms(3) to_fun_to_poly)     
    have "p of g = p"
      using A0 A1 P_def sub_const UP_cring_axioms assms(1) by blast
    then have P1: "p = to_poly b"
      using b_def by auto
    have "to_fun g a \<in> carrier R"
      using assms
      by (simp add: to_fun_closed)  
    then show "to_fun (p of g) a =  to_fun p (to_fun g a)"
      using P1 \<open>to_fun (p of g) a = b\<close> b_def 
      by (simp add: to_fun_to_poly)      
  qed
  show "\<And>p. 0 < degree p \<Longrightarrow> p \<in> carrier P \<Longrightarrow> 
            to_fun (trunc p of g) a = to_fun (trunc p) (to_fun g a) \<Longrightarrow> 
            to_fun (p of g) a = to_fun p (to_fun g a)"
  proof-
    fix p
    assume A0: "0 < degree p"
    assume A1: " p \<in> carrier P"
    assume A2: "to_fun (trunc p of g) a = to_fun (trunc p) (to_fun g a)"
    show "to_fun (p of g) a = to_fun p (to_fun g a)"
    proof-
      have "p of g = (trunc p) of g \<oplus>\<^bsub>P\<^esub> (ltrm p) of g"
        by (metis A1 assms(1) ltrm_closed sub_add trunc_simps(1) trunc_closed)
      then have "to_fun (p of g) a = to_fun ((trunc p) of g) a \<oplus> (to_fun ((ltrm p) of g) a)"
        by (simp add: A1 assms(1) assms(3) to_fun_plus ltrm_closed sub_closed trunc_closed)        
      then have 0: "to_fun (p of g) a = to_fun (trunc p) (to_fun g a) \<oplus> (to_fun ((ltrm p) of g) a)"
        by (simp add: A2)
      have "(to_fun ((ltrm p) of g) a) = to_fun (ltrm p) (to_fun g a)"
        using to_fun_sub_monom 
        by (simp add: A1 assms(1) assms(3) ltrm_is_UP_monom)
      then have "to_fun (p of g) a = to_fun (trunc p) (to_fun g a) \<oplus>  to_fun (ltrm p) (to_fun g a)"
        using 0 by auto 
      then show ?thesis 
        by (metis A1 assms(1) assms(3) to_fun_closed to_fun_plus ltrm_closed trunc_simps(1) trunc_closed)
    qed
  qed
qed
end


text\<open>More material on constant terms and constant coefficients\<close>

context UP_cring
begin

lemma to_fun_ctrm:
  assumes "f \<in> carrier P"
  assumes  "b \<in> carrier R"  
  shows "to_fun (ctrm f) b = (f 0)"
  using assms 
  by (metis ctrm_degree ctrm_is_poly lcf_monom(2) P_def cfs_closed to_fun_to_poly to_poly_inverse)   

lemma to_fun_smult:
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  assumes "c \<in> carrier R"
  shows "to_fun (c \<odot>\<^bsub>P\<^esub> f) b = c \<otimes>(to_fun f b)"
proof-
  have "(c \<odot>\<^bsub>P\<^esub> f) = (to_poly c) \<otimes>\<^bsub>P\<^esub> f"
    by (metis P_def assms(1) assms(3) monom_mult_is_smult to_polynomial_def)
  then have "to_fun (c \<odot>\<^bsub>P\<^esub> f) b = to_fun (to_poly c) b \<otimes> to_fun f b"
    by (simp add: assms(1) assms(2) assms(3) to_fun_mult to_poly_closed)    
  then show  ?thesis 
    by (simp add: assms(2) assms(3) to_fun_to_poly)  
qed

lemma to_fun_monom:
  assumes "c \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "to_fun (monom P c n) x = c \<otimes> x [^] n"
  by (smt P_def R.m_comm R.nat_pow_closed UP_cring.to_poly_nat_pow UP_cring_axioms assms(1) 
      assms(2) monom_is_UP_monom(1) sub_monom(1) to_fun_smult to_fun_sub_monom to_fun_to_poly 
      to_poly_closed to_poly_mult_simp(2))

lemma zcf_monom:
  assumes "a \<in> carrier R"
  shows "zcf (monom P a n) = to_fun (monom P a n) \<zero>"
  using to_fun_monom unfolding zcf_def 
  by (simp add: R.nat_pow_zero assms cfs_monom)

lemma zcf_to_fun: 
  assumes "p \<in> carrier P"
  shows "zcf p = to_fun p \<zero>"
  apply(rule poly_induct3[of p])
  apply (simp add: assms)
  using R.zero_closed zcf_add to_fun_plus apply presburger
  using zcf_monom by blast

lemma zcf_to_poly[simp]:
  assumes "a \<in> carrier R"
  shows "zcf (to_poly a) = a"
  by (metis assms cfs_closed degree_to_poly to_fun_to_poly to_poly_inverse to_poly_closed zcf_def)

lemma zcf_ltrm_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree p > 0"
  shows "zcf((ltrm p) \<otimes>\<^bsub>P\<^esub> q) = \<zero>"
  using zcf_to_fun[of "ltrm p \<otimes>\<^bsub>P\<^esub> q" ]
  by (metis ltrm_closed P.l_null P.m_closed R.zero_closed UP_zero_closed zcf_to_fun
      zcf_zero assms(1) assms(2) assms(3) coeff_ltrm to_fun_mult)

lemma zcf_mult:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "zcf(p \<otimes>\<^bsub>P\<^esub> q) = (zcf p) \<otimes> (zcf q)"
  using zcf_to_fun[of " p \<otimes>\<^bsub>P\<^esub> q" ] zcf_to_fun[of "p" ] zcf_to_fun[of "q" ] to_fun_mult[of q p \<zero>]
  by (simp add: assms(1) assms(2))

lemma zcf_is_ring_hom:
"zcf\<in> ring_hom P R"
  apply(rule ring_hom_memI)
  using zcf_mult zcf_add
  apply (simp add: P_def UP_ring.cfs_closed UP_ring_axioms zcf_def)
    apply (simp add: zcf_mult)
      using zcf_add apply auto[1]
        by simp  

lemma ctrm_is_ring_hom:
"ctrm \<in> ring_hom P P"
  apply(rule ring_hom_memI)
     apply (simp add: ctrm_is_poly)
      apply (metis zcf_def zcf_mult cfs_closed monom_mult zero_eq_add_iff_both_eq_0)     
        using cfs_add[of _ _ 0] 
        apply (simp add: cfs_closed)        
  by auto  


(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Describing the Image of (UP R) in the Ring of Functions from R to R\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma to_fun_diff:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "to_fun (p \<ominus>\<^bsub>P\<^esub> q) a = to_fun p a \<ominus> to_fun q a"
  using to_fun_plus[of "\<ominus>\<^bsub>P\<^esub> q" p a]
  by (simp add: P.minus_eq R.minus_eq assms(1) assms(2) assms(3) to_fun_minus)

lemma to_fun_const:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_fun (monom P a 0) b = a"
  by (metis lcf_monom(2) P_def UP_cring.to_fun_ctrm UP_cring_axioms assms(1) assms(2) deg_const monom_closed)

lemma to_fun_monic_monom:
  assumes "b \<in> carrier R"
  shows "to_fun (monom P \<one> n) b = b[^]n"
  by (simp add: assms to_fun_monom)


text\<open>Constant polynomials map to constant polynomials\<close>

lemma const_to_constant:
  assumes "a \<in> carrier R"
  shows "to_fun (monom P a 0) = constant_function (carrier R) a"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "carrier R"])
  unfolding ring_functions_def apply(simp add: R.ring_axioms)
    apply (simp add: assms to_fun_is_Fun)
      using assms ring_functions.constant_function_closed[of R a "carrier R"]
      unfolding ring_functions_def apply (simp add: R.ring_axioms)
        using assms to_fun_const[of a ] unfolding constant_function_def 
        by auto 

text\<open>Monomial polynomials map to monomial functions\<close>

lemma monom_to_monomial:
  assumes "a \<in> carrier R"
  shows "to_fun (monom P a n) = monomial_function R a n"
  apply(rule ring_functions.function_ring_car_eqI[of R _ "carrier R"])
  unfolding ring_functions_def apply(simp add: R.ring_axioms)
    apply (simp add: assms to_fun_is_Fun)
      using assms U_function_ring.monomial_functions[of R a n] R.ring_axioms
      unfolding U_function_ring_def  
      apply auto[1]
        unfolding monomial_function_def 
        using assms to_fun_monom[of a _ n]
        by auto 
end 


(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Taylor Expansions\<close>
(**************************************************************************************************)
(**************************************************************************************************)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Monic Linear Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>The polynomial representing the variable X\<close>

definition X_poly where
"X_poly R = monom (UP R) \<one>\<^bsub>R\<^esub> 1"

context UP_cring
begin

abbreviation(input) X where
"X \<equiv> X_poly R"

lemma X_closed:
"X \<in> carrier P"
  unfolding X_poly_def 
  using P_def monom_closed by blast

lemma degree_X[simp]:
  assumes "\<one> \<noteq>\<zero>"
  shows"degree X = 1"
  unfolding X_poly_def 
  using assms P_def deg_monom[of \<one> 1]  
  by blast

lemma X_not_zero:
  assumes "\<one> \<noteq>\<zero>"
  shows"X \<noteq> \<zero>\<^bsub>P\<^esub>"
  using degree_X assms by force  

lemma sub_X[simp]:
  assumes "p \<in> carrier P"
  shows "X of p = p"
  unfolding X_poly_def
  using P_def UP_pre_univ_prop.eval_monom1 assms compose_def to_poly_UP_pre_univ_prop 
  by metis

lemma sub_monom_deg_one:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "monom P a 1 of p = a \<odot>\<^bsub>P\<^esub> p"
  using assms sub_smult[of X p a] unfolding X_poly_def
  by (metis P_def R.one_closed R.r_one X_closed X_poly_def monom_mult_smult sub_X)

lemma monom_rep_X_pow:
  assumes "a \<in> carrier R"
  shows "monom P a n = a\<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)"
proof-
  have "monom P a n = a\<odot>\<^bsub>P\<^esub>monom P \<one> n"
    by (metis R.one_closed R.r_one assms monom_mult_smult)
  then show ?thesis 
    unfolding X_poly_def 
    using monom_pow 
    by (simp add: P_def)
qed

lemma X_sub[simp]:
  assumes "p \<in> carrier P"
  shows "p of X = p"
  apply(rule poly_induct3)
  apply (simp add: assms)
  using X_closed sub_add apply presburger
  using sub_monom[of X] P_def monom_rep_X_pow X_closed by auto

text\<open>representation of monomials as scalar multiples of powers of X\<close>

lemma ltrm_rep_X_pow:
  assumes "p \<in> carrier P"
  shows "ltrm p = (lcf p)\<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(degree p))"
proof-
  have "ltrm p =  monom P (lcf p) (degree p)"
    using assms unfolding leading_term_def by (simp add: P_def)
  then show ?thesis 
    using monom_rep_X_pow P_def assms 
    by (simp add: cfs_closed)     
qed

lemma to_fun_monom':
  assumes "c \<in> carrier R"
  assumes "c \<noteq>\<zero>"
  assumes "x \<in> carrier R"
  shows "to_fun (c \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n::nat)) x = c \<otimes> x [^] n"
  using P_def to_fun_monom monom_rep_X_pow UP_cring_axioms assms(1) assms(2) assms(3) by fastforce

lemma to_fun_X_pow:
  assumes "x \<in> carrier R"
  shows "to_fun (X[^]\<^bsub>P\<^esub>(n::nat)) x = x [^] n"
  using to_fun_monom'[of \<one> x n] assms 
  by (metis P.nat_pow_closed R.l_one R.nat_pow_closed R.one_closed R.r_null R.r_one 
      UP_one_closed X_closed to_fun_to_poly ring_hom_one smult_l_null smult_one to_poly_is_ring_hom)  
end

text\<open>Monic linear polynomials\<close>

definition X_poly_plus where
"X_poly_plus R a = (X_poly R) \<oplus>\<^bsub>(UP R)\<^esub> to_polynomial R a"

definition X_poly_minus where
"X_poly_minus R a = (X_poly R) \<ominus>\<^bsub>(UP R)\<^esub> to_polynomial R a"

context UP_cring
begin

abbreviation(input) X_plus where
"X_plus \<equiv> X_poly_plus R"

abbreviation(input) X_minus where
"X_minus \<equiv> X_poly_minus R"

lemma X_plus_closed:
  assumes "a \<in> carrier R"
  shows "(X_plus a) \<in> carrier P"
  unfolding X_poly_plus_def using X_closed to_poly_closed 
  using P_def UP_a_closed assms by auto

lemma X_minus_closed:
  assumes "a \<in> carrier R"
  shows "(X_minus a) \<in> carrier P"
  unfolding X_poly_minus_def using X_closed to_poly_closed
  by (simp add: P_def UP_cring.UP_cring UP_cring_axioms assms cring.cring_simprules(4))   

lemma X_minus_plus:
  assumes "a \<in> carrier R"
  shows "(X_minus a) = X_plus (\<ominus>a)"
  using P_def UP_ring.UP_ring  UP_ring_axioms
  by (simp add: X_poly_minus_def X_poly_plus_def a_minus_def assms to_poly_a_inv)
  
lemma degree_of_X_plus:
  assumes "a \<in> carrier R"
  assumes "\<one> \<noteq>\<zero>"
  shows "degree (X_plus a) = 1"
proof-
  have 0:"degree (X_plus a) \<le> 1"
    using deg_add degree_X  P_def unfolding X_poly_plus_def 
      using UP_cring.to_poly_closed UP_cring_axioms X_closed assms(1) assms(2) by fastforce      
  have 1:"degree (X_plus a) > 0"
    by (metis One_nat_def P_def R.one_closed R.r_zero X_poly_def 
        X_closed X_poly_plus_def X_plus_closed  assms  coeff_add coeff_monom deg_aboveD  
         gr0I  lessI  n_not_Suc_n to_polynomial_def to_poly_closed)
  then show ?thesis 
    using "0" by linarith
qed

lemma degree_of_X_minus:
  assumes "a \<in> carrier R"
  assumes "\<one> \<noteq>\<zero>"
  shows "degree (X_minus a) = 1"
  using degree_of_X_plus[of "\<ominus>a"] X_minus_plus[simp] assms by auto  

lemma ltrm_of_X:
shows"ltrm X = X"
  unfolding leading_term_def
  by (metis P_def R.one_closed X_poly_def is_UP_monom_def is_UP_monomI leading_term_def)

lemma ltrm_of_X_plus:
  assumes "a \<in> carrier R"
  assumes "\<one> \<noteq>\<zero>"
  shows "ltrm (X_plus a) = X"
  unfolding X_poly_plus_def
  using X_closed  assms  ltrm_of_sum_diff_degree[of X "to_poly a"]  
    degree_to_poly[of a]  to_poly_closed[of a] degree_X ltrm_of_X 
    by (simp add: P_def)  

lemma ltrm_of_X_minus:
  assumes "a \<in> carrier R"
  assumes "\<one> \<noteq>\<zero>"
  shows "ltrm (X_minus a) = X"
  using X_minus_plus[of a]  assms 
  by (simp add: ltrm_of_X_plus)

lemma lcf_of_X_minus:
  assumes "a \<in> carrier R"
  assumes "\<one> \<noteq>\<zero>"
  shows "lcf (X_minus a) = \<one>"
  using ltrm_of_X_minus unfolding X_poly_def 
  using P_def UP_cring.X_minus_closed UP_cring.lcf_eq UP_cring_axioms assms(1) assms(2) lcf_monom 
  by (metis R.one_closed)
  
lemma lcf_of_X_plus:
  assumes "a \<in> carrier R"
  assumes "\<one> \<noteq>\<zero>"
  shows "lcf (X_plus a) = \<one>"
  using ltrm_of_X_plus unfolding X_poly_def 
  by (metis lcf_of_X_minus P_def UP_cring.lcf_eq UP_cring.X_plus_closed UP_cring_axioms X_minus_closed assms(1) assms(2) degree_of_X_minus)

lemma to_fun_X[simp]:
  assumes "a \<in> carrier R"
  shows "to_fun X a = a"
  using X_closed assms to_fun_sub_monom ltrm_is_UP_monom ltrm_of_X to_poly_closed 
  by (metis sub_X to_fun_to_poly)

lemma to_fun_X_plus[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_fun (X_plus a) b = b \<oplus> a"
  unfolding X_poly_plus_def 
  using assms to_fun_X[of b] to_fun_plus[of "to_poly a" X  b] to_fun_to_poly[of a b] 
  using P_def X_closed to_poly_closed by auto

lemma to_fun_X_minus[simp]:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_fun (X_minus a) b = b \<ominus> a"
  using to_fun_X_plus[of "\<ominus> a" b] X_minus_plus[of a] assms 
  by (simp add: R.minus_eq)

lemma cfs_X_plus:
  assumes "a \<in> carrier R"
  shows "X_plus a n = (if n = 0 then a else (if n = 1 then \<one> else \<zero>))"
  using assms cfs_add monom_closed UP_ring_axioms cfs_monom 
  unfolding X_poly_plus_def to_polynomial_def X_poly_def P_def    
  by auto 

lemma cfs_X_minus:
  assumes "a \<in> carrier R"
  shows "X_minus a n = (if n = 0 then \<ominus> a else (if n = 1 then \<one> else \<zero>))"
  using cfs_X_plus[of "\<ominus> a"] assms
  unfolding X_poly_plus_def X_poly_minus_def 
  by (simp add: P_def a_minus_def to_poly_a_inv)

text\<open>Linear substituions\<close>
 
lemma X_plus_sub_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (f of (X_plus a)) = degree f"
  apply(cases "\<one> = \<zero>")
   apply (metis P_def UP_one_closed X_plus_closed X_poly_def sub_X assms(1) assms(2) deg_one monom_one monom_zero sub_const)
  using cring_sub_deg[of "X_plus a" f] assms X_plus_closed[of a] lcf_of_X_plus[of a]  
        ltrm_of_X_plus degree_of_X_plus[of a] P_def 
  by (metis lcf_eq R.nat_pow_one R.r_one UP_cring.cring_sub_deg UP_cring_axioms X_closed X_sub 
      cfs_closed coeff_simp deg_nzero_nzero degree_X lcoeff_nonzero2 sub_const) 

lemma X_minus_sub_deg:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "degree (f of (X_minus a)) = degree f"
  using X_plus_sub_deg[of "\<ominus>a"] assms X_minus_plus[of a]
  by simp

lemma plus_minus_sub:
  assumes " a \<in> carrier R"
  shows "X_plus a of X_minus a = X"
  unfolding X_poly_plus_def
proof-
  have "(X \<oplus>\<^bsub>P\<^esub> to_poly a) of X_minus a = (X  of X_minus a) \<oplus>\<^bsub>P\<^esub> (to_poly a) of X_minus a"
    using sub_add
    by (simp add: X_closed X_minus_closed assms to_poly_closed)     
  then have "(X \<oplus>\<^bsub>P\<^esub> to_poly a) of X_minus a = (X_minus a) \<oplus>\<^bsub>P\<^esub> (to_poly a)"
    by (simp add: X_minus_closed assms sub_to_poly)
  then show "(X \<oplus>\<^bsub>UP R\<^esub> to_poly a) of X_minus a = X" 
    unfolding to_polynomial_def X_poly_minus_def
    by (metis P.add.inv_solve_right P.minus_eq P_def 
        X_closed X_poly_minus_def X_minus_closed assms monom_closed to_polynomial_def)
qed

lemma minus_plus_sub:
  assumes " a \<in> carrier R"
  shows "X_minus a of X_plus a = X"
  using plus_minus_sub[of "\<ominus>a"]
  unfolding X_poly_minus_def
  unfolding X_poly_plus_def
  using assms  apply simp
  by (metis P_def R.add.inv_closed R.minus_minus a_minus_def to_poly_a_inv)

lemma ltrm_times_X:
  assumes "p \<in> carrier P"
  shows "ltrm (X \<otimes>\<^bsub>P\<^esub> p) = X \<otimes>\<^bsub>P\<^esub> (ltrm p)"
  using assms ltrm_of_X cring_ltrm_mult[of X p]
  by (metis ltrm_deg_0 P.r_null R.l_one R.one_closed UP_cring.lcf_monom(1)
      UP_cring_axioms X_closed X_poly_def cfs_closed deg_zero deg_ltrm monom_zero)

lemma times_X_not_zero:
  assumes "p \<in> carrier P"
  assumes "p \<noteq> \<zero>\<^bsub>P\<^esub>"
  shows "(X \<otimes>\<^bsub>P\<^esub> p) \<noteq> \<zero>\<^bsub>P\<^esub>"
  by (metis (no_types, hide_lams) lcf_monom(1) lcf_of_X_minus ltrm_of_X_minus P.inv_unique
      P.r_null R.l_one R.one_closed UP_zero_closed X_closed zcf_def 
      zcf_zero_degree_zero assms(1) assms(2) cfs_closed cfs_zero cring_lcf_mult 
      deg_monom deg_nzero_nzero deg_ltrm degree_X degree_of_X_minus 
      monom_one monom_zero)

lemma degree_times_X:
  assumes "p \<in> carrier P"
  assumes "p \<noteq> \<zero>\<^bsub>P\<^esub>"
  shows "degree (X \<otimes>\<^bsub>P\<^esub> p) = degree p + 1"
  using cring_deg_mult[of X p] assms times_X_not_zero[of p]
  by (metis (no_types, lifting) P.r_null P.r_one P_def R.l_one R.one_closed
      UP_cring.lcf_monom(1) UP_cring_axioms UP_zero_closed X_closed X_poly_def cfs_closed 
      deg_zero deg_ltrm degree_X monom_one monom_zero to_poly_inverse)
   
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Basic Facts About Taylor Expansions\<close>
(**************************************************************************************************)
(**************************************************************************************************)
definition taylor_expansion where
"taylor_expansion R a p = compose R p (X_poly_plus R a)"

definition(in UP_cring) taylor  where
"taylor \<equiv> taylor_expansion R"

context UP_cring
begin

lemma taylor_expansion_ring_hom:
  assumes "c \<in> carrier R"
  shows "taylor_expansion R c \<in> ring_hom P P"
  unfolding taylor_expansion_def 
  using rev_sub_is_hom[of "X_plus c"]
  unfolding rev_compose_def compose_def 
  using X_plus_closed assms by auto 

notation  taylor ("T\<^bsub>_\<^esub>")

lemma(in UP_cring) taylor_closed:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "T\<^bsub>a\<^esub> f \<in>  carrier P"
  unfolding taylor_def
  by (simp add: X_plus_closed assms(1) assms(2) sub_closed taylor_expansion_def)

lemma taylor_deg:
  assumes "a \<in> carrier R"
  assumes "p \<in> carrier P"
  shows "degree (T\<^bsub>a\<^esub> p) = degree p"
  unfolding taylor_def taylor_expansion_def 
  using X_plus_sub_deg[of a p] assms 
  by (simp add: taylor_expansion_def)

lemma taylor_id:
  assumes "a \<in> carrier R"
  assumes "p \<in> carrier P"
  shows "p = (T\<^bsub>a\<^esub> p) of (X_minus a)"
  unfolding taylor_expansion_def taylor_def
  using assms sub_assoc[of p "X_plus a" "X_minus a"] X_plus_closed[of a]  X_minus_closed[of a]
  by (metis X_sub plus_minus_sub taylor_expansion_def)

lemma taylor_eval:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  shows "to_fun (T\<^bsub>a\<^esub> f) b = to_fun f (b \<oplus> a)"
  unfolding  taylor_expansion_def taylor_def
  using to_fun_sub[of "(X_plus a)" f b] to_fun_X_plus[of a b] 
        assms X_plus_closed[of a] by auto

lemma taylor_eval':
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  shows "to_fun f (b) = to_fun (T\<^bsub>a\<^esub> f) (b \<ominus> a) "
  unfolding taylor_expansion_def taylor_def
  using to_fun_sub[of "(X_minus a)" "T\<^bsub>a\<^esub> f" b] to_fun_X_minus[of b a] 
        assms X_minus_closed[of a] 
  by (metis taylor_closed taylor_def taylor_id taylor_expansion_def to_fun_X_minus)

lemma(in UP_cring) degree_monom:
  assumes "a \<in> carrier R"
  shows "degree (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub>n) = (if a = \<zero> then 0 else n)"
  apply(cases "a = \<zero>")
  apply (metis (full_types) P.nat_pow_closed P_def R.one_closed UP_smult_zero X_poly_def deg_zero monom_closed)
  using P_def UP_cring.monom_rep_X_pow UP_cring_axioms assms deg_monom by fastforce  

lemma(in UP_cring) poly_comp_finsum:
  assumes "\<And>i::nat. i \<le> n \<Longrightarrow> g i \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "p = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..n}. g i)"
  shows "p of q = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..n}. (g i) of q)"  
proof- 
  have 0: "p of q  = rev_sub q p"
    unfolding compose_def rev_compose_def by blast 
  have 1: "p of q = finsum P (rev_compose R q \<circ> g) {..n}" 
    unfolding 0 unfolding assms 
    apply(rule ring_hom_finsum[of "rev_compose R q" P "{..n}" g ])
    using assms(2) rev_sub_is_hom apply blast
    apply (simp add: UP_ring)
     apply simp
  by (simp add: assms(1))
  show ?thesis unfolding 1 
    unfolding comp_apply rev_compose_def compose_def
    by auto 
qed

lemma(in UP_cring) poly_comp_expansion:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "degree p \<le> n"
  shows "p of q = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..n}. (p i) \<odot>\<^bsub>P\<^esub> q[^]\<^bsub>P\<^esub>i)"
proof-
  obtain g where g_def: "g = (\<lambda>i. monom P (p i) i)"
    by blast 
  have 0: "\<And>i. (g i) of q = (p i) \<odot>\<^bsub>P\<^esub> q[^]\<^bsub>P\<^esub>i"
  proof- fix i show "g i of q = p i \<odot>\<^bsub>P\<^esub> q [^]\<^bsub>P\<^esub> i"
      using assms g_def  P_def coeff_simp monom_sub 
      by (simp add: cfs_closed)           
  qed
  have 1: "(\<And>i. i \<le> n \<Longrightarrow> g i \<in> carrier P)"
    using g_def assms 
    by (simp add: cfs_closed)   
  have  "(\<Oplus>\<^bsub>P\<^esub>i\<in>{..n}. monom P (p i) i) = p"
    using assms up_repr_le[of p n] coeff_simp[of p] unfolding P_def 
    by auto     
  then have  "p = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..n}. g i)"
    using g_def by auto       
  then have "p of q = (\<Oplus>\<^bsub>P\<^esub>i\<in>{..n}. g i of q)" 
    using 0 1 poly_comp_finsum[of n g q p]
    using assms(2) 
    by blast
  then show ?thesis 
    by(simp add: 0)
qed

lemma(in UP_cring) taylor_sum:
  assumes "p \<in> carrier P"
  assumes "degree p \<le> n"
  assumes "a \<in> carrier R"
  shows "p = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..n}. T\<^bsub>a\<^esub> p i \<odot>\<^bsub>P\<^esub> (X_minus a)[^]\<^bsub>P\<^esub>i)"
proof-
  have 0: "(T\<^bsub>a\<^esub> p) of X_minus a = p" 
    using P_def taylor_id assms(1) assms(3) 
    by fastforce
  have 1: "degree (T\<^bsub>a\<^esub> p) \<le> n"
    using assms 
    by (simp add: taylor_deg)
  have 2: "T\<^bsub>a\<^esub> p of X_minus a = (\<Oplus>\<^bsub>P\<^esub>i\<in>{..n}. T\<^bsub>a\<^esub> p i \<odot>\<^bsub>P\<^esub> X_minus a [^]\<^bsub>P\<^esub> i)"
    using 1 X_minus_closed[of a]  poly_comp_expansion[of "T\<^bsub>a\<^esub> p" "X_minus a" n] 
          assms  taylor_closed 
    by blast
  then show ?thesis
    using 0 
    by simp
qed

text\<open>The $i^{th}$ term in the taylor expansion\<close>
definition taylor_term where
"taylor_term c p i = (taylor_expansion R c p i) \<odot>\<^bsub>UP R\<^esub> (UP_cring.X_minus R c) [^]\<^bsub>UP R\<^esub>i" 

lemma (in UP_cring) taylor_term_closed:
assumes "p \<in> carrier P"
assumes "a \<in> carrier R"
shows "taylor_term a p i \<in> carrier (UP R)"
 unfolding taylor_term_def 
  using P.nat_pow_closed P_def taylor_closed taylor_def X_minus_closed assms(1) assms(2) smult_closed 
  by (simp add: cfs_closed)

lemma(in UP_cring) taylor_term_sum:
  assumes "p \<in> carrier P"
  assumes "degree p \<le> n"
  assumes "a \<in> carrier R"
  shows "p = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..n}. taylor_term a p i)"
  unfolding taylor_term_def taylor_def
  using assms taylor_sum[of p n a] P_def 
  using taylor_def by auto
  
lemma (in UP_cring) taylor_expansion_add:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "c \<in> carrier R"
  shows "taylor_expansion R c (p \<oplus>\<^bsub>UP R\<^esub> q) = (taylor_expansion R c p) \<oplus>\<^bsub>UP R\<^esub> (taylor_expansion R c q)"
  unfolding taylor_expansion_def 
  using assms X_plus_closed[of c] P_def sub_add 
  by blast

lemma (in UP_cring) taylor_term_add:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "taylor_term a (p \<oplus>\<^bsub>UP R\<^esub>q) i = taylor_term a p i \<oplus>\<^bsub>UP R\<^esub> taylor_term a q i"
  using assms   taylor_expansion_add[of p q a]  
  unfolding taylor_term_def 
  using P.nat_pow_closed P_def taylor_closed X_minus_closed cfs_add smult_l_distr 
  by (simp add: taylor_def cfs_closed)
  
lemma (in UP_cring) to_fun_taylor_term:
assumes "p \<in> carrier P"
assumes "a \<in> carrier R"
assumes "c \<in> carrier R"
shows "to_fun (taylor_term c p i) a = (T\<^bsub>c\<^esub> p i) \<otimes> (a \<ominus> c)[^]i"
  using assms to_fun_smult[of "X_minus c [^]\<^bsub>UP R\<^esub> i" a "taylor_expansion R c p i"] 
              to_fun_X_minus[of c a] to_fun_nat_pow[of "X_minus c" a i]  
  unfolding taylor_term_def 
  using P.nat_pow_closed P_def taylor_closed taylor_def X_minus_closed 
  by (simp add: cfs_closed)    


end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Defining the (Scalar-Valued) Derivative of a Polynomial Using the Taylor Expansion\<close>
(**************************************************************************************************)
(**************************************************************************************************)
definition derivative where
"derivative R f a = (taylor_expansion R a f) 1"

context UP_cring
begin 

abbreviation(in UP_cring) deriv where
"deriv \<equiv> derivative R"

lemma(in UP_cring) deriv_closed:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(derivative R f a) \<in> carrier R"
  unfolding derivative_def  
  using taylor_closed taylor_def assms(1) assms(2) cfs_closed by auto

lemma(in UP_cring) deriv_add:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "deriv (f \<oplus>\<^bsub>P\<^esub> g) a = deriv f a \<oplus> deriv g a"
  unfolding derivative_def taylor_expansion_def  using assms 
  by (simp add: X_plus_closed sub_add sub_closed)

end 
(**************************************************************************************************)
(**************************************************************************************************)
section\<open>The Polynomial-Valued Derivative Operator\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context UP_cring
begin

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Operator Which Shifts Coefficients\<close>
  (**********************************************************************)
  (**********************************************************************)
lemma cfs_times_X:
  assumes "g \<in> carrier P"
  shows "(X \<otimes>\<^bsub>P\<^esub> g) (Suc n) = g n"
  apply(rule poly_induct3[of g])
  apply (simp add: assms)
  apply (metis (no_types, lifting) P.m_closed P.r_distr X_closed cfs_add)
  by (metis (no_types, lifting) P_def R.l_one R.one_closed R.r_null Suc_eq_plus1 X_poly_def
      cfs_monom coeff_monom_mult coeff_simp monom_closed monom_mult)

lemma times_X_pow_coeff:
  assumes "g \<in> carrier P"
  shows "(monom P \<one> k \<otimes>\<^bsub>P\<^esub> g) (n + k) = g n"
  using coeff_monom_mult P.m_closed P_def assms coeff_simp monom_closed 
  by (simp add: cfs_closed)

lemma zcf_eq_zero_unique:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P \<and> (f = X \<otimes>\<^bsub>P\<^esub> g)"
  shows "\<And> h. h  \<in> carrier P \<and> (f = X \<otimes>\<^bsub>P\<^esub> h) \<Longrightarrow> h = g"
proof-
  fix h
  assume A: "h  \<in> carrier P \<and> (f = X \<otimes>\<^bsub>P\<^esub> h)"
  then have 0: " X \<otimes>\<^bsub>P\<^esub> g =  X \<otimes>\<^bsub>P\<^esub> h"
    using assms(2) by auto
 show "h = g"
   using 0 A assms 
   by (metis P_def coeff_simp  cfs_times_X up_eqI)
qed

lemma f_minus_ctrm:
  assumes "f \<in> carrier P"
  shows "zcf(f \<ominus>\<^bsub>P\<^esub> ctrm f) = \<zero>"
  using assms 
  by (smt ctrm_is_poly P.add.inv_closed P.minus_closed P_def R.r_neg R.zero_closed zcf_to_fun 
        to_fun_minus to_fun_plus UP_cring_axioms zcf_ctrm zcf_def a_minus_def cfs_closed)

definition poly_shift where
"poly_shift f n = f (Suc n)"
   
lemma poly_shift_closed:
  assumes "f \<in> carrier P"
  shows "poly_shift f \<in> carrier P"
  apply(rule UP_car_memI[of "deg R f"])
  unfolding poly_shift_def 
proof -
  fix n :: nat
  assume "deg R f < n"
  then have "deg R f < Suc n"
    using Suc_lessD by blast
  then have "f (Suc n) = \<zero>\<^bsub>P\<^esub> (Suc n)"
    by (metis P.l_zero UP_zero_closed assms coeff_of_sum_diff_degree0)
  then show "f (Suc n) = \<zero>"
    by simp
next
  show " \<And>n. f (Suc n) \<in> carrier R"
    by(rule cfs_closed, rule assms)
qed

lemma poly_shift_eq_0:
  assumes "f \<in> carrier P"
  shows "f  n = (ctrm f \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> poly_shift f) n"
  apply(cases "n = 0")
  apply (smt ctrm_degree ctrm_is_poly ltrm_of_X One_nat_def P.r_null P.r_zero P_def UP_cring.lcf_monom(1) UP_cring_axioms UP_mult_closed UP_r_one UP_zero_closed X_closed zcf_ltrm_mult zcf_def zcf_zero assms cfs_add cfs_closed deg_zero degree_X lessI monom_one poly_shift_closed to_poly_inverse)
proof- assume A: "n \<noteq> 0"
  then obtain k where k_def: " n = Suc k"
    by (meson lessI less_Suc_eq_0_disj)
  show ?thesis 
    using  cfs_times_X[of "poly_shift f" k] poly_shift_def[of f k] poly_shift_closed assms
        cfs_add[of "ctrm f" "X \<otimes>\<^bsub>P\<^esub> poly_shift f" n] unfolding k_def 
    by (simp add: X_closed cfs_closed cfs_monom)
qed   
        
lemma poly_shift_eq:
  assumes "f \<in> carrier P"
  shows "f = (ctrm f \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> poly_shift f)"
by(rule ext, rule poly_shift_eq_0, rule assms)

lemma poly_shift_id:
  assumes "f \<in> carrier P"
  shows "f \<ominus>\<^bsub>P\<^esub> ctrm f = X \<otimes>\<^bsub>P\<^esub> poly_shift f"
  using assms poly_shift_eq[of f] poly_shift_closed unfolding a_minus_def 
  by (metis ctrm_is_poly P.add.inv_solve_left P.m_closed UP_a_comm UP_a_inv_closed X_closed)

lemma poly_shift_degree_zero:
  assumes "p \<in> carrier P"
  assumes "degree p = 0"
  shows "poly_shift p = \<zero>\<^bsub>P\<^esub>"
  by (metis ltrm_deg_0 P.r_neg P.r_null UP_ring UP_zero_closed X_closed zcf_eq_zero_unique 
      abelian_group.minus_eq assms(1) assms(2) poly_shift_closed poly_shift_id ring_def)

lemma poly_shift_degree:
  assumes "p \<in> carrier P"
  assumes "degree p > 0"
  shows "degree (poly_shift p) = degree p - 1 "
  using poly_shift_id[of p] 
  by (metis ctrm_degree ctrm_is_poly P.r_null X_closed add_diff_cancel_right' assms(1) assms(2) 
      deg_zero degree_of_difference_diff_degree degree_times_X nat_less_le poly_shift_closed)
  
lemma poly_shift_monom:
  assumes "a \<in> carrier R"
  shows "poly_shift (monom P a (Suc k)) = (monom P a k)"
proof-
  have "(monom P a (Suc k)) = ctrm (monom P a (Suc k)) \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    using poly_shift_eq[of "monom P a (Suc k)"] assms monom_closed 
    by blast
  then have "(monom P a (Suc k)) = \<zero>\<^bsub>P\<^esub> \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    using assms by simp
  then have "(monom P a (Suc k)) = X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    using X_closed assms poly_shift_closed by auto  
  then have "X \<otimes>\<^bsub>P\<^esub>(monom P a k) = X \<otimes>\<^bsub>P\<^esub>poly_shift (monom P a (Suc k))"
    by (metis P_def R.l_one R.one_closed X_poly_def assms monom_mult plus_1_eq_Suc)
  then show ?thesis 
    using X_closed X_not_zero assms 
    by (meson UP_mult_closed zcf_eq_zero_unique monom_closed poly_shift_closed)        
qed

lemma(in UP_cring) poly_shift_add:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows "poly_shift (f \<oplus>\<^bsub>P\<^esub> g) = (poly_shift f) \<oplus>\<^bsub>P\<^esub> (poly_shift g)"
  apply(rule ext)
  using cfs_add[of "poly_shift f" "poly_shift g"] poly_shift_closed poly_shift_def 
  by (simp add: poly_shift_def assms(1) assms(2))

lemma(in UP_cring) poly_shift_s_mult:
  assumes "f \<in> carrier P"
  assumes "s \<in> carrier R"
  shows "poly_shift (s \<odot>\<^bsub>P\<^esub>f) = s \<odot>\<^bsub>P\<^esub> (poly_shift f)"
proof-
  have "(s \<odot>\<^bsub>P\<^esub>f) = (ctrm (s \<odot>\<^bsub>P\<^esub>f)) \<oplus>\<^bsub>P\<^esub>(X \<otimes>\<^bsub>P\<^esub> poly_shift (s \<odot>\<^bsub>P\<^esub>f))"
    using poly_shift_eq[of "(s \<odot>\<^bsub>P\<^esub>f)"] assms(1) assms(2) 
    by blast
  then have 0: "(s \<odot>\<^bsub>P\<^esub>f) = (s \<odot>\<^bsub>P\<^esub>(ctrm f)) \<oplus>\<^bsub>P\<^esub>(X \<otimes>\<^bsub>P\<^esub> poly_shift (s \<odot>\<^bsub>P\<^esub>f))"
    using ctrm_smult assms(1) assms(2) by auto   
  have 1: "(s \<odot>\<^bsub>P\<^esub>f) = s \<odot>\<^bsub>P\<^esub> ((ctrm f) \<oplus>\<^bsub>P\<^esub>  (X \<otimes>\<^bsub>P\<^esub> (poly_shift f)))"
    using assms(1) poly_shift_eq by auto
  have 2:  "(s \<odot>\<^bsub>P\<^esub>f) = (s \<odot>\<^bsub>P\<^esub>(ctrm f)) \<oplus>\<^bsub>P\<^esub>  (s \<odot>\<^bsub>P\<^esub>(X \<otimes>\<^bsub>P\<^esub> (poly_shift f)))"
    by (simp add: "1" X_closed assms(1) assms(2) ctrm_is_poly poly_shift_closed smult_r_distr)    
  have 3:  "(s \<odot>\<^bsub>P\<^esub>f) = (s \<odot>\<^bsub>P\<^esub>(ctrm f)) \<oplus>\<^bsub>P\<^esub>  (X \<otimes>\<^bsub>P\<^esub> (s \<odot>\<^bsub>P\<^esub>(poly_shift f)))"
    using "2" UP_m_comm X_closed assms(1) assms(2) smult_assoc2
    by (simp add: poly_shift_closed)    
  have 4: "(X \<otimes>\<^bsub>P\<^esub> poly_shift (s \<odot>\<^bsub>P\<^esub>f)) =  (X \<otimes>\<^bsub>P\<^esub> (s \<odot>\<^bsub>P\<^esub>(poly_shift f)))"
    using 3 0  X_closed assms(1) assms(2) ctrm_is_poly poly_shift_closed 
    by auto     
  then show ?thesis 
    using X_closed X_not_zero assms(1) assms(2) 
    by (metis UP_mult_closed UP_smult_closed zcf_eq_zero_unique poly_shift_closed)  
qed

lemma zcf_poly_shift:
  assumes "f \<in>  carrier P"
  shows "zcf (poly_shift f) = f 1"  
  apply(rule poly_induct3)
  apply (simp add: assms)
  using poly_shift_add zcf_add cfs_add poly_shift_closed apply metis 
  unfolding zcf_def using poly_shift_monom poly_shift_degree_zero
  by (simp add: poly_shift_def)

fun poly_shift_iter ("shift") where
Base:"poly_shift_iter 0 f = f"|
Step:"poly_shift_iter (Suc n) f = poly_shift (poly_shift_iter n f)"

lemma shift_closed:
  assumes "f \<in> carrier P"
  shows "shift n f \<in> carrier P"
  apply(induction n)
  using assms poly_shift_closed by auto 

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Operator Which Multiplies Coefficients by Their Degree\<close>
  (**********************************************************************)
  (**********************************************************************)

definition n_mult where 
"n_mult f = (\<lambda>n. [n]\<cdot>\<^bsub>R\<^esub>(f n))"

lemma(in UP_cring) n_mult_closed:
  assumes "f \<in> carrier P"
  shows "n_mult f \<in> carrier P"
  apply(rule UP_car_memI[of "deg R f"])
  unfolding n_mult_def 
  apply (metis P.l_zero R.add.nat_pow_one UP_zero_closed assms cfs_zero coeff_of_sum_diff_degree0)
  using assms cfs_closed by auto 

text\<open>Facts about the shift function\<close>

lemma shift_one:
"shift (Suc 0) = poly_shift"
  by auto 

lemma shift_factor0:
  assumes "f \<in> carrier P"
  shows "degree f \<ge> (Suc k) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k)))) < (Suc k)"
proof(induction k)
  case 0
  have 0: " f \<ominus>\<^bsub>P\<^esub> (ctrm f) =  (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X"
    by (metis UP_m_comm X_closed assms poly_shift_id shift_closed shift_one)         
  then have  " f \<ominus>\<^bsub>P\<^esub>(shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X =    (ctrm f) "
  proof-
    have " f \<ominus>\<^bsub>P\<^esub> (ctrm f) \<ominus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X=  (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X \<ominus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X"
      using 0   by simp
    then have " f \<ominus>\<^bsub>P\<^esub> (ctrm f) \<ominus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X = \<zero>\<^bsub>P\<^esub>"
      using UP_cring.UP_cring[of R] assms 
      by (metis "0" P.ring_simprules(4) P_def UP_ring.UP_ring UP_ring_axioms 
          a_minus_def abelian_group.r_neg ctrm_is_poly ring_def)
    then have " f \<ominus>\<^bsub>P\<^esub> ((ctrm f) \<oplus>\<^bsub>P\<^esub> (shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X) = \<zero>\<^bsub>P\<^esub>"
      using assms P.ring_simprules  
      by (metis "0" poly_shift_id poly_shift_eq)
    then have " f \<ominus>\<^bsub>P\<^esub> ((shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X \<oplus>\<^bsub>P\<^esub> (ctrm f) ) = \<zero>\<^bsub>P\<^esub>"
      using P.m_closed UP_a_comm X_closed assms ctrm_is_poly shift_closed 
      by presburger      
    then have "f \<ominus>\<^bsub>P\<^esub> ((shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>X) \<ominus>\<^bsub>P\<^esub> (ctrm f)= \<zero>\<^bsub>P\<^esub>"
      using P.add.m_assoc P.ring_simprules(14) P.ring_simprules(19) assms "0" 
          P.add.inv_closed P.r_neg P.r_zero ctrm_is_poly
      by smt      
    then show ?thesis 
      by (metis "0" P.add.m_comm P.m_closed P.ring_simprules(14) P.ring_simprules(18) 
          P.ring_simprules(3) X_closed assms ctrm_is_poly poly_shift_id poly_shift_eq 
          shift_closed)
  qed
  then have  " f \<ominus>\<^bsub>P\<^esub>(shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc 0)) =    (ctrm f) "
  proof-
    have "X = X[^]\<^bsub>P\<^esub>(Suc 0)"
      by (simp add: X_closed)
    then show ?thesis 
      using 0 \<open>f \<ominus>\<^bsub>P\<^esub> shift (Suc 0) f \<otimes>\<^bsub>P\<^esub> X = ctrm f\<close> 
      by auto   
  qed
  then have " degree (f \<ominus>\<^bsub>P\<^esub>(shift (Suc 0) f)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc 0))) < 1"
    using ctrm_degree[of f] assms   by simp
  then show ?case 
    by blast
next
  case (Suc n)
  fix k
  assume IH: "degree f \<ge> (Suc k) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc k) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc k)))) < (Suc k)"
  show  "degree f \<ge> (Suc (Suc k)) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc (Suc k)) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc (Suc k))))) < (Suc (Suc k))"
  proof-
    obtain n where n_def: "n = Suc k"
      by simp
    have IH': "degree f \<ge> n \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift n f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))) < n"
      using n_def IH by auto 
    have P: "degree f \<ge> (Suc n) \<Longrightarrow> degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc n) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc n)))) < (Suc n)"
    proof-
      obtain g where g_def: "g = (f \<ominus>\<^bsub>P\<^esub> ((shift n f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)))"
        by simp
      obtain s where s_def: "s = shift n f"
        by simp
      obtain s' where s'_def: "s' = shift (Suc n) f"
        by simp
      have P: "g \<in> carrier P" "s \<in> carrier P" "s' \<in> carrier P" "(X[^]\<^bsub>P\<^esub>n) \<in> carrier P"
        using s_def s'_def g_def assms shift_closed[of f n]  
        apply (simp add: X_closed)
        apply (simp add: \<open>f \<in> carrier P \<Longrightarrow> shift n f \<in> carrier P\<close> assms s_def)
        using P_def UP_cring.shift_closed UP_cring_axioms assms s'_def apply blast
        using X_closed by blast
      have g_def': "g = (f \<ominus>\<^bsub>P\<^esub> (s \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)))"
        using g_def s_def by auto 
      assume "degree f \<ge> (Suc n)"
      then have " degree (f \<ominus>\<^bsub>P\<^esub> (s \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))) < n" 
        using IH' Suc_leD s_def by blast
      then have d_g: "degree g < n" using g_def' by auto 
      have P0: "f \<ominus>\<^bsub>P\<^esub> (s' \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc n))) = ((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g"
      proof-
        have "s = (ctrm s) \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> s')"
          using s_def s'_def  P_def poly_shift_eq UP_cring_axioms assms shift_closed 
          by (simp add: UP_cring.poly_shift_eq)
        then have 0: "g = f \<ominus>\<^bsub>P\<^esub> ((ctrm s) \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> s')) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)"
          using g_def'  by auto
        then have "g = f \<ominus>\<^bsub>P\<^esub> ((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<ominus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          using P cring X_closed  P.l_distr P.ring_simprules(19) UP_a_assoc a_minus_def assms
          by (simp add: a_minus_def ctrm_is_poly)
        then have "g \<oplus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> ((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          using P cring X_closed  P.l_distr P.ring_simprules UP_a_assoc a_minus_def assms
          by (simp add: P.r_neg2 ctrm_is_poly)                                                   
        then have " ((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> (g \<oplus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)))"
          using P cring X_closed P.ring_simprules UP_a_assoc a_minus_def assms
          by (simp add: P.ring_simprules(17) ctrm_is_poly)           
        then have " ((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> (((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g)"
          by (simp add: P(1) P(3) UP_a_comm X_closed)          
        then have "((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) =  f \<ominus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<ominus>\<^bsub>P\<^esub> g"
          using P(1) P(3) P.ring_simprules(19) UP_a_assoc a_minus_def assms
          by (simp add: a_minus_def X_closed) 
        then have "((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g=  f \<ominus>\<^bsub>P\<^esub> ((X \<otimes>\<^bsub>P\<^esub> s') \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          by (metis P(1) P(3) P(4) P.add.inv_solve_right P.m_closed P.ring_simprules(14)
              P.ring_simprules(4) P_def UP_cring.X_closed UP_cring_axioms assms)
        then have "((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g=  f \<ominus>\<^bsub>P\<^esub> ((s' \<otimes>\<^bsub>P\<^esub> X) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))"
          by (simp add: P(3) UP_m_comm X_closed)         
        then have "((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g=  f \<ominus>\<^bsub>P\<^esub> (s' \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc n)))"
          using P(3) P.nat_pow_Suc2 UP_m_assoc X_closed by auto
        then show ?thesis
          by auto 
      qed
      have P1: "degree (((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<oplus>\<^bsub>P\<^esub> g) \<le> n"
      proof-
        have Q0: "degree ((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n))  \<le> n"
        proof(cases "ctrm s = \<zero>\<^bsub>P\<^esub>")
          case True
          then show ?thesis 
            by (simp add: P(4))
        next
          case False
          then have F0: "degree ((ctrm s)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)) \<le> degree (ctrm s) + degree (X[^]\<^bsub>P\<^esub>n) "
            by (meson ctrm_is_poly P(2) P(4) deg_mult_ring)             
          have F1: "\<one>\<noteq>\<zero>\<Longrightarrow> degree (X[^]\<^bsub>P\<^esub>n) = n"
            unfolding X_poly_def 
            using P_def cring_monom_degree by auto
          show ?thesis 
            by (metis (no_types, hide_lams) F0 F1 ltrm_deg_0 P(2) P.r_null P_def R.l_null R.l_one 
                R.nat_pow_closed R.zero_closed X_poly_def assms cfs_closed 
                add_0 deg_const deg_zero deg_ltrm 
                monom_pow monom_zero zero_le)                                    
        qed
        then show ?thesis 
          using d_g
          by (simp add: P(1) P(2) P(4) bound_deg_sum ctrm_is_poly) 
      qed
      then show ?thesis 
        using s'_def P0 by auto
    qed
    assume "degree f \<ge> (Suc (Suc k)) "
    then show "degree (f \<ominus>\<^bsub>P\<^esub> ((shift (Suc (Suc k)) f) \<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc (Suc k))))) < (Suc (Suc k))"
      using P by(simp add: n_def)
  qed
qed

lemma(in UP_cring) shift_degree0:
  assumes "f \<in> carrier P"
  shows "degree f >n \<Longrightarrow> Suc (degree (shift (Suc n) f)) = degree (shift n f)"
proof(induction n) 
  case 0
  assume B: "0< degree f"
  have 0: "degree (shift 0 f) = degree f"
    by simp
  have 1: "degree f = degree (f \<ominus>\<^bsub>P\<^esub> (ctrm f))"
    using assms(1) B ctrm_degree degree_of_difference_diff_degree
    by (simp add: ctrm_is_poly)   
  have "(f \<ominus>\<^bsub>P\<^esub> (ctrm f)) = X \<otimes>\<^bsub>P\<^esub>(shift 1 f)"
    using P_def poly_shift_id UP_cring_axioms assms(1) by auto
  then have "degree (f \<ominus>\<^bsub>P\<^esub> (ctrm f)) = 1 + (degree (shift 1 f))"
    by (metis "1" B P.r_null X_closed add.commute assms deg_nzero_nzero degree_times_X not_gr_zero shift_closed)        
  then have  "degree (shift 0 f) = 1 + (degree (shift 1 f))"
    using 0 1 by auto 
  then show ?case 
    by simp
next
  case (Suc n)
  fix n 
  assume IH: "(n < degree f \<Longrightarrow> Suc (degree (shift (Suc n) f)) = degree (shift n f))"
  show "Suc n < degree f \<Longrightarrow> Suc (degree (shift (Suc (Suc n)) f)) = degree (shift (Suc n) f)"
  proof-
    assume A: " Suc n < degree f"
    then have 0: "(shift (Suc n) f) = ctrm ((shift (Suc n) f)) \<oplus>\<^bsub>P\<^esub>  (shift (Suc (Suc n)) f)\<otimes>\<^bsub>P\<^esub>X"
      by (metis UP_m_comm X_closed assms local.Step poly_shift_eq shift_closed)                
    have N: "(shift (Suc (Suc n)) f) \<noteq> \<zero>\<^bsub>P\<^esub>"
    proof
      assume C: "shift (Suc (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
      obtain g where g_def: "g = f \<ominus>\<^bsub>P\<^esub>  (shift (Suc (Suc n)) f)\<otimes>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>(Suc (Suc n)))"
        by simp
      have C0: "degree g < degree f"
        using g_def assms A 
        by (meson Suc_leI Suc_less_SucD Suc_mono less_trans_Suc shift_factor0)
      have C1: "g = f" 
        using C
        by (simp add: P.minus_eq X_closed assms g_def)          
      then show False 
        using C0 by auto 
    qed
    have 1: "degree (shift (Suc n) f) = degree ((shift (Suc n) f) \<ominus>\<^bsub>P\<^esub> ctrm ((shift (Suc n) f)))"
    proof(cases "degree (shift (Suc n) f) = 0")
      case True
      then show ?thesis 
        using N assms poly_shift_degree_zero poly_shift_closed shift_closed by auto        
    next
      case False
      then have "degree (shift (Suc n) f) > degree  (ctrm ((shift (Suc n) f)))"
      proof -
        have "shift (Suc n) f \<in> carrier P"
          using assms shift_closed by blast
        then show ?thesis
          using False ctrm_degree by auto
      qed        
      then show ?thesis
      proof -
        show ?thesis
          using \<open>degree (ctrm (shift (Suc n) f)) < degree (shift (Suc n) f)\<close> 
            assms ctrm_is_poly degree_of_difference_diff_degree shift_closed by presburger
      qed         
    qed
    have 2: "(shift (Suc n) f) \<ominus>\<^bsub>P\<^esub> ctrm ((shift (Suc n) f)) =  (shift (Suc (Suc n)) f)\<otimes>\<^bsub>P\<^esub>X"
      using 0
      by (metis Cring_Poly.INTEG.Step P.m_comm X_closed assms poly_shift_id shift_closed)                                   
    have 3: "degree ((shift (Suc n) f) \<ominus>\<^bsub>P\<^esub> ctrm ((shift (Suc n) f))) =  degree (shift (Suc (Suc n)) f) + 1"
      using 2 N X_closed X_not_zero assms  degree_X shift_closed 
      by (metis UP_m_comm degree_times_X)
    then show ?thesis using 1
      by linarith
  qed
qed

lemma(in UP_cring) shift_degree:
  assumes "f \<in> carrier P"
  shows "degree f \<ge> n \<Longrightarrow>  degree (shift n f) + n = degree f"
proof(induction n)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  fix n
  assume IH: "(n \<le> degree f \<Longrightarrow> degree (shift n f) + n = degree f)"
  show "Suc n \<le> degree f \<Longrightarrow> degree (shift (Suc n) f) + Suc n = degree f"
  proof-
    assume A: "Suc n \<le> degree f "
    have 0: "degree (shift n f) + n = degree f" 
      using IH A by auto  
    have 1: "degree (shift n f) = Suc (degree (shift (Suc n) f))"
      using A assms shift_degree0 by auto 
    show "degree (shift (Suc n) f) + Suc n = degree f" 
      using 0 1  by simp
  qed
qed

lemma(in UP_cring) shift_degree':
  assumes "f \<in> carrier P"
  shows "degree (shift (degree f) f) = 0"
  using shift_degree assms 
  by fastforce

lemma(in UP_cring) shift_above_degree:
  assumes "f \<in> carrier P"
  assumes "k > degree f"
  shows "(shift k f) = \<zero>\<^bsub>P\<^esub>"
proof-
  have "\<And>n. shift ((degree f)+ (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
  proof-
    fix n
    show "shift ((degree f)+ (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
    proof(induction n)
      case 0
      have B0:"shift (degree f) f  = ctrm(shift (degree f) f) \<oplus>\<^bsub>P\<^esub> (shift (degree f + Suc 0) f)\<otimes>\<^bsub>P\<^esub>X"
      proof -
        have f1: "\<forall>f n. f \<notin> carrier P \<or> shift n f \<in> carrier P"
          by (meson shift_closed)
        then have "shift (degree f + Suc 0) f \<in> carrier P"
          using assms(1) by blast
        then show ?thesis
          using f1 by (simp add: P.m_comm X_closed assms(1) poly_shift_eq)
      qed        
      have B1:"shift (degree f) f = ctrm(shift (degree f) f)"
      proof -
        have "shift (degree f) f \<in> carrier P"
          using assms(1) shift_closed by blast
        then show ?thesis
          using ltrm_deg_0 assms(1) shift_degree' by auto          
      qed        
      have B2: "(shift (degree f + Suc 0) f)\<otimes>\<^bsub>P\<^esub>X = \<zero>\<^bsub>P\<^esub>"
        using B0 B1 X_closed assms(1)
      proof -
        have "\<forall>f n. f \<notin> carrier P \<or> shift n f \<in> carrier P"
          using shift_closed by blast
        then show ?thesis
          by (metis (no_types) B0 B1 P.add.l_cancel_one UP_mult_closed X_closed assms(1))
      qed         
      then show ?case 
        by (metis P.r_null UP_m_comm UP_zero_closed X_closed assms(1) zcf_eq_zero_unique shift_closed)        
    next
      case (Suc n)
      fix n
      assume "shift (degree f + Suc n) f = \<zero>\<^bsub>P\<^esub>"
      then show "shift (degree f + Suc (Suc n)) f = \<zero>\<^bsub>P\<^esub>"
        by (simp add: poly_shift_degree_zero)
    qed
  qed
  then show ?thesis 
    using assms(2) less_iff_Suc_add by auto
qed

lemma(in UP_domain) shift_cfs0:
  assumes "f \<in> carrier P"
  shows "zcf(shift 1 f) = f 1"
  using assms 
  by (simp add: zcf_poly_shift) 

lemma(in UP_cring) X_mult_cf:
  assumes "p \<in> carrier P"
  shows "(p \<otimes>\<^bsub>P\<^esub> X) (k+1) = p k"
  unfolding X_poly_def
  using assms 
  by (metis UP_m_comm X_closed X_poly_def add.commute plus_1_eq_Suc cfs_times_X)
 
lemma(in UP_cring) X_pow_cf:
  assumes "p \<in> carrier P"
  shows "(p \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n::nat)) (n + k) = p k"
proof-
  have P: "\<And>f. f \<in> carrier P \<Longrightarrow> (f \<otimes>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n::nat)) (n + k) = f k"
  proof(induction n)
    show "\<And>f. f \<in> carrier P \<Longrightarrow> (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> (0::nat)) (0 + k) = f k"
    proof-
      fix f
      assume B0: "f \<in> carrier P"
      show "(f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> (0::nat)) (0 + k) = f k"
        by (simp add: B0)
    qed
    fix n
    fix f
    assume IH: "(\<And>f. f \<in> carrier P \<Longrightarrow> (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n) (n + k) = f k)"
    assume A0: " f \<in> carrier P"
    show "(f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> Suc n) (Suc n + k) = f k"
    proof-
      have 0: "(f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)(n + k) = f k"
        using A0 IH by simp
      have 1: "((f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)\<otimes>\<^bsub>P\<^esub>X) (Suc n + k) = (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)(n + k)"
        using X_mult_cf A0 P.m_closed P.nat_pow_closed 
              Suc_eq_plus1 X_closed add_Suc by presburger
      have 2: "(f \<otimes>\<^bsub>P\<^esub> (X [^]\<^bsub>P\<^esub> n \<otimes>\<^bsub>P\<^esub>X)) (Suc n + k) = (f \<otimes>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> n)(n + k)"
        using 1
        by (simp add: A0 UP_m_assoc X_closed)         
      then show ?thesis 
        by (simp add: "0")
    qed
  qed
  show ?thesis using assms P[of p] by auto 
qed

lemma poly_shift_cfs:
  assumes "f \<in> carrier P"
  shows "poly_shift f n = f (Suc n)"
proof-
  have "(f \<ominus>\<^bsub>P\<^esub> ctrm f) (Suc n) = (X \<otimes>\<^bsub>P\<^esub> (poly_shift f)) (Suc n)"
    using assms poly_shift_id by auto
  then show ?thesis unfolding X_poly_def using poly_shift_closed assms 
    by (metis (no_types, lifting) ctrm_degree ctrm_is_poly 
        P.add.m_comm P.minus_closed coeff_of_sum_diff_degree0 poly_shift_id poly_shift_eq cfs_times_X zero_less_Suc)
qed

lemma(in UP_cring) shift_cfs:
  assumes "p \<in> carrier P"
  shows "(shift k p) n = p (k + n)"
  apply(induction k arbitrary: n)
  by (auto simp: assms poly_shift_cfs shift_closed)

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>The Derivative Operator\<close>
  (**********************************************************************)
  (**********************************************************************)
definition pderiv where
"pderiv  p = poly_shift (n_mult p)"

lemma pderiv_closed:
  assumes "p \<in> carrier P"
  shows "pderiv p \<in> carrier P"
  unfolding  pderiv_def 
  using assms n_mult_closed[of p]  poly_shift_closed[of "n_mult p"] 
  by blast

text\<open>Function which obtains the first n+1 terms of f, in ascending order of degree:\<close>

definition trms_of_deg_leq  where
"trms_of_deg_leq n f \<equiv> f \<ominus>\<^bsub>(UP R)\<^esub> ((shift (Suc n) f) \<otimes>\<^bsub>UP R\<^esub> monom P \<one> (Suc n))"

lemma trms_of_deg_leq_closed:
  assumes "f \<in> carrier P"
  shows "trms_of_deg_leq n f \<in> carrier P"
  unfolding trms_of_deg_leq_def using assms 
  by (metis P.m_closed P.minus_closed P_def R.one_closed monom_closed shift_closed)

lemma trms_of_deg_leq_id:
  assumes "f \<in> carrier P"
  shows "f \<ominus>\<^bsub>P\<^esub> (trms_of_deg_leq k f) = shift (Suc k) f \<otimes>\<^bsub>P\<^esub> monom P \<one> (Suc k)"
  unfolding trms_of_deg_leq_def 
  using assms 
  by (smt P.add.inv_closed P.l_zero P.m_closed P.minus_add P.minus_minus P.r_neg
      P_def R.one_closed UP_a_assoc a_minus_def monom_closed shift_closed)

lemma trms_of_deg_leq_id':
  assumes "f \<in> carrier P"
  shows "f = (trms_of_deg_leq k f)  \<oplus>\<^bsub>P\<^esub> shift (Suc k) f \<otimes>\<^bsub>P\<^esub> monom P \<one> (Suc k)"
  using trms_of_deg_leq_id assms  trms_of_deg_leq_closed[of f]
  by (smt P.add.inv_closed P.l_zero P.m_closed P.minus_add P.minus_minus P.r_neg R.one_closed UP_a_assoc a_minus_def monom_closed shift_closed)

lemma deg_leqI:
  assumes "p \<in> carrier P"
  assumes "\<And>n. n > k \<Longrightarrow> p n = \<zero>"
  shows "degree p \<le> k"
  by (metis assms(1) assms(2) deg_zero deg_ltrm le0 le_less_linear monom_zero)

lemma deg_leE:
  assumes "p \<in> carrier P"
  assumes "degree p < k"
  shows "p k = \<zero>"
  using assms  coeff_of_sum_diff_degree0 P_def coeff_simp deg_aboveD 
  by auto

lemma trms_of_deg_leq_deg:
  assumes "f \<in> carrier P"
  shows "degree (trms_of_deg_leq k f) \<le> k"
proof-
  have "\<And>n. (trms_of_deg_leq k f) (Suc k + n) = \<zero>"
  proof-
    fix n
    have 0: "(shift (Suc k) f \<otimes>\<^bsub>UP R\<^esub> monom P \<one> (Suc k)) (Suc k + n) = shift (Suc k) f n"
      using assms shift_closed cfs_monom_mult_l 
      by (metis P.m_comm P_def R.one_closed add.commute monom_closed times_X_pow_coeff)
    then show "trms_of_deg_leq k f (Suc k + n) = \<zero>" 
      unfolding trms_of_deg_leq_def
      using shift_cfs[of f "Suc k" n] 
            cfs_minus[of f "shift (Suc k) f \<otimes>\<^bsub>UP R\<^esub> monom P \<one> (Suc k)" "Suc k + n"]
      by (metis P.m_closed P.r_neg P_def R.one_closed a_minus_def assms 
          cfs_minus cfs_zero monom_closed shift_closed)
  qed
  then show ?thesis using deg_leqI 
    by (metis (no_types, lifting) assms le_iff_add less_Suc_eq_0_disj less_Suc_eq_le trms_of_deg_leq_closed)
qed
  
lemma trms_of_deg_leq_zero_is_ctrm:
  assumes "f \<in> carrier P"
  assumes "degree f > 0"
  shows "trms_of_deg_leq 0 f = ctrm f"
proof-
  have "f = ctrm f \<oplus>\<^bsub>P\<^esub> (X \<otimes>\<^bsub>P\<^esub> (shift (Suc 0) f))"
    using assms poly_shift_eq 
    by simp
  then have "f = ctrm f \<oplus>\<^bsub>P\<^esub> (X [^]\<^bsub>UP R\<^esub> Suc 0 \<otimes>\<^bsub>P\<^esub> (shift (Suc 0) f))"
    using P.nat_pow_eone P_def X_closed  by auto
  then show ?thesis 
  unfolding trms_of_deg_leq_def 
  by (metis (no_types, lifting) ctrm_is_poly One_nat_def P.add.right_cancel P.m_closed 
      P.minus_closed P.nat_pow_eone P_def UP_m_comm X_closed X_poly_def assms(1) shift_closed
      trms_of_deg_leq_def trms_of_deg_leq_id')
qed

lemma cfs_monom_mult:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "k < n"
  shows "(p \<otimes>\<^bsub>P\<^esub> (monom P a n)) k = \<zero>"
  apply(rule poly_induct3[of p])
    apply (simp add: assms(1))
   apply (metis (no_types, lifting) P.l_distr P.m_closed R.r_zero R.zero_closed assms(2) cfs_add monom_closed)
  using assms monom_mult[of _ a _ n] 
  by (metis R.m_closed R.m_comm add.commute cfs_monom not_add_less1)

lemma(in UP_cring) cfs_monom_mult_2:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "m < n"
  shows "((monom P a n) \<otimes>\<^bsub>P\<^esub> f) m = \<zero>"
  using cfs_monom_mult
  by (simp add: P.m_comm assms(1) assms(2) assms(3))

lemma trms_of_deg_leq_cfs:
  assumes "f \<in> carrier P"
  shows "trms_of_deg_leq n f k = (if k \<le> n then (f k) else \<zero>)"
  unfolding trms_of_deg_leq_def 
  apply(cases "k \<le> n")
  using cfs_minus[of f "shift (Suc n) f \<otimes>\<^bsub>UP R\<^esub> monom P \<one> (Suc n)"] 
        cfs_monom_mult[of _ \<one> k "Suc n"] 
   apply (metis (no_types, lifting) P.m_closed P.minus_closed P_def R.one_closed R.r_zero assms
      cfs_add cfs_closed le_refl monom_closed nat_less_le nat_neq_iff not_less_eq_eq shift_closed 
      trms_of_deg_leq_def trms_of_deg_leq_id')
  using trms_of_deg_leq_deg[of f n] deg_leE   
  unfolding trms_of_deg_leq_def 
  using assms trms_of_deg_leq_closed trms_of_deg_leq_def by auto
 
lemma trms_of_deg_leq_iter:
  assumes "f \<in> carrier P"
  shows "trms_of_deg_leq (Suc k) f = (trms_of_deg_leq k f) \<oplus>\<^bsub>P\<^esub> monom P (f (Suc k)) (Suc k)"
proof fix x
  show "trms_of_deg_leq (Suc k) f x = (trms_of_deg_leq k f \<oplus>\<^bsub>P\<^esub> monom P (f (Suc k)) (Suc k)) x"
    apply(cases "x \<le> k")
    using trms_of_deg_leq_cfs trms_of_deg_leq_closed cfs_closed[of f "Suc k"]
          cfs_add[of "trms_of_deg_leq k f" "monom P (f (Suc k)) (Suc k)" x]   
     apply (simp add: assms)
    using deg_leE assms cfs_closed cfs_monom apply auto[1]
    by (simp add: assms cfs_closed cfs_monom trms_of_deg_leq_cfs trms_of_deg_leq_closed)   
qed 

lemma trms_of_deg_leq_0:
  assumes "f \<in> carrier P"
  shows "trms_of_deg_leq 0 f = ctrm f"
  by (metis One_nat_def P.r_null P_def UP_m_comm UP_zero_closed X_closed X_poly_def assms not_gr_zero
      poly_shift_degree_zero shift_one trms_of_deg_leq_def trms_of_deg_leq_zero_is_ctrm trunc_simps(2) trunc_zero)
  
lemma trms_of_deg_leq_degree_f:
  assumes "f \<in>  carrier P"
  shows "trms_of_deg_leq (degree f) f = f"
proof fix x 
  show "trms_of_deg_leq (deg R f) f x = f x"
    using assms trms_of_deg_leq_cfs deg_leE[of f x] 
  by simp
qed

definition(in UP_cring) lin_part where
"lin_part f = trms_of_deg_leq 1 f"

lemma(in UP_cring) lin_part_id:
  assumes "f \<in> carrier P"
  shows "lin_part f = (ctrm f) \<oplus>\<^bsub>P\<^esub> monom P (f 1) 1"
  unfolding lin_part_def
  by (simp add: assms trms_of_deg_leq_0 trms_of_deg_leq_iter)

lemma(in UP_cring) lin_part_eq:
  assumes "f \<in> carrier P"
  shows "f = lin_part f \<oplus>\<^bsub>P\<^esub> (shift 2 f) \<otimes>\<^bsub>P\<^esub> monom P \<one> 2"
  unfolding lin_part_def 
  by (metis Suc_1 assms trms_of_deg_leq_id')

text\<open>Constant term of a substitution:\<close>

lemma zcf_eval:
  assumes "f \<in> carrier P"
  shows "zcf f = to_fun f \<zero>"
  using assms zcf_to_fun by blast

lemma ctrm_of_sub:
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows "zcf(f of g) = to_fun f (zcf g)"
  apply(rule poly_induct3[of f]) 
  apply (simp add: assms(1))
  using P_def UP_cring.to_fun_closed UP_cring_axioms zcf_add zcf_to_fun assms(2) to_fun_plus sub_add sub_closed apply fastforce
  using R.zero_closed zcf_to_fun assms(2) to_fun_sub monom_closed sub_closed by presburger
 
text\<open>Evaluation of linear part:\<close>

lemma to_fun_lin_part:
  assumes "f \<in> carrier P"
  assumes "b \<in> carrier R"
  shows "to_fun (lin_part f) b = (f 0) \<oplus> (f 1) \<otimes> b"
  using assms lin_part_id[of f] to_fun_ctrm to_fun_monom monom_closed 
   by (simp add: cfs_closed to_fun_plus) 

text\<open>Constant term of taylor expansion:\<close>

lemma taylor_zcf:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "zcf(T\<^bsub>a\<^esub> f) = to_fun f a"
  unfolding taylor_expansion_def
  using ctrm_of_sub assms P_def zcf_eval X_plus_closed taylor_closed taylor_eval by auto

lemma(in UP_cring) taylor_eq_1:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "(T\<^bsub>a\<^esub> f) \<ominus>\<^bsub>P\<^esub> (trms_of_deg_leq 1 (T\<^bsub>a\<^esub> f)) = (shift (2::nat) (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(2::nat))"
  by (metis P.nat_pow_eone P.nat_pow_mult P_def Suc_1 taylor_closed X_closed X_poly_def assms(1) 
      assms(2) monom_one_Suc2 one_add_one trms_of_deg_leq_id)

lemma(in UP_cring) taylor_deg_1:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "f of (X_plus a) = (lin_part (T\<^bsub>a\<^esub> f)) \<oplus>\<^bsub>P\<^esub> (shift (2::nat) (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(2::nat))"
  using taylor_eq_1[of f a]
  unfolding taylor_expansion_def lin_part_def
  using One_nat_def X_plus_closed assms(1) 
        assms(2) trms_of_deg_leq_id' numeral_2_eq_2 sub_closed 
  by (metis P.nat_pow_Suc2 P.nat_pow_eone P_def taylor_def X_closed X_poly_def monom_one_Suc taylor_expansion_def)

lemma(in UP_cring) taylor_deg_1_eval:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = to_fun (shift (2::nat) (T\<^bsub>a\<^esub> f)) b"
  assumes "fa = to_fun f a"
  assumes "f'a = deriv f a"
  shows "to_fun f (b \<oplus> a) = fa \<oplus> (f'a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
  using assms taylor_deg_1 unfolding derivative_def   
proof-
  have 0: "to_fun f (b \<oplus> a) = to_fun (f of (X_plus a)) b"
    using to_fun_sub assms X_plus_closed by auto    
  have 1: "to_fun (lin_part (T\<^bsub>a\<^esub> f)) b = fa \<oplus> (f'a \<otimes> b) "
    using assms to_fun_lin_part[of "(T\<^bsub>a\<^esub> f)" b]  
    by (metis P_def taylor_def UP_cring.taylor_zcf UP_cring.taylor_closed UP_cring_axioms zcf_def derivative_def)    
  have 2: "(T\<^bsub>a\<^esub> f) = (lin_part (T\<^bsub>a\<^esub> f)) \<oplus>\<^bsub>P\<^esub> ((shift 2 (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>(2::nat))"
    using lin_part_eq[of "(T\<^bsub>a\<^esub>f)"] assms(1) assms(2) taylor_closed 
    by (metis taylor_def taylor_deg_1 taylor_expansion_def)        
  then have "to_fun (T\<^bsub>a\<^esub>f) b = fa \<oplus> (f'a \<otimes> b) \<oplus> to_fun ((shift 2 (T\<^bsub>a\<^esub> f))\<otimes>\<^bsub>P\<^esub>X[^]\<^bsub>P\<^esub>(2::nat)) b"
    using 1 2 
    by (metis P.nat_pow_closed taylor_closed UP_mult_closed X_closed assms(1) assms(2) assms(3) 
        to_fun_plus lin_part_def shift_closed trms_of_deg_leq_closed)    
  then have  "to_fun (T\<^bsub>a\<^esub>f) b = fa \<oplus> (f'a \<otimes> b) \<oplus> c \<otimes> to_fun (X[^]\<^bsub>P\<^esub>(2::nat)) b"
    by (simp add: taylor_closed X_closed assms(1) assms(2) assms(3) assms(4) to_fun_mult shift_closed)    
  then have 3: "to_fun f (b \<oplus> a)= fa \<oplus> (f'a \<otimes> b) \<oplus> c \<otimes> to_fun (X[^]\<^bsub>P\<^esub>(2::nat)) b"
    using taylor_eval assms(1) assms(2) assms(3) by auto
  have "to_fun (X[^]\<^bsub>P\<^esub>(2::nat)) b = b[^](2::nat)"
    by (metis P.nat_pow_Suc2 P.nat_pow_eone R.nat_pow_Suc2 
        R.nat_pow_eone Suc_1 to_fun_X 
        X_closed assms(3) to_fun_mult)
  then show ?thesis 
    using 3 by auto 
qed

lemma(in UP_cring) taylor_deg_1_eval':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = to_fun (shift (2::nat) (T\<^bsub>a\<^esub> f)) b"
  assumes "fa = to_fun f a"
  assumes "f'a = deriv f a"
  shows "to_fun f (a \<oplus> b) = fa \<oplus> (f'a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
  using R.add.m_comm taylor_deg_1_eval assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) 
  by auto

lemma(in UP_cring) taylor_deg_1_eval'':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = to_fun (shift (2::nat) (T\<^bsub>a\<^esub> f)) (\<ominus>b)"
  shows "to_fun f (a \<ominus> b) = (to_fun f a) \<ominus> (deriv f a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
proof-
  have "\<ominus>b \<in> carrier R"
    using assms 
    by blast
  then have 0: "to_fun f (a \<ominus> b) = (to_fun f a)\<oplus> (deriv f a \<otimes> (\<ominus>b)) \<oplus> (c \<otimes> (\<ominus>b)[^](2::nat))"
  unfolding a_minus_def
  using taylor_deg_1_eval'[of f a "\<ominus>b" c "(to_fun f a)" "deriv f a"] assms
  by auto 
  have 1: "\<ominus> (deriv f a \<otimes> b) = (deriv f a \<otimes> (\<ominus>b))"
    using assms 
    by (simp add: R.r_minus deriv_closed)
  have 2: "(c \<otimes> b[^](2::nat)) = (c \<otimes> (\<ominus>b)[^](2::nat))"
    using assms 
    by (metis R.add.inv_closed R.add.inv_solve_right R.l_zero R.nat_pow_Suc2 
        R.nat_pow_eone R.zero_closed Suc_1 UP_ring_axioms UP_ring_def
        ring.ring_simprules(26) ring.ring_simprules(27))
  show ?thesis 
    using 0 1 2 
    unfolding a_minus_def
    by simp 
qed

lemma(in UP_cring) taylor_deg_1_expansion:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = to_fun (shift (2::nat) (T\<^bsub>a\<^esub> f)) (b \<ominus> a)"
  assumes "fa = to_fun f a"
  assumes "f'a = deriv f a"
  shows "to_fun f (b) = fa \<oplus> f'a \<otimes> (b \<ominus> a) \<oplus> (c \<otimes> (b \<ominus> a)[^](2::nat))"
proof-
  obtain b' where b'_def: "b'= b \<ominus> a "
    by simp
  then have b'_def': "b = b' \<oplus> a"
    using assms 
    by (metis R.add.inv_solve_right R.minus_closed R.minus_eq)
  have "to_fun f (b' \<oplus> a) = fa \<oplus> (f'a \<otimes> b') \<oplus> (c \<otimes> b'[^](2::nat))" 
    using assms taylor_deg_1_eval[of f a b' c fa f'a]  b'_def 
    by blast
  then have "to_fun f (b) = fa \<oplus> (f'a \<otimes> b') \<oplus> (c \<otimes> b'[^](2::nat))" 
    using b'_def' 
    by auto 
  then show "to_fun f (b) = fa \<oplus> f'a \<otimes> (b \<ominus> a) \<oplus> c \<otimes> (b \<ominus> a) [^] (2::nat)"
    using b'_def
    by auto   
qed

lemma(in UP_cring) Taylor_deg_1_expansion':
  assumes "f \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "\<exists>c \<in> carrier R. to_fun f (b) = (to_fun f a) \<oplus> (deriv f a) \<otimes> (b \<ominus> a) \<oplus> (c \<otimes> (b \<ominus> a)[^](2::nat))"
  using taylor_deg_1_expansion[of f a b] assms unfolding P_def 
  by (metis P_def R.minus_closed taylor_closed shift_closed to_fun_closed)


text\<open>Basic Properties of deriv and pderiv:\<close>

lemma n_mult_degree_bound:
  assumes "f \<in> carrier P"
  shows "degree (n_mult f) \<le> degree f"
  apply(rule deg_leqI)
  apply (simp add: assms n_mult_closed)
  by (simp add: assms deg_leE n_mult_def)

lemma pderiv_deg_0[simp]:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  shows "pderiv f = \<zero>\<^bsub>P\<^esub>"
proof-
  have "degree (n_mult f) = 0"
    using P_def n_mult_degree_bound  assms(1) assms(2) by fastforce
  then show ?thesis 
    unfolding pderiv_def
    by (simp add: assms(1) n_mult_closed poly_shift_degree_zero)    
qed

lemma deriv_deg_0:
  assumes "f \<in> carrier P"
  assumes "degree f = 0"
  assumes "a \<in> carrier R"
  shows "deriv f a = \<zero>"
  unfolding derivative_def taylor_expansion_def
  using X_plus_closed assms(1) assms(2) assms(3) deg_leE sub_const by force

lemma poly_shift_monom':
  assumes "a \<in> carrier R"
  shows "poly_shift (a \<odot>\<^bsub>P\<^esub> (X[^]\<^bsub>P\<^esub>(Suc n))) = a\<odot>\<^bsub>P\<^esub>(X[^]\<^bsub>P\<^esub>n)"
  using assms monom_rep_X_pow poly_shift_monom by auto

lemma monom_coeff:
  assumes "a \<in> carrier R"
  shows "(a \<odot>\<^bsub>P\<^esub> X [^]\<^bsub>P\<^esub> (n::nat)) k = (if (k = n) then a else \<zero>)"
  using assms cfs_monom monom_rep_X_pow by auto

lemma cfs_n_mult:
  assumes "p \<in> carrier P"
  shows "n_mult p n = [n]\<cdot>(p n)"
  by (simp add: n_mult_def)

lemma cfs_add_nat_pow:
  assumes "p \<in> carrier P"
  shows "([(n::nat)]\<cdot>\<^bsub>P\<^esub>p) k = [n]\<cdot>(p k)"
  apply(induction n) by (auto simp: assms)

lemma cfs_add_int_pow:
  assumes "p \<in> carrier P"
  shows "([(n::int)]\<cdot>\<^bsub>P\<^esub>p) k = [n]\<cdot>(p k)"
  apply(induction n)
  by(auto simp: add_pow_int_ge assms cfs_add_nat_pow add_pow_int_lt)

lemma add_nat_pow_monom:
  assumes "a \<in> carrier R"
  shows "[(n::nat)]\<cdot>\<^bsub>P\<^esub>monom P a k = monom P ([n]\<cdot>a) k"
  apply(rule ext) 
  by (simp add: assms cfs_add_nat_pow cfs_monom)
  
lemma add_int_pow_monom:
  assumes "a \<in> carrier R"
  shows "[(n::int)]\<cdot>\<^bsub>P\<^esub>monom P a k = monom P ([n]\<cdot>a) k"
  apply(rule ext) 
  by (simp add: assms cfs_add_int_pow cfs_monom)

lemma n_mult_monom:
  assumes "a \<in> carrier R"
  shows "n_mult (monom P a (Suc n)) = monom P ([Suc n]\<cdot>a) (Suc n)"
  apply(rule ext)
  unfolding n_mult_def 
  using assms cfs_monom by auto

lemma pderiv_monom:
  assumes "a \<in> carrier R"
  shows "pderiv (monom P a n) = monom P ([n]\<cdot>a) (n-1)"
  apply(cases "n = 0")
   apply (simp add: assms)
  unfolding pderiv_def 
  using assms Suc_diff_1[of n] n_mult_monom[of a "n-1"] poly_shift_monom[of "[Suc (n-1)]\<cdot>a" "Suc (n-1)"]
  by (metis R.add.nat_pow_closed neq0_conv poly_shift_monom)

lemma pderiv_monom':
  assumes "a \<in> carrier R"
  shows "pderiv (a \<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n::nat)) = ([n]\<cdot>a)\<odot>\<^bsub>P\<^esub> X[^]\<^bsub>P\<^esub>(n-1)"  
  using assms pderiv_monom[of a n ] 
  by (simp add: P_def UP_cring.monom_rep_X_pow UP_cring_axioms)

lemma n_mult_add:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "n_mult (p \<oplus>\<^bsub>P\<^esub> q) = n_mult p \<oplus>\<^bsub>P\<^esub> n_mult q"
proof(rule ext) fix x show "n_mult (p \<oplus>\<^bsub>P\<^esub> q) x = (n_mult p \<oplus>\<^bsub>P\<^esub> n_mult q) x"
  using assms R.add.nat_pow_distrib[of "p x" "q x" x]  cfs_add[of p q x] 
        cfs_add[of "n_mult p" "n_mult q" x] n_mult_closed
  unfolding n_mult_def 
  by (simp add: cfs_closed) 
qed

lemma pderiv_add:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "pderiv (p \<oplus>\<^bsub>P\<^esub> q) = pderiv p \<oplus>\<^bsub>P\<^esub> pderiv q"
  unfolding pderiv_def 
  using assms poly_shift_add n_mult_add 
  by (simp add: n_mult_closed)

lemma zcf_monom_sub:
  assumes "p \<in> carrier P"
  shows "zcf ((monom P \<one> (Suc n)) of  p) = zcf p [^] (Suc n)"
  apply(induction n)
  using One_nat_def P.nat_pow_eone R.nat_pow_eone R.one_closed R.zero_closed zcf_to_fun assms to_fun_closed monom_sub smult_one apply presburger
  using P_def UP_cring.ctrm_of_sub UP_cring_axioms zcf_to_fun assms to_fun_closed to_fun_monom monom_closed 
  by fastforce

lemma zcf_monom_sub':
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "zcf ((monom P a (Suc n)) of  p) = a \<otimes> zcf p [^] (Suc n)"
  using zcf_monom_sub assms P_def R.zero_closed UP_cring.ctrm_of_sub UP_cring.to_fun_monom UP_cring_axioms
    zcf_to_fun to_fun_closed monom_closed by fastforce
  
lemma deriv_monom:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "deriv (monom P a n) b =  ([n]\<cdot>a)\<otimes>(b[^](n-1))"  
proof(induction n)
  case 0
  have 0: "b [^] ((0::nat) - 1) \<in> carrier R"
    using assms 
    by simp
  then show ?case unfolding derivative_def using assms  
    by (smt One_nat_def P_def R.add.nat_pow_0 R.nat_pow_Suc2 R.nat_pow_eone R.zero_closed 
        taylor_def taylor_deg UP_cring.taylor_closed UP_cring.zcf_monom UP_cring.shift_one 
        UP_cring_axioms zcf_degree_zero zcf_zero_degree_zero degree_monom monom_closed 
        monom_rep_X_pow plus_1_eq_Suc poly_shift_degree_zero shift_cfs to_fun_monom to_fun_zero zero_diff)
next
  case (Suc n)
  show ?case
  proof(cases "n = 0")
    case True
    have T0: "[Suc n] \<cdot> a \<otimes> b [^] (Suc n - 1) = a"
      by (simp add: True assms(1))
    have T1: "(X_poly R \<oplus>\<^bsub>UP R\<^esub> to_polynomial R b) [^]\<^bsub>UP R\<^esub> Suc n = X_poly R \<oplus>\<^bsub>UP R\<^esub> to_polynomial R b "
      using P.nat_pow_eone P_def True UP_a_closed X_closed assms(2) to_poly_closed by auto
    then show ?thesis 
      unfolding derivative_def taylor_expansion_def
      using T0 T1 True sub_monom(2)[of "X_plus b" a "Suc n"] cfs_add assms
      unfolding P_def X_poly_plus_def to_polynomial_def X_poly_def  
      by (smt Group.nat_pow_0 lcf_eq lcf_monom(2) ltrm_of_X_plus One_nat_def P_def R.one_closed 
          R.r_one R.r_zero UP_cring.zcf_monom UP_cring.degree_of_X_plus 
          UP_cring.poly_shift_degree_zero UP_cring_axioms X_closed X_plus_closed X_poly_def 
          X_poly_plus_def zcf_zero_degree_zero cfs_monom_mult_l degree_to_poly to_fun_X_pow 
          plus_1_eq_Suc poly_shift_cfs poly_shift_monom to_poly_closed to_poly_mult_simp(2)
          to_poly_nat_pow to_polynomial_def)
  next
    case False
  have "deriv (monom P a (Suc n)) b = ((monom P a (Suc n)) of (X_plus b)) 1"
    unfolding derivative_def taylor_expansion_def 
    by auto
  then have "deriv (monom P a (Suc n)) b = (((monom P a n) of (X_plus b)) \<otimes>\<^bsub>P\<^esub> (X_plus b)) 1"
    using  monom_mult[of a \<one> n 1] sub_mult[of "X_plus b" "monom P a n" "monom P \<one> 1" ]  X_plus_closed[of b] assms   
    by (metis lcf_monom(1) P.l_one P.nat_pow_eone P_def R.one_closed R.r_one Suc_eq_plus1 
        deg_one monom_closed monom_one sub_monom(1) to_poly_inverse)
  then have "deriv (monom P a (Suc n)) b = (((monom P a n) of (X_plus b)) \<otimes>\<^bsub>P\<^esub> (monom P \<one> 1) \<oplus>\<^bsub>P\<^esub>  
                                            (((monom P a n) of (X_plus b)) \<otimes>\<^bsub>P\<^esub> to_poly b)) 1"
    unfolding X_poly_plus_def 
    by (metis P.r_distr P_def X_closed X_plus_closed X_poly_def X_poly_plus_def assms(1) assms(2) monom_closed sub_closed to_poly_closed)
  then have "deriv (monom P a (Suc n)) b = ((monom P a n) of (X_plus b)) 0 \<oplus> b \<otimes> ((monom P a n) of (X_plus b)) 1"
    unfolding X_poly_plus_def 
    by (smt One_nat_def P.m_closed P_def UP_m_comm X_closed X_plus_closed X_poly_def X_poly_plus_def
        assms(1) assms(2) cfs_add cfs_monom_mult_l monom_closed plus_1_eq_Suc sub_closed cfs_times_X to_polynomial_def)
  then have "deriv (monom P a (Suc n)) b = ((monom P a n) of (X_plus b)) 0 \<oplus> b \<otimes> (deriv (monom P a n) b)"
    by (simp add: derivative_def taylor_expansion_def)
  then have "deriv (monom P a (Suc n)) b = ((monom P a n) of (X_plus b)) 0 \<oplus> b \<otimes> ( ([n]\<cdot>a)\<otimes>(b[^](n-1)))"
    by (simp add: Suc)
  then have 0: "deriv (monom P a (Suc n)) b = ((monom P a n) of (X_plus b)) 0 \<oplus> ([n]\<cdot>a)\<otimes>(b[^]n)"
    using assms R.m_comm[of b] R.nat_pow_mult[of b "n-1" 1] False 
    by (metis (no_types, lifting) R.add.nat_pow_closed R.m_lcomm R.nat_pow_closed R.nat_pow_eone add.commute add_eq_if plus_1_eq_Suc)
  have 1: "((monom P a n) of (X_plus b)) 0 = a \<otimes> b[^]n"
     unfolding X_poly_plus_def using zcf_monom_sub' 
     by (smt ctrm_of_sub One_nat_def P_def R.l_zero R.one_closed UP_cring.zcf_to_poly 
         UP_cring.f_minus_ctrm UP_cring_axioms X_plus_closed X_poly_def X_poly_plus_def zcf_add
         zcf_def assms(1) assms(2) to_fun_monom monom_closed monom_one_Suc2 poly_shift_id poly_shift_monom to_poly_closed)
   show ?thesis 
     using 0 1  R.add.nat_pow_Suc2 R.add.nat_pow_closed R.l_distr R.nat_pow_closed assms(1) assms(2) diff_Suc_1 by presburger
 qed
qed

lemma deriv_smult:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "g \<in> carrier P"
  shows "deriv (a \<odot>\<^bsub>P\<^esub> g) b = a \<otimes> (deriv g b)"
  unfolding derivative_def taylor_expansion_def 
  using assms sub_smult X_plus_closed cfs_smult
  by (simp add: sub_closed)

lemma deriv_const:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "deriv (monom P a 0) b = \<zero>"
  unfolding derivative_def 
  using assms taylor_closed taylor_def taylor_deg deg_leE by auto 

lemma deriv_monom_deg_one:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "deriv (monom P a 1) b = a"
  unfolding derivative_def taylor_expansion_def 
  using assms cfs_X_plus[of b 1] sub_monom_deg_one X_plus_closed[of b]
  by simp  

lemma monom_Suc:
  assumes "a \<in> carrier R"
  shows "monom P a (Suc n) = monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P a n"
        "monom P a (Suc n) = monom P a n \<otimes>\<^bsub>P\<^esub> monom P \<one> 1"
  apply (metis R.l_one R.one_closed Suc_eq_plus1_left assms monom_mult)
  by (metis R.one_closed R.r_one Suc_eq_plus1 assms monom_mult)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>The Product Rule\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma(in UP_cring) times_x_product_rule: 
  assumes "f \<in> carrier P"
  shows "pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) =  f \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
proof(rule poly_induct3[of f])
  show "f \<in> carrier P"
    using assms by blast 
  show "\<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           pderiv (p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = p \<oplus>\<^bsub>P\<^esub> pderiv p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 \<Longrightarrow>
           pderiv (q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = q \<oplus>\<^bsub>P\<^esub> pderiv q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 \<Longrightarrow>
           pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = p \<oplus>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> pderiv (p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
  proof- fix p q assume A: "q \<in> carrier P"
           "p \<in> carrier P"
           "pderiv (p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = p \<oplus>\<^bsub>P\<^esub> pderiv p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
           "pderiv (q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = q \<oplus>\<^bsub>P\<^esub> pderiv q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
    have 0: "(p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 =  (p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) \<oplus>\<^bsub>P\<^esub> (q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1)"
      using A assms  by (meson R.one_closed UP_l_distr is_UP_monomE(1) is_UP_monomI)
    have  1: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = pderiv (p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) \<oplus>\<^bsub>P\<^esub> pderiv (q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1)"
      unfolding 0 apply(rule pderiv_add) 
      using A is_UP_monomE(1) monom_is_UP_monom(1) apply blast
      using A is_UP_monomE(1) monom_is_UP_monom(1) by blast
    have 2: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = p \<oplus>\<^bsub>P\<^esub> pderiv p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 \<oplus>\<^bsub>P\<^esub> (q \<oplus>\<^bsub>P\<^esub> pderiv q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1)"
      unfolding 1 A  by blast 
    have 3: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = p \<oplus>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> (pderiv p \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 \<oplus>\<^bsub>P\<^esub> pderiv q \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1)"
      unfolding 2 
      using A P.add.m_lcomm R.one_closed UP_a_assoc UP_a_closed UP_mult_closed is_UP_monomE(1) monom_is_UP_monom(1) pderiv_closed by presburger
    have 4: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = p \<oplus>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> ((pderiv p \<oplus>\<^bsub>P\<^esub> pderiv q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1)"
      unfolding 3 using A P.l_distr R.one_closed is_UP_monomE(1) monom_is_UP_monom(1) pderiv_closed by presburger
    show 5: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = p \<oplus>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> pderiv (p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
      unfolding 4 using pderiv_add A by presburger
  qed
  show "\<And>a n. a \<in> carrier R \<Longrightarrow>
           pderiv (up_ring.monom P a n \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = up_ring.monom P a n \<oplus>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
  proof- fix a n assume A: "a \<in> carrier R"
    have 0: "up_ring.monom P a n \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 = up_ring.monom P a (Suc n)"
      using A monom_Suc(2) by presburger
    have 1: "pderiv (up_ring.monom P a n \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) =  [(Suc n)] \<cdot>\<^bsub>P\<^esub> (up_ring.monom P a n)"
      unfolding 0 using A add_nat_pow_monom n_mult_monom pderiv_def poly_shift_monom 
      by (simp add: P_def)
    have 2: "pderiv (up_ring.monom P a n \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = (up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> [n] \<cdot>\<^bsub>P\<^esub> (up_ring.monom P a n)"
      unfolding 1 using A P.add.nat_pow_Suc2 is_UP_monomE(1) monom_is_UP_monom(1) by blast
    have 3: "pderiv (up_ring.monom P a n) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 =  [n] \<cdot>\<^bsub>P\<^esub> (up_ring.monom P a n)"
      apply(cases "n = 0")
      using A  add_nat_pow_monom n_mult_monom pderiv_def poly_shift_monom pderiv_deg_0 apply auto[1]
      using monom_Suc(2)[of a "n-1"] A  add_nat_pow_monom n_mult_monom pderiv_def poly_shift_monom
      by (metis R.add.nat_pow_closed Suc_eq_plus1 add_eq_if monom_Suc(2) pderiv_monom)     
    show "pderiv (up_ring.monom P a n \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = up_ring.monom P a n \<oplus>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
      unfolding 2 3 by blast 
  qed
qed

lemma(in UP_cring) deg_one_eval:
  assumes "g \<in> carrier (UP R)"
  assumes "deg R g = 1"
  shows "\<And>t. t \<in> carrier R \<Longrightarrow> to_fun g t = g 0 \<oplus> (g 1)\<otimes>t"
proof-
  obtain h where h_def: "h = ltrm g"
    by blast 
  have 0: "deg R (g \<ominus>\<^bsub>UP R\<^esub> h) = 0"
    using assms unfolding h_def 
    by (metis ltrm_closed ltrm_eq_imp_deg_drop ltrm_monom P_def UP_car_memE(1) less_one)
  have 1: "g \<ominus>\<^bsub>UP R\<^esub> h = to_poly (g 0)"
  proof(rule ext) fix x show "(g \<ominus>\<^bsub>UP R\<^esub> h) x = to_polynomial R (g 0) x"
    proof(cases "x = 0")
      case True
      have T0: "h 0 = \<zero>"
        unfolding h_def using assms UP_car_memE(1) cfs_monom by presburger
      have T1: "(g \<ominus>\<^bsub>UP R\<^esub> h) 0 = g 0 \<ominus> h 0"
        using ltrm_closed P_def assms(1) cfs_minus h_def by blast
      then show ?thesis using T0 assms  
        by (smt "0" ltrm_closed ltrm_deg_0 P.minus_closed P_def UP_car_memE(1) UP_zero_closed zcf_def zcf_zero deg_zero degree_to_poly h_def to_poly_closed to_poly_inverse to_poly_minus trunc_simps(2) trunc_zero)        
    next
      case False
      then have "x > 0"
        by presburger 
      then show ?thesis 
        by (metis "0" ltrm_closed P.minus_closed P_def UP_car_memE(1) UP_cring.degree_to_poly UP_cring_axioms assms(1) deg_leE h_def to_poly_closed)     
    qed
  qed
  have 2: "g = (g \<ominus>\<^bsub>UP R\<^esub> h) \<oplus>\<^bsub>UP R\<^esub> h"
    unfolding h_def using assms 
    by (metis "1" P_def h_def lin_part_def lin_part_id to_polynomial_def trms_of_deg_leq_degree_f)    
  fix t assume A: "t \<in> carrier R"
  have 3: " to_fun g t = to_fun (g \<ominus>\<^bsub>UP R\<^esub> h) t \<oplus> to_fun h t"
    using 2 
    by (metis "1" A P_def UP_car_memE(1) assms(1) h_def monom_closed to_fun_plus to_polynomial_def)
  then show "to_fun g t = g 0 \<oplus> g 1 \<otimes> t "
    unfolding 1 h_def 
    using A P_def UP_cring.lin_part_def UP_cring_axioms assms(1) assms(2) to_fun_lin_part trms_of_deg_leq_degree_f by fastforce
qed

lemma nmult_smult:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "n_mult (a \<odot>\<^bsub>P\<^esub> f) = a \<odot>\<^bsub>P\<^esub> (n_mult f)"
  apply(rule poly_induct4[of f])
  apply (simp add: assms(2))
  using assms(1) n_mult_add n_mult_closed smult_closed smult_r_distr apply presburger
  using assms  apply(intro ext, metis (no_types, lifting) ctrm_smult ltrm_deg_0 P_def R.add.nat_pow_0 UP_cring.ctrm_degree UP_cring.n_mult_closed UP_cring.n_mult_def UP_cring_axioms UP_smult_closed UP_zero_closed zcf_degree_zero zcf_zero deg_const deg_zero le_0_eq monom_closed n_mult_degree_bound smult_r_null)
  using monom_mult_smult n_mult_monom assms 
  by (smt lcf_monom(1) P_def R.add.nat_pow_closed R.add_pow_rdistr R.zero_closed UP_cring.to_poly_mult_simp(1) UP_cring_axioms UP_smult_closed cfs_closed cring_lcf_mult monom_closed to_polynomial_def)

lemma pderiv_smult:
  assumes "a \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "pderiv (a \<odot>\<^bsub>P\<^esub> f) = a \<odot>\<^bsub>P\<^esub> (pderiv f)"
  unfolding pderiv_def
  using assms
  by (simp add: n_mult_closed nmult_smult poly_shift_s_mult) 

lemma(in UP_cring) pderiv_minus:
  assumes "a \<in> carrier P"
  assumes "b \<in> carrier P"
  shows "pderiv (a \<ominus>\<^bsub>P\<^esub> b) = pderiv a \<ominus>\<^bsub>P\<^esub> pderiv b"
proof-
  have "\<ominus>\<^bsub>P\<^esub> b = (\<ominus>\<one>)\<odot>\<^bsub>P\<^esub>b"
    using R.one_closed UP_smult_one assms(2) smult_l_minus by presburger
  thus ?thesis unfolding a_minus_def using pderiv_add assms pderiv_smult
    by (metis P.add.inv_closed R.add.inv_closed R.one_closed UP_smult_one pderiv_closed smult_l_minus)
qed

lemma(in UP_cring) pderiv_const:
  assumes "b \<in> carrier R"
  shows "pderiv (up_ring.monom P b 0) = \<zero>\<^bsub>P\<^esub>"
  using assms pderiv_monom[of b 0] deg_const is_UP_monomE(1) monom_is_UP_monom(1) pderiv_deg_0 
  by blast
   
lemma(in UP_cring) pderiv_minus_const:
  assumes "a \<in> carrier P"
  assumes "b \<in> carrier R"
  shows "pderiv (a \<ominus>\<^bsub>P\<^esub> up_ring.monom P b 0) = pderiv a"
  using pderiv_minus[of a "up_ring.monom P b 0" ] assms pderiv_const[of b] 
  by (smt P.l_zero P.minus_closed P_def UP_cring.pderiv_const UP_cring.pderiv_minus UP_cring.poly_shift_eq UP_cring_axioms cfs_closed monom_closed pderiv_add pderiv_closed poly_shift_id)

lemma(in UP_cring) monom_product_rule: 
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R" 
  shows "pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n) =  f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n"
proof-
  have "\<forall>f. f \<in> carrier P \<longrightarrow> pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n) =  f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n"
  proof(induction n)
    case 0
    show ?case 
    proof fix f show "f \<in> carrier P \<longrightarrow> pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a 0) = f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a 0) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a 0 "
      proof assume A: "f \<in> carrier P"
        have 0: "f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a 0 = a \<odot>\<^bsub>P\<^esub>f"
          using assms A  UP_m_comm is_UP_monomE(1) monom_is_UP_monom(1) monom_mult_is_smult by presburger
        have 1: "f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a 0) = \<zero>\<^bsub>P\<^esub>"
          using A assms P.r_null pderiv_const by presburger
        have 2: "pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a 0 = a \<odot>\<^bsub>P\<^esub> pderiv f"
          using assms A  UP_m_comm is_UP_monomE(1) monom_is_UP_monom(1) monom_mult_is_smult  pderiv_closed by presburger
        show "pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a 0) = f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a 0) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a 0"
          unfolding 0 1 2 using A UP_l_zero UP_smult_closed assms(2) pderiv_closed pderiv_smult by presburger
      qed
    qed
  next
    case (Suc n)
    show "\<forall>f. f \<in> carrier P \<longrightarrow>
             pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)) = f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a (Suc n)) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)"
    proof fix f
      show "f \<in> carrier P \<longrightarrow>
         pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)) = f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a (Suc n)) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)"
      proof
       assume A: "f \<in> carrier P"
      show " pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)) = f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a (Suc n)) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)"
      proof(cases "n = 0")
        case True
        have 0: "(f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)) = a \<odot>\<^bsub>P\<^esub> f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1"
        proof -
          have "\<forall>n. up_ring.monom P a n \<in> carrier P"
            using assms(2) is_UP_monomE(1) monom_is_UP_monom(1) by presburger
          then show ?thesis
            by (metis A P.m_assoc P.m_comm R.one_closed True assms(2) is_UP_monomE(1) monom_Suc(2) monom_is_UP_monom(1) monom_mult_is_smult)
        qed
        have 1: "f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a (Suc n)) = a \<odot>\<^bsub>P\<^esub> f"
          using assms True 
          by (metis A One_nat_def P.m_comm R.add.nat_pow_eone diff_Suc_1 is_UP_monomE(1) is_UP_monomI monom_mult_is_smult pderiv_monom)
        have 2: "pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n) = a \<odot>\<^bsub>P\<^esub> (pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1)"
          using A assms unfolding True 
          by (metis P.m_lcomm R.one_closed UP_mult_closed is_UP_monomE(1) monom_Suc(2) monom_is_UP_monom(1) monom_mult_is_smult pderiv_closed)
        have 3: "a \<odot>\<^bsub>P\<^esub> f \<oplus>\<^bsub>P\<^esub> a \<odot>\<^bsub>P\<^esub> (pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) = a \<odot>\<^bsub>P\<^esub> (f \<oplus>\<^bsub>P\<^esub>(pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1))"
          using assms A  P.m_closed R.one_closed is_UP_monomE(1) monom_is_UP_monom(1) pderiv_closed smult_r_distr by presburger
        show ?thesis
          unfolding 0 1 2 3 
          using A times_x_product_rule P.m_closed R.one_closed UP_smult_assoc2 assms(2) is_UP_monomE(1) monom_is_UP_monom(1) pderiv_smult by presburger
      next
        case False
      have IH: "pderiv ((f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n) = (f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> pderiv (f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n"
        using Suc A P.m_closed R.one_closed is_UP_monomE(1) is_UP_monomI by presburger
      have 0: "f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n) = (f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1)  \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n"
        using A R.one_closed UP_m_assoc assms(2) is_UP_monomE(1) monom_Suc(1) monom_is_UP_monom(1) by presburger
      have 1: "(f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> pderiv (f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n = 
               (f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> (f \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n "
        using A times_x_product_rule by presburger
      have 2: "(f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) =(f \<otimes>\<^bsub>P\<^esub>up_ring.monom P ([n]\<cdot>a) n)"
      proof-
        have 20: "up_ring.monom P ([n] \<cdot> a) (n) = up_ring.monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> up_ring.monom P ([n] \<cdot> a) (n - 1)"
          using A assms False monom_mult[of \<one> "[n]\<cdot>a" 1 "n-1"] 
          by (metis R.add.nat_pow_closed R.l_one R.one_closed Suc_eq_plus1 add.commute add_eq_if )          
        show ?thesis unfolding 20 using assms A False   pderiv_monom[of a n] 
          using P.m_assoc R.one_closed is_UP_monomE(1) monom_is_UP_monom(1) by simp
      qed
      have 3: "(f \<otimes>\<^bsub>P\<^esub>up_ring.monom P ([n]\<cdot>a) n) = [n]\<cdot>\<^bsub>P\<^esub>(f \<otimes>\<^bsub>P\<^esub>up_ring.monom P a n)"
        using A assms by (metis P.add_pow_rdistr add_nat_pow_monom is_UP_monomE(1) monom_is_UP_monom(1))
      have 4: "pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) =  (f \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1)"
        using times_x_product_rule  A by blast
      have 5: " (f \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n  = 
 (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n ) \<oplus>\<^bsub>P\<^esub> (pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n )"
        using A assms  by (meson P.l_distr P.m_closed R.one_closed is_UP_monomE(1) is_UP_monomI pderiv_closed)
      have 6: " (f \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n  = 
 (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n ) \<oplus>\<^bsub>P\<^esub> (pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n )"
        using A assms False 5  by blast
      have 7: "(f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> pderiv (f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n =
               [(Suc n)] \<cdot>\<^bsub>P\<^esub> (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n"
        unfolding 2 3  5 6 using assms A P.a_assoc 
        by (smt "1" "2" "3" "6" P.add.nat_pow_Suc P.m_closed R.one_closed is_UP_monomE(1) monom_is_UP_monom(1) pderiv_closed)
      have 8: "pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)) = pderiv ((f \<otimes>\<^bsub>P\<^esub>up_ring.monom P \<one> 1) \<otimes>\<^bsub>P\<^esub> up_ring.monom P a n)"
        using A assms 0  by presburger
      show " pderiv (f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)) = f \<otimes>\<^bsub>P\<^esub> pderiv (up_ring.monom P a (Suc n)) \<oplus>\<^bsub>P\<^esub> pderiv f \<otimes>\<^bsub>P\<^esub> up_ring.monom P a (Suc n)"
        unfolding 8 IH 0 1 2 3 4 5 6 
        by (smt "2" "4" "6" "7" A P.add_pow_rdistr R.one_closed UP_m_assoc add_nat_pow_monom assms(2) diff_Suc_1 is_UP_monomE(1) is_UP_monomI monom_Suc(1) pderiv_closed pderiv_monom)        
       qed
     qed
   qed
 qed
  thus ?thesis using assms by blast 
qed

lemma(in UP_cring) product_rule: 
  assumes "f \<in> carrier (UP R)"
  assumes "g \<in> carrier (UP R)"
  shows "pderiv (f \<otimes>\<^bsub>UP R\<^esub>g) = (pderiv f \<otimes>\<^bsub>UP R\<^esub> g) \<oplus>\<^bsub>UP R\<^esub> (f \<otimes>\<^bsub>UP R\<^esub> pderiv g)"
proof(rule poly_induct3[of f])
  show "f \<in> carrier P"
    using assms unfolding P_def by blast 
  show "\<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           pderiv (p \<otimes>\<^bsub>UP R\<^esub> g) = pderiv p \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> p \<otimes>\<^bsub>UP R\<^esub> pderiv g \<Longrightarrow>
           pderiv (q \<otimes>\<^bsub>UP R\<^esub> g) = pderiv q \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>UP R\<^esub> pderiv g \<Longrightarrow>
           pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = pderiv (p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> (p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> pderiv g"
  proof- fix p q 
    assume A: "q \<in> carrier P" "p \<in> carrier P"
           "pderiv (p \<otimes>\<^bsub>UP R\<^esub> g) = pderiv p \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> p \<otimes>\<^bsub>UP R\<^esub> pderiv g"
           "pderiv (q \<otimes>\<^bsub>UP R\<^esub> g) = pderiv q \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>UP R\<^esub> pderiv g"
    have 0: "(p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g = p \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>UP R\<^esub> g"
      using A assms unfolding P_def using P_def UP_l_distr by blast
    have 1: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = pderiv (p \<otimes>\<^bsub>UP R\<^esub> g) \<oplus>\<^bsub>UP R\<^esub> pderiv (q \<otimes>\<^bsub>UP R\<^esub> g)"
      unfolding 0  using pderiv_add[of "p \<otimes>\<^bsub>P\<^esub> g" "q \<otimes>\<^bsub>P\<^esub> g"] unfolding P_def 
      using A(1) A(2) P_def UP_mult_closed assms(2) by blast
    have 2: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = pderiv p \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> p \<otimes>\<^bsub>UP R\<^esub> pderiv g \<oplus>\<^bsub>UP R\<^esub> (pderiv q \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>UP R\<^esub> pderiv g)"
      unfolding 1 A by blast 
    have 3: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = pderiv p \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> pderiv q \<otimes>\<^bsub>UP R\<^esub> g  \<oplus>\<^bsub>UP R\<^esub> p \<otimes>\<^bsub>UP R\<^esub> pderiv g  \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>UP R\<^esub> pderiv g"
      using A assms 
      by (smt "2" P.add.m_lcomm P.m_closed P_def UP_a_assoc pderiv_closed)
    have 4: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = (pderiv p \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> pderiv q \<otimes>\<^bsub>UP R\<^esub> g)  \<oplus>\<^bsub>UP R\<^esub> (p \<otimes>\<^bsub>UP R\<^esub> pderiv g  \<oplus>\<^bsub>UP R\<^esub> q \<otimes>\<^bsub>UP R\<^esub> pderiv g)"
      unfolding 3 using A assms P_def UP_a_assoc UP_a_closed UP_mult_closed pderiv_closed by auto
    have 5: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = ((pderiv p  \<oplus>\<^bsub>UP R\<^esub> pderiv q) \<otimes>\<^bsub>UP R\<^esub> g)  \<oplus>\<^bsub>UP R\<^esub> ((p \<oplus>\<^bsub>UP R\<^esub> q)  \<otimes>\<^bsub>UP R\<^esub> pderiv g)"
      unfolding 4 using A assms  by (metis P.l_distr P_def pderiv_closed)
    have 6: "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = ((pderiv (p \<oplus>\<^bsub>P\<^esub> q)) \<otimes>\<^bsub>UP R\<^esub> g)  \<oplus>\<^bsub>UP R\<^esub> ((p \<oplus>\<^bsub>UP R\<^esub> q)  \<otimes>\<^bsub>UP R\<^esub> pderiv g)"
      unfolding 5 using A assms  
      by (metis P_def pderiv_add)
    show "pderiv ((p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g) = pderiv (p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> (p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>UP R\<^esub> pderiv g"
      unfolding 6 using A assms P_def by blast     
  qed
  show "\<And>a n. a \<in> carrier R \<Longrightarrow>
           pderiv (up_ring.monom P a n \<otimes>\<^bsub>UP R\<^esub> g) = pderiv (up_ring.monom P a n) \<otimes>\<^bsub>UP R\<^esub> g \<oplus>\<^bsub>UP R\<^esub> up_ring.monom P a n \<otimes>\<^bsub>UP R\<^esub> pderiv g"
    using P_def UP_m_comm assms(2) is_UP_monomE(1) monom_is_UP_monom(1) monom_product_rule pderiv_closed by presburger
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>The Chain Rule\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma(in UP_cring) chain_rule: 
  assumes "f \<in> carrier P"
  assumes "g \<in> carrier P"
  shows "pderiv (compose R f g) = compose R (pderiv f) g \<otimes>\<^bsub>UP R\<^esub> pderiv g"
proof(rule poly_induct3[of f])
  show "f \<in> carrier P"
    using assms by blast
  show "\<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           pderiv (Cring_Poly.compose R p g) = Cring_Poly.compose R (pderiv p) g \<otimes>\<^bsub>UP R\<^esub> pderiv g \<Longrightarrow>
           pderiv (Cring_Poly.compose R q g) = Cring_Poly.compose R (pderiv q) g \<otimes>\<^bsub>UP R\<^esub> pderiv g \<Longrightarrow>
           pderiv (Cring_Poly.compose R (p \<oplus>\<^bsub>P\<^esub> q) g) = Cring_Poly.compose R (pderiv (p \<oplus>\<^bsub>P\<^esub> q)) g \<otimes>\<^bsub>UP R\<^esub> pderiv g"
  using pderiv_add sub_add 
  by (smt P_def UP_a_closed UP_m_comm UP_r_distr assms(2) pderiv_closed sub_closed)
  show "\<And>a n. a \<in> carrier R \<Longrightarrow>
           pderiv (compose R (up_ring.monom P a n) g) = compose R (pderiv (up_ring.monom P a n)) g \<otimes>\<^bsub>UP R\<^esub> pderiv g"
  proof-
    fix a n assume A: "a \<in> carrier R"
    show "pderiv (compose R (up_ring.monom P a n) g) = compose R (pderiv (up_ring.monom P a n)) g \<otimes>\<^bsub>UP R\<^esub> pderiv g"
    proof(induction n)
      case 0
      have 00: "(compose R (up_ring.monom P a 0) g) = (up_ring.monom P a 0)"
        using A P_def assms(2) deg_const is_UP_monom_def monom_is_UP_monom(1) sub_const by presburger
      have 01: "pderiv (up_ring.monom P a 0) = \<zero>\<^bsub>P\<^esub>"
        using A pderiv_const by blast
      show ?case unfolding 00 01 
        by (metis P.l_null P_def UP_zero_closed assms(2) deg_zero pderiv_closed sub_const)
    next
      case (Suc n)
      show "pderiv (Cring_Poly.compose R (up_ring.monom P a (Suc n)) g) = Cring_Poly.compose R (pderiv (up_ring.monom P a (Suc n))) g \<otimes>\<^bsub>UP R\<^esub> pderiv g"
      proof(cases "n = 0")
        case True
        have 0: "compose R (up_ring.monom P a (Suc n)) g = a \<odot>\<^bsub>P\<^esub> g"
          using A assms sub_monom_deg_one[of g a] unfolding True using One_nat_def 
          by presburger
        have 1: "(pderiv (up_ring.monom P a (Suc n))) = up_ring.monom P a 0"
          unfolding True 
        proof -
          have "pderiv (up_ring.monom P a 0) = \<zero>\<^bsub>P\<^esub>"
            using A pderiv_const by blast
          then show "pderiv (up_ring.monom P a (Suc 0)) = up_ring.monom P a 0"
            using A lcf_monom(1) P_def  X_closed deg_const deg_nzero_nzero  is_UP_monomE(1) monom_Suc(2) monom_is_UP_monom(1) monom_rep_X_pow pderiv_monom poly_shift_degree_zero poly_shift_eq sub_monom(2) sub_monom_deg_one to_poly_inverse to_poly_mult_simp(2)
            by (metis (no_types, lifting) P.l_null P.r_zero X_poly_def times_x_product_rule)
        qed
        then show ?thesis unfolding 0 1 
          using A P_def assms(2) deg_const is_UP_monomE(1) monom_is_UP_monom(1) monom_mult_is_smult pderiv_closed pderiv_smult sub_const 
          by presburger
      next
        case False
      have 0: "compose R (up_ring.monom P a (Suc n)) g = (compose R (up_ring.monom P a n) g) \<otimes>\<^bsub>P\<^esub> (compose R (up_ring.monom P \<one> 1) g)"
        using assms A by (metis R.one_closed monom_Suc(2) monom_closed sub_mult)
      have 1: "compose R (up_ring.monom P a (Suc n)) g = (compose R (up_ring.monom P a n) g) \<otimes>\<^bsub>P\<^esub> g"
        unfolding 0 using A assms 
        by (metis P_def R.one_closed UP_cring.lcf_monom(1) UP_cring.to_poly_inverse UP_cring_axioms UP_l_one UP_one_closed deg_one monom_one sub_monom_deg_one to_poly_mult_simp(1))
      have 2: "pderiv (compose R (up_ring.monom P a (Suc n)) g ) =
                    ((pderiv (compose R (up_ring.monom P a n) g)) \<otimes>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> ((compose R (up_ring.monom P a n) g) \<otimes>\<^bsub>P\<^esub> pderiv g)"
        unfolding 1 unfolding P_def apply(rule product_rule)
        using A assms unfolding P_def using P_def is_UP_monomE(1) is_UP_monomI rev_sub_closed sub_rev_sub apply presburger
        using assms unfolding P_def  by blast 
      have 3: "pderiv (compose R (up_ring.monom P a (Suc n)) g ) = 
                    (compose R (pderiv (up_ring.monom P a n)) g \<otimes>\<^bsub>UP R\<^esub> pderiv g \<otimes>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> ((compose R (up_ring.monom P a n) g) \<otimes>\<^bsub>P\<^esub> pderiv g)"
        unfolding 2 Suc by blast 
      have 4: "pderiv (compose R (up_ring.monom P a (Suc n)) g ) = 
                    ((compose R (pderiv (up_ring.monom P a n)) g  \<otimes>\<^bsub>P\<^esub> g) \<otimes>\<^bsub>UP R\<^esub> pderiv g) \<oplus>\<^bsub>P\<^esub> ((compose R (up_ring.monom P a n) g) \<otimes>\<^bsub>P\<^esub> pderiv g)"
        unfolding 3 using A assms m_assoc m_comm 
        by (smt P_def monom_closed monom_rep_X_pow pderiv_closed sub_closed)
      have 5: "pderiv (compose R (up_ring.monom P a (Suc n)) g ) = 
                    ((compose R (pderiv (up_ring.monom P a n)) g  \<otimes>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> (compose R (up_ring.monom P a n) g)) \<otimes>\<^bsub>P\<^esub> pderiv g"
        unfolding 4 using A assms 
        by (metis P.l_distr P.m_closed P_def UP_cring.pderiv_closed UP_cring_axioms monom_closed sub_closed)
      have 6: "compose R (pderiv (up_ring.monom P a n)) g  \<otimes>\<^bsub>P\<^esub> g = [n]\<cdot>\<^bsub>P\<^esub>compose R ((up_ring.monom P a n)) g"
      proof-
        have 60: "(pderiv (up_ring.monom P a n)) = (up_ring.monom P ([n]\<cdot>a) (n-1))" 
          using A assms pderiv_monom by blast
        have 61: "compose R (pderiv (up_ring.monom P a n)) g \<otimes>\<^bsub>P\<^esub> g  = compose R ((up_ring.monom P ([n]\<cdot>a) (n-1))) g \<otimes>\<^bsub>P\<^esub> (compose R (up_ring.monom P \<one> 1) g)"
          unfolding 60 using A assms sub_monom_deg_one[of g \<one> ] R.one_closed smult_one by presburger
        have 62: "compose R (pderiv (up_ring.monom P a n)) g  \<otimes>\<^bsub>P\<^esub> g = compose R (up_ring.monom P ([n]\<cdot>a) n) g"
          unfolding 61 using False A assms sub_mult[of g "up_ring.monom P ([n] \<cdot> a) (n - 1)" "up_ring.monom P \<one> 1" ] monom_mult[of "[n]\<cdot>a" \<one> "n-1" 1] 
          by (metis Nat.add_0_right R.add.nat_pow_closed R.one_closed R.r_one Suc_eq_plus1 add_eq_if monom_closed)
        have 63: "\<And>k::nat. Cring_Poly.compose R (up_ring.monom P ([k] \<cdot> a) n) g = [k] \<cdot>\<^bsub>P\<^esub>Cring_Poly.compose R (up_ring.monom P a n) g"
        proof- fix k::nat show "Cring_Poly.compose R (up_ring.monom P ([k] \<cdot> a) n) g = [k] \<cdot>\<^bsub>P\<^esub>Cring_Poly.compose R (up_ring.monom P a n) g"
            apply(induction k)
            using  UP_zero_closed assms(2) deg_zero monom_zero sub_const 
             apply (metis A P.add.nat_pow_0 add_nat_pow_monom)
          proof- 
            fix k::nat
            assume a: "Cring_Poly.compose R (monom P ([k] \<cdot> a) n) g =
         [k] \<cdot>\<^bsub>P\<^esub> Cring_Poly.compose R (monom P a n) g"
            have 0: "(monom P ([Suc k] \<cdot> a) n) = [Suc k] \<cdot> a \<odot>\<^bsub>P\<^esub>(monom P \<one> n)"
              by (simp add: A monic_monom_smult)
            have 1: "(monom P ([Suc k] \<cdot> a) n) = [k] \<cdot> a \<odot>\<^bsub>P\<^esub>(monom P \<one> n) \<oplus>\<^bsub>P\<^esub>a \<odot>\<^bsub>P\<^esub>(monom P \<one> n) "
              unfolding 0 
              by (simp add: A UP_smult_l_distr)
            show "Cring_Poly.compose R (monom P ([Suc k] \<cdot> a) n) g =
         [Suc k] \<cdot>\<^bsub>P\<^esub> (Cring_Poly.compose R (monom P a n) g) "
              unfolding 1 
              by (simp add: A a assms(2) monic_monom_smult sub_add)
          qed
        qed
        have 64: "Cring_Poly.compose R (up_ring.monom P ([n] \<cdot> a) n) g = [n] \<cdot>\<^bsub>P\<^esub>Cring_Poly.compose R (up_ring.monom P a n) g"
          using 63 by blast 
        show ?thesis unfolding 62 64 by blast 
      qed
      have 63: "\<And>k::nat. Cring_Poly.compose R (up_ring.monom P ([k] \<cdot> a) n) g = [k] \<cdot>\<^bsub>P\<^esub>Cring_Poly.compose R (up_ring.monom P a n) g"
      proof- fix k::nat show "Cring_Poly.compose R (up_ring.monom P ([k] \<cdot> a) n) g = [k] \<cdot>\<^bsub>P\<^esub>Cring_Poly.compose R (up_ring.monom P a n) g"
            apply(induction k)
            using UP_zero_closed assms(2) deg_zero monom_zero sub_const 
            apply (metis A P.add.nat_pow_0 add_nat_pow_monom)           
            using A P.add.nat_pow_Suc add_nat_pow_monom assms(2) is_UP_monomE(1) monom_is_UP_monom(1) rev_sub_add sub_rev_sub
            by (metis P.add.nat_pow_closed)            
      qed
      have 7: "([n] \<cdot>\<^bsub>P\<^esub> Cring_Poly.compose R (up_ring.monom P a n) g \<oplus>\<^bsub>P\<^esub> Cring_Poly.compose R (up_ring.monom P a n) g) = 
                                [Suc n] \<cdot>\<^bsub>P\<^esub> (Cring_Poly.compose R (up_ring.monom P a n) g)"
        using A assms P.add.nat_pow_Suc by presburger
      have 8: "[Suc n] \<cdot>\<^bsub>P\<^esub> Cring_Poly.compose R (up_ring.monom P a n) g \<otimes>\<^bsub>P\<^esub> pderiv g = Cring_Poly.compose R (up_ring.monom P ([Suc n] \<cdot> a) n) g \<otimes>\<^bsub>P\<^esub> pderiv g"
        unfolding  63[of "Suc n"] by blast 
      show ?thesis unfolding 5 6 7 8 using A assms pderiv_monom[of  "a" "Suc n"] 
        using P_def diff_Suc_1 by metis  
    qed
  qed
  qed
qed

lemma deriv_prod_rule_times_monom:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "q \<in> carrier P"
  shows "deriv ((monom P a n) \<otimes>\<^bsub>P\<^esub> q) b = (deriv (monom P a n) b) \<otimes> (to_fun q b) \<oplus> (to_fun (monom P a n) b) \<otimes> deriv q b"
proof(rule poly_induct3[of q])
  show "q \<in> carrier P"
    using assms by simp 
  show " \<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           deriv (monom P a n \<otimes>\<^bsub>P\<^esub> p) b = deriv (monom P a n) b \<otimes> to_fun p b \<oplus> to_fun (monom P a n) b \<otimes> deriv p b \<Longrightarrow>
           deriv (monom P a n \<otimes>\<^bsub>P\<^esub> q) b = deriv (monom P a n) b \<otimes> to_fun q b \<oplus> to_fun (monom P a n) b \<otimes> deriv q b \<Longrightarrow>
           deriv (monom P a n \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q)) b = deriv (monom P a n) b \<otimes> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b \<oplus> to_fun (monom P a n) b \<otimes> deriv (p \<oplus>\<^bsub>P\<^esub> q) b"
  proof- fix p q assume A: "q \<in> carrier P" " p \<in> carrier P"
          "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> p) b = deriv (monom P a n) b \<otimes> to_fun p b \<oplus> to_fun (monom P a n) b \<otimes> deriv p b"
          "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> q) b = deriv (monom P a n) b \<otimes> to_fun q b \<oplus> to_fun (monom P a n) b \<otimes> deriv q b"
    have "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q)) b =  deriv (monom P a n) b \<otimes> to_fun p b \<oplus> to_fun (monom P a n) b \<otimes> deriv p b
                                                  \<oplus>deriv (monom P a n) b \<otimes> to_fun q b \<oplus> to_fun (monom P a n) b \<otimes> deriv q b"
      using A assms 
      by (simp add: P.r_distr R.add.m_assoc deriv_add deriv_closed to_fun_closed)    
    hence "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q)) b =  deriv (monom P a n) b \<otimes> to_fun p b \<oplus>deriv (monom P a n) b \<otimes> to_fun q b 
              \<oplus> to_fun (monom P a n) b \<otimes> deriv p b  \<oplus> to_fun (monom P a n) b \<otimes> deriv q b"
      using A(1) A(2) R.add.m_assoc R.add.m_comm assms(1) assms(2) deriv_closed to_fun_closed by auto
    hence "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q)) b =  deriv (monom P a n) b \<otimes> (to_fun p b \<oplus>  to_fun q b)
              \<oplus> to_fun (monom P a n) b \<otimes> (deriv p b  \<oplus> deriv q b)"
      by (simp add: A(1) A(2) R.add.m_assoc R.r_distr assms(1) assms(2) deriv_closed to_fun_closed)
    thus "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q)) b = deriv (monom P a n) b \<otimes> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b \<oplus> to_fun (monom P a n) b \<otimes> deriv (p \<oplus>\<^bsub>P\<^esub> q) b"
      by (simp add: A(1) A(2) assms(2) deriv_add to_fun_plus)
  qed
  show "\<And>c m. c \<in> carrier R \<Longrightarrow>  deriv (monom P a n \<otimes>\<^bsub>P\<^esub> monom P c m) b = 
                                    deriv (monom P a n) b \<otimes> to_fun (monom P c m) b 
                                  \<oplus> to_fun (monom P a n) b \<otimes> deriv (monom P c m) b"
  proof- fix c m assume A: "c \<in> carrier R"
    show "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> monom P c m) b = deriv (monom P a n) b \<otimes> to_fun (monom P c m) b \<oplus> to_fun (monom P a n) b \<otimes> deriv (monom P c m) b"
    proof(cases "n = 0")
      case True
      have LHS: "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> monom P c m) b = deriv (monom P (a \<otimes> c) m) b"
        by (metis A True add.left_neutral assms(1) monom_mult)
      have RHS: "deriv (monom P a n) b \<otimes> to_fun (monom P c m) b \<oplus> to_fun (monom P a n) b \<otimes> deriv (monom P c m) b 
                = a \<otimes> deriv (monom P c m) b "
        using deriv_const to_fun_monom A True assms(1) assms(2) deriv_closed by auto
      show ?thesis using A assms  LHS RHS deriv_monom 
        by (smt R.add.nat_pow_closed R.add_pow_rdistr R.m_assoc R.m_closed R.nat_pow_closed)
    next
      case False
      show ?thesis 
      proof(cases "m = 0")
        case True
        have LHS: "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> monom P c m) b = deriv (monom P (a \<otimes> c) n) b"
          by (metis A True add.comm_neutral assms(1) monom_mult)
        have RHS: "deriv (monom P a n) b \<otimes> to_fun (monom P c m) b \<oplus> to_fun (monom P a n) b \<otimes> deriv (monom P c m) b 
                = c \<otimes> deriv (monom P a n) b "
          by (metis (no_types, lifting) A lcf_monom(1) P_def R.m_closed R.m_comm R.r_null
              R.r_zero True UP_cring.to_fun_ctrm UP_cring_axioms assms(1) assms(2) deg_const 
              deriv_closed deriv_const to_fun_closed monom_closed)
        show ?thesis using LHS RHS deriv_monom A assms 
          by (smt R.add.nat_pow_closed R.add_pow_ldistr R.m_assoc R.m_closed R.m_comm R.nat_pow_closed)
      next
        case F: False
        have pos: "n > 0" "m >0"
          using F False by auto 
        have RHS: "deriv (monom P a n \<otimes>\<^bsub>P\<^esub> monom P c m) b = [(n + m)] \<cdot> (a \<otimes> c) \<otimes> b [^] (n + m - 1)"
          using deriv_monom[of "a \<otimes> c" b "n + m"] monom_mult[of a c n m]  
          by (simp add: A assms(1) assms(2))
        have LHS: "deriv (monom P a n) b \<otimes> to_fun (monom P c m) b  \<oplus> to_fun (monom P a n) b \<otimes> deriv (monom P c m) b
                    = [n]\<cdot>a \<otimes>(b[^](n-1)) \<otimes> c \<otimes> b[^]m \<oplus>  a \<otimes> b[^]n  \<otimes>  [m]\<cdot>c \<otimes>(b[^](m-1))"
          using deriv_monom[of a b n] to_fun_monom[of a b n] 
            deriv_monom[of c b m] to_fun_monom[of c b m] A assms 
          by (simp add: R.m_assoc)
        have 0: "[n]\<cdot>a \<otimes> (b[^](n-1)) \<otimes> c \<otimes> b[^]m = [n]\<cdot>a \<otimes> c \<otimes> b[^](n + m -1) "
        proof-
          have "[n]\<cdot>a \<otimes> (b[^](n-1)) \<otimes> c \<otimes> b[^]m = [n]\<cdot>a  \<otimes> c \<otimes> (b[^](n-1)) \<otimes> b[^]m"
            by (simp add: A R.m_lcomm R.semiring_axioms assms(1) assms(2) semiring.semiring_simprules(8))
          hence "[n]\<cdot>a \<otimes> (b[^](n-1)) \<otimes> c \<otimes> b[^]m = [n]\<cdot>a  \<otimes> c \<otimes> ((b[^](n-1)) \<otimes> b[^]m)"
            by (simp add: A R.m_assoc assms(1) assms(2))
          thus ?thesis 
            by (simp add: False R.nat_pow_mult add_eq_if assms(2))
        qed
        have 1: "a \<otimes> b[^]n  \<otimes>  [m]\<cdot>c \<otimes>(b[^](m-1)) = a \<otimes> [m]\<cdot>c \<otimes> b[^](n + m -1)" 
        proof-
          have "a \<otimes> b[^]n  \<otimes>  [m]\<cdot>c \<otimes>(b[^](m-1)) = a \<otimes>  [m]\<cdot>c \<otimes> b[^]n  \<otimes>(b[^](m-1))"
            using A R.m_comm R.m_lcomm assms(1) assms(2) by auto
          hence "a \<otimes> b[^]n  \<otimes>  [m]\<cdot>c \<otimes>(b[^](m-1)) = a \<otimes>  [m]\<cdot>c \<otimes> (b[^]n  \<otimes>(b[^](m-1)))"
            by (simp add: A R.m_assoc assms(1) assms(2))
          thus ?thesis 
            by (simp add: F R.nat_pow_mult add.commute add_eq_if assms(2))
        qed
        have LHS: "deriv (monom P a n) b \<otimes> to_fun (monom P c m) b  \<oplus> to_fun (monom P a n) b \<otimes> deriv (monom P c m) b
                    = [n]\<cdot>a \<otimes> c \<otimes> b[^](n + m -1)  \<oplus>  a \<otimes> [m]\<cdot>c \<otimes> b[^](n + m -1)"      
          using LHS 0 1 
          by simp
        hence LHS: "deriv (monom P a n) b \<otimes> to_fun (monom P c m) b  \<oplus> to_fun (monom P a n) b \<otimes> deriv (monom P c m) b
                    = [n]\<cdot> (a \<otimes> c \<otimes> b[^](n + m -1))  \<oplus>  [m]\<cdot> (a \<otimes> c \<otimes> b[^](n + m -1))"                
          by (simp add: A R.add_pow_ldistr R.add_pow_rdistr assms(1) assms(2))
        show ?thesis using LHS RHS 
          by (simp add: A R.add.nat_pow_mult R.add_pow_ldistr assms(1) assms(2))
      qed
    qed
  qed
qed
               
lemma deriv_prod_rule:
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "deriv (p \<otimes>\<^bsub>P\<^esub> q) a = deriv p a \<otimes> (to_fun q a) \<oplus> (to_fun p a) \<otimes> deriv q a"
proof(rule poly_induct3[of p])
  show "p \<in> carrier P"
    using assms(1) by simp 
  show " \<And>p qa.
       qa \<in> carrier P \<Longrightarrow>
       p \<in> carrier P \<Longrightarrow>
       deriv (p \<otimes>\<^bsub>P\<^esub> q) a = deriv p a \<otimes> to_fun q a \<oplus> to_fun p a \<otimes> deriv q a \<Longrightarrow>
       deriv (qa \<otimes>\<^bsub>P\<^esub> q) a = deriv qa a \<otimes> to_fun q a \<oplus> to_fun qa a \<otimes> deriv q a \<Longrightarrow>
       deriv ((p \<oplus>\<^bsub>P\<^esub> qa) \<otimes>\<^bsub>P\<^esub> q) a = deriv (p \<oplus>\<^bsub>P\<^esub> qa) a \<otimes> to_fun q a \<oplus> to_fun (p \<oplus>\<^bsub>P\<^esub> qa) a \<otimes> deriv q a"
  proof- fix f g assume A: "f \<in> carrier P" "g \<in> carrier P"
                  "deriv (f \<otimes>\<^bsub>P\<^esub> q) a = deriv f a \<otimes> to_fun q a \<oplus> to_fun f a \<otimes> deriv q a"
                  "deriv (g \<otimes>\<^bsub>P\<^esub> q) a = deriv g a \<otimes> to_fun q a \<oplus> to_fun g a \<otimes> deriv q a"
    have "deriv ((f \<oplus>\<^bsub>P\<^esub> g) \<otimes>\<^bsub>P\<^esub> q) a = deriv f a \<otimes> to_fun q a \<oplus> to_fun f a \<otimes> deriv q a \<oplus>
                                         deriv g a \<otimes> to_fun q a \<oplus> to_fun g a \<otimes> deriv q a"
      using A deriv_add 
      by (simp add: P.l_distr R.add.m_assoc assms(2) assms(3) deriv_closed to_fun_closed)
    hence "deriv ((f \<oplus>\<^bsub>P\<^esub> g) \<otimes>\<^bsub>P\<^esub> q) a = deriv f a \<otimes> to_fun q a \<oplus> deriv g a \<otimes> to_fun q a \<oplus> 
                                       to_fun f a \<otimes> deriv q a \<oplus>  to_fun g a \<otimes> deriv q a"
      using R.a_comm R.a_assoc deriv_closed to_fun_closed assms 
      by (simp add: A(1) A(2))      
    hence "deriv ((f \<oplus>\<^bsub>P\<^esub> g) \<otimes>\<^bsub>P\<^esub> q) a = (deriv f a \<otimes> to_fun q a \<oplus> deriv g a \<otimes> to_fun q a) \<oplus> 
                                         (to_fun f a \<otimes> deriv q a \<oplus>  to_fun g a \<otimes> deriv q a)"
      by (simp add: A(1) A(2) R.add.m_assoc assms(2) assms(3) deriv_closed to_fun_closed)
    thus "deriv ((f \<oplus>\<^bsub>P\<^esub> g) \<otimes>\<^bsub>P\<^esub> q) a = deriv (f \<oplus>\<^bsub>P\<^esub> g) a \<otimes> to_fun q a \<oplus> to_fun (f \<oplus>\<^bsub>P\<^esub> g) a \<otimes> deriv q a"
      by (simp add: A(1) A(2) R.l_distr assms(2) assms(3) deriv_add deriv_closed to_fun_closed to_fun_plus)
  qed
  show "\<And>aa n. aa \<in> carrier R \<Longrightarrow> deriv (monom P aa n \<otimes>\<^bsub>P\<^esub> q) a = deriv (monom P aa n) a \<otimes> to_fun q a \<oplus> to_fun (monom P aa n) a \<otimes> deriv q a"
    using deriv_prod_rule_times_monom 
    by (simp add: assms(2) assms(3))
qed

lemma pderiv_eval_deriv_monom:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "to_fun (pderiv (monom P a n)) b = deriv (monom P a n) b"
  using deriv_monom assms pderiv_monom  
  by (simp add: P_def UP_cring.to_fun_monom UP_cring_axioms)

lemma pderiv_eval_deriv:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "deriv f a = to_fun (pderiv f) a"
  apply(rule poly_induct3[of f])
  apply (simp add: assms(1))
    using assms(2) deriv_add to_fun_plus pderiv_add pderiv_closed apply presburger
      using assms(2) pderiv_eval_deriv_monom 
  by presburger

text\<open>Taking taylor expansions commutes with taking derivatives:\<close>

lemma(in UP_cring) taylor_expansion_pderiv_comm:
  assumes "f \<in> carrier (UP R)"
  assumes "c \<in> carrier R"
  shows "pderiv (taylor_expansion R c f) = taylor_expansion R c (pderiv f)"
  apply(rule poly_induct3[of f])
  using assms unfolding P_def  apply blast
proof-
  fix p q assume A: " q \<in> carrier (UP R)" "p \<in> carrier (UP R)"
           "pderiv (taylor_expansion R c p) = taylor_expansion R c (pderiv p)"
           "pderiv (taylor_expansion R c q) = taylor_expansion R c (pderiv q)"
  have 0: " pderiv (taylor_expansion R c (p \<oplus>\<^bsub>UP R\<^esub> q)) =  pderiv (taylor_expansion R c p \<oplus>\<^bsub>UP R\<^esub> taylor_expansion R c q)"
    using A P_def taylor_expansion_add assms(2) by presburger
  show "pderiv (taylor_expansion R c (p \<oplus>\<^bsub>UP R\<^esub> q)) = taylor_expansion R c (pderiv (p \<oplus>\<^bsub>UP R\<^esub> q))"
    unfolding 0
    using A(1) A(2) A(3) A(4) taylor_def UP_cring.taylor_closed UP_cring.taylor_expansion_add UP_cring.pderiv_add UP_cring.pderiv_closed UP_cring_axioms assms(2) by fastforce
next
  fix a n assume A: "a \<in> carrier R"
  show "pderiv (taylor_expansion R c (up_ring.monom (UP R) a n)) = taylor_expansion R c (pderiv (up_ring.monom (UP R) a n))"
  proof(cases "n = 0")
    case True
    have 0: "deg R (taylor_expansion R c (up_ring.monom (UP R) a n)) = 0"
      unfolding True 
      using P_def A assms taylor_def taylor_deg deg_const is_UP_monomE(1) monom_is_UP_monom(2) by presburger
    have 1: "(pderiv (up_ring.monom (UP R) a n)) = \<zero>\<^bsub>P\<^esub>"
      unfolding True using P_def A assms pderiv_const by blast
    show ?thesis unfolding 1 using 0 A assms P_def 
      by (metis P.add.right_cancel taylor_closed taylor_def taylor_expansion_add UP_l_zero UP_zero_closed monom_closed pderiv_deg_0)
  next
    case False
    have 0: "pderiv (up_ring.monom (UP R) a n) =  (up_ring.monom (UP R) ([n]\<cdot>a) (n-1))"
      using A  
      by (simp add: UP_cring.pderiv_monom UP_cring_axioms)      
    have 1: "pderiv (taylor_expansion R c (up_ring.monom (UP R) a n)) = (Cring_Poly.compose R (up_ring.monom (UP R) ([n]\<cdot>a) (n-1)) (X_plus c)) \<otimes>\<^bsub>P\<^esub> pderiv (X_plus c)"
      using chain_rule[of "up_ring.monom (UP R) a n" "X_plus c"] unfolding 0 taylor_expansion_def
      using A P_def X_plus_closed assms(2) is_UP_monom_def monom_is_UP_monom(1) by presburger
    have 2: "pderiv (X_plus c) = \<one>\<^bsub>P\<^esub>"
      using pderiv_add[of "X_poly R" "to_poly c"]  P.l_null P.l_one P.r_zero P_def R.one_closed  X_closed 
        X_poly_def X_poly_plus_def assms(2) monom_one pderiv_const to_poly_closed to_polynomial_def
      by (metis times_x_product_rule)
      show ?thesis unfolding 1 0 2 taylor_expansion_def
        by (metis "1" "2" A P.l_one P_def R.add.nat_pow_closed UP_m_comm UP_one_closed X_plus_closed assms(2) monom_closed sub_closed taylor_expansion_def)      
  qed
qed

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Linear Substitutions\<close>
  (**********************************************************************)
  (**********************************************************************)
lemma(in UP_ring) lcoeff_Lcf:
  assumes "f \<in> carrier P"
  shows "lcoeff f = lcf f"
  unfolding P_def
  using assms  coeff_simp[of f] by metis

lemma(in UP_cring) linear_sub_cfs:
  assumes "f \<in> carrier (UP R)"
  assumes "d \<in> carrier R"
  assumes "g = compose R f (up_ring.monom (UP R) d 1)"
  shows "g i = d[^]i \<otimes> f i"
proof-
  have 0: "(up_ring.monom (UP R) d 1) \<in> carrier (UP R)"
    using assms by (meson R.ring_axioms UP_ring.intro UP_ring.monom_closed)
  have 1: "(\<forall>i. compose R f (up_ring.monom (UP R) d 1) i = d[^]i \<otimes> f i)"
    apply(rule poly_induct3[of f])
    using assms unfolding P_def apply blast
  proof-
    show "\<And>p q. q \<in> carrier (UP R) \<Longrightarrow>
           p \<in> carrier (UP R) \<Longrightarrow>
           \<forall>i. Cring_Poly.compose R p (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> p i \<Longrightarrow>
           \<forall>i. Cring_Poly.compose R q (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> q i \<Longrightarrow>
           \<forall>i. Cring_Poly.compose R (p \<oplus>\<^bsub>UP R\<^esub> q) (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> (p \<oplus>\<^bsub>UP R\<^esub> q) i"
    proof 
    fix p q i
    assume A: "q \<in> carrier (UP R)"
           "p \<in> carrier (UP R)"
           "\<forall>i. Cring_Poly.compose R p (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> p i"
           "\<forall>i. Cring_Poly.compose R q (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> q i"
    show "Cring_Poly.compose R (p \<oplus>\<^bsub>UP R\<^esub> q) (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> (p \<oplus>\<^bsub>UP R\<^esub> q) i"
    proof- 
      have 1: "Cring_Poly.compose R (p \<oplus>\<^bsub>UP R\<^esub> q) (up_ring.monom (UP R) d 1) = 
              Cring_Poly.compose R p (up_ring.monom (UP R) d 1) \<oplus>\<^bsub>UP R\<^esub> Cring_Poly.compose R q (up_ring.monom (UP R) d 1)"
        using A(1) A(2) sub_add[of "up_ring.monom (UP R) d 1" q p] unfolding P_def 
        using "0" P_def sub_add by blast
      have 2: "Cring_Poly.compose R (p \<oplus>\<^bsub>UP R\<^esub> q) (up_ring.monom (UP R) d 1) i = 
              Cring_Poly.compose R p (up_ring.monom (UP R) d 1) i \<oplus> Cring_Poly.compose R q (up_ring.monom (UP R) d 1) i"
        using 1 by (metis (no_types, lifting) "0" A(1) A(2) P_def cfs_add sub_closed)
      have 3: "Cring_Poly.compose R (p \<oplus>\<^bsub>UP R\<^esub> q) (up_ring.monom (UP R) d 1) i =   d [^] i \<otimes> p i \<oplus> d [^] i \<otimes> q i"
        unfolding 2 using A by presburger
      have 4: "Cring_Poly.compose R (p \<oplus>\<^bsub>UP R\<^esub> q) (up_ring.monom (UP R) d 1) i =   d [^] i \<otimes> (p i \<oplus>  q i)"
        using "3" A(1) A(2) R.nat_pow_closed R.r_distr UP_car_memE(1) assms(2) by presburger
      thus "Cring_Poly.compose R (p \<oplus>\<^bsub>UP R\<^esub> q) (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> (p \<oplus>\<^bsub>UP R\<^esub> q) i"
        unfolding 4  using A(1) A(2) P_def cfs_add by presburger
    qed
  qed
  show "\<And>a n. a \<in> carrier R \<Longrightarrow>
           \<forall>i. Cring_Poly.compose R (up_ring.monom (UP R) a n) (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> up_ring.monom (UP R) a n i"
  proof fix a n i assume A: "a \<in> carrier R"
    have 0: "Cring_Poly.compose R (up_ring.monom (UP R) a n) (up_ring.monom (UP R) d 1)  = 
                         a \<odot>\<^bsub>UP R\<^esub>(up_ring.monom (UP R) d 1)[^]\<^bsub>UP R\<^esub>n"
      using assms A 0 P_def monom_sub by blast
    have 1: "Cring_Poly.compose R (up_ring.monom (UP R) a n) (up_ring.monom (UP R) d 1)  = 
                         a \<odot>\<^bsub>UP R\<^esub> (d[^]n \<odot>\<^bsub>UP R\<^esub>(up_ring.monom (UP R) \<one> n))"
      unfolding  0 using A assms 
      by (metis P_def R.nat_pow_closed monic_monom_smult monom_pow mult.left_neutral)
    have 2: "Cring_Poly.compose R (up_ring.monom (UP R) a n) (up_ring.monom (UP R) d 1)  = 
                         (a \<otimes>d[^]n)\<odot>\<^bsub>UP R\<^esub>(up_ring.monom (UP R) \<one> n)"
      unfolding 1 using A assms  
      by (metis R.nat_pow_closed R.one_closed R.ring_axioms UP_ring.UP_smult_assoc1 UP_ring.intro UP_ring.monom_closed)
    show "Cring_Poly.compose R (up_ring.monom (UP R) a n) (up_ring.monom (UP R) d 1) i = d [^] i \<otimes> up_ring.monom (UP R) a n i"
      apply(cases "i = n")
      unfolding 2 using A P_def R.m_closed R.m_comm R.nat_pow_closed assms(2) cfs_monom monic_monom_smult apply presburger
      using A P_def R.m_closed R.nat_pow_closed R.r_null assms(2) cfs_monom monic_monom_smult by presburger
  qed
  qed
  show ?thesis using 1 unfolding assms   
    by blast 
qed

lemma(in UP_cring) linear_sub_deriv: 
  assumes "f \<in> carrier (UP R)"
  assumes "d \<in> carrier R"
  assumes "g = compose R f (up_ring.monom (UP R) d 1)"
  assumes "c \<in> carrier R"
  shows "pderiv g = d \<odot>\<^bsub>UP R\<^esub> compose R (pderiv f) (up_ring.monom (UP R) d 1)"
  unfolding assms 
proof(rule  poly_induct3[of f])
  show "f \<in> carrier P"
    using assms unfolding P_def  by blast
  show "\<And> p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           pderiv (Cring_Poly.compose R p (up_ring.monom (UP R) d 1)) = d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv p) (up_ring.monom (UP R) d 1) \<Longrightarrow>
           pderiv (Cring_Poly.compose R q (up_ring.monom (UP R) d 1)) = d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv q) (up_ring.monom (UP R) d 1) \<Longrightarrow>
           pderiv (Cring_Poly.compose R (p \<oplus>\<^bsub>P\<^esub> q) (up_ring.monom (UP R) d 1)) =
           d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv (p \<oplus>\<^bsub>P\<^esub> q)) (up_ring.monom (UP R) d 1)"
  proof- fix p q assume A: "q \<in> carrier P" "p \<in> carrier P"
           "pderiv (Cring_Poly.compose R p (up_ring.monom (UP R) d 1)) = d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv p) (up_ring.monom (UP R) d 1)"
           "pderiv (Cring_Poly.compose R q (up_ring.monom (UP R) d 1)) = d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv q) (up_ring.monom (UP R) d 1)"
    show " pderiv (Cring_Poly.compose R (p \<oplus>\<^bsub>P\<^esub> q) (up_ring.monom (UP R) d 1)) =
           d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv (p \<oplus>\<^bsub>P\<^esub> q)) (up_ring.monom (UP R) d 1)"
      using A assms 
      by (smt P_def UP_a_closed UP_r_distr monom_closed monom_mult_is_smult pderiv_add pderiv_closed rev_sub_add sub_closed sub_rev_sub)
  qed
  show "\<And>a n. a \<in> carrier R \<Longrightarrow>
           pderiv (Cring_Poly.compose R (up_ring.monom P a n) (up_ring.monom (UP R) d 1)) =
           d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv (up_ring.monom P a n)) (up_ring.monom (UP R) d 1)"
  proof- fix a n assume A: "a \<in> carrier R"
    have "(Cring_Poly.compose R (up_ring.monom P a n) (up_ring.monom (UP R) d 1)) = a \<odot>\<^bsub>UP R\<^esub> (up_ring.monom P d 1)[^]\<^bsub>UP R\<^esub> n"
      using A assms sub_monom(2)  P_def is_UP_monomE(1) monom_is_UP_monom(1) by blast
    hence 0: "(Cring_Poly.compose R (up_ring.monom P a n) (up_ring.monom (UP R) d 1)) = a \<odot>\<^bsub>UP R\<^esub> (up_ring.monom P (d[^]n) n)"
      using A assms P_def monom_pow nat_mult_1 by metis 
    show "pderiv (Cring_Poly.compose R (up_ring.monom P a n) (up_ring.monom (UP R) d 1)) =
           d \<odot>\<^bsub>UP R\<^esub> Cring_Poly.compose R (pderiv (up_ring.monom P a n)) (up_ring.monom (UP R) d 1)"
    proof(cases  "n = 0")
      case True
      have T0: "pderiv (up_ring.monom P a n) = \<zero>\<^bsub> UP R\<^esub>" unfolding True 
        using A P_def pderiv_const by blast
      have T1: "(Cring_Poly.compose R (up_ring.monom P a n) (up_ring.monom (UP R) d 1)) = up_ring.monom P a n"
        unfolding True 
        using A assms  P_def deg_const is_UP_monomE(1) monom_is_UP_monom(1) sub_const by presburger
      thus ?thesis unfolding T0 T1  
        by (metis P.nat_pow_eone P_def UP_smult_closed UP_zero_closed X_closed assms(2) deg_zero monom_rep_X_pow smult_r_null sub_const)
    next
      case False
      have F0: "pderiv (Cring_Poly.compose R (up_ring.monom P a n) (up_ring.monom (UP R) d 1)) = (a \<odot>\<^bsub>UP R\<^esub> (up_ring.monom P ([n]\<cdot>\<^bsub>R\<^esub>(d[^]n))(n-1)))"
        using A assms pderiv_monom unfolding 0 
        using P_def R.nat_pow_closed is_UP_monomE(1) monom_is_UP_monom(1) pderiv_smult by metis 
      have F1: "(pderiv (up_ring.monom P a n)) = up_ring.monom P ([n] \<cdot> a) (n - 1)"
        using A assms pderiv_monom[of a n] by blast 
      hence F2: "(pderiv (up_ring.monom P a n)) = ([n] \<cdot> a) \<odot>\<^bsub>UP R\<^esub>up_ring.monom P \<one> (n - 1)"
        using A P_def monic_monom_smult by auto        
      have F3: "Cring_Poly.compose R ((([n] \<cdot> a) \<odot>\<^bsub>UP R\<^esub> (up_ring.monom P \<one> (n - 1)))) (up_ring.monom (UP R) d 1) = 
                ([n] \<cdot> a) \<odot>\<^bsub>UP R\<^esub> ((up_ring.monom (UP R) d 1)[^]\<^bsub>UP R\<^esub>(n-1))"
        using A F1 F2 P_def assms(2) monom_closed sub_monom(2) by fastforce
      have F4: "Cring_Poly.compose R ((([n] \<cdot> a) \<odot>\<^bsub>UP R\<^esub> (up_ring.monom P \<one> (n - 1)))) (up_ring.monom (UP R) d 1) =
                ([n] \<cdot> a) \<odot>\<^bsub>UP R\<^esub> ((up_ring.monom (UP R) (d[^](n-1)) (n-1)))"
        by (metis F3 P_def assms(2) monom_pow nat_mult_1)
      have F5: "d \<odot>\<^bsub>UP R\<^esub> (Cring_Poly.compose R (pderiv (up_ring.monom P a n)) (up_ring.monom (UP R) d 1)) = 
                (d \<otimes>([n] \<cdot> a)) \<odot>\<^bsub>UP R\<^esub> up_ring.monom (UP R) (d [^] (n - 1)) (n - 1)"
        unfolding F4 F2 
        using A P_def assms(2) monom_closed smult_assoc1 by auto       
      have F6: "d \<odot>\<^bsub>UP R\<^esub> (Cring_Poly.compose R (pderiv (up_ring.monom P a n)) (up_ring.monom (UP R) d 1)) = 
                (d \<otimes> d[^](n-1) \<otimes>[n] \<cdot> a) \<odot>\<^bsub>UP R\<^esub> ((up_ring.monom (UP R) \<one> (n-1)))"
        unfolding F5 using False A  assms P_def  R.m_assoc R.m_closed R.m_comm R.nat_pow_closed monic_monom_smult monom_mult_smult
        by (smt R.add.nat_pow_closed)        
      have F7: "pderiv (Cring_Poly.compose R (up_ring.monom P a n) (up_ring.monom (UP R) d 1)) = (a \<otimes> ([n]\<cdot>\<^bsub>R\<^esub>(d[^]n)) \<odot>\<^bsub>UP R\<^esub> (up_ring.monom P \<one> (n-1)))"
        unfolding F0 using A assms  P_def  R.m_closed R.nat_pow_closed monic_monom_smult monom_mult_smult
        by simp
      have F8: "a \<otimes> [n] \<cdot> (d [^] n)  = d \<otimes> d [^] (n - 1) \<otimes> [n] \<cdot> a"
      proof-
        have F80: "d \<otimes> d [^] (n - 1) \<otimes> [n] \<cdot> a = d [^] n \<otimes> [n] \<cdot> a"
          using A assms  False by (metis R.nat_pow_Suc2 add.right_neutral add_eq_if)
        show ?thesis unfolding F80 
          using A R.add_pow_rdistr R.m_comm R.nat_pow_closed assms(2) by presburger
      qed
      show ?thesis unfolding F6 F7 unfolding  F8 P_def by blast  
    qed
  qed
qed

lemma(in UP_cring) linear_sub_deriv': 
  assumes "f \<in> carrier (UP R)"
  assumes "d \<in> carrier R"
  assumes "g = compose R f (up_ring.monom (UP R) d 1)"
  assumes "c \<in> carrier R"
  shows "pderiv g = compose R (d \<odot>\<^bsub>UP R\<^esub> pderiv f) (up_ring.monom (UP R) d 1)"
  using assms linear_sub_deriv[of f d g c] P_def is_UP_monomE(1) is_UP_monomI pderiv_closed sub_smult by metis 

lemma(in UP_cring) linear_sub_inv:
  assumes "f \<in> carrier (UP R)"
  assumes "d \<in> Units R"
  assumes "g = compose R f (up_ring.monom (UP R) d 1)"
  shows "compose R g (up_ring.monom (UP R) (inv d) 1) = f"
  unfolding assms 
proof fix x 
  have 0: "Cring_Poly.compose R (Cring_Poly.compose R f (up_ring.monom (UP R) d 1)) (up_ring.monom (UP R) (inv d) 1) x = 
        (inv d)[^]x \<otimes> ((Cring_Poly.compose R f (up_ring.monom (UP R) d 1)) x)"
    apply(rule linear_sub_cfs) 
    using P_def R.Units_closed assms(1) assms(2) monom_closed sub_closed apply auto[1]
     apply (simp add: assms(2))
    by blast
  show "Cring_Poly.compose R (Cring_Poly.compose R f (up_ring.monom (UP R) d 1)) (up_ring.monom (UP R) (inv d) 1) x = f x "
    unfolding 0 using linear_sub_cfs[of f d "Cring_Poly.compose R f (up_ring.monom (UP R) d 1)" x]
      assms 
  by (smt R.Units_closed R.Units_inv_closed R.Units_l_inv R.m_assoc R.m_comm R.nat_pow_closed R.nat_pow_distrib R.nat_pow_one R.r_one UP_car_memE(1))
qed

lemma(in UP_cring) linear_sub_deg: 
  assumes "f \<in> carrier (UP R)"
  assumes "d \<in> Units R"
  assumes "g = compose R f (up_ring.monom (UP R) d 1)"
  shows "deg R g = deg R f"
proof(cases "deg R f = 0")
  case True
  show ?thesis using assms 
    unfolding True assms using P_def True monom_closed 
    by (simp add: R.Units_closed sub_const)    
next
  case False
  have 0: "monom (UP R) d 1 (deg R (monom (UP R) d 1)) = d"
    using assms  lcf_monom(2) by blast
  have 1: "d[^](deg R f) \<in> Units R" 
    using assms(2)
    by (metis Group.comm_monoid.axioms(1) R.units_comm_group R.units_of_pow comm_group_def monoid.nat_pow_closed units_of_carrier)
  have 2: "f (deg R f) \<noteq> \<zero>"
    using assms False P_def UP_cring.ltrm_rep_X_pow UP_cring_axioms deg_ltrm degree_monom by fastforce
  have "deg R g = deg R f * deg R (up_ring.monom (UP R) d 1)" 
    unfolding assms 
    apply(rule cring_sub_deg[of "up_ring.monom (UP R) d 1" f] )
    using assms P_def monom_closed apply blast
    unfolding P_def apply(rule assms)
    unfolding 0 using 2 1 
    by (metis R.Units_closed R.Units_l_cancel R.m_comm R.r_null R.zero_closed UP_car_memE(1) assms(1))  
  thus ?thesis using assms  unfolding assms
    by (metis (no_types, lifting) P_def R.Units_closed deg_monom deg_zero is_UP_monomE(1) linear_sub_inv monom_is_UP_monom(2) monom_zero mult.right_neutral mult_0_right sub_closed sub_const)
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Lemmas About Polynomial Division\<close>
(**************************************************************************************************)
(**************************************************************************************************)
context UP_cring
begin

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Division by Linear Terms\<close>
  (**********************************************************************)
  (**********************************************************************)
definition UP_root_div where
"UP_root_div f a =  (poly_shift (T\<^bsub>a\<^esub> f)) of (X_minus a)"

definition UP_root_rem where
"UP_root_rem f a = ctrm (T\<^bsub>a\<^esub> f)"

lemma UP_root_div_closed:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "UP_root_div f a \<in> carrier P"
  using assms 
  unfolding UP_root_div_def
  by (simp add: taylor_closed X_minus_closed poly_shift_closed sub_closed)

lemma rem_closed:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "UP_root_rem f a \<in> carrier P"
  using assms 
  unfolding UP_root_rem_def
  by (simp add: taylor_closed ctrm_is_poly) 

lemma rem_deg:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "degree (UP_root_rem f a) = 0"
  by (simp add: taylor_closed assms(1) assms(2) ctrm_degree UP_root_rem_def)

lemma remainder_theorem:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "g = UP_root_div f a"
  assumes "r = UP_root_rem f a"
  shows "f = r \<oplus>\<^bsub>P\<^esub> (X_minus a) \<otimes>\<^bsub>P\<^esub> g"
proof-
  have  "T\<^bsub>a\<^esub>f = (ctrm (T\<^bsub>a\<^esub>f)) \<oplus>\<^bsub>P\<^esub> X \<otimes>\<^bsub>P\<^esub> poly_shift (T\<^bsub>a\<^esub>f)"
    using poly_shift_eq[of "T\<^bsub>a\<^esub>f"] assms taylor_closed 
    by blast     
  hence 1: "T\<^bsub>a\<^esub>f of (X_minus a) = (ctrm (T\<^bsub>a\<^esub>f)) \<oplus>\<^bsub>P\<^esub> (X_minus a) \<otimes>\<^bsub>P\<^esub> (poly_shift (T\<^bsub>a\<^esub>f) of (X_minus a))"
    using assms taylor_closed[of f a] X_minus_closed[of a] X_closed 
          sub_add[of "X_minus a" "ctrm (T\<^bsub>a\<^esub>f)" "X \<otimes>\<^bsub>P\<^esub> poly_shift (T\<^bsub>a\<^esub>f)"] 
          sub_const[of "X_minus a"]  sub_mult[of "X_minus a" X  "poly_shift (T\<^bsub>a\<^esub>f)"] 
          ctrm_degree ctrm_is_poly P.m_closed poly_shift_closed sub_X 
    by presburger
  have 2: "f = (ctrm (T\<^bsub>a\<^esub>f)) \<oplus>\<^bsub>P\<^esub> (X_minus a) \<otimes>\<^bsub>P\<^esub> (poly_shift (T\<^bsub>a\<^esub>f) of (X_minus a))"
    using 1 taylor_id[of a f] assms 
    by simp 
  then show ?thesis
    using assms
    unfolding UP_root_div_def UP_root_rem_def
    by auto 
qed

lemma remainder_theorem':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "f = UP_root_rem f a \<oplus>\<^bsub>P\<^esub> (X_minus a) \<otimes>\<^bsub>P\<^esub> UP_root_div f a"
  using assms remainder_theorem by auto 

lemma factor_theorem:
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "g = UP_root_div f a"
  assumes "to_fun f a = \<zero>"
  shows "f = (X_minus a) \<otimes>\<^bsub>P\<^esub> g"
  using remainder_theorem[of f a g _] assms
  unfolding UP_root_rem_def 
  by (simp add: ctrm_zcf taylor_zcf taylor_closed UP_root_div_closed X_minus_closed)

lemma factor_theorem':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "to_fun f a = \<zero>"
  shows "f = (X_minus a) \<otimes>\<^bsub>P\<^esub> UP_root_div f a"
  by (simp add: assms(1) assms(2) assms(3) factor_theorem)

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Geometric Sums\<close>
  (**********************************************************************)
  (**********************************************************************)
lemma geom_quot:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "p = monom P \<one> (Suc n) \<ominus>\<^bsub>P\<^esub> monom P (b[^](Suc n)) 0 "
  assumes "g = UP_root_div p b"
  shows "a[^](Suc n) \<ominus> b[^] (Suc n) = (a \<ominus> b) \<otimes> (to_fun g a)"
proof-
  have root: "to_fun p b = \<zero>"
    using assms to_fun_const[of "b[^](Suc n)" b] to_fun_monic_monom[of b "Suc n"] R.nat_pow_closed[of b "Suc n"]
          to_fun_diff[of "monom P \<one> (Suc n)" "monom P (b[^](Suc n)) 0" b] monom_closed 
    by (metis P.minus_closed P_def R.one_closed R.zero_closed UP_cring.f_minus_ctrm 
        UP_cring.to_fun_diff UP_cring_axioms zcf_to_fun cfs_monom to_fun_const)
  have LHS: "to_fun p a = a[^](Suc n) \<ominus> b[^] (Suc n)"
    using assms to_fun_const to_fun_monic_monom to_fun_diff 
    by auto
  have RHS: "to_fun ((X_minus b) \<otimes>\<^bsub>P\<^esub> g) a = (a \<ominus> b) \<otimes> (to_fun g a)"
    using to_fun_mult[of g "X_minus b"] assms X_minus_closed 
    by (metis P.minus_closed P_def R.nat_pow_closed R.one_closed UP_cring.UP_root_div_closed UP_cring_axioms to_fun_X_minus monom_closed)
  show ?thesis 
    using RHS LHS root factor_theorem' assms(2) assms(3) assms(4) 
    by auto
qed

end

context UP_cring
begin 

definition geometric_series where
"geometric_series n a b = to_fun (UP_root_div (monom P \<one> (Suc n) \<ominus>\<^bsub>UP R\<^esub> (monom P (b[^](Suc n)) 0)) b) a"

lemma geometric_series_id:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "a[^](Suc n) \<ominus>b[^] (Suc n) = (a \<ominus> b) \<otimes> (geometric_series n a b)"
  using assms geom_quot 
  by (simp add: P_def geometric_series_def)

lemma geometric_series_closed:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "(geometric_series n a b) \<in> carrier R"
  unfolding geometric_series_def 
  using assms  P.minus_closed P_def UP_root_div_closed to_fun_closed monom_closed 
  by auto

text\<open>Shows that $a^n - b^n$ has $a - b$ as a factor:\<close>
lemma to_fun_monic_monom_diff:
    assumes "a \<in> carrier R"
    assumes "b \<in> carrier R"
    shows "\<exists>c. c \<in> carrier R \<and> to_fun (monom P \<one> n) a \<ominus> to_fun (monom P \<one> n) b = (a \<ominus> b) \<otimes> c"
proof(cases "n = 0")
  case True
  have "to_fun (monom P \<one> 0) a \<ominus> to_fun (monom P \<one> 0) b = (a \<ominus> b) \<otimes> \<zero>"
    unfolding a_minus_def using to_fun_const[of \<one>] assms 
    by (simp add: R.r_neg)
  then show ?thesis 
    using True by blast 
next
  case False
  then show ?thesis 
    using Suc_diff_1[of n] geometric_series_id[of a b "n-1"] geometric_series_closed[of a b "n-1"]
        assms(1) assms(2) to_fun_monic_monom 
    by auto
qed

lemma to_fun_diff_factor:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "f \<in> carrier P"
  shows "\<exists>c. c \<in> carrier R \<and>(to_fun f a) \<ominus> (to_fun f b) = (a \<ominus> b)\<otimes>c"
proof(rule poly_induct5[of f])
  show "f \<in> carrier P" using assms by simp 
  show "\<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           \<exists>c. c \<in> carrier R \<and> to_fun p a \<ominus> to_fun p b = (a \<ominus> b) \<otimes> c \<Longrightarrow>
           \<exists>c. c \<in> carrier R \<and> to_fun q a \<ominus> to_fun q b = (a \<ominus> b) \<otimes> c \<Longrightarrow>
     \<exists>c. c \<in> carrier R \<and> to_fun (p \<oplus>\<^bsub>P\<^esub> q) a \<ominus> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b = (a \<ominus> b) \<otimes> c"
  proof- fix p q assume A: "q \<in> carrier P" "p \<in> carrier P" 
                          "\<exists>c. c \<in> carrier R \<and> to_fun p a \<ominus> to_fun p b = (a \<ominus> b) \<otimes> c"
                          "\<exists>c. c \<in> carrier R \<and> to_fun q a \<ominus> to_fun q b = (a \<ominus> b) \<otimes> c"
    obtain c  where c_def: "c \<in> carrier R \<and> to_fun p a \<ominus> to_fun p b = (a \<ominus> b) \<otimes> c"
      using A by blast 
    obtain c'  where c'_def: "c' \<in> carrier R \<and> to_fun q a \<ominus> to_fun q b = (a \<ominus> b) \<otimes> c'"
      using A by blast 
    have 0: "(a \<ominus> b) \<otimes> c \<oplus> (a \<ominus> b) \<otimes> c' = (a \<ominus> b)\<otimes>(c \<oplus> c')"
      using assms c_def c'_def  unfolding a_minus_def       
      by (simp add: R.r_distr R.r_minus)   
    have 1: "to_fun (p \<oplus>\<^bsub>P\<^esub>q) a \<ominus> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b = to_fun p a \<oplus> to_fun q a \<ominus> to_fun p b \<ominus> to_fun q b"
      using A to_fun_plus[of p q a] to_fun_plus[of p q b] assms to_fun_closed 
            R.ring_simprules(19)[of "to_fun p b" "to_fun q b"] 
      by (simp add: R.add.m_assoc R.minus_eq to_fun_plus)
    hence "to_fun (p \<oplus>\<^bsub>P\<^esub>q) a \<ominus> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b = to_fun p a \<ominus> to_fun p b \<oplus> to_fun q a \<ominus> to_fun q b"
      using 0 A assms R.ring_simprules  to_fun_closed a_assoc a_comm 
      unfolding a_minus_def 
      by smt
    hence "to_fun (p \<oplus>\<^bsub>P\<^esub>q) a \<ominus> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b = to_fun p a \<ominus> to_fun p b \<oplus> (to_fun q a \<ominus> to_fun q b)"
      using 0 A assms R.ring_simprules  to_fun_closed 
      unfolding a_minus_def 
      by metis 
    hence "to_fun (p \<oplus>\<^bsub>P\<^esub>q) a \<ominus> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b = (a \<ominus> b)\<otimes>(c \<oplus> c')"
      using 0 A c_def c'_def  
      by simp
    thus "\<exists>c. c \<in> carrier R \<and> to_fun (p \<oplus>\<^bsub>P\<^esub> q) a \<ominus> to_fun (p \<oplus>\<^bsub>P\<^esub> q) b = (a \<ominus> b) \<otimes> c"
      using R.add.m_closed c'_def c_def by blast
  qed
  show "\<And>n. \<exists>c. c \<in> carrier R \<and> to_fun (monom P \<one> n) a \<ominus> to_fun (monom P \<one> n) b = (a \<ominus> b) \<otimes> c"
    by (simp add: assms(1) assms(2) to_fun_monic_monom_diff)
  show "\<And>p aa.
       aa \<in> carrier R \<Longrightarrow>
       p \<in> carrier P \<Longrightarrow> \<exists>c. c \<in> carrier R \<and> to_fun p a \<ominus> to_fun p b = (a \<ominus> b) \<otimes> c \<Longrightarrow> \<exists>c. c \<in> carrier R \<and> to_fun (aa \<odot>\<^bsub>P\<^esub> p) a \<ominus> to_fun (aa \<odot>\<^bsub>P\<^esub> p) b = (a \<ominus> b) \<otimes> c"
  proof- fix p c assume A: "c \<in> carrier R" " p \<in> carrier P" 
                          "\<exists>e. e \<in> carrier R \<and> to_fun p a \<ominus> to_fun p b = (a \<ominus> b) \<otimes> e"
    then obtain d where d_def: "d \<in> carrier R \<and> to_fun p a \<ominus> to_fun p b = (a \<ominus> b) \<otimes> d"
      by blast 
    have "to_fun (c \<odot>\<^bsub>P\<^esub> p) a \<ominus> to_fun (c \<odot>\<^bsub>P\<^esub> p) b = c \<otimes> (to_fun p a \<ominus> to_fun p b)"
      using A d_def assms to_fun_smult[of p a c] to_fun_smult[of p b c] 
            to_fun_closed[of p a] to_fun_closed[of p b]  R.ring_simprules 
      by smt
    hence "c\<otimes>d \<in> carrier R \<and> to_fun (c \<odot>\<^bsub>P\<^esub> p) a \<ominus> to_fun (c \<odot>\<^bsub>P\<^esub> p) b = (a \<ominus> b) \<otimes> (c \<otimes>d)"
      by (simp add: A(1) R.m_lcomm assms(1) assms(2) d_def)
    thus "\<exists>e. e \<in> carrier R \<and> to_fun (c \<odot>\<^bsub>P\<^esub> p) a \<ominus> to_fun (c \<odot>\<^bsub>P\<^esub> p) b = (a \<ominus> b) \<otimes> e" 
      by blast 
  qed
qed

text\<open>Any finite set over a domain is the zero set of a polynomial:\<close>
lemma(in UP_domain) fin_set_poly_roots:
  assumes "F \<subseteq> carrier R"
  assumes "finite F"
  shows "\<exists> P \<in> carrier (UP R). \<forall> x \<in> carrier R. to_fun P x = \<zero> \<longleftrightarrow> x \<in> F"
  apply(rule finite.induct)
    apply (simp add: assms(2))
proof-
  show "\<exists>P\<in>carrier (UP R). \<forall>x\<in>carrier R. (to_fun P x = \<zero>) = (x \<in> {})"
  proof-
    have "\<forall>x\<in>carrier R. (to_fun (\<one>\<^bsub>UP R\<^esub>) x = \<zero>) = (x \<in> {})"
    proof
      fix x
      assume A: "x \<in> carrier R"
      then have "(to_fun (\<one>\<^bsub>UP R\<^esub>)) x = \<one>"
        by (metis P_def R.one_closed UP_cring.to_fun_to_poly UP_cring_axioms ring_hom_one to_poly_is_ring_hom)
      then show "(to_fun \<one>\<^bsub>UP R\<^esub> x = \<zero>) = (x \<in> {})"
        by simp      
    qed
    then show ?thesis 
      using P_def UP_one_closed 
      by blast
  qed
  show "\<And>A a. finite A \<Longrightarrow>
           \<exists>P\<in>carrier (UP R). \<forall>x\<in>carrier R. (to_fun P x = \<zero>) = (x \<in> A) \<Longrightarrow> \<exists>P\<in>carrier (UP R). \<forall>x\<in>carrier R. (to_fun P x = \<zero>) = (x \<in> insert a A)"
  proof-
    fix A :: "'a set" fix a
    assume fin_A: "finite A"
    assume IH: "\<exists>P\<in>carrier (UP R). \<forall>x\<in>carrier R. (to_fun P x = \<zero>) = (x \<in> A)"
    then obtain p  where p_def: "p \<in>carrier (UP R) \<and> (\<forall>x\<in>carrier R. (to_fun p x = \<zero>) = (x \<in> A))"
      by blast
    show "\<exists>P\<in>carrier (UP R). \<forall>x\<in>carrier R. (to_fun P x = \<zero>) = (x \<in> insert a A)"
    proof(cases "a \<in> carrier R")
      case True
        obtain Q where Q_def: "Q = p \<otimes>\<^bsub>UP R\<^esub> (X \<ominus>\<^bsub>UP R\<^esub> to_poly a)"
      by blast
      have "\<forall>x\<in>carrier R. (to_fun Q x = \<zero>) = (x \<in> insert a A)" 
      proof fix x
        assume P: "x \<in> carrier R"
        have P0: "to_fun (X \<ominus>\<^bsub>UP R\<^esub> to_poly a) x = x \<ominus> a" 
          using to_fun_plus[of X "\<ominus>\<^bsub>UP R\<^esub> to_poly a" x] True P 
          unfolding a_minus_def 
          by (metis X_poly_minus_def a_minus_def to_fun_X_minus)
        then have "to_fun Q x = (to_fun p x) \<otimes> (x \<ominus> a)"
        proof-
          have 0: " p \<in> carrier P"
          by (simp add: P_def p_def)
          have 1: "    X \<ominus>\<^bsub>UP R\<^esub> to_poly a \<in> carrier P"
          using P.minus_closed P_def True X_closed to_poly_closed by auto
          have 2: "x \<in> carrier R"
          by (simp add: P)
          then show ?thesis 
          using to_fun_mult[of p "(X \<ominus>\<^bsub>UP R\<^esub> to_poly a)" x] P0 0 1 2 Q_def True P_def to_fun_mult 
          by auto
        qed
       then show "(to_fun Q x = \<zero>) = (x \<in> insert a A)" 
        using p_def 
        by (metis P R.add.inv_closed R.integral_iff R.l_neg R.minus_closed R.minus_unique True UP_cring.to_fun_closed UP_cring_axioms a_minus_def insert_iff)        
    qed
    then have "Q \<in> carrier (UP R) \<and> (\<forall>x\<in>carrier R. (to_fun Q x = \<zero>) = (x \<in> insert a A))" 
      using P.minus_closed P_def Q_def True UP_mult_closed X_closed p_def to_poly_closed by auto
    then show ?thesis 
      by blast
  next
    case False 
    then show ?thesis 
      using IH subsetD by auto
  qed
  qed
qed

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Polynomial Evaluation at Multiplicative Inverses\<close>
  (**********************************************************************)
  (**********************************************************************)
text\<open>For every polynomial $p(x)$ of degree $n$, there is a unique polynomial $q(x)$ which satisfies the equation $q(x) = x^n p(1/x)$. This section defines this polynomial and proves this identity.\<close>
definition(in UP_cring) one_over_poly where
"one_over_poly p = (\<lambda> n. if n \<le> degree p then p ((degree  p) - n) else \<zero>)"

lemma(in UP_cring) one_over_poly_closed: 
  assumes "p \<in> carrier P"
  shows "one_over_poly p \<in> carrier P"
  apply(rule UP_car_memI[of "degree p" ])
  unfolding one_over_poly_def using assms  apply simp
  by (simp add: assms cfs_closed)
  
lemma(in UP_cring) one_over_poly_monom:
  assumes "a \<in> carrier R"
  shows "one_over_poly (monom P a n) = monom P a 0"
  apply(rule ext)
  unfolding one_over_poly_def using assms 
  by (metis cfs_monom deg_monom diff_diff_cancel diff_is_0_eq diff_self_eq_0 zero_diff)

lemma(in UP_cring) one_over_poly_monom_add:
  assumes "a \<in> carrier R"
  assumes "a \<noteq> \<zero>"
  assumes "p \<in> carrier P"
  assumes "degree p < n"
  shows "one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n) = monom P a 0 \<oplus>\<^bsub>P\<^esub> monom P \<one> (n - degree p) \<otimes>\<^bsub>P\<^esub> one_over_poly p"
proof-
  have 0: "degree (p \<oplus>\<^bsub>P\<^esub> monom P a n) = n"
    by (simp add: assms(1) assms(2) assms(3) assms(4) equal_deg_sum)
  show ?thesis 
  proof(rule ext) fix x show "one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n) x =
                                 (monom P a 0 \<oplus>\<^bsub>P\<^esub> monom P \<one> (n - deg R p) \<otimes>\<^bsub>P\<^esub> one_over_poly p) x"
    proof(cases "x = 0")
      case T: True
      have T0: "one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n) 0 = a"
        unfolding one_over_poly_def 
        by (metis lcf_eq lcf_monom(1) ltrm_of_sum_diff_deg P.add.m_closed assms(1) assms(2) assms(3) assms(4) diff_zero le0 monom_closed)        
      have T1: "(monom P a 0 \<oplus>\<^bsub>P\<^esub> monom P \<one> (n - degree p) \<otimes>\<^bsub>P\<^esub> one_over_poly p) 0 = a"
        using one_over_poly_closed 
        by (metis (no_types, lifting) lcf_monom(1) R.one_closed R.r_zero UP_m_comm UP_mult_closed assms(1) assms(3) assms(4) cfs_add cfs_monom_mult deg_const monom_closed zero_less_diff)                    
      show ?thesis  using T0 T1 T by auto 
    next
      case F: False
      show ?thesis
      proof(cases "x < n - degree p")
        case True
        then have T0: "degree p < n - x \<and> n - x < n"
          using F by auto
        then have T1: "one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n) x = \<zero>"
          using True F 0 unfolding one_over_poly_def 
          using assms(1) assms(3) coeff_of_sum_diff_degree0 
          by (metis ltrm_cfs ltrm_of_sum_diff_deg P.add.m_closed P.add.m_comm assms(2) assms(4) monom_closed nat_neq_iff)          
        have "(monom P a 0 \<oplus>\<^bsub>P\<^esub> monom P \<one> (n - degree p) \<otimes>\<^bsub>P\<^esub> one_over_poly p) x = \<zero>"  
          using True F 0  one_over_poly_def one_over_poly_closed 
          by (metis (no_types, lifting) P.add.m_comm P.m_closed R.one_closed UP_m_comm assms(1)
              assms(3) cfs_monom_mult coeff_of_sum_diff_degree0 deg_const monom_closed neq0_conv)
        then show ?thesis using T1 by auto 
      next
        case False
        then have "n - degree p \<le> x"
          by auto 
        then obtain k where k_def: "k + (n - degree p) = x"
          using le_Suc_ex  diff_add 
          by blast
        have F0: "(monom P a 0 \<oplus>\<^bsub>P\<^esub> monom P \<one> (n - deg R p) \<otimes>\<^bsub>P\<^esub> one_over_poly p) x
              = one_over_poly p k"
          using k_def one_over_poly_closed assms 
                times_X_pow_coeff[of "one_over_poly p" "n - deg R p" k]
                P.m_closed 
          by (metis (no_types, lifting) P.add.m_comm R.one_closed add_gr_0 coeff_of_sum_diff_degree0 deg_const monom_closed zero_less_diff)                
        show ?thesis 
        proof(cases "x \<le> n")
          case True
          have T0: "n - x = degree p - k"
            using assms(4) k_def by linarith
          have T1: "n - x < n"
            using True F 
            by linarith
          then have F1: "(p \<oplus>\<^bsub>P\<^esub> monom P a n) (n - x) = p (degree p - k)"
            using True False F0 0 k_def cfs_add 
            by (simp add: F0 T0 assms(1) assms(3) cfs_closed cfs_monom)            
          then show ?thesis 
            using "0" F0 assms(1) assms(2) assms(3) degree_of_sum_diff_degree k_def one_over_poly_def
            by auto          
        next
          case False
          then show ?thesis 
            using "0" F0 assms(1) assms(2) assms(3) degree_of_sum_diff_degree k_def one_over_poly_def 
            by auto          
        qed
      qed
    qed 
  qed
qed

lemma( in UP_cring) one_over_poly_eval: 
  assumes "p \<in> carrier P"
  assumes "x \<in> carrier R"
  assumes "x \<in> Units R"
  shows "to_fun (one_over_poly p) x = (x[^](degree p)) \<otimes> (to_fun p (inv\<^bsub>R\<^esub> x))" 
proof(rule poly_induct6[of p])
  show " p \<in> carrier P"
    using assms by simp 
  show "\<And>a n. a \<in> carrier R \<Longrightarrow> 
        to_fun (one_over_poly (monom P a 0)) x = x [^] deg R (monom P a 0) \<otimes> to_fun (monom P a 0) (inv x)"
    using assms to_fun_const one_over_poly_monom by auto
  show "\<And>a n p.
       a \<in> carrier R \<Longrightarrow>
       a \<noteq> \<zero> \<Longrightarrow>
       p \<in> carrier P \<Longrightarrow>
       deg R p < n \<Longrightarrow>
       to_fun (one_over_poly p) x = x [^] deg R p \<otimes> to_fun p (inv x) \<Longrightarrow>
      to_fun (one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n)) x = x [^] deg R (p \<oplus>\<^bsub>P\<^esub> monom P a n) \<otimes> to_fun (p \<oplus>\<^bsub>P\<^esub> monom P a n) (inv x)"
  proof- fix a n p assume A: "a \<in> carrier R" "a \<noteq> \<zero>" "p \<in> carrier P" "deg R p < n"
                             "to_fun (one_over_poly p) x = x [^] deg R p \<otimes> to_fun p (inv x)"
    have "one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n) = monom P a 0 \<oplus>\<^bsub>P\<^esub> monom P \<one> (n - degree p) \<otimes>\<^bsub>P\<^esub> one_over_poly p"
      using A by (simp add: one_over_poly_monom_add)
    hence "to_fun ( one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n)) x = 
                a \<oplus> to_fun ( monom P \<one> (n - degree p) \<otimes>\<^bsub>P\<^esub> one_over_poly p) x"
      using A to_fun_plus one_over_poly_closed cfs_add 
      by (simp add: assms(2) to_fun_const)
    hence "to_fun (one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n)) x = a \<oplus> x[^](n - degree p) \<otimes> x [^] degree p \<otimes> to_fun p (inv x)"
      by (simp add: A(3) A(5) R.m_assoc assms(2) assms(3) to_fun_closed to_fun_monic_monom to_fun_mult one_over_poly_closed)
    hence 0:"to_fun (one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n)) x = a \<oplus> x[^]n \<otimes> to_fun p (inv x)"
      using A R.nat_pow_mult assms(2)
      by auto
    have 1: "to_fun (one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n)) x = x[^]n \<otimes> (a \<otimes> inv x [^]n \<oplus> to_fun p (inv x))"
    proof-
      have "x[^]n \<otimes> a \<otimes> inv x [^]n = a"
        by (metis (no_types, hide_lams) A(1) R.Units_inv_closed R.Units_r_inv R.m_assoc 
            R.m_comm R.nat_pow_closed R.nat_pow_distrib R.nat_pow_one R.r_one assms(2) assms(3))
      thus ?thesis 
        using A R.ring_simprules(23)[of _ _  "x[^]n"] 0 R.m_assoc assms(2) assms(3) to_fun_closed 
        by auto
    qed
    have 2: "degree (p \<oplus>\<^bsub>P\<^esub> monom P a n) = n"
      by (simp add: A(1) A(2) A(3) A(4) equal_deg_sum)
    show " to_fun (one_over_poly (p \<oplus>\<^bsub>P\<^esub> monom P a n)) x = x [^] deg R (p \<oplus>\<^bsub>P\<^esub> monom P a n) \<otimes> to_fun (p \<oplus>\<^bsub>P\<^esub> monom P a n) (inv x)"
      using 1 2 
      by (metis (no_types, lifting) A(1) A(3) P_def R.Units_inv_closed R.add.m_comm 
          UP_cring.to_fun_monom UP_cring_axioms assms(3) to_fun_closed to_fun_plus monom_closed)
  qed
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Lifting Homomorphisms of Rings to Polynomial Rings by Application to Coefficients\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition poly_lift_hom where
"poly_lift_hom R S \<phi> = eval R (UP S) (to_polynomial S \<circ> \<phi>) (X_poly S)"

context UP_ring
begin

lemma(in UP_cring) pre_poly_lift_hom_is_hom:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  shows "ring_hom_ring R (UP S) (to_polynomial S \<circ> \<phi>)"
  apply(rule ring_hom_ringI) 
       apply (simp add: R.ring_axioms)
  apply (simp add: UP_ring.UP_ring UP_ring.intro assms(1) cring.axioms(1))
  using UP_cring.intro UP_cring.to_poly_closed assms(1) assms(2) ring_hom_closed apply fastforce
  using assms UP_cring.to_poly_closed[of S] ring_hom_closed[of \<phi> R S] comp_apply[of "to_polynomial S" \<phi>]
  unfolding UP_cring_def 
  apply (metis UP_cring.to_poly_mult UP_cring_def ring_hom_mult)
  using assms UP_cring.to_poly_closed[of S] ring_hom_closed[of \<phi> R S] comp_apply[of "to_polynomial S" \<phi>]
  unfolding UP_cring_def 
    apply (metis UP_cring.to_poly_add UP_cring_def ring_hom_add)
  using assms UP_cring.to_poly_closed[of S] ring_hom_one[of \<phi> R S] comp_apply[of "to_polynomial S" \<phi>]
  unfolding UP_cring_def 
  by (simp add: \<open>\<phi> \<in> ring_hom R S \<Longrightarrow> \<phi> \<one> = \<one>\<^bsub>S\<^esub>\<close> UP_cring.intro UP_cring.to_poly_is_ring_hom ring_hom_one)

lemma(in UP_cring) poly_lift_hom_is_hom:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  shows "poly_lift_hom R S \<phi> \<in> ring_hom (UP R) (UP S)"
  unfolding poly_lift_hom_def
  apply( rule UP_pre_univ_prop.eval_ring_hom[of R "UP S" ])
  unfolding UP_pre_univ_prop_def
  apply (simp add: R_cring RingHom.ring_hom_cringI UP_cring.UP_cring UP_cring_def assms(1) assms(2) pre_poly_lift_hom_is_hom)
  by (simp add: UP_cring.X_closed UP_cring.intro assms(1))

lemma(in UP_cring) poly_lift_hom_closed: 
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier (UP R)"
  shows "poly_lift_hom R S \<phi> p \<in> carrier (UP S)"
  by (metis assms(1) assms(2) assms(3) poly_lift_hom_is_hom ring_hom_closed)

lemma(in UP_cring) poly_lift_hom_add: 
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier (UP R)"
  assumes "q \<in> carrier (UP R)"
  shows "poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>UP R\<^esub> q) = poly_lift_hom R S \<phi> p \<oplus>\<^bsub>UP S\<^esub> poly_lift_hom R S \<phi> q"
  using assms poly_lift_hom_is_hom[of S \<phi>] ring_hom_add[of "poly_lift_hom R S \<phi>" "UP R" "UP S" p q] 
  by blast

lemma(in UP_cring) poly_lift_hom_mult: 
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier (UP R)"
  assumes "q \<in> carrier (UP R)"
  shows "poly_lift_hom R S \<phi> (p \<otimes>\<^bsub>UP R\<^esub> q) = poly_lift_hom R S \<phi> p \<otimes>\<^bsub>UP S\<^esub> poly_lift_hom R S \<phi> q"
  using assms poly_lift_hom_is_hom[of  S \<phi>] ring_hom_mult[of "poly_lift_hom R S \<phi>" "UP R" "UP S" p q] 
  by blast 

lemma(in UP_cring) poly_lift_hom_extends_hom:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "r \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (to_polynomial R r) = to_polynomial S (\<phi> r)"
  using UP_pre_univ_prop.eval_const[of R "UP S" "to_polynomial S \<circ> \<phi>" "X_poly S" r ] assms 
        comp_apply[of "\<lambda>a. monom (UP S) a 0"  \<phi> r] pre_poly_lift_hom_is_hom[of  S \<phi>]
  unfolding poly_lift_hom_def to_polynomial_def UP_pre_univ_prop_def 
  by (simp add: R_cring RingHom.ring_hom_cringI UP_cring.UP_cring UP_cring.X_closed UP_cring.intro)

lemma(in UP_cring) poly_lift_hom_extends_hom':
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "r \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (monom P r 0) = monom (UP S) (\<phi> r) 0"
  using poly_lift_hom_extends_hom[of S \<phi> r] assms 
  unfolding to_polynomial_def P_def 
  by blast

lemma(in UP_cring) poly_lift_hom_smult: 
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "poly_lift_hom R S \<phi>  (a \<odot>\<^bsub>UP R\<^esub> p) = \<phi> a \<odot>\<^bsub>UP S\<^esub> (poly_lift_hom R S \<phi> p)"
  using assms poly_lift_hom_is_hom[of S \<phi>] poly_lift_hom_extends_hom'[of S \<phi> a] 
        poly_lift_hom_mult[of  S \<phi> "monom P a 0" p] ring_hom_closed[of \<phi> R S a]
        UP_ring.monom_mult_is_smult[of S "\<phi> a" "poly_lift_hom R S \<phi> p"]
        monom_mult_is_smult[of a p] monom_closed[of a 0] poly_lift_hom_closed[of S \<phi> p]
  unfolding to_polynomial_def UP_ring_def P_def cring_def 
  by simp        

lemma(in UP_cring) poly_lift_hom_monom:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "r \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (monom (UP R) r n) = (monom (UP S) (\<phi> r) n)"
proof-
  have "eval R (UP S) (to_polynomial S \<circ> \<phi>) (X_poly S) (monom (UP R) r n) = (to_polynomial S \<circ> \<phi>) r \<otimes>\<^bsub>UP S\<^esub> X_poly S [^]\<^bsub>UP S\<^esub> n"
    using assms UP_pre_univ_prop.eval_monom[of R "UP S" "to_polynomial S \<circ> \<phi>" r "X_poly S" n]
    unfolding UP_pre_univ_prop_def UP_cring_def ring_hom_cring_def
    by (meson UP_cring.UP_cring UP_cring.X_closed UP_cring.pre_poly_lift_hom_is_hom UP_cring_axioms 
        UP_cring_def ring_hom_cring_axioms.intro ring_hom_ring.homh)     
   then have "eval R (UP S) (to_polynomial S \<circ> \<phi>) (X_poly S) (monom (UP R) r n) = (to_polynomial S (\<phi> r)) \<otimes>\<^bsub>UP S\<^esub> X_poly S [^]\<^bsub>UP S\<^esub> n"
    by simp
  then show ?thesis
  unfolding poly_lift_hom_def
  using assms UP_cring.monom_rep_X_pow[of S "\<phi> r" n]  ring_hom_closed[of \<phi> R S r]
    by (metis UP_cring.X_closed UP_cring.intro UP_cring.monom_sub UP_cring.sub_monom(1))
qed

lemma(in UP_cring) poly_lift_hom_X_var:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  shows "poly_lift_hom R S \<phi> (monom (UP R) \<one>\<^bsub>R\<^esub> 1) = (monom (UP S) \<one>\<^bsub>S\<^esub> 1)"
  using assms(1) assms(2) poly_lift_hom_monom ring_hom_one by fastforce

lemma(in UP_cring) poly_lift_hom_X_var':
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  shows "poly_lift_hom R S \<phi> (X_poly R) = (X_poly S)"
  unfolding X_poly_def 
  using assms(1) assms(2) poly_lift_hom_X_var by blast
  
lemma(in UP_cring) poly_lift_hom_X_var'':
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  shows "poly_lift_hom R S \<phi> (monom (UP R) \<one>\<^bsub>R\<^esub> n) = (monom (UP S) \<one>\<^bsub>S\<^esub> n)"
  using assms(1) assms(2) poly_lift_hom_monom ring_hom_one by fastforce

lemma(in UP_cring) poly_lift_hom_X_var''':
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  shows "poly_lift_hom R S \<phi> (X_poly R [^]\<^bsub>UP R\<^esub> (n::nat)) = (X_poly S) [^]\<^bsub>UP S\<^esub> (n::nat)"
  using assms 
  by (smt ltrm_of_X P.nat_pow_closed P_def R.ring_axioms UP_cring.to_fun_closed UP_cring.intro
      UP_cring.monom_pow UP_cring.poly_lift_hom_monom UP_cring_axioms X_closed cfs_closed 
      cring.axioms(1) to_fun_X_pow poly_lift_hom_X_var' ring_hom_closed ring_hom_nat_pow)  

lemma(in UP_cring) poly_lift_hom_X_plus:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (X_poly_plus R a) = X_poly_plus S (\<phi> a)"
  using ring_hom_add
  unfolding X_poly_plus_def 
  using P_def X_closed assms(1) assms(2) assms(3) poly_lift_hom_X_var' poly_lift_hom_add poly_lift_hom_extends_hom to_poly_closed by fastforce

lemma(in UP_cring) poly_lift_hom_X_plus_nat_pow:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (X_poly_plus R a [^]\<^bsub>UP R\<^esub> (n::nat)) = X_poly_plus S (\<phi> a) [^]\<^bsub>UP S\<^esub> (n::nat)"
  using assms poly_lift_hom_X_plus[of S \<phi> a] 
        ring_hom_nat_pow[of "UP R" "UP S" "poly_lift_hom R S \<phi>" "X_poly_plus R a" n] 
        poly_lift_hom_is_hom[of S \<phi>] X_plus_closed[of a] UP_ring.UP_ring[of S]
  unfolding P_def cring_def UP_cring_def
  using P_def UP_ring UP_ring.intro
  by (simp add: UP_ring.intro)
 
lemma(in UP_cring) X_poly_plus_nat_pow_closed:
  assumes "a \<in> carrier R"
  shows " X_poly_plus R a [^]\<^bsub>UP R\<^esub> (n::nat) \<in> carrier (UP R)"
  using assms P.nat_pow_closed P_def X_plus_closed by auto

lemma(in UP_cring) poly_lift_hom_X_plus_nat_pow_smult:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (b \<odot>\<^bsub>UP R\<^esub> X_poly_plus R a [^]\<^bsub>UP R\<^esub> (n::nat)) = \<phi> b \<odot>\<^bsub>UP S \<^esub>X_poly_plus S (\<phi> a) [^]\<^bsub>UP S\<^esub> (n::nat)"
  by (simp add: X_poly_plus_nat_pow_closed assms(1) assms(2) assms(3) assms(4) poly_lift_hom_X_plus_nat_pow poly_lift_hom_smult)

lemma(in UP_cring) poly_lift_hom_X_minus:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (X_poly_minus R a) = X_poly_minus S (\<phi> a)"
  using poly_lift_hom_X_plus[of S \<phi> "\<ominus> a"] X_minus_plus[of a] UP_cring.X_minus_plus[of S "\<phi> a"]
        R.ring_hom_a_inv[of S \<phi> a]
  unfolding UP_cring_def P_def
  by (metis R.add.inv_closed assms(1) assms(2) assms(3) cring.axioms(1) ring_hom_closed)

lemma(in UP_cring) poly_lift_hom_X_minus_nat_pow:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (X_poly_minus R a [^]\<^bsub>UP R\<^esub> (n::nat)) = X_poly_minus S (\<phi> a) [^]\<^bsub>UP S\<^esub> (n::nat)"
  using assms poly_lift_hom_X_minus ring_hom_nat_pow X_minus_plus UP_cring.X_minus_plus 
      poly_lift_hom_X_plus poly_lift_hom_X_plus_nat_pow by fastforce

lemma(in UP_cring) X_poly_minus_nat_pow_closed:
  assumes "a \<in> carrier R"
  shows "X_poly_minus R a [^]\<^bsub>UP R\<^esub> (n::nat) \<in> carrier (UP R)"
  using assms monoid.nat_pow_closed[of "UP R" "X_poly_minus R a" n] 
        P.nat_pow_closed P_def X_minus_closed by auto

lemma(in UP_cring) poly_lift_hom_X_minus_nat_pow_smult:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (b \<odot>\<^bsub>UP R\<^esub> X_poly_minus R a [^]\<^bsub>UP R\<^esub> (n::nat)) = \<phi> b \<odot>\<^bsub>UP S \<^esub>X_poly_minus S (\<phi> a) [^]\<^bsub>UP S\<^esub> (n::nat)"
  by (simp add: X_poly_minus_nat_pow_closed assms(1) assms(2) assms(3) assms(4) poly_lift_hom_X_minus_nat_pow poly_lift_hom_smult)

lemma(in UP_cring) poly_lift_hom_cf:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier P"
  shows "poly_lift_hom R S \<phi> p k = \<phi> (p k)"
  apply(rule poly_induct3[of p])
  apply (simp add: assms(3))
proof-
  show "\<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           poly_lift_hom R S \<phi> p k = \<phi> (p k) \<Longrightarrow> poly_lift_hom R S \<phi> q k = \<phi> (q k) \<Longrightarrow> poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>P\<^esub> q) k = \<phi> ((p \<oplus>\<^bsub>P\<^esub> q) k)"
  proof- fix p q assume A: "p \<in> carrier P"  "q \<in> carrier P"
          "poly_lift_hom R S \<phi> p k = \<phi> (p k)" "poly_lift_hom R S \<phi> q k = \<phi> (q k)"
    show "poly_lift_hom R S \<phi> q k = \<phi> (q k) \<Longrightarrow> poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>P\<^esub> q) k = \<phi> ((p \<oplus>\<^bsub>P\<^esub> q) k)"
      using A assms poly_lift_hom_add[of S \<phi> p q] 
            poly_lift_hom_closed[of S \<phi> p] poly_lift_hom_closed[of S \<phi> q]   
           UP_ring.cfs_closed[of S "poly_lift_hom R S \<phi> q " k] UP_ring.cfs_closed[of S "poly_lift_hom R S \<phi> p" k] 
           UP_ring.cfs_add[of S "poly_lift_hom R S \<phi> p" "poly_lift_hom R S \<phi> q" k]       
      unfolding P_def UP_ring_def  
      by (metis (full_types) P_def cfs_add cfs_closed cring.axioms(1) ring_hom_add)
  qed
  show "\<And>a n. a \<in> carrier R \<Longrightarrow> poly_lift_hom R S \<phi> (monom P a n) k = \<phi> (monom P a n k)"
  proof- fix a m assume A: "a \<in> carrier R" 
    show "poly_lift_hom R S \<phi> (monom P a m) k = \<phi> (monom P a m k)"     
      apply(cases "m = k")
    using cfs_monom[of a m k] assms poly_lift_hom_monom[of S \<phi> a m] UP_ring.cfs_monom[of S "\<phi> a" m k] 
       unfolding P_def UP_ring_def  
       apply (simp add: A cring.axioms(1) ring_hom_closed)
           using cfs_monom[of a m k] assms poly_lift_hom_monom[of S \<phi> a m] UP_ring.cfs_monom[of S "\<phi> a" m k] 
       unfolding P_def UP_ring_def  
       by (metis A P_def R.ring_axioms cring.axioms(1) ring_hom_closed ring_hom_zero)     
  qed
qed

lemma(in ring) ring_hom_monom_term:
  assumes "a \<in> carrier R"
  assumes "c \<in> carrier R"
  assumes "ring S"
  assumes "h \<in> ring_hom R S"
  shows "h (a \<otimes> c[^](n::nat)) = h a \<otimes>\<^bsub>S\<^esub> (h c)[^]\<^bsub>S\<^esub>n"
  apply(induction n)
  using assms ringE(2) ring_hom_closed apply fastforce
  by (metis assms(1) assms(2) assms(3) assms(4) local.ring_axioms nat_pow_closed ring_hom_mult ring_hom_nat_pow)

lemma(in UP_cring) poly_lift_hom_eval:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "UP_cring.to_fun  S (poly_lift_hom R S \<phi> p) (\<phi> a) = \<phi> (to_fun p a) "
  apply(rule poly_induct3[of p])
    apply (simp add: assms(3))
proof-
  show "\<And>p q. q \<in> carrier P \<Longrightarrow>
           p \<in> carrier P \<Longrightarrow>
           UP_cring.to_fun S (poly_lift_hom R S \<phi> p) (\<phi> a) = \<phi> (to_fun p a) \<Longrightarrow>
           UP_cring.to_fun S (poly_lift_hom R S \<phi> q) (\<phi> a) = \<phi> (to_fun q a) \<Longrightarrow>
           UP_cring.to_fun S (poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>P\<^esub> q)) (\<phi> a) = \<phi> (to_fun (p \<oplus>\<^bsub>P\<^esub> q) a)"
  proof- fix p q  assume A: "q \<in> carrier P"  "p \<in> carrier P"
           "UP_cring.to_fun S (poly_lift_hom R S \<phi> p) (\<phi> a) = \<phi> (to_fun p a)"
           "UP_cring.to_fun S (poly_lift_hom R S \<phi> q) (\<phi> a) = \<phi> (to_fun q a)"
    have "(poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>P\<^esub> q)) = poly_lift_hom R S \<phi> p \<oplus>\<^bsub>UP S\<^esub> poly_lift_hom R S \<phi> q"
      using A(1) A(2) P_def assms(1) assms(2) poly_lift_hom_add by auto
    hence "UP_cring.to_fun S (poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>P\<^esub> q)) (\<phi> a) = 
          UP_cring.to_fun S (poly_lift_hom R S \<phi> p) (\<phi> a) \<oplus>\<^bsub>S\<^esub> UP_cring.to_fun S (poly_lift_hom R S \<phi> q) (\<phi> a)"
      using UP_cring.to_fun_plus[of S] assms 
      unfolding UP_cring_def 
      by (metis (no_types, lifting) A(1) A(2) P_def poly_lift_hom_closed ring_hom_closed)
    thus "UP_cring.to_fun S (poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>P\<^esub> q)) (\<phi> a) = \<phi> (to_fun (p \<oplus>\<^bsub>P\<^esub> q) a)"
      using A to_fun_plus assms ring_hom_add[of \<phi> R S]
        poly_lift_hom_closed[of S \<phi>]  UP_cring.to_fun_def[of S] to_fun_def
      unfolding P_def UP_cring_def 
      using UP_cring.to_fun_closed UP_cring_axioms 
      by metis 
  qed
  show "\<And>c n. c \<in> carrier R \<Longrightarrow> UP_cring.to_fun  S (poly_lift_hom R S \<phi> (monom P c n)) (\<phi> a) = \<phi> (to_fun (monom P c n) a)"
    unfolding P_def
  proof - fix c n assume A: "c \<in> carrier R"
    have 0: "\<phi> (a [^]\<^bsub>R\<^esub> (n::nat)) =  \<phi> a [^]\<^bsub>S\<^esub> n" 
      using assms ring_hom_nat_pow[of R S \<phi> a n] 
      unfolding cring_def 
      using R.ring_axioms by blast
    have 1: "\<phi> (c \<otimes>\<^bsub>R\<^esub> a [^]\<^bsub>R\<^esub> n) = \<phi> c \<otimes>\<^bsub>S\<^esub> \<phi> a [^]\<^bsub>S\<^esub> n"
      using ring_hom_mult[of \<phi> R S c "a [^]\<^bsub>R\<^esub> n" ] 0 assms A monoid.nat_pow_closed [of R a n]
      by (simp add: cring.axioms(1) ringE(2))
    show "UP_cring.to_fun  S (poly_lift_hom R S \<phi> (monom (UP R) c n)) (\<phi> a) = \<phi> (to_fun(monom (UP R) c n) a)"
      using assms A poly_lift_hom_monom[of S \<phi> c n] UP_cring.to_fun_monom[of S "\<phi> c" "\<phi> a" n]
           to_fun_monom[of c a n]  0 1 ring_hom_closed[of \<phi> R S] unfolding UP_cring_def
      by (simp add: P_def to_fun_def)      
  qed
qed

lemma(in UP_cring) poly_lift_hom_sub:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier P"
  assumes "q \<in> carrier P"
  shows "poly_lift_hom R S \<phi> (compose R p q) = compose S (poly_lift_hom R S \<phi> p) (poly_lift_hom R S \<phi> q)"
  apply(rule poly_induct3[of p])
  apply (simp add: assms(3))
proof-
  show " \<And>p qa.
       qa \<in> carrier P \<Longrightarrow>
       p \<in> carrier P \<Longrightarrow>
       poly_lift_hom R S \<phi> (Cring_Poly.compose R p q) = Cring_Poly.compose S (poly_lift_hom R S \<phi> p) (poly_lift_hom R S \<phi> q) \<Longrightarrow>
       poly_lift_hom R S \<phi> (Cring_Poly.compose R qa q) = Cring_Poly.compose S (poly_lift_hom R S \<phi> qa) (poly_lift_hom R S \<phi> q) \<Longrightarrow>
       poly_lift_hom R S \<phi> (Cring_Poly.compose R (p \<oplus>\<^bsub>P\<^esub> qa) q) = Cring_Poly.compose S (poly_lift_hom R S \<phi> (p \<oplus>\<^bsub>P\<^esub> qa)) (poly_lift_hom R S \<phi> q)"
  proof- fix a b assume A: "a \<in> carrier P"
       "b \<in> carrier P"
       "poly_lift_hom R S \<phi> (Cring_Poly.compose R a q) = Cring_Poly.compose S (poly_lift_hom R S \<phi> a) (poly_lift_hom R S \<phi> q)"
       "poly_lift_hom R S \<phi> (Cring_Poly.compose R b q) = Cring_Poly.compose S (poly_lift_hom R S \<phi> b) (poly_lift_hom R S \<phi> q)"
    show "poly_lift_hom R S \<phi> (Cring_Poly.compose R (a \<oplus>\<^bsub>P\<^esub> b) q) = Cring_Poly.compose S (poly_lift_hom R S \<phi> (a \<oplus>\<^bsub>P\<^esub> b)) (poly_lift_hom R S \<phi> q)"
      using assms UP_cring.sub_add[of R q a b ] UP_cring.sub_add[of S  ] 
      unfolding UP_cring_def 
      by (metis A(1) A(2) A(3) A(4) P_def R_cring UP_cring.sub_closed UP_cring_axioms poly_lift_hom_add poly_lift_hom_closed)
  qed
  show "\<And>a n. a \<in> carrier R \<Longrightarrow>
           poly_lift_hom R S \<phi> (Cring_Poly.compose R (monom P a n) q) = 
            Cring_Poly.compose S (poly_lift_hom R S \<phi> (monom P a n)) (poly_lift_hom R S \<phi> q)"
  proof-
    fix a n assume A: "a \<in> carrier R"
    have 0: "(poly_lift_hom R S \<phi> (monom (UP R) a n)) = monom (UP S) (\<phi> a) n"
      by (simp add: A assms(1) assms(2) assms(3) assms(4) poly_lift_hom_monom)
    have 1: " q [^]\<^bsub>UP R\<^esub> n \<in> carrier (UP R)"
      using monoid.nat_pow_closed[of "UP R" q n] UP_ring.UP_ring UP_ring.intro assms(1) assms
            P.monoid_axioms P_def by blast
    have 2: "poly_lift_hom R S \<phi> (to_polynomial R a \<otimes>\<^bsub>UP R\<^esub> q [^]\<^bsub>UP R\<^esub> n) = 
            to_polynomial S (\<phi> a) \<otimes>\<^bsub>UP S\<^esub> (poly_lift_hom R S \<phi> q) [^]\<^bsub>UP S\<^esub> n"
      using poly_lift_hom_mult[of S \<phi> "to_polynomial R a" "q [^]\<^bsub>UP R\<^esub> n"] poly_lift_hom_is_hom[of S \<phi>]
            ring_hom_nat_pow[of P "UP S" "poly_lift_hom R S \<phi>" q n]   UP_cring.UP_cring[of S]
            UP_cring poly_lift_hom_monom[of S \<phi> a 0] ring_hom_closed[of \<phi> R S a] 
            monom_closed[of a 0] nat_pow_closed[of q n] assms A
      unfolding to_polynomial_def P_def UP_cring_def cring_def
      by auto 
    have 3: "poly_lift_hom R S \<phi> (Cring_Poly.compose R (monom (UP R) a n) q) = to_polynomial S (\<phi> a) \<otimes>\<^bsub>UP S\<^esub> (poly_lift_hom R S \<phi> q) [^]\<^bsub>UP S\<^esub> n"
      using "2" A P_def assms(4) sub_monom(1) by auto      
    have 4: "Cring_Poly.compose S (poly_lift_hom R S \<phi> (monom (UP R) a n)) (poly_lift_hom R S \<phi> q) 
                              = Cring_Poly.compose S (monom (UP S) (\<phi> a) n) (poly_lift_hom R S \<phi> q)"
      by (simp add: "0")    
    have "poly_lift_hom R S \<phi> q \<in> carrier (UP S)"
      using P_def UP_cring.poly_lift_hom_closed UP_cring_axioms assms(1) assms(2) assms(4) by blast
    then have 5: "Cring_Poly.compose S (poly_lift_hom R S \<phi> (monom (UP R) a n)) (poly_lift_hom R S \<phi> q)
                              = to_polynomial S (\<phi> a) \<otimes>\<^bsub>UP S\<^esub> (poly_lift_hom R S \<phi> q) [^]\<^bsub>UP S\<^esub> n"
      using 4 UP_cring.sub_monom[of S "poly_lift_hom R S \<phi> q" "\<phi> a" n] assms 
      unfolding UP_cring_def  
      by (simp add: A ring_hom_closed)
    thus "poly_lift_hom R S \<phi> (Cring_Poly.compose R (monom P a n) q) = 
            Cring_Poly.compose S (poly_lift_hom R S \<phi> (monom P a n)) (poly_lift_hom R S \<phi> q)"
      using 0 1 2 3 4 assms A 
      by (simp add: P_def)
  qed
qed

lemma(in UP_cring) poly_lift_hom_comm_taylor_expansion:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (taylor_expansion R a p) = taylor_expansion S (\<phi> a) (poly_lift_hom R S \<phi> p)"
  unfolding taylor_expansion_def 
  using  poly_lift_hom_sub[of S \<phi> p "(X_poly_plus R a)"] poly_lift_hom_X_plus[of S \<phi> a] assms 
  by (simp add: P_def UP_cring.X_plus_closed UP_cring_axioms)
 
lemma(in UP_cring) poly_lift_hom_comm_taylor_expansion_cf:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "\<phi> (taylor_expansion R a p i) = taylor_expansion S (\<phi> a) (poly_lift_hom R S \<phi> p) i"
  using poly_lift_hom_cf assms poly_lift_hom_comm_taylor_expansion P_def 
        taylor_def UP_cring.taylor_closed UP_cring_axioms by fastforce
  
lemma(in UP_cring) taylor_expansion_cf_closed:
  assumes "p \<in> carrier P"
  assumes "a \<in> carrier R"
  shows "taylor_expansion R a p i \<in> carrier R"
  using assms taylor_closed
  by (simp add: taylor_def cfs_closed)

lemma(in UP_cring) poly_lift_hom_comm_taylor_term:
  assumes "cring S"
  assumes "\<phi> \<in> ring_hom R S"
  assumes "p \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "poly_lift_hom R S \<phi> (taylor_term a p i) = UP_cring.taylor_term S (\<phi> a) (poly_lift_hom R S \<phi> p) i"
  using poly_lift_hom_X_minus_nat_pow_smult[of S \<phi> a "taylor_expansion R a p i" i] 
        poly_lift_hom_comm_taylor_expansion[of S \<phi> p a]
        poly_lift_hom_comm_taylor_expansion_cf[of S \<phi> p a i]
        assms UP_cring.taylor_term_def[of S]
    unfolding taylor_term_def UP_cring_def P_def
  by (simp add: UP_cring.taylor_expansion_cf_closed UP_cring_axioms) 

lemma(in UP_cring) poly_lift_hom_degree_bound:
  assumes "cring S"
  assumes "h \<in> ring_hom R S"
  assumes "f \<in> carrier (UP R)"
  shows "deg S (poly_lift_hom R S h f) \<le> deg R f"
    using poly_lift_hom_closed[of S h f]  UP_cring.deg_leqI[of S "poly_lift_hom R S h f" "deg R f"] assms ring_hom_zero[of h R S] deg_aboveD[of f] coeff_simp[of f]
    unfolding P_def UP_cring_def
    by (simp add: P_def R.ring_axioms cring.axioms(1) poly_lift_hom_cf)

lemma(in UP_cring) deg_eqI:
  assumes "f \<in> carrier (UP R)"
  assumes "deg R f \<le> n"
  assumes "f n \<noteq> \<zero>"
  shows "deg R f = n"
  using assms coeff_simp[of f] P_def deg_leE le_neq_implies_less by blast

lemma(in UP_cring) poly_lift_hom_degree_eq:
  assumes "cring S"
  assumes "h \<in> ring_hom R S"
  assumes "h (lcf f) \<noteq> \<zero>\<^bsub>S\<^esub>"
  assumes "f \<in> carrier (UP R)"
  shows "deg S (poly_lift_hom R S h f) = deg R f"
  apply(rule UP_cring.deg_eqI)
  using assms unfolding UP_cring_def apply blast
  using poly_lift_hom_closed[of S h f] assms apply blast 
  using poly_lift_hom_degree_bound[of S h f] assms apply blast 
  using assms poly_lift_hom_cf[of S h f] 
  by (metis P_def)

lemma(in UP_cring) poly_lift_hom_lcoeff:
  assumes "cring S"
  assumes "h \<in> ring_hom R S"
  assumes "h (lcf f) \<noteq> \<zero>\<^bsub>S\<^esub>"
  assumes "f \<in> carrier (UP R)"
  shows "UP_ring.lcf S (poly_lift_hom R S h f) = h (lcf f)"
  using poly_lift_hom_degree_eq[of S h f] assms 
  by (simp add: P_def poly_lift_hom_cf)

end 

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Coefficient List Constructor for Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition list_to_poly where
"list_to_poly R as n = (if n < length as then as!n else \<zero>\<^bsub>R\<^esub>)"

context UP_ring
begin

lemma(in UP_ring) list_to_poly_closed:
  assumes "set as \<subseteq> carrier R"
  shows "list_to_poly R as \<in> carrier P"
  apply(rule UP_car_memI[of "length as"])
  apply (simp add: list_to_poly_def)
  by (metis R.zero_closed assms in_mono list_to_poly_def nth_mem)

lemma(in UP_ring) list_to_poly_zero[simp]:
"list_to_poly R [] = \<zero>\<^bsub>UP R\<^esub>"
  unfolding list_to_poly_def 
  apply auto 
  by(simp add: UP_def)   

lemma(in UP_domain) list_to_poly_singleton:
  assumes "a \<in> carrier R"
  shows "list_to_poly R [a] = monom P a 0"
  apply(rule ext)
  unfolding list_to_poly_def using assms 
  by (simp add: cfs_monom)
end 

definition cf_list where 
"cf_list R p = map p [(0::nat)..< Suc (deg R p)]"

lemma cf_list_length:
"length (cf_list R p) = Suc (deg R p)"
  unfolding cf_list_def 
  by simp

lemma cf_list_entries:
  assumes "i \<le> deg R p"
  shows "(cf_list R p)!i = p i"
  unfolding cf_list_def 
  by (metis add.left_neutral assms diff_zero less_Suc_eq_le map_eq_map_tailrec nth_map_upt)
  
lemma(in UP_ring) list_to_poly_cf_list_inv:
  assumes "p \<in> carrier (UP R)"
  shows "list_to_poly R (cf_list R p) = p"
proof
  fix x 
  show "list_to_poly R (cf_list R p) x = p x"
    apply(cases "x < degree p")
    unfolding list_to_poly_def 
    using assms cf_list_length[of R p] cf_list_entries[of _ R p]
     apply simp
    by (metis P_def UP_ring.coeff_simp UP_ring_axioms \<open>\<And>i. i \<le> deg R p \<Longrightarrow> cf_list R p ! i = p i\<close> \<open>length (cf_list R p) = Suc (deg R p)\<close> assms deg_belowI less_Suc_eq_le)
qed

section\<open>Polynomial Rings over a Subring\<close>

subsection\<open>Characterizing the Carrier of a Polynomial Ring over a Subring\<close>
lemma(in ring) carrier_update: 
"carrier (R\<lparr>carrier := S\<rparr>) = S"
"\<zero>\<^bsub>(R\<lparr>carrier := S\<rparr>)\<^esub> = \<zero>"
"\<one>\<^bsub>(R\<lparr>carrier := S\<rparr>)\<^esub> = \<one>"
"(\<oplus>\<^bsub>(R\<lparr>carrier := S\<rparr>)\<^esub>) = (\<oplus>)"
"(\<otimes>\<^bsub>(R\<lparr>carrier := S\<rparr>)\<^esub>) = (\<otimes>)"
by auto 


lemma(in UP_cring) poly_cfs_subring:
  assumes "subring S R"
  assumes "g \<in> carrier (UP R)"
  assumes "\<And>n. g n \<in> S"
  shows "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  apply(rule UP_cring.UP_car_memI')
  using R.subcringI' R.subcring_iff UP_cring.intro assms(1) subringE(1) apply blast
proof-
  have "carrier (R\<lparr>carrier := S\<rparr>) = S"
    using ring.carrier_update  by simp
  then show 0: "\<And>x. g x \<in> carrier (R\<lparr>carrier := S\<rparr>)"
    using assms by blast
  have 0: "\<zero>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> = \<zero>"
    using R.carrier_update(2) by blast
  then show "\<And>x. (deg R g) < x \<Longrightarrow> g x = \<zero>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub>"
    using UP_car_memE assms(2) by presburger
qed

lemma(in UP_cring) UP_ring_subring:
  assumes "subring S R"
  shows "UP_cring (R \<lparr> carrier := S \<rparr>)"  "UP_ring (R \<lparr> carrier := S \<rparr>)"
  using assms unfolding UP_cring_def 
  using R.subcringI' R.subcring_iff subringE(1) apply blast  
  using assms unfolding UP_ring_def 
  using R.subcringI' R.subcring_iff subringE(1)  
  by (simp add: R.subring_is_ring)
  
lemma(in UP_cring) UP_ring_subring_is_ring:
  assumes "subring S R"
  shows "cring (UP (R \<lparr> carrier := S \<rparr>))"
  using assms UP_ring_subring[of S] UP_cring.UP_cring[of "R\<lparr>carrier := S\<rparr>"] 
  by blast
  
lemma(in UP_cring) UP_ring_subring_add_closed:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "f \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "f \<oplus>\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  using assms UP_ring_subring_is_ring[of S] 
  by (meson cring.cring_simprules(1))

lemma(in UP_cring) UP_ring_subring_mult_closed:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "f \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "f \<otimes>\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  using assms UP_ring_subring_is_ring[of S] 
  by (meson cring.carrier_is_subcring subcringE(6))

lemma(in UP_cring) UP_ring_subring_car:
  assumes "subring S R"
  shows "carrier (UP (R \<lparr> carrier := S \<rparr>)) = {h \<in> carrier (UP R). \<forall>n. h n \<in> S}"
proof
  show "carrier (UP (R\<lparr>carrier := S\<rparr>)) \<subseteq> {h \<in> carrier (UP R). \<forall>n. h n \<in> S}"
  proof
    fix h assume A: "h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
    have "h \<in> carrier P"
      apply(rule UP_car_memI[of "deg (R\<lparr>carrier := S\<rparr>) h"]) unfolding P_def 
      using UP_cring.UP_car_memE[of "R\<lparr>carrier := S\<rparr>" h] R.carrier_update[of S]
            assms UP_ring_subring A apply presburger
      using UP_cring.UP_car_memE[of "R\<lparr>carrier := S\<rparr>" h] assms 
      by (metis A R.ring_axioms UP_cring_def \<open>carrier (R\<lparr>carrier := S\<rparr>) = S\<close> cring.subcringI' is_UP_cring ring.subcring_iff subringE(1) subsetD)
    then show "h \<in> {h \<in> carrier (UP R). \<forall>n. h n \<in> S}"
      unfolding P_def 
      using assms A  UP_cring.UP_car_memE[of "R\<lparr>carrier := S\<rparr>" h] R.carrier_update[of S]
      UP_ring_subring by blast
  qed
  show "{h \<in> carrier (UP R). \<forall>n. h n \<in> S} \<subseteq> carrier (UP (R\<lparr>carrier := S\<rparr>))"
  proof fix h assume A: "h \<in> {h \<in> carrier (UP R). \<forall>n. h n \<in> S}"
    have 0: "h \<in> carrier (UP R)"
      using A by blast 
    have 1: "\<And>n. h n \<in> S"
      using A by blast 
    show "h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
      apply(rule UP_ring.UP_car_memI[of _ "deg R h"])
      using assms UP_ring_subring[of S] UP_cring.axioms UP_ring.intro cring.axioms(1) apply blast
      using UP_car_memE[of h] carrier_update 0 R.carrier_update(2) apply presburger
      using assms 1  R.carrier_update(1) by blast
  qed
qed

lemma(in UP_cring) UP_ring_subring_car_subset:
  assumes "subring S R"
  shows "carrier (UP (R \<lparr> carrier := S \<rparr>)) \<subseteq> carrier (UP R)"
proof fix h assume "h \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  then show "h \<in> carrier (UP R)"
  using assms UP_ring_subring_car[of S] by blast
qed

lemma(in UP_cring) UP_ring_subring_car_subset':
  assumes "subring S R"
  assumes "h \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "h \<in>  carrier (UP R)"
  using assms UP_ring_subring_car_subset[of S] by blast 

lemma(in UP_cring) UP_ring_subring_add:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "f \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "g \<oplus>\<^bsub>UP R\<^esub> f = g \<oplus>\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>f"
proof(rule ext) fix x show "(g \<oplus>\<^bsub>UP R\<^esub> f) x = (g \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> f) x"
  proof-
    have 0: " (g \<oplus>\<^bsub>P\<^esub> f) x = g x \<oplus> f x"
      using assms cfs_add[of g f x] unfolding P_def 
      using UP_ring_subring_car_subset' by blast
    have 1: "(g \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> f) x = g x \<oplus>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> f x"
      using   UP_ring.cfs_add[of "R \<lparr> carrier := S \<rparr>" g f x] UP_ring_subring[of S] assms 
      unfolding UP_ring_def UP_cring_def 
      using R.subring_is_ring by blast
    show ?thesis using 0 1  R.carrier_update(4)[of S]  
    by (simp add: P_def)
  qed
qed

lemma(in UP_cring) UP_ring_subring_deg:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "deg R g = deg (R \<lparr> carrier := S \<rparr>) g"
proof-
  have 0: "g \<in> carrier (UP R)"
    using assms UP_ring_subring_car[of S] by blast
  have 1: "deg R g \<le> deg (R \<lparr> carrier := S \<rparr>) g"
    using 0 assms UP_cring.UP_car_memE[of "R \<lparr> carrier := S \<rparr>" g]
             UP_car_memE[of g] P_def R.carrier_update(2) UP_ring_subring deg_leqI by presburger
  have 2: "deg (R \<lparr> carrier := S \<rparr>) g \<le> deg R g"
    using 0 assms UP_cring.UP_car_memE[of "R \<lparr> carrier := S \<rparr>" g]
             UP_car_memE[of g] P_def R.carrier_update(2) UP_ring_subring UP_cring.deg_leqI 
    by metis 

  show ?thesis using 1 2 by presburger 
qed


lemma(in UP_cring) UP_subring_monom:
  assumes "subring S R"
  assumes "a \<in> S"
  shows "up_ring.monom (UP R) a n = up_ring.monom (UP (R \<lparr> carrier := S \<rparr>)) a n"
proof fix x
  have 0: "a \<in> carrier R"
    using assms subringE(1)  by blast
  have 1: "a \<in> carrier (R\<lparr>carrier := S\<rparr>)"
    using assms  by (simp add: assms(2))
  have 2: " up_ring.monom (UP (R\<lparr>carrier := S\<rparr>)) a n x = (if n = x then a else \<zero>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub>)"
    using 1  assms UP_ring_subring[of S] UP_ring.cfs_monom[of "R\<lparr>carrier := S\<rparr>" a n x] UP_cring.axioms UP_ring.intro cring.axioms(1) 
    by blast
  show "up_ring.monom (UP R) a n x = up_ring.monom (UP (R\<lparr>carrier := S\<rparr>)) a n x"
    using 0 1 2 cfs_monom[of a n x]  R.carrier_update(2)[of S] unfolding P_def by presburger
qed

lemma(in UP_cring) UP_ring_subring_mult:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "f \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "g \<otimes>\<^bsub>UP R\<^esub> f = g \<otimes>\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>f"
proof(rule UP_ring.poly_induct3[of "R \<lparr> carrier := S \<rparr>" f])
  show "UP_ring (R\<lparr>carrier := S\<rparr>)"
    by (simp add: UP_ring_subring(2) assms(1))
  show " f \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
    by (simp add: assms(3))
  show " \<And>p q. q \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<Longrightarrow>
           p \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<Longrightarrow>
           g \<otimes>\<^bsub>UP R\<^esub> p = g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> p \<Longrightarrow>
           g \<otimes>\<^bsub>UP R\<^esub> q = g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q \<Longrightarrow> g \<otimes>\<^bsub>UP R\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) = g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q)"
  proof- fix p q 
    assume A: " q \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
           "p \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
           "g \<otimes>\<^bsub>UP R\<^esub> p = g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> p"
           "g \<otimes>\<^bsub>UP R\<^esub> q = g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q"
    have 0: "p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q = p \<oplus>\<^bsub>UP R\<^esub> q"
      using A UP_ring_subring_add[of S p q] 
      by (simp add: assms(1))
    have 1: "g \<otimes>\<^bsub>UP R\<^esub> (p \<oplus>\<^bsub>UP R\<^esub> q) = g \<otimes>\<^bsub>UP R\<^esub> p \<oplus>\<^bsub>UP R\<^esub> g \<otimes>\<^bsub>UP R\<^esub> q"
      using 0 A assms  P.r_distr P_def UP_ring_subring_car_subset' by auto
    hence 2:"g \<otimes>\<^bsub>UP R\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) = g \<otimes>\<^bsub>UP R\<^esub> p \<oplus>\<^bsub>UP R\<^esub> g \<otimes>\<^bsub>UP R\<^esub> q"
      using 0 by simp
    have 3: "g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) =
          g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q"
      using 0 A assms semiring.r_distr[of "UP (R\<lparr>carrier := S\<rparr>)"]  UP_ring_subring_car_subset' 
      using UP_ring.UP_r_distr \<open>UP_ring (R\<lparr>carrier := S\<rparr>)\<close> by blast
    hence 4: "g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) =
          g \<otimes>\<^bsub>UP R\<^esub> p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> g \<otimes>\<^bsub>UP R\<^esub> q"
      using A by simp 
    hence 5: "g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) =
          g \<otimes>\<^bsub>UP R\<^esub> p \<oplus>\<^bsub>UP R\<^esub> g \<otimes>\<^bsub>UP R\<^esub> q"
      using UP_ring_subring_add[of S]
      by (simp add: A(1) A(2) A(3) A(4) UP_ring.UP_mult_closed \<open>UP_ring (R\<lparr>carrier := S\<rparr>)\<close> assms(1) assms(2))
    show "g \<otimes>\<^bsub>UP R\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) = g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q)"
      by (simp add: "2" "5")
  qed
  show "\<And>a n. a \<in> carrier (R\<lparr>carrier := S\<rparr>) \<Longrightarrow> g \<otimes>\<^bsub>UP R\<^esub> monom (UP (R\<lparr>carrier := S\<rparr>)) a n = g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> monom (UP (R\<lparr>carrier := S\<rparr>)) a n"
  proof fix a n x assume A: "a \<in> carrier (R\<lparr>carrier := S\<rparr>)"
    have 0: "monom (UP (R\<lparr>carrier := S\<rparr>)) a n = monom (UP R) a n"
      using A UP_subring_monom assms(1) by auto
    have 1: "g \<in> carrier (UP R)"
      using assms UP_ring_subring_car_subset' by blast
    have 2: "a \<in> carrier R"
      using A assms subringE(1)[of S R] R.carrier_update[of S] by blast       
    show "(g \<otimes>\<^bsub>UP R\<^esub> monom (UP (R\<lparr>carrier := S\<rparr>)) a n) x = (g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> monom (UP (R\<lparr>carrier := S\<rparr>)) a n) x"
    proof(cases "x < n")
      case True
      have T0: "(g \<otimes>\<^bsub>UP R\<^esub> monom (UP R) a n) x = \<zero>" 
        using 1 2 True cfs_monom_mult[of g a x n] A assms unfolding P_def  by blast
      then show ?thesis using UP_cring.cfs_monom_mult[of "R\<lparr>carrier := S\<rparr>" g a x n] 0 A True 
          UP_ring_subring(1) assms(1) assms(2) by auto
    next
      case False
      have F0: "(g \<otimes>\<^bsub>UP R\<^esub> monom (UP R) a n) x = a \<otimes> (g (x - n))" 
        using 1 2 False cfs_monom_mult_l[of g a n "x - n"] A assms unfolding P_def by simp
      have F1: "(g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> monom (UP (R\<lparr>carrier := S\<rparr>)) a n) (x - n + n) = a \<otimes>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> g (x - n)" 
        using 1 2 False UP_cring.cfs_monom_mult_l[of "R\<lparr>carrier := S\<rparr>" g a n "x - n"] A assms 
              UP_ring_subring(1) by blast
      hence F2: "(g \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> monom (UP R) a n) (x - n + n) = a \<otimes> g (x - n)" 
        using UP_subring_monom[of S a n] R.carrier_update[of S] assms 0 by metis         
      show ?thesis using F0 F1 1 2 assms 
        by (simp add: "0" False add.commute add_diff_inverse_nat)
    qed
  qed
qed

lemma(in UP_cring) UP_ring_subring_one:
  assumes "subring S R"
  shows "\<one>\<^bsub>UP R\<^esub> = \<one>\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>"
  using UP_subring_monom[of S \<one> 0] assms P_def R.subcringI' UP_ring.monom_one UP_ring_subring(2) monom_one subcringE(3) by force

lemma(in UP_cring) UP_ring_subring_zero:
  assumes "subring S R"
  shows "\<zero>\<^bsub>UP R\<^esub> = \<zero>\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>"
  using UP_subring_monom[of S \<zero> 0] UP_ring.monom_zero[of "R \<lparr> carrier := S \<rparr>" 0]  assms monom_zero[of 0]
  UP_ring_subring[of S] subringE(2)[of S R]
  unfolding P_def  
  by (simp add: P_def R.carrier_update(2))

lemma(in UP_cring) UP_ring_subring_nat_pow:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "g[^]\<^bsub>UP R\<^esub>n = g[^]\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>(n::nat)"
  apply(induction n)
  using assms apply (simp add: UP_ring_subring_one)
proof-
  fix n::nat
  assume A: "g [^]\<^bsub>UP R\<^esub> n = g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n"
  have "Group.monoid (UP (R\<lparr>carrier := S\<rparr>)) "
    using assms UP_ring_subring[of S] UP_ring.UP_ring[of "R\<lparr>carrier := S\<rparr>"] ring.is_monoid by blast
  hence 0 : " g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
    using monoid.nat_pow_closed[of "UP (R \<lparr> carrier := S \<rparr>)" g n] assms UP_ring_subring
    unfolding UP_ring_def ring_def by blast
  have 1: "g [^]\<^bsub>UP R\<^esub> n \<in> carrier (UP R)"
    using 0 assms UP_ring_subring_car_subset'[of S] by (simp add: A)
  then have 2: "g [^]\<^bsub>UP R\<^esub> n \<otimes>\<^bsub>UP R\<^esub> g = g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n \<otimes>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> g"
    using assms UP_ring_subring_mult[of S "g [^]\<^bsub>UP R\<^esub> n" g] 
    by (simp add: "0" A)
  then show "g [^]\<^bsub>UP R\<^esub> Suc n = g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> Suc n" 
    by simp
qed

lemma(in UP_cring) UP_subring_compose_monom:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  shows "compose R (up_ring.monom (UP R) a n) g = compose (R \<lparr> carrier := S \<rparr>) (up_ring.monom (UP (R \<lparr> carrier := S \<rparr>)) a n) g"
proof-
  have g_closed: "g \<in> carrier (UP R)"
    using assms UP_ring_subring_car by blast
  have 0: "a \<in> carrier R"
    using assms subringE(1) by blast  
  have 1: "compose R (up_ring.monom (UP R) a n) g = a \<odot>\<^bsub>UP R\<^esub> (g[^]\<^bsub>UP R\<^esub>n)"
    using monom_sub[of a g n] unfolding P_def 
    using "0" assms(2) g_closed by blast
  have 2: "compose (R\<lparr>carrier := S\<rparr>) (up_ring.monom (UP (R\<lparr>carrier := S\<rparr>)) a n) g = a \<odot>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n"
    using assms UP_cring.monom_sub[of "R \<lparr> carrier := S \<rparr>" a g n] UP_ring_subring[of S] R.carrier_update[of S]
    by blast
  have 3: " g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n = g[^]\<^bsub>UP R\<^esub>n"
    using UP_ring_subring_nat_pow[of S g n] 
    by (simp add: assms(1) assms(2))
  have 4: "a \<odot>\<^bsub>UP R\<^esub> (g[^]\<^bsub>UP R\<^esub>n) = a \<odot>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n"
  proof fix x  
    show "(a \<odot>\<^bsub>UP R\<^esub> g [^]\<^bsub>UP R\<^esub> n) x = (a \<odot>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n) x"
    proof-
      have LHS: "(a \<odot>\<^bsub>UP R\<^esub> g [^]\<^bsub>UP R\<^esub> n) x = a \<otimes> ((g [^]\<^bsub>UP R\<^esub> n) x)"
        using "0" P.nat_pow_closed P_def cfs_smult g_closed by auto
      have RHS: "(a \<odot>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n) x = a \<otimes>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> ((g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n) x)"
      proof-
        have "Group.monoid (UP (R\<lparr>carrier := S\<rparr>)) "
          using assms UP_ring_subring[of S] UP_ring.UP_ring[of "R\<lparr>carrier := S\<rparr>"] ring.is_monoid by blast
        hence 0 : " g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
          using monoid.nat_pow_closed[of "UP (R \<lparr> carrier := S \<rparr>)" g n] assms UP_ring_subring
          unfolding UP_ring_def ring_def by blast
        have 1: "g [^]\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> n \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
          using assms UP_ring_subring[of S] R.carrier_update[of S] 0 by blast
        then show ?thesis using UP_ring.cfs_smult UP_ring_subring assms 
          by (simp add: UP_ring.cfs_smult)
      qed
      show ?thesis using R.carrier_update RHS LHS 3 assms  
        by simp
    qed
  qed
  show ?thesis using 0 1 2 3 4 
    by simp
qed

lemma(in UP_cring) UP_subring_compose:
  assumes "subring S R"
  assumes "g \<in> carrier (UP R)"
  assumes "f \<in> carrier (UP R)"
  assumes "\<And>n. g n \<in> S"
  assumes "\<And>n. f n \<in> S"
  shows "compose R f g = compose (R \<lparr> carrier := S \<rparr>) f g"
proof-
  have g_closed: "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
    using assms poly_cfs_subring by blast
  have 0: "\<And>n. (\<forall> h. h \<in> carrier (UP R) \<and> deg R h \<le> n \<and> h \<in> carrier (UP (R \<lparr> carrier := S \<rparr>)) \<longrightarrow> compose R h g = compose (R \<lparr> carrier := S \<rparr>) h g)"
  proof-  fix n show "(\<forall> h. h \<in> carrier (UP R) \<and> deg R h \<le> n \<and> h \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))   \<longrightarrow> compose R h g = compose (R \<lparr> carrier := S \<rparr>) h g)"
    proof(induction n)
      show "\<forall>h. h \<in> carrier (UP R) \<and> deg R h \<le> 0 \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<longrightarrow> Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g"
      proof fix h 
        show "h \<in> carrier (UP R) \<and> deg R h \<le> 0 \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<longrightarrow> Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g"
        proof
          assume A: "h \<in> carrier (UP R) \<and> deg R h \<le> 0 \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
          then have 0: "deg R h = 0"
            by linarith 
          then have 1: "deg (R \<lparr> carrier := S \<rparr>) h = 0"
            using A assms UP_ring_subring_deg[of S h] 
            by linarith
          show "Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g"
            using 0 1 g_closed assms sub_const[of g h] UP_cring.sub_const[of "R\<lparr>carrier := S\<rparr>" g h] A P_def UP_ring_subring
            by presburger
        qed
      qed
      show "\<And>n. \<forall>h. h \<in> carrier (UP R) \<and> deg R h \<le> n \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<longrightarrow>
             Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g \<Longrightarrow>
         \<forall>h. h \<in> carrier (UP R) \<and> deg R h \<le> Suc n \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<longrightarrow>
             Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g"
      proof fix n h 
        assume IH: "\<forall>h. h \<in> carrier (UP R) \<and> deg R h \<le> n \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<longrightarrow>
               Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g"
        show "h \<in> carrier (UP R) \<and> deg R h \<le> Suc n \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<longrightarrow>
           Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g"
        proof assume A: "h \<in> carrier (UP R) \<and> deg R h \<le> Suc n \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
          show "Cring_Poly.compose R h g = Cring_Poly.compose (R\<lparr>carrier := S\<rparr>) h g"
          proof(cases "deg R h \<le> n")
            case True
            then show ?thesis using A IH by blast
          next
            case False
            then have F0: "deg R h = Suc n"
              using A by (simp add: A le_Suc_eq)
            then have F1: "deg (R\<lparr>carrier := S\<rparr>) h = Suc n"
              using UP_ring_subring_deg[of S h] A  
              by (simp add: \<open>h \<in> carrier (UP R) \<and> deg R h \<le> Suc n \<and> h \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))\<close> assms(1))
            obtain j where j_def: "j \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<and>
          h = j \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> up_ring.monom (UP (R\<lparr>carrier := S\<rparr>)) (h (deg (R\<lparr>carrier := S\<rparr>) h)) (deg (R\<lparr>carrier := S\<rparr>) h) \<and>
          deg (R\<lparr>carrier := S\<rparr>) j < deg (R\<lparr>carrier := S\<rparr>) h"
              using A UP_ring.ltrm_decomp[of "R\<lparr>carrier := S\<rparr>" h] assms UP_ring_subring[of S] 
              F1 by (metis (mono_tags, lifting) F0 False zero_less_Suc)
            have j_closed: "j \<in> carrier (UP R)"  
              using j_def assms UP_ring_subring_car_subset by blast 
            have F2: "deg R j < deg R h"
              using j_def  assms  
              by (metis (no_types, lifting) F0 F1 UP_ring_subring_deg)
            have F3: "(deg (R\<lparr>carrier := S\<rparr>) h) = deg R h"
              by (simp add: F0 F1)
            have F30: "h (deg (R\<lparr>carrier := S\<rparr>) h) \<in> S "
              using A UP_cring.UP_car_memE[of "R\<lparr>carrier := S\<rparr>" h "deg (R\<lparr>carrier := S\<rparr>) h"]
              by (metis R.carrier_update(1) UP_ring_subring(1) assms(1))
            hence F4: "up_ring.monom P (h (deg R h)) (deg R h) = 
                  up_ring.monom (UP (R\<lparr>carrier := S\<rparr>)) (h (deg (R\<lparr>carrier := S\<rparr>) h)) (deg (R\<lparr>carrier := S\<rparr>) h)"
              using F3 g_closed j_def UP_subring_monom[of S "h (deg (R\<lparr>carrier := S\<rparr>) h)"] assms 
              unfolding  P_def by metis 
            have F5: "compose R (up_ring.monom (UP R) (h (deg R h)) (deg R h)) g = 
                      compose (R \<lparr> carrier := S \<rparr>) (up_ring.monom (UP (R \<lparr> carrier := S \<rparr>)) (h (deg (R\<lparr>carrier := S\<rparr>) h)) (deg (R\<lparr>carrier := S\<rparr>) h)) g"
              using F0 F1 F2 F3 F4 UP_subring_compose_monom[of S] assms  P_def \<open>h (deg (R\<lparr>carrier := S\<rparr>) h) \<in> S\<close> 
              by (metis g_closed)
            have F5: "compose R j g =  compose (R \<lparr> carrier := S \<rparr>) j g"
              using F0 F2 IH UP_ring_subring_car_subset' assms(1) j_def by auto
            have F6: "h = j \<oplus>\<^bsub>UP R\<^esub> monom (UP R) (h (deg R h)) (deg R h)"
              using j_def F4 UP_ring_subring_add[of S j "up_ring.monom (UP (R\<lparr>carrier := S\<rparr>)) (h (deg (R\<lparr>carrier := S\<rparr>) h)) (deg (R\<lparr>carrier := S\<rparr>) h)"]
                    UP_ring.monom_closed[of "R\<lparr>carrier := S\<rparr>" "h (deg (R\<lparr>carrier := S\<rparr>) h)" "deg (R\<lparr>carrier := S\<rparr>) h"]          
              using P_def UP_ring_subring(2) \<open>h (deg (R\<lparr>carrier := S\<rparr>) h) \<in> S\<close> assms(1) by auto
            have F7: "compose R h g =compose R  j g \<oplus>\<^bsub>UP R\<^esub>
                                    compose R (up_ring.monom (UP R) (h (deg R h)) (deg R h)) g"
            proof-
              show ?thesis 
              using assms(2) j_closed  F5 sub_add[of g j "up_ring.monom P (h (deg R h)) (deg R h)" ] 
                     F4 F3 F2 F1 g_closed  unfolding P_def              
              by (metis A F6 ltrm_closed P_def)
            qed
            have F8: "compose (R \<lparr> carrier := S \<rparr>) h g = compose (R \<lparr> carrier := S \<rparr>)  j g \<oplus>\<^bsub>UP (R \<lparr> carrier := S \<rparr>)\<^esub>
                                    compose (R \<lparr> carrier := S \<rparr>) (up_ring.monom (UP (R \<lparr> carrier := S \<rparr>)) (h (deg (R \<lparr> carrier := S \<rparr>) h)) (deg (R \<lparr> carrier := S \<rparr>) h)) g"
            proof-
              have 0: " UP_cring (R\<lparr>carrier := S\<rparr>)"
                by (simp add: UP_ring_subring(1) assms(1))
              have 1: "monom (UP (R\<lparr>carrier := S\<rparr>)) (h (deg R h)) (deg R h) \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
                using assms 0 F30 UP_ring.monom_closed[of "R\<lparr>carrier := S\<rparr>" "h (deg R h)" "deg R h"] R.carrier_update[of S]
                unfolding UP_ring_def UP_cring_def 
                by (simp add: F3 cring.axioms(1))
              show ?thesis
                using 0 1 g_closed j_def UP_cring.sub_add[of "R \<lparr> carrier := S \<rparr>" g j "monom (UP (R\<lparr>carrier := S\<rparr>)) (h (deg R h)) (deg R h)" ]
                using F3 by auto
            qed
            have F9: "compose R  j g \<in> carrier (UP R)"
              by (simp add: UP_cring.sub_closed assms(2) is_UP_cring j_closed)
            have F10: "compose (R \<lparr> carrier := S \<rparr>) j g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
              using assms j_def UP_cring.sub_closed[of "R \<lparr> carrier := S \<rparr>"] UP_ring_subring(1) g_closed by blast
            have F11: " compose R (up_ring.monom (UP R) (h (deg R h)) (deg R h)) g \<in> carrier (UP R)"
              using assms j_def UP_cring.sub_closed[of "R \<lparr> carrier := S \<rparr>"] 
                    UP_ring.monom_closed[of "R \<lparr> carrier := S \<rparr>"]
              by (simp add: A UP_car_memE(1) UP_cring.rev_sub_closed UP_ring.monom_closed is_UP_cring is_UP_ring sub_rev_sub)
            have F12: " compose (R \<lparr> carrier := S \<rparr>) (up_ring.monom (UP (R \<lparr> carrier := S \<rparr>)) (h (deg (R \<lparr> carrier := S \<rparr>) h)) (deg (R \<lparr> carrier := S \<rparr>) h)) g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
              using assms j_def UP_cring.sub_closed[of "R \<lparr> carrier := S \<rparr>"] 
                    UP_ring.monom_closed[of "R \<lparr> carrier := S \<rparr>"] UP_ring_subring[of S]
              using A UP_ring.ltrm_closed g_closed by fastforce
            show ?thesis using F9 F10 F11 F12 F7 F8 F5 UP_ring_subring_add[of S "compose R  j g" "compose R (up_ring.monom (UP R) (h (deg R h)) (deg R h)) g"]
                    assms 
              using F3 F30 UP_subring_compose_monom g_closed by auto
          qed
        qed
      qed
    qed
  qed
  show  ?thesis using 0[of "deg R f"]   
    by (simp add: assms(1) assms(3) assms(5) poly_cfs_subring)
qed   


subsection\<open>Evaluation over a Subring\<close>

lemma(in UP_cring) UP_subring_eval:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  shows "to_function R g a = to_function (R \<lparr> carrier := S \<rparr>) g a"
  apply(rule UP_ring.poly_induct3[of "R \<lparr> carrier := S \<rparr>" g] )
  apply (simp add: UP_ring_subring(2) assms(1))
    apply (simp add: assms(2))
proof-
  show "\<And>p q. q \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<Longrightarrow>
           p \<in> carrier (UP (R\<lparr>carrier := S\<rparr>)) \<Longrightarrow>
           to_function R p a = to_function (R\<lparr>carrier := S\<rparr>) p a \<Longrightarrow>
           to_function R q a = to_function (R\<lparr>carrier := S\<rparr>) q a \<Longrightarrow>
           to_function R (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) a = to_function (R\<lparr>carrier := S\<rparr>) (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) a"
  proof- fix p q assume A: "q \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
           "p \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
          " to_function R p a = to_function (R\<lparr>carrier := S\<rparr>) p a"
          " to_function R q a = to_function (R\<lparr>carrier := S\<rparr>) q a"
    have a_closed: "a \<in> carrier R"
      using  assms R.carrier_update[of S] subringE(1) by blast
    have 0: "UP_cring (R\<lparr>carrier := S\<rparr>)"
      using assms by (simp add: UP_ring_subring(1))
    have 1: "to_function (R\<lparr>carrier := S\<rparr>) p a \<in> S"
      using A 0 UP_cring.to_fun_closed[of "R\<lparr>carrier := S\<rparr>"]  
      by (simp add: UP_cring.to_fun_def assms(3))
    have 2: "to_function (R\<lparr>carrier := S\<rparr>) q a \<in> S"
      using A 0 UP_cring.to_fun_closed[of "R\<lparr>carrier := S\<rparr>"]  
      by (simp add: UP_cring.to_fun_def assms(3))
    have 3: "p \<in> carrier (UP R)"
      using A  assms 0 UP_ring_subring_car_subset' by blast
    have 4: "q \<in> carrier (UP R)"
      using A  assms 0 UP_ring_subring_car_subset' by blast
    have 5: "to_fun p a \<oplus> to_fun q a =  UP_cring.to_fun (R\<lparr>carrier := S\<rparr>) p a \<oplus>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> UP_cring.to_fun (R\<lparr>carrier := S\<rparr>) q a"
      using 1 2 A R.carrier_update[of S] assms by (simp add: "0" UP_cring.to_fun_def to_fun_def)
    have 6: "UP_cring.to_fun (R\<lparr>carrier := S\<rparr>) (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) a =
    UP_cring.to_fun (R\<lparr>carrier := S\<rparr>) p a \<oplus>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> UP_cring.to_fun (R\<lparr>carrier := S\<rparr>) q a"
      using UP_cring.to_fun_plus[of "R \<lparr> carrier := S \<rparr>" q p a] 
      by (simp add: "0" A(1) A(2) assms(3))
    have 7: "to_fun (p \<oplus>\<^bsub>P\<^esub> q) a = to_fun p a \<oplus> to_fun q a"
      using to_fun_plus[of q p a] 3 4 a_closed by (simp add: P_def)
    have 8: "p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q = p \<oplus>\<^bsub>P\<^esub> q"
      unfolding P_def using assms A R.carrier_update[of S] UP_ring_subring_add[of S p q] by simp
    show "to_function R (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) a = to_function (R\<lparr>carrier := S\<rparr>) (p \<oplus>\<^bsub>UP (R\<lparr>carrier := S\<rparr>)\<^esub> q) a"
      using UP_ring_subring_car_subset'[of S ] 0 1 2 3 4 5 6 7 8 A R.carrier_update[of S] 
      unfolding P_def by (simp add: UP_cring.to_fun_def to_fun_def)
  qed
  show "\<And>b n.
       b \<in> carrier (R\<lparr>carrier := S\<rparr>) \<Longrightarrow>
       to_function R (monom (UP (R\<lparr>carrier := S\<rparr>)) b n) a = to_function (R\<lparr>carrier := S\<rparr>) (monom (UP (R\<lparr>carrier := S\<rparr>)) b n) a"  
  proof- fix b n assume A: "b \<in> carrier (R\<lparr>carrier := S\<rparr>)"
    have 0: "UP_cring (R\<lparr>carrier := S\<rparr>)"
      by (simp add: UP_ring_subring(1) assms(1))
    have a_closed: "a \<in> carrier R"
      using assms subringE by blast 
    have 1: "UP_cring.to_fun (R\<lparr>carrier := S\<rparr>) (monom (UP (R\<lparr>carrier := S\<rparr>)) b n) a = b \<otimes>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> a [^]\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> n"
      using assms A UP_cring.to_fun_monom[of "R\<lparr>carrier := S\<rparr>" b a n]  
      by (simp add: "0")
    have 2: "UP_cring.to_fun (R\<lparr>carrier := S\<rparr>) (monom (UP (R\<lparr>carrier := S\<rparr>)) b n) \<equiv> to_function (R\<lparr>carrier := S\<rparr>) (monom (UP (R\<lparr>carrier := S\<rparr>)) b n)"
      using UP_cring.to_fun_def[of "R\<lparr>carrier := S\<rparr>" "monom (UP (R\<lparr>carrier := S\<rparr>)) b n"] 0 by linarith
    have 3: "(monom (UP (R\<lparr>carrier := S\<rparr>)) b n) = monom P b n"
      using A assms unfolding P_def using  UP_subring_monom by auto
    have 4:  " b \<otimes> a [^] n = b \<otimes>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> a [^]\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> n" 
      apply(induction n) using R.carrier_update[of S] apply simp
      using R.carrier_update[of S] R.nat_pow_consistent by auto
    hence 5: "to_function R (monom (UP (R\<lparr>carrier := S\<rparr>)) b n) a = b \<otimes>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> a[^]\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub>n"
      using 0 1 2 3 assms A UP_cring.to_fun_monom[of "R\<lparr>carrier := S\<rparr>" b a n] UP_cring.to_fun_def[of "R\<lparr>carrier := S\<rparr>" "monom (UP (R\<lparr>carrier := S\<rparr>)) b n"]
             R.carrier_update[of S] subringE[of S R] a_closed UP_ring.monom_closed[of "R\<lparr>carrier := S\<rparr>" a n]  
             to_fun_monom[of b a n]
      unfolding P_def UP_cring.to_fun_def to_fun_def by (metis subsetD)
    thus " to_function R (monom (UP (R\<lparr>carrier := S\<rparr>)) b n) a = to_function (R\<lparr>carrier := S\<rparr>) (monom (UP (R\<lparr>carrier := S\<rparr>)) b n) a"
      using "1" "2" by auto
  qed
qed

lemma(in UP_cring) UP_subring_eval':
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  shows "to_fun g a = to_function (R \<lparr> carrier := S \<rparr>) g a"
  unfolding to_fun_def using assms 
  by (simp add: UP_subring_eval)

lemma(in UP_cring) UP_subring_eval_closed:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  shows "to_fun g a \<in> S"
  using assms  UP_subring_eval'[of S g a] UP_cring.to_fun_closed  UP_cring.to_fun_def R.carrier_update(1) UP_ring_subring(1) by fastforce

subsection\<open>Derivatives and Taylor Expansions over a Subring\<close>


lemma(in UP_cring) UP_subring_taylor:
  assumes "subring S R"
  assumes "g \<in> carrier (UP R)"
  assumes "\<And>n. g n \<in> S"
  assumes "a \<in> S"
  shows "taylor_expansion R a g = taylor_expansion (R \<lparr> carrier := S \<rparr>) a g"
proof-
  have a_closed: "a \<in> carrier R"
    using assms subringE by blast
  have 0: "X_plus a \<in> carrier (UP R)"
    using assms X_plus_closed  unfolding P_def  
    using local.a_closed by auto
  have 1: "\<And>n. X_plus a n \<in> S"
  proof- fix n
    have "X_plus a n = (if n = 0 then a else 
                        (if n = 1 then \<one> else \<zero>))"
      using a_closed 
      by (simp add: cfs_X_plus)
    then show "X_plus a n \<in> S" using subringE assms 
      by (simp add: subringE(2) subringE(3))
  qed
  have 2: "(X_poly_plus (R\<lparr>carrier := S\<rparr>) a) = X_plus a"
  proof-
    have 20: "(X_poly_plus (R\<lparr>carrier := S\<rparr>) a) = (\<lambda>k. if k = (0::nat) then a else 
                        (if k = 1 then \<one> else \<zero>))"
      using a_closed assms UP_cring.cfs_X_plus[of "R\<lparr>carrier := S\<rparr>" a] R.carrier_update 
            UP_ring_subring(1) by auto
    have 21: "X_plus a = (\<lambda>k. if k = (0::nat) then a else 
                        (if k = 1 then \<one> else \<zero>))"
       using cfs_X_plus[of a] a_closed 
       by blast
     show ?thesis apply(rule ext) using 20 21
       by auto
  qed     
  show ?thesis
    unfolding taylor_expansion_def using 0 1 2 assms UP_subring_compose[of S g "X_plus a"] 
    by (simp add: UP_subring_compose)
qed

lemma(in UP_cring) UP_subring_taylor_closed:
  assumes "subring S R"
  assumes "g \<in> carrier (UP R)"
  assumes "\<And>n. g n \<in> S"
  assumes "a \<in> S"
  shows "taylor_expansion R a g \<in> carrier  (UP (R \<lparr> carrier := S \<rparr>))"
proof-
  have "g \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
    by (metis P_def R.carrier_update(1) R.carrier_update(2) UP_cring.UP_car_memI' UP_ring_subring(1) assms(1) assms(2) assms(3) deg_leE)
  then show ?thesis   
    using assms UP_cring.taylor_def[of "R\<lparr>carrier := S\<rparr>"] UP_subring_taylor[of S g a]
          UP_cring.taylor_closed[of "R \<lparr> carrier := S \<rparr>" g a] UP_ring_subring(1)[of S] by simp
qed

lemma(in UP_cring) UP_subring_taylor_closed':
  assumes "subring S R"
  assumes "g \<in> carrier  (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  shows "taylor_expansion R a g \<in> carrier  (UP (R \<lparr> carrier := S \<rparr>))"
  using UP_subring_taylor_closed assms UP_cring.UP_car_memE[of "R \<lparr> carrier := S \<rparr>" g] R.carrier_update[of S]
        UP_ring_subring(1) UP_ring_subring_car_subset' by auto

lemma(in UP_cring) UP_subring_taylor':
  assumes "subring S R"
  assumes "g \<in> carrier (UP R)"
  assumes "\<And>n. g n \<in> S"
  assumes "a \<in> S"
  shows "taylor_expansion R a g n \<in> S"
  using assms UP_subring_taylor R.carrier_update[of S] UP_cring.taylor_closed[of "R \<lparr> carrier := S \<rparr>"]
  using UP_cring.taylor_expansion_cf_closed UP_ring_subring(1) poly_cfs_subring by metis 


lemma(in UP_cring) UP_subring_deriv:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  shows  "deriv g a= UP_cring.deriv (R \<lparr> carrier := S \<rparr>) g a"
proof-
  have 0: "(\<And>n. g n \<in> S)"
    using assms UP_ring_subring_car by blast
  thus ?thesis 
    unfolding derivative_def using 0 UP_ring_subring_car_subset[of S] assms UP_subring_taylor[of S g a] 
    by (simp add: subset_iff)
qed

lemma(in UP_cring) UP_subring_deriv_closed:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  shows  "deriv g a \<in> S"
  using assms  UP_cring.deriv_closed[of "R \<lparr> carrier := S \<rparr>" g a] UP_subring_deriv[of S g a]
        UP_ring_subring_car_subset[of S] UP_ring_subring[of S]
  by simp

lemma(in UP_cring) poly_shift_subring_closed:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "poly_shift g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  using UP_cring.poly_shift_closed[of "R \<lparr> carrier := S \<rparr>" g] assms UP_ring_subring[of S]
  by simp

lemma(in UP_cring) UP_subring_taylor_appr:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  assumes "b \<in> S"
  shows "\<exists>c \<in> S. to_fun g a= to_fun g b \<oplus> (deriv g b)\<otimes> (a \<ominus> b) \<oplus>  (c \<otimes> (a \<ominus>  b)[^](2::nat))"
proof-
  have  a_closed: "a \<in> carrier R"
    using assms subringE by blast
  have b_closed: "b \<in> carrier R"
    using assms subringE by blast
  have g_closed:  " g \<in> carrier (UP R)"
    using UP_ring_subring_car_subset[of S] assms by blast 
  have 0: "to_fun (shift 2 (T\<^bsub>b\<^esub> g)) (a \<ominus> b) = to_fun (shift 2 (T\<^bsub>b\<^esub> g)) (a \<ominus> b)"
    by simp
  have 1: "to_fun g b = to_fun g b"
    by simp
  have 2: "deriv g b = deriv g b"
    by simp 
  have 3: "to_fun g a = to_fun g b \<oplus> deriv g b \<otimes> (a \<ominus> b) \<oplus> to_fun (shift 2 (T\<^bsub>b\<^esub> g)) (a \<ominus> b) \<otimes> (a \<ominus> b) [^] (2::nat)"
    using taylor_deg_1_expansion[of g b a "to_fun (shift 2 (T\<^bsub>b\<^esub> g)) (a \<ominus> b)" "to_fun g b" "deriv g b"]
          assms a_closed b_closed g_closed 0 1 2 unfolding P_def by blast
  have 4: "to_fun (shift 2 (T\<^bsub>b\<^esub> g)) (a \<ominus> b) \<in> S"
  proof-
    have 0: "(2::nat) = Suc (Suc 0)"
      by simp
    have 1: "a \<ominus> b \<in> S"
      using assms unfolding a_minus_def  
      by (simp add: subringE(5) subringE(7))
    have 2: "poly_shift (T\<^bsub>b\<^esub> g) \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
      using poly_shift_subring_closed[of S "taylor_expansion R b g"] UP_ring_subring[of S]
            UP_subring_taylor_closed'[of S g b] assms       unfolding taylor_def
      by blast
    hence 3: "poly_shift (poly_shift (T\<^bsub>b\<^esub> g)) \<in> carrier (UP (R\<lparr>carrier := S\<rparr>))"
      using    UP_cring.poly_shift_closed[of "R\<lparr>carrier := S\<rparr>" "(poly_shift (T\<^bsub>b\<^esub> g))"]            
      unfolding taylor_def 
      using assms(1) poly_shift_subring_closed by blast
    have 4: "to_fun (poly_shift (poly_shift (T\<^bsub>b\<^esub> g))) (a \<ominus> b) \<in> S"
      using 1 2 3 0 UP_subring_eval_closed[of S "poly_shift (poly_shift (T\<^bsub>b\<^esub> g))"  "a \<ominus> b"] 
              UP_cring.poly_shift_closed[of "R\<lparr>carrier := S\<rparr>"] assms
      by blast
    then show ?thesis 
      by (simp add: numeral_2_eq_2)
  qed
  obtain c where c_def: "c = to_fun (shift 2 (T\<^bsub>b\<^esub> g)) (a \<ominus> b)"
    by blast 
  have 5: "c \<in> S \<and> to_fun g a = to_fun g b \<oplus> deriv g b \<otimes> (a \<ominus> b) \<oplus> c \<otimes> (a \<ominus> b) [^] (2::nat)"
    unfolding c_def using 3 4 by blast 
  thus ?thesis using c_def  4 by blast 
qed

lemma(in UP_cring) UP_subring_taylor_appr':
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  assumes "a \<in> S"
  assumes "b \<in> S"
  shows "\<exists>c c' c''. c \<in> S \<and> c' \<in> S \<and> c'' \<in> S \<and> to_fun g a= c \<oplus> c'\<otimes> (a \<ominus> b) \<oplus>  (c'' \<otimes> (a \<ominus>  b)[^](2::nat))"
  using UP_subring_taylor_appr[of S g a b] assms UP_subring_deriv_closed[of S g b] UP_subring_eval_closed[of S g b]
  by blast 

lemma (in UP_cring) pderiv_cfs: 
  assumes"g \<in> carrier (UP R)"
  shows "pderiv g n = [Suc n]\<cdot>(g (Suc n))"
  unfolding pderiv_def  
  using n_mult_closed[of g] assms  poly_shift_cfs[of "n_mult g" n] 
  unfolding P_def n_mult_def by blast

lemma(in ring) subring_add_pow:
  assumes "subring S R"
  assumes "a \<in> S"
  shows "[(n::nat)] \<cdot>\<^bsub>R\<lparr>carrier := S\<rparr>\<^esub> a = [(n::nat)] \<cdot>a"
proof-
  have 0: "a \<in> carrier R"
    using assms(1) assms(2) subringE(1) by blast
  have 1: "a \<in> carrier (R\<lparr>carrier := S\<rparr>)"
    by (simp add: assms(2))
  show ?thesis
  apply(induction n)
  using assms 0 1 carrier_update[of S] 
  apply (simp add: add_pow_def)
  using assms 0 1 carrier_update[of S] 
  by (simp add: add_pow_def)
qed

lemma(in UP_cring) UP_subring_pderiv_equal:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "pderiv g = UP_cring.pderiv (R\<lparr>carrier := S\<rparr>) g"
proof fix n
  show "pderiv g n = UP_cring.pderiv (R\<lparr>carrier := S\<rparr>) g n"
    using UP_cring.pderiv_cfs[of "R \<lparr> carrier := S \<rparr>" g n] pderiv_cfs[of g n]
          assms R.subring_add_pow[of S "g (Suc n)" "Suc n"]
    by (simp add: UP_ring_subring(1) UP_ring_subring_car)
qed
  
lemma(in UP_cring) UP_subring_pderiv_closed:
  assumes "subring S R"
  assumes "g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  shows "pderiv g \<in> carrier (UP (R \<lparr> carrier := S \<rparr>))"
  using assms UP_cring.pderiv_closed[of "R \<lparr> carrier := S \<rparr>" g] R.carrier_update(1) UP_ring_subring(1)
UP_subring_pderiv_equal by auto

lemma(in UP_cring) UP_subring_pderiv_closed':
  assumes "subring S R"
  assumes "g \<in> carrier (UP R)"
  assumes "\<And>n. g n \<in> S"
  shows "\<And>n. pderiv g n \<in> S"
  using assms UP_subring_pderiv_closed[of S g] poly_cfs_subring[of S g] UP_ring_subring_car
  by blast

lemma(in UP_cring) taylor_deg_one_expansion_subring:
  assumes "f \<in> carrier (UP R)"
  assumes "subring S R"
  assumes "\<And>i. f i \<in> S"
  assumes "a \<in> S"
  assumes "b \<in> S"
  shows "\<exists>c \<in> S. to_fun f b = (to_fun f a) \<oplus> (deriv f a) \<otimes> (b \<ominus> a) \<oplus> (c \<otimes> (b \<ominus> a)[^](2::nat))"
  apply(rule UP_subring_taylor_appr, rule assms) 
  using assms poly_cfs_subring apply blast
  by(rule assms, rule assms)
  
lemma(in UP_cring) taylor_deg_one_expansion_subring':
  assumes "f \<in> carrier (UP R)"
  assumes "subring S R"
  assumes "\<And>i. f i \<in> S"
  assumes "a \<in> S"
  assumes "b \<in> S"
  shows "\<exists>c \<in> S. to_fun f b = (to_fun f a) \<oplus> (to_fun (pderiv f) a) \<otimes> (b \<ominus> a) \<oplus> (c \<otimes> (b \<ominus> a)[^](2::nat))"
proof-
  have "S \<subseteq> carrier R"
    using assms subringE(1) by blast
  hence 0: "deriv f a = to_fun (pderiv f) a"
    using assms  pderiv_eval_deriv[of f a] unfolding P_def  by blast 
  show ?thesis 
    using assms taylor_deg_one_expansion_subring[of f S a b]
    unfolding 0 by blast 
qed

end
