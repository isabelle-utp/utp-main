(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Simon Foster
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

theory Quantales
  imports Kleene_Algebras Omega_Algebra Galois_Connections
begin

context complete_lattice
begin

  lemma Sup_is_sup: "is_sup (\<Squnion> A) A"
    by (simp add: local.Sup_le_iff local.is_sup_def)

  lemma Sup_as_THE [simp]: "(THE w. is_sup w A) = \<Squnion> A"
  proof -
    have "is_sup (THE w. is_sup w A) A"
      by (auto intro: theI Sup_is_sup simp add: Sup_is_sup is_sup_unique)
    thus ?thesis
      using Sup_is_sup local.is_sup_unique by blast
  qed

end

lemma lfp_equality [intro?]: 
  assumes "mono f" "f x = x" "\<And>y. f y = y \<Longrightarrow> x \<le> y"
  shows "x = lfp f"
proof -
  from assms(1,3) have "x \<le> lfp f"
    using lfp_unfold[of f] by auto
  moreover have "lfp f \<le> x"
    by (simp add: assms(2) lfp_lowerbound)
  ultimately show ?thesis
    by (simp add: order_class.antisym)
qed

lemma gfp_equality [intro?]: 
  assumes "mono f" "f x = x" "\<And>y. f y = y \<Longrightarrow> y \<le> x"
  shows "x = gfp f"
proof -
  from assms(1,3) have "gfp f \<le> x"
    using gfp_unfold[of f] by auto
  moreover have "x \<le> gfp f"
    by (simp add: assms(2) gfp_upperbound)
  ultimately show ?thesis
    by (simp add: order_class.antisym)
qed

theorem lfp_fusion_leq [simp]:
  assumes upper_ex: "lower_adjoint f"
  and hiso: "mono h" and kiso: "mono k"
  and comm: "f\<circ>h \<le> k\<circ>f"
  shows "f (lfp h) \<le> lfp k"
proof (rule lfp_greatest)
  fix y assume ky: "k y \<le> y"
  obtain g where conn: "galois_connection f g" 
    using lower_adjoint_def upper_ex by blast
  have "lfp h \<le> g y" using hiso
  proof (rule_tac lfp_lowerbound)
    have "f (g y) \<le> y" 
      using conn galois_connection_def by blast
    hence "f (h (g y)) \<le> y" 
      by (metis comm comp_def kiso ky le_fun_def mono_def order.trans)
    thus "h (g y) \<le> g y"
      using conn galois_connection_def by blast
  qed
  thus "f (lfp h) \<le> y" 
    using conn galois_connection_def by blast
qed

theorem lfp_fusion [simp]:
  assumes upper_ex: "lower_adjoint f"
  and hiso: "mono h" and kiso: "mono k"
  and comm: "f\<circ>h = k\<circ>f"
  shows "f (lfp h) = lfp k"
proof
  from kiso show "mono k"
    by simp
next
  show "k (f (lfp h)) = f (lfp h)"
    by (metis comm comp_eq_dest hiso lfp_unfold)
next
  fix y assume ky: "k y = y"
  obtain g where conn: "galois_connection f g" 
    using lower_adjoint_def upper_ex by blast
  have "lfp h \<le> g y" using hiso
  proof (rule_tac lfp_lowerbound)
    have "f (g y) \<le> y" 
      using conn galois_connection_def by blast
    hence "f (h (g y)) \<le> y" 
      using comm comp_eq_dest kiso ky order_class.monoD by fastforce
    thus "h (g y) \<le> g y"
      using conn galois_connection_def by blast
  qed
  thus "f (lfp h) \<le> y" 
    using conn galois_connection_def by blast
qed

theorem gfp_fusion_geq [simp]:
  assumes upper_ex: "upper_adjoint g"
  and hiso: "mono h" and kiso: "mono k"
  and comm: "g\<circ>h \<ge> k\<circ>g"
  shows "g (gfp h) \<ge> gfp k"
proof (rule gfp_least)
  fix y assume ky: "k y \<ge> y"
  obtain f where conn: "galois_connection f g"
    using upper_ex upper_adjoint_def by blast
  have "f y \<le> gfp h" using hiso
  proof (rule_tac gfp_upperbound)
    have "y \<le> g (f y)" 
      using conn galois_connection_def by blast
    hence "y \<le> g (h (f y))"
      by (metis (no_types, lifting) comm comp_eq_dest_lhs kiso ky le_fun_def monoD order_trans)
    thus "f y \<le> h (f y)" 
      using conn galois_connection_def by blast
  qed
  thus "y \<le> g (gfp h)"
    using conn galois_connection_def by blast
qed

theorem gfp_fusion [simp]:
  assumes upper_ex: "upper_adjoint g"
  and hiso: "mono h" and kiso: "mono k"
  and comm: "g\<circ>h = k\<circ>g"
  shows "g (gfp h) = gfp k"
proof
  from assms show "mono k" by simp
next
  show "k (g (gfp h)) = g (gfp h)" 
    by (metis comm comp_eq_dest gfp_unfold hiso)
next
  fix y assume ky: "k y = y"
  obtain f where conn: "galois_connection f g"
    using upper_ex upper_adjoint_def by blast
  have "f y \<le> gfp h" using hiso
  proof (rule_tac gfp_upperbound)
    have "y \<le> g (f y)" 
      using conn galois_connection_def by blast
    hence "y \<le> g (h (f y))"
      using comm comp_eq_dest kiso ky order_class.monoD by fastforce
    thus "f y \<le> h (f y)" 
      using conn galois_connection_def by blast
  qed
  thus "y \<le> g (gfp h)"
    using conn galois_connection_def by blast
qed

default_sort complete_lattice

definition join_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "join_preserving f \<longleftrightarrow> (\<forall> X. \<Squnion> (f ` X) = f (\<Squnion> X))"

definition meet_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "meet_preserving g \<longleftrightarrow> (\<forall> X. \<Sqinter> (g ` X) = g (\<Sqinter> X))"

lemma lower_adjoint_join_preserving:
  assumes "lower_adjoint f"
  shows "join_preserving f"
proof (unfold join_preserving_def SUP_def, intro allI impI)
  obtain g where conn: "galois_connection f g" 
    using assms lower_adjoint_def by blast
  fix X :: "'a set"
  show "\<Squnion>(f ` X) = f (\<Squnion> X)"
  proof -
    have a: "\<forall>y. (f (\<Squnion> X) \<le> y) = (\<forall>z \<in> f`X. z \<le> y)"
      using Sup_least conn galois_connection_def
      by (auto, meson Sup_upper dual_order.trans lower_iso monoD, fastforce)
    moreover have "\<forall>y. (\<forall>z \<in> f`X. z \<le> y) = (\<Squnion> (f ` X) \<le> y)"
    proof
      fix y
      have "\<forall>z \<in> f`X. z \<le> y \<Longrightarrow> \<Squnion> (f ` X) \<le> y"
        using Sup_least by blast
      moreover have "\<Squnion> (f ` X) \<le> y \<Longrightarrow> \<forall>z \<in> f`X. z \<le> y"
        by (meson Sup_upper dual_order.trans)
      ultimately show "(\<forall>z \<in> f`X. z \<le> y) = (\<Squnion> (f ` X) \<le> y)"
        by blast
    qed
    ultimately have "\<forall>y. (f (\<Squnion> X) \<le> y) = (\<Squnion> (f ` X) \<le> y)" by metis
    thus "\<Squnion> (f ` X) = f (\<Squnion> X)" by (metis eq_iff)
  qed
qed  

theorem galois_suprema:
  assumes "mono f" "join_preserving f"
  shows "galois_connection f (\<lambda> y. \<Squnion> {x. f x \<le> y})"
proof (auto simp add: galois_connection_def)
  fix x y
  assume "f x \<le> y"
  thus "x \<le> \<Squnion>{x. f x \<le> y}"
    by (simp add: Sup_upper)
next
  fix x y
  assume a2: "x \<le> \<Squnion>{x. f x \<le> y}"
  show "f x \<le> y"
  proof -
    have lem: "\<Squnion> (f ` {x. f x \<le> y}) \<le> y"
      by (metis (mono_tags, lifting) SUP_def SUP_least mem_Collect_eq)
    have "f x \<le> y \<Longrightarrow> x \<le> \<Squnion> {z. f z \<le> y}" 
      using a2 by blast
    moreover have "x \<le> \<Squnion> {z. f z \<le> y} \<Longrightarrow> f x \<le> f (\<Squnion> {z. f z \<le> y})"
      using assms(1) monoD by blast
    moreover have "(f x \<le> f (\<Squnion> {z. f z \<le> y})) = (f x \<le> \<Squnion> (f ` {z. f z \<le> y}))"
      by (metis assms(2) join_preserving_def)
    moreover have "... \<Longrightarrow> f x \<le> y" using lem by (metis order_trans)
    ultimately show ?thesis
      using a2 by blast
  qed
qed

theorem join_preserving_lower_adjoint:
  assumes "mono f" "join_preserving f"
  shows "lower_adjoint f"
  using assms 
  by (auto simp add: lower_adjoint_def intro: galois_suprema)

theorem galois_infima: 
  assumes "mono g" "meet_preserving g"
  shows "galois_connection (\<lambda> x. \<Sqinter> {y. x \<le> g y}) g"
proof (auto simp add: galois_connection_def)
  fix x y
  assume a2: "\<Sqinter>{y. x \<le> g y} \<le> y"
  show "x \<le> g y"
  proof -
    have lem: "x \<le> \<Sqinter> (g ` {y. x \<le> g y})"
      by (metis (no_types, lifting) INF_greatest Inf_image_eq mem_Collect_eq)

    have "x \<le> g y \<Longrightarrow> \<Sqinter> {z. x \<le> g z} \<le> y"
      using a2 by blast
    moreover have "\<Sqinter> {z. x \<le> g z} \<le> y \<Longrightarrow> g (\<Sqinter> {z. x \<le> g z}) \<le> g y"
      using assms(1) monoD by blast
    moreover have "(g (\<Sqinter> {z. x \<le> g z}) \<le> g y) = (\<Sqinter> (g ` {z. x \<le> g z}) \<le> g y)"
      by (metis assms(2) meet_preserving_def)
    moreover have "... \<Longrightarrow> x \<le> g y" using lem by (metis order_trans)
    ultimately show ?thesis using a2 by blast
  qed
next
  fix x y
  assume "x \<le> g y"
  thus "\<Sqinter>{y. x \<le> g y} \<le> y"
    by (simp add: Inf_lower)
qed

theorem meet_preserving_upper_adjoint:
  assumes "mono f" "meet_preserving f"
  shows "upper_adjoint f"
  using assms 
  by (auto simp add: upper_adjoint_def intro: galois_infima)

default_sort type

class quantale = complete_lattice + semigroup_mult +
  assumes Sup_distl: "x \<cdot> \<Squnion> Y = \<Squnion> ((\<lambda> y. x\<cdot>y) ` Y)"
  and Sup_distr: "\<Squnion> Y \<cdot> x = \<Squnion> ((\<lambda> y. y\<cdot>x) ` Y)"
begin

  lemma bot_zeror: "x \<cdot> \<bottom> = \<bottom>"
  proof -
    have "x \<cdot> bot = x \<cdot> Sup {}"
      by simp
    also have "... = Sup ((\<lambda> y. x\<cdot>y) ` {})"
      using Sup_distl by blast
    finally show ?thesis
      by simp
  qed

  lemma bot_zerol: "\<bottom> \<cdot> x = \<bottom>"
  proof -
    have "\<bottom> \<cdot> x = \<Squnion> {} \<cdot> x"
      by simp
    also have "... = \<Squnion> ((\<lambda> y. y\<cdot>x) ` {})"
      using Sup_distr by blast
    finally show ?thesis
      by simp
  qed

  lemma qdistl1: "x \<cdot> (y \<squnion> z) = (x \<cdot> y) \<squnion> (x \<cdot> z)"
  proof -
    have "x \<cdot> \<Squnion> {y,z} = \<Squnion> ((\<lambda>y. x\<cdot>y) ` {y,z})" using Sup_distl .
    thus ?thesis by simp
  qed

  lemma qdistr1: "(y \<squnion> z) \<cdot> x = (y \<cdot> x) \<squnion> (z \<cdot> x)"
  proof -
    have "\<Squnion> {y,z} \<cdot> x = \<Squnion> ((\<lambda>y. y\<cdot>x) ` {y,z})" using Sup_distr .
    thus ?thesis by simp
  qed

  lemma qmult_isotonel: "x \<le> y \<Longrightarrow> x\<cdot>z \<le> y\<cdot>z"
    by (metis local.sup.absorb1 local.sup.orderI qdistr1)    

  lemma qmult_isotoner: "y \<le> z \<Longrightarrow> x\<cdot>y \<le> x\<cdot>z"
    by (metis local.sup.absorb1 local.sup.orderI qdistl1)    
end

lemma qmult_join_preserving:
  fixes x :: "'a :: quantale"
  shows "join_preserving (\<lambda>y. x\<cdot>y)"
    by (unfold join_preserving_def SUP_def Sup_distl, simp)

lemma qmult_lower_adjoint:
  fixes x :: "'a :: quantale"
  shows "lower_adjoint (\<lambda>y. x\<cdot>y)"
  by (simp add: join_preserving_lower_adjoint monoI qmult_isotoner qmult_join_preserving)

sublocale quantale \<subseteq> dioid
  where plus = "op \<squnion>"
proof
  fix x y z :: 'a
  show "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
    by (simp add: local.qdistr1)
  show "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
    by (simp add: local.qdistl1)
  show "x \<squnion> y \<squnion> z = x \<squnion> (y \<squnion> z)"
    by (simp add: local.sup_assoc)
  show "x \<squnion> y = y \<squnion> x"
    by (simp add: local.sup_commute)
  show "x \<le> y \<longleftrightarrow> x \<squnion> y = y"
    by (simp add: local.le_iff_sup)
  show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
    by auto
  show "x \<squnion> x = x"
    by simp
qed

class quantale_plus = quantale +
  assumes Inf_distl: "x \<squnion> \<Sqinter> Y = \<Sqinter> ((\<lambda> y. x\<squnion>y) ` Y)"
  and Inf_distr: "\<Sqinter> Y \<squnion> x = \<Sqinter> ((\<lambda> y. y\<squnion>x) ` Y)"
begin

  lemma qplus_distl1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  proof -
    have "x \<squnion> \<Sqinter> {y,z} = \<Sqinter> ((\<lambda>y. x\<squnion>y) ` {y,z})" using Inf_distl .
    thus ?thesis by simp
  qed

  lemma qplus_qdistr1: "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  proof -
    have "\<Sqinter> {y,z} \<squnion> x = \<Sqinter> ((\<lambda>y. y\<squnion>x) ` {y,z})" using Inf_distr .
    thus ?thesis by simp
  qed

  lemma qplus_isotonel: "x \<le> y \<Longrightarrow> x\<squnion>z \<le> y\<squnion>z"
    by (metis local.inf.orderI local.inf_absorb1 qplus_qdistr1)    

  lemma qplus_isotoner: "y \<le> z \<Longrightarrow> x\<squnion>y \<le> x\<squnion>z"
    by (metis local.inf.orderI local.inf_absorb1 qplus_distl1)    

end

lemma qplus_meet_preserving:
  fixes x :: "'a :: quantale_plus"
  shows "meet_preserving (\<lambda>y. x\<squnion>y)"
    by (unfold meet_preserving_def INF_def Inf_distl, simp)

lemma qplus_upper_adjoint:
  fixes x :: "'a :: quantale_plus"
  shows "upper_adjoint (\<lambda>y. x\<squnion>y)"
  by (meson meet_preserving_upper_adjoint monoI qplus_isotoner qplus_meet_preserving)

(* +------------------------------------------------------------------------+
   | Unital Quantales                                                       |
   +------------------------------------------------------------------------+ *)

class unital_quantale = quantale + monoid_mult

sublocale unital_quantale \<subseteq> dioid_one_zero
  where plus = "op \<squnion>" and zero = "\<bottom>"
proof
  fix x y z :: 'a
  show "1 \<cdot> x = x" by simp
  show "x \<cdot> 1 = x" by simp
  show "\<bottom> \<squnion> x = x" by simp
  show "\<bottom> \<cdot> x = \<bottom>"
    by (simp add: local.bot_zerol)
  show "x \<cdot> \<bottom> = \<bottom>"
    by (simp add: local.bot_zeror)
qed

context unital_quantale
begin

  definition "qstar x = \<Squnion> (powers x)"

  lemma set_predicate_eq: "\<forall>x. P x = Q x \<Longrightarrow> {x. P x} = {x. Q x}"
    by (metis (no_types) order_eq_iff predicate1I)

  lemma qstar_distl: "x \<cdot> qstar y = \<Squnion> {x\<cdot>z|z. (\<exists>i. z = y ^ i)}"
  proof (unfold qstar_def powers_def Sup_distl SUP_def, rule_tac f = "\<lambda>x. \<Squnion> x" in arg_cong)
    have "op \<cdot> x ` {z. \<exists>i. z = y ^ i} = {z. \<exists>p. (\<exists>i. p = y ^ i) \<and> z = x \<cdot> p}"
      by (simp add: image_def)
    also have "... = {z. \<exists>i. z = x \<cdot> y ^ i}"
      by (rule set_predicate_eq, blast)
    also have "... = {x \<cdot> w |w. \<exists>i. w = y ^ i}"
      by blast
    finally show "op \<cdot> x ` {z. \<exists>i. z = y ^ i} = {x \<cdot> w |w. \<exists>i. w = y ^ i}"
      by metis
  qed

  lemma qstar_distr: "qstar x \<cdot> y = \<Squnion> {z\<cdot>y|z. (\<exists>i. z = x ^ i)}"    
    by (unfold qstar_def powers_def Sup_distr, rule_tac f = "\<lambda>x. \<Squnion> x" in arg_cong, auto)

end

sublocale unital_quantale \<subseteq> star_continuous_ka
  where plus = "op \<squnion>" and zero = "\<bottom>" and star = qstar
proof (unfold_locales, clarify)
  fix x y z :: 'a
  show "\<exists>w. is_sup w (powers_c x y z)" 
    using local.Sup_is_sup by blast
  show "x \<cdot> qstar y \<cdot> z = (THE w. is_sup w (powers_c x y z))"
    by (simp only: Sup_as_THE qstar_distl Sup_distr, rule_tac f = "\<lambda>X. \<Squnion> X" in arg_cong)
       (auto simp add: powers_c_def)
qed

lemma qstar_lfp_def:
  fixes x :: "'a::unital_quantale"  
  shows "qstar x = lfp(\<lambda>y. 1 \<squnion> y\<cdot>x)"
proof
  show "mono (\<lambda>y. 1 \<squnion> y \<cdot> x)"
    using qmult_isotonel quantale_class.add_iso_var by (blast intro: monoI)
  show "1 \<squnion> qstar x \<cdot> x = qstar x"
    by simp
  fix y
  show "1 \<squnion> y \<cdot> x = y \<Longrightarrow> qstar x \<le> y"
    using unital_quantale_class.star_inductr_eq by fastforce
qed

class unital_quantale_plus = unital_quantale + quantale_plus
begin

definition "qomega a = gfp (\<lambda> x. a \<cdot> x)"

end

lemma qomega_unfold: 
  fixes x :: "'a :: unital_quantale_plus"
  shows "qomega x = x \<cdot> qomega x"
  apply (auto simp add: qomega_def)
  apply (subst gfp_unfold)
  apply (auto intro: monoI qmult_isotoner)
done

lemma omega_left:
  fixes a :: "'a :: unital_quantale_plus"
  assumes "y = a \<squnion> y \<cdot> b"
  shows "gfp (\<lambda> x. a \<squnion> x \<cdot> b) = y \<squnion> gfp (\<lambda> x. x \<cdot> b)"
proof -
  have upj: "upper_adjoint (\<lambda> x. y \<squnion> x)"
    using qplus_upper_adjoint by blast
  moreover have "mono (\<lambda>x. x \<cdot> b)"
    using mono_def qmult_isotonel by blast
  moreover have "mono (\<lambda>x. a \<squnion> x \<cdot> b)"
    by (metis calculation(2) mono_def qplus_isotoner)
  moreover have "\<forall> x. a \<squnion> (y \<squnion> x) \<cdot> b = y \<squnion> x \<cdot> b"
    by (metis add_commute assms quantale_class.add_assoc' quantale_class.distrib_right')
  ultimately show ?thesis
    by (rule_tac gfp_fusion[OF upj, THEN sym], auto)
qed

lemma omega_right:
  fixes a :: "'a :: unital_quantale_plus"
  assumes "y = a \<squnion> b \<cdot> y"
  shows "gfp (\<lambda> x. a \<squnion> b \<cdot> x) = y \<squnion> gfp (\<lambda> x. b \<cdot> x)"
proof -
  have upj: "upper_adjoint (\<lambda> x. y \<squnion> x)"
    using qplus_upper_adjoint by blast
  moreover have "mono (\<lambda>x. b \<cdot> x)"
    by (simp add: monoI quantale_class.mult_isol)
  moreover have "mono (\<lambda>x. a \<squnion> b \<cdot> x)"
    by (metis calculation(2) mono_def qplus_isotoner)
  moreover have "\<forall> x. a \<squnion> b \<cdot> (y \<squnion> x) = y \<squnion> b \<cdot> x"
    by (metis add_commute assms quantale_class.add_assoc' quantale_class.distrib_left)
  ultimately show ?thesis
    by (rule_tac gfp_fusion[OF upj, THEN sym], auto)
qed

lemma qomega_fusion:
  "qomega a \<squnion> qstar a \<cdot> b = gfp (\<lambda>x. b \<squnion> a \<cdot> x)"
proof -
  have q: "qstar a \<cdot> b = b \<squnion> a \<cdot> (qstar a \<cdot> b)"
  proof -
    have "qstar a \<cdot> b = (1 \<squnion> a \<cdot> qstar a) \<cdot> b"
      by simp
    also have "... = 1 \<cdot> b \<squnion> a \<cdot> qstar a \<cdot> b"
      using quantale_class.distrib_right' by blast
    finally show ?thesis
      by (metis mult.assoc mult.left_neutral)
  qed

  have "qomega a \<squnion> qstar a \<cdot> b = gfp (\<lambda> x. a \<cdot> x) \<squnion> qstar a \<cdot> b"
    by (simp add: qomega_def)

  moreover have "... = gfp (\<lambda> x. b \<squnion> a \<cdot> x)"
    by (simp add: omega_right[OF q])

  ultimately show ?thesis by simp
qed

lemma qomega_coinduct:
  fixes x :: "'a :: unital_quantale_plus"
  assumes "y \<le> z \<squnion> x \<cdot> y" 
  shows "y \<le> qomega x \<squnion> qstar x \<cdot> z"
proof -
  have "y \<le> gfp (\<lambda> y. z \<squnion> x \<cdot> y)"
    by (simp add: assms gfp_upperbound)
  thus ?thesis
    by (simp add: qomega_fusion[of x z])
qed

end