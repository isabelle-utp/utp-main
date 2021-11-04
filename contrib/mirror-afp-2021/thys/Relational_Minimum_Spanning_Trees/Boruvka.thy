(* Title:      Borůvka's Minimum Spanning Tree Algorithm
   Author:     Nicolas Robinson-O'Brien
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Bor\r{u}vka's Minimum Spanning Tree Algorithm\<close>

text \<open>
In this theory we prove partial correctness of Bor\r{u}vka's minimum spanning tree algorithm.
\<close>

theory Boruvka

imports
  Relational_Disjoint_Set_Forests.Disjoint_Set_Forests
  Kruskal

begin

subsection \<open>General results\<close>

text \<open>
The proof is carried out in $m$-$k$-Stone-Kleene relation algebras.
In this section we give results that hold more generally.
\<close>

context stone_kleene_relation_algebra
begin

definition "big_forest H d \<equiv>
    equivalence H
  \<and> d \<le> -H
  \<and> univalent (H * d)
  \<and> H \<sqinter> d * d\<^sup>T \<le> 1
  \<and> (H * d)\<^sup>+ \<le> - H"

definition "bf_between_points p q H d \<equiv> point p \<and> point q \<and> p \<le> (H * d)\<^sup>\<star> * H * d"

definition "bf_between_arcs a b H d \<equiv> arc a \<and> arc b \<and> a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top"

text \<open>Theorem 3\<close>

lemma He_eq_He_THe_star:
  assumes "arc e"
    and "equivalence H"
  shows "H * e = H * e * (top * H * e)\<^sup>\<star>"
proof -
  let ?x = "H * e"
  have 1: "H * e \<le> H * e * (top * H * e)\<^sup>\<star>"
    using comp_isotone star.circ_reflexive by fastforce
  have "H * e * (top * H * e)\<^sup>\<star> = H * e * (top * e)\<^sup>\<star>"
    by (metis assms(2) preorder_idempotent surjective_var)
  also have "... \<le> H * e * (1 \<squnion> top * (e * top)\<^sup>\<star> * e)"
    by (metis eq_refl star.circ_mult_1)
  also have "... \<le> H * e * (1 \<squnion> top * top * e)"
    by (simp add: star.circ_left_top)
  also have "... = H * e \<squnion> H * e * top * e"
    by (simp add: mult.semigroup_axioms semiring.distrib_left semigroup.assoc)
  finally have 2: "H * e * (top * H * e)\<^sup>\<star> \<le> H * e"
    using assms arc_top_arc mult_assoc by auto
  thus ?thesis
    using 1 2 by simp
qed

lemma path_through_components:
  assumes "equivalence H"
    and "arc e"
  shows "(H * (d \<squnion> e))\<^sup>\<star> = (H * d)\<^sup>\<star> \<squnion> (H * d)\<^sup>\<star> * H * e * (H * d)\<^sup>\<star>"
proof -
  have "H * e * (H * d)\<^sup>\<star> * H * e \<le> H * e * top * H * e"
    by (simp add: comp_isotone)
  also have "... = H * e * top * e"
    by (metis assms(1) preorder_idempotent surjective_var mult_assoc)
  also have "... = H * e"
    using assms(2) arc_top_arc mult_assoc by auto
  finally have 1: "H * e * (H * d)\<^sup>\<star> * H * e \<le> H * e"
    by simp
  have "(H * (d \<squnion> e))\<^sup>\<star> = (H * d \<squnion> H * e)\<^sup>\<star>"
    by (simp add: comp_left_dist_sup)
  also have "... = (H * d)\<^sup>\<star> \<squnion> (H * d)\<^sup>\<star> * H * e * (H * d)\<^sup>\<star>"
    using 1 star_separate_3 by (simp add: mult_assoc)
  finally show ?thesis
    by simp
qed

lemma simplify_f:
  assumes "regular p"
    and "regular e"
  shows "(f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> - p)\<^sup>T \<squnion> e\<^sup>T \<squnion> e = f \<squnion> f\<^sup>T \<squnion> e \<squnion> e\<^sup>T"
proof -
  have "(f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> - p)\<^sup>T \<squnion> e\<^sup>T \<squnion> e
    = (f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p) \<squnion> (f\<^sup>T \<sqinter> - e \<sqinter> p\<^sup>T) \<squnion> (f\<^sup>T \<sqinter> - e \<sqinter> - p\<^sup>T) \<squnion> e\<^sup>T \<squnion> e"
    by (simp add: conv_complement conv_dist_inf)
  also have "... =
      ((f \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)) \<sqinter> (- e\<^sup>T \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)) \<sqinter> (- p \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)))
    \<squnion> ((f\<^sup>T \<squnion> (f\<^sup>T \<sqinter> - e \<sqinter> - p\<^sup>T)) \<sqinter> (- e \<squnion> (f\<^sup>T \<sqinter> - e \<sqinter> - p\<^sup>T)) \<sqinter> (p\<^sup>T \<squnion> (f\<^sup>T \<sqinter> - e \<sqinter> - p\<^sup>T)))
    \<squnion> e\<^sup>T \<squnion> e"
    by (metis sup_inf_distrib2 sup_assoc)
  also have "... =
      ((f \<squnion> f) \<sqinter> (f \<squnion> - e\<^sup>T) \<sqinter> (f \<squnion> p) \<sqinter> (- e\<^sup>T \<squnion> f) \<sqinter> (- e\<^sup>T \<squnion> - e\<^sup>T) \<sqinter> (- e\<^sup>T \<squnion> p) \<sqinter> (- p \<squnion> f) \<sqinter> (- p \<squnion> - e\<^sup>T) \<sqinter> (- p \<squnion> p))
    \<squnion> ((f\<^sup>T \<squnion> f\<^sup>T) \<sqinter> (f\<^sup>T \<squnion> - e) \<sqinter> (f\<^sup>T \<squnion> - p\<^sup>T) \<sqinter> (- e \<squnion> f\<^sup>T) \<sqinter> (- e \<squnion> - e) \<sqinter> (- e \<squnion> - p\<^sup>T) \<sqinter> (p\<^sup>T \<squnion> f\<^sup>T) \<sqinter> (p\<^sup>T \<squnion> - e) \<sqinter> (p\<^sup>T \<squnion> - p\<^sup>T))
    \<squnion> e\<^sup>T \<squnion> e"
    using sup_inf_distrib1 sup_assoc inf_assoc sup_inf_distrib1 by simp
  also have "... =
      ((f \<squnion> f) \<sqinter> (f \<squnion> - e\<^sup>T) \<sqinter> (f \<squnion> p) \<sqinter> (f \<squnion> - p) \<sqinter> (- e\<^sup>T \<squnion> f) \<sqinter> (- e\<^sup>T \<squnion> - e\<^sup>T) \<sqinter> (- e\<^sup>T \<squnion> p) \<sqinter> (- e\<^sup>T \<squnion> - p) \<sqinter> (- p \<squnion> p))
    \<squnion> ((f\<^sup>T \<squnion> f\<^sup>T) \<sqinter> (f\<^sup>T \<squnion> - e) \<sqinter> (f\<^sup>T \<squnion> - p\<^sup>T) \<sqinter> (- e \<squnion> f\<^sup>T) \<sqinter> (f\<^sup>T \<squnion> p\<^sup>T) \<sqinter> (- e \<squnion> - e) \<sqinter> (- e \<squnion> - p\<^sup>T) \<sqinter> (- e \<squnion> p\<^sup>T) \<sqinter> (p\<^sup>T \<squnion> - p\<^sup>T))
    \<squnion> e\<^sup>T \<squnion> e"
    by (smt abel_semigroup.commute inf.abel_semigroup_axioms inf.left_commute sup.abel_semigroup_axioms)
  also have "... = (f \<sqinter> - e\<^sup>T \<sqinter> (- p \<squnion> p)) \<squnion> (f\<^sup>T \<sqinter> - e \<sqinter> (p\<^sup>T \<squnion> - p\<^sup>T)) \<squnion> e\<^sup>T \<squnion> e"
    by (smt inf.sup_monoid.add_assoc inf.sup_monoid.add_commute inf_sup_absorb sup.idem)
  also have "... = (f \<sqinter> - e\<^sup>T) \<squnion> (f\<^sup>T \<sqinter> - e) \<squnion> e\<^sup>T \<squnion> e"
    by (metis assms(1) conv_complement inf_top_right stone)
  also have "... = (f \<squnion> e\<^sup>T) \<sqinter> (- e\<^sup>T \<squnion> e\<^sup>T) \<squnion> (f\<^sup>T \<squnion> e) \<sqinter> (- e \<squnion> e)"
    by (metis sup.left_commute sup_assoc sup_inf_distrib2)
  finally show ?thesis
    by (metis abel_semigroup.commute assms(2) conv_complement inf_top_right stone sup.abel_semigroup_axioms sup_assoc)
qed

lemma simplify_forest_components_f:
  assumes "regular p"
    and "regular e"
    and "injective (f \<sqinter> - e\<^sup>T \<sqinter> - p \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e)"
    and "injective f"
  shows "forest_components ((f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> -e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e) = (f \<squnion> f\<^sup>T \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
proof -
  have "forest_components ((f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> -e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e) = wcc ((f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e)"
    by (simp add: assms(3) forest_components_wcc)
  also have "... = ((f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> - p)\<^sup>T \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p) \<squnion> e\<^sup>T)\<^sup>\<star>"
    using conv_dist_sup sup_assoc by auto
  also have "... = ((f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p) \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> - p)\<^sup>T \<squnion> e\<^sup>T \<squnion> e)\<^sup>\<star>"
    using sup_assoc sup_commute by auto
  also have "... = (f \<squnion> f\<^sup>T \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    using assms(1, 2, 3, 4) simplify_f by auto
  finally show ?thesis
    by simp
qed

lemma components_disj_increasing:
  assumes "regular p"
    and "regular e"
    and "injective (f \<sqinter> - e\<^sup>T \<sqinter> - p \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e)"
    and "injective f"
  shows "forest_components f \<le> forest_components (f \<sqinter> - e\<^sup>T \<sqinter> - p \<squnion> (f \<sqinter> - e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e)"
proof -
  have 1: "forest_components ((f \<sqinter> - e\<^sup>T \<sqinter> - p) \<squnion> (f \<sqinter> -e\<^sup>T \<sqinter> p)\<^sup>T \<squnion> e) = (f \<squnion> f\<^sup>T \<squnion> e \<squnion> e\<^sup>T)\<^sup>\<star>"
    using simplify_forest_components_f assms(1, 2, 3, 4) by blast
  have "forest_components f = wcc f"
    by (simp add: assms(4) forest_components_wcc)
  also have "... \<le> (f \<squnion> f\<^sup>T \<squnion> e\<^sup>T \<squnion> e)\<^sup>\<star>"
    by (simp add: le_supI2 star_isotone sup_commute)
  finally show ?thesis
    using 1 sup.left_commute sup_commute by simp
qed

lemma fch_equivalence:
  assumes "forest h"
  shows "equivalence (forest_components h)"
  by (simp add: assms forest_components_equivalence)

lemma big_forest_path_split_1:
  assumes "arc a"
    and "equivalence H"
  shows "(H * d)\<^sup>\<star> * H * a * top = (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top"
proof -
  let ?H = "H"
  let ?x = "?H * (d \<sqinter> -a)"
  let ?y = "?H * a"
  let ?a = "?H * a * top"
  let ?d = "?H * d"
  have 1: "?d\<^sup>\<star> * ?a \<le> ?x\<^sup>\<star> * ?a"
  proof -
    have "?x\<^sup>\<star> *?y * ?x\<^sup>\<star> * ?a \<le> ?x\<^sup>\<star> * ?a * ?a"
      by (smt mult_left_isotone star.circ_right_top top_right_mult_increasing mult_assoc)
    also have "... = ?x\<^sup>\<star> * ?a * a * top"
      by (metis ex231e mult_assoc)
    also have "... = ?x\<^sup>\<star> * ?a"
      by (simp add: assms(1) mult_assoc)
    finally have 11: "?x\<^sup>\<star> *?y * ?x\<^sup>\<star> * ?a \<le> ?x\<^sup>\<star> * ?a"
      by simp
    have "?d\<^sup>\<star> * ?a = (?H * (d \<sqinter> a) \<squnion> ?H * (d \<sqinter> -a))\<^sup>\<star> * ?a"
    proof -
      have 12: "regular a"
        using assms(1) arc_regular by simp
      have "?H * ((d \<sqinter> a) \<squnion> (d \<sqinter> - a)) = ?H * (d \<sqinter> top)"
        using 12 by (metis inf_top_right maddux_3_11_pp)
      thus ?thesis
        using mult_left_dist_sup by auto
    qed
    also have "... \<le> (?y \<squnion> ?x)\<^sup>\<star> * ?a"
      by (metis comp_inf.coreflexive_idempotent comp_isotone inf.cobounded1 inf.sup_monoid.add_commute semiring.add_mono star_isotone top.extremum)
    also have "... = (?x \<squnion> ?y)\<^sup>\<star> * ?a"
      by (simp add: sup_commute mult_assoc)
    also have "... = ?x\<^sup>\<star> * ?a \<squnion> (?x\<^sup>\<star> * ?y * (?x\<^sup>\<star> * ?y)\<^sup>\<star> * ?x\<^sup>\<star>) * ?a"
      by (smt mult_right_dist_sup star.circ_sup_9 star.circ_unfold_sum mult_assoc)
    also have "... \<le> ?x\<^sup>\<star> * ?a \<squnion> (?x\<^sup>\<star> * ?y * (top * ?y)\<^sup>\<star> * ?x\<^sup>\<star>) * ?a"
    proof -
      have "(?x\<^sup>\<star> * ?y)\<^sup>\<star> \<le> (top * ?y)\<^sup>\<star>"
        by (simp add: mult_left_isotone star_isotone)
      thus ?thesis
        by (metis comp_inf.coreflexive_idempotent comp_inf.transitive_star eq_refl mult_left_dist_sup top.extremum mult_assoc)
    qed
    also have "... = ?x\<^sup>\<star> * ?a \<squnion> (?x\<^sup>\<star> * ?y * ?x\<^sup>\<star>) * ?a"
      using assms(1, 2) He_eq_He_THe_star arc_regular mult_assoc by auto
    finally have 13: "(?H * d)\<^sup>\<star> * ?a \<le> ?x\<^sup>\<star> * ?a \<squnion> ?x\<^sup>\<star> * ?y * ?x\<^sup>\<star> * ?a"
      by (simp add: mult_assoc)
    have 14: "?x\<^sup>\<star> * ?y * ?x\<^sup>\<star> * ?a \<le> ?x\<^sup>\<star> * ?a"
      using 11 mult_assoc by auto
    thus ?thesis
      using 13 14 sup.absorb1 by auto
  qed
  have 2: "?d\<^sup>\<star> * ?a \<ge> ?x\<^sup>\<star> *?a"
    by (simp add: comp_isotone star_isotone)
  thus ?thesis
    using 1 2 antisym mult_assoc by simp
qed

lemma dTransHd_le_1:
  assumes "equivalence H"
    and "univalent (H * d)"
  shows "d\<^sup>T * H * d \<le> 1"
proof -
  have "d\<^sup>T * H\<^sup>T * H * d \<le> 1"
    using assms(2) conv_dist_comp mult_assoc by auto
  thus ?thesis
    using assms(1) mult_assoc by (simp add: preorder_idempotent)
qed

lemma HcompaT_le_compHaT:
  assumes "equivalence H"
    and "injective (a * top)"
  shows "-H * a * top \<le> - (H * a * top)"
proof -
  have "a * top * a\<^sup>T \<le> 1"
    by (metis assms(2) conv_dist_comp symmetric_top_closed vector_top_closed mult_assoc)
  hence "a * top * a\<^sup>T * H \<le> H"
    using assms(1) comp_isotone order_trans by blast
  hence "a * top * top * a\<^sup>T * H \<le> H"
    by (simp add: vector_mult_closed)
  hence "a * top * (H * a * top)\<^sup>T \<le> H"
    by (metis assms(1) conv_dist_comp symmetric_top_closed vector_top_closed mult_assoc)
  thus ?thesis
    using assms(2) comp_injective_below_complement mult_assoc by auto
qed

text \<open>Theorem 4\<close>

lemma expand_big_forest:
  assumes "big_forest H d"
  shows "(d\<^sup>T * H)\<^sup>\<star> * (H * d)\<^sup>\<star> = (d\<^sup>T * H)\<^sup>\<star> \<squnion> (H * d)\<^sup>\<star>"
proof -
  have "(H * d)\<^sup>T * H * d \<le> 1"
    using assms big_forest_def mult_assoc by auto
  hence "d\<^sup>T * H * H * d \<le> 1"
    using assms big_forest_def conv_dist_comp by auto
  thus ?thesis
    by (simp add: cancel_separate_eq comp_associative)
qed


lemma big_forest_path_bot:
  assumes "arc a"
    and "a \<le> d"
    and "big_forest H d"
  shows "(d \<sqinter> - a)\<^sup>T * (H * a * top) \<le> bot"
proof -
  have 1: "d\<^sup>T * H * d \<le> 1"
    using assms(3) big_forest_def dTransHd_le_1 by blast
  hence "d * - 1 * d\<^sup>T \<le> - H"
    using triple_schroeder_p by force
  hence "d * - 1 * d\<^sup>T \<le> 1 \<squnion> - H"
    by (simp add: le_supI2)
  hence "d * d\<^sup>T \<squnion> d * - 1 * d\<^sup>T \<le> 1 \<squnion> - H"
    by (metis assms(3) big_forest_def inf_commute regular_one_closed shunting_p le_supI)
  hence "d * 1 * d\<^sup>T \<squnion> d * - 1 * d\<^sup>T \<le> 1 \<squnion> - H"
    by simp
  hence "d * (1 \<squnion> - 1) * d\<^sup>T \<le> 1 \<squnion> - H"
    using comp_associative mult_right_dist_sup by (simp add: mult_left_dist_sup)
  hence "d * top * d\<^sup>T \<le> 1 \<squnion> - H"
    using regular_complement_top by auto
  hence "d * top * a\<^sup>T \<le> 1 \<squnion> - H"
    using assms(2) conv_isotone dual_order.trans mult_right_isotone by blast
  hence "d * (a * top)\<^sup>T \<le> 1 \<squnion> - H"
    by (simp add: comp_associative conv_dist_comp)
  hence "d \<le> (1 \<squnion> - H) * (a * top)"
    by (simp add: assms(1) shunt_bijective)
  hence "d \<le> a * top \<squnion> - H * a * top"
    by (simp add: comp_associative mult_right_dist_sup)
  also have "... \<le> a * top \<squnion> - (H * a * top)"
    using assms(1, 3) HcompaT_le_compHaT big_forest_def sup_right_isotone by auto
  finally have "d \<le> a * top \<squnion> - (H * a * top)"
    by simp
  hence "d \<sqinter> --( H * a * top) \<le> a * top"
    using shunting_var_p by auto
  hence 2:"d \<sqinter> H * a * top \<le> a * top"
    using inf.sup_right_isotone order.trans pp_increasing by blast
  have 3:"d \<sqinter> H * a * top \<le> top * a"
  proof -
    have "d \<sqinter> H * a * top \<le> (H * a \<sqinter> d * top\<^sup>T) * (top \<sqinter> (H * a)\<^sup>T * d)"
      by (metis dedekind inf_commute)
    also have "... = d * top \<sqinter> H * a * a\<^sup>T * H\<^sup>T * d"
      by (simp add: conv_dist_comp inf_vector_comp mult_assoc)
    also have "... \<le> d * top \<sqinter> H * a * d\<^sup>T * H\<^sup>T * d"
      using assms(2) mult_right_isotone mult_left_isotone conv_isotone inf.sup_right_isotone by auto
    also have "... = d * top \<sqinter> H * a * d\<^sup>T * H * d"
      using assms(3) big_forest_def by auto
    also have "... \<le> d * top \<sqinter> H * a * 1"
      using 1 by (metis inf.sup_right_isotone mult_right_isotone mult_assoc)
    also have "... \<le> H * a"
      by simp
    also have "... \<le> top * a"
      by (simp add: mult_left_isotone)
    finally have "d \<sqinter> H * a * top \<le> top * a"
      by simp
    thus ?thesis
      by simp
  qed
  have "d \<sqinter> H * a * top \<le> a * top \<sqinter> top * a"
    using 2 3 by simp
  also have "... = a * top * top * a"
    by (metis comp_associative comp_inf.star.circ_decompose_9 comp_inf.star_star_absorb comp_inf_covector vector_inf_comp vector_top_closed)
  also have "... = a * top * a"
    by (simp add: vector_mult_closed)
  finally have 4:"d \<sqinter> H * a * top \<le> a"
    by (simp add: assms(1) arc_top_arc)
  hence "d \<sqinter> - a \<le> -(H * a * top)"
    using assms(1) arc_regular p_shunting_swap by fastforce
  hence "(d \<sqinter> - a) * top \<le> -(H * a * top)"
    using mult.semigroup_axioms p_antitone_iff schroeder_4_p semigroup.assoc by fastforce
  thus ?thesis
    by (simp add: schroeder_3_p)
qed

lemma big_forest_path_split_2:
  assumes "arc a"
    and "a \<le> d"
    and "big_forest H d"
  shows "(H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top = (H * ((d \<sqinter> - a) \<squnion> (d \<sqinter> - a)\<^sup>T))\<^sup>\<star> * H * a * top"
proof -
  let ?lhs = "(H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top"
  have 1: "d\<^sup>T * H * d \<le> 1"
    using assms(3) big_forest_def dTransHd_le_1 by blast
  have 2: "H * a * top \<le> ?lhs"
    by (metis le_iff_sup star.circ_loop_fixpoint star.circ_transitive_equal star_involutive sup_commute mult_assoc)
  have "(d \<sqinter> - a)\<^sup>T * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top) = (d \<sqinter> - a)\<^sup>T * H * (d \<sqinter> - a) * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top)"
  proof -
    have "(d \<sqinter> - a)\<^sup>T * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top) = (d \<sqinter> - a)\<^sup>T * (1 \<squnion> H * (d \<sqinter> - a) * (H * (d \<sqinter> - a))\<^sup>\<star>) * (H * a * top)"
      by (simp add: star_left_unfold_equal)
    also have "... = (d \<sqinter> - a)\<^sup>T * H * a * top \<squnion> (d \<sqinter> - a)\<^sup>T * H * (d \<sqinter> - a) * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top)"
      by (smt mult_left_dist_sup star.circ_loop_fixpoint star.circ_mult_1 star_slide sup_commute mult_assoc)
    also have "... = bot \<squnion> (d \<sqinter> - a)\<^sup>T * H * (d \<sqinter> - a) * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top)"
      by (metis assms(1, 2, 3) big_forest_path_bot mult_assoc le_bot)
    thus ?thesis
      by (simp add: calculation)
  qed
  also have "... \<le> d\<^sup>T * H * d * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top)"
    using conv_isotone inf.cobounded1 mult_isotone by auto
  also have "... \<le> 1 * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top)"
    using 1 by (metis le_iff_sup mult_right_dist_sup)
  finally have 3: "(d \<sqinter> - a)\<^sup>T * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top) \<le> ?lhs"
    using mult_assoc by auto
  hence 4: "H * (d \<sqinter> - a)\<^sup>T * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top) \<le> ?lhs"
  proof -
    have "H * (d \<sqinter> - a)\<^sup>T * (H * (d \<sqinter> - a))\<^sup>\<star> * (H * a * top) \<le> H * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top"
      using 3 mult_right_isotone mult_assoc by auto
    also have "... = H * H * ((d \<sqinter> - a) * H)\<^sup>\<star> * H * a * top"
      by (metis assms(3) big_forest_def star_slide mult_assoc preorder_idempotent)
    also have "... = H * ((d \<sqinter> - a) * H)\<^sup>\<star> * H * a * top"
      using assms(3) big_forest_def preorder_idempotent by fastforce
    finally show ?thesis
      by (metis assms(3) big_forest_def preorder_idempotent star_slide mult_assoc)
  qed
  have 5: "(H * (d \<sqinter> - a) \<squnion> H * (d \<sqinter> - a)\<^sup>T) * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top \<le> ?lhs"
  proof -
    have 51: "H * (d \<sqinter> - a) * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top \<le> (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top"
      using star.left_plus_below_circ mult_left_isotone by simp
    have 52: "(H * (d \<sqinter> - a) \<squnion> H * (d \<sqinter> - a)\<^sup>T) * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top = H * (d \<sqinter> - a) * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top \<squnion> H * (d \<sqinter> - a)\<^sup>T * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top"
      using mult_right_dist_sup by auto
    hence "... \<le> (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top \<squnion> H * (d \<sqinter> - a)\<^sup>T * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top"
      using star.left_plus_below_circ mult_left_isotone sup_left_isotone by auto
    thus ?thesis
      using 4 51 52 mult_assoc by auto
  qed
  hence "(H * (d \<sqinter> - a) \<squnion> H * (d \<sqinter> - a)\<^sup>T)\<^sup>\<star> * H * a * top \<le> ?lhs"
  proof -
    have "(H * (d \<sqinter> - a) \<squnion> H * (d \<sqinter> - a)\<^sup>T)\<^sup>\<star> * (H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top \<le> ?lhs"
      using 5 star_left_induct_mult_iff mult_assoc by auto
    thus ?thesis
      using star.circ_decompose_11 star_decompose_1 by auto
  qed
  hence 6: "(H * ((d \<sqinter> - a) \<squnion> (d \<sqinter> - a)\<^sup>T))\<^sup>\<star> * H * a * top \<le> ?lhs"
    using mult_left_dist_sup by auto
  have 7: "(H * (d \<sqinter> - a))\<^sup>\<star> * H * a * top \<le> (H * ((d \<sqinter> - a) \<squnion> (d \<sqinter> - a)\<^sup>T))\<^sup>\<star> * H * a * top"
    by (simp add: mult_left_isotone semiring.distrib_left star_isotone)
  thus ?thesis
    using 6 7 by (simp add: mult_assoc)
qed

end

subsection \<open>An operation to select components\<close>

text \<open>
We introduce the operation \<open>choose_component\<close>.
\begin{itemize}
\item Axiom \<open>component_in_v\<close> expresses that the result of \<open>choose_component\<close> is contained in the set of vertices, $v$, we are selecting from, ignoring the weights.
\item Axiom \<open>component_is_vector\<close> states that the result of \<open>choose_component\<close> is a vector.
\item Axiom \<open>component_is_regular\<close> states that the result of \<open>choose_component\<close> is regular.
\item Axiom \<open>component_is_connected\<close> states that any two vertices from the result of \<open>choose_component\<close> are connected in $e$.
\item Axiom \<open>component_single\<close> states that the result of \<open>choose_component\<close> is closed under being connected in $e$.
\item Finally, axiom \<open>component_not_bot_when_v_bot_bot\<close> expresses that the operation \<open>choose_component\<close> returns a non-empty component if the input satisfies the given criteria.
\end{itemize}
\<close>

class choose_component =
  fixes choose_component :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

class choose_component_algebra = choose_component + stone_relation_algebra +
  assumes component_in_v: "choose_component e v \<le> --v"
  assumes component_is_vector: "vector (choose_component e v)"
  assumes component_is_regular: "regular (choose_component e v)"
  assumes component_is_connected: "choose_component e v * (choose_component e v)\<^sup>T \<le> e"
  assumes component_single: "choose_component e v = e * choose_component e v"
  assumes component_not_bot_when_v_bot_bot: "
      regular e
    \<and> equivalence e
    \<and> vector v
    \<and> regular v
    \<and> e * v = v
    \<and> v \<noteq> bot \<longrightarrow> choose_component e v \<noteq> bot"

text \<open>Theorem 1\<close>

text \<open>
Every \<open>m_kleene_algebra\<close> is an instance of \<open>choose_component_algebra\<close> when the \<open>choose_component\<close> operation is defined as follows:
\<close>

context m_kleene_algebra
begin

definition "choose_component_input_condition e v \<equiv>
    regular e
  \<and> equivalence e
  \<and> vector v
  \<and> regular v
  \<and> e * v = v"

definition "m_choose_component e v \<equiv>
  if choose_component_input_condition e v then
    e * minarc(v) * top
  else
    bot"

sublocale m_choose_component_algebra: choose_component_algebra where choose_component = m_choose_component
proof
  fix e v
  show "m_choose_component e v \<le> -- v"
  proof (cases "choose_component_input_condition e v")
    case True
    hence "m_choose_component e v = e * minarc(v) * top"
      by (simp add: m_choose_component_def)
    also have "... \<le> e * --v * top"
      by (simp add: comp_isotone minarc_below)
    also have "... = e * v * top"
      using True choose_component_input_condition_def by auto
    also have "... = v * top"
      using True choose_component_input_condition_def by auto
    finally show ?thesis
      using True choose_component_input_condition_def by auto
  next
    case False
    hence "m_choose_component e v = bot"
      using False m_choose_component_def by auto
    thus ?thesis
      by simp
  qed
next
  fix e v
  show "vector (m_choose_component e v)"
  proof (cases "choose_component_input_condition e v")
    case True
    thus ?thesis
      by (simp add: mult_assoc m_choose_component_def)
  next
    case False
    thus ?thesis
      by (simp add: m_choose_component_def)
  qed
next
  fix e v
  show "regular (m_choose_component e v)"
    using choose_component_input_condition_def minarc_regular regular_closed_star regular_mult_closed m_choose_component_def by auto
next
  fix e v
  show "m_choose_component e v * (m_choose_component e v)\<^sup>T \<le> e"
  proof (cases "choose_component_input_condition e v")
    case True
    assume 1: "choose_component_input_condition e v"
    hence "m_choose_component e v * (m_choose_component e v)\<^sup>T = e * minarc(v) * top * (e * minarc(v) * top)\<^sup>T"
      by (simp add: m_choose_component_def)
    also have "... = e * minarc(v) * top * top\<^sup>T * minarc(v)\<^sup>T * e\<^sup>T"
      by (metis comp_associative conv_dist_comp)
    also have "... = e * minarc(v) * top * top * minarc(v)\<^sup>T * e"
      using 1 choose_component_input_condition_def by auto
    also have "... = e * minarc(v) * top * minarc(v)\<^sup>T * e"
      by (simp add: comp_associative)
    also have "... \<le> e"
    proof (cases "v = bot")
      case True
      thus ?thesis
        by (simp add: True minarc_bot)
    next
      case False
      assume 3: "v \<noteq> bot"
      hence "e * minarc(v) * top * minarc(v)\<^sup>T \<le> e * 1"
        using 3 minarc_arc arc_expanded comp_associative mult_right_isotone by fastforce
      hence "e * minarc(v) * top * minarc(v)\<^sup>T * e \<le> e * 1 * e"
        using mult_left_isotone by auto
      also have "... = e"
        using 1 choose_component_input_condition_def preorder_idempotent by auto
      thus ?thesis
        using calculation by auto
    qed
    thus ?thesis
      by (simp add: calculation)
  next
    case False
    thus ?thesis
      by (simp add: m_choose_component_def)
  qed
next
  fix e v
  show "m_choose_component e v = e * m_choose_component e v"
  proof (cases "choose_component_input_condition e v")
    case True
    thus ?thesis
      by (metis choose_component_input_condition_def preorder_idempotent m_choose_component_def mult_assoc)
  next
    case False
    thus ?thesis
      by (simp add: m_choose_component_def)
  qed
next
  fix e v
  show "regular e \<and> equivalence e \<and> vector v \<and> regular v \<and> e * v = v \<and> v \<noteq> bot \<longrightarrow> m_choose_component e v \<noteq> bot"
  proof (cases "choose_component_input_condition e v")
    case True
    hence "m_choose_component e v \<ge> minarc(v) * top"
      by (metis choose_component_input_condition_def mult_1_left mult_left_isotone m_choose_component_def)
    also have "... \<ge> minarc(v)"
      using calculation dual_order.trans top_right_mult_increasing by blast
    thus ?thesis
      using True bot_unique minarc_bot_iff by fastforce
  next
    case False
    thus ?thesis
      using choose_component_input_condition_def by blast
  qed
qed

end

subsection \<open>m-k-Stone-Kleene relation algebras\<close>

text \<open>
$m$-$k$-Stone-Kleene relation algebras are an extension of $m$-Kleene algebras where the \<open>choose_component\<close> operation has been added.
\<close>

class m_kleene_algebra_choose_component =
  m_kleene_algebra
  + choose_component_algebra
begin

text \<open>
A \<open>selected_edge\<close> is a minimum-weight edge whose source is in a component, with respect to $h$, $j$ and $g$, and whose target is not in that component.
\<close>

abbreviation "selected_edge h j g \<equiv> minarc (choose_component (forest_components h) j * - choose_component (forest_components h) j\<^sup>T \<sqinter> g)"

text \<open>
A \<open>path\<close> is any sequence of edges in the forest, $f$, of the graph, $g$, backwards from the target of the \<open>selected_edge\<close> to a root in $f$.
\<close>

abbreviation "path f h j g \<equiv> top * selected_edge h j g * (f \<sqinter> - selected_edge h j g\<^sup>T)\<^sup>T\<^sup>\<star>"

definition "boruvka_outer_invariant f g \<equiv>
    symmetric g
  \<and> forest f
  \<and> f \<le> --g
  \<and> regular f
  \<and> (\<exists>w . minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T)"

definition "boruvka_inner_invariant j f h g d \<equiv>
    boruvka_outer_invariant f g
  \<and> g \<noteq> bot
  \<and> vector j
  \<and> regular j
  \<and> boruvka_outer_invariant h g
  \<and> forest h
  \<and> forest_components h \<le> forest_components f
  \<and> big_forest (forest_components h) d
  \<and> d * top \<le> - j
  \<and> forest_components h * j = j
  \<and> forest_components f = (forest_components h * (d \<squnion> d\<^sup>T))\<^sup>\<star> * forest_components h
  \<and> f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T
  \<and> (\<forall> a b . bf_between_arcs a b (forest_components h) d \<and> a \<le> -(forest_components h) \<sqinter> -- g \<and> b \<le> d
    \<longrightarrow> sum(b \<sqinter> g) \<le> sum(a \<sqinter> g))
  \<and> regular d"

lemma expression_equivalent_without_e_complement:
  assumes "selected_edge h j g \<le> - forest_components f"
  shows "f \<sqinter> - (selected_edge h j g)\<^sup>T \<sqinter> - (path f h j g) \<squnion> (f \<sqinter> - (selected_edge h j g)\<^sup>T \<sqinter> (path f h j g))\<^sup>T \<squnion> (selected_edge h j g)
         = f \<sqinter> - (path f h j g) \<squnion> (f \<sqinter> (path f h j g))\<^sup>T \<squnion> (selected_edge h j g)"
proof -
  let ?p = "path f h j g"
  let ?e = "selected_edge h j g"
  let ?F = "forest_components f"
  have 1: "?e \<le> - ?F"
    by (simp add: assms)
  have "f\<^sup>T \<le> ?F"
    by (metis conv_dist_comp conv_involutive conv_order conv_star_commute forest_components_increasing)
  hence "- ?F \<le> - f\<^sup>T"
    using p_antitone by auto
  hence "?e \<le> - f\<^sup>T"
    using 1 dual_order.trans by blast
  hence "f\<^sup>T \<le> - ?e"
    by (simp add: p_antitone_iff)
  hence "f\<^sup>T\<^sup>T \<le> - ?e\<^sup>T"
    by (metis conv_complement conv_dist_inf inf.orderE inf.orderI)
  hence "f \<le> - ?e\<^sup>T"
    by auto
  hence "f = f \<sqinter> - ?e\<^sup>T"
    using inf.orderE by blast
  hence "f \<sqinter> - ?e\<^sup>T \<sqinter> - ?p \<squnion> (f \<sqinter> - ?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> ?e = f \<sqinter> - ?p \<squnion> (f \<sqinter> ?p)\<^sup>T \<squnion> ?e"
    by auto
  thus ?thesis by auto
qed

text \<open>Theorem 2\<close>

text \<open>
The source of the \<open>selected_edge\<close> is contained in $j$, the vector describing those vertices still to be processed in the inner loop of Bor\r{u}vka's algorithm.
\<close>

lemma et_below_j:
  assumes "vector j"
    and "regular j"
    and "j \<noteq> bot"
  shows "selected_edge h j g * top \<le> j"
proof -
  let ?e = "selected_edge h j g"
  let ?c = "choose_component (forest_components h) j"
  have "?e * top \<le> --(?c * -?c\<^sup>T \<sqinter> g) * top"
    using comp_isotone minarc_below by blast
  also have "... = (--(?c * -?c\<^sup>T) \<sqinter> --g) * top"
    by simp
  also have "... = (?c * -?c\<^sup>T \<sqinter> --g) * top"
    using component_is_regular regular_mult_closed by auto
  also have "... = (?c \<sqinter> -?c\<^sup>T \<sqinter> --g) * top"
    by (metis component_is_vector conv_complement vector_complement_closed vector_covector)
  also have "... \<le> ?c * top"
    using inf.cobounded1 mult_left_isotone order_trans by blast
  also have "... \<le> j * top"
    by (metis assms(2) comp_inf.star.circ_sup_2 comp_isotone component_in_v)
  also have "... = j"
    by (simp add: assms(1))
  finally show ?thesis
    by simp
qed

subsubsection \<open>Components of forests and big forests\<close>

text \<open>
We prove a number of properties about \<open>big_forest\<close> and \<open>forest_components\<close>.
\<close>

lemma fc_j_eq_j_inv:
  assumes "forest h"
    and "forest_components h * j = j"
  shows "forest_components h * (j \<sqinter> - choose_component (forest_components h) j) = j \<sqinter> - choose_component (forest_components h) j"
proof -
  let ?c = "choose_component (forest_components h) j"
  let ?H = "forest_components h"
  have 1:"equivalence ?H"
    by (simp add: assms(1) forest_components_equivalence)
  have "?H * (j \<sqinter> - ?c) = ?H * j \<sqinter> ?H * - ?c"
    using 1 by (metis assms(2) equivalence_comp_dist_inf inf.sup_monoid.add_commute)
  hence 2: "?H * (j \<sqinter> - ?c) = j \<sqinter> ?H * - ?c"
    by (simp add: assms(2))
  have 3: "j \<sqinter> - ?c \<le> ?H * - ?c"
    using 1 by (metis assms(2) dedekind_1 dual_order.trans equivalence_comp_dist_inf inf.cobounded2)
  have "?H * ?c \<le> ?c"
    using component_single by auto
  hence "?H\<^sup>T * ?c \<le> ?c"
    using 1 by simp
  hence "?H * - ?c \<le> - ?c"
    using component_is_regular schroeder_3_p by force
  hence "j \<sqinter> ?H * - ?c \<le> j \<sqinter> - ?c"
    using inf.sup_right_isotone by auto
  thus ?thesis
    using 2 3 antisym by simp
qed

text \<open>Theorem 5\<close>

text \<open>
There is a path in the \<open>big_forest\<close> between edges $a$ and $b$ if and only if there is either a path in the \<open>big_forest\<close> from $a$ to $b$ or one from $a$ to $c$ and one from $c$ to $b$.
\<close>

lemma big_forest_path_split_disj:
  assumes "equivalence H"
    and "arc c"
    and "regular a \<and> regular b \<and> regular c \<and> regular d \<and> regular H"
  shows "bf_between_arcs a b H (d \<squnion> c) \<longleftrightarrow> bf_between_arcs a b H d \<or> (bf_between_arcs a c H d \<and> bf_between_arcs c b H d)"
proof -
  have 1: "bf_between_arcs a b H (d \<squnion> c) \<longrightarrow> bf_between_arcs a b H d \<or> (bf_between_arcs a c H d \<and> bf_between_arcs c b H d)"
  proof (rule impI)
    assume 11: "bf_between_arcs a b H (d \<squnion> c)"
    hence "a\<^sup>T * top \<le> (H * (d \<squnion> c))\<^sup>\<star> * H * b * top"
      by (simp add: bf_between_arcs_def)
    also have "... = ((H * d)\<^sup>\<star> \<squnion> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star>) * H * b * top"
      using assms(1, 2) path_through_components by simp
    also have "... = (H * d)\<^sup>\<star> * H * b * top \<squnion> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star> * H * b * top"
      by (simp add: mult_right_dist_sup)
    finally have 12:"a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top \<squnion> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star> * H * b * top"
      by simp
    have 13: "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top \<or> a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star> * H * b * top"
    proof (rule point_in_vector_sup)
      show "point (a\<^sup>T * top)"
        using 11 bf_between_arcs_def mult_assoc by auto
    next
      show "vector ((H * d)\<^sup>\<star> * H * b * top)"
        using vector_mult_closed by simp
    next
      show "regular ((H * d)\<^sup>\<star> * H * b * top)"
        using assms(3) pp_dist_comp pp_dist_star by auto
    next
      show "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top \<squnion> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star> * H * b * top"
        using 12 by simp
    qed
    thus "bf_between_arcs a b H d \<or> (bf_between_arcs a c H d \<and> bf_between_arcs c b H d)"
    proof (cases "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top")
      case True
      assume "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top"
      hence "bf_between_arcs a b H d"
        using 11 bf_between_arcs_def by auto
      thus ?thesis
        by simp
    next
      case False
      have 14: "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star> * H * b * top"
        using 13 by (simp add: False)
      hence 15: "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * c * top"
        by (metis mult_right_isotone order_lesseq_imp top_greatest mult_assoc)
      have "c\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top"
      proof (rule ccontr)
        assume "\<not> c\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top"
        hence "c\<^sup>T * top \<le> -((H * d)\<^sup>\<star> * H * b * top)"
          by (meson assms(2, 3) point_in_vector_or_complement regular_closed_star regular_closed_top regular_mult_closed vector_mult_closed vector_top_closed)
        hence "c * (H * d)\<^sup>\<star> * H * b * top \<le> bot"
          using schroeder_3_p mult_assoc by auto
        thus "False"
          using 13 False sup.absorb_iff1 mult_assoc by auto
      qed
      hence "bf_between_arcs a c H d \<and> bf_between_arcs c b H d"
        using 11 15 assms(2) bf_between_arcs_def by auto
      thus ?thesis
        by simp
    qed
  qed
  have 2: "bf_between_arcs a b H d \<or> (bf_between_arcs a c H d \<and> bf_between_arcs c b H d) \<longrightarrow> bf_between_arcs a b H (d \<squnion> c)"
  proof -
    have 21: "bf_between_arcs a b H d \<longrightarrow> bf_between_arcs a b H (d \<squnion> c)"
    proof (rule impI)
      assume 22:"bf_between_arcs a b H d"
      hence "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * b * top"
        using bf_between_arcs_def by blast
      hence "a\<^sup>T * top \<le> (H * (d \<squnion> c))\<^sup>\<star> * H * b * top"
        by (simp add: mult_left_isotone mult_right_dist_sup mult_right_isotone order.trans star_isotone star_slide)
      thus "bf_between_arcs a b H (d \<squnion> c)"
        using 22 bf_between_arcs_def by blast
    qed
    have "bf_between_arcs a c H d \<and> bf_between_arcs c b H d \<longrightarrow> bf_between_arcs a b H (d \<squnion> c)"
    proof (rule impI)
      assume 23: "bf_between_arcs a c H d \<and> bf_between_arcs c b H d"
      hence "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * c * top"
        using bf_between_arcs_def by blast
      also have "... \<le> (H * d)\<^sup>\<star> * H * c * c\<^sup>T * c * top"
        by (metis ex231c comp_inf.star.circ_sup_2 mult_isotone mult_right_isotone mult_assoc)
      also have "... \<le> (H * d)\<^sup>\<star> * H * c * c\<^sup>T * top"
        by (simp add: mult_right_isotone mult_assoc)
      also have "... \<le> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star> * H * b * top"
        using 23 mult_right_isotone mult_assoc by (simp add: bf_between_arcs_def)
      also have "... \<le> (H * d)\<^sup>\<star> * H * b * top \<squnion> (H * d)\<^sup>\<star> * H * c * (H * d)\<^sup>\<star> * H * b * top"
        by (simp add: bf_between_arcs_def)
      finally have "a\<^sup>T * top \<le> (H * (d \<squnion> c))\<^sup>\<star> * H * b * top"
        using assms(1, 2) path_through_components mult_right_dist_sup by simp
      thus "bf_between_arcs a b H (d \<squnion> c)"
        using 23 bf_between_arcs_def by blast
    qed
    thus ?thesis
      using 21 by auto
  qed
  thus ?thesis
    using 1 2 by blast
qed

lemma dT_He_eq_bot:
  assumes "vector j"
    and "regular j"
    and "d * top \<le> - j"
    and "forest_components h * j = j"
    and "j \<noteq> bot"
  shows "d\<^sup>T * forest_components h * selected_edge h j g \<le> bot"
proof -
  let ?e = "selected_edge h j g"
  let ?H = "forest_components h"
  have 1: "?e * top \<le> j"
    using assms(1, 2, 5) et_below_j by auto
  have "d\<^sup>T * ?H * ?e \<le> (d * top)\<^sup>T * ?H * (?e * top)"
    by (simp add: comp_isotone conv_isotone top_right_mult_increasing)
  also have "... \<le> (d * top)\<^sup>T * ?H * j"
    using 1 mult_right_isotone by auto
  also have "... \<le> (- j)\<^sup>T * ?H * j"
    by (simp add: assms(3) conv_isotone mult_left_isotone)
  also have "... = (- j)\<^sup>T * j"
    using assms(4) comp_associative by auto
  also have "... = bot"
    by (simp add: assms(1) conv_complement covector_vector_comp)
  finally show ?thesis
    using coreflexive_bot_closed le_bot by blast
qed

lemma big_forest_d_U_e:
  assumes "forest f"
    and "vector j"
    and "regular j"
    and "forest h"
    and "forest_components h \<le> forest_components f"
    and "big_forest (forest_components h) d"
    and "d * top \<le> - j"
    and "forest_components h * j = j"
    and "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
    and "selected_edge h j g \<le> - forest_components f"
    and "selected_edge h j g \<noteq> bot"
    and "j \<noteq> bot"
  shows "big_forest (forest_components h) (d \<squnion> selected_edge h j g)"
proof (unfold big_forest_def, intro conjI)
  let ?H = "forest_components h"
  let ?F = "forest_components f"
  let ?e = "selected_edge h j g"
  let ?d' = "d \<squnion> ?e"
  show 01: "reflexive ?H"
    by (simp add: assms(4) forest_components_equivalence)
  show 02: "transitive ?H"
    by (simp add: assms(4) forest_components_equivalence)
  show 03: "symmetric ?H"
    by (simp add: assms(4) forest_components_equivalence)
  have 04: "equivalence ?H"
    by (simp add: 01 02 03)
  show 1: "?d' \<le> - ?H"
  proof -
    have "?H \<le> ?F"
      by (simp add: assms(5))
    hence 11: "?e \<le> - ?H"
      using assms(10) order_lesseq_imp p_antitone by blast
    have "d \<le> - ?H"
      using assms(6) big_forest_def by auto
    thus ?thesis
      by (simp add: 11)
  qed
  show "univalent (?H * ?d')"
  proof -
    have "(?H * ?d')\<^sup>T * (?H * ?d') = ?d'\<^sup>T * ?H\<^sup>T * ?H * ?d'"
      using conv_dist_comp mult_assoc by auto
    also have "... = ?d'\<^sup>T * ?H * ?H * ?d'"
      by (simp add: conv_dist_comp conv_star_commute)
    also have "... = ?d'\<^sup>T * ?H * ?d'"
      using 01 02 by (metis preorder_idempotent mult_assoc)
    finally have 21: "univalent (?H * ?d') \<longleftrightarrow> ?e\<^sup>T * ?H * d \<squnion> d\<^sup>T * ?H * ?e \<squnion> ?e\<^sup>T * ?H * ?e \<squnion> d\<^sup>T * ?H * d \<le> 1"
      using conv_dist_sup semiring.distrib_left semiring.distrib_right by auto
    have 22: "?e\<^sup>T * ?H * ?e \<le> 1"
    proof -
      have 221: "?e\<^sup>T * ?H * ?e \<le> ?e\<^sup>T * top * ?e"
        by (simp add: mult_left_isotone mult_right_isotone)
      have "arc ?e"
        using assms(11) minarc_arc minarc_bot_iff by blast
      hence "?e\<^sup>T * top * ?e \<le> 1"
        using arc_expanded by blast
      thus ?thesis
        using 221 dual_order.trans by blast
    qed
    have 24: "d\<^sup>T * ?H * ?e \<le> 1"
      by (metis assms(2, 3, 7, 8, 12) dT_He_eq_bot coreflexive_bot_closed le_bot)
    hence "(d\<^sup>T * ?H * ?e)\<^sup>T \<le> 1\<^sup>T"
      using conv_isotone by blast
    hence "?e\<^sup>T * ?H\<^sup>T * d\<^sup>T\<^sup>T \<le> 1"
      by (simp add: conv_dist_comp mult_assoc)
    hence 25: "?e\<^sup>T * ?H * d \<le> 1"
      using assms(4) fch_equivalence by auto
    have 8: "d\<^sup>T * ?H * d \<le> 1"
      using 04 assms(6) dTransHd_le_1 big_forest_def by blast
    thus ?thesis
      using 21 22 24 25 by simp
  qed
  show "coreflexive (?H \<sqinter> ?d' * ?d'\<^sup>T)"
  proof -
    have "coreflexive (?H \<sqinter> ?d' * ?d'\<^sup>T) \<longleftrightarrow> ?H \<sqinter> (d \<squnion> ?e) * (d\<^sup>T \<squnion> ?e\<^sup>T) \<le> 1"
      by (simp add: conv_dist_sup)
    also have "... \<longleftrightarrow> ?H \<sqinter> (d * d\<^sup>T \<squnion> d * ?e\<^sup>T \<squnion> ?e * d\<^sup>T \<squnion> ?e * ?e\<^sup>T) \<le> 1"
      by (metis mult_left_dist_sup mult_right_dist_sup sup.left_commute sup_commute)
    finally have 1: "coreflexive (?H \<sqinter> ?d' * ?d'\<^sup>T) \<longleftrightarrow> ?H \<sqinter> d * d\<^sup>T \<squnion> ?H \<sqinter> d * ?e\<^sup>T \<squnion> ?H \<sqinter> ?e * d\<^sup>T \<squnion> ?H \<sqinter> ?e * ?e\<^sup>T \<le> 1"
      by (simp add: inf_sup_distrib1)
    have 31: "?H \<sqinter> d * d\<^sup>T \<le> 1"
      using assms(6) big_forest_def by blast
    have 32: "?H \<sqinter> ?e * d\<^sup>T \<le> 1"
    proof -
      have "?e * d\<^sup>T \<le> ?e * top * (d * top)\<^sup>T"
        by (simp add: conv_isotone mult_isotone top_right_mult_increasing)
      also have "... \<le> ?e * top * - j\<^sup>T"
        by (metis assms(7) conv_complement conv_isotone mult_right_isotone)
      also have "... \<le> j * - j\<^sup>T"
        using assms(2, 3, 12) et_below_j mult_left_isotone by auto
      also have "... \<le> - ?H"
        using 03 by (metis assms(2, 3, 8) conv_complement conv_dist_comp equivalence_top_closed mult_left_isotone schroeder_3_p vector_top_closed)
      finally have "?e * d\<^sup>T \<le> - ?H"
        by simp
      thus ?thesis
        by (metis inf.coboundedI1 p_antitone_iff p_shunting_swap regular_one_closed)
    qed
    have 33: "?H \<sqinter> d * ?e\<^sup>T \<le> 1"
    proof -
      have 331: "injective h"
        by (simp add: assms(4))
      have "(?H \<sqinter> ?e * d\<^sup>T)\<^sup>T \<le> 1"
        using 32 coreflexive_conv_closed by auto
      hence "?H \<sqinter> (?e * d\<^sup>T)\<^sup>T \<le> 1"
        using 331 conv_dist_inf forest_components_equivalence by auto
      thus ?thesis
        using conv_dist_comp by auto
    qed
    have 34: "?H \<sqinter> ?e * ?e\<^sup>T \<le> 1"
    proof -
      have 341:"arc ?e \<and> arc (?e\<^sup>T)"
        using assms(11) minarc_arc minarc_bot_iff by auto
      have "?H \<sqinter> ?e * ?e\<^sup>T \<le> ?e * ?e\<^sup>T"
        by auto
      thus ?thesis
        using 341 arc_injective le_infI2 by blast
    qed
    thus ?thesis
      using 1 31 32 33 34 by simp
  qed
  show 4:"(?H * (d \<squnion> ?e))\<^sup>+ \<le> - ?H"
  proof -
    have "?e \<le> - ?F"
      by (simp add: assms(10))
    hence "?F \<le> - ?e"
      by (simp add: p_antitone_iff)
    hence "?F\<^sup>T * ?F \<le> - ?e"
      using assms(1) fch_equivalence by fastforce
    hence "?F\<^sup>T * ?F * ?F\<^sup>T \<le> - ?e"
      by (metis assms(1) fch_equivalence forest_components_star star.circ_decompose_9)
    hence 41: "?F * ?e * ?F \<le> - ?F"
      using triple_schroeder_p by blast
    hence 42:"(?F * ?F)\<^sup>\<star> * ?F * ?e * (?F * ?F)\<^sup>\<star> \<le> - ?F"
    proof -
      have 43: "?F * ?F = ?F"
        using assms(1) forest_components_equivalence preorder_idempotent by auto
      hence "?F * ?e * ?F = ?F * ?F * ?e * ?F"
        by simp
      also have "... = (?F)\<^sup>\<star> * ?F * ?e * (?F)\<^sup>\<star>"
        by (simp add: assms(1) forest_components_star)
      also have "... = (?F * ?F)\<^sup>\<star> * ?F * ?e * (?F * ?F)\<^sup>\<star>"
        using 43 by simp
      finally show ?thesis
        using 41 by simp
    qed
    hence 44: "(?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> \<le> - ?H"
    proof -
      have 45: "?H \<le> ?F"
        by (simp add: assms(5))
      hence 46:"?H * ?e \<le> ?F * ?e"
        by (simp add: mult_left_isotone)
      have "d \<le> f \<squnion> f\<^sup>T"
        using assms(9) sup.left_commute sup_commute by auto
      also have "... \<le> ?F"
        by (metis forest_components_increasing le_supI2 star.circ_back_loop_fixpoint star.circ_increasing sup.bounded_iff)
      finally have "d \<le> ?F"
        by simp
      hence "?H * d \<le> ?F * ?F"
        using 45 mult_isotone by auto
      hence 47: "(?H * d)\<^sup>\<star> \<le> (?F * ?F)\<^sup>\<star>"
        by (simp add: star_isotone)
      hence "(?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> \<le> (?H * d)\<^sup>\<star> * ?F * ?e * (?H * d)\<^sup>\<star>"
        using 46 by (metis mult_left_isotone mult_right_isotone mult_assoc)
      also have "... \<le> (?F * ?F)\<^sup>\<star> * ?F * ?e * (?F * ?F)\<^sup>\<star>"
        using 47 mult_left_isotone mult_right_isotone by (simp add: comp_isotone)
      also have "... \<le> - ?F"
        using 42 by simp
      also have "... \<le> - ?H"
        using 45 by (simp add: p_antitone)
      finally show ?thesis
        by simp
    qed
    have "(?H * (d \<squnion> ?e))\<^sup>+ = (?H * (d \<squnion> ?e))\<^sup>\<star> * (?H * (d \<squnion> ?e))"
      using star.circ_plus_same by auto
    also have "... = ((?H * d)\<^sup>\<star> \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star>) * (?H * (d \<squnion> ?e))"
      using assms(4, 11) forest_components_equivalence minarc_arc minarc_bot_iff path_through_components by auto
    also have "... = (?H * d)\<^sup>\<star> * (?H * (d \<squnion> ?e)) \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * (?H * (d \<squnion> ?e))"
      using mult_right_dist_sup by auto
    also have "... = (?H * d)\<^sup>\<star> * (?H * d \<squnion> ?H * ?e) \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * (?H * d \<squnion> ?H * ?e)"
      by (simp add: mult_left_dist_sup)
    also have "... = (?H * d)\<^sup>\<star> * ?H * d \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * (?H * d \<squnion> ?H * ?e)"
      using mult_left_dist_sup mult_assoc by auto
    also have "... = (?H * d)\<^sup>+ \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * (?H * d \<squnion> ?H * ?e)"
      by (simp add: star.circ_plus_same mult_assoc)
    also have "... = (?H * d)\<^sup>+ \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * ?H * d \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * ?H * ?e"
      by (simp add: mult.semigroup_axioms semiring.distrib_left sup.semigroup_axioms semigroup.assoc)
    also have "... \<le> (?H * d)\<^sup>+ \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * ?H * d \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e"
    proof -
      have "?e * (?H * d)\<^sup>\<star> * ?H * ?e \<le> ?e * top * ?e"
        by (metis comp_associative comp_inf.coreflexive_idempotent comp_inf.coreflexive_transitive comp_isotone top.extremum)
      also have "... \<le> ?e"
        using assms(11) arc_top_arc minarc_arc minarc_bot_iff by auto
      finally have "?e * (?H * d)\<^sup>\<star> * ?H * ?e \<le> ?e"
        by simp
      hence "(?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
        by (simp add: comp_associative comp_isotone)
      thus ?thesis
        using sup_right_isotone by blast
    qed
    also have "... = (?H * d)\<^sup>+ \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star> * ?H * d"
      by (smt eq_iff sup.left_commute sup.orderE sup_commute)
    also have "... = (?H * d)\<^sup>+ \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>+"
      using star.circ_plus_same mult_assoc by auto
    also have "... = (?H * d)\<^sup>+ \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (1 \<squnion> (?H * d)\<^sup>+)"
      by (simp add: mult_left_dist_sup sup_assoc)
    also have "... = (?H * d)\<^sup>+ \<squnion> (?H * d)\<^sup>\<star> * ?H * ?e * (?H * d)\<^sup>\<star>"
      by (simp add: star_left_unfold_equal)
    also have "... \<le> - ?H"
      using 44 assms(6) big_forest_def by auto
    finally show ?thesis
      by simp
  qed
qed

subsubsection \<open>Identifying arcs\<close>

text \<open>
The expression $d \sqcap \top e^\top H \sqcap (H d^\top)^* H a^\top \top$ identifies the edge incoming to the component that the \<open>selected_edge\<close>, $e$, is outgoing from and which is on the path from edge $a$ to $e$.
Here, we prove this expression is an \<open>arc\<close>.
\<close>

lemma shows_arc_x:
  assumes "big_forest H d"
    and "bf_between_arcs a e H d"
    and "H * d * (H * d)\<^sup>\<star> \<le> - H"
    and "\<not> a\<^sup>T * top \<le> H * e * top"
    and "regular a"
    and "regular e"
    and "regular H"
    and "regular d"
  shows "arc (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)"
proof -
  let ?x = "d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top"
  have 1:"regular ?x"
    using assms(5, 6, 7, 8) regular_closed_star regular_conv_closed regular_mult_closed by auto
  have 2: "a\<^sup>T * top * a \<le> 1"
    using arc_expanded assms(2) bf_between_arcs_def by auto
  have 3: "e * top * e\<^sup>T \<le> 1"
    using assms(2) bf_between_arcs_def arc_expanded by blast
  have 4: "top * ?x * top = top"
  proof -
    have "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * e * top"
      using assms(2) bf_between_arcs_def by blast
    also have "... = H * e * top \<squnion> (H * d)\<^sup>\<star> * H * d * H * e * top"
      by (metis star.circ_loop_fixpoint star.circ_plus_same sup_commute mult_assoc)
    finally have "a\<^sup>T * top \<le> H * e * top \<squnion> (H * d)\<^sup>\<star> * H * d * H * e * top"
      by simp
    hence "a\<^sup>T * top \<le> H * e * top \<or> a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * d * H * e * top"
      using assms(2, 6, 7) point_in_vector_sup bf_between_arcs_def regular_mult_closed vector_mult_closed by auto
    hence "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * d * H * e * top"
      using assms(4) by blast
    also have "... = (H * d)\<^sup>\<star> * H * d * (H * e * top \<sqinter> H * e * top)"
      by (simp add: mult_assoc)
    also have "... = (H * d)\<^sup>\<star> * H * (d \<sqinter> (H * e * top)\<^sup>T) * H * e * top"
      by (metis comp_associative covector_inf_comp_3 star.circ_left_top star.circ_top)
    also have "... = (H * d)\<^sup>\<star> * H * (d \<sqinter> top\<^sup>T * e\<^sup>T * H\<^sup>T) * H * e * top"
      using conv_dist_comp mult_assoc by auto
    also have "... = (H * d)\<^sup>\<star> * H * (d \<sqinter> top * e\<^sup>T * H) * H * e * top"
      using assms(1) by (simp add: big_forest_def)
    finally have 2: "a\<^sup>T * top \<le> (H * d)\<^sup>\<star> * H * (d \<sqinter> top * e\<^sup>T * H) * H * e * top"
      by simp
    hence "e * top \<le> ((H * d)\<^sup>\<star> * H * (d \<sqinter> top * e\<^sup>T * H) * H)\<^sup>T * a\<^sup>T * top"
    proof -
      have "bijective (e * top) \<and> bijective (a\<^sup>T * top)"
        using assms(2) bf_between_arcs_def by auto
      thus ?thesis
        using 2 by (metis bijective_reverse mult_assoc)
    qed
    also have "... = H\<^sup>T * (d \<sqinter> top * e\<^sup>T * H)\<^sup>T * H\<^sup>T * (H * d)\<^sup>\<star>\<^sup>T * a\<^sup>T * top"
      by (simp add: conv_dist_comp mult_assoc)
    also have "... = H * (d \<sqinter> top * e\<^sup>T * H)\<^sup>T * H * (H * d)\<^sup>\<star>\<^sup>T * a\<^sup>T * top"
      using assms(1) big_forest_def by auto
    also have "... = H * (d \<sqinter> top * e\<^sup>T * H)\<^sup>T * H * (d\<^sup>T * H)\<^sup>\<star> * a\<^sup>T * top"
      using assms(1) big_forest_def conv_dist_comp conv_star_commute by auto
    also have "... = H * (d\<^sup>T \<sqinter> H * e * top) * H * (d\<^sup>T * H)\<^sup>\<star> * a\<^sup>T * top"
      using assms(1) conv_dist_comp big_forest_def comp_associative conv_dist_inf by auto
    also have "... = H * (d\<^sup>T \<sqinter> H * e * top) * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top"
      by (simp add: comp_associative star_slide)
    also have "... = H * (d\<^sup>T \<sqinter> H * e * top) * ((H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)"
      using mult_assoc by auto
    also have "... = H * (d\<^sup>T \<sqinter> H * e * top \<sqinter> ((H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)\<^sup>T) * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top"
      by (smt comp_inf_vector covector_comp_inf vector_conv_covector vector_top_closed mult_assoc)
    also have "... = H * (d\<^sup>T \<sqinter> (top * e\<^sup>T * H)\<^sup>T \<sqinter> ((H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)\<^sup>T) * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top"
      using assms(1) big_forest_def conv_dist_comp mult_assoc by auto
    also have "... = H * (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top"
      by (simp add: conv_dist_inf)
    finally have 3: "e * top \<le> H * ?x\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top"
      by auto
    have "?x \<noteq> bot"
    proof (rule ccontr)
      assume "\<not> ?x \<noteq> bot"
      hence "e * top = bot"
        using 3 le_bot by auto
      thus "False"
        using assms(2, 4) bf_between_arcs_def mult_assoc semiring.mult_zero_right by auto
    qed
    thus ?thesis
      using 1 using tarski by blast
  qed
  have 5: "?x * top * ?x\<^sup>T \<le> 1"
  proof -
    have 51: "H * (d * H)\<^sup>\<star> \<sqinter> d * H * d\<^sup>T \<le> 1"
    proof -
      have 511: "d * (H * d)\<^sup>\<star> \<le> - H"
        using assms(1, 3) big_forest_def preorder_idempotent schroeder_4_p triple_schroeder_p by fastforce
      hence "(d * H)\<^sup>\<star> * d \<le> - H"
        using star_slide by auto
      hence "H * (d\<^sup>T * H)\<^sup>\<star> \<le> - d"
        by (smt assms(1) big_forest_def conv_dist_comp conv_star_commute schroeder_4_p star_slide)
      hence "H * (d * H)\<^sup>\<star> \<le> - d\<^sup>T"
        using 511 by (metis assms(1) big_forest_def schroeder_5_p star_slide)
      hence "H * (d * H)\<^sup>\<star> \<le> - (H * d\<^sup>T)"
        by (metis assms(3) p_antitone_iff schroeder_4_p star_slide mult_assoc)
      hence "H * (d * H)\<^sup>\<star> \<sqinter> H * d\<^sup>T \<le> bot"
        by (simp add: bot_unique pseudo_complement)
      hence "H * d * (H * (d * H)\<^sup>\<star> \<sqinter> H * d\<^sup>T) \<le> 1"
        by (simp add: bot_unique)
      hence 512: "H * d * H * (d * H)\<^sup>\<star> \<sqinter> H * d * H * d\<^sup>T \<le> 1"
        using univalent_comp_left_dist_inf assms(1) big_forest_def mult_assoc by fastforce
      hence 513: "H * d * H * (d * H)\<^sup>\<star> \<sqinter> d * H * d\<^sup>T \<le> 1"
      proof -
        have "d * H * d\<^sup>T \<le> H * d * H * d\<^sup>T"
          by (metis assms(1) big_forest_def conv_dist_comp conv_involutive mult_1_right mult_left_isotone)
        thus ?thesis
          using 512 by (smt dual_order.trans p_antitone p_shunting_swap regular_one_closed)
      qed
      have "d\<^sup>T * H * d \<le> 1 \<squnion> - H"
        using assms(1) big_forest_def dTransHd_le_1 le_supI1 by blast
      hence "(- 1 \<sqinter> H) * d\<^sup>T * H \<le> - d\<^sup>T"
        by (metis assms(1) big_forest_def dTransHd_le_1 inf.sup_monoid.add_commute le_infI2 p_antitone_iff regular_one_closed schroeder_4_p mult_assoc)
      hence "d * (- 1 \<sqinter> H) * d\<^sup>T \<le> - H"
        by (metis assms(1) big_forest_def conv_dist_comp schroeder_3_p triple_schroeder_p)
      hence "H \<sqinter> d * (- 1 \<sqinter> H) * d\<^sup>T \<le> 1"
        by (metis inf.coboundedI1 p_antitone_iff p_shunting_swap regular_one_closed)
      hence "H \<sqinter> d * d\<^sup>T \<squnion> H \<sqinter> d * (- 1 \<sqinter> H) * d\<^sup>T \<le> 1"
        using assms(1) big_forest_def le_supI by blast
      hence "H \<sqinter> (d * 1 * d\<^sup>T \<squnion> d * (- 1 \<sqinter> H) * d\<^sup>T) \<le> 1"
        using comp_inf.semiring.distrib_left by auto
      hence "H \<sqinter> (d * (1 \<squnion> (- 1 \<sqinter> H)) * d\<^sup>T) \<le> 1"
        by (simp add: mult_left_dist_sup mult_right_dist_sup)
      hence 514: "H \<sqinter> d * H * d\<^sup>T \<le> 1"
        by (metis assms(1) big_forest_def comp_inf.semiring.distrib_left inf.le_iff_sup inf.sup_monoid.add_commute inf_top_right regular_one_closed stone)
      thus ?thesis
      proof -
        have "H \<sqinter> d * H * d\<^sup>T \<squnion> H * d * H * (d * H)\<^sup>\<star> \<sqinter> d * H * d\<^sup>T \<le> 1"
          using 513 514 by simp
        hence "d * H * d\<^sup>T \<sqinter> (H \<squnion> H * d * H * (d * H)\<^sup>\<star>) \<le> 1"
          by (simp add: comp_inf.semiring.distrib_left inf.sup_monoid.add_commute)
        hence "d * H * d\<^sup>T \<sqinter> H * (1 \<squnion> d * H * (d * H)\<^sup>\<star>) \<le> 1"
          by (simp add: mult_left_dist_sup mult_assoc)
        thus ?thesis
          by (simp add: inf.sup_monoid.add_commute star_left_unfold_equal)
      qed
    qed
    have "?x * top * ?x\<^sup>T = (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top) * top * (d\<^sup>T \<sqinter> H\<^sup>T * e\<^sup>T\<^sup>T * top\<^sup>T \<sqinter> top\<^sup>T * a\<^sup>T\<^sup>T * H\<^sup>T * (d\<^sup>T\<^sup>T * H\<^sup>T)\<^sup>\<star>)"
      by (simp add: conv_dist_comp conv_dist_inf conv_star_commute mult_assoc)
    also have "... = (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top) * top * (d\<^sup>T \<sqinter> H * e * top \<sqinter> top * a * H * (d * H)\<^sup>\<star>)"
      using assms(1) big_forest_def by auto
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top \<sqinter> (d \<sqinter> top * e\<^sup>T * H) * top * (d\<^sup>T \<sqinter> H * e * top \<sqinter> top * a * H * (d * H)\<^sup>\<star>)"
      by (metis inf_vector_comp vector_export_comp)
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top \<sqinter> (d \<sqinter> top * e\<^sup>T * H) * top * top * (d\<^sup>T \<sqinter> H * e * top \<sqinter> top * a * H * (d * H)\<^sup>\<star>)"
      by (simp add: vector_mult_closed)
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top \<sqinter> d * ((top * e\<^sup>T * H)\<^sup>T \<sqinter> top) * top * (d\<^sup>T \<sqinter> H * e * top \<sqinter> top * a * H * (d * H)\<^sup>\<star>)"
      by (simp add: covector_comp_inf_1 covector_mult_closed)
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top \<sqinter> d * ((top * e\<^sup>T * H)\<^sup>T \<sqinter> (H * e * top)\<^sup>T) * d\<^sup>T \<sqinter> top * a * H * (d * H)\<^sup>\<star>"
      by (smt comp_associative comp_inf.star_star_absorb comp_inf_vector conv_star_commute covector_comp_inf covector_conv_vector fc_top star.circ_top total_conv_surjective vector_conv_covector vector_inf_comp)
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top \<sqinter> top * a * H * (d * H)\<^sup>\<star> \<sqinter> d * ((top * e\<^sup>T * H)\<^sup>T \<sqinter> (H * e * top)\<^sup>T) * d\<^sup>T"
      using inf.sup_monoid.add_assoc inf.sup_monoid.add_commute by auto
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * top * a * H * (d * H)\<^sup>\<star> \<sqinter> d * ((top * e\<^sup>T * H)\<^sup>T \<sqinter> (H * e * top)\<^sup>T) * d\<^sup>T"
      by (smt comp_inf.star.circ_decompose_9 comp_inf.star_star_absorb comp_inf_covector fc_top star.circ_decompose_11 star.circ_top vector_export_comp)
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * a * H * (d * H)\<^sup>\<star> \<sqinter> d * (H * e * top \<sqinter> top * e\<^sup>T * H) * d\<^sup>T"
      using assms(1) big_forest_def conv_dist_comp mult_assoc by auto
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * a * H * (d * H)\<^sup>\<star> \<sqinter> d * H * e * top * e\<^sup>T * H * d\<^sup>T"
      by (metis comp_inf_covector inf_top.left_neutral mult_assoc)
    also have "... \<le> (H * d\<^sup>T)\<^sup>\<star> * (H * d)\<^sup>\<star> * H \<sqinter> d * H * e * top * e\<^sup>T * H * d\<^sup>T"
    proof -
      have "(H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * a * H * (d * H)\<^sup>\<star> \<le> (H * d\<^sup>T)\<^sup>\<star> * H * 1 * H * (d * H)\<^sup>\<star>"
        using 2 by (metis comp_associative comp_isotone mult_left_isotone mult_semi_associative star.circ_transitive_equal)
      also have "... = (H * d\<^sup>T)\<^sup>\<star> * H * (d * H)\<^sup>\<star>"
        using assms(1) big_forest_def mult.semigroup_axioms preorder_idempotent semigroup.assoc by fastforce
      also have "... = (H * d\<^sup>T)\<^sup>\<star> * (H * d)\<^sup>\<star> * H"
        by (metis star_slide mult_assoc)
      finally show ?thesis
        using inf.sup_left_isotone by auto
    qed
    also have "... \<le> (H * d\<^sup>T)\<^sup>\<star> * (H * d)\<^sup>\<star> * H \<sqinter> d * H * d\<^sup>T"
    proof -
      have "d * H * e * top * e\<^sup>T * H * d\<^sup>T \<le> d * H * 1 * H * d\<^sup>T"
        using 3 by (metis comp_isotone idempotent_one_closed mult_left_isotone mult_sub_right_one mult_assoc)
      also have "... \<le> d * H * d\<^sup>T"
        by (metis assms(1) big_forest_def mult_left_isotone mult_one_associative mult_semi_associative preorder_idempotent)
      finally show ?thesis
        using inf.sup_right_isotone by auto
    qed
    also have "... = H * (d\<^sup>T * H)\<^sup>\<star> * (H * d)\<^sup>\<star> * H \<sqinter> d * H * d\<^sup>T"
      by (metis assms(1) big_forest_def comp_associative preorder_idempotent star_slide)
    also have "... = H * ((d\<^sup>T * H)\<^sup>\<star> \<squnion> (H * d)\<^sup>\<star>) * H \<sqinter> d * H * d\<^sup>T"
      by (simp add: assms(1) expand_big_forest mult.semigroup_axioms semigroup.assoc)
    also have "... = (H * (d\<^sup>T * H)\<^sup>\<star> * H \<squnion> H * (H * d)\<^sup>\<star> * H) \<sqinter> d * H * d\<^sup>T"
      by (simp add: mult_left_dist_sup mult_right_dist_sup)
    also have "... = (H * d\<^sup>T)\<^sup>\<star> * H \<sqinter> d * H * d\<^sup>T \<squnion> H * (d * H)\<^sup>\<star> \<sqinter> d * H * d\<^sup>T"
      by (smt assms(1) big_forest_def inf_sup_distrib2 mult.semigroup_axioms preorder_idempotent star_slide semigroup.assoc)
    also have "... \<le> (H * d\<^sup>T)\<^sup>\<star> * H \<sqinter> d * H * d\<^sup>T \<squnion> 1"
      using 51 comp_inf.semiring.add_left_mono by blast
    finally have "?x * top * ?x\<^sup>T \<le> 1"
      using 51 by (smt assms(1) big_forest_def conv_dist_comp conv_dist_inf conv_dist_sup conv_involutive conv_star_commute equivalence_one_closed mult.semigroup_axioms sup.absorb2 semigroup.assoc conv_isotone conv_order)
    thus ?thesis
      by simp
  qed
  have 6: "?x\<^sup>T * top * ?x \<le> 1"
  proof -
    have "?x\<^sup>T * top * ?x = (d\<^sup>T \<sqinter> H\<^sup>T * e\<^sup>T\<^sup>T * top\<^sup>T \<sqinter> top\<^sup>T * a\<^sup>T\<^sup>T * H\<^sup>T * (d\<^sup>T\<^sup>T * H\<^sup>T)\<^sup>\<star>) * top * (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)"
      by (simp add: conv_dist_comp conv_dist_inf conv_star_commute mult_assoc)
    also have "... = (d\<^sup>T \<sqinter> H * e * top \<sqinter> top * a * H * (d * H)\<^sup>\<star>) * top * (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)"
      using assms(1) big_forest_def by auto
    also have "... = H * e * top \<sqinter> (d\<^sup>T \<sqinter> top * a * H * (d * H)\<^sup>\<star>) * top * (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)"
      by (smt comp_associative inf.sup_monoid.add_assoc inf.sup_monoid.add_commute star.circ_left_top star.circ_top vector_inf_comp)
    also have "... = H * e * top \<sqinter> d\<^sup>T * ((top * a * H * (d * H)\<^sup>\<star>)\<^sup>T \<sqinter> top) * (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)"
      by (simp add: covector_comp_inf_1 covector_mult_closed)
    also have "... = H * e * top \<sqinter> d\<^sup>T * (d * H)\<^sup>\<star>\<^sup>T * H * a\<^sup>T * top * (d \<sqinter> top * e\<^sup>T * H \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)"
      using assms(1) big_forest_def comp_associative conv_dist_comp by auto
    also have "... = H * e * top \<sqinter> d\<^sup>T * (d * H)\<^sup>\<star>\<^sup>T * H * a\<^sup>T * top * (d \<sqinter> (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top) \<sqinter> top * e\<^sup>T * H"
      by (smt comp_associative comp_inf_covector inf.sup_monoid.add_assoc inf.sup_monoid.add_commute)
    also have "... = H * e * top \<sqinter> d\<^sup>T * (d * H)\<^sup>\<star>\<^sup>T * H * a\<^sup>T * (top \<sqinter> ((H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)\<^sup>T) * d \<sqinter> top * e\<^sup>T * H"
      by (metis comp_associative comp_inf_vector vector_conv_covector vector_top_closed)
    also have "... = H * e * top \<sqinter> (H * e * top)\<^sup>T \<sqinter> d\<^sup>T * (d * H)\<^sup>\<star>\<^sup>T * H * a\<^sup>T * ((H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)\<^sup>T * d"
      by (smt assms(1) big_forest_def conv_dist_comp inf.left_commute inf.sup_monoid.add_commute symmetric_top_closed mult_assoc inf_top.left_neutral)
    also have "... = H * e * top * (H * e * top)\<^sup>T \<sqinter> d\<^sup>T * (d * H)\<^sup>\<star>\<^sup>T * H * a\<^sup>T * ((H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top)\<^sup>T * d"
      using vector_covector vector_mult_closed by auto
    also have "... = H * e * top * top\<^sup>T * e\<^sup>T * H\<^sup>T \<sqinter> d\<^sup>T * (d * H)\<^sup>\<star>\<^sup>T * H * a\<^sup>T * top\<^sup>T * a\<^sup>T\<^sup>T * H\<^sup>T * (H * d\<^sup>T)\<^sup>\<star>\<^sup>T * d"
      by (smt conv_dist_comp mult.semigroup_axioms symmetric_top_closed semigroup.assoc)
    also have "... = H * e * top * top * e\<^sup>T * H \<sqinter> d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * a * H * (d * H)\<^sup>\<star> * d"
      using assms(1) big_forest_def conv_dist_comp conv_star_commute by auto
    also have "... = H * e * top * e\<^sup>T * H \<sqinter> d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * a * H * (d * H)\<^sup>\<star> * d"
      using vector_top_closed mult_assoc by auto
    also have "... \<le> H \<sqinter> d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * (d * H)\<^sup>\<star> * d"
    proof -
      have "H * e * top * e\<^sup>T * H \<le> H * 1 * H"
        using 3 by (metis comp_associative mult_left_isotone mult_right_isotone)
      also have "... = H"
        using assms(1) big_forest_def preorder_idempotent by auto
      finally have 611: "H * e * top * e\<^sup>T * H \<le> H"
        by simp
      have "d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * a * H * (d * H)\<^sup>\<star> * d \<le> d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * 1 * H * (d * H)\<^sup>\<star> * d"
        using 2 by (metis comp_associative mult_left_isotone mult_right_isotone)
      also have "... = d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * (d * H)\<^sup>\<star> * d"
        using assms(1) big_forest_def mult.semigroup_axioms preorder_idempotent semigroup.assoc by fastforce
      finally have "d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * a\<^sup>T * top * a * H * (d * H)\<^sup>\<star> * d \<le> d\<^sup>T * (H * d\<^sup>T)\<^sup>\<star> * H * (d * H)\<^sup>\<star> * d"
        by simp
      thus ?thesis
        using 611 comp_inf.comp_isotone by blast
    qed
    also have "... = H \<sqinter> (d\<^sup>T * H)\<^sup>\<star> * d\<^sup>T * H * d * (H * d)\<^sup>\<star>"
      using star_slide mult_assoc by auto
    also have "... \<le> H \<sqinter> (d\<^sup>T * H)\<^sup>\<star> * (H * d)\<^sup>\<star>"
    proof -
      have "(d\<^sup>T * H)\<^sup>\<star> * d\<^sup>T * H * d * (H * d)\<^sup>\<star> \<le> (d\<^sup>T * H)\<^sup>\<star> * 1 * (H * d)\<^sup>\<star>"
        by (smt assms(1) big_forest_def conv_dist_comp mult_left_isotone mult_right_isotone preorder_idempotent mult_assoc)
      also have "... = (d\<^sup>T * H)\<^sup>\<star> * (H * d)\<^sup>\<star>"
        by simp
      finally show ?thesis
        using inf.sup_right_isotone by blast
    qed
    also have "... = H \<sqinter> ((d\<^sup>T * H)\<^sup>\<star> \<squnion> (H * d)\<^sup>\<star>)"
      by (simp add: assms(1) expand_big_forest)
    also have "... = H \<sqinter> (d\<^sup>T * H)\<^sup>\<star> \<squnion> H \<sqinter> (H * d)\<^sup>\<star>"
      by (simp add: comp_inf.semiring.distrib_left)
    also have "... = 1 \<squnion> H \<sqinter> (d\<^sup>T * H)\<^sup>+ \<squnion> H \<sqinter> (H * d)\<^sup>+"
    proof -
      have 612: "H \<sqinter> (H * d)\<^sup>\<star> = 1 \<squnion> H \<sqinter> (H * d)\<^sup>+"
        using assms(1) big_forest_def reflexive_inf_star by blast
      have "H \<sqinter> (d\<^sup>T * H)\<^sup>\<star> = 1 \<squnion> H \<sqinter> (d\<^sup>T * H)\<^sup>+"
        using assms(1) big_forest_def reflexive_inf_star by auto
      thus ?thesis
        using 612 sup_assoc sup_commute by auto
    qed
    also have "... \<le> 1"
    proof -
      have 613: "H \<sqinter> (H * d)\<^sup>+ \<le> 1"
        by (metis assms(3) inf.coboundedI1 p_antitone_iff p_shunting_swap regular_one_closed)
      hence "H \<sqinter> (d\<^sup>T * H)\<^sup>+ \<le> 1"
        by (metis assms(1) big_forest_def conv_dist_comp conv_dist_inf conv_plus_commute coreflexive_symmetric)
      thus ?thesis
        by (simp add: 613)
    qed
    finally show ?thesis
      by simp
  qed
  have 7:"bijective (?x * top)"
    using 4 5 6 arc_expanded by blast
  have "bijective (?x\<^sup>T * top)"
    using 4 5 6 arc_expanded by blast
  thus ?thesis
    using 7 by simp
qed

text \<open>
To maintain that $f$ can be extended to a minimum spanning forest we identify an edge, $i = v \sqcap \overline{F}e\top \sqcap \top e^\top F$, that may be exchanged with the \<open>selected_edge\<close>, $e$.
Here, we show that $i$ is an \<open>arc\<close>.
\<close>

lemma boruvka_edge_arc:
  assumes "equivalence F"
    and "forest v"
    and "arc e"
    and "regular F"
    and "F \<le> forest_components (F \<sqinter> v)"
    and "regular v"
    and "v * e\<^sup>T = bot"
    and "e * F * e = bot"
    and "e\<^sup>T \<le> v\<^sup>\<star>"
    and "e \<noteq> bot"
  shows "arc (v \<sqinter> -F * e * top \<sqinter> top * e\<^sup>T * F)"
proof -
  let ?i = "v \<sqinter> -F * e * top \<sqinter> top * e\<^sup>T * F"
  have 1: "?i\<^sup>T * top * ?i \<le> 1"
  proof -
    have "?i\<^sup>T * top * ?i = (v\<^sup>T \<sqinter> top * e\<^sup>T * -F \<sqinter> F * e * top) * top * (v \<sqinter> -F * e * top \<sqinter> top * e\<^sup>T * F)"
      using assms(1) conv_complement conv_dist_comp conv_dist_inf mult.semigroup_axioms semigroup.assoc by fastforce
    also have "... = F * e * top \<sqinter> (v\<^sup>T \<sqinter> top * e\<^sup>T * -F) * top * (v \<sqinter> -F * e * top) \<sqinter> top * e\<^sup>T * F"
      by (smt covector_comp_inf covector_mult_closed inf_vector_comp vector_export_comp vector_top_closed)
    also have "... = F * e * top \<sqinter> (v\<^sup>T \<sqinter> top * e\<^sup>T * -F) * top * top * (v \<sqinter> -F * e * top) \<sqinter> top * e\<^sup>T * F"
      by (simp add: comp_associative)
    also have "... = F * e * top \<sqinter> v\<^sup>T * (top \<sqinter> (top * e\<^sup>T * -F)\<^sup>T) * top * (v \<sqinter> -F * e * top) \<sqinter> top * e\<^sup>T * F"
      using comp_associative comp_inf_vector_1 by auto
    also have "... = F * e * top \<sqinter> v\<^sup>T * (top \<sqinter> (top * e\<^sup>T * -F)\<^sup>T) * (top \<sqinter> (-F * e * top)\<^sup>T) * v \<sqinter> top * e\<^sup>T * F"
      by (smt comp_inf_vector conv_dist_comp mult.semigroup_axioms symmetric_top_closed semigroup.assoc)
    also have "... = F * e * top \<sqinter> v\<^sup>T * (top * e\<^sup>T * -F)\<^sup>T * (-F * e * top)\<^sup>T * v \<sqinter> top * e\<^sup>T * F"
      by simp
    also have "... = F * e * top \<sqinter> v\<^sup>T * -F\<^sup>T * e\<^sup>T\<^sup>T * top\<^sup>T * top\<^sup>T * e\<^sup>T * -F\<^sup>T * v \<sqinter> top * e\<^sup>T * F"
      by (metis comp_associative conv_complement conv_dist_comp)
    also have "... = F * e * top \<sqinter> v\<^sup>T * -F * e * top * top * e\<^sup>T * -F * v \<sqinter> top * e\<^sup>T * F"
      by (simp add: assms(1))
    also have "... = F * e * top \<sqinter> v\<^sup>T * -F * e * top \<sqinter> top * e\<^sup>T * -F * v \<sqinter> top * e\<^sup>T * F"
      by (metis comp_associative comp_inf_covector inf.sup_monoid.add_assoc inf_top.left_neutral vector_top_closed)
    also have "... = (F \<sqinter> v\<^sup>T * -F) * e * top \<sqinter> top * e\<^sup>T * -F * v \<sqinter> top * e\<^sup>T * F"
      using assms(3) injective_comp_right_dist_inf mult_assoc by auto
    also have "... = (F \<sqinter> v\<^sup>T * -F) * e * top \<sqinter> top * e\<^sup>T * (F \<sqinter> -F * v)"
      using assms(3) conv_dist_comp inf.sup_monoid.add_assoc inf.sup_monoid.add_commute mult.semigroup_axioms univalent_comp_left_dist_inf semigroup.assoc by fastforce
    also have "... = (F \<sqinter> v\<^sup>T * -F) * e * top * top * e\<^sup>T * (F \<sqinter> -F * v)"
      by (metis comp_associative comp_inf_covector inf_top.left_neutral vector_top_closed)
    also have "... = (F \<sqinter> v\<^sup>T * -F) * e * top * e\<^sup>T * (F \<sqinter> -F * v)"
      by (simp add: comp_associative)
    also have "... \<le> (F \<sqinter> v\<^sup>T * -F) * (F \<sqinter> -F * v)"
      by (smt assms(3) conv_dist_comp mult_left_isotone shunt_bijective symmetric_top_closed top_right_mult_increasing mult_assoc)
    also have "... \<le> (F \<sqinter> v\<^sup>T * -F) * (F \<sqinter> -F * v) \<sqinter> F"
      by (metis assms(1) inf.absorb1 inf.cobounded1 mult_isotone preorder_idempotent)
    also have "... \<le> (F \<sqinter> v\<^sup>T * -F) * (F \<sqinter> -F * v) \<sqinter> (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star>"
      using assms(5) comp_inf.mult_right_isotone by auto
    also have "... \<le> (-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star>"
    proof -
      have "F \<sqinter> v\<^sup>T * -F \<le> (v\<^sup>T \<sqinter> F * -F\<^sup>T) * -F"
        by (metis conv_complement dedekind_2 inf_commute)
      also have "... = (v\<^sup>T \<sqinter> -F\<^sup>T) * -F"
        using assms(1) equivalence_comp_left_complement by simp
      finally have "F \<sqinter> v\<^sup>T * -F \<le> F \<sqinter> (v\<^sup>T \<sqinter> -F) * -F"
        using assms(1) by auto
      hence 11: "F \<sqinter> v\<^sup>T * -F = F \<sqinter> (-F \<sqinter> v\<^sup>T) * -F"
        by (metis inf.antisym_conv inf.sup_monoid.add_commute comp_left_subdist_inf inf.boundedE inf.sup_right_isotone)
      hence "F\<^sup>T \<sqinter> -F\<^sup>T * v\<^sup>T\<^sup>T = F\<^sup>T \<sqinter> -F\<^sup>T * (-F\<^sup>T \<sqinter> v\<^sup>T\<^sup>T)"
        by (metis (full_types) assms(1) conv_complement conv_dist_comp conv_dist_inf)
      hence 12: "F \<sqinter> -F * v = F \<sqinter> -F * (-F \<sqinter> v)"
        using assms(1) by (simp add: abel_semigroup.commute inf.abel_semigroup_axioms)
      have "(F \<sqinter> v\<^sup>T * -F) * (F \<sqinter> -F * v) = (F \<sqinter> (-F \<sqinter> v\<^sup>T) * -F) * (F \<sqinter> -F * (-F \<sqinter> v))"
        using 11 12 by auto
      also have "... \<le> (-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v)"
        by (metis comp_associative comp_isotone inf.cobounded2)
      finally show ?thesis
        using comp_inf.mult_left_isotone by blast
    qed
    also have "... = ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v)\<^sup>T * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star>) \<squnion> ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v)\<^sup>\<star>)"
      by (metis comp_associative inf_sup_distrib1 star.circ_loop_fixpoint)
    also have "... = ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v\<^sup>T) * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star>) \<squnion> ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v)\<^sup>\<star>)"
      using assms(1) conv_dist_inf by auto
    also have "... = bot \<squnion> ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v)\<^sup>\<star>)"
    proof -
      have "(-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v\<^sup>T) * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star> \<le> bot"
        using assms(1, 2) forests_bot_2 by (simp add: comp_associative)
      thus ?thesis
        using le_bot by blast
    qed
    also have "... = (-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (1 \<squnion> (F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v))"
      by (simp add: star.circ_plus_same star_left_unfold_equal)
    also have "... = ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> 1) \<squnion> ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v))"
      by (simp add: comp_inf.semiring.distrib_left)
    also have "... \<le> 1 \<squnion> ((-F \<sqinter> v\<^sup>T) * -F * -F * (-F \<sqinter> v) \<sqinter> (F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v))"
      using sup_left_isotone by auto
    also have "... \<le> 1 \<squnion> bot"
      using assms(1, 2) forests_bot_3 comp_inf.semiring.add_left_mono by simp
    finally show ?thesis
      by simp
  qed
  have 2: "?i * top * ?i\<^sup>T \<le> 1"
  proof -
    have "?i * top * ?i\<^sup>T = (v \<sqinter> -F * e * top \<sqinter> top * e\<^sup>T * F) * top * (v\<^sup>T \<sqinter> (-F * e * top)\<^sup>T \<sqinter> (top * e\<^sup>T * F)\<^sup>T)"
      by (simp add: conv_dist_inf)
    also have "... = (v \<sqinter> -F * e * top \<sqinter> top * e\<^sup>T * F) * top * (v\<^sup>T \<sqinter> top\<^sup>T * e\<^sup>T * -F\<^sup>T \<sqinter> F\<^sup>T * e\<^sup>T\<^sup>T * top\<^sup>T)"
      by (simp add: conv_complement conv_dist_comp mult_assoc)
    also have "... = (v \<sqinter> -F * e * top \<sqinter> top * e\<^sup>T * F) * top * (v\<^sup>T \<sqinter> top * e\<^sup>T * -F \<sqinter> F * e * top)"
      by (simp add: assms(1))
    also have "... = -F * e * top \<sqinter> (v \<sqinter> top * e\<^sup>T * F) * top * (v\<^sup>T \<sqinter> top * e\<^sup>T * -F \<sqinter> F * e * top)"
      by (smt inf.left_commute inf.sup_monoid.add_assoc vector_export_comp)
    also have "... = -F * e * top \<sqinter> (v \<sqinter> top * e\<^sup>T * F) * top * (v\<^sup>T \<sqinter> F * e * top) \<sqinter> top * e\<^sup>T * -F"
      by (smt comp_inf_covector inf.sup_monoid.add_assoc inf.sup_monoid.add_commute mult_assoc)
    also have "... = -F * e * top \<sqinter> (v \<sqinter> top * e\<^sup>T * F) * top * top * (v\<^sup>T \<sqinter> F * e * top) \<sqinter> top * e\<^sup>T * -F"
      by (simp add: mult_assoc)
    also have "... = -F * e * top \<sqinter> v * ((top * e\<^sup>T * F)\<^sup>T \<sqinter> top) * top * (v\<^sup>T \<sqinter> F * e * top) \<sqinter> top * e\<^sup>T * -F"
      by (simp add: comp_inf_vector_1 mult.semigroup_axioms semigroup.assoc)
    also have "... = -F * e * top \<sqinter> v * ((top * e\<^sup>T * F)\<^sup>T \<sqinter> top) * (top \<sqinter> (F * e * top)\<^sup>T) * v\<^sup>T \<sqinter> top * e\<^sup>T * -F"
      by (smt comp_inf_vector covector_comp_inf vector_conv_covector vector_mult_closed vector_top_closed)
    also have "... = -F * e * top \<sqinter> v * (top * e\<^sup>T * F)\<^sup>T * (F * e * top)\<^sup>T * v\<^sup>T \<sqinter> top * e\<^sup>T * -F"
      by simp
    also have "... = -F * e * top \<sqinter> v * F\<^sup>T * e\<^sup>T\<^sup>T * top\<^sup>T * top\<^sup>T * e\<^sup>T * F\<^sup>T * v\<^sup>T \<sqinter> top * e\<^sup>T * -F"
      by (metis comp_associative conv_dist_comp)
    also have "... = -F * e * top \<sqinter> v * F * e * top * top * e\<^sup>T * F * v\<^sup>T \<sqinter> top * e\<^sup>T * -F"
      using assms(1) by auto
    also have "... = -F * e * top \<sqinter> v * F * e * top \<sqinter> top * e\<^sup>T * F * v\<^sup>T \<sqinter> top * e\<^sup>T * -F"
      by (smt comp_associative comp_inf_covector inf.sup_monoid.add_assoc inf_top.left_neutral vector_top_closed)
    also have "... = (-F \<sqinter> v * F) * e * top \<sqinter> top * e\<^sup>T * F * v\<^sup>T \<sqinter> top * e\<^sup>T * -F"
      using injective_comp_right_dist_inf assms(3) mult.semigroup_axioms semigroup.assoc by fastforce
    also have "... = (-F \<sqinter> v * F) * e * top \<sqinter> top * e\<^sup>T * (F * v\<^sup>T \<sqinter> -F)"
      using injective_comp_right_dist_inf assms(3) conv_dist_comp inf.sup_monoid.add_assoc mult.semigroup_axioms univalent_comp_left_dist_inf semigroup.assoc by fastforce
    also have "... = (-F \<sqinter> v * F) * e * top * top * e\<^sup>T * (F * v\<^sup>T \<sqinter> -F)"
      by (metis inf_top_right vector_export_comp vector_top_closed)
    also have "... = (-F \<sqinter> v * F) * e * top * e\<^sup>T * (F * v\<^sup>T \<sqinter> -F)"
      by (simp add: comp_associative)
    also have "... \<le> (-F \<sqinter> v * F) * (F * v\<^sup>T \<sqinter> -F)"
      by (smt assms(3) conv_dist_comp mult.semigroup_axioms mult_left_isotone shunt_bijective symmetric_top_closed top_right_mult_increasing semigroup.assoc)
    also have "... = (-F \<sqinter> v * F) * ((v * F)\<^sup>T \<sqinter> -F)"
      by (simp add: assms(1) conv_dist_comp)
    also have "... = (-F \<sqinter> v * F) * (-F \<sqinter> v * F)\<^sup>T"
      using assms(1) conv_complement conv_dist_inf by (simp add: inf.sup_monoid.add_commute)
    also have "... \<le> (-F \<sqinter> v) * (F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (-F \<sqinter> v)\<^sup>T"
    proof -
      let ?Fv = "F \<sqinter> v"
      have "-F \<sqinter> v * F \<le> -F \<sqinter> v * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star>"
        using assms(5) inf.sup_right_isotone mult_right_isotone comp_associative by auto
      also have "... \<le> -F \<sqinter> v * (F \<sqinter> v)\<^sup>\<star>"
      proof -
        have "v * v\<^sup>T \<le> 1"
          by (simp add: assms(2))
        hence "v * v\<^sup>T * F \<le> F"
          using assms(1) dual_order.trans mult_left_isotone by blast
        hence "v * v\<^sup>T * F\<^sup>T\<^sup>\<star> * F\<^sup>\<star> \<le> F"
          by (metis assms(1) mult_1_right preorder_idempotent star.circ_sup_one_right_unfold star.circ_transitive_equal star_one star_simulation_right_equal mult_assoc)
        hence "v * (F \<sqinter> v)\<^sup>T * F\<^sup>T\<^sup>\<star> * F\<^sup>\<star> \<le> F"
          by (meson conv_isotone dual_order.trans inf.cobounded2 inf.sup_monoid.add_commute mult_left_isotone mult_right_isotone)
        hence "v * (F \<sqinter> v)\<^sup>T * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star> \<le> F"
          by (meson conv_isotone dual_order.trans inf.cobounded2 inf.sup_monoid.add_commute mult_left_isotone mult_right_isotone comp_isotone conv_dist_inf inf.cobounded1 star_isotone)
        hence "-F \<sqinter> v * (F \<sqinter> v)\<^sup>T * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star> \<le> bot"
          using eq_iff p_antitone pseudo_complement by auto
        hence "(-F \<sqinter> v * (F \<sqinter> v)\<^sup>T * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star>) \<squnion> v * (v \<sqinter> F)\<^sup>\<star> \<le> v * (v \<sqinter> F)\<^sup>\<star>"
          using bot_least le_bot by fastforce
        hence "(-F \<squnion> v * (v \<sqinter> F)\<^sup>\<star>) \<sqinter> (v * (F \<sqinter> v)\<^sup>T * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star> \<squnion> v * (v \<sqinter> F)\<^sup>\<star>) \<le> v * (v \<sqinter> F)\<^sup>\<star>"
          by (simp add: sup_inf_distrib2)
        hence "(-F \<squnion> v * (v \<sqinter> F)\<^sup>\<star>) \<sqinter> v * ((F \<sqinter> v)\<^sup>T * (F \<sqinter> v)\<^sup>T\<^sup>\<star> \<squnion> 1) * (v \<sqinter> F)\<^sup>\<star> \<le> v * (v \<sqinter> F)\<^sup>\<star>"
          by (simp add: inf.sup_monoid.add_commute mult.semigroup_axioms mult_left_dist_sup mult_right_dist_sup semigroup.assoc)
        hence "(-F \<squnion> v * (v \<sqinter> F)\<^sup>\<star>) \<sqinter> v * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (v \<sqinter> F)\<^sup>\<star> \<le> v * (v \<sqinter> F)\<^sup>\<star>"
          by (simp add: star_left_unfold_equal sup_commute)
        hence "-F \<sqinter> v * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (v \<sqinter> F)\<^sup>\<star> \<le> v * (v \<sqinter> F)\<^sup>\<star>"
          using comp_inf.mult_right_sub_dist_sup_left inf.order_lesseq_imp by blast
        thus ?thesis
          by (simp add: inf.sup_monoid.add_commute)
      qed
      also have "... \<le> (v \<sqinter> -F * (F \<sqinter> v)\<^sup>T\<^sup>\<star>) * (F \<sqinter> v)\<^sup>\<star>"
        by (metis dedekind_2 conv_star_commute inf.sup_monoid.add_commute)
      also have "... \<le> (v \<sqinter> -F * F\<^sup>T\<^sup>\<star>) * (F \<sqinter> v)\<^sup>\<star>"
        using conv_isotone inf.sup_right_isotone mult_left_isotone mult_right_isotone star_isotone by auto
      also have "... = (v \<sqinter> -F * F) * (F \<sqinter> v)\<^sup>\<star>"
        by (metis assms(1) equivalence_comp_right_complement mult_left_one star_one star_simulation_right_equal)
      also have "... = (-F \<sqinter> v) * (F \<sqinter> v)\<^sup>\<star>"
        using assms(1) equivalence_comp_right_complement inf.sup_monoid.add_commute by auto
      finally have "-F \<sqinter> v * F \<le> (-F \<sqinter> v) * (F \<sqinter> v)\<^sup>\<star>"
        by simp
      hence "(-F \<sqinter> v * F) * (-F \<sqinter> v * F)\<^sup>T \<le> (-F \<sqinter> v) * (F \<sqinter> v)\<^sup>\<star> * ((-F \<sqinter> v) * (F \<sqinter> v)\<^sup>\<star>)\<^sup>T"
        by (simp add: comp_isotone conv_isotone)
      also have "... = (-F \<sqinter> v) * (F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (-F \<sqinter> v)\<^sup>T"
        by (simp add: comp_associative conv_dist_comp conv_star_commute)
      finally show ?thesis
        by simp
    qed
    also have "... \<le> (-F \<sqinter> v) * ((F \<sqinter> v\<^sup>\<star>) \<squnion> (F \<sqinter> v\<^sup>T\<^sup>\<star>)) * (-F \<sqinter> v)\<^sup>T"
    proof -
      have "(F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v)\<^sup>T\<^sup>\<star> \<le> F\<^sup>\<star> * F\<^sup>T\<^sup>\<star>"
        using fc_isotone by auto
      also have "... \<le> F * F"
        by (metis assms(1) preorder_idempotent star.circ_sup_one_left_unfold star.circ_transitive_equal star_right_induct_mult)
      finally have 21: "(F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v)\<^sup>T\<^sup>\<star> \<le> F"
        using assms(1) dual_order.trans by blast
      have "(F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v)\<^sup>T\<^sup>\<star> \<le> v\<^sup>\<star> * v\<^sup>T\<^sup>\<star>"
        by (simp add: fc_isotone)
      hence "(F \<sqinter> v)\<^sup>\<star> * (F \<sqinter> v)\<^sup>T\<^sup>\<star> \<le> F \<sqinter> v\<^sup>\<star> * v\<^sup>T\<^sup>\<star>"
        using 21 by simp
      also have "... = F \<sqinter> (v\<^sup>\<star> \<squnion> v\<^sup>T\<^sup>\<star>)"
        by (simp add: assms(2) cancel_separate_eq)
      finally show ?thesis
        by (metis assms(4, 6) comp_associative comp_inf.semiring.distrib_left comp_isotone inf_pp_semi_commute mult_left_isotone regular_closed_inf)
    qed
    also have "... \<le> (-F \<sqinter> v) * (F \<sqinter> v\<^sup>T\<^sup>\<star>) * (-F \<sqinter> v)\<^sup>T \<squnion> (-F \<sqinter> v) * (F \<sqinter> v\<^sup>\<star>) * (-F \<sqinter> v)\<^sup>T"
      by (simp add: mult_left_dist_sup mult_right_dist_sup)
    also have "... \<le> (-F \<sqinter> v) * (-F \<sqinter> v)\<^sup>T \<squnion> (-F \<sqinter> v) * (-F \<sqinter> v)\<^sup>T"
    proof -
      have "(-F \<sqinter> v) * (F \<sqinter> v\<^sup>T\<^sup>\<star>) \<le> (-F \<sqinter> v) * ((F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star> \<sqinter> v\<^sup>T\<^sup>\<star>)"
        by (simp add: assms(5) inf.coboundedI1 mult_right_isotone)
      also have "... = (-F \<sqinter> v) * ((F \<sqinter> v)\<^sup>T * (F \<sqinter> v)\<^sup>T\<^sup>\<star> * (F \<sqinter> v)\<^sup>\<star> \<sqinter> v\<^sup>T\<^sup>\<star>) \<squnion> (-F \<sqinter> v) * ((F \<sqinter> v)\<^sup>\<star> \<sqinter> v\<^sup>T\<^sup>\<star>)"
        by (metis comp_associative comp_inf.mult_right_dist_sup mult_left_dist_sup star.circ_loop_fixpoint)
      also have "... \<le> (-F \<sqinter> v) * (F \<sqinter> v)\<^sup>T * top \<squnion> (-F \<sqinter> v) * ((F \<sqinter> v)\<^sup>\<star> \<sqinter> v\<^sup>T\<^sup>\<star>)"
        by (simp add: comp_associative comp_isotone inf.coboundedI2 inf.sup_monoid.add_commute le_supI1)
      also have "... \<le> (-F \<sqinter> v) * (F \<sqinter> v)\<^sup>T * top \<squnion> (-F \<sqinter> v) * (v\<^sup>\<star> \<sqinter> v\<^sup>T\<^sup>\<star>)"
        by (smt comp_inf.mult_right_isotone comp_inf.semiring.add_mono eq_iff inf.cobounded2 inf.sup_monoid.add_commute mult_right_isotone star_isotone)
      also have "... \<le> bot \<squnion> (-F \<sqinter> v) * (v\<^sup>\<star> \<sqinter> v\<^sup>T\<^sup>\<star>)"
        by (metis assms(1, 2) forests_bot_1 comp_associative comp_inf.semiring.add_right_mono mult_semi_associative vector_bot_closed)
      also have "... \<le> -F \<sqinter> v"
        by (simp add: assms(2) acyclic_star_inf_conv)
      finally have 22: "(-F \<sqinter> v) * (F \<sqinter> v\<^sup>T\<^sup>\<star>) \<le> -F \<sqinter> v"
        by simp
      have "((-F \<sqinter> v) * (F \<sqinter> v\<^sup>T\<^sup>\<star>))\<^sup>T = (F \<sqinter> v\<^sup>\<star>) * (-F \<sqinter> v)\<^sup>T"
        by (simp add: assms(1) conv_dist_inf conv_star_commute conv_dist_comp)
      hence "(F \<sqinter> v\<^sup>\<star>) * (-F \<sqinter> v)\<^sup>T \<le> (-F \<sqinter> v)\<^sup>T"
        using 22 conv_isotone by fastforce
      thus ?thesis
        using 22 by (metis assms(4, 6) comp_associative comp_inf.pp_comp_semi_commute comp_inf.semiring.add_mono comp_isotone inf_pp_commute mult_left_isotone)
    qed
    also have "... = (-F \<sqinter> v) * (-F \<sqinter> v)\<^sup>T"
      by simp
    also have "... \<le> v * v\<^sup>T"
      by (simp add: comp_isotone conv_isotone)
    also have "... \<le> 1"
      by (simp add: assms(2))
    thus ?thesis
      using calculation dual_order.trans by blast
  qed
  have 3: "top * ?i * top = top"
  proof -
    have 31: "regular (e\<^sup>T * -F * v * F * e)"
      using assms(3, 4, 6) arc_regular regular_mult_closed by auto
    have 32: "bijective ((top * e\<^sup>T)\<^sup>T)"
      using assms(3) by (simp add: conv_dist_comp)
    have "top * ?i * top = top * (v \<sqinter> -F * e * top) * ((top * e\<^sup>T * F)\<^sup>T \<sqinter> top)"
      by (simp add: comp_associative comp_inf_vector_1)
    also have "... = (top \<sqinter> (-F * e * top)\<^sup>T) * v * ((top * e\<^sup>T * F)\<^sup>T \<sqinter> top)"
      using comp_inf_vector conv_dist_comp by auto
    also have "... = (-F * e * top)\<^sup>T * v * (top * e\<^sup>T * F)\<^sup>T"
      by simp
    also have "... = top\<^sup>T * e\<^sup>T * -F\<^sup>T * v * F\<^sup>T * e\<^sup>T\<^sup>T * top\<^sup>T"
      by (simp add: comp_associative conv_complement conv_dist_comp)
    finally have 33: "top * ?i * top = top * e\<^sup>T * -F * v * F * e * top"
      by (simp add: assms(1))
    have "top * ?i * top \<noteq> bot"
    proof (rule ccontr)
      assume "\<not> top * (v \<sqinter> - F * e * top \<sqinter> top * e\<^sup>T * F) * top \<noteq> bot"
      hence "top * e\<^sup>T * -F * v * F * e * top = bot"
        using 33 by auto
      hence "e\<^sup>T * -F * v * F * e = bot"
        using 31 tarski comp_associative le_bot by fastforce
      hence "top * (-F * v * F * e)\<^sup>T \<le> -(e\<^sup>T)"
        by (metis comp_associative conv_complement_sub_leq conv_involutive p_bot schroeder_5_p)
      hence "top * e\<^sup>T * F\<^sup>T * v\<^sup>T * -F\<^sup>T \<le> -(e\<^sup>T)"
        by (simp add: comp_associative conv_complement conv_dist_comp)
      hence "v * F * e * top * e\<^sup>T \<le> F"
        by (metis assms(1, 4) comp_associative conv_dist_comp schroeder_3_p symmetric_top_closed)
      hence "v * F * e * top * top * e\<^sup>T \<le> F"
        by (simp add: comp_associative)
      hence "v * F * e * top \<le> F * (top * e\<^sup>T)\<^sup>T"
        using 32 by (metis shunt_bijective comp_associative conv_involutive)
      hence "v * F * e * top \<le> F * e * top"
        using comp_associative conv_dist_comp by auto
      hence "v\<^sup>\<star> * F * e * top \<le> F * e * top"
        using comp_associative star_left_induct_mult_iff by auto
      hence "e\<^sup>T * F * e * top \<le> F * e * top"
        by (meson assms(9) mult_left_isotone order_trans)
      hence "e\<^sup>T * F * e * top * (e * top)\<^sup>T \<le> F"
        using 32 shunt_bijective assms(3) mult_assoc by auto
      hence 34: "e\<^sup>T * F * e * top * top * e\<^sup>T \<le> F"
        by (metis conv_dist_comp mult.semigroup_axioms symmetric_top_closed semigroup.assoc)
      hence "e\<^sup>T \<le> F"
      proof -
        have "e\<^sup>T \<le> e\<^sup>T * e * e\<^sup>T"
          by (metis conv_involutive ex231c)
        also have "... \<le> e\<^sup>T * F * e * e\<^sup>T"
          using assms(1) comp_associative mult_left_isotone mult_right_isotone by fastforce
        also have "... \<le> e\<^sup>T * F * e * top * top * e\<^sup>T"
          by (simp add: mult_left_isotone top_right_mult_increasing vector_mult_closed)
        finally show ?thesis
          using 34 by simp
      qed
      hence 35: "e \<le> F"
        using assms(1) conv_order by fastforce
      have "top * (F * e)\<^sup>T \<le> - e"
        using assms(8) comp_associative schroeder_4_p by auto
      hence "top * e\<^sup>T * F \<le> - e"
        by (simp add: assms(1) comp_associative conv_dist_comp)
      hence "(top * e\<^sup>T)\<^sup>T * e \<le> - F"
        using schroeder_3_p by auto
      hence "e * top * e \<le> - F"
        by (simp add: conv_dist_comp)
      hence "e \<le> - F"
        by (simp add: assms(3) arc_top_arc)
      hence "e \<le> F \<sqinter> - F"
        using 35 inf.boundedI by blast
      hence "e = bot"
        using bot_unique by auto
      thus "False"
        using assms(10) by auto
    qed
    thus ?thesis
      by (metis assms(3, 4, 6) arc_regular regular_closed_inf regular_closed_top regular_conv_closed regular_mult_closed semiring.mult_not_zero tarski)
  qed
  have "bijective (?i * top) \<and> bijective (?i\<^sup>T * top)"
    using 1 2 3 arc_expanded by blast
  thus ?thesis
    by blast
qed

subsubsection \<open>Comparison of edge weights\<close>

text \<open>
In this section we compare the weight of the \<open>selected_edge\<close> with other edges of interest.
Theorems 8, 9, 10 and 11 are supporting lemmas.
For example, Theorem 8 is used to show that the \<open>selected_edge\<close> has its source inside and its target outside the component it is chosen for.
\<close>

text \<open>Theorem 8\<close>

lemma e_leq_c_c_complement_transpose_general:
  assumes "e = minarc (c * -(c)\<^sup>T \<sqinter> g)"
    and "regular c"
  shows "e \<le> c * -(c)\<^sup>T"
proof -
  have "e \<le> -- (c * - c\<^sup>T \<sqinter> g)"
    using assms(1) minarc_below order_trans by blast
  also have "... \<le> -- (c * - c\<^sup>T)"
    using order_lesseq_imp pp_isotone_inf by blast
  also have "... = c * - c\<^sup>T"
    using assms(2) regular_mult_closed by auto
  finally show ?thesis
    by simp
qed

text \<open>Theorem 9\<close>

lemma x_leq_c_transpose_general:
  assumes "forest h"
    and "vector c"
    and "x\<^sup>T * top \<le> forest_components(h) * e * top"
    and "e \<le> c * -c\<^sup>T"
    and "c = forest_components(h) * c"
  shows "x \<le> c\<^sup>T"
proof -
  let ?H = "forest_components h"
  have "x \<le> top * x"
    using top_left_mult_increasing by blast
  also have "... \<le> (?H * e * top)\<^sup>T"
    using assms(3) conv_dist_comp conv_order by force
  also have "... = top * e\<^sup>T * ?H"
    using assms(1) comp_associative conv_dist_comp forest_components_equivalence by auto
  also have "... \<le> top * (c * - c\<^sup>T)\<^sup>T * ?H"
    by (simp add: assms(4) conv_isotone mult_left_isotone mult_right_isotone)
  also have "... = top * (- c * c\<^sup>T) * ?H"
    by (simp add: conv_complement conv_dist_comp)
  also have "... \<le> top * c\<^sup>T * ?H"
    by (metis mult_left_isotone top.extremum mult_assoc)
  also have "... = c\<^sup>T * ?H"
    using assms(1, 2) component_is_vector vector_conv_covector by auto
  also have "... = c\<^sup>T"
    by (metis assms(1, 5) fch_equivalence conv_dist_comp)
  finally show ?thesis
    by simp
qed

text \<open>Theorem 10\<close>

lemma x_leq_c_complement_general:
  assumes "vector c"
    and "c * c\<^sup>T \<le> forest_components h"
    and "x \<le> c\<^sup>T"
    and "x \<le> -forest_components h"
  shows "x \<le> -c"
proof -
  let ?H = "forest_components h"
  have "x \<le> - ?H \<sqinter> c\<^sup>T"
    using assms(3, 4) by auto
  also have "... \<le> - c"
  proof -
    have "c \<sqinter> c\<^sup>T \<le> ?H"
      using assms(1, 2) vector_covector by auto
    hence "-?H \<sqinter> c \<sqinter> c\<^sup>T \<le> bot"
      using inf.sup_monoid.add_assoc p_antitone pseudo_complement by fastforce
    thus ?thesis
      using le_bot p_shunting_swap pseudo_complement by blast
  qed
  finally show ?thesis
    by simp
qed

text \<open>Theorem 11\<close>

lemma sum_e_below_sum_x_when_outgoing_same_component_general:
  assumes "e = minarc (c * -(c)\<^sup>T \<sqinter> g)"
    and "regular c"
    and "forest h"
    and "vector c"
    and "x\<^sup>T * top \<le> (forest_components h) * e * top"
    and "c = (forest_components h) * c"
    and "c * c\<^sup>T \<le> forest_components h"
    and "x \<le> - forest_components h \<sqinter> -- g"
    and "symmetric g"
    and "arc x"
    and "c \<noteq> bot"
  shows "sum (e \<sqinter> g) \<le> sum (x \<sqinter> g)"
proof -
  let ?H = "forest_components h"
  have 1:"e \<le> c * - c\<^sup>T"
    using assms(1, 2) e_leq_c_c_complement_transpose_general by auto
  have 2: "x \<le> c\<^sup>T"
    using 1 assms(3, 4, 5, 6) x_leq_c_transpose_general by auto
  hence "x \<le> -c"
    using assms(4, 7, 8) x_leq_c_complement_general inf.boundedE by blast
  hence "x \<le> - c \<sqinter> c\<^sup>T"
    using 2 by simp
  hence "x \<le> - c * c\<^sup>T"
    using assms(4) by (simp add: vector_complement_closed vector_covector)
  hence "x\<^sup>T \<le> c\<^sup>T\<^sup>T * - c\<^sup>T"
    by (metis conv_complement conv_dist_comp conv_isotone)
  hence 3: "x\<^sup>T \<le> c * - c\<^sup>T"
    by simp
  hence "x \<le> -- g"
    using assms(8) by auto
  hence "x\<^sup>T \<le> -- g"
    using assms(9) conv_complement conv_isotone by fastforce
  hence "x\<^sup>T \<sqinter> c * - c\<^sup>T \<sqinter> -- g \<noteq> bot"
    using 3 by (metis assms(10, 11) comp_inf.semiring.mult_not_zero conv_dist_comp
          conv_involutive inf.orderE mult_right_zero top.extremum)
  hence "x\<^sup>T \<sqinter> c * - c\<^sup>T \<sqinter> g \<noteq> bot"
    using inf.sup_monoid.add_commute pp_inf_bot_iff by auto
  hence "sum (minarc (c * - c\<^sup>T \<sqinter> g) \<sqinter> (c * - c\<^sup>T \<sqinter> g)) \<le> sum (x\<^sup>T \<sqinter> c * - c\<^sup>T \<sqinter> g)"
    using assms(10) minarc_min inf.sup_monoid.add_assoc by auto
  hence "sum (e \<sqinter> c * - c\<^sup>T \<sqinter> g) \<le> sum (x\<^sup>T \<sqinter> c * - c\<^sup>T \<sqinter> g)"
    using assms(1) inf.sup_monoid.add_assoc by auto
  hence "sum (e \<sqinter> g) \<le> sum (x\<^sup>T \<sqinter> g)"
    using 1 3 by (metis inf.orderE)
  hence "sum (e \<sqinter> g) \<le> sum (x \<sqinter> g)"
    using assms(9) sum_symmetric by auto
  thus ?thesis
    by simp
qed

lemma sum_e_below_sum_x_when_outgoing_same_component:
  assumes "symmetric g"
    and "vector j"
    and "forest h"
    and "x \<le> - forest_components h \<sqinter> -- g"
    and "x\<^sup>T * top \<le> forest_components h * selected_edge h j g * top"
    and "j \<noteq> bot"
    and "arc x"
  shows "sum (selected_edge h j g \<sqinter> g) \<le> sum (x \<sqinter> g)"
proof -
  let ?e = "selected_edge h j g"
  let ?c = "choose_component (forest_components h) j"
  let ?H = "forest_components h"
  show ?thesis
  proof (rule sum_e_below_sum_x_when_outgoing_same_component_general)
  next
    show "?e = minarc (?c * - ?c\<^sup>T \<sqinter> g)"
      by simp
  next
    show "regular ?c"
      using component_is_regular by auto
  next
    show "forest h"
      by (simp add: assms(3))
  next
    show "vector ?c"
      by (simp add: assms(2, 6) component_is_vector)
  next
    show "x\<^sup>T * top \<le> ?H * ?e * top"
      by (simp add: assms(5))
  next
    show "?c = ?H * ?c"
      using component_single by auto
  next
    show "?c * ?c\<^sup>T \<le> ?H"
      by (simp add: component_is_connected)
  next
    show "x \<le> -?H \<sqinter> -- g"
      using assms(4) by auto
  next
    show "symmetric g"
      by (simp add: assms(1))
  next
    show "arc x"
      by (simp add: assms(7))
  next
    show "?c \<noteq> bot"
      using assms(2, 5 , 6, 7) inf_bot_left le_bot minarc_bot mult_left_zero mult_right_zero by fastforce
  qed
qed

text \<open>
If there is a path in the \<open>big_forest\<close> from an edge between components, $a$, to the \<open>selected_edge\<close>, $e$, then the weight of $e$ is no greater than the weight of $a$.
This is because either,
\begin{itemize}
\item the edges $a$ and $e$ are adjacent the same component so that we can use \<open>sum_e_below_sum_x_when_outgoing_same_component\<close>, or
\item there is at least one edge between $a$ and $e$, namely $x$, the edge incoming to the component that $e$ is outgoing from.
      The path from $a$ to $e$ is split on $x$ using \<open>big_forest_path_split_disj\<close>.
      We show that the weight of $e$ is no greater than the weight of $x$ by making use of lemma \<open>sum_e_below_sum_x_when_outgoing_same_component\<close>.
      We define $x$ in a way that we can show that the weight of $x$ is no greater than the weight of $a$ using the invariant.
      Then, it follows that the weight of $e$ is no greater than the weight of $a$ owing to transitivity.
\end{itemize}
\<close>

lemma a_to_e_in_bigforest:
  assumes "symmetric g"
    and "f \<le> --g"
    and "vector j"
    and "forest h"
    and "big_forest (forest_components h) d"
    and "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
    and "(\<forall> a b . bf_between_arcs a b (forest_components h) d \<and> a \<le> -(forest_components h) \<sqinter> -- g \<and> b \<le> d \<longrightarrow> sum(b \<sqinter> g) \<le> sum(a \<sqinter> g))"
    and "regular d"
    and "j \<noteq> bot"
    and "b = selected_edge h j g"
    and "arc a"
    and "bf_between_arcs a b (forest_components h) (d \<squnion> selected_edge h j g)"
    and "a \<le> - forest_components h \<sqinter> -- g"
    and "regular h"
  shows "sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
proof -
  let ?p = "path f h j g"
  let ?e = "selected_edge h j g"
  let ?F = "forest_components f"
  let ?H = "forest_components h"
  have "sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
  proof (cases "a\<^sup>T * top \<le> ?H * ?e * top")
    case True
    show "a\<^sup>T * top \<le> ?H * ?e * top \<Longrightarrow> sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
    proof-
      have "sum (?e \<sqinter> g) \<le> sum (a \<sqinter> g)"
      proof (rule sum_e_below_sum_x_when_outgoing_same_component)
        show "symmetric g"
          using assms(1) by auto
      next
        show "vector j"
          using assms(3) by blast
      next
        show "forest h"
          by (simp add: assms(4))
      next
        show "a \<le> - ?H \<sqinter> -- g"
          using assms(13) by auto
      next
        show "a\<^sup>T * top \<le> ?H * ?e * top"
          using True by auto
      next
        show "j \<noteq> bot"
          by (simp add: assms(9))
      next
        show "arc a"
          by (simp add: assms(11))
      qed
      thus ?thesis
        using assms(10) by auto
    qed
  next
    case False
    show "\<not> a\<^sup>T * top \<le> ?H * ?e * top \<Longrightarrow> sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
    proof -
      let ?d' = "d \<squnion> ?e"
      let ?x = "d \<sqinter> top * ?e\<^sup>T * ?H \<sqinter> (?H * d\<^sup>T)\<^sup>\<star> * ?H * a\<^sup>T * top"
      have 61: "arc (?x)"
      proof (rule shows_arc_x)
        show "big_forest ?H d"
          by (simp add: assms(5))
      next
        show "bf_between_arcs a ?e ?H d"
        proof -
          have 611: "bf_between_arcs a b ?H (d \<squnion> b)"
            using assms(10, 12) by auto
          have 616: "regular h"
            using assms(14) by auto
          have "regular a"
            using 611 bf_between_arcs_def arc_regular by fastforce
          thus ?thesis
            using 616 by (smt big_forest_path_split_disj assms(4, 8, 10, 12) bf_between_arcs_def fch_equivalence minarc_regular regular_closed_star regular_conv_closed regular_mult_closed)
        qed
      next
        show "(?H * d)\<^sup>+ \<le> - ?H"
          using assms(5) big_forest_def by blast
      next
        show "\<not> a\<^sup>T * top \<le> ?H * ?e * top"
          by (simp add: False)
      next
        show "regular a"
          using assms(12) bf_between_arcs_def arc_regular by auto
      next
        show "regular ?e"
          using minarc_regular by auto
      next
        show "regular ?H"
          using assms(14) pp_dist_star regular_conv_closed regular_mult_closed by auto
      next
        show "regular d"
          using assms(8) by auto
      qed
      have 62: "bijective (a\<^sup>T * top)"
        by (simp add: assms(11))
      have 63: "bijective (?x * top)"
        using 61 by simp
      have 64: "?x \<le> (?H * d\<^sup>T)\<^sup>\<star> * ?H * a\<^sup>T * top"
        by simp
      hence "?x * top \<le> (?H * d\<^sup>T)\<^sup>\<star> * ?H * a\<^sup>T * top"
        using mult_left_isotone inf_vector_comp by auto
      hence "a\<^sup>T * top \<le> ((?H * d\<^sup>T)\<^sup>\<star> * ?H)\<^sup>T * ?x * top"
        using 62 63 64 by (smt bijective_reverse mult_assoc)
      also have "... = ?H * (d * ?H)\<^sup>\<star> * ?x * top"
        using conv_dist_comp conv_star_commute by auto
      also have "... = (?H * d)\<^sup>\<star> * ?H * ?x * top"
        by (simp add: star_slide)
      finally have "a\<^sup>T * top \<le> (?H * d)\<^sup>\<star> * ?H * ?x * top"
        by simp
      hence 65: "bf_between_arcs a ?x ?H d"
        using 61 assms(12) bf_between_arcs_def by blast
      have 66: "?x \<le> d"
        by (simp add: inf.sup_monoid.add_assoc)
      hence x_below_a: "sum (?x \<sqinter> g) \<le> sum (a \<sqinter> g)"
        using 65 bf_between_arcs_def assms(7, 13) by blast
      have "sum (?e \<sqinter> g) \<le> sum (?x \<sqinter> g)"
      proof (rule sum_e_below_sum_x_when_outgoing_same_component)
        show "symmetric g"
          using assms(1) by auto
      next
        show "vector j"
          using assms(3) by blast
      next
        show "forest h"
          by (simp add: assms(4))
      next
        show "?x \<le> - ?H \<sqinter> -- g"
        proof -
          have 67: "?x \<le> - ?H"
            using 66 assms(5) big_forest_def order_lesseq_imp by blast
          have "?x \<le> d"
            by (simp add: conv_isotone inf.sup_monoid.add_assoc)
          also have "... \<le> f \<squnion> f\<^sup>T"
          proof -
            have "h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T = f \<squnion> f\<^sup>T"
              by (simp add: assms(6))
            thus ?thesis
              by (metis (no_types) le_supE sup.absorb_iff2 sup.idem)
          qed
          also have "... \<le> -- g"
            using assms(1, 2) conv_complement conv_isotone by fastforce
          finally have "?x \<le> -- g"
            by simp
          thus ?thesis
            by (simp add: 67)
        qed
      next
        show "?x\<^sup>T * top \<le> ?H * ?e * top"
        proof -
          have "?x \<le> top * ?e\<^sup>T * ?H"
            using inf.coboundedI1 by auto
          hence "?x\<^sup>T \<le> ?H * ?e * top"
            using conv_dist_comp conv_dist_inf conv_star_commute inf.orderI inf.sup_monoid.add_assoc inf.sup_monoid.add_commute mult_assoc by auto
          hence "?x\<^sup>T * top \<le> ?H * ?e * top * top"
            by (simp add: mult_left_isotone)
          thus ?thesis
            by (simp add: mult_assoc)
        qed
      next
        show "j \<noteq> bot"
          by (simp add: assms(9))
      next
        show "arc (?x)"
          using 61 by blast
      qed
      hence "sum (?e \<sqinter> g) \<le> sum (a \<sqinter> g)"
        using x_below_a order.trans by blast
      thus ?thesis
        by (simp add: assms(10))
    qed
  qed
  thus ?thesis
    by simp
qed

subsubsection \<open>Maintenance of algorithm invariants\<close>

text \<open>
In this section, most of the work is done to maintain the invariants of the inner and outer loops of the algorithm.
In particular, we use \<open>exists_a_w\<close> to maintain that $f$ can be extended to a minimum spanning forest.
\<close>

lemma boruvka_exchange_spanning_inv:
  assumes "forest v"
    and "v\<^sup>\<star> * e\<^sup>T = e\<^sup>T"
    and "i \<le> v \<sqinter> top * e\<^sup>T * w\<^sup>T\<^sup>\<star>"
    and "arc i"
    and "arc e"
    and "v \<le> --g"
    and "w \<le> --g"
    and "e \<le> --g"
    and "components g \<le> forest_components v"
  shows "i \<le> (v \<sqinter> -i)\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
proof -
  have 1: "(v \<sqinter> -i \<sqinter> -i\<^sup>T) * (v\<^sup>T \<sqinter> -i \<sqinter> -i\<^sup>T) \<le> 1"
    using assms(1) comp_isotone order.trans inf.cobounded1 by blast
  have 2: "bijective (i * top) \<and> bijective (e\<^sup>T * top)"
    using assms(4, 5) mult_assoc by auto
  have "i \<le> v * (top * e\<^sup>T * w\<^sup>T\<^sup>\<star>)\<^sup>T"
    using assms(3) covector_mult_closed covector_restrict_comp_conv order_lesseq_imp vector_top_closed by blast
  also have "... \<le> v * w\<^sup>T\<^sup>\<star>\<^sup>T * e\<^sup>T\<^sup>T * top\<^sup>T"
    by (simp add: comp_associative conv_dist_comp)
  also have "... \<le> v * w\<^sup>\<star> * e * top"
    by (simp add: conv_star_commute)
  also have "... = v * w\<^sup>\<star> * e * e\<^sup>T * e * top"
    using assms(5) arc_eq_1 by (simp add: comp_associative)
  also have "... \<le> v * w\<^sup>\<star> * e * e\<^sup>T * top"
    by (simp add: comp_associative mult_right_isotone)
  also have "... \<le> (--g) * (--g)\<^sup>\<star> * (--g) * e\<^sup>T * top"
    using assms(6, 7, 8) by (simp add: comp_isotone star_isotone)
  also have "... \<le> (--g)\<^sup>\<star> * e\<^sup>T * top"
    by (metis comp_isotone mult_left_isotone star.circ_increasing star.circ_transitive_equal)
  also have "... \<le> v\<^sup>T\<^sup>\<star> * v\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: assms(9) mult_left_isotone)
  also have "... \<le> v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: assms(2) comp_associative)
  finally have "i \<le> v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    by simp
  hence "i * top \<le> v\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    by (metis comp_associative mult_left_isotone vector_top_closed)
  hence "e\<^sup>T * top \<le> v\<^sup>T\<^sup>\<star>\<^sup>T * i * top"
    using 2 by (metis bijective_reverse mult_assoc)
  also have "... = v\<^sup>\<star> * i * top"
    by (simp add: conv_star_commute)
  also have "... \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
  proof -
    have 3: "i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      using star.circ_loop_fixpoint sup_right_divisibility mult_assoc by auto
    have "(v \<sqinter> i) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> i * top * i * top"
      by (metis comp_isotone inf.cobounded1 inf.sup_monoid.add_commute mult_left_isotone top.extremum)
    also have "... \<le> i * top"
      by simp
    finally have 4: "(v \<sqinter> i) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      using 3 dual_order.trans by blast
    have 5: "(v \<sqinter> -i \<sqinter> -i\<^sup>T) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      by (metis mult_left_isotone star.circ_increasing star.left_plus_circ)
    have "v\<^sup>+ \<le> -1"
      by (simp add: assms(1))
    hence "v * v \<le> -1"
      by (metis mult_left_isotone order_trans star.circ_increasing star.circ_plus_same)
    hence "v * 1 \<le> -v\<^sup>T"
      by (simp add: schroeder_5_p)
    hence "v \<le> -v\<^sup>T"
      by simp
    hence "v \<sqinter> v\<^sup>T \<le> bot"
      by (simp add: bot_unique pseudo_complement)
    hence 7: "v \<sqinter> i\<^sup>T \<le> bot"
      by (metis assms(3) comp_inf.mult_right_isotone conv_dist_inf inf.boundedE inf.le_iff_sup le_bot)
    hence "(v \<sqinter> i\<^sup>T) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> bot"
      using le_bot semiring.mult_zero_left by fastforce
    hence 6: "(v \<sqinter> i\<^sup>T) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      using bot_least le_bot by blast
    have 8: "v = (v \<sqinter> i) \<squnion> (v \<sqinter> i\<^sup>T) \<squnion> (v \<sqinter> -i \<sqinter> -i\<^sup>T)"
    proof -
      have 81: "regular i"
        by (simp add: assms(4) arc_regular)
      have "(v \<sqinter> i\<^sup>T) \<squnion> (v \<sqinter> -i \<sqinter> -i\<^sup>T) = (v \<sqinter> -i)"
        using 7 by (metis comp_inf.coreflexive_comp_inf_complement inf_import_p inf_p le_bot maddux_3_11_pp top.extremum)
      hence "(v \<sqinter> i) \<squnion> (v \<sqinter> i\<^sup>T) \<squnion> (v \<sqinter> -i \<sqinter> -i\<^sup>T) = (v \<sqinter> i) \<squnion> (v \<sqinter> -i)"
        by (simp add: sup.semigroup_axioms semigroup.assoc)
      also have "... = v"
        using 81 by (metis maddux_3_11_pp)
      finally show ?thesis
        by simp
    qed
    have "(v \<sqinter> i) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<squnion> (v \<sqinter> i\<^sup>T) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<squnion> (v \<sqinter> -i \<sqinter> -i\<^sup>T) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      using 4 5 6 by simp
    hence "((v \<sqinter> i) \<squnion> (v \<sqinter> i\<^sup>T) \<squnion> (v \<sqinter> -i \<sqinter> -i\<^sup>T)) * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      by (simp add: mult_right_dist_sup)
    hence "v * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      using 8 by auto
    hence "i * top \<squnion> v * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      using 3 by auto
    hence 9:"v\<^sup>\<star> * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      by (simp add: star_left_induct_mult mult_assoc)
    have "v\<^sup>\<star> * i * top \<le> v\<^sup>\<star> * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
      using 3 mult_right_isotone mult_assoc by auto
    thus ?thesis
      using 9 order.trans by blast
  qed
  finally have "e\<^sup>T * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * i * top"
    by simp
  hence "i * top \<le> (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star>\<^sup>T * e\<^sup>T * top"
    using 2 by (metis bijective_reverse mult_assoc)
  also have "... = (v\<^sup>T \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    using comp_inf.inf_vector_comp conv_complement conv_dist_inf conv_star_commute inf.sup_monoid.add_commute by auto
  also have "... \<le> ((v \<sqinter> -i \<sqinter> -i\<^sup>T) \<squnion> (v\<^sup>T \<sqinter> -i \<sqinter> -i\<^sup>T))\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: mult_left_isotone star_isotone)
  finally have "i \<le> ((v\<^sup>T \<sqinter> -i \<sqinter> -i\<^sup>T) \<squnion> (v \<sqinter> -i \<sqinter> -i\<^sup>T))\<^sup>\<star> * e\<^sup>T * top"
    using dual_order.trans top_right_mult_increasing sup_commute by auto
  also have "... = (v\<^sup>T \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * (v \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    using 1 cancel_separate_1 by (simp add: sup_commute)
  also have "... \<le> (v\<^sup>T \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * v\<^sup>\<star> * e\<^sup>T * top"
    by (simp add: inf_assoc mult_left_isotone mult_right_isotone star_isotone)
  also have "... = (v\<^sup>T \<sqinter> -i \<sqinter> -i\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    using assms(2) mult_assoc by simp
  also have "... \<le> (v\<^sup>T \<sqinter> -i\<^sup>T)\<^sup>\<star> * e\<^sup>T * top"
    by (metis mult_left_isotone star_isotone inf.cobounded2 inf.left_commute inf.sup_monoid.add_commute)
  also have "... = (v \<sqinter> -i)\<^sup>T\<^sup>\<star> * e\<^sup>T * top"
    using conv_complement conv_dist_inf by auto
  finally show ?thesis
    by simp
qed

lemma exists_a_w:
  assumes "symmetric g"
    and "forest f"
    and "f \<le> --g"
    and "regular f"
    and "(\<exists>w . minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T)"
    and "vector j"
    and "regular j"
    and "forest h"
    and "forest_components h \<le> forest_components f"
    and "big_forest (forest_components h) d"
    and "d * top \<le> - j"
    and "forest_components h * j = j"
    and "forest_components f = (forest_components h * (d \<squnion> d\<^sup>T))\<^sup>\<star> * forest_components h"
    and "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
    and "(\<forall> a b . bf_between_arcs a b (forest_components h) d \<and> a \<le> -(forest_components h) \<sqinter> -- g \<and> b \<le> d \<longrightarrow> sum(b \<sqinter> g) \<le> sum(a \<sqinter> g))"
    and "regular d"
    and "selected_edge h j g \<le> - forest_components f"
    and "selected_edge h j g \<noteq> bot"
    and "j \<noteq> bot"
    and "regular h"
    and "h \<le> --g"
  shows "\<exists>w. minimum_spanning_forest w g \<and>
    f \<sqinter> - (selected_edge h j g)\<^sup>T \<sqinter> - (path f h j g) \<squnion> (f \<sqinter> - (selected_edge h j g)\<^sup>T \<sqinter> (path f h j g))\<^sup>T \<squnion> (selected_edge h j g) \<le> w \<squnion> w\<^sup>T"
proof -
  let ?p = "path f h j g"
  let ?e = "selected_edge h j g"
  let ?f = "(f \<sqinter> -?e\<^sup>T \<sqinter> -?p) \<squnion> (f \<sqinter> -?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> ?e"
  let ?F = "forest_components f"
  let ?H = "forest_components h"
  let ?ec = "choose_component (forest_components h) j * - choose_component (forest_components h) j\<^sup>T \<sqinter> g"
  from assms(4) obtain w where 2: "minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T"
    using assms(5) by blast
  hence 3: "regular w \<and> regular f \<and> regular ?e"
    by (metis assms(4) minarc_regular minimum_spanning_forest_def spanning_forest_def)
  have 5: "equivalence ?F"
    using assms(2) forest_components_equivalence by auto
  have "?e\<^sup>T * top * ?e\<^sup>T = ?e\<^sup>T"
    by (metis arc_conv_closed arc_top_arc coreflexive_bot_closed coreflexive_symmetric minarc_arc minarc_bot_iff semiring.mult_not_zero)
  hence "?e\<^sup>T * top * ?e\<^sup>T \<le> -?F"
    using 5 assms(17) conv_complement conv_isotone by fastforce
  hence 6: "?e * ?F * ?e = bot"
    using assms(2) le_bot triple_schroeder_p by simp
  let ?q = "w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
  let ?v = "(w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>)) \<squnion> ?q\<^sup>T"
  have 7: "regular ?q"
    using 3 regular_closed_star regular_conv_closed regular_mult_closed by auto
  have 8: "injective ?v"
  proof (rule kruskal_exchange_injective_inv_1)
    show "injective w"
      using 2 minimum_spanning_forest_def spanning_forest_def by blast
  next
    show "covector (top * ?e * w\<^sup>T\<^sup>\<star>)"
      by (simp add: covector_mult_closed)
  next
    show "top * ?e * w\<^sup>T\<^sup>\<star> * w\<^sup>T \<le> top * ?e * w\<^sup>T\<^sup>\<star>"
      by (simp add: mult_right_isotone star.right_plus_below_circ mult_assoc)
  next
    show "coreflexive ((top * ?e * w\<^sup>T\<^sup>\<star>)\<^sup>T * (top * ?e * w\<^sup>T\<^sup>\<star>) \<sqinter> w\<^sup>T * w)"
      using 2 by (metis comp_inf.semiring.mult_not_zero forest_bot kruskal_injective_inv_3 minarc_arc minarc_bot_iff minimum_spanning_forest_def semiring.mult_not_zero spanning_forest_def)
  qed
  have 9: "components g \<le> forest_components ?v"
  proof (rule kruskal_exchange_spanning_inv_1)
    show "injective (w \<sqinter> - (top *?e * w\<^sup>T\<^sup>\<star>) \<squnion> (w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)\<^sup>T)"
      using 8 by simp
  next
    show "regular (w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)"
      using 7 by simp
  next
    show "components g \<le> forest_components w"
      using 2 minimum_spanning_forest_def spanning_forest_def by blast
  qed
  have 10: "spanning_forest ?v g"
  proof (unfold spanning_forest_def, intro conjI)
    show "injective ?v"
      using 8 by auto
  next
    show "acyclic ?v"
    proof (rule kruskal_exchange_acyclic_inv_1)
      show "pd_kleene_allegory_class.acyclic w"
        using 2 minimum_spanning_forest_def spanning_forest_def by blast
    next
      show "covector (top * ?e * w\<^sup>T\<^sup>\<star>)"
        by (simp add: covector_mult_closed)
    qed
  next
    show "?v \<le> --g"
    proof (rule sup_least)
      show "w \<sqinter> - (top * ?e * w\<^sup>T\<^sup>\<star>) \<le> - - g"
        using 7 inf.coboundedI1 minimum_spanning_forest_def spanning_forest_def 2 by blast
    next
      show "(w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)\<^sup>T \<le> - - g"
        using 2 by (metis assms(1) conv_complement conv_isotone inf.coboundedI1 minimum_spanning_forest_def spanning_forest_def)
    qed
  next
    show "components g \<le> forest_components ?v"
      using 9 by simp
  next
    show "regular ?v"
      using 3 regular_closed_star regular_conv_closed regular_mult_closed by auto
  qed
  have 11: "sum (?v \<sqinter> g) = sum (w \<sqinter> g)"
  proof -
    have "sum (?v \<sqinter> g) = sum (w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>) \<sqinter> g) + sum (?q\<^sup>T \<sqinter> g)"
      using 2 by (smt conv_complement conv_top epm_8 inf_import_p inf_top_right regular_closed_top vector_top_closed minimum_spanning_forest_def spanning_forest_def sum_disjoint)
    also have "... = sum (w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>) \<sqinter> g) + sum (?q \<sqinter> g)"
      by (simp add: assms(1) sum_symmetric)
    also have "... = sum (((w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>)) \<squnion> ?q) \<sqinter> g)"
      using inf_commute inf_left_commute sum_disjoint by simp
    also have "... = sum (w \<sqinter> g)"
      using 3 7 8 maddux_3_11_pp by auto
    finally show ?thesis
      by simp
  qed
  have 12: "?v \<squnion> ?v\<^sup>T = w \<squnion> w\<^sup>T"
  proof -
    have "?v \<squnion> ?v\<^sup>T = (w \<sqinter> -?q) \<squnion> ?q\<^sup>T \<squnion> (w\<^sup>T \<sqinter> -?q\<^sup>T) \<squnion> ?q"
      using conv_complement conv_dist_inf conv_dist_sup inf_import_p sup_assoc by simp
    also have "... = w \<squnion> w\<^sup>T"
      using 3 7 conv_complement conv_dist_inf inf_import_p maddux_3_11_pp sup_monoid.add_assoc sup_monoid.add_commute by auto
    finally show ?thesis
      by simp
  qed
  have 13: "?v * ?e\<^sup>T = bot"
  proof (rule kruskal_reroot_edge)
    show "injective (?e\<^sup>T * top)"
      using assms(18) minarc_arc minarc_bot_iff by blast
  next
    show "pd_kleene_allegory_class.acyclic w"
      using 2 minimum_spanning_forest_def spanning_forest_def by simp
  qed
  have "?v \<sqinter> ?e \<le> ?v \<sqinter> top * ?e"
    using inf.sup_right_isotone top_left_mult_increasing by simp
  also have "... \<le> ?v * (top * ?e)\<^sup>T"
    using covector_restrict_comp_conv covector_mult_closed vector_top_closed by simp
  finally have 14: "?v \<sqinter> ?e = bot"
    using 13 by (metis conv_dist_comp mult_assoc le_bot mult_left_zero)
  let ?i = "?v \<sqinter> (- ?F) * ?e * top \<sqinter> top * ?e\<^sup>T * ?F"
  let ?w = "(?v \<sqinter> -?i) \<squnion> ?e"
  have 15: "regular ?i"
    using 3 regular_closed_star regular_conv_closed regular_mult_closed by simp
  have 16: "?F \<le> -?i"
  proof -
    have 161: "bijective (?e * top)"
      using assms(18) minarc_arc minarc_bot_iff by auto
    have "?i \<le> - ?F * ?e * top"
      using inf.cobounded2 inf.coboundedI1 by blast
    also have "... = - (?F * ?e * top)"
      using 161 comp_bijective_complement by (simp add: mult_assoc)
    finally have "?i \<le> - (?F * ?e * top)"
      by blast
    hence 162: "?i \<sqinter> ?F \<le> - (?F * ?e * top)"
      using inf.coboundedI1 by blast
    have "?i \<sqinter> ?F \<le> ?F \<sqinter> (top * ?e\<^sup>T * ?F)"
      by (meson inf_le1 inf_le2 le_infI order_trans)
    also have "... \<le> ?F * (top * ?e\<^sup>T * ?F)\<^sup>T"
      by (simp add: covector_mult_closed covector_restrict_comp_conv)
    also have "... = ?F * ?F\<^sup>T * ?e\<^sup>T\<^sup>T * top\<^sup>T"
      by (simp add: conv_dist_comp mult_assoc)
    also have "... = ?F * ?F * ?e * top"
      by (simp add: conv_dist_comp conv_star_commute)
    also have "... = ?F * ?e * top"
      by (simp add: 5 preorder_idempotent)
    finally have "?i \<sqinter> ?F \<le> ?F * ?e * top"
      by simp
    hence "?i \<sqinter> ?F \<le> ?F * ?e * top \<sqinter> - (?F * ?e * top)"
      using 162 inf.bounded_iff by blast
    also have "... = bot"
      by simp
    finally show ?thesis
      using le_bot p_antitone_iff pseudo_complement by blast
  qed
  have 17: "?i \<le> top * ?e\<^sup>T * (?F \<sqinter> ?v \<sqinter> -?i)\<^sup>T\<^sup>\<star>"
  proof -
    have "?i \<le> ?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> * (?F \<sqinter> ?v)\<^sup>\<star>"
      using 2 8 12 by (smt inf.sup_right_isotone kruskal_forest_components_inf mult_right_isotone mult_assoc)
    also have "... = ?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> * (1 \<squnion> (?F \<sqinter> ?v)\<^sup>\<star> * (?F \<sqinter> ?v))"
      using star_left_unfold_equal star.circ_right_unfold_1 by auto
    also have "... = ?v \<sqinter> - ?F * ?e * top \<sqinter> (top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> \<squnion> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> * (?F \<sqinter> ?v)\<^sup>\<star> * (?F \<sqinter> ?v))"
      by (simp add: mult_left_dist_sup mult_assoc)
    also have "... = (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star>) \<squnion> (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> * (?F \<sqinter> ?v)\<^sup>\<star> * (?F \<sqinter> ?v))"
      using comp_inf.semiring.distrib_left by blast
    also have "... \<le> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> \<squnion> (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> * (?F \<sqinter> ?v)\<^sup>\<star> * (?F \<sqinter> ?v))"
      using comp_inf.semiring.add_right_mono inf_le2 by blast
    also have "... \<le> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> \<squnion> (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * (?F\<^sup>T \<sqinter> ?v\<^sup>T)\<^sup>\<star> * (?F \<sqinter> ?v)\<^sup>\<star> * (?F \<sqinter> ?v))"
      by (simp add: conv_dist_inf)
    also have "... \<le> top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> \<squnion> (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F\<^sup>T\<^sup>\<star> * ?F\<^sup>\<star> * (?F \<sqinter> ?v))"
    proof -
      have "top * ?e\<^sup>T * (?F\<^sup>T \<sqinter> ?v\<^sup>T)\<^sup>\<star> * (?F \<sqinter> ?v)\<^sup>\<star> * (?F \<sqinter> ?v) \<le> top * ?e\<^sup>T * ?F\<^sup>T\<^sup>\<star> * ?F\<^sup>\<star> * (?F \<sqinter> ?v)"
        using star_isotone by (simp add: comp_isotone)
      hence "?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * (?F\<^sup>T \<sqinter> ?v\<^sup>T)\<^sup>\<star> * (?F \<sqinter> ?v)\<^sup>\<star> * (?F \<sqinter> ?v) \<le> ?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F\<^sup>T\<^sup>\<star> * ?F\<^sup>\<star> * (?F \<sqinter> ?v)"
        using inf.sup_right_isotone by blast
      thus ?thesis
        using sup_right_isotone by blast
    qed
    also have "... = top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> \<squnion> (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F\<^sup>\<star> * ?F\<^sup>\<star> * (?F \<sqinter> ?v))"
      using 5 by auto
    also have "... = top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> \<squnion> (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F * ?F * (?F \<sqinter> ?v))"
      by (simp add: assms(2) forest_components_star)
    also have "... = top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star> \<squnion> (?v \<sqinter> - ?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F * (?F \<sqinter> ?v))"
      using 5 mult.semigroup_axioms preorder_idempotent semigroup.assoc by fastforce
    also have "... = top * ?e\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>\<star>"
    proof -
      have "?e * top * ?e\<^sup>T \<le> 1"
        using assms(18) arc_expanded minarc_arc minarc_bot_iff by auto
      hence "?F * ?e * top * ?e\<^sup>T \<le> ?F * 1"
        by (metis comp_associative comp_isotone mult_semi_associative star.circ_transitive_equal)
      hence "?v * ?v\<^sup>T * ?F * ?e * top * ?e\<^sup>T \<le> 1 * ?F * 1"
        using 8 by (smt comp_isotone mult_assoc)
      hence 171: "?v * ?v\<^sup>T * ?F * ?e * top * ?e\<^sup>T \<le> ?F"
        by simp
      hence "?v * (?F \<sqinter> ?v)\<^sup>T * ?F * ?e * top * ?e\<^sup>T \<le> ?F"
      proof -
        have "?v * (?F \<sqinter> ?v)\<^sup>T * ?F * ?e * top * ?e\<^sup>T \<le> ?v * ?v\<^sup>T * ?F * ?e * top * ?e\<^sup>T"
          by (simp add: conv_dist_inf mult_left_isotone mult_right_isotone)
        thus ?thesis
          using 171 order_trans by blast
      qed
      hence 172: "-?F * ((?F \<sqinter> ?v)\<^sup>T * ?F * ?e * top * ?e\<^sup>T)\<^sup>T \<le> -?v"
        by (smt schroeder_4_p comp_associative order_lesseq_imp pp_increasing)
      have "-?F * ((?F \<sqinter> ?v)\<^sup>T * ?F * ?e * top * ?e\<^sup>T)\<^sup>T = -?F * ?e\<^sup>T\<^sup>T * top\<^sup>T * ?e\<^sup>T * ?F\<^sup>T * (?F \<sqinter> ?v)\<^sup>T\<^sup>T"
        by (simp add: comp_associative conv_dist_comp)
      also have "... = -?F * ?e * top * ?e\<^sup>T * ?F * (?F \<sqinter> ?v)"
        using 5 by auto
      also have "... = -?F * ?e * top * top * ?e\<^sup>T * ?F * (?F \<sqinter> ?v)"
        using comp_associative by auto
      also have "... = -?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F * (?F \<sqinter> ?v)"
        by (smt comp_associative comp_inf.star.circ_decompose_9 comp_inf.star_star_absorb comp_inf_covector inf_vector_comp vector_top_closed)
      finally have "-?F * ((?F \<sqinter> ?v)\<^sup>T * ?F * ?e * top * ?e\<^sup>T)\<^sup>T = -?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F * (?F \<sqinter> ?v)"
        by simp
      hence "-?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F * (?F \<sqinter> ?v) \<le> -?v"
        using 172 by auto
      hence "?v \<sqinter> -?F * ?e * top \<sqinter> top * ?e\<^sup>T * ?F * (?F \<sqinter> ?v) \<le> bot"
        by (smt bot_unique inf.sup_monoid.add_commute p_shunting_swap pseudo_complement)
      thus ?thesis
        using le_bot sup_monoid.add_0_right by blast
    qed
    also have "... = top * ?e\<^sup>T * (?F \<sqinter> ?v \<sqinter> -?i)\<^sup>T\<^sup>\<star>"
      using 16 by (smt comp_inf.coreflexive_comp_inf_complement inf_top_right p_bot pseudo_complement top.extremum)
    finally show ?thesis
      by blast
  qed
  have 18: "?i \<le> top * ?e\<^sup>T * ?w\<^sup>T\<^sup>\<star>"
  proof -
    have "?i \<le> top * ?e\<^sup>T * (?F \<sqinter> ?v \<sqinter> -?i)\<^sup>T\<^sup>\<star>"
      using 17 by simp
    also have "... \<le> top * ?e\<^sup>T * (?v \<sqinter> -?i)\<^sup>T\<^sup>\<star>"
      using mult_right_isotone conv_isotone star_isotone inf.cobounded2 inf.sup_monoid.add_assoc by (simp add: inf.sup_monoid.add_assoc eq_iff inf.sup_monoid.add_commute)
    also have "... \<le> top * ?e\<^sup>T * ((?v \<sqinter> -?i) \<squnion> ?e)\<^sup>T\<^sup>\<star>"
      using mult_right_isotone conv_isotone star_isotone sup_ge1 by simp
    finally show ?thesis
      by blast
  qed
  have 19: "?i \<le> top * ?e\<^sup>T * ?v\<^sup>T\<^sup>\<star>"
  proof -
    have "?i \<le> top * ?e\<^sup>T * (?F \<sqinter> ?v \<sqinter> -?i)\<^sup>T\<^sup>\<star>"
      using 17 by simp
    also have "... \<le> top * ?e\<^sup>T * (?v \<sqinter> -?i)\<^sup>T\<^sup>\<star>"
      using mult_right_isotone conv_isotone star_isotone inf.cobounded2 inf.sup_monoid.add_assoc by (simp add: inf.sup_monoid.add_assoc eq_iff inf.sup_monoid.add_commute)
    also have "... \<le> top * ?e\<^sup>T * (?v)\<^sup>T\<^sup>\<star>"
      using mult_right_isotone conv_isotone star_isotone by auto
    finally show ?thesis
      by blast
  qed
  have 20: "f \<squnion> f\<^sup>T \<le> (?v \<sqinter> -?i \<sqinter> -?i\<^sup>T) \<squnion> (?v\<^sup>T \<sqinter> -?i \<sqinter> -?i\<^sup>T)"
  proof (rule kruskal_edge_between_components_2)
    show "?F \<le> - ?i"
      using 16 by simp
  next
    show "injective f"
      by (simp add: assms(2))
  next
    show "f \<squnion> f\<^sup>T \<le> w \<sqinter> - (top * ?e * w\<^sup>T\<^sup>\<star>) \<squnion> (w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> (w \<sqinter> - (top * ?e * w\<^sup>T\<^sup>\<star>) \<squnion> (w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)\<^sup>T)\<^sup>T"
      using 2 12 by (metis conv_dist_sup conv_involutive conv_isotone le_supI sup_commute)
  qed
  have "minimum_spanning_forest ?w g \<and> ?f \<le> ?w \<squnion> ?w\<^sup>T"
  proof (intro conjI)
    have 211: "?e\<^sup>T \<le> ?v\<^sup>\<star>"
    proof (rule kruskal_edge_arc_1[where g=g and h="?ec"])
      show "?e \<le> -- ?ec"
        using minarc_below by blast
    next
      show "?ec \<le> g"
        using assms(4) inf.cobounded2 by (simp add: boruvka_inner_invariant_def boruvka_outer_invariant_def conv_dist_inf)
    next
      show "symmetric g"
        by (meson assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def)
    next
      show "components g \<le> forest_components (w \<sqinter> - (top * ?e * w\<^sup>T\<^sup>\<star>) \<squnion> (w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)\<^sup>T)"
        using 9 by simp
    next
      show "(w \<sqinter> - (top * ?e * w\<^sup>T\<^sup>\<star>) \<squnion> (w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)\<^sup>T) * ?e\<^sup>T = bot"
        using 13 by blast
    qed
    have 212: "arc ?i"
    proof (rule boruvka_edge_arc)
      show "equivalence ?F"
        by (simp add: 5)
    next
      show "forest ?v"
        using 10 spanning_forest_def by blast
    next
      show "arc ?e"
        using assms(18) minarc_arc minarc_bot_iff by blast
    next
      show "regular ?F"
        using 3 regular_closed_star regular_conv_closed regular_mult_closed by auto
    next
      show "?F \<le> forest_components (?F \<sqinter> ?v)"
        by (simp add: 12 2 8 kruskal_forest_components_inf)
    next
      show "regular ?v"
        using 10 spanning_forest_def by blast
    next
      show "?v * ?e\<^sup>T = bot"
        using 13 by auto
    next
      show "?e * ?F * ?e = bot"
        by (simp add: 6)
    next
      show "?e\<^sup>T \<le> ?v\<^sup>\<star>"
        using 211 by auto

    next
      show "?e \<noteq> bot"
        by (simp add: assms(18))
    qed
    show "minimum_spanning_forest ?w g"
    proof (unfold minimum_spanning_forest_def, intro conjI)
      have "(?v \<sqinter> -?i) * ?e\<^sup>T \<le> ?v * ?e\<^sup>T"
        using inf_le1 mult_left_isotone by simp
      hence "(?v \<sqinter> -?i) * ?e\<^sup>T = bot"
        using 13 le_bot by simp
      hence 221: "?e * (?v \<sqinter> -?i)\<^sup>T = bot"
        using conv_dist_comp conv_involutive conv_bot by force
      have 222: "injective ?w"
      proof (rule injective_sup)
        show "injective (?v \<sqinter> -?i)"
          using 8 by (simp add: injective_inf_closed)
      next
        show "coreflexive (?e * (?v \<sqinter> -?i)\<^sup>T)"
          using 221 by simp
      next
        show "injective ?e"
          by (metis arc_injective minarc_arc coreflexive_bot_closed coreflexive_injective minarc_bot_iff)
      qed
      show "spanning_forest ?w g"
      proof (unfold spanning_forest_def, intro conjI)
        show "injective ?w"
          using 222 by simp
      next
        show "acyclic ?w"
        proof (rule kruskal_exchange_acyclic_inv_2)
          show "acyclic ?v"
            using 10 spanning_forest_def by blast
        next
          show "injective ?v"
            using 8 by simp
        next
          show "?i \<le>?v"
            using inf.coboundedI1 by simp
        next
          show "bijective (?i\<^sup>T * top)"
            using 212 by simp
        next
          show "bijective (?e * top)"
            using 14 212 by (smt assms(4) comp_inf.idempotent_bot_closed conv_complement minarc_arc minarc_bot_iff p_bot regular_closed_bot semiring.mult_not_zero symmetric_top_closed)
        next
          show "?i \<le> top * ?e\<^sup>T *?v\<^sup>T\<^sup>\<star>"
            using 19 by simp
        next
          show "?v * ?e\<^sup>T * top = bot"
            using 13 by simp
        qed
      next
        have "?w \<le> ?v \<squnion> ?e"
          using inf_le1 sup_left_isotone by simp
        also have "... \<le> --g \<squnion> ?e"
          using 10 sup_left_isotone spanning_forest_def by blast
        also have "... \<le> --g \<squnion> --h"
        proof -
          have 1: "--g \<le> --g \<squnion> --h"
            by simp
          have 2: "?e \<le> --g \<squnion> --h"
            by (metis inf.coboundedI1 inf.sup_monoid.add_commute minarc_below order.trans p_dist_inf p_dist_sup sup.cobounded1)
          thus ?thesis
            using 1 2 by simp
        qed
        also have "... \<le> --g"
            using assms(20, 21) by auto
        finally show "?w \<le> --g"
          by simp
      next
        have 223: "?i \<le> (?v \<sqinter> -?i)\<^sup>T\<^sup>\<star> * ?e\<^sup>T * top"
        proof (rule boruvka_exchange_spanning_inv)
          show "forest ?v"
            using 10 spanning_forest_def by blast
        next
          show "?v\<^sup>\<star> * ?e\<^sup>T = ?e\<^sup>T"
            using 13 by (smt conv_complement conv_dist_comp conv_involutive conv_star_commute dense_pp fc_top regular_closed_top star_absorb)
        next
          show "?i \<le> ?v \<sqinter> top * ?e\<^sup>T * ?w\<^sup>T\<^sup>\<star>"
            using 18 inf.sup_monoid.add_assoc by auto
        next
          show "arc ?i"
            using 212 by blast
        next
          show "arc ?e"
            using assms(18) minarc_arc minarc_bot_iff by auto
        next
          show "?v \<le> --g"
            using 10 spanning_forest_def by blast
        next
          show "?w \<le> --g"
          proof -
            have 2231: "?e \<le> --g"
              by (metis inf.boundedE minarc_below pp_dist_inf)
            have "?w \<le> ?v \<squnion> ?e"
              using inf_le1 sup_left_isotone by simp
            also have "... \<le> --g"
              using 2231 10 spanning_forest_def sup_least by blast
            finally show ?thesis
              by blast
          qed
        next
          show "?e \<le> --g"
            by (metis inf.boundedE minarc_below pp_dist_inf)
        next
          show "components g \<le> forest_components ?v"
            by (simp add: 9)
        qed
        have "components g \<le> forest_components ?v"
          using 10 spanning_forest_def by auto
        also have "... \<le> forest_components ?w"
        proof (rule kruskal_exchange_forest_components_inv)
        next
          show "injective ((?v \<sqinter> -?i) \<squnion> ?e)"
            using 222 by simp
        next
          show "regular ?i"
            using 15 by simp
        next
          show "?e * top * ?e = ?e"
            by (metis arc_top_arc minarc_arc minarc_bot_iff semiring.mult_not_zero)
        next
          show "?i \<le> top * ?e\<^sup>T * ?v\<^sup>T\<^sup>\<star>"
            using 19 by blast
        next
          show "?v * ?e\<^sup>T * top = bot"
            using 13 by simp
        next
          show "injective ?v"
            using 8 by simp
        next
          show "?i \<le> ?v"
            by (simp add: le_infI1)
        next
          show "?i \<le> (?v \<sqinter> -?i)\<^sup>T\<^sup>\<star> * ?e\<^sup>T * top"
            using 223 by blast
        qed
        finally show "components g \<le> forest_components ?w"
          by simp
      next
        show "regular ?w"
          using 3 7 regular_conv_closed by simp
      qed
    next
      have 224: "?e \<sqinter> g \<noteq> bot"
        using assms(18) inf.left_commute inf_bot_right minarc_meet_bot by fastforce
      have 225: "sum (?e \<sqinter> g) \<le> sum (?i \<sqinter> g)"
      proof (rule a_to_e_in_bigforest)
        show "symmetric g"
          using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
      next
        show "j \<noteq> bot"
          by (simp add: assms(19))
      next
        show "f \<le> -- g"
          by (simp add: assms(3))
      next
        show "vector j"
          using assms(6) boruvka_inner_invariant_def by blast
      next
        show "forest h"
          by (simp add: assms(8))
      next
        show " big_forest (forest_components h) d"
          by (simp add: assms(10))
      next
        show "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
          by (simp add: assms(14))
      next
        show "\<forall>a b. bf_between_arcs a b (?H) d \<and> a \<le> - ?H \<sqinter> - - g \<and> b \<le> d \<longrightarrow> sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
          by (simp add: assms(15))
      next
        show "regular d"
          using assms(16) by auto
      next
        show "?e = ?e"
          by simp
      next
        show "arc ?i"
          using 212 by blast
      next
        show "bf_between_arcs ?i ?e ?H (d \<squnion> ?e)"
        proof -
          have "d\<^sup>T * ?H * ?e = bot"
            using assms(6, 7, 11, 12, 19) dT_He_eq_bot le_bot by blast
          hence 251: "d\<^sup>T * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
            by simp
          hence "d\<^sup>T * ?H * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
            by (metis assms(8) forest_components_star star.circ_decompose_9 mult_assoc)
          hence "d\<^sup>T * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
          proof -
            have "d\<^sup>T * ?H * d \<le> 1"
              using assms(10) big_forest_def dTransHd_le_1 by blast
            hence "d\<^sup>T * ?H * d * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
              by (metis mult_left_isotone star.circ_circ_mult star_involutive star_one)
            hence "d\<^sup>T * ?H * ?e \<squnion> d\<^sup>T * ?H * d * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
              using 251 by simp
            hence "d\<^sup>T * (1 \<squnion> ?H * d * (?H * d)\<^sup>\<star>) * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
              by (simp add: comp_associative comp_left_dist_sup semiring.distrib_right)
            thus ?thesis
              by (simp add: star_left_unfold_equal)
          qed
          hence "?H * d\<^sup>T * (?H * d)\<^sup>\<star> * ?H * ?e \<le> ?H * (?H * d)\<^sup>\<star> * ?H * ?e"
            by (simp add: mult_right_isotone mult_assoc)
          hence "?H * d\<^sup>T * (?H * d)\<^sup>\<star> * ?H * ?e \<le> ?H * ?H * (d * ?H)\<^sup>\<star> * ?e"
            by (smt star_slide mult_assoc)
          hence "?H * d\<^sup>T * (?H * d)\<^sup>\<star> * ?H * ?e \<le> ?H * (d * ?H)\<^sup>\<star> * ?e"
            by (metis assms(8) forest_components_star star.circ_decompose_9)
          hence "?H * d\<^sup>T * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
            using star_slide by auto
          hence "?H * d * (?H * d)\<^sup>\<star> * ?H * ?e \<squnion> ?H * d\<^sup>T * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
            by (smt le_supI star.circ_loop_fixpoint sup.cobounded2 sup_commute mult_assoc)
          hence "(?H * (d \<squnion> d\<^sup>T)) * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
            by (simp add: semiring.distrib_left semiring.distrib_right)
          hence "(?H * (d \<squnion> d\<^sup>T))\<^sup>\<star> * (?H * d)\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
            by (simp add: star_left_induct_mult mult_assoc)
          hence 252: "(?H * (d \<squnion> d\<^sup>T))\<^sup>\<star> * ?H * ?e \<le> (?H * d)\<^sup>\<star> * ?H * ?e"
            by (smt mult_left_dist_sup star.circ_transitive_equal star_slide star_sup_1 mult_assoc)
          have "?i \<le> top * ?e\<^sup>T * ?F"
            by auto
          hence "?i\<^sup>T \<le> ?F\<^sup>T * ?e\<^sup>T\<^sup>T * top\<^sup>T"
            by (simp add: conv_dist_comp conv_dist_inf mult_assoc)
          hence "?i\<^sup>T * top \<le> ?F\<^sup>T * ?e\<^sup>T\<^sup>T * top\<^sup>T * top"
            using comp_isotone by blast
          also have "... = ?F\<^sup>T * ?e\<^sup>T\<^sup>T * top\<^sup>T"
            by (simp add: vector_mult_closed)
          also have "... = ?F * ?e\<^sup>T\<^sup>T * top\<^sup>T"
            by (simp add: conv_dist_comp conv_star_commute)
          also have "... = ?F * ?e * top"
            by simp
          also have "... = (?H * (d \<squnion> d\<^sup>T))\<^sup>\<star> * ?H * ?e * top"
            by (simp add: assms(13))
          also have "... \<le> (?H * d)\<^sup>\<star> * ?H * ?e * top"
            by (simp add: 252 comp_isotone)
          also have "... \<le> (?H * (d \<squnion> ?e))\<^sup>\<star> * ?H * ?e * top"
            by (simp add: comp_isotone star_isotone)
          finally have "?i\<^sup>T * top \<le> (?H * (d \<squnion> ?e))\<^sup>\<star> * ?H * ?e * top"
            by blast
          thus ?thesis
            using 212 assms(18) bf_between_arcs_def minarc_arc minarc_bot_iff by blast
        qed
      next
        show "?i \<le> - ?H \<sqinter> -- g"
        proof -
          have 241: "?i \<le> -?H"
            using 16 assms(9) inf.order_lesseq_imp p_antitone_iff by blast
          have "?i \<le> -- g"
            using 10 inf.coboundedI1 spanning_forest_def by blast
          thus ?thesis
            using 241 inf_greatest by blast
        qed
      next
        show "regular h"
          using assms(20) by auto
      qed
      have "?v \<sqinter> ?e \<sqinter> -?i = bot"
        using 14 by simp
      hence "sum (?w \<sqinter> g) = sum (?v \<sqinter> -?i \<sqinter> g) + sum (?e \<sqinter> g)"
        using sum_disjoint inf_commute inf_assoc by simp
      also have "... \<le> sum (?v \<sqinter> -?i \<sqinter> g) + sum (?i \<sqinter> g)"
        using 224 225 sum_plus_right_isotone by simp
      also have "... = sum (((?v \<sqinter> -?i) \<squnion> ?i) \<sqinter> g)"
        using sum_disjoint inf_le2 pseudo_complement by simp
      also have "... = sum ((?v \<squnion> ?i) \<sqinter> (-?i \<squnion> ?i) \<sqinter> g)"
        by (simp add: sup_inf_distrib2)
      also have "... = sum ((?v \<squnion> ?i) \<sqinter> g)"
        using 15 by (metis inf_top_right stone)
      also have "... = sum (?v \<sqinter> g)"
        by (simp add: inf.sup_monoid.add_assoc)
      finally have "sum (?w \<sqinter> g) \<le> sum (?v \<sqinter> g)"
        by simp
      thus "\<forall>u . spanning_forest u g \<longrightarrow> sum (?w \<sqinter> g) \<le> sum (u \<sqinter> g)"
        using 2 11 minimum_spanning_forest_def by auto
    qed
  next
    have "?f \<le> f \<squnion> f\<^sup>T \<squnion> ?e"
      by (smt conv_dist_inf inf_le1 sup_left_isotone sup_mono inf.order_lesseq_imp)
    also have "... \<le> (?v \<sqinter> -?i \<sqinter> -?i\<^sup>T) \<squnion> (?v\<^sup>T \<sqinter> -?i \<sqinter> -?i\<^sup>T) \<squnion> ?e"
      using 20 sup_left_isotone by simp
    also have "... \<le> (?v \<sqinter> -?i) \<squnion> (?v\<^sup>T \<sqinter> -?i \<sqinter> -?i\<^sup>T) \<squnion> ?e"
      by (metis inf.cobounded1 sup_inf_distrib2)
    also have "... = ?w \<squnion> (?v\<^sup>T \<sqinter> -?i \<sqinter> -?i\<^sup>T)"
      by (simp add: sup_assoc sup_commute)
    also have "... \<le> ?w \<squnion> (?v\<^sup>T \<sqinter> -?i\<^sup>T)"
      using inf.sup_right_isotone inf_assoc sup_right_isotone by simp
    also have "... \<le> ?w \<squnion> ?w\<^sup>T"
      using conv_complement conv_dist_inf conv_dist_sup sup_right_isotone by simp
    finally show "?f \<le> ?w \<squnion> ?w\<^sup>T"
      by simp
  qed
  thus ?thesis by auto
qed

lemma boruvka_outer_invariant_when_e_not_bot:
  assumes "boruvka_inner_invariant j f h g d"
    and "j \<noteq> bot"
    and "selected_edge h j g \<le> - forest_components f"
    and "selected_edge h j g \<noteq> bot"
  shows "boruvka_outer_invariant (f \<sqinter> - selected_edge h j g\<^sup>T \<sqinter> - path f h j g \<squnion> (f \<sqinter> - selected_edge h j g\<^sup>T \<sqinter> path f h j g)\<^sup>T \<squnion> selected_edge h j g) g"
proof -
  let ?c = "choose_component (forest_components h) j"
  let ?p = "path f h j g"
  let ?F = "forest_components f"
  let ?H = "forest_components h"
  let ?e = "selected_edge h j g"
  let ?f' = "f \<sqinter> -?e\<^sup>T \<sqinter> -?p \<squnion> (f \<sqinter> -?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> ?e"
  let ?d' = "d \<squnion> ?e"
  let ?j' = "j \<sqinter> -?c"
  show "boruvka_outer_invariant ?f' g"
  proof (unfold boruvka_outer_invariant_def, intro conjI)
    show "symmetric g"
      by (meson assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def)
  next
    show "injective ?f'"
    proof (rule kruskal_injective_inv)
      show "injective (f \<sqinter> - ?e\<^sup>T)"
        by (meson assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def injective_inf_closed)
      show "covector (?p)"
        using covector_mult_closed by simp
      show "?p * (f \<sqinter> - ?e\<^sup>T)\<^sup>T \<le> ?p"
        by (simp add: mult_right_isotone star.left_plus_below_circ star_plus mult_assoc)
      show "?e \<le> ?p"
        by (meson mult_left_isotone order.trans star_outer_increasing top.extremum)
      show "?p * (f \<sqinter> - ?e\<^sup>T)\<^sup>T \<le> - ?e"
      proof -
        have "?p * (f \<sqinter> - ?e\<^sup>T)\<^sup>T \<le> ?p * f\<^sup>T"
          by (simp add: conv_dist_inf mult_right_isotone)
        also have "... \<le> top * ?e * (f)\<^sup>T\<^sup>\<star> * f\<^sup>T"
          using conv_dist_inf star_isotone comp_isotone by simp
        also have "... \<le> - ?e"
          using assms(1, 4) boruvka_inner_invariant_def boruvka_outer_invariant_def kruskal_injective_inv_2 minarc_arc minarc_bot_iff by auto
        finally show ?thesis .
      qed
      show "injective (?e)"
        by (metis arc_injective coreflexive_bot_closed minarc_arc minarc_bot_iff semiring.mult_not_zero)
      show "coreflexive (?p\<^sup>T * ?p \<sqinter> (f \<sqinter> - ?e\<^sup>T)\<^sup>T * (f \<sqinter> - ?e\<^sup>T))"
      proof -
        have "(?p\<^sup>T * ?p \<sqinter> (f \<sqinter> - ?e\<^sup>T)\<^sup>T * (f \<sqinter> - ?e\<^sup>T)) \<le> ?p\<^sup>T * ?p \<sqinter> f\<^sup>T * f"
          using conv_dist_inf inf.sup_right_isotone mult_isotone by simp
        also have "... \<le> (top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T * (top * ?e * f\<^sup>T\<^sup>\<star>) \<sqinter> f\<^sup>T * f"
          by (metis comp_associative comp_inf.coreflexive_transitive comp_inf.mult_right_isotone comp_isotone conv_isotone inf.cobounded1 inf.idem inf.sup_monoid.add_commute star_isotone top.extremum)
        also have "... \<le> 1"
          using assms(1, 4) boruvka_inner_invariant_def boruvka_outer_invariant_def kruskal_injective_inv_3 minarc_arc minarc_bot_iff by auto
        finally show ?thesis
          by simp
      qed
    qed
  next
    show "acyclic ?f'"
    proof (rule kruskal_acyclic_inv)
      show "acyclic (f \<sqinter> - ?e\<^sup>T)"
      proof -
        have f_intersect_below: "(f \<sqinter> - ?e\<^sup>T) \<le> f" by simp
        have "acyclic f"
          by (meson assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def)
        thus ?thesis
          using comp_isotone dual_order.trans star_isotone f_intersect_below by blast
      qed
    next
      show "covector ?p"
        by (metis comp_associative vector_top_closed)
    next
      show "(f \<sqinter> - ?e\<^sup>T \<sqinter> ?p)\<^sup>T * (f \<sqinter> - ?e\<^sup>T)\<^sup>\<star> * ?e = bot"
      proof -
        have "?e \<le> - (f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>)"
          by (simp add: assms(3))
        hence "?e * top * ?e \<le> - (f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>)"
          by (metis arc_top_arc minarc_arc minarc_bot_iff semiring.mult_not_zero)
        hence "?e\<^sup>T * top * ?e\<^sup>T \<le> - (f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>)\<^sup>T"
          by (metis comp_associative conv_complement conv_dist_comp conv_isotone symmetric_top_closed)
        hence "?e\<^sup>T * top * ?e\<^sup>T \<le> - (f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>)"
          by (simp add: conv_dist_comp conv_star_commute)
        hence "?e * (f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>) * ?e \<le> bot"
          using triple_schroeder_p by auto
        hence 1: "?e * f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> * ?e \<le> bot"
          using mult_assoc by auto
        have 2: "(f \<sqinter> - ?e\<^sup>T)\<^sup>T\<^sup>\<star> \<le> f\<^sup>T\<^sup>\<star>"
          by (simp add: conv_dist_inf star_isotone)
        have "(f \<sqinter> - ?e\<^sup>T \<sqinter> ?p)\<^sup>T * (f \<sqinter> - ?e\<^sup>T)\<^sup>\<star> * ?e \<le> (f \<sqinter> ?p)\<^sup>T * (f \<sqinter> - ?e\<^sup>T)\<^sup>\<star> * ?e"
          by (simp add: comp_isotone conv_dist_inf inf.orderI inf.sup_monoid.add_assoc)
        also have "... \<le> (f \<sqinter> ?p)\<^sup>T * f\<^sup>\<star> * ?e"
          by (simp add: comp_isotone star_isotone)
        also have "... \<le> (f \<sqinter> top * ?e * (f)\<^sup>T\<^sup>\<star>)\<^sup>T * f\<^sup>\<star> * ?e"
          using 2 by (metis comp_inf.comp_isotone comp_inf.coreflexive_transitive comp_isotone conv_isotone inf.idem top.extremum)
        also have "... = (f\<^sup>T \<sqinter> (top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T) * f\<^sup>\<star> * ?e"
          by (simp add: conv_dist_inf)
        also have "... \<le> top * (f\<^sup>T \<sqinter> (top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T) * f\<^sup>\<star> * ?e"
          using top_left_mult_increasing mult_assoc by auto
        also have "... = (top \<sqinter> top * ?e * f\<^sup>T\<^sup>\<star>) * f\<^sup>T * f\<^sup>\<star> * ?e"
          by (smt covector_comp_inf_1 covector_mult_closed eq_iff inf.sup_monoid.add_commute vector_top_closed)
        also have "... = top * ?e * f\<^sup>T\<^sup>\<star> * f\<^sup>T * f\<^sup>\<star> * ?e"
          by simp
        also have "... \<le> top * ?e * f\<^sup>T\<^sup>\<star> * f\<^sup>\<star> * ?e"
          by (smt conv_dist_comp conv_isotone conv_star_commute mult_left_isotone mult_right_isotone star.left_plus_below_circ mult_assoc)
        also have "... \<le> bot"
          using 1 covector_bot_closed le_bot mult_assoc by fastforce
        finally show ?thesis
          using le_bot by auto
      qed
    next
      show "?e * (f \<sqinter> - ?e\<^sup>T)\<^sup>\<star> * ?e = bot"
      proof -
        have 1: "?e \<le> - ?F"
          by (simp add: assms(3))
        have 2: "injective f"
          by (meson assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def)
        have 3: "equivalence ?F"
          using 2 forest_components_equivalence by simp
        hence 4: "?e\<^sup>T = ?e\<^sup>T * top * ?e\<^sup>T"
          by (smt arc_conv_closed arc_top_arc covector_complement_closed covector_conv_vector ex231e minarc_arc minarc_bot_iff pp_surjective regular_closed_top vector_mult_closed vector_top_closed)
        also have "... \<le> - ?F" using 1 3 conv_isotone conv_complement calculation by fastforce
        finally have 5: "?e * ?F * ?e = bot"
          using 4 by (smt triple_schroeder_p le_bot pp_total regular_closed_top vector_top_closed)
        have "(f \<sqinter> - ?e\<^sup>T)\<^sup>\<star> \<le> f\<^sup>\<star>"
          by (simp add: star_isotone)
        hence "?e * (f \<sqinter> - ?e\<^sup>T)\<^sup>\<star> * ?e \<le> ?e * f\<^sup>\<star> * ?e"
          using mult_left_isotone mult_right_isotone by blast
        also have "... \<le> ?e * ?F * ?e"
          by (metis conv_star_commute forest_components_increasing mult_left_isotone mult_right_isotone star_involutive)
        also have 6: "... = bot"
          using 5 by simp
        finally show ?thesis using 6 le_bot by blast
      qed
    next
      show "forest_components (f \<sqinter> -?e\<^sup>T) \<le> - ?e"
      proof -
        have 1: "?e \<le> - ?F"
          by (simp add: assms(3))
        have "f \<sqinter> - ?e\<^sup>T \<le> f"
          by simp
        hence "forest_components (f \<sqinter> - ?e\<^sup>T) \<le> ?F"
          using forest_components_isotone by blast
        thus ?thesis
          using 1 order_lesseq_imp p_antitone_iff by blast
      qed
    qed
  next
    show "?f' \<le> --g"
    proof -
      have 1: "(f \<sqinter> - ?e\<^sup>T \<sqinter> - ?p) \<le> --g"
        by (meson assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def inf.coboundedI1)
      have 2: "(f \<sqinter> - ?e\<^sup>T \<sqinter> ?p)\<^sup>T \<le> --g"
      proof -
        have "(f \<sqinter> - ?e\<^sup>T \<sqinter> ?p)\<^sup>T \<le> f\<^sup>T"
          by (simp add: conv_isotone inf.sup_monoid.add_assoc)
        also have "... \<le> --g"
          by (metis assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def conv_complement conv_isotone)
        finally show ?thesis
          by simp
      qed
      have 3: "?e \<le> --g"
        by (metis inf.boundedE minarc_below pp_dist_inf)
      show ?thesis using 1 2 3
        by simp
    qed
  next
    show "regular ?f'"
      using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def minarc_regular regular_closed_star regular_conv_closed regular_mult_closed by auto
  next
    show "\<exists>w. minimum_spanning_forest w g \<and> ?f' \<le> w \<squnion> w\<^sup>T"
    proof (rule exists_a_w)
      show "symmetric g"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
    next
      show "forest f"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
    next
      show "f \<le> --g"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
    next
      show "regular f"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
    next
      show "(\<exists>w . minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T)"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
    next
      show "vector j"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "regular j"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "forest h"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "forest_components h \<le> forest_components f"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "big_forest (forest_components h) d"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "d * top \<le> - j"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "forest_components h * j = j"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "forest_components f = (forest_components h * (d \<squnion> d\<^sup>T))\<^sup>\<star> * forest_components h"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "(\<forall> a b . bf_between_arcs a b (forest_components h) d \<and> a \<le> -(forest_components h) \<sqinter> -- g \<and> b \<le> d \<longrightarrow> sum(b \<sqinter> g) \<le> sum(a \<sqinter> g))"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "regular d"
        using assms(1) boruvka_inner_invariant_def by blast
    next
      show "selected_edge h j g \<le> - forest_components f"
        by (simp add: assms(3))
    next
      show "selected_edge h j g \<noteq> bot"
        by (simp add: assms(4))
    next
      show "j \<noteq> bot"
        by (simp add: assms(2))
    next
      show "regular h"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
    next
      show "h \<le> --g"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
    qed
  qed
qed

lemma second_inner_invariant_when_e_not_bot:
  assumes "boruvka_inner_invariant j f h g d"
    and "j \<noteq> bot"
    and "selected_edge h j g \<le> - forest_components f"
    and "selected_edge h j g \<noteq> bot"
  shows "boruvka_inner_invariant
         (j \<sqinter> - choose_component (forest_components h) j)
         (f \<sqinter> - selected_edge h j g\<^sup>T \<sqinter> - path f h j g \<squnion>
          (f \<sqinter> - selected_edge h j g\<^sup>T \<sqinter> path f h j g)\<^sup>T \<squnion>
          selected_edge h j g)
         h g (d \<squnion> selected_edge h j g)"
proof -
  let ?c = "choose_component (forest_components h) j"
  let ?p = "path f h j g"
  let ?F = "forest_components f"
  let ?H = "forest_components h"
  let ?e = "selected_edge h j g"
  let ?f' = "f \<sqinter> -?e\<^sup>T \<sqinter> -?p \<squnion> (f \<sqinter> -?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> ?e"
  let ?d' = "d \<squnion> ?e"
  let ?j' = "j \<sqinter> -?c"
  show "boruvka_inner_invariant ?j' ?f' h g ?d'"
  proof (unfold boruvka_inner_invariant_def, intro conjI)
    have 1: "boruvka_outer_invariant ?f' g"
      using assms(1, 2, 3, 4) boruvka_outer_invariant_when_e_not_bot by blast
    show "boruvka_outer_invariant ?f' g"
      using assms(1, 2, 3, 4) boruvka_outer_invariant_when_e_not_bot by blast
    show "g \<noteq> bot"
      using assms(1) boruvka_inner_invariant_def by force
    show "vector ?j'"
      using assms(1, 2) boruvka_inner_invariant_def component_is_vector vector_complement_closed vector_inf_closed by simp
    show "regular ?j'"
      using assms(1) boruvka_inner_invariant_def by auto
    show "boruvka_outer_invariant h g"
      by (meson assms(1) boruvka_inner_invariant_def)
    show "injective h"
      by (meson assms(1) boruvka_inner_invariant_def)
    show "pd_kleene_allegory_class.acyclic h"
      by (meson assms(1) boruvka_inner_invariant_def)
    show "?H \<le> forest_components ?f'"
    proof -
      have 2: "?F \<le> forest_components ?f'"
      proof (rule components_disj_increasing)
        show "regular ?p"
          using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def minarc_regular regular_closed_star regular_conv_closed regular_mult_closed by auto[1]
      next
        show "regular ?e"
          using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def minarc_regular regular_closed_star regular_conv_closed regular_mult_closed by auto[1]
      next
        show "injective ?f'"
          using 1 boruvka_outer_invariant_def by blast
      next
        show "injective f"
          using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by blast
      qed
      thus ?thesis
        using assms(1) boruvka_inner_invariant_def dual_order.trans by blast
    qed
    show "big_forest ?H ?d'"
      using assms(1, 2, 3, 4) big_forest_d_U_e boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
  next
    show "?d' * top \<le> -?j'"
    proof -
      have 31: "?d' * top = d * top \<squnion> ?e * top"
        by (simp add: mult_right_dist_sup)
      have 32: "d * top \<le> -?j'"
        by (meson assms(1) boruvka_inner_invariant_def inf.coboundedI1 p_antitone_iff)
      have "regular (?c * - ?c\<^sup>T)"
        using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def component_is_regular regular_conv_closed regular_mult_closed by auto
      hence "minarc(?c * - ?c\<^sup>T \<sqinter> g) = minarc(?c \<sqinter> - ?c\<^sup>T \<sqinter> g)"
        by (metis component_is_vector covector_comp_inf inf_top.left_neutral vector_conv_compl)
      also have "... \<le> -- (?c \<sqinter> - ?c\<^sup>T \<sqinter> g)"
        using minarc_below by blast
      also have "... \<le> -- ?c"
        by (simp add: inf.sup_monoid.add_assoc)
      also have "... = ?c"
        using component_is_regular by auto
      finally have "?e \<le> ?c"
        by simp
      hence "?e * top \<le> ?c"
        by (metis component_is_vector mult_left_isotone)
      also have "... \<le> -j \<squnion> ?c"
        by simp
      also have "... = - (j \<sqinter> - ?c)"
        using component_is_regular by auto
      finally have 33: "?e * top \<le> - (j \<sqinter> - ?c)"
        by simp
      show ?thesis
        using 31 32 33 by auto
    qed
  next
    show "?H * ?j' = ?j'"
      using fc_j_eq_j_inv assms(1) boruvka_inner_invariant_def by blast
  next
    show "forest_components ?f' = (?H * (?d' \<squnion> ?d'\<^sup>T))\<^sup>\<star> * ?H"
    proof -
      have "forest_components ?f' = (f \<squnion> f\<^sup>T \<squnion> ?e \<squnion> ?e\<^sup>T)\<^sup>\<star>"
      proof (rule simplify_forest_components_f)
        show "regular ?p"
          using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def minarc_regular regular_closed_star regular_conv_closed regular_mult_closed by auto
      next
        show "regular ?e"
          using minarc_regular by auto
      next
        show "injective ?f'"
          using assms(1, 2, 3, 4) boruvka_outer_invariant_def boruvka_outer_invariant_when_e_not_bot by blast
      next
        show "injective f"
          using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by blast
      qed
      also have "... = (h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T \<squnion> ?e \<squnion> ?e\<^sup>T)\<^sup>\<star>"
        using assms(1) boruvka_inner_invariant_def by simp
      also have "... = (h \<squnion> h\<^sup>T \<squnion> ?d' \<squnion> ?d'\<^sup>T)\<^sup>\<star>"
        by (smt conv_dist_sup sup_monoid.add_assoc sup_monoid.add_commute)
      also have "... = ((h \<squnion> h\<^sup>T)\<^sup>\<star> * (?d' \<squnion> ?d'\<^sup>T))\<^sup>\<star> * (h \<squnion> h\<^sup>T)\<^sup>\<star>"
        by (metis star.circ_sup_9 sup_assoc)
      finally show ?thesis
        using assms(1) boruvka_inner_invariant_def forest_components_wcc by simp
    qed
  next
    show "?f' \<squnion> ?f'\<^sup>T = h \<squnion> h\<^sup>T \<squnion> ?d' \<squnion> ?d'\<^sup>T"
    proof -
      have "?f' \<squnion> ?f'\<^sup>T = f \<sqinter> - ?e\<^sup>T \<sqinter> - ?p \<squnion> (f \<sqinter> - ?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> ?e \<squnion> (f \<sqinter> - ?e\<^sup>T \<sqinter> - ?p)\<^sup>T \<squnion> (f \<sqinter> - ?e\<^sup>T \<sqinter> ?p) \<squnion> ?e\<^sup>T"
        by (simp add: conv_dist_sup sup_monoid.add_assoc)
      also have "... = (f \<sqinter> - ?e\<^sup>T \<sqinter> - ?p) \<squnion> (f \<sqinter> - ?e\<^sup>T \<sqinter> ?p) \<squnion> (f \<sqinter> - ?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> (f \<sqinter> - ?e\<^sup>T \<sqinter> - ?p)\<^sup>T \<squnion> ?e\<^sup>T \<squnion> ?e"
        by (simp add: sup.left_commute sup_commute)
      also have "... = f \<squnion> f\<^sup>T \<squnion> ?e \<squnion> ?e\<^sup>T"
      proof (rule simplify_f)
        show "regular ?p"
          using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def minarc_regular regular_closed_star regular_conv_closed regular_mult_closed by auto
      next
        show "regular ?e"
          using minarc_regular by blast
      qed
      also have "... = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T \<squnion> ?e \<squnion> ?e\<^sup>T"
        using assms(1) boruvka_inner_invariant_def by auto
      finally show ?thesis
        by (smt conv_dist_sup sup.left_commute sup_commute)
    qed
  next
    show "\<forall> a b . bf_between_arcs a b ?H ?d' \<and> a \<le> - ?H \<sqinter> -- g \<and> b \<le> ?d' \<longrightarrow> sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
    proof (intro allI, rule impI, unfold bf_between_arcs_def)
      fix a b
      assume 1: "(arc a \<and> arc b \<and> a\<^sup>T * top \<le> (?H * ?d')\<^sup>\<star> * ?H * b * top) \<and> a \<le> - ?H \<sqinter> -- g \<and> b \<le> ?d'"
      thus "sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
      proof (cases "b = ?e")
        case b_equals_e: True
        thus ?thesis
        proof (cases "a = ?e")
          case True
          thus ?thesis
            using b_equals_e by auto
        next
          case a_ne_e: False
          have "sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
          proof (rule a_to_e_in_bigforest)
            show "symmetric g"
              using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
          next
            show "j \<noteq> bot"
              by (simp add: assms(2))
          next
            show "f \<le> -- g"
              using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
          next
            show "vector j"
              using assms(1) boruvka_inner_invariant_def by blast
          next
            show "forest h"
              using assms(1) boruvka_inner_invariant_def by blast
          next
            show " big_forest (forest_components h) d"
              using assms(1) boruvka_inner_invariant_def by blast
          next
            show "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
              using assms(1) boruvka_inner_invariant_def by blast
          next
            show "\<forall>a b. bf_between_arcs a b (?H) d \<and> a \<le> - ?H \<sqinter> - - g \<and> b \<le> d \<longrightarrow> sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
              using assms(1) boruvka_inner_invariant_def by blast
          next
            show "regular d"
              using assms(1) boruvka_inner_invariant_def by blast
          next
            show "b = ?e"
              using b_equals_e by simp
          next
            show "arc a"
              using 1 by simp
          next
            show "bf_between_arcs a b ?H ?d'"
              using 1 bf_between_arcs_def by simp
          next
            show "a \<le> - ?H \<sqinter> -- g"
              using 1 by simp
          next
            show "regular h"
              using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
          qed
          thus ?thesis
            by simp
        qed
      next
        case b_not_equal_e: False
        hence b_below_d: "b \<le> d"
          using 1 by (metis assms(4) different_arc_in_sup_arc minarc_arc minarc_bot_iff)
        thus ?thesis
        proof (cases "?e \<le> d")
          case True
          hence "bf_between_arcs a b ?H d \<and> b \<le> d"
            using 1 bf_between_arcs_def sup.absorb1 by auto
          thus ?thesis
            using 1 assms(1) boruvka_inner_invariant_def by blast
        next
          case e_not_less_than_d: False
          have 71:"equivalence ?H"
            using assms(1) fch_equivalence boruvka_inner_invariant_def by auto
          hence 72: "bf_between_arcs a b ?H ?d' \<longleftrightarrow> bf_between_arcs a b ?H d \<or> (bf_between_arcs a ?e ?H d \<and> bf_between_arcs ?e b ?H d)"
          proof (rule big_forest_path_split_disj)
            show "arc ?e"
              using assms(4) minarc_arc minarc_bot_iff by blast
          next
            show "regular a \<and> regular b \<and> regular ?e \<and> regular d \<and> regular ?H"
              using assms(1) 1 boruvka_inner_invariant_def boruvka_outer_invariant_def arc_regular minarc_regular regular_closed_star regular_conv_closed regular_mult_closed by auto
          qed
          thus ?thesis
          proof (cases "bf_between_arcs a b ?H d")
            case True
            have "bf_between_arcs a b ?H d \<and> b \<le> d"
              using 1 by (metis assms(4) True b_not_equal_e minarc_arc minarc_bot_iff different_arc_in_sup_arc)
            thus ?thesis
              using 1 assms(1) b_below_d boruvka_inner_invariant_def by auto
          next
            case False
            have 73:"bf_between_arcs a ?e ?H d \<and> bf_between_arcs ?e b ?H d"
              using 1 72 False bf_between_arcs_def by blast
            have 74: "?e \<le> --g"
              by (metis inf.boundedE minarc_below pp_dist_inf)
            have "?e \<le> - ?H"
              by (meson assms(1, 3) boruvka_inner_invariant_def dual_order.trans p_antitone_iff)
            hence "?e \<le> - ?H \<sqinter> --g"
              using 74 by simp
            hence 75: "sum (b \<sqinter> g) \<le> sum (?e \<sqinter> g)"
              using assms(1) b_below_d 73 boruvka_inner_invariant_def by blast
            have 76: "bf_between_arcs a ?e ?H ?d'"
              using 73 by (meson big_forest_path_split_disj assms(1) bf_between_arcs_def boruvka_inner_invariant_def boruvka_outer_invariant_def fch_equivalence arc_regular regular_closed_star regular_conv_closed regular_mult_closed)
            have 77: "sum (?e \<sqinter> g) \<le> sum (a \<sqinter> g)"
            proof (rule a_to_e_in_bigforest)
              show "symmetric g"
                using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
            next
              show "j \<noteq> bot"
                by (simp add: assms(2))
            next
              show "f \<le> -- g"
                using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
            next
              show "vector j"
                using assms(1) boruvka_inner_invariant_def by blast
            next
              show "forest h"
                using assms(1) boruvka_inner_invariant_def by blast
            next
              show " big_forest (forest_components h) d"
                using assms(1) boruvka_inner_invariant_def by blast
            next
              show "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
                using assms(1) boruvka_inner_invariant_def by blast
            next
              show "\<forall>a b. bf_between_arcs a b (?H) d \<and> a \<le> - ?H \<sqinter> - - g \<and> b \<le> d \<longrightarrow> sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
                using assms(1) boruvka_inner_invariant_def by blast
            next
              show "regular d"
                using assms(1) boruvka_inner_invariant_def by blast
            next
              show "?e = ?e"
                by simp
            next
              show "arc a"
                using 1 by simp
            next
              show "bf_between_arcs a ?e ?H ?d'"
                by (simp add: 76)
            next
              show "a \<le> - ?H \<sqinter> --g"
                using 1 by simp
            next
              show "regular h"
                using assms(1) boruvka_inner_invariant_def boruvka_outer_invariant_def by auto
            qed
            thus ?thesis
              using 75 order.trans by blast
          qed
        qed
      qed
    qed
  next
    show "regular ?d'"
      using assms(1) boruvka_inner_invariant_def minarc_regular by auto
  qed
qed

lemma second_inner_invariant_when_e_bot:
  assumes "selected_edge h j g = bot"
    and "selected_edge h j g \<le> - forest_components f"
    and "boruvka_inner_invariant j f h g d"
  shows "boruvka_inner_invariant
     (j \<sqinter> - choose_component (forest_components h) j)
     (f \<sqinter> - selected_edge h j g\<^sup>T \<sqinter> - path f h j g \<squnion>
      (f \<sqinter> - selected_edge h j g\<^sup>T \<sqinter> path f h j g)\<^sup>T \<squnion>
      selected_edge h j g)
     h g (d \<squnion> selected_edge h j g)"
proof -
  let ?c = "choose_component (forest_components h) j"
  let ?p = "path f h j g"
  let ?F = "forest_components f"
  let ?H = "forest_components h"
  let ?e = "selected_edge h j g"
  let ?f' = "f \<sqinter> -?e\<^sup>T \<sqinter> -?p \<squnion> (f \<sqinter> -?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> ?e"
  let ?d' = "d \<squnion> ?e"
  let ?j' = "j \<sqinter> -?c"
  show "boruvka_inner_invariant ?j' ?f' h g ?d'"
  proof (unfold boruvka_inner_invariant_def, intro conjI)
  next
    show "boruvka_outer_invariant ?f' g"
      using assms(1, 3) boruvka_inner_invariant_def by auto
  next
    show "g \<noteq> bot"
      using assms(3) boruvka_inner_invariant_def by blast
  next
    show "vector ?j'"
      by (metis assms(3) boruvka_inner_invariant_def component_is_vector vector_complement_closed vector_inf_closed)
  next
    show "regular ?j'"
      using assms(3) boruvka_inner_invariant_def by auto
  next
    show "boruvka_outer_invariant h g"
      using assms(3) boruvka_inner_invariant_def by blast
  next
    show "injective h"
      using assms(3) boruvka_inner_invariant_def by blast
  next
    show "pd_kleene_allegory_class.acyclic h"
      using assms(3) boruvka_inner_invariant_def by blast
  next
    show "?H \<le> forest_components ?f'"
      using assms(1, 3) boruvka_inner_invariant_def by auto
  next
    show " big_forest ?H ?d'"
      using assms(1, 3) boruvka_inner_invariant_def by auto
  next
    show "?d' * top \<le> -?j'"
      by (metis assms(1, 3) boruvka_inner_invariant_def order.trans p_antitone_inf sup_monoid.add_0_right)
  next
    show "?H * ?j' = ?j'"
      using assms(3) fc_j_eq_j_inv boruvka_inner_invariant_def by blast
  next
    show "forest_components ?f' = (?H * (?d' \<squnion> ?d'\<^sup>T))\<^sup>\<star> *?H"
      using assms(1, 3) boruvka_inner_invariant_def by auto
  next
    show "?f' \<squnion> ?f'\<^sup>T = h \<squnion> h\<^sup>T \<squnion> ?d' \<squnion> ?d'\<^sup>T"
      using assms(1, 3) boruvka_inner_invariant_def by auto
  next
    show "\<forall>a b. bf_between_arcs a b ?H ?d' \<and> a \<le> -?H \<sqinter> --g \<and> b \<le> ?d' \<longrightarrow> sum(b \<sqinter> g) \<le> sum(a \<sqinter> g)"
      using assms(1, 3) boruvka_inner_invariant_def by auto
  next
    show "regular ?d'"
      using assms(1, 3) boruvka_inner_invariant_def by auto
  qed
qed

subsection \<open>Formalization and correctness proof\<close>

text \<open>
The following result shows that Bor\r{u}vka's algorithm constructs a minimum spanning forest.
We have the same postcondition as the proof of Kruskal's minimum spanning tree algorithm.
We show only partial correctness.
\<close>

theorem boruvka_mst:
  "VARS f j h c e d
  { symmetric g }
  f := bot;
  WHILE -(forest_components f) \<sqinter> g \<noteq> bot
    INV { boruvka_outer_invariant f g }
    DO
      j := top;
      h := f;
      d := bot;
      WHILE j \<noteq> bot
        INV { boruvka_inner_invariant j f h g d }
        DO
          c := choose_component (forest_components h) j;
          e := minarc(c * -c\<^sup>T \<sqinter> g);
          IF e \<le> -(forest_components f) THEN
            f := f \<sqinter> -e\<^sup>T;
            f := (f \<sqinter> -(top * e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> e;
            d := d \<squnion> e
          ELSE
            SKIP
          FI;
          j := j \<sqinter> -c
        OD
    OD
  { minimum_spanning_forest f g }"
proof vcg_simp
  assume 1: "symmetric g"
  show "boruvka_outer_invariant bot g"
    using 1 boruvka_outer_invariant_def kruskal_exists_minimal_spanning by auto
next
  fix f
  let ?F = "forest_components f"
  assume 1: "boruvka_outer_invariant f g \<and> - ?F \<sqinter> g \<noteq> bot"
  have 2: "equivalence ?F"
    using 1 boruvka_outer_invariant_def forest_components_equivalence by auto
  show "boruvka_inner_invariant top f f g bot"
  proof (unfold boruvka_inner_invariant_def, intro conjI)
    show "boruvka_outer_invariant f g"
      by (simp add: 1)
  next
    show "g \<noteq> bot"
      using 1 by auto
  next
    show "surjective top"
      by simp
  next
    show "regular top"
      by simp
  next
    show "boruvka_outer_invariant f g"
      using 1 by auto
  next
    show "injective f"
      using 1 boruvka_outer_invariant_def by blast
  next
    show "pd_kleene_allegory_class.acyclic f"
      using 1 boruvka_outer_invariant_def by blast
  next
    show "?F \<le> ?F"
      by simp
  next
    show "big_forest ?F bot"
      by (simp add: 2 big_forest_def)
  next
    show "bot * top \<le> - top"
      by simp
  next
    show "times_top_class.total (?F)"
      by (simp add: star.circ_right_top mult_assoc)
  next
    show "?F = (?F * (bot \<squnion> bot\<^sup>T))\<^sup>\<star> * ?F"
      by (metis mult_right_zero semiring.mult_zero_left star.circ_loop_fixpoint sup_commute sup_monoid.add_0_right symmetric_bot_closed)
  next
    show "f \<squnion> f\<^sup>T = f \<squnion> f\<^sup>T \<squnion> bot \<squnion> bot\<^sup>T"
      by simp
  next
    show "\<forall> a b. bf_between_arcs a b ?F bot \<and> a \<le> - ?F \<sqinter> -- g \<and> b \<le> bot \<longrightarrow> sum (b \<sqinter> g) \<le> sum (a \<sqinter> g)"
      by (metis (full_types) bf_between_arcs_def bot_unique mult_left_zero mult_right_zero top.extremum)
  next
    show "regular bot"
      by auto
  qed
next
  fix f j h d
  let ?c = "choose_component (forest_components h) j"
  let ?p = "path f h j g"
  let ?F = "forest_components f"
  let ?H = "forest_components h"
  let ?e = "selected_edge h j g"
  let ?f' = "f \<sqinter> -?e\<^sup>T \<sqinter> -?p \<squnion> (f \<sqinter> -?e\<^sup>T \<sqinter> ?p)\<^sup>T \<squnion> ?e"
  let ?d' = "d \<squnion> ?e"
  let ?j' = "j \<sqinter> -?c"
  assume 1: "boruvka_inner_invariant j f h g d \<and> j \<noteq> bot"
  show "(?e \<le> -?F \<longrightarrow> boruvka_inner_invariant ?j' ?f' h g ?d') \<and> (\<not> ?e \<le> -?F \<longrightarrow> boruvka_inner_invariant ?j' f h g d)"
  proof (intro conjI)
    show "?e \<le> -?F \<longrightarrow> boruvka_inner_invariant ?j' ?f' h g ?d'"
    proof (cases "?e = bot")
      case True
      thus ?thesis
        using 1 second_inner_invariant_when_e_bot by simp
    next
      case False
      thus ?thesis
        using 1 second_inner_invariant_when_e_not_bot by simp
    qed
  next
    show "\<not> ?e \<le> -?F \<longrightarrow> boruvka_inner_invariant ?j' f h g d"
    proof (rule impI, unfold boruvka_inner_invariant_def, intro conjI)
      show "boruvka_outer_invariant f g"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "g \<noteq> bot"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "vector ?j'"
        using 1 boruvka_inner_invariant_def component_is_vector vector_complement_closed vector_inf_closed by auto
    next
      show "regular ?j'"
        using 1 boruvka_inner_invariant_def by auto
    next
      show "boruvka_outer_invariant h g"
        using 1 boruvka_inner_invariant_def by auto
    next
      show "injective h"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "pd_kleene_allegory_class.acyclic h"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "?H \<le> ?F"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "big_forest ?H d"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "d * top \<le> -?j'"
        using 1 by (meson boruvka_inner_invariant_def dual_order.trans p_antitone_inf)
    next
      show "?H * ?j' = ?j'"
        using 1 fc_j_eq_j_inv boruvka_inner_invariant_def by blast
    next
      show "?F = (?H * (d \<squnion> d\<^sup>T))\<^sup>\<star> * ?H"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "f \<squnion> f\<^sup>T = h \<squnion> h\<^sup>T \<squnion> d \<squnion> d\<^sup>T"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "\<not> ?e \<le> -?F \<Longrightarrow> \<forall>a b. bf_between_arcs a b ?H d \<and> a \<le> -?H \<sqinter> --g \<and> b \<le> d \<longrightarrow> sum(b \<sqinter> g) \<le> sum(a \<sqinter> g)"
        using 1 boruvka_inner_invariant_def by blast
    next
      show "\<not> ?e \<le> -?F \<Longrightarrow> regular d"
        using 1 boruvka_inner_invariant_def by blast
    qed
  qed
next
  fix f h d
  assume "boruvka_inner_invariant bot f h g d"
  thus "boruvka_outer_invariant f g"
    by (meson boruvka_inner_invariant_def)
next
  fix f
  assume 1: "boruvka_outer_invariant f g \<and> - forest_components f \<sqinter> g = bot"
  hence 2:"spanning_forest f g"
  proof (unfold spanning_forest_def, intro conjI)
    show "injective f"
      using 1 boruvka_outer_invariant_def by blast
  next
    show "acyclic f"
      using 1 boruvka_outer_invariant_def by blast
  next
    show "f \<le> --g"
      using 1 boruvka_outer_invariant_def by blast
  next
    show "components g \<le> forest_components f"
    proof -
      let ?F = "forest_components f"
      have "-?F \<sqinter> g \<le> bot"
        by (simp add: 1)
      hence "--g \<le> bot \<squnion> --?F"
        using 1 shunting_p p_antitone pseudo_complement by auto
      hence "--g \<le> ?F"
        using 1 boruvka_outer_invariant_def pp_dist_comp pp_dist_star regular_conv_closed by auto
      hence "(--g)\<^sup>\<star> \<le> ?F\<^sup>\<star>"
        by (simp add: star_isotone)
      thus ?thesis
        using 1 boruvka_outer_invariant_def forest_components_star by auto
    qed
  next
    show "regular f"
      using 1 boruvka_outer_invariant_def by auto
  qed
  from 1 obtain w where 3: "minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T"
    using boruvka_outer_invariant_def by blast
  hence "w = w \<sqinter> --g"
    by (simp add: inf.absorb1 minimum_spanning_forest_def spanning_forest_def)
  also have "... \<le> w \<sqinter> components g"
    by (metis inf.sup_right_isotone star.circ_increasing)
  also have "... \<le> w \<sqinter> f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>"
    using 2 spanning_forest_def inf.sup_right_isotone by simp
  also have "... \<le> f \<squnion> f\<^sup>T"
  proof (rule cancel_separate_6[where z=w and y="w\<^sup>T"])
    show "injective w"
      using 3 minimum_spanning_forest_def spanning_forest_def by simp
  next
    show "f\<^sup>T \<le> w\<^sup>T \<squnion> w"
      using 3 by (metis conv_dist_inf conv_dist_sup conv_involutive inf.cobounded2 inf.orderE)
  next
    show "f \<le> w\<^sup>T \<squnion> w"
      using 3 by (simp add: sup_commute)
  next
    show "injective w"
      using 3 minimum_spanning_forest_def spanning_forest_def by simp
  next
    show "w \<sqinter> w\<^sup>T\<^sup>\<star> = bot"
      using 3 by (metis acyclic_star_below_complement comp_inf.mult_right_isotone inf_p le_bot minimum_spanning_forest_def spanning_forest_def)
  qed
  finally have 4: "w \<le> f \<squnion> f\<^sup>T"
    by simp
  have "sum (f \<sqinter> g) = sum ((w \<squnion> w\<^sup>T) \<sqinter> (f \<sqinter> g))"
    using 3 by (metis inf_absorb2 inf.assoc)
  also have "... = sum (w \<sqinter> (f \<sqinter> g)) + sum (w\<^sup>T \<sqinter> (f \<sqinter> g))"
    using 3 inf.commute acyclic_asymmetric sum_disjoint minimum_spanning_forest_def spanning_forest_def by simp
  also have "... = sum (w \<sqinter> (f \<sqinter> g)) + sum (w \<sqinter> (f\<^sup>T \<sqinter> g\<^sup>T))"
    by (metis conv_dist_inf conv_involutive sum_conv)
  also have "... = sum (f \<sqinter> (w \<sqinter> g)) + sum (f\<^sup>T \<sqinter> (w \<sqinter> g))"
  proof -
    have 51:"f\<^sup>T \<sqinter> (w \<sqinter> g) = f\<^sup>T \<sqinter> (w \<sqinter> g\<^sup>T)"
      using 1 boruvka_outer_invariant_def by auto
    have 52:"f \<sqinter> (w \<sqinter> g) = w \<sqinter> (f \<sqinter> g)"
      by (simp add: inf.left_commute)
    thus ?thesis
      using 51 52 abel_semigroup.left_commute inf.abel_semigroup_axioms by fastforce
  qed
  also have "... = sum ((f \<squnion> f\<^sup>T) \<sqinter> (w \<sqinter> g))"
    using 2 acyclic_asymmetric inf.sup_monoid.add_commute sum_disjoint spanning_forest_def by simp
  also have "... = sum (w \<sqinter> g)"
    using 4 by (metis inf_absorb2 inf.assoc)
  finally show "minimum_spanning_forest f g"
    using 2 3 minimum_spanning_forest_def by simp
qed

end

end

