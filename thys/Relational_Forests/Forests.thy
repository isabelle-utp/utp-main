(* Title:      Orientations and Undirected Forests
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Orientations and Undirected Forests\<close>

text \<open>
In this theory we study orientations and various second-order specifications of undirected forests.
The results are structured by the classes in which they can be proved, which correspond to algebraic structures.
Most classes are generalisations of Kleene relation algebras.
None of the classes except \<open>kleene_relation_algebra\<close> assumes the double-complement law \<open>--x = x\<close> available in Boolean algebras.
The corresponding paper does not elaborate these fine distinctions, so some results take a different form in this theory.
They usually specialise to Kleene relation algebras after simplification using \<open>--x = x\<close>.
\<close>

theory Forests

imports Stone_Kleene_Relation_Algebras.Kleene_Relation_Algebras

begin

subsection \<open>Orientability\<close>

(* move to Relation_Algebras *)
context bounded_distrib_allegory_signature
begin

abbreviation irreflexive_inf :: "'a \<Rightarrow> bool" where "irreflexive_inf x \<equiv> x \<sqinter> 1 = bot"

end

context bounded_distrib_allegory
begin

(* move to Relation_Algebras *)
lemma irreflexive_inf_arc_asymmetric:
  "irreflexive_inf x \<Longrightarrow> arc x \<Longrightarrow> asymmetric x"
proof -
  assume "irreflexive_inf x" "arc x"
  hence "bot = (x * top)\<^sup>T \<sqinter> x"
    by (metis arc_top_arc comp_right_one schroeder_1)
  thus ?thesis
    by (metis comp_inf.semiring.mult_zero_right conv_inf_bot_iff inf.sup_relative_same_increasing top_right_mult_increasing)
qed

lemma asymmetric_inf:
  "asymmetric x \<longleftrightarrow> irreflexive_inf (x * x)"
  using inf.sup_monoid.add_commute schroeder_2 by force

lemma asymmetric_irreflexive_inf:
  "asymmetric x \<Longrightarrow> irreflexive_inf x"
  by (metis asymmetric_inf_closed coreflexive_symmetric inf.idem inf_le2)

lemma transitive_asymmetric_irreflexive_inf:
  "transitive x \<Longrightarrow> asymmetric x \<longleftrightarrow> irreflexive_inf x"
  by (smt asymmetric_inf asymmetric_irreflexive_inf inf.absorb2 inf.cobounded1 inf.sup_monoid.add_commute inf_assoc le_bot)

abbreviation "orientation x y \<equiv> y \<squnion> y\<^sup>T = x \<and> asymmetric y"
abbreviation "loop_orientation x y \<equiv> y \<squnion> y\<^sup>T = x \<and> antisymmetric y"
abbreviation "super_orientation x y \<equiv> x \<le> y \<squnion> y\<^sup>T \<and> asymmetric y"
abbreviation "loop_super_orientation x y \<equiv> x \<le> y \<squnion> y\<^sup>T \<and> antisymmetric y"

lemma orientation_symmetric:
  "orientation x y \<Longrightarrow> symmetric x"
  using conv_dist_sup sup_commute by auto

lemma orientation_irreflexive_inf:
  "orientation x y \<Longrightarrow> irreflexive_inf x"
  using asymmetric_irreflexive_inf asymmetric_conv_closed inf_sup_distrib2 by auto

lemma loop_orientation_symmetric:
  "loop_orientation x y \<Longrightarrow> symmetric x"
  using conv_dist_sup sup_commute by auto

lemma loop_orientation_diagonal:
  "loop_orientation x y \<Longrightarrow> y \<sqinter> y\<^sup>T = x \<sqinter> 1"
  by (metis inf.sup_monoid.add_commute inf.sup_same_context inf_le2 inf_sup_distrib1 one_inf_conv sup.idem)

lemma super_orientation_irreflexive_inf:
  "super_orientation x y \<Longrightarrow> irreflexive_inf x"
  using coreflexive_bot_closed inf.sup_monoid.add_assoc inf.sup_right_divisibility inf_bot_right loop_orientation_diagonal by fastforce

lemma loop_super_orientation_diagonal:
  "loop_super_orientation x y \<Longrightarrow> x \<sqinter> 1 \<le> y \<sqinter> y\<^sup>T"
  using inf.sup_right_divisibility inf_assoc loop_orientation_diagonal by fastforce

definition "orientable x \<equiv> \<exists>y . orientation x y"
definition "loop_orientable x \<equiv> \<exists>y . loop_orientation x y"
definition "super_orientable x \<equiv> \<exists>y . super_orientation x y"
definition "loop_super_orientable x \<equiv> \<exists>y . loop_super_orientation x y"

lemma orientable_symmetric:
  "orientable x \<Longrightarrow> symmetric x"
  using orientable_def orientation_symmetric by blast

lemma orientable_irreflexive_inf:
  "orientable x \<Longrightarrow> irreflexive_inf x"
  using orientable_def orientation_irreflexive_inf by blast

lemma loop_orientable_symmetric:
  "loop_orientable x \<Longrightarrow> symmetric x"
  using loop_orientable_def loop_orientation_symmetric by blast

lemma super_orientable_irreflexive_inf:
  "super_orientable x \<Longrightarrow> irreflexive_inf x"
  using super_orientable_def super_orientation_irreflexive_inf by blast

lemma orientable_down_closed:
  assumes "symmetric x"
      and "x \<le> y"
      and "orientable y"
    shows "orientable x"
proof -
  from assms(3) obtain z where 1: "z \<squnion> z\<^sup>T = y \<and> asymmetric z"
    using orientable_def by blast
  let ?z = "x \<sqinter> z"
  have "orientation x ?z"
  proof (rule conjI)
    show "asymmetric ?z"
      using 1 by (simp add: conv_dist_inf inf.left_commute inf.sup_monoid.add_assoc)
    thus "?z \<squnion> ?z\<^sup>T = x"
      using 1 by (metis assms(1,2) conv_dist_inf inf.orderE inf_sup_distrib1)
  qed
  thus ?thesis
    using orientable_def by blast
qed

lemma loop_orientable_down_closed:
  assumes "symmetric x"
      and "x \<le> y"
      and "loop_orientable y"
    shows "loop_orientable x"
proof -
  from assms(3) obtain z where 1: "z \<squnion> z\<^sup>T = y \<and> antisymmetric z"
    using loop_orientable_def by blast
  let ?z = "x \<sqinter> z"
  have "loop_orientation x ?z"
  proof (rule conjI)
    show "antisymmetric ?z"
      using 1 antisymmetric_inf_closed inf_commute by fastforce
    thus "?z \<squnion> ?z\<^sup>T = x"
      using 1 by (metis assms(1,2) conv_dist_inf inf.orderE inf_sup_distrib1)
  qed
  thus ?thesis
    using loop_orientable_def by blast
qed

lemma super_orientable_down_closed:
  assumes "x \<le> y"
      and "super_orientable y"
    shows "super_orientable x"
  using assms order_lesseq_imp super_orientable_def by auto

lemma loop_super_orientable_down_closed:
  assumes "x \<le> y"
      and "loop_super_orientable y"
    shows "loop_super_orientable x"
  using assms order_lesseq_imp loop_super_orientable_def by auto

abbreviation "orientable_1 x \<equiv> loop_super_orientable x"
abbreviation "orientable_2 x \<equiv> \<exists>y . x \<le> y \<squnion> y\<^sup>T \<and> y \<sqinter> y\<^sup>T \<le> x \<sqinter> 1"
abbreviation "orientable_3 x \<equiv> \<exists>y . x \<le> y \<squnion> y\<^sup>T \<and> y \<sqinter> y\<^sup>T = x \<sqinter> 1"
abbreviation "orientable_4 x \<equiv> irreflexive_inf x \<longrightarrow> super_orientable x"
abbreviation "orientable_5 x \<equiv> symmetric x \<longrightarrow> loop_orientable x"
abbreviation "orientable_6 x \<equiv> symmetric x \<longrightarrow> (\<exists>y . y \<squnion> y\<^sup>T = x \<and> y \<sqinter> y\<^sup>T \<le> x \<sqinter> 1)"
abbreviation "orientable_7 x \<equiv> symmetric x \<longrightarrow> (\<exists>y . y \<squnion> y\<^sup>T = x \<and> y \<sqinter> y\<^sup>T = x \<sqinter> 1)"
abbreviation "orientable_8 x \<equiv> symmetric x \<and> irreflexive_inf x \<longrightarrow> orientable x"

lemma super_orientation_diagonal:
  "x \<le> y \<squnion> y\<^sup>T \<Longrightarrow> y \<sqinter> y\<^sup>T \<le> x \<sqinter> 1 \<Longrightarrow> y \<sqinter> y\<^sup>T = x \<sqinter> 1"
  using inf.antisym loop_super_orientation_diagonal by auto

lemma orientable_2_implies_1:
  "orientable_2 x \<Longrightarrow> orientable_1 x"
  using loop_super_orientable_def by auto

lemma orientable_2_3:
  "orientable_2 x \<longleftrightarrow> orientable_3 x"
  using eq_refl super_orientation_diagonal by blast

lemma orientable_5_6:
  "orientable_5 x \<longleftrightarrow> orientable_6 x"
  using loop_orientable_def loop_orientation_diagonal by fastforce

lemma orientable_6_7:
  "orientable_6 x \<longleftrightarrow> orientable_7 x"
  using super_orientation_diagonal by fastforce

lemma orientable_7_implies_8:
  "orientable_7 x \<Longrightarrow> orientable_8 x"
  using orientable_def by blast

lemma orientable_5_implies_1:
  "orientable_5 (x \<squnion> x\<^sup>T) \<Longrightarrow> orientable_1 x"
  using conv_dist_sup loop_orientable_def loop_super_orientable_def sup_commute by fastforce

text \<open>ternary predicate S called \<open>split\<close> here\<close>

abbreviation "split x y z \<equiv> y \<sqinter> y\<^sup>T = x \<and> y \<squnion> y\<^sup>T = z"

text \<open>Theorem 3.1\<close>

lemma orientation_split:
  "orientation x y \<longleftrightarrow> split bot y x"
  by auto

text \<open>Theorem 3.2\<close>

lemma split_1_loop_orientation:
  "split 1 y x \<Longrightarrow> loop_orientation x y"
  by simp

text \<open>Theorem 3.3\<close>

lemma loop_orientation_split:
  "loop_orientation x y \<longleftrightarrow> split (x \<sqinter> 1) y x"
  by (metis inf.cobounded2 loop_orientation_diagonal)

text \<open>Theorem 3.4\<close>

lemma loop_orientation_split_inf_1:
  "loop_orientation x y \<longleftrightarrow> split (y \<sqinter> 1) y x"
  by (metis inf.sup_monoid.add_commute inf.sup_same_context inf_le2 one_inf_conv)

lemma loop_orientation_top_split:
  "loop_orientation top y \<longleftrightarrow> split 1 y top"
  by (simp add: loop_orientation_split)

text \<open>injective and transitive orientations\<close>

definition "injectively_orientable x \<equiv> \<exists>y . orientation x y \<and> injective y"

lemma injectively_orientable_orientable:
  "injectively_orientable x \<Longrightarrow> orientable x"
  using injectively_orientable_def orientable_def by auto

lemma orientable_orientable_1:
  "orientable x \<Longrightarrow> orientable_1 x"
  by (metis bot_least order_refl loop_super_orientable_def orientable_def)

lemma injectively_orientable_down_closed:
  assumes "symmetric x"
      and "x \<le> y"
      and "injectively_orientable y"
    shows "injectively_orientable x"
proof -
  from assms(3) obtain z where 1: "z \<squnion> z\<^sup>T = y \<and> asymmetric z \<and> injective z"
    using injectively_orientable_def by blast
  let ?z = "x \<sqinter> z"
  have 2: "injective ?z"
    using 1 inf_commute injective_inf_closed by fastforce
  have "orientation x ?z"
  proof (rule conjI)
    show "asymmetric ?z"
      using 1 by (simp add: conv_dist_inf inf.left_commute inf.sup_monoid.add_assoc)
    thus "?z \<squnion> ?z\<^sup>T = x"
      using 1 by (metis assms(1,2) conv_dist_inf inf.orderE inf_sup_distrib1)
  qed
  thus ?thesis
    using 2 injectively_orientable_def by blast
qed

definition "transitively_orientable x \<equiv> \<exists>y . orientation x y \<and> transitive y"

lemma transitively_orientable_orientable:
  "transitively_orientable x \<Longrightarrow> orientable x"
  using transitively_orientable_def orientable_def by auto

lemma irreflexive_transitive_orientation_asymmetric:
  assumes "irreflexive_inf x"
      and "transitive y"
      and "y \<squnion> y\<^sup>T = x"
    shows "asymmetric y"
  using assms comp_inf.mult_right_dist_sup transitive_asymmetric_irreflexive_inf by auto

text \<open>Theorem 12\<close>

lemma transitively_orientable_2:
  "transitively_orientable x \<longleftrightarrow> irreflexive_inf x \<and> (\<exists>y . y \<squnion> y\<^sup>T = x \<and> transitive y)"
  by (metis irreflexive_transitive_orientation_asymmetric coreflexive_bot_closed loop_orientation_split transitively_orientable_def)

end

context relation_algebra_signature
begin

abbreviation asymmetric_var :: "'a \<Rightarrow> bool" where "asymmetric_var x \<equiv> irreflexive (x * x)"

end

context pd_allegory
begin

text \<open>Theorem 1.4\<close>

lemma asymmetric_var:
  "asymmetric x \<longleftrightarrow> asymmetric_var x"
  using asymmetric_inf pseudo_complement by auto

text \<open>Theorem 1.3\<close>
text \<open>(Theorem 1.2 is \<open>asymmetric_irreflexive\<close> in \<open>Relation_Algebras\<close>)\<close>

lemma transitive_asymmetric_irreflexive:
  "transitive x \<Longrightarrow> asymmetric x \<longleftrightarrow> irreflexive x"
  using strict_order_var by blast

lemma orientable_irreflexive:
  "orientable x \<Longrightarrow> irreflexive x"
  using orientable_irreflexive_inf pseudo_complement by blast

lemma super_orientable_irreflexive:
  "super_orientable x \<Longrightarrow> irreflexive x"
  using pseudo_complement super_orientable_irreflexive_inf by blast

lemma orientation_diversity_split:
  "orientation (-1) y \<longleftrightarrow> split bot y (-1)"
  by auto

abbreviation "linear_orderable_1 x \<equiv> linear_order x"
abbreviation "linear_orderable_2 x \<equiv> linear_strict_order x"
abbreviation "linear_orderable_3 x \<equiv> transitive x \<and> asymmetric x \<and> strict_linear x"
abbreviation "linear_orderable_3a x \<equiv> transitive x \<and> strict_linear x"

abbreviation "orientable_11 x \<equiv> split 1 x top"
abbreviation "orientable_12 x \<equiv> split bot x (-1)"

lemma linear_strict_order_split:
  "linear_strict_order x \<longleftrightarrow> transitive x \<and> split bot x (-1)"
  using strict_order_var by blast

text \<open>Theorem 1.6\<close>

lemma linear_strict_order_without_irreflexive:
  "linear_strict_order x \<longleftrightarrow> transitive x \<and> strict_linear x"
  using strict_linear_irreflexive by auto

lemma linear_order_without_reflexive:
  "linear_order x \<longleftrightarrow> antisymmetric x \<and> transitive x \<and> linear x"
  using linear_reflexive by blast

lemma linear_orderable_1_implies_2:
  "linear_orderable_1 x \<Longrightarrow> linear_orderable_2 (x \<sqinter> -1)"
  using linear_order_strict_order by blast

lemma linear_orderable_2_3:
  "linear_orderable_2 x \<longleftrightarrow> linear_orderable_3 x"
  using linear_strict_order_split by auto

lemma linear_orderable_3_3a:
  "linear_orderable_3 x \<longleftrightarrow> linear_orderable_3a x"
  using strict_linear_irreflexive strict_order_var by blast

lemma linear_orderable_3_implies_orientable_12:
  "linear_orderable_3 x \<Longrightarrow> orientable_12 x"
  by simp

lemma orientable_11_implies_12:
  "orientable_11 x \<Longrightarrow> orientable_12 (x \<sqinter> -1)"
  by (smt inf_sup_distrib2 conv_complement conv_dist_inf conv_involutive inf_import_p inf_top.left_neutral linear_asymmetric maddux_3_13 p_inf symmetric_one_closed)

end

context stone_relation_algebra
begin

text \<open>Theorem 3.5\<close>

lemma split_symmetric_asymmetric:
  assumes "regular x"
    shows "split x y z \<longleftrightarrow> y \<sqinter> y\<^sup>T = x \<and> (y \<sqinter> -y\<^sup>T) \<squnion> (y \<sqinter> -y\<^sup>T)\<^sup>T = z \<sqinter> -x \<and> x \<le> z"
proof
  assume "split x y z"
  thus "y \<sqinter> y\<^sup>T = x \<and> (y \<sqinter> -y\<^sup>T) \<squnion> (y \<sqinter> -y\<^sup>T)\<^sup>T = z \<sqinter> -x \<and> x \<le> z"
    by (metis conv_complement conv_dist_inf conv_involutive inf.cobounded1 inf.sup_monoid.add_commute inf_import_p inf_sup_distrib2 le_supI1)
next
  assume "y \<sqinter> y\<^sup>T = x \<and> (y \<sqinter> -y\<^sup>T) \<squnion> (y \<sqinter> -y\<^sup>T)\<^sup>T = z \<sqinter> -x \<and> x \<le> z"
  thus "split x y z"
    by (smt (z3) assms conv_dist_sup conv_involutive inf.absorb2 inf.boundedE inf.cobounded1 inf.idem inf.sup_monoid.add_commute inf_import_p maddux_3_11_pp sup.left_commute sup_commute sup_inf_absorb)
qed

lemma orientable_1_2:
  "orientable_1 x \<longleftrightarrow> orientable_2 x"
proof
  assume "orientable_1 x"
  from this obtain y where 1: "x \<le> y \<squnion> y\<^sup>T \<and> y \<sqinter> y\<^sup>T \<le> 1"
    using loop_super_orientable_def by blast
  let ?y = "(x \<sqinter> 1) \<squnion> (y \<sqinter> -1)"
  have "x \<le> ?y \<squnion> ?y\<^sup>T \<and> ?y \<sqinter> ?y\<^sup>T \<le> x \<sqinter> 1"
  proof
    have "x \<sqinter> -1 \<le> (y \<sqinter> -1) \<squnion> (y\<^sup>T \<sqinter> -1)"
      using 1 inf.sup_right_divisibility inf_commute inf_left_commute inf_sup_distrib2 by auto
    also have "... \<le> ?y \<squnion> ?y\<^sup>T"
      by (metis comp_inf.semiring.add_mono conv_complement conv_dist_inf conv_isotone sup.cobounded2 symmetric_one_closed)
    finally show "x \<le> ?y \<squnion> ?y\<^sup>T"
      by (metis comp_inf.semiring.add_mono maddux_3_11_pp regular_one_closed sup.cobounded1 sup.left_idem)
    have "x = (x \<sqinter> 1) \<squnion> (x \<sqinter> -1)"
      by (metis maddux_3_11_pp regular_one_closed)
    have "?y \<sqinter> ?y\<^sup>T = (x \<sqinter> 1) \<squnion> ((y \<sqinter> -1) \<sqinter> (y\<^sup>T \<sqinter> -1))"
      by (metis comp_inf.semiring.distrib_left conv_complement conv_dist_inf conv_dist_sup coreflexive_symmetric distrib_imp1 inf_le2 symmetric_one_closed)
    also have "... = x \<sqinter> 1"
      by (metis 1 inf_assoc inf_commute pseudo_complement regular_one_closed selection_closed_id inf.cobounded2 maddux_3_11_pp)
    finally show "?y \<sqinter> ?y\<^sup>T \<le> x \<sqinter> 1"
      by simp
  qed
  thus "orientable_2 x"
    by blast
next
  assume "orientable_2 x"
  thus "orientable_1 x"
    using loop_super_orientable_def by auto
qed

lemma orientable_8_implies_5:
  assumes "orientable_8 (x \<sqinter> -1)"
  shows "orientable_5 x"
proof
  assume 1: "symmetric x"
  hence "symmetric (x \<sqinter> -1)"
    by (simp add: conv_complement symmetric_inf_closed)
  hence "orientable (x \<sqinter> -1)"
    by (simp add: assms pseudo_complement)
  from this obtain y where 2: "y \<squnion> y\<^sup>T = x \<sqinter> -1 \<and> asymmetric y"
    using orientable_def by blast
  let ?y = "y \<squnion> (x \<sqinter> 1)"
  have "loop_orientation x ?y"
  proof
    have "?y \<squnion> ?y\<^sup>T = y \<squnion> y\<^sup>T \<squnion> (x \<sqinter> 1)"
      using 1 conv_dist_inf conv_dist_sup sup_assoc sup_commute by auto
    thus "?y \<squnion> ?y\<^sup>T = x"
      by (metis 2 maddux_3_11_pp regular_one_closed)
    have "?y \<sqinter> ?y\<^sup>T = (y \<sqinter> y\<^sup>T) \<squnion> (x \<sqinter> 1)"
      by (simp add: 1 conv_dist_sup sup_inf_distrib2 symmetric_inf_closed)
    thus "antisymmetric ?y"
      by (simp add: 2)
  qed
  thus "loop_orientable x"
    using loop_orientable_def by blast
qed

lemma orientable_4_implies_1:
  assumes "orientable_4 (x \<sqinter> -1)"
  shows "orientable_1 x"
proof -
  obtain y where 1: "x \<sqinter> -1 \<le> y \<squnion> y\<^sup>T \<and> asymmetric y"
    using assms pseudo_complement super_orientable_def by auto
  let ?y = "y \<squnion> 1"
  have "loop_super_orientation x ?y"
  proof
    show "x \<le> ?y \<squnion> ?y\<^sup>T"
      by (smt 1 comp_inf.semiring.add_mono conv_dist_sup inf_le2 maddux_3_11_pp reflexive_one_closed regular_one_closed sup.absorb1 sup.left_commute sup_assoc symmetric_one_closed)
    show "antisymmetric ?y"
      using 1 conv_dist_sup distrib_imp1 inf_sup_distrib1 sup_monoid.add_commute by auto
  qed
  thus ?thesis
    using loop_super_orientable_def by blast
qed

lemma orientable_1_implies_4:
  assumes "orientable_1 (x \<squnion> 1)"
  shows "orientable_4 x"
proof
  assume 1: "irreflexive_inf x"
  obtain y where 2: "x \<squnion> 1 \<le> y \<squnion> y\<^sup>T \<and> antisymmetric y"
    using assms loop_super_orientable_def by blast
  let ?y = "y \<sqinter> -1"
  have "super_orientation x ?y"
  proof
    have "x \<le> (y \<squnion> y\<^sup>T) \<sqinter> -1"
      using 1 2 pseudo_complement by auto
    thus "x \<le> ?y \<squnion> ?y\<^sup>T"
      by (simp add: conv_complement conv_dist_inf inf_sup_distrib2)
    have "?y \<sqinter> ?y\<^sup>T = y \<sqinter> y\<^sup>T \<sqinter> -1"
      using conv_complement conv_dist_inf inf_commute inf_left_commute by auto
    thus "asymmetric ?y"
      using 2 pseudo_complement by auto
  qed
  thus "super_orientable x"
    using super_orientable_def by blast
qed

lemma orientable_1_implies_5:
  assumes "orientable_1 x"
  shows "orientable_5 x"
proof
  assume 1: "symmetric x"
  obtain y where 2: "x \<le> y \<squnion> y\<^sup>T \<and> antisymmetric y"
    using assms loop_super_orientable_def by blast
  let ?y = "(x \<sqinter> 1) \<squnion> (y \<sqinter> x \<sqinter> -1)"
  have "loop_orientation x ?y"
  proof
    have "?y \<squnion> ?y\<^sup>T = ((y \<squnion> y\<^sup>T) \<sqinter> x \<sqinter> -1) \<squnion> (x \<sqinter> 1)"
      by (simp add: 1 conv_complement conv_dist_inf conv_dist_sup inf_sup_distrib2 sup.left_commute sup_commute)
    thus "?y \<squnion> ?y\<^sup>T = x"
      by (metis 2 inf_absorb2 maddux_3_11_pp regular_one_closed)
    have "?y \<sqinter> ?y\<^sup>T = (x \<sqinter> 1) \<squnion> ((y \<sqinter> x \<sqinter> -1) \<sqinter> (y\<^sup>T \<sqinter> x\<^sup>T \<sqinter> -1))"
      by (simp add: 1 conv_complement conv_dist_inf conv_dist_sup sup_inf_distrib1)
    thus "antisymmetric ?y"
      by (metis 2 antisymmetric_inf_closed conv_complement conv_dist_inf inf_le2 le_supI symmetric_one_closed)
  qed
  thus "loop_orientable x"
    using loop_orientable_def by blast
qed

text \<open>Theorem 2\<close>

lemma all_orientable_characterisations:
  shows "(\<forall>x . orientable_1 x) \<longleftrightarrow> (\<forall>x . orientable_2 x)"
    and "(\<forall>x . orientable_1 x) \<longleftrightarrow> (\<forall>x . orientable_3 x)"
    and "(\<forall>x . orientable_1 x) \<longleftrightarrow> (\<forall>x . orientable_4 x)"
    and "(\<forall>x . orientable_1 x) \<longleftrightarrow> (\<forall>x . orientable_5 x)"
    and "(\<forall>x . orientable_1 x) \<longleftrightarrow> (\<forall>x . orientable_6 x)"
    and "(\<forall>x . orientable_1 x) \<longleftrightarrow> (\<forall>x . orientable_7 x)"
    and "(\<forall>x . orientable_1 x) \<longleftrightarrow> (\<forall>x . orientable_8 x)"
  subgoal using orientable_1_2 by simp
  subgoal using orientable_1_2 orientable_2_3 by simp
  subgoal using orientable_1_implies_4 orientable_4_implies_1 by blast
  subgoal using orientable_5_implies_1 orientable_1_implies_5 by blast
  subgoal using orientable_5_6 orientable_5_implies_1 orientable_1_implies_5 by blast
  subgoal using orientable_5_6 orientable_5_implies_1 orientable_6_7 orientable_1_implies_5 by force
  subgoal using orientable_5_6 orientable_5_implies_1 orientable_6_7 orientable_7_implies_8 orientable_1_implies_5 orientable_8_implies_5 by auto
  done

lemma orientable_12_implies_11:
  "orientable_12 x \<Longrightarrow> orientable_11 (x \<squnion> 1)"
  by (smt inf_top.right_neutral conv_complement conv_dist_sup conv_involutive inf_import_p maddux_3_13 p_bot p_dist_inf p_dist_sup regular_one_closed symmetric_one_closed)

(* The following lemma might go into Relation_Algebras. *)
lemma linear_strict_order_order:
  "linear_strict_order x \<Longrightarrow> linear_order (x \<squnion> 1)"
  by (simp add: strict_order_order transitive_asymmetric_irreflexive orientable_12_implies_11)

lemma linear_orderable_2_implies_1:
  "linear_orderable_2 x \<Longrightarrow> linear_orderable_1 (x \<squnion> 1)"
  using linear_strict_order_order by simp

text \<open>Theorem 4\<close>
text \<open>Theorem 12\<close>
text \<open>Theorem 13\<close>

lemma exists_split_characterisations:
  shows "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_2 x)"
  and "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_3 x)"
  and "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_3a x)"
  and "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> transitively_orientable (-1)"
  and "(\<exists>x . linear_orderable_1 x) \<Longrightarrow> (\<exists>x . orientable_11 x)"
  and "(\<exists>x . orientable_11 x) \<longleftrightarrow> (\<exists>x . orientable_12 x)"
  subgoal 1 using linear_strict_order_order linear_order_strict_order by blast
  subgoal 2 using 1 strict_order_var by blast
  subgoal using 1 linear_strict_order_without_irreflexive by auto
  subgoal using 2 transitively_orientable_def by auto
  subgoal using loop_orientation_top_split by blast
  subgoal using orientable_11_implies_12 orientable_12_implies_11 by blast
  done

text \<open>Theorem 4\<close>
text \<open>Theorem 12\<close>

lemma exists_all_orientable:
  shows "(\<exists>x . orientable_11 x) \<longleftrightarrow> (\<forall>x . orientable_1 x)"
    and "transitively_orientable (-1) \<Longrightarrow> (\<forall>x . orientable_8 x)"
  subgoal apply (rule iffI)
    subgoal using loop_super_orientable_def top_greatest by blast
    subgoal using loop_orientation_top_split loop_super_orientable_def top_le by blast
    done
  subgoal using orientable_down_closed pseudo_complement transitively_orientable_orientable by blast
  done

end

subsection \<open>Undirected forests\<close>

text \<open>
We start with a few general results in Kleene algebras and a few basic properties of directed acyclic graphs.
\<close>

(* move to Kleene_Algebras *)
context kleene_algebra
begin

text \<open>Theorem 1.9\<close>

lemma plus_separate_comp_bot:
  assumes "x * y = bot"
  shows "(x \<squnion> y)\<^sup>+ = x\<^sup>+ \<squnion> y\<^sup>+ \<squnion> y\<^sup>+ * x\<^sup>+"
proof -
  have "(x \<squnion> y)\<^sup>+ = x * y\<^sup>\<star> * x\<^sup>\<star> \<squnion> y\<^sup>+ * x\<^sup>\<star>"
    using assms cancel_separate_1 semiring.distrib_right mult_assoc by auto
  also have "... = x\<^sup>+ \<squnion> y\<^sup>+ * x\<^sup>\<star>"
    by (simp add: assms star_absorb)
  finally show ?thesis
    by (metis star.circ_back_loop_fixpoint star.circ_plus_same sup_assoc sup_commute mult_assoc)
qed

end

(* move to Kleene_Relation_Algebras *)
context bounded_distrib_kleene_allegory
begin

lemma reflexive_inf_plus_star:
  assumes "reflexive x"
  shows "x \<sqinter> y\<^sup>+ \<le> 1 \<longleftrightarrow> x \<sqinter> y\<^sup>\<star> = 1"
  using assms reflexive_inf_star sup.absorb_iff1 by auto

end

context pd_kleene_allegory
begin

(* move to Kleene_Relation_Algebras *)
lemma acyclic_star_inf_conv_iff:
  assumes "irreflexive w"
  shows "acyclic w \<longleftrightarrow> w\<^sup>\<star> \<sqinter> w\<^sup>T\<^sup>\<star> = 1"
  by (metis assms acyclic_star_below_complement_1 acyclic_star_inf_conv conv_complement conv_order equivalence_one_closed inf.absorb1 inf.left_commute pseudo_complement star.circ_increasing)

text \<open>Theorem 1.7\<close>

(* move to Kleene_Relation_Algebras *)
lemma acyclic_irreflexive_star_antisymmetric:
  "acyclic x \<longleftrightarrow> irreflexive x \<and> antisymmetric (x\<^sup>\<star>)"
  by (metis acyclic_star_inf_conv_iff conv_star_commute dual_order.trans eq_iff reflexive_inf_closed star.circ_mult_increasing star.circ_reflexive)

text \<open>Theorem 1.8\<close>

(* move to Kleene_Relation_Algebras *)
lemma acyclic_plus_asymmetric:
  "acyclic x \<longleftrightarrow> asymmetric (x\<^sup>+)"
  using acyclic_asymmetric asymmetric_irreflexive star.circ_transitive_equal star.left_plus_circ mult_assoc by auto

text \<open>Theorem 1.3\<close>
text \<open>(Theorem 1.1 is \<open>acyclic_asymmetric\<close> in \<open>Kleene_Relation_Algebras\<close>)\<close>

lemma transitive_acyclic_irreflexive:
  "transitive x \<Longrightarrow> acyclic x \<longleftrightarrow> irreflexive x"
  using antisym star.circ_mult_increasing star_right_induct_mult by fastforce

lemma transitive_acyclic_asymmetric:
  "transitive x \<Longrightarrow> acyclic x \<longleftrightarrow> asymmetric x"
  using strict_order_var transitive_acyclic_irreflexive by blast

text \<open>Theorem 1.5\<close>

lemma strict_order_transitive_acyclic:
  "strict_order x \<longleftrightarrow> transitive x \<and> acyclic x"
  using transitive_acyclic_irreflexive by auto

lemma linear_strict_order_transitive_acyclic:
  "linear_strict_order x \<longleftrightarrow> transitive x \<and> acyclic x \<and> strict_linear x"
  using transitive_acyclic_irreflexive by auto

text \<open>
The following are various specifications of an undirected graph being acyclic.
\<close>

definition "acyclic_1 x \<equiv> \<forall>y . orientation x y \<longrightarrow> acyclic y"
definition "acyclic_1b x \<equiv> \<forall>y . orientation x y \<longrightarrow> y\<^sup>\<star> \<sqinter> y\<^sup>T\<^sup>\<star> = 1"
definition "acyclic_2 x \<equiv> \<forall>y . y \<le> x \<and> asymmetric y \<longrightarrow> acyclic y"
definition "acyclic_2a x \<equiv> \<forall>y . y \<squnion> y\<^sup>T \<le> x \<and> asymmetric y \<longrightarrow> acyclic y"
definition "acyclic_2b x \<equiv> \<forall>y . y \<squnion> y\<^sup>T \<le> x \<and> asymmetric y \<longrightarrow> y\<^sup>\<star> \<sqinter> y\<^sup>T\<^sup>\<star> = 1"
definition "acyclic_3a x \<equiv> \<forall>y . y \<le> x \<and> x \<le> y\<^sup>\<star> \<longrightarrow> y = x"
definition "acyclic_3b x \<equiv> \<forall>y . y \<le> x \<and> y\<^sup>\<star> = x\<^sup>\<star> \<longrightarrow> y = x"
definition "acyclic_3c x \<equiv> \<forall>y . y \<le> x \<and> x \<le> y\<^sup>+ \<longrightarrow> y = x"
definition "acyclic_3d x \<equiv> \<forall>y . y \<le> x \<and> y\<^sup>+ = x\<^sup>+ \<longrightarrow> y = x"
definition "acyclic_4 x \<equiv> \<forall>y . y \<le> x \<longrightarrow> x \<sqinter> y\<^sup>\<star> \<le> --y"
definition "acyclic_4a x \<equiv> \<forall>y . y \<le> x \<longrightarrow> x \<sqinter> y\<^sup>\<star> \<le> y"
definition "acyclic_4b x \<equiv> \<forall>y . y \<le> x \<longrightarrow> x \<sqinter> y\<^sup>\<star> = y"
definition "acyclic_4c x \<equiv> \<forall>y . y \<le> x \<longrightarrow> y \<sqinter> (x \<sqinter> -y)\<^sup>\<star> = bot"
definition "acyclic_5a x \<equiv> \<forall>y . y \<le> x \<longrightarrow> y\<^sup>\<star> \<sqinter> (x \<sqinter> -y)\<^sup>\<star> = 1"
definition "acyclic_5b x \<equiv> \<forall>y . y \<le> x \<longrightarrow> y\<^sup>\<star> \<sqinter> (x \<sqinter> -y)\<^sup>+ \<le> 1"
definition "acyclic_5c x \<equiv> \<forall>y . y \<le> x \<longrightarrow> y\<^sup>+ \<sqinter> (x \<sqinter> -y)\<^sup>\<star> \<le> 1"
definition "acyclic_5d x \<equiv> \<forall>y . y \<le> x \<longrightarrow> y\<^sup>+ \<sqinter> (x \<sqinter> -y)\<^sup>+ \<le> 1"
definition "acyclic_5e x \<equiv> \<forall>y z . y \<le> x \<and> z \<le> x \<and> y \<sqinter> z = bot \<longrightarrow> y\<^sup>\<star> \<sqinter> z\<^sup>\<star> = 1"
definition "acyclic_5f x \<equiv> \<forall>y z . y \<squnion> z \<le> x \<and> y \<sqinter> z = bot \<longrightarrow> y\<^sup>\<star> \<sqinter> z\<^sup>\<star> = 1"
definition "acyclic_5g x \<equiv> \<forall>y z . y \<squnion> z = x \<and> y \<sqinter> z = bot \<longrightarrow> y\<^sup>\<star> \<sqinter> z\<^sup>\<star> = 1"
definition "acyclic_6 x \<equiv> \<exists>y . y \<squnion> y\<^sup>T = x \<and> acyclic y \<and> injective y"

text \<open>Theorem 6\<close>

lemma acyclic_2_2a:
  assumes "symmetric x"
  shows "acyclic_2 x \<longleftrightarrow> acyclic_2a x"
proof -
  have "\<And>y . y \<le> x \<longleftrightarrow> y \<squnion> y\<^sup>T \<le> x"
    using assms conv_isotone by force
  thus ?thesis
    by (simp add: acyclic_2_def acyclic_2a_def)
qed

text \<open>Theorem 6\<close>

lemma acyclic_2a_2b:
  shows "acyclic_2a x \<longleftrightarrow> acyclic_2b x"
  by (simp add: acyclic_2a_def acyclic_2b_def acyclic_star_inf_conv_iff asymmetric_irreflexive)

text \<open>Theorem 5\<close>

lemma acyclic_1_1b:
  shows "acyclic_1 x \<longleftrightarrow> acyclic_1b x"
  by (simp add: acyclic_1_def acyclic_1b_def acyclic_star_inf_conv_iff asymmetric_irreflexive)

text \<open>Theorem 10\<close>

lemma acyclic_6_1_injectively_orientable:
  "acyclic_6 x \<longleftrightarrow> acyclic_1 x \<and> injectively_orientable x"
proof
  assume "acyclic_6 x"
  from this obtain y where 1: "y \<squnion> y\<^sup>T = x \<and> acyclic y \<and> injective y"
    using acyclic_6_def by blast
  have "acyclic_1 x"
  proof (unfold acyclic_1_def, rule allI, rule impI)
    fix z
    assume 2: "orientation x z"
    hence 3: "z = (z \<sqinter> y) \<squnion> (z \<sqinter> y\<^sup>T)"
      by (metis 1 inf_sup_absorb inf_sup_distrib1)
    have "(z \<sqinter> y) * (z \<sqinter> y\<^sup>T) \<le> z * z \<sqinter> y * y\<^sup>T"
      by (simp add: comp_isotone)
    also have "... \<le> -1 \<sqinter> 1"
      using 1 2 asymmetric_var comp_inf.mult_isotone by blast
    finally have 4: "(z \<sqinter> y) * (z \<sqinter> y\<^sup>T) = bot"
      by (simp add: le_bot)
    have "z\<^sup>+ = (z \<sqinter> y)\<^sup>+ \<squnion> (z \<sqinter> y\<^sup>T)\<^sup>+ \<squnion> (z \<sqinter> y\<^sup>T)\<^sup>+ * (z \<sqinter> y)\<^sup>+"
      using 3 4 plus_separate_comp_bot by fastforce
    also have "... \<le> y\<^sup>+ \<squnion> (z \<sqinter> y\<^sup>T)\<^sup>+ \<squnion> (z \<sqinter> y\<^sup>T)\<^sup>+ * (z \<sqinter> y)\<^sup>+"
      using comp_isotone semiring.add_right_mono star_isotone by auto
    also have "... \<le> y\<^sup>+ \<squnion> y\<^sup>T\<^sup>+ \<squnion> (z \<sqinter> y\<^sup>T)\<^sup>+ * (z \<sqinter> y)\<^sup>+"
      using comp_isotone semiring.add_left_mono semiring.add_right_mono star_isotone by auto
    also have "... \<le> -1 \<squnion> (z \<sqinter> y\<^sup>T)\<^sup>+ * (z \<sqinter> y)\<^sup>+"
      by (smt 1 conv_complement conv_isotone conv_plus_commute inf.absorb2 inf.orderE order_conv_closed order_one_closed semiring.add_right_mono sup.absorb1)
    also have "... = -1"
    proof -
      have "(z \<sqinter> y\<^sup>T)\<^sup>+ * (z \<sqinter> y)\<^sup>+ \<le> (z \<sqinter> y\<^sup>T) * top * (z \<sqinter> y)\<^sup>+"
        using comp_isotone by auto
      also have "... \<le> (z \<sqinter> y\<^sup>T) * top * (z \<sqinter> y)"
        by (metis inf.eq_refl star.circ_left_top star_plus mult_assoc)
      also have "... \<le> -1"
        by (metis 4 bot_least comp_commute_below_diversity inf.absorb2 pseudo_complement schroeder_1 mult_assoc)
      finally show ?thesis
        using sup.absorb1 by blast
    qed
    finally show "acyclic z"
      by simp
  qed
  thus "acyclic_1 x \<and> injectively_orientable x"
    using 1 injectively_orientable_def acyclic_asymmetric by blast
next
  assume "acyclic_1 x \<and> injectively_orientable x"
  thus "acyclic_6 x"
    using acyclic_6_def acyclic_1_def injectively_orientable_def by auto
qed

lemma acyclic_6_symmetric:
  "acyclic_6 x \<Longrightarrow> symmetric x"
  by (simp add: acyclic_6_1_injectively_orientable injectively_orientable_orientable orientable_symmetric)

lemma acyclic_6_irreflexive:
  "acyclic_6 x \<Longrightarrow> irreflexive x"
  by (simp add: acyclic_6_1_injectively_orientable injectively_orientable_orientable orientable_irreflexive)

lemma acyclic_4_irreflexive:
  "acyclic_4 x \<Longrightarrow> irreflexive x"
  by (metis acyclic_4_def bot_least inf.absorb2 inf.sup_monoid.add_assoc p_bot pseudo_complement star.circ_reflexive)

text \<open>Theorem 6.4\<close>

lemma acyclic_2_implies_1:
  "acyclic_2 x \<Longrightarrow> acyclic_1 x"
  using acyclic_2_def acyclic_1_def by auto

text \<open>Theorem 8\<close>

lemma acyclic_4a_4b:
  "acyclic_4a x \<longleftrightarrow> acyclic_4b x"
  using acyclic_4a_def acyclic_4b_def eq_iff star.circ_increasing by auto

text \<open>Theorem 7\<close>

lemma acyclic_3a_3b:
  "acyclic_3a x \<longleftrightarrow> acyclic_3b x"
  by (metis acyclic_3a_def acyclic_3b_def antisym star.circ_increasing star_involutive star_isotone)

text \<open>Theorem 7\<close>

lemma acyclic_3a_3c:
  assumes "irreflexive x"
  shows "acyclic_3a x \<longleftrightarrow> acyclic_3c x"
proof
  assume "acyclic_3a x"
  thus "acyclic_3c x"
    by (meson acyclic_3a_def acyclic_3c_def order_lesseq_imp star.left_plus_below_circ)
next
  assume 1: "acyclic_3c x"
  show "acyclic_3a x"
  proof (unfold acyclic_3a_def, rule allI, rule impI)
    fix y
    assume "y \<le> x \<and> x \<le> y\<^sup>\<star>"
    hence "y \<le> x \<and> x \<le> y\<^sup>+"
      by (metis assms inf.order_lesseq_imp le_infI p_inf_sup_below star_left_unfold_equal)
    thus "y = x"
      using 1 acyclic_3c_def by blast
  qed
qed

text \<open>Theorem 7\<close>

lemma acyclic_3c_3d:
  shows "acyclic_3c x \<longleftrightarrow> acyclic_3d x"
proof -
  have "\<And>y z . y \<le> z \<and> z \<le> y\<^sup>+ \<longleftrightarrow> y \<le> z \<and> y\<^sup>+ = z\<^sup>+"
    apply (rule iffI)
    apply (smt comp_associative plus_sup star.circ_transitive_equal star.left_plus_circ sup_absorb1 sup_absorb2)
    by (simp add: star.circ_mult_increasing)
  thus ?thesis
    by (simp add: acyclic_3c_def acyclic_3d_def)
qed

text \<open>Theorem 8\<close>

lemma acyclic_4a_implies_3a:
  "acyclic_4a x \<Longrightarrow> acyclic_3a x"
  using acyclic_4a_def acyclic_3a_def inf.absorb1 by auto

lemma acyclic_4a_implies_4:
  "acyclic_4a x \<Longrightarrow> acyclic_4 x"
  by (simp add: acyclic_4_def acyclic_4a_4b acyclic_4b_def pp_increasing)

lemma acyclic_4b_implies_4c:
  "acyclic_4b x \<Longrightarrow> acyclic_4c x"
  by (simp add: acyclic_4b_def acyclic_4c_def inf.sup_relative_same_increasing)

text \<open>Theorem 8.5\<close>

lemma acyclic_4_implies_2:
  assumes "symmetric x"
  shows "acyclic_4 x \<Longrightarrow> acyclic_2 x"
proof -
  assume 1: "acyclic_4 x"
  show "acyclic_2 x"
  proof (unfold acyclic_2_def, rule allI, rule impI)
    fix y
    assume 2: "y \<le> x \<and> asymmetric y"
    hence "y\<^sup>T \<le> x \<sqinter> -y"
      using assms conv_inf_bot_iff conv_isotone pseudo_complement by force
    hence "y\<^sup>\<star> \<sqinter> y\<^sup>T \<le> y\<^sup>\<star> \<sqinter> x \<sqinter> -y"
      using dual_order.trans by auto
    also have "... \<le> --y \<sqinter> -y"
      using 1 2 by (metis inf.commute acyclic_4_def comp_inf.mult_left_isotone)
    finally show "acyclic y"
      by (simp add: acyclic_star_below_complement_1 le_bot)
  qed
qed

text \<open>Theorem 10.3\<close>

lemma acyclic_6_implies_4a:
  "acyclic_6 x \<Longrightarrow> acyclic_4a x"
proof -
  assume "acyclic_6 x"
  from this obtain y where 1: "y \<squnion> y\<^sup>T = x \<and> acyclic y \<and> injective y"
    using acyclic_6_def by auto
  show "acyclic_4a x"
  proof (unfold acyclic_4a_def, rule allI, rule impI)
    fix z
    assume "z \<le> x"
    hence "z = (z \<sqinter> y) \<squnion> (z \<sqinter> y\<^sup>T)"
      using 1 by (metis inf.orderE inf_sup_distrib1)
    hence 2: "z\<^sup>\<star> = (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star>"
      using 1 by (metis cancel_separate_2)
    hence "x \<sqinter> z\<^sup>\<star> = (y \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star>) \<squnion> (y\<^sup>T \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star>)"
      using 1 inf_sup_distrib2 by auto
    also have "... \<le> z"
    proof (rule sup_least)
      have "y \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star> = (y \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>\<star>) \<squnion> (y \<sqinter> z\<^sup>\<star> * (z \<sqinter> y))"
        using 2 by (metis inf_sup_distrib1 star.circ_back_loop_fixpoint sup_commute)
      also have "... \<le> (y \<sqinter> y\<^sup>T\<^sup>\<star>) \<squnion> (y \<sqinter> z\<^sup>\<star> * (z \<sqinter> y))"
        using inf.sup_right_isotone semiring.add_right_mono star_isotone by auto
      also have "... = y \<sqinter> z\<^sup>\<star> * (z \<sqinter> y)"
        using 1 by (metis acyclic_star_below_complement bot_least inf.sup_monoid.add_commute pseudo_complement sup.absorb2)
      also have "... \<le> (z\<^sup>\<star> \<sqinter> y * (z \<sqinter> y)\<^sup>T) * (z \<sqinter> y)"
        using dedekind_2 inf_commute by auto
      also have "... \<le> y * y\<^sup>T * z"
        by (simp add: conv_isotone inf.coboundedI2 mult_isotone)
      also have "... \<le> z"
        using 1 mult_left_isotone by fastforce
      finally show "y \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star> \<le> z"
        .
      have "y\<^sup>T \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star> = (y\<^sup>T \<sqinter> (z \<sqinter> y)\<^sup>\<star>) \<squnion> (y\<^sup>T \<sqinter> (z \<sqinter> y\<^sup>T) * z\<^sup>\<star>)"
        using 2 by (metis inf_sup_distrib1 star.circ_loop_fixpoint sup_commute)
      also have "... \<le> (y\<^sup>T \<sqinter> y\<^sup>\<star>) \<squnion> (y\<^sup>T \<sqinter> (z \<sqinter> y\<^sup>T) * z\<^sup>\<star>)"
        using inf.sup_right_isotone semiring.add_right_mono star_isotone by auto
      also have "... = y\<^sup>T \<sqinter> (z \<sqinter> y\<^sup>T) * z\<^sup>\<star>"
        using 1 acyclic_star_below_complement_1 inf_commute by auto
      also have "... \<le> (z \<sqinter> y\<^sup>T) * (z\<^sup>\<star> \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>T * y\<^sup>T)"
        using dedekind_1 inf_commute by auto
      also have "... \<le> z * y * y\<^sup>T"
        by (simp add: comp_associative comp_isotone conv_dist_inf inf.coboundedI2)
      also have "... \<le> z"
        using 1 mult_right_isotone mult_assoc by fastforce
      finally show "y\<^sup>T \<sqinter> (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star> \<le> z"
        .
    qed
    finally show "x \<sqinter> z\<^sup>\<star> \<le> z"
      .
  qed
qed

text \<open>Theorem 1.10\<close>

lemma top_injective_inf_complement:
  assumes "injective x"
  shows "top * (x \<sqinter> y) \<sqinter> top * (x \<sqinter> -y) = bot"
proof -
  have "(x \<sqinter> -y) * (x\<^sup>T \<sqinter> y\<^sup>T) \<le> -1"
    by (metis conv_dist_inf inf.cobounded2 inf_left_idem mult_left_one p_shunting_swap schroeder_4_p)
  hence "(x \<sqinter> -y) * (x\<^sup>T \<sqinter> y\<^sup>T) = bot"
    by (smt assms comp_isotone coreflexive_comp_inf coreflexive_idempotent coreflexive_symmetric dual_order.trans inf.cobounded1 strict_order_var)
  thus ?thesis
    by (simp add: conv_dist_inf schroeder_2 mult_assoc)
qed

lemma top_injective_inf_complement_2:
  assumes "injective x"
  shows "(x\<^sup>T \<sqinter> y) * top \<sqinter> (x\<^sup>T \<sqinter> -y) * top = bot"
  by (smt assms top_injective_inf_complement conv_dist_comp conv_dist_inf conv_involutive conv_complement conv_top conv_bot)

text \<open>Theorem 10.3\<close>

lemma acyclic_6_implies_5a:
  "acyclic_6 x \<Longrightarrow> acyclic_5a x"
proof -
  assume "acyclic_6 x"
  from this obtain y where 1: "y \<squnion> y\<^sup>T = x \<and> acyclic y \<and> injective y"
    using acyclic_6_def by auto
  show "acyclic_5a x"
  proof (unfold acyclic_5a_def, rule allI, rule impI)
    fix z
    assume "z \<le> x"
    hence 2: "z = (z \<sqinter> y) \<squnion> (z \<sqinter> y\<^sup>T)"
      by (metis 1 inf.orderE inf_sup_distrib1)
    hence 3: "z\<^sup>\<star> = (z \<sqinter> y\<^sup>T)\<^sup>\<star> * (z \<sqinter> y)\<^sup>\<star>"
      by (metis 1 cancel_separate_2)
    have "(x \<sqinter> -z)\<^sup>\<star> = ((y \<sqinter> -z) \<squnion> (y\<^sup>T \<sqinter> -z))\<^sup>\<star>"
      using 1 inf_sup_distrib2 by auto
    also have "... = (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star>"
      using 1 cancel_separate_2 inf_commute by auto
    finally have "z\<^sup>\<star> \<sqinter> (x \<sqinter> -z)\<^sup>\<star> = (y\<^sup>T \<sqinter> z)\<^sup>\<star> * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star>"
      using 3 inf_commute by simp
    also have "... = ((y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star>) \<squnion> ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star>)"
      by (smt inf.sup_monoid.add_commute inf_sup_distrib1 star.circ_loop_fixpoint sup_commute mult_assoc)
    also have "... = (1 \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star>) \<squnion> ((y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star>) \<squnion> ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star>)"
      by (metis inf_sup_distrib2 star_left_unfold_equal)
    also have "... \<le> 1"
    proof (intro sup_least)
      show "1 \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star> \<le> 1"
        by simp
      have "(y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star> = ((y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star>) \<squnion> ((y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>+)"
        by (metis inf_sup_distrib1 star.circ_back_loop_fixpoint star.circ_plus_same sup_commute mult_assoc)
      also have "... \<le> bot"
      proof (rule sup_least)
        have "(y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> \<le> y\<^sup>+ \<sqinter> y\<^sup>T\<^sup>\<star>"
          by (meson comp_inf.mult_isotone comp_isotone inf.cobounded1 star_isotone)
        also have "... = bot"
          using 1 by (smt acyclic_star_inf_conv inf.orderE inf.sup_monoid.add_assoc pseudo_complement star.left_plus_below_circ)
        finally show "(y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> \<le> bot"
          .
        have "(y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>+ \<le> top * (y \<sqinter> z) \<sqinter> top * (y \<sqinter> -z)"
          by (metis comp_associative comp_inf.mult_isotone star.circ_left_top star.circ_plus_same top_left_mult_increasing)
        also have "... = bot"
          using 1 by (simp add: top_injective_inf_complement)
        finally show "(y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>+ \<le> bot"
          .
      qed
      finally show "(y \<sqinter> z)\<^sup>+ \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star> \<le> 1"
        using bot_least le_bot by blast
      have "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star> = ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y \<sqinter> -z)\<^sup>\<star>) \<squnion> ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>+ * (y \<sqinter> -z)\<^sup>\<star>)"
        by (metis inf_sup_distrib1 star.circ_loop_fixpoint sup_commute mult_assoc)
      also have "... = ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> 1) \<squnion> ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y \<sqinter> -z)\<^sup>+) \<squnion> ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>+ * (y \<sqinter> -z)\<^sup>\<star>)"
        by (metis inf_sup_distrib1 star_left_unfold_equal)
      also have "... \<le> 1"
      proof (intro sup_least)
        show "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> 1 \<le> 1"
          by simp
        have "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y \<sqinter> -z)\<^sup>+ = ((y\<^sup>T \<sqinter> z)\<^sup>+ \<sqinter> (y \<sqinter> -z)\<^sup>+) \<squnion> ((y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>+ \<sqinter> (y \<sqinter> -z)\<^sup>+)"
          by (smt inf.sup_monoid.add_commute inf_sup_distrib1 star.circ_back_loop_fixpoint star.circ_plus_same sup_commute mult_assoc)
        also have "... \<le> bot"
        proof (rule sup_least)
          have "(y\<^sup>T \<sqinter> z)\<^sup>+ \<sqinter> (y \<sqinter> -z)\<^sup>+ \<le> y\<^sup>T\<^sup>+ \<sqinter> y\<^sup>+"
            by (meson comp_inf.mult_isotone comp_isotone inf.cobounded1 star_isotone)
          also have "... = bot"
            using 1 by (metis acyclic_asymmetric conv_inf_bot_iff conv_plus_commute star_sup_1 sup.idem mult_assoc)
          finally show "(y\<^sup>T \<sqinter> z)\<^sup>+ \<sqinter> (y \<sqinter> -z)\<^sup>+ \<le> bot"
            .
          have "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>+ \<sqinter> (y \<sqinter> -z)\<^sup>+ \<le> top * (y \<sqinter> z) \<sqinter> top * (y \<sqinter> -z)"
            by (smt comp_inf.mult_isotone comp_isotone inf.cobounded1 inf.orderE star.circ_plus_same top.extremum mult_assoc)
          also have "... = bot"
            using 1 by (simp add: top_injective_inf_complement)
          finally show "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>+ \<sqinter> (y \<sqinter> -z)\<^sup>+ \<le> bot"
            .
        qed
        finally show "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y \<sqinter> -z)\<^sup>+ \<le> 1"
          using bot_least le_bot by blast
        have "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>+ * (y \<sqinter> -z)\<^sup>\<star> \<le> (y\<^sup>T \<sqinter> z) * top \<sqinter> (y\<^sup>T \<sqinter> -z) * top"
          by (smt comp_inf.mult_isotone comp_isotone eq_iff top.extremum mult_assoc)
        also have "... = bot"
          using 1 by (simp add: top_injective_inf_complement_2)
        finally show "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>+ * (y \<sqinter> -z)\<^sup>\<star> \<le> 1"
          using bot_least le_bot by blast
      qed
      finally show "(y\<^sup>T \<sqinter> z)\<^sup>+ * (y \<sqinter> z)\<^sup>\<star> \<sqinter> (y\<^sup>T \<sqinter> -z)\<^sup>\<star> * (y \<sqinter> -z)\<^sup>\<star> \<le> 1"
        .
    qed
    finally show "z\<^sup>\<star> \<sqinter> (x \<sqinter> -z)\<^sup>\<star> = 1"
      by (simp add: antisym star.circ_reflexive)
  qed
qed

text \<open>Theorem 9.7\<close>

lemma acyclic_5b_implies_4:
  assumes "irreflexive x"
      and "acyclic_5b x"
    shows "acyclic_4 x"
proof (unfold acyclic_4_def, rule allI, rule impI)
  fix y
  assume "y \<le> x"
  hence "y\<^sup>\<star> \<sqinter> (x \<sqinter> -y)\<^sup>+ \<le> 1"
    using acyclic_5b_def assms(2) by blast
  hence "y\<^sup>\<star> \<sqinter> x \<sqinter> -y \<le> 1"
    by (smt inf.sup_left_divisibility inf.sup_monoid.add_assoc star.circ_mult_increasing)
  hence "y\<^sup>\<star> \<sqinter> x \<sqinter> -y = bot"
    by (smt assms(1) comp_inf.semiring.mult_zero_left inf.orderE inf.sup_monoid.add_assoc inf.sup_monoid.add_commute pseudo_complement)
  thus "x \<sqinter> y\<^sup>\<star> \<le> --y"
    using inf.sup_monoid.add_commute pseudo_complement by fastforce
qed

text \<open>Theorem 9\<close>

lemma acyclic_5a_5b:
  "acyclic_5a x \<longleftrightarrow> acyclic_5b x"
  by (simp add: acyclic_5a_def acyclic_5b_def star.circ_reflexive reflexive_inf_plus_star)

text \<open>Theorem 9\<close>

lemma acyclic_5a_5c:
  "acyclic_5a x \<longleftrightarrow> acyclic_5c x"
  by (metis acyclic_5a_def acyclic_5c_def inf_commute star.circ_reflexive reflexive_inf_plus_star)

text \<open>Theorem 9\<close>

lemma acyclic_5b_5d:
  "acyclic_5b x \<longleftrightarrow> acyclic_5d x"
proof -
  have "acyclic_5b x \<longleftrightarrow> (\<forall>y . y \<le> x \<longrightarrow> (y\<^sup>+ \<squnion> 1) \<sqinter> (x \<sqinter> -y)\<^sup>+ \<le> 1)"
    by (simp add: acyclic_5b_def star_left_unfold_equal sup_commute)
  also have "... \<longleftrightarrow> acyclic_5d x"
    by (simp add: inf_sup_distrib2 acyclic_5d_def)
  finally show ?thesis
    .
qed

lemma acyclic_5a_5e:
  "acyclic_5a x \<longleftrightarrow> acyclic_5e x"
proof
  assume 1: "acyclic_5a x"
  show "acyclic_5e x"
  proof (unfold acyclic_5e_def, intro allI, rule impI)
    fix y z
    assume 2: "y \<le> x \<and> z \<le> x \<and> y \<sqinter> z = bot"
    hence "z \<le> x \<sqinter> -y"
      using p_antitone_iff pseudo_complement by auto
    hence "y\<^sup>\<star> \<sqinter> z\<^sup>\<star> \<le> 1"
      using 1 2 by (metis acyclic_5a_def comp_inf.mult_isotone inf.cobounded1 inf.right_idem star_isotone)
    thus "y\<^sup>\<star> \<sqinter> z\<^sup>\<star> = 1"
      by (simp add: antisym star.circ_reflexive)
  qed
next
  assume 1: "acyclic_5e x"
  show "acyclic_5a x"
  proof (unfold acyclic_5a_def, rule allI, rule impI)
    fix y
    let ?z = "x \<sqinter> -y"
    assume 2: "y \<le> x"
    have "y \<sqinter> ?z = bot"
      by (simp add: inf.left_commute)
    thus "y\<^sup>\<star> \<sqinter> ?z\<^sup>\<star> = 1"
      using 1 2 by (simp add: acyclic_5e_def)
  qed
qed

text \<open>Theorem 9\<close>

lemma acyclic_5e_5f:
  "acyclic_5e x \<longleftrightarrow> acyclic_5f x"
  by (simp add: acyclic_5e_def acyclic_5f_def)

lemma acyclic_5e_down_closed:
  assumes "x \<le> y"
      and "acyclic_5e y"
    shows "acyclic_5e x"
  using assms acyclic_5e_def order.trans by blast

lemma acyclic_5a_down_closed:
  assumes "x \<le> y"
      and "acyclic_5a y"
    shows "acyclic_5a x"
  using acyclic_5e_down_closed assms acyclic_5a_5e by blast

text \<open>further variants of the existence of a linear order\<close>

abbreviation "linear_orderable_4 x \<equiv> transitive x \<and> acyclic x \<and> strict_linear x"
abbreviation "linear_orderable_5 x \<equiv> transitive x \<and> acyclic x \<and> linear (x\<^sup>\<star>)"
abbreviation "linear_orderable_6 x \<equiv> acyclic x \<and> linear (x\<^sup>\<star>)"
abbreviation "linear_orderable_7 x \<equiv> split 1 (x\<^sup>\<star>) top"
abbreviation "linear_orderable_8 x \<equiv> split bot (x\<^sup>+) (-1)"

lemma linear_orderable_3_4:
  "linear_orderable_3 x \<longleftrightarrow> linear_orderable_4 x"
  using transitive_acyclic_asymmetric by blast

lemma linear_orderable_5_implies_6:
  "linear_orderable_5 x \<Longrightarrow> linear_orderable_6 x"
  by simp

lemma linear_orderable_6_implies_3:
  assumes "linear_orderable_6 x"
  shows "linear_orderable_3 (x\<^sup>+)"
proof -
  have 1: "transitive (x\<^sup>+)"
    by (simp add: comp_associative mult_isotone star.circ_mult_upper_bound star.left_plus_below_circ)
  have 2: "asymmetric (x\<^sup>+)"
    by (simp add: assms acyclic_asymmetric star.circ_transitive_equal star.left_plus_circ mult_assoc)
  have 3: "strict_linear (x\<^sup>+)"
    by (smt assms acyclic_star_inf_conv conv_star_commute inf.sup_monoid.add_commute inf_absorb2 maddux_3_13 orientable_11_implies_12 star_left_unfold_equal)
  show ?thesis
    using 1 2 3 by simp
qed

lemma linear_orderable_7_implies_1:
  "linear_orderable_7 x \<Longrightarrow> linear_orderable_1 (x\<^sup>\<star>)"
  using star.circ_transitive_equal by auto

lemma linear_orderable_6_implies_8:
  "linear_orderable_6 x \<Longrightarrow> linear_orderable_8 x"
  by (simp add: linear_orderable_6_implies_3)

abbreviation "path_orderable x \<equiv> univalent x \<and> injective x \<and> acyclic x \<and> linear (x\<^sup>\<star>)"

lemma path_orderable_implies_linear_orderable_6:
  "path_orderable x \<Longrightarrow> linear_orderable_6 x"
  by simp

definition "simple_paths x \<equiv> \<exists>y . y \<squnion> y\<^sup>T = x \<and> acyclic y \<and> injective y \<and> univalent y"

text \<open>Theorem 14.1\<close>

lemma simple_paths_acyclic_6:
  "simple_paths x \<Longrightarrow> acyclic_6 x"
  using simple_paths_def acyclic_6_def by blast

text \<open>Theorem 14.2\<close>

lemma simple_paths_transitively_orientable:
  assumes "simple_paths x"
  shows "transitively_orientable (x\<^sup>+ \<sqinter> -1)"
proof -
  from assms obtain y where 1: "y \<squnion> y\<^sup>T = x \<and> acyclic y \<and> injective y \<and> univalent y"
    using simple_paths_def by auto
  let ?y = "y\<^sup>+"
  have 2: "transitive ?y"
    by (simp add: comp_associative mult_right_isotone star.circ_mult_upper_bound star.left_plus_below_circ)
  have 3: "asymmetric ?y"
    using 1 acyclic_plus_asymmetric by auto
  have "?y \<squnion> ?y\<^sup>T = x\<^sup>+ \<sqinter> -1"
  proof (rule antisym)
    have 4: "?y \<le> x\<^sup>+"
      using 1 comp_isotone star_isotone by auto
    hence "?y\<^sup>T \<le> x\<^sup>+"
      using 1 by (metis conv_dist_sup conv_involutive conv_order conv_plus_commute sup_commute)
    thus "?y \<squnion> ?y\<^sup>T \<le> x\<^sup>+ \<sqinter> -1"
      using 1 4 by (simp add: irreflexive_conv_closed)
    have "x\<^sup>+ \<le> y\<^sup>\<star> \<squnion> y\<^sup>\<star>\<^sup>T"
      using 1 by (metis cancel_separate_1_sup conv_star_commute star.left_plus_below_circ)
    also have "... = ?y \<squnion> ?y\<^sup>T \<squnion> 1"
      by (smt conv_plus_commute conv_star_commute star.circ_reflexive star_left_unfold_equal sup.absorb1 sup_assoc sup_monoid.add_commute)
    finally show "x\<^sup>+ \<sqinter> -1 \<le> ?y \<squnion> ?y\<^sup>T"
      by (metis inf.order_lesseq_imp inf.sup_monoid.add_commute inf.sup_right_isotone p_inf_sup_below sup_commute)
  qed
  thus ?thesis
    using 2 3 transitively_orientable_def by auto
qed

abbreviation "spanning x y \<equiv> y \<le> x \<and> x \<le> (y \<squnion> y\<^sup>T)\<^sup>\<star> \<and> acyclic y \<and> injective y"
definition "spannable x \<equiv> \<exists>y . spanning x y"

lemma acyclic_6_implies_spannable:
  "acyclic_6 x \<Longrightarrow> spannable x"
  by (metis acyclic_6_def star.circ_increasing sup.cobounded1 spannable_def)

lemma acyclic_3a_spannable_implies_6:
  assumes "acyclic_3a x"
      and "spannable x"
      and "symmetric x"
    shows "acyclic_6 x"
  by (smt acyclic_6_def acyclic_3a_def assms conv_isotone le_supI spannable_def)

text \<open>Theorem 10.3\<close>

lemma acyclic_6_implies_3a:
  "acyclic_6 x \<Longrightarrow> acyclic_3a x"
  by (simp add: acyclic_6_implies_4a acyclic_4a_implies_3a)

text \<open>Theorem 10.3\<close>

lemma acyclic_6_implies_2:
  "acyclic_6 x \<Longrightarrow> acyclic_2 x"
  by (simp add: acyclic_6_implies_4a acyclic_6_symmetric acyclic_4_implies_2 acyclic_4a_implies_4)

text \<open>Theorem 11\<close>

lemma acyclic_6_3a_spannable:
  "acyclic_6 x \<longleftrightarrow> symmetric x \<and> spannable x \<and> acyclic_3a x"
  using acyclic_6_implies_3a acyclic_3a_spannable_implies_6 acyclic_6_implies_spannable acyclic_6_symmetric by blast

end

context stone_kleene_relation_algebra
begin

text \<open>Theorem 11.3\<close>

lemma point_spanning:
  assumes "point p"
  shows "spanning (-1) (p \<sqinter> -1)"
        "spannable (-1)"
proof -
  let ?y = "p \<sqinter> -1"
  have 1: "injective ?y"
    by (simp add: assms injective_inf_closed)
  have "?y * ?y \<le> -1"
    using assms cancel_separate_5 inf.sup_monoid.add_commute vector_inf_comp by auto
  hence 2: "transitive ?y"
    by (simp add: assms vector_inf_comp)
  hence 3: "acyclic ?y"
    by (simp add: transitive_acyclic_irreflexive)
  have 4: "p \<le> ?y \<squnion> 1"
    by (simp add: regular_complement_top sup_commute sup_inf_distrib1)
  have "top = p\<^sup>T * p"
    using assms inf.eq_iff shunt_bijective top_greatest vector_conv_covector by blast
  also have "... \<le> (?y \<squnion> 1)\<^sup>T * (?y \<squnion> 1)"
    using 4 by (simp add: conv_isotone mult_isotone)
  also have "... = (?y \<squnion> ?y\<^sup>T)\<^sup>\<star>"
    using 1 2 by (smt antisym cancel_separate_1 conv_star_commute star.circ_mult_1 star.circ_mult_increasing star.right_plus_circ star_right_induct_mult sup_commute)
  finally have "-1 \<le> (?y \<squnion> ?y\<^sup>T)\<^sup>\<star>"
    using top.extremum top_le by blast
  thus "spanning (-1) (p \<sqinter> -1)"
    using 1 3 inf.cobounded2 by blast
  thus "spannable (-1)"
    using spannable_def by blast
qed

(* move to Kleene_Relation_Algebras *)
lemma irreflexive_star:
  "(x \<sqinter> -1)\<^sup>\<star> = x\<^sup>\<star>"
proof -
  have 1: "x \<sqinter> 1 \<le> (x \<sqinter> -1)\<^sup>\<star>"
    by (simp add: le_infI2 star.circ_reflexive)
  have "x \<sqinter> -1 \<le> (x \<sqinter> -1)\<^sup>\<star>"
    by (simp add: star.circ_increasing)
  hence "x \<le> (x \<sqinter> -1)\<^sup>\<star>"
    using 1 by (smt maddux_3_11_pp regular_one_closed sup.absorb_iff1 sup_assoc)
  thus ?thesis
    by (metis antisym inf.cobounded1 star_involutive star_isotone)
qed

text \<open>Theorem 6.5\<close>

lemma acyclic_2_1:
  assumes "orientable x"
  shows "acyclic_2 x \<longleftrightarrow> acyclic_1 x"
proof
  assume "acyclic_2 x"
  thus "acyclic_1 x"
    using acyclic_2_implies_1 by blast
next
  assume 1: "acyclic_1 x"
  obtain y where 2: "orientation x y \<and> symmetric x"
    using assms orientable_def orientable_symmetric by blast
  show "acyclic_2 x"
  proof (unfold acyclic_2_def, rule allI, rule impI)
    fix z
    assume 3: "z \<le> x \<and> asymmetric z"
    let ?z = "(--z \<sqinter> x) \<squnion> (-(z \<squnion> z\<^sup>T) \<sqinter> y)"
    have "orientation x ?z"
    proof
      have "?z \<squnion> ?z\<^sup>T = ((--z \<squnion> --z\<^sup>T) \<sqinter> x) \<squnion> (-(z \<squnion> z\<^sup>T) \<sqinter> (y \<squnion> y\<^sup>T))"
        by (smt 2 3 comp_inf.semiring.combine_common_factor conv_complement conv_dist_inf conv_dist_sup inf_sup_distrib1 orientation_symmetric sup.left_commute sup_assoc)
      also have "... = x"
        by (metis 2 inf_commute maddux_3_11_pp pp_dist_sup sup_monoid.add_commute)
      finally show "?z \<squnion> ?z\<^sup>T = x"
        .
      have "?z \<sqinter> ?z\<^sup>T = ((--z \<sqinter> x) \<squnion> (-(z \<squnion> z\<^sup>T) \<sqinter> y)) \<sqinter> ((--z\<^sup>T \<sqinter> x) \<squnion> (-(z \<squnion> z\<^sup>T) \<sqinter> y\<^sup>T))"
        by (simp add: 2 conv_complement conv_dist_inf conv_dist_sup inf.sup_monoid.add_commute)
      also have "... = ((--z \<sqinter> x) \<sqinter> (--z\<^sup>T \<sqinter> x)) \<squnion> ((--z \<sqinter> x) \<sqinter> (-(z \<squnion> z\<^sup>T) \<sqinter> y\<^sup>T)) \<squnion> ((-(z \<squnion> z\<^sup>T) \<sqinter> y) \<sqinter> (--z\<^sup>T \<sqinter> x)) \<squnion> ((-(z \<squnion> z\<^sup>T) \<sqinter> y) \<sqinter> (-(z \<squnion> z\<^sup>T) \<sqinter> y\<^sup>T))"
        by (smt comp_inf.semiring.distrib_left inf_sup_distrib2 sup_assoc)
      also have "... = bot"
        by (smt 2 3 inf.cobounded1 inf.left_commute inf.orderE p_dist_sup pseudo_complement sup.absorb_iff1)
      finally show "?z \<sqinter> ?z\<^sup>T = bot"
        .
    qed
    hence 4: "acyclic ?z"
      using 1 acyclic_1_def by auto
    have "z \<le> ?z"
      by (simp add: 3 le_supI1 pp_increasing)
    thus "acyclic z"
      using 4 comp_isotone star_isotone by fastforce
  qed
qed

text \<open>Theorem 8\<close>

lemma acyclic_4_4c:
  "acyclic_4 x \<longleftrightarrow> acyclic_4c x"
proof
  assume 1: "acyclic_4 x"
  show "acyclic_4c x"
  proof (unfold acyclic_4c_def, rule allI, rule impI)
    fix y
    assume 2: "y \<le> x"
    have "x \<sqinter> (x \<sqinter> -y)\<^sup>\<star> \<le> --(x \<sqinter> -y)"
      using 1 acyclic_4_def inf.cobounded1 by blast
    also have "... \<le> -y"
      by simp
    finally have "x \<sqinter> y \<sqinter> (x \<sqinter> -y)\<^sup>\<star> = bot"
      by (simp add: p_shunting_swap pseudo_complement)
    thus "y \<sqinter> (x \<sqinter> -y)\<^sup>\<star> = bot"
      using 2 inf_absorb2 by auto
  qed
next
  assume 3: "acyclic_4c x"
  show "acyclic_4 x"
  proof (unfold acyclic_4_def, rule allI, rule impI)
    fix y
    assume 4: "y \<le> x"
    have "x \<sqinter> -y \<sqinter> (x \<sqinter> -(x \<sqinter> -y))\<^sup>\<star> = bot"
      using 3 acyclic_4c_def inf_le1 by blast
    hence "x \<sqinter> -y \<sqinter> (x \<sqinter> --y)\<^sup>\<star> = bot"
      using inf_import_p by auto
    hence "x \<sqinter> -y \<sqinter> (x \<sqinter> y)\<^sup>\<star> = bot"
      by (smt p_inf_pp pp_dist_star pp_pp_inf_bot_iff)
    hence "x \<sqinter> -y \<sqinter> y\<^sup>\<star> = bot"
      using 4 inf_absorb2 by auto
    thus "x \<sqinter> y\<^sup>\<star> \<le> --y"
      using p_shunting_swap pseudo_complement by auto
  qed
qed

text \<open>Theorem 9\<close>

lemma acyclic_5f_5g:
  "acyclic_5f x \<longleftrightarrow> acyclic_5g x"
proof
  assume "acyclic_5f x"
  thus "acyclic_5g x"
    using acyclic_5f_def acyclic_5g_def by auto
next
  assume 1: "acyclic_5g x"
  show "acyclic_5f x"
  proof (unfold acyclic_5f_def, intro allI, rule impI)
    fix y z
    let ?y = "x \<sqinter> --y"
    let ?z = "x \<sqinter> -y"
    assume "y \<squnion> z \<le> x \<and> y \<sqinter> z = bot"
    hence "y \<le> ?y \<and> z \<le> ?z"
      using inf.sup_monoid.add_commute pseudo_complement by fastforce
    hence "y\<^sup>\<star> \<sqinter> z\<^sup>\<star> \<le> ?y\<^sup>\<star> \<sqinter> ?z\<^sup>\<star>"
      using comp_inf.mult_isotone star_isotone by blast
    also have "... = 1"
      using 1 by (simp add: acyclic_5g_def inf.left_commute inf.sup_monoid.add_commute maddux_3_11_pp)
    finally show "y\<^sup>\<star> \<sqinter> z\<^sup>\<star> = 1"
      by (simp add: antisym star.circ_reflexive)
  qed
qed

lemma linear_orderable_3_implies_5:
  assumes "linear_orderable_3 x"
  shows "linear_orderable_5 x"
proof -
  have "top = x \<squnion> x\<^sup>T \<squnion> 1"
    using assms conv_dist_sup orientable_12_implies_11 sup_assoc sup_commute by fastforce
  also have "... \<le> x\<^sup>\<star> \<squnion> x\<^sup>\<star>\<^sup>T"
    by (smt conv_star_commute star.circ_increasing star_sup_one sup_assoc sup_commute sup_mono)
  finally show ?thesis
    by (simp add: assms top_le transitive_acyclic_asymmetric)
qed

lemma linear_orderable_8_implies_7:
  "linear_orderable_8 x \<Longrightarrow> linear_orderable_7 x"
  using orientable_12_implies_11 star_left_unfold_equal sup_commute by fastforce

text \<open>Theorem 13\<close>

lemma exists_split_characterisations_2:
  shows "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_4 x)"
  and "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_5 x)"
  and "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_6 x)"
  and "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_7 x)"
  and "(\<exists>x . linear_orderable_1 x) \<longleftrightarrow> (\<exists>x . linear_orderable_8 x)"
  subgoal 1 using exists_split_characterisations(1) strict_order_transitive_acyclic by auto
  subgoal 2 using 1 linear_orderable_3_implies_5 linear_orderable_6_implies_3 transitive_acyclic_asymmetric by auto
  subgoal 3 using 2 exists_split_characterisations(1) linear_orderable_6_implies_3 by auto
  subgoal using 2 linear_orderable_8_implies_7 linear_orderable_6_implies_3 linear_orderable_7_implies_1 by blast
  subgoal using 3 linear_orderable_8_implies_7 asymmetric_irreflexive linear_orderable_6_implies_3 by blast
  done

end

subsection \<open>Arc axiom\<close>

class stone_kleene_relation_algebra_arc = stone_kleene_relation_algebra +
  assumes arc_axiom: "x \<noteq> bot \<Longrightarrow> \<exists>y . arc y \<and> y \<le> --x"
begin

subclass stone_relation_algebra_tarski
proof unfold_locales
  fix x
  assume 1: "regular x" and 2: "x \<noteq> bot"
  from 2 obtain y where "arc y \<and> y \<le> --x"
    using arc_axiom by auto
  thus "top * x * top = top"
    using 1 by (metis mult_assoc le_iff_sup mult_left_isotone semiring.distrib_left sup.orderE top.extremum)
qed

context
  assumes orientable_path: "arc x \<Longrightarrow> x \<le> --y\<^sup>\<star> \<Longrightarrow> \<exists>z . z \<le> y \<and> asymmetric z \<and> x \<le> --z\<^sup>\<star>"
begin

text \<open>Theorem 8.6\<close>

lemma acyclic_2_4:
  assumes "irreflexive x"
      and "symmetric x"
    shows "acyclic_2 x \<longleftrightarrow> acyclic_4 x"
proof
  show "acyclic_2 x \<Longrightarrow> acyclic_4 x"
  proof (unfold acyclic_4_def, intro allI, intro impI, rule ccontr)
    fix y
    assume 1: "acyclic_2 x" and 2: "y \<le> x" and 3: "\<not> x \<sqinter> y\<^sup>\<star> \<le> --y"
    hence "x \<sqinter> y\<^sup>\<star> \<sqinter> -y \<noteq> bot"
      by (simp add: pseudo_complement)
    from this obtain z where 4: "arc z \<and> z \<le> --(x \<sqinter> y\<^sup>\<star> \<sqinter> -y)"
      using arc_axiom by blast
    from this obtain w where 5: "w \<le> y \<and> asymmetric w \<and> z \<le> --w\<^sup>\<star>"
      using orientable_path by auto
    let ?y = "w \<squnion> (z\<^sup>T \<sqinter> x)"
    have 6: "?y \<le> x"
      using 2 5 by auto
    have "?y \<sqinter> ?y\<^sup>T = (w \<sqinter> w\<^sup>T) \<squnion> (w \<sqinter> z \<sqinter> x\<^sup>T) \<squnion> (z\<^sup>T \<sqinter> x \<sqinter> w\<^sup>T) \<squnion> (z\<^sup>T \<sqinter> x \<sqinter> z \<sqinter> x\<^sup>T)"
      by (simp add: inf.commute sup.commute inf.left_commute sup.left_commute conv_dist_inf conv_dist_sup inf_sup_distrib1)
    also have "... \<le> bot"
    proof (intro sup_least)
      show "w \<sqinter> w\<^sup>T \<le> bot"
        by (simp add: 5)
      have "w \<sqinter> z \<sqinter> x\<^sup>T \<le> y \<sqinter> z"
        by (simp add: 5 inf.coboundedI1)
      also have "... \<le> y \<sqinter> -y"
        using 4 by (metis eq_refl inf.cobounded1 inf.left_commute inf.sup_monoid.add_commute inf_p order_trans pseudo_complement)
      finally show "w \<sqinter> z \<sqinter> x\<^sup>T \<le> bot"
        by simp
      thus "z\<^sup>T \<sqinter> x \<sqinter> w\<^sup>T \<le> bot"
        by (smt conv_dist_inf conv_inf_bot_iff inf.left_commute inf.sup_monoid.add_commute le_bot)
      have "irreflexive z"
        by (meson 4 assms(1) dual_order.trans irreflexive_complement_reflexive irreflexive_inf_closed reflexive_complement_irreflexive)
      hence "asymmetric z"
        using 4 by (simp add: pseudo_complement irreflexive_inf_arc_asymmetric)
      thus "z\<^sup>T \<sqinter> x \<sqinter> z \<sqinter> x\<^sup>T \<le> bot"
        by (simp add: inf.left_commute inf.sup_monoid.add_commute)
    qed
    finally have "acyclic ?y"
      using 1 6 by (simp add: le_bot acyclic_2_def)
    hence "?y\<^sup>\<star> \<sqinter> ?y\<^sup>T = bot"
      using acyclic_star_below_complement_1 by blast
    hence "w\<^sup>\<star> \<sqinter> ?y\<^sup>T = bot"
      using dual_order.trans pseudo_complement star.circ_sub_dist by blast
    hence "w\<^sup>\<star> \<sqinter> z \<sqinter> x\<^sup>T = bot"
      by (simp add: comp_inf.semiring.distrib_left conv_dist_inf conv_dist_sup inf.sup_monoid.add_assoc)
    hence "z \<sqinter> x\<^sup>T = bot"
      using 5 by (metis comp_inf.p_pp_comp inf.absorb2 pp_pp_inf_bot_iff)
    hence "z \<sqinter> --x = bot"
      using assms(2) pseudo_complement by auto
    hence "z = bot"
      using 4 inf.orderE by auto
    thus "False"
      using 3 4 comp_inf.coreflexive_pseudo_complement inf_bot_right by auto
  qed
next
  show "acyclic_4 x \<Longrightarrow> acyclic_2 x"
    by (simp add: assms(2) acyclic_4_implies_2)
qed

end

end

context kleene_relation_algebra
begin

text \<open>Theorem 8\<close>

lemma acyclic_3a_implies_4b:
  assumes "acyclic_3a x"
    shows "acyclic_4b x"
proof (unfold acyclic_4b_def, rule allI, rule impI)
  fix y
  let ?y = "(x \<sqinter> -y\<^sup>\<star>) \<squnion> y"
  assume 1: "y \<le> x"
  have "x = (x \<sqinter> -y\<^sup>\<star>) \<squnion> (x \<sqinter> y\<^sup>\<star>)"
    by simp
  also have "... \<le> ?y \<squnion> y\<^sup>\<star>"
    using shunting_var by fastforce
  also have "... \<le> ?y\<^sup>\<star>"
    by (simp add: star.circ_increasing star.circ_sub_dist sup_commute)
  finally have "?y = x"
    using 1 assms acyclic_3a_def by simp
  hence "x \<sqinter> y\<^sup>\<star> = y \<sqinter> y\<^sup>\<star>"
    by (smt (z3) inf.sup_monoid.add_commute inf_sup_absorb inf_sup_distrib2 maddux_3_13 sup_commute sup_inf_absorb)
  thus "x \<sqinter> y\<^sup>\<star> = y"
    by (simp add: inf_absorb1 star.circ_increasing)
qed

lemma acyclic_3a_4b:
  "acyclic_3a x \<longleftrightarrow> acyclic_4b x"
  using acyclic_3a_implies_4b acyclic_4a_4b acyclic_4a_implies_3a by blast

lemma acyclic_4_4a:
  "acyclic_4 x \<longleftrightarrow> acyclic_4a x"
  by (simp add: acyclic_4_def acyclic_4a_def)

subsection \<open>Counterexamples\<close>

text \<open>
Calls to nitpick have been put into comments to save processing time.
\<close>

text \<open>independence of (0)\<close>

lemma "symmetric x \<Longrightarrow> irreflexive_inf x \<Longrightarrow> orientable x"
  text \<open>nitpick[expect=genuine,card=4,timeout=600]\<close>
  oops

lemma "linear_orderable_6 x \<Longrightarrow> path_orderable x"
  text \<open>nitpick[expect=genuine,card=8,timeout=600]\<close>
  oops

text \<open>(5) does not imply (6)\<close>

lemma "symmetric x \<Longrightarrow> irreflexive x \<Longrightarrow> acyclic_5a x \<Longrightarrow> acyclic_6 x"
  text \<open>nitpick[expect=genuine,card=4,timeout=600]\<close>
  oops

text \<open>(2) does not imply (4)\<close>

lemma "symmetric x \<Longrightarrow> irreflexive x \<Longrightarrow> acyclic_2 x \<Longrightarrow> acyclic_4 x"
  text \<open>nitpick[expect=genuine,card=8,timeout=600]\<close>
  oops

end

end

