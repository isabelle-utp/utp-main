(* Title:      Kruskal's Minimum Spanning Tree Algorithm
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Kruskal's Minimum Spanning Tree Algorithm\<close>

text \<open>
In this theory we prove total correctness of Kruskal's minimum spanning tree algorithm.
The proof uses the following steps \cite{Guttmann2018c}.
We first establish that the algorithm terminates and constructs a spanning tree.
This is a constructive proof of the existence of a spanning tree; any spanning tree algorithm could be used for this.
We then conclude that a minimum spanning tree exists.
This is necessary to establish the invariant for the actual correctness proof, which shows that Kruskal's algorithm produces a minimum spanning tree.
\<close>

theory Kruskal

imports "HOL-Hoare.Hoare_Logic" Aggregation_Algebras.Aggregation_Algebras

begin

context m_kleene_algebra
begin

definition "spanning_forest f g \<equiv> forest f \<and> f \<le> --g \<and> components g \<le> forest_components f \<and> regular f"
definition "minimum_spanning_forest f g \<equiv> spanning_forest f g \<and> (\<forall>u . spanning_forest u g \<longrightarrow> sum (f \<sqinter> g) \<le> sum (u \<sqinter> g))"
definition "kruskal_spanning_invariant f g h \<equiv> symmetric g \<and> h = h\<^sup>T \<and> g \<sqinter> --h = h \<and> spanning_forest f (-h \<sqinter> g)"
definition "kruskal_invariant f g h \<equiv> kruskal_spanning_invariant f g h \<and> (\<exists>w . minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T)"

text \<open>
We first show two verification conditions which are used in both correctness proofs.
\<close>

lemma kruskal_vc_1:
  assumes "symmetric g"
    shows "kruskal_spanning_invariant bot g g"
proof (unfold kruskal_spanning_invariant_def, intro conjI)
  show "symmetric g"
    using assms by simp
next
  show "g = g\<^sup>T"
    using assms by simp
next
  show "g \<sqinter> --g = g"
    using inf.sup_monoid.add_commute selection_closed_id by simp
next
  show "spanning_forest bot (-g \<sqinter> g)"
    using star.circ_transitive_equal spanning_forest_def by simp
qed

lemma kruskal_vc_2:
  assumes "kruskal_spanning_invariant f g h"
      and "h \<noteq> bot"
    shows "(minarc h \<le> -forest_components f \<longrightarrow> kruskal_spanning_invariant ((f \<sqinter> -(top * minarc h * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * minarc h * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> minarc h) g (h \<sqinter> -minarc h \<sqinter> -minarc h\<^sup>T)
                                               \<and> card { x . regular x \<and> x \<le> --h \<and> x \<le> -minarc h \<and> x \<le> -minarc h\<^sup>T } < card { x . regular x \<and> x \<le> --h }) \<and>
           (\<not> minarc h \<le> -forest_components f \<longrightarrow> kruskal_spanning_invariant f g (h \<sqinter> -minarc h \<sqinter> -minarc h\<^sup>T)
                                                 \<and> card { x . regular x \<and> x \<le> --h \<and> x \<le> -minarc h \<and> x \<le> -minarc h\<^sup>T } < card { x . regular x \<and> x \<le> --h })"
proof -
  let ?e = "minarc h"
  let ?f = "(f \<sqinter> -(top * ?e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> ?e"
  let ?h = "h \<sqinter> -?e \<sqinter> -?e\<^sup>T"
  let ?F = "forest_components f"
  let ?n1 = "card { x . regular x \<and> x \<le> --h }"
  let ?n2 = "card { x . regular x \<and> x \<le> --h \<and> x \<le> -?e \<and> x \<le> -?e\<^sup>T }"
  have 1: "regular f \<and> regular ?e"
    by (metis assms(1) kruskal_spanning_invariant_def spanning_forest_def minarc_regular)
  hence 2: "regular ?f \<and> regular ?F \<and> regular (?e\<^sup>T)"
    using regular_closed_star regular_conv_closed regular_mult_closed by simp
  have 3: "\<not> ?e \<le> -?e"
    using assms(2) inf.orderE minarc_bot_iff by fastforce
  have 4: "?n2 < ?n1"
    apply (rule psubset_card_mono)
    using finite_regular apply simp
    using 1 3 kruskal_spanning_invariant_def minarc_below by auto
  show "(?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant ?f g ?h \<and> ?n2 < ?n1) \<and> (\<not> ?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant f g ?h \<and> ?n2 < ?n1)"
  proof (rule conjI)
    have 5: "injective ?f"
      apply (rule kruskal_injective_inv)
      using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
      apply (simp add: covector_mult_closed)
      apply (simp add: comp_associative comp_isotone star.right_plus_below_circ)
      apply (meson mult_left_isotone order_lesseq_imp star_outer_increasing top.extremum)
      using assms(1,2) kruskal_spanning_invariant_def kruskal_injective_inv_2 minarc_arc spanning_forest_def apply simp
      using assms(2) arc_injective minarc_arc apply blast
      using assms(1,2) kruskal_spanning_invariant_def kruskal_injective_inv_3 minarc_arc spanning_forest_def by simp
    show "?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant ?f g ?h \<and> ?n2 < ?n1"
    proof
      assume 6: "?e \<le> -?F"
      have 7: "equivalence ?F"
        using assms(1) kruskal_spanning_invariant_def forest_components_equivalence spanning_forest_def by simp
      have "?e\<^sup>T * top * ?e\<^sup>T = ?e\<^sup>T"
        using assms(2) by (simp add: arc_top_arc minarc_arc)
      hence "?e\<^sup>T * top * ?e\<^sup>T \<le> -?F"
        using 6 7 conv_complement conv_isotone by fastforce
      hence 8: "?e * ?F * ?e = bot"
        using le_bot triple_schroeder_p by simp
      show "kruskal_spanning_invariant ?f g ?h \<and> ?n2 < ?n1"
      proof (unfold kruskal_spanning_invariant_def, intro conjI)
        show "symmetric g"
          using assms(1) kruskal_spanning_invariant_def by simp
      next
        show "?h = ?h\<^sup>T"
          using assms(1) by (simp add: conv_complement conv_dist_inf inf_commute inf_left_commute kruskal_spanning_invariant_def)
      next
        show "g \<sqinter> --?h = ?h"
          using 1 2 by (metis (hide_lams) assms(1) kruskal_spanning_invariant_def inf_assoc pp_dist_inf)
      next
        show "spanning_forest ?f (-?h \<sqinter> g)"
        proof (unfold spanning_forest_def, intro conjI)
          show "injective ?f"
            using 5 by simp
        next
          show "acyclic ?f"
            apply (rule kruskal_acyclic_inv)
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
            apply (simp add: covector_mult_closed)
            using 8 assms(1) kruskal_spanning_invariant_def spanning_forest_def kruskal_acyclic_inv_1 apply simp
            using 8 apply (metis comp_associative mult_left_sub_dist_sup_left star.circ_loop_fixpoint sup_commute le_bot)
            using 6 by (simp add: p_antitone_iff)
        next
          show "?f \<le> --(-?h \<sqinter> g)"
            apply (rule kruskal_subgraph_inv)
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
            using assms(1) apply (metis kruskal_spanning_invariant_def minarc_below order.trans pp_isotone_inf)
            using assms(1) kruskal_spanning_invariant_def apply simp
            using assms(1) kruskal_spanning_invariant_def by simp
        next
          show "components (-?h \<sqinter> g) \<le> forest_components ?f"
            apply (rule kruskal_spanning_inv)
            using 5 apply simp
            using 1 regular_closed_star regular_conv_closed regular_mult_closed apply simp
            using 1 apply simp
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
        next
          show "regular ?f"
            using 2 by simp
        qed
      next
        show "?n2 < ?n1"
          using 4 by simp
      qed
    qed
  next
    show "\<not> ?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant f g ?h \<and> ?n2 < ?n1"
    proof
      assume "\<not> ?e \<le> -?F"
      hence 9: "?e \<le> ?F"
        using 2 assms(2) arc_in_partition minarc_arc by fastforce
      show "kruskal_spanning_invariant f g ?h \<and> ?n2 < ?n1"
      proof (unfold kruskal_spanning_invariant_def, intro conjI)
        show "symmetric g"
          using assms(1) kruskal_spanning_invariant_def by simp
      next
        show "?h = ?h\<^sup>T"
          using assms(1) by (simp add: conv_complement conv_dist_inf inf_commute inf_left_commute kruskal_spanning_invariant_def)
      next
        show "g \<sqinter> --?h = ?h"
          using 1 2 by (metis (hide_lams) assms(1) kruskal_spanning_invariant_def inf_assoc pp_dist_inf)
      next
        show "spanning_forest f (-?h \<sqinter> g)"
        proof (unfold spanning_forest_def, intro conjI)
          show "injective f"
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
        next
          show "acyclic f"
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
        next
          have "f \<le> --(-h \<sqinter> g)"
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def by simp
          also have "... \<le> --(-?h \<sqinter> g)"
            using comp_inf.mult_right_isotone inf.sup_monoid.add_commute inf_left_commute p_antitone_inf pp_isotone by presburger
          finally show "f \<le> --(-?h \<sqinter> g)"
            by simp
        next
          show "components (-?h \<sqinter> g) \<le> ?F"
            apply (rule kruskal_spanning_inv_1)
            using 9 apply simp
            using 1 apply simp
            using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
            using assms(1) kruskal_spanning_invariant_def forest_components_equivalence spanning_forest_def by simp
        next
          show "regular f"
            using 1 by simp
        qed
      next
        show "?n2 < ?n1"
          using 4 by simp
      qed
    qed
  qed
qed

text \<open>
The following result shows that Kruskal's algorithm terminates and constructs a spanning tree.
We cannot yet show that this is a minimum spanning tree.
\<close>

theorem kruskal_spanning:
  "VARS e f h
  [ symmetric g ]
  f := bot;
  h := g;
  WHILE h \<noteq> bot
    INV { kruskal_spanning_invariant f g h }
    VAR { card { x . regular x \<and> x \<le> --h } }
     DO e := minarc h;
        IF e \<le> -forest_components f THEN
          f := (f \<sqinter> -(top * e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> e
        ELSE
          SKIP
        FI;
        h := h \<sqinter> -e \<sqinter> -e\<^sup>T
     OD
  [ spanning_forest f g ]"
  apply vcg_tc_simp
  using kruskal_vc_1 apply simp
  using kruskal_vc_2 apply simp
  using kruskal_spanning_invariant_def by auto

text \<open>
Because we have shown total correctness, we conclude that a spanning tree exists.
\<close>

lemma kruskal_exists_spanning:
  "symmetric g \<Longrightarrow> \<exists>f . spanning_forest f g"
  using tc_extract_function kruskal_spanning by blast

text \<open>
This implies that a minimum spanning tree exists, which is used in the subsequent correctness proof.
\<close>

lemma kruskal_exists_minimal_spanning:
  assumes "symmetric g"
    shows "\<exists>f . minimum_spanning_forest f g"
proof -
  let ?s = "{ f . spanning_forest f g }"
  have "\<exists>m\<in>?s . \<forall>z\<in>?s . sum (m \<sqinter> g) \<le> sum (z \<sqinter> g)"
    apply (rule finite_set_minimal)
    using finite_regular spanning_forest_def apply simp
    using assms kruskal_exists_spanning apply simp
    using sum_linear by simp
  thus ?thesis
    using minimum_spanning_forest_def by simp
qed

text \<open>
Kruskal's minimum spanning tree algorithm terminates and is correct.
This is the same algorithm that is used in the previous correctness proof, with the same precondition and variant, but with a different invariant and postcondition.
\<close>

theorem kruskal:
  "VARS e f h
  [ symmetric g ]
  f := bot;
  h := g;
  WHILE h \<noteq> bot
    INV { kruskal_invariant f g h }
    VAR { card { x . regular x \<and> x \<le> --h } }
     DO e := minarc h;
        IF e \<le> -forest_components f THEN
          f := (f \<sqinter> -(top * e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> e
        ELSE
          SKIP
        FI;
        h := h \<sqinter> -e \<sqinter> -e\<^sup>T
     OD
  [ minimum_spanning_forest f g ]"
proof vcg_tc_simp
  assume "symmetric g"
  thus "kruskal_invariant bot g g"
    using kruskal_vc_1 kruskal_exists_minimal_spanning kruskal_invariant_def by simp
next
  fix f h
  let ?e = "minarc h"
  let ?f = "(f \<sqinter> -(top * ?e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> ?e"
  let ?h = "h \<sqinter> -?e \<sqinter> -?e\<^sup>T"
  let ?F = "forest_components f"
  let ?n1 = "card { x . regular x \<and> x \<le> --h }"
  let ?n2 = "card { x . regular x \<and> x \<le> --h \<and> x \<le> -?e \<and> x \<le> -?e\<^sup>T }"
  assume 1: "kruskal_invariant f g h \<and> h \<noteq> bot"
  from 1 obtain w where 2: "minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T"
    using kruskal_invariant_def by auto
  hence 3: "regular f \<and> regular w \<and> regular ?e"
    using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def minimum_spanning_forest_def spanning_forest_def minarc_regular)
  show "(?e \<le> -?F \<longrightarrow> kruskal_invariant ?f g ?h \<and> ?n2 < ?n1) \<and> (\<not> ?e \<le> -?F \<longrightarrow> kruskal_invariant f g ?h \<and> ?n2 < ?n1)"
  proof (rule conjI)
    show "?e \<le> -?F \<longrightarrow> kruskal_invariant ?f g ?h \<and> ?n2 < ?n1"
    proof
      assume 4: "?e \<le> -?F"
      have 5: "equivalence ?F"
        using 1 kruskal_invariant_def kruskal_spanning_invariant_def forest_components_equivalence spanning_forest_def by simp
      have "?e\<^sup>T * top * ?e\<^sup>T = ?e\<^sup>T"
        using 1 by (simp add: arc_top_arc minarc_arc)
      hence "?e\<^sup>T * top * ?e\<^sup>T \<le> -?F"
        using 4 5 conv_complement conv_isotone by fastforce
      hence 6: "?e * ?F * ?e = bot"
        using le_bot triple_schroeder_p by simp
      show "kruskal_invariant ?f g ?h \<and> ?n2 < ?n1"
      proof (unfold kruskal_invariant_def, intro conjI)
        show "kruskal_spanning_invariant ?f g ?h"
          using 1 4 kruskal_vc_2 kruskal_invariant_def by simp
      next
        show "\<exists>w . minimum_spanning_forest w g \<and> ?f \<le> w \<squnion> w\<^sup>T"
        proof
          let ?p = "w \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
          let ?v = "(w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>)) \<squnion> ?p\<^sup>T"
          have 7: "regular ?p"
            using 3 regular_closed_star regular_conv_closed regular_mult_closed by simp
          have 8: "injective ?v"
            apply (rule kruskal_exchange_injective_inv_1)
            using 2 minimum_spanning_forest_def spanning_forest_def apply simp
            apply (simp add: covector_mult_closed)
            apply (simp add: comp_associative comp_isotone star.right_plus_below_circ)
            using 1 2 kruskal_injective_inv_3 minarc_arc minimum_spanning_forest_def spanning_forest_def by simp
          have 9: "components g \<le> forest_components ?v"
            apply (rule kruskal_exchange_spanning_inv_1)
            using 8 apply simp
            using 7 apply simp
            using 2 minimum_spanning_forest_def spanning_forest_def by simp
          have 10: "spanning_forest ?v g"
          proof (unfold spanning_forest_def, intro conjI)
            show "injective ?v"
              using 8 by simp
          next
            show "acyclic ?v"
              apply (rule kruskal_exchange_acyclic_inv_1)
              using 2 minimum_spanning_forest_def spanning_forest_def apply simp
              by (simp add: covector_mult_closed)
          next
            show "?v \<le> --g"
              apply (rule sup_least)
              using 2 inf.coboundedI1 minimum_spanning_forest_def spanning_forest_def apply simp
              using 1 2 by (metis kruskal_invariant_def kruskal_spanning_invariant_def conv_complement conv_dist_inf order.trans inf.absorb2 inf.cobounded1 minimum_spanning_forest_def spanning_forest_def)
          next
            show "components g \<le> forest_components ?v"
              using 9 by simp
          next
            show "regular ?v"
              using 3 regular_closed_star regular_conv_closed regular_mult_closed by simp
          qed
          have 11: "sum (?v \<sqinter> g) = sum (w \<sqinter> g)"
          proof -
            have "sum (?v \<sqinter> g) = sum (w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>) \<sqinter> g) + sum (?p\<^sup>T \<sqinter> g)"
              using 2 by (metis conv_complement conv_top epm_8 inf_import_p inf_top_right regular_closed_top vector_top_closed minimum_spanning_forest_def spanning_forest_def sum_disjoint)
            also have "... = sum (w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>) \<sqinter> g) + sum (?p \<sqinter> g)"
              using 1 kruskal_invariant_def kruskal_spanning_invariant_def sum_symmetric by simp
            also have "... = sum (((w \<sqinter> -(top * ?e * w\<^sup>T\<^sup>\<star>)) \<squnion> ?p) \<sqinter> g)"
              using inf_commute inf_left_commute sum_disjoint by simp
            also have "... = sum (w \<sqinter> g)"
              using 3 7 maddux_3_11_pp by simp
            finally show ?thesis
              by simp
          qed
          have 12: "?v \<squnion> ?v\<^sup>T = w \<squnion> w\<^sup>T"
          proof -
            have "?v \<squnion> ?v\<^sup>T = (w \<sqinter> -?p) \<squnion> ?p\<^sup>T \<squnion> (w\<^sup>T \<sqinter> -?p\<^sup>T) \<squnion> ?p"
              using conv_complement conv_dist_inf conv_dist_sup inf_import_p sup_assoc by simp
            also have "... = w \<squnion> w\<^sup>T"
              using 3 7 conv_complement conv_dist_inf inf_import_p maddux_3_11_pp sup_monoid.add_assoc sup_monoid.add_commute by simp
            finally show ?thesis
              by simp
          qed
          have 13: "?v * ?e\<^sup>T = bot"
            apply (rule kruskal_reroot_edge)
            using 1 apply (simp add: minarc_arc)
            using 2 minimum_spanning_forest_def spanning_forest_def by simp
          have "?v \<sqinter> ?e \<le> ?v \<sqinter> top * ?e"
            using inf.sup_right_isotone top_left_mult_increasing by simp
          also have "... \<le> ?v * (top * ?e)\<^sup>T"
            using covector_restrict_comp_conv covector_mult_closed vector_top_closed by simp
          finally have 14: "?v \<sqinter> ?e = bot"
            using 13 by (metis conv_dist_comp mult_assoc le_bot mult_left_zero)
          let ?d = "?v \<sqinter> top * ?e\<^sup>T * ?v\<^sup>T\<^sup>\<star> \<sqinter> ?F * ?e\<^sup>T * top \<sqinter> top * ?e * -?F"
          let ?w = "(?v \<sqinter> -?d) \<squnion> ?e"
          have 15: "regular ?d"
            using 3 regular_closed_star regular_conv_closed regular_mult_closed by simp
          have 16: "?F \<le> -?d"
            apply (rule kruskal_edge_between_components_1)
            using 5 apply simp
            using 1 conv_dist_comp minarc_arc mult_assoc by simp
          have 17: "f \<squnion> f\<^sup>T \<le> (?v \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T)"
            apply (rule kruskal_edge_between_components_2)
            using 16 apply simp
            using 1 kruskal_invariant_def kruskal_spanning_invariant_def spanning_forest_def apply simp
            using 2 12 by (metis conv_dist_sup conv_involutive conv_isotone le_supI sup_commute)
          show "minimum_spanning_forest ?w g \<and> ?f \<le> ?w \<squnion> ?w\<^sup>T"
          proof (intro conjI)
            have 18: "?e\<^sup>T \<le> ?v\<^sup>\<star>"
              apply (rule kruskal_edge_arc_1[where g=g and h=h])
              using minarc_below apply simp
              using 1 apply (metis kruskal_invariant_def kruskal_spanning_invariant_def inf_le1)
              using 1 kruskal_invariant_def kruskal_spanning_invariant_def apply simp
              using 9 apply simp
              using 13 by simp
            have 19: "arc ?d"
              apply (rule kruskal_edge_arc)
              using 5 apply simp
              using 10 spanning_forest_def apply blast
              using 1 apply (simp add: minarc_arc)
              using 3 apply (metis conv_complement pp_dist_star regular_mult_closed)
              using 2 8 12 apply (simp add: kruskal_forest_components_inf)
              using 10 spanning_forest_def apply simp
              using 13 apply simp
              using 6 apply simp
              using 18 by simp
            show "minimum_spanning_forest ?w g"
            proof (unfold minimum_spanning_forest_def, intro conjI)
              have "(?v \<sqinter> -?d) * ?e\<^sup>T \<le> ?v * ?e\<^sup>T"
                using inf_le1 mult_left_isotone by simp
              hence "(?v \<sqinter> -?d) * ?e\<^sup>T = bot"
                using 13 le_bot by simp
              hence 20: "?e * (?v \<sqinter> -?d)\<^sup>T = bot"
                using conv_dist_comp conv_involutive conv_bot by force
              have 21: "injective ?w"
                apply (rule injective_sup)
                using 8 apply (simp add: injective_inf_closed)
                using 20 apply simp
                using 1 arc_injective minarc_arc by blast
              show "spanning_forest ?w g"
              proof (unfold spanning_forest_def, intro conjI)
                show "injective ?w"
                  using 21 by simp
              next
                show "acyclic ?w"
                  apply (rule kruskal_exchange_acyclic_inv_2)
                  using 10 spanning_forest_def apply blast
                  using 8 apply simp
                  using inf.coboundedI1 apply simp
                  using 19 apply simp
                  using 1 apply (simp add: minarc_arc)
                  using inf.cobounded2 inf.coboundedI1 apply simp
                  using 13 by simp
              next
                have "?w \<le> ?v \<squnion> ?e"
                  using inf_le1 sup_left_isotone by simp
                also have "... \<le> --g \<squnion> ?e"
                  using 10 sup_left_isotone spanning_forest_def by blast
                also have "... \<le> --g \<squnion> --h"
                  by (simp add: le_supI2 minarc_below)
                also have "... = --g"
                  using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def pp_isotone_inf sup.orderE)
                finally show "?w \<le> --g"
                  by simp
              next
                have 22: "?d \<le> (?v \<sqinter> -?d)\<^sup>T\<^sup>\<star> * ?e\<^sup>T * top"
                  apply (rule kruskal_exchange_spanning_inv_2)
                  using 8 apply simp
                  using 13 apply (metis semiring.mult_not_zero star_absorb star_simulation_right_equal)
                  using 17 apply simp
                  by (simp add: inf.coboundedI1)
                have "components g \<le> forest_components ?v"
                  using 10 spanning_forest_def by auto
                also have "... \<le> forest_components ?w"
                  apply (rule kruskal_exchange_forest_components_inv)
                  using 21 apply simp
                  using 15 apply simp
                  using 1 apply (simp add: arc_top_arc minarc_arc)
                  apply (simp add: inf.coboundedI1)
                  using 13 apply simp
                  using 8 apply simp
                  apply (simp add: le_infI1)
                  using 22 by simp
                finally show "components g \<le> forest_components ?w"
                  by simp
              next
                show "regular ?w"
                  using 3 7 regular_conv_closed by simp
              qed
            next
              have 23: "?e \<sqinter> g \<noteq> bot"
                using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def comp_inf.semiring.mult_zero_right inf.sup_monoid.add_assoc inf.sup_monoid.add_commute minarc_bot_iff minarc_meet_bot)
              have "g \<sqinter> -h \<le> (g \<sqinter> -h)\<^sup>\<star>"
                using star.circ_increasing by simp
              also have "... \<le> (--(g \<sqinter> -h))\<^sup>\<star>"
                using pp_increasing star_isotone by blast
              also have "... \<le> ?F"
                using 1 kruskal_invariant_def kruskal_spanning_invariant_def inf.sup_monoid.add_commute spanning_forest_def by simp
              finally have 24: "g \<sqinter> -h \<le> ?F"
                by simp
              have "?d \<le> --g"
                using 10 inf.coboundedI1 spanning_forest_def by blast
              hence "?d \<le> --g \<sqinter> -?F"
                using 16 inf.boundedI p_antitone_iff by simp
              also have "... = --(g \<sqinter> -?F)"
                by simp
              also have "... \<le> --h"
                using 24 p_shunting_swap pp_isotone by fastforce
              finally have 25: "?d \<le> --h"
                by simp
              have "?d = bot \<longrightarrow> top = bot"
                using 19 by (metis mult_left_zero mult_right_zero)
              hence "?d \<noteq> bot"
                using 1 le_bot by auto
              hence 26: "?d \<sqinter> h \<noteq> bot"
                using 25 by (metis inf.absorb_iff2 inf_commute pseudo_complement)
              have "sum (?e \<sqinter> g) = sum (?e \<sqinter> --h \<sqinter> g)"
                by (simp add: inf.absorb1 minarc_below)
              also have "... = sum (?e \<sqinter> h)"
                using 1 by (metis kruskal_invariant_def kruskal_spanning_invariant_def inf.left_commute inf.sup_monoid.add_commute)
              also have "... \<le> sum (?d \<sqinter> h)"
                using 19 26 minarc_min by simp
              also have "... = sum (?d \<sqinter> (--h \<sqinter> g))"
                using 1 kruskal_invariant_def kruskal_spanning_invariant_def inf_commute by simp
              also have "... = sum (?d \<sqinter> g)"
                using 25 by (simp add: inf.absorb2 inf_assoc inf_commute)
              finally have 27: "sum (?e \<sqinter> g) \<le> sum (?d \<sqinter> g)"
                by simp
              have "?v \<sqinter> ?e \<sqinter> -?d = bot"
                using 14 by simp
              hence "sum (?w \<sqinter> g) = sum (?v \<sqinter> -?d \<sqinter> g) + sum (?e \<sqinter> g)"
                using sum_disjoint inf_commute inf_assoc by simp
              also have "... \<le> sum (?v \<sqinter> -?d \<sqinter> g) + sum (?d \<sqinter> g)"
                using 23 27 sum_plus_right_isotone by simp
              also have "... = sum (((?v \<sqinter> -?d) \<squnion> ?d) \<sqinter> g)"
                using sum_disjoint inf_le2 pseudo_complement by simp
              also have "... = sum ((?v \<squnion> ?d) \<sqinter> (-?d \<squnion> ?d) \<sqinter> g)"
                by (simp add: sup_inf_distrib2)
              also have "... = sum ((?v \<squnion> ?d) \<sqinter> g)"
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
              using conv_dist_inf inf_le1 sup_left_isotone sup_mono by presburger
            also have "... \<le> (?v \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> ?e"
              using 17 sup_left_isotone by simp
            also have "... \<le> (?v \<sqinter> -?d) \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T) \<squnion> ?e"
              using inf.cobounded1 sup_inf_distrib2 by presburger
            also have "... = ?w \<squnion> (?v\<^sup>T \<sqinter> -?d \<sqinter> -?d\<^sup>T)"
              by (simp add: sup_assoc sup_commute)
            also have "... \<le> ?w \<squnion> (?v\<^sup>T \<sqinter> -?d\<^sup>T)"
              using inf.sup_right_isotone inf_assoc sup_right_isotone by simp
            also have "... \<le> ?w \<squnion> ?w\<^sup>T"
              using conv_complement conv_dist_inf conv_dist_sup sup_right_isotone by simp
            finally show "?f \<le> ?w \<squnion> ?w\<^sup>T"
              by simp
          qed
        qed
      next
        show "?n2 < ?n1"
          using 1 kruskal_vc_2 kruskal_invariant_def by auto
      qed
    qed
  next
    show "\<not> ?e \<le> -?F \<longrightarrow> kruskal_invariant f g ?h \<and> ?n2 < ?n1"
      using 1 kruskal_vc_2 kruskal_invariant_def by auto
  qed
next
  fix f
  assume 28: "kruskal_invariant f g bot"
  hence 29: "spanning_forest f g"
    using kruskal_invariant_def kruskal_spanning_invariant_def by auto
  from 28 obtain w where 30: "minimum_spanning_forest w g \<and> f \<le> w \<squnion> w\<^sup>T"
    using kruskal_invariant_def by auto
  hence "w = w \<sqinter> --g"
    by (simp add: inf.absorb1 minimum_spanning_forest_def spanning_forest_def)
  also have "... \<le> w \<sqinter> components g"
    by (metis inf.sup_right_isotone star.circ_increasing)
  also have "... \<le> w \<sqinter> f\<^sup>T\<^sup>\<star> * f\<^sup>\<star>"
    using 29 spanning_forest_def inf.sup_right_isotone by simp
  also have "... \<le> f \<squnion> f\<^sup>T"
    apply (rule cancel_separate_6[where z=w and y="w\<^sup>T"])
    using 30 minimum_spanning_forest_def spanning_forest_def apply simp
    using 30 apply (metis conv_dist_inf conv_dist_sup conv_involutive inf.cobounded2 inf.orderE)
    using 30 apply (simp add: sup_commute)
    using 30 minimum_spanning_forest_def spanning_forest_def apply simp
    using 30 by (metis acyclic_star_below_complement comp_inf.mult_right_isotone inf_p le_bot minimum_spanning_forest_def spanning_forest_def)
  finally have 31: "w \<le> f \<squnion> f\<^sup>T"
    by simp
  have "sum (f \<sqinter> g) = sum ((w \<squnion> w\<^sup>T) \<sqinter> (f \<sqinter> g))"
    using 30 by (metis inf_absorb2 inf.assoc)
  also have "... = sum (w \<sqinter> (f \<sqinter> g)) + sum (w\<^sup>T \<sqinter> (f \<sqinter> g))"
    using 30 inf.commute acyclic_asymmetric sum_disjoint minimum_spanning_forest_def spanning_forest_def by simp
  also have "... = sum (w \<sqinter> (f \<sqinter> g)) + sum (w \<sqinter> (f\<^sup>T \<sqinter> g\<^sup>T))"
    by (metis conv_dist_inf conv_involutive sum_conv)
  also have "... = sum (f \<sqinter> (w \<sqinter> g)) + sum (f\<^sup>T \<sqinter> (w \<sqinter> g))"
    using 28 inf.commute inf.assoc kruskal_invariant_def kruskal_spanning_invariant_def by simp
  also have "... = sum ((f \<squnion> f\<^sup>T) \<sqinter> (w \<sqinter> g))"
    using 29 acyclic_asymmetric inf.sup_monoid.add_commute sum_disjoint spanning_forest_def by simp
  also have "... = sum (w \<sqinter> g)"
    using 31 by (metis inf_absorb2 inf.assoc)
  finally show "minimum_spanning_forest f g"
    using 29 30 minimum_spanning_forest_def by simp
qed

end

end

