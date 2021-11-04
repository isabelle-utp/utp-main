(* Title:      Prim's Minimum Spanning Tree Algorithm
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Prim's Minimum Spanning Tree Algorithm\<close>

text \<open>
In this theory we prove total correctness of Prim's minimum spanning tree algorithm.
The proof has the same overall structure as the total-correctness proof of Kruskal's algorithm \cite{Guttmann2018c}.
The partial-correctness proof of Prim's algorithm is discussed in \cite{Guttmann2016c,Guttmann2018b}.
\<close>

theory Prim

imports "HOL-Hoare.Hoare_Logic" Aggregation_Algebras.Aggregation_Algebras

begin

context m_kleene_algebra
begin

abbreviation "component g r \<equiv> r\<^sup>T * (--g)\<^sup>\<star>"
definition "spanning_tree t g r \<equiv> forest t \<and> t \<le> (component g r)\<^sup>T * (component g r) \<sqinter> --g \<and> component g r \<le> r\<^sup>T * t\<^sup>\<star> \<and> regular t"
definition "minimum_spanning_tree t g r \<equiv> spanning_tree t g r \<and> (\<forall>u . spanning_tree u g r \<longrightarrow> sum (t \<sqinter> g) \<le> sum (u \<sqinter> g))"
definition "prim_precondition g r \<equiv> g = g\<^sup>T \<and> injective r \<and> vector r \<and> regular r"
definition "prim_spanning_invariant t v g r \<equiv> prim_precondition g r \<and> v\<^sup>T = r\<^sup>T * t\<^sup>\<star> \<and> spanning_tree t (v * v\<^sup>T \<sqinter> g) r"
definition "prim_invariant t v g r \<equiv> prim_spanning_invariant t v g r \<and> (\<exists>w . minimum_spanning_tree w g r \<and> t \<le> w)"

lemma span_tree_split:
  assumes "vector r"
    shows "t \<le> (component g r)\<^sup>T * (component g r) \<sqinter> --g \<longleftrightarrow> (t \<le> (component g r)\<^sup>T \<and> t \<le> component g r \<and> t \<le> --g)"
proof -
  have "(component g r)\<^sup>T * (component g r) = (component g r)\<^sup>T \<sqinter> component g r"
    by (metis assms conv_involutive covector_mult_closed vector_conv_covector vector_covector)
  thus ?thesis
    by simp
qed

lemma span_tree_component:
  assumes "spanning_tree t g r"
    shows "component g r = component t r"
  using assms by (simp add: antisym mult_right_isotone star_isotone spanning_tree_def)

text \<open>
We first show three verification conditions which are used in both correctness proofs.
\<close>

lemma prim_vc_1:
  assumes "prim_precondition g r"
    shows "prim_spanning_invariant bot r g r"
proof (unfold prim_spanning_invariant_def, intro conjI)
  show "prim_precondition g r"
    using assms by simp
next
  show "r\<^sup>T = r\<^sup>T * bot\<^sup>\<star>"
    by (simp add: star_absorb)
next
  let ?ss = "r * r\<^sup>T \<sqinter> g"
  show "spanning_tree bot ?ss r"
  proof (unfold spanning_tree_def, intro conjI)
    show "injective bot"
      by simp
  next
    show "acyclic bot"
      by simp
  next
    show "bot \<le> (component ?ss r)\<^sup>T * (component ?ss r) \<sqinter> --?ss"
      by simp
  next
    have "component ?ss r \<le> component (r * r\<^sup>T) r"
      by (simp add: mult_right_isotone star_isotone)
    also have "... \<le> r\<^sup>T * 1\<^sup>\<star>"
      using assms by (metis inf.eq_iff p_antitone regular_one_closed star_sub_one prim_precondition_def)
    also have "... = r\<^sup>T * bot\<^sup>\<star>"
      by (simp add: star.circ_zero star_one)
    finally show "component ?ss r \<le> r\<^sup>T * bot\<^sup>\<star>"
      .
  next
    show "regular bot"
      by simp
  qed
qed

lemma prim_vc_2:
  assumes "prim_spanning_invariant t v g r"
      and "v * -v\<^sup>T \<sqinter> g \<noteq> bot"
    shows "prim_spanning_invariant (t \<squnion> minarc (v * -v\<^sup>T \<sqinter> g)) (v \<squnion> minarc (v * -v\<^sup>T \<sqinter> g)\<^sup>T * top) g r \<and> card { x . regular x \<and> x \<le> component g r \<and> x \<le> -(v \<squnion> minarc (v * -v\<^sup>T \<sqinter> g)\<^sup>T * top)\<^sup>T } < card { x . regular x \<and> x \<le> component g r \<and> x \<le> -v\<^sup>T }"
proof -
  let ?vcv = "v * -v\<^sup>T \<sqinter> g"
  let ?e = "minarc ?vcv"
  let ?t = "t \<squnion> ?e"
  let ?v = "v \<squnion> ?e\<^sup>T * top"
  let ?c = "component g r"
  let ?g = "--g"
  let ?n1 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -v\<^sup>T }"
  let ?n2 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -?v\<^sup>T }"
  have 1: "regular v \<and> regular (v * v\<^sup>T) \<and> regular (?v * ?v\<^sup>T) \<and> regular (top * ?e)"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive regular_closed_top regular_closed_sup minarc_regular)
  hence 2: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def inf_pp_commute inf.boundedE)
  hence 3: "t \<le> v * v\<^sup>T"
    by simp
  have 4: "t \<le> ?g"
    using 2 by simp
  have 5: "?e \<le> v * -v\<^sup>T \<sqinter> ?g"
    using 1 by (metis minarc_below pp_dist_inf regular_mult_closed regular_closed_p)
  hence 6: "?e \<le> v * -v\<^sup>T"
    by simp
  have 7: "vector v"
    using assms(1) prim_spanning_invariant_def prim_precondition_def by (simp add: covector_mult_closed vector_conv_covector)
  hence 8: "?e \<le> v"
    using 6 by (metis conv_complement inf.boundedE vector_complement_closed vector_covector)
  have 9: "?e * t = bot"
    using 3 6 7 et(1) by blast
  have 10: "?e * t\<^sup>T = bot"
    using 3 6 7 et(2) by simp
  have 11: "arc ?e"
    using assms(2) minarc_arc by simp
  have "r\<^sup>T \<le> r\<^sup>T * t\<^sup>\<star>"
    by (metis mult_right_isotone order_refl semiring.mult_not_zero star.circ_separate_mult_1 star_absorb)
  hence 12: "r\<^sup>T \<le> v\<^sup>T"
    using assms(1) by (simp add: prim_spanning_invariant_def)
  have 13: "vector r \<and> injective r \<and> v\<^sup>T = r\<^sup>T * t\<^sup>\<star>"
    using assms(1) prim_spanning_invariant_def prim_precondition_def minimum_spanning_tree_def spanning_tree_def reachable_restrict by simp
  have "g = g\<^sup>T"
    using assms(1) prim_invariant_def prim_spanning_invariant_def prim_precondition_def by simp
  hence 14: "?g\<^sup>T = ?g"
    using conv_complement by simp
  show "prim_spanning_invariant ?t ?v g r \<and> ?n2 < ?n1"
  proof (rule conjI)
    show "prim_spanning_invariant ?t ?v g r"
    proof (unfold prim_spanning_invariant_def, intro conjI)
      show "prim_precondition g r"
        using assms(1) prim_spanning_invariant_def by simp
    next
      show "?v\<^sup>T = r\<^sup>T * ?t\<^sup>\<star>"
        using assms(1) 6 7 9 by (simp add: reachable_inv prim_spanning_invariant_def prim_precondition_def spanning_tree_def)
    next
      let ?G = "?v * ?v\<^sup>T \<sqinter> g"
      show "spanning_tree ?t ?G r"
      proof (unfold spanning_tree_def, intro conjI)
        show "injective ?t"
          using assms(1) 10 11 by (simp add: injective_inv prim_spanning_invariant_def spanning_tree_def)
      next
        show "acyclic ?t"
          using assms(1) 3 6 7 acyclic_inv prim_spanning_invariant_def spanning_tree_def by simp
      next
        show "?t \<le> (component ?G r)\<^sup>T * (component ?G r) \<sqinter> --?G"
          using 1 2 5 7 13 prim_subgraph_inv inf_pp_commute mst_subgraph_inv_2 by auto
      next
        show "component (?v * ?v\<^sup>T \<sqinter> g) r \<le> r\<^sup>T * ?t\<^sup>\<star>"
        proof -
          have 15: "r\<^sup>T * (v * v\<^sup>T \<sqinter> ?g)\<^sup>\<star> \<le> r\<^sup>T * t\<^sup>\<star>"
            using assms(1) 1 by (metis prim_spanning_invariant_def spanning_tree_def inf_pp_commute)
          have "component (?v * ?v\<^sup>T \<sqinter> g) r = r\<^sup>T * (?v * ?v\<^sup>T \<sqinter> ?g)\<^sup>\<star>"
            using 1 by simp
          also have "... \<le> r\<^sup>T * ?t\<^sup>\<star>"
            using 2 6 7 11 12 13 14 15 by (metis span_inv)
          finally show ?thesis
            .
        qed
      next
        show "regular ?t"
          using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def regular_closed_sup minarc_regular)
      qed
    qed
  next
    have 16: "top * ?e \<le> ?c"
    proof -
      have "top * ?e = top * ?e\<^sup>T * ?e"
        using 11 by (metis arc_top_edge mult_assoc)
      also have "... \<le> v\<^sup>T * ?e"
        using 7 8 by (metis conv_dist_comp conv_isotone mult_left_isotone symmetric_top_closed)
      also have "... \<le> v\<^sup>T * ?g"
        using 5 mult_right_isotone by auto
      also have "... = r\<^sup>T * t\<^sup>\<star> * ?g"
        using 13 by simp
      also have "... \<le> r\<^sup>T * ?g\<^sup>\<star> * ?g"
        using 4 by (simp add: mult_left_isotone mult_right_isotone star_isotone)
      also have "... \<le> ?c"
        by (simp add: comp_associative mult_right_isotone star.right_plus_below_circ)
      finally show ?thesis
        by simp
    qed
    have 17: "top * ?e \<le> -v\<^sup>T"
      using 6 7 by (simp add: schroeder_4_p vTeT)
    have 18: "\<not> top * ?e \<le> -(top * ?e)"
      by (metis assms(2) inf.orderE minarc_bot_iff conv_complement_sub_inf inf_p inf_top.left_neutral p_bot symmetric_top_closed vector_top_closed)
    have 19: "-?v\<^sup>T = -v\<^sup>T \<sqinter> -(top * ?e)"
      by (simp add: conv_dist_comp conv_dist_sup)
    hence 20: "\<not> top * ?e \<le> -?v\<^sup>T"
      using 18 by simp
    show "?n2 < ?n1"
      apply (rule psubset_card_mono)
      using finite_regular apply simp
      using 1 16 17 19 20 by auto
  qed
qed

lemma prim_vc_3:
  assumes "prim_spanning_invariant t v g r"
      and "v * -v\<^sup>T \<sqinter> g = bot"
    shows "spanning_tree t g r"
proof -
  let ?g = "--g"
  have 1: "regular v \<and> regular (v * v\<^sup>T)"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  have 2: "v * -v\<^sup>T \<sqinter> ?g = bot"
    using assms(2) pp_inf_bot_iff pp_pp_inf_bot_iff by simp
  have 3: "v\<^sup>T = r\<^sup>T * t\<^sup>\<star> \<and> vector v"
    using assms(1) by (simp add: covector_mult_closed prim_invariant_def prim_spanning_invariant_def vector_conv_covector prim_precondition_def)
  have 4: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    using assms(1) 1 by (metis prim_spanning_invariant_def inf_pp_commute spanning_tree_def inf.boundedE)
  have "r\<^sup>T * (v * v\<^sup>T \<sqinter> ?g)\<^sup>\<star> \<le> r\<^sup>T * t\<^sup>\<star>"
    using assms(1) 1 by (metis prim_spanning_invariant_def inf_pp_commute spanning_tree_def)
  hence 5: "component g r = v\<^sup>T"
    using 1 2 3 4 by (metis span_post)
  have "regular (v * v\<^sup>T)"
    using assms(1) by (metis prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  hence 6: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    by (metis assms(1) prim_spanning_invariant_def spanning_tree_def inf_pp_commute inf.boundedE)
  show "spanning_tree t g r"
    apply (unfold spanning_tree_def, intro conjI)
    using assms(1) prim_spanning_invariant_def spanning_tree_def apply simp
    using assms(1) prim_spanning_invariant_def spanning_tree_def apply simp
    using 5 6 apply simp
    using assms(1) 5 prim_spanning_invariant_def apply simp
    using assms(1) prim_spanning_invariant_def spanning_tree_def by simp
qed

text \<open>
The following result shows that Prim's algorithm terminates and constructs a spanning tree.
We cannot yet show that this is a minimum spanning tree.
\<close>

theorem prim_spanning:
  "VARS t v e
  [ prim_precondition g r ]
  t := bot;
  v := r;
  WHILE v * -v\<^sup>T \<sqinter> g \<noteq> bot
    INV { prim_spanning_invariant t v g r }
    VAR { card { x . regular x \<and> x \<le> component g r \<sqinter> -v\<^sup>T } }
     DO e := minarc (v * -v\<^sup>T \<sqinter> g);
        t := t \<squnion> e;
        v := v \<squnion> e\<^sup>T * top
     OD
  [ spanning_tree t g r ]"
  apply vcg_tc_simp
  apply (simp add: prim_vc_1)
  using prim_vc_2 apply blast
  using prim_vc_3 by auto

text \<open>
Because we have shown total correctness, we conclude that a spanning tree exists.
\<close>

lemma prim_exists_spanning:
  "prim_precondition g r \<Longrightarrow> \<exists>t . spanning_tree t g r"
  using tc_extract_function prim_spanning by blast

text \<open>
This implies that a minimum spanning tree exists, which is used in the subsequent correctness proof.
\<close>

lemma prim_exists_minimal_spanning:
  assumes "prim_precondition g r"
    shows "\<exists>t . minimum_spanning_tree t g r"
proof -
  let ?s = "{ t . spanning_tree t g r }"
  have "\<exists>m\<in>?s . \<forall>z\<in>?s . sum (m \<sqinter> g) \<le> sum (z \<sqinter> g)"
    apply (rule finite_set_minimal)
    using finite_regular spanning_tree_def apply simp
    using assms prim_exists_spanning apply simp
    using sum_linear by simp
  thus ?thesis
    using minimum_spanning_tree_def by simp
qed

text \<open>
Prim's minimum spanning tree algorithm terminates and is correct.
This is the same algorithm that is used in the previous correctness proof, with the same precondition and variant, but with a different invariant and postcondition.
\<close>

theorem prim:
  "VARS t v e
  [ prim_precondition g r \<and> (\<exists>w . minimum_spanning_tree w g r) ]
  t := bot;
  v := r;
  WHILE v * -v\<^sup>T \<sqinter> g \<noteq> bot
    INV { prim_invariant t v g r }
    VAR { card { x . regular x \<and> x \<le> component g r \<sqinter> -v\<^sup>T } }
     DO e := minarc (v * -v\<^sup>T \<sqinter> g);
        t := t \<squnion> e;
        v := v \<squnion> e\<^sup>T * top
     OD
  [ minimum_spanning_tree t g r ]"
proof vcg_tc_simp
  assume "prim_precondition g r \<and> (\<exists>w . minimum_spanning_tree w g r)"
  thus "prim_invariant bot r g r"
    using prim_invariant_def prim_vc_1 by simp
next
  fix t v
  let ?vcv = "v * -v\<^sup>T \<sqinter> g"
  let ?vv = "v * v\<^sup>T \<sqinter> g"
  let ?e = "minarc ?vcv"
  let ?t = "t \<squnion> ?e"
  let ?v = "v \<squnion> ?e\<^sup>T * top"
  let ?c = "component g r"
  let ?g = "--g"
  let ?n1 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -v\<^sup>T }"
  let ?n2 = "card { x . regular x \<and> x \<le> ?c \<and> x \<le> -?v\<^sup>T }"
  assume 1: "prim_invariant t v g r \<and> ?vcv \<noteq> bot"
  hence 2: "regular v \<and> regular (v * v\<^sup>T)"
    by (metis (no_types, hide_lams) prim_invariant_def prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  have 3: "t \<le> v * v\<^sup>T \<sqinter> ?g"
    using 1 2 by (metis (no_types, hide_lams) prim_invariant_def prim_spanning_invariant_def spanning_tree_def inf_pp_commute inf.boundedE)
  hence 4: "t \<le> v * v\<^sup>T"
    by simp
  have 5: "t \<le> ?g"
    using 3 by simp
  have 6: "?e \<le> v * -v\<^sup>T \<sqinter> ?g"
    using 2 by (metis minarc_below pp_dist_inf regular_mult_closed regular_closed_p)
  hence 7: "?e \<le> v * -v\<^sup>T"
    by simp
  have 8: "vector v"
    using 1 prim_invariant_def prim_spanning_invariant_def prim_precondition_def by (simp add: covector_mult_closed vector_conv_covector)
  have 9: "arc ?e"
    using 1 minarc_arc by simp
  from 1 obtain w where 10: "minimum_spanning_tree w g r \<and> t \<le> w"
    by (metis prim_invariant_def)
  hence 11: "vector r \<and> injective r \<and> v\<^sup>T = r\<^sup>T * t\<^sup>\<star> \<and> forest w \<and> t \<le> w \<and> w \<le> ?c\<^sup>T * ?c \<sqinter> ?g \<and> r\<^sup>T * (?c\<^sup>T * ?c \<sqinter> ?g)\<^sup>\<star> \<le> r\<^sup>T * w\<^sup>\<star>"
    using 1 2 prim_invariant_def prim_spanning_invariant_def prim_precondition_def minimum_spanning_tree_def spanning_tree_def reachable_restrict by simp
  hence 12: "w * v \<le> v"
    using predecessors_reachable reachable_restrict by auto
  have 13: "g = g\<^sup>T"
    using 1 prim_invariant_def prim_spanning_invariant_def prim_precondition_def by simp
  hence 14: "?g\<^sup>T = ?g"
    using conv_complement by simp
  show "prim_invariant ?t ?v g r \<and> ?n2 < ?n1"
  proof (unfold prim_invariant_def, intro conjI)
    show "prim_spanning_invariant ?t ?v g r"
      using 1 prim_invariant_def prim_vc_2 by blast
  next
    show "\<exists>w . minimum_spanning_tree w g r \<and> ?t \<le> w"
    proof
      let ?f = "w \<sqinter> v * -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
      let ?p = "w \<sqinter> -v * -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
      let ?fp = "w \<sqinter> -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>"
      let ?w = "(w \<sqinter> -?fp) \<squnion> ?p\<^sup>T \<squnion> ?e"
      have 15: "regular ?f \<and> regular ?fp \<and> regular ?w"
        using 2 10 by (metis regular_conv_closed regular_closed_star regular_mult_closed regular_closed_top regular_closed_inf regular_closed_sup minarc_regular minimum_spanning_tree_def spanning_tree_def)
      show "minimum_spanning_tree ?w g r \<and> ?t \<le> ?w"
      proof (intro conjI)
        show "minimum_spanning_tree ?w g r"
        proof (unfold minimum_spanning_tree_def, intro conjI)
          show "spanning_tree ?w g r"
          proof (unfold spanning_tree_def, intro conjI)
            show "injective ?w"
              using 7 8 9 11 exchange_injective by blast
          next
            show "acyclic ?w"
              using 7 8 11 12 exchange_acyclic by blast
          next
            show "?w \<le> ?c\<^sup>T * ?c \<sqinter> --g"
            proof -
              have 16: "w \<sqinter> -?fp \<le> ?c\<^sup>T * ?c \<sqinter> --g"
                using 10 by (simp add: le_infI1 minimum_spanning_tree_def spanning_tree_def)
              have "?p\<^sup>T \<le> w\<^sup>T"
                by (simp add: conv_isotone inf.sup_monoid.add_assoc)
              also have "... \<le> (?c\<^sup>T * ?c \<sqinter> --g)\<^sup>T"
                using 11 conv_order by simp
              also have "... = ?c\<^sup>T * ?c \<sqinter> --g"
                using 2 14 conv_dist_comp conv_dist_inf by simp
              finally have 17: "?p\<^sup>T \<le> ?c\<^sup>T * ?c \<sqinter> --g"
                .
              have "?e \<le> ?c\<^sup>T * ?c \<sqinter> ?g"
                using 5 6 11 mst_subgraph_inv by auto
              thus ?thesis
                using 16 17 by simp
            qed
          next
            show "?c \<le> r\<^sup>T * ?w\<^sup>\<star>"
            proof -
              have "?c \<le> r\<^sup>T * w\<^sup>\<star>"
                using 10 minimum_spanning_tree_def spanning_tree_def by simp
              also have "... \<le> r\<^sup>T * ?w\<^sup>\<star>"
                using 4 7 8 10 11 12 15 by (metis mst_reachable_inv)
              finally show ?thesis
                .
            qed
          next
            show "regular ?w"
              using 15 by simp
          qed
        next
          have 18: "?f \<squnion> ?p = ?fp"
            using 2 8 epm_1 by fastforce
          have "arc (w \<sqinter> --v * -v\<^sup>T \<sqinter> top * ?e * w\<^sup>T\<^sup>\<star>)"
            using 5 6 8 9 11 12 reachable_restrict arc_edge by auto
          hence 19: "arc ?f"
            using 2 by simp
          hence "?f = bot \<longrightarrow> top = bot"
            by (metis mult_left_zero mult_right_zero)
          hence "?f \<noteq> bot"
            using 1 le_bot by auto
          hence "?f \<sqinter> v * -v\<^sup>T \<sqinter> ?g \<noteq> bot"
            using 2 11 by (simp add: inf.absorb1 le_infI1)
          hence "g \<sqinter> (?f \<sqinter> v * -v\<^sup>T) \<noteq> bot"
            using inf_commute pp_inf_bot_iff by simp
          hence 20: "?f \<sqinter> ?vcv \<noteq> bot"
            by (simp add: inf_assoc inf_commute)
          hence 21: "?f \<sqinter> g = ?f \<sqinter> ?vcv"
            using 2 by (simp add: inf_assoc inf_commute inf_left_commute)
          have 22: "?e \<sqinter> g = minarc ?vcv \<sqinter> ?vcv"
            using 7 by (simp add: inf.absorb2 inf.assoc inf.commute)
          hence 23: "sum (?e \<sqinter> g) \<le> sum (?f \<sqinter> g)"
            using 15 19 20 21 by (simp add: minarc_min)
          have "?e \<noteq> bot"
            using 20 comp_inf.semiring.mult_not_zero semiring.mult_not_zero by blast
          hence 24: "?e \<sqinter> g \<noteq> bot"
            using 22 minarc_meet_bot by auto
          have "sum (?w \<sqinter> g) = sum (w \<sqinter> -?fp \<sqinter> g) + sum (?p\<^sup>T \<sqinter> g) + sum (?e \<sqinter> g)"
            using 7 8 10 by (metis sum_disjoint_3 epm_8 epm_9 epm_10 minimum_spanning_tree_def spanning_tree_def)
          also have "... = sum (((w \<sqinter> -?fp) \<squnion> ?p\<^sup>T) \<sqinter> g) + sum (?e \<sqinter> g)"
            using 11 by (metis epm_8 sum_disjoint)
          also have "... \<le> sum (((w \<sqinter> -?fp) \<squnion> ?p\<^sup>T) \<sqinter> g) + sum (?f \<sqinter> g)"
            using 23 24 by (simp add: sum_plus_right_isotone)
          also have "... = sum (w \<sqinter> -?fp \<sqinter> g) + sum (?p\<^sup>T \<sqinter> g) + sum (?f \<sqinter> g)"
            using 11 by (metis epm_8 sum_disjoint)
          also have "... = sum (w \<sqinter> -?fp \<sqinter> g) + sum (?p \<sqinter> g) + sum (?f \<sqinter> g)"
            using 13 sum_symmetric by auto
          also have "... = sum (((w \<sqinter> -?fp) \<squnion> ?p \<squnion> ?f) \<sqinter> g)"
            using 2 8 by (metis sum_disjoint_3 epm_11 epm_12 epm_13)
          also have "... = sum (w \<sqinter> g)"
            using 2 8 15 18 epm_2 by force
          finally have "sum (?w \<sqinter> g) \<le> sum (w \<sqinter> g)"
            .
          thus "\<forall>u . spanning_tree u g r \<longrightarrow> sum (?w \<sqinter> g) \<le> sum (u \<sqinter> g)"
            using 10 order_lesseq_imp minimum_spanning_tree_def by auto
        qed
      next
        show "?t \<le> ?w"
          using 4 8 10 mst_extends_new_tree by simp
      qed
    qed
  next
    show "?n2 < ?n1"
      using 1 prim_invariant_def prim_vc_2 by auto
  qed
next
  fix t v
  let ?g = "--g"
  assume 25: "prim_invariant t v g r \<and> v * -v\<^sup>T \<sqinter> g = bot"
  hence 26: "regular v"
    by (metis prim_invariant_def prim_spanning_invariant_def spanning_tree_def prim_precondition_def regular_conv_closed regular_closed_star regular_mult_closed conv_involutive)
  from 25 obtain w where 27: "minimum_spanning_tree w g r \<and> t \<le> w"
    by (metis prim_invariant_def)
  have "spanning_tree t g r"
    using 25 prim_invariant_def prim_vc_3 by blast
  hence "component g r = v\<^sup>T"
    by (metis 25 prim_invariant_def span_tree_component prim_spanning_invariant_def spanning_tree_def)
  hence 28: "w \<le> v * v\<^sup>T"
    using 26 27 by (simp add: minimum_spanning_tree_def spanning_tree_def inf_pp_commute)
  have "vector r \<and> injective r \<and> forest w"
    using 25 27 by (simp add: prim_invariant_def prim_spanning_invariant_def prim_precondition_def minimum_spanning_tree_def spanning_tree_def)
  hence "w = t"
    using 25 27 28 prim_invariant_def prim_spanning_invariant_def mst_post by blast
  thus "minimum_spanning_tree t g r"
    using 27 by simp
qed

end

end

