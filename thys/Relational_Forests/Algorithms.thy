(* Title:      Axioms and Algorithmic Proofs
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Axioms and Algorithmic Proofs\<close>

text \<open>
In this theory we verify the correctness of three basic graph algorithms.
We use them to constructively prove a number of graph properties.
\<close>

theory Algorithms

imports "HOL-Hoare.Hoare_Logic" Forests

begin

context stone_kleene_relation_algebra_arc
begin

text \<open>
Assuming the arc axiom we can define the function \<open>choose_arc\<close> that selects an arc in a non-empty graph.
\<close>

definition "choose_arc x \<equiv> if x = bot then bot else SOME y . arc y \<and> y \<le> --x"

lemma choose_arc_below:
  "choose_arc x \<le> --x"
proof (cases "x = bot")
  case True
  thus ?thesis
    using choose_arc_def by auto
next
  let ?P = "\<lambda>y . arc y \<and> y \<le> --x"
  case False
  have "?P (SOME y . ?P y)"
    apply (rule someI_ex)
    using someI_ex False arc_axiom by auto
  thus ?thesis
    using False choose_arc_def by auto
qed

lemma choose_arc_arc:
  assumes "x \<noteq> bot"
  shows "arc (choose_arc x)"
proof -
  let ?P = "\<lambda>y . arc y \<and> y \<le> --x"
  have "?P (SOME y . ?P y)"
    apply (rule someI_ex)
    using someI_ex assms arc_axiom by auto
  thus ?thesis
    using assms choose_arc_def by auto
qed

lemma choose_arc_bot:
  "choose_arc bot = bot"
  by (metis bot_unique choose_arc_below regular_closed_bot)

lemma choose_arc_bot_iff:
  "choose_arc x = bot \<longleftrightarrow> x = bot"
  using covector_bot_closed inf_bot_right choose_arc_arc vector_bot_closed choose_arc_bot by fastforce

lemma choose_arc_regular:
  "regular (choose_arc x)"
proof (cases "x = bot")
  assume "x = bot"
  thus ?thesis
    by (simp add: choose_arc_bot)
next
  assume "x \<noteq> bot"
  thus ?thesis
    by (simp add: arc_regular choose_arc_arc)
qed

subsection \<open>Constructing a spanning tree\<close>

definition "spanning_forest f g \<equiv> forest f \<and> f \<le> --g \<and> components g \<le> forest_components f \<and> regular f"
definition "kruskal_spanning_invariant f g h \<equiv> symmetric g \<and> h = h\<^sup>T \<and> g \<sqinter> --h = h \<and> spanning_forest f (-h \<sqinter> g)"

lemma spanning_forest_spanning:
  "spanning_forest f g \<Longrightarrow> spanning (--g) f"
  by (smt (z3) cancel_separate_1 order_trans star.circ_increasing spanning_forest_def)

lemma spanning_forest_spanning_regular:
  assumes "regular f"
      and "regular g"
  shows "spanning_forest f g \<longleftrightarrow> spanning g f"
  by (smt (z3) assms cancel_separate_1 components_increasing dual_order.trans forest_components_star star_isotone spanning_forest_def)

text \<open>
We prove total correctness of Kruskal's spanning tree algorithm (ignoring edge weights) \cite{Kruskal1956}.
The algorithm and proof are adapted from the AFP theory \<open>Relational_Minimum_Spanning_Trees.Kruskal\<close> to work in Stone-Kleene relation algebras \cite{Guttmann2017c,Guttmann2018c}.
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

text \<open>
For the remainder of this theory we assume there are finitely many regular elements.
This means that the graphs are finite and is needed for proving termination of the algorithms.
\<close>

context
  assumes finite_regular: "finite { x . regular x }"
begin

lemma kruskal_vc_2:
  assumes "kruskal_spanning_invariant f g h"
      and "h \<noteq> bot"
    shows "(choose_arc h \<le> -forest_components f \<longrightarrow> kruskal_spanning_invariant ((f \<sqinter> -(top * choose_arc h * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * choose_arc h * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> choose_arc h) g (h \<sqinter> -choose_arc h \<sqinter> -choose_arc h\<^sup>T)
                                               \<and> card { x . regular x \<and> x \<le> --h \<and> x \<le> -choose_arc h \<and> x \<le> -choose_arc h\<^sup>T } < card { x . regular x \<and> x \<le> --h }) \<and>
           (\<not> choose_arc h \<le> -forest_components f \<longrightarrow> kruskal_spanning_invariant f g (h \<sqinter> -choose_arc h \<sqinter> -choose_arc h\<^sup>T)
                                                 \<and> card { x . regular x \<and> x \<le> --h \<and> x \<le> -choose_arc h \<and> x \<le> -choose_arc h\<^sup>T } < card { x . regular x \<and> x \<le> --h })"
proof -
  let ?e = "choose_arc h"
  let ?f = "(f \<sqinter> -(top * ?e * f\<^sup>T\<^sup>\<star>)) \<squnion> (f \<sqinter> top * ?e * f\<^sup>T\<^sup>\<star>)\<^sup>T \<squnion> ?e"
  let ?h = "h \<sqinter> -?e \<sqinter> -?e\<^sup>T"
  let ?F = "forest_components f"
  let ?n1 = "card { x . regular x \<and> x \<le> --h }"
  let ?n2 = "card { x . regular x \<and> x \<le> --h \<and> x \<le> -?e \<and> x \<le> -?e\<^sup>T }"
  have 1: "regular f \<and> regular ?e"
    by (metis assms(1) kruskal_spanning_invariant_def spanning_forest_def choose_arc_regular)
  hence 2: "regular ?f \<and> regular ?F \<and> regular (?e\<^sup>T)"
    using regular_closed_star regular_conv_closed regular_mult_closed by simp
  have 3: "\<not> ?e \<le> -?e"
    using assms(2) inf.orderE choose_arc_bot_iff by fastforce
  have 4: "?n2 < ?n1"
    apply (rule psubset_card_mono)
    using finite_regular apply simp
    using 1 3 kruskal_spanning_invariant_def choose_arc_below by auto
  show "(?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant ?f g ?h \<and> ?n2 < ?n1) \<and> (\<not> ?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant f g ?h \<and> ?n2 < ?n1)"
  proof (rule conjI)
    have 5: "injective ?f"
      apply (rule kruskal_injective_inv)
      using assms(1) kruskal_spanning_invariant_def spanning_forest_def apply simp
      apply (simp add: covector_mult_closed)
      apply (simp add: comp_associative comp_isotone star.right_plus_below_circ)
      apply (meson mult_left_isotone order_lesseq_imp star_outer_increasing top.extremum)
      using assms(1,2) kruskal_spanning_invariant_def kruskal_injective_inv_2 choose_arc_arc spanning_forest_def apply simp
      using assms(2) arc_injective choose_arc_arc apply blast
      using assms(1,2) kruskal_spanning_invariant_def kruskal_injective_inv_3 choose_arc_arc spanning_forest_def by simp
    show "?e \<le> -?F \<longrightarrow> kruskal_spanning_invariant ?f g ?h \<and> ?n2 < ?n1"
    proof
      assume 6: "?e \<le> -?F"
      have 7: "equivalence ?F"
        using assms(1) kruskal_spanning_invariant_def forest_components_equivalence spanning_forest_def by simp
      have "?e\<^sup>T * top * ?e\<^sup>T = ?e\<^sup>T"
        using assms(2) by (simp add: arc_top_arc choose_arc_arc)
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
            using assms(1) apply (metis kruskal_spanning_invariant_def choose_arc_below order.trans pp_isotone_inf)
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
        using 2 assms(2) arc_in_partition choose_arc_arc by fastforce
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
            using comp_inf.mult_right_isotone inf.sup_monoid.add_commute inf_left_commute p_antitone_inf pp_isotone by auto
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

theorem kruskal_spanning:
  "VARS e f h
  [ symmetric g ]
  f := bot;
  h := g;
  WHILE h \<noteq> bot
    INV { kruskal_spanning_invariant f g h }
    VAR { card { x . regular x \<and> x \<le> --h } }
     DO e := choose_arc h;
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

lemma kruskal_exists_spanning:
  "symmetric g \<Longrightarrow> \<exists>f . spanning_forest f g"
  using tc_extract_function kruskal_spanning by blast

text \<open>Theorem 16\<close>

lemma symmetric_spannable:
  "symmetric g \<Longrightarrow> spannable (--g)"
  using kruskal_exists_spanning spanning_forest_spanning spannable_def by blast

subsection \<open>Breadth-first search\<close>

text \<open>
We prove total correctness of a simple breadth-first search algorithm.
It is a variant of an algorithm discussed in \cite{Berghammer1999}.
\<close>

theorem bfs_reachability:
  "VARS p q t
  [ regular r \<and> regular s \<and> vector s ]
  t := bot;
  q := s;
  p := -s \<sqinter> r\<^sup>T * s;
  WHILE p \<noteq> bot
    INV { regular r \<and> regular q \<and> vector q \<and> asymmetric t \<and> t \<le> r \<and> t \<le> q \<and> q = t\<^sup>T\<^sup>\<star> * s \<and> p = -q \<sqinter> r\<^sup>T * q }
    VAR { card { x . regular x \<and> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s) } }
     DO t := t \<squnion> (r \<sqinter> q * p\<^sup>T);
        q := q \<squnion> p;
        p := -q \<sqinter> r\<^sup>T * p
     OD
  [ asymmetric t \<and> t \<le> r \<and> q = t\<^sup>T\<^sup>\<star> * s \<and> q = r\<^sup>T\<^sup>\<star> * s ]"
proof vcg_tc
  fix p q t
  assume "regular r \<and> regular s \<and> vector s"
  thus "regular r \<and> regular s \<and> vector s \<and> asymmetric bot \<and> bot \<le> r \<and> bot \<le> s \<and> s = bot\<^sup>T\<^sup>\<star> * s \<and> -s \<sqinter> r\<^sup>T * s = -s \<sqinter> r\<^sup>T * s"
    by (simp add: star.circ_zero)
next
  fix p q t
  assume 1: "(regular r \<and> regular q \<and> vector q \<and> asymmetric t \<and> t \<le> r \<and> t \<le> q \<and> q = t\<^sup>T\<^sup>\<star> * s \<and> p = -q \<sqinter> r\<^sup>T * q) \<and> \<not> p \<noteq> bot"
  have "q = r\<^sup>T\<^sup>\<star> * s"
    apply (rule antisym)
    using 1 conv_order mult_left_isotone star_isotone apply simp
    using 1 by (metis inf.sup_monoid.add_commute mult_1_left mult_left_isotone mult_right_isotone order_lesseq_imp pseudo_complement star.circ_reflexive star_left_induct_mult)
  thus "asymmetric t \<and> t \<le> r \<and> q = t\<^sup>T\<^sup>\<star> * s \<and> q = r\<^sup>T\<^sup>\<star> * s"
    using 1 by simp
next
  fix n p q t
  assume 2: "((regular r \<and> regular q \<and> vector q \<and> asymmetric t \<and> t \<le> r \<and> t \<le> q \<and> q = t\<^sup>T\<^sup>\<star> * s \<and> p = -q \<sqinter> r\<^sup>T * q) \<and> p \<noteq> bot) \<and> card { x . regular x \<and> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s) } = n"
  hence 3: "vector p"
    using vector_complement_closed vector_inf_closed vector_mult_closed by blast
  show "(-(q \<squnion> p) \<sqinter> r\<^sup>T * p, q \<squnion> p, t \<squnion> (r \<sqinter> q * p\<^sup>T))
        \<in> { trip . (case trip of (p, q, t) \<Rightarrow> regular r \<and> regular q \<and> vector q \<and> asymmetric t \<and> t \<le> r \<and> t \<le> q \<and> q = t\<^sup>T\<^sup>\<star> * s \<and> p = -q \<sqinter> r\<^sup>T * q) \<and>
                   (case trip of (p, q, t) \<Rightarrow> card { x . regular x \<and> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s) }) < n }"
    apply (rule CollectI, rule conjI)
    subgoal proof (intro case_prodI, intro conjI)
      show "regular r"
        using 2 by blast
      show "regular (q \<squnion> p)"
        using 2 regular_conv_closed regular_mult_closed by force
      show "vector (q \<squnion> p)"
        using 2 vector_complement_closed vector_inf_closed vector_mult_closed vector_sup_closed by force
      show "asymmetric (t \<squnion> (r \<sqinter> q * p\<^sup>T))"
      proof -
        have "t \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T \<le> t \<sqinter> p * q\<^sup>T"
          by (metis comp_inf.mult_right_isotone conv_dist_comp conv_involutive conv_order inf.cobounded2)
        also have "... \<le> t \<sqinter> p"
          using 3 by (metis comp_inf.mult_right_isotone comp_inf.star.circ_sup_sub_sup_one_1 inf.boundedE le_sup_iff mult_right_isotone)
        finally have 4: "t \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T = bot"
          using 2 by (metis antisym bot_least inf.sup_monoid.add_assoc pseudo_complement)
        hence 5: "r \<sqinter> q * p\<^sup>T \<sqinter> t\<^sup>T = bot"
          using conv_inf_bot_iff inf_commute by force
        have "r \<sqinter> q * p\<^sup>T \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T \<le> q * p\<^sup>T \<sqinter> p * q\<^sup>T"
          by (metis comp_inf.comp_isotone conv_dist_comp conv_involutive conv_order inf.cobounded2)
        also have "... \<le> q \<sqinter> p"
          using 2 3 by (metis comp_inf.comp_isotone inf.cobounded1 vector_covector)
        finally have 6: "r \<sqinter> q * p\<^sup>T \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T = bot"
          using 2 by (metis inf.cobounded1 inf.sup_monoid.add_commute le_bot pseudo_complement)
        have "(t \<squnion> (r \<sqinter> q * p\<^sup>T)) \<sqinter> (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T = (t \<sqinter> t\<^sup>T) \<squnion> (t \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T) \<squnion> (r \<sqinter> q * p\<^sup>T \<sqinter> t\<^sup>T) \<squnion> (r \<sqinter> q * p\<^sup>T \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T)"
          by (simp add: sup.commute sup.left_commute conv_dist_sup inf_sup_distrib1 inf_sup_distrib2)
        also have "... = bot"
          using 2 4 5 6 by auto
        finally show ?thesis
          .
      qed
      show "t \<squnion> (r \<sqinter> q * p\<^sup>T) \<le> r"
        using 2 by (meson inf.cobounded1 le_supI)
      show "t \<squnion> (r \<sqinter> q * p\<^sup>T) \<le> q \<squnion> p"
        using 2 by (metis comp_inf.star.circ_sup_sub_sup_one_1 inf.absorb2 inf.coboundedI2 inf.sup_monoid.add_commute le_sup_iff mult_right_isotone sup_left_divisibility)
      show "q \<squnion> p = (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T\<^sup>\<star> * s"
      proof (rule antisym)
        have 7: "q \<le> (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T\<^sup>\<star> * s"
          using 2 by (metis conv_order mult_left_isotone star_isotone sup_left_divisibility)
        have "-q \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T * q \<le> (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T * t\<^sup>T\<^sup>\<star> * s"
          using 2 comp_associative conv_dist_sup inf.coboundedI2 mult_right_sub_dist_sup_right by auto
        also have "... \<le> (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T\<^sup>\<star> * s"
          by (simp add: conv_dist_sup mult_left_isotone star.circ_increasing star.circ_mult_upper_bound star.circ_sub_dist)
        finally have 8: "-q \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T * q \<le> (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T\<^sup>\<star> * s"
          .
        have 9: "(r \<sqinter> -q)\<^sup>T * q = bot"
          using 2 by (metis conv_dist_inf covector_inf_comp_3 pp_inf_p semiring.mult_not_zero vector_complement_closed)
        have "-q \<sqinter> (r \<sqinter> -(q * p\<^sup>T))\<^sup>T * q = -q \<sqinter> (r \<sqinter> (-q \<squnion> -p\<^sup>T))\<^sup>T * q"
          using 2 3 by (metis p_dist_inf vector_covector)
        also have "... = (-q \<sqinter> (r \<sqinter> -q)\<^sup>T * q) \<squnion> (-q \<sqinter> (r \<sqinter> -p\<^sup>T)\<^sup>T * q)"
          by (simp add: conv_dist_sup inf_sup_distrib1 mult_right_dist_sup)
        also have "... = -q \<sqinter> (r \<sqinter> -p\<^sup>T)\<^sup>T * q"
          using 9 by simp
        also have "... = -q \<sqinter> -p \<sqinter> r\<^sup>T * q"
          using 3 by (metis conv_complement conv_dist_inf conv_involutive inf.sup_monoid.add_assoc inf_vector_comp vector_complement_closed)
        finally have 10: "-q \<sqinter> (r \<sqinter> -(q * p\<^sup>T))\<^sup>T * q = bot"
          using 2 inf_import_p pseudo_complement by auto
        have "r = (r \<sqinter> q * p\<^sup>T) \<squnion> (r \<sqinter> -(q * p\<^sup>T))"
          using 2 by (smt (z3) maddux_3_11_pp pp_dist_comp regular_closed_inf regular_conv_closed)
        hence "p = -q \<sqinter> ((r \<sqinter> q * p\<^sup>T) \<squnion> (r \<sqinter> -(q * p\<^sup>T)))\<^sup>T * q"
          using 2 by auto
        also have "... = (-q \<sqinter> (r \<sqinter> q * p\<^sup>T)\<^sup>T * q) \<squnion> (-q \<sqinter> (r \<sqinter> -(q * p\<^sup>T))\<^sup>T * q)"
          by (simp add: conv_dist_sup inf_sup_distrib1 semiring.distrib_right)
        also have "... \<le> (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T\<^sup>\<star> * s"
          using 8 10 le_sup_iff bot_least by blast
        finally show "q \<squnion> p \<le> (t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T\<^sup>\<star> * s"
          using 7 by simp
        have 11: "t\<^sup>T * q \<le> r\<^sup>T * q"
          using 2 conv_order mult_left_isotone by auto
        have "t\<^sup>T * p \<le> t\<^sup>T * top"
          by (simp add: mult_right_isotone)
        also have "... = t\<^sup>T * q \<squnion> t\<^sup>T * -q"
          using 2 regular_complement_top semiring.distrib_left by force
        also have "... = t\<^sup>T * q"
        proof -
          have "t\<^sup>T * -q = bot"
            using 2 by (metis bot_least conv_complement_sub conv_dist_comp conv_involutive mult_right_isotone regular_closed_bot stone sup.absorb2 sup_commute)
          thus ?thesis
            by simp
        qed
        finally have 12: "t\<^sup>T * p \<le> r\<^sup>T * q"
          using 11 order.trans by blast
        have 13: "(r \<sqinter> q * p\<^sup>T)\<^sup>T * q \<le> r\<^sup>T * q"
          by (simp add: conv_dist_inf mult_left_isotone)
        have "(r \<sqinter> q * p\<^sup>T)\<^sup>T * p \<le> p"
          using 3 by (metis conv_dist_comp conv_dist_inf conv_involutive inf.coboundedI2 mult_isotone mult_right_isotone top.extremum)
        hence 14: "(r \<sqinter> q * p\<^sup>T)\<^sup>T * p \<le> r\<^sup>T * q"
          using 2 le_infE by blast
        have "(t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T * (q \<squnion> p) = t\<^sup>T * q \<squnion> t\<^sup>T * p \<squnion> (r \<sqinter> q * p\<^sup>T)\<^sup>T * q \<squnion> (r \<sqinter> q * p\<^sup>T)\<^sup>T * p"
          by (metis conv_dist_sup semiring.distrib_left semiring.distrib_right sup_assoc)
        also have "... \<le> r\<^sup>T * q"
          using 11 12 13 14 by simp
        finally have "(t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T * (q \<squnion> p) \<le> q \<squnion> p"
          using 2 by (metis maddux_3_21_pp sup.boundedE sup_right_divisibility)
        thus "(t \<squnion> (r \<sqinter> q * p\<^sup>T))\<^sup>T\<^sup>\<star> * s \<le> q \<squnion> p"
          using 2 by (smt (verit, ccfv_SIG) star.circ_loop_fixpoint star_left_induct sup.bounded_iff sup_left_divisibility)
      qed
      show "-(q \<squnion> p) \<sqinter> r\<^sup>T * p = -(q \<squnion> p) \<sqinter> r\<^sup>T * (q \<squnion> p)"
      proof (rule antisym)
        show "-(q \<squnion> p) \<sqinter> r\<^sup>T * p \<le> -(q \<squnion> p) \<sqinter> r\<^sup>T * (q \<squnion> p)"
          using inf.sup_right_isotone mult_left_sub_dist_sup_right by blast
        have 15: "- (q \<squnion> p) \<sqinter> r\<^sup>T * (q \<squnion> p) = - (q \<squnion> p) \<sqinter> r\<^sup>T * q \<squnion> - (q \<squnion> p) \<sqinter> r\<^sup>T * p"
          by (simp add: comp_inf.semiring.distrib_left mult_left_dist_sup)
        have "- (q \<squnion> p) \<sqinter> r\<^sup>T * q \<le> - (q \<squnion> p) \<sqinter> r\<^sup>T * p"
          using 2 by (metis bot_least p_dist_inf p_dist_sup p_inf_sup_below pseudo_complement)
        thus "- (q \<squnion> p) \<sqinter> r\<^sup>T * (q \<squnion> p) \<le> - (q \<squnion> p) \<sqinter> r\<^sup>T * p"
          using 15 sup.absorb2 by force
      qed
    qed
    subgoal proof clarsimp
      have "card { x . regular x \<and> x \<le> -q \<and> x \<le> -p \<and> x \<le> --(r\<^sup>T\<^sup>\<star> * s) } < card { x . regular x \<and> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s) }"
      proof (rule psubset_card_mono)
        show "finite { x . regular x \<and> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s) }"
          using finite_regular by simp
        show "{ x . regular x \<and> x \<le> -q \<and> x \<le> -p \<and> x \<le> --(r\<^sup>T\<^sup>\<star> * s) } \<subset> { x . regular x \<and> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s) }"
        proof -
          have "\<forall>x . x \<le> -q \<and> x \<le> --(r\<^sup>T\<^sup>\<star> * s) \<longrightarrow> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s)"
            by auto
          hence 16: "{ x . regular x \<and> x \<le> -q \<and> x \<le> -p \<and> x \<le> --(r\<^sup>T\<^sup>\<star> * s) } \<subseteq> { x . regular x \<and> x \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s) }"
            by blast
          have 17: "regular p"
            using 2 regular_conv_closed regular_mult_closed by force
          hence 18: "\<not> p \<le> -p"
            using 2 by (metis inf.absorb1 pp_inf_p)
          have 19: "p \<le> -q"
            using 2 by simp
          have "r\<^sup>T * q \<le> r\<^sup>T\<^sup>\<star> * s"
            using 2 by (metis (no_types, lifting) comp_associative conv_dist_sup mult_left_isotone star.circ_increasing star.circ_mult_upper_bound star.circ_sub_dist sup_left_divisibility)
          hence 20: "p \<le> --(r\<^sup>T\<^sup>\<star> * s)"
            using 2 le_infI2 order_lesseq_imp pp_increasing by blast
          hence 21: "p \<le> --(-q \<sqinter> r\<^sup>T\<^sup>\<star> * s)"
            using 2 by simp
          show ?thesis
            using 16 17 18 19 20 21 by blast
        qed
      qed
      thus "card { x . regular x \<and> x \<le> -q \<and> x \<le> -p \<and> x \<le> --(r\<^sup>T\<^sup>\<star> * s) } < n"
        using 2 by auto
    qed
    done
qed

text \<open>Theorem 18\<close>

lemma bfs_reachability_exists:
  "regular r \<and> regular s \<and> vector s \<Longrightarrow> \<exists>t . asymmetric t \<and> t \<le> r \<and> t\<^sup>T\<^sup>\<star> * s = r\<^sup>T\<^sup>\<star> * s"
  using tc_extract_function bfs_reachability by blast

text \<open>Theorem 17\<close>

lemma orientable_path:
  "arc x \<Longrightarrow> x \<le> --y\<^sup>\<star> \<Longrightarrow> \<exists>z . z \<le> y \<and> asymmetric z \<and> x \<le> --z\<^sup>\<star>"
proof -
  assume 1: "arc x" and 2: "x \<le> --y\<^sup>\<star>"
  hence "regular (--y) \<and> regular (x * top) \<and> vector (x * top)"
    using bijective_regular mult_assoc by auto
  from this obtain t where 3: "asymmetric t \<and> t \<le> --y \<and> t\<^sup>T\<^sup>\<star> * (x * top) = (--y)\<^sup>T\<^sup>\<star> * (x * top)"
    using bfs_reachability_exists by blast
  let ?z = "t \<sqinter> y"
  have "x\<^sup>T * top * x\<^sup>T \<le> (--y)\<^sup>T\<^sup>\<star>"
    using 1 2 by (metis arc_top_arc conv_complement conv_isotone conv_star_commute arc_conv_closed pp_dist_star)
  hence "x\<^sup>T \<le> (--y)\<^sup>T\<^sup>\<star> * x * top"
    using 1 comp_associative conv_dist_comp shunt_bijective by force
  also have "... = t\<^sup>T\<^sup>\<star> * x * top"
    using 3 mult_assoc by force
  finally have "x\<^sup>T * top * x\<^sup>T \<le> t\<^sup>T\<^sup>\<star>"
    using 1 comp_associative conv_dist_comp shunt_bijective by force
  hence "x\<^sup>T \<le> t\<^sup>T\<^sup>\<star>"
    using 1 by (metis arc_top_arc arc_conv_closed)
  also have "... \<le> (--?z)\<^sup>T\<^sup>\<star>"
    using 3 by (metis conv_order inf.orderE inf_pp_semi_commute star_isotone)
  finally have "x \<le> --?z\<^sup>\<star>"
    using conv_order conv_star_commute pp_dist_star by fastforce
  thus "\<exists>z . z \<le> y \<and> asymmetric z \<and> x \<le> --z\<^sup>\<star>"
    using 3 asymmetric_inf_closed inf.cobounded2 by blast
qed

subsection \<open>Extending partial orders to linear orders\<close>

text \<open>
We prove total correctness of Szpilrajn's algorithm \cite{Szpilrajn1930}.
A partial-correctness proof using Prover9 is given in \cite{BerghammerStruth2010}.
\<close>

theorem szpilrajn:
  "VARS e t
  [ order p \<and> regular p ]
  t := p;
  WHILE t \<squnion> t\<^sup>T \<noteq> top
    INV { order t \<and> regular t \<and> p \<le> t }
    VAR { card { x . regular x \<and> x \<le> -(t \<squnion> t\<^sup>T) } }
     DO e := choose_arc (-(t \<squnion> t\<^sup>T));
        t := t \<squnion> t * e * t
     OD
  [ linear_order t \<and> p \<le> t ]"
proof vcg_tc_simp
  fix t
  let ?e = "choose_arc (-t \<sqinter> -t\<^sup>T)"
  let ?tet = "t * ?e * t"
  let ?t = "t \<squnion> ?tet"
  let ?s1 = "{ x . regular x \<and> x \<le> -t \<and> x \<le> -?tet \<and> x \<le> -?t\<^sup>T }"
  let ?s2 = "{ x . regular x \<and> x \<le> -t \<and> x \<le> -t\<^sup>T }"
  assume 1: "reflexive t \<and> transitive t \<and> antisymmetric t \<and> regular t \<and> p \<le> t \<and> \<not> linear t"
  show "reflexive ?t \<and>
        transitive ?t \<and>
        antisymmetric ?t \<and>
        ?t = t \<squnion> --?tet \<and>
        p \<le> ?t \<and>
        card ?s1 < card ?s2"
  proof (intro conjI)
    show "reflexive ?t"
      using 1 by (simp add: sup.coboundedI1)
    have "-t \<sqinter> -t\<^sup>T \<noteq> bot"
      using 1 regular_closed_top regular_conv_closed by force
    hence 2: "arc ?e"
      using choose_arc_arc by blast
    have "?t * ?t = t * t \<squnion> t * ?tet \<squnion> ?tet * t \<squnion> ?tet * ?tet"
      by (smt (z3) mult_left_dist_sup mult_right_dist_sup sup_assoc)
    also have "... \<le> ?t"
    proof (intro sup_least)
      show "t * t \<le> ?t"
        using 1 sup.coboundedI1 by blast
      show "t * ?tet \<le> ?t"
        using 1 by (metis le_supI2 mult_left_isotone mult_assoc)
      show "?tet * t \<le> ?t"
        using 1 mult_right_isotone sup.coboundedI2 mult_assoc by auto
      have "?e * t * t * ?e \<le> ?e"
        using 2 by (smt arc_top_arc mult_assoc mult_right_isotone mult_left_isotone top_greatest)
      hence "transitive ?tet"
        by (smt mult_assoc mult_right_isotone mult_left_isotone)
      thus "?tet * ?tet \<le> ?t"
        using le_supI2 by auto
    qed
    finally show "transitive ?t"
      .
    have 3: "?e \<le> -t\<^sup>T"
      by (metis choose_arc_below inf.cobounded2 order_lesseq_imp p_dist_sup regular_closed_p)
    have 4: "?e \<le> -t"
      by (metis choose_arc_below inf.cobounded1 order_trans regular_closed_inf regular_closed_p)
    have "?t \<sqinter> ?t\<^sup>T = (t \<sqinter> t\<^sup>T) \<squnion> (t \<sqinter> ?tet\<^sup>T) \<squnion> (?tet \<sqinter> t\<^sup>T) \<squnion> (?tet \<sqinter> ?tet\<^sup>T)"
      by (smt (z3) conv_dist_sup inf_sup_distrib1 inf_sup_distrib2 sup_monoid.add_assoc)
    also have "... \<le> 1"
    proof (intro sup_least)
      show "antisymmetric t"
        using 1 by simp
      have "t * t * t = t"
        using 1 preorder_idempotent by fastforce
      also have "... \<le> -?e\<^sup>T"
        using 3 by (metis p_antitone_iff conv_complement conv_order conv_involutive)
      finally have "t\<^sup>T * ?e\<^sup>T * t\<^sup>T \<le> -t"
        using triple_schroeder_p by blast
      hence "t \<sqinter> ?tet\<^sup>T = bot"
        by (simp add: comp_associative conv_dist_comp p_antitone pseudo_complement_pp)
      thus "t \<sqinter> ?tet\<^sup>T \<le> 1"
        by simp
      thus "?tet \<sqinter> t\<^sup>T \<le> 1"
        by (smt conv_isotone inf_commute conv_one conv_dist_inf conv_involutive)
      have "?e * t * ?e \<le> ?e"
        using 2 by (smt arc_top_arc mult_assoc mult_right_isotone mult_left_isotone top_greatest)
      also have "... \<le> -t\<^sup>T"
        using 3 by simp
      finally have "?tet \<le> -?e\<^sup>T"
        by (metis conv_dist_comp schroeder_3_p triple_schroeder_p)
      hence "t * t * ?e * t * t \<le> -?e\<^sup>T"
        using 1 by (metis preorder_idempotent mult_assoc)
      hence "t\<^sup>T * ?e\<^sup>T * t\<^sup>T \<le> -?tet"
        using triple_schroeder_p mult_assoc by auto
      hence "?tet \<sqinter> ?tet\<^sup>T = bot"
        by (simp add: conv_dist_comp p_antitone pseudo_complement_pp mult_assoc)
      thus "antisymmetric ?tet"
        by simp
    qed
    finally show "antisymmetric ?t"
      .
    show "?t = t \<squnion> --?tet"
      using 1 choose_arc_regular regular_mult_closed by auto
    show "p \<le> ?t"
      using 1 by (simp add: le_supI1)
    show "card ?s1 < card ?s2"
    proof (rule psubset_card_mono)
      show "finite { x . regular x \<and> x \<le> -t \<and> x \<le> -t\<^sup>T }"
        using finite_regular by simp
      show "{ x . regular x \<and> x \<le> -t \<and> x \<le> -?tet \<and> x \<le> -?t\<^sup>T } \<subset> { x . regular x \<and> x \<le> -t \<and> x \<le> -t\<^sup>T }"
      proof -
        have "\<forall>x . regular x \<and> x \<le> -t \<and> x \<le> -?tet \<and> x \<le> -?t\<^sup>T \<longrightarrow> regular x \<and> x \<le> -t \<and> x \<le> -t\<^sup>T"
          using conv_dist_sup by auto
        hence 5: "{ x . regular x \<and> x \<le> -t \<and> x \<le> -?tet \<and> x \<le> -?t\<^sup>T } \<subseteq> { x . regular x \<and> x \<le> -t \<and> x \<le> -t\<^sup>T }"
          by blast
        have 6: "regular ?e \<and> ?e \<le> -t \<and> ?e \<le> -t\<^sup>T"
          using 2 3 4 choose_arc_regular by blast
        have "\<not> ?e \<le> -?tet"
        proof
          assume 7: "?e \<le> -?tet"
          have "?e \<le> ?e * t"
            using 1 by (meson mult_right_isotone mult_sub_right_one order.trans) 
          also have "?e * t \<le> -(t\<^sup>T * ?e)"
            using 7 p_antitone_iff schroeder_3_p mult_assoc by auto
          also have "... \<le> -(1\<^sup>T * ?e)"
            using 1 conv_isotone mult_left_isotone p_antitone by blast
          also have "... = -?e"
            by simp
          finally show False
            using 1 2 by (smt (z3) bot_least eq_refl inf.absorb1 pseudo_complement semiring.mult_not_zero top_le)
        qed
        thus ?thesis
          using 5 6 by blast
      qed
    qed
  qed
qed

text \<open>Theorem 15\<close>

lemma szpilrajn_exists:
  "order p \<and> regular p \<Longrightarrow> \<exists>t . linear_order t \<and> p \<le> t"
  using tc_extract_function szpilrajn by blast

lemma complement_one_transitively_orientable:
  "transitively_orientable (-1)"
proof -
  have "\<exists>t . linear_order t"
    using szpilrajn_exists bijective_one_closed bijective_regular order_one_closed by blast
  thus ?thesis
    using exists_split_characterisations(4) by blast
qed

end

end

end

