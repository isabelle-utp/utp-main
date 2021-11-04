(* Title:      Correctness of Path Algorithms
   Author:     Walter Guttmann, Peter Hoefner
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
               Peter Hoefner <peter at hoefner-online.de>
*)

section \<open>Correctness of Path Algorithms\<close>

text \<open>
To show that our theory of paths integrates with verification tasks, we verify the correctness of three basic path algorithms.
Algorithms at the presented level are executable and can serve prototyping purposes.
Data refinement can be carried out to move from such algorithms to more efficient programs.
The total-correctness proofs use a library developed in \cite{Guttmann2018c}.
\<close>

theory Path_Algorithms

imports "HOL-Hoare.Hoare_Logic" Rooted_Paths

begin

no_notation
  trancl ("(_\<^sup>+)" [1000] 999)

class choose_singleton_point_signature =
  fixes choose_singleton :: "'a \<Rightarrow> 'a"
  fixes choose_point :: "'a \<Rightarrow> 'a"

class relation_algebra_rtc_tarski_choose_point =
  relation_algebra_rtc_tarski + choose_singleton_point_signature +
  assumes choose_singleton_singleton: "x \<noteq> 0 \<Longrightarrow> singleton (choose_singleton x)"
  assumes choose_singleton_decreasing: "choose_singleton x \<le> x"
  assumes choose_point_point: "is_vector x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> point (choose_point x)"
  assumes choose_point_decreasing: "choose_point x \<le> x"
begin

no_notation
  composition (infixl ";" 75) and
  times (infixl "*" 70)

notation
  composition (infixl "*" 75)

subsection \<open>Construction of a path\<close>

text \<open>
Our first example is a basic greedy algorithm that constructs a path from a vertex $x$ to a different vertex $y$ of a directed acyclic graph $D$.
\<close>

abbreviation "construct_path_inv q x y D W \<equiv>
    is_acyclic D \<and> point x \<and> point y \<and> point q \<and>
    D\<^sup>\<star> * q \<le> D\<^sup>T\<^sup>\<star> * x \<and> W \<le> D \<and> terminating_path W \<and>
    (W = 0 \<longleftrightarrow> q=y) \<and> (W \<noteq> 0 \<longleftrightarrow> q = start_points W \<and> y = end_points W)"

abbreviation "construct_path_inv_simp q x y D W \<equiv>
    is_acyclic D \<and> point x \<and> point y \<and> point q \<and>
    D\<^sup>\<star> * q \<le> D\<^sup>T\<^sup>\<star> * x \<and> W \<le> D \<and> terminating_path W \<and>
    q = start_points W \<and> y = end_points W"

lemma construct_path_pre:
  assumes "is_acyclic D"
      and "point y"
      and "point x"
      and "D\<^sup>\<star> * y \<le> D\<^sup>T\<^sup>\<star> * x"
    shows "construct_path_inv y x y D 0"
  apply (intro conjI, simp_all add: assms is_inj_def is_p_fun_def path_def)
  using assms(2) cycle_iff by fastforce

text \<open>
The following three lemmas are auxiliary lemmas for \<open>construct_path_inv\<close>.
They are pulled out of the main proof to have more structure.
\<close>

lemma path_inv_points:
  assumes "construct_path_inv q x y D W \<and> q \<noteq> x"
  shows "point q"
    and "point (choose_point (D*q))"
 using assms apply blast
by (metis assms choose_point_point comp_assoc is_vector_def point_def reachable_implies_predecessor)

lemma path_inv_choose_point_decrease:
  assumes "construct_path_inv q x y D W \<and> q \<noteq> x"
    shows "W\<noteq>0 \<Longrightarrow> choose_point (D*q) \<le> -((W + choose_point (D*q) * q\<^sup>T)\<^sup>T*1)"
proof -
  let ?q = "choose_point (D*q)"
  let ?W = "W + ?q * q\<^sup>T"
  assume as: "W\<noteq>0"
  hence "q*W \<le> W\<^sup>+" (* "connected_root q W" *)
    by (metis assms conv_contrav conv_invol conv_iso conv_terminating_path
              forward_terminating_path_end_points_1 plus_conv point_def ss423bij
              terminating_path_iff)
  hence "?q \<cdot> W\<^sup>T*1 \<le> D*q \<cdot> W\<^sup>T\<^sup>+*q"
    using choose_point_decreasing meet_iso meet_isor inf_mono assms connected_root_iff2 by simp
  also have "... \<le> (D \<cdot> D\<^sup>T\<^sup>+)*q"
    by (metis assms inj_distr point_def conv_contrav conv_invol conv_iso meet_isor
              mult_isol_var mult_isor star_conv star_slide_var star_subdist sup.commute sup.orderE)
  also have "... \<le> 0"
    by (metis acyclic_trans assms conv_zero step_has_target eq_iff galois_aux ss_p18)
  finally have a: "?q \<le> -(W\<^sup>T*1)"
    using galois_aux le_bot by blast

  have "point ?q"
    using assms by(rule path_inv_points(2))
  hence "?q \<le> -(q*?q\<^sup>T*1)"
    by (metis assms acyclic_imp_one_step_different_points(2) point_is_point
            choose_point_decreasing edge_end end_point_char end_point_no_successor)
  with a show ?thesis
    by (simp add: inf.boundedI)
qed

lemma end_points:
  assumes "construct_path_inv q x y D W \<and> q \<noteq> x"
    shows "choose_point (D*q) = start_points (W + choose_point (D*q) * q\<^sup>T)"
      and "y = end_points (W + choose_point (D*q) * q\<^sup>T)"
proof -
  let ?q = "choose_point (D*q)"
  let ?W = "W + ?q * q\<^sup>T"
  show 1: "?q = start_points ?W"
  proof (rule antisym)
    show" start_points ?W \<le> ?q"
      by (metis assms(1) path_inv_points(2) acyclic_imp_one_step_different_points(2)
                choose_point_decreasing edge_end edge_start sup.commute
                path_concatenation_start_points_approx point_is_point eq_iff sup_bot_left)
    show "?q \<le> start_points ?W"
    proof -
      have a: "?q = ?q*q\<^sup>T*1"
        by (metis assms(1) comp_assoc point_equations(1) point_is_point aux4 conv_zero
                  choose_point_decreasing choose_point_point conv_contrav conv_one point_def
                  inf.orderE inf_compl_bot inf_compl_bot_right is_vector_def maddux_142
                  sup_bot_left sur_def_var1)
      hence "?q =(q \<cdot> -q) + (?q \<cdot> -q \<cdot> -(?W\<^sup>T*1))"
        by (metis assms path_inv_points(2) path_inv_choose_point_decrease
                  acyclic_imp_one_step_different_points(1) choose_point_decreasing inf.orderE
                  inf_compl_bot sup_inf_absorb edge_start point_is_point sup_bot_left)
      also have "... \<le> (W*1 \<cdot> -(?W\<^sup>T*1) \<cdot> -q) + (?q \<cdot> -q \<cdot> -(?W\<^sup>T*1))"
        by simp
      also have "... = (W*1 + ?q) \<cdot> -(q + ?W\<^sup>T*1)"
        by (metis compl_sup inf_sup_distrib2 meet_assoc sup.commute)
      also have "... \<le> ?W*1 \<cdot> -(?W\<^sup>T*1)"
        using a by (metis inf.left_commute distrib_right' compl_sup inf.cobounded2)
      finally show "?q \<le> start_points ?W" .
    qed
  qed
  show "y = end_points ?W"
  proof -
    have point_nq: "point ?q"
      using assms by(rule path_inv_points(2))
    hence yp: "y \<le> -?q"
      using 1 assms
      by (metis acyclic_imp_one_step_different_points(2) choose_point_decreasing cycle_no_points(1)
                finite_iff finite_iff_msc forward_finite_iff_msc path_aux1a path_edge_equals_cycle
                point_is_point point_not_equal(1) terminating_iff1)
    have "y = y + (W*1 \<cdot> -(W\<^sup>T*1) \<cdot> -(W*1))"
      by (simp add: inf.commute)
    also have "... = y + (q \<cdot> -(W*1))"
      using assms by fastforce
    also have "... = y + (q \<cdot> -(W*1) \<cdot> -?q)"
      by (metis calculation sup_assoc sup_inf_absorb)
    also have "... = (y \<cdot> -?q) + (q \<cdot> -(W*1) \<cdot> -?q)"
      using yp by (simp add: inf.absorb1)
    also have "... = (W\<^sup>T*1 \<cdot> -(W*1) \<cdot> -?q) + (q \<cdot> -(W*1) \<cdot> -?q)"
      using assms by fastforce
    also have "... = (W\<^sup>T*1 + q) \<cdot> -(W*1) \<cdot> -?q"
      by (simp add: inf_sup_distrib2)
    also have "... = (W\<^sup>T*1 + q) \<cdot> -(W*1 + ?q)"
      by (simp add: inf.assoc)
    also have "... = (W\<^sup>T*1 + q*?q\<^sup>T*1) \<cdot> -(W*1 + ?q*q\<^sup>T*1)"
      using point_nq
      by(metis assms(1) comp_assoc conv_contrav conv_one is_vector_def point_def sur_def_var1)
    also have "... = (?W\<^sup>T)*1 \<cdot> -(?W*1)"
      by simp
    finally show ?thesis .
  qed
qed

lemma construct_path_inv:
  assumes "construct_path_inv q x y D W \<and> q \<noteq> x"
  shows "construct_path_inv (choose_point (D*q)) x y D (W + choose_point (D*q)*q\<^sup>T)"
proof (intro conjI)
  let ?q = "choose_point (D*q)"
  let ?W = "W + ?q * q\<^sup>T"
  show "is_acyclic D"
    using assms by blast
  show point_y: "point y"
    using assms by blast
  show "point x"
    using assms by blast
  show "?W \<le> D"
    using assms choose_point_decreasing le_sup_iff point_def ss423bij inf.boundedE by blast
  show "D\<^sup>\<star>*?q \<le> D\<^sup>T\<^sup>\<star>*x"
  proof -
    have "D\<^sup>+*q \<le> D\<^sup>T\<^sup>\<star>*x"
      using assms conv_galois_2 order_trans star_1l by blast
    thus ?thesis
      by (metis choose_point_decreasing comp_assoc dual_order.trans mult_isol star_slide_var)
  qed
  show point_nq: "point ?q"
    using assms by(rule path_inv_points(2))
  show pathW: "path ?W"
    proof(cases "W=0")
      assume "W=0"
      thus ?thesis
        using assms edge_is_path point_is_point point_nq by simp
    next
      assume a: "W\<noteq>0"
      have b: "?q*q\<^sup>T \<le> 1*?q*q\<^sup>T*-(?q*q\<^sup>T*1)"
      proof -
        have "?q*q\<^sup>T \<le>1" by simp
        thus ?thesis
          using assms point_nq
          by(metis different_points_consequences(1) point_def sur_def_var1
               acyclic_imp_one_step_different_points(2) choose_point_decreasing comp_assoc
               is_vector_def point_def point_equations(3,4) point_is_point)
      qed
      have c: "W \<le> -(1*W)*W*1"
        using assms terminating_path_iff by blast
      have d: "(?q*q\<^sup>T)\<^sup>T*1 \<cdot> -((?q*q\<^sup>T)*1) = W*1 \<cdot> -(W\<^sup>T*1)"
        using a
        by (metis assms path_inv_points(2) acyclic_reachable_points choose_point_decreasing
                  edge_end point_is_point comp_assoc point_def sur_total total_one)
      have e: "?q*q\<^sup>T*1 \<cdot> W\<^sup>T*1 = 0"
      proof -
        have "?q*q\<^sup>T*1 \<cdot> W\<^sup>T*1 = ?q \<cdot> W\<^sup>T*1"
          using assms point_nq
          by (metis comp_assoc conv_contrav conv_one is_vector_def point_def sur_def_var1)
        also have "... \<le> -(?W\<^sup>T*1) \<cdot> ?W\<^sup>T*1"
          using assms path_inv_choose_point_decrease
          by (smt a conv_contrav conv_iso conv_one inf_mono less_eq_def subdistl_eq)
        also have "... \<le> 0"
          using compl_inf_bot eq_refl by blast
        finally show ?thesis
          using bot_unique by blast
      qed
      show ?thesis
      using b c d e by (metis assms comp_assoc edge_is_path path_concatenation_cycle_free
                                point_is_point sup.commute point_nq)
  qed
  show "?W = 0 \<longleftrightarrow> ?q = y"
    apply (rule iffI)
    apply (metis assms conv_zero dist_alt edge_start inf_compl_bot_right modular_1_aux' modular_2_aux'
              point_is_point sup.left_idem sup_bot_left point_nq)
    by (smt assms end_points(1) conv_contrav conv_invol cycle_no_points(1) end_point_iff2 has_start_end_points_iff path_aux1b path_edge_equals_cycle point_is_point start_point_iff2 sup_bot_left top_greatest pathW)
  show "?W\<noteq>0 \<longleftrightarrow> ?q = start_points ?W \<and> y = end_points ?W"
    apply (rule iffI)
    using assms end_points apply blast
    using assms by force
  show "terminating ?W"
    by (smt assms end_points end_point_iff2 has_start_end_points_iff point_is_point start_point_iff2
            terminating_iff1 pathW point_nq)
qed

theorem construct_path_partial: "VARS p q W
  { is_acyclic D \<and> point y \<and> point x \<and> D\<^sup>\<star>*y \<le> D\<^sup>T\<^sup>\<star>*x }
  W := 0;
  q := y;
  WHILE q \<noteq> x
    INV { construct_path_inv q x y D W }
     DO p := choose_point (D*q);
        W := W + p*q\<^sup>T;
        q := p
     OD
  { W \<le> D \<and> terminating_path W \<and> (W=0 \<longleftrightarrow> x=y) \<and> (W\<noteq>0 \<longleftrightarrow> x = start_points W \<and> y = end_points W) }"
  apply vcg
  using construct_path_pre apply blast
  using construct_path_inv apply blast
  by fastforce

end (* relation_algebra_rtc_tarski_choose_point *)

text \<open>For termination, we additionally need finiteness.\<close>

context finite
begin

lemma decrease_set:
  assumes "\<forall>x::'a . Q x \<longrightarrow> P x"
      and "P w"
      and "\<not> Q w"
    shows "card { x . Q x } < card { x . P x }"
by (metis Collect_mono assms card_seteq finite mem_Collect_eq not_le)

end

class relation_algebra_rtc_tarski_choose_point_finite =
      relation_algebra_rtc_tarski_choose_point + relation_algebra_rtc_tarski_point_finite
begin

lemma decrease_variant:
  assumes "y \<le> z"
      and "w \<le> z"
      and "\<not> w \<le> y"
    shows "card { x . x \<le> y } < card { x . x \<le> z }"
by (metis Collect_mono assms card_seteq linorder_not_le dual_order.trans finite_code mem_Collect_eq)

lemma construct_path_inv_termination:
  assumes "construct_path_inv q x y D W \<and> q \<noteq> x"
    shows "card { z . z \<le> -(W + choose_point (D*q)*q\<^sup>T) } < card { z . z \<le> -W }"
proof -
  let ?q = "choose_point (D*q)"
  let ?W = "W + ?q * q\<^sup>T"
  show ?thesis
  proof (rule decrease_variant)
    show "-?W \<le> -W"
      by simp
    show "?q * q\<^sup>T \<le> -W"
      by (metis assms galois_aux inf_compl_bot_right maddux_142 mult_isor order_trans top_greatest)
    show "\<not> (?q * q\<^sup>T \<le> -?W)"
      using assms end_points(1)
      by (smt acyclic_imp_one_step_different_points(2) choose_point_decreasing compl_sup inf.absorb1
              inf_compl_bot_right sup.commute sup_bot.left_neutral conv_zero end_points(2))
  qed
qed

theorem construct_path_total: "VARS p q W
  [ is_acyclic D \<and> point y \<and> point x \<and> D\<^sup>\<star>*y \<le> D\<^sup>T\<^sup>\<star>*x ]
  W := 0;
  q := y;
  WHILE q \<noteq> x
    INV { construct_path_inv q x y D W }
    VAR { card { z . z \<le> -W } }
     DO p := choose_point (D*q);
        W := W + p*q\<^sup>T;
        q := p
     OD
  [ W \<le> D \<and> terminating_path W \<and> (W=0 \<longleftrightarrow> x=y) \<and> (W\<noteq>0 \<longleftrightarrow> x = start_points W \<and> y = end_points W) ]"
  apply vcg_tc
  using construct_path_pre apply blast
  apply (rule CollectI, rule conjI)
  using construct_path_inv apply blast
  using construct_path_inv_termination apply clarsimp
  by fastforce


end (* relation_algebra_rtc_tarski_choose_point_finite *)

subsection \<open>Topological sorting\<close>

text \<open>
In our second example we look at topological sorting.
Given a directed acyclic graph, the problem is to construct a linear order of its vertices that contains $x$ before $y$ for each edge $(x,y)$ of the graph.
If the input graph models dependencies between tasks, the output is a linear schedule of the tasks that respects all dependencies.
\<close>

context relation_algebra_rtc_tarski_choose_point
begin

abbreviation topological_sort_inv
  where "topological_sort_inv q v R W \<equiv>
         regressively_finite R \<and> R \<cdot> v*v\<^sup>T \<le> W\<^sup>+ \<and> terminating_path W \<and> W*1 = v\<cdot>-q \<and>
         (W = 0 \<or> q = end_points W) \<and> point q \<and> R*v \<le> v \<and> q \<le> v \<and> is_vector v"

lemma topological_sort_pre:
  assumes "regressively_finite R"
  shows "topological_sort_inv (choose_point (minimum R 1)) (choose_point (minimum R 1)) R 0"
proof (intro conjI,simp_all add:assms)
  let ?q = "choose_point (- (R\<^sup>T * 1))"
  show point_q: "point ?q"
    using assms by (metis (full_types) annir choose_point_point galois_aux2 is_inj_def is_sur_def
                          is_vector_def one_idem_mult point_def ss_p18 inf_top_left one_compl)
  show "R \<cdot> ?q * ?q\<^sup>T \<le> 0"
    by (metis choose_point_decreasing conv_invol end_point_char eq_iff inf_bot_left schroeder_2)
  show "path 0"
    by (simp add: is_inj_def is_p_fun_def path_def)
  show "R*?q \<le> ?q"
    by (metis choose_point_decreasing compl_bot_eq conv_galois_1 inf_compl_bot_left2 le_inf_iff)
  show "is_vector ?q"
    using point_q point_def by blast
qed

lemma topological_sort_inv:
  assumes "v \<noteq> 1"
      and "topological_sort_inv q v R W"
    shows "topological_sort_inv (choose_point (minimum R (- v))) (v +
                      choose_point (minimum R (- v))) R (W + q * choose_point (minimum R (- v))\<^sup>T)"
proof (intro conjI)
  let ?p = "choose_point (minimum R (-v))"
  let ?W = "W + q*?p\<^sup>T"
  let ?v = "v + ?p"
  show point_p: "point ?p"
    using assms
    by (metis choose_point_point compl_bot_eq double_compl galois_aux2 comp_assoc is_vector_def
              vector_compl vector_mult)
  hence ep_np: "end_points (q*?p\<^sup>T) = ?p"
    using assms(2)
    by (metis aux4 choose_point_decreasing edge_end le_supI1 point_in_vector_or_complement_iff
              point_is_point)
  hence sp_q: "start_points (q*?p\<^sup>T) = q"
    using assms(2) point_p
    by (metis (no_types, lifting) conv_contrav conv_invol edge_start point_is_point)
  hence ep_sp: "W \<noteq> 0 \<Longrightarrow> end_points W = start_points (q*?p\<^sup>T)"
    using assms(2) by force
  have "W*1 \<cdot> (q*?p\<^sup>T)\<^sup>T*1 = v\<cdot>-q\<cdot>?p"
    using assms(2) point_p is_vector_def mult_assoc point_def point_equations(3) point_is_point
    by auto
  hence 1: "W*1 \<cdot> (q*?p\<^sup>T)\<^sup>T*1 = 0"
    by (metis choose_point_decreasing dual_order.trans galois_aux inf.cobounded2 inf.commute)

  show "regressively_finite R"
    using assms(2) by blast
  show "R \<cdot> ?v*?v\<^sup>T \<le> ?W\<^sup>+"
  proof -
    have a: "R \<cdot> v*v\<^sup>T \<le> ?W\<^sup>+"
      using assms(2) by (meson mult_isol_var order.trans order_prop star_subdist)
    have b: "R \<cdot> v*?p\<^sup>T \<le> ?W\<^sup>+"
    proof -
      have "R \<cdot> v*?p\<^sup>T \<le> W*1*?p\<^sup>T + q*?p\<^sup>T"
        by (metis inf_le2 assms(2) aux4 double_compl inf_absorb2 distrib_right)
      also have "... = W*?p\<^sup>T + q*?p\<^sup>T"
        using point_p by (metis conv_contrav conv_one is_vector_def mult_assoc point_def)
      also have "... \<le> W\<^sup>+*end_points W*?p\<^sup>T + q*?p\<^sup>T"
        using assms(2)
        by (meson forward_terminating_path_end_points_1 join_iso mult_isor terminating_path_iff)
      also have "... \<le> W\<^sup>+*q*?p\<^sup>T + q*?p\<^sup>T"
        using assms(2) by (metis annil eq_refl)
      also have "... = W\<^sup>\<star>*q*?p\<^sup>T"
        using conway.dagger_unfoldl_distr mult_assoc sup_commute by fastforce
      also have "... \<le> ?W\<^sup>+"
        by (metis mult_assoc mult_isol_var star_slide_var star_subdist sup_ge2)
      finally show ?thesis .
    qed
    have c: "R \<cdot> ?p*v\<^sup>T \<le> ?W\<^sup>+"
    proof -
      have "v \<le> -?p"
        using choose_point_decreasing compl_le_swap1 inf_le1 order_trans by blast
      hence "R*v \<le> -?p"
        using assms(2) order.trans by blast
      thus ?thesis
        by (metis galois_aux inf_le2 schroeder_2)
    qed
    have d: "R \<cdot> ?p*?p\<^sup>T \<le> ?W\<^sup>+"
    proof -
      have "R \<cdot> ?p*?p\<^sup>T \<le> R \<cdot> 1'"
        using point_p is_inj_def meet_isor point_def by blast
      also have "... = 0"
        using assms(2) regressively_finite_irreflexive galois_aux by blast
      finally show ?thesis
        using bot_least inf.absorb_iff2 by simp
    qed
    have "R \<cdot> ?v*?v\<^sup>T = (R \<cdot> v*v\<^sup>T) + (R \<cdot> v*?p\<^sup>T) + (R \<cdot> ?p*v\<^sup>T) + (R \<cdot> ?p*?p\<^sup>T)"
      by (metis conv_add distrib_left distrib_right inf_sup_distrib1 sup.commute sup.left_commute)
    also have "... \<le> ?W\<^sup>+"
      using a b c d by (simp add: le_sup_iff)
    finally show ?thesis .
  qed
  show pathW: "path ?W"
  proof (cases "W = 0")
    assume "W = 0"
    thus ?thesis
      using assms(2) point_p edge_is_path point_is_point sup_bot_left by auto
  next
    assume a1: "W \<noteq> 0"
    have fw_path: "forward_terminating_path W"
      using assms(2) terminating_iff by blast
    have bw_path: "backward_terminating_path (q*?p\<^sup>T)"
      using assms point_p sp_q
      by (metis conv_backward_terminating conv_has_start_points conv_path edge_is_path
                forward_terminating_iff1 point_is_point start_point_iff2)
    show ?thesis
      using fw_path bw_path ep_sp 1 a1 path_concatenation_cycle_free by blast
  qed
  show "terminating ?W"
  proof (rule start_end_implies_terminating)
    show "has_start_points ?W"
      apply (cases "W = 0")
      using assms(2) sp_q pathW
      apply (metis (no_types, lifting) point_is_point start_point_iff2 sup_bot.left_neutral)
      using assms(2) ep_sp 1 pathW
      by (metis has_start_end_points_iff path_concatenation_start_points start_point_iff2
                terminating_iff1)
    show "has_end_points ?W"
      apply (cases "W = 0")
      using point_p ep_np ep_sp pathW end_point_iff2 point_is_point apply force
      using point_p ep_np ep_sp 1 pathW
      by (metis end_point_iff2 path_concatenation_end_points point_is_point)
  qed
  show "?W*1 = ?v\<cdot>-?p"
  proof -
    have "?W*1 = v"
      by (metis assms(2) point_p is_vector_def mult_assoc point_def point_equations(3)
                point_is_point aux4 distrib_right' inf_absorb2 sup.commute)
    also have "... = v\<cdot>-?p"
      by (metis choose_point_decreasing compl_le_swap1 inf.cobounded1 inf.orderE order_trans)
    finally show ?thesis
      by (simp add: inf_sup_distrib2)
  qed
  show "?W = 0 \<or> ?p = end_points ?W"
    using ep_np ep_sp 1 by (metis path_concatenation_end_points sup_bot_left)
  show "R*?v \<le> ?v"
    using assms(2)
    by (meson choose_point_decreasing conv_galois_1 inf.cobounded2 order.trans sup.coboundedI1
              sup_least)
  show "?p \<le> ?v"
    by simp
  show "is_vector ?v"
    using assms(2) point_p point_def vector_add by blast
qed

lemma topological_sort_post:
 assumes "\<not> v \<noteq> 1"
     and "topological_sort_inv q v R W"
   shows "R \<le> W\<^sup>+ \<and> terminating_path W \<and> (W + W\<^sup>T)*1 = -1'*1"
proof (intro conjI,simp_all add:assms)
  show "R \<le> W\<^sup>+"
    using assms by force
  show " backward_terminating W \<and> W \<le> 1 * W * (- v + q)"
    using assms by force
  show "v \<cdot> - q + W\<^sup>T * 1 = - 1' * 1"
    proof (cases "W = 0")
      assume "W = 0"
      thus ?thesis
        using assms
        by (metis compl_bot_eq conv_one conv_zero double_compl inf_top.left_neutral is_inj_def
                  le_bot mult_1_right one_idem_mult point_def ss_p18 star_zero sup.absorb2 top_le)
    next
      assume a1: "W \<noteq> 0"
      hence "-1' \<noteq> 0"
        using assms backward_terminating_path_irreflexive le_bot by fastforce
      hence "1 = 1*-1'*1"
        by (simp add: tarski)
      also have "... = -1'*1"
        by (metis comp_assoc distrib_left mult_1_left sup_top_left distrib_right sup_compl_top)
      finally have a: "1 = -1'*1" .
      have "W*1 + W\<^sup>T*1 = 1"
        using assms a1 by (metis double_compl galois_aux4 inf.absorb_iff2 inf_top.left_neutral)
      thus ?thesis
        using a by (simp add: assms(2))
    qed
qed

theorem topological_sort_partial: "VARS p q v W
  { regressively_finite R }
  W := 0;
  q := choose_point (minimum R 1);
  v := q;
  WHILE v \<noteq> 1
    INV { topological_sort_inv q v R W }
     DO p := choose_point (minimum R (-v));
        W := W + q*p\<^sup>T;
        q := p;
        v := v + p
     OD
  { R \<le> W\<^sup>+ \<and> terminating_path W \<and> (W + W\<^sup>T)*1 = -1'*1 }"
  apply vcg
  using topological_sort_pre apply blast
  using topological_sort_inv apply blast
  using topological_sort_post by blast

end (* relation_algebra_rtc_tarski_choose_point *)

context relation_algebra_rtc_tarski_choose_point_finite
begin

lemma topological_sort_inv_termination:
  assumes "v \<noteq> 1"
      and "topological_sort_inv q v R W"
    shows "card {z . z \<le> -(v + choose_point (minimum R (-v)))} < card { z . z \<le> -v }"
proof (rule decrease_variant)
  let ?p = "choose_point (minimum R (-v))"
  let ?v = "v + ?p"
  show "-?v \<le> -v"
    by simp
  show "?p \<le> -v"
    using choose_point_decreasing inf.boundedE by blast
  have "point ?p"
    using assms
    by (metis choose_point_point compl_bot_eq double_compl galois_aux2 comp_assoc is_vector_def
              vector_compl vector_mult)
  thus "\<not> (?p \<le> -?v)"
    by (metis annir compl_sup inf.absorb1 inf_compl_bot_right maddux_20 no_end_point_char)
qed

text \<open>
Use precondition \<open>is_acyclic\<close> instead of \<open>regressively_finite\<close>.
They are equivalent for finite graphs.
\<close>

theorem topological_sort_total: "VARS p q v W
  [ is_acyclic R ]
  W := 0;
  q := choose_point (minimum R 1);
  v := q;
  WHILE v \<noteq> 1
    INV { topological_sort_inv q v R W }
    VAR { card { z . z \<le> -v } }
      DO p := choose_point (minimum R (-v));
         W := W + q*p\<^sup>T;
         q := p;
         v := v + p
      OD
   [ R \<le> W\<^sup>+ \<and> terminating_path W \<and> (W + W\<^sup>T)*1 = -1'*1 ]"
  apply vcg_tc
  apply (drule acyclic_regressively_finite)
  using topological_sort_pre apply blast
  apply (rule CollectI, rule conjI)
  using topological_sort_inv apply blast
  using topological_sort_inv_termination apply auto[1]
  using topological_sort_post by blast

end (* relation_algebra_rtc_tarski_choose_point_finite *)

subsection \<open>Construction of a tree\<close>

text \<open>
Our last application is a correctness proof of an algorithm that constructs a non-empty cycle for a given directed graph.
This works in two steps.
The first step is to construct a directed tree from a given root along the edges of the graph.
\<close>

context relation_algebra_rtc_tarski_choose_point
begin

abbreviation construct_tree_pre
  where "construct_tree_pre x y R \<equiv> y \<le> R\<^sup>T\<^sup>\<star>*x \<and> point x"
abbreviation construct_tree_inv
  where "construct_tree_inv v x y D R \<equiv> construct_tree_pre x y R \<and> is_acyclic D \<and> is_inj D \<and>
                                         D \<le> R \<and> D*x = 0 \<and> v = x + D\<^sup>T*1 \<and> x*v\<^sup>T \<le> D\<^sup>\<star> \<and> D \<le> v*v\<^sup>T \<and>
                                         is_vector v"
abbreviation construct_tree_post
  where "construct_tree_post x y D R \<equiv> is_acyclic D \<and> is_inj D \<and> D \<le> R \<and> D*x = 0 \<and> D\<^sup>T*1 \<le> D\<^sup>T\<^sup>\<star>*x \<and>
                                        D\<^sup>\<star>*y \<le> D\<^sup>T\<^sup>\<star>*x"

lemma construct_tree_pre:
  assumes "construct_tree_pre x y R"
    shows "construct_tree_inv x x y 0 R"
using assms by (simp add: is_inj_def point_def)

lemma construct_tree_inv_aux:
  assumes "\<not> y \<le> v"
      and "construct_tree_inv v x y D R"
    shows "singleton (choose_singleton (v*-v\<^sup>T \<cdot> R))"
proof (rule choose_singleton_singleton, rule notI)
  assume "v*-v\<^sup>T \<cdot> R = 0"
  hence "R\<^sup>T\<^sup>\<star>*v \<le> v"
    by (metis galois_aux conv_compl conv_galois_1 conv_galois_2 conv_invol double_compl
              star_inductl_var)
  hence "y = 0"
    using assms by (meson mult_isol order_trans sup.cobounded1)
  thus False
   using assms point_is_point by auto
qed

lemma construct_tree_inv:
  assumes "\<not> y \<le> v"
      and "construct_tree_inv v x y D R"
    shows "construct_tree_inv (v + choose_singleton (v*-v\<^sup>T \<cdot> R)\<^sup>T*1) x y (D +
                               choose_singleton (v*-v\<^sup>T \<cdot> R)) R"
proof (intro conjI)
  let ?e = "choose_singleton (v*-v\<^sup>T \<cdot> R)"
  let ?D = "D + ?e"
  let ?v = "v + ?e\<^sup>T*1"
  have 1: "?e \<le> v*-v\<^sup>T"
    using choose_singleton_decreasing inf.boundedE by blast
  show "point x"
    by (simp add: assms)
  show "y \<le> R\<^sup>T\<^sup>\<star>*x"
    by (simp add: assms)
  show "is_acyclic ?D"
    using 1 assms acyclic_inv by fastforce
  show "is_inj ?D"
    using 1 construct_tree_inv_aux assms injective_inv by blast
  show "?D \<le> R"
    apply (rule sup.boundedI)
    using assms apply blast
    using choose_singleton_decreasing inf.boundedE by blast
  show "?D*x = 0"
  proof -
    have "?D*x = ?e*x"
      by (simp add: assms)
    also have "... \<le> ?e*v"
      by (simp add: assms mult_isol)
    also have "... \<le> v*-v\<^sup>T*v"
      using 1 mult_isor by blast
    also have "... = 0"
      by (metis assms(2) annir comp_assoc vector_prop1)
    finally show ?thesis
      using le_bot by blast
  qed
  show "?v = x + ?D\<^sup>T*1"
    by (simp add: assms sup_assoc)
  show "x*?v\<^sup>T \<le> ?D\<^sup>\<star>"
  proof -
    have "x*?v\<^sup>T = x*v\<^sup>T + x*1*?e"
      by (simp add: distrib_left mult_assoc)
    also have "... \<le> D\<^sup>\<star> + x*1*(?e \<cdot> v*-v\<^sup>T)"
      using 1 by (metis assms(2) inf.absorb1 join_iso)
    also have "... = D\<^sup>\<star> + x*1*(?e \<cdot> v \<cdot> -v\<^sup>T)"
      by (metis assms(2) comp_assoc conv_compl inf.assoc vector_compl vector_meet_comp)
    also have "... \<le> D\<^sup>\<star> + x*1*(?e \<cdot> v)"
      using join_isol mult_subdistl by fastforce
    also have "... = D\<^sup>\<star> + x*(1 \<cdot> v\<^sup>T)*?e"
      by (metis assms(2) inf.commute mult_assoc vector_2)
    also have "... = D\<^sup>\<star> + x*v\<^sup>T*?e"
      by simp
    also have "... \<le> D\<^sup>\<star> + D\<^sup>\<star>*?e"
      using assms join_isol mult_isor by blast
    also have "... \<le> ?D\<^sup>\<star>"
      by (meson le_sup_iff prod_star_closure star_ext star_subdist)
    finally show ?thesis .
  qed
  show "?D \<le> ?v*?v\<^sup>T"
  proof (rule sup.boundedI)
    show "D \<le> ?v*?v\<^sup>T"
      using assms
      by (meson conv_add distrib_left le_supI1 conv_iso dual_order.trans mult_isol_var order_prop)
    have "?e \<le> v*(-v\<^sup>T \<cdot> v\<^sup>T*?e)"
      using 1 inf.absorb_iff2 modular_1' by fastforce
    also have "... \<le> v*1*?e"
      by (simp add: comp_assoc le_infI2 mult_isol_var)
    also have "... \<le> ?v*?v\<^sup>T"
      by (metis conv_contrav conv_invol conv_iso conv_one mult_assoc mult_isol_var sup.cobounded1
                sup_ge2)
    finally show "?e \<le> ?v*?v\<^sup>T"
      by simp
  qed
  show "is_vector ?v"
    using assms comp_assoc is_vector_def by fastforce
qed

lemma construct_tree_post:
  assumes "y \<le> v"
      and "construct_tree_inv v x y D R"
    shows "construct_tree_post x y D R"
proof -
  have "v*x\<^sup>T \<le> D\<^sup>T\<^sup>\<star>"
    by (metis (no_types, lifting) assms(2) conv_contrav conv_invol conv_iso star_conv)
  hence 1: "v \<le> D\<^sup>T\<^sup>\<star>*x"
    using assms point_def ss423bij by blast
  hence 2: "D\<^sup>T*1 \<le> D\<^sup>T\<^sup>\<star>*x"
    using assms le_supE by blast
  have "D\<^sup>\<star>*y \<le> D\<^sup>T\<^sup>\<star>*x"
  proof (rule star_inductl, rule sup.boundedI)
    show "y \<le> D\<^sup>T\<^sup>\<star>*x"
      using 1 assms order.trans by blast
  next
    have "D*(D\<^sup>T\<^sup>\<star>*x) = D*x + D*D\<^sup>T\<^sup>+*x"
      by (metis conway.dagger_unfoldl_distr distrib_left mult_assoc)
    also have "... = D*D\<^sup>T\<^sup>+*x"
      using assms by simp
    also have "... \<le> 1'*D\<^sup>T\<^sup>\<star>*x"
      by (metis assms(2) is_inj_def mult_assoc mult_isor)
    finally show "D*(D\<^sup>T\<^sup>\<star>*x) \<le> D\<^sup>T\<^sup>\<star>*x"
      by simp
  qed
  thus "construct_tree_post x y D R"
    using 2 assms by simp
qed

theorem construct_tree_partial: "VARS e v D
  { construct_tree_pre x y R }
  D := 0;
  v := x;
  WHILE \<not> y \<le> v
    INV { construct_tree_inv v x y D R }
     DO e := choose_singleton (v*-v\<^sup>T \<cdot> R);
        D := D + e;
        v := v + e\<^sup>T*1
     OD
  { construct_tree_post x y D R }"
 apply vcg
 using construct_tree_pre apply blast
 using construct_tree_inv apply blast
 using construct_tree_post by blast

end (* relation_algebra_rtc_tarski_choose_point *)

context relation_algebra_rtc_tarski_choose_point_finite
begin

lemma construct_tree_inv_termination:
 assumes " \<not> y \<le> v"
     and "construct_tree_inv v x y D R"
   shows "card { z . z \<le> -(v + choose_singleton (v*-v\<^sup>T \<cdot> R)\<^sup>T*1) } < card { z . z \<le> -v }"
proof (rule decrease_variant)
  let ?e = "choose_singleton (v*-v\<^sup>T \<cdot> R)"
  let ?v = "v + ?e\<^sup>T*1"
  have 1: "?e \<le> v*-v\<^sup>T"
    using choose_singleton_decreasing inf.boundedE by blast
  have 2: "singleton ?e"
    using construct_tree_inv_aux assms by auto
  show "-?v \<le> -v"
    by simp
  have "?e\<^sup>T \<le> -v*v\<^sup>T"
    using 1 conv_compl conv_iso by force
  also have "... \<le> -v*1"
    by (simp add: mult_isol)
  finally show "?e\<^sup>T*1 \<le> -v"
    using assms by (metis is_vector_def mult_isor one_compl)
  thus "\<not> (?e\<^sup>T*1 \<le> -?v)"
    using 2 by (metis annir compl_sup inf.absorb1 inf_compl_bot_right surj_one tarski)
qed

theorem construct_tree_total: "VARS e v D
 [ construct_tree_pre x y R ]
 D := 0;
 v := x;
 WHILE \<not> y \<le> v
   INV { construct_tree_inv v x y D R }
   VAR { card { z . z \<le> -v } }
    DO e := choose_singleton (v*-v\<^sup>T \<cdot> R);
       D := D + e;
       v := v + e\<^sup>T*1
    OD
 [ construct_tree_post x y D R ]"
  apply vcg_tc
  using construct_tree_pre apply blast
  apply (rule CollectI, rule conjI)
  using construct_tree_inv apply blast
  using construct_tree_inv_termination apply force
  using construct_tree_post by blast

end (* relation_algebra_rtc_tarski_choose_point_finite *)

subsection \<open>Construction of a non-empty cycle\<close>

text \<open>
The second step is to construct a path from the root to a given vertex in the tree.
Adding an edge back to the root gives the cycle.
\<close>

context relation_algebra_rtc_tarski_choose_point
begin

abbreviation comment
  where "comment _ \<equiv> SKIP" (* instead of inner comments *)
abbreviation construct_cycle_inv
  where "construct_cycle_inv v x y D R \<equiv> construct_tree_inv v x y D R \<and> point y \<and> y*x\<^sup>T \<le> R"

lemma construct_cycle_pre:
 assumes " \<not> is_acyclic R"
     and "y = choose_point ((R\<^sup>+ \<cdot> 1')*1)"
     and "x = choose_point (R\<^sup>\<star>*y \<cdot> R\<^sup>T*y)"
   shows "construct_cycle_inv x x y 0 R"
proof(rule conjI, rule_tac [2] conjI)
  show point_y: "point y"
    using assms by (simp add: choose_point_point is_vector_def mult_assoc galois_aux ss_p18)
  have "R\<^sup>\<star>*y \<cdot> R\<^sup>T*y \<noteq> 0"
  proof
    have "R\<^sup>+ \<cdot> 1' = (R\<^sup>+)\<^sup>T \<cdot> 1'"
      by (metis (mono_tags, hide_lams) conv_e conv_times inf.cobounded1 inf.commute
                many_strongly_connected_iff_6_eq mult_oner star_subid)
    also have "... = R\<^sup>T\<^sup>+ \<cdot> 1'"
      using plus_conv by fastforce
    also have "... \<le> (R\<^sup>T\<^sup>\<star> \<cdot> R)*R\<^sup>T"
      by (metis conv_contrav conv_e conv_invol modular_2_var mult_oner star_slide_var)
    also have "... \<le> (R\<^sup>T\<^sup>\<star> \<cdot> R)*1"
      by (simp add: mult_isol)
    finally have a: "(R\<^sup>+ \<cdot> 1')*1 \<le> (R\<^sup>T\<^sup>\<star> \<cdot> R)*1"
      by (metis mult_assoc mult_isor one_idem_mult)
    assume "R\<^sup>\<star>*y \<cdot> R\<^sup>T*y = 0"
    hence "(R\<^sup>\<star> \<cdot> R\<^sup>T)*y = 0"
      using point_y inj_distr point_def by blast
    hence "(R\<^sup>\<star> \<cdot> R\<^sup>T)\<^sup>T*1 \<le> -y"
      by (simp add: conv_galois_1)
    hence "y \<le> -((R\<^sup>\<star> \<cdot> R\<^sup>T)\<^sup>T*1)"
      using compl_le_swap1 by blast
    also have "... = -((R\<^sup>T\<^sup>\<star> \<cdot> R)*1)"
      by (simp add: star_conv)
    also have "... \<le> -((R\<^sup>+ \<cdot> 1')*1)"
      using a comp_anti by blast
    also have "... \<le> -y"
      by (simp add: assms galois_aux ss_p18 choose_point_decreasing)
    finally have "y = 0"
      using inf.absorb2 by fastforce
    thus False
      using point_y annir point_equations(2) point_is_point tarski by force
  qed
  hence point_x: "point x"
    by (metis point_y assms(3) inj_distr is_vector_def mult_assoc point_def choose_point_point)
  hence "y \<le> R\<^sup>T\<^sup>\<star> * x"
    by (metis assms(3) point_y choose_point_decreasing inf_le1 order.trans point_swap star_conv)
  thus tree_inv: "construct_tree_inv x x y 0 R"
    using point_x construct_tree_pre by blast
  show "y * x\<^sup>T \<le> R"
  proof -
    have "x \<le> R\<^sup>\<star>*y \<cdot> R\<^sup>T*y"
      using assms(3) choose_point_decreasing by blast
    also have "... = (R\<^sup>\<star> \<cdot> R\<^sup>T)*y"
      using point_y inj_distr point_def by fastforce
    finally have "x*y\<^sup>T \<le> R\<^sup>\<star> \<cdot> R\<^sup>T"
      using point_y point_def ss423bij by blast
    also have "... \<le> R\<^sup>T"
      by simp
    finally show ?thesis
      using conv_iso by force
  qed
qed

lemma construct_cycle_pre2:
 assumes "y \<le> v"
     and "construct_cycle_inv v x y D R"
   shows "construct_path_inv y x y D 0 \<and> D \<le> R \<and> D * x = 0 \<and> y * x\<^sup>T \<le> R"
proof(intro conjI, simp_all add: assms)
  show "D\<^sup>\<star> * y \<le> D\<^sup>T\<^sup>\<star> * x"
    using assms construct_tree_post by blast
  show "path 0"
    by (simp add: is_inj_def is_p_fun_def path_def)
  show "y \<noteq> 0"
    using assms(2) is_point_def point_is_point by blast
qed

lemma construct_cycle_post:
  assumes "\<not> q \<noteq> x"
      and "(construct_path_inv q x y D W \<and> D \<le> R \<and> D * x = 0 \<and> y * x\<^sup>T \<le> R)"
    shows "W + y * x\<^sup>T \<noteq> 0 \<and> W + y * x\<^sup>T \<le> R \<and> cycle (W + y * x\<^sup>T)"
proof(intro conjI)
  let ?C = "W + y*x\<^sup>T"
  show "?C \<noteq> 0"
    by (metis assms acyclic_imp_one_step_different_points(2) no_trivial_inverse point_def ss423bij
              sup_bot.monoid_axioms monoid.left_neutral)
  show "?C \<le> R"
    using assms(2) order_trans sup.boundedI by blast
  show "path (W + y * x\<^sup>T)"
    by (metis assms construct_tree_pre edge_is_path less_eq_def path_edge_equals_cycle
              point_is_point terminating_iff1)
  show "many_strongly_connected (W + y * x\<^sup>T)"
    by (metis assms construct_tree_pre bot_least conv_zero less_eq_def
              path_edge_equals_cycle star_conv star_subid terminating_iff1)
  qed

theorem construct_cycle_partial: "VARS e p q v x y C D W
  { \<not> is_acyclic R }
  y := choose_point ((R\<^sup>+ \<cdot> 1')*1);
  x := choose_point (R\<^sup>\<star>*y \<cdot> R\<^sup>T*y);
  D := 0;
  v := x;
  WHILE \<not> y \<le> v
    INV { construct_cycle_inv v x y D R }
     DO e := choose_singleton (v*-v\<^sup>T \<cdot> R);
        D := D + e;
        v := v + e\<^sup>T*1
     OD;
  comment { is_acyclic D \<and> point y \<and> point x \<and> D\<^sup>\<star>*y \<le> D\<^sup>T\<^sup>\<star>*x };
  W := 0;
  q := y;
  WHILE q \<noteq> x
    INV { construct_path_inv q x y D W \<and> D \<le> R \<and> D*x = 0 \<and> y*x\<^sup>T \<le> R }
     DO p := choose_point (D*q);
        W := W + p*q\<^sup>T;
        q := p
     OD;
  comment { W \<le> D \<and> terminating_path W \<and> (W = 0 \<longleftrightarrow> q=y) \<and> (W \<noteq> 0 \<longleftrightarrow> q = start_points W \<and> y = end_points W) };
  C := W + y*x\<^sup>T
  { C \<noteq> 0 \<and> C \<le> R \<and> cycle C }"
  apply vcg
  using construct_cycle_pre apply blast
  using construct_tree_inv apply blast
  using construct_cycle_pre2 apply blast
  using construct_path_inv apply blast
  using construct_cycle_post by blast

end (* relation_algebra_rtc_tarski_choose_point *)

context relation_algebra_rtc_tarski_choose_point_finite
begin

theorem construct_cycle_total: "VARS e p q v x y C D W
  [ \<not> is_acyclic R ]
  y := choose_point ((R\<^sup>+ \<cdot> 1')*1);
  x := choose_point (R\<^sup>\<star>*y \<cdot> R\<^sup>T*y);
  D := 0;
  v := x;
  WHILE \<not> y \<le> v
    INV { construct_cycle_inv v x y D R }
    VAR { card { z . z \<le> -v } }
     DO e := choose_singleton (v*-v\<^sup>T \<cdot> R);
        D := D + e;
        v := v + e\<^sup>T*1
     OD;
  comment { is_acyclic D \<and> point y \<and> point x \<and> D\<^sup>\<star>*y \<le> D\<^sup>T\<^sup>\<star>*x };
  W := 0;
  q := y;
  WHILE q \<noteq> x
    INV { construct_path_inv q x y D W \<and> D \<le> R \<and> D*x = 0 \<and> y*x\<^sup>T \<le> R }
    VAR { card { z . z \<le> -W } }
     DO p := choose_point (D*q);
        W := W + p*q\<^sup>T;
        q := p
     OD;
  comment { W \<le> D \<and> terminating_path W \<and> (W = 0 \<longleftrightarrow> q=y) \<and> (W \<noteq> 0 \<longleftrightarrow> q = start_points W \<and> y = end_points W)};
  C := W + y*x\<^sup>T
 [ C \<noteq> 0 \<and> C \<le> R \<and> cycle C ]"
  apply vcg_tc
  using construct_cycle_pre apply blast
  apply (rule CollectI, rule conjI)
  using construct_tree_inv apply blast
  using construct_tree_inv_termination apply force
  using construct_cycle_pre2 apply blast
  apply (rule CollectI, rule conjI)
  using construct_path_inv apply blast
  using construct_path_inv_termination apply clarsimp
  using construct_cycle_post by blast

end (* relation_algebra_rtc_tarski_choose_point_finite *)

end
