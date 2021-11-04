(* Title:      Relational Characterisation of Rooted Paths
   Author:     Walter Guttmann, Peter Hoefner
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
               Peter Hoefner <peter at hoefner-online.de>
*)

section \<open>Relational Characterisation of Rooted Paths\<close>

text \<open>
We characterise paths together with a designated root.
This is important as often algorithms start with a single vertex, and then build up a path, a tree or another structure.
An example is Dijkstra's shortest path algorithm.
\<close>

theory Rooted_Paths

imports Paths

begin

context relation_algebra
begin

text \<open>General theorems\<close>

lemma step_has_target:
  assumes "x;r \<noteq> 0"
    shows "x\<^sup>T;1 \<noteq> 0"
using assms inf.commute inf_bot_right schroeder_1 by fastforce

lemma end_point_char:
  "x\<^sup>T;p = 0 \<longleftrightarrow> p \<le> -(x;1)"
using antisym bot_least compl_bot_eq conv_galois_1 by fastforce

end (* relation_algebra *)

context relation_algebra_tarski
begin

text \<open>General theorems concerning points\<close>

lemma successor_point:
  assumes "is_inj x"
      and "point r"
      and "x;r \<noteq> 0"
    shows "point (x;r)"
using assms
by (simp add: inj_compose is_point_def is_vector_def mult_assoc point_is_point)

lemma no_end_point_char:
  assumes "point p"
    shows "x\<^sup>T;p \<noteq> 0 \<longleftrightarrow> p \<le> x;1"
by (simp add: assms comp_assoc end_point_char is_vector_def point_in_vector_or_complement_iff)

lemma no_end_point_char_converse:
  assumes "point p"
    shows "x;p \<noteq> 0 \<longleftrightarrow> p \<le> x\<^sup>T;1"
using assms no_end_point_char by force

end (* relation_algebra_tarski *)

subsection \<open>Consequences without the Tarski rule\<close>

context relation_algebra_rtc
begin

text \<open>Definitions for path classifications\<close>

definition path_root
  where "path_root r x \<equiv> r;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star> \<and> is_inj x \<and> is_p_fun x \<and> point r"

abbreviation connected_root
  where "connected_root r x \<equiv> r;x \<le> x\<^sup>+"

definition backward_finite_path_root
  where "backward_finite_path_root r x \<equiv> connected_root r x \<and> is_inj x \<and> is_p_fun x \<and> point r"

abbreviation backward_terminating_path_root
  where "backward_terminating_path_root r x \<equiv> backward_finite_path_root r x \<and> x;r = 0"

abbreviation cycle_root
  where "cycle_root r x \<equiv> r;x \<le> x\<^sup>+ \<cdot> x\<^sup>T;1 \<and> is_inj x \<and> is_p_fun x \<and> point r"

abbreviation non_empty_cycle_root
  where "non_empty_cycle_root r x \<equiv> backward_finite_path_root r x \<and> r \<le> x\<^sup>T;1"

abbreviation finite_path_root_end
  where "finite_path_root_end r x e \<equiv> backward_finite_path_root r x \<and> point e \<and> r \<le> x\<^sup>\<star>;e"

abbreviation terminating_path_root_end
  where "terminating_path_root_end r x e \<equiv> finite_path_root_end r x e \<and> x\<^sup>T;e = 0"

text \<open>Equivalent formulations of \<open>connected_root\<close>\<close>

lemma connected_root_iff1:
  assumes "point r"
    shows "connected_root r x \<longleftrightarrow> 1;x \<le> r\<^sup>T;x\<^sup>+"
by (metis assms comp_assoc is_vector_def point_def ss423conv)

lemma connected_root_iff2:
  assumes "point r"
    shows "connected_root r x \<longleftrightarrow> x\<^sup>T;1 \<le> x\<^sup>T\<^sup>+;r"
by (metis assms conv_contrav conv_invol conv_iso conv_one star_conv star_slide_var
          connected_root_iff1)

lemma connected_root_aux:
  "x\<^sup>T\<^sup>+;r \<le> x\<^sup>T;1"
by (simp add: comp_assoc mult_isol)

lemma connected_root_iff3:
  assumes "point r"
    shows "connected_root r x \<longleftrightarrow> x\<^sup>T;1 = x\<^sup>T\<^sup>+;r"
using assms antisym connected_root_aux connected_root_iff2 by fastforce

lemma connected_root_iff4:
  assumes "point r"
    shows "connected_root r x \<longleftrightarrow> 1;x = r\<^sup>T;x\<^sup>+"
by (metis assms conv_contrav conv_invol conv_one star_conv star_slide_var connected_root_iff3)

text \<open>Consequences of \<open>connected_root\<close>\<close>

lemma has_root_contra:
  assumes "connected_root r x"
      and "point r"
      and "x\<^sup>T;r = 0"
    shows "x = 0"
using assms comp_assoc independence1 conv_zero ss_p18 connected_root_iff3
by force

lemma has_root:
  assumes "connected_root r x"
      and "point r"
      and "x \<noteq> 0"
    shows "x\<^sup>T;r \<noteq> 0"
using has_root_contra assms by blast

lemma connected_root_move_root:
  assumes "connected_root r x"
      and "q \<le> x\<^sup>\<star>;r"
    shows "connected_root q x"
by (metis assms comp_assoc mult_isol phl_cons1 star_slide_var star_trans_eq)

lemma root_cycle_converse:
  assumes "connected_root r x"
      and "point r"
      and "x;r \<noteq> 0"
    shows "x\<^sup>T;r \<noteq> 0"
using assms conv_zero has_root by fastforce

text \<open>Rooted paths\<close>

lemma path_iff_aux_1:
  assumes "bijective r"
    shows "r;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star> \<longleftrightarrow> x \<le> r\<^sup>T;(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>)"
by (simp add: assms ss423conv)

lemma path_iff_aux_2:
  assumes "bijective r"
  shows "r;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star> \<longleftrightarrow> x\<^sup>T \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);r"
proof -
  have "((x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);r)\<^sup>T = r\<^sup>T;(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>)"
     by (metis conv_add conv_contrav conv_invol star_conv sup.commute)
  thus ?thesis
    by (metis assms conv_invol conv_iso path_iff_aux_1)
qed

lemma path_iff_backward:
  assumes "is_inj x"
      and "is_p_fun x"
      and "point r"
      and "r;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    shows "connected x"
proof -
  have "x\<^sup>T;1;x\<^sup>T \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);r;1;x\<^sup>T"
    using assms(3,4) path_iff_aux_2 mult_isor point_def by blast
  also have "... = (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);r;1;x\<^sup>T;x;x\<^sup>T"
    using assms(1) comp_assoc inj_p_fun p_fun_triple by fastforce
  also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);r;x;x\<^sup>T"
    by (metis assms(3) mult_double_iso top_greatest point_def is_vector_def comp_assoc)
  also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);x\<^sup>T"
    by (metis assms(4) comp_assoc mult_double_iso)
  also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>)"
    using le_supI2 mult_isol star_ext by blast
  also have "... = x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using assms(1,2) cancel_separate_converse_idempotent by fastforce
  finally show ?thesis
    by (metis conv_add conv_contrav conv_invol conv_one mult_assoc star_conv sup.orderE sup.orderI
              sup_commute)
qed

lemma empty_path_root_end:
  assumes "terminating_path_root_end r x e"
    shows "e = r \<longleftrightarrow> x = 0"
  apply(standard)
 using assms has_root backward_finite_path_root_def apply blast
by (metis assms antisym conv_e conv_zero independence1 is_inj_def mult_oner point_swap
          backward_finite_path_root_def ss423conv sur_def_var1 x_leq_triple_x)

lemma path_root_acyclic:
  assumes "path_root r x"
      and "x;r = 0"
    shows "is_acyclic x"
proof -
  have "x\<^sup>+\<cdot>1' = (x\<^sup>+)\<^sup>T\<cdot>x\<^sup>+\<cdot>1'"
    by (metis conv_e conv_times inf.assoc inf.left_idem inf_le2 many_strongly_connected_iff_7 mult_oner star_subid)
  also have "... \<le> x\<^sup>T;1\<cdot>x\<^sup>+\<cdot>1'"
    by (metis conv_contrav inf.commute maddux_20 meet_double_iso plus_top star_conv star_slide_var)
  finally have "r;(x\<^sup>+\<cdot>1') \<le> r;(x\<^sup>T;1\<cdot>x\<^sup>+\<cdot>1')"
    using mult_isol by blast
  also have "... = (r\<cdot>1;x);(x\<^sup>+\<cdot>1')"
    by (metis (no_types, lifting) comp_assoc conv_contrav conv_invol conv_one inf.assoc is_vector_def one_idem_mult vector_2)
  also have "... = r;x;(x\<^sup>+\<cdot>1')"
    by (metis assms(1) path_root_def point_def inf_top_right vector_1)
  also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);(x\<^sup>+\<cdot>1')"
    using assms(1) mult_isor path_root_def by blast
  also have "... = x\<^sup>\<star>;(x\<^sup>+\<cdot>1') + x\<^sup>T\<^sup>+;(x\<^sup>+\<cdot>1')"
    by (metis distrib_right star_star_plus sup.commute)
  also have "... \<le> x\<^sup>\<star>;(x\<^sup>+\<cdot>1') + x\<^sup>T;1"
    by (metis join_isol mult_isol plus_top top_greatest)
  finally have "r;(x\<^sup>+\<cdot>1');1 \<le> x\<^sup>\<star>;(x\<^sup>+\<cdot>1');1 + x\<^sup>T;1"
    by (metis distrib_right inf_absorb2 mult_assoc mult_subdistr one_idem_mult)
  hence 1: "r;(x\<^sup>+\<cdot>1');1 \<le> x\<^sup>T;1"
    by (metis assms(1) inj_implies_step_forwards_backwards sup_absorb2 path_root_def)
  have "x\<^sup>+\<cdot>1' \<le> (x\<^sup>+\<cdot>1');1"
    by (simp add: maddux_20)
  also have "... \<le> r\<^sup>T;r;(x\<^sup>+\<cdot>1');1"
    by (metis assms(1) comp_assoc order.refl point_def ss423conv path_root_def)
  also have "... \<le> r\<^sup>T;x\<^sup>T;1"
    using 1 by (simp add: comp_assoc mult_isol)
  also have "... = 0"
    using assms(2) annil conv_contrav conv_zero by force
  finally show ?thesis
    using galois_aux le_bot by blast
qed

text \<open>Start points and end points\<close>

lemma start_points_in_root_aux:
  assumes "backward_finite_path_root r x"
  shows "x;1 \<le> x\<^sup>T\<^sup>\<star>;r"
proof -
  have "x;1 \<le> x;x\<^sup>T\<^sup>+;r"
    by (metis assms inf_top.left_neutral modular_var_2 mult_assoc connected_root_iff3
              backward_finite_path_root_def)
  also have "... \<le> 1';x\<^sup>T\<^sup>\<star>;r"
    by (metis assms is_inj_def mult_assoc mult_isor backward_finite_path_root_def)
  finally show ?thesis
    by simp
qed

lemma start_points_in_root:
  assumes "backward_finite_path_root r x"
  shows "start_points x \<le> r"
using assms galois_1 sup_commute connected_root_iff3 backward_finite_path_root_def
      start_points_in_root_aux by fastforce

lemma start_points_not_zero_contra:
  assumes "connected_root r x"
      and "point r"
      and "start_points x = 0"
      and "x;r = 0"
    shows "x = 0"
proof -
  have "x;1 \<le> x\<^sup>T;1"
    using assms(3) galois_aux by force
  also have "... \<le> -r"
    using assms(4) comp_res compl_bot_eq by blast
  finally show ?thesis
    using assms(1,2) has_root_contra galois_aux schroeder_1 by force
qed

lemma start_points_not_zero:
  assumes "connected_root r x"
      and "point r"
      and "x \<noteq> 0"
      and "x;r = 0"
    shows "start_points x \<noteq> 0"
using assms start_points_not_zero_contra by blast

text \<open>Backwards terminating and backwards finite\<close>

lemma backward_terminating_path_root_aux:
  assumes "backward_terminating_path_root r x"
  shows "x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
proof -
  have "x\<^sup>T\<^sup>\<star>;r \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
    using assms comp_res compl_bot_eq compl_le_swap1 mult_isol by blast
  thus ?thesis
    using assms dual_order.trans maddux_20 start_points_in_root_aux by blast
qed

lemma backward_finite_path_connected_aux:
  assumes "backward_finite_path_root r x"
    shows "x\<^sup>T;r;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
proof -
  have "x\<^sup>T;r;x\<^sup>T \<cdot> r\<^sup>T = x\<^sup>T;r;(x\<^sup>T \<cdot> r\<^sup>T)"
    by (metis conv_invol conv_times vector_1_comm comp_assoc conv_contrav assms
              backward_finite_path_root_def point_def)
  also have "... \<le> x\<^sup>T;r;r\<^sup>T"
    by (simp add: mult_isol)
  also have 1: "... \<le> x\<^sup>T"
    by (metis assms comp_assoc is_inj_def mult_1_right mult_isol point_def
              backward_finite_path_root_def)
  also have "... \<le> x\<^sup>T\<^sup>\<star>"
    by simp
  finally have 2: "x\<^sup>T;r;x\<^sup>T \<cdot> r\<^sup>T \<le> x\<^sup>T\<^sup>\<star>" .
  let ?v = "x;1 \<cdot> -r"
  have "?v \<le> x\<^sup>T\<^sup>+;r"
    by (simp add: assms galois_1 start_points_in_root_aux)
  hence "r\<^sup>T;x \<cdot> ?v \<le> r\<^sup>T;x \<cdot> x\<^sup>T\<^sup>+;r"
    using meet_isor by blast
  also have 3: "... = x\<^sup>T\<^sup>+;r \<cdot> 1;r\<^sup>T;x"
    by (metis assms conv_contrav conv_one inf_commute is_vector_def point_def
              backward_finite_path_root_def)
  also have "... = (x\<^sup>T\<^sup>+;r \<cdot> 1);r\<^sup>T;x"
    using 3 by (metis comp_assoc inf_commute is_vector_def star_conv vector_1 assms
                      backward_finite_path_root_def point_def)
  also have "... = x\<^sup>T\<^sup>+;r;r\<^sup>T;x"
    by simp
  also have "... \<le> x\<^sup>T\<^sup>+;x"
    using 1 by (metis mult_assoc mult_isol mult_isor star_slide_var)
  also have "... = x\<^sup>T\<^sup>\<star>;x\<^sup>T;x"
    by (simp add: star_slide_var)
  also have "... \<le> x\<^sup>T\<^sup>\<star>"
    by (metis assms backward_finite_path_root_def is_p_fun_def mult_1_right mult_assoc mult_isol_var
              star_1l star_inductl_star)
  finally have 4: "x\<^sup>T;r \<cdot> ?v\<^sup>T \<le> x\<^sup>\<star>"
    using conv_iso star_conv by force
  have "x\<^sup>T;r;x\<^sup>T \<cdot> -r\<^sup>T = (x\<^sup>T;r \<cdot> 1);x\<^sup>T \<cdot> -r\<^sup>T"
    by simp
  also have "... = x\<^sup>T;r \<cdot> 1;x\<^sup>T \<cdot> -r\<^sup>T"
    by (metis inf.commute is_vector_def comp_assoc vector_1 assms backward_finite_path_root_def
              point_def)
  also have "... \<le> x\<^sup>\<star>"
    using 4 by (simp add: conv_compl inf.assoc)
  finally have "(x\<^sup>T;r;x\<^sup>T \<cdot> -r\<^sup>T) + (x\<^sup>T;r;x\<^sup>T \<cdot> r\<^sup>T) \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using 2 sup.mono by blast
  thus ?thesis
    by fastforce
qed

lemma backward_finite_path_connected:
  assumes "backward_finite_path_root r x"
    shows "connected x"
proof -
  from assms obtain r where 1: "backward_finite_path_root r x" ..
  have "x\<^sup>T;(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>) = x\<^sup>T;(1' + x\<^sup>+) + x\<^sup>T\<^sup>+"
    by (simp add: distrib_left)
  also have "... = x\<^sup>T;x\<^sup>+ + x\<^sup>T\<^sup>+"
    using calculation distrib_left star_star_plus by fastforce
  also have "... \<le> 1';x\<^sup>\<star> + x\<^sup>T\<^sup>+"
    using 1 by (metis add_iso comp_assoc is_p_fun_def mult_isor backward_finite_path_root_def)
  also have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using join_isol by fastforce
  finally have "x\<^sup>T;r;x\<^sup>T + x\<^sup>T;(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>) \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using 1 backward_finite_path_connected_aux by simp
  hence "x\<^sup>T\<^sup>\<star>;x\<^sup>T;r;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using star_inductl comp_assoc by simp
  hence "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using 1 backward_finite_path_root_def connected_root_iff3 star_slide_var by fastforce
  thus ?thesis
    by (metis (mono_tags, lifting) sup.commute comp_assoc conv_add conv_contrav conv_invol conv_iso
              conv_one star_conv)
qed

lemma backward_finite_path_root_path:
  assumes "backward_finite_path_root r x"
    shows "path x"
using assms path_def backward_finite_path_connected backward_finite_path_root_def by blast

lemma backward_finite_path_root_path_root:
  assumes "backward_finite_path_root r x"
    shows "path_root r x"
using assms backward_finite_path_root_def le_supI1 star_star_plus path_root_def by fastforce

lemma zero_backward_terminating_path_root:
  assumes "point r"
    shows "backward_terminating_path_root r 0"
by (simp add: assms is_inj_def is_p_fun_def backward_finite_path_root_def)

lemma backward_finite_path_root_move_root:
  assumes "backward_finite_path_root r x"
      and "point q"
      and "q \<le> x\<^sup>\<star>;r"
    shows "backward_finite_path_root q x"
using assms connected_root_move_root backward_finite_path_root_def by blast

text \<open>Cycle\<close>

lemma non_empty_cycle_root_var_axioms_1:
  "non_empty_cycle_root r x \<longleftrightarrow> x\<^sup>T;1 \<le> x\<^sup>T\<^sup>+;r \<and> is_inj x \<and> is_p_fun x \<and> point r \<and> r \<le> x\<^sup>T;1"
using connected_root_iff2 backward_finite_path_root_def by blast

lemma non_empty_cycle_root_loop:
  assumes "non_empty_cycle_root r x"
    shows "r \<le> x\<^sup>T\<^sup>+;r"
using assms connected_root_iff3 backward_finite_path_root_def by fastforce

lemma cycle_root_end_empty:
  assumes "terminating_path_root_end r x e"
      and "many_strongly_connected x"
    shows "x = 0"
by (metis assms has_root_contra point_swap backward_finite_path_root_def
          backward_finite_path_root_move_root star_conv)

lemma cycle_root_end_empty_var:
  assumes "terminating_path_root_end r x e"
      and "x \<noteq> 0"
    shows "\<not> many_strongly_connected x"
using assms cycle_root_end_empty by blast

text \<open>Terminating path\<close>

lemma terminating_path_root_end_connected:
  assumes "terminating_path_root_end r x e"
    shows "x;1 \<le> x\<^sup>+;e"
proof -
  have "x;1 \<le> x;x\<^sup>T;1"
    by (metis comp_assoc inf_top.left_neutral modular_var_2)
  also have "... = x;x\<^sup>T\<^sup>+;r"
    using assms backward_finite_path_root_def connected_root_iff3 comp_assoc by fastforce
  also have "... \<le> x;x\<^sup>T\<^sup>+;x\<^sup>\<star>;e"
    by (simp add: assms comp_assoc mult_isol)
  also have "... = x;x\<^sup>T;(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);e"
    using assms cancel_separate_p_fun_converse comp_assoc backward_finite_path_root_def by fastforce
  also have "... = x;x\<^sup>T;(x\<^sup>+ + x\<^sup>T\<^sup>\<star>);e"
    by (simp add: star_star_plus)
  also have "... = x;x\<^sup>T;x\<^sup>+;e + x;x\<^sup>T\<^sup>+;e"
    by (simp add: comp_assoc distrib_left)
  also have "... = x;x\<^sup>T;x\<^sup>+;e"
    by (simp add: assms comp_assoc independence1)
  also have "... \<le> x\<^sup>+;e"
    by (metis assms annil independence1 is_inj_def mult_isor mult_oner backward_finite_path_root_def)
  finally show ?thesis .
qed

lemma terminating_path_root_end_forward_finite:
  assumes "terminating_path_root_end r x e"
    shows "backward_finite_path_root e (x\<^sup>T)"
using assms terminating_path_root_end_connected inj_p_fun connected_root_iff2
      backward_finite_path_root_def by force

end (* relation_algebra_rtc *)

subsection \<open>Consequences with the Tarski rule\<close>

context relation_algebra_rtc_tarski
begin

text \<open>Some (more) results about points\<close>

lemma point_reachable_converse:
  assumes "is_vector v"
      and "v \<noteq> 0"
      and "point r"
      and "v \<le> x\<^sup>T\<^sup>+;r"
    shows "r \<le> x\<^sup>+;v"
proof -
  have "v\<^sup>T;v \<noteq> 0"
    by (metis assms(2) inf.idem inf_bot_right mult_1_right schroeder_1)
  hence "1;v\<^sup>T;v = 1"
    using assms(1) is_vector_def mult_assoc tarski by force
  hence 1: "r = r;v\<^sup>T;v"
    by (metis assms(3) is_vector_def mult_assoc point_def)
  have "v;r\<^sup>T \<le> x\<^sup>T\<^sup>+"
    using assms(3,4) point_def ss423bij by simp
  hence "r;v\<^sup>T \<le> x\<^sup>+"
    by (metis conv_contrav conv_invol conv_iso star_conv star_slide_var)
  thus ?thesis
    using 1 by (metis mult_isor)
qed

text \<open>Roots\<close>

lemma root_in_start_points:
  assumes "connected_root r x"
      and "is_vector r"
      and "x \<noteq> 0"
      and "x;r = 0"
    shows "r \<le> start_points x"
proof -
  have "r = r;x;1"
    by (metis assms(2,3) comp_assoc is_vector_def tarski)
  also have "... \<le> x;1"
    by (metis assms(1) comp_assoc one_idem_mult phl_seq top_greatest)
  finally show ?thesis
    using assms(4) comp_res compl_bot_eq compl_le_swap1 inf.boundedI by blast
qed

lemma root_equals_start_points:
  assumes "backward_terminating_path_root r x"
      and "x \<noteq> 0"
    shows "r = start_points x"
using assms antisym point_def backward_finite_path_root_def start_points_in_root root_in_start_points
by fastforce

lemma root_equals_end_points:
  assumes "backward_terminating_path_root r (x\<^sup>T)"
      and "x \<noteq> 0"
    shows "r = end_points x"
by (metis assms conv_invol step_has_target ss_p18 root_equals_start_points)

lemma root_in_edge_sources:
  assumes "connected_root r x"
      and "x \<noteq> 0"
      and "is_vector r"
    shows "r \<le> x;1"
proof -
  have "r;1;x;1 \<le> x\<^sup>+;1"
    using assms(1,3) is_vector_def mult_isor by fastforce
  thus ?thesis
    by (metis assms(2) comp_assoc conway.dagger_unfoldl_distr dual_order.trans maddux_20 sup.commute
              sup_absorb2 tarski top_greatest)
qed

text \<open>Rooted Paths\<close>

lemma non_empty_path_root_iff_aux:
  assumes "path_root r x"
      and "x \<noteq> 0"
    shows "r \<le> (x + x\<^sup>T);1"
proof -
  have "(r;x \<cdot> 1');1 = (x\<^sup>T;r\<^sup>T \<cdot> 1');1"
    by (metis conv_contrav conv_e conv_times inf.cobounded2 is_test_def test_eq_conv)
  also have "... \<le> x\<^sup>T;r\<^sup>T;1"
    using mult_subdistr by blast
  also have "... \<le> x\<^sup>T;1"
    by (metis mult_assoc mult_double_iso one_idem_mult top_greatest)
  finally have 1: "(r;x \<cdot> 1');1 \<le> x\<^sup>T;1" .
  have "r \<le> r;1;x;1"
    using assms(2) comp_assoc maddux_20 tarski by fastforce
  also have "... = r;x;1"
    using assms(1) path_root_def point_def is_vector_def by simp
  also have "... = (r;x \<cdot> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>));1"
    using assms(1) path_root_def by (simp add: inf.absorb_iff1)
  also have "... = (r;x \<cdot> (x\<^sup>+ + x\<^sup>T\<^sup>+ + 1'));1"
    by (metis star_star_plus star_unfoldl_eq sup_commute sup_left_commute)
  also have "... \<le> (x\<^sup>+ + x\<^sup>T\<^sup>+ + (r;x \<cdot> 1'));1"
    by (metis inf_le2 inf_sup_distrib1 mult_isor order_refl sup_mono)
  also have "... \<le> x;1 + x\<^sup>T;1 + (r;x \<cdot> 1');1"
    by (simp add: plus_top)
  also have "... = x;1 + x\<^sup>T;1"
    using 1 sup.coboundedI2 sup.order_iff by fastforce
  finally show ?thesis
    by simp
qed

text \<open>Backwards terminating and backwards finite\<close>

lemma backward_terminating_path_root_2:
  assumes "backward_terminating_path_root r x"
    shows "backward_terminating x"
using assms backward_terminating_iff2 path_def backward_terminating_path_root_aux
      backward_finite_path_connected backward_finite_path_root_def by blast

lemma backward_terminating_path_root:
  assumes "backward_terminating_path_root r x"
    shows "backward_terminating_path x"
using assms backward_finite_path_root_path backward_terminating_path_root_2 by fastforce

text \<open>(Non-empty) Cycle\<close>

lemma cycle_iff:
  assumes "point r"
    shows "x;r \<noteq> 0 \<longleftrightarrow> r \<le> x\<^sup>T;1"
by (simp add: assms no_end_point_char_converse)

lemma non_empty_cycle_root_iff:
  assumes "connected_root r x"
      and "point r"
    shows "x;r \<noteq> 0 \<longleftrightarrow> r \<le> x\<^sup>T\<^sup>+;r"
using assms connected_root_iff3 cycle_iff by simp

lemma backward_finite_path_root_terminating_or_cycle:
  "backward_finite_path_root r x \<longleftrightarrow> backward_terminating_path_root r x \<or> non_empty_cycle_root r x"
using cycle_iff backward_finite_path_root_def by blast

lemma non_empty_cycle_root_msc:
  assumes "non_empty_cycle_root r x"
    shows "many_strongly_connected x"
proof -
  let ?p = "x\<^sup>T;r"
  have 1: "is_point ?p"
    unfolding is_point_def
    using conjI assms is_vector_def mult_assoc point_def inj_compose p_fun_inj
      cycle_iff backward_finite_path_root_def root_cycle_converse by fastforce
  have "?p \<le> x\<^sup>T\<^sup>+;?p"
    by (metis assms comp_assoc mult_isol star_slide_var non_empty_cycle_root_loop)
  hence "?p \<le> x\<^sup>+;?p"
    using 1 bot_least point_def point_is_point point_reachable_converse by blast
  also have "... = x\<^sup>\<star>;(x;x\<^sup>T);r"
    by (metis comp_assoc star_slide_var)
  also have "... \<le> x\<^sup>\<star>;1';r"
    using assms is_inj_def mult_double_iso backward_finite_path_root_def by blast
  finally have 2: "?p \<le> x\<^sup>\<star>;r"
    by simp
  have "x\<^sup>T;x\<^sup>\<star>;r = ?p + x\<^sup>T;x\<^sup>+;r"
    by (metis conway.dagger_unfoldl_distr distrib_left mult_assoc)
  also have "... \<le> ?p + 1';x\<^sup>\<star>;r"
    by (metis assms is_p_fun_def join_isol mult_assoc mult_isor backward_finite_path_root_def)
  also have "... = x\<^sup>\<star>;r"
    using 2 by (simp add: sup_absorb2)
  finally have 3: "x\<^sup>T\<^sup>\<star>;r \<le> x\<^sup>\<star>;r"
    by (metis star_inductl comp_assoc conway.dagger_unfoldl_distr le_supI order_prop)
  have "x\<^sup>T \<le> x\<^sup>T\<^sup>+;r"
    by (metis assms maddux_20 connected_root_iff3 backward_finite_path_root_def)
  also have "... \<le> x\<^sup>\<star>;r"
    using 3 by (metis assms conway.dagger_unfoldl_distr sup_absorb2 non_empty_cycle_root_loop)
  finally have 4: "x\<^sup>T \<le> x\<^sup>\<star>;r" .
  have "x\<^sup>T \<le> x\<^sup>T;x;x\<^sup>T"
    by (metis conv_invol x_leq_triple_x)
  also have "... \<le> 1;x;x\<^sup>T"
    by (simp add: mult_isor)
  also have "... = r\<^sup>T;x\<^sup>+;x\<^sup>T"
    using assms connected_root_iff4 backward_finite_path_root_def by fastforce
  also have "... \<le> r\<^sup>T;x\<^sup>\<star>"
    by (metis assms is_inj_def mult_1_right mult_assoc mult_isol backward_finite_path_root_def
              star_slide_var)
  finally have "x\<^sup>T \<le> x\<^sup>\<star>;r \<cdot> r\<^sup>T;x\<^sup>\<star>"
    using 4 by simp
  also have "... = x\<^sup>\<star>;r \<cdot> 1;r\<^sup>T;x\<^sup>\<star>"
    by (metis assms conv_contrav conv_one is_vector_def point_def backward_finite_path_root_def)
  also have "... = (x\<^sup>\<star>;r \<cdot> 1);r\<^sup>T;x\<^sup>\<star>"
    by (metis (no_types, lifting) assms is_vector_def mult_assoc point_def
              backward_finite_path_root_def vector_1)
  also have "... = x\<^sup>\<star>;r;r\<^sup>T;x\<^sup>\<star>"
    by simp
  also have "... \<le> x\<^sup>\<star>;x\<^sup>\<star>"
    by (metis assms is_inj_def mult_1_right mult_assoc mult_isol mult_isor point_def
              backward_finite_path_root_def)
  also have "... \<le> x\<^sup>\<star>"
    by simp
  finally show ?thesis
    by (simp add: many_strongly_connected_iff_1)
qed

lemma non_empty_cycle_root_msc_cycle:
  assumes "non_empty_cycle_root r x"
    shows "cycle x"
using assms backward_finite_path_root_path non_empty_cycle_root_msc by fastforce

lemma non_empty_cycle_root_non_empty:
  assumes "non_empty_cycle_root r x"
    shows "x \<noteq> 0"
using assms cycle_iff annil backward_finite_path_root_def by blast

lemma non_empty_cycle_root_rtc_symmetric:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>\<star>;r = x\<^sup>T\<^sup>\<star>;r"
using assms non_empty_cycle_root_msc by fastforce

lemma non_empty_cycle_root_point_exchange:
  assumes "non_empty_cycle_root r x"
      and "point p"
    shows "r \<le> x\<^sup>\<star>;p \<longleftrightarrow> p \<le> x\<^sup>\<star>;r"
by (metis assms(1,2) inj_sur_semi_swap point_def non_empty_cycle_root_msc
          backward_finite_path_root_def star_conv)

lemma non_empty_cycle_root_rtc_tc:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>\<star>;r = x\<^sup>+;r"
proof (rule antisym)
  have "r \<le> x\<^sup>+;r"
    using assms many_strongly_connected_iff_7 non_empty_cycle_root_loop non_empty_cycle_root_msc
    by simp
  thus "x\<^sup>\<star>;r \<le> x\<^sup>+;r"
    using sup_absorb2 by fastforce
next
  show "x\<^sup>+;r \<le> x\<^sup>\<star>;r"
    by (simp add: mult_isor)
qed

lemma non_empty_cycle_root_no_start_end_points:
  assumes "non_empty_cycle_root r x"
    shows "x;1 = x\<^sup>T;1"
using assms many_strongly_connected_implies_no_start_end_points non_empty_cycle_root_msc by blast

lemma non_empty_cycle_root_move_root:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "q \<le> x\<^sup>\<star>;r"
    shows "non_empty_cycle_root q x"
by (metis assms cycle_iff dual_order.trans backward_finite_path_root_move_root start_points_in_root
          root_equals_start_points non_empty_cycle_root_non_empty)

lemma non_empty_cycle_root_loop_converse:
  assumes "non_empty_cycle_root r x"
    shows "r \<le> x\<^sup>+;r"
using assms less_eq_def non_empty_cycle_root_rtc_tc by fastforce

lemma non_empty_cycle_root_move_root_same_reachable:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "q \<le> x\<^sup>\<star>;r"
    shows "x\<^sup>\<star>;r = x\<^sup>\<star>;q"
by (metis assms many_strongly_connected_iff_7 connected_root_iff3 connected_root_move_root
          backward_finite_path_root_def non_empty_cycle_root_msc non_empty_cycle_root_rtc_tc)

lemma non_empty_cycle_root_move_root_same_reachable_2:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "q \<le> x\<^sup>\<star>;r"
    shows "x\<^sup>\<star>;r = x\<^sup>T\<^sup>\<star>;q"
using assms non_empty_cycle_root_move_root_same_reachable non_empty_cycle_root_msc by simp

lemma non_empty_cycle_root_move_root_msc:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>T\<^sup>\<star>;q = x\<^sup>\<star>;q"
using assms non_empty_cycle_root_msc by simp

lemma non_empty_cycle_root_move_root_rtc_tc:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "q \<le> x\<^sup>\<star>;r"
    shows "x\<^sup>\<star>;q = x\<^sup>+;q"
using assms non_empty_cycle_root_move_root non_empty_cycle_root_rtc_tc by blast

lemma non_empty_cycle_root_move_root_loop_converse:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "q \<le> x\<^sup>\<star>;r"
    shows "q \<le> x\<^sup>T\<^sup>+;q"
using assms non_empty_cycle_root_loop non_empty_cycle_root_move_root by blast

lemma non_empty_cycle_root_move_root_loop:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "q \<le> x\<^sup>\<star>;r"
    shows "q \<le> x\<^sup>+;q"
using assms non_empty_cycle_root_loop_converse non_empty_cycle_root_move_root by blast

lemma non_empty_cycle_root_msc_plus:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>+;r = x\<^sup>T\<^sup>+;r"
using assms many_strongly_connected_iff_7 non_empty_cycle_root_msc by fastforce

lemma non_empty_cycle_root_tc_start_points:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>+;r = x;1"
by (metis assms connected_root_iff3 backward_finite_path_root_def non_empty_cycle_root_msc_plus
          non_empty_cycle_root_no_start_end_points)

lemma non_empty_cycle_root_rtc_start_points:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>\<star>;r = x;1"
by (simp add: assms non_empty_cycle_root_rtc_tc non_empty_cycle_root_tc_start_points)

lemma non_empty_cycle_root_converse_start_end_points:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>T \<le> x;1;x"
by (metis assms conv_contrav conv_invol conv_one inf.boundedI maddux_20 maddux_21 vector_meet_comp_x
          non_empty_cycle_root_no_start_end_points)

lemma non_empty_cycle_root_start_end_points_plus:
  assumes "non_empty_cycle_root r x"
    shows "x;1;x \<le> x\<^sup>+"
using assms eq_iff one_strongly_connected_iff one_strongly_connected_implies_7_eq
      backward_finite_path_connected non_empty_cycle_root_msc by blast

lemma non_empty_cycle_root_converse_plus:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>T \<le> x\<^sup>+"
using assms many_strongly_connected_iff_2 non_empty_cycle_root_msc by blast

lemma non_empty_cycle_root_plus_converse:
  assumes "non_empty_cycle_root r x"
    shows "x\<^sup>+ = x\<^sup>T\<^sup>+"
using assms many_strongly_connected_iff_7 non_empty_cycle_root_msc by fastforce

lemma non_empty_cycle_root_converse:
  assumes "non_empty_cycle_root r x"
    shows "non_empty_cycle_root r (x\<^sup>T)"
by (metis assms conv_invol inj_p_fun connected_root_iff3 backward_finite_path_root_def
          non_empty_cycle_root_msc_plus non_empty_cycle_root_tc_start_points)

lemma non_empty_cycle_root_move_root_forward:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "r \<le> x\<^sup>\<star>;q"
    shows "non_empty_cycle_root q x"
by (metis assms backward_finite_path_root_move_root non_empty_cycle_root_no_start_end_points
          non_empty_cycle_root_point_exchange non_empty_cycle_root_rtc_start_points)

lemma non_empty_cycle_root_move_root_forward_cycle:
  assumes "non_empty_cycle_root r x"
      and "point q"
      and "r \<le> x\<^sup>\<star>;q"
    shows "x;q \<noteq> 0 \<and> x\<^sup>T;q \<noteq> 0"
by (metis assms comp_assoc independence1 ss_p18 non_empty_cycle_root_move_root_forward
          non_empty_cycle_root_msc_plus non_empty_cycle_root_non_empty
          non_empty_cycle_root_tc_start_points)

lemma non_empty_cycle_root_equivalences:
  assumes "non_empty_cycle_root r x"
      and "point q"
    shows "(r \<le> x\<^sup>\<star>;q \<longleftrightarrow> q \<le> x\<^sup>\<star>;r)"
      and "(r \<le> x\<^sup>\<star>;q \<longleftrightarrow> x;q \<noteq> 0)"
      and "(r \<le> x\<^sup>\<star>;q \<longleftrightarrow> x\<^sup>T;q \<noteq> 0)"
      and "(r \<le> x\<^sup>\<star>;q \<longleftrightarrow> q \<le> x;1)"
      and "(r \<le> x\<^sup>\<star>;q \<longleftrightarrow> q \<le> x\<^sup>T;1)"
using assms cycle_iff no_end_point_char non_empty_cycle_root_no_start_end_points
      non_empty_cycle_root_point_exchange non_empty_cycle_root_rtc_start_points
by metis+

lemma non_empty_cycle_root_chord:
  assumes "non_empty_cycle_root r x"
      and "point p"
      and "point q"
      and "r \<le> x\<^sup>\<star>;p"
      and "r \<le> x\<^sup>\<star>;q"
    shows "p \<le> x\<^sup>\<star>;q"
using assms non_empty_cycle_root_move_root_same_reachable non_empty_cycle_root_point_exchange
by fastforce

lemma non_empty_cycle_root_var_axioms_2:
  "non_empty_cycle_root r x \<longleftrightarrow> x;1 \<le> x\<^sup>+;r \<and> is_inj x \<and> is_p_fun x \<and> point r \<and> r \<le> x;1"
apply (rule iffI)
 apply (metis eq_iff backward_finite_path_root_def non_empty_cycle_root_no_start_end_points
              non_empty_cycle_root_tc_start_points)
by (metis conv_invol p_fun_inj connected_root_iff2 connected_root_iff3
          non_empty_cycle_root_var_axioms_1 non_empty_cycle_root_msc_plus
          non_empty_cycle_root_rtc_start_points non_empty_cycle_root_rtc_tc)

lemma non_empty_cycle_root_var_axioms_3:
  "non_empty_cycle_root r x \<longleftrightarrow> x;1 \<le> x\<^sup>+;r \<and> is_inj x \<and> is_p_fun x \<and> point r \<and> r \<le> x\<^sup>+;x;1"
apply (rule iffI)
 apply (metis comp_assoc eq_refl backward_finite_path_root_def star_inductl_var_eq2
              non_empty_cycle_root_no_start_end_points non_empty_cycle_root_rtc_start_points
              non_empty_cycle_root_tc_start_points)
by (metis annir comp_assoc conv_contrav no_end_point_char non_empty_cycle_root_var_axioms_2)

lemma non_empty_cycle_root_subset_equals:
  assumes "non_empty_cycle_root r x"
      and "non_empty_cycle_root r y"
      and "x \<le> y"
    shows "x = y"
proof -
  have "y;x\<^sup>T\<^sup>\<star>;r = y;x\<^sup>T\<^sup>+;r"
    using assms(1) comp_assoc non_empty_cycle_root_msc non_empty_cycle_root_msc_plus
          non_empty_cycle_root_rtc_tc by fastforce
  also have "... \<le> y;y\<^sup>T;x\<^sup>T\<^sup>\<star>;r"
    using assms(3) comp_assoc conv_iso mult_double_iso by fastforce
  also have "... \<le> x\<^sup>T\<^sup>\<star>;r"
    using assms(2) backward_finite_path_root_def is_inj_def
    by (meson dual_order.trans mult_isor order.refl prod_star_closure star_ref)
  finally have "r + y;x\<^sup>T\<^sup>\<star>;r \<le> x\<^sup>T\<^sup>\<star>;r"
    by (metis conway.dagger_unfoldl_distr le_supI sup.cobounded1)
  hence "y\<^sup>\<star>;r \<le> x\<^sup>T\<^sup>\<star>;r"
    by (simp add: comp_assoc rtc_inductl)
  hence "y;1 \<le> x;1"
    using assms(1,2) non_empty_cycle_root_msc non_empty_cycle_root_rtc_start_points by fastforce
  thus ?thesis
    using assms(2,3) backward_finite_path_root_def ss422iv by blast
qed

lemma non_empty_cycle_root_subset_equals_change_root:
  assumes "non_empty_cycle_root r x"
      and "non_empty_cycle_root q y"
      and "x \<le> y"
    shows "x = y"
proof -
  have "r \<le> y;1"
    by (metis assms(1,3) dual_order.trans mult_isor non_empty_cycle_root_no_start_end_points)
  hence "non_empty_cycle_root r y"
    by (metis assms(1,2) connected_root_move_root backward_finite_path_root_def
              non_empty_cycle_root_no_start_end_points non_empty_cycle_root_rtc_start_points)
  thus ?thesis
    using assms(1,3) non_empty_cycle_root_subset_equals by blast
qed

lemma non_empty_cycle_root_equivalences_2:
  assumes "non_empty_cycle_root r x"
     shows "(v \<le> x\<^sup>\<star>;r \<longleftrightarrow> v \<le> x\<^sup>T;1)"
       and "(v \<le> x\<^sup>\<star>;r \<longleftrightarrow> v \<le> x;1)"
using assms non_empty_cycle_root_no_start_end_points non_empty_cycle_root_rtc_start_points
by metis+

lemma cycle_root_non_empty:
  assumes "x \<noteq> 0"
    shows "cycle_root r x \<longleftrightarrow> non_empty_cycle_root r x"
proof
  assume 1: "cycle_root r x"
  have "r \<le> r;1;x;1"
    using assms comp_assoc maddux_20 tarski by fastforce
  also have "... \<le> (x\<^sup>+ \<cdot> x\<^sup>T;1);1"
    using 1 by (simp add: is_vector_def mult_isor point_def)
  also have "... \<le> x\<^sup>T;1"
    by (simp add: ra_1)
  finally show "non_empty_cycle_root r x"
    using 1 backward_finite_path_root_def inf.boundedE by blast
next
  assume "non_empty_cycle_root r x"
  thus "cycle_root r x"
    by (metis backward_finite_path_root_def inf.orderE maddux_20 non_empty_cycle_root_plus_converse
              ra_1)
qed

text \<open>Start points and end points\<close>

lemma start_points_path_aux:
  assumes "backward_finite_path_root r x"
      and "start_points x \<noteq> 0"
    shows "x;r = 0"
by (metis assms compl_inf_bot inf.commute non_empty_cycle_root_no_start_end_points
          backward_finite_path_root_terminating_or_cycle)

lemma start_points_path:
  assumes "backward_finite_path_root r x"
      and "start_points x \<noteq> 0"
    shows "backward_terminating_path_root r x"
by (simp add: assms start_points_path_aux)

lemma root_in_start_points_2:
  assumes "backward_finite_path_root r x"
      and "start_points x \<noteq> 0"
    shows "r \<le> start_points x"
by (metis assms conv_zero eq_refl galois_aux2 root_equals_start_points start_points_path_aux)

lemma root_equals_start_points_2:
  assumes "backward_finite_path_root r x"
      and "start_points x \<noteq> 0"
    shows "r = start_points x"
by (metis assms inf_bot_left ss_p18 root_equals_start_points start_points_path)

lemma start_points_injective:
  assumes "backward_finite_path_root r x"
    shows "is_inj (start_points x)"
by (metis assms compl_bot_eq inj_def_var1 point_def backward_finite_path_root_def top_greatest
          root_equals_start_points_2)

lemma backward_terminating_path_root_aux_2:
 assumes "backward_finite_path_root r x"
     and "start_points x \<noteq> 0 \<or> x = 0"
   shows "x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
using assms bot_least backward_terminating_path_root_aux start_points_path by blast

lemma start_points_not_zero_iff:
  assumes "backward_finite_path_root r x"
    shows "x;r = 0 \<and> x \<noteq> 0 \<longleftrightarrow> start_points x \<noteq> 0"
by (metis assms conv_zero inf_compl_bot backward_finite_path_root_def start_points_not_zero_contra
          start_points_path_aux)

text \<open>Backwards terminating and backwards finite: Part II\<close>

lemma backward_finite_path_root_acyclic_terminating_aux:
  assumes "backward_finite_path_root r x"
      and "is_acyclic x"
    shows "x;r = 0"
proof (cases "x = 0")
  assume "x = 0"
  thus ?thesis
    by simp
next
  assume "x \<noteq> 0"
  hence 1: "r \<le> x;1"
    using assms(1) has_root_contra no_end_point_char backward_finite_path_root_def by blast
  have "r\<cdot>(x\<^sup>T;1) = r\<cdot>(x\<^sup>T\<^sup>+;r)"
    using assms(1) connected_root_iff3 backward_finite_path_root_def by fastforce
  also have "... \<le> r\<cdot>(-1';r)"
    by (metis assms(2) conv_compl conv_contrav conv_e conv_iso meet_isor mult_isor star_conv
              star_slide_var)
  also have "... = 0"
    by (metis (no_types) assms(1) inj_distr annil inf_compl_bot mult_1_left point_def
              backward_finite_path_root_def)
  finally have "r \<le> start_points x"
    using 1 galois_aux inf.boundedI le_bot by blast
  thus ?thesis
    using assms(1) annir le_bot start_points_path by blast
qed

lemma backward_finite_path_root_acyclic_terminating_iff:
  assumes "backward_finite_path_root r x"
    shows "is_acyclic x \<longleftrightarrow> x;r = 0"
 apply (rule iffI)
apply (simp add: assms backward_finite_path_root_acyclic_terminating_aux)
using assms backward_finite_path_root_path_root path_root_acyclic by blast

lemma backward_finite_path_root_acyclic_terminating:
 assumes "backward_finite_path_root r x"
     and "is_acyclic x"
   shows "backward_terminating_path_root r x"
by (simp add: assms backward_finite_path_root_acyclic_terminating_aux)

lemma non_empty_cycle_root_one_strongly_connected:
  assumes "non_empty_cycle_root r x"
    shows "one_strongly_connected x"
by (metis assms one_strongly_connected_iff order_trans star_1l star_star_plus sup.absorb2
          non_empty_cycle_root_msc non_empty_cycle_root_start_end_points_plus)

lemma backward_finite_path_root_nodes_reachable:
  assumes "backward_finite_path_root r x"
      and "v \<le> x;1 + x\<^sup>T;1"
      and "is_sur v"
    shows "r \<le> x\<^sup>\<star>;v"
proof -
  have "v \<le> x;1 + x\<^sup>T\<^sup>+;r"
    using assms connected_root_iff3 backward_finite_path_root_def by fastforce
  also have "... \<le> x\<^sup>T\<^sup>\<star>;r + x\<^sup>T\<^sup>+;r"
    using assms(1) join_iso start_points_in_root_aux by blast
  also have "... = x\<^sup>T\<^sup>\<star>;r"
    using mult_isor sup.absorb1 by fastforce
  finally show ?thesis
    using assms(1,3)
    by (simp add: inj_sur_semi_swap point_def backward_finite_path_root_def star_conv
                  inj_sur_semi_swap_short)
qed

lemma terminating_path_root_end_backward_terminating:
  assumes "terminating_path_root_end r x e"
    shows "backward_terminating_path_root r x"
using assms non_empty_cycle_root_move_root_forward_cycle
      backward_finite_path_root_terminating_or_cycle by blast

lemma terminating_path_root_end_converse:
  assumes "terminating_path_root_end r x e"
    shows "terminating_path_root_end e (x\<^sup>T) r"
by (metis assms terminating_path_root_end_backward_terminating backward_finite_path_root_def
          conv_invol terminating_path_root_end_forward_finite point_swap star_conv)

lemma terminating_path_root_end_forward_terminating:
  assumes "terminating_path_root_end r x e"
    shows "backward_terminating_path_root e (x\<^sup>T)"
using assms terminating_path_root_end_converse by blast

end (* relation_algebra_rtc_tarski *)

subsection \<open>Consequences with the Tarski rule and the point axiom\<close>

context relation_algebra_rtc_tarski_point
begin

text \<open>Rooted paths\<close>

lemma path_root_iff:
  "(\<exists>r . path_root r x) \<longleftrightarrow> path x"
proof
  assume "\<exists>r . path_root r x"
  thus "path x"
    using path_def path_iff_backward point_def path_root_def by blast
next
  assume 1: "path x"
  show "\<exists>r . path_root r x"
  proof (cases "x = 0")
    assume "x = 0"
    thus ?thesis
      by (simp add: is_inj_def is_p_fun_def point_exists path_root_def)
  next
    assume "\<not>(x = 0)"
    hence "x;1 \<noteq> 0"
      by (simp add: ss_p18)
    from this obtain r where 2: "point r \<and> r \<le> x;1"
      using comp_assoc is_vector_def one_idem_mult point_below_vector by fastforce
    hence "r;x \<le> x;1;x"
      by (simp add: mult_isor)
    also have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
      using 1 path_def by blast
    finally show ?thesis
      using 1 2 path_def path_root_def by blast
  qed
qed

lemma non_empty_path_root_iff:
  "(\<exists>r . path_root r x \<and> r \<le> (x + x\<^sup>T);1) \<longleftrightarrow> path x \<and> x \<noteq> 0"
apply (rule iffI)
 using non_empty_cycle_root_non_empty path_root_def zero_backward_terminating_path_root path_root_iff
 apply fastforce
using path_root_iff non_empty_path_root_iff_aux by blast

text \<open>(Non-empty) Cycle\<close>

lemma non_empty_cycle_root_iff:
  "(\<exists>r . non_empty_cycle_root r x) \<longleftrightarrow> cycle x \<and> x \<noteq> 0"
proof
  assume "\<exists>r . non_empty_cycle_root r x"
  thus "cycle x \<and> x \<noteq> 0"
    using non_empty_cycle_root_msc_cycle non_empty_cycle_root_non_empty by fastforce
next
  assume 1: "cycle x \<and> x \<noteq> 0"
  hence "x\<^sup>T;1 \<noteq> 0"
    using many_strongly_connected_implies_no_start_end_points ss_p18 by blast
  from this obtain r where 2: "point r \<and> r \<le> x\<^sup>T;1"
    using comp_assoc is_vector_def one_idem_mult point_below_vector by fastforce
  have 3: "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>\<star>"
    using 1 one_strongly_connected_iff path_def by blast
  have "r;x \<le> x\<^sup>T;1;x"
    using 2 by (simp add: is_vector_def mult_isor point_def)
  also have "... \<le> x\<^sup>T;1;x;x\<^sup>T;x"
    using comp_assoc mult_isol x_leq_triple_x by fastforce
  also have "... \<le> x\<^sup>T;1;x\<^sup>T;x"
    by (metis mult_assoc mult_double_iso top_greatest)
  also have "... \<le> x\<^sup>\<star>;x"
    using 3 mult_isor by blast
  finally have "connected_root r x"
    by (simp add: star_slide_var)
  hence "non_empty_cycle_root r x"
    using 1 2 path_def backward_finite_path_root_def by fastforce
  thus "\<exists>r . non_empty_cycle_root r x" ..
qed

lemma non_empty_cycle_subset_equals:
  assumes "cycle x"
      and "cycle y"
      and "x \<le> y"
      and "x \<noteq> 0"
    shows "x = y"
by (metis assms le_bot non_empty_cycle_root_subset_equals_change_root non_empty_cycle_root_iff)

lemma cycle_root_iff:
  "(\<exists>r . cycle_root r x) \<longleftrightarrow> cycle x"
proof (cases "x = 0")
  assume "x = 0"
  thus ?thesis
    using path_def point_exists by fastforce
next
  assume "x \<noteq> 0"
  thus ?thesis
    using cycle_root_non_empty non_empty_cycle_root_iff by simp
qed

text \<open>Backwards terminating and backwards finite\<close>

lemma backward_terminating_path_root_iff:
  "(\<exists>r . backward_terminating_path_root r x) \<longleftrightarrow> backward_terminating_path x"
proof
  assume "\<exists>r . backward_terminating_path_root r x"
  thus "backward_terminating_path x"
    using backward_terminating_path_root by fastforce
next
  assume 1: "backward_terminating_path x"
  show "\<exists>r . backward_terminating_path_root r x"
  proof (cases "x = 0")
    assume "x = 0"
    thus ?thesis
      using point_exists zero_backward_terminating_path_root by blast
  next
    let ?r = "start_points x"
    assume "x \<noteq> 0"
    hence 2: "is_point ?r"
      using 1 start_point_iff2 backward_terminating_iff1 by fastforce
    have 3: "x;?r = 0"
      by (metis inf_top.right_neutral modular_1_aux')
    have "x;1;x \<le> x;1;x;x\<^sup>T;x"
      using comp_assoc mult_isol x_leq_triple_x by fastforce
    also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);x\<^sup>T;x"
      using 1 mult_isor path_def by blast
    also have "... = (1' + x\<^sup>+ + x\<^sup>T\<^sup>+);x\<^sup>T;x"
      by (metis star_star_plus star_unfoldl_eq sup.commute)
    also have "... = x\<^sup>T;x + x\<^sup>+;x\<^sup>T;x + x\<^sup>T\<^sup>+;x\<^sup>T;x"
      by (metis distrib_right' mult_onel)
    also have "... = x\<^sup>T;(x + x\<^sup>T\<^sup>\<star>;x\<^sup>T;x) + x\<^sup>+;x\<^sup>T;x"
      using comp_assoc distrib_left sup.commute sup.assoc by simp
    also have "... \<le> x\<^sup>T;1 + x\<^sup>+;x\<^sup>T;x"
      using join_iso mult_isol by fastforce
    also have "... \<le> x\<^sup>T;1 + x\<^sup>+;1'"
      using 1 by (metis comp_assoc join_isol mult_isol path_def is_p_fun_def)
    finally have "-(x\<^sup>T;1) \<cdot> x;1;x \<le> x\<^sup>+"
      by (simp add: galois_1 inf.commute)
    hence "?r;x \<le> x\<^sup>+"
      by (metis inf_commute one_compl ra_1)
    hence "backward_terminating_path_root ?r x"
      using 1 2 3 by (simp add: point_is_point backward_finite_path_root_def path_def)
    thus ?thesis ..
  qed
qed

lemma non_empty_backward_terminating_path_root_iff:
  "backward_terminating_path_root (start_points x) x \<longleftrightarrow> backward_terminating_path x \<and> x \<noteq> 0"
apply (rule iffI)
  apply (metis backward_finite_path_root_path backward_terminating_path_root_2 conv_zero
               inf.cobounded1 non_empty_cycle_root_non_empty)
using backward_terminating_path_root_iff root_equals_start_points by blast

lemma non_empty_backward_terminating_path_root_iff':
  "backward_finite_path_root (start_points x) x \<longleftrightarrow> backward_terminating_path x \<and> x \<noteq> 0"
using start_point_no_predecessor non_empty_backward_terminating_path_root_iff by simp

lemma backward_finite_path_root_iff:
  "(\<exists>r . backward_finite_path_root r x) \<longleftrightarrow> backward_finite_path x"
proof
  assume "\<exists>r . backward_finite_path_root r x"
  thus "backward_finite_path x"
    by (meson backward_finite_iff_msc non_empty_cycle_root_msc backward_finite_path_root_path
              backward_finite_path_root_terminating_or_cycle backward_terminating_path_root)
next
  assume "backward_finite_path x"
  thus "\<exists>r . backward_finite_path_root r x"
    by (metis backward_finite_iff_msc point_exists non_empty_cycle_root_iff
              zero_backward_terminating_path_root backward_terminating_path_root_iff)
qed

lemma non_empty_backward_finite_path_root_iff:
  "(\<exists>r . backward_finite_path_root r x \<and> r \<le> x;1) \<longleftrightarrow> backward_finite_path x \<and> x \<noteq> 0"
apply (rule iffI)
 apply (metis backward_finite_path_root_iff annir backward_finite_path_root_def le_bot
              no_end_point_char ss_p18)
using backward_finite_path_root_iff backward_finite_path_root_def point_def root_in_edge_sources by blast

text \<open>Terminating\<close>

lemma terminating_path_root_end_aux:
  assumes "terminating_path x"
    shows "\<exists>r e . terminating_path_root_end r x e"
proof (cases "x = 0")
  assume "x = 0"
  thus ?thesis
    using point_exists zero_backward_terminating_path_root by fastforce
next
  assume 1: "\<not>(x = 0)"
  have 2: "backward_terminating_path x"
    using assms by simp
  from this obtain r where 3: "backward_terminating_path_root r x"
    using backward_terminating_path_root_iff by blast
  have "backward_terminating_path (x\<^sup>T)"
    using 2 by (metis assms backward_terminating_iff1 conv_backward_terminating_path conv_invol
                      conv_zero inf_top.left_neutral)
  from this obtain e where 4: "backward_terminating_path_root e (x\<^sup>T)"
    using backward_terminating_path_root_iff by blast
  have "r \<le> x;1"
    using 1 3 root_in_edge_sources backward_finite_path_root_def point_def by fastforce
  also have "... = x\<^sup>+;e"
    using 4 connected_root_iff3 backward_finite_path_root_def by fastforce
  also have "... \<le> x\<^sup>\<star>;e"
    by (simp add: mult_isor)
  finally show ?thesis
    using 3 4 backward_finite_path_root_def by blast
qed

lemma terminating_path_root_end_iff:
  "(\<exists>r e . terminating_path_root_end r x e) \<longleftrightarrow> terminating_path x"
proof
  assume 1: "\<exists>r e . terminating_path_root_end r x e"
  show "terminating_path x"
  proof (cases "x = 0")
    assume "x = 0"
    thus ?thesis
      by (simp add: is_inj_def is_p_fun_def path_def)
  next
    assume "\<not>(x = 0)"
    hence 2: "\<not> many_strongly_connected x"
      using 1 cycle_root_end_empty by blast
    hence 3: "backward_terminating_path x"
      using 1 backward_terminating_path_root terminating_path_root_end_backward_terminating by blast
    have "\<exists>e . backward_finite_path_root e (x\<^sup>T)"
      using 1 terminating_path_root_end_converse by blast
    hence "backward_terminating_path (x\<^sup>T)"
      using 1 backward_terminating_path_root terminating_path_root_end_converse by blast
    hence "forward_terminating_path x"
      by (simp add: conv_backward_terminating_path)
    thus ?thesis
      using 3 by (simp add: inf.boundedI)
  qed
next
  assume "terminating_path x"
  thus "\<exists>r e . terminating_path_root_end r x e"
    using terminating_path_root_end_aux by blast
qed

lemma non_empty_terminating_path_root_end_iff:
  "terminating_path_root_end (start_points x) x (end_points x) \<longleftrightarrow> terminating_path x \<and> x \<noteq> 0"
apply (rule iffI)
 apply (metis conv_zero non_empty_backward_terminating_path_root_iff terminating_path_root_end_iff)
using terminating_path_root_end_iff terminating_path_root_end_forward_terminating
      root_equals_end_points terminating_path_root_end_backward_terminating root_equals_start_points
by blast

lemma non_empty_finite_path_root_end_iff:
  "finite_path_root_end (start_points x) x (end_points x) \<longleftrightarrow> terminating_path x \<and> x \<noteq> 0"
using non_empty_terminating_path_root_end_iff end_point_no_successor by simp

end (* relation_algebra_rtc_tarski_point *)

end
