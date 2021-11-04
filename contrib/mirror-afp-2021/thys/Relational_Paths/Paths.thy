(* Title:      Relational Characterisation of Paths
   Author:     Walter Guttmann, Peter Hoefner
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
               Peter Hoefner <peter at hoefner-online.de>
*)

section \<open>Relational Characterisation of Paths\<close>

text \<open>
This theory provides the relation-algebraic characterisations of paths, as defined in Sections 3--5 of \cite{BerghammerFurusawaGuttmannHoefner2020}.
\<close>

theory Paths

imports More_Relation_Algebra

begin

context relation_algebra_tarski
begin

lemma path_concat_aux_0:
  assumes "is_vector v"
      and "v \<noteq> 0"
      and "w;v\<^sup>T \<le> x"
      and "v;z \<le> y"
    shows "w;1;z \<le> x;y"
proof -
  from tarski assms(1,2) have "1 = 1;v\<^sup>T;v;1"
    by (metis conv_contrav conv_one eq_refl inf_absorb1 inf_top_left is_vector_def ra_2)
  hence "w;1;z = w;1;v\<^sup>T;v;1;z"
    by (simp add: mult_isor mult_isol mult_assoc)
  also from assms(1) have "... = w;v\<^sup>T;v;z"
    by (metis is_vector_def comp_assoc conv_contrav conv_one)
  also from assms(3) have "... \<le> x;v;z"
    by (simp add: mult_isor)
  also from assms(4) have "... \<le> x;y"
    by (simp add: mult_isol mult_assoc)
  finally show ?thesis .
qed

end (* context relation_algebra_tarski *)

subsection \<open>Consequences without the Tarski rule\<close>

context relation_algebra_rtc
begin

text \<open>Definitions for path classifications\<close>

abbreviation connected
  where "connected x \<equiv> x;1;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"

abbreviation many_strongly_connected
  where "many_strongly_connected x \<equiv> x\<^sup>\<star> = x\<^sup>T\<^sup>\<star>"

abbreviation one_strongly_connected
  where "one_strongly_connected x \<equiv> x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>\<star>"

definition path
  where "path x \<equiv> connected x \<and> is_p_fun x \<and> is_inj x"

abbreviation cycle
  where "cycle x \<equiv> path x \<and> many_strongly_connected x"

abbreviation start_points
  where "start_points x \<equiv> x;1 \<cdot> -(x\<^sup>T;1)"

abbreviation end_points
  where "end_points x \<equiv> x\<^sup>T;1 \<cdot> -(x;1)"

abbreviation no_start_points
  where "no_start_points x \<equiv> x;1 \<le> x\<^sup>T;1"

abbreviation no_end_points
  where "no_end_points x \<equiv> x\<^sup>T;1 \<le> x;1"

abbreviation no_start_end_points
  where "no_start_end_points x \<equiv> x;1 = x\<^sup>T;1"

abbreviation has_start_points
  where "has_start_points x \<equiv> 1 = -(1;x);x;1"

abbreviation has_end_points
  where "has_end_points x \<equiv> 1 = 1;x;-(x;1)"

abbreviation has_start_end_points
  where "has_start_end_points x \<equiv> 1 = -(1;x);x;1 \<cdot> 1;x;-(x;1)"

abbreviation backward_terminating
  where "backward_terminating x \<equiv> x \<le> -(1;x);x;1"

abbreviation forward_terminating
  where "forward_terminating x \<equiv> x \<le> 1;x;-(x;1)"

abbreviation terminating
  where "terminating x \<equiv> x \<le> -(1;x);x;1 \<cdot> 1;x;-(x;1)"

abbreviation backward_finite
  where "backward_finite x \<equiv> x \<le> x\<^sup>T\<^sup>\<star> + -(1;x);x;1"

abbreviation forward_finite
  where "forward_finite x \<equiv> x \<le> x\<^sup>T\<^sup>\<star> + 1;x;-(x;1)"

abbreviation finite
  where "finite x \<equiv> x \<le> x\<^sup>T\<^sup>\<star> + (-(1;x);x;1 \<cdot> 1;x;-(x;1))"

abbreviation no_start_points_path
  where "no_start_points_path x \<equiv> path x \<and> no_start_points x"

abbreviation no_end_points_path
  where "no_end_points_path x \<equiv> path x \<and> no_end_points x"

abbreviation no_start_end_points_path
  where "no_start_end_points_path x \<equiv> path x \<and> no_start_end_points x"

abbreviation has_start_points_path
  where "has_start_points_path x \<equiv> path x \<and> has_start_points x"

abbreviation has_end_points_path
  where "has_end_points_path x \<equiv> path x \<and> has_end_points x"

abbreviation has_start_end_points_path
  where "has_start_end_points_path x \<equiv> path x \<and> has_start_end_points x"

abbreviation backward_terminating_path
  where "backward_terminating_path x \<equiv> path x \<and> backward_terminating x"

abbreviation forward_terminating_path
  where "forward_terminating_path x \<equiv> path x \<and> forward_terminating x"

abbreviation terminating_path
  where "terminating_path x \<equiv> path x \<and> terminating x"

abbreviation backward_finite_path
  where "backward_finite_path x \<equiv> path x \<and> backward_finite x"

abbreviation forward_finite_path
  where "forward_finite_path x \<equiv> path x \<and> forward_finite x"

abbreviation finite_path
  where "finite_path x \<equiv> path x \<and> finite x"

text \<open>General properties\<close>

lemma reachability_from_z_in_y:
  assumes "x \<le> y\<^sup>\<star>;z"
      and "x \<cdot> z = 0"
    shows "x \<le> y\<^sup>+;z"
by (metis assms conway.dagger_unfoldl_distr galois_1 galois_aux inf.orderE)

lemma reachable_imp:
  assumes "point p"
      and "point q"
      and "p\<^sup>\<star>;q \<le> p\<^sup>T\<^sup>\<star>;p"
    shows "p \<le> p\<^sup>\<star>;q"
by (metis assms conway.dagger_unfoldr_distr le_supE point_swap star_conv)

text \<open>Basic equivalences\<close>

lemma no_start_end_points_iff:
  "no_start_end_points x \<longleftrightarrow> no_start_points x \<and> no_end_points x"
by fastforce

lemma has_start_end_points_iff:
  "has_start_end_points x \<longleftrightarrow> has_start_points x \<and> has_end_points x"
by (metis inf_eq_top_iff)

lemma terminating_iff:
  "terminating x \<longleftrightarrow> backward_terminating x \<and> forward_terminating x"
by simp

lemma finite_iff:
  "finite x \<longleftrightarrow> backward_finite x \<and> forward_finite x"
by (simp add: sup_inf_distrib1 inf.boundedI)

lemma no_start_end_points_path_iff:
  "no_start_end_points_path x \<longleftrightarrow> no_start_points_path x \<and> no_end_points_path x"
by fastforce

lemma has_start_end_points_path_iff:
  "has_start_end_points_path x \<longleftrightarrow> has_start_points_path x \<and> has_end_points_path x"
using has_start_end_points_iff by blast

lemma terminating_path_iff:
  "terminating_path x \<longleftrightarrow> backward_terminating_path x \<and> forward_terminating_path x"
by fastforce

lemma finite_path_iff:
  "finite_path x \<longleftrightarrow> backward_finite_path x \<and> forward_finite_path x"
using finite_iff by fastforce

text \<open>Closure under converse\<close>

lemma connected_conv:
  "connected x \<longleftrightarrow> connected (x\<^sup>T)"
by (metis comp_assoc conv_add conv_contrav conv_iso conv_one star_conv)

lemma conv_many_strongly_connected:
  "many_strongly_connected x \<longleftrightarrow> many_strongly_connected (x\<^sup>T)"
by fastforce

lemma conv_one_strongly_connected:
  "one_strongly_connected x \<longleftrightarrow> one_strongly_connected (x\<^sup>T)"
by (metis comp_assoc conv_contrav conv_iso conv_one star_conv)

lemma conv_path:
  "path x \<longleftrightarrow> path (x\<^sup>T)"
using connected_conv inj_p_fun path_def by fastforce

lemma conv_cycle:
  "cycle x \<longleftrightarrow> cycle (x\<^sup>T)"
using conv_path by fastforce

lemma conv_no_start_points:
  "no_start_points x \<longleftrightarrow> no_end_points (x\<^sup>T)"
by simp

lemma conv_no_start_end_points:
  "no_start_end_points x \<longleftrightarrow> no_start_end_points (x\<^sup>T)"
by fastforce

lemma conv_has_start_points:
  "has_start_points x \<longleftrightarrow> has_end_points (x\<^sup>T)"
by (metis comp_assoc conv_compl conv_contrav conv_invol conv_one)

lemma conv_has_start_end_points:
  "has_start_end_points x \<longleftrightarrow> has_start_end_points (x\<^sup>T)"
by (metis comp_assoc conv_compl conv_contrav conv_invol conv_one inf_eq_top_iff)

lemma conv_backward_terminating:
  "backward_terminating x \<longleftrightarrow> forward_terminating (x\<^sup>T)"
by (metis comp_assoc conv_compl conv_contrav conv_iso conv_one)

lemma conv_terminating:
  "terminating x \<longleftrightarrow> terminating (x\<^sup>T)"
  apply (rule iffI)
 apply (metis conv_compl conv_contrav conv_one conv_times inf.commute le_iff_inf mult_assoc)
by (metis conv_compl conv_contrav conv_invol conv_one conv_times inf.commute le_iff_inf mult_assoc)

lemma conv_backward_finite:
  "backward_finite x \<longleftrightarrow> forward_finite (x\<^sup>T)"
by (metis comp_assoc conv_add conv_compl conv_contrav conv_iso conv_one star_conv)

lemma conv_finite:
  "finite x \<longleftrightarrow> finite (x\<^sup>T)"
by (metis finite_iff conv_backward_finite conv_invol)

lemma conv_no_start_points_path:
  "no_start_points_path x \<longleftrightarrow> no_end_points_path (x\<^sup>T)"
using conv_path by fastforce

lemma conv_no_start_end_points_path:
  "no_start_end_points_path x \<longleftrightarrow> no_start_end_points_path (x\<^sup>T)"
using conv_path by fastforce

lemma conv_has_start_points_path:
  "has_start_points_path x \<longleftrightarrow> has_end_points_path (x\<^sup>T)"
using conv_has_start_points conv_path by fastforce

lemma conv_has_start_end_points_path:
  "has_start_end_points_path x \<longleftrightarrow> has_start_end_points_path (x\<^sup>T)"
using conv_has_start_end_points conv_path by fastforce

lemma conv_backward_terminating_path:
  "backward_terminating_path x \<longleftrightarrow> forward_terminating_path (x\<^sup>T)"
using conv_backward_terminating conv_path by fastforce

lemma conv_terminating_path:
  "terminating_path x \<longleftrightarrow> terminating_path (x\<^sup>T)"
using conv_path conv_terminating by fastforce

lemma conv_backward_finite_path:
  "backward_finite_path x \<longleftrightarrow> forward_finite_path (x\<^sup>T)"
using conv_backward_finite conv_path by fastforce

lemma conv_finite_path:
  "finite_path x \<longleftrightarrow> finite_path (x\<^sup>T)"
using conv_finite conv_path by blast

text \<open>Equivalences for \<open>connected\<close>\<close>

lemma connected_iff2:
  assumes "is_inj x"
      and "is_p_fun x"
    shows "connected x \<longleftrightarrow> x;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
proof
  assume 1: "connected x"
  have "x;1;x\<^sup>T \<le> x;1;x;x\<^sup>T"
    by (metis conv_invol modular_var_3 vector_meet_comp_x')
  also have "... \<le> (x\<^sup>+ + x\<^sup>T\<^sup>\<star>);x\<^sup>T"
    using 1 mult_isor star_star_plus by fastforce
  also have "... \<le> x\<^sup>\<star>;x;x\<^sup>T + x\<^sup>T\<^sup>\<star>"
    using join_isol star_slide_var by simp
  also from assms(1) have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    by (metis is_inj_def comp_assoc join_iso mult_1_right mult_isol)
  finally show "x;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>" .
next
  assume 2: "x;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
  have "x;1;x \<le> x;1;x\<^sup>T;x"
    by (simp add: modular_var_3 vector_meet_comp_x)
  also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>+);x"
    using 2 by (metis mult_isor star_star_plus sup_commute)
  also have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>;x\<^sup>T;x"
    using join_iso star_slide_var by simp
  also from assms(2) have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    by (metis comp_assoc is_p_fun_def join_isol mult_1_right mult_isol)
  finally show "connected x" .
qed

lemma connected_iff3:
  assumes "is_inj x"
      and "is_p_fun x"
    shows "connected x \<longleftrightarrow> x\<^sup>T;1;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
by (metis assms connected_conv connected_iff2 inj_p_fun p_fun_inj conv_invol add_commute)

lemma connected_iff4:
  "connected x \<longleftrightarrow> x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
by (metis connected_conv conv_invol add_commute)

lemma connected_iff5:
  "connected x \<longleftrightarrow> x\<^sup>+;1;x\<^sup>+ \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
using comp_assoc plus_top top_plus by fastforce

lemma connected_iff6:
  assumes "is_inj x"
      and "is_p_fun x"
    shows "connected x \<longleftrightarrow> x\<^sup>+;1;(x\<^sup>+)\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
using assms connected_iff2 comp_assoc plus_conv plus_top top_plus by fastforce

lemma connected_iff7:
  assumes "is_inj x"
      and "is_p_fun x"
    shows "connected x \<longleftrightarrow> (x\<^sup>+)\<^sup>T;1;x\<^sup>+ \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
by (metis assms connected_iff3 conv_contrav conv_invol conv_one top_plus vector_meet_comp_x)

lemma connected_iff8:
  "connected x \<longleftrightarrow> (x\<^sup>+)\<^sup>T;1;(x\<^sup>+)\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
by (metis connected_iff4 comp_assoc conv_contrav conv_invol conv_one plus_conv star_conv top_plus)

text \<open>Equivalences and implications for \<open>many_strongly_connected\<close>\<close>

lemma many_strongly_connected_iff_1:
  "many_strongly_connected x \<longleftrightarrow> x\<^sup>T \<le> x\<^sup>\<star>"
 apply (rule iffI,simp)
by (metis conv_invol conv_iso eq_iff star_conv star_invol star_iso)

lemma many_strongly_connected_iff_2:
  "many_strongly_connected x \<longleftrightarrow> x\<^sup>T \<le> x\<^sup>+"
proof
  assume as: "many_strongly_connected x"
  hence "x\<^sup>T \<le> x\<^sup>\<star> \<cdot> (-(1') + x)"
    by (metis many_strongly_connected_iff_1 loop_backward_forward inf_greatest)
  also have "... \<le> (x\<^sup>\<star> \<cdot> -(1')) + (x\<^sup>\<star> \<cdot> x)"
    by (simp add: inf_sup_distrib1)
  also have "... \<le> x\<^sup>+"
    by (metis as eq_iff mult_1_right mult_isol star_ref sup.absorb1 conv_invol eq_refl galois_1
              inf.absorb_iff1 inf.commute star_unfoldl_eq sup_mono many_strongly_connected_iff_1)
  finally show "x\<^sup>T \<le> x\<^sup>+" .
next
  show "x\<^sup>T \<le> x\<^sup>+ \<Longrightarrow> many_strongly_connected x"
    using order_trans star_1l many_strongly_connected_iff_1 by blast
qed

lemma many_strongly_connected_iff_3:
  "many_strongly_connected x \<longleftrightarrow> x \<le> x\<^sup>T\<^sup>\<star>"
by (metis conv_invol many_strongly_connected_iff_1)

lemma many_strongly_connected_iff_4:
  "many_strongly_connected x \<longleftrightarrow> x \<le> x\<^sup>T\<^sup>+"
by (metis conv_invol many_strongly_connected_iff_2)

lemma many_strongly_connected_iff_5:
  "many_strongly_connected x \<longleftrightarrow> x\<^sup>\<star>;x\<^sup>T \<le> x\<^sup>+"
by (metis comp_assoc conv_contrav conway.dagger_unfoldr_distr star_conv star_denest_var_2
          star_invol star_trans_eq star_unfoldl_eq sup.boundedE many_strongly_connected_iff_2)

lemma many_strongly_connected_iff_6:
  "many_strongly_connected x \<longleftrightarrow> x\<^sup>T;x\<^sup>\<star> \<le> x\<^sup>+"
by (metis dual_order.trans star_1l star_conv star_inductl_star star_invol star_slide_var
          many_strongly_connected_iff_1 many_strongly_connected_iff_5)

lemma many_strongly_connected_iff_7:
  "many_strongly_connected x \<longleftrightarrow> x\<^sup>T\<^sup>+ = x\<^sup>+"
by (metis antisym conv_invol star_slide_var star_unfoldl_eq many_strongly_connected_iff_5)

lemma many_strongly_connected_iff_5_eq:
  "many_strongly_connected x \<longleftrightarrow> x\<^sup>\<star>;x\<^sup>T = x\<^sup>+"
by (metis order.refl star_slide_var many_strongly_connected_iff_5 many_strongly_connected_iff_7)

lemma many_strongly_connected_iff_6_eq:
  "many_strongly_connected x \<longleftrightarrow> x\<^sup>T;x\<^sup>\<star> = x\<^sup>+"
using many_strongly_connected_iff_6 many_strongly_connected_iff_7 by force

lemma many_strongly_connected_implies_no_start_end_points:
  assumes "many_strongly_connected x"
    shows "no_start_end_points x"
by (metis assms conway.dagger_unfoldl_distr mult_assoc sup_top_left conv_invol
        many_strongly_connected_iff_7)

lemma many_strongly_connected_implies_8:
  assumes "many_strongly_connected x"
    shows "x;x\<^sup>T \<le> x\<^sup>+"
by (simp add: assms mult_isol)

lemma many_strongly_connected_implies_9:
  assumes "many_strongly_connected x"
    shows "x\<^sup>T;x \<le> x\<^sup>+"
by (metis assms eq_refl phl_cons1 star_ext star_slide_var)

lemma many_strongly_connected_implies_10:
  assumes "many_strongly_connected x"
    shows "x;x\<^sup>T;x\<^sup>\<star> \<le> x\<^sup>+"
by (simp add: assms comp_assoc mult_isol)

lemma many_strongly_connected_implies_10_eq:
  assumes "many_strongly_connected x"
    shows "x;x\<^sup>T;x\<^sup>\<star> = x\<^sup>+"
proof (rule antisym)
  show "x;x\<^sup>T;x\<^sup>\<star> \<le> x\<^sup>+"
    by (simp add: assms comp_assoc mult_isol)
next
  have "x\<^sup>+ \<le> x;x\<^sup>T;x;x\<^sup>\<star>"
    using mult_isor x_leq_triple_x by blast
  thus "x\<^sup>+ \<le> x;x\<^sup>T;x\<^sup>\<star>"
    by (simp add: comp_assoc mult_isol order_trans)
qed

lemma many_strongly_connected_implies_11:
  assumes "many_strongly_connected x"
    shows "x\<^sup>\<star>;x\<^sup>T;x \<le> x\<^sup>+"
by (metis assms conv_contrav conv_iso mult_isol star_1l star_slide_var)

lemma many_strongly_connected_implies_11_eq:
  assumes "many_strongly_connected x"
    shows "x\<^sup>\<star>;x\<^sup>T;x = x\<^sup>+"
by (metis assms comp_assoc conv_invol many_strongly_connected_iff_5_eq
          many_strongly_connected_implies_10_eq)

lemma many_strongly_connected_implies_12:
  assumes "many_strongly_connected x"
    shows "x\<^sup>\<star>;x;x\<^sup>T \<le> x\<^sup>+"
by (metis assms comp_assoc mult_isol star_1l star_slide_var)

lemma many_strongly_connected_implies_12_eq:
  assumes "many_strongly_connected x"
    shows "x\<^sup>\<star>;x;x\<^sup>T = x\<^sup>+"
by (metis assms comp_assoc star_slide_var many_strongly_connected_implies_10_eq)

lemma many_strongly_connected_implies_13:
  assumes "many_strongly_connected x"
    shows "x\<^sup>T;x;x\<^sup>\<star> \<le> x\<^sup>+"
by (metis assms star_slide_var many_strongly_connected_implies_11 mult.assoc)

lemma many_strongly_connected_implies_13_eq:
  assumes "many_strongly_connected x"
    shows "x\<^sup>T;x;x\<^sup>\<star> = x\<^sup>+"
by (metis assms conv_invol many_strongly_connected_iff_7 many_strongly_connected_implies_10_eq)

lemma many_strongly_connected_iff_8:
  assumes "is_p_fun x"
    shows "many_strongly_connected x \<longleftrightarrow> x;x\<^sup>T \<le> x\<^sup>+"
 apply (rule iffI)
  apply (simp add: mult_isol)
 apply (simp add: many_strongly_connected_iff_1)
by (metis comp_assoc conv_invol dual_order.trans mult_isol x_leq_triple_x assms comp_assoc
          dual_order.trans is_p_fun_def order.refl prod_star_closure star_ref)

lemma many_strongly_connected_iff_9:
  assumes "is_inj x"
    shows "many_strongly_connected x \<longleftrightarrow> x\<^sup>T;x \<le> x\<^sup>+"
by (metis assms conv_contrav conv_iso inj_p_fun star_conv star_slide_var
          many_strongly_connected_iff_1 many_strongly_connected_iff_8)

lemma many_strongly_connected_iff_10:
  assumes "is_p_fun x"
    shows "many_strongly_connected x \<longleftrightarrow> x;x\<^sup>T;x\<^sup>\<star> \<le> x\<^sup>+"
 apply (rule iffI)
 apply (simp add: comp_assoc mult_isol)
by (metis assms mult_isol mult_oner order_trans star_ref many_strongly_connected_iff_8)

lemma many_strongly_connected_iff_10_eq:
  assumes "is_p_fun x"
    shows "many_strongly_connected x \<longleftrightarrow> x;x\<^sup>T;x\<^sup>\<star> = x\<^sup>+"
using assms many_strongly_connected_iff_10 many_strongly_connected_implies_10_eq by fastforce

lemma many_strongly_connected_iff_11:
  assumes "is_inj x"
    shows "many_strongly_connected x \<longleftrightarrow> x\<^sup>\<star>;x\<^sup>T;x \<le> x\<^sup>+"
by (metis assms comp_assoc conv_contrav conv_iso inj_p_fun plus_conv star_conv
          many_strongly_connected_iff_10 many_strongly_connected_iff_2)

lemma many_strongly_connected_iff_11_eq:
  assumes "is_inj x"
    shows "many_strongly_connected x \<longleftrightarrow> x\<^sup>\<star>;x\<^sup>T;x = x\<^sup>+"
using assms many_strongly_connected_iff_11 many_strongly_connected_implies_11_eq by fastforce

lemma many_strongly_connected_iff_12:
  assumes "is_p_fun x"
    shows "many_strongly_connected x \<longleftrightarrow> x\<^sup>\<star>;x;x\<^sup>T \<le> x\<^sup>+"
by (metis assms dual_order.trans mult_double_iso mult_oner star_ref star_slide_var
          many_strongly_connected_iff_8 many_strongly_connected_implies_12)

lemma many_strongly_connected_iff_12_eq:
  assumes "is_p_fun x"
    shows "many_strongly_connected x \<longleftrightarrow> x\<^sup>\<star>;x;x\<^sup>T = x\<^sup>+"
using assms many_strongly_connected_iff_12 many_strongly_connected_implies_12_eq by fastforce

lemma many_strongly_connected_iff_13:
  assumes "is_inj x"
    shows "many_strongly_connected x \<longleftrightarrow> x\<^sup>T;x;x\<^sup>\<star> \<le> x\<^sup>+"
by (metis assms comp_assoc conv_contrav conv_iso inj_p_fun star_conv star_slide_var
          many_strongly_connected_iff_1 many_strongly_connected_iff_12)

lemma many_strongly_connected_iff_13_eq:
  assumes "is_inj x"
    shows "many_strongly_connected x \<longleftrightarrow> x\<^sup>T;x;x\<^sup>\<star> = x\<^sup>+"
using assms many_strongly_connected_iff_13 many_strongly_connected_implies_13_eq by fastforce

text \<open>Equivalences and implications for \<open>one_strongly_connected\<close>\<close>

lemma one_strongly_connected_iff:
  "one_strongly_connected x \<longleftrightarrow> connected x \<and> many_strongly_connected x"
  apply (rule iffI)
 apply (metis top_greatest x_leq_triple_x mult_double_iso top_greatest dual_order.trans
              many_strongly_connected_iff_1 comp_assoc conv_contrav conv_invol conv_iso le_supI2
              star_conv)
by (metis comp_assoc conv_contrav conv_iso conv_one conway.dagger_denest star_conv star_invol
          star_sum_unfold star_trans_eq)

lemma one_strongly_connected_iff_1:
  "one_strongly_connected x \<longleftrightarrow> x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>+"
proof
  assume 1: "one_strongly_connected x"
  have "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>T;x;x\<^sup>T;1;x\<^sup>T"
    by (metis conv_invol mult_isor x_leq_triple_x)
  also from 1 have "... \<le> x\<^sup>T;x;x\<^sup>\<star>"
    by (metis distrib_left mult_assoc sup.absorb_iff1)
  also from 1 have "... \<le> x\<^sup>+"
    using many_strongly_connected_implies_13 one_strongly_connected_iff by blast
  finally show "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>+"
    .
next
  assume "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>+"
  thus "one_strongly_connected x"
    using dual_order.trans star_1l by blast
qed

lemma one_strongly_connected_iff_1_eq:
  "one_strongly_connected x \<longleftrightarrow> x\<^sup>T;1;x\<^sup>T = x\<^sup>+"
  apply (rule iffI, simp_all)
by (metis comp_assoc conv_contrav conv_invol mult_double_iso plus_conv star_slide_var top_greatest
          top_plus many_strongly_connected_implies_10_eq one_strongly_connected_iff eq_iff
          one_strongly_connected_iff_1)

lemma one_strongly_connected_iff_2:
  "one_strongly_connected x \<longleftrightarrow> x;1;x \<le> x\<^sup>T\<^sup>\<star>"
by (metis conv_invol eq_refl less_eq_def one_strongly_connected_iff)

lemma one_strongly_connected_iff_3:
  "one_strongly_connected x \<longleftrightarrow> x;1;x \<le> x\<^sup>T\<^sup>+"
by (metis comp_assoc conv_contrav conv_invol conv_iso conv_one star_conv
          one_strongly_connected_iff_1)

lemma one_strongly_connected_iff_3_eq:
  "one_strongly_connected x \<longleftrightarrow> x;1;x = x\<^sup>T\<^sup>+"
by (metis conv_invol one_strongly_connected_iff_1_eq one_strongly_connected_iff_2)

lemma one_strongly_connected_iff_4_eq:
  "one_strongly_connected x \<longleftrightarrow> x\<^sup>T;1;x = x\<^sup>+"
  apply (rule iffI)
 apply (metis comp_assoc top_plus many_strongly_connected_iff_7 one_strongly_connected_iff
              one_strongly_connected_iff_1_eq)
by (metis comp_assoc conv_contrav conv_invol conv_one plus_conv top_plus
          one_strongly_connected_iff_1_eq)

lemma one_strongly_connected_iff_5_eq:
  "one_strongly_connected x \<longleftrightarrow> x;1;x\<^sup>T = x\<^sup>+"
using comp_assoc conv_contrav conv_invol conv_one plus_conv top_plus many_strongly_connected_iff_7
      one_strongly_connected_iff one_strongly_connected_iff_3_eq by metis

lemma one_strongly_connected_iff_6_aux:
  "x;x\<^sup>+ \<le> x;1;x"
by (metis comp_assoc maddux_21 mult_isol top_plus)

lemma one_strongly_connected_implies_6_eq:
  assumes "one_strongly_connected x"
    shows "x;1;x = x;x\<^sup>+"
by (metis assms comp_assoc many_strongly_connected_iff_7 many_strongly_connected_implies_10_eq
          one_strongly_connected_iff one_strongly_connected_iff_3_eq)

lemma one_strongly_connected_iff_7_aux:
  "x\<^sup>+ \<le> x;1;x"
by (metis le_infI maddux_20 maddux_21 plus_top top_plus vector_meet_comp_x')

lemma one_strongly_connected_implies_7_eq:
  assumes "one_strongly_connected x"
    shows "x;1;x = x\<^sup>+"
using assms many_strongly_connected_iff_7 one_strongly_connected_iff one_strongly_connected_iff_3_eq
by force

lemma one_strongly_connected_implies_8:
  assumes "one_strongly_connected x"
    shows "x;1;x \<le> x\<^sup>\<star>"
using assms one_strongly_connected_iff by fastforce

lemma one_strongly_connected_iff_4:
  assumes "is_inj x"
    shows "one_strongly_connected x \<longleftrightarrow> x\<^sup>T;1;x \<le> x\<^sup>+"
proof
  assume "one_strongly_connected x"
  thus "x\<^sup>T;1;x \<le> x\<^sup>+"
    by (simp add: one_strongly_connected_iff_4_eq)
next
  assume 1: "x\<^sup>T;1;x \<le> x\<^sup>+"
  hence "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>\<star>;x;x\<^sup>T"
    by (metis mult_isor star_slide_var comp_assoc conv_invol modular_var_3 vector_meet_comp_x
              order.trans)
  also from assms have "... \<le> x\<^sup>\<star>"
    using comp_assoc is_inj_def mult_isol mult_oner by fastforce
  finally show "one_strongly_connected x"
    using dual_order.trans star_1l by fastforce
qed

lemma one_strongly_connected_iff_5:
  assumes "is_p_fun x"
    shows "one_strongly_connected x \<longleftrightarrow> x;1;x\<^sup>T \<le> x\<^sup>+"
  apply (rule iffI)
 using one_strongly_connected_iff_5_eq apply simp
by (metis assms comp_assoc mult_double_iso order.trans star_slide_var top_greatest top_plus
          many_strongly_connected_iff_12 many_strongly_connected_iff_7 one_strongly_connected_iff_3)

lemma one_strongly_connected_iff_6:
  assumes "is_p_fun x"
      and "is_inj x"
    shows "one_strongly_connected x \<longleftrightarrow> x;1;x \<le> x;x\<^sup>+"
proof
  assume "one_strongly_connected x"
  thus "x;1;x \<le> x;x\<^sup>+"
   by (simp add: one_strongly_connected_implies_6_eq)
next
  assume 1: "x;1;x \<le> x;x\<^sup>+"
  have "x\<^sup>T;1;x \<le> x\<^sup>T;x;x\<^sup>T;1;x"
    by (metis conv_invol mult_isor x_leq_triple_x)
  also have "... \<le> x\<^sup>T;x;1;x"
    by (metis comp_assoc mult_double_iso top_greatest)
  also from 1 have "... \<le> x\<^sup>T;x;x\<^sup>+"
    by (simp add: comp_assoc mult_isol)
  also from assms(1) have "... \<le> x\<^sup>+"
    by (metis comp_assoc is_p_fun_def mult_isor mult_onel)
  finally show "one_strongly_connected x"
    using assms(2) one_strongly_connected_iff_4 by blast
qed

lemma one_strongly_connected_iff_6_eq:
  assumes "is_p_fun x"
      and "is_inj x"
    shows "one_strongly_connected x \<longleftrightarrow> x;1;x = x;x\<^sup>+"
  apply (rule iffI)
 using one_strongly_connected_implies_6_eq apply blast
by (simp add: assms one_strongly_connected_iff_6)

text \<open>Start points and end points\<close>

lemma start_end_implies_terminating:
  assumes "has_start_points x"
      and "has_end_points x"
    shows "terminating x"
using assms by simp

lemma start_points_end_points_conv:
  "start_points x = end_points (x\<^sup>T)"
by simp

lemma start_point_at_most_one:
  assumes "path x"
    shows "is_inj (start_points x)"
proof -
  have isvec: "is_vector (x;1 \<cdot> -(x\<^sup>T;1))"
    by (simp add: comp_assoc is_vector_def one_compl vector_1)

  have "x;1 \<cdot> 1;x\<^sup>T \<le> x;1;x;x\<^sup>T"
    by (metis comp_assoc conv_contrav conv_one inf.cobounded2 mult_1_right mult_isol one_conv ra_2)
  also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);x\<^sup>T"
    using \<open>path x\<close> by (metis path_def mult_isor)
  also have "... = x\<^sup>T + x\<^sup>+;x\<^sup>T + x\<^sup>T\<^sup>+"
    by (simp add: star_slide_var)
  also have "... \<le> x\<^sup>T\<^sup>+ + x\<^sup>+;x\<^sup>T + x\<^sup>T\<^sup>+"
    by (metis add_iso mult_1_right star_unfoldl_eq subdistl)
  also have "... \<le> x\<^sup>\<star>;x;x\<^sup>T + x\<^sup>T\<^sup>+"
    by (simp add: star_slide_var add_comm)
  also have "... \<le> x\<^sup>\<star>;1' + x\<^sup>T\<^sup>+"
    using \<open>path x\<close> by (metis path_def is_inj_def comp_assoc distrib_left join_iso less_eq_def)
  also have "... = 1' + x\<^sup>\<star>;x + x\<^sup>T;x\<^sup>T\<^sup>\<star>"
    by simp
  also have "... \<le> 1' + 1;x + x\<^sup>T;1"
    by (metis join_isol mult_isol mult_isor sup.mono top_greatest)
  finally have aux: "x;1 \<cdot> 1;x\<^sup>T \<le> 1' + 1;x + x\<^sup>T;1" .

  from aux have "x;1 \<cdot> 1;x\<^sup>T \<cdot> -(x\<^sup>T;1) \<cdot> -(1;x) \<le> 1'"
    by (simp add: galois_1 sup_commute)
  hence "(x;1 \<cdot> -(x\<^sup>T;1)) \<cdot> (x;1 \<cdot> -(x\<^sup>T;1))\<^sup>T \<le> 1'"
    by (simp add: conv_compl inf.assoc inf.left_commute)
  with isvec have "(x;1 \<cdot> -(x\<^sup>T;1)) ; (x;1 \<cdot> -(x\<^sup>T;1))\<^sup>T \<le> 1'"
    by (metis vector_meet_comp')
  thus "is_inj (start_points x)"
    by (simp add: conv_compl is_inj_def)
qed

lemma start_point_zero_point:
  assumes "path x"
    shows "start_points x = 0 \<or> is_point (start_points x)"
using assms start_point_at_most_one comp_assoc is_point_def is_vector_def vector_compl vector_mult
by simp

lemma start_point_iff1:
  assumes "path x"
    shows "is_point (start_points x) \<longleftrightarrow> \<not>(no_start_points x)"
using assms start_point_zero_point galois_aux2 is_point_def by blast

lemma end_point_at_most_one:
  assumes "path x"
    shows "is_inj (end_points x)"
by (metis assms conv_path compl_bot_eq conv_invol inj_def_var1 is_point_def top_greatest
          start_point_zero_point)

lemma end_point_zero_point:
  assumes "path x"
    shows "end_points x = 0 \<or> is_point (end_points x)"
using assms conv_path start_point_zero_point by fastforce

lemma end_point_iff1:
  assumes "path x"
    shows "is_point (end_points x) \<longleftrightarrow> \<not>(no_end_points x)"
using assms end_point_zero_point galois_aux2 is_point_def by blast

lemma predecessor_point':
  assumes "path x"
      and "point s"
      and "point e"
      and "e;s\<^sup>T \<le> x"
    shows "x;s = e"
proof (rule antisym)
  show 1: "e \<le> x ; s"
    using assms(2,4) point_def ss423bij by blast
  show "x ; s \<le> e"
  proof -
    have "e\<^sup>T ; (x ; s) = 1"
      using 1 by (metis assms(3) eq_iff is_vector_def point_def ss423conv top_greatest)
    thus ?thesis
      by (metis assms(1-3) comp_assoc conv_contrav conv_invol eq_iff inj_compose is_vector_def
                mult_isol path_def point_def ss423conv sur_def_var1 top_greatest)
  qed
qed

lemma predecessor_point:
  assumes "path x"
      and "point s"
      and "point e"
      and "e;s\<^sup>T \<le> x"
    shows "point(x;s)"
using predecessor_point' assms by blast

lemma points_of_path_iff:
  shows "(x + x\<^sup>T);1 = x\<^sup>T;1 + start_points(x)"
    and "(x + x\<^sup>T);1 = x;1 + end_points(x)"
using aux9 inf.commute sup.commute by auto

text \<open>Path concatenation preliminaries\<close>

lemma path_concat_aux_1:
  assumes "x;1 \<cdot> y;1 \<cdot> y\<^sup>T;1 = 0"
      and "end_points x = start_points y"
    shows "x;1 \<cdot> y;1 = 0"
proof -
  have "x;1 \<cdot> y;1 = (x;1 \<cdot> y;1 \<cdot> y\<^sup>T;1) + (x;1 \<cdot> y;1 \<cdot> -(y\<^sup>T;1))"
    by simp
  also from assms(1) have "... = x;1 \<cdot> y;1 \<cdot> -(y\<^sup>T;1)"
    by (metis aux6_var de_morgan_3 inf.left_commute inf_compl_bot inf_sup_absorb)
  also from assms(2) have "... = x;1 \<cdot> x\<^sup>T;1 \<cdot> -(x;1)"
    by (simp add: inf.assoc)
  also have "... = 0"
    by (simp add: inf.commute inf.assoc)
  finally show ?thesis .
qed

lemma path_concat_aux_2:
  assumes "x;1 \<cdot> x\<^sup>T;1 \<cdot> y\<^sup>T;1 = 0"
      and "end_points x = start_points y"
    shows "x\<^sup>T;1 \<cdot> y\<^sup>T;1 = 0"
proof -
  have "y\<^sup>T;1 \<cdot> x\<^sup>T;1 \<cdot> (x\<^sup>T)\<^sup>T;1 = 0"
    using assms(1) inf.assoc inf.commute by force
  thus ?thesis
    by (metis assms(2) conv_invol inf.commute path_concat_aux_1)
qed

lemma path_concat_aux3_1:
  assumes "path x"
    shows "x;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
proof -
  have "x;1;x\<^sup>T \<le> x;1;x\<^sup>T;x;x\<^sup>T"
    by (metis comp_assoc conv_invol mult_isol x_leq_triple_x)
  also have "... \<le> x;1;x;x\<^sup>T"
    by (metis mult_isol mult_isor mult_assoc top_greatest)
  also from assms have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);x\<^sup>T"
    using path_def comp_assoc mult_isor by blast
  also have "... = x\<^sup>\<star>;x;x\<^sup>T + x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (simp add: star_slide_var star_star_plus)
  also have "... \<le> x\<^sup>\<star>;1' + x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (metis assms path_def is_inj_def join_iso mult_isol mult_assoc)
  also have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using join_isol by simp
  finally show ?thesis .
qed

lemma path_concat_aux3_2:
  assumes "path x"
    shows "x\<^sup>T;1;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
proof -
  have "x\<^sup>T;1;x \<le> x\<^sup>T;x;x\<^sup>T;1;x"
    by (metis comp_assoc conv_invol mult_isor x_leq_triple_x)
  also have "... \<le> x\<^sup>T;x;1;x"
    by (metis mult_isol mult_isor mult_assoc top_greatest)
  also from assms have "... \<le> x\<^sup>T;(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>)"
    by (simp add: comp_assoc mult_isol path_def)
  also have "... = x\<^sup>T;x;x\<^sup>\<star> + x\<^sup>T;x\<^sup>T\<^sup>\<star>"
    by (simp add: comp_assoc distrib_left star_star_plus)
  also have "... \<le> 1';x\<^sup>\<star> + x\<^sup>T;x\<^sup>T\<^sup>\<star>"
    by (metis assms path_def is_p_fun_def join_iso mult_isor mult_assoc)
  also have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using join_isol by simp
  finally show ?thesis .
qed

lemma path_concat_aux3_3:
  assumes "path x"
    shows "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
proof -
  have "x\<^sup>T;1;x\<^sup>T \<le> x\<^sup>T;x;x\<^sup>T;1;x\<^sup>T"
    by (metis comp_assoc conv_invol mult_isor x_leq_triple_x)
  also have "... \<le> x\<^sup>T;x;1;x\<^sup>T"
    by (metis mult_isol mult_isor mult_assoc top_greatest)
  also from assms have "... \<le> x\<^sup>T;(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>)"
    using path_concat_aux3_1 by (simp add: mult_assoc mult_isol)
  also have "... = x\<^sup>T;x;x\<^sup>\<star> + x\<^sup>T;x\<^sup>T\<^sup>\<star>"
    by (simp add: comp_assoc distrib_left star_star_plus)
  also have "... \<le> 1';x\<^sup>\<star> + x\<^sup>T;x\<^sup>T\<^sup>\<star>"
    by (metis assms path_def is_p_fun_def join_iso mult_isor mult_assoc)
  also have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using join_isol by simp
  finally show ?thesis .
qed

lemma path_concat_aux_3:
  assumes "path x"
      and "y \<le> x\<^sup>+ + x\<^sup>T\<^sup>+"
      and "z \<le> x\<^sup>+ + x\<^sup>T\<^sup>+"
    shows "y;1;z \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
proof -
  from assms(2,3) have "y;1;z \<le> (x\<^sup>+ + x\<^sup>T\<^sup>+);1;(x\<^sup>+ + x\<^sup>T\<^sup>+)"
    using mult_isol_var mult_isor by blast
  also have "... = x\<^sup>+;1;x\<^sup>+ + x\<^sup>+;1;x\<^sup>T\<^sup>+ + x\<^sup>T\<^sup>+;1;x\<^sup>+ + x\<^sup>T\<^sup>+;1;x\<^sup>T\<^sup>+"
    by (simp add: distrib_left sup_commute sup_left_commute)
  also have "... = x;x\<^sup>\<star>;1;x\<^sup>\<star>;x + x;x\<^sup>\<star>;1;x\<^sup>T\<^sup>\<star>;x\<^sup>T + x\<^sup>T;x\<^sup>T\<^sup>\<star>;1;x\<^sup>\<star>;x + x\<^sup>T;x\<^sup>T\<^sup>\<star>;1;x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (simp add: comp_assoc star_slide_var)
  also have "... \<le> x;1;x + x;x\<^sup>\<star>;1;x\<^sup>T\<^sup>\<star>;x\<^sup>T + x\<^sup>T;x\<^sup>T\<^sup>\<star>;1;x\<^sup>\<star>;x + x\<^sup>T;x\<^sup>T\<^sup>\<star>;1;x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (metis comp_assoc mult_double_iso top_greatest join_iso)
  also have "... \<le> x;1;x + x;1;x\<^sup>T + x\<^sup>T;x\<^sup>T\<^sup>\<star>;1;x\<^sup>\<star>;x + x\<^sup>T;x\<^sup>T\<^sup>\<star>;1;x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (metis comp_assoc mult_double_iso top_greatest join_iso join_isol)
  also have "... \<le> x;1;x + x;1;x\<^sup>T + x\<^sup>T;1;x + x\<^sup>T;x\<^sup>T\<^sup>\<star>;1;x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (metis comp_assoc mult_double_iso top_greatest join_iso join_isol)
  also have "... \<le> x;1;x + x;1;x\<^sup>T + x\<^sup>T;1;x + x\<^sup>T;1;x\<^sup>T"
    by (metis comp_assoc mult_double_iso top_greatest join_isol)
  also have "... \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
    using assms(1) path_def path_concat_aux3_1 path_concat_aux3_2 path_concat_aux3_3 join_iso join_isol
    by simp
  finally show ?thesis .
qed

lemma path_concat_aux_4:
  "x\<^sup>\<star> + x\<^sup>T\<^sup>\<star> \<le> x\<^sup>\<star> + x\<^sup>T;1"
by (metis star_star_plus add_comm join_isol mult_isol top_greatest)

lemma path_concat_aux_5:
  assumes "path x"
      and "y \<le> start_points x"
      and "z \<le> x + x\<^sup>T"
    shows "y;1;z \<le> x\<^sup>\<star>"
proof -
  from assms(1) have "x;1;x \<le> x\<^sup>\<star> + x\<^sup>T;1"
    using path_def path_concat_aux_4 dual_order.trans by blast
  hence aux1: "x;1;x \<cdot> -(x\<^sup>T;1) \<le> x\<^sup>\<star>"
    by (simp add: galois_1 sup_commute)

  from assms(1) have "x;1;x\<^sup>T \<le> x\<^sup>\<star> + x\<^sup>T;1"
    using dual_order.trans path_concat_aux3_1 path_concat_aux_4 by blast
  hence aux2: "x;1;x\<^sup>T \<cdot> -(x\<^sup>T;1) \<le> x\<^sup>\<star>"
    by (simp add: galois_1 sup_commute)

  from assms(2,3) have "y;1;z \<le> (x;1 \<cdot> -(x\<^sup>T;1));1;(x + x\<^sup>T)"
    by (simp add: mult_isol_var mult_isor)
  also have "... = (x;1 \<cdot> -(x\<^sup>T;1));1;x + (x;1 \<cdot> -(x\<^sup>T;1));1;x\<^sup>T"
    using distrib_left by blast
  also have "... = (x;1 \<cdot> -(x\<^sup>T;1) \<cdot> 1;x) + (x;1 \<cdot> -(x\<^sup>T;1));1;x\<^sup>T"
    by (metis comp_assoc inf_top_right is_vector_def one_idem_mult vector_1 vector_compl)
  also have "... = (x;1 \<cdot> -(x\<^sup>T;1) \<cdot> 1;x) + (x;1 \<cdot> -(x\<^sup>T;1) \<cdot> 1;x\<^sup>T)"
    by (metis comp_assoc inf_top_right is_vector_def one_idem_mult vector_1 vector_compl)
  also have "... = (x;1;x \<cdot> -(x\<^sup>T;1)) + (x;1;x\<^sup>T -(x\<^sup>T;1))"
    using vector_meet_comp_x vector_meet_comp_x' diff_eq inf.assoc inf.commute by simp
  also from aux1 aux2 have "... \<le> x\<^sup>\<star>"
    by (simp add: diff_eq join_iso)
  finally show ?thesis .
qed

lemma path_conditions_disjoint_points_iff:
  "x;1 \<cdot> (x\<^sup>T;1 + y;1) \<cdot> y\<^sup>T;1 = 0 \<and> start_points x \<cdot> end_points y = 0 \<longleftrightarrow> x;1 \<cdot> y\<^sup>T;1 = 0"
proof
  assume 1: "x ; 1 \<cdot> y\<^sup>T ; 1 = 0"
  hence g1: "x ; 1 \<cdot> (x\<^sup>T ; 1 + y ; 1) \<cdot> y\<^sup>T ; 1 = 0"
    by (metis inf.left_commute inf_bot_right inf_commute)
  have g2: "start_points x \<cdot> end_points y = 0"
    using 1 by (metis compl_inf_bot inf.assoc inf.commute inf.left_idem)
  show "x;1 \<cdot> (x\<^sup>T;1 + y;1) \<cdot> y\<^sup>T;1 = 0 \<and> start_points x \<cdot> end_points y = 0"
    using g1 and g2 by simp
next
  assume a: "x;1 \<cdot> (x\<^sup>T;1 + y;1) \<cdot> y\<^sup>T;1 = 0 \<and> start_points x \<cdot> end_points y = 0"
  from a have a1: "x;1 \<cdot> x\<^sup>T;1 \<cdot> y\<^sup>T;1 = 0"
    by (simp add: inf.commute inf_sup_distrib1)
  from a have a2: "x;1 \<cdot> y;1 \<cdot> y\<^sup>T;1 = 0"
    by (simp add: inf.commute inf_sup_distrib1)
  from a have a3: "start_points x \<cdot> end_points y = 0"
    by blast

  have "x;1 \<cdot> y\<^sup>T;1 = x;1 \<cdot> x\<^sup>T;1 \<cdot> y\<^sup>T;1 + x;1 \<cdot> -(x\<^sup>T;1) \<cdot> y\<^sup>T;1"
    by (metis aux4 inf_sup_distrib2)
  also from a1 have "... = x;1 \<cdot> -(x\<^sup>T;1) \<cdot> y\<^sup>T;1"
    using sup_bot_left by blast
  also have "... = x;1 \<cdot> -(x\<^sup>T;1) \<cdot> y;1 \<cdot> y\<^sup>T;1 + x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y;1) \<cdot> y\<^sup>T;1"
    by (metis aux4 inf_sup_distrib2)
  also have "... \<le> x;1 \<cdot> y;1 \<cdot> y\<^sup>T;1 + x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y;1) \<cdot> y\<^sup>T;1"
    using join_iso meet_iso by simp
  also from a2 have "... = start_points x \<cdot> end_points y"
    using sup_bot_left inf.commute inf.left_commute by simp
  also from a3 have "... = 0"
    by blast
  finally show "x;1 \<cdot> y\<^sup>T;1 = 0"
    using le_bot by blast
qed

end (* end relation_algebra_rtc *)

subsection \<open>Consequences with the Tarski rule\<close>

context relation_algebra_rtc_tarski
begin

text \<open>General theorems\<close>

lemma reachable_implies_predecessor:
  assumes "p \<noteq> q"
      and "point p"
      and "point q"
      and "x\<^sup>\<star>;q \<le> x\<^sup>T\<^sup>\<star>;p"
    shows "x;q \<noteq> 0"
proof
  assume contra: "x;q=0"
  with assms(4) have "q \<le> x\<^sup>T\<^sup>\<star>;p"
    by (simp add: independence1)
  hence "p \<le> x\<^sup>\<star>;q"
    by (metis assms(2,3) point_swap star_conv)
  with contra assms(2,3) have "p=q"
    by (simp add: independence1 is_point_def point_singleton point_is_point)
  with assms(1) show False
    by simp
qed

lemma acyclic_imp_one_step_different_points:
  assumes "is_acyclic x"
      and "point p"
      and "point q"
      and "p \<le> x;q"
    shows "p \<le> -q" and "p \<noteq> q"
using acyclic_reachable_points assms point_is_point point_not_equal(1) by auto

text \<open>Start points and end points\<close>

lemma start_point_iff2:
  assumes "path x"
    shows "is_point (start_points x) \<longleftrightarrow> has_start_points x"
proof -
  have "has_start_points x \<longleftrightarrow> 1 \<le> -(1;x);x;1"
    by (simp add: eq_iff)
  also have "... \<longleftrightarrow> 1 \<le> 1;x\<^sup>T;-(x\<^sup>T;1)"
    by (metis comp_assoc conv_compl conv_contrav conv_iso conv_one)
  also have "... \<longleftrightarrow> 1 \<le> 1;(x;1 \<cdot> -(x\<^sup>T;1))"
    by (metis (no_types) conv_contrav conv_one inf.commute is_vector_def one_idem_mult ra_2 vector_1
              vector_meet_comp_x)
  also have "... \<longleftrightarrow> 1 = 1;(x;1 \<cdot> -(x\<^sup>T;1))"
    by (simp add: eq_iff)
  also have "... \<longleftrightarrow> x;1 \<cdot> -(x\<^sup>T;1) \<noteq> 0"
    by (metis tarski comp_assoc one_compl ra_1 ss_p18)
  also have "... \<longleftrightarrow> is_point (start_points x)"
    using assms is_point_def start_point_zero_point by blast
  finally show ?thesis ..
qed

lemma end_point_iff2:
  assumes "path x"
    shows "is_point (end_points x) \<longleftrightarrow> has_end_points x"
by (metis assms conv_invol conv_has_start_points conv_path start_point_iff2)

lemma edge_is_path:
  assumes "is_point p"
      and "is_point q"
    shows "path (p;q\<^sup>T)"
  apply (unfold path_def; intro conjI)
    apply (metis assms comp_assoc is_point_def le_supI1 star_ext vector_rectangle point_equations(3))
   apply (metis is_p_fun_def assms comp_assoc conv_contrav conv_invol is_inj_def is_point_def
                vector_2_var vector_meet_comp_x' point_equations)
  by (metis is_inj_def assms conv_invol conv_times is_point_def p_fun_mult_var vector_meet_comp)

lemma edge_start:
  assumes "is_point p"
      and "is_point q"
      and "p \<noteq> q"
    shows "start_points (p;q\<^sup>T) = p"
using assms by (simp add: comp_assoc point_equations(1,3) point_not_equal inf.absorb1)

lemma edge_end:
  assumes "is_point p"
      and "is_point q"
      and "p \<noteq> q"
    shows "end_points (p;q\<^sup>T) = q"
using assms edge_start by simp

lemma loop_no_start:
  assumes "is_point p"
    shows "start_points (p;p\<^sup>T) = 0"
by simp

lemma loop_no_end:
  assumes "is_point p"
    shows "end_points (p;p\<^sup>T) = 0"
by simp

lemma start_point_no_predecessor:
  "x;start_points(x) = 0"
by (metis inf_top.right_neutral modular_1_aux')

lemma end_point_no_successor:
  "x\<^sup>T;end_points(x) = 0"
by (metis conv_invol start_point_no_predecessor)

lemma start_to_end:
  assumes "path x"
    shows "start_points(x);end_points(x)\<^sup>T \<le> x\<^sup>\<star>"
proof (cases "end_points(x) = 0")
  assume "end_points(x) = 0"
  thus ?thesis
    by simp
next
  assume ass: "end_points(x) \<noteq> 0"
  hence nz: "x;end_points(x) \<noteq> 0"
    by (metis comp_res_aux compl_bot_eq inf.left_idem)
  have a: "x;end_points(x);end_points(x)\<^sup>T \<le> x + x\<^sup>T"
    by (metis end_point_at_most_one assms(1) is_inj_def comp_assoc mult_isol mult_oner le_supI1)

  have "start_points(x);end_points(x)\<^sup>T = start_points(x);1;end_points(x)\<^sup>T"
    using ass by (simp add: comp_assoc is_vector_def one_compl vector_1)
  also have "... = start_points(x);1;x;end_points(x);1;end_points(x)\<^sup>T"
    using nz tarski by (simp add: comp_assoc)
  also have "... = start_points(x);1;x;end_points(x);end_points(x)\<^sup>T"
    using ass by (simp add: comp_assoc is_vector_def one_compl vector_1)
  also with a assms(1) have "... \<le> x\<^sup>\<star>"
    using path_concat_aux_5 comp_assoc eq_refl by simp
  finally show ?thesis .
qed

lemma path_acyclic:
  assumes "has_start_points_path x"
    shows "is_acyclic x"
proof -
  let ?r = "start_points(x)"
  have pt: "point(?r)"
    using assms point_is_point start_point_iff2 by blast
  have "x\<^sup>+\<cdot>1' = (x\<^sup>+)\<^sup>T\<cdot>x\<^sup>+\<cdot>1'"
    by (metis conv_e conv_times inf.assoc inf.left_idem inf_le2 many_strongly_connected_iff_7
              mult_oner star_subid)
  also have "... \<le> x\<^sup>T;1\<cdot>x\<^sup>+\<cdot>1'"
    by (metis conv_contrav inf.commute maddux_20 meet_double_iso plus_top star_conv star_slide_var)
  finally have "?r;(x\<^sup>+\<cdot>1') \<le> ?r;(x\<^sup>T;1\<cdot>x\<^sup>+\<cdot>1')"
    using mult_isol by blast
  also have "... = (?r\<cdot>1;x);(x\<^sup>+\<cdot>1')"
    by (metis (no_types, lifting) comp_assoc conv_contrav conv_invol conv_one inf.assoc
              is_vector_def one_idem_mult vector_2)
  also have "... = ?r;x;(x\<^sup>+\<cdot>1')"
    by (metis comp_assoc inf_top.right_neutral is_vector_def one_compl one_idem_mult vector_1)
  also have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);(x\<^sup>+\<cdot>1')"
    using assms(1) mult_isor
    by (meson connected_iff4 dual_order.trans mult_subdistr path_concat_aux3_3)
  also have "... = x\<^sup>\<star>;(x\<^sup>+\<cdot>1') + x\<^sup>T\<^sup>+;(x\<^sup>+\<cdot>1')"
    by (metis distrib_right star_star_plus sup.commute)
  also have "... \<le> x\<^sup>\<star>;(x\<^sup>+\<cdot>1') + x\<^sup>T;1"
    by (metis join_isol mult_isol plus_top top_greatest)
  finally have "?r;(x\<^sup>+\<cdot>1');1 \<le> x\<^sup>\<star>;(x\<^sup>+\<cdot>1');1 + x\<^sup>T;1"
    by (metis distrib_right inf_absorb2 mult_assoc mult_subdistr one_idem_mult)
  hence 1: "?r;(x\<^sup>+\<cdot>1');1 \<le> x\<^sup>T;1"
    using assms(1) path_def inj_implies_step_forwards_backwards sup_absorb2 by simp
  have "x\<^sup>+\<cdot>1' \<le> (x\<^sup>+\<cdot>1');1"
    by (simp add: maddux_20)
  also have "... \<le> ?r\<^sup>T;?r;(x\<^sup>+\<cdot>1');1"
    using pt comp_assoc point_def ss423conv by fastforce
  also have "... \<le> ?r\<^sup>T;x\<^sup>T;1"
    using 1 by (simp add: comp_assoc mult_isol)
  also have "... = 0"
    by (metis start_point_no_predecessor annil conv_contrav conv_zero)
  finally show ?thesis
    using galois_aux le_bot by blast
qed

text \<open>Equivalences for \<open>terminating\<close>\<close>

lemma backward_terminating_iff1:
  assumes "path x"
    shows "backward_terminating x \<longleftrightarrow> has_start_points x \<or> x = 0"
proof
  assume "backward_terminating x"
  hence "1;x;1 \<le> 1;-(1;x);x;1;1"
    by (metis mult_isor mult_isol comp_assoc)
  also have "... = -(1;x);x;1"
    by (metis conv_compl conv_contrav conv_invol conv_one mult_assoc one_compl one_idem_mult)
  finally have "1;x;1 \<le> -(1;x);x;1" .

  with tarski show "has_start_points x \<or> x = 0"
    by (metis top_le)
next
  show "has_start_points x \<or> x = 0 \<Longrightarrow> backward_terminating x"
    by fastforce
qed

lemma backward_terminating_iff2_aux:
  assumes "path x"
    shows "x;1 \<cdot> 1;x\<^sup>T \<cdot> -(1;x) \<le> x\<^sup>T\<^sup>\<star>"
proof -
  have "x;1 \<cdot> 1;x\<^sup>T \<le> x;1;x;x\<^sup>T"
    by (metis conv_invol modular_var_3 vector_meet_comp_x vector_meet_comp_x')
  also from assms have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);x\<^sup>T"
    using path_def mult_isor by blast
  also have "... \<le> x\<^sup>\<star>;x;x\<^sup>T + x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (simp add: star_star_plus star_slide_var add_comm)
  also from assms have "... \<le> x\<^sup>\<star>;1' + x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (metis path_def is_inj_def join_iso mult_assoc mult_isol)
  also have "... = x\<^sup>+ + x\<^sup>T\<^sup>\<star>"
    by (metis mult_1_right star_slide_var star_star_plus sup.commute)
  also have "... \<le> x\<^sup>T\<^sup>\<star> + 1;x"
    by (metis join_iso mult_isor star_slide_var top_greatest add_comm)
  finally have "x;1 \<cdot> 1;x\<^sup>T \<le> x\<^sup>T\<^sup>\<star> + 1;x" .
  thus ?thesis
    by (simp add: galois_1 sup.commute)
qed

lemma backward_terminating_iff2:
  assumes "path x"
    shows "backward_terminating x \<longleftrightarrow> x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
proof
  assume "backward_terminating x"
  with assms have "has_start_points x \<or> x = 0"
    by (simp add: backward_terminating_iff1)
  thus "x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
  proof
    assume "x = 0"
    thus ?thesis
      by simp
  next
    assume "has_start_points x"
    hence aux1: "1 = 1;x\<^sup>T;-(x\<^sup>T;1)"
      by (metis comp_assoc conv_compl conv_contrav conv_one)
    have "x = x \<cdot> 1"
      by simp
    also have "... \<le> (x;-(1;x) \<cdot> 1;x\<^sup>T);-(x\<^sup>T;1)"
      by (metis inf.commute aux1 conv_compl conv_contrav conv_invol conv_one modular_2_var)
    also have "... = (x;1 \<cdot> -(1;x) \<cdot> 1;x\<^sup>T);-(x\<^sup>T;1)"
      by (metis comp_assoc conv_compl conv_contrav conv_invol conv_one inf.commute inf_top_left
                one_compl ra_1)
    also from assms have "... \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
      using backward_terminating_iff2_aux inf.commute inf.assoc mult_isor by fastforce
    finally show "x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)" .
  qed
next
  assume "x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
  hence"x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1) \<cdot> x"
    by simp
  also have "... = (x\<^sup>T\<^sup>\<star> \<cdot> -(1;x));1 \<cdot> x"
    by (metis one_compl conv_compl conv_contrav conv_invol conv_one inf_top_left ra_2)
  also have "... \<le> (x\<^sup>T\<^sup>\<star> \<cdot> -(1;x)) ; (1 \<cdot> (x\<^sup>\<star> \<cdot> -(1;x)\<^sup>T);x)"
    by (metis (mono_tags) conv_compl conv_invol conv_times modular_1_var star_conv)
  also have "... \<le> -(1;x);x\<^sup>\<star>;x"
    by (simp add: mult_assoc mult_isol_var)
  also have "... \<le> -(1;x);x;1"
    by (simp add: mult_assoc mult_isol star_slide_var)
  finally show "backward_terminating x" .
qed

lemma backward_terminating_iff3_aux:
  assumes "path x"
    shows "x\<^sup>T;1 \<cdot> 1;x\<^sup>T \<cdot> -(1;x) \<le> x\<^sup>T\<^sup>\<star>"
proof -
  have "x\<^sup>T;1 \<cdot> 1;x\<^sup>T \<le> x\<^sup>T;1;x;x\<^sup>T"
    by (metis conv_invol modular_var_3 vector_meet_comp_x vector_meet_comp_x')
  also from assms have "... \<le> (x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);x\<^sup>T"
    using mult_isor path_concat_aux3_2 by blast
  also have "... \<le> x\<^sup>\<star>;x;x\<^sup>T + x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (simp add: star_star_plus star_slide_var add_comm)
  also from assms have "... \<le> x\<^sup>\<star>;1' + x\<^sup>T\<^sup>\<star>;x\<^sup>T"
    by (metis path_def is_inj_def join_iso mult_assoc mult_isol)
  also have "... = x\<^sup>+ + x\<^sup>T\<^sup>\<star>"
    by (metis mult_1_right star_slide_var star_star_plus sup.commute)
  also have "... \<le> x\<^sup>T\<^sup>\<star> + 1;x"
    by (metis join_iso mult_isor star_slide_var top_greatest add_comm)
  finally have "x\<^sup>T;1 \<cdot> 1;x\<^sup>T \<le> x\<^sup>T\<^sup>\<star> + 1;x" .
  thus ?thesis
    by (simp add: galois_1 sup.commute)
qed

lemma backward_terminating_iff3:
  assumes "path x"
    shows "backward_terminating x \<longleftrightarrow> x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
proof
  assume "backward_terminating x"
  with assms have "has_start_points x \<or> x = 0"
    by (simp add: backward_terminating_iff1)
  thus "x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
  proof
    assume "x = 0"
    thus ?thesis
      by simp
  next
    assume "has_start_points x"
    hence aux1: "1 = 1;x\<^sup>T;-(x\<^sup>T;1)"
      by (metis comp_assoc conv_compl conv_contrav conv_one)
    have "x\<^sup>T = x\<^sup>T \<cdot> 1"
      by simp
    also have "... \<le> (x\<^sup>T;-(1;x) \<cdot> 1;x\<^sup>T);-(x\<^sup>T;1)"
      by (metis inf.commute aux1 conv_compl conv_contrav conv_invol conv_one modular_2_var)
    also have "... = (x\<^sup>T;1 \<cdot> -(1;x) \<cdot> 1;x\<^sup>T);-(x\<^sup>T;1)"
      by (metis comp_assoc conv_compl conv_contrav conv_invol conv_one inf.commute inf_top_left one_compl ra_1)
    also from assms have "... \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
      using backward_terminating_iff3_aux inf.commute inf.assoc mult_isor by fastforce
    finally show "x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)" .
  qed
next
  have 1: "-(1;x) \<cdot> x = 0"
    by (simp add: galois_aux2 inf.commute maddux_21)
  assume "x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1)"
  hence "x = -(1;x);x\<^sup>\<star> \<cdot> x"
    by (metis (mono_tags, lifting) conv_compl conv_contrav conv_iso conv_one inf.absorb2 star_conv)
  also have "... = (-(1;x);x\<^sup>+ + -(1;x);1') \<cdot> x"
    by (metis distrib_left star_unfoldl_eq sup_commute)
  also have "... = -(1;x);x\<^sup>+ \<cdot> x + -(1;x) \<cdot> x"
    by (simp add: inf_sup_distrib2)
  also have "... \<le> -(1;x);x\<^sup>+"
    using 1 by simp
  also have "... \<le> -(1;x);x;1"
    by (simp add: mult_assoc mult_isol star_slide_var)
  finally show "backward_terminating x" .
qed

lemma backward_terminating_iff4:
  assumes "path x"
    shows "backward_terminating x \<longleftrightarrow> x \<le> -(1;x);x\<^sup>\<star>"
 apply (subst backward_terminating_iff3)
  apply (rule assms)
 by (metis (mono_tags, lifting) conv_compl conv_iso star_conv conv_contrav conv_one)

lemma forward_terminating_iff1:
  assumes "path x"
    shows "forward_terminating x \<longleftrightarrow> has_end_points x \<or> x = 0"
by (metis comp_assoc eq_refl le_bot one_compl tarski top_greatest)

lemma forward_terminating_iff2:
  assumes "path x"
    shows "forward_terminating x \<longleftrightarrow> x\<^sup>T \<le> x\<^sup>\<star>;-(x;1)"
by (metis assms backward_terminating_iff1 backward_terminating_iff2 end_point_iff2
          forward_terminating_iff1 compl_bot_eq conv_compl conv_invol conv_one conv_path
          double_compl start_point_iff2)

lemma forward_terminating_iff3:
  assumes "path x"
    shows "forward_terminating x \<longleftrightarrow> x \<le> x\<^sup>\<star>;-(x;1)"
by (metis assms backward_terminating_iff1 backward_terminating_iff3 end_point_iff2
          forward_terminating_iff1 compl_bot_eq conv_compl conv_invol conv_one conv_path
          double_compl start_point_iff2)

lemma forward_terminating_iff4:
  assumes "path x"
    shows "forward_terminating x \<longleftrightarrow> x \<le> -(1;x\<^sup>T);x\<^sup>T\<^sup>\<star>"
using forward_terminating_iff2 conv_contrav conv_iso star_conv assms conv_compl by force

lemma terminating_iff1:
  assumes "path x"
    shows "terminating x \<longleftrightarrow> has_start_end_points x \<or> x = 0"
using assms backward_terminating_iff1 forward_terminating_iff1 by fastforce

lemma terminating_iff2:
  assumes "path x"
    shows "terminating x \<longleftrightarrow> x \<le> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1) \<cdot> -(1;x\<^sup>T);x\<^sup>T\<^sup>\<star>"
using assms backward_terminating_iff2 forward_terminating_iff2 conv_compl conv_iso star_conv
by force

lemma terminating_iff3:
  assumes "path x"
    shows "terminating x \<longleftrightarrow> x \<le> x\<^sup>\<star>;-(x;1) \<cdot> -(1;x);x\<^sup>\<star>"
using assms backward_terminating_iff4 forward_terminating_iff3 by fastforce

lemma backward_terminating_path_irreflexive:
  assumes "backward_terminating_path x"
    shows "x \<le> -1'"
proof -
  have 1: "x;x\<^sup>T \<le> 1'"
    using assms is_inj_def path_def by blast
  have "x;(x\<^sup>T \<cdot> 1') \<le> x;x\<^sup>T \<cdot> x"
    by (metis inf.bounded_iff inf.commute mult_1_right mult_subdistl)
  also have "... \<le> 1' \<cdot> x"
    using 1 meet_iso by blast
  also have "... = 1' \<cdot> x\<^sup>T"
    by (metis conv_e conv_times inf.cobounded1 is_test_def test_eq_conv)
  finally have 2: "x\<^sup>T;-(x\<^sup>T \<cdot> 1') \<le> -(x\<^sup>T \<cdot> 1')"
    by (metis compl_le_swap1 conv_galois_1 inf.commute)
  have "x\<^sup>T \<cdot> 1' \<le> x\<^sup>T;1"
    by (simp add: le_infI1 maddux_20)
  hence "-(x\<^sup>T;1) \<le> -(x\<^sup>T \<cdot> 1')"
    using compl_mono by blast
  hence "x\<^sup>T;-(x\<^sup>T \<cdot> 1') + -(x\<^sup>T;1) \<le> -(x\<^sup>T \<cdot> 1')"
    using 2 by (simp add: le_supI)
  hence "x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1) \<le> -(x\<^sup>T \<cdot> 1')"
    by (simp add: rtc_inductl)
  hence "x\<^sup>T \<cdot> 1' \<cdot> x\<^sup>T\<^sup>\<star>;-(x\<^sup>T;1) = 0"
    by (simp add: compl_le_swap1 galois_aux)
  hence "x\<^sup>T \<cdot> 1' = 0"
    using assms backward_terminating_iff3 inf.order_iff le_infI1 by blast
  hence "x \<cdot> 1' = 0"
    by (simp add: conv_self_conjugate)
  thus ?thesis
    by (simp add: galois_aux)
qed

lemma forward_terminating_path_end_points_1:
  assumes "forward_terminating_path x"
    shows "x \<le> x\<^sup>+;end_points x"
proof -
  have 1: "-(x;1) \<cdot> x = 0"
    by (simp add: galois_aux maddux_20)
  have "x = x\<^sup>\<star>;-(x;1) \<cdot> x"
    using assms forward_terminating_iff3 inf.absorb2 by fastforce
  also have "... = (x\<^sup>+;-(x;1) + 1';-(x;1)) \<cdot> x"
    by (simp add: sup.commute)
  also have "... = x\<^sup>+;-(x;1) \<cdot> x + -(x;1) \<cdot> x"
    using inf_sup_distrib2 by fastforce
  also have "... = x\<^sup>+;-(x;1) \<cdot> x"
    using 1 by simp
  also have "... \<le> x\<^sup>+;(-(x;1) \<cdot> (x\<^sup>+)\<^sup>T;x)"
    using modular_1_var by blast
  also have "... = x\<^sup>+;(-(x;1) \<cdot> x\<^sup>T\<^sup>+;x)"
    using plus_conv by fastforce
  also have "... \<le> x\<^sup>+;end_points x"
    by (metis inf_commute inf_top_right modular_1' mult_subdistl plus_conv plus_top)
  finally show ?thesis .
qed

lemma forward_terminating_path_end_points_2:
  assumes "forward_terminating_path x"
    shows "x\<^sup>T \<le> x\<^sup>\<star>;end_points x"
proof -
  have "x\<^sup>T \<le> x\<^sup>T;x;x\<^sup>T"
    by (metis conv_invol x_leq_triple_x)
  also have "... \<le> x\<^sup>T;x;1"
    using mult_isol top_greatest by blast
  also have "... \<le> x\<^sup>T;x\<^sup>+;end_points x;1"
    by (metis assms forward_terminating_path_end_points_1 comp_assoc mult_isol mult_isor)
  also have "... = x\<^sup>T;x\<^sup>+;end_points x"
    by (metis inf_commute mult_assoc one_compl ra_1)
  also have "... \<le> x\<^sup>\<star>;end_points x"
    by (metis assms comp_assoc compl_le_swap1 conv_galois_1 conv_invol p_fun_compl path_def)
  finally show ?thesis .
qed

lemma forward_terminating_path_end_points_3:
  assumes "forward_terminating_path x"
  shows "start_points x \<le> x\<^sup>+;end_points x"
proof -
  have "start_points x \<le> x\<^sup>+;end_points x;1"
    using assms forward_terminating_path_end_points_1 comp_assoc mult_isor inf.coboundedI1
    by blast
  also have "... = x\<^sup>+;end_points x"
    by (metis inf_commute mult_assoc one_compl ra_1 )
  finally show ?thesis .
qed

lemma backward_terminating_path_start_points_1:
  assumes "backward_terminating_path x"
    shows "x\<^sup>T \<le> x\<^sup>T\<^sup>+;start_points x"
using assms forward_terminating_path_end_points_1 conv_backward_terminating_path by fastforce

lemma backward_terminating_path_start_points_2:
  assumes "backward_terminating_path x"
    shows "x \<le> x\<^sup>T\<^sup>\<star>;start_points x"
using assms forward_terminating_path_end_points_2 conv_backward_terminating_path by fastforce

lemma backward_terminating_path_start_points_3:
  assumes "backward_terminating_path x"
    shows "end_points x \<le> x\<^sup>T\<^sup>+;start_points x"
using assms forward_terminating_path_end_points_3 conv_backward_terminating_path by fastforce

(* lemma not shown in the paper; not necessary for other theorems *)
lemma path_aux1a:
 assumes "forward_terminating_path x"
   shows "x \<noteq> 0 \<longleftrightarrow> end_points x \<noteq> 0"
using assms end_point_iff2 forward_terminating_iff1 end_point_iff1 galois_aux2 by force

(* lemma not shown in the paper; not necessary for other theorems *)
lemma path_aux1b:
  assumes "backward_terminating_path y"
    shows "y \<noteq> 0 \<longleftrightarrow> start_points y \<noteq> 0"
using assms start_point_iff2 backward_terminating_iff1 start_point_iff1 galois_aux2 by force

(* lemma not shown in the paper; not necessary for other theorems *)
lemma path_aux1:
  assumes "forward_terminating_path x"
      and "backward_terminating_path y"
    shows "x \<noteq> 0 \<or> y \<noteq> 0 \<longleftrightarrow> end_points x \<noteq> 0 \<or> start_points y \<noteq> 0"
using assms path_aux1a path_aux1b by blast

text \<open>Equivalences for \<open>finite\<close>\<close>

lemma backward_finite_iff_msc:
  "backward_finite x \<longleftrightarrow> many_strongly_connected x \<or> backward_terminating x"
proof
  assume 1: "backward_finite x"
  thus "many_strongly_connected x \<or> backward_terminating x"
  proof (cases "-(1;x);x;1 = 0")
    assume "-(1;x);x;1 = 0"
    thus "many_strongly_connected x \<or> backward_terminating x"
      using 1 by (metis conv_invol many_strongly_connected_iff_1 sup_bot_right)
  next
    assume "-(1;x);x;1 \<noteq> 0"
    hence "1;-(1;x);x;1 = 1"
      by (simp add: comp_assoc tarski)
    hence "-(1;x);x;1 = 1"
      by (metis comp_assoc conv_compl conv_contrav conv_invol conv_one one_compl)
    thus "many_strongly_connected x \<or> backward_terminating x"
      using 1 by simp
  qed
next
  assume "many_strongly_connected x \<or> backward_terminating x"
  thus "backward_finite x"
    by (metis star_ext sup.coboundedI1 sup.coboundedI2)
qed

lemma forward_finite_iff_msc:
  "forward_finite x \<longleftrightarrow> many_strongly_connected x \<or> forward_terminating x"
by (metis backward_finite_iff_msc conv_backward_finite conv_backward_terminating conv_invol)

lemma finite_iff_msc:
  "finite x \<longleftrightarrow> many_strongly_connected x \<or> terminating x"
using backward_finite_iff_msc forward_finite_iff_msc finite_iff by fastforce

text \<open>Path concatenation\<close>

lemma path_concatenation:
  assumes "forward_terminating_path x"
      and "backward_terminating_path y"
      and "end_points x = start_points y"
      and "x;1 \<cdot> (x\<^sup>T;1 + y;1) \<cdot> y\<^sup>T;1 = 0"
    shows "path (x+y)"
proof (cases "y = 0")
  assume "y = 0"
  thus ?thesis
    using assms(1) by fastforce
next
  assume as: "y \<noteq> 0"
  show ?thesis
  proof (unfold path_def; intro conjI)
    from assms(4) have a: "x;1 \<cdot> x\<^sup>T;1 \<cdot> y\<^sup>T;1 + x;1 \<cdot> y;1 \<cdot> y\<^sup>T;1= 0"
      by (simp add: inf_sup_distrib1 inf_sup_distrib2)
    hence aux1: "x;1 \<cdot> x\<^sup>T;1 \<cdot> y\<^sup>T;1 = 0"
      using sup_eq_bot_iff by blast
    from a have aux2: "x;1 \<cdot> y;1 \<cdot> y\<^sup>T;1= 0"
      using sup_eq_bot_iff by blast

    show "is_inj (x + y)"
    proof (unfold is_inj_def; auto simp add: distrib_left)
      show "x;x\<^sup>T \<le> 1'"
        using assms(1) path_def is_inj_def by blast
      show "y;y\<^sup>T \<le> 1'"
        using assms(2) path_def is_inj_def by blast
      have "y;x\<^sup>T = 0"
        by (metis assms(3) aux1 annir comp_assoc conv_one le_bot modular_var_2 one_idem_mult
                  path_concat_aux_2 schroeder_2)
      thus "y;x\<^sup>T \<le> 1'"
        using bot_least le_bot by blast
      thus "x;y\<^sup>T \<le> 1'"
        using conv_iso by force
    qed

    show "is_p_fun (x + y)"
    proof (unfold is_p_fun_def; auto simp add: distrib_left)
      show "x\<^sup>T;x \<le> 1'"
        using assms(1) path_def is_p_fun_def by blast
      show "y\<^sup>T;y \<le> 1'"
        using assms(2) path_def is_p_fun_def by blast
      have "y\<^sup>T;x \<le> y\<^sup>T;(y;1 \<cdot> x;1)"
        by (metis conjugation_prop2 inf.commute inf_top.left_neutral maddux_20 mult_isol order_trans
                  schroeder_1_var)
      also have "... = 0"
        using assms(3) aux2 annir inf_commute path_concat_aux_1 by fastforce
      finally show "y\<^sup>T;x \<le> 1'"
        using bot_least le_bot by blast
      thus "x\<^sup>T;y \<le> 1'"
        using conv_iso by force
    qed

    show "connected (x + y)"
    proof (auto simp add: distrib_left)
      have "x;1;x \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
        using assms(1) path_def by simp
      also have "... \<le> (x\<^sup>\<star>;y\<^sup>\<star>)\<^sup>\<star> + (x\<^sup>T\<^sup>\<star>;y\<^sup>T\<^sup>\<star>)\<^sup>\<star>"
        using join_iso join_isol star_subdist by simp
      finally show "x;1;x \<le> (x\<^sup>\<star>;y\<^sup>\<star>)\<^sup>\<star> + (x\<^sup>T\<^sup>\<star>;y\<^sup>T\<^sup>\<star>)\<^sup>\<star>" .
      have "y;1;y \<le> y\<^sup>\<star> + y\<^sup>T\<^sup>\<star>"
        using assms(2) path_def by simp
      also have "... \<le> (x\<^sup>\<star>;y\<^sup>\<star>)\<^sup>\<star> + (x\<^sup>T\<^sup>\<star>;y\<^sup>T\<^sup>\<star>)\<^sup>\<star>"
        by (metis star_denest star_subdist sup.mono sup_commute)
      finally show "y;1;y \<le> (x\<^sup>\<star>;y\<^sup>\<star>)\<^sup>\<star> + (x\<^sup>T\<^sup>\<star>;y\<^sup>T\<^sup>\<star>)\<^sup>\<star>" .

      show "y;1;x \<le> (x\<^sup>\<star>;y\<^sup>\<star>)\<^sup>\<star> + (x\<^sup>T\<^sup>\<star>;y\<^sup>T\<^sup>\<star>)\<^sup>\<star>"
      proof -
        have "(y;1);1;(1;x) \<le> y\<^sup>T\<^sup>\<star>;x\<^sup>T\<^sup>\<star>"
        proof (rule_tac v="start_points y" in path_concat_aux_0)
          show "is_vector (start_points y)"
            by (metis is_vector_def comp_assoc one_compl one_idem_mult ra_1)
          show "start_points y \<noteq> 0"
            using as
            by (metis assms(2) conv_compl conv_contrav conv_one inf.orderE inf_bot_right
                      inf_top.right_neutral maddux_141)
          have "(start_points y);1;y\<^sup>T \<le> y\<^sup>\<star>"
            by (rule path_concat_aux_5) (simp_all add: assms(2))
          thus "y;1;(start_points y)\<^sup>T \<le> y\<^sup>T\<^sup>\<star>"
            by (metis (mono_tags, lifting) conv_iso comp_assoc conv_contrav conv_invol conv_one
                      star_conv)
          have "end_points x;1;x \<le> x\<^sup>T\<^sup>\<star>"
            apply (rule path_concat_aux_5)
            using assms(1) conv_path by simp_all
          thus "start_points y;(1;x) \<le> x\<^sup>T\<^sup>\<star>"
            by (metis assms(3) mult_assoc)
        qed
        thus ?thesis
          by (metis comp_assoc le_supI2 less_eq_def one_idem_mult star_denest star_subdist_var_1
                    sup.commute)
      qed

      show "x;1;y \<le> (x\<^sup>\<star>;y\<^sup>\<star>)\<^sup>\<star> + (x\<^sup>T\<^sup>\<star>;y\<^sup>T\<^sup>\<star>)\<^sup>\<star>"
      proof -
        have "(x;1);1;(1;y) \<le> x\<^sup>\<star>;y\<^sup>\<star>"
        proof (rule_tac v="start_points y" in path_concat_aux_0)
          show "is_vector (start_points y)"
            by (simp add: comp_assoc is_vector_def one_compl vector_1_comm)
          show "start_points y \<noteq> 0"
            using as assms(2,4) backward_terminating_iff1 galois_aux2 start_point_iff1 start_point_iff2
            by blast
          have "end_points x;1;x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>"
            apply (rule path_concat_aux_5)
            using assms(1) conv_path by simp_all
          hence "(end_points x;1;x\<^sup>T)\<^sup>T \<le> (x\<^sup>T\<^sup>\<star>)\<^sup>T"
            using conv_iso by blast
          thus "x;1;(start_points y)\<^sup>T \<le> x\<^sup>\<star>"
            by (simp add: assms(3) comp_assoc star_conv)
          have "start_points y;1;y \<le> y\<^sup>\<star>"
            by (rule path_concat_aux_5) (simp_all add: assms(2))
          thus "start_points y;(1;y) \<le> y\<^sup>\<star>"
            by (simp add: mult_assoc)
        qed
        thus ?thesis
          by (metis comp_assoc dual_order.trans le_supI1 one_idem_mult star_ext)
      qed
    qed
  qed
qed

lemma path_concatenation_with_edge:
   assumes "x\<noteq>0"
      and "forward_terminating_path x"
      and "is_point q"
      and "q \<le> -(1;x)"
    shows "path (x+(end_points x);q\<^sup>T)"
proof (rule path_concatenation)
  from assms(1,2) have 1: "is_point(end_points x)"
    using end_point_zero_point path_aux1a by blast
  show 2: "backward_terminating_path ((end_points x);q\<^sup>T)"
    apply (intro conjI)
    apply (metis edge_is_path 1 assms(3))
    by (metis assms(2-4) 1 bot_least comp_assoc compl_le_swap1 conv_galois_2 double_compl
              end_point_iff1 le_supE point_equations(1) tarski top_le)
  thus "end_points x = start_points ((end_points x);q\<^sup>T)"
    by (metis assms(3) 1 edge_start comp_assoc compl_top_eq double_compl inf.absorb_iff2 inf.commute
              inf_top_right modular_2_aux' point_equations(2))
  show "x;1 \<cdot> (x\<^sup>T;1 + ((end_points x);q\<^sup>T);1) \<cdot> ((end_points x);q\<^sup>T)\<^sup>T;1 = 0"
    using 2 by (metis assms(3,4) annir compl_le_swap1 compl_top_eq conv_galois_2 double_compl
                      inf.absorb_iff2 inf.commute modular_1' modular_2_aux' point_equations(2))
  show "forward_terminating_path x"
    by (simp add: assms(2))
qed

lemma path_concatenation_cycle_free:
  assumes "forward_terminating_path x"
      and "backward_terminating_path y"
      and "end_points x = start_points y"
      and "x;1 \<cdot> y\<^sup>T;1 = 0"
    shows "path (x+y)"
apply (rule path_concatenation,simp_all add: assms)
by (metis assms(4) inf.left_commute inf_bot_right inf_commute)

lemma path_concatenation_start_points_approx:
  assumes "end_points x = start_points y"
    shows "start_points (x+y) \<le> start_points x"
proof -
  have "start_points (x+y) = x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1) + y;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1)"
    by (simp add: inf.assoc inf_sup_distrib2)
  also with assms(1) have "... = x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1) + x\<^sup>T;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(x;1)"
    by (metis inf.assoc inf.left_commute)
  also have "... = x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1)"
    by simp
  also have "... \<le> start_points x"
    using inf_le1 by blast
  finally show ?thesis .
qed

lemma path_concatenation_end_points_approx:
  assumes "end_points x = start_points y"
     shows "end_points (x+y) \<le> end_points y"
proof -
  have "end_points (x+y) = x\<^sup>T;1 \<cdot> -(x;1) \<cdot> -(y;1) + y\<^sup>T;1 \<cdot> -(x;1) \<cdot> -(y;1)"
    by (simp add: inf.assoc inf_sup_distrib2)
  also from assms(1) have "... = y;1 \<cdot> -(y\<^sup>T;1) \<cdot> -(y;1) + y\<^sup>T;1 \<cdot> -(x;1) \<cdot> -(y;1)"
    by simp
  also have "... = y\<^sup>T;1 \<cdot> -(x;1) \<cdot> -(y;1)"
    by (simp add: inf.commute)
  also have "... \<le> end_points y"
    using inf_le1 meet_iso by blast
  finally show ?thesis .
qed

lemma path_concatenation_start_points:
  assumes "end_points x = start_points y"
      and "x;1 \<cdot> y\<^sup>T;1 = 0"
    shows "start_points (x+y) = start_points x"
proof -
  from assms(2) have aux: "x;1 \<cdot> -(y\<^sup>T;1) = x;1"
    by (simp add: galois_aux inf.absorb1)

  have "start_points (x+y) = (x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1)) + (y;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1))"
    by (simp add: inf_sup_distrib2 inf.assoc)
  also from assms(1) have "... = (x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1)) + (x\<^sup>T;1 \<cdot> -(x;1) \<cdot> -(x\<^sup>T;1))"
    using inf.assoc inf.commute by simp
  also have "... = (x;1 \<cdot> -(x\<^sup>T;1) \<cdot> -(y\<^sup>T;1))"
    by (simp add: inf.assoc)
  also from aux have "... = x;1 \<cdot> -(x\<^sup>T;1)"
    by (metis inf.assoc inf.commute)
  finally show ?thesis .
qed

lemma path_concatenation_end_points:
  assumes "end_points x = start_points y"
      and "x;1 \<cdot> y\<^sup>T;1 = 0"
    shows "end_points (x+y) = end_points y"
proof -
  from assms(2) have aux: "y\<^sup>T;1 \<cdot> -(x;1) = y\<^sup>T;1"
    using galois_aux inf.absorb1 inf_commute by blast

  have "end_points (x+y) = (x\<^sup>T;1 + y\<^sup>T;1) \<cdot> -(x;1) \<cdot> -(y;1)"
    using inf.assoc by simp
  also from assms(1) have "... = (y;1 \<cdot> -(y\<^sup>T;1) \<cdot> -(y;1)) + (y\<^sup>T;1 \<cdot> -(x;1) \<cdot> -(y;1))"
    by (simp add: inf_sup_distrib2)
  also have "... = y\<^sup>T;1 \<cdot> -(x;1) \<cdot> -(y;1)"
    by (simp add: inf.assoc)
  also from aux have "... = y\<^sup>T;1 \<cdot> -(y;1)"
    by (metis inf.assoc inf.commute)
  finally show ?thesis .
qed

lemma path_concatenation_cycle_free_complete:
  assumes "forward_terminating_path x"
      and "backward_terminating_path y"
      and "end_points x = start_points y"
      and "x;1 \<cdot> y\<^sup>T;1 = 0"
    shows "path (x+y) \<and> start_points (x+y) = start_points x \<and> end_points (x+y) = end_points y"
using assms path_concatenation_cycle_free path_concatenation_end_points path_concatenation_start_points
by blast

text \<open>Path restriction (path from a given point)\<close>

lemma reachable_points_iff:
  assumes "point p"
    shows "(x\<^sup>T\<^sup>\<star>;p \<cdot> x) = (x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x"
proof (rule antisym)
  show "(x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x \<le> x\<^sup>T\<^sup>\<star>;p \<cdot> x"
  proof (rule le_infI)
    show "(x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x \<le> x\<^sup>T\<^sup>\<star>;p"
    proof -
      have "(x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x \<le> x\<^sup>T\<^sup>\<star>;p;1"
        by (simp add: mult_isol_var)
      also have "... \<le> x\<^sup>T\<^sup>\<star>;p"
        using assms by (simp add: comp_assoc eq_iff point_equations(1) point_is_point)
      finally show ?thesis .
    qed
    show "(x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x \<le> x"
      by (metis inf_le2 mult_isor mult_onel)
  qed
  show "x\<^sup>T\<^sup>\<star>;p \<cdot> x \<le> (x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x"
  proof -
    have "(x\<^sup>T\<^sup>\<star>;p);x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>;p + -1'"
      by (metis assms comp_assoc is_vector_def mult_isol point_def sup.coboundedI1 top_greatest)
    hence aux: "(-(x\<^sup>T\<^sup>\<star>;p) \<cdot> 1');x \<le> -(x\<^sup>T\<^sup>\<star>;p)"
      using compl_mono conv_galois_2 by fastforce
    have "x = (x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x + (-(x\<^sup>T\<^sup>\<star>;p) \<cdot> 1');x"
      by (metis aux4 distrib_right inf_commute mult_1_left)
    also with aux have "... \<le> (x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x + -(x\<^sup>T\<^sup>\<star>;p)"
      using join_isol by blast
    finally have "x \<le> (x\<^sup>T\<^sup>\<star>;p \<cdot> 1');x + -(x\<^sup>T\<^sup>\<star>;p)" .
    thus ?thesis
      using galois_2 inf.commute by fastforce
  qed
qed

lemma path_from_given_point:
  assumes "path x"
      and "point p"
    shows "path(x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
      and "start_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) \<le> p"
      and "end_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) \<le> end_points(x)"
proof (unfold path_def; intro conjI)
  show uni: "is_p_fun (x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
    by (metis assms(1) inf_commute is_p_fun_def p_fun_mult_var path_def)
  show inj: "is_inj (x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
    by (metis abel_semigroup.commute assms(1) conv_times inf.abel_semigroup_axioms inj_p_fun
              is_p_fun_def p_fun_mult_var path_def)
  show "connected (x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
  proof -
    let ?t="x\<^sup>T\<^sup>\<star>;p \<cdot> 1'"
    let ?u="-(x\<^sup>T\<^sup>\<star>;p) \<cdot> 1'"
    (* some aux statements about ?t and ?u *)
    have t_plus_u: "?t + ?u = 1'"
      by (simp add: inf.commute)
    have t_times_u: "?t ; ?u \<le> 0"
      by (simp add: inf.left_commute is_test_def test_comp_eq_mult)
    have t_conv: "?t\<^sup>T=?t"
      using inf.cobounded2 is_test_def test_eq_conv by blast
    have txu_zero: "?t;x;?u \<le> 0"
    proof -
      have "x\<^sup>T;?t;1 \<le> -?u"
      proof -
        have "x\<^sup>T;?t;1 \<le> x\<^sup>T;x\<^sup>T\<^sup>\<star>;p"
          using assms(2)
          by (simp add: is_vector_def mult.semigroup_axioms mult_isol_var mult_subdistr order.refl
                        point_def semigroup.assoc)
        also have "... \<le> -?u"
          by (simp add: le_supI1 mult_isor)
        finally show ?thesis .
      qed
      thus ?thesis
        by (metis compl_bot_eq compl_le_swap1 conv_contrav conv_galois_1 t_conv)
    qed
    hence txux_zero: "?t;x;?u;x \<le> 0"
      using annil le_bot by fastforce
    (* end some aux statements about ?t and ?u *)

    have tx_leq: "?t;x\<^sup>\<star> \<le> (?t;x)\<^sup>\<star>"
    proof -
      have "?t;x\<^sup>\<star> = ?t;(?t;x + ?u;x)\<^sup>\<star>"
        using t_plus_u by (metis distrib_right' mult_onel)
      also have "... = ?t;(?u;x;(?u;x)\<^sup>\<star>;(?t;x)\<^sup>\<star>+(?t;x)\<^sup>\<star>)"
        using txux_zero star_denest_10 by (simp add: comp_assoc le_bot)
      also have "... = ?t;?u;x;(?u;x)\<^sup>\<star>;(?t;x)\<^sup>\<star>+?t;(?t;x)\<^sup>\<star>"
        by (simp add: comp_assoc distrib_left)
      also have "... \<le> 0;x;(?u;x)\<^sup>\<star>;(?t;x)\<^sup>\<star>+?t;(?t;x)\<^sup>\<star>"
        using le_bot t_times_u by blast
      also have "... \<le>(?t;x)\<^sup>\<star>"
        by (metis annil inf.commute inf_bot_right le_supI mult_onel mult_subdistr)
      finally show ?thesis .
    qed

    hence aux: "?t;x\<^sup>\<star>;?t \<le> (?t;x)\<^sup>\<star>"
      using inf.cobounded2 order.trans prod_star_closure star_ref by blast
    with t_conv have aux_trans: "?t;x\<^sup>T\<^sup>\<star>;?t \<le> (?t;x)\<^sup>T\<^sup>\<star>"
      by (metis comp_assoc conv_contrav conv_self_conjugate_var g_iso star_conv)

    from aux aux_trans have "?t;(x\<^sup>\<star>+x\<^sup>T\<^sup>\<star>);?t \<le> (?t;x)\<^sup>\<star> + (?t;x)\<^sup>T\<^sup>\<star>"
      by (metis sup_mono distrib_right' distrib_left)
    with assms(1) path_concat_aux3_1 have "?t;(x;1;x\<^sup>T);?t \<le> (?t;x)\<^sup>\<star> + (?t;x)\<^sup>T\<^sup>\<star>"
      using dual_order.trans mult_double_iso by blast
    with t_conv have "(?t;x);1;(?t;x)\<^sup>T \<le> (?t;x)\<^sup>\<star> + (?t;x)\<^sup>T\<^sup>\<star>"
      using comp_assoc conv_contrav by fastforce
    with connected_iff2 show ?thesis
      using assms(2) inj reachable_points_iff uni by fastforce
  qed
next
  show "start_points (x\<^sup>T\<^sup>\<star>;p \<cdot> x) \<le> p"
  proof -
    have 1: "is_vector (x\<^sup>T\<^sup>\<star>;p)"
      using assms(2) by (simp add: is_vector_def mult_assoc point_def)
    hence "(x\<^sup>T\<^sup>\<star>;p \<cdot> x);1 \<le> x\<^sup>T\<^sup>\<star>;p"
      by (simp add: inf.commute vector_1_comm)
    also have "... = x\<^sup>T\<^sup>+;p + p"
      by (simp add: sup.commute)
    finally have 2: "(x\<^sup>T\<^sup>\<star>;p \<cdot> x);1 \<cdot> -(x\<^sup>T\<^sup>+;p) \<le> p"
      using galois_1 by blast
    have "(x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 = (x\<^sup>T \<cdot> (x\<^sup>T\<^sup>\<star>;p)\<^sup>T);1"
      by (simp add: inf.commute)
    also have "... = x\<^sup>T;(x\<^sup>T\<^sup>\<star>;p \<cdot> 1)"
      using 1 vector_2 by blast
    also have "... = x\<^sup>T\<^sup>+;p"
      by (simp add: comp_assoc)
    finally show "start_points (x\<^sup>T\<^sup>\<star>;p \<cdot> x) \<le> p"
      using 2 by simp
  qed
next
  show "end_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) \<le> end_points(x)"
  proof -
    have 1: "is_vector (x\<^sup>T\<^sup>\<star>;p)"
      using assms(2) by (simp add: is_vector_def mult_assoc point_def)
    have "(x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 = ((x\<^sup>T\<^sup>\<star>;p)\<^sup>T \<cdot> x\<^sup>T);1"
      by (simp add: star_conv)
    also have "... = x\<^sup>T;(x\<^sup>T\<^sup>\<star>;p \<cdot> 1)"
      using 1 vector_2 inf.commute by fastforce
    also have "... \<le> x\<^sup>T\<^sup>\<star>;p"
      using comp_assoc mult_isor by fastforce
    finally have 2: "(x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 \<cdot> -(x\<^sup>T\<^sup>\<star>;p) = 0"
      using galois_aux2 by blast
    have "(x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 \<cdot> -((x\<^sup>T\<^sup>\<star>;p \<cdot> x);1) = (x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 \<cdot> (-(x\<^sup>T\<^sup>\<star>;p) + -(x;1))"
      using 1 vector_1 by fastforce
    also have "... = (x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 \<cdot> -(x\<^sup>T\<^sup>\<star>;p) + (x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 \<cdot> -(x;1)"
      using inf_sup_distrib1 by blast
    also have "... = (x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 \<cdot> -(x;1)"
      using 2 by simp
    also have "... \<le> x\<^sup>T;1 \<cdot> -(x;1)"
      using meet_iso mult_subdistr_var by fastforce
    finally show ?thesis .
  qed
qed

lemma path_from_given_point':
  assumes "has_start_points_path x"
      and "point p"
      and "p \<le> x;1" (* p has a successor hence path not empty *)
    shows "path(x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
      and "start_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) = p"
      and "end_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) = end_points(x)"
proof -
  show "path(x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
    using assms path_from_given_point(1) by blast
next
  show "start_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) = p"
  proof (simp only: eq_iff; rule conjI)
    show "start_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) \<le> p"
      using assms path_from_given_point(2) by blast
    show "p \<le> start_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
    proof -
      have 1: "is_vector(x\<^sup>T\<^sup>\<star>;p)"
        using assms(2) comp_assoc is_vector_def point_equations(1) point_is_point by fastforce
      hence a: "p \<le> (x\<^sup>T\<^sup>\<star>;p \<cdot> x);1"
        by (metis vector_1 assms(3) conway.dagger_unfoldl_distr inf.orderI inf_greatest
                  inf_sup_absorb)

      have "x\<^sup>T\<^sup>+;p \<cdot> p \<le> (x\<^sup>T\<^sup>+ \<cdot> 1'); p"
        using assms(2) inj_distr point_def by fastforce
      also have "... \<le> (-1'\<^sup>T \<cdot> 1'); p"
        using assms(1) path_acyclic
        by (metis conv_contrav conv_e meet_iso mult_isor star_conv star_slide_var test_converse)
      also have "... \<le> 0"
        by simp
      finally have 2: "x\<^sup>T\<^sup>+;p \<cdot> p \<le> 0" .

      have b: "p \<le> -((x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1)"
      proof -
        have "(x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1 = ((x\<^sup>T\<^sup>\<star>;p)\<^sup>T \<cdot> x\<^sup>T);1"
          by (simp add: star_conv)
        also have "... = x\<^sup>T;(x\<^sup>T\<^sup>\<star>;p \<cdot> 1)"
          using 1 vector_2 inf.commute by fastforce
        also have "... = x\<^sup>T;x\<^sup>T\<^sup>\<star>;p"
          by (simp add: comp_assoc)
        also have "... \<le> -p"
          using 2 galois_aux le_bot by blast
        finally show ?thesis
          using compl_le_swap1 by blast
      qed
      with a show ?thesis
        by simp
    qed
  qed
next
  show "end_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) = end_points(x)"
  proof (simp only: eq_iff; rule conjI)
    show "end_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x) \<le> end_points(x)"
      using assms path_from_given_point(3) by blast
    show "end_points(x) \<le> end_points(x\<^sup>T\<^sup>\<star>;p \<cdot> x)"
    proof -
      have 1: "is_vector(x\<^sup>T\<^sup>\<star>;p)"
        using assms(2) comp_assoc is_vector_def point_equations(1) point_is_point by fastforce
      have 2: "is_vector(end_points(x))"
        by (simp add: comp_assoc is_vector_def one_compl vector_1_comm)
      have a: "end_points(x) \<le> (x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1"
      proof -
        have "x\<^sup>T;1 \<cdot> 1;x\<^sup>T = x\<^sup>T;1;x\<^sup>T"
          by (simp add: vector_meet_comp_x')
        also have "... \<le> x\<^sup>T\<^sup>\<star> + x\<^sup>\<star>"
          using assms(1) path_concat_aux3_3 sup.commute by fastforce
        also have "... = x\<^sup>T\<^sup>\<star> + x\<^sup>+"
          by (simp add: star_star_plus sup.commute)
        also have "... \<le> x\<^sup>T\<^sup>\<star> + x;1"
          using join_isol mult_isol by fastforce
        finally have "end_points(x) \<cdot> 1;x\<^sup>T \<le> x\<^sup>T\<^sup>\<star>"
          by (metis galois_1 inf.assoc inf.commute sup_commute)
        hence "end_points(x) \<cdot> p\<^sup>T \<le> x\<^sup>T\<^sup>\<star>"
          using assms(3)
          by (metis conv_contrav conv_iso conv_one dual_order.trans inf.cobounded1 inf.right_idem
                    inf_mono)
        hence "end_points(x) ; p\<^sup>T \<le> x\<^sup>T\<^sup>\<star>"
          using assms(2) 2 by (simp add: point_def vector_meet_comp)
        hence "end_points(x) \<le> x\<^sup>T\<^sup>\<star>;p"
          using assms(2) point_def ss423bij by blast
        hence "x\<^sup>T;1 \<le> x\<^sup>T\<^sup>\<star>;p + x;1"
          by (simp add: galois_1 sup_commute)
        hence "x\<^sup>T;1 \<le> x\<^sup>T\<^sup>+;p + p + x;1"
          by (metis conway.dagger_unfoldl_distr sup_commute)
        hence "x\<^sup>T;1 \<le> x\<^sup>T\<^sup>+;p + x;1"
          by (simp add: assms(3) sup.absorb2 sup.assoc)
        hence "end_points(x) \<le> x\<^sup>T\<^sup>+;p"
          by (simp add: galois_1 sup_commute)
        also have "... = (x\<^sup>T\<^sup>\<star>;p \<cdot> x)\<^sup>T;1"
          using 1 inf_commute mult_assoc vector_2 by fastforce
        finally show ?thesis .
      qed
      have "x\<^sup>T;1 \<cdot> (x\<^sup>T\<^sup>\<star>;p \<cdot> x);1 \<le> x;1"
        by (simp add: le_infI2 mult_isor)
      hence b: "end_points(x) \<le> -((x\<^sup>T\<^sup>\<star>;p \<cdot> x);1)"
        using galois_1 galois_2 by blast
      with a show ?thesis
        by simp
    qed
  qed
qed

text \<open>Cycles\<close>

lemma selfloop_is_cycle:
  assumes "is_point x"
  shows "cycle (x;x\<^sup>T)"
  by (simp add: assms edge_is_path)

lemma start_point_no_cycle:
  assumes "has_start_points_path x"
    shows "\<not> cycle x"
using assms many_strongly_connected_implies_no_start_end_points no_start_end_points_iff
      start_point_iff1 start_point_iff2 by blast

lemma end_point_no_cycle:
  assumes "has_end_points_path x"
    shows "\<not> cycle x"
using assms end_point_iff2 end_point_iff1 many_strongly_connected_implies_no_start_end_points
      no_start_end_points_iff by blast

lemma cycle_no_points:
  assumes "cycle x"
    shows "start_points x = 0"
      and "end_points x = 0"
  by (metis assms inf_compl_bot many_strongly_connected_implies_no_start_end_points)+

text \<open>Path concatenation to cycle\<close>

lemma path_path_equals_cycle_aux:
  assumes "has_start_end_points_path x"
      and "has_start_end_points_path y"
      and "start_points x = end_points y"
      and "end_points x = start_points y"
shows "x \<le> (x+y)\<^sup>T\<^sup>\<star>"
proof-
  let ?e = "end_points(x)"
  let ?s = "start_points(x)"
  have sp: "is_point(?s)"
    using assms(1) start_point_iff2 has_start_end_points_path_iff by blast
  have ep: "is_point(?e)"
    using assms(1) end_point_iff2 has_start_end_points_path_iff by blast

  have "x \<le> x\<^sup>T\<^sup>\<star>;?s;1 \<cdot> 1;?e\<^sup>T;x\<^sup>T\<^sup>\<star>"
      by (metis assms(1) backward_terminating_path_start_points_2 end_point_iff2 ep
                forward_terminating_iff1 forward_terminating_path_end_points_2 comp_assoc
                conv_contrav conv_invol conv_iso inf.boundedI point_equations(1) point_equations(4)
                star_conv sp start_point_iff2)
    also have "... = x\<^sup>T\<^sup>\<star>;?s;1;?e\<^sup>T;x\<^sup>T\<^sup>\<star>"
      by (metis inf_commute inf_top_right ra_1)
    also have "... = x\<^sup>T\<^sup>\<star>;?s;?e\<^sup>T;x\<^sup>T\<^sup>\<star>"
      by (metis ep comp_assoc point_equations(4))
    also have "... \<le> x\<^sup>T\<^sup>\<star>;y\<^sup>T\<^sup>\<star>;x\<^sup>T\<^sup>\<star>"
      by (metis (mono_tags, lifting) assms(2-4) start_to_end comp_assoc conv_contrav conv_invol
                conv_iso mult_double_iso star_conv)
    also have "... = (x\<^sup>\<star>;y\<^sup>\<star>;x\<^sup>\<star>)\<^sup>T"
      by (simp add: comp_assoc star_conv)
    also have "... \<le> ((x+y)\<^sup>\<star>;(x+y)\<^sup>\<star>;(x+y)\<^sup>\<star>)\<^sup>T"
      by (metis conv_invol conv_iso prod_star_closure star_conv star_denest star_ext star_iso
                star_trans_eq sup_ge1)
    also have "... = (x+y)\<^sup>T\<^sup>\<star>"
       by (metis star_conv star_trans_eq)
    finally show x: "x \<le> (x+y)\<^sup>T\<^sup>\<star>" .
  qed

lemma path_path_equals_cycle:
  assumes "has_start_end_points_path x"
      and "has_start_end_points_path y"
      and "start_points x = end_points y"
      and "end_points x = start_points y"
      and "x;1 \<cdot> (x\<^sup>T;1 + y;1) \<cdot> y\<^sup>T;1 = 0"
    shows "cycle(x + y)"
proof (intro conjI)
  show "path (x + y)"
    apply (rule path_concatenation)
    using assms by(simp_all add:has_start_end_points_iff)
  show "many_strongly_connected (x + y)"
    by (metis path_path_equals_cycle_aux assms(1-4) sup.commute le_supI many_strongly_connected_iff_3)
qed

lemma path_edge_equals_cycle:
  assumes "has_start_end_points_path x"
    shows "cycle(x + end_points(x);(start_points x)\<^sup>T)"
proof (rule path_path_equals_cycle)
  let ?s = "start_points x"
  let ?e = "end_points x"
  let ?y = "(?e;?s\<^sup>T)"

  have sp: "is_point(?s)"
    using start_point_iff2 assms has_start_end_points_path_iff by blast
  have ep: "is_point(?e)"
    using end_point_iff2 assms has_start_end_points_path_iff by blast

  show "has_start_end_points_path x"
    using assms by blast
  show "has_start_end_points_path ?y"
    using edge_is_path
    by (metis assms edge_end edge_start end_point_iff2 end_point_iff1 galois_aux2
              has_start_end_points_iff inf.left_idem inf_compl_bot_right start_point_iff2)
  show "?s = end_points ?y"
    by (metis sp ep edge_end annil conv_zero inf.left_idem inf_compl_bot_right)
  thus "?e = start_points ?y"
    by (metis edge_start ep conv_contrav conv_invol sp)
  show "x;1 \<cdot> (x\<^sup>T;1 + ?e;?s\<^sup>T;1) \<cdot> (?e;?s\<^sup>T)\<^sup>T;1 = 0"
  proof -
    have "x;1 \<cdot> (x\<^sup>T;1 + ?e;?s\<^sup>T;1) \<cdot> (?e;?s\<^sup>T)\<^sup>T;1 = x;1 \<cdot> (x\<^sup>T;1 + ?e;1;?s\<^sup>T;1) \<cdot> (?s;?e\<^sup>T);1"
      using sp comp_assoc point_equations(3) by fastforce
    also have "... = x;1 \<cdot> (x\<^sup>T;1 + ?e;1) \<cdot> ?s;1"
      by (metis sp ep comp_assoc point_equations(1,3))
    also have "... \<le> 0"
      by (simp add: sp ep inf.assoc point_equations(1))
    finally show ?thesis
      using bot_unique by blast
  qed
qed

text \<open>Break cycles\<close>

lemma cycle_remove_edge:
  assumes "cycle x"
      and "point s"
      and "point e"
      and "e;s\<^sup>T \<le> x"
    shows "path(x \<cdot> -(e;s\<^sup>T))"
      and "start_points (x \<cdot> -(e;s\<^sup>T)) \<le> s"
      and "end_points (x \<cdot> -(e;s\<^sup>T)) \<le> e"
proof -
  show "path(x \<cdot> -(e;s\<^sup>T))"
  proof (unfold path_def; intro conjI)
    show 1: "is_p_fun(x \<cdot> -(e;s\<^sup>T))"
      using assms(1) path_def is_p_fun_def p_fun_mult_var by blast
    show 2: "is_inj(x \<cdot> -(e;s\<^sup>T))"
      using assms(1) path_def inf.cobounded1 injective_down_closed by blast
    show "connected (x \<cdot> -(e;s\<^sup>T))"
    proof -
      have "x\<^sup>\<star> = ((x \<cdot> -(e;s\<^sup>T)) + e;s\<^sup>T)\<^sup>\<star>"
        by (metis assms(4) aux4_comm inf.absorb2)
      also have "... = (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; (e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>)\<^sup>\<star>"
        by simp
      also have "... = (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; (1' + e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>;(e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>)\<^sup>\<star>)"
        by fastforce
      also have "... = (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>;(e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>)\<^sup>\<star>"
        by (simp add: distrib_left mult_assoc)
      also have "... = (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; e;(s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>;e)\<^sup>\<star>;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>"
        by (simp add: comp_assoc star_slide)
      also have "... \<le> (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; e;1;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>"
        using top_greatest join_isol mult_double_iso by (metis mult_assoc)
      also have "... = (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>"
        using assms(3) by (simp add: comp_assoc is_vector_def point_def)
      finally have 3: "x\<^sup>\<star> \<le> (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>" .

      from assms(4) have "e;s\<^sup>T \<le> e;e\<^sup>T;x"
        using assms(3) comp_assoc mult_isol point_def ss423conv by fastforce
      also have "... \<le> e;e\<^sup>T;(x\<^sup>\<star>)\<^sup>T"
        using assms(1) many_strongly_connected_iff_3 mult_isol star_conv by fastforce
      also have "... \<le> e;e\<^sup>T;((x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>)\<^sup>T"
        using 3 conv_iso mult_isol by blast
      also have "... \<le> e;e\<^sup>T;((x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star> ; s;e\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>)"
        by (simp add: star_conv comp_assoc)
      also have "... \<le> e;e\<^sup>T;(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star> + e;e\<^sup>T;(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star> ; s;e\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>"
        by (simp add: comp_assoc distrib_left)
      also have "... \<le> e;e\<^sup>T;(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star> + e;1;e\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>"
        by (metis comp_assoc join_isol mult_isol mult_isor top_greatest)
      also have "... \<le> e;e\<^sup>T;(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star> + e;e\<^sup>T;(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>"
        using assms(3) by (simp add: point_equations(1) point_is_point)
      also have "... = e;e\<^sup>T;(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>"
        by simp
      also have "... \<le> 1';(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>"
        using assms(3) is_inj_def point_def join_iso mult_isor by blast
      finally have 4: "e;s\<^sup>T \<le>(x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>"
        by simp

      have "(x \<cdot> -(e;s\<^sup>T));1;(x \<cdot> -(e;s\<^sup>T)) \<le> x;1;x"
        by (simp add: mult_isol_var)
      also have "...\<le> x\<^sup>\<star>"
        using assms(1) connected_iff4 one_strongly_connected_iff one_strongly_connected_implies_8
              path_concat_aux3_3 by blast
      also have "... \<le> (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; e;s\<^sup>T ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>"
        by (rule 3)
      also have "... \<le> (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> ; (x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star> ; (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star>"
        using 4 by (metis comp_assoc join_isol mult_isol mult_isor)
      also have "... \<le> (x \<cdot> -(e;s\<^sup>T))\<^sup>\<star> + (x \<cdot> -(e;s\<^sup>T))\<^sup>T\<^sup>\<star>"
        using 1 2 triple_star by force
      finally show ?thesis .
    qed
  qed
next
  show "start_points (x \<cdot> -(e;s\<^sup>T)) \<le> s"
  proof -
    have 1: "is_vector(-s)"
      using assms(2) by (simp add: point_def vector_compl)
    have "(x \<cdot> -(e;s\<^sup>T));1 \<cdot> -s \<le> x;1 \<cdot> -s"
      using meet_iso mult_subdistr by blast
    also have "... \<le> x\<^sup>T;1 \<cdot> -s"
      using assms(1) many_strongly_connected_implies_no_start_end_points meet_iso
            no_start_end_points_path_iff by blast
    also have "... \<le> (x\<^sup>T \<cdot> -s);1"
      using 1 by (simp add: vector_1_comm)
    also have "... \<le> (x\<^sup>T \<cdot> -(s;e\<^sup>T));1"
      by (metis 1 galois_aux inf.boundedI inf.cobounded1 inf.commute mult_isor schroeder_2
                vector_1_comm)
    also have "... = (x \<cdot> -(e;s\<^sup>T))\<^sup>T;1"
      by (simp add: conv_compl)
    finally show ?thesis
      by (simp add: galois_1 sup_commute)
  qed
next
  show "end_points (x \<cdot> -(e;s\<^sup>T)) \<le> e"
  proof -
    have 1: "is_vector(-e)"
      using assms(3) by (simp add: point_def vector_compl)
    have "(x \<cdot> -(e;s\<^sup>T))\<^sup>T;1 \<cdot> -e \<le> x\<^sup>T;1 \<cdot> -e"
      using meet_iso mult_subdistr by simp
    also have "... \<le> x;1 \<cdot> -e"
      using assms(1) many_strongly_connected_implies_no_start_end_points meet_iso
            no_start_end_points_path_iff by blast
    also have "... \<le> (x \<cdot> -e);1"
      using 1 by (simp add: vector_1_comm)
    also have "... \<le> (x \<cdot> -(e;s\<^sup>T));1"
      by (metis 1 galois_aux inf.boundedI inf.cobounded1 inf.commute mult_isor schroeder_2
                vector_1_comm)
    finally show ?thesis
      by (simp add: galois_1 sup_commute)
  qed
qed

lemma cycle_remove_edge':
  assumes "cycle x"
      and "point s"
      and "point e"
      and "s\<noteq>e"
      and "e;s\<^sup>T \<le> x"
    shows "path(x \<cdot> -(e;s\<^sup>T))"
      and "s = start_points (x \<cdot> -(e;s\<^sup>T))"
      and "e = end_points (x \<cdot> -(e;s\<^sup>T))"
proof -
  show "path (x \<cdot> - (e ; s\<^sup>T))"
    using assms(1,2,3,5) cycle_remove_edge(1) by blast
next
  show "s = start_points (x \<cdot> - (e ; s\<^sup>T))"
  proof (simp only: eq_iff; rule conjI)
    show "s \<le> start_points (x \<cdot> - (e ; s\<^sup>T))"
    proof -
      have a: "s \<le> (x \<cdot> - (e ; s\<^sup>T));1"
      proof -
        have 1: "is_vector(-e)"
          using assms(3) point_def vector_compl by blast
        from assms(2-4) have "s = s \<cdot> -e"
          using comp_assoc edge_end point_equations(1) point_equations(3) point_is_point by fastforce
        also have "... \<le> x\<^sup>T;e \<cdot> -e"
          using assms(3,5) conv_iso meet_iso point_def ss423conv by fastforce
        also have "... \<le> x;1 \<cdot> -e"
          by (metis assms(1) many_strongly_connected_implies_no_start_end_points meet_iso mult_isol
                    top_greatest)
        also have "... \<le> (x \<cdot> -e);1"
          using 1 by (simp add: vector_1_comm)
        also have "... \<le> (x \<cdot> - (e ; s\<^sup>T));1"
          by (metis assms(3) comp_anti is_vector_def meet_isor mult_isol mult_isor point_def
                    top_greatest)
        finally show ?thesis .
      qed
      have b: "s \<le> -((x \<cdot> - (e ; s\<^sup>T))\<^sup>T;1)"
      proof -
        have 1: "x;s =e"
          using assms predecessor_point' by blast
        have "s \<cdot> x\<^sup>T = s;(e\<^sup>T+-(e\<^sup>T)) \<cdot> x\<^sup>T"
          using assms(2) point_equations(1) point_is_point by fastforce
        also have "... = s;e\<^sup>T \<cdot> x\<^sup>T"
          by (metis 1 conv_contrav inf.commute inf_sup_absorb modular_1')
        also have "... \<le> e\<^sup>T"
          by (metis assms(3) inf.coboundedI1 mult_isor point_equations(4) point_is_point
                    top_greatest)
        finally have "s \<cdot> x\<^sup>T \<le> s \<cdot> e\<^sup>T"
          by simp
        also have "... \<le> s ; e\<^sup>T"
          using assms(2,3) by (simp add: point_def vector_meet_comp)
        finally have 2: "s \<cdot> x\<^sup>T \<cdot> -(s ; e\<^sup>T) = 0"
          using galois_aux2 by blast
        thus ?thesis
        proof -
          have "s ; e\<^sup>T = e\<^sup>T \<cdot> s"
            using assms(2,3) inf_commute point_def vector_meet_comp by force
          thus ?thesis
            using 2
            by (metis assms(2,3) conv_compl conv_invol conv_one conv_times galois_aux
                      inf.assoc point_def point_equations(1) point_is_point schroeder_2
                      vector_meet_comp)
        qed
      qed
      with a show ?thesis
        by simp
    qed
    show "start_points (x \<cdot> - (e ; s\<^sup>T)) \<le> s"
      using assms(1,2,3,5) cycle_remove_edge(2) by blast
  qed
next
  show "e = end_points (x \<cdot> - (e ; s\<^sup>T))"
  proof (simp only: eq_iff; rule conjI)
    show "e \<le> end_points (x \<cdot> - (e ; s\<^sup>T))"
      (* just copied and adapted the proof of the previous case (start_point) *)
    proof -
      have a: "e \<le> (x \<cdot> - (e ; s\<^sup>T))\<^sup>T;1"
      proof -
        have 1: "is_vector(-s)"
          using assms(2) point_def vector_compl by blast
        from assms(2-4) have "e = e \<cdot> -s"
          using comp_assoc edge_end point_equations(1) point_equations(3) point_is_point by fastforce
        also have "... \<le> x;s \<cdot> -s"
          using assms(2,5) meet_iso point_def ss423bij by fastforce
        also have "... \<le> x\<^sup>T;1 \<cdot> -s"
          by (metis assms(1) many_strongly_connected_implies_no_start_end_points meet_iso mult_isol
                    top_greatest)
        also have "... \<le> (x\<^sup>T \<cdot> -s);1"
          using 1 by (simp add: vector_1_comm)
        also have "... \<le> (x\<^sup>T \<cdot> - (s ; e\<^sup>T));1"
          by (metis assms(2) comp_anti is_vector_def meet_isor mult_isol mult_isor point_def
                    top_greatest)
        finally show ?thesis
          by (simp add: conv_compl)
      qed
      have b: "e \<le> -((x \<cdot> - (e ; s\<^sup>T));1)"
      proof -
        have 1: "x\<^sup>T;e =s"
          using assms predecessor_point' by (metis conv_contrav conv_invol conv_iso conv_path)
        have "e \<cdot> x = e;(s\<^sup>T+-(s\<^sup>T)) \<cdot> x"
          using assms(3) point_equations(1) point_is_point by fastforce
        also have "... = e;s\<^sup>T \<cdot> x"
          by (metis 1 conv_contrav conv_invol inf.commute inf_sup_absorb modular_1')
        also have "... \<le> s\<^sup>T"
          by (metis assms(2) inf.coboundedI1 mult_isor point_equations(4) point_is_point top_greatest)
        finally have "e \<cdot> x \<le> e \<cdot> s\<^sup>T"
          by simp
        also have "... \<le> e ; s\<^sup>T"
          using assms(2,3) by (simp add: point_def vector_meet_comp)
        finally have 2: "e \<cdot> x \<cdot> -(e ; s\<^sup>T) = 0"
          using galois_aux2 by blast
        thus ?thesis
        proof -
          have "e ; s\<^sup>T = s\<^sup>T \<cdot> e"
            using assms(2,3) inf_commute point_def vector_meet_comp by force
          thus ?thesis
            using 2
            by (metis assms(2,3) conv_one galois_aux inf.assoc point_def point_equations(1)
                      point_is_point schroeder_2 vector_meet_comp)
        qed
      qed
      with a show ?thesis
        by simp
    qed
    show "end_points (x \<cdot> - (e ; s\<^sup>T)) \<le> e"
      using assms(1,2,3,5) cycle_remove_edge(3) by blast
  qed
qed

end (* context relation_algebra_rtc_tarski *)

end
