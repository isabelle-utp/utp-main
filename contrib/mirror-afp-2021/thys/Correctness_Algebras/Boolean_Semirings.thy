(* Title:      Boolean Semirings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Boolean Semirings\<close>

theory Boolean_Semirings

imports Stone_Algebras.P_Algebras Lattice_Ordered_Semirings

begin

class complemented_distributive_lattice = bounded_distrib_lattice + uminus +
  assumes inf_complement: "x \<sqinter> (-x) = bot"
  assumes sup_complement: "x \<squnion> (-x) = top"
begin

sublocale boolean_algebra where minus = "\<lambda>x y . x \<sqinter> (-y)" and inf = inf and sup = sup and bot = bot and top = top
  apply unfold_locales
  apply (simp add: inf_complement)
  apply (simp add: sup_complement)
  by simp

end

text \<open>M0-algebra\<close>

context lattice_ordered_pre_left_semiring
begin

text \<open>Section 7\<close>

lemma vector_1:
  "vector x \<longleftrightarrow> x * top \<le> x"
  by (simp add: antisym_conv top_right_mult_increasing)

definition zero_vector :: "'a \<Rightarrow> bool" where "zero_vector x \<equiv> x \<le> x * bot"
definition one_vector :: "'a \<Rightarrow> bool" where "one_vector x \<equiv> x * bot \<le> x"

lemma zero_vector_left_zero:
  assumes "zero_vector x"
    shows "x * y = x * bot"
proof -
  have "x * y \<le> x * bot"
    by (metis assms mult_isotone top.extremum vector_mult_closed zero_vector zero_vector_def)
  thus ?thesis
    by (simp add: order.antisym mult_right_isotone)
qed

lemma zero_vector_1:
  "zero_vector x \<longleftrightarrow> (\<forall>y . x * y = x * bot)"
  by (metis top_right_mult_increasing zero_vector_def zero_vector_left_zero)

lemma zero_vector_2:
  "zero_vector x \<longleftrightarrow> (\<forall>y . x * y \<le> x * bot)"
  by (metis eq_refl order_trans top_right_mult_increasing zero_vector_def zero_vector_left_zero)

lemma zero_vector_3:
  "zero_vector x \<longleftrightarrow> x * 1 = x * bot"
  by (metis mult_sub_right_one zero_vector_def zero_vector_left_zero)

lemma zero_vector_4:
  "zero_vector x \<longleftrightarrow> x * 1 \<le> x * bot"
  using order.antisym mult_right_isotone zero_vector_3 by auto

lemma zero_vector_5:
  "zero_vector x \<longleftrightarrow> x * top = x * bot"
  by (metis top_right_mult_increasing zero_vector_def zero_vector_left_zero)

lemma zero_vector_6:
  "zero_vector x \<longleftrightarrow> x * top \<le> x * bot"
  by (meson mult_right_isotone order_trans top.extremum zero_vector_2)

lemma zero_vector_7:
  "zero_vector x \<longleftrightarrow> (\<forall>y . x * top = x * y)"
  by (metis zero_vector_1)

lemma zero_vector_8:
  "zero_vector x \<longleftrightarrow> (\<forall>y . x * top \<le> x * y)"
  by (metis zero_vector_6 zero_vector_left_zero)

lemma zero_vector_9:
  "zero_vector x \<longleftrightarrow> (\<forall>y . x * 1 = x * y)"
  by (metis zero_vector_1)

lemma zero_vector_0:
  "zero_vector x \<longleftrightarrow> (\<forall>y z . x * y = x * z)"
  by (metis zero_vector_5 zero_vector_left_zero)

text \<open>Theorem 6 / Figure 2: relations between properties\<close>

lemma co_vector_zero_vector_one_vector:
  "co_vector x \<longleftrightarrow> zero_vector x \<and> one_vector x"
  using co_vector_def one_vector_def zero_vector_def by auto

lemma up_closed_one_vector:
  "up_closed x \<Longrightarrow> one_vector x"
  by (metis bot_least mult_right_isotone up_closed_def one_vector_def)

lemma zero_vector_dense:
  "zero_vector x \<Longrightarrow> dense_rel x"
  by (metis zero_vector_0 zero_vector_def)

lemma zero_vector_sup_distributive:
  "zero_vector x \<Longrightarrow> sup_distributive x"
  by (metis sup_distributive_def sup_idem zero_vector_0)

lemma zero_vector_inf_distributive:
  "zero_vector x \<Longrightarrow> inf_distributive x"
  by (metis inf_idem inf_distributive_def zero_vector_0)

lemma up_closed_zero_vector_vector:
  "up_closed x \<Longrightarrow> zero_vector x \<Longrightarrow> vector x"
  by (metis up_closed_def zero_vector_0)

lemma zero_vector_one_vector_vector:
  "zero_vector x \<Longrightarrow> one_vector x \<Longrightarrow> vector x"
  by (metis one_vector_def vector_1 zero_vector_0)

lemma co_vector_vector:
  "co_vector x \<Longrightarrow> vector x"
  by (simp add: co_vector_zero_vector_one_vector zero_vector_one_vector_vector)

text \<open>Theorem 10 / Figure 3: closure properties\<close>

text \<open>zero-vector\<close>

lemma zero_zero_vector:
  "zero_vector bot"
  by (simp add: zero_vector_def)

lemma sup_zero_vector:
  "zero_vector x \<Longrightarrow> zero_vector y \<Longrightarrow> zero_vector (x \<squnion> y)"
  by (simp add: mult_right_dist_sup zero_vector_3)

lemma comp_zero_vector:
  "zero_vector x \<Longrightarrow> zero_vector y \<Longrightarrow> zero_vector (x * y)"
  by (metis mult_one_associative zero_vector_0)

text \<open>one-vector\<close>

lemma zero_one_vector:
  "one_vector bot"
  by (simp add: one_vector_def)

lemma one_one_vector:
  "one_vector 1"
  by (simp add: one_up_closed up_closed_one_vector)

lemma top_one_vector:
  "one_vector top"
  by (simp add: one_vector_def)

lemma sup_one_vector:
  "one_vector x \<Longrightarrow> one_vector y \<Longrightarrow> one_vector (x \<squnion> y)"
  by (simp add: mult_right_dist_sup order_trans one_vector_def)

lemma inf_one_vector:
  "one_vector x \<Longrightarrow> one_vector y \<Longrightarrow> one_vector (x \<sqinter> y)"
  by (meson order.trans inf.boundedI mult_right_sub_dist_inf_left mult_right_sub_dist_inf_right one_vector_def)

lemma comp_one_vector:
  "one_vector x \<Longrightarrow> one_vector y \<Longrightarrow> one_vector (x * y)"
  using mult_isotone mult_semi_associative order_lesseq_imp one_vector_def by blast

end

context multirelation_algebra_1
begin

text \<open>Theorem 10 / Figure 3: closure properties\<close>

text \<open>zero-vector\<close>

lemma top_zero_vector:
   "zero_vector top"
  by (simp add: mult_left_top zero_vector_def)

end

text \<open>M1-algebra\<close>

context multirelation_algebra_2
begin

text \<open>Section 7\<close>

lemma zero_vector_10:
  "zero_vector x \<longleftrightarrow> x * top = x * 1"
  by (metis mult_one_associative mult_top_associative zero_vector_7)

lemma zero_vector_11:
  "zero_vector x \<longleftrightarrow> x * top \<le> x * 1"
  using order.antisym mult_right_isotone zero_vector_10 by fastforce

text \<open>Theorem 6 / Figure 2: relations between properties\<close>

lemma vector_zero_vector:
  "vector x \<Longrightarrow> zero_vector x"
  by (simp add: zero_vector_def vector_left_annihilator)

lemma vector_up_closed_zero_vector:
  "vector x \<longleftrightarrow> up_closed x \<and> zero_vector x"
  using up_closed_zero_vector_vector vector_up_closed vector_zero_vector by blast

lemma vector_zero_vector_one_vector:
  "vector x \<longleftrightarrow> zero_vector x \<and> one_vector x"
  by (simp add: co_vector_zero_vector_one_vector vector_co_vector)

(*
lemma "(x * bot \<sqinter> y) * 1 = x * bot \<sqinter> y * 1" nitpick [expect=genuine,card=7] oops
*)

end

text \<open>M3-algebra\<close>

context up_closed_multirelation_algebra
begin

lemma up_closed:
  "up_closed x"
  by (simp add: up_closed_def)

lemma dedekind_1_left:
  "x * 1 \<sqinter> y \<le> (x \<sqinter> y * 1) * 1"
  by simp

text \<open>Theorem 10 / Figure 3: closure properties\<close>

text \<open>zero-vector\<close>

lemma zero_vector_dual:
  "zero_vector x \<longleftrightarrow> zero_vector (x\<^sup>d)"
  using up_closed_zero_vector_vector vector_dual vector_zero_vector up_closed by blast

end

text \<open>complemented M0-algebra\<close>

class lattice_ordered_pre_left_semiring_b = lattice_ordered_pre_left_semiring + complemented_distributive_lattice
begin

definition down_closed :: "'a \<Rightarrow> bool" where "down_closed x \<equiv> -x * 1 \<le> -x"

text \<open>Theorem 10 / Figure 3: closure properties\<close>

text \<open>down-closed\<close>

lemma zero_down_closed:
  "down_closed bot"
  by (simp add: down_closed_def)

lemma top_down_closed:
  "down_closed top"
  by (simp add: down_closed_def)

lemma complement_down_closed_up_closed:
  "down_closed x \<longleftrightarrow> up_closed (-x)"
  using down_closed_def order.antisym mult_sub_right_one up_closed_def by auto

lemma sup_down_closed:
  "down_closed x \<Longrightarrow> down_closed y \<Longrightarrow> down_closed (x \<squnion> y)"
  by (simp add: complement_down_closed_up_closed inf_up_closed)

lemma inf_down_closed:
  "down_closed x \<Longrightarrow> down_closed y \<Longrightarrow> down_closed (x \<sqinter> y)"
  by (simp add: complement_down_closed_up_closed sup_up_closed)

end

class multirelation_algebra_1b = multirelation_algebra_1 + complemented_distributive_lattice
begin

subclass lattice_ordered_pre_left_semiring_b ..

text \<open>Theorem 7.1\<close>

lemma complement_mult_zero_sub:
  "-(x * bot) \<le> -x * bot"
proof -
  have "top = -x * bot \<squnion> x * bot"
    by (metis compl_sup_top mult_left_top mult_right_dist_sup)
  thus ?thesis
    by (simp add: heyting.implies_order sup.commute)
qed

text \<open>Theorem 7.2\<close>

lemma transitive_zero_vector_complement:
  "transitive x \<Longrightarrow> zero_vector (-x)"
  by (meson complement_mult_zero_sub compl_mono mult_right_isotone order_trans zero_vector_def bot_least)

lemma transitive_dense_complement:
  "transitive x \<Longrightarrow> dense_rel (-x)"
  by (simp add: zero_vector_dense transitive_zero_vector_complement)

lemma transitive_sup_distributive_complement:
  "transitive x \<Longrightarrow> sup_distributive (-x)"
  by (simp add: zero_vector_sup_distributive transitive_zero_vector_complement)

lemma transitive_inf_distributive_complement:
  "transitive x \<Longrightarrow> inf_distributive (-x)"
  by (simp add: zero_vector_inf_distributive transitive_zero_vector_complement)

lemma up_closed_zero_vector_complement:
  "up_closed x \<Longrightarrow> zero_vector (-x)"
  by (meson complement_mult_zero_sub compl_le_swap2 one_vector_def order_trans up_closed_one_vector zero_vector_def)

lemma up_closed_dense_complement:
  "up_closed x \<Longrightarrow> dense_rel (-x)"
  by (simp add: zero_vector_dense up_closed_zero_vector_complement)

lemma up_closed_sup_distributive_complement:
  "up_closed x \<Longrightarrow> sup_distributive (-x)"
  by (simp add: zero_vector_sup_distributive up_closed_zero_vector_complement)

lemma up_closed_inf_distributive_complement:
  "up_closed x \<Longrightarrow> inf_distributive (-x)"
  by (simp add: zero_vector_inf_distributive up_closed_zero_vector_complement)

text \<open>Theorem 10 / Figure 3: closure properties\<close>

text \<open>closure under complement\<close>

lemma co_total_total:
  "co_total x \<Longrightarrow> total (-x)"
  by (metis complement_mult_zero_sub co_total_def compl_bot_eq mult_left_sub_dist_sup_right sup_bot_right top_le)

lemma complement_one_vector_zero_vector:
  "one_vector x \<Longrightarrow> zero_vector (-x)"
  using compl_mono complement_mult_zero_sub one_vector_def order_trans zero_vector_def by blast

text \<open>Theorem 6 / Figure 2: relations between properties\<close>

lemma down_closed_zero_vector:
  "down_closed x \<Longrightarrow> zero_vector x"
  using complement_down_closed_up_closed up_closed_zero_vector_complement by force

lemma down_closed_one_vector_vector:
  "down_closed x \<Longrightarrow> one_vector x \<Longrightarrow> vector x"
  by (simp add: down_closed_zero_vector zero_vector_one_vector_vector)

(*
lemma complement_vector: "vector x \<longrightarrow> vector (-x)" nitpick [expect=genuine,card=8] oops
*)

end

class multirelation_algebra_1c = multirelation_algebra_1b +
  assumes dedekind_top_left: "x * top \<sqinter> y \<le> (x \<sqinter> y * top) * top"
  assumes comp_zero_inf: "(x * bot \<sqinter> y) * bot \<le> (x \<sqinter> y) * bot"
begin

text \<open>Theorem 7.3\<close>

lemma schroeder_top_sub:
  "-(x * top) * top \<le> -x"
proof -
  have "-(x * top) * top \<sqinter> x \<le> bot"
    by (metis dedekind_top_left p_inf zero_vector)
  thus ?thesis
    by (simp add: shunting_1)
qed

text \<open>Theorem 7.4\<close>

lemma schroeder_top:
  "x * top \<le> y \<longleftrightarrow> -y * top \<le> -x"
  apply (rule iffI)
  using compl_mono inf.order_trans mult_left_isotone schroeder_top_sub apply blast
  by (metis compl_mono double_compl mult_left_isotone order_trans schroeder_top_sub)

text \<open>Theorem 7.5\<close>

lemma schroeder_top_eq:
  "-(x * top) * top = -(x * top)"
  using vector_1 vector_mult_closed vector_top_closed schroeder_top by auto

lemma schroeder_one_eq:
  "-(x * top) * 1 = -(x * top)"
  by (metis top_mult_right_one schroeder_top_eq)

text \<open>Theorem 7.6\<close>

lemma vector_inf_comp:
  "x * top \<sqinter> y * z = (x * top \<sqinter> y) * z"
proof (rule order.antisym)
  have "x * top \<sqinter> y * z = x * top \<sqinter> ((x * top \<sqinter> y) \<squnion> (-(x * top) \<sqinter> y)) * z"
    by (simp add: inf_commute)
  also have "... = x * top \<sqinter> ((x * top \<sqinter> y) * z \<squnion> (-(x * top) \<sqinter> y) * z)"
    by (simp add: inf_sup_distrib2 mult_right_dist_sup)
  also have "... = (x * top \<sqinter> (x * top \<sqinter> y) * z) \<squnion> (x * top \<sqinter> (-(x * top) \<sqinter> y) * z)"
    by (simp add: inf_sup_distrib1)
  also have "... \<le> (x * top \<sqinter> y) * z \<squnion> (x * top \<sqinter> (-(x * top) \<sqinter> y) * z)"
    by (simp add: le_infI2)
  also have "... \<le> (x * top \<sqinter> y) * z \<squnion> (x * top \<sqinter> -(x * top) * z)"
    by (metis inf.sup_left_isotone inf_commute mult_right_sub_dist_inf_left sup_right_isotone)
  also have "... \<le> (x * top \<sqinter> y) * z \<squnion> (x * top \<sqinter> -(x * top) * top)"
    using inf.sup_right_isotone mult_right_isotone sup_right_isotone by auto
  also have "... = (x * top \<sqinter> y) * z"
    by (simp add: schroeder_top_eq)
  finally show "x * top \<sqinter> y * z \<le> (x * top \<sqinter> y) * z"
    .
next
  show "(x * top \<sqinter> y) * z \<le> x * top \<sqinter> y * z"
    by (metis inf.bounded_iff mult_left_top mult_right_sub_dist_inf_left mult_right_sub_dist_inf_right mult_semi_associative order_lesseq_imp)
qed

(*
lemma dedekind_top_left:
  "x * top \<sqinter> y \<le> (x \<sqinter> y * top) * top"
  by (metis inf.commute top_right_mult_increasing vector_inf_comp)
*)

text \<open>Theorem 7.7\<close>

lemma vector_zero_inf_comp:
  "(x * bot \<sqinter> y) * z = x * bot \<sqinter> y * z"
  by (metis vector_inf_comp vector_mult_closed zero_vector)

lemma vector_zero_inf_comp_2:
  "(x * bot \<sqinter> y) * z = (x * bot \<sqinter> y * 1) * z"
  by (simp add: vector_zero_inf_comp)

text \<open>Theorem 7.8\<close>

lemma comp_zero_inf_2:
  "x * bot \<sqinter> y * bot = (x \<sqinter> y) * bot"
  using order.antisym mult_right_sub_dist_inf comp_zero_inf vector_zero_inf_comp by auto

lemma comp_zero_inf_3:
  "x * bot \<sqinter> y * bot = (x * bot \<sqinter> y) * bot"
  by (simp add: vector_zero_inf_comp)

lemma comp_zero_inf_4:
  "x * bot \<sqinter> y * bot = (x * bot \<sqinter> y * bot) * bot"
  by (metis comp_zero_inf_2 inf.commute vector_zero_inf_comp)

lemma comp_zero_inf_5:
  "x * bot \<sqinter> y * bot = (x * 1 \<sqinter> y * 1) * bot"
  by (metis comp_zero_inf_2 mult_one_associative)

lemma comp_zero_inf_6:
  "x * bot \<sqinter> y * bot = (x * 1 \<sqinter> y * bot) * bot"
  using inf.sup_monoid.add_commute vector_zero_inf_comp by fastforce

lemma comp_zero_inf_7:
  "x * bot \<sqinter> y * bot = (x * 1 \<sqinter> y) * bot"
  by (metis comp_zero_inf_2 mult_one_associative)

text \<open>Theorem 10 / Figure 3: closure properties\<close>

text \<open>zero-vector\<close>

lemma inf_zero_vector:
  "zero_vector x \<Longrightarrow> zero_vector y \<Longrightarrow> zero_vector (x \<sqinter> y)"
  by (metis comp_zero_inf_2 inf.sup_mono zero_vector_def)

text \<open>down-closed\<close>

lemma comp_down_closed:
  "down_closed x \<Longrightarrow> down_closed y \<Longrightarrow> down_closed (x * y)"
  by (metis complement_down_closed_up_closed down_closed_zero_vector up_closed_def zero_vector_0 schroeder_one_eq)

text \<open>closure under complement\<close>

lemma complement_vector:
  "vector x \<longleftrightarrow> vector (-x)"
  using vector_1 schroeder_top by blast

lemma complement_zero_vector_one_vector:
  "zero_vector x \<Longrightarrow> one_vector (-x)"
  by (metis comp_zero_inf_2 order.antisym complement_mult_zero_sub double_compl inf.sup_monoid.add_commute mult_left_zero one_vector_def order.refl pseudo_complement top_right_mult_increasing zero_vector_0)

lemma complement_zero_vector_one_vector_iff:
  "zero_vector x \<longleftrightarrow> one_vector (-x)"
  using complement_zero_vector_one_vector complement_one_vector_zero_vector by force

lemma complement_one_vector_zero_vector_iff:
  "one_vector x \<longleftrightarrow> zero_vector (-x)"
  using complement_zero_vector_one_vector complement_one_vector_zero_vector by force

text \<open>Theorem 6 / Figure 2: relations between properties\<close>

lemma vector_down_closed:
  "vector x \<Longrightarrow> down_closed x"
  using complement_vector complement_down_closed_up_closed vector_up_closed by blast

lemma co_vector_down_closed:
  "co_vector x \<Longrightarrow> down_closed x"
  by (simp add: co_vector_vector vector_down_closed)

lemma vector_down_closed_one_vector:
  "vector x \<longleftrightarrow> down_closed x \<and> one_vector x"
  using down_closed_one_vector_vector up_closed_one_vector vector_up_closed vector_down_closed by blast

lemma vector_up_closed_down_closed:
  "vector x \<longleftrightarrow> up_closed x \<and> down_closed x"
  using down_closed_zero_vector up_closed_zero_vector_vector vector_up_closed vector_down_closed by blast

text \<open>Section 7\<close>

lemma vector_b1:
  "vector x \<longleftrightarrow> -x * top = -x"
  using complement_vector by auto

lemma vector_b2:
  "vector x \<longleftrightarrow> -x * bot = -x"
  by (metis down_closed_zero_vector vector_mult_closed zero_vector zero_vector_left_zero vector_b1 vector_down_closed)

lemma covector_b1:
  "co_vector x \<longleftrightarrow> -x * top = -x"
  using co_vector_def co_vector_vector vector_b1 vector_b2 by force

lemma covector_b2:
  "co_vector x \<longleftrightarrow> -x * bot = -x"
  using covector_b1 vector_b1 vector_b2 by auto

lemma vector_co_vector_iff:
  "vector x \<longleftrightarrow> co_vector x"
  by (simp add: covector_b2 vector_b2)

lemma zero_vector_b:
  "zero_vector x \<longleftrightarrow> -x * bot \<le> -x"
  by (simp add: complement_zero_vector_one_vector_iff one_vector_def)

lemma one_vector_b1:
  "one_vector x \<longleftrightarrow> -x \<le> -x * bot"
  by (simp add: complement_one_vector_zero_vector_iff zero_vector_def)

lemma one_vector_b0:
  "one_vector x \<longleftrightarrow> (\<forall>y z . -x * y = -x * z)"
  by (simp add: complement_one_vector_zero_vector_iff zero_vector_0)

(*
lemma schroeder_one: "x * -1 \<le> y \<longleftrightarrow> -y * -1 \<le> -x" nitpick [expect=genuine,card=8] oops
*)

end

class multirelation_algebra_2b = multirelation_algebra_2 + complemented_distributive_lattice
begin

subclass multirelation_algebra_1b ..

(*
lemma "-x * bot \<le> -(x * bot)" nitpick [expect=genuine,card=8] oops
*)

end

text \<open>complemented M1-algebra\<close>

class multirelation_algebra_2c = multirelation_algebra_2b + multirelation_algebra_1c

class multirelation_algebra_3b = multirelation_algebra_3 + complemented_distributive_lattice
begin

subclass lattice_ordered_pre_left_semiring_b ..

lemma dual_complement_commute:
  "-(x\<^sup>d) = (-x)\<^sup>d"
  by (metis compl_unique dual_dist_sup dual_dist_inf dual_top dual_zero inf_complement sup_compl_top)

end

text \<open>complemented M2-algebra\<close>

class multirelation_algebra_5b = multirelation_algebra_5 + complemented_distributive_lattice
begin

subclass multirelation_algebra_2b ..

subclass multirelation_algebra_3b ..

lemma dual_down_closed:
  "down_closed x \<longleftrightarrow> down_closed (x\<^sup>d)"
  using complement_down_closed_up_closed dual_complement_commute dual_up_closed by auto

end

class multirelation_algebra_5c = multirelation_algebra_5b + multirelation_algebra_1c
begin

lemma complement_mult_zero_below:
  "-x * bot \<le> -(x * bot)"
  by (simp add: comp_zero_inf_2 shunting_1)

(*
lemma "x * 1 \<sqinter> y * 1 \<le> (x \<sqinter> y) * 1" nitpick [expect=genuine,card=4] oops
lemma "x * 1 \<sqinter> (y * 1) \<le> (x * 1 \<sqinter> y) * 1" nitpick [expect=genuine,card=4] oops
*)

end

class up_closed_multirelation_algebra_b = up_closed_multirelation_algebra + complemented_distributive_lattice
begin

subclass multirelation_algebra_5c
  apply unfold_locales
  apply (metis inf.sup_monoid.add_commute top_right_mult_increasing vector_inf_comp)
  using mult_right_dist_inf vector_zero_inf_comp by auto

lemma complement_zero_vector:
  "zero_vector x \<longleftrightarrow> zero_vector (-x)"
  by (simp add: zero_right_mult_decreasing zero_vector_b)

lemma down_closed:
  "down_closed x"
  by (simp add: down_closed_def)

lemma vector:
  "vector x"
  by (simp add: down_closed up_closed_def vector_up_closed_down_closed)

end

end

