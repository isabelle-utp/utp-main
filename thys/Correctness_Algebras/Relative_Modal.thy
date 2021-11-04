(* Title:      Relative Modal Operators
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Relative Modal Operators\<close>

theory Relative_Modal

imports Relative_Domain

begin

class relative_diamond_semiring = relative_domain_semiring + diamond +
  assumes diamond_def: "|x>y = d(x * y)"
begin

lemma diamond_x_1:
  "|x>1 = d(x)"
  by (simp add: diamond_def)

lemma diamond_x_d:
  "|x>d(y) = d(x * y)"
  using d_mult_d diamond_def by auto

lemma diamond_x_und:
  "|x>d(y) = |x>y"
  using diamond_x_d diamond_def by auto

lemma diamond_d_closed:
  "|x>y = d( |x>y)"
  by (simp add: d_involutive diamond_def)

text \<open>Theorem 46.11\<close>

lemma diamond_bot_y:
  "|bot>y = bot"
  by (simp add: d_zero diamond_def)

lemma diamond_1_y:
  "|1>y = d(y)"
  by (simp add: diamond_def)

text \<open>Theorem 46.12\<close>

lemma diamond_1_d:
  "|1>d(y) = d(y)"
  by (simp add: diamond_1_y diamond_x_und)

text \<open>Theorem 46.10\<close>

lemma diamond_d_y:
  "|d(x)>y = d(x) * d(y)"
  by (simp add: d_export diamond_def)

text \<open>Theorem 46.11\<close>

lemma diamond_d_bot:
  "|d(x)>bot = bot"
  by (metis diamond_bot_y diamond_d_y d_commutative d_zero)

text \<open>Theorem 46.12\<close>

lemma diamond_d_1:
  "|d(x)>1 = d(x)"
  by (simp add: diamond_x_1 d_involutive)

lemma diamond_d_d:
  "|d(x)>d(y) = d(x) * d(y)"
  by (simp add: diamond_d_y diamond_x_und)

text \<open>Theorem 46.12\<close>

lemma diamond_d_d_same:
  "|d(x)>d(x) = d(x)"
  by (simp add: diamond_d_d d_idempotent)

text \<open>Theorem 46.2\<close>

lemma diamond_left_dist_sup:
  "|x \<squnion> y>z = |x>z \<squnion> |y>z"
  by (simp add: d_dist_sup diamond_def mult_right_dist_sup)

text \<open>Theorem 46.3\<close>

lemma diamond_right_sub_dist_sup:
  "|x>y \<squnion> |x>z \<le> |x>(y \<squnion> z)"
  by (metis d_dist_sup diamond_def le_iff_sup mult_left_sub_dist_sup)

text \<open>Theorem 46.4\<close>

lemma diamond_associative:
  "|x * y>z = |x>(y * z)"
  by (simp add: diamond_def mult_assoc)

text \<open>Theorem 46.4\<close>

lemma diamond_left_mult:
  "|x * y>z = |x>|y>z"
  using diamond_x_und diamond_def mult_assoc by auto

lemma diamond_right_mult:
  "|x>(y * z) = |x>|y>z"
  using diamond_associative diamond_left_mult by auto

text \<open>Theorem 46.6\<close>

lemma diamond_d_export:
  "|d(x) * y>z = d(x) * |y>z"
  using diamond_d_y diamond_def mult_assoc by auto

lemma diamond_diamond_export:
  "||x>y>z = |x>y * |z>1"
  using diamond_d_y diamond_def by force

text \<open>Theorem 46.1\<close>

lemma diamond_left_isotone:
  "x \<le> y \<Longrightarrow> |x>z \<le> |y>z"
  by (metis diamond_left_dist_sup le_iff_sup)

text \<open>Theorem 46.1\<close>

lemma diamond_right_isotone:
  "y \<le> z \<Longrightarrow> |x>y \<le> |x>z"
  by (metis diamond_right_sub_dist_sup le_iff_sup le_sup_iff)

lemma diamond_isotone:
  "w \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> |w>x \<le> |y>z"
  by (meson diamond_left_isotone diamond_right_isotone order_trans)

lemma diamond_left_upper_bound:
  "|x>y \<le> |x \<squnion> z>y"
  by (simp add: diamond_left_isotone)

lemma diamond_right_upper_bound:
  "|x>y \<le> |x>(y \<squnion> z)"
  by (simp add: diamond_right_isotone)

lemma diamond_lower_bound_right:
  "|x>(d(y) * d(z)) \<le> |x>d(y)"
  by (simp add: diamond_right_isotone d_mult_left_lower_bound)

lemma diamond_lower_bound_left:
  "|x>(d(y) * d(z)) \<le> |x>d(z)"
  using diamond_lower_bound_right d_commutative by force

text \<open>Theorem 46.5\<close>

lemma diamond_right_sub_dist_mult:
  "|x>(d(y) * d(z)) \<le> |x>d(y) * |x>d(z)"
  using diamond_lower_bound_left diamond_lower_bound_right d_mult_greatest_lower_bound diamond_def by force

text \<open>Theorem 46.13\<close>

lemma diamond_demodalisation_1:
  "d(x) * |y>z \<le> Z \<longleftrightarrow> d(x) * y * d(z) \<le> Z"
  by (metis d_weak_locality diamond_def mult_assoc)

text \<open>Theorem 46.14\<close>

lemma diamond_demodalisation_3:
  "|x>y \<le> d(z) \<longleftrightarrow> x * d(y) \<le> d(z) * x \<squnion> Z"
  apply (rule iffI)
  apply (smt (verit) sup_commute sup_right_isotone d_below_one d_restrict diamond_def diamond_x_und mult_left_isotone mult_right_isotone mult_1_right order_trans)
  by (smt sup_commute sup_bot_left d_Z d_commutative d_dist_sup d_involutive d_mult_sub d_plus_left_upper_bound diamond_d_y diamond_def diamond_x_und le_iff_sup order_trans)

text \<open>Theorem 46.6\<close>

lemma diamond_d_export_2:
  "|d(x) * y>z = d(x) * |d(x) * y>z"
  by (metis diamond_d_export diamond_left_mult d_idempotent)

text \<open>Theorem 46.7\<close>

lemma diamond_d_promote:
  "|x * d(y)>z = |x * d(y)>(d(y) * z)"
  by (metis d_idempotent diamond_def mult_assoc)

text \<open>Theorem 46.8\<close>

lemma diamond_d_import_iff:
  "d(x) \<le> |y>z \<longleftrightarrow> d(x) \<le> |d(x) * y>z"
  by (metis diamond_d_export diamond_d_y d_order diamond_def order.eq_iff)

text \<open>Theorem 46.9\<close>

lemma diamond_d_import_iff_2:
  "d(x) * d(y) \<le> |z>w \<longleftrightarrow> d(x) * d(y) \<le> |d(y) * z>w"
  apply (rule iffI)
  apply (metis diamond_associative d_export d_mult_greatest_lower_bound diamond_def order.refl)
  by (metis diamond_d_y d_mult_greatest_lower_bound diamond_def mult_assoc)

end

class relative_box_semiring = relative_diamond_semiring + relative_antidomain_semiring + box +
  assumes box_def: "|x]y = a(x * a(y))"
begin

text \<open>Theorem 47.1\<close>

lemma box_diamond:
  "|x]y = a( |x>a(y))"
  by (simp add: box_def d_a_closed diamond_def)

text \<open>Theorem 47.2\<close>

lemma diamond_box:
  "|x>y = a( |x]a(y))"
  using box_def d_def d_mult_d diamond_def by auto

lemma box_x_bot:
  "|x]bot = a(x)"
  by (metis box_def mult_1_right one_def)

lemma box_x_1:
  "|x]1 = a(x * bot)"
  by (simp add: box_def)

lemma box_x_d:
  "|x]d(y) = a(x * a(y))"
  by (simp add: box_def d_a_closed)

lemma box_x_und:
  "|x]d(y) = |x]y"
  by (simp add: box_diamond d_a_closed)

lemma box_x_a:
  "|x]a(y) = a(x * y)"
  using a_mult_d box_def by auto

text \<open>Theorem 47.15\<close>

lemma box_bot_y:
  "|bot]y = 1"
  using box_def by auto

lemma box_1_y:
  "|1]y = d(y)"
  by (simp add: box_def d_def)

text \<open>Theorem 47.16\<close>

lemma box_1_d:
  "|1]d(y) = d(y)"
  by (simp add: box_1_y box_x_und)

lemma box_1_a:
  "|1]a(y) = a(y)"
  by (simp add: box_x_a)

lemma box_d_y:
  "|d(x)]y = a(x) \<squnion> d(y)"
  using a_export_a box_def d_def by auto

lemma box_a_y:
  "|a(x)]y = d(x) \<squnion> d(y)"
  by (simp add: a_mult_deMorgan_1 box_def)

text \<open>Theorem 47.14\<close>

lemma box_d_bot:
  "|d(x)]bot = a(x)"
  by (simp add: box_x_bot d_a_closed)

lemma box_a_bot:
  "|a(x)]bot = d(x)"
  by (simp add: box_x_bot d_def)

text \<open>Theorem 47.15\<close>

lemma box_d_1:
  "|d(x)]1 = 1"
  by (simp add: box_d_y d_one_one)

lemma box_a_1:
  "|a(x)]1 = 1"
  by (simp add: box_x_1)

text \<open>Theorem 47.13\<close>

lemma box_d_d:
  "|d(x)]d(y) = a(x) \<squnion> d(y)"
  by (simp add: box_d_y box_x_und)

lemma box_a_d:
  "|a(x)]d(y) = d(x) \<squnion> d(y)"
  by (simp add: box_a_y box_x_und)

lemma box_d_a:
  "|d(x)]a(y) = a(x) \<squnion> a(y)"
  by (simp add: box_x_a a_export_d)

lemma box_a_a:
  "|a(x)]a(y) = d(x) \<squnion> a(y)"
  by (simp add: box_a_y a_d_closed)

text \<open>Theorem 47.15\<close>

lemma box_d_d_same:
  "|d(x)]d(x) = 1"
  using box_x_d d_complement_zero by auto

lemma box_a_a_same:
  "|a(x)]a(x) = 1"
  by (simp add: box_def)

text \<open>Theorem 47.16\<close>

lemma box_d_below_box:
  "d(x) \<le> |d(y)]d(x)"
  by (simp add: box_d_d)

lemma box_d_closed:
  "|x]y = d( |x]y)"
  by (simp add: a_d_closed box_def)

lemma box_deMorgan_1:
  "a( |x]y) = |x>a(y)"
  by (simp add: diamond_box box_def)

lemma box_deMorgan_2:
  "a( |x>y) = |x]a(y)"
  using box_x_a d_a_closed diamond_def by auto

text \<open>Theorem 47.5\<close>

lemma box_left_dist_sup:
  "|x \<squnion> y]z = |x]z * |y]z"
  by (simp add: a_dist_sup box_def mult_right_dist_sup)

lemma box_right_dist_sup:
  "|x](y \<squnion> z) = a(x * a(y) * a(z))"
  by (simp add: a_dist_sup box_def mult_assoc)

lemma box_associative:
  "|x * y]z = a(x * y * a(z))"
  by (simp add: box_def)

text \<open>Theorem 47.6\<close>

lemma box_left_mult:
  "|x * y]z = |x]|y]z"
  using box_x_a box_def mult_assoc by force

lemma box_right_mult:
  "|x](y * z) = a(x * a(y * z))"
  by (simp add: box_def)

text \<open>Theorem 47.7\<close>

lemma box_right_submult_d_d:
  "|x](d(y) * d(z)) \<le> |x]d(y) * |x]d(z)"
  by (smt a_antitone a_dist_sup a_export_d box_diamond d_a_closed diamond_def mult_left_sub_dist_sup)

lemma box_right_submult_a_d:
  "|x](a(y) * d(z)) \<le> |x]a(y) * |x]d(z)"
  by (metis box_right_submult_d_d a_d_closed)

lemma box_right_submult_d_a:
  "|x](d(y) * a(z)) \<le> |x]d(y) * |x]a(z)"
  using box_right_submult_a_d box_x_a d_def tests_dual.sub_commutative by auto

lemma box_right_submult_a_a:
  "|x](a(y) * a(z)) \<le> |x]a(y) * |x]a(z)"
  by (metis box_right_submult_d_d a_d_closed)

text \<open>Theorem 47.8\<close>

lemma box_d_export:
  "|d(x) * y]z = a(x) \<squnion> |y]z"
  by (simp add: a_export_d box_def mult_assoc)

lemma box_a_export:
  "|a(x) * y]z = d(x) \<squnion> |y]z"
  using box_a_y box_d_closed box_left_mult by auto

text \<open>Theorem 47.4\<close>

lemma box_left_antitone:
  "y \<le> x \<Longrightarrow> |x]z \<le> |y]z"
  by (metis a_antitone box_def mult_left_isotone)

text \<open>Theorem 47.3\<close>

lemma box_right_isotone:
  "y \<le> z \<Longrightarrow> |x]y \<le> |x]z"
  by (metis a_antitone box_def mult_right_isotone)

lemma box_antitone_isotone:
  "y \<le> w \<Longrightarrow> x \<le> z \<Longrightarrow> |w]x \<le> |y]z"
  by (meson box_left_antitone box_right_isotone order_trans)

lemma diamond_1_a:
  "|1>a(y) = a(y)"
  by (simp add: d_def diamond_1_y)

lemma diamond_a_y:
  "|a(x)>y = a(x) * d(y)"
  by (metis a_d_closed diamond_d_y)

lemma diamond_a_bot:
  "|a(x)>bot = bot"
  by (simp add: diamond_a_y d_zero)

lemma diamond_a_1:
  "|a(x)>1 = a(x)"
  by (simp add: d_def diamond_x_1)

lemma diamond_a_d:
  "|a(x)>d(y) = a(x) * d(y)"
  by (simp add: diamond_a_y diamond_x_und)

lemma diamond_d_a:
  "|d(x)>a(y) = d(x) * a(y)"
  by (simp add: a_d_closed diamond_d_y)

lemma diamond_a_a:
  "|a(x)>a(y) = a(x) * a(y)"
  by (simp add: a_mult_closed diamond_def)

lemma diamond_a_a_same:
  "|a(x)>a(x) = a(x)"
  by (simp add: diamond_a_a)

lemma diamond_a_export:
  "|a(x) * y>z = a(x) * |y>z"
  using diamond_a_y diamond_associative diamond_def by auto

lemma a_box_a_a:
  "a(p) * |a(p)]a(q) = a(p) * a(q)"
  using box_a_a box_a_bot box_x_bot tests_dual.sup_complement_intro by auto

lemma box_left_lower_bound:
  "|x \<squnion> y]z \<le> |x]z"
  by (simp add: box_left_antitone)

lemma box_right_upper_bound:
  "|x]y \<le> |x](y \<squnion> z)"
  by (simp add: box_right_isotone)

lemma box_lower_bound_right:
  "|x](d(y) * d(z)) \<le> |x]d(y)"
  by (simp add: box_right_isotone d_mult_left_lower_bound)

lemma box_lower_bound_left:
  "|x](d(y) * d(z)) \<le> |x]d(z)"
  by (simp add: box_right_isotone d_restrict_iff_1)

text \<open>Theorem 47.9\<close>

lemma box_d_import:
  "d(x) * |y]z = d(x) * |d(x) * y]z"
  using a_box_a_a box_left_mult box_def d_def by force

text \<open>Theorem 47.10\<close>

lemma box_d_promote:
  "|x * d(y)]z = |x * d(y)](d(y) * z)"
  using a_box_a_a box_x_a box_def d_def mult_assoc by auto

text \<open>Theorem 47.11\<close>

lemma box_d_import_iff:
  "d(x) \<le> |y]z \<longleftrightarrow> d(x) \<le> |d(x) * y]z"
  using box_d_export box_def d_def tests_dual.shunting by auto

text \<open>Theorem 47.12\<close>

lemma box_d_import_iff_2:
  "d(x) * d(y) \<le> |z]w \<longleftrightarrow> d(x) * d(y) \<le> |d(y) * z]w"
  apply (rule iffI)
  using box_d_export le_supI2 apply simp
  by (metis box_d_import d_commutative d_restrict_iff_1)

text \<open>Theorem 47.20\<close>

lemma box_demodalisation_2:
  "-p \<le> |y](-q) \<longleftrightarrow> -p * y * --q \<le> Z"
  by (simp add: a_greatest_left_absorber box_def mult_assoc)

lemma box_right_sub_dist_sup:
  "|x]d(y) \<squnion> |x]d(z) \<le> |x](d(y) \<squnion> d(z))"
  by (simp add: box_right_isotone)

lemma box_diff_var:
  "|x](d(y) \<squnion> a(z)) * |x]d(z) \<le> |x]d(z)"
  by (simp add: box_right_dist_sup box_x_d tests_dual.upper_bound_right)

text \<open>Theorem 47.19\<close>

lemma diamond_demodalisation_2:
  "|x>y \<le> d(z) \<longleftrightarrow> a(z) * x * d(y) \<le> Z"
  using a_antitone a_greatest_left_absorber a_mult_d d_def diamond_def mult_assoc by fastforce

text \<open>Theorem 47.17\<close>

lemma box_below_Z:
  "( |x]y) * x * a(y) \<le> Z"
  by (simp add: a_restrict box_def mult_assoc)

text \<open>Theorem 47.18\<close>

lemma box_partial_correctness:
  "|x]1 = 1 \<longleftrightarrow> x * bot \<le> Z"
  by (simp add: box_x_1 a_strict)

lemma diamond_split:
  "|x>y = d(z) * |x>y \<squnion> a(z) * |x>y"
  by (metis d_def diamond_def sup_monoid.add_commute tests_dual.sba_dual.sup_cases tests_dual.sub_commutative)

lemma box_import_shunting:
  "-p * -q \<le> |x](-r) \<longleftrightarrow> -q \<le> |-p * x](-r)"
  by (smt box_demodalisation_2 mult_assoc sub_comm sub_mult_closed)

(*
lemma box_dist_mult: "|x](d(y) * d(z)) = |x](d(y)) * |x](d(z))" nitpick [expect=genuine,card=6] oops
lemma box_demodalisation_3: "d(x) \<le> |y]d(z) \<longrightarrow> d(x) * y \<le> y * d(z) \<squnion> Z" nitpick [expect=genuine,card=6] oops
lemma fbox_diff: "|x](d(y) \<squnion> a(z)) \<le> |x]y \<squnion> a( |x]z)" nitpick [expect=genuine,card=6] oops
lemma diamond_diff: "|x>y * a( |x>z) \<le> |x>(d(y) * a(z))" nitpick [expect=genuine,card=6] oops
lemma diamond_diff_var: "|x>d(y) \<le> |x>(d(y) * a(z)) \<squnion> |x>d(z)" nitpick [expect=genuine,card=6] oops
*)

end

class relative_left_zero_diamond_semiring = relative_diamond_semiring + relative_domain_semiring + idempotent_left_zero_semiring
begin

lemma diamond_right_dist_sup:
  "|x>(y \<squnion> z) = |x>y \<squnion> |x>z"
  by (simp add: d_dist_sup diamond_def mult_left_dist_sup)

end

class relative_left_zero_box_semiring = relative_box_semiring + relative_left_zero_antidomain_semiring
begin

subclass relative_left_zero_diamond_semiring ..

lemma box_right_mult_d_d:
  "|x](d(y) * d(z)) = |x]d(y) * |x]d(z)"
  using a_dist_sup box_d_a box_def d_def mult_left_dist_sup by auto

lemma box_right_mult_a_d:
  "|x](a(y) * d(z)) = |x]a(y) * |x]d(z)"
  by (metis box_right_mult_d_d a_d_closed)

lemma box_right_mult_d_a:
  "|x](d(y) * a(z)) = |x]d(y) * |x]a(z)"
  using box_right_mult_a_d box_def box_x_a d_def by auto

lemma box_right_mult_a_a:
  "|x](a(y) * a(z)) = |x]a(y) * |x]a(z)"
  using a_dist_sup box_def mult_left_dist_sup tests_dual.sub_sup_demorgan by force

lemma box_demodalisation_3:
  assumes "d(x) \<le> |y]d(z)"
    shows "d(x) * y \<le> y * d(z) \<squnion> Z"
proof -
  have "d(x) * y * a(z) \<le> Z"
    using assms a_greatest_left_absorber box_x_d d_def mult_assoc by auto
  thus ?thesis
    by (simp add: a_a_below case_split_right_sup d_def sup_commute mult_assoc)
qed

lemma fbox_diff:
  "|x](d(y) \<squnion> a(z)) \<le> |x]y \<squnion> a( |x]z)"
  by (smt (z3) a_compl_intro a_dist_sup a_mult_d a_plus_left_lower_bound sup_commute box_def d_def mult_left_dist_sup tests_dual.sba_dual.shunting)

lemma diamond_diff_var:
  "|x>d(y) \<le> |x>(d(y) * a(z)) \<squnion> |x>d(z)"
  by (metis d_cancellation_1 diamond_right_dist_sup diamond_right_isotone sup_commute)

lemma diamond_diff:
  "|x>y * a( |x>z) \<le> |x>(d(y) * a(z))"
  by (metis d_a_shunting d_involutive diamond_def diamond_diff_var diamond_x_und)

end

end

