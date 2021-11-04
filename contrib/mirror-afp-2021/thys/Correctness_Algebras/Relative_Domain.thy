(* Title:      Relative Domain
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Relative Domain\<close>

theory Relative_Domain

imports Tests

begin

class Z =
  fixes Z :: "'a"

class relative_domain_semiring = idempotent_left_semiring + dom + Z +
  assumes d_restrict : "x \<le> d(x) * x \<squnion> Z"
  assumes d_mult_d   : "d(x * y) = d(x * d(y))"
  assumes d_below_one: "d(x) \<le> 1"
  assumes d_Z        : "d(Z) = bot"
  assumes d_dist_sup : "d(x \<squnion> y) = d(x) \<squnion> d(y)"
  assumes d_export   : "d(d(x) * y) = d(x) * d(y)"
begin

lemma d_plus_one: 
  "d(x) \<squnion> 1 = 1"
  by (simp add: d_below_one sup_absorb2)

text \<open>Theorem 44.2\<close>

lemma d_zero:
  "d(bot) = bot"
  by (metis d_Z d_export mult_left_zero)

text \<open>Theorem 44.3\<close>

lemma d_involutive:
  "d(d(x)) = d(x)"
  by (metis d_mult_d mult_left_one)

lemma d_fixpoint:
  "(\<exists>y . x = d(y)) \<longleftrightarrow> x = d(x)"
  using d_involutive by auto

lemma d_type:
  "\<forall>P . (\<forall>x . x = d(x) \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x . P(d(x)))"
  by (metis d_involutive)

text \<open>Theorem 44.4\<close>

lemma d_mult_sub:
  "d(x * y) \<le> d(x)"
  by (smt (verit, ccfv_threshold) d_plus_one d_dist_sup d_mult_d le_iff_sup mult.right_neutral mult_left_sub_dist_sup_right sup_commute)

lemma d_sub_one:
  "x \<le> 1 \<Longrightarrow> x \<le> d(x) \<squnion> Z"
  by (metis sup_left_isotone d_restrict mult_right_isotone mult_1_right order_trans)

lemma d_one:
  "d(1) \<squnion> Z = 1 \<squnion> Z"
  by (meson d_sub_one d_below_one order.trans preorder_one_closed sup.cobounded1 sup_same_context)

text \<open>Theorem 44.8\<close>

lemma d_strict:
  "d(x) = bot \<longleftrightarrow> x \<le> Z"
  by (metis sup_commute sup_bot_right d_Z d_dist_sup d_restrict le_iff_sup mult_left_zero)

text \<open>Theorem 44.1\<close>

lemma d_isotone:
  "x \<le> y \<Longrightarrow> d(x) \<le> d(y)"
  using d_dist_sup sup_right_divisibility by force

lemma d_plus_left_upper_bound:
  "d(x) \<le> d(x \<squnion> y)"
  by (simp add: d_isotone)

lemma d_idempotent:
  "d(x) * d(x) = d(x)"
  by (smt (verit, ccfv_threshold) d_involutive d_mult_sub d_Z d_dist_sup d_export d_restrict le_iff_sup sup_bot_left sup_commute)

text \<open>Theorem 44.12\<close>

lemma d_least_left_preserver:
  "x \<le> d(y) * x \<squnion> Z \<longleftrightarrow> d(x) \<le> d(y)"
  apply (rule iffI)
  apply (smt (z3) comm_monoid.comm_neutral d_involutive d_mult_sub d_plus_left_upper_bound d_Z d_dist_sup order_trans sup_absorb2 sup_bot.comm_monoid_axioms)
  by (smt (verit, del_insts) d_restrict mult_right_dist_sup sup.cobounded1 sup.orderE sup_assoc sup_commute)

text \<open>Theorem 44.9\<close>

lemma d_weak_locality:
  "x * y \<le> Z \<longleftrightarrow> x * d(y) \<le> Z"
  by (metis d_mult_d d_strict)

lemma d_sup_closed:
  "d(d(x) \<squnion> d(y)) = d(x) \<squnion> d(y)"
  by (simp add: d_involutive d_dist_sup)

lemma d_mult_closed:
  "d(d(x) * d(y)) = d(x) * d(y)"
  using d_export d_mult_d by auto

lemma d_mult_left_lower_bound:
  "d(x) * d(y) \<le> d(x)"
  by (metis d_export d_involutive d_mult_sub)

lemma d_mult_left_absorb_sup:
  "d(x) * (d(x) \<squnion> d(y)) = d(x)"
  by (smt d_sup_closed d_export d_idempotent d_involutive d_mult_sub order.eq_iff mult_left_sub_dist_sup_left)

lemma d_sup_left_absorb_mult:
  "d(x) \<squnion> d(x) * d(y) = d(x)"
  using d_mult_left_lower_bound sup.absorb_iff1 by auto

lemma d_commutative:
  "d(x) * d(y) = d(y) * d(x)"
  by (metis sup_commute order.antisym d_sup_left_absorb_mult d_below_one d_export d_mult_left_absorb_sup mult_assoc mult_left_isotone mult_left_one)

lemma d_mult_greatest_lower_bound:
  "d(x) \<le> d(y) * d(z) \<longleftrightarrow> d(x) \<le> d(y) \<and> d(x) \<le> d(z)"
  by (metis d_commutative d_idempotent d_mult_left_lower_bound mult_isotone order_trans)

lemma d_sup_left_dist_mult:
  "d(x) \<squnion> d(y) * d(z) = (d(x) \<squnion> d(y)) * (d(x) \<squnion> d(z))"
  by (metis sup_assoc d_commutative d_dist_sup d_idempotent d_mult_left_absorb_sup mult_right_dist_sup)

lemma d_order:
  "d(x) \<le> d(y) \<longleftrightarrow> d(x) = d(x) * d(y)"
  by (metis d_mult_greatest_lower_bound d_mult_left_absorb_sup le_iff_sup order_refl)

text \<open>Theorem 44.6\<close>

lemma Z_mult_decreasing:
  "Z * x \<le> Z"
  by (metis d_mult_sub bot.extremum d_strict order.eq_iff)

text \<open>Theorem 44.5\<close>

lemma d_below_d_one:
  "d(x) \<le> d(1)"
  by (metis d_mult_sub mult_left_one)

text \<open>Theorem 44.7\<close>

lemma d_relative_Z:
  "d(x) * x \<squnion> Z = x \<squnion> Z"
  by (metis sup_ge1 sup_same_context d_below_one d_restrict mult_isotone mult_left_one)

lemma Z_left_zero_above_one:
  "1 \<le> x \<Longrightarrow> Z * x = Z"
  by (metis Z_mult_decreasing order.eq_iff mult_right_isotone mult_1_right)

text \<open>Theorem 44.11\<close>

lemma kat_4:
  "d(x) * y = d(x) * y * d(z) \<Longrightarrow> d(x) * y \<le> y * d(z)"
  by (metis d_below_one mult_left_isotone mult_left_one)

lemma kat_4_equiv:
  "d(x) * y = d(x) * y * d(z) \<longleftrightarrow> d(x) * y \<le> y * d(z)"
  apply (rule iffI)
  apply (simp add: kat_4)
  apply (rule order.antisym)
  apply (metis d_idempotent mult_assoc mult_right_isotone)
  by (metis d_below_one mult_right_isotone mult_1_right)

lemma kat_4_equiv_opp:
  "y * d(x) = d(z) * y * d(x) \<longleftrightarrow> y * d(x) \<le> d(z) * y"
  apply (rule iffI)
  using d_below_one mult_right_isotone apply fastforce
  apply (rule order.antisym)
  apply (metis d_idempotent mult_assoc mult_left_isotone)
  by (metis d_below_one mult_left_isotone mult_left_one)

text \<open>Theorem 44.10\<close>

lemma d_restrict_iff_1:
  "d(x) * y \<le> z \<longleftrightarrow> d(x) * y \<le> d(x) * z"
  by (smt (verit, del_insts) d_below_one d_idempotent mult_assoc mult_left_isotone mult_left_one mult_right_isotone order_trans)

(* independence of axioms, checked in relative_domain_semiring without the respective axiom:
lemma d_restrict : "x \<le> d(x) * x \<squnion> Z" nitpick [expect=genuine,card=2] oops
lemma d_mult_d   : "d(x * y) = d(x * d(y))" nitpick [expect=genuine,card=3] oops
lemma d_below_one: "d(x) \<le> 1" nitpick [expect=genuine,card=3] oops
lemma d_Z        : "d(Z) = bot" nitpick [expect=genuine,card=2] oops
lemma d_dist_sup : "d(x \<squnion> y) = d(x) \<squnion> d(y)" nitpick [expect=genuine,card=3] oops
lemma d_export   : "d(d(x) * y) = d(x) * d(y)" nitpick [expect=genuine,card=5] oops
*)

end

typedef (overloaded) 'a dImage = "{ x::'a::relative_domain_semiring . (\<exists>y::'a . x = d(y)) }"
  by auto

lemma simp_dImage[simp]:
  "\<exists>y . Rep_dImage x = d(y)"
  using Rep_dImage by simp

setup_lifting type_definition_dImage

text \<open>Theorem 44\<close>

instantiation dImage :: (relative_domain_semiring) bounded_distrib_lattice
begin

lift_definition sup_dImage :: "'a dImage \<Rightarrow> 'a dImage \<Rightarrow> 'a dImage" is sup
  by (metis d_dist_sup)

lift_definition inf_dImage :: "'a dImage \<Rightarrow> 'a dImage \<Rightarrow> 'a dImage" is times
  by (metis d_export)

lift_definition bot_dImage :: "'a dImage" is bot
  by (metis d_zero)

lift_definition top_dImage :: "'a dImage" is "d(1)"
  by auto

lift_definition less_eq_dImage :: "'a dImage \<Rightarrow> 'a dImage \<Rightarrow> bool" is less_eq .

lift_definition less_dImage :: "'a dImage \<Rightarrow> 'a dImage \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (simp add: less_dImage.rep_eq less_eq_dImage.rep_eq less_le_not_le)
  apply (simp add: less_eq_dImage.rep_eq)
  using less_eq_dImage.rep_eq apply simp
  apply (simp add: Rep_dImage_inject less_eq_dImage.rep_eq)
  apply (metis (mono_tags) d_involutive d_mult_sub inf_dImage.rep_eq less_eq_dImage.rep_eq simp_dImage)
  apply (metis (mono_tags) d_mult_greatest_lower_bound inf_dImage.rep_eq less_eq_dImage.rep_eq order_refl simp_dImage)
  apply (metis (mono_tags) d_mult_greatest_lower_bound inf_dImage.rep_eq less_eq_dImage.rep_eq simp_dImage)
  apply (simp add: less_eq_dImage.rep_eq sup_dImage.rep_eq)
  apply (simp add: less_eq_dImage.rep_eq sup_dImage.rep_eq)
  apply (simp add: less_eq_dImage.rep_eq sup_dImage.rep_eq)
  apply (simp add: bot_dImage.rep_eq less_eq_dImage.rep_eq)
  apply (smt (z3) d_below_d_one less_eq_dImage.rep_eq simp_dImage top_dImage.rep_eq)
  by (smt (z3) inf_dImage.rep_eq sup_dImage.rep_eq simp_dImage Rep_dImage_inject d_sup_left_dist_mult)

end

class bounded_relative_domain_semiring = relative_domain_semiring + bounded_idempotent_left_semiring
begin

lemma Z_top:
  "Z * top = Z"
  by (simp add: Z_left_zero_above_one)

lemma d_restrict_top:
  "x \<le> d(x) * top \<squnion> Z"
  by (metis sup_left_isotone d_restrict mult_right_isotone order_trans top_greatest)

(*
lemma d_one_one: "d(1) = 1" nitpick [expect=genuine,card=2] oops
*)

end

class relative_domain_semiring_split = relative_domain_semiring +
  assumes split_Z: "x * (y \<squnion> Z) \<le> x * y \<squnion> Z"
begin

lemma d_restrict_iff:
  "(x \<le> y \<squnion> Z) \<longleftrightarrow> (x \<le> d(x) * y \<squnion> Z)"
proof -
  have "x \<le> y \<squnion> Z \<longrightarrow> x \<le> d(x) * (y \<squnion> Z) \<squnion> Z"
    by (smt sup_left_isotone d_restrict le_iff_sup mult_left_sub_dist_sup_left order_trans)
  hence "x \<le> y \<squnion> Z \<longrightarrow> x \<le> d(x) * y \<squnion> Z"
    by (meson le_supI order_lesseq_imp split_Z sup.cobounded2)
  thus ?thesis
    by (meson d_restrict_iff_1 le_supI mult_left_sub_dist_sup_left order_lesseq_imp sup.cobounded2)
qed

end

class relative_antidomain_semiring = idempotent_left_semiring + dom + Z + uminus +
  assumes a_restrict  : "-x * x \<le> Z"
  assumes a_mult_d    : "-(x * y) = -(x * --y)"
  assumes a_complement: "-x * --x = bot"
  assumes a_Z         : "-Z = 1"
  assumes a_export    : "-(--x * y) = -x \<squnion> -y"
  assumes a_dist_sup  : "-(x \<squnion> y) = -x * -y"
  assumes d_def       : "d(x) = --x"
begin

notation
  uminus ("a")

text \<open>Theorem 45.7\<close>

lemma a_complement_one:
  "--x \<squnion> -x = 1"
  by (metis a_Z a_complement a_export a_mult_d mult_left_one)

text \<open>Theorem 45.5 and Theorem 45.6\<close>

lemma a_d_closed:
  "d(a(x)) = a(x)"
  by (metis a_mult_d d_def mult_left_one)

lemma a_below_one:
  "a(x) \<le> 1"
  using a_complement_one sup_right_divisibility by auto

lemma a_export_a:
  "a(a(x) * y) = d(x) \<squnion> a(y)"
  by (metis a_d_closed a_export d_def)

lemma a_sup_absorb:
  "(x \<squnion> a(y)) * a(a(y)) = x * a(a(y))"
  by (simp add: a_complement mult_right_dist_sup)

text \<open>Theorem 45.10\<close>

lemma a_greatest_left_absorber:
  "a(x) * y \<le> Z \<longleftrightarrow> a(x) \<le> a(y)"
  apply (rule iffI)
  apply (smt a_Z a_sup_absorb a_dist_sup a_export_a a_mult_d sup_commute d_def le_iff_sup mult_left_one)
  by (meson a_restrict mult_isotone order.refl order_trans)

lemma a_plus_left_lower_bound:
  "a(x \<squnion> y) \<le> a(x)"
  by (metis a_greatest_left_absorber a_restrict sup_commute mult_left_sub_dist_sup_right order_trans)

text \<open>Theorem 45.2\<close>

subclass relative_domain_semiring
  apply unfold_locales
  apply (smt (verit) a_Z a_complement_one a_restrict sup_commute sup_ge1 case_split_left d_def order_trans)
  using a_mult_d d_def apply force
  apply (simp add: a_below_one d_def)
  apply (metis a_Z a_complement d_def mult_left_one)
  apply (simp add: a_export_a a_dist_sup d_def)
  using a_dist_sup a_export d_def by auto

text \<open>Theorem 45.1\<close>

subclass tests
  apply unfold_locales
  apply (simp add: mult_assoc)
  apply (metis a_dist_sup sup_commute)
  apply (smt a_complement a_d_closed a_export_a sup_bot_right d_sup_left_dist_mult)
  apply (metis a_d_closed a_dist_sup d_def)
  apply (rule the_equality[THEN sym])
  apply (simp add: a_complement)
  apply (simp add: a_complement)
  using a_d_closed a_Z d_Z d_def apply force
  using a_export a_mult_d apply fastforce
  apply (metis a_d_closed d_order)
  by (simp add: less_le_not_le)

lemma a_plus_mult_d:
  "-(x * y) \<squnion> -(x * --y) = -(x * --y)"
  using a_mult_d by auto

lemma a_mult_d_2:
  "a(x * y) = a(x * d(y))"
  using a_mult_d d_def by auto

lemma a_3:
  "a(x) * a(y) * d(x \<squnion> y) = bot"
  by (metis a_complement a_dist_sup d_def)

lemma a_fixpoint:
  "\<forall>x . (a(x) = x \<longrightarrow> (\<forall>y . y = bot))"
  by (metis a_complement_one mult_1_left mult_left_zero order.refl sup.order_iff tests_dual.one_def)

text \<open>Theorem 45.9\<close>

lemma a_strict:
  "a(x) = 1 \<longleftrightarrow> x \<le> Z"
  by (metis a_Z d_def d_strict order.refl tests_dual.sba_dual.double_negation)

lemma d_complement_zero:
  "d(x) * a(x) = bot"
  by (simp add: d_def tests_dual.sub_commutative)

lemma a_complement_zero:
  "a(x) * d(x) = bot"
  by (simp add: d_def)

lemma a_shunting_zero:
  "a(x) * d(y) = bot \<longleftrightarrow> a(x) \<le> a(y)"
  by (simp add: d_def tests_dual.sba_dual.less_eq_inf_bot)

lemma a_antitone:
  "x \<le> y \<Longrightarrow> a(y) \<le> a(x)"
  using a_plus_left_lower_bound sup_commute sup_right_divisibility by fastforce

lemma a_mult_deMorgan:
  "a(a(x) * a(y)) = d(x \<squnion> y)"
  by (simp add: a_dist_sup d_def)

lemma a_mult_deMorgan_1:
  "a(a(x) * a(y)) = d(x) \<squnion> d(y)"
  by (simp add: a_mult_deMorgan d_dist_sup)

lemma a_mult_deMorgan_2:
  "a(d(x) * d(y)) = a(x) \<squnion> a(y)"
  using a_export d_def by auto

lemma a_plus_deMorgan:
  "a(a(x) \<squnion> a(y)) = d(x) * d(y)"
  by (simp add: a_dist_sup d_def)

lemma a_plus_deMorgan_1:
  "a(d(x) \<squnion> d(y)) = a(x) * a(y)"
  by (simp add: a_dist_sup d_def)

text \<open>Theorem 45.8\<close>

lemma a_mult_left_upper_bound:
  "a(x) \<le> a(x * y)"
  using a_shunting_zero d_def d_mult_sub tests_dual.less_eq_sup_top by auto

text \<open>Theorem 45.6\<close>

lemma d_a_closed:
  "a(d(x)) = a(x)"
  by (simp add: d_def)

lemma a_export_d:
  "a(d(x) * y) = a(x) \<squnion> a(y)"
  by (simp add: a_export d_def)

lemma a_7:
  "d(x) * a(d(y) \<squnion> d(z)) = d(x) * a(y) * a(z)"
  by (simp add: a_plus_deMorgan_1 mult_assoc)

lemma d_a_shunting:
  "d(x) * a(y) \<le> d(z) \<longleftrightarrow> d(x) \<le> d(z) \<squnion> d(y)"
  by (simp add: d_def tests_dual.sba_dual.shunting_right)

lemma d_d_shunting:
  "d(x) * d(y) \<le> d(z) \<longleftrightarrow> d(x) \<le> d(z) \<squnion> a(y)"
  by (simp add: d_def tests_dual.sba_dual.shunting_right)

lemma d_cancellation_1:
  "d(x) \<le> d(y) \<squnion> (d(x) * a(y))"
  by (smt (z3) a_d_closed d_a_shunting d_export eq_refl sup_commute)

lemma d_cancellation_2:
  "(d(z) \<squnion> d(y)) * a(y) \<le> d(z)"
  by (metis d_a_shunting d_dist_sup eq_refl)

lemma a_sup_closed:
  "d(a(x) \<squnion> a(y)) = a(x) \<squnion> a(y)"
  using a_mult_deMorgan tests_dual.sub_inf_def by auto

lemma a_mult_closed:
  "d(a(x) * a(y)) = a(x) * a(y)"
  using d_def tests_dual.sub_sup_closed by auto

lemma d_a_shunting_zero:
  "d(x) * a(y) = bot \<longleftrightarrow> d(x) \<le> d(y)"
  using a_shunting_zero d_def by force

lemma d_d_shunting_zero:
  "d(x) * d(y) = bot \<longleftrightarrow> d(x) \<le> a(y)"
  using d_a_shunting_zero d_def by auto

lemma d_compl_intro:
  "d(x) \<squnion> d(y) = d(x) \<squnion> a(x) * d(y)"
  by (simp add: d_def tests_dual.sba_dual.sup_complement_intro)

lemma a_compl_intro:
  "a(x) \<squnion> a(y) = a(x) \<squnion> d(x) * a(y)"
  by (simp add: d_def tests_dual.sba_dual.sup_complement_intro)

lemma kat_2:
  "y * a(z) \<le> a(x) * y \<Longrightarrow> d(x) * y * a(z) = bot"
  by (metis d_complement_zero order.eq_iff mult_assoc mult_left_zero mult_right_isotone bot_least)

text \<open>Theorem 45.4\<close>

lemma kat_2_equiv:
  "y * a(z) \<le> a(x) * y \<longleftrightarrow> d(x) * y * a(z) = bot"
  apply (rule iffI)
  apply (simp add: kat_2)
  by (smt (verit, best) a_Z a_below_one a_complement_one case_split_left d_def mult_assoc mult_right_isotone mult_1_right bot_least)

lemma kat_3_equiv_opp:
  "a(z) * y * d(x) = bot \<longleftrightarrow> y * d(x) = d(z) * y * d(x)"
  using kat_2_equiv d_def kat_4_equiv_opp by auto

text \<open>Theorem 45.4\<close>

lemma kat_3_equiv_opp_2:
  "d(z) * y * a(x) = bot \<longleftrightarrow> y * a(x) = a(z) * y * a(x)"
  by (metis a_d_closed kat_3_equiv_opp d_def)

lemma kat_equiv_6:
  "d(x) * y * a(z) = d(x) * y * bot \<longleftrightarrow> d(x) * y * a(z) \<le> y * bot"
  by (metis d_restrict_iff_1 order.eq_iff mult_left_sub_dist_sup_right tests_dual.sba_dual.sup_right_unit mult_assoc)

lemma d_one_one:
  "d(1) = 1"
  by (simp add: d_def)

lemma case_split_left_sup:
  "-p * x \<le> y \<and> --p * x \<le> z \<Longrightarrow> x \<le> y \<squnion> z"
  by (smt (z3) a_complement_one case_split_left order_lesseq_imp sup.cobounded2 sup_ge1)

lemma test_mult_left_sub_dist_shunt:
  "-p * (--p * x \<squnion> Z) \<le> Z"
  by (simp add: a_greatest_left_absorber a_Z a_dist_sup a_export)

lemma test_mult_left_dist_shunt:
  "-p * (--p * x \<squnion> Z) = -p * Z"
  by (smt (verit, ccfv_SIG) order.antisym mult_left_sub_dist_sup_right sup.orderE tests_dual.sba_dual.sup_idempotent mult_assoc test_mult_left_sub_dist_shunt tests_dual.sup_absorb)

(* independence of axioms, checked in relative_antidomain_semiring without the respective axiom:
lemma a_restrict  : "-x * x \<le> Z" nitpick [expect=genuine,card=3] oops
lemma a_mult_d    : "-(x * y) = -(x * --y)" nitpick [expect=genuine,card=3] oops
lemma a_complement: "-x * --x = bot" nitpick [expect=genuine,card=2] oops
lemma a_Z         : "-Z = 1" nitpick [expect=genuine,card=2] oops
lemma a_export    : "-(--x * y) = -x \<squnion> -y" nitpick [expect=genuine,card=5] oops
lemma a_dist_sup  : "-(x \<squnion> y) = -x * -y" nitpick [expect=genuine,card=3] oops
lemma d_def       : "d(x) = --x" nitpick [expect=genuine,card=2] oops
*)

end

typedef (overloaded) 'a aImage = "{ x::'a::relative_antidomain_semiring . (\<exists>y::'a . x = a(y)) }"
  by auto

lemma simp_aImage[simp]:
  "\<exists>y . Rep_aImage x = a(y)"
  using Rep_aImage by simp

setup_lifting type_definition_aImage

text \<open>Theorem 45.3\<close>

instantiation aImage :: (relative_antidomain_semiring) boolean_algebra
begin

lift_definition sup_aImage :: "'a aImage \<Rightarrow> 'a aImage \<Rightarrow> 'a aImage" is sup
  using tests_dual.sba_dual.sba_dual.inf_closed by auto

lift_definition inf_aImage :: "'a aImage \<Rightarrow> 'a aImage \<Rightarrow> 'a aImage" is times
  using tests_dual.sba_dual.inf_closed by auto

lift_definition minus_aImage :: "'a aImage \<Rightarrow> 'a aImage \<Rightarrow> 'a aImage" is "\<lambda>x y . x * a(y)"
  using tests_dual.sba_dual.inf_closed by blast

lift_definition uminus_aImage :: "'a aImage \<Rightarrow> 'a aImage" is a
  by auto

lift_definition bot_aImage :: "'a aImage" is bot
  by (metis tests_dual.sba_dual.sba_dual.complement_bot)

lift_definition top_aImage :: "'a aImage" is 1
  using a_Z by auto

lift_definition less_eq_aImage :: "'a aImage \<Rightarrow> 'a aImage \<Rightarrow> bool" is less_eq .

lift_definition less_aImage :: "'a aImage \<Rightarrow> 'a aImage \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (simp add: less_aImage.rep_eq less_eq_aImage.rep_eq less_le_not_le)
  apply (simp add: less_eq_aImage.rep_eq)
  using less_eq_aImage.rep_eq apply simp
  apply (simp add: Rep_aImage_inject less_eq_aImage.rep_eq)
  apply (metis (mono_tags) a_below_one inf_aImage.rep_eq less_eq_aImage.rep_eq mult.right_neutral mult_right_isotone simp_aImage)
  apply (metis (mono_tags, lifting) less_eq_aImage.rep_eq a_d_closed a_export bot.extremum_unique inf_aImage.rep_eq kat_equiv_6 mult.assoc mult.left_neutral mult_left_isotone mult_left_zero simp_aImage sup.cobounded1 tests_dual.sba_dual.sba_dual.complement_top)
  apply (smt (z3) less_eq_aImage.rep_eq inf_aImage.rep_eq mult_isotone simp_aImage tests_dual.sba_dual.inf_idempotent)
  apply (simp add: less_eq_aImage.rep_eq sup_aImage.rep_eq)
  apply (simp add: less_eq_aImage.rep_eq sup_aImage.rep_eq)
  using less_eq_aImage.rep_eq sup_aImage.rep_eq apply force
  apply (simp add: less_eq_aImage.rep_eq bot_aImage.rep_eq)
  apply (smt (z3) less_eq_aImage.rep_eq a_below_one simp_aImage top_aImage.rep_eq)
  apply (metis (mono_tags, lifting) tests_dual.sba_dual.sba_dual.inf_left_dist_sup Rep_aImage_inject inf_aImage.rep_eq sup_aImage.rep_eq simp_aImage)
  apply (smt (z3) inf_aImage.rep_eq uminus_aImage.rep_eq Rep_aImage_inject a_complement bot_aImage.rep_eq simp_aImage)
  apply (smt (z3) top_aImage.rep_eq Rep_aImage_inject a_complement_one simp_aImage sup_aImage.rep_eq sup_commute uminus_aImage.rep_eq)
  by (metis (mono_tags) inf_aImage.rep_eq Rep_aImage_inject minus_aImage.rep_eq uminus_aImage.rep_eq)

end

class bounded_relative_antidomain_semiring = relative_antidomain_semiring + bounded_idempotent_left_semiring
begin

subclass bounded_relative_domain_semiring ..

lemma a_top:
  "a(top) = bot"
  by (metis a_plus_left_lower_bound bot_unique sup_right_top tests_dual.sba_dual.complement_top)

lemma d_top:
  "d(top) = 1"
  using a_top d_def by auto

lemma shunting_top_1:
  "-p * x \<le> y \<Longrightarrow> x \<le> --p * top \<squnion> y"
  by (metis sup_commute case_split_left_sup mult_right_isotone top_greatest)

lemma shunting_Z:
  "-p * x \<le> Z \<longleftrightarrow> x \<le> --p * top \<squnion> Z"
  apply (rule iffI)
  apply (simp add: shunting_top_1)
  by (smt a_top a_Z a_antitone a_dist_sup a_export a_greatest_left_absorber sup_commute sup_bot_right mult_left_one)

(*
lemma a_left_dist_sup: "-p * (y \<squnion> z) = -p * y \<squnion> -p * z" nitpick [expect=genuine,card=7] oops
lemma shunting_top: "-p * x \<le> y \<longleftrightarrow> x \<le> --p * top \<squnion> y" nitpick [expect=genuine,card=7] oops
*)

end

class relative_left_zero_antidomain_semiring = relative_antidomain_semiring + idempotent_left_zero_semiring
begin

lemma kat_3:
  "d(x) * y * a(z) = bot \<Longrightarrow> d(x) * y = d(x) * y * d(z)"
  by (metis d_def mult_1_right mult_left_dist_sup sup_monoid.add_0_left tests_dual.inf_complement)

lemma a_a_below:
  "a(a(x)) * y \<le> y"
  using d_def d_restrict_iff_1 by auto

lemma kat_equiv_5:
  "d(x) * y \<le> y * d(z) \<longleftrightarrow> d(x) * y * a(z) = d(x) * y * bot"
proof
  assume "d(x) * y \<le> y * d(z)"
  thus "d(x) * y * a(z) = d(x) * y * bot"
    by (metis d_complement_zero kat_4_equiv mult_assoc)
next
  assume "d(x) * y * a(z) = d(x) * y * bot"
  hence "a(a(x)) * y * a(z) \<le> y * a(a(z))"
    by (simp add: a_a_below d_def mult_isotone)
  thus "d(x) * y \<le> y * d(z)"
    by (metis a_a_below a_complement_one case_split_right d_def mult_isotone order_refl)
qed

lemma case_split_right_sup:
  "x * -p \<le> y \<Longrightarrow> x * --p \<le> z \<Longrightarrow> x \<le> y \<squnion> z"
  by (smt (verit, ccfv_SIG) a_complement_one order.trans mult_1_right mult_left_dist_sup sup_commute sup_right_isotone)

end

class bounded_relative_left_zero_antidomain_semiring = relative_left_zero_antidomain_semiring + bounded_idempotent_left_zero_semiring
begin

lemma shunting_top:
  "-p * x \<le> y \<longleftrightarrow> x \<le> --p * top \<squnion> y"
  apply (rule iffI)
  apply (metis sup_commute case_split_left_sup mult_right_isotone top_greatest)
  by (metis a_complement sup_bot_left sup_right_divisibility mult_assoc mult_left_dist_sup mult_left_one mult_left_zero mult_right_dist_sup mult_right_isotone order_trans tests_dual.inf_left_unit)

end

end

