(* Title:      Domain
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Domain\<close>

theory Domain

imports Stone_Relation_Algebras.Semirings Tests

begin

context idempotent_left_semiring
begin

sublocale ils: il_semiring where inf = times and sup = sup and bot = bot and less_eq = less_eq and less = less and top = 1
  apply unfold_locales
  apply (simp add: sup_assoc)
  apply (simp add: sup_commute)
  apply simp
  apply simp
  apply (simp add: mult_assoc)
  apply (simp add: mult_right_dist_sup)
  apply simp
  apply simp
  apply simp
  apply (simp add: mult_right_isotone)
  apply (simp add: le_iff_sup)
  by (simp add: less_le_not_le)

end

class left_zero_domain_semiring = idempotent_left_zero_semiring + dom +
  assumes d_restrict: "x \<squnion> d(x) * x = d(x) * x"
  assumes d_mult_d  : "d(x * y) = d(x * d(y))"
  assumes d_plus_one: "d(x) \<squnion> 1 = 1"
  assumes d_zero    : "d(bot) = bot"
  assumes d_dist_sup: "d(x \<squnion> y) = d(x) \<squnion> d(y)"
begin

text \<open>Many lemmas in this class are taken from Georg Struth's theories.\<close>

lemma d_restrict_equals:
  "x = d(x) * x"
  by (metis sup_commute d_plus_one d_restrict mult_left_one mult_right_dist_sup)

lemma d_involutive:
  "d(d(x)) = d(x)"
  by (metis d_mult_d mult_left_one)

lemma d_fixpoint:
  "(\<exists>y . x = d(y)) \<longleftrightarrow> x = d(x)"
  using d_involutive by auto

lemma d_type:
  "\<forall>P . (\<forall>x . x = d(x) \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x . P(d(x)))"
  by (metis d_involutive)

lemma d_mult_sub:
  "d(x * y) \<le> d(x)"
  by (metis d_dist_sup d_mult_d d_plus_one le_iff_sup mult_left_sub_dist_sup_left mult_1_right)

lemma d_sub_one:
  "x \<le> 1 \<Longrightarrow> x \<le> d(x)"
  by (metis d_restrict_equals mult_right_isotone mult_1_right)

lemma d_strict:
  "d(x) = bot \<longleftrightarrow> x = bot"
  by (metis d_restrict_equals d_zero mult_left_zero)

lemma d_one:
  "d(1) = 1"
  by (metis d_restrict_equals mult_1_right)

lemma d_below_one:
  "d(x) \<le> 1"
  by (simp add: d_plus_one le_iff_sup)

lemma d_isotone:
  "x \<le> y \<Longrightarrow> d(x) \<le> d(y)"
  by (metis d_dist_sup le_iff_sup)

lemma d_plus_left_upper_bound:
  "d(x) \<le> d(x \<squnion> y)"
  by (simp add: d_isotone)

lemma d_export:
  "d(d(x) * y) = d(x) * d(y)"
  apply (rule order.antisym)
  apply (metis d_below_one d_involutive d_mult_sub d_restrict_equals d_isotone d_mult_d mult_isotone mult_left_one)
  by (metis d_below_one d_sub_one coreflexive_mult_closed d_mult_d)

lemma d_idempotent:
  "d(x) * d(x) = d(x)"
  by (metis d_export d_restrict_equals)

lemma d_commutative:
  "d(x) * d(y) = d(y) * d(x)"
  by (metis ils.il_inf_associative order.antisym d_export d_mult_d d_mult_sub d_one d_restrict_equals mult_isotone mult_left_one)

lemma d_least_left_preserver:
  "x \<le> d(y) * x \<longleftrightarrow> d(x) \<le> d(y)"
  by (metis d_below_one d_involutive d_mult_sub d_restrict_equals order.eq_iff mult_left_isotone mult_left_one)

lemma d_weak_locality:
  "x * y = bot \<longleftrightarrow> x * d(y) = bot"
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

lemma d_mult_greatest_lower_bound:
  "d(x) \<le> d(y) * d(z) \<longleftrightarrow> d(x) \<le> d(y) \<and> d(x) \<le> d(z)"
  by (metis d_commutative d_idempotent d_mult_left_lower_bound mult_isotone order_trans)

lemma d_mult_left_absorb_sup:
  "d(x) * (d(x) \<squnion> d(y)) = d(x)"
  by (metis sup_commute d_idempotent d_plus_one mult_left_dist_sup mult_1_right)

lemma d_sup_left_absorb_mult:
  "d(x) \<squnion> d(x) * d(y) = d(x)"
  using d_mult_left_lower_bound sup.absorb_iff1 by auto

lemma d_sup_left_dist_mult:
  "d(x) \<squnion> d(y) * d(z) = (d(x) \<squnion> d(y)) * (d(x) \<squnion> d(z))"
  by (smt sup_assoc d_commutative d_idempotent d_mult_left_absorb_sup mult_left_dist_sup mult_right_dist_sup)

lemma d_order:
  "d(x) \<le> d(y) \<longleftrightarrow> d(x) = d(x) * d(y)"
  by (metis d_mult_greatest_lower_bound d_mult_left_absorb_sup le_iff_sup order_refl)

lemma d_mult_below:
  "d(x) * y \<le> y"
  by (metis sup_left_divisibility d_plus_one mult_left_one mult_right_dist_sup)

lemma d_preserves_equation:
  "d(y) * x \<le> x * d(y) \<longleftrightarrow> d(y) * x = d(y) * x * d(y)"
  by (simp add: d_below_one d_idempotent test_preserves_equation)

end

class left_zero_antidomain_semiring = idempotent_left_zero_semiring + dom + uminus +
  assumes a_restrict   : "-x * x = bot"
  assumes a_plus_mult_d: "-(x * y) \<squnion> -(x * --y) = -(x * --y)"
  assumes a_complement : "--x \<squnion> -x = 1"
  assumes d_def        : "d(x) = --x"
begin

sublocale aa: a_algebra where minus = "\<lambda>x y . -(-x \<squnion> y)" and uminus = uminus and inf = times and sup = sup and bot = bot and less_eq = less_eq and less = less and top = 1
  apply unfold_locales
  apply (simp add: a_restrict)
  using a_complement sup_commute apply fastforce
  apply (simp add: a_plus_mult_d le_iff_sup)
  by simp

subclass left_zero_domain_semiring
  apply unfold_locales
  apply (simp add: d_def aa.double_complement_above)
  apply (simp add: aa.a_d.d3_eq d_def)
  apply (simp add: d_def)
  apply (simp add: d_def)
  by (simp add: d_def aa.l15)

subclass tests
  apply unfold_locales
  apply (simp add: mult_assoc)
  apply (simp add: aa.sba_dual.sub_commutative)
  apply (simp add: aa.sba_dual.sub_complement)
  using aa.sba_dual.sub_sup_closed apply simp
  apply simp
  apply simp
  apply (simp add: aa.sba_dual.sub_inf_def)
  apply (simp add: aa.less_eq_inf)
  by (simp add: less_le_not_le)

text \<open>Many lemmas in this class are taken from Georg Struth's theories.\<close>

notation
  uminus ("a")

lemma a_greatest_left_absorber:
  "a(x) * y = bot \<longleftrightarrow> a(x) \<le> a(y)"
  by (simp add: aa.l10_iff)

lemma a_mult_d:
  "a(x * y) = a(x * d(y))"
  by (simp add: d_def aa.sba3_complement_inf_double_complement)

lemma a_d_closed:
  "d(a(x)) = a(x)"
  by (simp add: d_def)

lemma a_plus_left_lower_bound:
  "a(x \<squnion> y) \<le> a(x)"
  by (simp add: aa.l9)

lemma a_mult_sup:
  "a(x) * (y \<squnion> x) = a(x) * y"
  by (simp add: aa.sba3_inf_complement_bot semiring.distrib_left)

lemma a_3:
  "a(x) * a(y) * d(x \<squnion> y) = bot"
  using d_weak_locality aa.l12 aa.sba3_inf_complement_bot by force

lemma a_export:
  "a(a(x) * y) = d(x) \<squnion> a(y)"
  using a_mult_d d_def aa.sba_dual.sub_inf_def by auto

lemma a_fixpoint:
  "\<forall>x . (a(x) = x \<longrightarrow> (\<forall>y . y = bot))"
  by (metis aa.a_d.d_fully_strict aa.sba2_bot_unit aa.sup_idempotent aa.sup_right_zero_var)

lemma a_strict:
  "a(x) = 1 \<longleftrightarrow> x = bot"
  using aa.a_d.d_fully_strict one_def by fastforce

lemma d_complement_zero:
  "d(x) * a(x) = bot"
  by (simp add: aa.sba3_inf_complement_bot d_def)

lemma a_complement_zero:
  "a(x) * d(x) = bot"
  by (simp add: d_def)

lemma a_shunting_zero:
  "a(x) * d(y) = bot \<longleftrightarrow> a(x) \<le> a(y)"
  by (simp add: aa.less_eq_inf_bot d_def)

lemma a_antitone:
  "x \<le> y \<Longrightarrow> a(y) \<le> a(x)"
  by (simp add: aa.l9)

lemma a_mult_deMorgan:
  "a(a(x) * a(y)) = d(x \<squnion> y)"
  by (simp add: aa.sup_demorgan d_def)

lemma a_mult_deMorgan_1:
  "a(a(x) * a(y)) = d(x) \<squnion> d(y)"
  by (simp add: a_export d_def)

lemma a_mult_deMorgan_2:
  "a(d(x) * d(y)) = a(x) \<squnion> a(y)"
  by (simp add: d_def sup_def)

lemma a_plus_deMorgan:
  "a(a(x) \<squnion> a(y)) = d(x) * d(y)"
  by (simp add: aa.sub_sup_demorgan d_def)

lemma a_plus_deMorgan_1:
  "a(d(x) \<squnion> d(y)) = a(x) * a(y)"
  by (simp add: aa.sup_demorgan d_def)

lemma a_mult_left_upper_bound:
  "a(x) \<le> a(x * y)"
  using aa.l5 d_def d_mult_sub by auto

lemma d_a_closed:
  "a(d(x)) = a(x)"
  by (simp add: d_def)

lemma a_export_d:
  "a(d(x) * y) = a(x) \<squnion> a(y)"
  using a_mult_d a_mult_deMorgan_2 by auto

lemma a_7:
  "d(x) * a(d(y) \<squnion> d(z)) = d(x) * a(y) * a(z)"
  by (simp add: a_plus_deMorgan_1 mult_assoc)

lemma d_a_shunting:
  "d(x) * a(y) \<le> d(z) \<longleftrightarrow> d(x) \<le> d(z) \<squnion> d(y)"
  using aa.sba_dual.shunting_right d_def by auto

lemma d_d_shunting:
  "d(x) * d(y) \<le> d(z) \<longleftrightarrow> d(x) \<le> d(z) \<squnion> a(y)"
  using d_a_shunting d_def by auto

lemma d_cancellation_1:
  "d(x) \<le> d(y) \<squnion> (d(x) * a(y))"
  by (metis a_d_closed aa.sba2_export aa.sup_demorgan d_def eq_refl le_supE sup_commute)

lemma d_cancellation_2:
  "(d(z) \<squnion> d(y)) * a(y) \<le> d(z)"
  by (metis d_a_shunting d_dist_sup eq_refl)

lemma a_sup_closed:
  "d(a(x) \<squnion> a(y)) = a(x) \<squnion> a(y)"
  using aa.sub_sup_closed d_def by auto

lemma a_mult_closed:
  "d(a(x) * a(y)) = a(x) * a(y)"
  using a_d_closed aa.l12 by auto

lemma d_a_shunting_zero:
  "d(x) * a(y) = bot \<longleftrightarrow> d(x) \<le> d(y)"
  by (simp add: aa.l10_iff d_def)

lemma d_d_shunting_zero:
  "d(x) * d(y) = bot \<longleftrightarrow> d(x) \<le> a(y)"
  by (simp add: aa.l10_iff d_def)

lemma d_compl_intro:
  "d(x) \<squnion> d(y) = d(x) \<squnion> a(x) * d(y)"
  by (simp add: aa.sup_complement_intro d_def)

lemma a_compl_intro:
  "a(x) \<squnion> a(y) = a(x) \<squnion> d(x) * a(y)"
  by (simp add: aa.sup_complement_intro d_def)

lemma kat_2:
  "y * a(z) \<le> a(x) * y \<Longrightarrow> d(x) * y * a(z) = bot"
  by (smt a_export a_plus_left_lower_bound le_sup_iff d_d_shunting_zero d_export d_strict le_iff_sup mult_assoc)

lemma kat_3:
  "d(x) * y * a(z) = bot \<Longrightarrow> d(x) * y = d(x) * y * d(z)"
  by (metis a_export_d aa.complement_bot d_complement_zero d_def mult_1_right mult_left_dist_sup sup_bot_left)

lemma kat_4:
  "d(x) * y = d(x) * y * d(z) \<Longrightarrow> d(x) * y \<le> y * d(z)"
  using d_mult_below mult_assoc by auto

lemma kat_2_equiv:
  "y * a(z) \<le> a(x) * y \<longleftrightarrow> d(x) * y * a(z) = bot"
  apply (rule iffI)
  apply (simp add: kat_2)
  by (metis aa.top_greatest a_complement sup_bot_left d_def mult_left_one mult_right_dist_sup mult_right_isotone mult_1_right)

lemma kat_4_equiv:
  "d(x) * y = d(x) * y * d(z) \<longleftrightarrow> d(x) * y \<le> y * d(z)"
  apply (rule iffI)
  apply (simp add: kat_4)
  apply (rule order.antisym)
  apply (metis d_idempotent le_iff_sup mult_assoc mult_left_dist_sup)
  by (metis d_plus_one le_iff_sup mult_left_dist_sup mult_1_right)

lemma kat_3_equiv_opp:
  "a(z) * y * d(x) = bot \<longleftrightarrow> y * d(x) = d(z) * y * d(x)"
  by (metis a_complement a_restrict sup_bot_left d_a_closed d_def mult_assoc mult_left_one mult_left_zero mult_right_dist_sup)

lemma kat_4_equiv_opp:
  "y * d(x) = d(z) * y * d(x) \<longleftrightarrow> y * d(x) \<le> d(z) * y"
  using kat_2_equiv kat_3_equiv_opp d_def by auto

lemma d_restrict_iff:
  "(x \<le> y) \<longleftrightarrow> (x \<le> d(x) * y)"
  by (metis d_mult_below d_restrict_equals mult_isotone order_lesseq_imp)

lemma d_restrict_iff_1:
  "(d(x) * y \<le> z) \<longleftrightarrow> (d(x) * y \<le> d(x) * z)"
  by (metis sup_commute d_export d_mult_left_lower_bound d_plus_one d_restrict_iff mult_left_isotone mult_left_one mult_right_sub_dist_sup_right order_trans)

end

end

