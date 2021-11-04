(* Title:      Instances of Monotonic Boolean Transformers
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Instances of Monotonic Boolean Transformers\<close>

theory Monotonic_Boolean_Transformers_Instances

imports Monotonic_Boolean_Transformers Pre_Post_Modal General_Refinement_Algebras

begin

sublocale mbt_algebra < mbta: bounded_idempotent_left_semiring
  apply unfold_locales
  apply (simp add: le_comp)
  apply (simp add: sup_comp)
  apply simp
  apply simp
  apply simp
  apply simp
  by (simp add: mult_assoc)

sublocale mbt_algebra < mbta_dual: bounded_idempotent_left_semiring where less = greater and less_eq = greater_eq and sup = inf and bot = top and top = bot
  apply unfold_locales
  using inf.bounded_iff inf_le1 inf_le2 mbta.mult_right_isotone apply simp
  using inf_comp apply blast
  apply simp
  apply simp
  apply simp
  apply simp
  by (simp add: mult_assoc)

sublocale mbt_algebra < mbta: bounded_general_refinement_algebra where star = dual_star and Omega = dual_omega
  apply unfold_locales
  using dual_star_fix sup_commute apply force
  apply (simp add: dual_star_least)
  using dual_omega_fix sup_commute apply force
  by (simp add: dual_omega_greatest sup_commute)

sublocale mbt_algebra < mbta_dual: bounded_general_refinement_algebra where less = greater and less_eq = greater_eq and sup = inf and bot = top and Omega = omega and top = bot
  apply unfold_locales
  using order.eq_iff star_fix apply simp
  using star_greatest apply simp
  using inf_commute omega_fix apply fastforce
  by (simp add: inf.sup_monoid.add_commute omega_least)

text \<open>Theorem 50.9(b)\<close>

sublocale mbt_algebra < mbta: left_conway_semiring_L where circ = dual_star and L = bot
  apply unfold_locales
  apply (simp add: mbta.star_one)
  by simp

text \<open>Theorem 50.8(a)\<close>

sublocale mbt_algebra < mbta_dual: left_conway_semiring_L where circ = omega and less = greater and less_eq = greater_eq and sup = inf and bot = top and L = bot
  apply unfold_locales
  apply simp
  by simp

text \<open>Theorem 50.8(b)\<close>

sublocale mbt_algebra < mbta_fix: left_conway_semiring_L where circ = dual_omega and L = top
  apply unfold_locales
  apply (simp add: mbta.Omega_one)
  by simp

text \<open>Theorem 50.9(a)\<close>

sublocale mbt_algebra < mbta_fix_dual: left_conway_semiring_L where circ = star and less = greater and less_eq = greater_eq and sup = inf and bot = top and L = top
  apply unfold_locales
  apply (simp add: mbta_dual.star_one)
  by simp

sublocale mbt_algebra < mbta: left_kleene_conway_semiring where circ = dual_star and star = dual_star ..

sublocale mbt_algebra < mbta_dual: left_kleene_conway_semiring where circ = omega and less = greater and less_eq = greater_eq and sup = inf and bot = top ..

sublocale mbt_algebra < mbta_fix: left_kleene_conway_semiring where circ = dual_omega and star = dual_star ..

sublocale mbt_algebra < mbta_fix_dual: left_kleene_conway_semiring where circ = star and less = greater and less_eq = greater_eq and sup = inf and bot = top ..

sublocale mbt_algebra < mbta: tests where uminus = neg_assert
  apply unfold_locales
  apply (simp add: mult_assoc)
  apply (metis neg_assertion assertion_inf_comp_eq inf_commute)
  subgoal for x y
  proof -
    have "(x ^ o * bot \<squnion> y * top) \<sqinter> ((x ^ o * bot \<squnion> y ^ o * bot) \<sqinter> 1) = x ^ o * bot \<sqinter> 1"
      by (metis inf_assoc dual_neg sup_bot_right sup_inf_distrib1)
    thus ?thesis
      by (simp add: dual_inf dual_comp inf_comp sup_comp neg_assert_def)
  qed
  apply (simp add: neg_assertion)
  using assertion_inf_comp_eq inf_uminus neg_assertion apply force
  apply (simp add: neg_assert_def)
  apply (simp add: dual_inf dual_comp sup_comp neg_assert_def inf_sup_distrib2)
  apply (simp add: assertion_inf_comp_eq inf.absorb_iff1 neg_assertion)
  using inf.less_le_not_le by blast

sublocale mbt_algebra < mbta_dual: tests where less = greater and less_eq = greater_eq and sup = inf and uminus = neg_assume and bot = top
  apply unfold_locales
  apply (simp add: mult_assoc)
  apply (metis neg_assumption assumption_sup_comp_eq sup_commute)
  subgoal for x y
  proof -
    have "(x ^ o * top \<sqinter> y * bot) \<squnion> ((x ^ o * top \<sqinter> y ^ o * top) \<squnion> 1) = x ^ o * top \<squnion> 1"
      by (metis dual_dual dual_neg_top inf_sup_distrib1 inf_top_right sup_assoc)
    thus ?thesis
      by (simp add: dual_comp dual_sup inf_comp sup_comp neg_assume_def)
  qed
  using assumption_neg_assume comp_assumption neg_assumption apply blast
  using assumption_sup_comp_eq inf_uminus_assume neg_assumption apply fastforce
  apply (simp add: neg_assume_def)
  apply (simp add: dual_inf dual_comp dual_sup inf_comp sup_comp neg_assume_def sup_inf_distrib2)
  apply (simp add: assumption_sup_comp_eq neg_assumption sup.absorb_iff1)
  using inf.less_le_not_le by auto

text \<open>Theorem 51.2\<close>

sublocale mbt_algebra < mbta: bounded_relative_antidomain_semiring where d = "\<lambda>x . (x * top) \<sqinter> 1" and uminus = neg_assert and Z = bot
  apply unfold_locales
  subgoal for x
  proof -
    have "x ^ o * bot \<sqinter> x \<le> bot"
      by (metis dual_neg eq_refl inf.commute inf_mono mbta.top_right_mult_increasing)
    thus ?thesis
      by (simp add: neg_assert_def inf_comp)
  qed
  apply (simp add: dual_comp dual_inf neg_assert_def sup_comp mult_assoc)
  apply simp
  apply simp
  apply (simp add: dual_inf dual_comp sup_comp neg_assert_def inf_sup_distrib2)
  apply (simp add: dual_sup inf_comp neg_assert_def inf.assoc)
  by (simp add: dual_inf dual_comp sup_comp neg_assert_def)

text \<open>Theorem 51.1\<close>

sublocale mbt_algebra < mbta_dual: bounded_relative_antidomain_semiring where d = "\<lambda>x . (x * bot) \<squnion> 1" and less = greater and less_eq = greater_eq and sup = inf and uminus = neg_assume and bot = top and top = bot and Z = top
  apply unfold_locales
  subgoal for x
  proof -
    have "top \<le> x ^ o * top \<squnion> x"
      by (metis dual_dual dual_neg_top mbta_dual.top_right_mult_increasing sup_commute sup_left_isotone)
    thus ?thesis
      by (simp add: sup_comp neg_assume_def)
  qed
  using assume_bot dual_comp neg_assume_def sup_comp mult_assoc apply simp
  apply simp
  apply simp
  apply (simp add: dual_inf dual_comp dual_sup inf_comp sup_comp neg_assume_def sup_inf_distrib2)
  apply (simp add: dual_inf sup_comp neg_assume_def sup.assoc)
  by (simp add: dual_comp dual_sup inf_comp neg_assume_def)

sublocale mbt_algebra < mbta: relative_domain_semiring_split where d = "\<lambda>x . (x * top) \<sqinter> 1" and Z = bot
  apply unfold_locales
  by simp

sublocale mbt_algebra < mbta_dual: relative_domain_semiring_split where d = "\<lambda>x . (x * bot) \<squnion> 1" and less = greater and less_eq = greater_eq and sup = inf and bot = top and Z = top
  apply unfold_locales
  by simp

sublocale mbt_algebra < mbta: diamond_while where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Z = bot
  apply unfold_locales
  apply simp
  apply simp
  apply (rule wpt_def)
  apply simp
  by simp

sublocale mbt_algebra < mbta_dual: box_while where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and top = bot and Z = top
  apply unfold_locales
  apply simp
  apply simp
  apply (metis assume_bot dual_comp mbta_dual.a_mult_d_2 mbta_dual.d_def neg_assume_def wpb_def mult_assoc)
  apply simp
  by simp

sublocale mbt_algebra < mbta_fix: diamond_while where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Z = bot
  apply unfold_locales
  by simp_all

sublocale mbt_algebra < mbta_fix_dual: box_while where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and top = bot and Z = top
  apply unfold_locales
  by simp_all

sublocale mbt_algebra < mbta_pre: box_while where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Z = bot
  apply unfold_locales
  apply (metis dual_comp dual_dual dual_top inf_top_right mbta_dual.mult_right_dist_sup mult_1_left neg_assert_def top_comp wpt_def mult_assoc)
  apply simp
  by simp

sublocale mbt_algebra < mbta_pre_dual: diamond_while where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and top = bot and Z = top
  apply unfold_locales
  apply (simp add: wpb_def)
  apply simp
  by simp

sublocale mbt_algebra < mbta_pre_fix: box_while where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Z = bot
  apply unfold_locales
  by simp_all

sublocale mbt_algebra < mbta_pre_fix_dual: diamond_while where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and top = bot and Z = top
  apply unfold_locales
  by simp_all

sublocale post_mbt_algebra < mbta: pre_post_spec_Hd where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and pre = "\<lambda>x y . wpt (x * y)" and pre_post = "\<lambda>p q . p * post q" and uminus = neg_assert and Hd = "post 1" and Z = bot
  apply unfold_locales
  apply (metis mult.assoc mult.left_neutral post_1)
  apply (metis inf.commute inf_top_right mult.assoc mult.left_neutral post_2)
  apply (metis neg_assertion assertion_disjunctive disjunctiveD)
  subgoal for p x q
  proof
    let ?pt = "neg_assert p"
    let ?qt = "neg_assert q"
    assume "?pt \<le> wpt (x * ?qt)"
    hence "?pt * post ?qt \<le> x * ?qt * top * post ?qt \<sqinter> post ?qt"
      by (metis mbta.mult_left_isotone wpt_def inf_comp mult.left_neutral)
    thus "?pt * post ?qt \<le> x"
      by (smt mbta.top_left_zero mult.assoc post_2 order_trans)
  next
    let ?pt = "neg_assert p"
    let ?qt = "neg_assert q"
    assume "?pt * post ?qt \<le> x"
    thus "?pt \<le> wpt (x * ?qt)"
      by (smt mbta.a_d_closed post_1 mult_assoc mbta.diamond_left_isotone wpt_def)
  qed
  by (simp add: mbta_dual.mult_right_dist_sup)

sublocale post_mbt_algebra < mbta_dual: pre_post_spec_H where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and pre_post = "\<lambda>p q . (p ^ o) * post (q ^ o)" and uminus = neg_assume and bot = top and H = "post 1" and top = bot and Z = top
proof
  fix p x q
  let ?pt = "neg_assume p"
  let ?qt = "neg_assume q"
  show "wpb (x ^ o * ?qt) \<le> ?pt \<longleftrightarrow> ?pt ^ o * post (?qt ^ o) \<le> x"
  proof
    assume "wpb (x ^ o * ?qt) \<le> ?pt"
    hence "?pt ^ o * post (?qt ^ o) \<le> (x * (?qt ^ o) * top \<sqinter> 1) * post (?qt ^ o)"
      by (smt wpb_def dual_le dual_comp dual_dual dual_one dual_sup dual_top mbta.mult_left_isotone)
    thus "?pt ^ o * post (?qt ^ o) \<le> x"
      by (smt inf_comp mult_assoc top_comp mult.left_neutral post_2 order_trans)
  next
    assume 1: "?pt ^ o * post (?qt ^ o) \<le> x"
    have "?pt ^ o = ?pt ^ o * post (?qt ^ o) * (?qt ^ o) * top \<sqinter> 1"
      by (metis assert_iff_assume assertion_prop dual_dual mult_assoc neg_assumption post_1)
    thus "wpb (x ^ o * ?qt) \<le> ?pt"
      using 1 by (smt dual_comp dual_dual dual_le dual_one dual_sup dual_top wpb_def mbta.diamond_left_isotone)
  qed
  show "post 1 * top = top"
    by (simp add: mbta.Hd_total)
  have "x * ?qt * bot \<sqinter> (post 1 * neg_assume ?qt) = (x * neg_assume ?qt ^ o * top \<sqinter> post 1) * neg_assume ?qt"
    by (simp add: assume_bot mbta_dual.mult_right_dist_sup mult_assoc)
  also have "... \<le> x * neg_assume ?qt ^ o"
    by (smt assumption_assertion_absorb dual_comp dual_dual mbta.mult_left_isotone mult.right_neutral mult_assoc neg_assumption post_2)
  also have "... \<le> x"
    by (metis dual_comp dual_dual dual_le mbta.mult_left_sub_dist_sup_left mult.right_neutral neg_assume_def sup.commute)
  finally show "x * ?qt * bot \<sqinter> (post 1 * neg_assume ?qt) \<le> x"
    .
qed

sublocale post_mbt_algebra < mbta_pre: pre_post_spec_H where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and pre = "\<lambda>x y . wpt (x ^ o * y)" and pre_post = "\<lambda>p q . p ^ o * (post q ^ o)" and uminus = neg_assert and H = "post 1 ^ o" and Z = bot
proof
  fix p x q
  let ?pt = "neg_assert p"
  let ?qt = "neg_assert q"
  show "?pt \<le> wpt (x ^ o * ?qt) \<longleftrightarrow> x \<le> ?pt ^ o * (post ?qt ^ o)"
  proof
    assume "?pt \<le> wpt (x ^ o * ?qt)"
    hence "?pt * post ?qt \<le> (x ^ o * ?qt * top \<sqinter> 1) * post ?qt"
      by (simp add: mbta_dual.mult_left_isotone wpt_def)
    also have "... \<le> x ^ o"
      using mbta.pre_pre_post wpt_def by auto
    finally show "x \<le> ?pt ^ o * (post ?qt ^ o)"
      by (metis dual_le dual_comp dual_dual)
  next
    assume "x \<le> ?pt ^ o * (post ?qt ^ o)"
    hence "x * ?qt ^ o * bot \<squnion> 1 \<le> (?pt * post ?qt * ?qt * top \<sqinter> 1) ^ o"
      by (smt (z3) inf.absorb_iff1 sup_inf_distrib2 dual_comp dual_inf dual_one dual_top mbta.mult_left_isotone)
    also have "... = ?pt ^ o"
      by (simp add: mbta.diamond_a_export post_1)
    finally show "?pt \<le> wpt (x ^ o * ?qt)"
      by (smt dual_comp dual_dual dual_le dual_neg_top dual_one dual_sup dual_top wpt_def)
  qed
  show "post 1 ^ o * bot = bot"
    by (metis dual_comp dual_top mbta.Hd_total)
  have "x ^ o * ?qt ^ o * bot \<sqinter> (post 1 * neg_assert ?qt ^ o) \<le> x ^ o * neg_assert ?qt * neg_assert ?qt ^ o"
    by (smt (verit, del_insts) bot_comp inf.commute inf_comp inf_top_left mbta.mult_left_isotone mult.left_neutral mult_assoc neg_assert_def post_2)
  also have "... \<le> x ^ o"
    by (smt assert_iff_assume assumption_assertion_absorb dual_comp dual_dual le_comp mbta.a_below_one mult_assoc neg_assertion mult_1_right)
  finally show "x \<le> x * ?qt * top \<squnion> post 1 ^ o * neg_assert ?qt"
    by (smt dual_comp dual_dual dual_inf dual_le dual_top)
qed

sublocale post_mbt_algebra < mbta_pre_dual: pre_post_spec_Hd where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and pre_post = "\<lambda>p q . p * (post (q ^ o) ^ o)" and uminus = neg_assume and bot = top and Hd = "post 1 ^ o" and top = bot and Z = top
  apply unfold_locales
  apply (simp add: mbta_pre.H_zero_2)
  apply (simp add: mbta_pre.H_greatest_finite)
  apply (metis (no_types, lifting) dual_comp dual_dual dual_inf dual_top mbta_dual.mult_L_circ_mult mult_1_right neg_assume_def sup_commute sup_inf_distrib2)
  subgoal for p x q
  proof
    let ?pt = "neg_assume p"
    let ?qt = "neg_assume q"
    assume "wpb (x * ?qt) \<le> ?pt"
    hence "?pt ^ o * post (?qt ^ o) \<le> (x ^ o * ?qt ^ o * top \<sqinter> 1) * post (?qt ^ o)"
      by (smt dual_comp dual_dual dual_le dual_one dual_sup dual_top le_comp_right wpb_def)
    also have "... \<le> x ^ o"
      using mbta_dual.mult_right_dist_sup post_2 by force
    finally show "x \<le> ?pt * post (?qt ^ o) ^ o"
      by (smt dual_comp dual_dual dual_le)
  next
    let ?pt = "neg_assume p"
    let ?qt = "neg_assume q"
    assume "x \<le> ?pt * post (?qt ^ o) ^ o"
    thus "wpb (x * ?qt) \<le> ?pt"
      by (metis dual_comp dual_dual dual_le mbta_dual.pre_post_galois)
  qed
  by (simp add: sup_comp)

sublocale post_mbt_algebra < mbta_dual: pre_post_spec_whiledo where ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and pre_post = "\<lambda>p q . (p ^ o) * post (q ^ o)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and top = bot ..

sublocale post_mbt_algebra < mbta_fix_dual: pre_post_spec_whiledo where ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and pre_post = "\<lambda>p q . (p ^ o) * post (q ^ o)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and top = bot ..

sublocale post_mbt_algebra < mbta_pre: pre_post_spec_whiledo where ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and pre_post = "\<lambda>p q . p ^ o * (post q ^ o)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" ..

sublocale post_mbt_algebra < mbta_pre_fix: pre_post_spec_whiledo where ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and pre_post = "\<lambda>p q . p ^ o * (post q ^ o)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" ..

sublocale post_mbt_algebra < mbta_dual: pre_post_L where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and pre_post = "\<lambda>p q . (p ^ o) * post (q ^ o)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and L = bot and top = bot and Z = top
  apply unfold_locales
  by simp

sublocale post_mbt_algebra < mbta_fix_dual: pre_post_L where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and pre_post = "\<lambda>p q . (p ^ o) * post (q ^ o)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and L = top and top = bot and Z = top
  apply unfold_locales
  by simp

sublocale post_mbt_algebra < mbta_pre: pre_post_L where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and pre_post = "\<lambda>p q . p ^ o * (post q ^ o)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and L = bot and Z = bot
  apply unfold_locales
  by simp

sublocale post_mbt_algebra < mbta_pre_fix: pre_post_L where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and pre_post = "\<lambda>p q . p ^ o * (post q ^ o)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and L = top and Z = bot
  apply unfold_locales
  by simp

sublocale complete_mbt_algebra < mbta: complete_tests where uminus = neg_assert
  apply unfold_locales
  apply (smt mbta.test_set_def neg_assertion subset_eq Sup_assertion assertion_neg_assert)
  apply (simp add: Sup_upper)
  by (simp add: Sup_least)

sublocale complete_mbt_algebra < mbta_dual: complete_tests where less = greater and less_eq = greater_eq and sup = inf and uminus = neg_assume and bot = top and Inf = Sup and Sup = Inf
  apply unfold_locales
  apply (smt mbta_dual.test_set_def neg_assumption subset_eq Inf_assumption assumption_neg_assume)
  apply (simp add: Inf_lower)
  by (simp add: Inf_greatest)

sublocale complete_mbt_algebra < mbta: complete_antidomain_semiring where d = "\<lambda>x . (x * top) \<sqinter> 1" and uminus = neg_assert and Z = bot
proof
  fix f :: "nat \<Rightarrow> 'a"
  let ?F = "dual ` {f n | n . True}"
  show "ascending_chain f \<longrightarrow> neg_assert (complete_tests.Sum Sup f) = complete_tests.Prod Inf (\<lambda>n. neg_assert (f n))"
  proof
    have "neg_assert (complete_tests.Sum Sup f) = 1 \<sqinter> (\<Sqinter>x\<in>?F . x * bot)"
      using Inf_comp dual_Sup mbta.Sum_def neg_assert_def inf_commute by auto
    also have "... = (\<Sqinter>x\<in>?F . 1 \<sqinter> x * bot)"
      apply (subst inf_Inf)
      apply blast
      by (simp add: image_image)
    also have "... = \<Sqinter>{f n ^ o * bot \<sqinter> 1 | n . True}"
      apply (rule arg_cong[where f="Inf"])
      using inf_commute by auto
    also have "... = complete_tests.Prod Inf (\<lambda>n. neg_assert (f n))"
      using mbta.Prod_def neg_assert_def by auto
    finally show "neg_assert (complete_tests.Sum Sup f) = complete_tests.Prod Inf (\<lambda>n. neg_assert (f n))"
      .
  qed
  show "descending_chain f \<longrightarrow> neg_assert (complete_tests.Prod Inf f) = complete_tests.Sum Sup (\<lambda>n. neg_assert (f n))"
  proof
    have "neg_assert (complete_tests.Prod Inf f) = 1 \<sqinter> (\<Squnion>x\<in>?F . x * bot)"
      using Sup_comp dual_Inf mbta.Prod_def neg_assert_def inf_commute by auto
    also have "... = (\<Squnion>x\<in>?F . 1 \<sqinter> x * bot)"
      by (simp add: inf_Sup image_image)
    also have "... = \<Squnion>{f n ^ o * bot \<sqinter> 1 |n. True}"
      apply (rule arg_cong[where f="Sup"])
      using inf_commute by auto
    also have "... = complete_tests.Sum Sup (\<lambda>n. neg_assert (f n))"
      using mbta.Sum_def neg_assert_def by auto
    finally show "neg_assert (complete_tests.Prod Inf f) = complete_tests.Sum Sup (\<lambda>n. neg_assert (f n))"
      .
  qed
qed

sublocale complete_mbt_algebra < mbta_dual: complete_antidomain_semiring where d = "\<lambda>x . (x * bot) \<squnion> 1" and less = greater and less_eq = greater_eq and sup = inf and uminus = neg_assume and bot = top and Inf = Sup and Sup = Inf and Z = top
proof
  fix f :: "nat \<Rightarrow> 'a"
  let ?F = "dual ` {f n | n . True}"
  show "ord.ascending_chain greater_eq f \<longrightarrow> neg_assume (complete_tests.Sum Inf f) = complete_tests.Prod Sup (\<lambda>n. neg_assume (f n))"
  proof
    have "neg_assume (complete_tests.Sum Inf f) = 1 \<squnion> (\<Squnion>x\<in>?F . x * top)"
      using mbta_dual.Sum_def neg_assume_def dual_Inf Sup_comp sup_commute by auto
    also have "... = (\<Squnion>x\<in>?F . 1 \<squnion> x * top)"
      apply (subst sup_Sup)
      apply blast
      by (simp add: image_image)
    also have "... = \<Squnion>{f n ^ o * top \<squnion> 1 | n . True}"
      apply (rule arg_cong[where f="Sup"])
      using sup_commute by auto
    also have "... = complete_tests.Prod Sup (\<lambda>n. neg_assume (f n))"
      using mbta_dual.Prod_def neg_assume_def by auto
    finally show "neg_assume (complete_tests.Sum Inf f) = complete_tests.Prod Sup (\<lambda>n. neg_assume (f n))"
      .
  qed
  show "ord.descending_chain greater_eq f \<longrightarrow> neg_assume (complete_tests.Prod Sup f) = complete_tests.Sum Inf (\<lambda>n. neg_assume (f n))"
  proof
    have "neg_assume (complete_tests.Prod Sup f) = 1 \<squnion> (\<Sqinter>x\<in>?F . x * top)"
      using mbta_dual.Prod_def neg_assume_def dual_Inf dual_Sup Inf_comp sup_commute by auto
    also have "... = (\<Sqinter>x\<in>?F . 1 \<squnion> x * top)"
      by (simp add: sup_Inf image_image)
    also have "... = \<Sqinter>{f n ^ o * top \<squnion> 1 |n. True}"
      apply (rule arg_cong[where f="Inf"])
      using sup_commute by auto
    also have "... = complete_tests.Sum Inf (\<lambda>n. neg_assume (f n))"
      using mbta_dual.Sum_def neg_assume_def by auto
    finally show "neg_assume (complete_tests.Prod Sup f) = complete_tests.Sum Inf (\<lambda>n. neg_assume (f n))"
      .
  qed
qed

sublocale complete_mbt_algebra < mbta: diamond_while_program where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Atomic_program = Continuous and Atomic_test = assertion and Z = bot
  apply unfold_locales
  apply (simp add: one_continuous)
  by simp_all

sublocale complete_mbt_algebra < mbta_dual: box_while_program where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and Atomic_program = Continuous and Atomic_test = assumption and top = bot and Z = top
  apply unfold_locales
  apply (simp add: one_continuous)
  by simp_all

sublocale complete_mbt_algebra < mbta_fix: diamond_while_program where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Atomic_program = Co_continuous and Atomic_test = assertion and Z = bot
  apply unfold_locales
  apply (simp add: one_co_continuous)
  by simp_all

sublocale complete_mbt_algebra < mbta_fix_dual: box_while_program where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and Atomic_program = Co_continuous and Atomic_test = assumption and top = bot and Z = top
  apply unfold_locales
  apply (simp add: one_co_continuous)
  by simp_all

sublocale complete_mbt_algebra < mbta_pre: box_while_program where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Atomic_program = Continuous and Atomic_test = assertion and Z = bot ..

sublocale complete_mbt_algebra < mbta_pre_dual: diamond_while_program where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and Atomic_program = Continuous and Atomic_test = assumption and top = bot and Z = top ..

sublocale complete_mbt_algebra < mbta_pre_fix: box_while_program where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Atomic_program = Co_continuous and Atomic_test = assertion and Z = bot ..

sublocale complete_mbt_algebra < mbta_pre_fix_dual: diamond_while_program where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and Atomic_program = Co_continuous and Atomic_test = assumption and top = bot and Z = top ..

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta: diamond_hoare_sound where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x * y)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Atomic_program = Continuous and Atomic_test = assertion and Z = bot
  apply unfold_locales
  by (simp add: mbta.aL_one_circ mbta.star_one)

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_dual: box_hoare_sound where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and Atomic_program = Continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot and Z = top
  apply unfold_locales
  using mbta.top_greatest mbta.vector_bot_closed mbta_dual.aL_one_circ mbta_dual.a_top omega_one top_comp by auto

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_fix: diamond_hoare_sound_2 where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x * y)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Atomic_program = Co_continuous and Atomic_test = assertion and Z = bot
proof (unfold_locales, rule impI)
  fix p q x
  let ?pt = "neg_assert p"
  let ?qt = "neg_assert q"
  assume "neg_assert ?pt * ?qt \<le> x * ?qt * top \<sqinter> 1"
  hence "?qt * top \<le> x ^ \<mho> * ?pt * top"
    by (smt mbta.Omega_induct mbta.d_def mbta.d_mult_top mbta.mult_left_isotone mbta.shunting_top_1 mult.assoc)
  thus "mbta_fix.aL * ?qt \<le> x ^ \<mho> * ?pt * top \<sqinter> 1"
    by (smt (z3) inf.absorb_iff1 inf.sup_monoid.add_commute inf_comp inf_le2 inf_left_commute inf_top_left mbta_fix.aL_one_circ mbta_pre_dual.top_left_zero mult_1_left neg_assert_def mult.assoc)
qed

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_fix_dual: box_hoare_sound where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and Atomic_program = Co_continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot and Z = top
  apply unfold_locales
  by (simp add: mbta_dual.star_one mbta_fix_dual.aL_one_circ)

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_pre: box_hoare_sound where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Atomic_program = Continuous and Atomic_test = assertion and Z = bot
  apply unfold_locales
  using mbta.star_one mbta_pre.aL_one_circ by auto

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_pre_dual: diamond_hoare_sound_2 where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and Atomic_program = Continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot and Z = top
proof (unfold_locales, rule impI)
  fix p q x
  let ?pt = "neg_assume p"
  let ?qt = "neg_assume q"
  assume "x * ?qt * bot \<squnion> 1 \<le> neg_assume ?pt * ?qt"
  hence "x * ?qt * bot \<sqinter> ?pt \<le> ?qt"
    by (smt (z3) inf.absorb_iff1 inf_left_commute inf_commute inf_le1 le_supE mbta_dual.a_compl_intro mbta_dual.d_def order_trans)
  hence "(x * ?qt * bot \<sqinter> ?pt) * bot \<le> ?qt * bot"
    using mbta.mult_left_isotone by blast
  hence "x ^ \<omega> * ?pt * bot \<squnion> 1 \<le> ?qt"
    by (smt bot_comp inf_comp sup_left_isotone mbta_dual.a_d_closed mult_assoc omega_least)
  thus "x ^ \<omega> * ?pt * bot \<squnion> 1 \<le> mbta_pre_dual.aL * ?qt"
    by (simp add: mbta_pre_dual.aL_one_circ)
qed

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_pre_fix: box_hoare_sound where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Atomic_program = Co_continuous and Atomic_test = assertion and Z = bot
  apply unfold_locales
  using mbta.Omega_one mbta_pre_fix.aL_def by auto

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_pre_fix_dual: diamond_hoare_sound where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and Atomic_program = Co_continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot and Z = top
  apply unfold_locales
  by (simp add: mbta_dual.star_one mbta_pre_fix_dual.aL_one_circ)

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta: diamond_hoare_valid where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_star and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and hoare_triple = "\<lambda>p x q . p \<le> wpt(x * q)" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x * y)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Atomic_program = Continuous and Atomic_test = assertion and Z = bot
  apply unfold_locales
  apply (simp add: mbta.aL_zero)
  using mbta.aL_zero apply blast
  subgoal for x t
  proof
    assume 1: "x \<in> while_program.While_program (*) neg_assert Continuous assertion (\<lambda>p x . (p * x) ^ \<otimes> * neg_assert p) (\<lambda>x p y . p * x \<squnion> neg_assert p * y) \<and> ascending_chain t \<and> tests.test_seq neg_assert t"
    have "x \<in> Continuous"
      apply (induct x rule: while_program.While_program.induct[where pre="\<lambda>x y . wpt (x * y)" and while="\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p"])
      apply unfold_locales
      using 1 apply blast
      apply simp
      using mult_continuous apply blast
      apply (metis assertion_continuous mbta.test_expression_test mult_continuous neg_assertion sup_continuous)
      by (metis assertion_continuous dual_star_continuous mbta.test_expression_test mult_continuous neg_assertion)
    thus "x * complete_tests.Sum Sup t = complete_tests.Sum Sup (\<lambda>n. x * t n)"
      using 1 by (smt continuous_dist_ascending_chain SUP_cong mbta.Sum_range)
  qed
  using wpt_def by auto

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_dual: box_hoare_valid where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = omega and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and hoare_triple = "\<lambda>p x q . wpb(x ^ o * q) \<le> p" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and Atomic_program = Continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot and Z = top
proof
  fix p x q t
  show "neg_assume q \<le> neg_assume p * neg_assume (x * neg_assume (neg_assume q)) \<longrightarrow> neg_assume q \<sqinter> whiledo.aL (\<lambda>p x. (p * x) ^ \<omega> * neg_assume p) (\<lambda>x y. wpb (x ^ o * y)) 1 \<le> neg_assume (x ^ \<omega> * neg_assume (neg_assume p))"
  proof
    let ?pt = "neg_assume p"
    let ?qt = "neg_assume q"
    assume "?qt \<le> ?pt * neg_assume (x * neg_assume ?qt)"
    also have "... \<le> x ^ o * ?qt \<squnion> ?pt"
      by (smt assumption_sup_comp_eq sup_left_isotone mbta.zero_right_mult_decreasing mbta_dual.pre_def neg_assume_def neg_assumption sup.commute sup.left_commute sup.left_idem wpb_def)
    finally show "?qt \<sqinter> mbta_dual.aL \<le> neg_assume (x ^ \<omega> * neg_assume ?pt)"
      by (smt dual_dual dual_omega_def dual_omega_greatest le_infI1 mbta_dual.a_d_closed mbta_dual.d_isotone mbta_dual.pre_def wpb_def)
  qed
  show "whiledo.aL (\<lambda>p x. (p * x) ^ \<omega> * neg_assume p) (\<lambda>x y. wpb (x ^ o * y)) 1 = top \<or> whiledo.aL (\<lambda>p x. (p * x) ^ \<omega> * neg_assume p) (\<lambda>x y. wpb (x ^ o * y)) 1 = 1"
    using mbta_dual.L_def mbta_dual.aL_one_circ mbta_dual.a_top by auto
  show "x \<in> while_program.While_program (*) neg_assume Continuous assumption (\<lambda>p x. (p * x) ^ \<omega> * neg_assume p) (\<lambda>x p y. p * x \<sqinter> neg_assume p * y) \<and> ord.descending_chain (\<lambda>x y. y \<le> x) t \<and> tests.test_seq neg_assume t \<longrightarrow> x * complete_tests.Prod Sup t = complete_tests.Prod Sup (\<lambda>n. x * t n)"
  proof
    assume 1: "x \<in> while_program.While_program (*) neg_assume Continuous assumption (\<lambda>p x . (p * x) ^ \<omega> * neg_assume p) (\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)) \<and> ord.descending_chain greater_eq t \<and> tests.test_seq neg_assume t"
    have "x \<in> Continuous"
      apply (induct x rule: while_program.While_program.induct[where pre="\<lambda>x y . wpb (x ^ o * y)" and while="\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p"])
      apply unfold_locales
      using 1 apply blast
      apply simp
      apply (simp add: mult_continuous)
      apply (metis assumption_continuous mbta_dual.test_expression_test mult_continuous neg_assumption inf_continuous)
      by (metis assumption_continuous omega_continuous mbta_dual.test_expression_test mult_continuous neg_assumption)
    thus "x * complete_tests.Prod Sup t = complete_tests.Prod Sup (\<lambda>n. x * t n)"
      using 1 by (smt ord.descending_chain_def ascending_chain_def continuous_dist_ascending_chain SUP_cong mbta_dual.Prod_range)
  qed
  show "(wpb (x ^ o * q) \<le> p) = (neg_assume (x * neg_assume q) \<le> p)"
    by (simp add: mbta_dual.pre_def)
qed

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_pre_fix_dual: diamond_hoare_valid where box = "\<lambda>x y . neg_assume (x * neg_assume y)" and circ = star and d = "\<lambda>x . (x * bot) \<squnion> 1" and diamond = "\<lambda>x y . (x * y * bot) \<squnion> 1" and hoare_triple = "\<lambda>p x q . wpb(x * q) \<le> p" and ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x * y)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and Atomic_program = Co_continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot and Z = top
  apply unfold_locales
  using mbta_dual.star_one mbta_pre_fix_dual.aL_one_circ apply simp
  using mbta_pre_fix_dual.aL_zero apply blast
  subgoal for x t
  proof
    assume 1: "x \<in> while_program.While_program (*) neg_assume Co_continuous assumption (\<lambda>p x . (p * x) ^ * * neg_assume p) (\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)) \<and> ord.ascending_chain greater_eq t \<and> tests.test_seq neg_assume t"
    have "x \<in> Co_continuous"
      apply (induct x rule: while_program.While_program.induct[where pre="\<lambda>x y . wpb (x * y)" and while="\<lambda>p x . ((p * x) ^ * ) * neg_assume p"])
      apply unfold_locales
      using 1 apply blast
      apply simp
      apply (simp add: mult_co_continuous)
      apply (metis assumption_co_continuous mbta_dual.test_expression_test mult_co_continuous neg_assumption inf_co_continuous)
      by (metis assumption_co_continuous star_co_continuous mbta_dual.test_expression_test mult_co_continuous neg_assumption)
    thus "x * complete_tests.Sum Inf t = complete_tests.Sum Inf (\<lambda>n. x * t n)"
      using 1 by (smt descending_chain_def ord.ascending_chain_def co_continuous_dist_descending_chain INF_cong mbta_dual.Sum_range)
  qed
  using wpb_def by auto

text \<open>Theorem 52\<close>

sublocale complete_mbt_algebra < mbta_pre_fix: box_hoare_valid where box = "\<lambda>x y . neg_assert (x * neg_assert y)" and circ = dual_omega and d = "\<lambda>x . (x * top) \<sqinter> 1" and diamond = "\<lambda>x y . (x * y * top) \<sqinter> 1" and hoare_triple = "\<lambda>p x q . p \<le> wpt(x ^ o * q)" and ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and star = dual_star and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Atomic_program = Co_continuous and Atomic_test = assertion and Z = bot
proof
  fix p x q t
  show "neg_assert p * neg_assert (x * neg_assert (neg_assert q)) \<le> neg_assert q \<longrightarrow> neg_assert (x ^ \<mho> * neg_assert (neg_assert p)) \<le> neg_assert q \<squnion> whiledo.aL (\<lambda>p x. (p * x) ^ \<mho> * neg_assert p) (\<lambda>x y. wpt (x ^ o * y)) 1"
  proof
    let ?pt = "neg_assert p"
    let ?qt = "neg_assert q"
    assume 1: "?pt * neg_assert (x * neg_assert ?qt) \<le> ?qt"
    have "x ^ o * ?qt \<sqinter> ?pt \<le> ?pt * neg_assert (x * neg_assert ?qt)"
      by (smt (z3) inf.boundedI inf.cobounded1 inf.sup_monoid.add_commute le_infI2 inf_comp mbta.tests_dual.sub_commutative mbta.top_right_mult_increasing mbta_pre.pre_def mult.left_neutral mult_assoc top_comp wpt_def)
    also have "... \<le> ?qt"
      using 1 by simp
    finally have "(x ^ o) ^ \<omega> * ?pt * top \<le> ?qt * top"
      using mbta.mult_left_isotone omega_least by blast
    hence "neg_assert (x ^ \<mho> * neg_assert ?pt) \<le> ?qt"
      by (smt dual_omega_def inf_mono mbta.d_a_closed mbta.d_def mbta_pre.pre_def order_refl wpt_def mbta.a_d_closed)
    thus "neg_assert (x ^ \<mho> * neg_assert ?pt) \<le> ?qt \<squnion> mbta_pre_fix.aL"
      using le_supI1 by blast
  qed
  show "whiledo.aL (\<lambda>p x. (p * x) ^ \<mho> * neg_assert p) (\<lambda>x y. wpt (x ^ o * y)) 1 = bot \<or> whiledo.aL (\<lambda>p x. (p * x) ^ \<mho> * neg_assert p) (\<lambda>x y. wpt (x ^ o * y)) 1 = 1"
    using mbta.Omega_one mbta.a_top mbta_dual.vector_bot_closed mbta_pre_fix.aL_one_circ by auto
  show "x \<in> while_program.While_program (*) neg_assert Co_continuous assertion (\<lambda>p x. (p * x) ^ \<mho> * neg_assert p) (\<lambda>x p y. p * x \<squnion> neg_assert p * y) \<and> descending_chain t \<and> tests.test_seq neg_assert t \<longrightarrow> x * complete_tests.Prod Inf t = complete_tests.Prod Inf (\<lambda>n. x * t n)"
  proof
    assume 1: "x \<in> while_program.While_program (*) neg_assert Co_continuous assertion (\<lambda>p x . (p * x) ^ \<mho> * neg_assert p) (\<lambda>x p y . p * x \<squnion> neg_assert p * y) \<and> descending_chain t \<and> tests.test_seq neg_assert t"
    have "x \<in> Co_continuous"
      apply (induct x rule: while_program.While_program.induct[where pre="\<lambda>x y . wpt (x ^ o * y)" and while="\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p"])
      apply unfold_locales
      using 1 apply blast
      apply simp
      apply (simp add: mult_co_continuous)
      apply (metis assertion_co_continuous mbta.test_expression_test mult_co_continuous neg_assertion sup_co_continuous)
      by (metis assertion_co_continuous dual_omega_co_continuous mbta.test_expression_test mult_co_continuous neg_assertion)
    thus "x * complete_tests.Prod Inf t = complete_tests.Prod Inf (\<lambda>n. x * t n)"
      using 1 by (smt descending_chain_def co_continuous_dist_descending_chain INF_cong mbta.Prod_range)
  qed
  show "(p \<le> wpt (x ^ o * q)) = (p \<le> neg_assert (x * neg_assert q))"
    by (simp add: mbta_pre.pre_def)
qed

sublocale complete_mbt_algebra < mbta_dual: pre_post_spec_hoare where ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and pre_post = "\<lambda>p q . (p ^ o) * post (q ^ o)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ \<omega>) * neg_assume p" and bot = top and Atomic_program = Continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot ..

sublocale complete_mbt_algebra < mbta_fix_dual: pre_post_spec_hoare where ite = "\<lambda>x p y . (p * x) \<sqinter> (neg_assume p * y)" and less = greater and less_eq = greater_eq and sup = inf and pre = "\<lambda>x y . wpb (x ^ o * y)" and pre_post = "\<lambda>p q . (p ^ o) * post (q ^ o)" and uminus = neg_assume and while = "\<lambda>p x . ((p * x) ^ *) * neg_assume p" and bot = top and Atomic_program = Co_continuous and Atomic_test = assumption and Inf = Sup and Sup = Inf and top = bot ..

sublocale complete_mbt_algebra < mbta_pre: pre_post_spec_hoare where ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and pre_post = "\<lambda>p q . p ^ o * (post q ^ o)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<otimes>) * neg_assert p" and Atomic_program = Continuous and Atomic_test = assertion ..

sublocale complete_mbt_algebra < mbta_pre_fix: pre_post_spec_hoare where ite = "\<lambda>x p y . (p * x) \<squnion> (neg_assert p * y)" and pre = "\<lambda>x y . wpt (x ^ o * y)" and pre_post = "\<lambda>p q . p ^ o * (post q ^ o)" and uminus = neg_assert and while = "\<lambda>p x . ((p * x) ^ \<mho>) * neg_assert p" and Atomic_program = Co_continuous and Atomic_test = assertion ..

end

