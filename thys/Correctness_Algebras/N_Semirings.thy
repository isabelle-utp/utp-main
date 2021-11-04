(* Title:      N-Semirings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>N-Semirings\<close>

theory N_Semirings

imports Test_Iterings Omega_Algebras

begin

class n_semiring = bounded_idempotent_left_zero_semiring + n + L +
  assumes n_bot         : "n(bot) = bot"
  assumes n_top         : "n(top) = 1"
  assumes n_dist_sup    : "n(x \<squnion> y) = n(x) \<squnion> n(y)"
  assumes n_export      : "n(n(x) * y) = n(x) * n(y)"
  assumes n_sub_mult_bot: "n(x) = n(x * bot) * n(x)"
  assumes n_L_split     : "x * n(y) * L = x * bot \<squnion> n(x * y) * L"
  assumes n_split       : "x \<le> x * bot \<squnion> n(x * L) * top"
begin

lemma n_sub_one:
  "n(x) \<le> 1"
  by (metis sup_left_top sup_ge2 n_dist_sup n_top)

text \<open>Theorem 15\<close>

lemma n_isotone:
  "x \<le> y \<Longrightarrow> n(x) \<le> n(y)"
  by (metis le_iff_sup n_dist_sup)

lemma n_mult_idempotent:
  "n(x) * n(x) = n(x)"
  by (metis mult_assoc mult_1_right n_export n_sub_mult_bot n_top)

text \<open>Theorem 15.3\<close>

lemma n_mult_bot:
  "n(x) = n(x * bot)"
  by (metis sup_commute sup_left_top sup_bot_right mult_left_dist_sup mult_1_right n_dist_sup n_sub_mult_bot n_top)

lemma n_mult_left_upper_bound:
  "n(x) \<le> n(x * y)"
  by (metis mult_right_isotone n_isotone n_mult_bot bot_least)

lemma n_mult_right_bot:
  "n(x) * bot = bot"
  by (metis sup_left_top sup_bot_left mult_left_one mult_1_right n_export n_dist_sup n_sub_mult_bot n_top n_bot)

text \<open>Theorem 15.9\<close>

lemma n_mult_n:
  "n(x * n(y)) = n(x)"
  by (metis mult_assoc n_mult_right_bot n_mult_bot)

lemma n_mult_left_absorb_sup:
  "n(x) * (n(x) \<squnion> n(y)) = n(x)"
  by (metis sup_left_top mult_left_dist_sup mult_1_right n_dist_sup n_mult_idempotent n_top)

lemma n_mult_right_absorb_sup:
  "(n(x) \<squnion> n(y)) * n(y) = n(y)"
  by (metis sup_commute sup_left_top mult_left_one mult_right_dist_sup n_dist_sup n_mult_idempotent n_top)

lemma n_sup_left_absorb_mult:
  "n(x) \<squnion> n(x) * n(y) = n(x)"
  using mult_left_dist_sup n_mult_idempotent n_mult_left_absorb_sup by auto

lemma n_sup_right_absorb_mult:
  "n(x) * n(y) \<squnion> n(y) = n(y)"
  using mult_right_dist_sup n_mult_idempotent n_mult_right_absorb_sup by auto

lemma n_mult_commutative:
  "n(x) * n(y) = n(y) * n(x)"
  by (smt sup_commute mult_left_dist_sup mult_right_dist_sup n_sup_left_absorb_mult n_sup_right_absorb_mult n_export n_mult_idempotent)

lemma n_sup_left_dist_mult:
  "n(x) \<squnion> n(y) * n(z) = (n(x) \<squnion> n(y)) * (n(x) \<squnion> n(z))"
  by (metis sup_assoc mult_left_dist_sup mult_right_dist_sup n_sup_right_absorb_mult n_mult_commutative n_mult_left_absorb_sup)

lemma n_sup_right_dist_mult:
  "n(x) * n(y) \<squnion> n(z) = (n(x) \<squnion> n(z)) * (n(y) \<squnion> n(z))"
  by (simp add: sup_commute n_sup_left_dist_mult)

lemma n_order:
  "n(x) \<le> n(y) \<longleftrightarrow> n(x) * n(y) = n(x)"
  by (metis le_iff_sup n_sup_right_absorb_mult n_mult_left_absorb_sup)

lemma n_mult_left_lower_bound:
  "n(x) * n(y) \<le> n(x)"
  by (simp add: sup.orderI n_sup_left_absorb_mult)

lemma n_mult_right_lower_bound:
  "n(x) * n(y) \<le> n(y)"
  by (simp add: le_iff_sup n_sup_right_absorb_mult)

lemma n_mult_least_upper_bound:
  "n(x) \<le> n(y) \<and> n(x) \<le> n(z) \<longleftrightarrow> n(x) \<le> n(y) * n(z)"
  by (metis order.trans mult_left_isotone n_mult_commutative n_mult_right_lower_bound n_order)

lemma n_mult_left_divisibility:
  "n(x) \<le> n(y) \<longleftrightarrow> (\<exists>z . n(x) = n(y) * n(z))"
  by (metis n_mult_commutative n_mult_left_lower_bound n_order)

lemma n_mult_right_divisibility:
  "n(x) \<le> n(y) \<longleftrightarrow> (\<exists>z . n(x) = n(z) * n(y))"
  by (simp add: n_mult_commutative n_mult_left_divisibility)

text \<open>Theorem 15.1\<close>

lemma n_one:
  "n(1) = bot"
  by (metis mult_left_one n_mult_bot n_bot)

lemma n_split_equal:
  "x \<squnion> n(x * L) * top = x * bot \<squnion> n(x * L) * top"
  using n_split order_trans sup.cobounded1 sup_same_context zero_right_mult_decreasing by blast

lemma n_split_top:
  "x * top \<le> x * bot \<squnion> n(x * L) * top"
  by (metis mult_left_isotone n_split vector_bot_closed vector_mult_closed vector_sup_closed vector_top_closed)

text \<open>Theorem 15.2\<close>

lemma n_L:
  "n(L) = 1"
  by (metis sup_bot_left order.antisym mult_left_one n_export n_isotone n_mult_commutative n_split_top n_sub_one n_top)

text \<open>Theorem 15.5\<close>

lemma n_split_L:
  "x * L = x * bot \<squnion> n(x * L) * L"
  by (metis mult_1_right n_L n_L_split)

lemma n_n_L:
  "n(n(x) * L) = n(x)"
  by (simp add: n_export n_L)

lemma n_L_decreasing:
  "n(x) * L \<le> x"
  by (metis mult_left_zero n_L_split order_trans sup.orderI zero_right_mult_decreasing mult_assoc n_mult_bot)

text \<open>Theorem 15.10\<close>

lemma n_galois:
  "n(x) \<le> n(y) \<longleftrightarrow> n(x) * L \<le> y"
  by (metis order.trans mult_left_isotone n_L_decreasing n_isotone n_n_L)

text \<open>Theorem 15.6\<close>

lemma split_L:
  "x * L \<le> x * bot \<squnion> L"
  by (metis sup_commute sup_left_isotone n_galois n_L n_split_L n_sub_one)

text \<open>Theorem 15.7\<close>

lemma L_left_zero:
  "L * x = L"
  by (metis order.antisym mult.left_neutral mult_left_zero zero_right_mult_decreasing n_L n_L_decreasing n_mult_bot mult.assoc)

text \<open>Theorem 15.8\<close>

lemma n_mult:
  "n(x * n(y) * L) = n(x * y)"
  using n_L_split n_dist_sup sup.absorb2 n_mult_left_upper_bound n_mult_bot n_n_L by auto

lemma n_mult_top:
  "n(x * n(y) * top) = n(x * y)"
  by (metis mult_1_right n_mult n_top)

text \<open>Theorem 15.4\<close>

lemma n_top_L:
  "n(x * top) = n(x * L)"
  by (metis mult_1_right n_L n_mult_top)

lemma n_top_split:
  "x * n(y) * top \<le> x * bot \<squnion> n(x * y) * top"
  by (metis mult_assoc n_mult n_mult_right_bot n_split_top)

lemma n_mult_right_upper_bound:
  "n(x * y) \<le> n(z) \<longleftrightarrow> n(x) \<le> n(z) \<and> x * n(y) * L \<le> x * bot \<squnion> n(z) * L"
  apply (rule iffI)
  apply (metis sup_right_isotone order.eq_iff mult_isotone n_L_split n_mult_left_upper_bound order_trans)
  by (smt (verit, ccfv_threshold) n_dist_sup n_export sup.absorb_iff2 n_mult n_mult_commutative n_mult_bot n_n_L)

lemma n_preserves_equation:
  "n(y) * x \<le> x * n(y) \<longleftrightarrow> n(y) * x = n(y) * x * n(y)"
  using eq_refl test_preserves_equation n_mult_idempotent n_sub_one by auto

definition ni :: "'a \<Rightarrow> 'a"
  where "ni x = n(x) * L"

lemma ni_bot:
  "ni(bot) = bot"
  by (simp add: n_bot ni_def)

lemma ni_one:
  "ni(1) = bot"
  by (simp add: n_one ni_def)

lemma ni_L:
  "ni(L) = L"
  by (simp add: n_L ni_def)

lemma ni_top:
  "ni(top) = L"
  by (simp add: n_top ni_def)

lemma ni_dist_sup:
  "ni(x \<squnion> y) = ni(x) \<squnion> ni(y)"
  by (simp add: mult_right_dist_sup n_dist_sup ni_def)

lemma ni_mult_bot:
  "ni(x) = ni(x * bot)"
  using n_mult_bot ni_def by auto

lemma ni_split:
  "x * ni(y) = x * bot \<squnion> ni(x * y)"
  using n_L_split mult_assoc ni_def by auto

lemma ni_decreasing:
  "ni(x) \<le> x"
  by (simp add: n_L_decreasing ni_def)

lemma ni_isotone:
  "x \<le> y \<Longrightarrow> ni(x) \<le> ni(y)"
  using mult_left_isotone n_isotone ni_def by auto

lemma ni_mult_left_upper_bound:
  "ni(x) \<le> ni(x * y)"
  using mult_left_isotone n_mult_left_upper_bound ni_def by force

lemma ni_idempotent:
  "ni(ni(x)) = ni(x)"
  by (simp add: n_n_L ni_def)

lemma ni_below_L:
  "ni(x) \<le> L"
  using n_L n_galois n_sub_one ni_def by auto

lemma ni_left_zero:
  "ni(x) * y = ni(x)"
  by (simp add: L_left_zero mult_assoc ni_def)

lemma ni_split_L:
  "x * L = x * bot \<squnion> ni(x * L)"
  using n_split_L ni_def by auto

lemma ni_top_L:
  "ni(x * top) = ni(x * L)"
  by (simp add: n_top_L ni_def)

lemma ni_galois:
  "ni(x) \<le> ni(y) \<longleftrightarrow> ni(x) \<le> y"
  by (metis n_galois n_n_L ni_def)

lemma ni_mult:
  "ni(x * ni(y)) = ni(x * y)"
  using mult_assoc n_mult ni_def by auto

lemma ni_n_order:
  "ni(x) \<le> ni(y) \<longleftrightarrow> n(x) \<le> n(y)"
  using n_galois ni_def ni_galois by auto

lemma ni_n_equal:
  "ni(x) = ni(y) \<longleftrightarrow> n(x) = n(y)"
  by (metis n_n_L ni_def)

lemma ni_mult_right_upper_bound:
  "ni(x * y) \<le> ni(z) \<longleftrightarrow> ni(x) \<le> ni(z) \<and> x * ni(y) \<le> x * bot \<squnion> ni(z)"
  using mult_assoc n_mult_right_upper_bound ni_def ni_n_order by auto

lemma n_ni:
  "n(ni(x)) = n(x)"
  by (simp add: n_n_L ni_def)

lemma ni_n:
  "ni(n(x)) = bot"
  by (metis n_mult_right_bot ni_mult_bot ni_bot)

lemma ni_n_galois:
  "n(x) \<le> n(y) \<longleftrightarrow> ni(x) \<le> y"
  by (simp add: n_galois ni_def)

lemma n_mult_ni:
  "n(x * ni(y)) = n(x * y)"
  using ni_mult ni_n_equal by auto

lemma ni_mult_n:
  "ni(x * n(y)) = ni(x)"
  by (simp add: n_mult_n ni_def)

lemma ni_export:
  "ni(n(x) * y) = n(x) * ni(y)"
  by (simp add: n_mult_right_bot ni_split)

lemma ni_mult_top:
  "ni(x * n(y) * top) = ni(x * y)"
  by (simp add: n_mult_top ni_def)

lemma ni_n_bot:
  "ni(x) = bot \<longleftrightarrow> n(x) = bot"
  using n_bot ni_n_equal ni_bot by force

lemma ni_n_L:
  "ni(x) = L \<longleftrightarrow> n(x) = 1"
  using n_L ni_L ni_n_equal by force

(* independence of axioms, checked in n_semiring without the respective axiom:
lemma n_bot         : "n(bot) = bot" nitpick [expect=genuine,card=2] oops
lemma n_top         : "n(top) = 1" nitpick [expect=genuine,card=3] oops
lemma n_dist_sup    : "n(x \<squnion> y) = n(x) \<squnion> n(y)" nitpick [expect=genuine,card=5] oops
lemma n_export      : "n(n(x) * y) = n(x) * n(y)" nitpick [expect=genuine,card=6] oops
lemma n_sub_mult_bot: "n(x) = n(x * bot) * n(x)" nitpick [expect=genuine,card=2] oops
lemma n_L_split     : "x * n(y) * L = x * bot \<squnion> n(x * y) * L" nitpick [expect=genuine,card=4] oops
lemma n_split       : "x \<le> x * bot \<squnion> n(x * L) * top" nitpick [expect=genuine,card=3] oops
*)

end

typedef (overloaded) 'a nImage = "{ x::'a::n_semiring . (\<exists>y::'a . x = n(y)) }"
  by auto

lemma simp_nImage[simp]:
  "\<exists>y . Rep_nImage x = n(y)"
  using Rep_nImage by simp

setup_lifting type_definition_nImage

text \<open>Theorem 15\<close>

instantiation nImage :: (n_semiring) bounded_idempotent_semiring
begin

lift_definition sup_nImage :: "'a nImage \<Rightarrow> 'a nImage \<Rightarrow> 'a nImage" is sup
  by (metis n_dist_sup)

lift_definition times_nImage :: "'a nImage \<Rightarrow> 'a nImage \<Rightarrow> 'a nImage" is times
  by (metis n_export)

lift_definition bot_nImage :: "'a nImage" is bot
  by (metis n_bot)

lift_definition one_nImage :: "'a nImage" is 1
  using n_L by auto

lift_definition top_nImage :: "'a nImage" is 1
  using n_L by auto

lift_definition less_eq_nImage :: "'a nImage \<Rightarrow> 'a nImage \<Rightarrow> bool" is less_eq .

lift_definition less_nImage :: "'a nImage \<Rightarrow> 'a nImage \<Rightarrow> bool" is less .

instance
  apply intro_classes
  apply (simp add: less_eq_nImage.rep_eq less_le_not_le less_nImage.rep_eq)
  apply (simp add: less_eq_nImage.rep_eq)
  using less_eq_nImage.rep_eq apply force
  apply (simp add: less_eq_nImage.rep_eq Rep_nImage_inject)
  apply (simp add: sup_nImage.rep_eq less_eq_nImage.rep_eq)
  apply (simp add: less_eq_nImage.rep_eq sup_nImage.rep_eq)
  apply (simp add: sup_nImage.rep_eq less_eq_nImage.rep_eq)
  apply (simp add: bot_nImage.rep_eq less_eq_nImage.rep_eq)
  apply (simp add: sup_nImage.rep_eq times_nImage.rep_eq less_eq_nImage.rep_eq mult_left_dist_sup)
  apply (metis (mono_tags, lifting) sup_nImage.rep_eq times_nImage.rep_eq Rep_nImage_inverse mult_right_dist_sup)
  apply (smt (z3) times_nImage.rep_eq Rep_nImage_inverse bot_nImage.rep_eq mult_left_zero)
  using Rep_nImage_inject one_nImage.rep_eq times_nImage.rep_eq apply fastforce
  apply (simp add: one_nImage.rep_eq times_nImage.rep_eq less_eq_nImage.rep_eq)
  apply (smt (verit, del_insts) sup_nImage.rep_eq Rep_nImage Rep_nImage_inject mem_Collect_eq n_sub_one sup.absorb2 top_nImage.rep_eq)
  apply (simp add: less_eq_nImage.rep_eq mult.assoc times_nImage.rep_eq)
  using Rep_nImage_inject mult.assoc times_nImage.rep_eq apply fastforce
  using Rep_nImage_inject one_nImage.rep_eq times_nImage.rep_eq apply fastforce
  apply (metis (mono_tags, lifting) sup_nImage.rep_eq times_nImage.rep_eq Rep_nImage_inject mult_left_dist_sup)
  by (smt (z3) Rep_nImage_inject bot_nImage.rep_eq n_mult_right_bot simp_nImage times_nImage.rep_eq)

end

text \<open>Theorem 15\<close>

instantiation nImage :: (n_semiring) bounded_distrib_lattice
begin

lift_definition inf_nImage :: "'a nImage \<Rightarrow> 'a nImage \<Rightarrow> 'a nImage" is times
  by (metis n_export)

instance
  apply intro_classes
  apply (metis (mono_tags) inf_nImage.rep_eq less_eq_nImage.rep_eq n_mult_left_lower_bound simp_nImage)
  apply (metis (mono_tags) inf_nImage.rep_eq less_eq_nImage.rep_eq n_mult_right_lower_bound simp_nImage)
  apply (smt (z3) inf_nImage_def le_iff_sup less_eq_nImage.rep_eq mult_right_dist_sup n_mult_left_absorb_sup simp_nImage times_nImage.rep_eq times_nImage_def)
  apply simp
  by (smt (z3) Rep_nImage_inject inf_nImage.rep_eq n_sup_right_dist_mult simp_nImage sup.commute sup_nImage.rep_eq)

end

class n_itering = bounded_itering + n_semiring
begin

lemma mult_L_circ:
  "(x * L)\<^sup>\<circ> = 1 \<squnion> x * L"
  by (metis L_left_zero circ_mult mult_assoc)

lemma mult_L_circ_mult:
  "(x * L)\<^sup>\<circ> * y = y \<squnion> x * L"
  by (metis L_left_zero mult_L_circ mult_assoc mult_left_one mult_right_dist_sup)

lemma circ_L:
  "L\<^sup>\<circ> = L \<squnion> 1"
  by (metis L_left_zero sup_commute circ_left_unfold)

lemma circ_n_L:
  "x\<^sup>\<circ> * n(x) * L = x\<^sup>\<circ> * bot"
  by (metis sup_bot_left circ_left_unfold circ_plus_same mult_left_zero n_L_split n_dist_sup n_mult_bot n_one ni_def ni_split)

lemma n_circ_left_unfold:
  "n(x\<^sup>\<circ>) = n(x * x\<^sup>\<circ>)"
  by (metis circ_n_L circ_plus_same n_mult n_mult_bot)

lemma ni_circ:
  "ni(x)\<^sup>\<circ> = 1 \<squnion> ni(x)"
  by (simp add: mult_L_circ ni_def)

lemma circ_ni:
  "x\<^sup>\<circ> * ni(x) = x\<^sup>\<circ> * bot"
  using circ_n_L ni_def mult_assoc by auto

lemma ni_circ_left_unfold:
  "ni(x\<^sup>\<circ>) = ni(x * x\<^sup>\<circ>)"
  by (simp add: ni_def n_circ_left_unfold)

lemma n_circ_import:
  "n(y) * x \<le> x * n(y) \<Longrightarrow> n(y) * x\<^sup>\<circ> = n(y) * (n(y) * x)\<^sup>\<circ>"
  by (simp add: circ_import n_mult_idempotent n_sub_one)

end

class n_omega_itering = left_omega_conway_semiring + n_itering +
  assumes circ_circ: "x\<^sup>\<circ>\<^sup>\<circ> = L \<squnion> x\<^sup>\<star>"
begin

lemma L_below_one_circ:
  "L \<le> 1\<^sup>\<circ>"
  by (metis sup_left_divisibility circ_circ circ_one)

lemma circ_below_L_sup_star:
  "x\<^sup>\<circ> \<le> L \<squnion> x\<^sup>\<star>"
  by (metis circ_circ circ_increasing)

lemma L_sup_circ_sup_star:
  "L \<squnion> x\<^sup>\<circ> = L \<squnion> x\<^sup>\<star>"
  by (metis circ_circ circ_star star_circ)

lemma circ_one_L:
  "1\<^sup>\<circ> = L \<squnion> 1"
  using circ_circ circ_one star_one by auto

lemma one_circ_zero:
  "L = 1\<^sup>\<circ> * bot"
  by (metis L_left_zero circ_L circ_ni circ_one_L circ_plus_same ni_L)

lemma circ_not_simulate:
  "(\<forall>x y z . x * z \<le> z * y \<longrightarrow> x\<^sup>\<circ> * z \<le> z * y\<^sup>\<circ>) \<longrightarrow> 1 = bot"
  by (metis L_left_zero circ_one_L order.eq_iff mult_left_one mult_left_zero mult_right_sub_dist_sup_left n_L n_bot bot_least)

lemma star_circ_L:
  "x\<^sup>\<star>\<^sup>\<circ> = L \<squnion> x\<^sup>\<star>"
  by (simp add: circ_circ star_circ)

lemma circ_circ_2:
  "x\<^sup>\<circ>\<^sup>\<circ> = L \<squnion> x\<^sup>\<circ>"
  by (simp add: L_sup_circ_sup_star circ_circ)

lemma circ_sup_6:
  "L \<squnion> (x \<squnion> y)\<^sup>\<circ> = (x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ>"
  by (metis circ_circ_2 sup_assoc sup_commute circ_sup_1 circ_circ_sup circ_decompose_4)

lemma circ_sup_7:
  "(x\<^sup>\<circ> * y\<^sup>\<circ>)\<^sup>\<circ> = L \<squnion> (x \<squnion> y)\<^sup>\<star>"
  using L_sup_circ_sup_star circ_sup_6 by auto

end

class n_omega_algebra_2 = bounded_left_zero_omega_algebra + n_semiring + Omega +
  assumes Omega_def: "x\<^sup>\<Omega> = n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star>"
begin

lemma mult_L_star:
  "(x * L)\<^sup>\<star> = 1 \<squnion> x * L"
  by (simp add: L_left_zero transitive_star mult_assoc)

lemma mult_L_omega:
  "(x * L)\<^sup>\<omega> = x * L"
  by (metis L_left_zero omega_slide)

lemma mult_L_sup_star:
  "(x * L \<squnion> y)\<^sup>\<star> = y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
  by (metis L_left_zero star.mult_zero_sup_circ_2 sup_commute mult_assoc)

lemma mult_L_sup_omega:
  "(x * L \<squnion> y)\<^sup>\<omega> = y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * x * L"
  by (metis L_left_zero mult_bot_add_omega sup_commute mult_assoc)

lemma mult_L_sup_circ:
  "(x * L \<squnion> y)\<^sup>\<Omega> = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> \<squnion> y\<^sup>\<star> * x * L"
  by (smt sup_assoc sup_commute Omega_def le_iff_sup mult_L_sup_omega mult_L_sup_star mult_right_dist_sup n_L_decreasing n_dist_sup)

lemma circ_sup_n:
  "(x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega> = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L)"
  by (smt L_left_zero sup_assoc sup_commute Omega_def mult_L_sup_circ mult_assoc mult_left_dist_sup mult_right_dist_sup)

text \<open>Theorem 20.6\<close>

lemma n_omega_induct:
  "n(y) \<le> n(x * y \<squnion> z) \<Longrightarrow> n(y) \<le> n(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z)"
  by (smt sup_commute mult_assoc n_dist_sup n_galois n_mult omega_induct)

lemma n_Omega_left_unfold:
  "1 \<squnion> x * x\<^sup>\<Omega> = x\<^sup>\<Omega>"
proof -
  have "1 \<squnion> x * x\<^sup>\<Omega> = 1 \<squnion> x * n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star>"
    by (simp add: Omega_def semiring.distrib_left sup_assoc mult_assoc)
  also have "... = n(x * x\<^sup>\<omega>) * L \<squnion> (1 \<squnion> x * x\<^sup>\<star>)"
    by (metis sup_assoc sup_commute sup_bot_left mult_left_dist_sup n_L_split)
  also have "... = n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star>"
    using omega_unfold star_left_unfold_equal by auto
  also have "... = x\<^sup>\<Omega>"
    by (simp add: Omega_def)
  finally show ?thesis
    .
qed

lemma n_Omega_circ_sup:
  "(x \<squnion> y)\<^sup>\<Omega> = (x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
proof -
  have "(x\<^sup>\<Omega> * y)\<^sup>\<Omega> * x\<^sup>\<Omega> = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> ((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * n(x\<^sup>\<omega>) * L)"
    by (simp add: circ_sup_n)
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega>) * L \<squnion> n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * bot \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star>"
    using n_L_split sup.left_commute sup_commute by auto
  also have "... = n((x\<^sup>\<star> * y)\<^sup>\<omega> \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L \<squnion> (x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<star>"
    by (smt sup_assoc sup_bot_left mult_left_dist_sup mult_right_dist_sup n_dist_sup)
  also have "... = (x \<squnion> y)\<^sup>\<Omega>"
    by (simp add: Omega_def omega_decompose star.circ_sup_9)
  finally show ?thesis
    ..
qed

lemma n_Omega_circ_simulate_right_sup:
  assumes "z * x \<le> y * y\<^sup>\<Omega> * z \<squnion> w"
    shows "z * x\<^sup>\<Omega> \<le> y\<^sup>\<Omega> * (z \<squnion> w * x\<^sup>\<Omega>)"
proof -
  have "z * x \<le> y * y\<^sup>\<Omega> * z \<squnion> w"
    by (simp add: assms)
  also have "... = y * n(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    using L_left_zero Omega_def mult_right_dist_sup semiring.distrib_left mult_assoc by auto
  finally have 1: "z * x \<le> n(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w"
    by (metis sup_assoc sup_commute sup_bot_left mult_assoc mult_left_dist_sup n_L_split omega_unfold)
  hence "(n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>) * x \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * (n(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z \<squnion> w) \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt L_left_zero sup_assoc sup_ge1 sup_ge2 le_iff_sup mult_assoc mult_left_dist_sup mult_right_dist_sup star.circ_back_loop_fixpoint)
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * y * y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    using semiring.distrib_left sup_assoc mult_assoc by auto
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * y * y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt (verit, ccfv_SIG) le_supI1 order.refl semiring.add_mono star.circ_back_loop_prefixpoint sup.bounded_iff sup.coboundedI1 sup.mono sup_left_divisibility sup_right_divisibility sup_same_context)
  also have "... = n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * y * y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt sup_assoc sup_commute sup_idem mult_assoc mult_left_dist_sup n_L_split star_mult_omega)
  also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (meson mult_left_isotone order_refl semiring.add_left_mono star.circ_mult_upper_bound star.right_plus_below_circ sup_left_isotone)
  finally have 2: "z * x\<^sup>\<star> \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    by (smt le_supI1 le_sup_iff sup_ge1 star.circ_loop_fixpoint star_right_induct)
  have "z * x * x\<^sup>\<omega> \<le> n(y\<^sup>\<omega>) * L \<squnion> y * y\<^sup>\<star> * z * x\<^sup>\<omega> \<squnion> w * x\<^sup>\<omega>"
    using 1 by (smt (verit, del_insts) L_left_zero mult_assoc mult_left_isotone mult_right_dist_sup)
  hence "n(z * x * x\<^sup>\<omega>) \<le> n(y * y\<^sup>\<star> * z * x\<^sup>\<omega> \<squnion> n(y\<^sup>\<omega>) * L \<squnion> w * x\<^sup>\<omega>)"
    by (simp add: n_isotone sup_commute)
  hence "n(z * x\<^sup>\<omega>) \<le> n(y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * w * x\<^sup>\<omega>)"
    by (smt (verit, del_insts) sup_assoc sup_commute left_plus_omega le_iff_sup mult_assoc mult_left_dist_sup n_L_decreasing n_omega_induct omega_unfold star.left_plus_circ star_mult_omega)
  hence "n(z * x\<^sup>\<omega>) * L \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L"
    by (metis n_dist_sup n_galois n_mult n_n_L)
  hence "z * n(x\<^sup>\<omega>) * L \<le> z * bot \<squnion> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L"
    using n_L_split semiring.add_left_mono sup_assoc by auto
  also have "... \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L"
    by (smt (z3) order.trans mult_1_left mult_right_sub_dist_sup_left semiring.add_right_mono star_left_unfold_equal sup_commute zero_right_mult_decreasing)
  finally have "z * n(x\<^sup>\<omega>) * L \<le> n(y\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * z \<squnion> y\<^sup>\<star> * w * n(x\<^sup>\<omega>) * L \<squnion> y\<^sup>\<star> * w * x\<^sup>\<star>"
    using le_supI1 by blast
  thus ?thesis
    using 2 by (smt L_left_zero Omega_def sup_assoc le_iff_sup mult_assoc mult_left_dist_sup mult_right_dist_sup)
qed

lemma n_Omega_circ_simulate_left_sup:
  assumes "x * z \<le> z * y\<^sup>\<Omega> \<squnion> w"
    shows "x\<^sup>\<Omega> * z \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
proof -
  have "x * (z * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * n(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>) = x * z * n(y\<^sup>\<omega>) * L \<squnion> x * z * y\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * w * n(y\<^sup>\<omega>) * L \<squnion> x * x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt sup_assoc sup_commute mult_assoc mult_left_dist_sup n_L_split omega_unfold)
  also have "... \<le> (z * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w) * n(y\<^sup>\<omega>) * L \<squnion> (z * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w) * y\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * n(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt assms Omega_def sup_assoc sup_ge2 le_iff_sup mult_assoc mult_left_dist_sup mult_right_dist_sup star.circ_loop_fixpoint)
  also have "... = z * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> * n(y\<^sup>\<omega>) * L \<squnion> w * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w * y\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * n(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt L_left_zero sup_assoc sup_commute sup_idem mult_assoc mult_right_dist_sup star.circ_transitive_equal)
  also have "... = z * n(y\<^sup>\<omega>) * L \<squnion> w * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> w * y\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * n(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt sup_assoc sup_commute sup_idem le_iff_sup mult_assoc n_L_split star_mult_omega zero_right_mult_decreasing)
  finally have "x * (z * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * n(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>) \<le> z * n(y\<^sup>\<omega>) * L \<squnion> z * y\<^sup>\<star> \<squnion> n(x\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * n(y\<^sup>\<omega>) * L \<squnion> x\<^sup>\<star> * w * y\<^sup>\<star>"
    by (smt sup_assoc sup_commute sup_idem mult_assoc star.circ_loop_fixpoint)
  thus "x\<^sup>\<Omega> * z \<le> (z \<squnion> x\<^sup>\<Omega> * w) * y\<^sup>\<Omega>"
    by (smt (verit, del_insts) L_left_zero Omega_def sup_assoc le_supI1 le_sup_iff sup_ge1 mult_assoc mult_left_dist_sup mult_right_dist_sup star.circ_back_loop_fixpoint star_left_induct)
qed

end

text \<open>Theorem 2.6 and Theorem 19\<close>

sublocale n_omega_algebra_2 < nL_omega: itering where circ = Omega
  apply unfold_locales
  apply (simp add: n_Omega_circ_sup)
  apply (smt L_left_zero sup_assoc sup_commute sup_bot_left Omega_def mult_assoc mult_left_dist_sup mult_right_dist_sup n_L_split omega_slide star.circ_mult)
  apply (simp add: n_Omega_circ_simulate_right_sup)
  using n_Omega_circ_simulate_left_sup by auto

sublocale n_omega_algebra_2 < nL_omega: n_omega_itering where circ = Omega
  apply unfold_locales
  by (smt Omega_def sup_assoc sup_commute le_iff_sup mult_L_sup_star mult_left_one n_L_split n_top ni_below_L ni_def star_involutive star_mult_omega star_omega_top zero_right_mult_decreasing)

sublocale n_omega_algebra_2 < nL_omega: left_zero_kleene_conway_semiring where circ = Omega ..

sublocale n_omega_algebra_2 < nL_star: left_omega_conway_semiring where circ = star ..

context n_omega_algebra_2
begin

lemma circ_sup_8:
  "n((x\<^sup>\<star> * y)\<^sup>\<star> * x\<^sup>\<omega>) * L \<le> (x\<^sup>\<star> * y)\<^sup>\<Omega> * x\<^sup>\<Omega>"
  by (metis sup_ge1 nL_omega.circ_sup_4 Omega_def mult_left_isotone n_isotone omega_sum_unfold_3 order_trans)

lemma n_split_omega_omega:
  "x\<^sup>\<omega> \<le> x\<^sup>\<omega> * bot \<squnion> n(x\<^sup>\<omega>) * top"
  by (metis n_split n_top_L omega_vector)

text \<open>Theorem 20.1\<close>

lemma n_below_n_star:
  "n(x) \<le> n(x\<^sup>\<star>)"
  by (simp add: n_isotone star.circ_increasing)

text \<open>Theorem 20.2\<close>

lemma n_star_below_n_omega:
  "n(x\<^sup>\<star>) \<le> n(x\<^sup>\<omega>)"
  by (metis n_mult_left_upper_bound star_mult_omega)

lemma n_below_n_omega:
  "n(x) \<le> n(x\<^sup>\<omega>)"
  using order.trans n_below_n_star n_star_below_n_omega by blast

text \<open>Theorem 20.4\<close>

lemma star_n_L:
  "x\<^sup>\<star> * n(x) * L = x\<^sup>\<star> * bot"
  by (metis sup_bot_left mult_left_zero n_L_split n_dist_sup n_mult_bot n_one ni_def ni_split star_left_unfold_equal star_plus)

lemma star_L_split:
  assumes "y \<le> z"
      and "x * z * L \<le> x * bot \<squnion> z * L"
    shows "x\<^sup>\<star> * y * L \<le> x\<^sup>\<star> * bot \<squnion> z * L"
proof -
  have "x * (x\<^sup>\<star> * bot \<squnion> z * L) \<le> x\<^sup>\<star> * bot \<squnion> x * z * L"
    by (metis sup_bot_right order.eq_iff mult_assoc mult_left_dist_sup star.circ_loop_fixpoint)
  also have "... \<le> x\<^sup>\<star> * bot \<squnion> x * bot \<squnion> z * L"
    using assms(2) semiring.add_left_mono sup_assoc by auto
  also have "... = x\<^sup>\<star> * bot \<squnion> z * L"
    using mult_left_isotone star.circ_increasing sup.absorb_iff2 sup_commute by auto
  finally have "y * L \<squnion> x * (x\<^sup>\<star> * bot \<squnion> z * L) \<le> x\<^sup>\<star> * bot \<squnion> z * L"
    by (metis assms(1) le_sup_iff sup_ge2 mult_left_isotone order_trans)
  thus ?thesis
    by (simp add: star_left_induct mult_assoc)
qed

lemma star_L_split_same:
  "x * y * L \<le> x * bot \<squnion> y * L \<Longrightarrow> x\<^sup>\<star> * y * L = x\<^sup>\<star> * bot \<squnion> y * L"
  apply (rule order.antisym)
  apply (simp add: star_L_split)
  by (metis bot_least le_supI mult_isotone nL_star.star_below_circ star.circ_loop_fixpoint sup.cobounded2 mult_assoc)

lemma star_n_L_split_equal:
  "n(x * y) \<le> n(y) \<Longrightarrow> x\<^sup>\<star> * n(y) * L = x\<^sup>\<star> * bot \<squnion> n(y) * L"
  by (simp add: n_mult_right_upper_bound star_L_split_same)

lemma n_star_mult:
  "n(x * y) \<le> n(y) \<Longrightarrow> n(x\<^sup>\<star> * y) = n(x\<^sup>\<star>) \<squnion> n(y)"
  by (metis n_dist_sup n_mult n_mult_bot n_n_L star_n_L_split_equal)

text \<open>Theorem 20.3\<close>

lemma n_omega_mult:
  "n(x\<^sup>\<omega> * y) = n(x\<^sup>\<omega>)"
  by (simp add: n_isotone n_mult_left_upper_bound omega_sub_vector order.eq_iff)

lemma n_star_left_unfold:
  "n(x\<^sup>\<star>) = n(x * x\<^sup>\<star>)"
  by (metis n_mult n_mult_bot star.circ_plus_same star_n_L)

lemma ni_star_below_ni_omega:
  "ni(x\<^sup>\<star>) \<le> ni(x\<^sup>\<omega>)"
  by (simp add: ni_n_order n_star_below_n_omega)

lemma ni_below_ni_omega:
  "ni(x) \<le> ni(x\<^sup>\<omega>)"
  by (simp add: ni_n_order n_below_n_omega)

lemma ni_star:
  "ni(x)\<^sup>\<star> = 1 \<squnion> ni(x)"
  by (simp add: mult_L_star ni_def)

lemma ni_omega:
  "ni(x)\<^sup>\<omega> = ni(x)"
  using mult_L_omega ni_def by auto

lemma ni_omega_induct:
  "ni(y) \<le> ni(x * y \<squnion> z) \<Longrightarrow> ni(y) \<le> ni(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z)"
  using n_omega_induct ni_n_order by blast

lemma star_ni:
  "x\<^sup>\<star> * ni(x) = x\<^sup>\<star> * bot"
  using ni_def mult_assoc star_n_L by auto

lemma star_ni_split_equal:
  "ni(x * y) \<le> ni(y) \<Longrightarrow> x\<^sup>\<star> * ni(y) = x\<^sup>\<star> * bot \<squnion> ni(y)"
  using ni_def ni_mult_right_upper_bound mult_assoc star_L_split_same by auto

lemma ni_star_mult:
  "ni(x * y) \<le> ni(y) \<Longrightarrow> ni(x\<^sup>\<star> * y) = ni(x\<^sup>\<star>) \<squnion> ni(y)"
  using mult_right_dist_sup ni_def ni_n_order n_star_mult by auto

lemma ni_omega_mult:
  "ni(x\<^sup>\<omega> * y) = ni(x\<^sup>\<omega>)"
  by (simp add: ni_def n_omega_mult)

lemma ni_star_left_unfold:
  "ni(x\<^sup>\<star>) = ni(x * x\<^sup>\<star>)"
  by (simp add: ni_def n_star_left_unfold)

lemma n_star_import:
  assumes "n(y) * x \<le> x * n(y)"
    shows "n(y) * x\<^sup>\<star> = n(y) * (n(y) * x)\<^sup>\<star>"
proof (rule order.antisym)
  have "n(y) * (n(y) * x)\<^sup>\<star> * x \<le> n(y) * (n(y) * x)\<^sup>\<star>"
    by (smt assms mult_assoc mult_right_dist_sup mult_right_sub_dist_sup_left n_mult_idempotent n_preserves_equation star.circ_back_loop_fixpoint)
  thus "n(y) * x\<^sup>\<star> \<le> n(y) * (n(y) * x)\<^sup>\<star>"
    using assms eq_refl n_mult_idempotent n_sub_one star.circ_import by auto
next
  show "n(y) * (n(y) * x)\<^sup>\<star> \<le> n(y) * x\<^sup>\<star>"
    by (simp add: assms n_mult_idempotent n_sub_one star.circ_import)
qed

lemma n_omega_export:
  "n(y) * x \<le> x * n(y) \<Longrightarrow> n(y) * x\<^sup>\<omega> = (n(y) * x)\<^sup>\<omega>"
  apply (rule order.antisym)
  apply (simp add: n_preserves_equation omega_simulation)
  by (metis mult_right_isotone mult_1_right n_sub_one omega_isotone omega_slide)

lemma n_omega_import:
  "n(y) * x \<le> x * n(y) \<Longrightarrow> n(y) * x\<^sup>\<omega> = n(y) * (n(y) * x)\<^sup>\<omega>"
  by (simp add: n_mult_idempotent omega_import)

text \<open>Theorem 20.5\<close>

lemma star_n_omega_top:
  "x\<^sup>\<star> * n(x\<^sup>\<omega>) * top = x\<^sup>\<star> * bot \<squnion> n(x\<^sup>\<omega>) * top"
  by (smt (verit, del_insts) le_supI le_sup_iff sup_right_divisibility order.antisym mult_assoc nL_star.circ_mult_omega nL_star.star_zero_below_circ_mult n_top_split star.circ_loop_fixpoint)

(*
lemma n_star_induct_sup: "n(z \<squnion> x * y) \<le> n(y) \<Longrightarrow> n(x\<^sup>\<star> * z) \<le> n(y)" oops
*)

end

end

