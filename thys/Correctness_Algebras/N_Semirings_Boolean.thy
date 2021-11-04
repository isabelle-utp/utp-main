(* Title:      Boolean N-Semirings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Boolean N-Semirings\<close>

theory N_Semirings_Boolean

imports N_Semirings

begin

class an =
  fixes an :: "'a \<Rightarrow> 'a"

class an_semiring = bounded_idempotent_left_zero_semiring + L + n + an + uminus +
  assumes an_complement: "an(x) \<squnion> n(x) = 1"
  assumes an_dist_sup  : "an(x \<squnion> y) = an(x) * an(y)"
  assumes an_export    : "an(an(x) * y) = n(x) \<squnion> an(y)"
  assumes an_mult_zero : "an(x) = an(x * bot)"
  assumes an_L_split   : "x * n(y) * L = x * bot \<squnion> n(x * y) * L"
  assumes an_split     : "an(x * L) * x \<le> x * bot"
  assumes an_uminus    : "-x = an(x * L)"
begin

text \<open>Theorem 21\<close>

lemma n_an_def:
  "n(x) = an(an(x) * L)"
  by (metis an_dist_sup an_export an_split bot_least mult_right_isotone semiring.add_nonneg_eq_0_iff sup.orderE top_greatest vector_bot_closed)

text \<open>Theorem 21\<close>

lemma an_complement_bot:
  "an(x) * n(x) = bot"
  by (metis an_dist_sup an_split bot_least le_iff_sup mult_left_zero sup_commute n_an_def)

text \<open>Theorem 21\<close>

lemma an_n_def:
  "an(x) = n(an(x) * L)"
  by (smt (verit, ccfv_threshold) an_complement_bot an_complement mult.right_neutral mult_left_dist_sup mult_right_dist_sup sup_commute n_an_def)

lemma an_case_split_left:
  "an(z) * x \<le> y \<and> n(z) * x \<le> y \<longleftrightarrow> x \<le> y"
  by (metis le_sup_iff an_complement mult_left_one mult_right_dist_sup)

lemma an_case_split_right:
  "x * an(z) \<le> y \<and> x * n(z) \<le> y \<longleftrightarrow> x \<le> y"
  by (metis le_sup_iff an_complement mult_1_right mult_left_dist_sup)

lemma split_sub:
  "x * y \<le> z \<squnion> x * top"
  by (simp add: le_supI2 mult_right_isotone)

text \<open>Theorem 21\<close>

subclass n_semiring
  apply unfold_locales
  apply (metis an_dist_sup an_split mult_left_zero sup.absorb2 sup_bot_left sup_commute n_an_def)
  apply (metis sup_left_top an_complement an_dist_sup an_export mult_assoc n_an_def)
  apply (metis an_dist_sup an_export mult_assoc n_an_def)
  apply (metis an_dist_sup an_export an_n_def mult_right_dist_sup n_an_def)
  apply (metis sup_idem an_dist_sup an_mult_zero n_an_def)
  apply (simp add: an_L_split)
  by (meson an_case_split_left an_split le_supI1 split_sub)

lemma n_complement_bot:
  "n(x) * an(x) = bot"
  by (metis an_complement_bot an_n_def n_an_def)

lemma an_bot:
  "an(bot) = 1"
  by (metis sup_bot_right an_complement n_bot)

lemma an_one:
  "an(1) = 1"
  by (metis sup_bot_right an_complement n_one)

lemma an_L:
  "an(L) = bot"
  using an_one n_one n_an_def by auto

lemma an_top:
  "an(top) = bot"
  by (metis mult_left_one n_complement_bot n_top)

lemma an_export_n:
  "an(n(x) * y) = an(x) \<squnion> an(y)"
  by (metis an_export an_n_def n_an_def)

lemma n_export_an:
  "n(an(x) * y) = an(x) * n(y)"
  by (metis an_n_def n_export)

lemma n_an_mult_commutative:
  "n(x) * an(y) = an(y) * n(x)"
  by (metis sup_commute an_dist_sup n_an_def)

lemma an_mult_commutative:
  "an(x) * an(y) = an(y) * an(x)"
  by (metis sup_commute an_dist_sup)

lemma an_mult_idempotent:
  "an(x) * an(x) = an(x)"
  by (metis sup_idem an_dist_sup)

lemma an_sub_one:
  "an(x) \<le> 1"
  using an_complement sup.cobounded1 by fastforce

text \<open>Theorem 21\<close>

lemma an_antitone:
  "x \<le> y \<Longrightarrow> an(y) \<le> an(x)"
  by (metis an_n_def an_dist_sup n_order sup.absorb1)

lemma an_mult_left_upper_bound:
  "an(x * y) \<le> an(x)"
  by (metis an_antitone an_mult_zero mult_right_isotone bot_least)

lemma an_mult_right_zero:
  "an(x) * bot = bot"
  by (metis an_n_def n_mult_right_bot)

lemma n_mult_an:
  "n(x * an(y)) = n(x)"
  by (metis an_n_def n_mult_n)

lemma an_mult_n:
  "an(x * n(y)) = an(x)"
  by (metis an_n_def n_an_def n_mult_n)

lemma an_mult_an:
  "an(x * an(y)) = an(x)"
  by (metis an_mult_n an_n_def)

lemma an_mult_left_absorb_sup:
  "an(x) * (an(x) \<squnion> an(y)) = an(x)"
  by (metis an_n_def n_mult_left_absorb_sup)

lemma an_mult_right_absorb_sup:
  "(an(x) \<squnion> an(y)) * an(y) = an(y)"
  by (metis an_n_def n_mult_right_absorb_sup)

lemma an_sup_left_absorb_mult:
  "an(x) \<squnion> an(x) * an(y) = an(x)"
  using an_case_split_right sup_absorb1 by blast

lemma an_sup_right_absorb_mult:
  "an(x) * an(y) \<squnion> an(y) = an(y)"
  using an_case_split_left sup_absorb2 by blast

lemma an_sup_left_dist_mult:
  "an(x) \<squnion> an(y) * an(z) = (an(x) \<squnion> an(y)) * (an(x) \<squnion> an(z))"
  by (metis an_n_def n_sup_left_dist_mult)

lemma an_sup_right_dist_mult:
  "an(x) * an(y) \<squnion> an(z) = (an(x) \<squnion> an(z)) * (an(y) \<squnion> an(z))"
  by (simp add: an_sup_left_dist_mult sup_commute)

lemma an_n_order:
  "an(x) \<le> an(y) \<longleftrightarrow> n(y) \<le> n(x)"
  by (smt (verit) an_n_def an_dist_sup le_iff_sup n_dist_sup n_mult_right_absorb_sup sup.orderE n_an_def)

lemma an_order:
  "an(x) \<le> an(y) \<longleftrightarrow> an(x) * an(y) = an(x)"
  by (metis an_n_def n_order)

lemma an_mult_left_lower_bound:
  "an(x) * an(y) \<le> an(x)"
  using an_case_split_right by blast

lemma an_mult_right_lower_bound:
  "an(x) * an(y) \<le> an(y)"
  by (simp add: an_sup_right_absorb_mult le_iff_sup)

lemma an_n_mult_left_lower_bound:
  "an(x) * n(y) \<le> an(x)"
  using an_case_split_right by blast

lemma an_n_mult_right_lower_bound:
  "an(x) * n(y) \<le> n(y)"
  using an_case_split_left by auto

lemma n_an_mult_left_lower_bound:
  "n(x) * an(y) \<le> n(x)"
  using an_case_split_right by auto

lemma n_an_mult_right_lower_bound:
  "n(x) * an(y) \<le> an(y)"
  using an_case_split_left by blast

lemma an_mult_least_upper_bound:
  "an(x) \<le> an(y) \<and> an(x) \<le> an(z) \<longleftrightarrow> an(x) \<le> an(y) * an(z)"
  by (metis an_mult_idempotent an_mult_left_lower_bound an_mult_right_lower_bound order.trans mult_isotone)

lemma an_mult_left_divisibility:
  "an(x) \<le> an(y) \<longleftrightarrow> (\<exists>z . an(x) = an(y) * an(z))"
  by (metis an_mult_commutative an_mult_left_lower_bound an_order)

lemma an_mult_right_divisibility:
  "an(x) \<le> an(y) \<longleftrightarrow> (\<exists>z . an(x) = an(z) * an(y))"
  by (simp add: an_mult_commutative an_mult_left_divisibility)

lemma an_split_top:
  "an(x * L) * x * top \<le> x * bot"
  by (metis an_split mult_assoc mult_left_isotone mult_left_zero)

lemma an_n_L:
  "an(n(x) * L) = an(x)"
  using an_n_def n_an_def by auto

lemma an_galois:
  "an(y) \<le> an(x) \<longleftrightarrow> n(x) * L \<le> y"
  by (simp add: an_n_order n_galois)

lemma an_mult:
  "an(x * n(y) * L) = an(x * y)"
  by (metis an_n_L n_mult)

lemma n_mult_top:
  "an(x * n(y) * top) = an(x * y)"
  by (metis an_n_L n_mult_top)

lemma an_n_equal:
  "an(x) = an(y) \<longleftrightarrow> n(x) = n(y)"
  by (metis an_n_L n_an_def)

lemma an_top_L:
  "an(x * top) = an(x * L)"
  by (simp add: an_n_equal n_top_L)

lemma an_case_split_left_equal:
  "an(z) * x = an(z) * y \<Longrightarrow> n(z) * x = n(z) * y \<Longrightarrow> x = y"
  using an_complement case_split_left_equal by blast

lemma an_case_split_right_equal:
  "x * an(z) = y * an(z) \<Longrightarrow> x * n(z) = y * n(z) \<Longrightarrow> x = y"
  using an_complement case_split_right_equal by blast

lemma an_equal_complement:
  "n(x) \<squnion> an(y) = 1 \<and> n(x) * an(y) = bot \<longleftrightarrow> an(x) = an(y)"
  by (metis sup_commute an_complement an_dist_sup mult_left_one mult_right_dist_sup n_complement_bot)

lemma n_equal_complement:
  "n(x) \<squnion> an(y) = 1 \<and> n(x) * an(y) = bot \<longleftrightarrow> n(x) = n(y)"
  by (simp add: an_equal_complement an_n_equal)

lemma an_shunting:
  "an(z) * x \<le> y \<longleftrightarrow> x \<le> y \<squnion> n(z) * top"
  apply (rule iffI)
  apply (meson an_case_split_left le_supI1 split_sub)
  by (metis sup_bot_right an_case_split_left an_complement_bot mult_assoc mult_left_dist_sup mult_left_zero mult_right_isotone order_refl order_trans)

lemma an_shunting_an:
  "an(z) * an(x) \<le> an(y) \<longleftrightarrow> an(x) \<le> n(z) \<squnion> an(y)"
  apply (rule iffI)
  apply (smt sup_ge1 sup_ge2 an_case_split_left n_an_mult_left_lower_bound order_trans)
  by (metis sup_bot_left sup_ge2 an_case_split_left an_complement_bot mult_left_dist_sup mult_right_isotone order_trans)

lemma an_L_zero:
  "an(x * L) * x = an(x * L) * x * bot"
  by (metis an_complement_bot n_split_equal sup_monoid.add_0_right vector_bot_closed mult_assoc n_export_an)

lemma n_plus_complement_intro_n:
  "n(x) \<squnion> an(x) * n(y) = n(x) \<squnion> n(y)"
  by (metis sup_commute an_complement an_n_def mult_1_right n_sup_right_dist_mult n_an_mult_commutative)

lemma n_plus_complement_intro_an:
  "n(x) \<squnion> an(x) * an(y) = n(x) \<squnion> an(y)"
  by (metis an_n_def n_plus_complement_intro_n)

lemma an_plus_complement_intro_n:
  "an(x) \<squnion> n(x) * n(y) = an(x) \<squnion> n(y)"
  by (metis an_n_def n_an_def n_plus_complement_intro_n)

lemma an_plus_complement_intro_an:
  "an(x) \<squnion> n(x) * an(y) = an(x) \<squnion> an(y)"
  by (metis an_n_def an_plus_complement_intro_n)

lemma n_mult_complement_intro_n:
  "n(x) * (an(x) \<squnion> n(y)) = n(x) * n(y)"
  by (simp add: mult_left_dist_sup n_complement_bot)

lemma n_mult_complement_intro_an:
  "n(x) * (an(x) \<squnion> an(y)) = n(x) * an(y)"
  by (simp add: semiring.distrib_left n_complement_bot)

lemma an_mult_complement_intro_n:
  "an(x) * (n(x) \<squnion> n(y)) = an(x) * n(y)"
  by (simp add: an_complement_bot mult_left_dist_sup)

lemma an_mult_complement_intro_an:
  "an(x) * (n(x) \<squnion> an(y)) = an(x) * an(y)"
  by (simp add: an_complement_bot semiring.distrib_left)

lemma an_preserves_equation:
  "an(y) * x \<le> x * an(y) \<longleftrightarrow> an(y) * x = an(y) * x * an(y)"
  by (metis an_n_def n_preserves_equation)

lemma wnf_lemma_1:
  "(n(p * L) * n(q * L) \<squnion> an(p * L) * an(r * L)) * n(p * L) = n(p * L) * n(q * L)"
  by (smt sup_commute an_n_def n_sup_left_absorb_mult n_sup_right_dist_mult n_export n_mult_commutative n_mult_complement_intro_n)

lemma wnf_lemma_2:
  "(n(p * L) * n(q * L) \<squnion> an(r * L) * an(q * L)) * n(q * L) = n(p * L) * n(q * L)"
  by (metis an_mult_commutative n_mult_commutative wnf_lemma_1)

lemma wnf_lemma_3:
  "(n(p * L) * n(r * L) \<squnion> an(p * L) * an(q * L)) * an(p * L) = an(p * L) * an(q * L)"
  by (metis an_n_def sup_commute wnf_lemma_1 n_an_def)

lemma wnf_lemma_4:
  "(n(r * L) * n(q * L) \<squnion> an(p * L) * an(q * L)) * an(q * L) = an(p * L) * an(q * L)"
  by (metis an_mult_commutative n_mult_commutative wnf_lemma_3)

lemma wnf_lemma_5:
  "n(p \<squnion> q) * (n(q) * x \<squnion> an(q) * y) = n(q) * x \<squnion> an(q) * n(p) * y"
  by (smt sup_bot_right mult_assoc mult_left_dist_sup n_an_mult_commutative n_complement_bot n_dist_sup n_mult_right_absorb_sup)

definition ani :: "'a \<Rightarrow> 'a"
  where "ani x \<equiv> an(x) * L"

lemma ani_bot:
  "ani(bot) = L"
  using an_bot ani_def by auto

lemma ani_one:
  "ani(1) = L"
  using an_one ani_def by auto

lemma ani_L:
  "ani(L) = bot"
  by (simp add: an_L ani_def)

lemma ani_top:
  "ani(top) = bot"
  by (simp add: an_top ani_def)

lemma ani_complement:
  "ani(x) \<squnion> ni(x) = L"
  by (metis an_complement ani_def mult_right_dist_sup n_top ni_def ni_top)

lemma ani_mult_zero:
  "ani(x) = ani(x * bot)"
  using ani_def an_mult_zero by auto

lemma ani_antitone:
  "y \<le> x \<Longrightarrow> ani(x) \<le> ani(y)"
  by (simp add: an_antitone ani_def mult_left_isotone)

lemma ani_mult_left_upper_bound:
  "ani(x * y) \<le> ani(x)"
  by (simp add: an_mult_left_upper_bound ani_def mult_left_isotone)

lemma ani_involutive:
  "ani(ani(x)) = ni(x)"
  by (simp add: ani_def ni_def n_an_def)

lemma ani_below_L:
  "ani(x) \<le> L"
  using an_case_split_left ani_def by auto

lemma ani_left_zero:
  "ani(x) * y = ani(x)"
  by (simp add: ani_def L_left_zero mult_assoc)

lemma ani_top_L:
  "ani(x * top) = ani(x * L)"
  by (simp add: an_top_L ani_def)

lemma ani_ni_order:
  "ani(x) \<le> ani(y) \<longleftrightarrow> ni(y) \<le> ni(x)"
  by (metis an_n_L ani_antitone ani_def ani_involutive ni_def)

lemma ani_ni_equal:
  "ani(x) = ani(y) \<longleftrightarrow> ni(x) = ni(y)"
  by (metis ani_ni_order order.antisym order_refl)

lemma ni_ani:
  "ni(ani(x)) = ani(x)"
  using an_n_def ani_def ni_def by auto

lemma ani_ni:
  "ani(ni(x)) = ani(x)"
  by (simp add: an_n_L ani_def ni_def)

lemma ani_mult:
  "ani(x * ni(y)) = ani(x * y)"
  using ani_ni_equal ni_mult by blast

lemma ani_an_order:
  "ani(x) \<le> ani(y) \<longleftrightarrow> an(x) \<le> an(y)"
  using an_galois ani_ni_order ni_def ni_galois by auto

lemma ani_an_equal:
  "ani(x) = ani(y) \<longleftrightarrow> an(x) = an(y)"
  by (metis an_n_def ani_def)

lemma n_mult_ani:
  "n(x) * ani(x) = bot"
  by (metis an_L ani_L ani_def mult_assoc n_complement_bot)

lemma an_mult_ni:
  "an(x) * ni(x) = bot"
  by (metis an_n_def ani_def n_an_def n_mult_ani ni_def)

lemma n_mult_ni:
  "n(x) * ni(x) = ni(x)"
  by (metis n_export n_order ni_def ni_export order_refl)

lemma an_mult_ani:
  "an(x) * ani(x) = ani(x)"
  by (metis an_n_def ani_def n_mult_ni ni_def)

lemma ani_ni_meet:
  "x \<le> ani(y) \<Longrightarrow> x \<le> ni(y) \<Longrightarrow> x = bot"
  by (metis an_case_split_left an_mult_ni bot_unique mult_right_isotone n_mult_ani)

lemma ani_galois:
  "ani(x) \<le> y \<longleftrightarrow> ni(x \<squnion> y) = L"
  apply (rule iffI)
  apply (smt (z3) an_L an_mult_commutative an_mult_right_zero ani_def an_dist_sup ni_L ni_n_equal sup.absorb1 mult_assoc n_an_def n_complement_bot)
  by (metis an_L an_galois an_mult_ni an_n_def an_shunting_an ani_def an_dist_sup an_export idempotent_bot_closed n_bot transitive_bot_closed)

lemma an_ani:
  "an(ani(x)) = n(x)"
  by (simp add: ani_def n_an_def)

lemma n_ani:
  "n(ani(x)) = an(x)"
  using an_n_def ani_def by auto

lemma an_ni:
  "an(ni(x)) = an(x)"
  by (simp add: an_n_L ni_def)

lemma ani_an:
  "ani(an(x)) = L"
  by (metis an_mult_right_zero an_mult_zero an_bot ani_def mult_left_one)

lemma ani_n:
  "ani(n(x)) = L"
  by (simp add: ani_an n_an_def)

lemma ni_an:
  "ni(an(x)) = bot"
  using an_L ani_an ani_def ni_n_bot n_an_def by force

lemma ani_mult_n:
  "ani(x * n(y)) = ani(x)"
  by (simp add: an_mult_n ani_def)

lemma ani_mult_an:
  "ani(x * an(y)) = ani(x)"
  by (simp add: an_mult_an ani_def)

lemma ani_export_n:
  "ani(n(x) * y) = ani(x) \<squnion> ani(y)"
  by (simp add: an_export_n ani_def mult_right_dist_sup)

lemma ani_export_an:
  "ani(an(x) * y) = ni(x) \<squnion> ani(y)"
  by (simp add: ani_def an_export ni_def semiring.distrib_right)

lemma ni_export_an:
  "ni(an(x) * y) = an(x) * ni(y)"
  by (simp add: an_mult_right_zero ni_split)

lemma ani_mult_top:
  "ani(x * n(y) * top) = ani(x * y)"
  using ani_def n_mult_top by auto

lemma ani_an_bot:
  "ani(x) = bot \<longleftrightarrow> an(x) = bot"
  using an_L ani_L ani_an_equal by force

lemma ani_an_L:
  "ani(x) = L \<longleftrightarrow> an(x) = 1"
  using an_bot ani_an_equal ani_bot by force

text \<open>Theorem 21\<close>

subclass tests
  apply unfold_locales
  apply (simp add: mult_assoc)
  apply (simp add: an_mult_commutative an_uminus)
  apply (smt an_sup_left_dist_mult an_export_n an_n_L an_uminus n_an_def n_complement_bot n_export)
  apply (metis an_dist_sup an_n_def an_uminus n_an_def)
  using an_complement_bot an_uminus n_an_def apply fastforce
  apply (simp add: an_bot an_uminus)
  using an_export_n an_mult an_uminus n_an_def apply fastforce
  using an_order an_uminus apply force
  by (simp add: less_le_not_le)

end

class an_itering = n_itering + an_semiring + while +
  assumes while_circ_def: "p \<star> y = (p * y)\<^sup>\<circ> * -p"
begin

subclass test_itering
  apply unfold_locales
  by (rule while_circ_def)

lemma an_circ_left_unfold:
  "an(x\<^sup>\<circ>) = an(x * x\<^sup>\<circ>)"
  by (metis an_dist_sup an_one circ_left_unfold mult_left_one)

lemma an_circ_x_n_circ:
  "an(x\<^sup>\<circ>) * x * n(x\<^sup>\<circ>) \<le> x * bot"
  by (metis an_circ_left_unfold an_mult an_split mult_assoc n_mult_right_bot)

lemma an_circ_invariant:
  "an(x\<^sup>\<circ>) * x \<le> x * an(x\<^sup>\<circ>)"
proof -
  have 1: "an(x\<^sup>\<circ>) * x * an(x\<^sup>\<circ>) \<le> x * an(x\<^sup>\<circ>)"
    by (metis an_case_split_left mult_assoc order_refl)
  have "an(x\<^sup>\<circ>) * x * n(x\<^sup>\<circ>) \<le> x * an(x\<^sup>\<circ>)"
    by (metis an_circ_x_n_circ order_trans mult_right_isotone bot_least)
  thus ?thesis
    using 1 an_case_split_right by blast
qed

lemma ani_circ:
  "ani(x)\<^sup>\<circ> = 1 \<squnion> ani(x)"
  by (simp add: ani_def mult_L_circ)

lemma ani_circ_left_unfold:
  "ani(x\<^sup>\<circ>) = ani(x * x\<^sup>\<circ>)"
  by (simp add: an_circ_left_unfold ani_def)

lemma an_circ_import:
  "an(y) * x \<le> x * an(y) \<Longrightarrow> an(y) * x\<^sup>\<circ> = an(y) * (an(y) * x)\<^sup>\<circ>"
  by (metis an_n_def n_circ_import)

lemma preserves_L:
  "preserves L (-p)"
  using L_left_zero preserves_equation_test mult_assoc by force

end

class an_omega_algebra = n_omega_algebra_2 + an_semiring + while +
  assumes while_Omega_def: "p \<star> y = (p * y)\<^sup>\<Omega> * -p"
begin

lemma an_split_omega_omega:
  "an(x\<^sup>\<omega>) * x\<^sup>\<omega> \<le> x\<^sup>\<omega> * bot"
  by (meson an_antitone an_split mult_left_isotone omega_sub_vector order_trans)

lemma an_omega_below_an_star:
  "an(x\<^sup>\<omega>) \<le> an(x\<^sup>\<star>)"
  by (simp add: an_n_order n_star_below_n_omega)

lemma an_omega_below_an:
  "an(x\<^sup>\<omega>) \<le> an(x)"
  by (simp add: an_n_order n_below_n_omega)

lemma an_omega_induct:
  "an(x * y \<squnion> z) \<le> an(y) \<Longrightarrow> an(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<le> an(y)"
  by (simp add: an_n_order n_omega_induct)

lemma an_star_mult:
  "an(y) \<le> an(x * y) \<Longrightarrow> an(x\<^sup>\<star> * y) = an(x\<^sup>\<star>) * an(y)"
  by (metis an_dist_sup an_n_L an_n_order n_dist_sup n_star_mult)

lemma an_omega_mult:
  "an(x\<^sup>\<omega> * y) = an(x\<^sup>\<omega>)"
  by (simp add: an_n_equal n_omega_mult)

lemma an_star_left_unfold:
  "an(x\<^sup>\<star>) = an(x * x\<^sup>\<star>)"
  by (simp add: an_n_equal n_star_left_unfold)

lemma an_star_x_n_star:
  "an(x\<^sup>\<star>) * x * n(x\<^sup>\<star>) \<le> x * bot"
  by (metis an_n_L an_split n_mult n_mult_right_bot n_star_left_unfold mult_assoc)

lemma an_star_invariant:
  "an(x\<^sup>\<star>) * x \<le> x * an(x\<^sup>\<star>)"
proof -
  have 1: "an(x\<^sup>\<star>) * x * an(x\<^sup>\<star>) \<le> x * an(x\<^sup>\<star>)"
    using an_case_split_left mult_assoc by auto
  have "an(x\<^sup>\<star>) * x * n(x\<^sup>\<star>) \<le> x * an(x\<^sup>\<star>)"
    by (metis an_star_x_n_star order_trans mult_right_isotone bot_least)
  thus ?thesis
    using 1 an_case_split_right by auto
qed

lemma n_an_star_unfold_invariant:
  "n(an(x\<^sup>\<star>) * x\<^sup>\<omega>) \<le> an(x) * n(x * an(x\<^sup>\<star>) * x\<^sup>\<omega>)"
proof -
  have "n(an(x\<^sup>\<star>) * x\<^sup>\<omega>) \<le> an(x)"
    using an_star_left_unfold an_case_split_right an_mult_left_upper_bound n_export_an by fastforce
  thus ?thesis
    by (smt an_star_invariant le_iff_sup mult_assoc mult_right_dist_sup n_isotone n_order omega_unfold)
qed

lemma ani_omega_below_ani_star:
  "ani(x\<^sup>\<omega>) \<le> ani(x\<^sup>\<star>)"
  by (simp add: an_omega_below_an_star ani_an_order)

lemma ani_omega_below_ani:
  "ani(x\<^sup>\<omega>) \<le> ani(x)"
  by (simp add: an_omega_below_an ani_an_order)

lemma ani_star:
  "ani(x)\<^sup>\<star> = 1 \<squnion> ani(x)"
  by (simp add: ani_def mult_L_star)

lemma ani_omega:
  "ani(x)\<^sup>\<omega> = ani(x) * L"
  by (simp add: L_left_zero ani_def mult_L_omega mult_assoc)

lemma ani_omega_induct:
  "ani(x * y \<squnion> z) \<le> ani(y) \<Longrightarrow> ani(x\<^sup>\<omega> \<squnion> x\<^sup>\<star> * z) \<le> ani(y)"
  by (simp add: an_omega_induct ani_an_order)

lemma ani_omega_mult:
  "ani(x\<^sup>\<omega> * y) = ani(x\<^sup>\<omega>)"
  by (simp add: an_omega_mult ani_def)

lemma ani_star_left_unfold:
  "ani(x\<^sup>\<star>) = ani(x * x\<^sup>\<star>)"
  by (simp add: an_star_left_unfold ani_def)

lemma an_star_import:
  "an(y) * x \<le> x * an(y) \<Longrightarrow> an(y) * x\<^sup>\<star> = an(y) * (an(y) * x)\<^sup>\<star>"
  by (metis an_n_def n_star_import)

lemma an_omega_export:
  "an(y) * x \<le> x * an(y) \<Longrightarrow> an(y) * x\<^sup>\<omega> = (an(y) * x)\<^sup>\<omega>"
  by (metis an_n_def n_omega_export)

lemma an_omega_import:
  "an(y) * x \<le> x * an(y) \<Longrightarrow> an(y) * x\<^sup>\<omega> = an(y) * (an(y) * x)\<^sup>\<omega>"
  by (simp add: an_mult_idempotent omega_import)

end

text \<open>Theorem 22\<close>

sublocale an_omega_algebra < nL_omega: an_itering where circ = Omega
  apply unfold_locales
  by (rule while_Omega_def)

context an_omega_algebra
begin

lemma preserves_star:
  "nL_omega.preserves x (-p) \<Longrightarrow> nL_omega.preserves (x\<^sup>\<star>) (-p)"
  by (simp add: nL_omega.preserves_def star.circ_simulate)

end

end

