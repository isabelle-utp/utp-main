(* Title:      Modal N-Semirings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Modal N-Semirings\<close>

theory N_Semirings_Modal

imports N_Semirings_Boolean

begin

class n_diamond_semiring = n_semiring + diamond +
  assumes ndiamond_def: "|x>y = n(x * y * L)"
begin

lemma diamond_x_bot:
  "|x>bot = n(x)"
  using n_mult_bot ndiamond_def mult_assoc by auto

lemma diamond_x_1:
  "|x>1 = n(x * L)"
  by (simp add: ndiamond_def)

lemma diamond_x_L:
  "|x>L = n(x * L)"
  by (simp add: L_left_zero ndiamond_def mult_assoc)

lemma diamond_x_top:
  "|x>top = n(x * L)"
  by (metis mult_assoc n_top_L ndiamond_def top_mult_top)

lemma diamond_x_n:
  "|x>n(y) = n(x * y)"
  by (simp add: n_mult ndiamond_def)

lemma diamond_bot_y:
  "|bot>y = bot"
  by (simp add: n_bot ndiamond_def)

lemma diamond_1_y:
  "|1>y = n(y * L)"
  by (simp add: ndiamond_def)

lemma diamond_1_n:
  "|1>n(y) = n(y)"
  by (simp add: diamond_1_y n_n_L)

lemma diamond_L_y:
  "|L>y = 1"
  by (simp add: L_left_zero n_L ndiamond_def)

lemma diamond_top_y:
  "|top>y = 1"
  by (metis sup_left_top sup_right_top diamond_L_y mult_right_dist_sup n_dist_sup n_top ndiamond_def)

lemma diamond_n_y:
  "|n(x)>y = n(x) * n(y * L)"
  by (simp add: n_export ndiamond_def mult_assoc)

lemma diamond_n_bot:
  "|n(x)>bot = bot"
  by (simp add: n_bot n_mult_right_bot ndiamond_def)

lemma diamond_n_1:
  "|n(x)>1 = n(x)"
  using diamond_1_n diamond_1_y diamond_x_1 by auto

lemma diamond_n_n:
  "|n(x)>n(y) = n(x) * n(y)"
  by (simp add: diamond_x_n n_export)

lemma diamond_n_n_same:
  "|n(x)>n(x) = n(x)"
  by (simp add: diamond_n_n n_mult_idempotent)

text \<open>Theorem 23.1\<close>

lemma diamond_left_dist_sup:
  "|x \<squnion> y>z = |x>z \<squnion> |y>z"
  by (simp add: mult_right_dist_sup n_dist_sup ndiamond_def)

text \<open>Theorem 23.2\<close>

lemma diamond_right_dist_sup:
  "|x>(y \<squnion> z) = |x>y \<squnion> |x>z"
  by (simp add: mult_left_dist_sup n_dist_sup ndiamond_def semiring.distrib_right)

text \<open>Theorem 23.3\<close>

lemma diamond_associative:
  "|x * y>z = |x>(y * z)"
  by (simp add: ndiamond_def mult_assoc)

text \<open>Theorem 23.3\<close>

lemma diamond_left_mult:
  "|x * y>z = |x>|y>z"
  using n_mult_ni ndiamond_def ni_def mult_assoc by auto

lemma diamond_right_mult:
  "|x>(y * z) = |x>|y>z"
  using diamond_associative diamond_left_mult by force

lemma diamond_n_export:
  "|n(x) * y>z = n(x) * |y>z"
  by (simp add: n_export ndiamond_def mult_assoc)

lemma diamond_diamond_export:
  "||x>y>z = |x>y * |z>1"
  using diamond_n_y ndiamond_def by auto

lemma diamond_left_isotone:
  "x \<le> y \<Longrightarrow> |x>z \<le> |y>z"
  by (metis diamond_left_dist_sup le_iff_sup)

lemma diamond_right_isotone:
  "y \<le> z \<Longrightarrow> |x>y \<le> |x>z"
  by (metis diamond_right_dist_sup le_iff_sup)

lemma diamond_isotone:
  "w \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> |w>x \<le> |y>z"
  by (meson diamond_left_isotone diamond_right_isotone order_trans)

definition ndiamond_L :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<parallel> _ \<guillemotright> _" [50,90] 95)
  where "\<parallel>x\<guillemotright>y \<equiv> n(x * y) * L"

lemma ndiamond_to_L:
  "\<parallel>x\<guillemotright>y = |x>n(y) * L"
  by (simp add: diamond_x_n ndiamond_L_def)

lemma ndiamond_from_L:
  "|x>y = n(\<parallel>x\<guillemotright>(y * L))"
  by (simp add: n_n_L ndiamond_def mult_assoc ndiamond_L_def)

lemma diamond_L_ni:
  "\<parallel>x\<guillemotright>y = ni(x * y)"
  by (simp add: ni_def ndiamond_L_def)

lemma diamond_L_associative:
  "\<parallel>x * y\<guillemotright>z = \<parallel>x\<guillemotright>(y * z)"
  by (simp add: diamond_L_ni mult_assoc)

lemma diamond_L_left_mult:
  "\<parallel>x * y\<guillemotright>z = \<parallel>x\<guillemotright>\<parallel>y\<guillemotright>z"
  using diamond_L_associative diamond_L_ni ni_mult by auto

lemma diamond_L_right_mult:
  "\<parallel>x\<guillemotright>(y * z) = \<parallel>x\<guillemotright>\<parallel>y\<guillemotright>z"
  using diamond_L_associative diamond_L_left_mult by auto

lemma diamond_L_left_dist_sup:
  "\<parallel>x \<squnion> y\<guillemotright>z = \<parallel>x\<guillemotright>z \<squnion> \<parallel>y\<guillemotright>z"
  by (simp add: diamond_L_ni mult_right_dist_sup ni_dist_sup)

lemma diamond_L_x_ni:
  "\<parallel>x\<guillemotright>ni(y) = ni(x * y)"
  using n_mult_ni ni_def ndiamond_L_def by auto

lemma diamond_L_left_isotone:
  "x \<le> y \<Longrightarrow> \<parallel>x\<guillemotright>z \<le> \<parallel>y\<guillemotright>z"
  using mult_left_isotone ni_def ni_isotone ndiamond_L_def by auto

lemma diamond_L_right_isotone:
  "y \<le> z \<Longrightarrow> \<parallel>x\<guillemotright>y \<le> \<parallel>x\<guillemotright>z"
  using mult_right_isotone ni_def ni_isotone ndiamond_L_def by auto

lemma diamond_L_isotone:
  "w \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> \<parallel>w\<guillemotright>x \<le> \<parallel>y\<guillemotright>z"
  using diamond_L_ni mult_isotone ni_isotone by force

end

class n_box_semiring = n_diamond_semiring + an_semiring + box +
  assumes nbox_def: "|x]y = an(x * an(y * L) * L)"
begin

text \<open>Theorem 23.8\<close>

lemma box_diamond:
  "|x]y = an( |x>an(y * L) * L)"
  by (simp add: an_n_L nbox_def ndiamond_def)

text \<open>Theorem 23.4\<close>

lemma diamond_box:
  "|x>y = an( |x]an(y * L) * L)"
  using n_an_def n_mult nbox_def ndiamond_def mult_assoc by force

lemma box_x_bot:
  "|x]bot = an(x * L)"
  by (simp add: an_bot nbox_def)

lemma box_x_1:
  "|x]1 = an(x)"
  using an_L an_mult_an nbox_def mult_assoc by auto

lemma box_x_L:
  "|x]L = an(x)"
  using box_x_1 L_left_zero nbox_def by auto

lemma box_x_top:
  "|x]top = an(x)"
  by (metis box_diamond box_x_1 box_x_bot diamond_top_y)

lemma box_x_n:
  "|x]n(y) = an(x * an(y) * L)"
  by (simp add: an_n_L nbox_def)

lemma box_x_an:
  "|x]an(y) = an(x * y)"
  using an_mult n_an_def nbox_def by auto

lemma box_bot_y:
  "|bot]y = 1"
  by (simp add: an_bot nbox_def)

lemma box_1_y:
  "|1]y = n(y * L)"
  by (simp add: n_an_def nbox_def)

lemma box_1_n:
  "|1]n(y) = n(y)"
  using box_1_y diamond_1_n diamond_1_y by auto

lemma box_1_an:
  "|1]an(y) = an(y)"
  by (simp add: box_x_an)

lemma box_L_y:
  "|L]y = bot"
  by (simp add: L_left_zero an_L nbox_def)

lemma box_top_y:
  "|top]y = bot"
  by (simp add: box_diamond an_L diamond_top_y)

lemma box_n_y:
  "|n(x)]y = an(x) \<squnion> n(y * L)"
  using an_export_n n_an_def nbox_def mult_assoc by auto

lemma box_an_y:
  "|an(x)]y = n(x) \<squnion> n(y * L)"
  by (metis an_n_def box_n_y n_an_def)

lemma box_n_bot:
  "|n(x)]bot = an(x)"
  by (simp add: box_x_bot an_n_L)

lemma box_an_bot:
  "|an(x)]bot = n(x)"
  by (simp add: box_x_bot n_an_def)

lemma box_n_1:
  "|n(x)]1 = 1"
  using box_x_1 ani_an_L ani_n by auto

lemma box_an_1:
  "|an(x)]1 = 1"
  using box_x_1 ani_an ani_an_L by fastforce

lemma box_n_n:
  "|n(x)]n(y) = an(x) \<squnion> n(y)"
  using box_1_n box_1_y box_n_y by auto

lemma box_an_n:
  "|an(x)]n(y) = n(x) \<squnion> n(y)"
  using box_x_n an_dist_sup n_an_def n_dist_sup by auto

lemma box_n_an:
  "|n(x)]an(y) = an(x) \<squnion> an(y)"
  by (simp add: box_x_an an_export_n)

lemma box_an_an:
  "|an(x)]an(y) = n(x) \<squnion> an(y)"
  by (simp add: box_x_an an_export)

lemma box_n_n_same:
  "|n(x)]n(x) = 1"
  by (simp add: box_n_n an_complement)

lemma box_an_an_same:
  "|an(x)]an(x) = 1"
  using box_an_bot an_bot an_complement_bot nbox_def by auto

text \<open>Theorem 23.5\<close>

lemma box_left_dist_sup:
  "|x \<squnion> y]z = |x]z * |y]z"
  using an_dist_sup nbox_def semiring.distrib_right by auto

lemma box_right_dist_sup:
  "|x](y \<squnion> z) = an(x * an(y * L) * an(z * L) * L)"
  by (simp add: an_dist_sup mult_right_dist_sup nbox_def mult_assoc)

lemma box_associative:
  "|x * y]z = an(x * y * an(z * L) * L)"
  by (simp add: nbox_def)

text \<open>Theorem 23.7\<close>

lemma box_left_mult:
  "|x * y]z = |x]|y]z"
  using box_x_an nbox_def mult_assoc by auto

lemma box_right_mult:
  "|x](y * z) = an(x * an(y * z * L) * L)"
  by (simp add: nbox_def)

text \<open>Theorem 23.6\<close>

lemma box_right_mult_n_n:
  "|x](n(y) * n(z)) = |x]n(y) * |x]n(z)"
  by (smt an_dist_sup an_export_n an_n_L mult_assoc mult_left_dist_sup mult_right_dist_sup nbox_def)

lemma box_right_mult_an_n:
  "|x](an(y) * n(z)) = |x]an(y) * |x]n(z)"
  by (metis an_n_def box_right_mult_n_n)

lemma box_right_mult_n_an:
  "|x](n(y) * an(z)) = |x]n(y) * |x]an(z)"
  by (simp add: box_right_mult_an_n box_x_an box_x_n an_mult_commutative n_an_mult_commutative)

lemma box_right_mult_an_an:
  "|x](an(y) * an(z)) = |x]an(y) * |x]an(z)"
  by (metis an_dist_sup box_x_an mult_left_dist_sup)

lemma box_n_export:
  "|n(x) * y]z = an(x) \<squnion> |y]z"
  using box_left_mult box_n_an nbox_def by auto

lemma box_an_export:
  "|an(x) * y]z = n(x) \<squnion> |y]z"
  using box_an_an box_left_mult nbox_def by auto

lemma box_left_antitone:
  "y \<le> x \<Longrightarrow> |x]z \<le> |y]z"
  by (smt an_mult_commutative an_order box_diamond box_left_dist_sup le_iff_sup)

lemma box_right_isotone:
  "y \<le> z \<Longrightarrow> |x]y \<le> |x]z"
  by (metis an_antitone mult_left_isotone mult_right_isotone nbox_def)

lemma box_antitone_isotone:
  "y \<le> w \<Longrightarrow> x \<le> z \<Longrightarrow> |w]x \<le> |y]z"
  by (meson box_left_antitone box_right_isotone order.trans)

definition nbox_L :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<parallel> _ \<rbrakk> _" [50,90] 95)
  where "\<parallel>x\<rbrakk>y \<equiv> an(x * an(y) * L) * L"

lemma nbox_to_L:
  "\<parallel>x\<rbrakk>y = |x]n(y) * L"
  by (simp add: box_x_n nbox_L_def)

lemma nbox_from_L:
  "|x]y = n(\<parallel>x\<rbrakk>(y * L))"
  using an_n_def nbox_def nbox_L_def by auto

lemma diamond_x_an:
  "|x>an(y) = n(x * an(y) * L)"
  by (simp add: ndiamond_def)

lemma diamond_1_an:
  "|1>an(y) = an(y)"
  using box_1_an box_1_y diamond_1_y by auto

lemma diamond_an_y:
  "|an(x)>y = an(x) * n(y * L)"
  by (simp add: n_export_an ndiamond_def mult_assoc)

lemma diamond_an_bot:
  "|an(x)>bot = bot"
  by (simp add: an_mult_right_zero n_bot ndiamond_def)

lemma diamond_an_1:
  "|an(x)>1 = an(x)"
  using an_n_def diamond_x_1 by auto

lemma diamond_an_n:
  "|an(x)>n(y) = an(x) * n(y)"
  by (simp add: diamond_x_n n_export_an)

lemma diamond_n_an:
  "|n(x)>an(y) = n(x) * an(y)"
  using an_n_def diamond_n_y by auto

lemma diamond_an_an:
  "|an(x)>an(y) = an(x) * an(y)"
  using diamond_an_y an_n_def by auto

lemma diamond_an_an_same:
  "|an(x)>an(x) = an(x)"
  by (simp add: diamond_an_an an_mult_idempotent)

lemma diamond_an_export:
  "|an(x) * y>z = an(x) * |y>z"
  using diamond_an_an diamond_box diamond_left_mult by auto

lemma box_ani:
  "|x]y = an(x * ani(y * L))"
  by (simp add: ani_def nbox_def mult_assoc)

lemma box_x_n_ani:
  "|x]n(y) = an(x * ani(y))"
  by (simp add: box_x_n ani_def mult_assoc)

lemma box_L_ani:
  "\<parallel>x\<rbrakk>y = ani(x * ani(y))"
  using box_x_n_ani ani_def nbox_to_L by auto

lemma box_L_left_mult:
  "\<parallel>x * y\<rbrakk>z = \<parallel>x\<rbrakk>\<parallel>y\<rbrakk>z"
  using an_mult n_an_def mult_assoc nbox_L_def by auto

lemma diamond_x_an_ani:
  "|x>an(y) = n(x * ani(y))"
  by (simp add: ani_def ndiamond_def mult_assoc)

lemma box_L_left_antitone:
  "y \<le> x \<Longrightarrow> \<parallel>x\<rbrakk>z \<le> \<parallel>y\<rbrakk>z"
  by (simp add: box_L_ani ani_antitone mult_left_isotone)

lemma box_L_right_isotone:
  "y \<le> z \<Longrightarrow> \<parallel>x\<rbrakk>y \<le> \<parallel>x\<rbrakk>z"
  using ani_antitone ani_def mult_right_isotone mult_assoc nbox_L_def by auto

lemma box_L_antitone_isotone:
  "y \<le> w \<Longrightarrow> x \<le> z \<Longrightarrow> \<parallel>w\<rbrakk>x \<le> \<parallel>y\<rbrakk>z"
  using ani_antitone ani_def mult_isotone mult_assoc nbox_L_def by force

end

class n_box_omega_algebra = n_box_semiring + an_omega_algebra
begin

lemma diamond_omega:
  "|x\<^sup>\<omega>>y = |x\<^sup>\<omega>>z"
  by (simp add: n_omega_mult ndiamond_def mult_assoc)

lemma box_omega:
  "|x\<^sup>\<omega>]y = |x\<^sup>\<omega>]z"
  by (metis box_diamond diamond_omega)

lemma an_box_omega_induct:
  "|x]an(y) * n(z * L) \<le> an(y) \<Longrightarrow> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]z \<le> an(y)"
  by (smt an_dist_sup an_omega_induct an_omega_mult box_left_dist_sup box_x_an mult_assoc n_an_def nbox_def)

lemma n_box_omega_induct:
  "|x]n(y) * n(z * L) \<le> n(y) \<Longrightarrow> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]z \<le> n(y)"
  by (simp add: an_box_omega_induct n_an_def)

lemma an_box_omega_induct_an:
  "|x]an(y) * an(z) \<le> an(y) \<Longrightarrow> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(z) \<le> an(y)"
  using an_box_omega_induct an_n_def by auto

text \<open>Theorem 23.13\<close>

lemma n_box_omega_induct_n:
  "|x]n(y) * n(z) \<le> n(y) \<Longrightarrow> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]n(z) \<le> n(y)"
  using an_box_omega_induct_an n_an_def by force

lemma n_diamond_omega_induct:
  "n(y) \<le> |x>n(y) \<squnion> n(z * L) \<Longrightarrow> n(y) \<le> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>z"
  using diamond_x_n mult_right_dist_sup n_dist_sup n_omega_induct n_omega_mult ndiamond_def mult_assoc by force

lemma an_diamond_omega_induct:
  "an(y) \<le> |x>an(y) \<squnion> n(z * L) \<Longrightarrow> an(y) \<le> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>z"
  by (metis n_diamond_omega_induct an_n_def)

text \<open>Theorem 23.9\<close>

lemma n_diamond_omega_induct_n:
  "n(y) \<le> |x>n(y) \<squnion> n(z) \<Longrightarrow> n(y) \<le> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>n(z)"
  using box_1_n box_1_y n_diamond_omega_induct by auto

lemma an_diamond_omega_induct_an:
  "an(y) \<le> |x>an(y) \<squnion> an(z) \<Longrightarrow> an(y) \<le> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>an(z)"
  using an_diamond_omega_induct an_n_def by auto

lemma box_segerberg_an:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y) = an(y) * |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>](n(y) \<squnion> |x]an(y))"
proof (rule order.antisym)
  have "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y) \<le> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]|x]an(y)"
    by (smt box_left_dist_sup box_left_mult box_omega sup_right_isotone box_left_antitone mult_right_dist_sup star.right_plus_below_circ)
  hence "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y) \<le> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>](n(y) \<squnion> |x]an(y))"
    using box_right_isotone order_lesseq_imp sup.cobounded2 by blast
  thus"|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y) \<le> an(y) * |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>](n(y) \<squnion> |x]an(y))"
    by (metis le_sup_iff box_1_an box_left_antitone order_refl star_left_unfold_equal an_mult_least_upper_bound nbox_def)
next
  have "an(y) * |x](n(y) \<squnion> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y)) * (n(y) \<squnion> |x]an(y)) = |x]( |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y) * an(y)) * an(y)"
    by (smt sup_bot_left an_export an_mult_commutative box_right_mult_an_an mult_assoc mult_right_dist_sup n_complement_bot nbox_def)
  hence 1: "an(y) * |x](n(y) \<squnion> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y)) * (n(y) \<squnion> |x]an(y)) \<le> n(y) \<squnion> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y)"
    by (smt sup_assoc sup_commute sup_ge2 box_1_an box_left_dist_sup box_left_mult mult_left_dist_sup omega_unfold star_left_unfold_equal star.circ_plus_one)
  have "n(y) * |x](n(y) \<squnion> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y)) * (n(y) \<squnion> |x]an(y)) \<le> n(y) \<squnion> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y)"
    by (smt sup_ge1 an_n_def mult_left_isotone n_an_mult_left_lower_bound n_mult_left_absorb_sup nbox_def order_trans)
  thus "an(y) * |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>](n(y) \<squnion> |x]an(y)) \<le> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y)"
    using 1 by (smt an_case_split_left an_shunting_an mult_assoc n_box_omega_induct_n n_dist_sup nbox_def nbox_from_L)
qed

text \<open>Theorem 23.16\<close>

lemma box_segerberg_n:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]n(y) = n(y) * |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>](an(y) \<squnion> |x]n(y))"
  using box_segerberg_an an_n_def n_an_def by force

lemma diamond_segerberg_an:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>an(y) = an(y) \<squnion> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>(n(y) * |x>an(y))"
  by (smt an_export an_n_L box_diamond box_segerberg_an diamond_box mult_assoc n_an_def)

text \<open>Theorem 23.12\<close>

lemma diamond_segerberg_n:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>n(y) = n(y) \<squnion> |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>(an(y) * |x>n(y))"
  using diamond_segerberg_an an_n_L n_an_def by auto

text \<open>Theorem 23.11\<close>

lemma diamond_star_unfold_n:
  "|x\<^sup>\<star>>n(y) = n(y) \<squnion> |an(y) * x>|x\<^sup>\<star>>n(y)"
proof -
  have "|x\<^sup>\<star>>n(y) = n(y) \<squnion> n(y) * |x * x\<^sup>\<star>>n(y) \<squnion> |an(y) * x * x\<^sup>\<star>>n(y)"
    by (smt sup_assoc sup_commute sup_bot_right an_complement an_complement_bot diamond_an_n diamond_left_dist_sup diamond_n_export diamond_n_n_same mult_assoc mult_left_one mult_right_dist_sup star_left_unfold_equal)
  thus ?thesis
    by (metis diamond_left_mult diamond_x_n n_sup_left_absorb_mult)
qed

lemma diamond_star_unfold_an:
  "|x\<^sup>\<star>>an(y) = an(y) \<squnion> |n(y) * x>|x\<^sup>\<star>>an(y)"
  by (metis an_n_def diamond_star_unfold_n n_an_def)

text \<open>Theorem 23.15\<close>

lemma box_star_unfold_n:
  "|x\<^sup>\<star>]n(y) = n(y) * |n(y) * x]|x\<^sup>\<star>]n(y)"
  by (smt an_export an_n_L box_diamond diamond_box diamond_star_unfold_an n_an_def n_export)

lemma box_star_unfold_an:
  "|x\<^sup>\<star>]an(y) = an(y) * |an(y) * x]|x\<^sup>\<star>]an(y)"
  by (metis an_n_def box_star_unfold_n)

text \<open>Theorem 23.10\<close>

lemma diamond_omega_unfold_n:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>n(y) = n(y) \<squnion> |an(y) * x>|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>n(y)"
  by (smt sup_assoc sup_commute diamond_an_export diamond_left_dist_sup diamond_right_dist_sup diamond_star_unfold_n diamond_x_n n_omega_mult n_plus_complement_intro_n omega_unfold)

lemma diamond_omega_unfold_an:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>an(y) = an(y) \<squnion> |n(y) * x>|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>an(y)"
  by (metis an_n_def diamond_omega_unfold_n n_an_def)

text \<open>Theorem 23.14\<close>

lemma box_omega_unfold_n:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]n(y) = n(y) * |n(y) * x]|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]n(y)"
  by (smt an_export an_n_L box_diamond diamond_box diamond_omega_unfold_an n_an_def n_export)

lemma box_omega_unfold_an:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y) = an(y) * |an(y) * x]|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y)"
  by (metis an_n_def box_omega_unfold_n)

lemma box_cut_iteration_an:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]an(y) = |(an(y) * x)\<^sup>\<omega> \<squnion> (an(y) * x)\<^sup>\<star>]an(y)"
  apply (rule order.antisym)
  apply (meson semiring.add_mono an_case_split_left box_left_antitone omega_isotone order_refl star.circ_isotone)
  by (smt (z3) an_box_omega_induct_an an_mult_commutative box_omega_unfold_an nbox_def order_refl)

lemma box_cut_iteration_n:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>]n(y) = |(n(y) * x)\<^sup>\<omega> \<squnion> (n(y) * x)\<^sup>\<star>]n(y)"
  using box_cut_iteration_an n_an_def by auto

lemma diamond_cut_iteration_an:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>an(y) = |(n(y) * x)\<^sup>\<omega> \<squnion> (n(y) * x)\<^sup>\<star>>an(y)"
  using box_cut_iteration_n diamond_box n_an_def by auto

lemma diamond_cut_iteration_n:
  "|x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>n(y) = |(an(y) * x)\<^sup>\<omega> \<squnion> (an(y) * x)\<^sup>\<star>>n(y)"
  using box_cut_iteration_an an_n_L diamond_box by auto

lemma ni_diamond_omega_induct:
  "ni(y) \<le> \<parallel>x\<guillemotright>ni(y) \<squnion> ni(z) \<Longrightarrow> ni(y) \<le> \<parallel>x\<^sup>\<omega> \<squnion> x\<^sup>\<star>\<guillemotright>z"
  by (metis diamond_L_left_dist_sup diamond_L_x_ni diamond_L_ni ni_dist_sup ni_omega_induct ni_omega_mult)

lemma ani_diamond_omega_induct:
  "ani(y) \<le> \<parallel>x\<guillemotright>ani(y) \<squnion> ni(z) \<Longrightarrow> ani(y) \<le> \<parallel>x\<^sup>\<omega> \<squnion> x\<^sup>\<star>\<guillemotright>z"
  by (metis ni_ani ni_diamond_omega_induct)

lemma n_diamond_omega_L:
  "|n(x\<^sup>\<omega>) * L>y = |x\<^sup>\<omega>>y"
  using L_left_zero mult_1_right n_L n_export n_omega_mult ndiamond_def mult_assoc by auto

lemma n_diamond_loop:
  "|x\<^sup>\<Omega>>y = |x\<^sup>\<omega> \<squnion> x\<^sup>\<star>>y"
  by (metis Omega_def diamond_left_dist_sup n_diamond_omega_L)

text \<open>Theorem 24.1\<close>

lemma cut_iteration_loop:
  "|x\<^sup>\<Omega>>n(y) = |(an(y) * x)\<^sup>\<Omega>>n(y)"
  using diamond_cut_iteration_n n_diamond_loop by auto

lemma cut_iteration_while_loop:
  "|x\<^sup>\<Omega>>n(y) = |(an(y) * x)\<^sup>\<Omega> * n(y)>n(y)"
  using cut_iteration_loop diamond_left_mult diamond_n_n_same by auto

text \<open>Theorem 24.1\<close>

lemma cut_iteration_while_loop_2:
  "|x\<^sup>\<Omega>>n(y) = |an(y) \<star> x>n(y)"
  by (metis cut_iteration_while_loop an_uminus n_an_def while_Omega_def)

lemma modal_while:
  assumes "-q * -p * L \<le> x * -p * L \<and> -p \<le> -q \<squnion> -r"
    shows "-p \<le> |n((-q * x)\<^sup>\<omega>) * L \<squnion> (-q * x)\<^sup>\<star> * --q>(-r)"
proof -
  have 1: "--q * -p \<le> |-q * x>(-p) \<squnion> --q * -r"
    using assms mult_right_isotone sup.coboundedI2 tests_dual.sup_complement_intro by auto
  have "-q * -p = n(-q * -q * -p * L)"
    using an_uminus n_export_an mult_assoc mult_1_right n_L tests_dual.sup_idempotent by auto
  also have "... \<le> n(-q * x * -p * L)"
    by (metis assms n_isotone mult_right_isotone mult_assoc)
  also have "... \<le> |-q * x>(-p) \<squnion> --q * -r"
    by (simp add: ndiamond_def)
  finally have "-p \<le> |-q * x>(-p) \<squnion> --q * -r"
    using 1 by (smt sup_assoc le_iff_sup tests_dual.inf_cases sub_comm)
  thus ?thesis
    by (smt L_left_zero an_diamond_omega_induct_an an_uminus diamond_left_dist_sup mult_assoc n_n_L n_omega_mult ndiamond_def sub_mult_closed)
qed

lemma modal_while_loop:
  "-q * -p * L \<le> x * -p * L \<and> -p \<le> -q \<squnion> -r \<Longrightarrow> -p \<le> |(-q * x)\<^sup>\<Omega> * --q>(-r)"
  by (metis L_left_zero Omega_def modal_while mult_assoc mult_right_dist_sup)

text \<open>Theorem 24.2\<close>

lemma modal_while_loop_2:
  "-q * -p * L \<le> x * -p * L \<and> -p \<le> -q \<squnion> -r \<Longrightarrow> -p \<le> |-q \<star> x>(-r)"
  by (simp add: while_Omega_def modal_while_loop)

lemma modal_while_2:
  assumes "-p * L \<le> x * -p * L"
    shows "-p \<le> |n((-q * x)\<^sup>\<omega>) * L \<squnion> (-q * x)\<^sup>\<star> * --q>(--q)"
proof -
  have "-p \<le> |-q * x>(-p) \<squnion> --q"
    by (smt (verit, del_insts) assms an_uminus tests_dual.double_negation n_an_def n_isotone ndiamond_def diamond_an_export sup_assoc sup_commute le_iff_sup tests_dual.inf_complement_intro)
  thus ?thesis
    by (smt L_left_zero an_diamond_omega_induct_an an_uminus diamond_left_dist_sup mult_assoc tests_dual.sup_idempotent n_n_L n_omega_mult ndiamond_def)
qed

end

class n_modal_omega_algebra = n_box_omega_algebra +
  assumes n_star_induct: "n(x * y) \<le> n(y) \<longrightarrow> n(x\<^sup>\<star> * y) \<le> n(y)"
begin

lemma n_star_induct_sup:
  "n(z \<squnion> x * y) \<le> n(y) \<Longrightarrow> n(x\<^sup>\<star> * z) \<le> n(y)"
  by (metis an_dist_sup an_mult_least_upper_bound an_n_order n_mult_right_upper_bound n_star_induct star_L_split)

lemma n_star_induct_star:
  "n(x * y) \<le> n(y) \<Longrightarrow> n(x\<^sup>\<star>) \<le> n(y)"
  using n_star_induct n_star_mult by auto

lemma n_star_induct_iff:
  "n(x * y) \<le> n(y) \<longleftrightarrow> n(x\<^sup>\<star> * y) \<le> n(y)"
  by (metis mult_left_isotone n_isotone n_star_induct order_trans star.circ_increasing)

lemma n_star_bot:
  "n(x) = bot \<longleftrightarrow> n(x\<^sup>\<star>) = bot"
  by (metis sup_bot_right le_iff_sup mult_1_right n_one n_star_induct_iff)

lemma n_diamond_star_induct:
  "|x>n(y) \<le> n(y) \<Longrightarrow> |x\<^sup>\<star>>n(y) \<le> n(y)"
  by (simp add: diamond_x_n n_star_induct)

lemma n_diamond_star_induct_sup:
  "|x>n(y) \<squnion> n(z) \<le> n(y) \<Longrightarrow> |x\<^sup>\<star>>n(z) \<le> n(y)"
  by (simp add: diamond_x_n n_dist_sup n_star_induct_sup)

lemma n_diamond_star_induct_iff:
  "|x>n(y) \<le> n(y) \<longleftrightarrow> |x\<^sup>\<star>>n(y) \<le> n(y)"
  using diamond_x_n n_star_induct_iff by auto

lemma an_star_induct:
  "an(y) \<le> an(x * y) \<Longrightarrow> an(y) \<le> an(x\<^sup>\<star> * y)"
  using an_n_order n_star_induct by auto

lemma an_star_induct_sup:
  "an(y) \<le> an(z \<squnion> x * y) \<Longrightarrow> an(y) \<le> an(x\<^sup>\<star> * z)"
  using an_n_order n_star_induct_sup by auto

lemma an_star_induct_star:
  "an(y) \<le> an(x * y) \<Longrightarrow> an(y) \<le> an(x\<^sup>\<star>)"
  by (simp add: an_n_order n_star_induct_star)

lemma an_star_induct_iff:
  "an(y) \<le> an(x * y) \<longleftrightarrow> an(y) \<le> an(x\<^sup>\<star> * y)"
  using an_n_order n_star_induct_iff by auto

lemma an_star_one:
  "an(x) = 1 \<longleftrightarrow> an(x\<^sup>\<star>) = 1"
  by (metis an_n_equal an_bot n_star_bot n_bot)

lemma an_box_star_induct:
  "an(y) \<le> |x]an(y) \<Longrightarrow> an(y) \<le> |x\<^sup>\<star>]an(y)"
  by (simp add: an_star_induct box_x_an)

lemma an_box_star_induct_sup:
  "an(y) \<le> |x]an(y) * an(z) \<Longrightarrow> an(y) \<le> |x\<^sup>\<star>]an(z)"
  by (simp add: an_star_induct_sup an_dist_sup an_mult_commutative box_x_an)

lemma an_box_star_induct_iff:
  "an(y) \<le> |x]an(y) \<longleftrightarrow> an(y) \<le> |x\<^sup>\<star>]an(y)"
  using an_star_induct_iff box_x_an by auto

lemma box_star_segerberg_an:
  "|x\<^sup>\<star>]an(y) = an(y) * |x\<^sup>\<star>](n(y) \<squnion> |x]an(y))"
proof (rule order.antisym)
  show "|x\<^sup>\<star>]an(y) \<le> an(y) * |x\<^sup>\<star>](n(y) \<squnion> |x]an(y))"
    by (smt (verit) sup_ge2 box_1_an box_left_dist_sup box_left_mult box_right_isotone mult_right_isotone star.circ_right_unfold)
next
  have "an(y) * |x\<^sup>\<star>](n(y) \<squnion> |x]an(y)) \<le> an(y) * |x]an(y)"
    by (metis sup_bot_left an_complement_bot box_an_an box_left_antitone box_x_an mult_left_dist_sup mult_left_one mult_right_isotone star.circ_reflexive)
  thus "an(y) * |x\<^sup>\<star>](n(y) \<squnion> |x]an(y)) \<le> |x\<^sup>\<star>]an(y)"
    by (smt an_box_star_induct_sup an_case_split_left an_dist_sup an_mult_least_upper_bound box_left_antitone box_left_mult box_right_mult_an_an star.left_plus_below_circ nbox_def)
qed

lemma box_star_segerberg_n:
  "|x\<^sup>\<star>]n(y) = n(y) * |x\<^sup>\<star>](an(y) \<squnion> |x]n(y))"
  using box_star_segerberg_an an_n_def n_an_def by auto

lemma diamond_segerberg_an:
  "|x\<^sup>\<star>>an(y) = an(y) \<squnion> |x\<^sup>\<star>>(n(y) * |x>an(y))"
  by (smt an_export an_n_L box_diamond box_star_segerberg_an diamond_box mult_assoc n_an_def)

lemma diamond_star_segerberg_n:
  "|x\<^sup>\<star>>n(y) = n(y) \<squnion> |x\<^sup>\<star>>(an(y) * |x>n(y))"
  using an_n_def diamond_segerberg_an n_an_def by auto

lemma box_cut_star_iteration_an:
  "|x\<^sup>\<star>]an(y) = |(an(y) * x)\<^sup>\<star>]an(y)"
  by (smt an_box_star_induct_sup an_mult_commutative an_mult_complement_intro_an order.antisym box_an_export box_star_unfold_an nbox_def order_refl)

lemma box_cut_star_iteration_n:
  "|x\<^sup>\<star>]n(y) = |(n(y) * x)\<^sup>\<star>]n(y)"
  using box_cut_star_iteration_an n_an_def by auto

lemma diamond_cut_star_iteration_an:
  "|x\<^sup>\<star>>an(y) = |(n(y) * x)\<^sup>\<star>>an(y)"
  using box_cut_star_iteration_an diamond_box n_an_def by auto

lemma diamond_cut_star_iteration_n:
  "|x\<^sup>\<star>>n(y) = |(an(y) * x)\<^sup>\<star>>n(y)"
  using box_cut_star_iteration_an an_n_L diamond_box by auto

lemma ni_star_induct:
  "ni(x * y) \<le> ni(y) \<Longrightarrow> ni(x\<^sup>\<star> * y) \<le> ni(y)"
  using n_star_induct ni_n_order by auto

lemma ni_star_induct_sup:
  "ni(z \<squnion> x * y) \<le> ni(y) \<Longrightarrow> ni(x\<^sup>\<star> * z) \<le> ni(y)"
  by (simp add: ni_n_order n_star_induct_sup)

lemma ni_star_induct_star:
  "ni(x * y) \<le> ni(y) \<Longrightarrow> ni(x\<^sup>\<star>) \<le> ni(y)"
  using ni_n_order n_star_induct_star by auto

lemma ni_star_induct_iff:
  "ni(x * y) \<le> ni(y) \<longleftrightarrow> ni(x\<^sup>\<star> * y) \<le> ni(y)"
  using ni_n_order n_star_induct_iff by auto

lemma ni_star_bot:
  "ni(x) = bot \<longleftrightarrow> ni(x\<^sup>\<star>) = bot"
  using ni_n_bot n_star_bot by auto

lemma ni_diamond_star_induct:
  "\<parallel>x\<guillemotright>ni(y) \<le> ni(y) \<Longrightarrow> \<parallel>x\<^sup>\<star>\<guillemotright>ni(y) \<le> ni(y)"
  by (simp add: diamond_L_x_ni ni_star_induct)

lemma ni_diamond_star_induct_sup:
  "\<parallel>x\<guillemotright>ni(y) \<squnion> ni(z) \<le> ni(y) \<Longrightarrow> \<parallel>x\<^sup>\<star>\<guillemotright>ni(z) \<le> ni(y)"
  by (simp add: diamond_L_x_ni ni_dist_sup ni_star_induct_sup)

lemma ni_diamond_star_induct_iff:
  "\<parallel>x\<guillemotright>ni(y) \<le> ni(y) \<longleftrightarrow> \<parallel>x\<^sup>\<star>\<guillemotright>ni(y) \<le> ni(y)"
  using diamond_L_x_ni ni_star_induct_iff by auto

lemma ani_star_induct:
  "ani(y) \<le> ani(x * y) \<Longrightarrow> ani(y) \<le> ani(x\<^sup>\<star> * y)"
  using an_star_induct ani_an_order by blast

lemma ani_star_induct_sup:
  "ani(y) \<le> ani(z \<squnion> x * y) \<Longrightarrow> ani(y) \<le> ani(x\<^sup>\<star> * z)"
  by (simp add: an_star_induct_sup ani_an_order)

lemma ani_star_induct_star:
  "ani(y) \<le> ani(x * y) \<Longrightarrow> ani(y) \<le> ani(x\<^sup>\<star>)"
  using an_star_induct_star ani_an_order by auto

lemma ani_star_induct_iff:
  "ani(y) \<le> ani(x * y) \<longleftrightarrow> ani(y) \<le> ani(x\<^sup>\<star> * y)"
  using an_star_induct_iff ani_an_order by auto

lemma ani_star_L:
  "ani(x) = L \<longleftrightarrow> ani(x\<^sup>\<star>) = L"
  using an_star_one ani_an_L by auto

lemma ani_box_star_induct:
  "ani(y) \<le> \<parallel>x\<rbrakk>ani(y) \<Longrightarrow> ani(y) \<le> \<parallel>x\<^sup>\<star>\<rbrakk>ani(y)"
  by (metis an_ani ani_def ani_star_induct_iff n_ani box_L_ani)

lemma ani_box_star_induct_iff:
  "ani(y) \<le> \<parallel>x\<rbrakk>ani(y) \<longleftrightarrow> ani(y) \<le> \<parallel>x\<^sup>\<star>\<rbrakk>ani(y)"
  using ani_box_star_induct box_L_left_antitone order_lesseq_imp star.circ_increasing by blast

lemma ani_box_star_induct_sup:
  "ani(y) \<le> \<parallel>x\<rbrakk>ani(y) \<Longrightarrow> ani(y) \<le> ani(z) \<Longrightarrow> ani(y) \<le> \<parallel>x\<^sup>\<star>\<rbrakk>ani(z)"
  by (meson ani_box_star_induct_iff box_L_right_isotone order_trans)

end

end

