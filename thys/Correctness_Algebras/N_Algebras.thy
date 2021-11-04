(* Title:      N-Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>N-Algebras\<close>

theory N_Algebras

imports Stone_Kleene_Relation_Algebras.Iterings Base Lattice_Ordered_Semirings

begin

class C_left_n_algebra = bounded_idempotent_left_semiring + bounded_distrib_lattice + n + L
begin

abbreviation C :: "'a \<Rightarrow> 'a" where "C x \<equiv> n(L) * top \<sqinter> x"

text \<open>AACP Theorem 3.38\<close>

lemma C_isotone:
  "x \<le> y \<longrightarrow> C x \<le> C y"
  using inf.sup_right_isotone by auto

text \<open>AACP Theorem 3.40\<close>

lemma C_decreasing:
  "C x \<le> x"
  by simp

end

class left_n_algebra = C_left_n_algebra +
  assumes n_dist_n_add            : "n(x) \<squnion> n(y) = n(n(x) * top \<squnion> y)"
  assumes n_export                : "n(x) * n(y) = n(n(x) * y)"
  assumes n_left_upper_bound      : "n(x) \<le> n(x \<squnion> y)"
  assumes n_nL_meet_L_nL0         : "n(L) * x = (x \<sqinter> L) \<squnion> n(L * bot) * x"
  assumes n_n_L_split_n_n_L_L     : "x * n(y) * L = x * bot \<squnion> n(x * n(y) * L) * L"
  assumes n_sub_nL                : "n(x) \<le> n(L)"
  assumes n_L_decreasing          : "n(x) * L \<le> x"
  assumes n_L_T_meet_mult_combined: "C (x * y) * z \<le> C x * y * C z"
  assumes n_n_top_split_n_top     : "x * n(y) * top \<le> x * bot \<squnion> n(x * y) * top"
  assumes n_top_meet_L_below_L    : "x * top * y \<sqinter> L \<le> x * L * y"
begin

subclass lattice_ordered_pre_left_semiring ..

lemma n_L_T_meet_mult_below:
  "C (x * y) \<le> C x * y"
proof -
  have "C (x * y) \<le> C x * y * C 1"
    by (meson order.trans mult_sub_right_one n_L_T_meet_mult_combined)
  also have "... \<le> C x * y"
    by (metis mult_1_right mult_left_sub_dist_inf_right)
  finally show ?thesis
    .
qed

text \<open>AACP Theorem 3.41\<close>

lemma n_L_T_meet_mult_propagate:
  "C x * y \<le> x * C y"
proof -
  have "C x * y \<le> C x * 1 * C y"
    by (metis mult_1_right mult_assoc n_L_T_meet_mult_combined mult_1_right)
  also have "... \<le> x * C y"
    by (simp add: mult_right_sub_dist_inf_right)
  finally show ?thesis
    .
qed

text \<open>AACP Theorem 3.43\<close>

lemma C_n_mult_closed:
  "C (n(x) * y) = n(x) * y"
  by (simp add: inf.absorb2 mult_isotone n_sub_nL)

text \<open>AACP Theorem 3.40\<close>

lemma meet_L_below_C:
  "x \<sqinter> L \<le> C x"
  by (simp add: le_supI1 n_nL_meet_L_nL0)

text \<open>AACP Theorem 3.42\<close>

lemma n_L_T_meet_mult:
  "C (x * y) = C x * y"
  apply (rule order.antisym)
  apply (rule n_L_T_meet_mult_below)
  by (smt (z3) C_n_mult_closed inf.boundedE inf.sup_monoid.add_assoc inf.sup_monoid.add_commute mult_right_sub_dist_inf mult_assoc)

text \<open>AACP Theorem 3.42\<close>

lemma C_mult_propagate:
  "C x * y = C x * C y"
  by (smt (z3) C_n_mult_closed order.eq_iff inf.left_commute inf.sup_monoid.add_commute mult_left_sub_dist_inf_right n_L_T_meet_mult_propagate)

text \<open>AACP Theorem 3.32\<close>

lemma meet_L_below_n_L:
  "x \<sqinter> L \<le> n(L) * x"
  by (simp add: n_nL_meet_L_nL0)

text \<open>AACP Theorem 3.27\<close>

lemma n_vector_meet_L:
  "x * top \<sqinter> L \<le> x * L"
  by (metis mult_1_right n_top_meet_L_below_L)

lemma n_right_upper_bound:
  "n(x) \<le> n(y \<squnion> x)"
  by (simp add: n_left_upper_bound sup_commute)

text \<open>AACP Theorem 3.1\<close>

lemma n_isotone:
  "x \<le> y \<Longrightarrow> n(x) \<le> n(y)"
  by (metis le_iff_sup n_left_upper_bound)

lemma n_add_left_zero:
  "n(bot) \<squnion> n(x) = n(x)"
  using le_iff_sup sup_bot_right sup_right_divisibility n_isotone by auto

text \<open>AACP Theorem 3.13\<close>

lemma n_mult_right_zero_L:
  "n(x) * bot \<le> L"
  by (meson bot_least mult_isotone n_L_decreasing n_sub_nL order_trans)

lemma n_add_left_top:
  "n(top) \<squnion> n(x) = n(top)"
  by (simp add: sup_absorb1 n_isotone)

text \<open>AACP Theorem 3.18\<close>

lemma n_n_L:
  "n(n(x) * L) = n(x)"
  by (metis order.antisym n_dist_n_add n_export n_sub_nL sup_bot_right sup_commute sup_top_left n_add_left_zero n_right_upper_bound)

lemma n_mult_transitive:
  "n(x) * n(x) \<le> n(x)"
  by (metis mult_right_isotone n_export n_sub_nL n_n_L)

lemma n_mult_left_absorb_add_sub:
  "n(x) * (n(x) \<squnion> n(y)) \<le> n(x)"
  by (metis mult_right_isotone n_dist_n_add n_export n_sub_nL n_n_L)

text \<open>AACP Theorem 3.21\<close>

lemma n_mult_left_lower_bound:
  "n(x) * n(y) \<le> n(x)"
  by (metis mult_right_isotone n_export n_sub_nL n_n_L)

text \<open>AACP Theorem 3.20\<close>

lemma n_mult_left_zero:
  "n(bot) * n(x) = n(bot)"
  by (metis n_export sup_absorb1 n_add_left_zero n_mult_left_lower_bound)

lemma n_mult_right_one:
  "n(x) * n(top) = n(x)"
  using n_dist_n_add n_export sup_commute n_add_left_zero by fastforce

lemma n_L_increasing:
  "n(x) \<le> n(n(x) * L)"
  by (simp add: n_n_L)

text \<open>AACP Theorem 3.2\<close>

lemma n_galois:
  "n(x) \<le> n(y) \<longleftrightarrow> n(x) * L \<le> y"
  by (metis mult_left_isotone n_L_decreasing n_L_increasing n_isotone order_trans)

lemma n_add_n_top:
  "n(x \<squnion> n(x) * top) = n(x)"
  by (metis n_dist_n_add sup.idem sup_commute)

text \<open>AACP Theorem 3.6\<close>

lemma n_L_below_nL_top:
  "L \<le> n(L) * top"
  by (metis inf_top.left_neutral meet_L_below_n_L)

text \<open>AACP Theorem 3.4\<close>

lemma n_less_eq_char_n:
  "x \<le> y \<longleftrightarrow> x \<le> y \<squnion> L \<and> C x \<le> y \<squnion> n(y) * top"
proof
  assume "x \<le> y"
  thus "x \<le> y \<squnion> L \<and> C x \<le> y \<squnion> n(y) * top"
    by (simp add: inf.coboundedI2 le_supI1)
next
  assume 1: "x \<le> y \<squnion> L \<and> C x \<le> y \<squnion> n(y) * top"
  hence "x \<le> y \<squnion> (x \<sqinter> L)"
    using sup_commute sup_inf_distrib2 by force
  also have "... \<le> y \<squnion> C x"
    using sup_right_isotone meet_L_below_C by blast
  also have "... \<le> y \<squnion> n(y) * top"
    using 1 by simp
  finally have "x \<le> y \<squnion> (L \<sqinter> n(y) * top)"
    using 1 by (simp add: sup_inf_distrib1)
  thus "x \<le> y"
    by (metis inf_commute n_L_decreasing order_trans sup_absorb1 n_vector_meet_L)
qed

text \<open>AACP Theorem 3.31\<close>

lemma n_L_decreasing_meet_L:
  "n(x) * L \<le> x \<sqinter> L"
  using n_sub_nL n_galois by auto

text \<open>AACP Theorem 3.5\<close>

lemma n_zero_L_zero:
  "n(bot) * L = bot"
  by (simp add: le_bot n_L_decreasing)

lemma n_L_top_below_L:
  "L * top \<le> L"
proof -
  have "n(L * bot) * L * top \<le> L * bot"
    by (metis dense_top_closed mult_isotone n_L_decreasing zero_vector mult_assoc)
  hence "n(L * bot) * L * top \<le> L"
    using order_lesseq_imp zero_right_mult_decreasing by blast
  hence "n(L) * L * top \<le> L"
    by (metis inf.absorb2 n_nL_meet_L_nL0 order.refl sup.absorb_iff1 top_right_mult_increasing mult_assoc)
  thus "L * top \<le> L"
    by (metis inf.absorb2 inf.sup_monoid.add_commute n_L_decreasing n_L_below_nL_top n_vector_meet_L)
qed

text \<open>AACP Theorem 3.9\<close>

lemma n_L_top_L:
  "L * top = L"
  by (simp add: order.antisym top_right_mult_increasing n_L_top_below_L)

text \<open>AACP Theorem 3.10\<close>

lemma n_L_below_L:
  "L * x \<le> L"
  by (metis mult_right_isotone top.extremum n_L_top_L)

text \<open>AACP Theorem 3.7\<close>

lemma n_nL_nT:
  "n(L) = n(top)"
  using order.eq_iff n_sub_nL n_add_left_top by auto

text \<open>AACP Theorem 3.8\<close>

lemma n_L_L:
  "n(L) * L = L"
  using order.antisym meet_L_below_n_L n_L_decreasing_meet_L by fastforce

lemma n_top_L:
  "n(top) * L = L"
  using n_L_L n_nL_nT by auto

text \<open>AACP Theorem 3.23\<close>

lemma n_n_L_split_n_L:
  "x * n(y) * L \<le> x * bot \<squnion> n(x * y) * L"
  by (metis n_n_L_split_n_n_L_L n_L_decreasing mult_assoc mult_left_isotone mult_right_isotone n_isotone sup_right_isotone)

text \<open>AACP Theorem 3.12\<close>

lemma n_L_split_n_L_L:
  "x * L = x * bot \<squnion> n(x * L) * L"
  apply (rule order.antisym)
  apply (metis mult_assoc n_n_L_split_n_L n_L_L)
  by (simp add: mult_right_isotone n_L_decreasing)

text \<open>AACP Theorem 3.11\<close>

lemma n_L_split_L:
  "x * L \<le> x * bot \<squnion> L"
  by (metis n_n_L_split_n_n_L_L n_sub_nL sup_right_isotone mult_assoc n_L_L n_galois)

text \<open>AACP Theorem 3.24\<close>

lemma n_split_top:
  "x * n(y) * top \<le> x * y \<squnion> n(x * y) * top"
proof -
  have "x * bot \<squnion> n(x * y) * top \<le> x * y \<squnion> n(x * y) * top"
    by (meson bot_least mult_isotone order.refl sup_left_isotone)
  thus ?thesis
    using order.trans n_n_top_split_n_top by blast
qed

text \<open>AACP Theorem 3.9\<close>

lemma n_L_L_L:
  "L * L = L"
  by (metis inf.sup_monoid.add_commute inf_absorb1 n_L_below_L n_L_top_L n_vector_meet_L)

text \<open>AACP Theorem 3.9\<close>

lemma n_L_top_L_L:
  "L * top * L = L"
  by (simp add: n_L_L_L n_L_top_L)

text \<open>AACP Theorem 3.19\<close>

lemma n_n_nL:
  "n(x) = n(x) * n(L)"
  by (simp add: n_export n_n_L)

lemma n_L_mult_idempotent:
  "n(L) * n(L) = n(L)"
  using n_n_nL by auto

text \<open>AACP Theorem 3.22\<close>

lemma n_n_L_n:
  "n(x * n(y) * L) \<le> n(x * y)"
  by (simp add: mult_right_isotone n_L_decreasing mult_assoc n_isotone)

text \<open>AACP Theorem 3.3\<close>

lemma n_less_eq_char:
  "x \<le> y \<longleftrightarrow> x \<le> y \<squnion> L \<and> x \<le> y \<squnion> n(y) * top"
  by (meson inf.coboundedI2 le_supI1 n_less_eq_char_n)

text \<open>AACP Theorem 3.28\<close>

lemma n_top_meet_L_split_L:
  "x * top * y \<sqinter> L \<le> x * bot \<squnion> L * y"
proof -
  have "x * top * y \<sqinter> L \<le> x * bot \<squnion> n(x * L) * L * y"
    by (smt n_top_meet_L_below_L mult_assoc n_L_L_L n_L_split_n_L_L mult_right_dist_sup mult_left_zero)
  also have "... \<le> x * bot \<squnion> x * L * y"
    using mult_left_isotone n_L_decreasing sup_right_isotone by force
  also have "... \<le> x * bot \<squnion> (x * bot \<squnion> L) * y"
    using mult_left_isotone sup_right_isotone n_L_split_L by blast
  also have "... = x * bot \<squnion> x * bot * y \<squnion> L * y"
    by (simp add: mult_right_dist_sup sup_assoc)
  also have "... = x * bot \<squnion> L * y"
    by (simp add: mult_assoc)
  finally show ?thesis
    .
qed

text \<open>AACP Theorem 3.29\<close>

lemma n_top_meet_L_L_meet_L:
  "x * top * y \<sqinter> L = x * L * y \<sqinter> L"
  apply (rule order.antisym)
  apply (simp add: n_top_meet_L_below_L)
  by (metis inf.sup_monoid.add_commute inf.sup_right_isotone mult_isotone order.refl top.extremum)

lemma n_n_top_below_n_L:
  "n(x * top) \<le> n(x * L)"
  by (meson order.trans n_L_decreasing_meet_L n_galois n_vector_meet_L)

text \<open>AACP Theorem 3.14\<close>

lemma n_n_top_n_L:
  "n(x * top) = n(x * L)"
  by (metis order.antisym mult_right_isotone n_isotone n_n_top_below_n_L top_greatest)

text \<open>AACP Theorem 3.30\<close>

lemma n_meet_L_0_below_0_meet_L:
  "(x \<sqinter> L) * bot \<le> x * bot \<sqinter> L"
  by (meson inf.boundedE inf.boundedI mult_right_sub_dist_inf_left zero_right_mult_decreasing)

text \<open>AACP Theorem 3.15\<close>

lemma n_n_L_below_L:
  "n(x) * L \<le> x * L"
  by (metis mult_assoc mult_left_isotone n_L_L_L n_L_decreasing)

lemma n_n_L_below_n_L_L:
  "n(x) * L \<le> n(x * L) * L"
  by (simp add: mult_left_isotone n_galois n_n_L_below_L)

text \<open>AACP Theorem 3.16\<close>

lemma n_below_n_L:
  "n(x) \<le> n(x * L)"
  by (simp add: n_galois n_n_L_below_L)

text \<open>AACP Theorem 3.17\<close>

lemma n_below_n_L_mult:
  "n(x) \<le> n(L) * n(x)"
  by (metis n_export order_trans meet_L_below_n_L n_L_decreasing_meet_L n_isotone n_n_L)

text \<open>AACP Theorem 3.33\<close>

lemma n_meet_L_below:
  "n(x) \<sqinter> L \<le> x"
  by (meson inf.coboundedI1 inf.coboundedI2 le_supI2 sup.cobounded1 top_right_mult_increasing n_less_eq_char)

text \<open>AACP Theorem 3.35\<close>

lemma n_meet_L_top_below_n_L:
  "(n(x) \<sqinter> L) * top \<le> n(x) * L"
proof -
  have "(n(x) \<sqinter> L) * top \<le> n(x) * top \<sqinter> L * top"
    by (meson mult_right_sub_dist_inf)
  thus ?thesis
    by (metis n_L_top_L n_vector_meet_L order_trans)
qed

text \<open>AACP Theorem 3.34\<close>

lemma n_meet_L_top_below:
  "(n(x) \<sqinter> L) * top \<le> x"
  using order.trans n_L_decreasing n_meet_L_top_below_n_L by blast

text \<open>AACP Theorem 3.36\<close>

lemma n_n_meet_L:
  "n(x) = n(x \<sqinter> L)"
  by (meson order.antisym inf.cobounded1 n_L_decreasing_meet_L n_galois n_isotone)

lemma n_T_below_n_meet:
  "n(x) * top = n(C x) * top"
  by (metis inf.absorb2 inf.sup_monoid.add_assoc meet_L_below_C n_n_meet_L)

text \<open>AACP Theorem 3.44\<close>

lemma n_C:
  "n(C x) = n(x)"
  by (metis n_T_below_n_meet n_export n_mult_right_one)

text \<open>AACP Theorem 3.37\<close>

lemma n_T_meet_L:
  "n(x) * top \<sqinter> L = n(x) * L"
  by (metis antisym_conv n_L_decreasing_meet_L n_n_L n_n_top_n_L n_vector_meet_L)

text \<open>AACP Theorem 3.39\<close>

lemma n_L_top_meet_L:
  "C L = L"
  by (simp add: n_L_L n_T_meet_L)

end

class n_algebra = left_n_algebra + idempotent_left_zero_semiring
begin

(* independence of axioms, checked in n_algebra without the respective axiom:
  lemma n_dist_n_add            : "n(x) \<squnion> n(y) = n(n(x) * top \<squnion> y)" nitpick [expect=genuine,card=5] oops
  lemma n_export                : "n(x) * n(y) = n(n(x) * y)" nitpick [expect=genuine,card=4] oops
  lemma n_left_upper_bound      : "n(x) \<le> n(x \<squnion> y)" nitpick [expect=genuine,card=5] oops
  lemma n_nL_meet_L_nL0         : "n(L) * x = (x \<sqinter> L) \<squnion> n(L * bot) * x" nitpick [expect=genuine,card=2] oops
  lemma n_n_L_split_n_n_L_L     : "x * n(y) * L = x * bot \<squnion> n(x * n(y) * L) * L" nitpick [expect=genuine,card=6] oops
  lemma n_sub_nL                : "n(x) \<le> n(L)" nitpick [expect=genuine,card=2] oops
  lemma n_L_decreasing          : "n(x) * L \<le> x" nitpick [expect=genuine,card=3] oops
  lemma n_L_T_meet_mult_combined: "C (x * y) * z \<le> C x * y * C z" nitpick [expect=genuine,card=4] oops
  lemma n_n_top_split_n_top     : "x * n(y) * top \<le> x * bot \<squnion> n(x * y) * top" nitpick [expect=genuine,card=4] oops
  lemma n_top_meet_L_below_L    : "x * top * y \<sqinter> L \<le> x * L * y" nitpick [expect=genuine,card=5] oops
*)

text \<open>AACP Theorem 3.25\<close>

lemma n_top_split_0:
  "n(x) * top * y \<le> x * y \<squnion> n(x * bot) * top"
proof -
  have 1: "n(x) * top * y \<sqinter> L \<le> x * y"
    using inf.coboundedI1 mult_left_isotone n_L_decreasing_meet_L n_top_meet_L_L_meet_L by force
  have "n(x) * top * y = n(x) * n(L) * top * y"
    using n_n_nL by auto
  also have "... = n(x) * ((top * y \<sqinter> L) \<squnion> n(L * bot) * top * y)"
    by (metis mult_assoc n_nL_meet_L_nL0)
  also have "... \<le> n(x) * (top * y \<sqinter> L) \<squnion> n(x) * n(L * bot) * top"
    by (metis sup_right_isotone mult_assoc mult_left_dist_sup mult_right_isotone top_greatest)
  also have "... \<le> (n(x) * top * y \<sqinter> L) \<squnion> n(n(x) * L * bot) * top"
    by (smt sup_left_isotone order.trans inf_greatest mult_assoc mult_left_sub_dist_inf_left mult_left_sub_dist_inf_right n_export n_galois n_sub_nL)
  also have "... \<le> x * y \<squnion> n(n(x) * L * bot) * top"
    using 1 sup_left_isotone by blast
  also have "... \<le> x * y \<squnion> n(x * bot) * top"
    using mult_left_isotone n_galois n_isotone order.refl sup_right_isotone by auto
  finally show ?thesis
    .
qed

text \<open>AACP Theorem 3.26\<close>

lemma n_top_split:
  "n(x) * top * y \<le> x * y \<squnion> n(x * y) * top"
  by (metis order.trans sup_bot_right mult_assoc sup_right_isotone mult_left_isotone mult_left_sub_dist_sup_right n_isotone n_top_split_0)

(*
lemma n_zero: "n(bot) = bot" nitpick [expect=genuine,card=2] oops
lemma n_one: "n(1) = bot" nitpick [expect=genuine,card=2] oops
lemma n_nL_one: "n(L) = 1" nitpick [expect=genuine,card=2] oops
lemma n_nT_one: "n(top) = 1" nitpick [expect=genuine,card=2] oops
lemma n_n_zero: "n(x) = n(x * bot)" nitpick [expect=genuine,card=2] oops
lemma n_dist_add: "n(x) \<squnion> n(y) = n(x \<squnion> y)" nitpick [expect=genuine,card=4] oops
lemma n_L_split: "x * n(y) * L = x * bot \<squnion> n(x * y) * L" nitpick [expect=genuine,card=3] oops
lemma n_split: "x \<le> x * bot \<squnion> n(x * L) * top" nitpick [expect=genuine,card=2] oops
lemma n_mult_top_1: "n(x * y) \<le> n(x * n(y) * top)" nitpick [expect=genuine,card=3] oops
lemma l91_1: "n(L) * x \<le> n(x * top) * top" nitpick [expect=genuine,card=3] oops
lemma meet_domain_top: "x \<sqinter> n(y) * top = n(y) * x" nitpick [expect=genuine,card=3] oops
lemma meet_domain_2: "x \<sqinter> n(y) * top \<le> n(L) * x" nitpick [expect=genuine,card=4] oops
lemma n_nL_top_n_top_meet_L_top_2: "n(L) * x * top \<le> n(x * top \<sqinter> L) * top" nitpick [expect=genuine,card=3] oops
lemma n_nL_top_n_top_meet_L_top_1: "n(x * top \<sqinter> L) * top \<le> n(L) * x * top" nitpick [expect=genuine,card=2] oops
lemma l9: "x * bot \<sqinter> L \<le> n(x * L) * L" nitpick [expect=genuine,card=4] oops
lemma l18_2: "n(x * L) * L \<le> n(x) * L" nitpick [expect=genuine,card=3] oops
lemma l51_1: "n(x) * L \<le> (x \<sqinter> L) * bot" nitpick [expect=genuine,card=2] oops
lemma l51_2: "(x \<sqinter> L) * bot \<le> n(x) * L" nitpick [expect=genuine,card=4] oops

lemma n_split_equal: "x \<squnion> n(x * L) * top = x * bot \<squnion> n(x * L) * top" nitpick [expect=genuine,card=2] oops
lemma n_split_top: "x * top \<le> x * bot \<squnion> n(x * L) * top" nitpick [expect=genuine,card=2] oops
lemma n_mult: "n(x * n(y) * L) = n(x * y)" nitpick [expect=genuine,card=3] oops
lemma n_mult_1: "n(x * y) \<le> n(x * n(y) * L)" nitpick [expect=genuine,card=3] oops
lemma n_mult_top: "n(x * n(y) * top) = n(x * y)" nitpick [expect=genuine,card=3] oops
lemma n_mult_right_upper_bound: "n(x * y) \<le> n(z) \<longleftrightarrow> n(x) \<le> n(z) \<and> x * n(y) * L \<le> x * bot \<squnion> n(z) * L" nitpick [expect=genuine,card=2] oops
lemma meet_domain: "x \<sqinter> n(y) * z = n(y) * (x \<sqinter> z)" nitpick [expect=genuine,card=3] oops
lemma meet_domain_1: "x \<sqinter> n(y) * z \<le> n(y) * x" nitpick [expect=genuine,card=3] oops
lemma meet_domain_top_3: "x \<sqinter> n(y) * top \<le> n(y) * x" nitpick [expect=genuine,card=3] oops
lemma n_n_top_n_top_split_n_n_top_top: "n(x) * top \<squnion> x * n(y) * top = x * bot \<squnion> n(x * n(y) * top) * top" nitpick [expect=genuine,card=2] oops
lemma n_n_top_n_top_split_n_n_top_top_1: "x * bot \<squnion> n(x * n(y) * top) * top \<le> n(x) * top \<squnion> x * n(y) * top" nitpick [expect=genuine,card=5] oops
lemma n_n_top_n_top_split_n_n_top_top_2: "n(x) * top \<squnion> x * n(y) * top \<le> x * bot \<squnion> n(x * n(y) * top) * top" nitpick [expect=genuine,card=2] oops
lemma n_nL_top_n_top_meet_L_top: "n(L) * x * top = n(x * top \<sqinter> L) * top" nitpick [expect=genuine,card=2] oops
lemma l18: "n(x) * L = n(x * L) * L" nitpick [expect=genuine,card=3] oops
lemma l22: "x * bot \<sqinter> L = n(x) * L" nitpick [expect=genuine,card=2] oops
lemma l22_1: "x * bot \<sqinter> L = n(x * L) * L" nitpick [expect=genuine,card=2] oops
lemma l22_2: "x \<sqinter> L = n(x) * L" nitpick [expect=genuine,card=3] oops
lemma l22_3: "x \<sqinter> L = n(x * L) * L" nitpick [expect=genuine,card=3] oops
lemma l22_4: "x \<sqinter> L \<le> n(x) * L" nitpick [expect=genuine,card=3] oops
lemma l22_5: "x * bot \<sqinter> L \<le> n(x) * L" nitpick [expect=genuine,card=4] oops
lemma l23: "x * top \<sqinter> L = n(x) * L" nitpick [expect=genuine,card=3] oops
lemma l51: "n(x) * L = (x \<sqinter> L) * bot" nitpick [expect=genuine,card=2] oops
lemma l91: "x = x * top \<longrightarrow> n(L) * x \<le> n(x) * top" nitpick [expect=genuine,card=3] oops
lemma l92: "x = x * top \<longrightarrow> n(L) * x \<le> n(x \<sqinter> L) * top" nitpick [expect=genuine,card=3] oops
lemma "x \<sqinter> L \<le> n(x) * top" nitpick [expect=genuine,card=3] oops
lemma n_meet_comp: "n(x) \<sqinter> n(y) \<le> n(x) * n(y)" nitpick [expect=genuine,card=3] oops

lemma n_n_meet_L_n_zero: "n(x) = (n(x) \<sqinter> L) \<squnion> n(x * bot)" oops
lemma n_below_n_zero: "n(x) \<le> x \<squnion> n(x * bot)" oops
lemma n_n_top_split_n_L_n_zero_top: "n(x) * top = n(x) * L \<squnion> n(x * bot) * top" oops
lemma n_meet_L_0_0_meet_L: "(x \<sqinter> L) * bot = x * bot \<sqinter> L" oops
*)

end

end

