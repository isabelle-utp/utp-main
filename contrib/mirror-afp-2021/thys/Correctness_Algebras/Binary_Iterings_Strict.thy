(* Title:      Strict Binary Iterings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Strict Binary Iterings\<close>

theory Binary_Iterings_Strict

imports Stone_Kleene_Relation_Algebras.Iterings Binary_Iterings

begin

class strict_itering = itering + while +
  assumes while_def: "x \<star> y = x\<^sup>\<circ> * y"
begin

text \<open>Theorem 8.1\<close>

subclass extended_binary_itering
  apply unfold_locales
  apply (metis circ_loop_fixpoint circ_slide_1 sup_commute while_def mult_assoc)
  apply (metis circ_sup mult_assoc while_def)
  apply (simp add: mult_left_dist_sup while_def)
  apply (simp add: while_def mult_assoc)
  apply (metis circ_simulate_left_plus mult_assoc mult_left_isotone mult_right_dist_sup mult_1_right while_def)
  apply (metis circ_simulate_right_plus mult_assoc mult_left_isotone mult_right_dist_sup while_def)
  by (metis circ_loop_fixpoint mult_right_sub_dist_sup_right while_def mult_assoc)

text \<open>Theorem 13.1\<close>

lemma while_associative:
  "(x \<star> y) * z = x \<star> (y * z)"
  by (simp add: while_def mult_assoc)

text \<open>Theorem 13.3\<close>

lemma while_one_mult:
  "(x \<star> 1) * x = x \<star> x"
  by (simp add: while_def)

lemma while_back_loop_is_fixpoint:
  "is_fixpoint (\<lambda>x . x * y \<squnion> z) (z * (y \<star> 1))"
  by (simp add: circ_back_loop_is_fixpoint while_def)

text \<open>Theorem 13.4\<close>

lemma while_sumstar_var:
  "(x \<squnion> y) \<star> z = ((x \<star> 1) * y) \<star> ((x \<star> 1) * z)"
  by (simp add: while_sumstar_3 while_associative)

text \<open>Theorem 13.2\<close>

lemma while_mult_1_assoc:
  "(x \<star> 1) * y = x \<star> y"
  by (simp add: while_def)

(*
lemma "y \<star> (x \<star> 1) \<le> x \<star> (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops
lemma "y * x \<le> (1 \<squnion> x) * (y \<star> 1) \<Longrightarrow> (x \<squnion> y) \<star> 1 = x \<star> (y \<star> 1)" oops
lemma while_square_1: "x \<star> 1 = (x * x) \<star> (x \<squnion> 1)" oops
lemma while_absorb_below_one: "y * x \<le> x \<Longrightarrow> y \<star> x \<le> 1 \<star> x" oops
*)

end

class bounded_strict_itering = bounded_itering + strict_itering
begin

subclass bounded_extended_binary_itering ..

text \<open>Theorem 13.6\<close>

lemma while_top_2:
  "top \<star> z = top * z"
  by (simp add: circ_top while_def)

text \<open>Theorem 13.5\<close>

lemma while_mult_top_2:
  "(x * top) \<star> z = z \<squnion> x * top * z"
  by (metis circ_left_top mult_assoc while_def while_left_unfold)

text \<open>Theorem 13 counterexamples\<close>

(*
lemma while_one_top: "1 \<star> x = top" nitpick [expect=genuine,card=2] oops
lemma while_top: "top \<star> x = top" nitpick [expect=genuine,card=2] oops
lemma while_sub_mult_one: "x * (1 \<star> y) \<le> 1 \<star> x" oops
lemma while_unfold_below_1: "x = y * x \<Longrightarrow> x \<le> y \<star> 1" oops
lemma while_unfold_below: "x = z \<squnion> y * x \<Longrightarrow> x \<le> y \<star> z" nitpick [expect=genuine,card=2] oops
lemma while_unfold_below: "x \<le> z \<squnion> y * x \<Longrightarrow> x \<le> y \<star> z" nitpick [expect=genuine,card=2] oops
lemma while_mult_top: "(x * top) \<star> z = z \<squnion> x * top" nitpick [expect=genuine,card=2] oops
lemma tarski_mult_top_idempotent: "x * top = x * top * x * top" oops

lemma while_loop_is_greatest_postfixpoint: "is_greatest_postfixpoint (\<lambda>x . y * x \<squnion> z) (y \<star> z)" nitpick [expect=genuine,card=2] oops
lemma while_loop_is_greatest_fixpoint: "is_greatest_fixpoint (\<lambda>x . y * x \<squnion> z) (y \<star> z)" nitpick [expect=genuine,card=2] oops
lemma while_sub_while_zero: "x \<star> z \<le> (x \<star> y) \<star> z" oops
lemma while_while_sub_associative: "x \<star> (y \<star> z) \<le> (x \<star> y) \<star> z" oops
lemma tarski: "x \<le> x * top * x * top" oops
lemma tarski_top_omega_below: "x * top \<le> (x * top) \<star> bot" nitpick [expect=genuine,card=2] oops
lemma tarski_top_omega: "x * top = (x * top) \<star> bot" nitpick [expect=genuine,card=2] oops
lemma tarski_below_top_omega: "x \<le> (x * top) \<star> bot" nitpick [expect=genuine,card=2] oops
lemma tarski: "x = bot \<or> top * x * top = top" oops
lemma "1 = (x * bot) \<star> 1" oops
lemma "1 \<squnion> x * bot = x \<star> 1" oops
lemma "x = x * (x \<star> 1)" oops
lemma "x * (x \<star> 1) = x \<star> 1" oops
lemma "x \<star> 1 = x \<star> (1 \<star> 1)" oops
lemma "(x \<squnion> y) \<star> 1 = (x \<star> (y \<star> 1)) \<star> 1" oops
lemma "z \<squnion> y * x = x \<Longrightarrow> y \<star> z \<le> x" oops
lemma "y * x = x \<Longrightarrow> y \<star> x \<le> x" oops
lemma "z \<squnion> x * y = x \<Longrightarrow> z * (y \<star> 1) \<le> x" oops
lemma "x * y = x \<Longrightarrow> x * (y \<star> 1) \<le> x" oops
lemma "x * z = z * y \<Longrightarrow> x \<star> z \<le> z * (y \<star> 1)" oops
*)

end

class binary_itering_unary = extended_binary_itering + circ +
  assumes circ_def: "x\<^sup>\<circ> = x \<star> 1"
begin

text \<open>Theorem 50.7\<close>

subclass left_conway_semiring
  apply unfold_locales
  using circ_def while_left_unfold apply simp
  apply (metis circ_def mult_1_right while_one_mult_below while_slide)
  using circ_def while_one_while while_sumstar_2 by auto

end

class strict_binary_itering = binary_itering + circ +
  assumes while_associative: "(x \<star> y) * z = x \<star> (y * z)"
  assumes circ_def: "x\<^sup>\<circ> = x \<star> 1"
begin

text \<open>Theorem 2.8\<close>

subclass itering
  apply unfold_locales
  apply (simp add: circ_def while_associative while_sumstar)
  apply (metis circ_def mult_1_right while_associative while_productstar while_slide)
  apply (metis circ_def mult_1_right while_associative mult_1_left while_slide while_simulate_right_plus)
  by (metis circ_def mult_1_right while_associative mult_1_left while_simulate_left_plus mult_right_dist_sup)

text \<open>Theorem 8.5\<close>

subclass extended_binary_itering
  apply unfold_locales
  by (simp add: while_associative while_increasing mult_assoc)

end

end

