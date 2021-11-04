(* Title:      Test Iterings
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Test Iterings\<close>

theory Test_Iterings

imports Stone_Kleene_Relation_Algebras.Iterings Tests

begin

class test_itering = itering + tests + while +
  assumes while_def: "p \<star> y = (p * y)\<^sup>\<circ> * -p"
begin

lemma wnf_lemma_5:
  "(-p \<squnion> -q) * (-q * x \<squnion> --q * y) = -q * x \<squnion> --q * -p * y"
  by (smt (z3) mult_left_dist_sup sup_commute tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.sup_complement_intro tests_dual.sba_dual.sup_idempotent tests_dual.sup_idempotent mult_assoc tests_dual.wnf_lemma_3)

lemma test_case_split_left_equal:
  "-z * x = -z * y \<Longrightarrow> --z * x = --z * y \<Longrightarrow> x = y"
  by (metis case_split_left_equal tests_dual.inf_complement)

lemma preserves_equation:
  "-y * x \<le> x * -y \<longleftrightarrow> -y * x = -y * x * -y"
  apply (rule iffI)
  apply (simp add: test_preserves_equation tests_dual.sub_bot_least)
  by (simp add: test_preserves_equation tests_dual.sub_bot_least)

text \<open>Theorem 5\<close>

lemma preserve_test:
  "-y * x \<le> x * -y \<Longrightarrow> -y * x\<^sup>\<circ> = -y * x\<^sup>\<circ> * -y"
  using circ_simulate preserves_equation by blast

text \<open>Theorem 5\<close>

lemma import_test:
  "-y * x \<le> x * -y \<Longrightarrow> -y * x\<^sup>\<circ> = -y * (-y * x)\<^sup>\<circ>"
  by (simp add: circ_import tests_dual.sub_bot_least)

definition ite :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<lhd> _ \<rhd> _" [58,58,58] 57)
  where "x \<lhd> p \<rhd> y \<equiv> p * x \<squnion> -p * y"

definition it :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<rhd> _" [58,58] 57)
  where "p \<rhd> x \<equiv> p * x \<squnion> -p"

(*
definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<star>" 59)
  where "p \<star> y \<equiv> (p * y)\<^sup>\<circ> * -p"
*)

definition assigns :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "assigns x p q \<equiv> x = x * (p * q \<squnion> -p * -q)"

definition preserves :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "preserves x p \<equiv> p * x \<le> x * p \<and> -p * x \<le> x * -p"

lemma ite_neg:
  "x \<lhd> -p \<rhd> y = y \<lhd> --p \<rhd> x"
  by (simp add: ite_def sup_commute)

lemma ite_import_true:
  "x \<lhd> -p \<rhd> y = -p * x \<lhd> -p \<rhd> y"
  by (metis ite_def tests_dual.sup_idempotent mult_assoc)

lemma ite_import_false:
  "x \<lhd> -p \<rhd> y = x \<lhd> -p \<rhd> --p * y"
  by (metis ite_import_true ite_neg)

lemma ite_import_true_false:
  "x \<lhd> -p \<rhd> y = -p * x \<lhd> -p \<rhd> --p * y"
  using ite_import_false ite_import_true by auto

lemma ite_context_true:
  "-p * (x \<lhd> -p \<rhd> y) = -p * x"
  by (metis sup_monoid.add_0_left tests_dual.sup_right_zero tests_dual.top_double_complement wnf_lemma_5 sup_bot_right ite_def mult_assoc mult_left_zero)

lemma ite_context_false:
  "--p * (x \<lhd> -p \<rhd> y) = --p * y"
  by (metis ite_neg ite_context_true)

lemma ite_context_import:
  "-p * (x \<lhd> -q \<rhd> y) = -p * (x \<lhd> -p * -q \<rhd> y)"
  by (smt ite_def mult_assoc tests_dual.sup_complement_intro tests_dual.sub_sup_demorgan tests_dual.sup_idempotent mult_left_dist_sup)

lemma ite_conjunction:
  "(x \<lhd> -q \<rhd> y) \<lhd> -p \<rhd> y = x \<lhd> -p * -q \<rhd> y"
  by (smt sup_assoc sup_commute ite_def mult_assoc tests_dual.sub_sup_demorgan mult_left_dist_sup mult_right_dist_sup tests_dual.inf_complement_intro)

lemma ite_disjunction:
  "x \<lhd> -p \<rhd> (x \<lhd> -q \<rhd> y) = x \<lhd> -p \<squnion> -q \<rhd> y"
  by (smt (z3) tests_dual.sba_dual.sub_sup_closed sup_assoc ite_def mult_assoc tests_dual.sup_complement_intro tests_dual.sub_sup_demorgan mult_left_dist_sup mult_right_dist_sup tests_dual.inf_demorgan)

lemma wnf_lemma_6:
  "(-p \<squnion> -q) * (x \<lhd> --p * -q \<rhd> y) = (-p \<squnion> -q) * (y \<lhd> -p \<rhd> x)"
  by (smt (z3) ite_conjunction ite_context_false ite_context_true semiring.distrib_right tests_dual.sba_dual.inf_cases_2 tests_dual.sba_dual.sub_inf_def tests_dual.sba_dual.sup_complement_intro tests_dual.sub_complement)

lemma it_ite:
  "-p \<rhd> x = x \<lhd> -p \<rhd> 1"
  by (simp add: it_def ite_def)

lemma it_neg:
  "--p \<rhd> x = 1 \<lhd> -p \<rhd> x"
  using it_ite ite_neg by auto

lemma it_import_true:
  "-p \<rhd> x = -p \<rhd> -p * x"
  using it_ite ite_import_true by auto

lemma it_context_true:
  "-p * (-p \<rhd> x) = -p * x"
  by (simp add: it_ite ite_context_true)

lemma it_context_false:
  "--p * (-p \<rhd> x) = --p"
  using it_ite ite_context_false by force

lemma while_unfold_it:
  "-p \<star> x = -p \<rhd> x * (-p \<star> x)"
  by (metis circ_loop_fixpoint it_def mult_assoc while_def)

lemma while_context_false:
  "--p * (-p \<star> x) = --p"
  by (metis it_context_false while_unfold_it)

lemma while_context_true:
  "-p * (-p \<star> x) = -p * x * (-p \<star> x)"
  by (metis it_context_true mult_assoc while_unfold_it)

lemma while_zero:
  "bot \<star> x = 1"
  by (metis circ_zero mult_left_one mult_left_zero one_def while_def)

lemma wnf_lemma_7:
  "1 * (bot \<star> 1) = 1"
  by (simp add: while_zero)

lemma while_import_condition:
  "-p \<star> x = -p \<star> -p * x"
  by (metis mult_assoc tests_dual.sup_idempotent while_def)

lemma while_import_condition_2:
  "-p * -q \<star> x = -p * -q \<star> -p * x"
  by (metis mult_assoc tests_dual.sup_idempotent sub_comm while_def)

lemma wnf_lemma_8:
  "-r * (-p \<squnion> --p * -q) \<star> (x \<lhd> --p * -q \<rhd> y) = -r * (-p \<squnion> -q) \<star> (y \<lhd> -p \<rhd> x)"
  by (metis mult_assoc while_def wnf_lemma_6 tests_dual.sba_dual.sup_complement_intro)

text \<open>Theorem 6 - see Theorem 31 on page 329 of Back and von Wright, Acta Informatica 36:295-334, 1999\<close>

lemma split_merge_loops:
  assumes "--p * y \<le> y * --p"
    shows "(-p \<squnion> -q) \<star> (x \<lhd> -p \<rhd> y) = (-p \<star> x) * (-q \<star> y)"
proof -
  have "-p \<squnion> -q \<star> (x \<lhd> -p \<rhd> y) = (-p * x \<squnion> --p * -q * y)\<^sup>\<circ> * --p * --q"
    by (smt ite_def mult_assoc sup_commute tests_dual.inf_demorgan while_def wnf_lemma_5)
  thus ?thesis
    by (smt assms circ_sup_1 circ_slide import_test mult_assoc preserves_equation sub_comm while_context_false while_def)
qed

lemma assigns_same:
  "assigns x (-p) (-p)"
  by (simp add: assigns_def)

lemma preserves_equation_test:
  "preserves x (-p) \<longleftrightarrow> -p * x = -p * x * -p \<and> --p * x = --p * x * --p"
  using preserves_def preserves_equation by auto

lemma preserves_test:
  "preserves (-q) (-p)"
  using tests_dual.sub_commutative preserves_def by auto

lemma preserves_zero:
  "preserves bot (-p)"
  using tests_dual.sba_dual.sub_bot_def preserves_test by blast

lemma preserves_one:
  "preserves 1 (-p)"
  using preserves_def by force

lemma preserves_sup:
  "preserves x (-p) \<Longrightarrow> preserves y (-p) \<Longrightarrow> preserves (x \<squnion> y) (-p)"
  by (simp add: mult_left_dist_sup mult_right_dist_sup preserves_equation_test)

lemma preserves_mult:
  "preserves x (-p) \<Longrightarrow> preserves y (-p) \<Longrightarrow> preserves (x * y) (-p)"
  by (smt (verit, best) mult_assoc preserves_equation_test)

lemma preserves_ite:
  "preserves x (-p) \<Longrightarrow> preserves y (-p) \<Longrightarrow> preserves (x \<lhd> -q \<rhd> y) (-p)"
  by (simp add: ite_def preserves_mult preserves_sup preserves_test)

lemma preserves_it:
  "preserves x (-p) \<Longrightarrow> preserves (-q \<rhd> x) (-p)"
  by (simp add: it_ite preserves_ite preserves_one)

lemma preserves_circ:
  "preserves x (-p) \<Longrightarrow> preserves (x\<^sup>\<circ>) (-p)"
  by (meson circ_simulate preserves_def)

lemma preserves_while:
  "preserves x (-p) \<Longrightarrow> preserves (-q \<star> x) (-p)"
  using while_def preserves_circ preserves_mult preserves_test by auto

lemma preserves_test_neg:
  "preserves x (-p) \<Longrightarrow> preserves x (--p)"
  using preserves_def by auto

lemma preserves_import_circ:
  "preserves x (-p) \<Longrightarrow> -p * x\<^sup>\<circ> = -p * (-p * x)\<^sup>\<circ>"
  using import_test preserves_def by blast

lemma preserves_simulate:
  "preserves x (-p) \<Longrightarrow> -p * x\<^sup>\<circ> = -p * x\<^sup>\<circ> * -p"
  using preserve_test preserves_def by auto

lemma preserves_import_ite:
  assumes "preserves z (-p)"
    shows "z * (x \<lhd> -p \<rhd> y) = z * x \<lhd> -p \<rhd> z * y"
proof -
  have 1: "-p * z * (x \<lhd> -p \<rhd> y) = -p * (z * x \<lhd> -p \<rhd> z * y)"
    by (smt assms ite_context_true mult_assoc preserves_equation_test)
  have "--p * z * (x \<lhd> -p \<rhd> y) = --p * (z * x \<lhd> -p \<rhd> z * y)"
    by (smt (z3) assms ite_context_false mult_assoc preserves_equation_test)
  thus ?thesis
    using 1 by (metis mult_assoc test_case_split_left_equal)
qed

lemma preserves_while_context:
  "preserves x (-p) \<Longrightarrow> -p * (-q \<star> x) = -p * (-p * -q \<star> x)"
  by (smt (verit, del_insts) mult_assoc tests_dual.sup_complement_intro tests_dual.sub_sup_demorgan preserves_import_circ preserves_mult preserves_simulate preserves_test while_def)

lemma while_ite_context_false:
  assumes "preserves y (-p)"
    shows "--p * (-p \<squnion> -q \<star> (x \<lhd> -p \<rhd> y)) = --p * (-q \<star> y)"
proof -
  have "--p * (-p \<squnion> -q \<star> (x \<lhd> -p \<rhd> y)) = --p * (--p * -q * y)\<^sup>\<circ> * -(-p \<squnion> -q)"
    by (smt (z3) assms import_test mult_assoc preserves_equation preserves_equation_test sub_comm while_def tests_dual.sba_dual.sub_sup_demorgan preserves_test split_merge_loops while_context_false)
  thus ?thesis
    by (metis (no_types, lifting) assms preserves_def mult.assoc split_merge_loops while_context_false)
qed

text \<open>Theorem 7.1\<close>

lemma while_ite_norm:
  assumes "assigns z (-p) (-q)"
      and "preserves x1 (-q)"
      and "preserves x2 (-q)"
      and "preserves y1 (-q)"
      and "preserves y2 (-q)"
    shows "z * (x1 * (-r1 \<star> y1) \<lhd> -p \<rhd> x2 * (-r2 \<star> y2)) = z * (x1 \<lhd> -q \<rhd> x2) * ((-q * -r1 \<squnion> --q * -r2) \<star> (y1 \<lhd> -q \<rhd> y2))"
proof -
  have 1: "-(-q * -r1 \<squnion> --q * -r2) = -q * --r1 \<squnion> --q * --r2"
    by (smt (z3) tests_dual.complement_2 tests_dual.sub_sup_closed tests_dual.case_duality tests_dual.sub_sup_demorgan)
  have "-p * -q * x1 * (-q * -r1 * y1 \<squnion> --q * -r2 * y2)\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2) = -p * -q * x1 * -q * (-q * (-q * -r1 * y1 \<squnion> --q * -r2 * y2))\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2)"
    by (smt (verit, del_insts) assms(2,4,5) mult_assoc preserves_sup preserves_equation_test preserves_import_circ preserves_mult preserves_test)
  also have "... = -p * -q * x1 * -q * (-q * -r1 * y1)\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2)"
    using ite_context_true ite_def mult_assoc by auto
  finally have 2: "-p * -q * x1 * (-q * -r1 * y1 \<squnion> --q * -r2 * y2)\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2) = -p * -q * x1 * (-r1 * y1)\<^sup>\<circ> * --r1"
    by (smt (verit, del_insts) assms ite_context_true ite_def mult_assoc preserves_equation_test preserves_import_circ preserves_mult preserves_simulate preserves_test)
  have "--p * --q * x2 * (-q * -r1 * y1 \<squnion> --q * -r2 * y2)\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2) = --p * --q * x2 * --q * (--q * (-q * -r1 * y1 \<squnion> --q * -r2 * y2))\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2)"
    by (smt (verit, del_insts) assms mult_assoc preserves_sup preserves_equation_test preserves_import_circ preserves_mult preserves_test preserves_test_neg)
  also have "... = --p * --q * x2 * --q * (--q * -r2 * y2)\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2)"
    using ite_context_false ite_def mult_assoc by auto
  finally have "--p * --q * x2 * (-q * -r1 * y1 \<squnion> --q * -r2 * y2)\<^sup>\<circ> * (-q * --r1 \<squnion> --q * --r2) = --p * --q * x2 * (-r2 * y2)\<^sup>\<circ> * --r2"
    by (smt (verit, del_insts) assms(3,5) ite_context_false ite_def mult_assoc preserves_equation_test preserves_import_circ preserves_mult preserves_simulate preserves_test preserves_test_neg)
  thus ?thesis
    using 1 2 by (smt (z3) assms(1) assigns_def mult_assoc mult_right_dist_sup while_def ite_context_false ite_context_true tests_dual.sub_commutative)
qed

lemma while_it_norm:
  "assigns z (-p) (-q) \<Longrightarrow> preserves x (-q) \<Longrightarrow> preserves y (-q) \<Longrightarrow> z * (-p \<rhd> x * (-r \<star> y)) = z * (-q \<rhd> x) * (-q * -r \<star> y)"
  by (metis sup_bot_right tests_dual.sup_right_zero it_context_true it_ite tests_dual.complement_bot preserves_one while_import_condition_2 while_ite_norm wnf_lemma_7)

lemma while_else_norm:
  "assigns z (-p) (-q) \<Longrightarrow> preserves x (-q) \<Longrightarrow> preserves y (-q) \<Longrightarrow> z * (1 \<lhd> -p \<rhd> x * (-r \<star> y)) = z * (1 \<lhd> -q \<rhd> x) * (--q * -r \<star> y)"
  by (metis sup_bot_left tests_dual.sup_right_zero ite_context_false tests_dual.complement_bot preserves_one while_import_condition_2 while_ite_norm wnf_lemma_7)

lemma while_while_pre_norm:
  "-p \<star> x * (-q \<star> y) = -p \<rhd> x * (-p \<squnion> -q \<star> (y \<lhd> -q \<rhd> x))"
  by (smt sup_commute circ_sup_1 circ_left_unfold circ_slide it_def ite_def mult_assoc mult_left_one mult_right_dist_sup tests_dual.inf_demorgan while_def wnf_lemma_5)

text \<open>Theorem 7.2\<close>

lemma while_while_norm:
  "assigns z (-p) (-r) \<Longrightarrow> preserves x (-r) \<Longrightarrow> preserves y (-r) \<Longrightarrow> z * (-p \<star> x * (-q \<star> y)) = z * (-r \<rhd> x) * (-r * (-p \<squnion> -q) \<star> (y \<lhd> -q \<rhd> x))"
  by (smt tests_dual.double_negation tests_dual.sub_sup_demorgan tests_dual.inf_demorgan preserves_ite while_it_norm while_while_pre_norm)

lemma while_seq_replace:
  "assigns z (-p) (-q) \<Longrightarrow> z * (-p \<star> x * z) * y = z * (-q \<star> x * z) * y"
  by (smt assigns_def circ_slide mult_assoc tests_dual.wnf_lemma_1 tests_dual.wnf_lemma_2 tests_dual.wnf_lemma_3 tests_dual.wnf_lemma_4 while_def)

lemma while_ite_replace:
  "assigns z (-p) (-q) \<Longrightarrow> z * (x \<lhd> -p \<rhd> y) = z * (x \<lhd> -q \<rhd> y)"
  by (smt assigns_def ite_def mult_assoc mult_left_dist_sup sub_comm tests_dual.wnf_lemma_1 tests_dual.wnf_lemma_3)

lemma while_post_norm_an:
  assumes "preserves y (-p)"
    shows "(-p \<star> x) * y = y \<lhd> --p \<rhd> (-p \<star> x * (--p \<rhd> y))"
proof -
  have "-p * (-p * x * (--p * y \<squnion> -p))\<^sup>\<circ> * --p = -p * x * ((--p * y \<squnion> -p) * -p * x)\<^sup>\<circ> * (--p * y \<squnion> -p) * --p"
    by (metis circ_slide_1 while_def mult_assoc while_context_true)
  also have "... = -p * x * (--p * y * bot \<squnion> -p * x)\<^sup>\<circ> * --p * y"
    by (smt assms sup_bot_right mult_assoc tests_dual.sup_complement tests_dual.sup_idempotent mult_left_zero mult_right_dist_sup preserves_equation_test sub_comm)
  finally have "-p * (-p * x * (--p * y \<squnion> -p))\<^sup>\<circ> * --p = -p * x * (-p * x)\<^sup>\<circ> * --p * y"
    by (metis circ_sup_mult_zero sup_commute mult_assoc)
  thus ?thesis
    by (smt circ_left_unfold tests_dual.double_negation it_def ite_def mult_assoc mult_left_one mult_right_dist_sup while_def)
qed

lemma while_post_norm:
  "preserves y (-p) \<Longrightarrow> (-p \<star> x) * y = -p \<star> x * (1 \<lhd> -p \<rhd> y) \<lhd> -p \<rhd> y"
  using it_neg ite_neg while_post_norm_an by force

lemma wnf_lemma_9:
  assumes "assigns z (-p) (-q)"
      and "preserves x1 (-q)"
      and "preserves y1 (-q)"
      and "preserves x2 (-q)"
      and "preserves y2 (-q)"
      and "preserves x2 (-p)"
      and "preserves y2 (-p)"
    shows "z * (x1 \<lhd> -q \<rhd> x2) * (-q * -p \<squnion> -r \<star> (y1 \<lhd> -q * -p \<rhd> y2)) = z * (x1 \<lhd> -p \<rhd> x2) * (-p \<squnion> -r \<star> (y1 \<lhd> -p \<rhd> y2))"
proof -
  have "z * --p * --q * (x1 \<lhd> -q \<rhd> x2) * (-q * -p \<squnion> -r \<star> (y1 \<lhd> -q * -p \<rhd> y2)) = z * --p * --q * x2 * --q * (--q * (-q * -p \<squnion> -r) \<star> (y1 \<lhd> -q * -p \<rhd> y2))"
    by (smt (verit, del_insts) assms(3-5) tests_dual.double_negation ite_context_false mult_assoc tests_dual.sub_sup_demorgan tests_dual.inf_demorgan preserves_equation_test preserves_ite preserves_while_context)
  also have "... = z * --p * --q * x2 * --q * (--q * -r \<star> --q * y2)"
    by (smt sup_bot_left tests_dual.double_negation ite_conjunction ite_context_false mult_assoc tests_dual.sup_complement mult_left_dist_sup mult_left_zero while_import_condition_2)
  also have "... = z * --p * --q * x2 * (-r \<star> y2)"
    by (metis assms(4,5) mult_assoc preserves_equation_test preserves_test_neg preserves_while_context while_import_condition_2)
  finally have 1: "z * --p * --q * (x1 \<lhd> -q \<rhd> x2) * (-q * -p \<squnion> -r \<star> (y1 \<lhd> -q * -p \<rhd> y2)) = z * --p * --q * (x1 \<lhd> -q \<rhd> x2) * (-p \<squnion> -r \<star> (y1 \<lhd> -p \<rhd> y2))"
    by (smt assms(6,7) ite_context_false mult_assoc preserves_equation_test sub_comm while_ite_context_false)
  have "z * -p * -q * (x1 \<lhd> -q \<rhd> x2) * (-q * -p \<squnion> -r \<star> (y1 \<lhd> -q * -p \<rhd> y2)) = z * -p * -q * (x1 \<lhd> -q \<rhd> x2) * -q * (-q * (-p \<squnion> -r) \<star> -q * (y1 \<lhd> -p \<rhd> y2))"
    by (smt (verit, del_insts) assms(2-5) tests_dual.double_negation ite_context_import mult_assoc tests_dual.sub_sup_demorgan tests_dual.sup_idempotent mult_left_dist_sup tests_dual.inf_demorgan preserves_equation_test preserves_ite preserves_while_context while_import_condition_2)
  hence "z * -p * -q * (x1 \<lhd> -q \<rhd> x2) * (-q * -p \<squnion> -r \<star> (y1 \<lhd> -q * -p \<rhd> y2)) = z * -p * -q * (x1 \<lhd> -q \<rhd> x2) * (-p \<squnion> -r \<star> (y1 \<lhd> -p \<rhd> y2))"
    by (smt assms(2-5) tests_dual.double_negation mult_assoc tests_dual.sub_sup_demorgan tests_dual.sup_idempotent preserves_equation_test preserves_ite preserves_while_context while_import_condition_2)
  thus ?thesis
    using 1 by (smt assms(1) assigns_def mult_assoc mult_left_dist_sup mult_right_dist_sup while_ite_replace)
qed

text \<open>Theorem 7.3\<close>

lemma while_seq_norm:
  assumes "assigns z1 (-r1) (-q)"
      and "preserves x2 (-q)"
      and "preserves y2 (-q)"
      and "preserves z2 (-q)"
      and "z1 * z2 = z2 * z1"
      and "assigns z2 (-q) (-r)"
      and "preserves y1 (-r)"
      and "preserves z1 (-r)"
      and "preserves x2 (-r)"
      and "preserves y2 (-r)"
    shows "x1 * z1 * z2 * (-r1 \<star> y1 * z1) * x2 * (-r2 \<star> y2) = x1 * z1 * z2 * (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> x2) * (-q \<squnion> -r2 \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2))"
proof -
  have 1: "preserves (y1 * z1 * (1 \<lhd> -q \<rhd> x2)) (-r)"
    by (simp add: assms(7-9) ite_def preserves_mult preserves_sup preserves_test)
  hence 2: "preserves (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2) (-r)"
    by (simp add: assms(10) preserves_ite)
  have "x1 * z1 * z2 * (-r1 \<star> y1 * z1) * x2 * (-r2 \<star> y2) = x1 * z1 * z2 * (-q \<star> y1 * z1) * x2 * (-r2 \<star> y2)"
    using assms(1,5) mult_assoc while_seq_replace by auto
  also have "... = x1 * z1 * z2 * (-q \<star> y1 * z1 * (1 \<lhd> -q \<rhd> x2 * (-r2 \<star> y2)) \<lhd> -q \<rhd> x2 * (-r2 \<star> y2))"
    by (smt assms(2,3) mult_assoc preserves_mult preserves_while while_post_norm)
  also have "... = x1 * z1 * (z2 * (-q \<star> y1 * z1 * (1 \<lhd> -q \<rhd> x2) * (--q * -r2 \<star> y2)) \<lhd> -q \<rhd> z2 * x2 * (-r2 \<star> y2))"
    by (smt assms(2-4) assigns_same mult_assoc preserves_import_ite while_else_norm)
  also have "... = x1 * z1 * (z2 * (-r \<rhd> y1 * z1 * (1 \<lhd> -q \<rhd> x2)) * (-r * (-q \<squnion> -r2) \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2)) \<lhd> -q \<rhd> z2 * x2 * (-r2 \<star> y2))"
    by (smt assms(6-10) tests_dual.double_negation tests_dual.sub_sup_demorgan tests_dual.inf_demorgan preserves_ite preserves_mult preserves_one while_while_norm wnf_lemma_8)
  also have "... = x1 * z1 * z2 * ((-r \<rhd> y1 * z1 * (1 \<lhd> -q \<rhd> x2)) * (-r * (-q \<squnion> -r2) \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2)) \<lhd> -r \<rhd> x2 * (-r2 \<star> y2))"
    by (smt assms(4,6) mult_assoc preserves_import_ite while_ite_replace)
  also have "... = x1 * z1 * z2 * (-r * (y1 * z1 * (1 \<lhd> -q \<rhd> x2)) * (-r * (-q \<squnion> -r2) \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2)) \<lhd> -r \<rhd> x2 * (-r2 \<star> y2))"
    by (smt mult_assoc it_context_true ite_import_true)
  also have "... = x1 * z1 * z2 * (-r * (y1 * z1 * (1 \<lhd> -q \<rhd> x2)) * -r * (-r * (-q \<squnion> -r2) \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2)) \<lhd> -r \<rhd> x2 * (-r2 \<star> y2))"
    using 1 by (simp add: preserves_equation_test)
  also have "... = x1 * z1 * z2 * (-r * (y1 * z1 * (1 \<lhd> -q \<rhd> x2)) * -r * (-q \<squnion> -r2 \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2)) \<lhd> -r \<rhd> x2 * (-r2 \<star> y2))"
    using 2 by (smt (z3) tests_dual.sba_dual.sub_sup_closed mult_assoc preserves_while_context)
  also have "... = x1 * z1 * z2 * (y1 * z1 * (1 \<lhd> -q \<rhd> x2) * (-q \<squnion> -r2 \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2)) \<lhd> -q \<rhd> x2 * (-r2 \<star> y2))"
    by (smt assms(6-9) tests_dual.double_negation ite_import_true mult_assoc tests_dual.sup_idempotent preserves_equation_test preserves_ite preserves_one while_ite_replace)
  also have "... = x1 * z1 * z2 * (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -r \<rhd> x2) * ((-r * (-q \<squnion> -r2) \<squnion> --r * -r2) \<star> ((y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2) \<lhd> -r \<rhd> y2))"
    by (smt assms(6-10) tests_dual.double_negation mult_assoc tests_dual.sub_sup_demorgan tests_dual.inf_demorgan preserves_ite preserves_mult preserves_one while_ite_norm)
  also have "... = x1 * z1 * z2 * (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -r \<rhd> x2) * ((-r * (-q \<squnion> -r2) \<squnion> --r * -r2) \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -r * -q \<rhd> y2))"
    using ite_conjunction by simp
  also have "... = x1 * z1 * z2 * (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -r \<rhd> x2) * ((-r * -q \<squnion> -r2) \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -r * -q \<rhd> y2))"
    by (smt (z3) mult_left_dist_sup sup_assoc tests_dual.sba_dual.sup_cases tests_dual.sub_commutative)
  also have "... = x1 * z1 * z2 * (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> x2) * (-q \<squnion> -r2 \<star> (y1 * z1 * (1 \<lhd> -q \<rhd> x2) \<lhd> -q \<rhd> y2))"
    using 1 by (metis assms(2,3,6,9,10) mult_assoc wnf_lemma_9)
  finally show ?thesis
    .
qed

end

end

