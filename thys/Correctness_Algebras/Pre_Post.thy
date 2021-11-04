(* Title:      Pre-Post Specifications
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Pre-Post Specifications\<close>

theory Pre_Post

imports Preconditions

begin

class pre_post =
  fixes pre_post :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<stileturn>" 55)

class pre_post_spec_greatest = bounded_idempotent_left_semiring + precondition + pre_post +
  assumes pre_post_galois: "-p \<le> x\<guillemotleft>-q \<longleftrightarrow> x \<le> -p\<stileturn>-q"
begin

text \<open>Theorem 42.1\<close>

lemma post_pre_left_antitone:
  "x \<le> y \<Longrightarrow> y\<guillemotleft>-q \<le> x\<guillemotleft>-q"
  by (smt order_refl order_trans pre_closed pre_post_galois)

lemma pre_left_sub_dist:
  "x\<squnion>y\<guillemotleft>-q \<le> x\<guillemotleft>-q"
  by (simp add: post_pre_left_antitone)

text \<open>Theorem 42.2\<close>

lemma pre_post_left_antitone:
  "-p \<le> -q \<Longrightarrow> -q\<stileturn>-r \<le> -p\<stileturn>-r"
  using order_lesseq_imp pre_post_galois by blast

lemma pre_post_left_sub_dist:
  "-p\<squnion>-q\<stileturn>-r \<le> -p\<stileturn>-r"
  by (metis sup.cobounded1 tests_dual.sba_dual.sub_sup_closed pre_post_left_antitone)

lemma pre_post_left_sup_dist:
  "-p\<stileturn>-r \<le> -p*-q\<stileturn>-r"
  by (metis tests_dual.sba_dual.sub_inf_def pre_post_left_sub_dist tests_dual.inf_absorb)

text \<open>Theorem 42.5\<close>

lemma pre_pre_post:
  "x \<le> (x\<guillemotleft>-p)\<stileturn>-p"
  by (metis order_refl pre_closed pre_post_galois)

text \<open>Theorem 42.6\<close>

lemma pre_post_pre:
  "-p \<le> (-p\<stileturn>-q)\<guillemotleft>-q"
  by (simp add: pre_post_galois)

text \<open>Theorem 42.8\<close>

lemma pre_post_zero_top:
  "bot\<stileturn>-q = top"
  by (metis order.eq_iff pre_post_galois sup.cobounded2 sup_monoid.add_0_right top_greatest tests_dual.top_double_complement)

text \<open>Theorem 42.7\<close>

lemma pre_post_pre_one:
  "(1\<stileturn>-q)\<guillemotleft>-q = 1"
  by (metis order.eq_iff pre_below_one tests_dual.sba_dual.top_double_complement pre_post_pre)

text \<open>Theorem 42.3\<close>

lemma pre_post_right_isotone:
  "-p \<le> -q \<Longrightarrow> -r\<stileturn>-p \<le> -r\<stileturn>-q"
  using order_lesseq_imp pre_iso pre_post_galois by blast

lemma pre_post_right_sub_dist:
  "-r\<stileturn>-p \<le> -r\<stileturn>-p\<squnion>-q"
  by (metis sup.cobounded1 tests_dual.sba_dual.sub_sup_closed pre_post_right_isotone)

lemma pre_post_right_sup_dist:
  "-r\<stileturn>-p*-q \<le> -r\<stileturn>-p"
  by (metis tests_dual.sub_sup_closed pre_post_right_isotone tests_dual.upper_bound_left)

text \<open>Theorem 42.7\<close>

lemma pre_post_reflexive:
  "1 \<le> -p\<stileturn>-p"
  using pre_one_increasing pre_post_galois by auto

text \<open>Theorem 42.9\<close>

lemma pre_post_compose:
  "-q \<le> -r \<Longrightarrow> (-p\<stileturn>-q)*(-r\<stileturn>-s) \<le> -p\<stileturn>-s"
  using order_lesseq_imp pre_compose pre_post_galois by blast

text \<open>Theorem 42.10\<close>

lemma pre_post_compose_1:
  "(-p\<stileturn>-q)*(-q\<stileturn>-r) \<le> -p\<stileturn>-r"
  by (simp add: pre_post_compose)

text \<open>Theorem 42.11\<close>

lemma pre_post_compose_2:
  "(-p\<stileturn>-p)*(-p\<stileturn>-q) = -p\<stileturn>-q"
  by (meson case_split_left order.eq_iff le_supI1 pre_post_compose_1 pre_post_reflexive)

text \<open>Theorem 42.12\<close>

lemma pre_post_compose_3:
  "(-p\<stileturn>-q)*(-q\<stileturn>-q) = -p\<stileturn>-q"
  by (meson order.eq_iff order.trans mult_right_isotone mult_sub_right_one pre_post_compose_1 pre_post_reflexive)

text \<open>Theorem 42.13\<close>

lemma pre_post_compose_4:
  "(-p\<stileturn>-p)*(-p\<stileturn>-p) = -p\<stileturn>-p"
  by (simp add: pre_post_compose_3)

text \<open>Theorem 42.14\<close>

lemma pre_post_one_one:
  "x\<guillemotleft>1 = 1 \<longleftrightarrow> x \<le> 1\<stileturn>1"
  by (metis order.eq_iff one_def pre_below_one pre_post_galois)

text \<open>Theorem 42.4\<close>

lemma post_pre_left_dist_sup:
  "x\<squnion>y\<guillemotleft>-q = (x\<guillemotleft>-q)*(y\<guillemotleft>-q)"
  apply (rule order.antisym)
  apply (metis mult_isotone pre_closed sup_commute tests_dual.sup_idempotent pre_left_sub_dist)
  by (smt (z3) order.refl pre_closed pre_post_galois sup.boundedI tests_dual.sba_dual.greatest_lower_bound tests_dual.sub_sup_closed)

(*
lemma pre_post_right_dist_sup: "-p\<stileturn>-q\<squnion>-r = (-p\<stileturn>-q) \<squnion> (-p\<stileturn>-r)" nitpick [expect=genuine,card=4] oops
*)

end

class pre_post_spec_greatest_2 = pre_post_spec_greatest + precondition_test_test
begin

subclass precondition_test_box
  apply unfold_locales
  by (smt (verit) sup_commute mult_1_right tests_dual.double_negation order.eq_iff mult_left_one mult_right_dist_sup one_def tests_dual.inf_complement tests_dual.inf_complement_intro pre_below_one pre_import pre_post_galois pre_test_test tests_dual.top_def bot_least)

lemma pre_post_seq_sub_associative:
  "(-p\<stileturn>-q)*-r \<le> -p\<stileturn>-q*-r"
  by (smt (z3) pre_compose pre_post_galois pre_post_pre sub_comm test_below_pre_test_mult tests_dual.sub_sup_closed)

lemma pre_post_right_import_mult:
  "(-p\<stileturn>-q)*-r = (-p\<stileturn>-q*-r)*-r"
  by (metis order.antisym mult_assoc tests_dual.sup_idempotent mult_left_isotone pre_post_right_sup_dist pre_post_seq_sub_associative)

lemma seq_pre_post_sub_associative:
  "-r*(-p\<stileturn>-q) \<le> --r\<squnion>-p\<stileturn>-q"
  by (smt (z3) pre_compose pre_post_galois pre_post_pre pre_test tests_dual.sba_dual.reflexive tests_dual.sba_dual.sub_sup_closed)

lemma pre_post_left_import_sup:
  "-r*(-p\<stileturn>-q) = -r*(--r\<squnion>-p\<stileturn>-q)"
  by (metis sup_commute order.antisym mult_assoc tests_dual.sup_idempotent mult_right_isotone pre_post_left_sub_dist seq_pre_post_sub_associative)

lemma pre_post_import_same:
  "-p*(-p\<stileturn>-q) = -p*(1\<stileturn>-q)"
  using pre_test pre_test_test_same pre_post_left_import_sup by auto

lemma pre_post_import_complement:
  "--p*(-p\<stileturn>-q) = --p*top"
  by (metis tests_dual.sup_idempotent tests_dual.inf_cases tests_dual.inf_closed pre_post_left_import_sup pre_post_zero_top tests_dual.top_def tests_dual.top_double_complement)

lemma pre_post_export:
  "-p\<stileturn>-q = (1\<stileturn>-q) \<squnion> --p*top"
proof (rule order.antisym)
  have 1: "-p*(-p\<stileturn>-q) \<le> (1\<stileturn>-q) \<squnion> --p*top"
    by (metis le_supI1 pre_test pre_test_test_same seq_pre_post_sub_associative)
  have "--p*(-p\<stileturn>-q) \<le> (1\<stileturn>-q) \<squnion> --p*top"
    by (simp add: pre_post_import_complement)
  thus "-p\<stileturn>-q \<le> (1\<stileturn>-q) \<squnion> --p*top"
    using 1 by (smt case_split_left eq_refl tests_dual.inf_complement)
next
  show "(1\<stileturn>-q) \<squnion> --p*top \<le> -p\<stileturn>-q"
    by (metis le_sup_iff tests_dual.double_negation tests_dual.sub_bot_least pre_neg_mult pre_post_galois pre_post_pre_one)
qed

lemma pre_post_left_dist_mult:
  "-p*-q\<stileturn>-r = (-p\<stileturn>-r) \<squnion> (-q\<stileturn>-r)"
proof -
  have "\<forall>p q . -p*(-p*-q\<stileturn>-r) = -p*(-q\<stileturn>-r)"
    using sup_monoid.add_commute tests_dual.sba_dual.sub_inf_def pre_post_left_import_sup tests_dual.inf_complement_intro by auto
  hence 1: "(-p\<squnion>-q)*(-p*-q\<stileturn>-r) \<le> (-p\<stileturn>-r) \<squnion> (-q\<stileturn>-r)"
    by (metis sup_commute le_sup_iff sup_ge2 mult_left_one mult_right_dist_sup tests_dual.inf_left_unit sub_comm)
  have "-(-p\<squnion>-q)*(-p*-q\<stileturn>-r) = -(-p\<squnion>-q)*top"
    by (smt (z3) sup.left_commute sup_commute tests_dual.sba_dual.sub_sup_closed tests_dual.sub_sup_closed pre_post_import_complement pre_post_left_import_sup tests_dual.inf_absorb)
  hence "-(-p\<squnion>-q)*(-p*-q\<stileturn>-r) \<le> (-p\<stileturn>-r) \<squnion> (-q\<stileturn>-r)"
    by (smt (z3) order.trans le_supI1 pre_post_left_sub_dist tests_dual.sba_dual.sub_sup_closed tests_dual.sub_sup_closed seq_pre_post_sub_associative)
  thus ?thesis
    using 1 by (smt (z3) le_sup_iff order.antisym case_split_left order_refl tests_dual.inf_closed tests_dual.inf_complement pre_post_left_sup_dist sub_comm)
qed

lemma pre_post_left_import_mult:
  "-r*(-p\<stileturn>-q) = -r*(-r*-p\<stileturn>-q)"
  by (metis sup_commute tests_dual.inf_complement_intro pre_post_left_import_sup sub_mult_closed)

lemma pre_post_right_import_sup:
  "(-p\<stileturn>-q)*-r = (-p\<stileturn>-q\<squnion>--r)*-r"
  by (smt (z3) sup_monoid.add_commute tests_dual.sba_dual.inf_cases_2 tests_dual.sba_dual.inf_complement_intro tests_dual.sub_complement tests_dual.sub_inf_def pre_post_right_import_mult)

lemma pre_post_shunting:
  "x \<le> -p*-q\<stileturn>-r \<longleftrightarrow> -p*x \<le> -q\<stileturn>-r"
proof -
  have "--p*x \<le> -p*-q\<stileturn>-r"
    by (metis tests_dual.double_negation order_trans pre_neg_mult pre_post_galois pre_post_left_sup_dist)
  hence 1: "-p*x \<le> -q\<stileturn>-r \<longrightarrow> x \<le> -p*-q\<stileturn>-r"
    by (smt case_split_left eq_refl order_trans tests_dual.inf_complement pre_post_left_sup_dist sub_comm)
  have "-p*(-p*-q\<stileturn>-r) \<le> -q\<stileturn>-r"
    by (metis mult_left_isotone mult_left_one tests_dual.sub_bot_least pre_post_left_import_mult)
  thus ?thesis
    using 1 mult_right_isotone order_lesseq_imp by blast
qed

(*
lemma pre_post_right_dist_sup: "-p\<stileturn>-q\<squnion>-r = (-p\<stileturn>-q) \<squnion> (-p\<stileturn>-r)" oops
*)

end

class left_zero_pre_post_spec_greatest_2 = pre_post_spec_greatest_2 + bounded_idempotent_left_zero_semiring
begin

lemma pre_post_right_dist_sup:
  "-p\<stileturn>-q\<squnion>-r = (-p\<stileturn>-q) \<squnion> (-p\<stileturn>-r)"
proof -
  have 1: "(-p\<stileturn>-q\<squnion>-r)*-q \<le> (-p\<stileturn>-q) \<squnion> (-p\<stileturn>-r)"
    by (metis le_supI1 pre_post_seq_sub_associative tests_dual.sba_dual.inf_absorb tests_dual.sba_dual.sub_sup_closed)
  have "(-p\<stileturn>-q\<squnion>-r)*--q = (-p\<stileturn>-r)*--q"
    by (simp add: pre_post_right_import_sup sup_commute)
  hence "(-p\<stileturn>-q\<squnion>-r)*--q \<le> (-p\<stileturn>-q) \<squnion> (-p\<stileturn>-r)"
    by (metis sup_ge2 mult_left_sub_dist_sup_right mult_1_right order_trans tests_dual.inf_left_unit)
  thus ?thesis
    using 1 by (metis le_sup_iff order.antisym case_split_right tests_dual.sub_bot_least tests_dual.inf_commutative tests_dual.inf_complement pre_post_right_sub_dist)
qed

end

class havoc =
  fixes H :: "'a"

class idempotent_left_semiring_H = bounded_idempotent_left_semiring + havoc +
  assumes H_zero : "H * bot = bot"
  assumes H_split: "x \<le> x * bot \<squnion> H"
begin

lemma H_galois:
  "x * bot \<le> y \<longleftrightarrow> x \<le> y \<squnion> H"
  apply (rule iffI)
  using H_split order_lesseq_imp sup_mono apply blast
  by (smt (verit, ccfv_threshold) H_zero mult_right_dist_sup sup.cobounded2 sup.orderE sup_assoc sup_bot_left sup_commute zero_right_mult_decreasing)

lemma H_greatest_finite:
  "x * bot = bot \<longleftrightarrow> x \<le> H"
  by (metis H_galois le_iff_sup sup_bot_left sup_monoid.add_0_right)

lemma H_reflexive:
  "1 \<le> H"
  using H_greatest_finite mult_left_one by blast

lemma H_transitive:
  "H = H * H"
  by (metis H_greatest_finite H_reflexive H_zero preorder_idempotent mult_assoc)

lemma T_split_H:
  "top * bot \<squnion> H = top"
  by (simp add: H_split order.antisym)

(*
lemma "H * (x \<squnion> y) = H * x \<squnion> H * y" nitpick [expect=genuine,card=6] oops
*)

end

class pre_post_spec_least = bounded_idempotent_left_semiring + precondition_test_test + precondition_promote + pre_post +
  assumes test_mult_right_distr_sup: "-p * (x \<squnion> y) = -p * x \<squnion> -p * y"
  assumes pre_post_galois: "-p \<le> x\<guillemotleft>-q \<longleftrightarrow> -p\<stileturn>-q \<le> x"
begin

lemma shunting_top:
  "-p * x \<le> y \<longleftrightarrow> x \<le> y \<squnion> --p * top"
proof
  assume "-p * x \<le> y"
  thus "x \<le> y \<squnion> --p * top"
    by (smt (verit, ccfv_SIG) case_split_left eq_refl le_supI1 le_supI2 mult_right_isotone tests_dual.sba_dual.top_def top_greatest)
next
  assume "x \<le> y \<squnion> --p * top"
  hence "-p * x \<le> -p * y"
    by (metis sup_bot_right mult_assoc tests_dual.sup_complement mult_left_zero mult_right_isotone test_mult_right_distr_sup)
  thus "-p * x \<le> y"
    by (metis mult_left_isotone mult_left_one tests_dual.sub_bot_least order_trans)
qed

lemma post_pre_left_isotone:
  "x \<le> y \<Longrightarrow> x\<guillemotleft>-q \<le> y\<guillemotleft>-q"
  by (smt order_refl order_trans pre_closed pre_post_galois)

lemma pre_left_sub_dist:
  "x\<guillemotleft>-q \<le> x\<squnion>y\<guillemotleft>-q"
  by (simp add: post_pre_left_isotone)

lemma pre_post_left_isotone:
  "-p \<le> -q \<Longrightarrow> -p\<stileturn>-r \<le> -q\<stileturn>-r"
  using order_lesseq_imp pre_post_galois by blast

lemma pre_post_left_sub_dist:
  "-p\<stileturn>-r \<le> -p\<squnion>-q\<stileturn>-r"
  by (metis sup_ge1 tests_dual.inf_closed pre_post_left_isotone)

lemma pre_post_left_sup_dist:
  "-p*-q\<stileturn>-r \<le> -p\<stileturn>-r"
  by (metis tests_dual.upper_bound_left pre_post_left_isotone sub_mult_closed)

lemma pre_pre_post:
  "(x\<guillemotleft>-p)\<stileturn>-p \<le> x"
  by (metis order_refl pre_closed pre_post_galois)

lemma pre_post_pre:
  "-p \<le> (-p\<stileturn>-q)\<guillemotleft>-q"
  by (simp add: pre_post_galois)

lemma pre_post_zero_top:
  "bot\<stileturn>-q = bot"
  using bot_least order.eq_iff pre_post_galois tests_dual.sba_dual.sub_bot_def by blast

lemma pre_post_pre_one:
  "(1\<stileturn>-q)\<guillemotleft>-q = 1"
  by (metis order.eq_iff pre_below_one pre_post_pre tests_dual.sba_dual.top_double_complement)

lemma pre_post_right_antitone:
  "-p \<le> -q \<Longrightarrow> -r\<stileturn>-q \<le> -r\<stileturn>-p"
  using order_lesseq_imp pre_iso pre_post_galois by blast

lemma pre_post_right_sub_dist:
  "-r\<stileturn>-p\<squnion>-q \<le> -r\<stileturn>-p"
  by (metis sup_ge1 tests_dual.inf_closed pre_post_right_antitone)

lemma pre_post_right_sup_dist:
  "-r\<stileturn>-p \<le> -r\<stileturn>-p*-q"
  by (metis tests_dual.upper_bound_left pre_post_right_antitone sub_mult_closed)

lemma pre_top:
  "top\<guillemotleft>-q = 1"
  using order.eq_iff pre_below_one pre_post_galois tests_dual.sba_dual.one_def top_greatest by blast

lemma pre_mult_top_increasing:
  "-p \<le> -p*top\<guillemotleft>-q"
  using pre_import_equiv pre_top tests_dual.sub_bot_least by auto

lemma pre_post_below_mult_top:
  "-p\<stileturn>-q \<le> -p*top"
  using pre_import_equiv pre_post_galois by auto

lemma pre_post_import_complement:
  "--p*(-p\<stileturn>-q) = bot"
proof -
  have "--p*(-p\<stileturn>-q) \<le> --p*(-p*top)"
    by (simp add: mult_right_isotone pre_post_below_mult_top)
  thus ?thesis
    by (metis mult_assoc mult_left_zero sub_comm tests_dual.top_def order.antisym bot_least)
qed

lemma pre_post_import_same:
  "-p*(-p\<stileturn>-q) = -p\<stileturn>-q"
proof -
  have "-p\<stileturn>-q = -p*(-p\<stileturn>-q) \<squnion> --p*(-p\<stileturn>-q)"
    by (metis mult_left_one mult_right_dist_sup tests_dual.inf_complement)
  thus ?thesis
    using pre_post_import_complement by auto
qed

lemma pre_post_export:
  "-p\<stileturn>-q = -p*(1\<stileturn>-q)"
proof (rule order.antisym)
  show "-p\<stileturn>-q \<le> -p*(1\<stileturn>-q)"
    by (metis tests_dual.sub_bot_least pre_import_equiv pre_post_galois pre_post_pre_one)
next
  have 1: "-p \<le> ((-p\<stileturn>-q) \<squnion> --p*top)\<guillemotleft>-q"
    by (simp add: pre_post_galois)
  have "--p \<le> ((-p\<stileturn>-q) \<squnion> --p*top)\<guillemotleft>-q"
    by (simp add: le_supI2 pre_post_galois pre_post_below_mult_top)
  hence "-p \<squnion> --p \<le> ((-p\<stileturn>-q) \<squnion> --p*top)\<guillemotleft>-q"
    using 1 le_supI by blast
  hence "1 \<le> ((-p\<stileturn>-q) \<squnion> --p*top)\<guillemotleft>-q"
    by simp
  hence "1\<stileturn>-q \<le> (-p\<stileturn>-q) \<squnion> --p*top"
    using pre_post_galois tests_dual.sba_dual.one_def by blast
  thus "-p*(1\<stileturn>-q) \<le> -p\<stileturn>-q"
    by (simp add: shunting_top)
qed

lemma pre_post_seq_associative:
  "-r*(-p\<stileturn>-q) = -r*-p\<stileturn>-q"
  by (metis pre_post_export tests_dual.sub_sup_closed mult_assoc)

lemma pre_post_left_import_mult:
  "-r*(-p\<stileturn>-q) = -r*(-r*-p\<stileturn>-q)"
  by (metis mult_assoc tests_dual.sup_idempotent pre_post_seq_associative)

lemma seq_pre_post_sub_associative:
  "-r*(-p\<stileturn>-q) \<le> --r\<squnion>-p\<stileturn>-q"
  by (metis le_supI1 pre_post_left_sub_dist sup_commute shunting_top)

lemma pre_post_left_import_sup:
  "-r*(-p\<stileturn>-q) = -r*(--r\<squnion>-p\<stileturn>-q)"
  by (metis tests_dual.sba_dual.sub_sup_closed pre_post_seq_associative tests_dual.sup_complement_intro)

lemma pre_post_left_dist_sup:
  "-p\<squnion>-q\<stileturn>-r = (-p\<stileturn>-r) \<squnion> (-q\<stileturn>-r)"
  by (metis mult_right_dist_sup tests_dual.inf_closed pre_post_export)

lemma pre_post_reflexive:
  "-p\<stileturn>-p \<le> 1"
  using pre_one_increasing pre_post_galois by auto

lemma pre_post_compose:
  "-q \<le> -r \<Longrightarrow> -p\<stileturn>-s \<le> (-p\<stileturn>-q)*(-r\<stileturn>-s)"
  by (meson pre_compose pre_post_galois pre_post_pre pre_post_right_antitone)

lemma pre_post_compose_1:
  "-p\<stileturn>-r \<le> (-p\<stileturn>-q)*(-q\<stileturn>-r)"
  by (simp add: pre_post_compose)

lemma pre_post_compose_2:
  "(-p\<stileturn>-p)*(-p\<stileturn>-q) = -p\<stileturn>-q"
  using order.eq_iff mult_left_isotone pre_post_compose_1 pre_post_reflexive by fastforce

lemma pre_post_compose_3:
  "(-p\<stileturn>-q)*(-q\<stileturn>-q) = -p\<stileturn>-q"
  by (metis order.antisym mult_right_isotone mult_1_right pre_post_compose_1 pre_post_reflexive)

lemma pre_post_compose_4:
  "(-p\<stileturn>-p)*(-p\<stileturn>-p) = -p\<stileturn>-p"
  by (simp add: pre_post_compose_3)

lemma pre_post_one_one:
  "x\<guillemotleft>1 = 1 \<longleftrightarrow> 1\<stileturn>1 \<le> x"
  using order.eq_iff pre_below_one pre_post_galois tests_dual.sub_bot_def by force

lemma pre_one_right:
  "-p\<guillemotleft>1 = -p"
  by (metis order.antisym mult_1_right one_def tests_dual.inf_complement pre_left_sub_dist pre_mult_top_increasing pre_one pre_seq pre_test_promote pre_top)

lemma pre_pre_one:
  "x\<guillemotleft>-q = x*-q\<guillemotleft>1"
  by (metis one_def pre_one_right pre_seq)

subclass precondition_test_diamond
  apply unfold_locales
  using tests_dual.sba_dual.sub_inf_def pre_one_right pre_pre_one by auto

(*
lemma pre_post_shunting: "x \<le> -p*-q\<stileturn>-r \<longleftrightarrow> -p*x \<le> -q\<stileturn>-r" nitpick [expect=genuine,card=3] oops
lemma "(-p\<stileturn>-q)*-r = (-p\<stileturn>-q\<squnion>-r)*-r" nitpick [expect=genuine,card=3] oops
lemma "(-p\<stileturn>-q)*-r = (-p\<stileturn>-q\<squnion>--r)*-r" nitpick [expect=genuine,card=3] oops
lemma "(-p\<stileturn>-q)*-r = (-p\<stileturn>-q*-r)*-r" nitpick [expect=genuine,card=3] oops
lemma "(-p\<stileturn>-q)*-r = (-p\<stileturn>-q*--r)*-r" nitpick [expect=genuine,card=3] oops
lemma "-p\<stileturn>-q\<squnion>-r = (-p\<stileturn>-q) \<squnion> (-p\<stileturn>-r)" nitpick [expect=genuine,card=3] oops
lemma "-p\<stileturn>-q\<squnion>-r = (-p\<stileturn>-q) * (-p\<stileturn>-r)" nitpick [expect=genuine,card=3] oops
lemma pre_post_right_dist_mult: "-p\<stileturn>-q*-r = (-p\<stileturn>-q) * (-p\<stileturn>-r)" oops
lemma pre_post_right_dist_mult: "-p\<stileturn>-q*-r = (-p\<stileturn>-q) \<squnion> (-p\<stileturn>-r)" oops
lemma post_pre_left_dist_sup: "x\<squnion>y\<guillemotleft>-q = (x\<guillemotleft>-q) \<squnion> (y\<guillemotleft>-q)" oops
*)

end

class havoc_dual =
  fixes Hd :: "'a"

class idempotent_left_semiring_Hd = bounded_idempotent_left_semiring + havoc_dual +
  assumes Hd_total: "Hd * top = top"
  assumes Hd_least: "x * top = top \<longrightarrow> Hd \<le> x"
begin

lemma Hd_least_total:
  "x * top = top \<longleftrightarrow> Hd \<le> x"
  by (metis Hd_least Hd_total order.antisym mult_left_isotone top_greatest)

lemma Hd_reflexive:
  "Hd \<le> 1"
  by (simp add: Hd_least)

lemma Hd_transitive:
  "Hd = Hd * Hd"
  by (simp add: Hd_least Hd_total order.antisym coreflexive_transitive total_mult_closed)

end

class pre_post_spec_least_Hd = idempotent_left_semiring_Hd + pre_post_spec_least +
  assumes pre_one_mult_top: "(x\<guillemotleft>1)*top = x*top"
begin

lemma Hd_pre_one:
  "Hd\<guillemotleft>1 = 1"
  by (metis Hd_total pre_seq pre_top)

lemma pre_post_below_Hd:
  "1\<stileturn>1 \<le> Hd"
  using Hd_pre_one pre_post_one_one by auto

lemma Hd_pre_post:
  "Hd = 1\<stileturn>1"
  by (metis Hd_least Hd_pre_one Hd_total order.eq_iff pre_one_mult_top pre_post_one_one)

lemma top_left_zero:
  "top*x = top"
  by (metis mult_assoc mult_left_one mult_left_zero pre_closed pre_one_mult_top pre_seq pre_top)

lemma test_dual_test:
  "(-p\<squnion>--p*top)*-p = -p\<squnion>--p*top"
  by (simp add: top_left_zero mult_right_dist_sup mult_assoc)

lemma pre_zero_mult_top:
  "(x\<guillemotleft>bot)*top = x*bot"
  by (metis mult_assoc mult_left_zero one_def pre_one_mult_top pre_seq pre_bot)

lemma pre_one_mult_Hd:
  "(x\<guillemotleft>1)*Hd \<le> x"
  by (metis Hd_pre_post one_def pre_closed pre_post_export pre_pre_post)

lemma Hd_mult_pre_one:
  "Hd*(x\<guillemotleft>1) \<le> x"
proof -
  have 1: "-(x\<guillemotleft>1)*Hd*(x\<guillemotleft>1) \<le> x"
    by (metis Hd_pre_post le_iff_sup mult_left_isotone pre_closed pre_one_right pre_post_export pre_pre_post sup_commute sup_monoid.add_0_right tests_dual.sba_dual.one_def tests_dual.top_def)
  have "(x\<guillemotleft>1)*Hd*(x\<guillemotleft>1) \<le> x"
    by (metis mult_isotone mult_1_right one_def pre_below_one pre_one_mult_Hd)
  thus ?thesis
    using 1 by (metis case_split_left pre_closed reflexive_one_closed tests_dual.sba_dual.one_def tests_dual.sba_dual.top_def mult_assoc)
qed

lemma pre_post_one_def_1:
  assumes "1 \<le> x\<guillemotleft>-q"
    shows "Hd*(-q\<squnion>--q*top) \<le> x"
proof -
  have "Hd*(-q\<squnion>--q*top) \<le> x*-q*(-q\<squnion>--q*top)"
    by (metis assms Hd_pre_post order.antisym pre_below_one pre_post_one_one pre_pre_one mult_left_isotone)
  thus ?thesis
    by (metis mult_assoc tests_dual.sup_complement mult_left_sub_dist_sup_left mult_left_zero mult_1_right tests_dual.inf_complement test_mult_right_distr_sup order_trans)
qed

lemma pre_post_one_def:
  "1\<stileturn>-q = Hd*(-q\<squnion>--q*top)"
proof (rule order.antisym)
  have "1 \<le> (1\<stileturn>1)*(-q\<squnion>--q)\<guillemotleft>1"
    by (metis pre_post_pre one_def mult_1_right tests_dual.inf_complement)
  also have "... \<le> (1\<stileturn>1)*(-q\<squnion>--q*top)\<guillemotleft>-q"
    by (metis sup_right_isotone mult_right_isotone mult_1_right one_def post_pre_left_isotone pre_seq pre_test_promote test_dual_test top_right_mult_increasing)
  finally show "1\<stileturn>-q \<le> Hd*(-q\<squnion>--q*top)"
    using Hd_pre_post pre_post_galois tests_dual.sub_bot_def by blast
next
  show "Hd*(-q\<squnion>--q*top) \<le> 1\<stileturn>-q"
    by (simp add: pre_post_pre_one pre_post_one_def_1)
qed

lemma pre_post_def:
  "-p\<stileturn>-q = -p*Hd*(-q\<squnion>--q*top)"
  by (simp add: pre_post_export mult_assoc pre_post_one_def)

end

end

