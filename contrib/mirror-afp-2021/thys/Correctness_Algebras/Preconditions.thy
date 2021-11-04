(* Title:      Preconditions
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Preconditions\<close>

theory Preconditions

imports Tests

begin

class pre =
  fixes pre :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<guillemotleft>" 55)

class precondition = tests + pre +
  assumes pre_closed: "x\<guillemotleft>-q = --(x\<guillemotleft>-q)"
  assumes pre_seq: "x*y\<guillemotleft>-q = x\<guillemotleft>y\<guillemotleft>-q"
  assumes pre_lower_bound_right: "x\<guillemotleft>-p*-q \<le> x\<guillemotleft>-q"
  assumes pre_one_increasing: "-q \<le> 1\<guillemotleft>-q"
begin

text \<open>Theorem 39.2\<close>

lemma pre_sub_distr:
  "x\<guillemotleft>-p*-q \<le> (x\<guillemotleft>-p)*(x\<guillemotleft>-q)"
  by (smt (z3) pre_closed pre_lower_bound_right tests_dual.sub_commutative tests_dual.sub_sup_closed tests_dual.least_upper_bound)

text \<open>Theorem 39.5\<close>

lemma pre_below_one:
  "x\<guillemotleft>-p \<le> 1"
  by (metis pre_closed tests_dual.sub_bot_least)

lemma pre_lower_bound_left:
  "x\<guillemotleft>-p*-q \<le> x\<guillemotleft>-p"
  using pre_lower_bound_right tests_dual.sub_commutative by fastforce

text \<open>Theorem 39.1\<close>

lemma pre_iso:
  "-p \<le> -q \<Longrightarrow> x\<guillemotleft>-p \<le> x\<guillemotleft>-q"
  by (metis leq_def pre_lower_bound_right)

text \<open>Theorem 39.4 and Theorem 40.9\<close>

lemma pre_below_pre_one:
  "x\<guillemotleft>-p \<le> x\<guillemotleft>1"
  using tests_dual.sba_dual.one_def pre_iso tests_dual.sub_bot_least by blast

text \<open>Theorem 39.3\<close>

lemma pre_seq_below_pre_one:
  "x*y\<guillemotleft>1 \<le> x\<guillemotleft>1"
  by (metis one_def pre_below_pre_one pre_closed pre_seq)

text \<open>Theorem 39.6\<close>

lemma pre_compose:
  "-p \<le> x\<guillemotleft>-q \<Longrightarrow> -q \<le> y\<guillemotleft>-r \<Longrightarrow> -p \<le> x*y\<guillemotleft>-r"
  by (metis pre_closed pre_iso tests_dual.transitive pre_seq)

(*
lemma pre_test_test: "-p*(-p\<guillemotleft>-q) = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test_promote: "-p\<guillemotleft>-q = -p\<guillemotleft>-p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = --p\<squnion>-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_distr_mult: "x\<guillemotleft>-p*-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=4] oops
lemma pre_distr_plus: "x\<guillemotleft>-p\<squnion>-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=2] oops
*)

end

class precondition_test_test = precondition +
  assumes pre_test_test: "-p*(-p\<guillemotleft>-q) = -p*-q"
begin

lemma pre_one:
  "1\<guillemotleft>-p = -p"
  by (metis pre_closed pre_test_test tests_dual.sba_dual.one_def tests_dual.sup_left_unit)

lemma pre_import:
  "-p*(x\<guillemotleft>-q) = -p*(-p*x\<guillemotleft>-q)"
  by (metis pre_closed pre_seq pre_test_test)

lemma pre_import_composition:
  "-p*(-p*x*y\<guillemotleft>-q) = -p*(x\<guillemotleft>y\<guillemotleft>-q)"
  by (metis pre_closed pre_seq pre_import)

lemma pre_import_equiv:
  "-p \<le> x\<guillemotleft>-q \<longleftrightarrow> -p \<le> -p*x\<guillemotleft>-q"
  by (metis leq_def pre_closed pre_import)

lemma pre_import_equiv_mult:
  "-p*-q \<le> x\<guillemotleft>-s \<longleftrightarrow> -p*-q \<le> -q*x\<guillemotleft>-s"
  by (smt leq_def pre_closed sub_assoc sub_mult_closed pre_import)

(*
lemma pre_test_promote: "-p\<guillemotleft>-q = -p\<guillemotleft>-p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = --p\<squnion>-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_distr_mult: "x\<guillemotleft>-p*-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=4] oops
lemma pre_distr_plus: "x\<guillemotleft>-p\<squnion>-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=2] oops
*)

end

class precondition_promote = precondition +
  assumes pre_test_promote: "-p\<guillemotleft>-q = -p\<guillemotleft>-p*-q"
begin

lemma pre_mult_test_promote:
  "x*-p\<guillemotleft>-q = x*-p\<guillemotleft>-p*-q"
  by (metis pre_seq pre_test_promote sub_mult_closed)

(*
lemma pre_test_test: "-p*(-p\<guillemotleft>-q) = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = --p\<squnion>-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_distr_mult: "x\<guillemotleft>-p*-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=4] oops
lemma pre_distr_plus: "x\<guillemotleft>-p\<squnion>-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=2] oops
*)

end

class precondition_test_box = precondition +
  assumes pre_test: "-p\<guillemotleft>-q = --p\<squnion>-q"
begin

lemma pre_test_neg:
  "--p*(-p\<guillemotleft>-q) = --p"
  by (simp add: pre_test)

lemma pre_bot:
  "bot\<guillemotleft>-q = 1"
  by (metis pre_test tests_dual.sba_dual.one_def tests_dual.sba_dual.sup_left_zero tests_dual.top_double_complement)

lemma pre_export:
  "-p*x\<guillemotleft>-q = --p\<squnion>(x\<guillemotleft>-q)"
  by (metis pre_closed pre_seq pre_test)

lemma pre_neg_mult:
  "--p \<le> -p*x\<guillemotleft>-q"
  by (metis leq_def pre_closed pre_seq pre_test_neg)

lemma pre_test_test_same:
  "-p\<guillemotleft>-p = 1"
  using pre_test tests_dual.sba_dual.less_eq_sup_top tests_dual.sba_dual.reflexive by auto

lemma test_below_pre_test_mult:
  "-q \<le> -p\<guillemotleft>-p*-q"
  by (metis pre_test tests_dual.sba_dual.reflexive tests_dual.sba_dual.shunting tests_dual.sub_sup_closed)

lemma test_below_pre_test:
  "-q \<le> -p\<guillemotleft>-q"
  by (simp add: pre_test tests_dual.sba_dual.upper_bound_right)

lemma test_below_pre_test_2:
  "--p \<le> -p\<guillemotleft>-q"
  by (simp add: pre_test tests_dual.sba_dual.upper_bound_left)

lemma pre_test_bot:
  "-p\<guillemotleft>bot = --p"
  by (metis pre_test tests_dual.sba_dual.sup_right_unit tests_dual.top_double_complement)

lemma pre_test_one:
  "-p\<guillemotleft>1 = 1"
  by (metis pre_seq pre_bot tests_dual.sup_right_zero)

subclass precondition_test_test
  apply unfold_locales
  by (simp add: pre_test tests_dual.sup_complement_intro)

subclass precondition_promote
  apply unfold_locales
  by (metis pre_test tests_dual.sba_dual.sub_commutative tests_dual.sub_sup_closed tests_dual.inf_complement_intro)

(*
lemma pre_test: "-p\<guillemotleft>-q = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_distr_mult: "x\<guillemotleft>-p*-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" oops
lemma pre_distr_plus: "x\<guillemotleft>-p\<squnion>-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=2] oops
*)

end

class precondition_test_diamond = precondition +
  assumes pre_test: "-p\<guillemotleft>-q = -p*-q"
begin

lemma pre_test_neg:
  "--p*(-p\<guillemotleft>-q) = bot"
  by (simp add: pre_test tests_dual.sub_associative tests_dual.sub_commutative)

lemma pre_bot:
  "bot\<guillemotleft>-q = bot"
  by (metis pre_test tests_dual.sup_left_zero tests_dual.top_double_complement)

lemma pre_export:
  "-p*x\<guillemotleft>-q = -p*(x\<guillemotleft>-q)"
  by (metis pre_closed pre_seq pre_test)

lemma pre_neg_mult:
  "-p*x\<guillemotleft>-q \<le> -p"
  by (metis pre_closed pre_export tests_dual.upper_bound_left)

lemma pre_test_test_same:
  "-p\<guillemotleft>-p = -p"
  by (simp add: pre_test)

lemma test_above_pre_test_plus:
  "--p\<guillemotleft>-p\<squnion>-q \<le> -q"
  using pre_test tests_dual.sba_dual.inf_complement_intro tests_dual.sub_commutative tests_dual.sub_inf_def tests_dual.upper_bound_left by auto

lemma test_above_pre_test:
  "-p\<guillemotleft>-q \<le> -q"
  by (simp add: pre_test tests_dual.upper_bound_right)

lemma test_above_pre_test_2:
  "-p\<guillemotleft>-q \<le> -p"
  by (simp add: pre_test tests_dual.upper_bound_left)

lemma pre_test_bot:
  "-p\<guillemotleft>bot = bot"
  by (metis pre_test tests_dual.sup_right_zero tests_dual.top_double_complement)

lemma pre_test_one:
  "-p\<guillemotleft>1 = -p"
  by (metis pre_test tests_dual.complement_top tests_dual.sup_right_unit)

subclass precondition_test_test
  apply unfold_locales
  by (simp add: pre_test tests_dual.sub_associative)

subclass precondition_promote
  apply unfold_locales
  by (metis pre_seq pre_test tests_dual.sup_idempotent)

(*
lemma pre_test: "-p\<guillemotleft>-q = --p\<squnion>-q" nitpick [expect=genuine,card=2] oops
lemma pre_distr_mult: "x\<guillemotleft>-p*-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=6] oops
lemma pre_distr_plus: "x\<guillemotleft>-p\<squnion>-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=2] oops
*)

end

class precondition_distr_mult = precondition +
  assumes pre_distr_mult: "x\<guillemotleft>-p*-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)"
begin

(*
lemma pre_test_test: "-p*(-p\<guillemotleft>-q) = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test_promote: "-p\<guillemotleft>-q = -p\<guillemotleft>-p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = --p\<squnion>-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_distr_plus: "x\<guillemotleft>-p\<squnion>-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=2] oops
*)

end

class precondition_distr_plus = precondition +
  assumes pre_distr_plus: "x\<guillemotleft>-p\<squnion>-q = (x\<guillemotleft>-p)\<squnion>(x\<guillemotleft>-q)"
begin

(*
lemma pre_test_test: "-p*(-p\<guillemotleft>-q) = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test_promote: "-p\<guillemotleft>-q = -p\<guillemotleft>-p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = --p\<squnion>-q" nitpick [expect=genuine,card=2] oops
lemma pre_test: "-p\<guillemotleft>-q = -p*-q" nitpick [expect=genuine,card=2] oops
lemma pre_distr_mult: "x\<guillemotleft>-p*-q = (x\<guillemotleft>-p)*(x\<guillemotleft>-q)" nitpick [expect=genuine,card=4] oops
*)

end

end

