(* Title:      Hoare Calculus
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Hoare Calculus\<close>

theory Hoare

imports Complete_Tests Preconditions

begin

class ite =
  fixes ite :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<lhd> _ \<rhd> _" [58,58,58] 57)

class hoare_triple =
  fixes hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lbrace> _ \<rbrace> _" [54,54,54] 53)

class ifthenelse = precondition + ite +
  assumes ite_pre: "x\<lhd>-p\<rhd>y\<guillemotleft>-q = -p*(x\<guillemotleft>-q) \<squnion> --p*(y\<guillemotleft>-q)"
begin

text \<open>Theorem 40.2\<close>

lemma ite_pre_then:
  "-p*(x\<lhd>-p\<rhd>y\<guillemotleft>-q) = -p*(x\<guillemotleft>-q)"
proof -
  have "-p*(x\<lhd>-p\<rhd>y\<guillemotleft>-q) = -p*(x\<guillemotleft>-q) \<squnion> bot*(y\<guillemotleft>-q)"
    by (smt (z3) ite_pre pre_closed tests_dual.sba_dual.sup_right_unit tests_dual.sub_commutative tests_dual.sup_left_zero tests_dual.sup_right_dist_inf tests_dual.top_double_complement tests_dual.wnf_lemma_1)
  thus ?thesis
    by (metis pre_closed tests_dual.sba_dual.sup_right_unit tests_dual.sub_sup_closed tests_dual.sup_left_zero)
qed

text \<open>Theorem 40.3\<close>

lemma ite_pre_else:
  "--p*(x\<lhd>-p\<rhd>y\<guillemotleft>-q) = --p*(y\<guillemotleft>-q)"
proof -
  have "--p*(x\<lhd>-p\<rhd>y\<guillemotleft>-q) = bot*(x\<guillemotleft>-q) \<squnion> --p*(y\<guillemotleft>-q)"
    by (smt (z3) ite_pre pre_closed tests_dual.sub_commutative tests_dual.sub_inf_left_zero tests_dual.sup_left_zero tests_dual.sup_right_dist_inf tests_dual.top_double_complement tests_dual.wnf_lemma_3)
  thus ?thesis
    by (metis pre_closed tests_dual.sba_dual.sub_sup_demorgan tests_dual.sub_inf_left_zero tests_dual.sup_left_zero)
qed

lemma ite_import_mult_then:
  "-p*-q \<le> x\<guillemotleft>-r \<Longrightarrow> -p*-q \<le> x\<lhd>-p\<rhd>y\<guillemotleft>-r"
  by (smt ite_pre_then leq_def pre_closed sub_assoc sub_comm sub_mult_closed)

lemma ite_import_mult_else:
  "--p*-q \<le> y\<guillemotleft>-r \<Longrightarrow> --p*-q \<le> x\<lhd>-p\<rhd>y\<guillemotleft>-r"
  by (smt ite_pre_else leq_def pre_closed sub_assoc sub_comm sub_mult_closed)

text \<open>Theorem 40.1\<close>

lemma ite_import_mult:
  "-p*-q \<le> x\<guillemotleft>-r \<Longrightarrow> --p*-q \<le> y\<guillemotleft>-r \<Longrightarrow> -q \<le> x\<lhd>-p\<rhd>y\<guillemotleft>-r"
  by (smt (verit) ite_import_mult_else ite_import_mult_then pre_closed tests_dual.sba_dual.inf_less_eq_cases)

end

class whiledo = ifthenelse + while +
  assumes while_pre: "-p\<star>x\<guillemotleft>-q = -p*(x\<guillemotleft>-p\<star>x\<guillemotleft>-q) \<squnion> --p*-q"
  assumes while_post: "-p\<star>x\<guillemotleft>-q = -p\<star>x\<guillemotleft>--p*-q"
begin

text \<open>Theorem 40.4\<close>

lemma while_pre_then:
  "-p*(-p\<star>x\<guillemotleft>-q) = -p*(x\<guillemotleft>-p\<star>x\<guillemotleft>-q)"
  by (smt pre_closed tests_dual.sub_commutative while_pre tests_dual.wnf_lemma_1)

text \<open>Theorem 40.5\<close>

lemma while_pre_else:
  "--p*(-p\<star>x\<guillemotleft>-q) = --p*-q"
  by (smt pre_closed tests_dual.sub_commutative while_pre tests_dual.wnf_lemma_3)

text \<open>Theorem 40.6\<close>

lemma while_pre_sub_1:
  "-p\<star>x\<guillemotleft>-q \<le> x*(-p\<star>x)\<lhd>-p\<rhd>1\<guillemotleft>-q"
  by (smt (z3) ite_import_mult pre_closed pre_one_increasing pre_seq tests_dual.sba_dual.transitive tests_dual.sub_sup_closed tests_dual.upper_bound_right while_pre_else while_pre_then)

text \<open>Theorem 40.7\<close>

lemma while_pre_sub_2:
  "-p\<star>x\<guillemotleft>-q \<le> x\<lhd>-p\<rhd>1\<guillemotleft>-p\<star>x\<guillemotleft>-q"
  by (smt (z3) ite_import_mult pre_closed pre_one_increasing tests_dual.sba_dual.transitive tests_dual.sub_sup_closed tests_dual.upper_bound_right while_pre_then)

text \<open>Theorem 40.8\<close>

lemma while_pre_compl:
  "--p \<le> -p\<star>x\<guillemotleft>--p"
  by (metis pre_closed tests_dual.sup_idempotent tests_dual.upper_bound_right while_pre_else)

lemma while_pre_compl_one:
  "--p \<le> -p\<star>x\<guillemotleft>1"
  by (metis tests_dual.sba_dual.top_double_complement while_post tests_dual.sup_right_unit while_pre_compl)

text \<open>Theorem 40.10\<close>

lemma while_export_equiv:
  "-q \<le> -p\<star>x\<guillemotleft>1 \<longleftrightarrow> -p*-q \<le> -p\<star>x\<guillemotleft>1"
  by (smt pre_closed tests_dual.sba_dual.shunting tests_dual.sba_dual.sub_less_eq_def tests_dual.sba_dual.top_double_complement while_pre_compl_one)

lemma nat_test_pre:
  assumes "nat_test t s"
      and "-q \<le> s"
      and "\<forall>n . t n*-p*-q \<le> x\<guillemotleft>pSum t n*-q"
    shows "-q \<le> -p\<star>x\<guillemotleft>--p*-q"
proof -
  have 1: "-q*--p \<le> -p\<star>x\<guillemotleft>--p*-q"
    by (metis pre_closed tests_dual.sub_commutative while_post tests_dual.upper_bound_right while_pre_else)
  have "\<forall>n . t n*-p*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
  proof
    fix n
    show "t n*-p*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
    proof (induct n rule: nat_less_induct)
      fix n
      have 2: "t n = --(t n)"
        using assms(1) nat_test_def by auto
      assume "\<forall>m<n . t m*-p*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
      hence "\<forall>m<n . t m*-p*-q \<squnion> t m*--p*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
        using 1 by (smt (verit, del_insts) assms(1) tests_dual.greatest_lower_bound leq_def nat_test_def pre_closed tests_dual.sub_associative tests_dual.sub_commutative sub_mult_closed)
      hence "\<forall>m<n . t m*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
        by (smt (verit, del_insts) assms(1) tests_dual.sup_right_unit tests_dual.sup_left_dist_inf tests_dual.sup_right_dist_inf nat_test_def tests_dual.inf_complement sub_mult_closed)
      hence "pSum t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
        by (smt assms(1) pSum_below_nat pre_closed sub_mult_closed)
      hence "t n*-p*-q*(-p\<star>x\<guillemotleft>--p*-q) = t n*-p*-q"
        using 2 by (smt assms(1,3) leq_def pSum_test_nat pre_closed pre_sub_distr sub_assoc sub_comm sub_mult_closed transitive while_pre_then)
      thus "t n*-p*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
        using 2 by (smt (z3) pre_closed tests_dual.sub_sup_closed tests_dual.upper_bound_right)
    qed
  qed
  hence "-q*-p \<le> -p\<star>x\<guillemotleft>--p*-q"
    by (smt (verit, del_insts) assms(1,2) leq_def nat_test_def pre_closed tests_dual.sub_associative tests_dual.sub_commutative sub_mult_closed)
  thus ?thesis
    using 1 by (smt (z3) pre_closed tests_dual.sba_dual.inf_less_eq_cases tests_dual.sub_commutative tests_dual.sub_sup_closed)
qed

lemma nat_test_pre_1:
  assumes "nat_test t s"
      and "-r \<le> s"
      and "-r \<le> -q"
      and "\<forall>n . t n*-p*-q \<le> x\<guillemotleft>pSum t n*-q"
    shows "-r \<le> -p\<star>x\<guillemotleft>--p*-q"
proof -
  let ?qs = "-q*s"
  have 1: "-r \<le> ?qs"
    by (metis assms(1-3) nat_test_def tests_dual.least_upper_bound)
  have "\<forall>n . t n*-p*?qs \<le> x\<guillemotleft>pSum t n*?qs"
  proof
    fix n
    have 2: "pSum t n \<le> s"
      by (simp add: assms(1) pSum_below_sum)
    have "t n = t n * s"
      by (metis assms(1) nat_test_def tests_dual.sba_dual.less_eq_inf)
    hence "t n*-p*?qs = t n*-p*-q"
      by (smt (verit, ccfv_threshold) assms(1) nat_test_def tests_dual.sub_sup_closed tests_dual.sub_associative tests_dual.sub_commutative)
    also have "t n*-p*-q \<le> x\<guillemotleft>pSum t n*-q"
      by (simp add: assms(4))
    also have "x\<guillemotleft>pSum t n*-q = x\<guillemotleft>pSum t n*?qs"
      using 2 by (smt (verit, ccfv_SIG) assms(1) leq_def nat_test_def pSum_test_nat tests_dual.sub_associative tests_dual.sub_commutative)
    finally show "t n*-p*?qs \<le> x\<guillemotleft>pSum t n*?qs"
      .
  qed
  hence 3: "?qs \<le> -p\<star>x\<guillemotleft>--p*?qs"
    by (smt (verit, ccfv_threshold) assms(1) tests_dual.upper_bound_left tests_dual.upper_bound_right nat_test_def nat_test_pre pSum_test_nat pre_closed tests_dual.sub_associative sub_mult_closed transitive)
  have "-p\<star>x\<guillemotleft>--p*?qs \<le> -p\<star>x\<guillemotleft>--p*-q"
    by (metis assms(1) nat_test_def pre_lower_bound_left tests_dual.sub_sup_closed while_post)
  thus ?thesis
    using 1 3 by (smt (verit, del_insts) leq_def tests_dual.sub_associative assms(1) nat_test_def pre_closed sub_mult_closed)
qed

lemma nat_test_pre_2:
  assumes "nat_test t s"
      and "-r \<le> s"
      and "\<forall>n . t n*-p \<le> x\<guillemotleft>pSum t n"
    shows "-r \<le> -p\<star>x\<guillemotleft>1"
proof -
  have 1: "-r \<le> -p\<star>x\<guillemotleft>--p*s"
    by (smt (verit, ccfv_threshold) assms leq_def nat_test_def nat_test_pre_1 pSum_below_sum pSum_test_nat tests_dual.sub_associative tests_dual.sub_commutative)
  have "-p\<star>x\<guillemotleft>--p*s \<le> -p\<star>x\<guillemotleft>1"
    by (metis assms(1) nat_test_def pre_below_pre_one while_post)
  thus ?thesis
    using 1 by (smt (verit) assms(1) nat_test_def pre_closed tests_dual.sba_dual.top_double_complement while_post tests_dual.transitive)
qed

lemma nat_test_pre_3:
  assumes "nat_test t s"
      and "-q \<le> s"
      and "\<forall>n . t n*-p*-q \<le> x\<guillemotleft>pSum t n*-q"
    shows "-q \<le> -p\<star>x\<guillemotleft>1"
proof -
  have "-p\<star>x\<guillemotleft>--p*-q \<le> -p\<star>x\<guillemotleft>1"
    by (metis pre_below_pre_one sub_mult_closed)
  thus ?thesis
    by (smt (verit, ccfv_threshold) assms pre_closed tests_dual.sba_dual.top_double_complement tests_dual.sba_dual.transitive tests_dual.sub_sup_closed nat_test_pre)
qed

definition aL :: "'a"
  where "aL \<equiv> 1\<star>1\<guillemotleft>1"

lemma aL_test:
  "aL = --aL"
  by (metis aL_def one_def pre_closed)

end

class atoms = tests +
  fixes Atomic_program :: "'a set"
  fixes Atomic_test :: "'a set"
  assumes one_atomic_program: "1 \<in> Atomic_program"
  assumes zero_atomic_test: "bot \<in> Atomic_test"
  assumes atomic_test_test: "p \<in> Atomic_test \<longrightarrow> p = --p"

class while_program = whiledo + atoms + power
begin

inductive_set Test_expression :: "'a set"
  where atom_test: "p \<in> Atomic_test \<Longrightarrow> p \<in> Test_expression"
      | neg_test:  "p \<in> Test_expression \<Longrightarrow> -p \<in> Test_expression"
      | conj_test: "p \<in> Test_expression \<Longrightarrow> q \<in> Test_expression \<Longrightarrow> p*q \<in> Test_expression"

lemma test_expression_test:
  "p \<in> Test_expression \<Longrightarrow> p = --p"
  apply (induct rule: Test_expression.induct)
  apply (simp add: atomic_test_test)
  apply simp
  by (metis tests_dual.sub_sup_closed)

lemma disj_test:
  "p \<in> Test_expression \<Longrightarrow> q \<in> Test_expression \<Longrightarrow> p\<squnion>q \<in> Test_expression"
  by (smt conj_test neg_test tests_dual.sub_inf_def test_expression_test)

lemma zero_test_expression:
  "bot \<in> Test_expression"
  by (simp add: Test_expression.atom_test zero_atomic_test)

lemma one_test_expression:
  "1 \<in> Test_expression"
  using Test_expression.simps tests_dual.sba_dual.one_def zero_test_expression by blast

lemma pSum_test_expression:
  "(\<forall>n . t n \<in> Test_expression) \<Longrightarrow> pSum t m \<in> Test_expression"
  apply (induct m)
  apply (simp add: zero_test_expression)
  by (simp add: disj_test)

inductive_set While_program :: "'a set"
  where atom_prog:  "x \<in> Atomic_program \<Longrightarrow> x \<in> While_program"
      | seq_prog:   "x \<in> While_program \<Longrightarrow> y \<in> While_program \<Longrightarrow> x*y \<in> While_program"
      | cond_prog:  "p \<in> Test_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> y \<in> While_program \<Longrightarrow> x\<lhd>p\<rhd>y \<in> While_program"
      | while_prog: "p \<in> Test_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> p\<star>x \<in> While_program"

lemma one_while_program:
  "1 \<in> While_program"
  by (simp add: While_program.atom_prog one_atomic_program)

lemma power_while_program:
  "x \<in> While_program \<Longrightarrow> x^m \<in> While_program"
  apply (induct m)
  apply (simp add: one_while_program)
  by (simp add: While_program.seq_prog)

inductive_set Pre_expression :: "'a set"
  where test_pre: "p \<in> Test_expression \<Longrightarrow> p \<in> Pre_expression"
      | neg_pre:  "p \<in> Pre_expression \<Longrightarrow> -p \<in> Pre_expression"
      | conj_pre: "p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> p*q \<in> Pre_expression"
      | pre_pre:  "p \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> x\<guillemotleft>p \<in> Pre_expression"

lemma pre_expression_test:
  "p \<in> Pre_expression \<Longrightarrow> p = --p"
  apply (induct rule: Pre_expression.induct)
  apply (simp add: test_expression_test)
  apply simp
  apply (metis sub_mult_closed)
  by (metis pre_closed)

lemma disj_pre:
  "p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> p\<squnion>q \<in> Pre_expression"
  by (smt conj_pre neg_pre tests_dual.sub_inf_def pre_expression_test)

lemma zero_pre_expression:
  "bot \<in> Pre_expression"
  by (simp add: Pre_expression.test_pre zero_test_expression)

lemma one_pre_expression:
  "1 \<in> Pre_expression"
  by (simp add: Pre_expression.test_pre one_test_expression)

lemma pSum_pre_expression:
  "(\<forall>n . t n \<in> Pre_expression) \<Longrightarrow> pSum t m \<in> Pre_expression"
  apply (induct m)
  apply (simp add: zero_pre_expression)
  by (simp add: disj_pre)

lemma aL_pre_expression:
  "aL \<in> Pre_expression"
  by (simp add: Pre_expression.pre_pre While_program.while_prog aL_def one_pre_expression one_test_expression one_while_program)

end

class hoare_calculus = while_program + complete_tests
begin

definition tfun :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "tfun p x q r \<equiv> p \<squnion> (x\<guillemotleft>q*r)"

lemma tfun_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> tfun p x q r = --tfun p x q r"
  by (smt tfun_def sub_mult_closed pre_closed tests_dual.inf_closed)

lemma tfun_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> r \<in> Pre_expression \<Longrightarrow> tfun p x q r \<in> Pre_expression"
  by (simp add: Pre_expression.conj_pre Pre_expression.pre_pre disj_pre tfun_def)

lemma tfun_iso:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> s = --s \<Longrightarrow> r \<le> s \<Longrightarrow> tfun p x q r \<le> tfun p x q s"
  by (smt tfun_def tests_dual.sub_sup_right_isotone pre_iso sub_mult_closed tests_dual.sub_inf_right_isotone pre_closed)

definition tseq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "tseq p x q r m \<equiv> (tfun p x q ^ m) r"

lemma tseq_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> tseq p x q r m = --tseq p x q r m"
  apply (induct m)
  apply (smt tseq_def tfun_test power_zero_id id_def)
  by (metis tseq_def tfun_test power_succ_unfold_ext)

lemma tseq_test_seq:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> test_seq (tseq p x q r)"
  using test_seq_def tseq_test by auto

lemma tseq_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> r \<in> Pre_expression \<Longrightarrow> tseq p x q r m \<in> Pre_expression"
  apply (induct m)
  apply (smt tseq_def id_def power_zero_id)
  by (smt tseq_def power_succ_unfold_ext tfun_pre_expression)

definition tsum :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "tsum p x q r \<equiv> Sum (tseq p x q r)"

lemma tsum_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> tsum p x q r = --tsum p x q r"
  using Sum_test tseq_test_seq tsum_def by auto

lemma t_fun_test:
  "q = --q \<Longrightarrow> tfun (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) = --tfun (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
  by (metis aL_test pre_closed tests_dual.sba_dual.double_negation tfun_def tfun_test)

lemma t_fun_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> tfun (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) \<in> Pre_expression"
  by (simp add: Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre Pre_expression.test_pre While_program.while_prog aL_pre_expression disj_pre tfun_pre_expression)

lemma t_seq_test:
  "q = --q \<Longrightarrow> tseq (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m = --tseq (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m"
  by (metis aL_test pre_closed tests_dual.sba_dual.double_negation tfun_def tfun_test tseq_test)

lemma t_seq_test_seq:
  "q = --q \<Longrightarrow> test_seq (tseq (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)))"
  using test_seq_def t_seq_test by auto

lemma t_seq_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> tseq (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m \<in> Pre_expression"
  using Pre_expression.pre_pre Pre_expression.test_pre Test_expression.neg_test While_program.while_prog aL_pre_expression tfun_def tfun_pre_expression tseq_pre_expression by auto

lemma t_sum_test:
  "q = --q \<Longrightarrow> tsum (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) = --tsum (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
  using Sum_test t_seq_test_seq tsum_def by auto

definition tfun2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "tfun2 p q x r s \<equiv> p \<squnion> q*(x\<guillemotleft>r*s)"

lemma tfun2_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> s = --s \<Longrightarrow> tfun2 p q x r s = --tfun2 p q x r s"
  by (smt tfun2_def sub_mult_closed pre_closed tests_dual.inf_closed)

lemma tfun2_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> r \<in> Pre_expression \<Longrightarrow> s \<in> Pre_expression \<Longrightarrow> tfun2 p q x r s \<in> Pre_expression"
  by (simp add: Pre_expression.conj_pre Pre_expression.pre_pre disj_pre tfun2_def)

lemma tfun2_iso:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> s1 = --s1 \<Longrightarrow> s2 = --s2 \<Longrightarrow> s1 \<le> s2 \<Longrightarrow> tfun2 p q x r s1 \<le> tfun2 p q x r s2"
  by (smt tfun2_def tests_dual.sub_inf_right_isotone pre_iso sub_mult_closed tests_dual.sub_sup_right_isotone pre_closed)

definition tseq2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "tseq2 p q x r s m \<equiv> (tfun2 p q x r ^ m) s"

lemma tseq2_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> s = --s \<Longrightarrow> tseq2 p q x r s m = --tseq2 p q x r s m"
  apply (induct m)
  apply (smt tseq2_def power_zero_id id_def)
  by (smt tseq2_def tfun2_test power_succ_unfold_ext)

lemma tseq2_test_seq:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> s = --s \<Longrightarrow> test_seq (tseq2 p q x r s)"
  using test_seq_def tseq2_test by force

lemma tseq2_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> r \<in> Pre_expression \<Longrightarrow> s \<in> Pre_expression \<Longrightarrow> tseq2 p q x r s m \<in> Pre_expression"
  apply (induct m)
  apply (smt tseq2_def id_def power_zero_id)
  by (smt tseq2_def power_succ_unfold_ext tfun2_pre_expression)

definition tsum2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "tsum2 p q x r s \<equiv> Sum (tseq2 p q x r s)"

lemma tsum2_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> r = --r \<Longrightarrow> s = --s \<Longrightarrow> tsum2 p q x r s = --tsum2 p q x r s"
  using Sum_test tseq2_test_seq tsum2_def by force

lemma t_fun2_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> tfun2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) = --tfun2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
  by (smt (z3) aL_test pre_closed tests_dual.sub_sup_closed tfun2_def tfun2_test)

lemma t_fun2_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> tfun2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) \<in> Pre_expression"
  by (simp add: Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre Pre_expression.test_pre While_program.while_prog aL_pre_expression disj_pre tfun2_pre_expression)

lemma t_seq2_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m = --tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m"
  by (smt (z3) aL_test pre_closed tests_dual.sub_sup_closed tfun2_def tfun2_test tseq2_test)

lemma t_seq2_test_seq:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> test_seq (tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)))"
  using test_seq_def t_seq2_test by auto

lemma t_seq2_pre_expression:
  "x \<in> While_program \<Longrightarrow> p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m \<in> Pre_expression"
  by (simp add: Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre Pre_expression.test_pre While_program.while_prog aL_pre_expression disj_pre tseq2_pre_expression)

lemma t_sum2_test:
  "p = --p \<Longrightarrow> q = --q \<Longrightarrow> tsum2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) = --tsum2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
  using Sum_test t_seq2_test_seq tsum2_def by auto

lemma t_seq2_below_t_seq:
  assumes "p \<in> Test_expression"
      and "q \<in> Pre_expression"
    shows "tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m \<le> tseq (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m"
proof -
  let ?t2 = "tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
  let ?t = "tseq (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
  show "?thesis"
  proof (induct m)
    case 0
    show "?t2 0 \<le> ?t 0"
      by (smt assms aL_test id_def tests_dual.upper_bound_left tests_dual.upper_bound_right tests_dual.inf_isotone power_zero_id pre_closed pre_expression_test sub_mult_closed test_pre tseq2_def tseq_def)
  next
    fix m
    assume "?t2 m \<le> ?t m"
    hence 1: "?t2 (Suc m) \<le> tfun2 (- p * q) p x (p \<star> x \<guillemotleft> q) (?t m)"
      by (smt assms power_succ_unfold_ext pre_closed pre_expression_test sub_mult_closed t_seq2_test t_seq_test test_pre tfun2_iso tseq2_def)
    have "... \<le> ?t (Suc m)"
      by (smt assms tests_dual.upper_bound_left tests_dual.upper_bound_right tests_dual.inf_isotone power_succ_unfold_ext pre_closed pre_expression_test sub_mult_closed t_seq_test test_pre tfun2_def tfun_def tseq_def)
    thus "?t2 (Suc m) \<le> ?t (Suc m)"
      using 1 by (smt (verit, del_insts) assms pre_closed pre_expression_test test_expression_test tests_dual.sba_dual.transitive tests_dual.sub_sup_closed t_seq2_test t_seq_test tfun2_test)
  qed
qed

lemma t_seq2_below_t_sum:
  "p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m \<le> tsum (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
   by (smt (verit, del_insts) Sum_upper pre_expression_test t_seq2_below_t_seq t_seq2_test t_seq_test t_sum_test test_pre test_seq_def tsum_def leq_def tests_dual.sub_associative)

lemma t_sum2_below_t_sum:
  "p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> tsum2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) \<le> tsum (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
  by (smt Sum_least pre_expression_test t_seq2_below_t_sum t_seq2_test t_sum_test test_pre test_seq_def tsum2_def)

lemma t_seq2_below_w:
  "p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m \<le> p\<star>x\<guillemotleft>q"
  apply (cases m)
  apply (smt aL_test id_def tests_dual.upper_bound_left tests_dual.sub_sup_right_isotone tests_dual.inf_commutative tests_dual.sub_inf_right_isotone power_zero_id pre_closed pre_expression_test pre_iso sub_mult_closed test_pre tseq2_def while_pre)
  by (smt tseq2_def power_succ_unfold_ext tests_dual.upper_bound_left tests_dual.sub_sup_right_isotone tests_dual.inf_commutative tests_dual.sub_inf_right_isotone pre_closed pre_expression_test pre_iso sub_mult_closed t_seq2_test test_pre tseq2_def while_pre tfun2_def)

lemma t_sum2_below_w:
  "p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> tsum2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) \<le> p\<star>x\<guillemotleft>q"
  by (smt Sum_least pre_closed pre_expression_test t_seq2_below_w t_seq2_test_seq test_pre tsum2_def)

lemma t_sum2_w:
  assumes "aL = 1"
      and "p \<in> Test_expression"
      and "q \<in> Pre_expression"
      and "x \<in> While_program"
    shows "tsum2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) = p\<star>x\<guillemotleft>q"
proof -
  let ?w = "p\<star>x\<guillemotleft>q"
  let ?s = "-p*q\<squnion>p*(x\<guillemotleft>?w*aL)"
  have "?w = tseq2 (-p*q) p x ?w ?s 0"
    by (smt assms(1-3) tests_dual.sup_right_unit id_def tests_dual.inf_commutative power_zero_id pre_closed pre_expression_test sub_mult_closed test_expression_test tseq2_def while_pre)
  hence "?w \<le> tsum2 (-p*q) p x ?w ?s"
    by (smt assms(2,3) Sum_upper pre_expression_test t_seq2_test_seq test_pre tsum2_def)
  thus ?thesis
    by (smt assms(2-4) tests_dual.antisymmetric pre_closed pre_expression_test t_sum2_test t_sum2_below_w test_pre)
qed

inductive derived_hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<lparr> _ \<rparr> _" [54,54,54] 53)
  where atom_trip:  "p \<in> Pre_expression \<Longrightarrow> x \<in> Atomic_program \<Longrightarrow> x\<guillemotleft>p\<lparr>x\<rparr>p"
      | seq_trip:   "p\<lparr>x\<rparr>q \<and> q\<lparr>y\<rparr>r \<Longrightarrow> p\<lparr>x*y\<rparr>r"
      | cond_trip:  "p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> p*q\<lparr>x\<rparr>r \<and> -p*q\<lparr>y\<rparr>r \<Longrightarrow> q\<lparr>x\<lhd>p\<rhd>y\<rparr>r"
      | while_trip: "p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> test_seq t \<and> q \<le> Sum t \<Longrightarrow> t 0*p*q\<lparr>x\<rparr>aL*q \<Longrightarrow> (\<forall>n>0 . t n*p*q\<lparr>x\<rparr>pSum t n*q) \<Longrightarrow> q\<lparr>p\<star>x\<rparr>-p*q"
      | cons_trip:  "p \<in> Pre_expression \<Longrightarrow> s \<in> Pre_expression \<Longrightarrow> p \<le> q \<and> q\<lparr>x\<rparr>r \<Longrightarrow> r \<le> s \<Longrightarrow> p\<lparr>x\<rparr>s"

lemma derived_type:
  "p\<lparr>x\<rparr>q \<Longrightarrow> p \<in> Pre_expression \<and> q \<in> Pre_expression \<and> x \<in> While_program"
  apply (induct rule: derived_hoare_triple.induct)
  apply (simp add: Pre_expression.pre_pre While_program.atom_prog)
  using While_program.seq_prog apply blast
  using While_program.cond_prog apply blast
  using Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.test_pre While_program.while_prog apply simp
  by blast

lemma cons_pre_trip:
  "p \<in> Pre_expression \<Longrightarrow> q\<lparr>y\<rparr>r \<Longrightarrow> p*q\<lparr>y\<rparr>r"
  by (metis cons_trip derived_type Pre_expression.conj_pre pre_expression_test tests_dual.sba_dual.reflexive tests_dual.upper_bound_right)

lemma cons_post_trip:
  "q \<in> Pre_expression \<Longrightarrow> r \<in> Pre_expression \<Longrightarrow> p\<lparr>y\<rparr>q*r \<longrightarrow> p\<lparr>y\<rparr>r"
  by (metis cons_trip derived_type pre_expression_test tests_dual.sba_dual.reflexive tests_dual.upper_bound_right)

definition valid_hoare_triple :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<langle> _ \<rangle> _" [54,54,54] 53)
  where "p\<langle>x\<rangle>q \<equiv> (p \<in> Pre_expression \<and> q \<in> Pre_expression \<and> x \<in> While_program \<and> p \<le> x\<guillemotleft>q)"

end

class hoare_calculus_sound = hoare_calculus +
  assumes while_soundness: "-p*-q \<le> x\<guillemotleft>-q \<longrightarrow> aL*-q \<le> -p\<star>x\<guillemotleft>-q"
begin

lemma while_soundness_0:
  "-p*-q \<le> x\<guillemotleft>-q \<Longrightarrow> -q*aL \<le> -p\<star>x\<guillemotleft>--p*-q"
  by (smt while_soundness aL_test sub_comm while_post)

lemma while_soundness_1:
  assumes "test_seq t"
      and "-q \<le> Sum t"
      and "t 0*-p*-q \<le> x\<guillemotleft>aL*-q"
      and "\<forall>n>0 . t n*-p*-q \<le> x\<guillemotleft>pSum t n*-q"
    shows "-q \<le> -p\<star>x\<guillemotleft>--p*-q"
proof -
  have "\<forall>n . t n*-p*-q \<le> x\<guillemotleft>-q"
  proof
    fix n
    show "t n*-p*-q \<le> x\<guillemotleft>-q"
    proof (cases n)
      case 0
      thus ?thesis
        by (smt (z3) assms(1) assms(3) aL_test leq_def pre_closed pre_lower_bound_right test_seq_def tests_dual.sub_associative tests_dual.sub_sup_closed)
    next
      case (Suc m)
      hence 1: "t n*-p*-q \<le> x\<guillemotleft>pSum t n*-q"
        using assms(4) by blast
      have "x\<guillemotleft>pSum t n*-q \<le> x\<guillemotleft>-q"
        by (metis assms(1) pSum_test pre_lower_bound_right)
      thus ?thesis
        using 1 by (smt (verit, del_insts) assms(1) pSum_test pre_closed sub_mult_closed test_seq_def leq_def tests_dual.sub_associative)
    qed
  qed
  hence 2: "-p*-q \<le> x\<guillemotleft>-q"
    by (smt assms(1,2) Sum_test leq_def mult_right_dist_Sum pre_closed sub_assoc sub_comm sub_mult_closed test_seq_def)
  have "\<forall>n . t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q \<and> pSum t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
  proof
    fix n
    show "t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q \<and> pSum t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
    proof (induct n rule: nat_less_induct)
      fix n
      assume 3: "\<forall>m<n . t m*-q \<le> -p\<star>x\<guillemotleft>--p*-q \<and> pSum t m*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
      have 4: "pSum t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
      proof (cases n)
        case 0
        thus ?thesis
          by (metis pSum.simps(1) pre_closed sub_mult_closed tests_dual.top_greatest tests_dual.sba_dual.less_eq_inf tests_dual.top_double_complement)
      next
        case (Suc m)
        hence "pSum t n*-q = (pSum t m \<squnion> t m)*-q"
          by simp
        also have "... = pSum t m*-q \<squnion> t m*-q"
          by (metis (full_types) assms(1) pSum_test test_seq_def tests_dual.sup_right_dist_inf)
        also have "... \<le> -p\<star>x\<guillemotleft>--p*-q"
        proof -
          have "pSum t m*-q = --(pSum t m*-q) \<and> t m*-q = --(t m*-q) \<and> -p\<star>x\<guillemotleft>--p*-q = --(-p\<star>x\<guillemotleft>--p*-q)"
            apply (intro conjI)
            apply (metis assms(1) pSum_test tests_dual.sub_sup_closed)
            apply (metis assms(1) test_seq_def tests_dual.sub_sup_closed)
            by (metis pre_closed tests_dual.sub_sup_closed)
          thus ?thesis
            using 3 by (smt (z3) lessI Suc tests_dual.greatest_lower_bound sub_mult_closed)
        qed
        finally show ?thesis
          .
      qed
      hence 5: "x\<guillemotleft>pSum t n*-q \<le> x\<guillemotleft>-p\<star>x\<guillemotleft>--p*-q"
        by (smt assms pSum_test pre_closed pre_iso sub_mult_closed)
      have 6: "-p*(t n*-q) \<le> -p*(-p\<star>x\<guillemotleft>--p*-q)"
      proof (cases n)
        case 0
        thus ?thesis
          using 2 by (smt assms(1,3) aL_test leq_def tests_dual.sup_idempotent tests_dual.sub_sup_right_isotone pre_closed pre_lower_bound_left sub_assoc sub_comm sub_mult_closed test_seq_def transitive while_pre_then while_soundness_0)
      next
        case (Suc m)
        hence "-p*(t n*-q) \<le> x\<guillemotleft>pSum t n*-q"
          by (smt assms(1,4) test_seq_def tests_dual.sub_associative tests_dual.sub_commutative zero_less_Suc)
        hence "-p*(t n*-q) \<le> x\<guillemotleft>-p\<star>x\<guillemotleft>--p*-q"
          using 5 by (smt assms(1) tests_dual.least_upper_bound pSum_test pre_closed sub_mult_closed test_seq_def leq_def)
        hence "-p*(t n*-q) \<le> -p*(x\<guillemotleft>-p\<star>x\<guillemotleft>--p*-q)"
          by (smt assms(1) tests_dual.upper_bound_left pre_closed sub_mult_closed test_seq_def leq_def tests_dual.sub_associative)
        thus ?thesis
          using while_post while_pre_then by auto
      qed
      have "--p*(t n*-q) \<le> --p*(-p\<star>x\<guillemotleft>--p*-q)"
        by (smt assms(1) leq_def tests_dual.upper_bound_right sub_assoc sub_comm sub_mult_closed test_seq_def while_pre_else)
      thus "t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q \<and> pSum t n*-q \<le> -p\<star>x\<guillemotleft>--p*-q"
        using 4 6 by (smt assms(1) tests_dual.sup_less_eq_cases_2 pre_closed sub_mult_closed test_seq_def)
    qed
  qed
  thus ?thesis
    by (smt assms(1,2) Sum_test leq_def mult_right_dist_Sum pre_closed sub_comm sub_mult_closed)
qed

lemma while_soundness_2:
  assumes "test_seq t"
      and "-r \<le> Sum t"
      and "\<forall>n . t n*-p \<le> x\<guillemotleft>pSum t n"
    shows "-r \<le> -p\<star>x\<guillemotleft>1"
proof -
  have 1: "\<forall>n>0 . t n*-p*Sum t \<le> x\<guillemotleft>pSum t n*Sum t"
    by (smt (z3) assms(1,3) Sum_test Sum_upper leq_def pSum_below_Sum pSum_test test_seq_def tests_dual.sub_associative tests_dual.sub_commutative)
  have 2: "t 0*-p*Sum t \<le> x\<guillemotleft>bot"
    by (smt assms(1,3) Sum_test Sum_upper leq_def sub_assoc sub_comm test_seq_def pSum.simps(1))
  have "x\<guillemotleft>bot \<le> x\<guillemotleft>aL*Sum t"
    by (smt assms(1) Sum_test aL_test pre_iso sub_mult_closed tests_dual.top_double_complement tests_dual.top_greatest)
  hence "t 0*-p*Sum t \<le> x\<guillemotleft>aL*Sum t"
    using 2 by (smt (z3) assms(1) Sum_test aL_test leq_def pSum.simps(1) pSum_test pre_closed test_seq_def tests_dual.sub_associative tests_dual.sub_sup_closed)
  hence 3: "Sum t \<le> -p\<star>x\<guillemotleft>--p*Sum t"
    using 1 by (smt (verit, del_insts) assms(1) Sum_test tests_dual.sba_dual.one_def tests_dual.sup_right_unit tests_dual.upper_bound_left while_soundness_1)
  have "-p\<star>x\<guillemotleft>--p*Sum t \<le> -p\<star>x\<guillemotleft>1"
    by (metis assms(1) Sum_test pre_below_pre_one tests_dual.sub_sup_closed)
  hence "Sum t \<le> -p\<star>x\<guillemotleft>1"
    using 3 by (smt (z3) assms(1) Sum_test pre_closed tests_dual.sba_dual.one_def while_post tests_dual.transitive)
  thus ?thesis
    by (smt (z3) assms(1,2) Sum_test pre_closed tests_dual.sba_dual.one_def tests_dual.transitive)
qed

theorem soundness:
  "p\<lparr>x\<rparr>q \<Longrightarrow> p\<langle>x\<rangle>q"
  apply (induct rule: derived_hoare_triple.induct)
  apply (metis Pre_expression.pre_pre While_program.atom_prog pre_expression_test tests_dual.sba_dual.reflexive valid_hoare_triple_def)
  apply (metis valid_hoare_triple_def pre_expression_test pre_compose While_program.seq_prog)
  apply (metis valid_hoare_triple_def ite_import_mult pre_expression_test cond_prog test_pre)
  apply (smt (verit, del_insts) Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.test_pre While_program.while_prog pre_expression_test valid_hoare_triple_def while_soundness_1)
  by (metis pre_expression_test pre_iso pre_pre tests_dual.sba_dual.transitive valid_hoare_triple_def)

end

class hoare_calculus_pre_complete = hoare_calculus +
  assumes aL_pre_import: "(x\<guillemotleft>-q)*aL \<le> x\<guillemotleft>-q*aL"
  assumes pre_right_dist_Sum: "x \<in> While_program \<and> ascending_chain t \<and> test_seq t \<longrightarrow> x\<guillemotleft>Sum t = Sum (\<lambda>n . x\<guillemotleft>t n)"
begin

lemma aL_pre_import_equal:
  "(x\<guillemotleft>-q)*aL = (x\<guillemotleft>-q*aL)*aL"
proof -
  have 1: "(x\<guillemotleft>-q)*aL \<le> (x\<guillemotleft>-q*aL)*aL"
    by (smt (z3) aL_pre_import aL_test pre_closed tests_dual.sub_sup_closed tests_dual.least_upper_bound tests_dual.upper_bound_right)
  have "(x\<guillemotleft>-q*aL)*aL \<le> (x\<guillemotleft>-q)*aL"
    by (smt (verit, ccfv_threshold) aL_test pre_closed pre_lower_bound_left tests_dual.sba_dual.inf_isotone tests_dual.sba_dual.reflexive tests_dual.sub_sup_closed)
  thus ?thesis
    using 1 by (smt (z3) tests_dual.antisymmetric aL_test pre_closed tests_dual.sub_sup_closed)
qed

lemma aL_pre_below_t_seq2:
  assumes "p \<in> Test_expression"
      and "q \<in> Pre_expression"
    shows "(p\<star>x\<guillemotleft>q)*aL \<le> tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) 0"
proof (unfold tseq2_def power_zero_id id_def while_pre)
  have "(p\<star>x\<guillemotleft>q)*aL = (p*(x\<guillemotleft>p\<star>x\<guillemotleft>q) \<squnion> -p*q)*aL"
    by (metis assms while_pre test_pre pre_expression_test)
  also have "... = p*(x\<guillemotleft>p\<star>x\<guillemotleft>q)*aL \<squnion> -p*q*aL"
    by (smt (z3) assms aL_test tests_dual.sup_right_dist_inf pre_closed pre_expression_test sub_mult_closed test_pre)
  also have "... = p*((x\<guillemotleft>p\<star>x\<guillemotleft>q)*aL) \<squnion> -p*q*aL"
    by (smt assms aL_test pre_closed pre_expression_test test_pre sub_assoc)
  also have "... \<le> p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL) \<squnion> -p*q"
  proof -
    have 1: "(x\<guillemotleft>p\<star>x\<guillemotleft>q)*aL \<le> x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL"
      by (metis assms(2) pre_closed pre_expression_test aL_pre_import)
    have "-p*q*aL \<le> -p*q"
      by (metis assms(2) aL_test pre_expression_test tests_dual.sub_sup_closed tests_dual.upper_bound_left)
    thus ?thesis
      using 1 by (smt assms aL_test pre_closed pre_expression_test test_pre tests_dual.sub_sup_closed tests_dual.sub_sup_right_isotone tests_dual.inf_isotone)
  qed
  also have "... = -p*q \<squnion> p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)"
    by (smt assms aL_test tests_dual.inf_commutative pre_closed pre_expression_test test_pre tests_dual.sub_sup_closed)
  finally show "(p\<star>x\<guillemotleft>q)*aL \<le> -p*q \<squnion> p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)"
    .
qed

lemma t_seq2_ascending:
  assumes "p \<in> Test_expression"
      and "q \<in> Pre_expression"
      and "x \<in> While_program"
    shows "tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) m \<le> tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)) (Suc m)"
proof (induct m)
  let ?w = "p\<star>x\<guillemotleft>q"
  let ?r = "-p*q\<squnion>p*(x\<guillemotleft>?w*aL)"
  case 0
  have 1: "?w*aL = --(?w*aL)"
    by (simp add: assms Pre_expression.conj_pre Pre_expression.pre_pre While_program.while_prog aL_pre_expression pre_expression_test)
  have 2: "?r = --?r"
    by (simp add: assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre Pre_expression.test_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test)
  have "?w*aL \<le> ?r"
    by (metis aL_pre_below_t_seq2 assms(1,2) id_def tseq2_def power_zero_id)
  hence "?w*aL \<le> ?w*?r"
    using 1 2 by (smt (verit, ccfv_threshold) assms Pre_expression.pre_pre While_program.while_prog aL_test pre_expression_test tests_dual.sub_associative tests_dual.sub_sup_right_isotone tests_dual.sba_dual.less_eq_inf tests_dual.sba_dual.reflexive)
  hence "x\<guillemotleft>?w*aL \<le> x\<guillemotleft>(?w*?r)"
    by (smt (verit, ccfv_threshold) assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test pre_iso test_pre)
  hence "p*(x\<guillemotleft>?w*aL) \<le> p*(x\<guillemotleft>(?w*?r))"
    by (smt (z3) assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test test_pre tests_dual.sub_sup_right_isotone)
  hence "?r \<le> -p*q\<squnion>p*(x\<guillemotleft>(?w*?r))"
    by (smt (verit, del_insts) assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test test_pre tests_dual.sba_dual.reflexive tests_dual.inf_isotone)
  thus ?case
    by (unfold tseq2_def power_zero_id power_succ_unfold_ext id_def tfun2_def)
next
  let ?w = "p\<star>x\<guillemotleft>q"
  let ?r = "-p*q\<squnion>p*(x\<guillemotleft>?w*aL)"
  let ?t = "tseq2 (-p*q) p x ?w ?r"
  case (Suc m)
  hence "?w*?t m \<le> ?w*?t (Suc m)"
    by (smt (z3) assms(1,2) pre_closed pre_expression_test t_seq2_test test_expression_test tests_dual.sub_sup_right_isotone)
  hence "x\<guillemotleft>?w*?t m \<le> x\<guillemotleft>?w*?t (Suc m)"
    by (smt (z3) assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test pre_iso test_pre tseq2_pre_expression)
  hence "p*(x\<guillemotleft>?w*?t m) \<le> p*(x\<guillemotleft>?w*?t (Suc m))"
    by (smt (z3) assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test test_pre tests_dual.sub_sup_right_isotone tseq2_pre_expression)
  hence "-p*q\<squnion>p*(x\<guillemotleft>?w*?t m) \<le> -p*q\<squnion>p*(x\<guillemotleft>?w*?t (Suc m))"
    by (smt (z3) assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test test_pre tests_dual.sba_dual.reflexive tests_dual.inf_isotone tseq2_pre_expression)
  thus ?case
    by (smt tseq2_def power_succ_unfold_ext tfun2_def)
qed

lemma t_seq2_ascending_chain:
  "p \<in> Test_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> ascending_chain (tseq2 (-p*q) p x (p\<star>x\<guillemotleft>q) (-p*q\<squnion>p*(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL)))"
  by (simp add: ord.ascending_chain_def t_seq2_ascending)

end

class hoare_calculus_complete = hoare_calculus_pre_complete +
  assumes while_completeness: "-p*(x\<guillemotleft>-q) \<le> -q \<longrightarrow> -p\<star>x\<guillemotleft>-q \<le> -q\<squnion>aL"
begin

lemma while_completeness_var:
  assumes "-p*(x\<guillemotleft>-q)\<squnion>-r \<le> -q"
    shows "-p\<star>x\<guillemotleft>-r \<le> -q\<squnion>aL"
proof -
  have 1: "-p\<star>x\<guillemotleft>-q \<le> -q\<squnion>aL"
    by (smt assms pre_closed tests_dual.sub_sup_closed tests_dual.greatest_lower_bound while_completeness)
  have "-p\<star>x\<guillemotleft>-r \<le> -p\<star>x\<guillemotleft>-q"
    by (smt assms pre_closed tests_dual.sub_sup_closed tests_dual.greatest_lower_bound pre_iso)
  thus ?thesis
    using 1 by (smt (z3) aL_test pre_closed tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.transitive)
qed

lemma while_completeness_sum:
  assumes "p \<in> Test_expression"
      and "q \<in> Pre_expression"
      and "x \<in> While_program"
    shows "p\<star>x\<guillemotleft>q \<le> tsum (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
proof -
  let ?w = "p\<star>x\<guillemotleft>q"
  let ?r = "-p*q\<squnion>p*(x\<guillemotleft>?w*aL)"
  let ?t = "tseq2 (-p*q) p x ?w ?r"
  let ?ts = "tsum2 (-p*q) p x ?w ?r"
  have 1: "?w = --?w"
    by (metis assms(2) pre_expression_test pre_closed)
  have 2: "?r = --?r"
    by (simp add: assms Pre_expression.conj_pre Pre_expression.neg_pre Pre_expression.pre_pre Pre_expression.test_pre While_program.while_prog aL_pre_expression disj_pre pre_expression_test)
  have 3: "?ts = --?ts"
    by (meson assms(1) assms(2) pre_expression_test t_sum2_test test_expression_test)
  have 4: "test_seq ?t"
    by (simp add: assms(1) assms(2) pre_expression_test t_seq2_test_seq test_expression_test)
  have "-p*q \<le> ?r"
    by (smt (z3) assms(1,2) aL_test pre_closed pre_expression_test sub_mult_closed test_pre tests_dual.lower_bound_left)
  hence 5: "-p*q \<le> ?ts"
    using 1 2 3 by (smt assms Sum_upper id_def tests_dual.sba_dual.transitive power_zero_id pre_expression_test sub_mult_closed test_pre tseq2_def tseq2_test_seq tsum2_def)
  have "\<forall>n . p*(x\<guillemotleft>?t n) \<le> ?ts"
  proof (rule allI, unfold tsum2_def)
    fix n
    have 6: "p*(x\<guillemotleft>?t n) \<le> ?t (Suc n)"
      using 4 by (smt assms leq_def power_succ_unfold_ext pre_closed pre_expression_test tests_dual.sub_commutative sub_mult_closed t_seq2_below_w test_pre test_seq_def tfun2_def tseq2_def tests_dual.lower_bound_right)
    have "?t (Suc n) \<le> Sum ?t"
      using 4 Sum_upper by auto
    thus "p*(x\<guillemotleft>?t n) \<le> Sum ?t"
      using 3 4 6 by (smt assms(1) pre_closed pre_expression_test sub_mult_closed test_pre test_seq_def tests_dual.transitive tsum2_def)
  qed
  hence "p*(x\<guillemotleft>?ts) \<le> ?ts"
    using 3 4 by (smt assms mult_left_dist_Sum pre_closed pre_right_dist_Sum t_seq2_ascending_chain test_expression_test test_seq_def tsum2_def)
  hence "p*(x\<guillemotleft>?ts)\<squnion>-p*q \<le> ?ts"
    using 3 5 by (smt assms(1,2) tests_dual.greatest_lower_bound pre_closed pre_expression_test sub_mult_closed test_pre)
  hence "?w \<le> ?ts\<squnion>aL"
    using 1 3 by (smt assms(1,2) pre_expression_test while_post sub_mult_closed t_sum2_below_t_sum t_sum_test test_pre transitive while_completeness_var)
  hence "?w = ?w*(?ts\<squnion>aL)"
    using 1 3 by (smt aL_test tests_dual.sba_dual.less_eq_inf tests_dual.sba_dual.sub_sup_closed)
  also have "... = ?w*?ts\<squnion>?w*aL"
    using 1 3 by (smt aL_test tests_dual.sup_left_dist_inf)
  also have "... \<le> ?ts\<squnion>?t 0"
    using 1 3 4 by (smt (z3) assms(1,2) aL_pre_below_t_seq2 tests_dual.upper_bound_right aL_test test_seq_def tests_dual.sub_sup_closed tests_dual.inf_isotone)
  also have "... = ?ts"
    using 3 4 by (smt Sum_upper tsum2_def test_seq_def tests_dual.less_eq_inf)
  finally have "?w \<le> ?ts"
    .
  thus ?thesis
    using 1 3 by (metis assms t_sum2_below_t_sum t_sum2_below_w tests_dual.antisymmetric)
qed

lemma while_complete:
  assumes "p \<in> Test_expression"
      and "q \<in> Pre_expression"
      and "x \<in> While_program"
      and "\<forall>r\<in>Pre_expression . x\<guillemotleft>r\<lparr>x\<rparr>r"
    shows "p\<star>x\<guillemotleft>q\<lparr>p\<star>x\<rparr>q"
proof -
  let ?w = "p\<star>x\<guillemotleft>q"
  let ?t = "tseq (-p) x ?w (-p\<squnion>(x\<guillemotleft>?w*aL))"
  have 1: "?w \<in> Pre_expression"
    by (simp add: assms(1-3) Pre_expression.pre_pre While_program.while_prog)
  have 2: "test_seq ?t"
    by (simp add: assms(2) pre_expression_test t_seq_test_seq)
  hence 3: "?w \<le> Sum ?t"
    using assms(1-3) tsum_def while_completeness_sum by auto
  have 4: "p = --p"
    by (simp add: assms(1) test_expression_test)
  have "x\<guillemotleft>?w*aL = --(x\<guillemotleft>?w*aL)"
    using 1 by (simp add: assms(3) Pre_expression.conj_pre Pre_expression.pre_pre aL_pre_expression pre_expression_test)
  hence 5: "(-p\<squnion>(x\<guillemotleft>?w*aL))*p = (x\<guillemotleft>?w*aL)*p"
    using 4 by (metis tests_dual.sba_dual.inf_complement_intro)
  have "x\<guillemotleft>aL*?w\<lparr>x\<rparr>aL*?w"
    using 1 by (simp add: assms(4) Pre_expression.conj_pre aL_pre_expression)
  hence "x\<guillemotleft>?w*aL\<lparr>x\<rparr>aL*?w"
    using 1 by (metis aL_test pre_expression_test sub_comm)
  hence "(x\<guillemotleft>?w*aL)*p*?w\<lparr>x\<rparr>aL*?w"
    using 1 by (smt (z3) assms(1) Pre_expression.conj_pre Pre_expression.test_pre derived_hoare_triple.cons_trip derived_type pre_expression_test sub_assoc tests_dual.sba_dual.reflexive tests_dual.upper_bound_left)
  hence "(-p\<squnion>(x\<guillemotleft>?w*aL))*p*?w\<lparr>x\<rparr>aL*?w"
    using 5 by simp
  hence 6: "?t 0*p*?w\<lparr>x\<rparr>aL*?w"
    by (unfold tseq_def power_zero_id id_def)
  have "\<forall>n>0 . ?t n*p*?w\<lparr>x\<rparr>pSum ?t n*?w"
  proof (rule allI, rule impI)
    fix n
    assume "0<(n::nat)"
    from this obtain m where 7: "n = Suc m"
      by (auto dest: less_imp_Suc_add)
    hence "?t m*?w \<le> pSum ?t n*?w"
      using 1 2 by (smt pSum.simps(2) pSum_test pre_expression_test test_seq_def tests_dual.lower_bound_right tests_dual.sba_dual.inf_isotone tests_dual.sba_dual.reflexive)
    thus "?t n*p*?w\<lparr>x\<rparr>pSum ?t n*?w"
      using 1 7 by (smt assms conj_pre cons_trip tests_dual.upper_bound_left tests_dual.sba_dual.inf_complement_intro pSum_pre_expression power_succ_unfold_ext pre_closed pre_expression_test sub_assoc sub_comm t_seq_pre_expression test_pre tfun_def tseq_def)
  qed
  hence "?w\<lparr>p\<star>x\<rparr>-p*?w"
    using 1 2 3 6 assms while_trip by auto
  hence "?w\<lparr>p\<star>x\<rparr>-p*q"
    using 4 by (metis assms(2) while_pre_else pre_expression_test while_pre_else)
  thus ?thesis
    using assms(1,2) Pre_expression.neg_pre Pre_expression.test_pre cons_post_trip by blast
qed

lemma pre_completeness:
  "x \<in> While_program \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x\<guillemotleft>q\<lparr>x\<rparr>q"
  apply (induct arbitrary: q rule: While_program.induct)
  apply (simp add: derived_hoare_triple.atom_trip)
  apply (metis pre_pre pre_seq seq_trip pre_expression_test)
  apply (smt cond_prog cond_trip cons_pre_trip ite_pre_else ite_pre_then neg_pre pre_pre pre_expression_test test_pre)
  by (simp add: while_complete)

theorem completeness:
  "p\<langle>x\<rangle>q \<Longrightarrow> p\<lparr>x\<rparr>q"
  by (metis valid_hoare_triple_def pre_completeness tests_dual.reflexive pre_expression_test cons_trip)

end

class hoare_calculus_sound_complete = hoare_calculus_sound + hoare_calculus_complete
begin

text \<open>Theorem 41\<close>

theorem soundness_completeness:
  "p\<lparr>x\<rparr>q \<longleftrightarrow> p\<langle>x\<rangle>q"
  using completeness soundness by blast

end

class hoare_rules = whiledo + complete_tests + hoare_triple +
  assumes rule_pre:   "x\<guillemotleft>-q\<lbrace>x\<rbrace>-q"
  assumes rule_seq:   "-p\<lbrace>x\<rbrace>-q \<and> -q\<lbrace>y\<rbrace>-r \<longrightarrow> -p\<lbrace>x*y\<rbrace>-r"
  assumes rule_cond:  "-p*-q\<lbrace>x\<rbrace>-r \<and> --p*-q\<lbrace>y\<rbrace>-r \<longrightarrow> -q\<lbrace>x\<lhd>-p\<rhd>y\<rbrace>-r"
  assumes rule_while: "test_seq t \<and> -q \<le> Sum t \<and> t 0*-p*-q\<lbrace>x\<rbrace>aL*-q \<and> (\<forall>n>0 . t n*-p*-q\<lbrace>x\<rbrace>pSum t n*-q) \<longrightarrow> -q\<lbrace>-p\<star>x\<rbrace>--p*-q"
  assumes rule_cons:  "-p \<le> -q \<and> -q\<lbrace>x\<rbrace>-r \<and> -r \<le> -s \<longrightarrow> -p\<lbrace>x\<rbrace>-s"
  assumes rule_disj:  "-p\<lbrace>x\<rbrace>-r \<and> -q\<lbrace>x\<rbrace>-s \<longrightarrow> -p\<squnion>-q\<lbrace>x\<rbrace>-r\<squnion>-s"
begin

lemma rule_cons_pre:
  "-p \<le> -q \<Longrightarrow> -q\<lbrace>x\<rbrace>-r \<Longrightarrow> -p\<lbrace>x\<rbrace>-r"
  using rule_cons tests_dual.sba_dual.reflexive by blast

lemma rule_cons_pre_mult:
  "-q\<lbrace>x\<rbrace>-r \<Longrightarrow> -p*-q\<lbrace>x\<rbrace>-r"
  by (metis tests_dual.sub_sup_closed rule_cons_pre tests_dual.upper_bound_right)

lemma rule_cons_pre_plus:
  "-p\<squnion>-q\<lbrace>x\<rbrace>-r \<Longrightarrow> -p\<lbrace>x\<rbrace>-r"
  by (metis tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.upper_bound_left rule_cons_pre)

lemma rule_cons_post:
  "-q\<lbrace>x\<rbrace>-r \<Longrightarrow> -r \<le> -s \<Longrightarrow> -q\<lbrace>x\<rbrace>-s"
  using rule_cons tests_dual.sba_dual.reflexive by blast

lemma rule_cons_post_mult:
  "-q\<lbrace>x\<rbrace>-r*-s \<Longrightarrow> -q\<lbrace>x\<rbrace>-s"
  by (metis rule_cons_post tests_dual.upper_bound_left sub_comm sub_mult_closed)

lemma rule_cons_post_plus:
  "-q\<lbrace>x\<rbrace>-r \<Longrightarrow> -q\<lbrace>x\<rbrace>-r\<squnion>-s"
  by (metis tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.upper_bound_left rule_cons_post)

lemma rule_disj_pre:
 "-p\<lbrace>x\<rbrace>-r \<Longrightarrow> -q\<lbrace>x\<rbrace>-r \<Longrightarrow> -p\<squnion>-q\<lbrace>x\<rbrace>-r"
  by (metis rule_disj tests_dual.sba_dual.sup_idempotent)

end

class hoare_calculus_valid = hoare_calculus_sound_complete + hoare_triple +
  assumes hoare_triple_valid: "-p\<lbrace>x\<rbrace>-q \<longleftrightarrow> -p \<le> x\<guillemotleft>-q"
begin

lemma valid_hoare_triple_same:
  "p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> p\<lbrace>x\<rbrace>q = p\<langle>x\<rangle>q"
  by (metis valid_hoare_triple_def hoare_triple_valid pre_expression_test)

lemma derived_hoare_triple_same:
  "p \<in> Pre_expression \<Longrightarrow> q \<in> Pre_expression \<Longrightarrow> x \<in> While_program \<Longrightarrow> p\<lbrace>x\<rbrace>q = p\<lparr>x\<rparr>q"
  by (simp add: soundness_completeness valid_hoare_triple_same)

lemma valid_rule_disj:
  assumes "-p\<lbrace>x\<rbrace>-r"
      and "-q\<lbrace>x\<rbrace>-s"
    shows "-p\<squnion>-q\<lbrace>x\<rbrace>-r\<squnion>-s"
proof -
  have "x\<guillemotleft>-r \<le> x\<guillemotleft>-r\<squnion>-s \<and> x\<guillemotleft>-s \<le> x\<guillemotleft>-r\<squnion>-s"
    by (metis pre_iso tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.upper_bound_left tests_dual.sba_dual.upper_bound_right)
  thus ?thesis
    by (smt assms hoare_triple_valid tests_dual.greatest_lower_bound tests_dual.sba_dual.sub_sup_closed pre_closed tests_dual.transitive)
qed

subclass hoare_rules
  apply unfold_locales
  apply (metis hoare_triple_valid pre_closed tests_dual.sba_dual.reflexive)
  apply (meson hoare_triple_valid pre_compose)
  apply (smt hoare_triple_valid ite_import_mult sub_mult_closed)
  apply (smt (verit, del_insts) hoare_triple_valid aL_test pSum_test sba_dual.sub_sup_closed sub_mult_closed test_seq_def while_soundness_1)
  apply (smt hoare_triple_valid pre_iso tests_dual.transitive pre_closed)
  by (simp add: valid_rule_disj)

lemma nat_test_rule_while:
  "nat_test t s \<Longrightarrow> -q \<le> s \<Longrightarrow> (\<forall>n . t n*-p*-q\<lbrace>x\<rbrace>pSum t n*-q) \<Longrightarrow> -q\<lbrace>-p\<star>x\<rbrace>--p*-q"
  by (smt (verit, ccfv_threshold) hoare_triple_valid nat_test_def nat_test_pre pSum_test_nat sub_mult_closed)

lemma test_seq_rule_while:
  "test_seq t \<Longrightarrow> -q \<le> Sum t \<Longrightarrow> t 0*-p*-q\<lbrace>x\<rbrace>aL*-q \<Longrightarrow> (\<forall>n>0 . t n*-p*-q\<lbrace>x\<rbrace>pSum t n*-q) \<Longrightarrow> -q\<lbrace>-p\<star>x\<rbrace>--p*-q"
  by (smt (verit, del_insts) hoare_triple_valid aL_test pSum_test sub_mult_closed test_seq_def while_soundness_1)

lemma rule_bot:
  "bot\<lbrace>x\<rbrace>-p"
  by (metis hoare_triple_valid pre_closed tests_dual.top_double_complement tests_dual.top_greatest)

lemma rule_skip:
  "-p\<lbrace>1\<rbrace>-p"
  by (simp add: hoare_triple_valid pre_one_increasing)

lemma rule_example_4:
  assumes "test_seq t"
      and "Sum t = 1"
      and "t 0*-p1*-p3 = bot"
      and "-p1\<lbrace>z1\<rbrace>-p1*-p2"
      and "\<forall>n>0 . t n*-p1*-p2*-p3\<lbrace>z2\<rbrace>pSum t n*-p1*-p2"
    shows "-p1\<lbrace>z1*(-p3\<star>z2)\<rbrace>-p2*--p3"
proof -
  have "t 0*-p3*(-p1*-p2) = bot"
    by (smt (verit, ccfv_threshold) assms(1,3) sub_assoc sub_comm sub_mult_closed test_seq_def tests_dual.sup_right_zero)
  hence 1: "t 0*-p3*(-p1*-p2)\<lbrace>z2\<rbrace>aL*(-p1*-p2)"
    by (metis aL_test sub_mult_closed rule_bot)
  have "\<forall>n>0 . t n*-p3*(-p1*-p2)\<lbrace>z2\<rbrace>pSum t n*(-p1*-p2)"
    by (smt assms(1,5) lower_bound_left pSum_test rule_cons_pre sub_assoc sub_comm sub_mult_closed test_seq_def)
  hence "-p1*-p2\<lbrace>-p3\<star>z2\<rbrace>--p3*(-p1*-p2)"
    using 1 by (smt (verit, del_insts) assms(1,2) tests_dual.sub_bot_least rule_while sub_mult_closed)
  thus ?thesis
    by (smt assms(4) tests_dual.upper_bound_left rule_cons_post rule_seq sub_assoc sub_comm sub_mult_closed)
qed

end

class hoare_calculus_pc_2 = hoare_calculus_sound + hoare_calculus_pre_complete +
  assumes aL_one: "aL = 1"
begin

subclass hoare_calculus_sound_complete
  apply unfold_locales
  by (simp add: aL_one pre_below_one)

lemma while_soundness_pc:
  assumes "-p*-q \<le> x\<guillemotleft>-q"
  shows "-q \<le> -p\<star>x\<guillemotleft>--p*-q"
proof -
  let ?t = "\<lambda>x . 1"
  have 1: "test_seq ?t"
    by (simp add: test_seq_def)
  hence 2: "-q \<le> Sum ?t"
    by (metis Sum_test Sum_upper tests_dual.sba_dual.one_def tests_dual.antisymmetric tests_dual.sub_bot_least)
  have 3: "?t 0*-p*-q \<le> x\<guillemotleft>aL*-q"
    using 1 by (simp add: assms aL_one)
  have "\<forall>n>0 . ?t n*-p*-q \<le> x\<guillemotleft>pSum ?t n*-q"
    using 1 by (metis assms pSum_test pSum_upper tests_dual.sba_dual.one_def tests_dual.antisymmetric tests_dual.sub_bot_least tests_dual.sup_left_unit)
  thus ?thesis
    using 1 2 3 aL_one while_soundness_0 by auto
qed

end

class hoare_calculus_pc = hoare_calculus_sound + hoare_calculus_pre_complete +
  assumes pre_one_one: "x\<guillemotleft>1 = 1"
begin

subclass hoare_calculus_pc_2
  apply unfold_locales
  by (simp add: aL_def pre_one_one)

end

class hoare_calculus_pc_valid = hoare_calculus_pc + hoare_calculus_valid
begin

lemma rule_while_pc:
  "-p*-q\<lbrace>x\<rbrace>-q \<Longrightarrow> -q\<lbrace>-p\<star>x\<rbrace>--p*-q"
  by (metis hoare_triple_valid sub_mult_closed while_soundness_pc)

lemma rule_alternation:
  "-p\<lbrace>x\<rbrace>-q \<Longrightarrow> -q\<lbrace>y\<rbrace>-p \<Longrightarrow> -p\<lbrace>-r\<star>x*y\<rbrace>--r*-p"
  by (meson rule_cons_pre_mult rule_seq rule_while_pc)

lemma rule_alternation_context:
  "-p\<lbrace>v\<rbrace>-p \<Longrightarrow> -p\<lbrace>w\<rbrace>-q \<Longrightarrow> -q\<lbrace>x\<rbrace>-q \<Longrightarrow> -q\<lbrace>y\<rbrace>-p \<and> -p\<lbrace>z\<rbrace>-p \<Longrightarrow> -p\<lbrace>-r\<star>v*w*x*y*z\<rbrace>--r*-p"
  by (meson rule_cons_pre_mult rule_seq rule_while_pc)

lemma rule_example_3:
  assumes "-p*-q\<lbrace>x\<rbrace>--p*-q"
      and "--p*-r\<lbrace>x\<rbrace>-p*-r"
      and "-p*-r\<lbrace>y\<rbrace>-p*-q"
      and "--p*-q\<lbrace>z\<rbrace>--p*-r"
    shows "-p*-q\<squnion>--p*-r\<lbrace>-s\<star>x*(y\<lhd>-p\<rhd>z)\<rbrace>--s*(-p*-q\<squnion>--p*-r)"
proof -
  have t1: "-p*-q\<squnion>--p*-r\<lbrace>x\<rbrace>--p*-q\<squnion>-p*-r"
    by (smt assms(1,2) rule_disj sub_mult_closed)
  have "-p*-r\<lbrace>y\<rbrace>-p*-q\<squnion>--p*-r"
    by (smt assms(3) rule_cons_post_plus sub_mult_closed)
  hence t2: "-p*(--p*-q\<squnion>-p*-r)\<lbrace>y\<rbrace>-p*-q\<squnion>--p*-r"
    by (smt (z3) tests_dual.sba_dual.less_eq_inf tests_dual.sba_dual.reflexive tests_dual.sba_dual.sub_sup_closed tests_dual.sub_associative tests_dual.sub_sup_closed tests_dual.upper_bound_left tests_dual.wnf_lemma_3)
  have "--p*-q\<lbrace>z\<rbrace>-p*-q\<squnion>--p*-r"
    by (smt assms(4) tests_dual.inf_commutative rule_cons_post_plus sub_mult_closed)
  hence "--p*(--p*-q\<squnion>-p*-r)\<lbrace>z\<rbrace>-p*-q\<squnion>--p*-r"
    by (smt (z3) tests_dual.sba_dual.one_def tests_dual.sba_dual.sup_absorb tests_dual.sba_dual.sup_complement_intro tests_dual.sba_dual.sup_right_unit tests_dual.sub_sup_closed tests_dual.sup_complement_intro tests_dual.sup_left_dist_inf tests_dual.sup_right_unit tests_dual.top_double_complement)
  hence "--p*-q\<squnion>-p*-r\<lbrace>y\<lhd>-p\<rhd>z\<rbrace>-p*-q\<squnion>--p*-r"
    using t2 by (smt tests_dual.inf_closed rule_cond sub_mult_closed)
  hence "-s*(-p*-q\<squnion>--p*-r)\<lbrace>x*(y\<lhd>-p\<rhd>z)\<rbrace>-p*-q\<squnion>--p*-r"
    using t1 by (smt tests_dual.inf_closed rule_cons_pre_mult rule_seq sub_mult_closed)
  thus ?thesis
    by (smt tests_dual.inf_closed rule_while_pc sub_mult_closed)
qed

end

class hoare_calculus_tc = hoare_calculus + precondition_test_test + precondition_distr_mult +
  assumes while_bnd: "p \<in> Test_expression \<and> q \<in> Pre_expression \<and> x \<in> While_program \<longrightarrow> p\<star>x\<guillemotleft>q \<le> Sum (\<lambda>n . (p*x)^n\<guillemotleft>bot)"
begin

lemma
  assumes "p \<in> Test_expression"
      and "q \<in> Pre_expression"
      and "x \<in> While_program"
    shows "p\<star>x\<guillemotleft>q \<le> tsum (-p) x (p\<star>x\<guillemotleft>q) (-p\<squnion>(x\<guillemotleft>(p\<star>x\<guillemotleft>q)*aL))"
proof -
  let ?w = "p\<star>x\<guillemotleft>q"
  let ?s = "-p\<squnion>(x\<guillemotleft>?w*aL)"
  let ?t = "tseq (-p) x ?w ?s"
  let ?b = "\<lambda>n . (p*x)^n\<guillemotleft>bot"
  have 2: "test_seq ?t"
    by (simp add: assms(2) pre_expression_test t_seq_test_seq)
  have 3: "test_seq ?b"
    using pre_closed test_seq_def tests_dual.sba_dual.complement_top by blast
  have 4: "?w = --?w"
    by (metis assms(2) pre_expression_test pre_closed)
  have "?w \<le> Sum ?b"
    using assms while_bnd by blast
  hence 5: "?w = Sum ?b*?w"
    using 3 4 by (smt Sum_test leq_def sub_comm)
  have "\<forall>n . ?b n*?w \<le> ?t n"
  proof
    fix n
    show "?b n*?w \<le> ?t n"
    proof (induct n)
      show "?b 0*?w \<le> ?t 0"
        using 2 4 by (metis power.power_0 pre_one test_seq_def tests_dual.sup_left_zero tests_dual.top_double_complement tests_dual.top_greatest)
    next
      fix n
      assume 6: "?b n*?w \<le> ?t n"
      have "-p \<le> ?t (Suc n)"
        apply (unfold tseq_def power_succ_unfold_ext)
        by (smt assms(2) pre_expression_test t_seq_test pre_closed sub_mult_closed tfun_def tseq_def tests_dual.lower_bound_left)
      hence 7: "-p*?b (Suc n)*?w \<le> ?t (Suc n)"
        using 2 3 4 by (smt tests_dual.upper_bound_left sub_mult_closed test_seq_def tests_dual.transitive)
      have 8: "p*?b (Suc n)*?w \<le> x\<guillemotleft>?w*(?b n*?w)"
        by (smt assms(1,2) tests_dual.upper_bound_right tests_dual.sup_idempotent power_Suc pre_closed pre_distr_mult pre_expression_test pre_import_composition sub_assoc sub_comm sub_mult_closed test_expression_test while_pre_then tests_dual.top_double_complement)
      have 9: "... \<le> x\<guillemotleft>?w*?t n"
        using 2 3 4 6 by (smt tests_dual.sub_sup_right_isotone pre_iso sub_mult_closed test_seq_def)
      have "... \<le> ?t (Suc n)"
        using 2 4 by (smt power_succ_unfold_ext pre_closed sub_mult_closed test_seq_def tfun_def tseq_def tests_dual.lower_bound_right)
      hence "p*?b (Suc n)*?w \<le> ?t (Suc n)"
        using 2 3 4 8 9 by (smt assms(1) pre_closed sub_mult_closed test_expression_test test_seq_def tests_dual.transitive)
      thus "?b (Suc n)*?w \<le> ?t (Suc n)"
        using 2 3 4 7 by (smt assms(1) tests_dual.sup_less_eq_cases sub_assoc sub_mult_closed test_expression_test test_seq_def)
    qed
  qed
  hence "Sum ?b*?w \<le> tsum (-p) x ?w ?s"
    using 3 4 by (smt assms(2) Sum_upper mult_right_dist_Sum pre_expression_test sub_mult_closed t_seq_test t_sum_test test_seq_def tests_dual.transitive tsum_def)
  thus ?thesis
    using 5 by auto
qed

end

class complete_pre = complete_tests + precondition + power
begin

definition bnd :: "'a \<Rightarrow> 'a"
  where "bnd x \<equiv> Sup { x^n\<guillemotleft>bot | n::nat . True }"

lemma bnd_test_set:
  "test_set { x^n\<guillemotleft>bot | n::nat . True }"
  by (smt (verit, del_insts) CollectD pre_closed test_set_def tests_dual.top_double_complement)

lemma bnd_test:
  "bnd x = --bnd x"
  using bnd_def bnd_test_set sup_test by auto

lemma bnd_upper:
  "x^m\<guillemotleft>bot \<le> bnd x"
proof -
  have "x^m\<guillemotleft>bot \<in> { x^m\<guillemotleft>bot | m::nat . True }"
    by auto
  thus ?thesis
    using bnd_def bnd_test_set sup_upper by auto
qed

lemma bnd_least:
  assumes "\<forall>n . x^n\<guillemotleft>bot \<le> -p"
    shows "bnd x \<le> -p"
proof -
  have "\<forall>y\<in>{ x^n\<guillemotleft>bot | n::nat . True } . y \<le> -p"
    using assms by blast
  thus ?thesis
    using bnd_def bnd_test_set sup_least by auto
qed

lemma mult_right_dist_bnd:
  assumes "\<forall>n . (x^n\<guillemotleft>bot)*-p \<le> -q"
    shows "bnd x*-p \<le> -q"
proof -
  have "Sup { y*-p | y . y \<in> { x^n\<guillemotleft>bot | n::nat . True } } \<le> -q"
    by (smt assms mem_Collect_eq tests_dual.complement_bot pre_closed sub_mult_closed sup_least test_set_def)
  thus ?thesis
    using bnd_test_set bnd_def mult_right_dist_sup by simp
qed

lemma tests_complete:
  "nat_test (\<lambda>n . (-p*x)^n\<guillemotleft>bot) (bnd(-p*x))"
  using bnd_test bnd_upper mult_right_dist_bnd nat_test_def tests_dual.complement_bot pre_closed by blast

end

end

