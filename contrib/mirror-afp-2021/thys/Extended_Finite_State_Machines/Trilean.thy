chapter\<open>Preliminaries\<close>
text\<open>In this chapter, we introduce the preliminaries, including a three-valued logic, variables,
arithmetic expressions and guard expressions.\<close>

section\<open>Three-Valued Logic\<close>

text\<open>Because our EFSMs are dynamically typed, we cannot rely on conventional Boolean logic when
evaluating expressions. For example, we may end up in the situation where we need to evaluate
the guard $r_1 > 5$. This is fine if $r_1$ holds a numeric value, but if $r_1$ evaluates to a
string, this causes problems. We cannot simply evaluate to \emph{false} because then the negation
would evaluate to \emph{true.} Instead, we need a three-valued logic such that we can meaningfully
evaluate nonsensical guards.

The \texttt{trilean} datatype is used to implement three-valued Bochvar logic
\cite{bochvar1981}. Here we prove that the logic is an idempotent semiring, define a partial order,
and prove some other useful lemmas.\<close>

theory Trilean
imports Main
begin

datatype trilean = true | false | invalid

instantiation trilean :: semiring begin
fun times_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" where
  "times_trilean _ invalid = invalid" |
  "times_trilean invalid _ = invalid" |
  "times_trilean true true = true" |
  "times_trilean _ false = false" |
  "times_trilean false _ = false"

fun plus_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" where
  "plus_trilean invalid _ = invalid" |
  "plus_trilean _ invalid = invalid" |
  "plus_trilean true _ = true" |
  "plus_trilean _ true = true" |
  "plus_trilean false false = false"

abbreviation maybe_and :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" (infixl "\<and>?" 70) where
  "maybe_and x y \<equiv> x * y"

abbreviation maybe_or :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" (infixl "\<or>?" 65) where
  "maybe_or x y \<equiv> x + y"

lemma plus_trilean_assoc:
  "a \<or>? b \<or>? c = a \<or>? (b \<or>? c)"
proof(induct a b  arbitrary: c rule: plus_trilean.induct)
case (1 uu)
  then show ?case
    by simp
next
  case "2_1"
  then show ?case
    by simp
next
  case "2_2"
  then show ?case
    by simp
next
  case "3_1"
  then show ?case
    by (metis plus_trilean.simps(2) plus_trilean.simps(4) trilean.exhaust)
next
  case "3_2"
  then show ?case
    by (metis plus_trilean.simps(3) plus_trilean.simps(5) plus_trilean.simps(6) plus_trilean.simps(7) trilean.exhaust)
next
  case 4
  then show ?case
    by (metis plus_trilean.simps(2) plus_trilean.simps(3) plus_trilean.simps(4) plus_trilean.simps(5) plus_trilean.simps(6) trilean.exhaust)
next
  case 5
  then show ?case
    by (metis plus_trilean.simps(6) plus_trilean.simps(7) trilean.exhaust)
qed

lemma plus_trilean_commutative: "a \<or>? b = b \<or>? a"
proof(induct a b rule: plus_trilean.induct)
  case (1 uu)
  then show ?case
    by (metis plus_trilean.simps(1) plus_trilean.simps(2) plus_trilean.simps(3) trilean.exhaust)
qed auto

lemma times_trilean_commutative: "a \<and>? b = b \<and>? a"
  by (metis (mono_tags) times_trilean.simps trilean.distinct(5) trilean.exhaust)

lemma times_trilean_assoc:
  "a \<and>? b \<and>? c = a \<and>? (b \<and>? c)"
proof(induct a b  arbitrary: c rule: plus_trilean.induct)
  case (1 uu)
  then show ?case
    by (metis (mono_tags, lifting) times_trilean.simps(1) times_trilean_commutative)
next
case "2_1"
  then show ?case
    by (metis (mono_tags, lifting) times_trilean.simps(1) times_trilean_commutative)
next
  case "2_2"
  then show ?case
    by (metis (mono_tags, lifting) times_trilean.simps(1) times_trilean_commutative)
next
  case "3_1"
  then show ?case
    by (metis times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) trilean.exhaust)
next
  case "3_2"
  then show ?case
    by (metis times_trilean.simps(1) times_trilean.simps(5) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
next
  case 4
  then show ?case
    by (metis times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) times_trilean.simps(7) trilean.exhaust)
next
case 5
  then show ?case
    by (metis (full_types) times_trilean.simps(1) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
qed

lemma trilean_distributivity_1:
  "(a \<or>? b) \<and>? c = a \<and>? c \<or>? b \<and>? c"
proof(induct a b rule: times_trilean.induct)
case (1 uu)
  then show ?case
    by (metis (mono_tags, lifting) plus_trilean.simps(1) plus_trilean_commutative times_trilean.simps(1) times_trilean_commutative)
next
  case "2_1"
  then show ?case
    by (metis (mono_tags, lifting) plus_trilean.simps(1) times_trilean.simps(1) times_trilean_commutative)
next
  case "2_2"
  then show ?case
    by (metis (mono_tags, lifting) plus_trilean.simps(1) times_trilean.simps(1) times_trilean_commutative)
next
  case 3
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(4) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) trilean.exhaust)
next
  case "4_1"
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(5) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
next
  case "4_2"
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
next
  case 5
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(6) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
qed

instance
  apply standard
      apply (simp add: plus_trilean_assoc)
     apply (simp add: plus_trilean_commutative)
    apply (simp add: times_trilean_assoc)
   apply (simp add: trilean_distributivity_1)
  using times_trilean_commutative trilean_distributivity_1 by auto
end

lemma maybe_or_idempotent: "a \<or>? a = a"
  by (cases a) auto

lemma maybe_and_idempotent: "a \<and>? a = a"
  by (cases a) auto

instantiation trilean :: ord begin
definition less_eq_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> bool" where
  "less_eq_trilean a b = (a + b = b)"

definition less_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> bool" where
  "less_trilean a b = (a \<le> b \<and> a \<noteq> b)"

declare less_trilean_def less_eq_trilean_def [simp]

instance
  by standard
end

instantiation trilean :: uminus begin
  fun maybe_not :: "trilean \<Rightarrow> trilean" ("\<not>? _" [60] 60) where
    "\<not>? true = false" |
    "\<not>? false = true" |
    "\<not>? invalid = invalid"

instance
  by standard
end

lemma maybe_and_one: "true \<and>? x = x"
  by (cases x, auto)

lemma maybe_or_zero: "false \<or>? x = x"
  by (cases x, auto)

lemma maybe_double_negation: "\<not>? \<not>? x = x"
  by (cases x, auto)

lemma maybe_negate_true: "(\<not>? x = true) = (x = false)"
  by (cases x, auto)

lemma maybe_negate_false: "(\<not>? x = false) = (x = true)"
  by (cases x, auto)

lemma maybe_and_true: "(x \<and>? y = true) = (x = true \<and> y = true)"
  using times_trilean.elims by blast

lemma maybe_and_not_true:
  "(x \<and>? y \<noteq> true) = (x \<noteq> true \<or> y \<noteq> true)"
  by (simp add: maybe_and_true)

lemma negate_valid: "(\<not>? x \<noteq> invalid) = (x \<noteq> invalid)"
  by (metis maybe_double_negation maybe_not.simps(3))

lemma maybe_and_valid:
  "x \<and>? y \<noteq> invalid \<Longrightarrow> x \<noteq> invalid \<and> y \<noteq> invalid"
  using times_trilean.elims by blast

lemma maybe_or_valid:
  "x \<or>? y \<noteq> invalid \<Longrightarrow> x \<noteq> invalid \<and> y \<noteq> invalid"
  using plus_trilean.elims by blast

lemma maybe_or_false:
  "(x \<or>? y = false) = (x = false \<and> y = false)"
  using plus_trilean.elims by blast

lemma maybe_or_true:
  "(x \<or>? y = true) = ((x = true \<or> y = true) \<and> x \<noteq> invalid \<and> y \<noteq> invalid)"
  using plus_trilean.elims by blast

lemma maybe_not_invalid: "(\<not>? x = invalid) = (x = invalid)"
  by (metis maybe_double_negation maybe_not.simps(3))

lemma maybe_or_invalid:
  "(x \<or>? y = invalid) = (x = invalid \<or> y = invalid)"
  using plus_trilean.elims by blast

lemma maybe_and_invalid:
  "(x \<and>? y = invalid) = (x = invalid \<or> y = invalid)"
  using times_trilean.elims by blast

lemma maybe_and_false:
  "(x \<and>? y = false) = ((x = false \<or> y = false) \<and> x \<noteq> invalid \<and> y \<noteq> invalid)"
  using times_trilean.elims by blast

lemma invalid_maybe_and: "invalid \<and>? x = invalid"
  using maybe_and_valid by blast

lemma maybe_not_eq: "(\<not>? x = \<not>? y) = (x = y)"
  by (metis maybe_double_negation)

lemma de_morgans_1:
  "\<not>? (a \<or>? b) = (\<not>?a) \<and>? (\<not>?b)"
  by (metis (no_types, hide_lams) add.commute invalid_maybe_and maybe_and_idempotent maybe_and_one maybe_not.elims maybe_not.simps(1) maybe_not.simps(3) maybe_not_invalid maybe_or_zero plus_trilean.simps(1) plus_trilean.simps(4) times_trilean.simps(1) times_trilean_commutative trilean.exhaust trilean.simps(6))

lemma de_morgans_2:
  "\<not>? (a \<and>? b) = (\<not>?a) \<or>? (\<not>?b)"
  by (metis de_morgans_1 maybe_double_negation)

lemma not_true: "(x \<noteq> true) = (x = false \<or> x = invalid)"
  by (metis (no_types, lifting) maybe_not.cases trilean.distinct(1) trilean.distinct(3))

lemma pull_negation: "(x = \<not>? y) = (\<not>? x = y)"
  using maybe_double_negation by auto

lemma comp_fun_commute_maybe_or: "comp_fun_commute maybe_or"
  apply standard
  apply (simp add: comp_def)
  apply (rule ext)
  by (simp add: add.left_commute)

lemma comp_fun_commute_maybe_and: "comp_fun_commute maybe_and"
  apply standard
  apply (simp add: comp_def)
  apply (rule ext)
  by (metis add.left_commute de_morgans_2 maybe_not_eq)

end
