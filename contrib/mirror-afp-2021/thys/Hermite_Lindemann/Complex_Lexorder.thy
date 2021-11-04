(*
  File:     Complex_Lexorder.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>The lexicographic ordering on complex numbers\<close>
theory Complex_Lexorder
  imports Complex_Main "HOL-Library.Multiset"
begin

text \<open>
  We define a lexicographic order on the complex numbers, comparing first the real parts
  and, if they are equal, the imaginary parts. This ordering is of course not compatible with
  multiplication, but it is compatible with addition.
\<close>

definition less_eq_complex_lex (infix "\<le>\<^sub>\<complex>" 50)  where
  "less_eq_complex_lex x y \<longleftrightarrow> Re x < Re y \<or> Re x = Re y \<and> Im x \<le> Im y"

definition less_complex_lex (infix "<\<^sub>\<complex>" 50) where
  "less_complex_lex x y \<longleftrightarrow> Re x < Re y \<or> Re x = Re y \<and> Im x < Im y"

interpretation complex_lex:
  linordered_ab_group_add "(+)" 0 "(-)" "uminus" less_eq_complex_lex less_complex_lex
  by standard (auto simp: less_eq_complex_lex_def less_complex_lex_def complex_eq_iff)

lemmas [trans] =
  complex_lex.order.trans complex_lex.less_le_trans
  complex_lex.less_trans complex_lex.le_less_trans

lemma (in ordered_comm_monoid_add) sum_mono_complex_lex:
  "(\<And>i. i\<in>K \<Longrightarrow> f i \<le>\<^sub>\<complex> g i) \<Longrightarrow> (\<Sum>i\<in>K. f i) \<le>\<^sub>\<complex> (\<Sum>i\<in>K. g i)"
  by (induct K rule: infinite_finite_induct) (use complex_lex.add_mono in auto)

lemma sum_strict_mono_ex1_complex_lex:
  fixes f g :: "'i \<Rightarrow> complex"
  assumes "finite A"
    and "\<forall>x\<in>A. f x \<le>\<^sub>\<complex> g x"
    and "\<exists>a\<in>A. f a <\<^sub>\<complex> g a"
  shows "sum f A <\<^sub>\<complex> sum g A"
proof-
  from assms(3) obtain a where a: "a \<in> A" "f a <\<^sub>\<complex> g a" by blast
  have "sum f A = sum f ((A - {a}) \<union> {a})"
    by (simp add: insert_absorb[OF \<open>a \<in> A\<close>])
  also have "\<dots> = sum f (A - {a}) + sum f {a}"
    using \<open>finite A\<close> by (subst sum.union_disjoint) auto
  also have "\<dots> \<le>\<^sub>\<complex> sum g (A - {a}) + sum f {a}"
    by (intro complex_lex.add_mono sum_mono_complex_lex) (simp_all add: assms)
  also have "\<dots> <\<^sub>\<complex> sum g (A - {a}) + sum g {a}"
    using a by (intro complex_lex.add_strict_left_mono) auto
  also have "\<dots> = sum g ((A - {a}) \<union> {a})"
    using \<open>finite A\<close> by (subst sum.union_disjoint[symmetric]) auto
  also have "\<dots> = sum g A" by (simp add: insert_absorb[OF \<open>a \<in> A\<close>])
  finally show ?thesis
    by simp
qed

lemma sum_list_mono_complex_lex:
  assumes "list_all2 (\<le>\<^sub>\<complex>) xs ys"
  shows   "sum_list xs \<le>\<^sub>\<complex> sum_list ys"
  using assms by induction (auto intro: complex_lex.add_mono)

lemma sum_mset_mono_complex_lex:
  assumes "rel_mset (\<le>\<^sub>\<complex>) A B"
  shows   "sum_mset A \<le>\<^sub>\<complex> sum_mset B"
  using assms by (auto simp: rel_mset_def sum_mset_sum_list intro: sum_list_mono_complex_lex)

lemma rel_msetI:
  assumes "list_all2 R xs ys" "mset xs = A" "mset ys = B"
  shows   "rel_mset R A B"
  using assms by (auto simp: rel_mset_def)

lemma mset_replicate [simp]: "mset (replicate n x) = replicate_mset n x"
  by (induction n) auto

lemma rel_mset_replicate_mset_right:
  assumes "\<And>x. x \<in># A \<Longrightarrow> R x y" "size A = n"
  shows   "rel_mset R A (replicate_mset n y)"
proof -
  obtain xs where [simp]: "A = mset xs"
    by (metis ex_mset)
  from assms have "\<forall>x\<in>set xs. R x y"
    by auto
  hence "list_all2 R xs (replicate (length xs) y)"
    by (induction xs) auto
  with assms(2) show ?thesis
    by (intro rel_msetI[of R xs "replicate n y"]) auto
qed

end