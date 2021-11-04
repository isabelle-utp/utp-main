(*
(C) Copyright Andreas Viktor Hess, DTU, 2018-2020
(C) Copyright Sebastian A. Mödersheim, DTU, 2018-2020
(C) Copyright Achim D. Brucker, University of Sheffield, 2018-2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      Labeled_Strands.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, The University of Sheffield
*)

section \<open>Labeled Strands\<close>
theory Labeled_Strands
imports Strands_and_Constraints
begin

subsection \<open>Definitions: Labeled Strands and Constraints\<close>
datatype 'l strand_label =
  LabelN (the_LabelN: "'l") ("ln _")
| LabelS ("\<star>")

text \<open>Labeled strands are strands whose steps are equipped with labels\<close>
type_synonym ('a,'b,'c) labeled_strand_step = "'c strand_label \<times> ('a,'b) strand_step"
type_synonym ('a,'b,'c) labeled_strand = "('a,'b,'c) labeled_strand_step list"

abbreviation is_LabelN where "is_LabelN n x \<equiv> fst x = ln n"
abbreviation is_LabelS where "is_LabelS x \<equiv> fst x = \<star>"

definition unlabel where "unlabel S \<equiv> map snd S"
definition proj where "proj n S \<equiv> filter (\<lambda>s. is_LabelN n s \<or> is_LabelS s) S"
abbreviation proj_unl where "proj_unl n S \<equiv> unlabel (proj n S)"

abbreviation wfrestrictedvars\<^sub>l\<^sub>s\<^sub>t where "wfrestrictedvars\<^sub>l\<^sub>s\<^sub>t S \<equiv> wfrestrictedvars\<^sub>s\<^sub>t (unlabel S)"

abbreviation subst_apply_labeled_strand_step (infix "\<cdot>\<^sub>l\<^sub>s\<^sub>t\<^sub>p" 51) where
  "x \<cdot>\<^sub>l\<^sub>s\<^sub>t\<^sub>p \<theta> \<equiv> (case x of (l, s) \<Rightarrow> (l, s \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>))"

abbreviation subst_apply_labeled_strand (infix "\<cdot>\<^sub>l\<^sub>s\<^sub>t" 51) where
  "S \<cdot>\<^sub>l\<^sub>s\<^sub>t \<theta> \<equiv> map (\<lambda>x. x \<cdot>\<^sub>l\<^sub>s\<^sub>t\<^sub>p \<theta>) S"

abbreviation trms\<^sub>l\<^sub>s\<^sub>t where "trms\<^sub>l\<^sub>s\<^sub>t S \<equiv> trms\<^sub>s\<^sub>t (unlabel S)"
abbreviation trms_proj\<^sub>l\<^sub>s\<^sub>t where "trms_proj\<^sub>l\<^sub>s\<^sub>t n S \<equiv> trms\<^sub>s\<^sub>t (proj_unl n S)"

abbreviation vars\<^sub>l\<^sub>s\<^sub>t where "vars\<^sub>l\<^sub>s\<^sub>t S \<equiv> vars\<^sub>s\<^sub>t (unlabel S)"
abbreviation vars_proj\<^sub>l\<^sub>s\<^sub>t where "vars_proj\<^sub>l\<^sub>s\<^sub>t n S \<equiv> vars\<^sub>s\<^sub>t (proj_unl n S)"

abbreviation bvars\<^sub>l\<^sub>s\<^sub>t where "bvars\<^sub>l\<^sub>s\<^sub>t S \<equiv> bvars\<^sub>s\<^sub>t (unlabel S)"
abbreviation fv\<^sub>l\<^sub>s\<^sub>t where "fv\<^sub>l\<^sub>s\<^sub>t S \<equiv> fv\<^sub>s\<^sub>t (unlabel S)"

abbreviation wf\<^sub>l\<^sub>s\<^sub>t where "wf\<^sub>l\<^sub>s\<^sub>t V S \<equiv> wf\<^sub>s\<^sub>t V (unlabel S)"


subsection \<open>Lemmata: Projections\<close>
lemma is_LabelS_proj_iff_not_is_LabelN:
  "list_all is_LabelS (proj l A) \<longleftrightarrow> \<not>list_ex (is_LabelN l) A"
by (induct A) (auto simp add: proj_def)

lemma proj_subset_if_no_label:
  assumes "\<not>list_ex (is_LabelN l) A"
  shows "set (proj l A) \<subseteq> set (proj l' A)"
    and "set (proj_unl l A) \<subseteq> set (proj_unl l' A)"
using assms by (induct A) (auto simp add: unlabel_def proj_def)

lemma proj_in_setD:
  assumes a: "a \<in> set (proj l A)"
  obtains k b where "a = (k, b)" "k = (ln l) \<or> k = \<star>"
using that a unfolding proj_def by (cases a) auto

lemma proj_set_mono:
  assumes "set A \<subseteq> set B"
  shows "set (proj n A) \<subseteq> set (proj n B)"
    and "set (proj_unl n A) \<subseteq> set (proj_unl n B)"
using assms unfolding proj_def unlabel_def by auto

lemma unlabel_nil[simp]: "unlabel [] = []"
by (simp add: unlabel_def)

lemma unlabel_mono: "set A \<subseteq> set B \<Longrightarrow> set (unlabel A) \<subseteq> set (unlabel B)"
by (auto simp add: unlabel_def)

lemma unlabel_in: "(l,x) \<in> set A \<Longrightarrow> x \<in> set (unlabel A)"
unfolding unlabel_def by force

lemma unlabel_mem_has_label: "x \<in> set (unlabel A) \<Longrightarrow> \<exists>l. (l,x) \<in> set A"
unfolding unlabel_def by auto

lemma proj_nil[simp]: "proj n [] = []" "proj_unl n [] = []"
unfolding unlabel_def proj_def by auto

lemma singleton_lst_proj[simp]:
  "proj_unl l [(ln l, a)] = [a]"
  "l \<noteq> l' \<Longrightarrow> proj_unl l' [(ln l, a)] = []"
  "proj_unl l [(\<star>, a)] = [a]"
  "unlabel [(l'', a)] = [a]"
unfolding proj_def unlabel_def by simp_all

lemma unlabel_nil_only_if_nil[simp]: "unlabel A = [] \<Longrightarrow> A = []"
unfolding unlabel_def by auto

lemma unlabel_Cons[simp]:
  "unlabel ((l,a)#A) = a#unlabel A"
  "unlabel (b#A) = snd b#unlabel A"
unfolding unlabel_def by simp_all

lemma unlabel_append[simp]: "unlabel (A@B) = unlabel A@unlabel B"
unfolding unlabel_def by auto

lemma proj_Cons[simp]:
  "proj n ((ln n,a)#A) = (ln n,a)#proj n A"
  "proj n ((\<star>,a)#A) = (\<star>,a)#proj n A"
  "m \<noteq> n \<Longrightarrow> proj n ((ln m,a)#A) = proj n A"
  "l = (ln n) \<Longrightarrow> proj n ((l,a)#A) = (l,a)#proj n A"
  "l = \<star> \<Longrightarrow> proj n ((l,a)#A) = (l,a)#proj n A"
  "fst b \<noteq> \<star> \<Longrightarrow> fst b \<noteq> (ln n) \<Longrightarrow> proj n (b#A) = proj n A"
unfolding proj_def by auto

lemma proj_append[simp]:
  "proj l (A'@B') = proj l A'@proj l B'"
  "proj_unl l (A@B) = proj_unl l A@proj_unl l B"
unfolding proj_def unlabel_def by auto

lemma proj_unl_cons[simp]:
  "proj_unl l ((ln l, a)#A) = a#proj_unl l A"
  "l \<noteq> l' \<Longrightarrow> proj_unl l' ((ln l, a)#A) = proj_unl l' A"
  "proj_unl l ((\<star>, a)#A) = a#proj_unl l A"
unfolding proj_def unlabel_def by simp_all

lemma trms_unlabel_proj[simp]:
  "trms\<^sub>s\<^sub>t\<^sub>p (snd (ln l, x)) \<subseteq> trms_proj\<^sub>l\<^sub>s\<^sub>t l [(ln l, x)]"
by auto

lemma trms_unlabel_star[simp]:
  "trms\<^sub>s\<^sub>t\<^sub>p (snd (\<star>, x)) \<subseteq> trms_proj\<^sub>l\<^sub>s\<^sub>t l [(\<star>, x)]"
by auto

lemma trms\<^sub>l\<^sub>s\<^sub>t_union[simp]: "trms\<^sub>l\<^sub>s\<^sub>t A = (\<Union>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l A)"
proof (induction A)
  case (Cons a A)
  obtain l s where ls: "a = (l,s)" by moura
  have "trms\<^sub>l\<^sub>s\<^sub>t [a] = (\<Union>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l [a])"
  proof -
    have *: "trms\<^sub>l\<^sub>s\<^sub>t [a] = trms\<^sub>s\<^sub>t\<^sub>p s" using ls by simp
    show ?thesis
    proof (cases l)
      case (LabelN n)
      hence "trms_proj\<^sub>l\<^sub>s\<^sub>t n [a] = trms\<^sub>s\<^sub>t\<^sub>p s" using ls by simp
      moreover have "\<forall>m. n \<noteq> m \<longrightarrow> trms_proj\<^sub>l\<^sub>s\<^sub>t m [a] = {}" using ls LabelN by auto
      ultimately show ?thesis using * ls by fastforce
    next
      case LabelS
      hence "\<forall>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l [a] = trms\<^sub>s\<^sub>t\<^sub>p s" using ls by auto
      thus ?thesis using * ls by fastforce
    qed
  qed
  moreover have "\<forall>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l (a#A) = trms_proj\<^sub>l\<^sub>s\<^sub>t l [a] \<union> trms_proj\<^sub>l\<^sub>s\<^sub>t l A"
    unfolding unlabel_def proj_def by auto
  hence "(\<Union>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l (a#A)) = (\<Union>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l [a]) \<union> (\<Union>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l A)" by auto
  ultimately show ?case using Cons.IH ls by auto
qed simp

lemma trms\<^sub>l\<^sub>s\<^sub>t_append[simp]: "trms\<^sub>l\<^sub>s\<^sub>t (A@B) = trms\<^sub>l\<^sub>s\<^sub>t A \<union> trms\<^sub>l\<^sub>s\<^sub>t B"
by (metis trms\<^sub>s\<^sub>t_append unlabel_append)

lemma trms_proj\<^sub>l\<^sub>s\<^sub>t_append[simp]: "trms_proj\<^sub>l\<^sub>s\<^sub>t l (A@B) = trms_proj\<^sub>l\<^sub>s\<^sub>t l A \<union> trms_proj\<^sub>l\<^sub>s\<^sub>t l B"
by (metis (no_types, lifting) filter_append proj_def trms\<^sub>l\<^sub>s\<^sub>t_append)

lemma trms_proj\<^sub>l\<^sub>s\<^sub>t_subset[simp]:
  "trms_proj\<^sub>l\<^sub>s\<^sub>t l A \<subseteq> trms_proj\<^sub>l\<^sub>s\<^sub>t l (A@B)"
  "trms_proj\<^sub>l\<^sub>s\<^sub>t l B \<subseteq> trms_proj\<^sub>l\<^sub>s\<^sub>t l (A@B)"
using trms_proj\<^sub>l\<^sub>s\<^sub>t_append[of l] by blast+

lemma trms\<^sub>l\<^sub>s\<^sub>t_subset[simp]:
  "trms\<^sub>l\<^sub>s\<^sub>t A \<subseteq> trms\<^sub>l\<^sub>s\<^sub>t (A@B)"
  "trms\<^sub>l\<^sub>s\<^sub>t B \<subseteq> trms\<^sub>l\<^sub>s\<^sub>t (A@B)"
proof (induction A)
  case (Cons a A)
  obtain l s where *: "a = (l,s)" by moura
  { case 1 thus ?case using Cons * by auto }
  { case 2 thus ?case using Cons * by auto }
qed simp_all

lemma vars\<^sub>l\<^sub>s\<^sub>t_union: "vars\<^sub>l\<^sub>s\<^sub>t A = (\<Union>l. vars_proj\<^sub>l\<^sub>s\<^sub>t l A)"
proof (induction A)
  case (Cons a A)
  obtain l s where ls: "a = (l,s)" by moura
  have "vars\<^sub>l\<^sub>s\<^sub>t [a] = (\<Union>l. vars_proj\<^sub>l\<^sub>s\<^sub>t l [a])"
  proof -
    have *: "vars\<^sub>l\<^sub>s\<^sub>t [a] = vars\<^sub>s\<^sub>t\<^sub>p s" using ls by auto
    show ?thesis
    proof (cases l)
      case (LabelN n)
      hence "vars_proj\<^sub>l\<^sub>s\<^sub>t n [a] = vars\<^sub>s\<^sub>t\<^sub>p s" using ls by simp
      moreover have "\<forall>m. n \<noteq> m \<longrightarrow> vars_proj\<^sub>l\<^sub>s\<^sub>t m [a] = {}" using ls LabelN by auto
      ultimately show ?thesis using * ls by fast
    next
      case LabelS
      hence "\<forall>l. vars_proj\<^sub>l\<^sub>s\<^sub>t l [a] = vars\<^sub>s\<^sub>t\<^sub>p s" using ls by auto
      thus ?thesis using * ls by fast
    qed
  qed
  moreover have "\<forall>l. vars_proj\<^sub>l\<^sub>s\<^sub>t l (a#A) = vars_proj\<^sub>l\<^sub>s\<^sub>t l [a] \<union> vars_proj\<^sub>l\<^sub>s\<^sub>t l A"
    unfolding unlabel_def proj_def by auto
  hence "(\<Union>l. vars_proj\<^sub>l\<^sub>s\<^sub>t l (a#A)) = (\<Union>l. vars_proj\<^sub>l\<^sub>s\<^sub>t l [a]) \<union> (\<Union>l. vars_proj\<^sub>l\<^sub>s\<^sub>t l A)"
    using strand_vars_split(1) by auto
  ultimately show ?case using Cons.IH ls strand_vars_split(1) by auto
qed simp

lemma unlabel_Cons_inv:
  "unlabel A = b#B \<Longrightarrow> \<exists>A'. (\<exists>n. A = (ln n, b)#A') \<or> A = (\<star>, b)#A'"
proof -
  assume *: "unlabel A = b#B"
  then obtain l A' where "A = (l,b)#A'" unfolding unlabel_def by moura
  thus "\<exists>A'. (\<exists>l. A = (ln l, b)#A') \<or> A = (\<star>, b)#A'" by (metis strand_label.exhaust)
qed

lemma unlabel_snoc_inv:
  "unlabel A = B@[b] \<Longrightarrow> \<exists>A'. (\<exists>n. A = A'@[(ln n, b)]) \<or> A = A'@[(\<star>, b)]"
proof -
  assume *: "unlabel A = B@[b]"
  then obtain A' l where "A = A'@[(l,b)]"
    unfolding unlabel_def by (induct A rule: List.rev_induct) auto
  thus "\<exists>A'. (\<exists>n. A = A'@[(ln n, b)]) \<or> A = A'@[(\<star>, b)]" by (cases l) auto
qed

lemma proj_idem[simp]: "proj l (proj l A) = proj l A"
unfolding proj_def by auto

lemma proj_ik\<^sub>s\<^sub>t_is_proj_rcv_set:
  "ik\<^sub>s\<^sub>t (proj_unl n A) = {t. (ln n, Receive t) \<in> set A \<or> (\<star>, Receive t) \<in> set A} "
using ik\<^sub>s\<^sub>t_is_rcv_set unfolding unlabel_def proj_def by force

lemma unlabel_ik\<^sub>s\<^sub>t_is_rcv_set:
  "ik\<^sub>s\<^sub>t (unlabel A) = {t | l t. (l, Receive t) \<in> set A}"
using ik\<^sub>s\<^sub>t_is_rcv_set unfolding unlabel_def by force

lemma proj_ik_union_is_unlabel_ik:
  "ik\<^sub>s\<^sub>t (unlabel A) = (\<Union>l. ik\<^sub>s\<^sub>t (proj_unl l A))"
proof
  show "(\<Union>l. ik\<^sub>s\<^sub>t (proj_unl l A)) \<subseteq> ik\<^sub>s\<^sub>t (unlabel A)"
    using unlabel_ik\<^sub>s\<^sub>t_is_rcv_set[of A] proj_ik\<^sub>s\<^sub>t_is_proj_rcv_set[of _ A] by auto

  show "ik\<^sub>s\<^sub>t (unlabel A) \<subseteq> (\<Union>l. ik\<^sub>s\<^sub>t (proj_unl l A))"
  proof
    fix t assume "t \<in> ik\<^sub>s\<^sub>t (unlabel A)"
    then obtain l where "(l, Receive t) \<in> set A"
      using ik\<^sub>s\<^sub>t_is_rcv_set unlabel_mem_has_label[of _ A]
      by moura
    thus "t \<in> (\<Union>l. ik\<^sub>s\<^sub>t (proj_unl l A))" using proj_ik\<^sub>s\<^sub>t_is_proj_rcv_set[of _ A] by (cases l) auto
  qed
qed

lemma proj_ik_append[simp]:
  "ik\<^sub>s\<^sub>t (proj_unl l (A@B)) = ik\<^sub>s\<^sub>t (proj_unl l A) \<union> ik\<^sub>s\<^sub>t (proj_unl l B)"
using proj_append(2)[of l A B] ik_append by auto

lemma proj_ik_append_subst_all:
  "ik\<^sub>s\<^sub>t (proj_unl l (A@B)) \<cdot>\<^sub>s\<^sub>e\<^sub>t I = (ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<union> (ik\<^sub>s\<^sub>t (proj_unl l B) \<cdot>\<^sub>s\<^sub>e\<^sub>t I)"
using proj_ik_append[of l] by auto

lemma ik_proj_subset[simp]: "ik\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> trms_proj\<^sub>l\<^sub>s\<^sub>t n A"
by auto

lemma prefix_proj:
  "prefix A B \<Longrightarrow> prefix (unlabel A) (unlabel B)"
  "prefix A B \<Longrightarrow> prefix (proj n A) (proj n B)"
  "prefix A B \<Longrightarrow> prefix (proj_unl n A) (proj_unl n B)"
unfolding prefix_def unlabel_def proj_def by auto


subsection \<open>Lemmata: Well-formedness\<close>
lemma wfvarsoccs\<^sub>s\<^sub>t_proj_union:
  "wfvarsoccs\<^sub>s\<^sub>t (unlabel A) = (\<Union>l. wfvarsoccs\<^sub>s\<^sub>t (proj_unl l A))"
proof (induction A)
  case (Cons a A)
  obtain l s where ls: "a = (l,s)" by moura
  have "wfvarsoccs\<^sub>s\<^sub>t (unlabel [a]) = (\<Union>l. wfvarsoccs\<^sub>s\<^sub>t (proj_unl l [a]))"
  proof -
    have *: "wfvarsoccs\<^sub>s\<^sub>t (unlabel [a]) = wfvarsoccs\<^sub>s\<^sub>t\<^sub>p s" using ls by auto
    show ?thesis
    proof (cases l)
      case (LabelN n)
      hence "wfvarsoccs\<^sub>s\<^sub>t (proj_unl n [a]) = wfvarsoccs\<^sub>s\<^sub>t\<^sub>p s" using ls by simp
      moreover have "\<forall>m. n \<noteq> m \<longrightarrow> wfvarsoccs\<^sub>s\<^sub>t (proj_unl m [a]) = {}" using ls LabelN by auto
      ultimately show ?thesis using * ls by fast
    next
      case LabelS
      hence "\<forall>l. wfvarsoccs\<^sub>s\<^sub>t (proj_unl l [a]) = wfvarsoccs\<^sub>s\<^sub>t\<^sub>p s" using ls by auto
      thus ?thesis using * ls by fast
    qed
  qed
  moreover have
      "wfvarsoccs\<^sub>s\<^sub>t (proj_unl l (a#A)) =
       wfvarsoccs\<^sub>s\<^sub>t (proj_unl l [a]) \<union> wfvarsoccs\<^sub>s\<^sub>t (proj_unl l A)"
    for l
    unfolding unlabel_def proj_def by auto
  hence "(\<Union>l. wfvarsoccs\<^sub>s\<^sub>t (proj_unl l (a#A))) =
         (\<Union>l. wfvarsoccs\<^sub>s\<^sub>t (proj_unl l [a])) \<union> (\<Union>l. wfvarsoccs\<^sub>s\<^sub>t (proj_unl l A))"
    using strand_vars_split(1) by auto
  ultimately show ?case using Cons.IH ls strand_vars_split(1) by auto
qed simp

lemma wf_if_wf_proj:
  assumes "\<forall>l. wf\<^sub>s\<^sub>t V (proj_unl l A)"
  shows "wf\<^sub>s\<^sub>t V (unlabel A)"
using assms
proof (induction A arbitrary: V rule: List.rev_induct)
  case (snoc a A)
  hence IH: "wf\<^sub>s\<^sub>t V (unlabel A)" using proj_append(2)[of _ A] by auto
  obtain b l where b: "a = (ln l, b) \<or> a = (\<star>, b)" by (cases a, metis strand_label.exhaust)
  hence *: "wf\<^sub>s\<^sub>t V (proj_unl l A@[b])"
    by (metis snoc.prems proj_append(2) singleton_lst_proj(1) proj_unl_cons(1,3))
  thus ?case using IH b snoc.prems proj_append(2)[of l A "[a]"] unlabel_append[of A "[a]"]
  proof (cases b)
    case (Receive t)
    have "fv t \<subseteq> wfvarsoccs\<^sub>s\<^sub>t (unlabel A) \<union> V"
    proof
      fix x assume "x \<in> fv t"
      hence "x \<in> V \<union> wfvarsoccs\<^sub>s\<^sub>t (proj_unl l A)" using wf_append_exec[OF *] b Receive by auto
      thus "x \<in> wfvarsoccs\<^sub>s\<^sub>t (unlabel A) \<union> V" using wfvarsoccs\<^sub>s\<^sub>t_proj_union[of A] by auto
    qed
    hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (unlabel A) \<union> V"
      using vars_snd_rcv_strand_subset2(4)[of "unlabel A"] by blast
    hence "wf\<^sub>s\<^sub>t V (unlabel A@[Receive t])" by (rule wf_rcv_append'''[OF IH])
    thus ?thesis using b Receive unlabel_append[of A "[a]"] by auto
  next
    case (Equality ac s t)
    have "fv t \<subseteq> wfvarsoccs\<^sub>s\<^sub>t (unlabel A) \<union> V" when "ac = Assign"
    proof
      fix x assume "x \<in> fv t"
      hence "x \<in> V \<union> wfvarsoccs\<^sub>s\<^sub>t (proj_unl l A)" using wf_append_exec[OF *] b Equality that by auto
      thus "x \<in> wfvarsoccs\<^sub>s\<^sub>t (unlabel A) \<union> V" using wfvarsoccs\<^sub>s\<^sub>t_proj_union[of A] by auto
    qed
    hence "fv t \<subseteq> wfrestrictedvars\<^sub>l\<^sub>s\<^sub>t A \<union> V" when "ac = Assign"
      using vars_snd_rcv_strand_subset2(4)[of "unlabel A"] that by blast
    hence "wf\<^sub>s\<^sub>t V (unlabel A@[Equality ac s t])"
      by (cases ac) (metis wf_eq_append'''[OF IH], metis wf_eq_check_append''[OF IH])
    thus ?thesis using b Equality unlabel_append[of A "[a]"] by auto
  qed auto
qed simp

end
