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

(*  Title:      Parallel_Compositionality.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, The University of Sheffield
*)

section \<open>Parallel Compositionality of Security Protocols\<close>
text \<open>\label{sec:Parallel-Compositionality}\<close>
theory Parallel_Compositionality
imports Typing_Result Labeled_Strands
begin


subsection \<open>Definitions: Labeled Typed Model Locale\<close>
locale labeled_typed_model = typed_model arity public Ana \<Gamma>
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,'var) term \<Rightarrow> (('fun,'var) term list \<times> ('fun,'var) term list)"
    and \<Gamma>::"('fun,'var) term \<Rightarrow> ('fun,'atom::finite) term_type"
  +
  fixes label_witness1 and label_witness2::"'lbl"
  assumes at_least_2_labels: "label_witness1 \<noteq> label_witness2"
begin

text \<open>The Ground Sub-Message Patterns (GSMP)\<close>
definition GSMP::"('fun,'var) terms \<Rightarrow> ('fun,'var) terms" where
  "GSMP P \<equiv> {t \<in> SMP P. fv t = {}}"

definition typing_cond where
  "typing_cond \<A> \<equiv>
    wf\<^sub>s\<^sub>t {} \<A> \<and>
    fv\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>s\<^sub>t \<A> = {} \<and>
    tfr\<^sub>s\<^sub>t \<A> \<and>
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t \<A>) \<and>
    Ana_invar_subst (ik\<^sub>s\<^sub>t \<A> \<union> assignment_rhs\<^sub>s\<^sub>t \<A>)"


subsection \<open>Definitions: GSMP Disjointedness and Parallel Composability\<close>
definition GSMP_disjoint where
  "GSMP_disjoint P1 P2 Secrets \<equiv> GSMP P1 \<inter> GSMP P2 \<subseteq> Secrets \<union> {m. {} \<turnstile>\<^sub>c m}"

definition declassified\<^sub>l\<^sub>s\<^sub>t where
  "declassified\<^sub>l\<^sub>s\<^sub>t (\<A>::('fun,'var,'lbl) labeled_strand) \<I> \<equiv> {t. (\<star>, Receive t) \<in> set \<A>} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"

definition par_comp where
  "par_comp (\<A>::('fun,'var,'lbl) labeled_strand) (Secrets::('fun,'var) terms) \<equiv> 
    (\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Secrets) \<and>
    (\<forall>s \<in> Secrets. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Secrets) \<and>
    ground Secrets"

definition strand_leaks\<^sub>l\<^sub>s\<^sub>t where
  "strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A> Sec \<I> \<equiv> (\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A> \<I>. \<exists>l. (\<I> \<Turnstile> \<langle>proj_unl l \<A>@[Send t]\<rangle>))"

subsection \<open>Definitions: Homogeneous and Numbered Intruder Deduction Variants\<close>

definition proj_specific where
  "proj_specific n t \<A> Secrets \<equiv> t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>) - (Secrets \<union> {m. {} \<turnstile>\<^sub>c m})"

definition heterogeneous\<^sub>l\<^sub>s\<^sub>t where
  "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Secrets \<equiv> (
    (\<exists>l1 l2. \<exists>s1 \<in> subterms t. \<exists>s2 \<in> subterms t.
      l1 \<noteq> l2 \<and> proj_specific l1 s1 \<A> Secrets \<and> proj_specific l2 s2 \<A> Secrets))"

abbreviation homogeneous\<^sub>l\<^sub>s\<^sub>t where
  "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Secrets \<equiv> \<not>heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Secrets"

definition intruder_deduct_hom::
  "('fun,'var) terms \<Rightarrow> ('fun,'var,'lbl) labeled_strand \<Rightarrow> ('fun,'var) terms \<Rightarrow> ('fun,'var) term
  \<Rightarrow> bool" ("\<langle>_;_;_\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m _" 50)
where
  "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t \<equiv> \<langle>M; \<lambda>t. homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec \<and> t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)\<rangle> \<turnstile>\<^sub>r t"

lemma intruder_deduct_hom_AxiomH[simp]:
  assumes "t \<in> M"
  shows "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t"
using intruder_deduct_restricted.AxiomR[of t M] assms
unfolding intruder_deduct_hom_def
by blast

lemma intruder_deduct_hom_ComposeH[simp]:
  assumes "length X = arity f" "public f" "\<And>x. x \<in> set X \<Longrightarrow> \<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m x"
  and "homogeneous\<^sub>l\<^sub>s\<^sub>t (Fun f X) \<A> Sec" "Fun f X \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  shows "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m Fun f X"
proof -
  let ?Q = "\<lambda>t. homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec \<and> t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  show ?thesis
    using intruder_deduct_restricted.ComposeR[of X f M ?Q] assms
    unfolding intruder_deduct_hom_def
    by blast
qed

lemma intruder_deduct_hom_DecomposeH:
  assumes "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t" "Ana t = (K, T)" "\<And>k. k \<in> set K \<Longrightarrow> \<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m k" "t\<^sub>i \<in> set T"
  shows "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t\<^sub>i"
proof -
  let ?Q = "\<lambda>t. homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec \<and> t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  show ?thesis
    using intruder_deduct_restricted.DecomposeR[of M ?Q t] assms
    unfolding intruder_deduct_hom_def
    by blast
qed

lemma intruder_deduct_hom_induct[consumes 1, case_names AxiomH ComposeH DecomposeH]:
  assumes "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t" "\<And>t. t \<in> M \<Longrightarrow> P M t"
          "\<And>X f. \<lbrakk>length X = arity f; public f;
                  \<And>x. x \<in> set X \<Longrightarrow> \<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m x;
                  \<And>x. x \<in> set X \<Longrightarrow> P M x;
                  homogeneous\<^sub>l\<^sub>s\<^sub>t (Fun f X) \<A> Sec;
                  Fun f X \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)
                  \<rbrakk> \<Longrightarrow> P M (Fun f X)"
          "\<And>t K T t\<^sub>i. \<lbrakk>\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t; P M t; Ana t = (K, T);
                       \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m k;
                       \<And>k. k \<in> set K \<Longrightarrow> P M k; t\<^sub>i \<in> set T\<rbrakk> \<Longrightarrow> P M t\<^sub>i"
        shows "P M t"
proof -
  let ?Q = "\<lambda>t. homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec \<and> t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  show ?thesis
    using intruder_deduct_restricted_induct[of M ?Q t "\<lambda>M Q t. P M t"] assms
    unfolding intruder_deduct_hom_def
    by blast
qed

lemma ideduct_hom_mono:
  "\<lbrakk>\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t; M \<subseteq> M'\<rbrakk> \<Longrightarrow> \<langle>M'; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t"
using ideduct_restricted_mono[of M _ t M']
unfolding intruder_deduct_hom_def
by fast

subsection \<open>Lemmata: GSMP\<close>
lemma GSMP_disjoint_empty[simp]:
  "GSMP_disjoint {} A Sec" "GSMP_disjoint A {} Sec"
unfolding GSMP_disjoint_def GSMP_def by fastforce+

lemma GSMP_mono:
  assumes "N \<subseteq> M"
  shows "GSMP N \<subseteq> GSMP M"
using SMP_mono[OF assms] unfolding GSMP_def by fast

lemma GSMP_SMP_mono:
  assumes "SMP N \<subseteq> SMP M"
  shows "GSMP N \<subseteq> GSMP M"
using assms unfolding GSMP_def by fast

lemma GSMP_subterm:
  assumes "t \<in> GSMP M" "t' \<sqsubseteq> t"
  shows "t' \<in> GSMP M"
using SMP.Subterm[of t M t'] ground_subterm[of t t'] assms unfolding GSMP_def by auto

lemma GSMP_subterms: "subterms\<^sub>s\<^sub>e\<^sub>t (GSMP M) = GSMP M"
using GSMP_subterm[of _ M] by blast

lemma GSMP_Ana_key:
  assumes "t \<in> GSMP M" "Ana t = (K,T)" "k \<in> set K"
  shows "k \<in> GSMP M"
using SMP.Ana[of t M K T k] Ana_keys_fv[of t K T] assms unfolding GSMP_def by auto

lemma GSMP_append[simp]: "GSMP (trms\<^sub>l\<^sub>s\<^sub>t (A@B)) = GSMP (trms\<^sub>l\<^sub>s\<^sub>t A) \<union> GSMP (trms\<^sub>l\<^sub>s\<^sub>t B)"
using SMP_union[of "trms\<^sub>l\<^sub>s\<^sub>t A" "trms\<^sub>l\<^sub>s\<^sub>t B"] trms\<^sub>l\<^sub>s\<^sub>t_append[of A B] unfolding GSMP_def by auto

lemma GSMP_union: "GSMP (A \<union> B) = GSMP A \<union> GSMP B"
using SMP_union[of A B] unfolding GSMP_def by auto

lemma GSMP_Union: "GSMP (trms\<^sub>l\<^sub>s\<^sub>t A) = (\<Union>l. GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l A))"
proof -
  define P where "P \<equiv> (\<lambda>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l A)"
  define Q where "Q \<equiv> trms\<^sub>l\<^sub>s\<^sub>t A"
  have "SMP (\<Union>l. P l) = (\<Union>l. SMP (P l))" "Q = (\<Union>l. P l)"
    unfolding P_def Q_def by (metis SMP_Union, metis trms\<^sub>l\<^sub>s\<^sub>t_union)
  hence "GSMP Q = (\<Union>l. GSMP (P l))" unfolding GSMP_def by auto
  thus ?thesis unfolding P_def Q_def by metis
qed

lemma in_GSMP_in_proj: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A) \<Longrightarrow> \<exists>n. t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)"
using GSMP_Union[of A] by blast

lemma in_proj_in_GSMP: "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) \<Longrightarrow> t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
using GSMP_Union[of A] by blast

lemma GSMP_disjointE:
  assumes A: "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) (trms_proj\<^sub>l\<^sub>s\<^sub>t m A) Sec"
  shows "GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t m A) \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
using assms unfolding GSMP_disjoint_def by auto

lemma GSMP_disjoint_term:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  shows "t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<or> t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) \<or> t \<in> Sec \<or> {} \<turnstile>\<^sub>c t"
using assms unfolding GSMP_disjoint_def by blast

lemma GSMP_wt_subst_subset:
  assumes "t \<in> GSMP (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
  shows "t \<in> GSMP M"
using SMP_wt_subst_subset[OF _ assms(2,3), of t M] assms(1) unfolding GSMP_def by simp

lemma GSMP_wt_substI:
  assumes "t \<in> M" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "t \<cdot> I \<in> GSMP M"
proof -
  have "t \<in> SMP M" using assms(1) by auto
  hence *: "t \<cdot> I \<in> SMP M" using SMP.Substitution assms(2,3) wf_trm_subst_range_iff[of I] by simp
  moreover have "fv (t \<cdot> I) = {}"
    using assms(1) interpretation_grounds_all'[OF assms(4)]
    by auto
  ultimately show ?thesis unfolding GSMP_def by simp
qed

lemma GSMP_disjoint_subset:
  assumes "GSMP_disjoint L R S" "L' \<subseteq> L" "R' \<subseteq> R"
  shows "GSMP_disjoint L' R' S"
using assms(1) SMP_mono[OF assms(2)] SMP_mono[OF assms(3)]
by (auto simp add: GSMP_def GSMP_disjoint_def)

lemma GSMP_disjoint_fst_specific_not_snd_specific:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec" "l \<noteq> l'"
  and "proj_specific l m \<A> Sec"
  shows "\<not>proj_specific l' m \<A> Sec"
using assms by (fastforce simp add: GSMP_disjoint_def proj_specific_def)

lemma GSMP_disjoint_snd_specific_not_fst_specific:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and "proj_specific l' m \<A> Sec"
  shows "\<not>proj_specific l m \<A> Sec"
using assms by (auto simp add: GSMP_disjoint_def proj_specific_def)

lemma GSMP_disjoint_intersection_not_specific:
  assumes "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and "t \<in> Sec \<or> {} \<turnstile>\<^sub>c t"
  shows "\<not>proj_specific l t \<A> Sec" "\<not>proj_specific l t \<A> Sec"
using assms by (auto simp add: GSMP_disjoint_def proj_specific_def)

subsection \<open>Lemmata: Intruder Knowledge and Declassification\<close>
lemma ik_proj_subst_GSMP_subset:
  assumes I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)"
proof
  fix t assume "t \<in> ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
  hence *: "t \<in> trms_proj\<^sub>l\<^sub>s\<^sub>t n A \<cdot>\<^sub>s\<^sub>e\<^sub>t I" by auto
  then obtain s where "s \<in> trms_proj\<^sub>l\<^sub>s\<^sub>t n A" "t = s \<cdot> I" by auto
  hence "t \<in> SMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)" using SMP_I I(1,2) wf_trm_subst_range_iff[of I] by simp
  moreover have "fv t = {}"
    using * interpretation_grounds_all'[OF I(3)]
    by auto
  ultimately show "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)" unfolding GSMP_def by simp
qed

lemma declassified_proj_ik_subset: "declassified\<^sub>l\<^sub>s\<^sub>t A I \<subseteq> ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
proof (induction A)
  case (Cons a A) thus ?case
    using proj_ik_append[of n "[a]" A] by (auto simp add: declassified\<^sub>l\<^sub>s\<^sub>t_def)
qed (simp add: declassified\<^sub>l\<^sub>s\<^sub>t_def)

lemma declassified_proj_GSMP_subset:
  assumes I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "declassified\<^sub>l\<^sub>s\<^sub>t A I \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)"
by (rule subset_trans[OF declassified_proj_ik_subset ik_proj_subst_GSMP_subset[OF I]])

lemma declassified_subterms_proj_GSMP_subset:
  assumes I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (declassified\<^sub>l\<^sub>s\<^sub>t A I) \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)"
proof
  fix t assume t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (declassified\<^sub>l\<^sub>s\<^sub>t A I)"
  then obtain t' where t': "t' \<in> declassified\<^sub>l\<^sub>s\<^sub>t A I" "t \<sqsubseteq> t'" by moura
  hence "t' \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)" using declassified_proj_GSMP_subset[OF assms] by blast
  thus "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n A)"
    using SMP.Subterm[of t' "trms_proj\<^sub>l\<^sub>s\<^sub>t n A" t] ground_subterm[OF _ t'(2)] t'(2)
    unfolding GSMP_def by fast
qed

lemma declassified_secrets_subset:
  assumes A: "\<forall>n m. n \<noteq> m \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) (trms_proj\<^sub>l\<^sub>s\<^sub>t m A) Sec"
  and I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "declassified\<^sub>l\<^sub>s\<^sub>t A I \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
using declassified_proj_GSMP_subset[OF I] A at_least_2_labels
unfolding GSMP_disjoint_def by blast

lemma declassified_subterms_secrets_subset:
  assumes A: "\<forall>n m. n \<noteq> m \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t n A) (trms_proj\<^sub>l\<^sub>s\<^sub>t m A) Sec"
  and I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (declassified\<^sub>l\<^sub>s\<^sub>t A I) \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
using declassified_subterms_proj_GSMP_subset[OF I, of A label_witness1]
      declassified_subterms_proj_GSMP_subset[OF I, of A label_witness2]
      A at_least_2_labels
unfolding GSMP_disjoint_def by fast

lemma declassified_proj_eq: "declassified\<^sub>l\<^sub>s\<^sub>t A I = declassified\<^sub>l\<^sub>s\<^sub>t (proj n A) I"
unfolding declassified\<^sub>l\<^sub>s\<^sub>t_def proj_def by auto

lemma declassified_append: "declassified\<^sub>l\<^sub>s\<^sub>t (A@B) I = declassified\<^sub>l\<^sub>s\<^sub>t A I \<union> declassified\<^sub>l\<^sub>s\<^sub>t B I"
unfolding declassified\<^sub>l\<^sub>s\<^sub>t_def by auto

lemma declassified_prefix_subset: "prefix A B \<Longrightarrow> declassified\<^sub>l\<^sub>s\<^sub>t A I \<subseteq> declassified\<^sub>l\<^sub>s\<^sub>t B I"
using declassified_append unfolding prefix_def by auto

subsection \<open>Lemmata: Homogeneous and Heterogeneous Terms\<close>
lemma proj_specific_secrets_anti_mono:
  assumes "proj_specific l t \<A> Sec" "Sec' \<subseteq> Sec"
  shows "proj_specific l t \<A> Sec'"
using assms unfolding proj_specific_def by fast

lemma heterogeneous_secrets_anti_mono:
  assumes "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "Sec' \<subseteq> Sec"
  shows "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec'"
using assms proj_specific_secrets_anti_mono unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by metis

lemma homogeneous_secrets_mono:
  assumes "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec'" "Sec' \<subseteq> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
using assms heterogeneous_secrets_anti_mono by blast

lemma heterogeneous_supterm:
  assumes "heterogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "t \<sqsubseteq> t'"
  shows "heterogeneous\<^sub>l\<^sub>s\<^sub>t t' \<A> Sec"
proof -
  obtain l1 l2 s1 s2 where *:
      "l1 \<noteq> l2"
      "s1 \<sqsubseteq> t" "proj_specific l1 s1 \<A> Sec"
      "s2 \<sqsubseteq> t" "proj_specific l2 s2 \<A> Sec"
    using assms(1) unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by moura
  thus ?thesis
    using term.order_trans[OF *(2) assms(2)] term.order_trans[OF *(4) assms(2)]
    by (auto simp add: heterogeneous\<^sub>l\<^sub>s\<^sub>t_def)
qed

lemma homogeneous_subterm:
  assumes "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "t' \<sqsubseteq> t"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t' \<A> Sec"
by (metis assms heterogeneous_supterm)

lemma proj_specific_subterm:
  assumes "t \<sqsubseteq> t'" "proj_specific l t' \<A> Sec"
  shows "proj_specific l t \<A> Sec \<or> t \<in> Sec \<or> {} \<turnstile>\<^sub>c t"
using GSMP_subterm[OF _ assms(1)] assms(2) by (auto simp add: proj_specific_def)

lemma heterogeneous_term_is_Fun:
  assumes "heterogeneous\<^sub>l\<^sub>s\<^sub>t t A S" shows "\<exists>f T. t = Fun f T"
using assms by (cases t) (auto simp add: GSMP_def heterogeneous\<^sub>l\<^sub>s\<^sub>t_def proj_specific_def)

lemma proj_specific_is_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "proj_specific l m \<A> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
proof
  assume "heterogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
  then obtain s l' where s: "s \<in> subterms m" "proj_specific l' s \<A> Sec" "l \<noteq> l'"
    unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by moura
  hence "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)"
    using t by (auto simp add: GSMP_def proj_specific_def)
  hence "s \<in> Sec \<or> {} \<turnstile>\<^sub>c s"
    using \<A> s(3) by (auto simp add: GSMP_disjoint_def)
  thus False using s(2) by (auto simp add: proj_specific_def)
qed

lemma deduct_synth_homogeneous:
  assumes "{} \<turnstile>\<^sub>c t"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
proof -
  have "\<forall>s \<in> subterms t. {} \<turnstile>\<^sub>c s" using deduct_synth_subterm[OF assms] by auto
  thus ?thesis unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def proj_specific_def by auto
qed

lemma GSMP_proj_is_homogeneous:
  assumes "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l A) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' A) Sec"
  and "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l A)" "t \<notin> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t A Sec"
proof
  assume "heterogeneous\<^sub>l\<^sub>s\<^sub>t t A Sec"
  then obtain s l' where s: "s \<in> subterms t" "proj_specific l' s A Sec" "l \<noteq> l'"
    unfolding heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by moura
  hence "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l A)" "s \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' A)"
    using assms by (auto simp add: GSMP_def proj_specific_def)
  hence "s \<in> Sec \<or> {} \<turnstile>\<^sub>c s" using assms(1) s(3) by (auto simp add: GSMP_disjoint_def)
  thus False using s(2) by (auto simp add: proj_specific_def)
qed

lemma homogeneous_is_not_proj_specific:
  assumes "homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
  shows "\<exists>l::'lbl. \<not>proj_specific l m \<A> Sec"
proof -
  let ?P = "\<lambda>l s. proj_specific l s \<A> Sec"
  have "\<forall>l1 l2. \<forall>s1\<in>subterms m. \<forall>s2\<in>subterms m. (l1 \<noteq> l2 \<longrightarrow> (\<not>?P l1 s1 \<or> \<not>?P l2 s2))"
    using assms heterogeneous\<^sub>l\<^sub>s\<^sub>t_def by metis
  then obtain l1 l2 where "l1 \<noteq> l2" "\<not>?P l1 m \<or> \<not>?P l2 m"
    by (metis term.order_refl at_least_2_labels)
  thus ?thesis by metis
qed

lemma secrets_are_homogeneous:
  assumes "\<forall>s \<in> Sec. P s \<longrightarrow> (\<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Sec)" "s \<in> Sec" "P s"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t s \<A> Sec"
using assms by (auto simp add: heterogeneous\<^sub>l\<^sub>s\<^sub>t_def proj_specific_def)

lemma GSMP_is_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" "t \<notin> Sec"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
proof -
  obtain n where n: "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>)" using in_GSMP_in_proj[OF t(1)] by moura
  show ?thesis using GSMP_proj_is_homogeneous[OF \<A> n t(2)] by metis
qed

lemma GSMP_intersection_is_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
    and t: "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)" "l \<noteq> l'"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
proof -
  define M where "M \<equiv> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
  define M' where "M' \<equiv> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)"

  have t_in: "t \<in> M \<inter> M'" "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
    using t(1) in_proj_in_GSMP[of t _ \<A>]
    unfolding M_def M'_def by blast+

  have "M \<inter> M' \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
    using \<A> GSMP_disjointE[of l \<A> l' Sec] t(2)
    unfolding M_def M'_def by presburger
  moreover have "subterms\<^sub>s\<^sub>e\<^sub>t (M \<inter> M') = M \<inter> M'"
    using GSMP_subterms unfolding M_def M'_def by blast
  ultimately have *: "subterms\<^sub>s\<^sub>e\<^sub>t (M \<inter> M') \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
    by blast

  show ?thesis
  proof (cases "t \<in> Sec")
    case True thus ?thesis
      using * secrets_are_homogeneous[of Sec "\<lambda>t. t \<in> M \<inter> M'", OF _ _ t_in(1)]
      by fast
  qed (metis GSMP_is_homogeneous[OF \<A> t_in(2)])
qed

lemma GSMP_is_homogeneous':
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
         "t \<notin> Sec - \<Union>{GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) | l1 l2. l1 \<noteq> l2}"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec"
using GSMP_is_homogeneous[OF \<A> t(1)] GSMP_intersection_is_homogeneous[OF \<A>] t(2)
by blast

lemma declassified_secrets_are_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
    and \<I>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and s: "s \<in> declassified\<^sub>l\<^sub>s\<^sub>t \<A> \<I>"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t s \<A> Sec"
proof -
  have s_in: "s \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
    using declassified_proj_GSMP_subset[OF \<I>, of \<A> label_witness1]
          in_proj_in_GSMP[of s label_witness1 \<A>] s
    by blast

  show ?thesis
  proof (cases "s \<in> Sec")
    case True thus ?thesis
      using declassified_subterms_secrets_subset[OF \<A> \<I>]
            secrets_are_homogeneous[of Sec "\<lambda>s. s \<in> declassified\<^sub>l\<^sub>s\<^sub>t \<A> \<I>", OF _ _ s]
      by fast
  qed (metis GSMP_is_homogeneous[OF \<A> s_in])
qed

lemma Ana_keys_homogeneous:
  assumes \<A>: "\<forall>l l'. l \<noteq> l' \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>) Sec"
  and t: "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  and k: "Ana t = (K,T)" "k \<in> set K"
         "k \<notin> Sec - \<Union>{GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) | l1 l2. l1 \<noteq> l2}"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t k \<A> Sec"
proof (cases "k \<in> \<Union>{GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) | l1 l2. l1 \<noteq> l2}")
  case False
  hence "k \<notin> Sec" using k(3) by fast
  moreover have "k \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
    using t SMP.Ana[OF _ k(1,2)] Ana_keys_fv[OF k(1)] k(2)
    unfolding GSMP_def by auto
  ultimately show ?thesis using GSMP_is_homogeneous[OF \<A>, of k] by metis
qed (use GSMP_intersection_is_homogeneous[OF \<A>] in blast)

subsection \<open>Lemmata: Intruder Deduction Equivalences\<close>
lemma deduct_if_hom_deduct: "\<langle>M;A;S\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m m \<Longrightarrow> M \<turnstile> m"
using deduct_if_restricted_deduct unfolding intruder_deduct_hom_def by blast

lemma hom_deduct_if_hom_ik:
  assumes "\<langle>M;A;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m m" "\<forall>m \<in> M. homogeneous\<^sub>l\<^sub>s\<^sub>t m A Sec \<and> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
  shows "homogeneous\<^sub>l\<^sub>s\<^sub>t m A Sec \<and> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
proof -
  let ?Q = "\<lambda>m. homogeneous\<^sub>l\<^sub>s\<^sub>t m A Sec \<and> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t A)"
  have "?Q t'" when "?Q t" "t' \<sqsubseteq> t" for t t'
    using homogeneous_subterm[OF _ that(2)] GSMP_subterm[OF _ that(2)] that(1)
    by blast
  thus ?thesis
    using assms(1) restricted_deduct_if_restricted_ik[OF _ assms(2)]
    unfolding intruder_deduct_hom_def
    by blast
qed

lemma deduct_hom_if_synth:
  assumes hom: "homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec" "m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  and m: "M \<turnstile>\<^sub>c m"
  shows "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m m"
proof -
  let ?Q = "\<lambda>m. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec \<and> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  have "?Q t'" when "?Q t" "t' \<sqsubseteq> t" for t t'
    using homogeneous_subterm[OF _ that(2)] GSMP_subterm[OF _ that(2)] that(1)
    by blast
  thus ?thesis
    using assms deduct_restricted_if_synth[of ?Q]
    unfolding intruder_deduct_hom_def
    by blast
qed

lemma hom_deduct_if_deduct:
  assumes \<A>: "par_comp \<A> Sec"
  and M: "\<forall>m\<in>M. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec \<and> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  and m: "M \<turnstile> m" "m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
shows "\<langle>M; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m m"
proof -
  let ?P = "\<lambda>x. homogeneous\<^sub>l\<^sub>s\<^sub>t x \<A> Sec \<and> x \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"

  have GSMP_hom: "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" when "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" for t
    using \<A> GSMP_is_homogeneous[of \<A> Sec t]
          secrets_are_homogeneous[of Sec "\<lambda>x. True" t \<A>] that
    unfolding par_comp_def by blast

  have P_Ana: "?P k" when "?P t" "Ana t = (K, T)" "k \<in> set K" for t K T k
    using GSMP_Ana_key[OF _ that(2,3), of "trms\<^sub>l\<^sub>s\<^sub>t \<A>"] \<A> that GSMP_hom
    by presburger

  have P_subterm: "?P t'" when "?P t" "t' \<sqsubseteq> t" for t t'
    using GSMP_subterm[of _ "trms\<^sub>l\<^sub>s\<^sub>t \<A>"] homogeneous_subterm[of _ \<A> Sec] that
    by blast

  have P_m: "?P m"
    using GSMP_hom[OF m(2)] m(2)
    by metis

  show ?thesis
    using restricted_deduct_if_deduct'[OF M _ _ m(1) P_m] P_Ana P_subterm
    unfolding intruder_deduct_hom_def
    by fast
qed


subsection \<open>Lemmata: Deduction Reduction of Parallel Composable Constraints\<close>
lemma par_comp_hom_deduct:
  assumes \<A>: "par_comp \<A> Sec"
  and M: "\<forall>l. \<forall>m \<in> M l. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
         "\<forall>l. M l \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
         "\<forall>l. Discl \<subseteq> M l"
         "Discl \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
  and Sec: "\<forall>l. \<forall>s \<in> Sec - Discl. \<not>(\<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m s)"
  and t: "\<langle>\<Union>l. M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t"
  shows "t \<notin> Sec - Discl" (is ?A)
        "\<forall>l. t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t" (is ?B)
proof -
  have M': "\<forall>l. \<forall>m \<in> M l. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  proof (intro allI ballI)
    fix l m show "m \<in> M l \<Longrightarrow> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" using M(2) in_proj_in_GSMP[of m l \<A>] by blast
  qed

  show ?A ?B using t
  proof (induction t rule: intruder_deduct_hom_induct)
    case (AxiomH t)
    then obtain lt where t_in_proj_ik: "t \<in> M lt" by moura
    show t_not_Sec: "t \<notin> Sec - Discl"
    proof
      assume "t \<in> Sec - Discl"
      hence "\<forall>l. \<not>(\<langle>M l;\<A>;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t)" using Sec by auto
      thus False using intruder_deduct_hom_AxiomH[OF t_in_proj_ik] by metis
    qed
    
    have 1: "\<forall>l. t \<in> M l \<longrightarrow> t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
      using M(2,3) AxiomH by auto
  
    have 3: "\<And>l1 l2. l1 \<noteq> l2 \<Longrightarrow> t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) \<inter> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>)
                              \<Longrightarrow> {} \<turnstile>\<^sub>c t \<or> t \<in> Discl"
      using \<A> t_not_Sec by (auto simp add: par_comp_def GSMP_disjoint_def)
  
    have 4: "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" using M(1) M' t_in_proj_ik by auto
  
    { fix l assume "t \<in> Discl"
      hence "t \<in> M l" using M(3) by auto
      hence "\<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t" by auto
    } hence 5: "\<forall>l. t \<in> Discl \<longrightarrow> \<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t" by metis
    
    show "\<forall>l. t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t"
      by (metis (lifting) Int_iff empty_subsetI
          1 3 4 5 t_in_proj_ik
          intruder_deduct_hom_AxiomH[of t _ \<A> Sec]
          deduct_hom_if_synth[of t \<A> Sec "{}"]
          ideduct_hom_mono[of "{}" \<A> Sec t])
  next
    case (ComposeH T f)
    show "\<forall>l. Fun f T \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m Fun f T"
    proof (intro allI impI)
      fix l
      assume "Fun f T \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
      hence "\<And>t. t \<in> set T \<Longrightarrow> t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
        using GSMP_subterm[OF _ subtermeqI''] by auto
      thus "\<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m Fun f T"
        using ComposeH.IH(2) intruder_deduct_hom_ComposeH[OF ComposeH.hyps(1,2) _ ComposeH.hyps(4,5)]
        by simp
    qed
    thus "Fun f T \<notin> Sec - Discl"
      using Sec ComposeH.hyps(5) trms\<^sub>l\<^sub>s\<^sub>t_union[of \<A>] GSMP_Union[of \<A>]
      by (metis (no_types, lifting) UN_iff)
  next
    case (DecomposeH t K T t\<^sub>i)
    have ti_subt: "t\<^sub>i \<sqsubseteq> t" using Ana_subterm[OF DecomposeH.hyps(2)] \<open>t\<^sub>i \<in> set T\<close> by auto
    have t: "homogeneous\<^sub>l\<^sub>s\<^sub>t t \<A> Sec" "t \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
      using DecomposeH.hyps(1) hom_deduct_if_hom_ik M(1) M'
      by auto
    have ti: "homogeneous\<^sub>l\<^sub>s\<^sub>t t\<^sub>i \<A> Sec" "t\<^sub>i \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
      using intruder_deduct_hom_DecomposeH[OF DecomposeH.hyps] hom_deduct_if_hom_ik M(1) M' by auto
    { fix l assume *: "t\<^sub>i \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
      hence "\<And>k. k \<in> set K \<Longrightarrow> \<langle>M l;\<A>;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m k"
        using GSMP_Ana_key[OF _ DecomposeH.hyps(2)] DecomposeH.IH(4) by auto
      hence "\<langle>M l;\<A>;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t\<^sub>i" "t\<^sub>i \<notin> Sec - Discl"
        using Sec DecomposeH.IH(2) *(2)
              intruder_deduct_hom_DecomposeH[OF _ DecomposeH.hyps(2) _ \<open>t\<^sub>i \<in> set T\<close>]
        by force+
    } moreover {
      fix l1 l2 assume *: "t\<^sub>i \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>)" "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>)" "l1 \<noteq> l2"
      have "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec"
        using *(3) \<A> by (simp add: par_comp_def)
      hence "t\<^sub>i \<in> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
        using GSMP_subterm[OF *(2) ti_subt] *(1) by (auto simp add: GSMP_disjoint_def)
      moreover have "\<And>k. k \<in> set K \<Longrightarrow> \<langle>M l2;\<A>;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m k"
        using *(2) GSMP_Ana_key[OF _ DecomposeH.hyps(2)] DecomposeH.IH(4) by auto
      ultimately have "t\<^sub>i \<notin> Sec - Discl" "{} \<turnstile>\<^sub>c t\<^sub>i \<or> t\<^sub>i \<in> Discl"
        using Sec DecomposeH.IH(2) *(2)
              intruder_deduct_hom_DecomposeH[OF _ DecomposeH.hyps(2) _ \<open>t\<^sub>i \<in> set T\<close>]
         by (metis (lifting), metis (no_types, lifting) DiffI Un_iff mem_Collect_eq)
      hence "\<langle>M l1;\<A>;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t\<^sub>i" "\<langle>M l2;\<A>;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t\<^sub>i" "t\<^sub>i \<notin> Sec - Discl"
        using M(3,4) deduct_hom_if_synth[THEN ideduct_hom_mono] ti
        by (meson intruder_deduct_hom_AxiomH empty_subsetI subsetCE)+
    } moreover have
        "\<exists>l. t\<^sub>i \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
        "\<exists>l. t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
      using in_GSMP_in_proj[of _ \<A>] ti(2) t(2) by presburger+
    ultimately show
        "t\<^sub>i \<notin> Sec - Discl"
        "\<forall>l. t\<^sub>i \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>) \<longrightarrow> \<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t\<^sub>i"
      by (metis (no_types, lifting))+
  qed
qed

lemma par_comp_deduct_proj:
  assumes \<A>: "par_comp \<A> Sec"
  and M: "\<forall>l. \<forall>m\<in>M l. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec"
         "\<forall>l. M l \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
         "\<forall>l. Discl \<subseteq> M l"
  and t: "(\<Union>l. M l) \<turnstile> t" "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
  and Discl: "Discl \<subseteq> Sec \<union> {m. {} \<turnstile>\<^sub>c m}"
  shows "M l \<turnstile> t \<or> (\<exists>s \<in> Sec - Discl. \<exists>l. M l \<turnstile> s)"
using t
proof (induction t rule: intruder_deduct_induct)
  case (Axiom t)
  then obtain l' where t_in_ik_proj: "t \<in> M l'" by moura
  show ?case
  proof (cases "t \<in> Sec - Discl \<or> {} \<turnstile>\<^sub>c t")
    case True
    note T = True
    show ?thesis
    proof (cases "t \<in> Sec - Discl")
      case True thus ?thesis using intruder_deduct.Axiom[OF t_in_ik_proj] by metis
    next
      case False thus ?thesis using T ideduct_mono[of "{}" t] by auto
    qed
  next
    case False
    hence "t \<notin> Sec - Discl" "\<not>{} \<turnstile>\<^sub>c t" "t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" using Axiom by auto
    hence "(\<forall>l'. l \<noteq> l' \<longrightarrow> t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)) \<or> t \<in> Discl"
      using \<A> unfolding GSMP_disjoint_def par_comp_def by auto
    hence "(\<forall>l'. l \<noteq> l' \<longrightarrow> t \<notin> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l' \<A>)) \<or> t \<in> M l \<or> {} \<turnstile>\<^sub>c t" using M by auto
    thus ?thesis using Axiom deduct_if_synth[THEN ideduct_mono] t_in_ik_proj
      by (metis (no_types, lifting) False M(2) intruder_deduct.Axiom subsetCE) 
  qed
next
  case (Compose T f)
  hence "Fun f T \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" using Compose.prems by auto
  hence "\<And>t. t \<in> set T \<Longrightarrow> t \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" unfolding GSMP_def by auto
  hence IH: "\<And>t. t \<in> set T \<Longrightarrow> M l \<turnstile> t \<or> (\<exists>s \<in> Sec - Discl. \<exists>l. M l \<turnstile> s)"
    using Compose.IH by auto
  show ?case
  proof (cases "\<forall>t \<in> set T. M l \<turnstile> t")
    case True thus ?thesis by (metis intruder_deduct.Compose[OF Compose.hyps(1,2)])
  qed (metis IH)
next
  case (Decompose t K T t\<^sub>i)
  have hom_ik: "\<forall>l. \<forall>m\<in>M l. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec \<and> m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
  proof (intro allI ballI conjI)
    fix l m assume m: "m \<in> M l"
    thus "homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec" using M(1) by simp
    show "m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" using in_proj_in_GSMP[of m l \<A>] M(2) m by blast
  qed

  have par_comp_unfold:
      "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec"
    using \<A> by (auto simp add: par_comp_def)

  note ti_GSMP = in_proj_in_GSMP[OF Decompose.prems(1)]

  have "\<langle>\<Union>l. M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t\<^sub>i"
    using intruder_deduct.Decompose[OF Decompose.hyps]
          hom_deduct_if_deduct[OF \<A>, of "\<Union>l. M l"] hom_ik ti_GSMP (* ti_hom *)
    by blast
  hence "(\<langle>M l; \<A>; Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m t\<^sub>i) \<or> (\<exists>s \<in> Sec-Discl. \<exists>l. \<langle>M l;\<A>;Sec\<rangle> \<turnstile>\<^sub>h\<^sub>o\<^sub>m s)"
    using par_comp_hom_deduct(2)[OF \<A> M Discl(1)] Decompose.prems(1)
    by blast
  thus ?case using deduct_if_hom_deduct[of _ \<A> Sec] by auto
qed


subsection \<open>Theorem: Parallel Compositionality for Labeled Constraints\<close>
lemma par_comp_prefix: assumes "par_comp (A@B) M" shows "par_comp A M"
proof -
  let ?L = "\<lambda>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l A \<union> trms_proj\<^sub>l\<^sub>s\<^sub>t l B"
  have "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (?L l1) (?L l2) M"
    using assms unfolding par_comp_def
    by (metis trms\<^sub>s\<^sub>t_append proj_append(2) unlabel_append)
  hence "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 A) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 A) M"
    using SMP_union by (auto simp add: GSMP_def GSMP_disjoint_def)
  thus ?thesis using assms unfolding par_comp_def by blast
qed

theorem par_comp_constr_typed:
  assumes \<A>: "par_comp \<A> Sec"
  and \<I>: "\<I> \<Turnstile> \<langle>unlabel \<A>\<rangle>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
  shows "(\<forall>l. (\<I> \<Turnstile> \<langle>proj_unl l \<A>\<rangle>)) \<or> (\<exists>\<A>'. prefix \<A>' \<A> \<and> (strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A>' Sec \<I>))"
proof -
  let ?L = "\<lambda>\<A>'. \<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>. \<exists>l. \<lbrakk>{}; proj_unl l \<A>'@[Send t]\<rbrakk>\<^sub>d \<I>"
  have "\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>" using \<I> by (simp add: constr_sem_d_def)
  with \<A> have "(\<forall>l. \<lbrakk>{}; proj_unl l \<A>\<rbrakk>\<^sub>d \<I>) \<or> (\<exists>\<A>'. prefix \<A>' \<A> \<and> ?L \<A>')"
  proof (induction "unlabel \<A>" arbitrary: \<A> rule: List.rev_induct)
    case Nil
    hence "\<A> = []" using unlabel_nil_only_if_nil by simp
    thus ?case by auto
  next
    case (snoc b B \<A>)
    hence disj: "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec"
      by (auto simp add: par_comp_def)

    obtain a A n where a: "\<A> = A@[a]" "a = (ln n, b) \<or> a = (\<star>, b)"
      using unlabel_snoc_inv[OF snoc.hyps(2)[symmetric]] by moura
    hence A: "\<A> = A@[(ln n, b)] \<or> \<A> = A@[(\<star>, b)]" by metis

    have 1: "B = unlabel A" using a snoc.hyps(2) unlabel_append[of A "[a]"] by auto
    have 2: "par_comp A Sec" using par_comp_prefix snoc.prems(1) a by metis
    have 3: "\<lbrakk>{}; unlabel A\<rbrakk>\<^sub>d \<I>" by (metis 1 snoc.prems(2) snoc.hyps(2) strand_sem_split(3))
    have IH: "(\<forall>l. \<lbrakk>{}; proj_unl l A\<rbrakk>\<^sub>d \<I>) \<or> (\<exists>\<A>'. prefix \<A>' A \<and> ?L \<A>')"
      by (rule snoc.hyps(1)[OF 1 2 3])

    show ?case
    proof (cases "\<forall>l. \<lbrakk>{}; proj_unl l A\<rbrakk>\<^sub>d \<I>")
      case False
      then obtain \<A>' where \<A>': "prefix \<A>' A" "?L \<A>'" by (metis IH)
      hence "prefix \<A>' (A@[a])" using a prefix_prefix[of _ A "[a]"] by simp
      thus ?thesis using \<A>'(2) a by auto
    next
      case True
      note IH' = True
      show ?thesis
      proof (cases b)
        case (Send t)
        hence "ik\<^sub>s\<^sub>t (unlabel A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
          using a \<open>\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>\<close> strand_sem_split(2)[of "{}" "unlabel A" "unlabel [a]" \<I>]
                unlabel_append[of A "[a]"]
          by auto
        hence *: "(\<Union>l. (ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)) \<turnstile> t \<cdot> \<I>"
          using proj_ik_union_is_unlabel_ik image_UN by metis 

        have "ik\<^sub>s\<^sub>t (proj_unl l \<A>) = ik\<^sub>s\<^sub>t (proj_unl l A)" for l
          using Send A 
          by (metis append_Nil2 ik\<^sub>s\<^sub>t.simps(3) proj_unl_cons(3) proj_nil(2)
                    singleton_lst_proj(1,2) proj_ik_append)
        hence **: "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" for l
          using ik_proj_subst_GSMP_subset[OF \<I>(3,4,2), of _ \<A>]
          by auto

        note Discl =
          declassified_proj_ik_subset[of A \<I>]
          declassified_proj_GSMP_subset[OF \<I>(3,4,2), of A]
          declassified_secrets_subset[OF disj \<I>(3,4,2)]
          declassified_append[of A "[a]" \<I>]

        have Sec: "ground Sec"
          using \<A> by (auto simp add: par_comp_def)

        have "\<forall>m\<in>ik\<^sub>s\<^sub>t (proj_unl l \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec \<or> m \<in> Sec-declassified\<^sub>l\<^sub>s\<^sub>t A \<I>"
             "\<forall>m\<in>ik\<^sub>s\<^sub>t (proj_unl l \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. m \<in> GSMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
             "ik\<^sub>s\<^sub>t (proj_unl l \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
          for l
          using declassified_secrets_are_homogeneous[OF disj \<I>(3,4,2)]
                GSMP_proj_is_homogeneous[OF disj]
                ik_proj_subst_GSMP_subset[OF \<I>(3,4,2), of _ \<A>]
          apply (metis (no_types, lifting) Diff_iff Discl(4) UnCI a(1) subsetCE)
          using ik_proj_subst_GSMP_subset[OF \<I>(3,4,2), of _ \<A>]
                GSMP_Union[of \<A>]
          by auto
        moreover have "ik\<^sub>s\<^sub>t (proj_unl l [a]) = {}" for l
          using Send proj_ik\<^sub>s\<^sub>t_is_proj_rcv_set[of _ "[a]"] a(2) by auto
        ultimately have M:
            "\<forall>l. \<forall>m\<in>ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec \<or> m \<in> Sec-declassified\<^sub>l\<^sub>s\<^sub>t A \<I>"
            "\<forall>l. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)"
          using a(1) proj_ik_append[of _ A "[a]"] by auto

        have prefix_A: "prefix A \<A>" using A by auto

        have "s \<cdot> \<I> = s"
          when "s \<in> Sec" for s
          using that Sec by auto
        hence leakage_case: "\<lbrakk>{}; proj_unl l A@[Send s]\<rbrakk>\<^sub>d \<I>"
          when "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>" "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s" for l s
          using that strand_sem_append(2) IH' by auto

        have proj_deduct_case_n:
            "\<forall>m. m \<noteq> n \<longrightarrow> \<lbrakk>{}; proj_unl m (A@[a])\<rbrakk>\<^sub>d \<I>"
            "ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I> \<Longrightarrow> \<lbrakk>{}; proj_unl n (A@[a])\<rbrakk>\<^sub>d \<I>"
          when "a = (ln n, Send t)"
          using that IH' proj_append(2)[of _ A]
          by auto

        have proj_deduct_case_star:
            "\<lbrakk>{}; proj_unl l (A@[a])\<rbrakk>\<^sub>d \<I>"
          when "a = (\<star>, Send t)" "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" for l
          using that IH' proj_append(2)[of _ A] 
          by auto

        show ?thesis
        proof (cases "\<exists>l. \<exists>m \<in> ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. m \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>")
          case True
          then obtain l s where ls: "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>" "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s"
            using intruder_deduct.Axiom by metis
          thus ?thesis using leakage_case prefix_A by blast
        next
          case False
          hence M': "\<forall>l. \<forall>m\<in>ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. homogeneous\<^sub>l\<^sub>s\<^sub>t m \<A> Sec" using M(1) by blast

          note deduct_proj_lemma =
              par_comp_deduct_proj[OF snoc.prems(1) M' M(2) _ *, of "declassified\<^sub>l\<^sub>s\<^sub>t A \<I>" n]

          from a(2) show ?thesis
          proof
            assume "a = (ln n, b)"
            hence "a = (ln n, Send t)" "t \<cdot> \<I> \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>)"
              using Send a(1) trms_proj\<^sub>l\<^sub>s\<^sub>t_append[of n A "[a]"]
                    GSMP_wt_substI[OF _ \<I>(3,4,2)]
              by (metis, force)
            hence
                "a = (ln n, Send t)"
                "\<forall>m. m \<noteq> n \<longrightarrow> \<lbrakk>{}; proj_unl m (A@[a])\<rbrakk>\<^sub>d \<I>"
                "ik\<^sub>s\<^sub>t (proj_unl n A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I> \<Longrightarrow> \<lbrakk>{}; proj_unl n (A@[a])\<rbrakk>\<^sub>d \<I>"
                "t \<cdot> \<I> \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t n \<A>)"
              using proj_deduct_case_n
              by auto
            hence "(\<forall>l. \<lbrakk>{}; proj_unl l \<A>\<rbrakk>\<^sub>d \<I>) \<or>
                   (\<exists>s \<in> Sec-declassified\<^sub>l\<^sub>s\<^sub>t A \<I>. \<exists>l. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s)"
              using deduct_proj_lemma A a Discl
              by fast
            thus ?thesis using leakage_case prefix_A by metis
          next
            assume "a = (\<star>, b)"
            hence ***: "a = (\<star>, Send t)" "t \<cdot> \<I> \<in> GSMP (trms_proj\<^sub>l\<^sub>s\<^sub>t l \<A>)" for l
              using Send a(1) GSMP_wt_substI[OF _ \<I>(3,4,2)]
              by (metis, force)
            hence "t \<cdot> \<I> \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I> \<or>
                   t \<cdot> \<I> \<in> declassified\<^sub>l\<^sub>s\<^sub>t A \<I> \<or>
                   t \<cdot> \<I> \<in> {m. {} \<turnstile>\<^sub>c m}"
              using snoc.prems(1) a(1) at_least_2_labels
              unfolding par_comp_def GSMP_disjoint_def
              by blast
            thus ?thesis
            proof (elim disjE)
              assume "t \<cdot> \<I> \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>"
              hence "\<exists>s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t A \<I>. \<exists>l. ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> s"
                using deduct_proj_lemma ***(2) A a Discl
                by blast
              thus ?thesis using prefix_A leakage_case by blast
            next
              assume "t \<cdot> \<I> \<in> declassified\<^sub>l\<^sub>s\<^sub>t A \<I>"
              hence "ik\<^sub>s\<^sub>t (proj_unl l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" for l
                using intruder_deduct.Axiom Discl(1) by blast
              thus ?thesis using proj_deduct_case_star[OF ***(1)] a(1) by fast
            next
              assume "t \<cdot> \<I> \<in> {m. {} \<turnstile>\<^sub>c m}"
              hence "M \<turnstile> t \<cdot> \<I>" for M using ideduct_mono[OF deduct_if_synth] by blast
              thus ?thesis using IH' a(1) ***(1) by fastforce
            qed
          qed
        qed
      next
        case (Receive t)
        hence "\<lbrakk>{}; proj_unl l \<A>\<rbrakk>\<^sub>d \<I>" for l
          using IH' a proj_append(2)[of l A "[a]"]
          unfolding unlabel_def proj_def by auto
        thus ?thesis by metis
      next
        case (Equality ac t t')
        hence *: "\<lbrakk>M; [Equality ac t t']\<rbrakk>\<^sub>d \<I>" for M
          using a \<open>\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>\<close> unlabel_append[of A "[a]"]
          by auto
        show ?thesis
          using a proj_append(2)[of _ A "[a]"] Equality
                strand_sem_append(2)[OF _ *] IH'
          unfolding unlabel_def proj_def by auto
      next
        case (Inequality X F)
        hence *: "\<lbrakk>M; [Inequality X F]\<rbrakk>\<^sub>d \<I>" for M
          using a \<open>\<lbrakk>{}; unlabel \<A>\<rbrakk>\<^sub>d \<I>\<close> unlabel_append[of A "[a]"]
          by auto
        show ?thesis
          using a proj_append(2)[of _ A "[a]"] Inequality
                strand_sem_append(2)[OF _ *] IH'
          unfolding unlabel_def proj_def by auto
      qed
    qed
  qed
  thus ?thesis using \<I>(1) unfolding strand_leaks\<^sub>l\<^sub>s\<^sub>t_def by (simp add: constr_sem_d_def)
qed

theorem par_comp_constr:
  assumes \<A>: "par_comp \<A> Sec" "typing_cond (unlabel \<A>)"
  and \<I>: "\<I> \<Turnstile> \<langle>unlabel \<A>\<rangle>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<exists>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and> (\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel \<A>\<rangle>) \<and>
              ((\<forall>l. (\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl l \<A>\<rangle>)) \<or> (\<exists>\<A>'. prefix \<A>' \<A> \<and> (strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>)))"
proof -
  from \<A>(2) have *:
      "wf\<^sub>s\<^sub>t {} (unlabel \<A>)"
      "fv\<^sub>s\<^sub>t (unlabel \<A>) \<inter> bvars\<^sub>s\<^sub>t (unlabel \<A>) = {}"
      "tfr\<^sub>s\<^sub>t (unlabel \<A>)"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t (unlabel \<A>))"
      "Ana_invar_subst (ik\<^sub>s\<^sub>t (unlabel \<A>) \<union> assignment_rhs\<^sub>s\<^sub>t (unlabel \<A>))"
    unfolding typing_cond_def tfr\<^sub>s\<^sub>t_def by metis+

  obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>: "\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel \<A>\<rangle>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
    using wt_attack_if_tfr_attack_d[OF * \<I>(2,1)] by metis

  show ?thesis using par_comp_constr_typed[OF \<A>(1) \<I>\<^sub>\<tau>] \<I>\<^sub>\<tau> by auto
qed


subsection \<open>Theorem: Parallel Compositionality for Labeled Protocols\<close>
subsubsection \<open>Definitions: Labeled Protocols\<close>
text \<open>
  We state our result on the level of protocol traces (i.e., the constraints reachable in a
  symbolic execution of the actual protocol). Hence, we do not need to convert protocol strands
  to intruder constraints in the following well-formedness definitions.
\<close>
definition wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s::"('fun,'var,'lbl) labeled_strand set \<Rightarrow> bool" where
  "wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s \<S> \<equiv> (\<forall>\<A> \<in> \<S>. wf\<^sub>l\<^sub>s\<^sub>t {} \<A>) \<and> (\<forall>\<A> \<in> \<S>. \<forall>\<A>' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>t \<A>' = {})"

definition wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s'::"('fun,'var,'lbl) labeled_strand set \<Rightarrow> ('fun,'var,'lbl) labeled_strand \<Rightarrow> bool"
where
  "wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s' \<S> \<A> \<equiv> (\<forall>\<A>' \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>l\<^sub>s\<^sub>t \<A>) (unlabel \<A>')) \<and>
                 (\<forall>\<A>' \<in> \<S>. \<forall>\<A>'' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>t \<A>' \<inter> bvars\<^sub>l\<^sub>s\<^sub>t \<A>'' = {}) \<and>
                 (\<forall>\<A>' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>t \<A>' \<inter> bvars\<^sub>l\<^sub>s\<^sub>t \<A> = {}) \<and>
                 (\<forall>\<A>' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>t \<A>' = {})"

definition typing_cond_prot where
  "typing_cond_prot \<P> \<equiv>
    wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s \<P> \<and>
    tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>l\<^sub>s\<^sub>t ` \<P>)) \<and>
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>l\<^sub>s\<^sub>t ` \<P>)) \<and>
    (\<forall>\<A> \<in> \<P>. list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel \<A>)) \<and>
    Ana_invar_subst (\<Union>(ik\<^sub>s\<^sub>t ` unlabel ` \<P>) \<union> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` unlabel ` \<P>))"

definition par_comp_prot where
  "par_comp_prot \<P> Sec \<equiv>
    (\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow>
      GSMP_disjoint (\<Union>\<A> \<in> \<P>. trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (\<Union>\<A> \<in> \<P>. trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec) \<and>
    ground Sec \<and> (\<forall>s \<in> Sec. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Sec) \<and>
    typing_cond_prot \<P>"


subsubsection \<open>Lemmata: Labeled Protocols\<close>
lemma wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s_eqs_wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s'[simp]: "wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s S = wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s' S []"
unfolding wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s_def wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s'_def unlabel_def by auto

lemma par_comp_prot_impl_par_comp:
  assumes "par_comp_prot \<P> Sec" "\<A> \<in> \<P>"
  shows "par_comp \<A> Sec"
proof -
  have *: "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow>
              GSMP_disjoint (\<Union>\<A> \<in> \<P>. trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (\<Union>\<A> \<in> \<P>. trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec"
    using assms(1) unfolding par_comp_prot_def by metis
  { fix l1 l2::'lbl assume **: "l1 \<noteq> l2"
    hence ***: "GSMP_disjoint (\<Union>\<A> \<in> \<P>. trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (\<Union>\<A> \<in> \<P>. trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec"
      using * by auto
    have "GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec"
      using GSMP_disjoint_subset[OF ***] assms(2) by auto
  } hence "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 \<A>) (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 \<A>) Sec" by metis
  thus ?thesis using assms unfolding par_comp_prot_def par_comp_def by metis
qed

lemma typing_cond_prot_impl_typing_cond:
  assumes "typing_cond_prot \<P>" "\<A> \<in> \<P>"
  shows "typing_cond (unlabel \<A>)"
proof -
  have 1: "wf\<^sub>s\<^sub>t {} (unlabel \<A>)" "fv\<^sub>l\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>t \<A> = {}"
    using assms unfolding typing_cond_prot_def wf\<^sub>l\<^sub>s\<^sub>t\<^sub>s_def by auto

  have "tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>l\<^sub>s\<^sub>t ` \<P>))"
       "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>l\<^sub>s\<^sub>t ` \<P>))"
       "trms\<^sub>l\<^sub>s\<^sub>t \<A> \<subseteq> \<Union>(trms\<^sub>l\<^sub>s\<^sub>t ` \<P>)"
       "SMP (trms\<^sub>l\<^sub>s\<^sub>t \<A>) - Var`\<V> \<subseteq> SMP (\<Union>(trms\<^sub>l\<^sub>s\<^sub>t ` \<P>)) - Var`\<V>"
    using assms SMP_mono[of "trms\<^sub>l\<^sub>s\<^sub>t \<A>" "\<Union>(trms\<^sub>l\<^sub>s\<^sub>t ` \<P>)"]
    unfolding typing_cond_prot_def
    by (metis, metis, auto)
  hence 2: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>t \<A>)" and 3: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>t \<A>)"
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by (meson subsetD)+

  have 4: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel \<A>)" using assms unfolding typing_cond_prot_def by auto

  have "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t (unlabel \<A>) \<union> assignment_rhs\<^sub>s\<^sub>t (unlabel \<A>)) \<subseteq>
        subterms\<^sub>s\<^sub>e\<^sub>t (\<Union>(ik\<^sub>s\<^sub>t ` unlabel ` \<P>) \<union> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` unlabel ` \<P>))"
    using assms(2) by auto
  hence 5: "Ana_invar_subst (ik\<^sub>s\<^sub>t (unlabel \<A>) \<union> assignment_rhs\<^sub>s\<^sub>t (unlabel \<A>))"
    using assms SMP_mono unfolding typing_cond_prot_def Ana_invar_subst_def by (meson subsetD)

  show ?thesis using 1 2 3 4 5 unfolding typing_cond_def tfr\<^sub>s\<^sub>t_def by blast
qed


subsubsection \<open>Theorem: Parallel Compositionality for Labeled Protocols\<close>
definition component_prot where
  "component_prot n P \<equiv> (\<forall>l \<in> P. \<forall>s \<in> set l. is_LabelN n s \<or> is_LabelS s)"

definition composed_prot where
  "composed_prot \<P>\<^sub>i \<equiv> {\<A>. \<forall>n. proj n \<A> \<in> \<P>\<^sub>i n}"

definition component_secure_prot where
  "component_secure_prot n P Sec attack \<equiv> (\<forall>\<A> \<in> P. suffix [(ln n, Send (Fun attack []))] \<A> \<longrightarrow> 
     (\<forall>\<I>\<^sub>\<tau>. (interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)) \<longrightarrow>
            \<not>(\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>\<rangle>) \<and>
            (\<forall>\<A>'. prefix \<A>' \<A> \<longrightarrow>
                    (\<forall>t \<in> Sec-declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<not>(\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>'@[Send t]\<rangle>)))))"

definition component_leaks where
  "component_leaks n \<A> Sec \<equiv> (\<exists>\<A>' \<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and>
      prefix \<A>' \<A> \<and> (\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. (\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>'@[Send t]\<rangle>)))"

definition unsat where
  "unsat \<A> \<equiv> (\<forall>\<I>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<longrightarrow> \<not>(\<I> \<Turnstile> \<langle>unlabel \<A>\<rangle>))"

theorem par_comp_constr_prot:
  assumes P: "P = composed_prot Pi" "par_comp_prot P Sec" "\<forall>n. component_prot n (Pi n)"
  and left_secure: "component_secure_prot n (Pi n) Sec attack"
  shows "\<forall>\<A> \<in> P. suffix [(ln n, Send (Fun attack []))] \<A> \<longrightarrow>
                  unsat \<A> \<or> (\<exists>m. n \<noteq> m \<and> component_leaks m \<A> Sec)"
proof -
  { fix \<A> \<A>' assume \<A>: "\<A> = \<A>'@[(ln n, Send (Fun attack []))]" "\<A> \<in> P"
    let ?P = "\<exists>\<A>' \<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and> prefix \<A>' \<A> \<and>
                   (\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<exists>m. n \<noteq> m \<and> (\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl m \<A>'@[Send t]\<rangle>))"
    have tcp: "typing_cond_prot P" using P(2) unfolding par_comp_prot_def by simp
    have par_comp: "par_comp \<A> Sec" "typing_cond (unlabel \<A>)"
      using par_comp_prot_impl_par_comp[OF P(2) \<A>(2)]
            typing_cond_prot_impl_typing_cond[OF tcp \<A>(2)]
      by metis+
  
    have "unlabel (proj n \<A>) = proj_unl n \<A>" "proj_unl n \<A> = proj_unl n (proj n \<A>)"
         "\<And>A. A \<in> Pi n \<Longrightarrow> proj n A = A" 
         "proj n \<A> = (proj n \<A>')@[(ln n, Send (Fun attack []))]"
      using P(1,3) \<A> by (auto simp add: proj_def unlabel_def component_prot_def composed_prot_def)
    moreover have "proj n \<A> \<in> Pi n"
      using P(1) \<A> unfolding composed_prot_def by blast
    moreover {
      fix A assume "prefix A \<A>"
      hence *: "prefix (proj n A) (proj n \<A>)" unfolding proj_def prefix_def by force
      hence "proj_unl n A = proj_unl n (proj n A)"
            "\<forall>I. declassified\<^sub>l\<^sub>s\<^sub>t A I = declassified\<^sub>l\<^sub>s\<^sub>t (proj n A) I"
        unfolding proj_def declassified\<^sub>l\<^sub>s\<^sub>t_def by auto
      hence "\<exists>B. prefix B (proj n \<A>) \<and> proj_unl n A = proj_unl n B \<and>
                 (\<forall>I. declassified\<^sub>l\<^sub>s\<^sub>t A I = declassified\<^sub>l\<^sub>s\<^sub>t B I)"
        using * by metis
        
    }
    ultimately have *: 
        "\<forall>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<longrightarrow>
                  \<not>(\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>\<rangle>) \<and> (\<forall>\<A>'. prefix \<A>' \<A> \<longrightarrow>
                        (\<forall>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<not>(\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>'@[Send t]\<rangle>)))"
      using left_secure unfolding component_secure_prot_def composed_prot_def suffix_def by metis
    { fix \<I> assume \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "\<I> \<Turnstile> \<langle>unlabel \<A>\<rangle>"
      obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>:
          "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
          "\<exists>\<A>'. prefix \<A>' \<A> \<and> (strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>)"
        using par_comp_constr[OF par_comp \<I>(2,1)] * by moura
      hence "\<exists>\<A>'. prefix \<A>' \<A> \<and> (\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<exists>m.
                  n \<noteq> m \<and> (\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl m \<A>'@[Send t]\<rangle>))"
        using \<I>\<^sub>\<tau>(4) * unfolding strand_leaks\<^sub>l\<^sub>s\<^sub>t_def by metis
      hence ?P using \<I>\<^sub>\<tau>(1,2,3) by auto
    } hence "unsat \<A> \<or> (\<exists>m. n \<noteq> m \<and> component_leaks m \<A> Sec)"
      by (metis unsat_def component_leaks_def)
  } thus ?thesis unfolding suffix_def by metis
qed

end


subsection \<open>Automated GSMP Disjointness\<close>
locale labeled_typed_model' = typed_model' arity public Ana \<Gamma> +
  labeled_typed_model arity public Ana \<Gamma> label_witness1 label_witness2
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,(('fun,'atom::finite) term_type \<times> nat)) term
              \<Rightarrow> (('fun,(('fun,'atom) term_type \<times> nat)) term list
                 \<times> ('fun,(('fun,'atom) term_type \<times> nat)) term list)"
    and \<Gamma>::"('fun,(('fun,'atom) term_type \<times> nat)) term \<Rightarrow> ('fun,'atom) term_type"
    and label_witness1 label_witness2::'lbl
begin

lemma GSMP_disjointI:
  fixes A' A B B'::"('fun, ('fun, 'atom) term \<times> nat) term list"
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "\<delta> \<equiv> var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t (set A)))"
  assumes A'_wf: "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) A'"
    and B'_wf: "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) B'"
    and A_inst: "has_all_wt_instances_of \<Gamma> (set A') (set A)"
    and B_inst: "has_all_wt_instances_of \<Gamma> (set B') (set (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>))"
    and A_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> A"
    and B_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
    and AB_trms_disj:
      "\<forall>t \<in> set A. \<forall>s \<in> set (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>). \<Gamma> t = \<Gamma> s \<and> mgu t s \<noteq> None \<longrightarrow>
        (intruder_synth' public arity {} t \<and> intruder_synth' public arity {} s) \<or>
        ((\<exists>u \<in> Sec. is_wt_instance_of_cond \<Gamma> t u) \<and> (\<exists>u \<in> Sec. is_wt_instance_of_cond \<Gamma> s u))"
    and Sec_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s Sec"
  shows "GSMP_disjoint (set A') (set B') ((f Sec) - {m. {} \<turnstile>\<^sub>c m})"
proof -
  have A_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set A)" and B_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>))"
    and A'_wf': "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set A')" and B'_wf': "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set B')"
    using finite_SMP_representationD[OF A_SMP_repr]
          finite_SMP_representationD[OF B_SMP_repr]
          A'_wf B'_wf
    unfolding wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric] list_all_iff by blast+

  have AB_fv_disj: "fv\<^sub>s\<^sub>e\<^sub>t (set A) \<inter> fv\<^sub>s\<^sub>e\<^sub>t (set (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)) = {}"
    using var_rename_fv_set_disjoint'[of "set A" "set B", unfolded \<delta>_def[symmetric]] by simp

  have "GSMP_disjoint (set A) (set (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)) ((f Sec) - {m. {} \<turnstile>\<^sub>c m})"
    using ground_SMP_disjointI[OF AB_fv_disj A_SMP_repr B_SMP_repr Sec_wf AB_trms_disj]
    unfolding GSMP_def GSMP_disjoint_def f_def by blast
  moreover have "SMP (set A') \<subseteq> SMP (set A)" "SMP (set B') \<subseteq> SMP (set (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>))"
    using SMP_I'[OF A'_wf' A_wf A_inst] SMP_SMP_subset[of "set A'" "set A"]
          SMP_I'[OF B'_wf' B_wf B_inst] SMP_SMP_subset[of "set B'" "set (B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"]
    by blast+
  ultimately show ?thesis unfolding GSMP_def GSMP_disjoint_def by auto
qed

end

end
