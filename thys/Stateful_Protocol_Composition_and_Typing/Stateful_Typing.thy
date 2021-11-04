(*
(C) Copyright Andreas Viktor Hess, DTU, 2018-2020

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

(*  Title:      Stateful_Typing.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>Extending the Typing Result to Stateful Constraints\<close>
text \<open>\label{sec:Stateful-Typing}\<close>

theory Stateful_Typing
imports Typing_Result Stateful_Strands
begin

text \<open>Locale setup\<close>
locale stateful_typed_model = typed_model arity public Ana \<Gamma>
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,'var) term \<Rightarrow> (('fun,'var) term list \<times> ('fun,'var) term list)"
    and \<Gamma>::"('fun,'var) term \<Rightarrow> ('fun,'atom::finite) term_type"
  +
  fixes Pair::"'fun"
  assumes Pair_arity: "arity Pair = 2"
  and Ana_subst': "\<And>f T \<delta> K M. Ana (Fun f T) = (K,M) \<Longrightarrow> Ana (Fun f T \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>,M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
begin

lemma Ana_invar_subst'[simp]: "Ana_invar_subst \<S>"
using Ana_subst' unfolding Ana_invar_subst_def by force

definition pair where
  "pair d \<equiv> case d of (t,t') \<Rightarrow> Fun Pair [t,t']"

fun tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s::
  "(('fun,'var) term \<times> ('fun,'var) term) list \<Rightarrow>
   ('fun,'var) dbstatelist \<Rightarrow>
   (('fun,'var) term \<times> ('fun,'var) term) list list"
where
  "tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s [] D = [[]]"
| "tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) D =
    concat (map (\<lambda>d. map ((#) (pair (s,t), pair d)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)) D)"

text \<open>
  A translation/reduction \<open>tr\<close> from stateful constraints to (lists of) "non-stateful" constraints.
  The output represents a finite disjunction of constraints whose models constitute exactly the
  models of the input constraint. The typing result for "non-stateful" constraints is later lifted
  to the stateful setting through this reduction procedure.
\<close>
fun tr::"('fun,'var) stateful_strand \<Rightarrow> ('fun,'var) dbstatelist \<Rightarrow> ('fun,'var) strand list"
where
  "tr [] D = [[]]"
| "tr (send\<langle>t\<rangle>#A) D = map ((#) (send\<langle>t\<rangle>\<^sub>s\<^sub>t)) (tr A D)"
| "tr (receive\<langle>t\<rangle>#A) D = map ((#) (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)) (tr A D)"
| "tr (\<langle>ac: t \<doteq> t'\<rangle>#A) D = map ((#) (\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)) (tr A D)"
| "tr (insert\<langle>t,s\<rangle>#A) D = tr A (List.insert (t,s) D)"
| "tr (delete\<langle>t,s\<rangle>#A) D =
    concat (map (\<lambda>Di. map (\<lambda>B. (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
                               (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di])@B)
                          (tr A [d\<leftarrow>D. d \<notin> set Di]))
                (subseqs D))"
| "tr (\<langle>ac: t \<in> s\<rangle>#A) D =
    concat (map (\<lambda>B. map (\<lambda>d. \<langle>ac: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t#B) D) (tr A D))"
| "tr (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>#A) D =
    map ((@) (map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))) (tr A D)"

text \<open>Type-flaw resistance of stateful constraint steps\<close>
fun tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (Equality _ t t') = ((\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t')"
| "tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (NegChecks X F F') = (
    (F' = [] \<and> (\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F-set X. \<exists>a. \<Gamma> (Var x) = TAtom a)) \<or>
    (\<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') \<longrightarrow>
              T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X)))"
| "tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p _ = True"

text \<open>Type-flaw resistance of stateful constraints\<close>
definition tfr\<^sub>s\<^sub>s\<^sub>t where "tfr\<^sub>s\<^sub>s\<^sub>t S \<equiv> tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S) \<and> list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p S"


subsection \<open>Small Lemmata\<close>
lemma pair_in_pair_image_iff:
  "pair (s,t) \<in> pair ` P \<longleftrightarrow> (s,t) \<in> P"
unfolding pair_def by fast

lemma subst_apply_pairs_pair_image_subst:
  "pair ` set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) = pair ` set F \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
unfolding subst_apply_pairs_def pair_def by (induct F) auto

lemma Ana_subst_subterms_cases:
  fixes \<theta>::"('fun,'var) subst"
  assumes t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
    and s: "s \<in> set (snd (Ana t))"
  shows "(\<exists>u \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. t = u \<cdot> \<theta> \<and> s \<in> set (snd (Ana u)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<or> (\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. t \<sqsubseteq> \<theta> x)"
proof (cases "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>")
  case True
  then obtain u where u: "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t M" "t = u \<cdot> \<theta>" by moura
  show ?thesis
  proof (cases u)
    case (Var x)
    hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t M" using fv_subset_subterms[OF u(1)] by simp
    thus ?thesis using u(2) Var by fastforce
  next
    case (Fun f T)
    hence "set (snd (Ana t)) = set (snd (Ana u)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
      using Ana_subst'[of f T _ _ \<theta>] u(2) by (cases "Ana u") auto
    thus ?thesis using s u by blast
  qed
qed (use s t subterms\<^sub>s\<^sub>e\<^sub>t_subst in blast)

lemma tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_alt_def:
  "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p S =
    ((\<forall>ac t t'. Equality ac t t' \<in> set S \<and> (\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t') \<and>
     (\<forall>X F F'. NegChecks X F F' \<in> set S \<longrightarrow> (
        (F' = [] \<and> (\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F-set X. \<exists>a. \<Gamma> (Var x) = TAtom a)) \<or>
        (\<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') \<longrightarrow>
                  T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X)))))"
  (is "?P S = ?Q S")
proof
  show "?P S \<Longrightarrow> ?Q S"
  proof (induction S)
    case (Cons x S) thus ?case by (cases x) auto
  qed simp

  show "?Q S \<Longrightarrow> ?P S"
  proof (induction S)
    case (Cons x S) thus ?case by (cases x) auto
  qed simp
qed

lemma fun_pair_eq[dest]: "pair d = pair d' \<Longrightarrow> d = d'"
proof -
  obtain t s t' s' where "d = (t,s)" "d' = (t',s')" by moura
  thus "pair d = pair d' \<Longrightarrow> d = d'" unfolding pair_def by simp
qed

lemma fun_pair_subst: "pair d \<cdot> \<delta> = pair (d \<cdot>\<^sub>p \<delta>)"
using surj_pair[of d] unfolding pair_def by force  

lemma fun_pair_subst_set: "pair ` M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> = pair ` (M \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>)"
proof
  show "pair ` M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<subseteq> pair ` (M \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    using fun_pair_subst[of _ \<delta>] by fastforce

  show "pair ` (M \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>) \<subseteq> pair ` M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
  proof
    fix t assume t: "t \<in> pair ` (M \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta>)"
    then obtain p where p: "p \<in> M" "t = pair (p \<cdot>\<^sub>p \<delta>)" by blast
    thus "t \<in> pair ` M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>" using fun_pair_subst[of p \<delta>] by force
  qed
qed

lemma fun_pair_eq_subst: "pair d \<cdot> \<delta> = pair d' \<cdot> \<theta> \<longleftrightarrow> d \<cdot>\<^sub>p \<delta> = d' \<cdot>\<^sub>p \<theta>"
by (metis fun_pair_subst fun_pair_eq[of "d \<cdot>\<^sub>p \<delta>" "d' \<cdot>\<^sub>p \<theta>"])

lemma setops\<^sub>s\<^sub>s\<^sub>t_pair_image_cons[simp]:
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (x#S) = pair ` setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (send\<langle>t\<rangle>#S) = pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (receive\<langle>t\<rangle>#S) = pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (\<langle>ac: t \<doteq> t'\<rangle>#S) = pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (insert\<langle>t,s\<rangle>#S) = {pair (t,s)} \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (delete\<langle>t,s\<rangle>#S) = {pair (t,s)} \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (\<langle>ac: t \<in> s\<rangle>#S) = {pair (t,s)} \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>#S) = pair ` set G \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
unfolding setops\<^sub>s\<^sub>s\<^sub>t_def by auto

lemma setops\<^sub>s\<^sub>s\<^sub>t_pair_image_subst_cons[simp]:
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (x#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = pair ` setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (send\<langle>t\<rangle>#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (receive\<langle>t\<rangle>#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (\<langle>ac: t \<doteq> t'\<rangle>#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (insert\<langle>t,s\<rangle>#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = {pair (t,s) \<cdot> \<theta>} \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (delete\<langle>t,s\<rangle>#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = {pair (t,s) \<cdot> \<theta>} \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (\<langle>ac: t \<in> s\<rangle>#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) = {pair (t,s) \<cdot> \<theta>} \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  "pair ` setops\<^sub>s\<^sub>s\<^sub>t (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>#S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>) =
    pair ` set (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
using subst_sst_cons[of _ S \<theta>] unfolding setops\<^sub>s\<^sub>s\<^sub>t_def pair_def by auto

lemma setops\<^sub>s\<^sub>s\<^sub>t_are_pairs: "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<Longrightarrow> \<exists>s s'. t = pair (s,s')"
proof (induction A)
  case (Cons a A) thus ?case
    by (cases a) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma fun_pair_wf\<^sub>t\<^sub>r\<^sub>m: "wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m t' \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m (pair (t,t'))"
using Pair_arity unfolding wf\<^sub>t\<^sub>r\<^sub>m_def pair_def by auto

lemma wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_pairs: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (pair ` set F)"
using fun_pair_wf\<^sub>t\<^sub>r\<^sub>m by blast

lemma tfr\<^sub>s\<^sub>s\<^sub>t_Nil[simp]: "tfr\<^sub>s\<^sub>s\<^sub>t []"
by (simp add: tfr\<^sub>s\<^sub>s\<^sub>t_def setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma tfr\<^sub>s\<^sub>s\<^sub>t_append: "tfr\<^sub>s\<^sub>s\<^sub>t (A@B) \<Longrightarrow> tfr\<^sub>s\<^sub>s\<^sub>t A"
proof -
  assume assms: "tfr\<^sub>s\<^sub>s\<^sub>t (A@B)"
  let ?M = "trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A"
  let ?N = "trms\<^sub>s\<^sub>s\<^sub>t (A@B) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (A@B)"
  let ?P = "\<lambda>t t'. \<forall>x \<in> fv t \<union> fv t'. \<exists>a. \<Gamma> (Var x) = Var a"
  let ?Q = "\<lambda>X t t'. X = [] \<or> (\<forall>x \<in> (fv t \<union> fv t')-set X. \<exists>a. \<Gamma> (Var x) = Var a)"
  have *: "SMP ?M - Var`\<V> \<subseteq> SMP ?N - Var`\<V>" "?M \<subseteq> ?N"
    using SMP_mono[of ?M ?N] setops\<^sub>s\<^sub>s\<^sub>t_append[of A B]
    by auto
  { fix s t assume **: "tfr\<^sub>s\<^sub>e\<^sub>t ?N" "s \<in> SMP ?M - Var`\<V>" "t \<in> SMP ?M - Var`\<V>" "(\<exists>\<delta>. Unifier \<delta> s t)"
    hence "s \<in> SMP ?N - Var`\<V>" "t \<in> SMP ?N - Var`\<V>" using * by auto
    hence "\<Gamma> s = \<Gamma> t" using **(1,4) unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  } moreover have "\<forall>t \<in> ?N. wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> \<forall>t \<in> ?M. wf\<^sub>t\<^sub>r\<^sub>m t" using * by blast
  ultimately have "tfr\<^sub>s\<^sub>e\<^sub>t ?N \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t ?M" unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  hence "tfr\<^sub>s\<^sub>e\<^sub>t ?M" using assms unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by metis
  thus "tfr\<^sub>s\<^sub>s\<^sub>t A" using assms unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by simp
qed

lemma tfr\<^sub>s\<^sub>s\<^sub>t_append': "tfr\<^sub>s\<^sub>s\<^sub>t (A@B) \<Longrightarrow> tfr\<^sub>s\<^sub>s\<^sub>t B"
proof -
  assume assms: "tfr\<^sub>s\<^sub>s\<^sub>t (A@B)"
  let ?M = "trms\<^sub>s\<^sub>s\<^sub>t B \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t B"
  let ?N = "trms\<^sub>s\<^sub>s\<^sub>t (A@B) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (A@B)"
  let ?P = "\<lambda>t t'. \<forall>x \<in> fv t \<union> fv t'. \<exists>a. \<Gamma> (Var x) = Var a"
  let ?Q = "\<lambda>X t t'. X = [] \<or> (\<forall>x \<in> (fv t \<union> fv t')-set X. \<exists>a. \<Gamma> (Var x) = Var a)"
  have *: "SMP ?M - Var`\<V> \<subseteq> SMP ?N - Var`\<V>" "?M \<subseteq> ?N"
    using SMP_mono[of ?M ?N] setops\<^sub>s\<^sub>s\<^sub>t_append[of A B]
    by auto
  { fix s t assume **: "tfr\<^sub>s\<^sub>e\<^sub>t ?N" "s \<in> SMP ?M - Var`\<V>" "t \<in> SMP ?M - Var`\<V>" "(\<exists>\<delta>. Unifier \<delta> s t)"
    hence "s \<in> SMP ?N - Var`\<V>" "t \<in> SMP ?N - Var`\<V>" using * by auto
    hence "\<Gamma> s = \<Gamma> t" using **(1,4) unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  } moreover have "\<forall>t \<in> ?N. wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> \<forall>t \<in> ?M. wf\<^sub>t\<^sub>r\<^sub>m t" using * by blast
  ultimately have "tfr\<^sub>s\<^sub>e\<^sub>t ?N \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t ?M" unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  hence "tfr\<^sub>s\<^sub>e\<^sub>t ?M" using assms unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by metis
  thus "tfr\<^sub>s\<^sub>s\<^sub>t B" using assms unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by simp
qed

lemma tfr\<^sub>s\<^sub>s\<^sub>t_cons: "tfr\<^sub>s\<^sub>s\<^sub>t (a#A) \<Longrightarrow> tfr\<^sub>s\<^sub>s\<^sub>t A"
using tfr\<^sub>s\<^sub>s\<^sub>t_append'[of "[a]" A] by simp

lemma tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst:
  assumes s: "tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p s"
    and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s) \<inter> range_vars \<theta> = {}"
  shows "tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
proof (cases s)
  case (Equality a t t')
  thus ?thesis
  proof (cases "\<exists>\<delta>. Unifier \<delta> (t \<cdot> \<theta>) (t' \<cdot> \<theta>)")
    case True
    hence "\<exists>\<delta>. Unifier \<delta> t t'" by (metis subst_subst_compose[of _ \<theta>])
    moreover have "\<Gamma> t = \<Gamma> (t \<cdot> \<theta>)" "\<Gamma> t' = \<Gamma> (t' \<cdot> \<theta>)" by (metis wt_subst_trm''[OF assms(2)])+
    ultimately have "\<Gamma> (t \<cdot> \<theta>) = \<Gamma> (t' \<cdot> \<theta>)" using s Equality by simp
    thus ?thesis using Equality True by simp
  qed simp
next
  case (NegChecks X F G)
  let ?P = "\<lambda>F G. G = [] \<and> (\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F-set X. \<exists>a. \<Gamma> (Var x) = TAtom a)"
  let ?Q = "\<lambda>F G. \<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set G) \<longrightarrow>
                          T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X)"
  let ?\<theta> = "rm_vars (set X) \<theta>"

  have "?P F G \<or> ?Q F G" using NegChecks assms(1) by simp
  hence "?P (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) \<or> ?Q (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>)"
  proof
    assume *: "?P F G"
    have "G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta> = []" using * by simp
    moreover have "\<exists>a. \<Gamma> (Var x) = TAtom a" when x: "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) - set X" for x
    proof -
      obtain t t' where t: "(t,t') \<in> set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>)" "x \<in> fv t \<union> fv t' - set X"
        using x(1) by auto
      then obtain u u' where u: "(u,u') \<in> set F" "u \<cdot> ?\<theta> = t" "u' \<cdot> ?\<theta> = t'"
        unfolding subst_apply_pairs_def by auto
      obtain y where y: "y \<in> fv u \<union> fv u' - set X" "x \<in> fv (?\<theta> y)"
        using t(2) u(2,3) rm_vars_fv_obtain by fast
      hence a: "\<exists>a. \<Gamma> (Var y) = TAtom a" using u * by auto
      
      have a': "\<Gamma> (Var y) = \<Gamma> (?\<theta> y)"
        using wt_subst_trm''[OF wt_subst_rm_vars[OF \<theta>(1), of "set X"], of "Var y"]
        by simp

      have "(\<exists>z. ?\<theta> y = Var z) \<or> (\<exists>c. ?\<theta> y = Fun c [])"
      proof (cases "?\<theta> y \<in> subst_range \<theta>")
        case True thus ?thesis
          using a a' \<theta>(2) const_type_inv_wf
          by (cases "?\<theta> y") fastforce+
      qed fastforce
      hence "?\<theta> y = Var x" using y(2) by fastforce
      hence "\<Gamma> (Var x) = \<Gamma> (Var y)" using a' by simp
      thus ?thesis using a by presburger
    qed
    ultimately show ?thesis by simp
  next
    assume *: "?Q F G"
    have **: "set X \<inter> range_vars ?\<theta> = {}"
      using \<theta>(3) NegChecks rm_vars_img_fv_subset[of "set X" \<theta>] by auto
    have "?Q (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>) (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<theta>)"
      using ineq_subterm_inj_cond_subst[OF ** *]
            trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst[of F "rm_vars (set X) \<theta>"]
            subst_apply_pairs_pair_image_subst[of G "rm_vars (set X) \<theta>"]
      by (metis (no_types, lifting) image_Un)
    thus ?thesis by simp
  qed
  thus ?thesis using NegChecks by simp
qed simp_all

lemma tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_all_wt_subst_apply:
  assumes S: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p S"
    and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "bvars\<^sub>s\<^sub>s\<^sub>t S \<inter> range_vars \<theta> = {}"
  shows "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
proof -
  have "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s) \<inter> range_vars \<theta> = {}" when "s \<in> set S" for s
    using that \<theta>(3) unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def range_vars_alt_def by fastforce
  thus ?thesis
    using tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[OF _ \<theta>(1,2)] S
    unfolding list_all_iff
    by (auto simp add: subst_apply_stateful_strand_def)
qed

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_empty_case:
  assumes "tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D = []"
  shows "D = []" "F \<noteq> []"
proof -
  show "F \<noteq> []" using assms by (auto intro: ccontr)

  have "tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F (a#A) \<noteq> []" for a A
    by (induct F "a#A" rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct) fastforce+
  thus "D = []" using assms by (cases D) simp_all
qed

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_elem_length_eq:
  assumes "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)"
  shows "length G = length F" 
using assms by (induct F D arbitrary: G rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct) auto

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_index:
  assumes "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)" "i < length F"
  shows "\<exists>d \<in> set D. G ! i = (pair (F ! i), pair d)"
using assms
proof (induction F D arbitrary: i G rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
  case (2 s t F D)
  obtain d G' where G:
      "d \<in> set D" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)"
      "G = (pair (s,t), pair d)#G'"
    using "2.prems"(1) by moura
  show ?case
    using "2.IH"[OF G(1,2)] "2.prems"(2) G(1,3)
    by (cases i) auto
qed simp

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_cons:
  assumes "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)" "d \<in> set D"
  shows "(pair (s,t), pair d)#G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) D)"
using assms by auto

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_has_pair_lists:
  assumes "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)" "g \<in> set G"
  shows "\<exists>f \<in> set F. \<exists>d \<in> set D. g = (pair f, pair d)"
using assms
proof (induction F D arbitrary: G rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
  case (2 s t F D)
  obtain d G' where G:
      "d \<in> set D" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)"
      "G = (pair (s,t), pair d)#G'"
    using "2.prems"(1) by moura
  show ?case
    using "2.IH"[OF G(1,2)] "2.prems"(2) G(1,3)
    by (cases "g \<in> set G'") auto
qed simp

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_pair_lists:
  assumes "f \<in> set F" "d \<in> set D"
  shows "\<exists>G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D). (pair f, pair d) \<in> set G"
  (is "?P F D f d")
proof -
  have "\<forall>f \<in> set F. \<forall>d \<in> set D. ?P F D f d"
  proof (induction F D rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
    case (2 s t F D)
    hence IH: "\<forall>f \<in> set F. \<forall>d \<in> set D. ?P F D f d" by metis
    moreover have "\<forall>d \<in> set D. ?P ((s,t)#F) D (s,t) d"
    proof
      fix d assume d: "d \<in> set D"
      then obtain G where G: "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)"
        using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_empty_case(1) by force
      hence "(pair (s, t), pair d)#G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) D)"
        using d by auto
      thus "?P ((s,t)#F) D (s,t) d" using d G by auto
    qed
    ultimately show ?case by fastforce
  qed simp
  thus ?thesis by (metis assms)
qed

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_db_append_subset:
  "set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D) \<subseteq> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F (D@E))" (is ?A)
  "set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F E) \<subseteq> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F (D@E))" (is ?B)
proof -
  show ?A
  proof (induction F D rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
    case (2 s t F D)
    show ?case
    proof
      fix G assume "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) D)"
      then obtain d G' where G':
          "d \<in> set D" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)" "G = (pair (s,t), pair d)#G'"
        by moura
      have "d \<in> set (D@E)" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F (D@E))" using "2.IH"[OF G'(1)] G'(1,2) by auto
      thus "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) (D@E))" using G'(3) by auto
    qed
  qed simp

  show ?B
  proof (induction F E rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
    case (2 s t F E)
    show ?case
    proof
      fix G assume "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) E)"
      then obtain d G' where G':
          "d \<in> set E" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F E)" "G = (pair (s,t), pair d)#G'"
        by moura
      have "d \<in> set (D@E)" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F (D@E))" using "2.IH"[OF G'(1)] G'(1,2) by auto
      thus "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) (D@E))" using G'(3) by auto
    qed
  qed simp
qed

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_trms_subset:
  "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D) \<Longrightarrow> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<subseteq> pair ` set F \<union> pair ` set D"
proof (induction F D arbitrary: G rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
  case (2 s t F D G)
  obtain d G' where G:
      "d \<in> set D" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)" "G = (pair (s,t), pair d)#G'"
    using "2.prems"(1) by moura
 
  show ?case using "2.IH"[OF G(1,2)] G(1,3) by auto
qed simp

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_trms_subset':
  "\<Union>(trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ` set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)) \<subseteq> pair ` set F \<union> pair ` set D"
using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_trms_subset by blast

lemma tr_trms_subset:
  "A' \<in> set (tr A D) \<Longrightarrow> trms\<^sub>s\<^sub>t A' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D"
proof (induction A D arbitrary: A' rule: tr.induct)
  case 1 thus ?case by simp
next
  case (2 t A D)
  then obtain A'' where A'': "A' = send\<langle>t\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)" by moura
  hence "trms\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D" by (metis "2.IH")
  thus ?case using A'' by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (3 t A D)
  then obtain A'' where A'': "A' = receive\<langle>t\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)" by moura
  hence "trms\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D" by (metis "3.IH")
  thus ?case using A'' by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (4 ac t t' A D)
  then obtain A'' where A'': "A' = \<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)" by moura
  hence "trms\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D" by (metis "4.IH")
  thus ?case using A'' by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (5 t s A D)
  hence "A' \<in> set (tr A (List.insert (t,s) D))" by simp
  hence "trms\<^sub>s\<^sub>t A' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set (List.insert (t, s) D)"
    by (metis "5.IH")
  thus ?case by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (6 t s A D)
  from 6 obtain Di A'' B C where A'':
      "Di \<in> set (subseqs D)" "A'' \<in> set (tr A [d\<leftarrow>D. d \<notin> set Di])" "A' = (B@C)@A''"
      "B = map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di"
      "C = map (\<lambda>d. Inequality [] [(pair (t,s) , pair d)]) [d\<leftarrow>D. d \<notin> set Di]"
    by moura
  hence "trms\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set [d\<leftarrow>D. d \<notin> set Di]"
    by (metis "6.IH")
  hence "trms\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (Delete t s#A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (Delete t s#A) \<union> pair ` set D"
    by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  moreover have "trms\<^sub>s\<^sub>t (B@C) \<subseteq> insert (pair (t,s)) (pair ` set D)"
    using A''(4,5) subseqs_set_subset[OF A''(1)] by auto
  moreover have "pair (t,s) \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (Delete t s#A)" by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  ultimately show ?case using A''(3) trms\<^sub>s\<^sub>t_append[of "B@C" A'] by auto
next
  case (7 ac t s A D)
  from 7 obtain d A'' where A'':
      "d \<in> set D" "A'' \<in> set (tr A D)"
      "A' = \<langle>ac: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t#A''"
    by moura
  hence "trms\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D" by (metis "7.IH")
  moreover have "trms\<^sub>s\<^sub>t A' = {pair (t,s), pair d} \<union> trms\<^sub>s\<^sub>t A''"
    using A''(1,3) by auto
  ultimately show ?case using A''(1) by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (8 X F F' A D)
  from 8 obtain A'' where A'':
      "A'' \<in> set (tr A D)" "A' = (map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))@A''"
    by moura

  define B where "B \<equiv> \<Union>(trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ` set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))"

  have "trms\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D" by (metis A''(1) "8.IH")
  hence "trms\<^sub>s\<^sub>t A' \<subseteq> B \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D"
    using A'' B_def by auto
  moreover have "B \<subseteq> pair ` set F' \<union> pair ` set D"
    using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_trms_subset'[of F' D] B_def by simp
  moreover have "pair ` setops\<^sub>s\<^sub>s\<^sub>t (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>#A) = pair ` set F' \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A"
    by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  ultimately show ?case by auto
qed

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_vars_subset:
  "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D) \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s D"
proof (induction F D arbitrary: G rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
  case (2 s t F D G)
  obtain d G' where G:
      "d \<in> set D" "G' \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)" "G = (pair (s,t), pair d)#G'"
    using "2.prems"(1) by moura
 
  show ?case using "2.IH"[OF G(1,2)] G(1,3) unfolding pair_def by auto
qed simp

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_vars_subset': "\<Union>(fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ` set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F D)) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s D"
using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_vars_subset[of _ F D] by blast

lemma tr_vars_subset:
  assumes "A' \<in> set (tr A D)"
  shows "fv\<^sub>s\<^sub>t A' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t A \<union> (\<Union>(t,t') \<in> set D. fv t \<union> fv t')" (is ?P)
  and "bvars\<^sub>s\<^sub>t A' \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t A" (is ?Q)
proof -
  show ?P using assms
  proof (induction A arbitrary: A' D rule: strand_sem_stateful_induct)
    case (ConsIn A' D ac t s A)
    then obtain A'' d where *:
        "d \<in> set D" "A' = \<langle>ac: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t#A''"
        "A'' \<in> set (tr A D)"
      by moura
    hence "fv\<^sub>s\<^sub>t A'' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t A \<union> (\<Union>(t,t')\<in>set D. fv t \<union> fv t')" by (metis ConsIn.IH)
    thus ?case using * unfolding pair_def by auto
  next
    case (ConsDel A' D t s A)
    define Dfv where "Dfv \<equiv> \<lambda>D::('fun,'var) dbstatelist. (\<Union>(t,t')\<in>set D. fv t \<union> fv t')"
    define fltD where "fltD \<equiv> \<lambda>Di. filter (\<lambda>d. d \<notin> set Di) D"
    define constr where
      "constr \<equiv> \<lambda>Di. (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
                      (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) (fltD Di))"
    from ConsDel obtain A'' Di where *:
        "Di \<in> set (subseqs D)" "A' = (constr Di)@A''" "A'' \<in> set (tr A (fltD Di))"
      unfolding constr_def fltD_def by moura
    hence "fv\<^sub>s\<^sub>t A'' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t A \<union> Dfv (fltD Di)"
      unfolding Dfv_def constr_def fltD_def by (metis ConsDel.IH)
    moreover have "Dfv (fltD Di) \<subseteq> Dfv D" unfolding Dfv_def constr_def fltD_def by auto
    moreover have "Dfv Di \<subseteq> Dfv D"
      using subseqs_set_subset(1)[OF *(1)] unfolding Dfv_def constr_def fltD_def by fast
    moreover have "fv\<^sub>s\<^sub>t (constr Di) \<subseteq> fv t \<union> fv s \<union> (Dfv Di \<union> Dfv (fltD Di))"
      unfolding Dfv_def constr_def fltD_def pair_def by auto
    moreover have "fv\<^sub>s\<^sub>s\<^sub>t (Delete t s#A) = fv t \<union> fv s \<union> fv\<^sub>s\<^sub>s\<^sub>t A" by auto
    moreover have "fv\<^sub>s\<^sub>t A' = fv\<^sub>s\<^sub>t (constr Di) \<union> fv\<^sub>s\<^sub>t A''" using * by force
    ultimately have "fv\<^sub>s\<^sub>t A' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (Delete t s#A) \<union> Dfv D" by auto
    thus ?case unfolding Dfv_def fltD_def constr_def by simp
  next
    case (ConsNegChecks A' D X F F' A)
    then obtain A'' where A'':
        "A'' \<in> set (tr A D)" "A' = (map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))@A''"
      by moura

    define B where "B \<equiv> \<Union>(fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ` set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))"

    have 1: "fv\<^sub>s\<^sub>t (map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D)) \<subseteq> (B \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X"
      unfolding B_def by auto

    have 2: "B \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s D"
      using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_vars_subset'[of F' D]
      unfolding B_def by simp

    have "fv\<^sub>s\<^sub>t A' \<subseteq> ((fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s D \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X) \<union> fv\<^sub>s\<^sub>t A''"
      using 1 2 A''(2) by fastforce
    thus ?case using ConsNegChecks.IH[OF A''(1)] by auto
  qed fastforce+

  show ?Q using assms by (induct A arbitrary: A' D rule: strand_sem_stateful_induct) fastforce+
qed

lemma tr_vars_disj:
  assumes "A' \<in> set (tr A D)" "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
  and "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
  shows "fv\<^sub>s\<^sub>t A' \<inter> bvars\<^sub>s\<^sub>t A' = {}"
  using assms tr_vars_subset by fast

lemma wf_fun_pair_ineqs_map:
  assumes "wf\<^sub>s\<^sub>t X A"
  shows "wf\<^sub>s\<^sub>t X (map (\<lambda>d. \<forall>Y\<langle>\<or>\<noteq>: [(pair (t, s), pair d)]\<rangle>\<^sub>s\<^sub>t) D@A)"
using assms by (induct D) auto

lemma wf_fun_pair_negchecks_map:
  assumes "wf\<^sub>s\<^sub>t X A"
  shows "wf\<^sub>s\<^sub>t X (map (\<lambda>G. \<forall>Y\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) M@A)"
using assms by (induct M) auto

lemma wf_fun_pair_eqs_ineqs_map:
  fixes A::"('fun,'var) strand"
  assumes "wf\<^sub>s\<^sub>t X A" "Di \<in> set (subseqs D)" "\<forall>(t,t') \<in> set D. fv t \<union> fv t' \<subseteq> X"
  shows "wf\<^sub>s\<^sub>t X ((map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
                 (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di])@A)"
proof -
  let ?c1 = "map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di"
  let ?c2 = "map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]"
  have 1: "wf\<^sub>s\<^sub>t X (?c2@A)" using wf_fun_pair_ineqs_map[OF assms(1)] by simp
  have 2: "\<forall>(t,t') \<in> set Di. fv t \<union> fv t' \<subseteq> X" 
    using assms(2,3) by (meson contra_subsetD subseqs_set_subset(1))
  have "wf\<^sub>s\<^sub>t X (?c1@B)" when "wf\<^sub>s\<^sub>t X B" for B::"('fun,'var) strand"
    using 2 that by (induct Di) auto
  thus ?thesis using 1 by simp
qed

lemma trms\<^sub>s\<^sub>s\<^sub>t_wt_subst_ex:
  assumes \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    and t: "t \<in> trms\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  shows "\<exists>s \<delta>. s \<in> trms\<^sub>s\<^sub>s\<^sub>t S \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = s \<cdot> \<delta>"
using t
proof (induction S)
  case (Cons s S) thus ?case
  proof (cases "t \<in> trms\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)")
    case False
    hence "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"
      using Cons.prems trms\<^sub>s\<^sub>s\<^sub>t_subst_cons[of s S \<theta>]
      by auto
    then obtain u where u: "u \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p s" "t = u \<cdot> rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s)) \<theta>"
      using trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst'' by blast
    thus ?thesis
      using trms\<^sub>s\<^sub>s\<^sub>t_subst_cons[of s S \<theta>]
            wt_subst_rm_vars[OF \<theta>(1), of "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s)"]
            wf_trms_subst_rm_vars'[OF \<theta>(2), of "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p s)"]
      by fastforce
  qed auto
qed simp

lemma setops\<^sub>s\<^sub>s\<^sub>t_wt_subst_ex:
  assumes \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    and t: "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  shows "\<exists>s \<delta>. s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = s \<cdot> \<delta>"
using t
proof (induction S)
  case (Cons x S) thus ?case
  proof (cases x)
    case (Insert t' s)
    hence "t = pair (t',s) \<cdot> \<theta> \<or> t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
      using Cons.prems subst_sst_cons[of _ S \<theta>]
      unfolding pair_def by (force simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    thus ?thesis
      using Insert Cons.IH \<theta> by (cases "t = pair (t', s) \<cdot> \<theta>") (fastforce, auto)
  next
    case (Delete t' s)
    hence "t = pair (t',s) \<cdot> \<theta> \<or> t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
      using Cons.prems subst_sst_cons[of _ S \<theta>]
      unfolding pair_def by (force simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    thus ?thesis
      using Delete Cons.IH \<theta> by (cases "t = pair (t', s) \<cdot> \<theta>") (fastforce, auto)
  next
    case (InSet ac t' s)
    hence "t = pair (t',s) \<cdot> \<theta> \<or> t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
      using Cons.prems subst_sst_cons[of _ S \<theta>]
      unfolding pair_def by (force simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    thus ?thesis
      using InSet Cons.IH \<theta> by (cases "t = pair (t', s) \<cdot> \<theta>") (fastforce, auto)
  next
    case (NegChecks X F F')
    hence "t \<in> pair ` set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>) \<or> t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<theta>)"
      using Cons.prems subst_sst_cons[of _ S \<theta>]
      unfolding pair_def by (force simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    thus ?thesis
    proof
      assume "t \<in> pair ` set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)"
      then obtain s where s: "t = s \<cdot> rm_vars (set X) \<theta>" "s \<in> pair ` set F'"
        using subst_apply_pairs_pair_image_subst[of F' "rm_vars (set X) \<theta>"] by auto
      thus ?thesis
        using NegChecks setops\<^sub>s\<^sub>s\<^sub>t_pair_image_cons(8)[of X F F' S]
              wt_subst_rm_vars[OF \<theta>(1), of "set X"]
              wf_trms_subst_rm_vars'[OF \<theta>(2), of "set X"]
        by fast
    qed (use Cons.IH in auto)
  qed (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def subst_sst_cons[of _ S \<theta>])
qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s:
  "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (pair ` setops\<^sub>s\<^sub>s\<^sub>t A)"
  "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A)"
proof -
  show "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (pair ` setops\<^sub>s\<^sub>s\<^sub>t A)"
  proof (induction A)
    case (Cons a A)
    hence 0: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p a)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (pair ` setops\<^sub>s\<^sub>s\<^sub>t A)" by auto
    thus ?case
    proof (cases a)
      case (NegChecks X F F')
      hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F')" using 0 by simp
      thus ?thesis using NegChecks wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_pairs[of F'] 0 by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    qed (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def dest: fun_pair_wf\<^sub>t\<^sub>r\<^sub>m)
  qed (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  thus "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A)" by fast
qed

lemma SMP_MP_split:
  assumes "t \<in> SMP M"
    and M: "\<forall>m \<in> M. is_Fun m"
  shows "(\<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<or>
         t \<in> SMP ((subterms\<^sub>s\<^sub>e\<^sub>t M \<union> \<Union>((set \<circ> fst \<circ> Ana) ` M)) - M)"
  (is "?P t \<or> ?Q t")
using assms(1)
proof (induction t rule: SMP.induct)
  case (MP t)
  have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)" "M \<cdot>\<^sub>s\<^sub>e\<^sub>t Var = M" by simp_all
  thus ?case using MP by metis
next
  case (Subterm t t')
  show ?case using Subterm.IH
  proof
    assume "?P t"
    then obtain s \<delta> where s: "s \<in> M" "t = s \<cdot> \<delta>" and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" by moura
    then obtain f T where fT: "s = Fun f T" using M by fast

    have "(\<exists>s'. s' \<sqsubseteq> s \<and> t' = s' \<cdot> \<delta>) \<or> (\<exists>x \<in> fv s. t' \<sqsubset> \<delta> x)"
      using subterm_subst_unfold[OF Subterm.hyps(2)[unfolded s(2)]] by blast
    thus ?thesis
    proof
      assume "\<exists>s'. s' \<sqsubseteq> s \<and> t' = s' \<cdot> \<delta>"
      then obtain s' where s': "s' \<sqsubseteq> s" "t' = s' \<cdot> \<delta>" by moura
      show ?thesis
      proof (cases "s' \<in> M")
        case True thus ?thesis using s' \<delta> by blast
      next
        case False
        hence "s' \<in> (subterms\<^sub>s\<^sub>e\<^sub>t M \<union> \<Union>((set \<circ> fst \<circ> Ana) ` M)) - M" using s'(1) s(1) by force
        thus ?thesis using SMP.Substitution[OF SMP.MP[of s'] \<delta>] s' by presburger
      qed
    next
      assume "\<exists>x \<in> fv s. t' \<sqsubset> \<delta> x"
      then obtain x where x: "x \<in> fv s" "t' \<sqsubset> \<delta> x" by moura
      have "Var x \<notin> M" using M by blast
      hence "Var x \<in> (subterms\<^sub>s\<^sub>e\<^sub>t M \<union> \<Union>((set \<circ> fst \<circ> Ana) ` M)) - M"
        using s(1) var_is_subterm[OF x(1)] by blast
      hence "\<delta> x \<in> SMP ((subterms\<^sub>s\<^sub>e\<^sub>t M \<union> \<Union>((set \<circ> fst \<circ> Ana) ` M)) - M)"
        using SMP.Substitution[OF SMP.MP[of "Var x"] \<delta>] by auto
      thus ?thesis using SMP.Subterm x(2) by presburger
    qed
  qed (metis SMP.Subterm[OF _ Subterm.hyps(2)])
next
  case (Substitution t \<delta>)
  show ?case using Substitution.IH
  proof
    assume "?P t"
    then obtain \<theta> where "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "t \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" by moura
    hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<delta>))" "t \<cdot> \<delta> \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>)"
      using wt_subst_compose[of \<theta>, OF _ Substitution.hyps(2)]
            wf_trm_subst_compose[of \<theta> _ \<delta>, OF _ wf_trm_subst_rangeD[OF Substitution.hyps(3)]]
            wf_trm_subst_range_iff
      by (argo, blast, auto)
    thus ?thesis by blast
  next
    assume "?Q t" thus ?thesis using SMP.Substitution[OF _ Substitution.hyps(2,3)] by meson
  qed
next
  case (Ana t K T k)
  show ?case using Ana.IH
  proof
    assume "?P t"
    then obtain \<theta> where \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "t \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" by moura
    then obtain s where s: "s \<in> M" "t = s \<cdot> \<theta>" by auto
    then obtain f S where fT: "s = Fun f S" using M by (cases s) auto
    obtain K' T' where s_Ana: "Ana s = (K', T')" by (metis surj_pair)
    hence "set K = set K' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" "set T = set T' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
      using Ana_subst'[of f S K' T'] fT Ana.hyps(2) s(2) by auto
    then obtain k' where k': "k' \<in> set K'" "k = k' \<cdot> \<theta>" using Ana.hyps(3) by fast
    show ?thesis
    proof (cases "k' \<in> M")
      case True thus ?thesis using k' \<theta>(1,2) by blast
    next
      case False
      hence "k' \<in> (subterms\<^sub>s\<^sub>e\<^sub>t M \<union> \<Union>((set \<circ> fst \<circ> Ana) ` M)) - M" using k'(1) s_Ana s(1) by force
      thus ?thesis using SMP.Substitution[OF SMP.MP[of k'] \<theta>(1,2)] k'(2) by presburger
    qed
  next
    assume "?Q t" thus ?thesis using SMP.Ana[OF _ Ana.hyps(2,3)] by meson
  qed
qed

lemma setops_subterm_trms:
  assumes t: "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
    and s: "s \<sqsubset> t"
  shows "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)"
proof -
  obtain u u' where u: "pair (u,u') \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S" "t = pair (u,u')"
    using t setops\<^sub>s\<^sub>s\<^sub>t_are_pairs[of _ S] by blast
  hence "s \<sqsubseteq> u \<or> s \<sqsubseteq> u'" using s unfolding pair_def by auto
  thus ?thesis using u setops\<^sub>s\<^sub>s\<^sub>t_member_iff[of u u' S] unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by force
qed

lemma setops_subterms_cases:
  assumes t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (pair ` setops\<^sub>s\<^sub>s\<^sub>t S)"
  shows "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S) \<or> t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S"
proof -
  obtain s s' where s: "pair (s,s') \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S" "t \<sqsubseteq> pair (s,s')"
    using t setops\<^sub>s\<^sub>s\<^sub>t_are_pairs[of _ S] by blast
  hence "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S \<or> t \<sqsubseteq> s \<or> t \<sqsubseteq> s'" unfolding pair_def by auto
  thus ?thesis using s setops\<^sub>s\<^sub>s\<^sub>t_member_iff[of s s' S] unfolding trms\<^sub>s\<^sub>s\<^sub>t_def by force
qed

lemma setops_SMP_cases:
  assumes "t \<in> SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t S)"
    and "\<forall>p. Ana (pair p) = ([], [])"
  shows "(\<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<or> t \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S)"
proof -
  have 0: "\<Union>((set \<circ> fst \<circ> Ana) ` pair ` setops\<^sub>s\<^sub>s\<^sub>t S) = {}"
  proof (induction S)
    case (Cons x S) thus ?case
      using assms(2) by (cases x) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  
  have 1: "\<forall>m \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S. is_Fun m"
  proof (induction S)
    case (Cons x S) thus ?case
      unfolding pair_def by (cases x) (auto simp add: assms(2) setops\<^sub>s\<^sub>s\<^sub>t_def)
  qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

  have 2:
      "subterms\<^sub>s\<^sub>e\<^sub>t (pair ` setops\<^sub>s\<^sub>s\<^sub>t S) \<union>
       \<Union>((set \<circ> fst \<circ> Ana) ` (pair ` setops\<^sub>s\<^sub>s\<^sub>t S)) - pair ` setops\<^sub>s\<^sub>s\<^sub>t S
        \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)"
    using 0 setops_subterms_cases by fast

  show ?thesis
    using SMP_MP_split[OF assms(1) 1] SMP_mono[OF 2] SMP_subterms_eq[of "trms\<^sub>s\<^sub>s\<^sub>t S"]
    by blast
qed

lemma tfr_setops_if_tfr_trms:
  assumes "Pair \<notin> \<Union>(funs_term ` SMP (trms\<^sub>s\<^sub>s\<^sub>t S))"
    and "\<forall>p. Ana (pair p) = ([], [])"
    and "\<forall>s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S. \<forall>t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S. (\<exists>\<delta>. Unifier \<delta> s t) \<longrightarrow> \<Gamma> s = \<Gamma> t"
    and "\<forall>s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S. \<forall>t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S.
          (\<exists>\<sigma> \<theta> \<rho>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>) \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<and>
                   Unifier \<rho> (s \<cdot> \<sigma>) (t \<cdot> \<theta>))
          \<longrightarrow> (\<exists>\<delta>. Unifier \<delta> s t)"
    and tfr: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S)"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S)"
proof -
  have 0: "t \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var \<or> t \<in> SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t S) - range Var"
    when "t \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S) - range Var" for t
    using that SMP_union by blast

  have 1: "s \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var"
      when st: "s \<in> SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t S) - range Var"
               "t \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var"
               "\<exists>\<delta>. Unifier \<delta> s t"
         for s t
  proof -
    have "(\<exists>\<delta>. s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<or> s \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var"
      using st setops_SMP_cases[of s S] assms(2) by blast
    moreover {
      fix \<delta> assume \<delta>: "s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
      then obtain s' where s': "s' \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S" "s = s' \<cdot> \<delta>" by blast
      then obtain u u' where u: "s' = Fun Pair [u,u']"
        using setops\<^sub>s\<^sub>s\<^sub>t_are_pairs[of s'] unfolding pair_def by fast
      hence *: "s = Fun Pair [u \<cdot> \<delta>, u' \<cdot> \<delta>]" using \<delta> s' by simp

      obtain f T where fT: "t = Fun f T" using st(2) by (cases t) auto
      hence "f \<noteq> Pair" using st(2) assms(1) by auto
      hence False using st(3) * fT s' u by fast
    } ultimately show ?thesis by meson
  qed
  
  have 2: "\<Gamma> s = \<Gamma> t"
      when "s \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var"
           "t \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var"
           "\<exists>\<delta>. Unifier \<delta> s t"
       for s t
    using that tfr unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  
  have 3: "\<Gamma> s = \<Gamma> t"
      when st: "s \<in> SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t S) - range Var"
               "t \<in> SMP (pair ` setops\<^sub>s\<^sub>s\<^sub>t S) - range Var"
               "\<exists>\<delta>. Unifier \<delta> s t"
      for s t
  proof -
    let ?P = "\<lambda>s \<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> s \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
    have "(\<exists>\<delta>. ?P s \<delta>) \<or> s \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var"
         "(\<exists>\<delta>. ?P t \<delta>) \<or> t \<in> SMP (trms\<^sub>s\<^sub>s\<^sub>t S) - range Var"
      using setops_SMP_cases[of _ S] assms(2) st(1,2) by auto
    hence "(\<exists>\<delta> \<delta>'. ?P s \<delta> \<and> ?P t \<delta>') \<or> \<Gamma> s = \<Gamma> t" by (metis 1 2 st)
    moreover {
      fix \<delta> \<delta>' assume *: "?P s \<delta>" "?P t \<delta>'"
      then obtain s' t' where **:
          "s' \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S" "t' \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t S" "s = s' \<cdot> \<delta>" "t = t' \<cdot> \<delta>'"
        by blast
      hence "\<exists>\<theta>. Unifier \<theta> s' t'" using st(3) assms(4) * by blast
      hence "\<Gamma> s' = \<Gamma> t'" using assms(3) ** by blast
      hence "\<Gamma> s = \<Gamma> t" using * **(3,4) wt_subst_trm''[of \<delta> s'] wt_subst_trm''[of \<delta>' t'] by argo
    } ultimately show ?thesis by blast
  qed
  
  show ?thesis using 0 1 2 3 unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by metis
qed


subsection \<open>The Typing Result for Stateful Constraints\<close>
context
begin
private lemma tr_wf':
  assumes "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
  and "\<forall>(t,t') \<in> set D. fv t \<union> fv t' \<subseteq> X"
  and "wf'\<^sub>s\<^sub>s\<^sub>t X A" "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
  and "A' \<in> set (tr A D)"
  shows "wf\<^sub>s\<^sub>t X A'"
proof -
  define P where
    "P = (\<lambda>(D::('fun,'var) dbstatelist) (A::('fun,'var) stateful_strand).
          (\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}) \<and> fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {})"

  have "P D A" using assms(1,4) by (simp add: P_def)
  with assms(5,3,2) show ?thesis
  proof (induction A arbitrary: A' D X rule: wf'\<^sub>s\<^sub>s\<^sub>t.induct)
    case 1 thus ?case by simp
  next
    case (2 X t A A')
    then obtain A'' where A'': "A' = receive\<langle>t\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)" "fv t \<subseteq> X"
      by moura
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t X A" "\<forall>(s,s') \<in> set D. fv s \<union> fv s' \<subseteq> X" "P D A"
      using 2(1,2,3,4) apply (force, force)
      using 2(5) unfolding P_def by force
    show ?case using "2.IH"[OF A''(2) *] A''(1,3) by simp
  next
    case (3 X t A A')
    then obtain A'' where A'': "A' = send\<langle>t\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)"
      by moura
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t (X \<union> fv t) A" "\<forall>(s,s') \<in> set D. fv s \<union> fv s' \<subseteq> X \<union> fv t" "P D A"
      using 3(1,2,3,4) apply (force, force)
      using 3(5) unfolding P_def by force
    show ?case using "3.IH"[OF A''(2) *] A''(1) by simp
  next
    case (4 X t t' A A')
    then obtain A'' where A'': "A' = \<langle>assign: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)" "fv t' \<subseteq> X"
      by moura
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t (X \<union> fv t) A" "\<forall>(s,s') \<in> set D. fv s \<union> fv s' \<subseteq> X \<union> fv t" "P D A"
      using 4(1,2,3,4) apply (force, force)
      using 4(5) unfolding P_def by force
    show ?case using "4.IH"[OF A''(2) *] A''(1,3) by simp
  next
    case (5 X t t' A A')
    then obtain A'' where A'': "A' = \<langle>check: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)"
      by moura
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t X A" "P D A"
      using 5(3) apply force
      using 5(5) unfolding P_def by force
    show ?case using "5.IH"[OF A''(2) *(1) 5(4) *(2)] A''(1) by simp
  next
    case (6 X t s A A')
    hence A': "A' \<in> set (tr A (List.insert (t,s) D))" "fv t \<subseteq> X" "fv s \<subseteq> X" by auto
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t X A" "\<forall>(s,s') \<in> set (List.insert (t,s) D). fv s \<union> fv s' \<subseteq> X" using 6 by auto
    have **: "P (List.insert (t,s) D) A" using 6(5) unfolding P_def by force
    show ?case using "6.IH"[OF A'(1) * **] A'(2,3) by simp
  next
    case (7 X t s A A')
    let ?constr = "\<lambda>Di. (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
                        (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di])"
    from 7 obtain Di A'' where A'':
        "A' = ?constr Di@A''" "A'' \<in> set (tr A [d\<leftarrow>D. d \<notin> set Di])"
        "Di \<in> set (subseqs D)"
      by moura
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t X A" "\<forall>(t',s') \<in> set [d\<leftarrow>D. d \<notin> set Di]. fv t' \<union> fv s' \<subseteq> X"
      using 7 by auto
    have **: "P [d\<leftarrow>D. d \<notin> set Di] A" using 7 unfolding P_def by force
    have ***: "\<forall>(t, t') \<in> set D. fv t \<union> fv t' \<subseteq> X" using 7 by auto
    show ?case
      using "7.IH"[OF A''(2) * **] A''(1) wf_fun_pair_eqs_ineqs_map[OF _ A''(3) ***]
      by simp
  next
    case (8 X t s A A')
    then obtain d A'' where A'':
        "A' = \<langle>assign: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t#A''"
        "A'' \<in> set (tr A D)" "d \<in> set D"
      by moura
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t (X \<union> fv t \<union> fv s) A" "\<forall>(t',s')\<in>set D. fv t' \<union> fv s' \<subseteq> X \<union> fv t \<union> fv s" "P D A"
      using 8(1,2,3,4) apply (force, force)
      using 8(5) unfolding P_def by force
    have **: "fv (pair d) \<subseteq> X" using A''(3) "8.prems"(3) unfolding pair_def by fastforce
    have ***: "fv (pair (t,s)) = fv s \<union> fv t" unfolding pair_def by auto
    show ?case using "8.IH"[OF A''(2) *] A''(1) ** *** unfolding pair_def by (simp add: Un_assoc)
  next
    case (9 X t s A A')
    then obtain d A'' where A'':
        "A' = \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t#A''"
        "A'' \<in> set (tr A D)" "d \<in> set D"
      by moura
    have *: "wf'\<^sub>s\<^sub>s\<^sub>t X A""P D A"
      using 9(3) apply force
      using 9(5) unfolding P_def by force
    have **: "fv (pair d) \<subseteq> X" using A''(3) "9.prems"(3) unfolding pair_def by fastforce
    have ***: "fv (pair (t,s)) = fv s \<union> fv t" unfolding pair_def by auto
    show ?case using "9.IH"[OF A''(2) *(1) 9(4) *(2)] A''(1) ** *** by (simp add: Un_assoc)
  next
    case (10 X Y F F' A A')
    from 10 obtain A'' where A'':
        "A' = (map (\<lambda>G. \<forall>Y\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))@A''" "A'' \<in> set (tr A D)"
      by moura

    have *: "wf'\<^sub>s\<^sub>s\<^sub>t X A" "\<forall>(t',s') \<in> set D. fv t' \<union> fv s' \<subseteq> X" using 10 by auto
    
    have "bvars\<^sub>s\<^sub>s\<^sub>t A \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (\<forall>Y\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>#A)" "fv\<^sub>s\<^sub>s\<^sub>t A \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (\<forall>Y\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>#A)" by auto
    hence **:  "P D A" using 10 unfolding P_def by blast

    show ?case using "10.IH"[OF A''(2) * **] A''(1) wf_fun_pair_negchecks_map by simp
  qed
qed

private lemma tr_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s:
  assumes "A' \<in> set (tr A [])" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t A')"
using tr_trms_subset[OF assms(1)] setops\<^sub>s\<^sub>s\<^sub>t_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s(2)[OF assms(2)]
by auto

lemma tr_wf:
  assumes "A' \<in> set (tr A [])"
    and "wf\<^sub>s\<^sub>s\<^sub>t A"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t A)" 
  shows "wf\<^sub>s\<^sub>t {} A'"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t A')"
    and "fv\<^sub>s\<^sub>t A' \<inter> bvars\<^sub>s\<^sub>t A' = {}"
using tr_wf'[OF _ _ _ _ assms(1)]
      tr_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s[OF assms(1,3)]
      tr_vars_disj[OF assms(1)]
      assms(2)
by fastforce+

private lemma tr_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p:
  assumes "A' \<in> set (tr A D)" "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p A"
  and "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" (is "?P0 A D")
  and "\<forall>(t,s) \<in> set D. (fv t \<union> fv s) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" (is "?P1 A D")
  and "\<forall>t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D. \<forall>t' \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set D.
          (\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t'" (is "?P3 A D")
  shows "list_all tfr\<^sub>s\<^sub>t\<^sub>p A'"
proof -
  have sublmm: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p A" "?P0 A D" "?P1 A D" "?P3 A D"
    when p: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a#A)" "?P0 (a#A) D" "?P1 (a#A) D" "?P3 (a#A) D"
    for a A D
    using p(1) apply (simp add: tfr\<^sub>s\<^sub>s\<^sub>t_def)
    using p(2) fv\<^sub>s\<^sub>s\<^sub>t_cons_subset bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset apply fast
    using p(3) bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset apply fast
    using p(4) setops\<^sub>s\<^sub>s\<^sub>t_cons_subset by fast

  show ?thesis using assms
  proof (induction A D arbitrary: A' rule: tr.induct)
    case 1 thus ?case by simp
  next
    case (2 t A D)
    note prems = "2.prems"
    note IH = "2.IH"
    from prems(1) obtain A'' where A'': "A' = send\<langle>t\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)"
      by moura
    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p A''" using IH[OF A''(2)] prems(5) sublmm[OF prems(2,3,4,5)] by meson
    thus ?case using A''(1) by simp
  next
    case (3 t A D)
    note prems = "3.prems"
    note IH = "3.IH"
    from prems(1) obtain A'' where A'': "A' = receive\<langle>t\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)"
      by moura
    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p A''" using IH[OF A''(2)] prems(5) sublmm[OF prems(2,3,4,5)] by meson
    thus ?case using A''(1) by simp
  next
    case (4 ac t t' A D)
    note prems = "4.prems"
    note IH = "4.IH"
    from prems(1) obtain A'' where A'':
        "A' = \<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#A''" "A'' \<in> set (tr A D)"
      by moura
    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p A''" using IH[OF A''(2)] prems(5) sublmm[OF prems(2,3,4,5)] by meson
    moreover have "(\<exists>\<delta>. Unifier \<delta> t t') \<Longrightarrow> \<Gamma> t = \<Gamma> t'" using prems(2) by (simp add: tfr\<^sub>s\<^sub>s\<^sub>t_def)
    ultimately show ?case using A''(1) by auto
  next
    case (5 t s A D)
    note prems = "5.prems"
    note IH = "5.IH"
    from prems(1) have A': "A' \<in> set (tr A (List.insert (t,s) D))" by simp
  
    have 1: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p A" using sublmm[OF prems(2,3,4,5)] by simp
  
    have "pair ` setops\<^sub>s\<^sub>s\<^sub>t (Insert t s#A) \<union> pair`set D =
          pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair`set (List.insert (t,s) D)"
      by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    hence 3: "?P3 A (List.insert (t,s) D)" using prems(5) by metis
    moreover have "?P1 A (List.insert (t, s) D)" using prems(3,4) bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset[of A] by auto
    ultimately have "list_all tfr\<^sub>s\<^sub>t\<^sub>p A'" using IH[OF A' sublmm(1,2)[OF prems(2,3,4,5)] _ 3] by metis
    thus ?case using A'(1) by auto
  next
    case (6 t s A D)
    note prems = "6.prems"
    note IH = "6.IH"
    
    define constr where constr:
      "constr \<equiv> (\<lambda>Di. (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
                       (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]))"
    
    from prems(1) obtain Di A'' where A'':
        "A' = constr Di@A''" "A'' \<in> set (tr A [d\<leftarrow>D. d \<notin> set Di])"
        "Di \<in> set (subseqs D)"
      unfolding constr by auto
  
    define Q1 where "Q1 \<equiv> (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
        \<forall>x \<in> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X. \<exists>a. \<Gamma> (Var x) = TAtom a)"

    define Q2 where "Q2 \<equiv> (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
        \<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))"
  
    have "set [d\<leftarrow>D. d \<notin> set Di] \<subseteq> set D"
         "pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` set [d\<leftarrow>D. d \<notin> set Di]
          \<subseteq> pair ` setops\<^sub>s\<^sub>s\<^sub>t (Delete t s#A) \<union> pair ` set D"
      by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    hence *: "?P3 A [d\<leftarrow>D. d \<notin> set Di]" using prems(5) by blast
    have **: "?P1 A [d\<leftarrow>D. d \<notin> set Di]" using prems(4,5) by auto
    have 1: "list_all tfr\<^sub>s\<^sub>t\<^sub>p A''"
      using IH[OF A''(3,2) sublmm(1,2)[OF prems(2,3,4,5)] ** *]
      by metis
  
    have 2: "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set A'' \<or>
             (\<exists>d \<in> set Di. u = pair (t,s) \<and> u' = pair d)"
      when "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set A'" for ac u u'
      using that A''(1) unfolding constr by force
    have 3: "Inequality X U \<in> set A' \<Longrightarrow> Inequality X U \<in> set A'' \<or>
             (\<exists>d \<in> set [d\<leftarrow>D. d \<notin> set Di].
                U = [(pair (t,s), pair d)] \<and> Q2 [(pair (t,s), pair d)] X)"
        for X U
      using A''(1) unfolding Q2_def constr by force
    have 4:
        "\<forall>d\<in>set D. (\<exists>\<delta>. Unifier \<delta> (pair (t,s)) (pair d)) \<longrightarrow> \<Gamma> (pair (t,s)) = \<Gamma> (pair d)"
      using prems(5) by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  
    { fix ac u u'
      assume a: "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set A'" "\<exists>\<delta>. Unifier \<delta> u u'"
      hence "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set A'' \<or> (\<exists>d \<in> set Di. u = pair (t,s) \<and> u' = pair d)"
        using 2 by metis
      hence "\<Gamma> u = \<Gamma> u'"
        using 1(1) 4 subseqs_set_subset[OF A''(3)] a(2) tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of A'']
        by blast
    } moreover {
      fix u U
      assume "\<forall>U\<langle>\<or>\<noteq>: u\<rangle>\<^sub>s\<^sub>t \<in> set A'"
      hence "\<forall>U\<langle>\<or>\<noteq>: u\<rangle>\<^sub>s\<^sub>t \<in> set A'' \<or>
             (\<exists>d \<in> set [d\<leftarrow>D. d \<notin> set Di]. u = [(pair (t,s), pair d)] \<and> Q2 u U)"
        using 3 by metis
      hence "Q1 u U \<or> Q2 u U"
        using 1 4 subseqs_set_subset[OF A''(3)] tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of A'']
        unfolding Q1_def Q2_def
        by blast
    } ultimately show ?case using tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of A'] unfolding Q1_def Q2_def by blast
  next
    case (7 ac t s A D)
    note prems = "7.prems"
    note IH = "7.IH"

    from prems(1) obtain d A'' where A'':
        "A' = \<langle>ac: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t#A''"
        "A'' \<in> set (tr A D)" "d \<in> set D"
      by moura

    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p A''"
      using IH[OF A''(2) sublmm(1,2,3)[OF prems(2,3,4,5)] sublmm(4)[OF prems(2,3,4,5)]]
      by metis
    moreover have "(\<exists>\<delta>. Unifier \<delta> (pair (t,s)) (pair d)) \<Longrightarrow> \<Gamma> (pair (t,s)) = \<Gamma> (pair d)"
      using prems(2,5) A''(3) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    ultimately show ?case using A''(1) by fastforce
  next
    case (8 X F F' A D)
    note prems = "8.prems"
    note IH = "8.IH"

    define constr where "constr = (map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))"

    define Q1 where "Q1 \<equiv> (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
        \<forall>x \<in> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X. \<exists>a. \<Gamma> (Var x) = TAtom a)"

    define Q2 where "Q2 \<equiv> (\<lambda>(M::('fun,'var) terms) X.
        \<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))"

    have Q2_subset: "Q2 M' X" when "M' \<subseteq> M" "Q2 M X" for X M M'
      using that unfolding Q2_def by auto

    have Q2_supset: "Q2 (M \<union> M') X" when "Q2 M X" "Q2 M' X" for X M M'
      using that unfolding Q2_def by auto

    from prems(1) obtain A'' where A'': "A' = constr@A''" "A'' \<in> set (tr A D)"
      using constr_def by moura

    have 0: "F' = [] \<Longrightarrow> constr = [\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]" unfolding constr_def by simp

    have 1: "list_all tfr\<^sub>s\<^sub>t\<^sub>p A''"
      using IH[OF A''(2) sublmm(1,2,3)[OF prems(2,3,4,5)] sublmm(4)[OF prems(2,3,4,5)]]
      by metis

    have 2: "(F' = [] \<and> Q1 F X) \<or> Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') X"
      using prems(2) unfolding Q1_def Q2_def by simp
  
    have 3: "list_all tfr\<^sub>s\<^sub>t\<^sub>p constr" when "F' = []" "Q1 F X"
      using that 0 2 tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of constr] unfolding Q1_def by auto

    { fix c assume "c \<in> set constr"
      hence "\<exists>G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D). c = \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t" unfolding constr_def by force
    } moreover {
      fix G
      assume G: "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D)"
         and c: "\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t \<in> set constr"
         and e: "Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') X"

      have d_Q2: "Q2 (pair ` set D) X" unfolding Q2_def
      proof (intro allI impI)
        fix f T assume "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (pair ` set D)"
        then obtain d where d: "d \<in> set D" "Fun f T \<in> subterms (pair d)" by auto
        hence "fv (pair d) \<inter> set X = {}" using prems(4) unfolding pair_def by force
        thus "T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X)"
          by (metis fv_disj_Fun_subterm_param_cases d(2))
      qed

      have "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F@G) \<subseteq> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F' \<union> pair ` set D"
        using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_trms_subset[OF G] by auto
      hence "Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F@G)) X" using Q2_subset[OF _ Q2_supset[OF e d_Q2]] by metis
      hence "tfr\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)" by (metis Q2_def tfr\<^sub>s\<^sub>t\<^sub>p.simps(2))
    } ultimately have 4: "list_all tfr\<^sub>s\<^sub>t\<^sub>p constr" when "Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') X"
      using that Ball_set by blast

    have 5: "list_all tfr\<^sub>s\<^sub>t\<^sub>p constr" using 2 3 4 by metis

    show ?case using 1 5 A''(1) by simp
  qed
qed

lemma tr_tfr:
  assumes "A' \<in> set (tr A [])" and "tfr\<^sub>s\<^sub>s\<^sub>t A" and "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
  shows "tfr\<^sub>s\<^sub>t A'"
proof -
  have *: "trms\<^sub>s\<^sub>t A' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A" using tr_trms_subset[OF assms(1)] by simp
  hence "SMP (trms\<^sub>s\<^sub>t A') \<subseteq> SMP (trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A)" using SMP_mono by simp
  moreover have "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A)" using assms(2) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by fast
  ultimately have 1: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t A')" by (metis tfr_subset(2)[OF _ *])

  have **: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p A" using assms(2) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by fast
  have "pair ` setops\<^sub>s\<^sub>s\<^sub>t A \<subseteq> SMP (trms\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t A) - Var`\<V>"
    using setops\<^sub>s\<^sub>s\<^sub>t_are_pairs unfolding pair_def by auto
  hence ***: "\<forall>t \<in> pair`setops\<^sub>s\<^sub>s\<^sub>t A. \<forall>t' \<in> pair`setops\<^sub>s\<^sub>s\<^sub>t A. (\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t'"
    using assms(2) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  have 2: "list_all tfr\<^sub>s\<^sub>t\<^sub>p A'"
    using tr_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p[OF assms(1) ** assms(3)] *** unfolding pair_def by fastforce

  show ?thesis by (metis 1 2 tfr\<^sub>s\<^sub>t_def)
qed

private lemma fun_pair_ineqs:
  assumes "d \<cdot>\<^sub>p \<delta> \<cdot>\<^sub>p \<theta> \<noteq> d' \<cdot>\<^sub>p \<I>"
  shows "pair d \<cdot> \<delta> \<cdot> \<theta> \<noteq> pair d' \<cdot> \<I>"
proof -
  have "d \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<theta>) \<noteq> d' \<cdot>\<^sub>p \<I>" using assms subst_pair_compose by metis
  hence "pair d \<cdot> (\<delta> \<circ>\<^sub>s \<theta>) \<noteq> pair d' \<cdot> \<I>" using fun_pair_eq_subst by metis
  thus ?thesis by simp
qed

private lemma tr_Delete_constr_iff_aux1:
  assumes "\<forall>d \<in> set Di. (t,s) \<cdot>\<^sub>p \<I> = d \<cdot>\<^sub>p \<I>"
  and "\<forall>d \<in> set D - set Di. (t,s) \<cdot>\<^sub>p \<I> \<noteq> d \<cdot>\<^sub>p \<I>"
  shows "\<lbrakk>M; (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
             (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di])\<rbrakk>\<^sub>d \<I>"
proof -
  from assms(2) have
    "\<lbrakk>M; map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]\<rbrakk>\<^sub>d \<I>"
  proof (induction D)
    case (Cons d D)
    hence IH: "\<lbrakk>M; map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D . d \<notin> set Di]\<rbrakk>\<^sub>d \<I>" by auto
    thus ?case
    proof (cases "d \<in> set Di")
      case False
      hence "(t,s) \<cdot>\<^sub>p \<I> \<noteq> d \<cdot>\<^sub>p \<I>" using Cons by simp
      hence "pair (t,s) \<cdot> \<I> \<noteq> pair d \<cdot> \<I>" using fun_pair_eq_subst by metis
      moreover have "\<And>t (\<delta>::('fun,'var) subst). subst_domain \<delta> = {} \<Longrightarrow> t \<cdot> \<delta> = t" by auto
      ultimately have "\<forall>\<delta>. subst_domain \<delta> = {} \<longrightarrow> pair (t,s) \<cdot> \<delta> \<cdot> \<I> \<noteq> pair d \<cdot> \<delta> \<cdot> \<I>" by metis
      thus ?thesis using IH by (simp add: ineq_model_def)
    qed simp
  qed simp
  moreover {
    fix B assume "\<lbrakk>M; B\<rbrakk>\<^sub>d \<I>" 
    with assms(1) have "\<lbrakk>M; (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@B\<rbrakk>\<^sub>d \<I>"
      unfolding pair_def by (induction Di) auto
  } ultimately show ?thesis by metis
qed

private lemma tr_Delete_constr_iff_aux2:
  assumes "ground M"
  and "\<lbrakk>M; (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
           (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di])\<rbrakk>\<^sub>d \<I>"
  shows "(\<forall>d \<in> set Di. (t,s) \<cdot>\<^sub>p \<I> = d \<cdot>\<^sub>p \<I>) \<and> (\<forall>d \<in> set D - set Di. (t,s) \<cdot>\<^sub>p \<I> \<noteq> d \<cdot>\<^sub>p \<I>)"
proof -
  let ?c1 = "map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di"
  let ?c2 = "map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]"

  have "M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> = M" using assms(1) subst_all_ground_ident by metis
  moreover have "ik\<^sub>s\<^sub>t ?c1 = {}" by auto
  ultimately have *:
       "\<lbrakk>M; map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di\<rbrakk>\<^sub>d \<I>"
       "\<lbrakk>M; map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]\<rbrakk>\<^sub>d \<I>"
    using strand_sem_split(3,4)[of M ?c1 ?c2 \<I>] assms(2) by auto
  
  from *(1) have 1: "\<forall>d \<in> set Di. (t,s) \<cdot>\<^sub>p \<I> = d \<cdot>\<^sub>p \<I>" unfolding pair_def by (induct Di) auto
  from *(2) have 2: "\<forall>d \<in> set D - set Di. (t,s) \<cdot>\<^sub>p \<I> \<noteq> d \<cdot>\<^sub>p \<I>"
  proof (induction D arbitrary: Di)
    case (Cons d D) thus ?case
    proof (cases "d \<in> set Di")
      case False
      hence IH: "\<forall>d \<in> set D - set Di. (t,s) \<cdot>\<^sub>p \<I> \<noteq> d \<cdot>\<^sub>p \<I>" using Cons by force
      have "\<And>t (\<delta>::('fun,'var) subst). subst_domain \<delta> = {} \<and> ground (subst_range \<delta>) \<longleftrightarrow> \<delta> = Var"
        by auto
      moreover have "ineq_model \<I> [] [((pair (t,s)), (pair d))]"
        using False Cons.prems by simp
      ultimately have "pair (t,s) \<cdot> \<I> \<noteq> pair d \<cdot> \<I>" by (simp add: ineq_model_def)
      thus ?thesis using IH unfolding pair_def by force
    qed simp
  qed simp

  show ?thesis by (metis 1 2)
qed

private lemma tr_Delete_constr_iff:
  fixes \<I>::"('fun,'var) subst"
  assumes "ground M"
  shows "set Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {(t,s) \<cdot>\<^sub>p \<I>} \<and> (t,s) \<cdot>\<^sub>p \<I> \<notin> (set D - set Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<longleftrightarrow>
         \<lbrakk>M; (map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
             (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di])\<rbrakk>\<^sub>d \<I>"
proof -
  let ?constr = "(map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di)@
                 (map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di])"
  { assume "set Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {(t,s) \<cdot>\<^sub>p \<I>}" "(t,s) \<cdot>\<^sub>p \<I> \<notin> (set D - set Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
    hence "\<forall>d \<in> set Di. (t,s) \<cdot>\<^sub>p \<I> = d \<cdot>\<^sub>p \<I>" "\<forall>d \<in> set D - set Di. (t,s) \<cdot>\<^sub>p \<I> \<noteq> d \<cdot>\<^sub>p \<I>"
      by auto
    hence "\<lbrakk>M; ?constr\<rbrakk>\<^sub>d \<I>" using tr_Delete_constr_iff_aux1 by simp
  } moreover {
    assume "\<lbrakk>M; ?constr\<rbrakk>\<^sub>d \<I>"
    hence "\<forall>d \<in> set Di. (t,s) \<cdot>\<^sub>p \<I> = d \<cdot>\<^sub>p \<I>" "\<forall>d \<in> set D - set Di. (t,s) \<cdot>\<^sub>p \<I> \<noteq> d \<cdot>\<^sub>p \<I>"
      using assms tr_Delete_constr_iff_aux2 by auto
    hence "set Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {(t,s) \<cdot>\<^sub>p \<I>} \<and> (t,s) \<cdot>\<^sub>p \<I> \<notin> (set D - set Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>" by force
  } ultimately show ?thesis by metis
qed

private lemma tr_NotInSet_constr_iff:
  fixes \<I>::"('fun,'var) subst"
  assumes "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> set X = {}"
  shows "(\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> (t,s) \<cdot>\<^sub>p \<delta> \<cdot>\<^sub>p \<I> \<notin> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>)
          \<longleftrightarrow> \<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) D\<rbrakk>\<^sub>d \<I>"
proof -
  { assume "\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> (t,s) \<cdot>\<^sub>p \<delta> \<cdot>\<^sub>p \<I> \<notin> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
    with assms have "\<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) D\<rbrakk>\<^sub>d \<I>"
    proof (induction D)
      case (Cons d D)
      obtain t' s' where d: "d = (t',s')" by moura
      have "\<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) D\<rbrakk>\<^sub>d \<I>"
           "map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) (d#D) =
            \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t#map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) D"
        using Cons by auto
      moreover have
          "\<forall>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>) \<longrightarrow> pair (t, s) \<cdot> \<delta> \<cdot> \<I> \<noteq> pair d \<cdot> \<I>"
        using fun_pair_ineqs[of \<I> _  "(t,s)" \<I> d] Cons.prems(2) by auto
      moreover have "(fv t' \<union> fv s') \<inter> set X = {}" using Cons.prems(1) d by auto
      hence "\<forall>\<delta>. subst_domain \<delta> = set X \<longrightarrow> pair d \<cdot> \<delta> = pair d" using d unfolding pair_def by auto
      ultimately show ?case by (simp add: ineq_model_def)
    qed simp
  } moreover {
    fix \<delta>::"('fun,'var) subst"
    assume "\<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) D\<rbrakk>\<^sub>d \<I>"
      and \<delta>: "subst_domain \<delta> = set X" "ground (subst_range \<delta>)"
    with assms have "(t,s) \<cdot>\<^sub>p \<delta> \<cdot>\<^sub>p \<I> \<notin> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
    proof (induction D)
      case (Cons d D)
      obtain t' s' where d: "d = (t',s')" by moura
      have "(t,s) \<cdot>\<^sub>p \<delta> \<cdot>\<^sub>p \<I> \<notin> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
           "pair (t,s) \<cdot> \<delta> \<cdot> \<I> \<noteq> pair d \<cdot> \<delta> \<cdot> \<I>"
        using Cons d by (auto simp add: ineq_model_def simp del: subst_range.simps)
      moreover have "pair d \<cdot> \<delta> = pair d"
        using Cons.prems(1) fun_pair_subst[of d \<delta>] d \<delta>(1) unfolding pair_def by auto
      ultimately show ?case unfolding pair_def by force
    qed simp
  } ultimately show ?thesis by metis
qed

lemma tr_NegChecks_constr_iff:
  "(\<forall>G\<in>set L. ineq_model \<I> X (F@G)) \<longleftrightarrow> \<lbrakk>M; map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) L\<rbrakk>\<^sub>d \<I>" (is ?A)
  "negchecks_model \<I> D X F F' \<longleftrightarrow> \<lbrakk>M; D; [\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>]\<rbrakk>\<^sub>s \<I>" (is ?B)
proof -
  show ?A by (induct L) auto
  show ?B by simp
qed

lemma tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_sem_equiv:
  fixes \<I>::"('fun,'var) subst"
  assumes "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> set X = {}"
  shows "negchecks_model \<I> (set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) X F F' \<longleftrightarrow>
         (\<forall>G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D). ineq_model \<I> X (F@G))"
proof -
  define P where
    "P \<equiv> \<lambda>\<delta>::('fun,'var) subst. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)" 

  define Ineq where
    "Ineq \<equiv> \<lambda>(\<delta>::('fun,'var) subst) F. list_ex (\<lambda>f. fst f \<cdot> \<delta> \<circ>\<^sub>s \<I> \<noteq> snd f \<cdot> \<delta> \<circ>\<^sub>s \<I>) F"

  define Ineq' where
    "Ineq' \<equiv> \<lambda>(\<delta>::('fun,'var) subst) F. list_ex (\<lambda>f. fst f \<cdot> \<delta> \<circ>\<^sub>s \<I> \<noteq> snd f \<cdot> \<I>) F"
  
  define Notin where
    "Notin \<equiv> \<lambda>(\<delta>::('fun,'var) subst) D F'. list_ex (\<lambda>f. f \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) F'"

  have sublmm:
      "((s,t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) \<longleftrightarrow> (list_all (\<lambda>d. Ineq' \<delta> [(pair (s,t),pair d)]) D)"
    for s t \<delta> D
    unfolding pair_def by (induct D) (auto simp add: Ineq'_def)

  have "Notin \<delta> D F' \<longleftrightarrow> (\<forall>G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D). Ineq' \<delta> G)"
    (is "?A \<longleftrightarrow> ?B")
    when "P \<delta>" for \<delta>
  proof
    show "?A \<Longrightarrow> ?B"
    proof (induction F' D rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
      case (2 s t F' D)
      show ?case
      proof (cases "Notin \<delta> D F'")
        case False
        hence "(s,t) \<cdot>\<^sub>p \<delta> \<circ>\<^sub>s \<I> \<notin> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
          using "2.prems"
          by (auto simp add: Notin_def)
        hence "pair (s,t) \<cdot> \<delta> \<circ>\<^sub>s \<I> \<noteq> pair d \<cdot> \<I>" when "d \<in> set D" for d
          using that sublmm Ball_set[of D "\<lambda>d. Ineq' \<delta> [(pair (s,t), pair d)]"]
          by (simp add: Ineq'_def)
        moreover have "\<exists>d \<in> set D. \<exists>G'. G = (pair (s,t), pair d)#G'"
          when "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F') D)" for G
          using that tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_index[OF that, of 0] by force
        ultimately show ?thesis by (simp add: Ineq'_def)
      qed (auto dest: "2.IH" simp add: Ineq'_def)
    qed (simp add: Notin_def)

    have "\<not>?A \<Longrightarrow> \<not>?B"
    proof (induction F' D rule: tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s.induct)
      case (2 s t F' D)
      then obtain G where G: "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D)" "\<not>Ineq' \<delta> G"
        by (auto simp add: Notin_def)

      obtain d where d: "d \<in> set D" "pair (s,t) \<cdot> \<delta> \<circ>\<^sub>s \<I> = pair d \<cdot> \<I>"
        using "2.prems"
        unfolding pair_def by (auto simp add: Notin_def)
      thus ?case
        using G(2) tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_cons[OF G(1) d(1)]
        by (auto simp add: Ineq'_def)
    qed (simp add: Ineq'_def)
    thus "?B \<Longrightarrow> ?A" by metis
  qed
  hence *: "(\<forall>\<delta>. P \<delta> \<longrightarrow> Ineq \<delta> F \<or> Notin \<delta> D F') \<longleftrightarrow>
            (\<forall>G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D). \<forall>\<delta>. P \<delta> \<longrightarrow> Ineq \<delta> F \<or> Ineq' \<delta> G)"
    by auto

  have "snd g \<cdot> \<delta> = snd g"
    when "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D)" "g \<in> set G" "P \<delta>"
    for \<delta> g G
    using assms that(3) tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_has_pair_lists[OF that(1,2)]
    unfolding pair_def by (fastforce simp add: P_def)
  hence **: "Ineq' \<delta> G = Ineq \<delta> G"
    when "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D)" "P \<delta>"
    for \<delta> G
    using Bex_set[of G "\<lambda>f. fst f \<cdot> \<delta> \<circ>\<^sub>s \<I> \<noteq> snd f \<cdot> \<I>"]
          Bex_set[of G "\<lambda>f. fst f \<cdot> \<delta> \<circ>\<^sub>s \<I> \<noteq> snd f \<cdot> \<delta> \<circ>\<^sub>s \<I>"]
          that
    by (simp add: Ineq_def Ineq'_def)
  
  show ?thesis
    using * **
    by (simp add: Ineq_def Ineq'_def Notin_def P_def negchecks_model_def ineq_model_def)
qed

lemma tr_sem_equiv':
  assumes "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
    and "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
    and "ground M"
    and \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I> \<longleftrightarrow> (\<exists>A' \<in> set (tr A D). \<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>)" (is "?P \<longleftrightarrow> ?Q")
proof
  have \<I>_grounds: "\<And>t. fv (t \<cdot> \<I>) = {}" by (rule interpretation_grounds[OF \<I>])
  have "\<exists>A' \<in> set (tr A D). \<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>" when ?P using that assms(1,2,3)
  proof (induction A arbitrary: D rule: strand_sem_stateful_induct)
    case (ConsRcv M D t A)
    have "\<lbrakk>insert (t \<cdot> \<I>) M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground (insert (t \<cdot> \<I>) M)"
      using \<I> ConsRcv.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    then obtain A' where A': "A' \<in> set (tr A D)" "\<lbrakk>insert (t \<cdot> \<I>) M; A'\<rbrakk>\<^sub>d \<I>" by (metis ConsRcv.IH)
    thus ?case by auto
  next
    case (ConsSnd M D t A)
    have "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      and *: "M \<turnstile> t \<cdot> \<I>"
      using \<I> ConsSnd.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    then obtain A' where A': "A' \<in> set (tr A D)" "\<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>" by (metis ConsSnd.IH)
    thus ?case using * by auto
  next
    case (ConsEq M D ac t t' A)
    have "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      and *: "t \<cdot> \<I> = t' \<cdot> \<I>"
      using \<I> ConsEq.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    then obtain A' where A': "A' \<in> set (tr A D)" "\<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>" by (metis ConsEq.IH)
    thus ?case using * by auto
  next
    case (ConsIns M D t s A)
    have "\<lbrakk>M; set (List.insert (t,s) D) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
         "\<forall>(t,t') \<in> set (List.insert (t,s) D). (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      using ConsIns.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    then obtain A' where A': "A' \<in> set (tr A (List.insert (t,s) D))" "\<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>"
      by (metis ConsIns.IH)
    thus ?case by auto
  next
    case (ConsDel M D t s A)
    have *: "\<lbrakk>M; (set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - {(t,s) \<cdot>\<^sub>p \<I>}; A\<rbrakk>\<^sub>s \<I>"
            "\<forall>(t,t')\<in>set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
            "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      using ConsDel.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    then obtain Di where Di:
        "Di \<subseteq> set D" "Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {(t,s) \<cdot>\<^sub>p \<I>}" "(t,s) \<cdot>\<^sub>p \<I> \<notin> (set D - Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
      using subset_subst_pairs_diff_exists'[of "set D"] by moura
    hence **: "(set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - {(t,s) \<cdot>\<^sub>p \<I>} = (set D - Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>" by blast

    obtain Di' where Di': "set Di' = Di" "Di' \<in> set (subseqs D)"
      using subset_sublist_exists[OF Di(1)] by moura
    hence ***: "(set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - {(t,s) \<cdot>\<^sub>p \<I>} = (set [d\<leftarrow>D. d \<notin> set Di'] \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>)"
      using Di ** by auto
    
    define constr where "constr \<equiv>
        map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di'@
        map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di']"
    
    have ****: "\<forall>(t,t')\<in>set [d\<leftarrow>D. d \<notin> set Di']. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
      using *(2) Di(1) Di'(1) subseqs_set_subset[OF Di'(2)] by simp
    have "set D - Di = set [d\<leftarrow>D. d \<notin> set Di']" using Di Di' by auto
    hence *****: "\<lbrakk>M; set [d\<leftarrow>D. d \<notin> set Di'] \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
      using *(1) ** by metis
    obtain A' where A': "A' \<in> set (tr A [d\<leftarrow>D. d \<notin> set Di'])" "\<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>"
      using ConsDel.IH[OF ***** **** *(3,4)] by moura
    hence constr_sat: "\<lbrakk>M; constr\<rbrakk>\<^sub>d \<I>"
      using Di Di' *(1) *** tr_Delete_constr_iff[OF *(4), of \<I> Di' t s D] 
      unfolding constr_def by auto

    have "constr@A' \<in> set (tr (Delete t s#A) D)" using A'(1) Di' unfolding constr_def by auto
    moreover have "ik\<^sub>s\<^sub>t constr = {}" unfolding constr_def by auto
    hence "\<lbrakk>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; constr\<rbrakk>\<^sub>d \<I>" "\<lbrakk>M \<union> (ik\<^sub>s\<^sub>t constr \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>); A'\<rbrakk>\<^sub>d \<I>"
      using constr_sat A'(2) subst_all_ground_ident[OF *(4)] by simp_all
    ultimately show ?case
      using strand_sem_append(2)[of _ _ \<I>]
            subst_all_ground_ident[OF *(4), of \<I>]
      by metis
  next
    case (ConsIn M D ac t s A)
    have "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      and *: "(t,s) \<cdot>\<^sub>p \<I> \<in> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
      using \<I> ConsIn.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    then obtain A' where A': "A' \<in> set (tr A D)" "\<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>" by (metis ConsIn.IH)
    moreover obtain d where "d \<in> set D" "pair (t,s) \<cdot> \<I> = pair d \<cdot> \<I>"
      using * unfolding pair_def by auto
    ultimately show ?case using * by auto
  next
    case (ConsNegChecks M D X F F' A)
    let ?ineqs = "(map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))"
    have 1: "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>" "ground M" using ConsNegChecks by auto
    have 2: "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" 
      using ConsNegChecks.prems(2,3) \<I> unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by fastforce+
    
    have 3: "negchecks_model \<I> (set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) X F F'" using ConsNegChecks.prems(1) by simp
    from 1 2 obtain A' where A': "A' \<in> set (tr A D)" "\<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>" by (metis ConsNegChecks.IH)
    
    have 4: "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> set X = {}"
      using ConsNegChecks.prems(2) unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def by auto
    
    have "\<lbrakk>M; ?ineqs\<rbrakk>\<^sub>d \<I>"
      using 3 tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_sem_equiv[OF 4] tr_NegChecks_constr_iff
      by metis
    moreover have "ik\<^sub>s\<^sub>t ?ineqs = {}" by auto
    moreover have "M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> = M" using 1(2) \<I> by (simp add: subst_all_ground_ident)
    ultimately show ?case
      using strand_sem_append(2)[of M ?ineqs \<I> A'] A'
      by force
  qed simp
  thus "?P \<Longrightarrow> ?Q" by metis

  have "(\<exists>A' \<in> set (tr A D). \<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>) \<Longrightarrow> ?P" using assms(1,2,3)
  proof (induction A arbitrary: D rule: strand_sem_stateful_induct)
    case (ConsRcv M D t A)
    have "\<exists>A' \<in> set (tr A D). \<lbrakk>insert (t \<cdot> \<I>) M; A'\<rbrakk>\<^sub>d \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground (insert (t \<cdot> \<I>) M)"
      using \<I> ConsRcv.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    hence "\<lbrakk>insert (t \<cdot> \<I>) M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>" by (metis ConsRcv.IH)
    thus ?case by auto
  next
    case (ConsSnd M D t A)
    have "\<exists>A' \<in> set (tr A D). \<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      and *: "M \<turnstile> t \<cdot> \<I>"
      using \<I> ConsSnd.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    hence "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>" by (metis ConsSnd.IH)
    thus ?case using * by auto
  next
    case (ConsEq M D ac t t' A)
    have "\<exists>A' \<in> set (tr A D). \<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      and *: "t \<cdot> \<I> = t' \<cdot> \<I>"
      using \<I> ConsEq.prems unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    hence "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>" by (metis ConsEq.IH)
    thus ?case using * by auto
  next
    case (ConsIns M D t s A)
    hence "\<exists>A' \<in> set (tr A (List.insert (t,s) D)). \<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>"
          "\<forall>(t,t') \<in> set (List.insert (t,s) D). (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
          "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by auto+
    hence "\<lbrakk>M; set (List.insert (t,s) D) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>" by (metis ConsIns.IH)
    thus ?case by auto
  next
    case (ConsDel M D t s A)
    define constr where "constr \<equiv>
      \<lambda>Di. map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di@
           map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]"
    let ?flt = "\<lambda>Di. filter (\<lambda>d. d \<notin> set Di) D"

    have "\<exists>Di \<in> set (subseqs D). \<exists>B' \<in> set (tr A (?flt Di)). B = constr Di@B'"
      when "B \<in> set (tr (delete\<langle>t,s\<rangle>#A) D)" for B
      using that unfolding constr_def by auto
    then obtain A' Di where A':
        "constr Di@A' \<in> set (tr (Delete t s#A) D)"
        "A' \<in> set (tr A (?flt Di))"
        "Di \<in> set (subseqs D)"
        "\<lbrakk>M; constr Di@A'\<rbrakk>\<^sub>d \<I>"
      using ConsDel.prems(1) by blast

    have 1: "\<forall>(t,t')\<in>set (?flt Di). (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" using ConsDel.prems(2) by auto
    have 2: "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" using ConsDel.prems(3) by force+
    have "ik\<^sub>s\<^sub>t (constr Di) = {}" unfolding constr_def by auto
    hence 3: "\<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>"
      using subst_all_ground_ident[OF ConsDel.prems(4)] A'(4)
            strand_sem_split(4)[of M "constr Di" A' \<I>]
      by simp
    have IH: "\<lbrakk>M; set (?flt Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
      by (metis ConsDel.IH[OF _ 1 2 ConsDel.prems(4)] 3 A'(2))

    have "\<lbrakk>M; constr Di\<rbrakk>\<^sub>d \<I>"
      using subst_all_ground_ident[OF ConsDel.prems(4)] strand_sem_split(3) A'(4)
      by metis
    hence *: "set Di \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> {(t,s) \<cdot>\<^sub>p \<I>}" "(t,s) \<cdot>\<^sub>p \<I> \<notin> (set D - set Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
      using tr_Delete_constr_iff[OF ConsDel.prems(4), of \<I> Di t s D] unfolding constr_def by auto
    have 4: "set (?flt Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> = (set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - {((t,s) \<cdot>\<^sub>p \<I>)}"
    proof
      show "set (?flt Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> (set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - {((t,s) \<cdot>\<^sub>p \<I>)}"
      proof
        fix u u' assume u: "(u,u') \<in> set (?flt Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
        then obtain v v' where v: "(v,v') \<in> set D - set Di" "(v,v') \<cdot>\<^sub>p \<I> = (u,u')" by auto
        hence "(u,u') \<noteq> (t,s) \<cdot>\<^sub>p \<I>" using * by force
        thus "(u,u') \<in>  (set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - {((t,s) \<cdot>\<^sub>p \<I>)}"
          using u v * subseqs_set_subset[OF A'(3)] by auto
      qed
      show "(set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>) - {((t,s) \<cdot>\<^sub>p \<I>)} \<subseteq> set (?flt Di) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
        using * subseqs_set_subset[OF A'(3)] by force
    qed

    show ?case using 4 IH by simp
  next
    case (ConsIn M D ac t s A)
    have "\<exists>A' \<in> set (tr A D). \<lbrakk>M; A'\<rbrakk>\<^sub>d \<I>"
         "\<forall>(t,t') \<in> set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "ground M"
      and *: "(t,s) \<cdot>\<^sub>p \<I> \<in> set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
      using ConsIn.prems(1,2,3,4) apply (fastforce, fastforce, fastforce, fastforce)
      using ConsIn.prems(1) tr.simps(7)[of ac t s A D] unfolding pair_def by fastforce
    hence "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>" by (metis ConsIn.IH)
    moreover obtain d where "d \<in> set D" "pair (t,s) \<cdot> \<I> = pair d \<cdot> \<I>"
      using * unfolding pair_def by auto
    ultimately show ?case using * by auto
  next
    case (ConsNegChecks M D X F F' A)
    let ?ineqs = "(map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' D))"

    obtain B where B:
        "?ineqs@B \<in> set (tr (NegChecks X F F'#A) D)" "\<lbrakk>M; ?ineqs@B\<rbrakk>\<^sub>d \<I>" "B \<in> set (tr A D)"
      using ConsNegChecks.prems(1) by moura
    moreover have "M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> = M"
      using ConsNegChecks.prems(4) \<I> by (simp add: subst_all_ground_ident)
    moreover have "ik\<^sub>s\<^sub>t ?ineqs = {}" by auto
    ultimately have "\<lbrakk>M; B\<rbrakk>\<^sub>d \<I>" using strand_sem_split(4)[of M ?ineqs B \<I>] by simp
    moreover have "\<forall>(t,t')\<in>set D. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}"
      using ConsNegChecks.prems(2,3) unfolding fv\<^sub>s\<^sub>s\<^sub>t_def bvars\<^sub>s\<^sub>s\<^sub>t_def by force+
    ultimately have "\<lbrakk>M; set D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; A\<rbrakk>\<^sub>s \<I>"
      by (metis ConsNegChecks.IH B(3) ConsNegChecks.prems(4))
    moreover have "\<forall>(t, t')\<in>set D. (fv t \<union> fv t') \<inter> set X = {}"
      using ConsNegChecks.prems(2) unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def by force
    ultimately show ?case
      using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_sem_equiv tr_NegChecks_constr_iff
            B(2) strand_sem_split(3)[of M ?ineqs B \<I>] \<open>M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> = M\<close>
      by simp
  qed simp
  thus "?Q \<Longrightarrow> ?P" by metis
qed

lemma tr_sem_equiv:
  assumes "fv\<^sub>s\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>s\<^sub>t A = {}" and "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<I> \<Turnstile>\<^sub>s A \<longleftrightarrow> (\<exists>A' \<in> set (tr A []). (\<I> \<Turnstile> \<langle>A'\<rangle>))"
using tr_sem_equiv'[OF _ assms(1) _ assms(2), of "[]" "{}"]
unfolding constr_sem_d_def
by auto

theorem stateful_typing_result:
  assumes "wf\<^sub>s\<^sub>s\<^sub>t \<A>"
    and "tfr\<^sub>s\<^sub>s\<^sub>t \<A>"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t \<A>)"
    and "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and "\<I> \<Turnstile>\<^sub>s \<A>"
  obtains \<I>\<^sub>\<tau>
    where "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>"
    and "\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s \<A>"
    and "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
proof -
  obtain \<A>' where \<A>':
      "\<A>' \<in> set (tr \<A> [])" "\<I> \<Turnstile> \<langle>\<A>'\<rangle>"
    using tr_sem_equiv[of \<A>] assms(1,4,5)
    by auto

  have *: "wf\<^sub>s\<^sub>t {} \<A>'"
          "fv\<^sub>s\<^sub>t \<A>' \<inter> bvars\<^sub>s\<^sub>t \<A>' = {}"
          "tfr\<^sub>s\<^sub>t \<A>'" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t \<A>')"
    using tr_wf[OF \<A>'(1) assms(1,3)]
          tr_tfr[OF \<A>'(1) assms(2)] assms(1)
    by metis+

  obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>:
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "\<lbrakk>{}; \<A>'\<rbrakk>\<^sub>d \<I>\<^sub>\<tau>"
      "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
    using wt_attack_if_tfr_attack_d 
          * Ana_invar_subst' assms(4)
          \<A>'(2)
    unfolding constr_sem_d_def
    by moura

  thus ?thesis
    using that tr_sem_equiv[of \<A>] assms(1,3) \<A>'(1)
    unfolding constr_sem_d_def
    by auto
qed

end

end

subsection \<open>Proving type-flaw resistance automatically\<close>
definition pair' where
  "pair' pair_fun d \<equiv> case d of (t,t') \<Rightarrow> Fun pair_fun [t,t']"

fun comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> pair_fun (\<langle>_: t \<doteq> t'\<rangle>) = (mgu t t' \<noteq> None \<longrightarrow> \<Gamma> t = \<Gamma> t')"
| "comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> pair_fun (\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>) = (
    (F' = [] \<and> (\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. is_Var (\<Gamma> (Var x)))) \<or>
    (\<forall>u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair' pair_fun ` set F').
      is_Fun u \<longrightarrow> (args u = [] \<or> (\<exists>s \<in> set (args u). s \<notin> Var ` set X))))"
| "comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p _ _ _ = True"

definition comp_tfr\<^sub>s\<^sub>s\<^sub>t where
  "comp_tfr\<^sub>s\<^sub>s\<^sub>t arity Ana \<Gamma> pair_fun M S \<equiv>
    list_all (comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> pair_fun) S \<and>
    list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) (trms_list\<^sub>s\<^sub>s\<^sub>t S) \<and>
    has_all_wt_instances_of \<Gamma> (trms\<^sub>s\<^sub>s\<^sub>t S \<union> pair' pair_fun ` setops\<^sub>s\<^sub>s\<^sub>t S) (set M) \<and>
    comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> M"

locale stateful_typed_model' = stateful_typed_model arity public Ana \<Gamma> Pair
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,(('fun,'atom::finite) term_type \<times> nat)) term
              \<Rightarrow> (('fun,(('fun,'atom) term_type \<times> nat)) term list
                 \<times> ('fun,(('fun,'atom) term_type \<times> nat)) term list)"
    and \<Gamma>::"('fun,(('fun,'atom) term_type \<times> nat)) term \<Rightarrow> ('fun,'atom) term_type"
    and Pair::"'fun"
  +
  assumes \<Gamma>_Var_fst': "\<And>\<tau> n m. \<Gamma> (Var (\<tau>,n)) = \<Gamma> (Var (\<tau>,m))"
    and Ana_const': "\<And>c T. arity c = 0 \<Longrightarrow> Ana (Fun c T) = ([], [])"
begin

sublocale typed_model'
by (unfold_locales, rule \<Gamma>_Var_fst', metis Ana_const', metis Ana_subst')

lemma pair_code:
  "pair d = pair' Pair d"
by (simp add: pair_def pair'_def)

lemma tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p: "tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p a = comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> Pair a"
proof (cases a)
  case (Equality ac t t')
  thus ?thesis
    using mgu_always_unifies[of t _ t'] mgu_gives_MGU[of t t']
    by auto
next
  case (NegChecks X F F')
  thus ?thesis
    using tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps(2)[of X F F']
          comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p.simps(2)[of \<Gamma> Pair X F F']
          Fun_range_case(2)[of "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F')"]
    unfolding is_Var_def pair_code[symmetric]
    by auto
qed auto

lemma tfr\<^sub>s\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>s\<^sub>t:
  assumes "comp_tfr\<^sub>s\<^sub>s\<^sub>t arity Ana \<Gamma> Pair M S"
  shows "tfr\<^sub>s\<^sub>s\<^sub>t S"
unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def
proof
  have comp_tfr\<^sub>s\<^sub>e\<^sub>t_M: "comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> M"
    using assms unfolding comp_tfr\<^sub>s\<^sub>s\<^sub>t_def by blast
  
  have wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
      and wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_S: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t S \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S)"
      and S_trms_instance_M: "has_all_wt_instances_of \<Gamma> (trms\<^sub>s\<^sub>s\<^sub>t S \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S) (set M)"
    using assms setops\<^sub>s\<^sub>s\<^sub>t_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s(2)[of S] trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t[of S]
    unfolding comp_tfr\<^sub>s\<^sub>s\<^sub>t_def comp_tfr\<^sub>s\<^sub>e\<^sub>t_def list_all_iff pair_code[symmetric] wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric]
              finite_SMP_representation_def
    by (meson, meson, blast, meson)

  show "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t S \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t S)"
    using tfr_subset(3)[OF tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t[OF comp_tfr\<^sub>s\<^sub>e\<^sub>t_M] SMP_SMP_subset]
          SMP_I'[OF wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_S wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_M S_trms_instance_M]
    by blast

  have "list_all (comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> Pair) S" by (metis assms comp_tfr\<^sub>s\<^sub>s\<^sub>t_def)
  thus "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p S" by (induct S) (simp_all add: tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p)
qed

lemma tfr\<^sub>s\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>s\<^sub>t':
  assumes "comp_tfr\<^sub>s\<^sub>s\<^sub>t arity Ana \<Gamma> Pair (SMP0  Ana \<Gamma> (trms_list\<^sub>s\<^sub>s\<^sub>t S@map pair (setops_list\<^sub>s\<^sub>s\<^sub>t S))) S"
  shows "tfr\<^sub>s\<^sub>s\<^sub>t S"
by (rule tfr\<^sub>s\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>s\<^sub>t[OF assms])

end

end
