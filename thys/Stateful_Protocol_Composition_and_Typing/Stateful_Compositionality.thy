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

(*  Title:      Stateful_Compositionality.thy
    Author:     Andreas Viktor Hess, DTU
*)


section \<open>Stateful Protocol Compositionality\<close>
text \<open>\label{Stateful-Compositionality}\<close>

theory Stateful_Compositionality
imports Stateful_Typing Parallel_Compositionality Labeled_Stateful_Strands
begin

subsection \<open>Small Lemmata\<close>
lemma (in typed_model) wt_subst_sstp_vars_type_subset:
  fixes a::"('fun,'var) stateful_strand_step"
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
    and "\<forall>t \<in> subst_range \<delta>. fv t = {} \<or> (\<exists>x. t = Var x)"
  shows "\<Gamma> ` Var ` fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> \<Gamma> ` Var ` fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a" (is ?A)
    and "\<Gamma> ` Var ` set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)) = \<Gamma> ` Var ` set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a)" (is ?B)
    and "\<Gamma> ` Var ` vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<subseteq> \<Gamma> ` Var ` vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a" (is ?C)
proof -
  show ?A
  proof
    fix \<tau> assume \<tau>: "\<tau> \<in> \<Gamma> ` Var ` fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
    then obtain x where x: "x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)" "\<Gamma> (Var x) = \<tau>" by moura

    show "\<tau> \<in> \<Gamma> ` Var ` fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
    proof (cases "x \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a")
      case False
      hence "\<exists>y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. \<delta> y = Var x"
      proof (cases a)
        case (NegChecks X F G)
        hence *: "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>)"
                 "x \<notin> set X"
          using fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck(1)[of X "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>" "G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>"]
                fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck(1)[of X F G] False x(1)
          by fastforce+

        obtain y where y: "y \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" "x \<in> fv (rm_vars (set X) \<delta> y)"
          using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_obtain_var[of _ _ "rm_vars (set X) \<delta>"]
                fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_obtain_var[of _ _ "rm_vars (set X) \<delta>"]
                *(1)
          by blast

        have "fv (rm_vars (set X) \<delta> z) = {} \<or> (\<exists>u. rm_vars (set X) \<delta> z = Var u)" for z
          using assms(2) rm_vars_img_subset[of "set X" \<delta>] by blast
        hence "rm_vars (set X) \<delta> y = Var x" using y(2) by fastforce
        hence "\<exists>y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. rm_vars (set X) \<delta> y = Var x"
          using y fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck(1)[of X F G] NegChecks *(2) by fastforce
        thus ?thesis by (metis (full_types) *(2) term.inject(1))
      qed (use assms(2) x(1) subst_apply_img_var'[of x _ \<delta>] in fastforce)+
      then obtain y where y: "y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p a" "\<delta> y = Var x" by moura
      hence "\<Gamma> (Var y) = \<tau>" using x(2) assms(1) by (simp add: wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
      thus ?thesis using y(1) by auto
    qed (use x in auto)
  qed

  show ?B by (metis bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst)

  show ?C
  proof
    fix \<tau> assume \<tau>: "\<tau> \<in> \<Gamma> ` Var ` vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
    then obtain x where x: "x \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)" "\<Gamma> (Var x) = \<tau>" by moura

    show "\<tau> \<in> \<Gamma> ` Var ` vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
    proof (cases "x \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a")
      case False
      hence "\<exists>y \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. \<delta> y = Var x"
      proof (cases a)
        case (NegChecks X F G)
        hence *: "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>)"
                 "x \<notin> set X"
          using vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck[of X "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>" "G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>"]
                vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck[of X F G] False x(1)
          by (fastforce, blast)

        obtain y where y: "y \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" "x \<in> fv (rm_vars (set X) \<delta> y)"
          using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_obtain_var[of _ _ "rm_vars (set X) \<delta>"]
                fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_obtain_var[of _ _ "rm_vars (set X) \<delta>"]
                *(1)
          by blast

        have "fv (rm_vars (set X) \<delta> z) = {} \<or> (\<exists>u. rm_vars (set X) \<delta> z = Var u)" for z
          using assms(2) rm_vars_img_subset[of "set X" \<delta>] by blast
        hence "rm_vars (set X) \<delta> y = Var x" using y(2) by fastforce
        hence "\<exists>y \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. rm_vars (set X) \<delta> y = Var x"
          using y vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p_NegCheck[of X F G] NegChecks by blast
        thus ?thesis by (metis (full_types) *(2) term.inject(1))
      qed (use assms(2) x(1) subst_apply_img_var'[of x _ \<delta>] in fastforce)+
      then obtain y where y: "y \<in> vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p a" "\<delta> y = Var x" by moura
      hence "\<Gamma> (Var y) = \<tau>" using x(2) assms(1) by (simp add: wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
      thus ?thesis using y(1) by auto
    qed (use x in auto)
  qed
qed

lemma (in typed_model) wt_subst_lsst_vars_type_subset:
  fixes A::"('fun,'var,'a) labeled_stateful_strand"
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
    and "\<forall>t \<in> subst_range \<delta>. fv t = {} \<or> (\<exists>x. t = Var x)"
  shows "\<Gamma> ` Var ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) \<subseteq> \<Gamma> ` Var ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?A)
    and "\<Gamma> ` Var ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = \<Gamma> ` Var ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?B)
    and "\<Gamma> ` Var ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) \<subseteq> \<Gamma> ` Var ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?C)
proof -
  have "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
       "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
       "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
       "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
       "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
       "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) = set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
    when "a = (l,b)" for a l b and A::"('fun,'var,'a) labeled_stateful_strand"
    using that unlabel_Cons(1)[of l b A] unlabel_subst[of "a#A" \<delta>]
          subst_lsst_cons[of a A \<delta>] subst_sst_cons[of b "unlabel A" \<delta>]
          subst_apply_labeled_stateful_strand_step.simps(1)[of l b \<delta>]
          vars\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons[of l b A] vars\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons[of l "b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"]
          fv\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons[of l b A] fv\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons[of l "b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"]
          bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons[of l b A] bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons[of l "b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"]
    by simp_all
  hence *: "\<Gamma> ` Var ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) =
            \<Gamma> ` Var ` vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> \<Gamma> ` Var ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
           "\<Gamma> ` Var ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) = \<Gamma> ` Var ` vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<union> \<Gamma> ` Var ` vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
           "\<Gamma> ` Var ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) =
            \<Gamma> ` Var ` fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> \<Gamma> ` Var ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
           "\<Gamma> ` Var ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) = \<Gamma> ` Var ` fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<union> \<Gamma> ` Var ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
           "\<Gamma> ` Var ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) =
            \<Gamma> ` Var ` set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)) \<union> \<Gamma> ` Var ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
           "\<Gamma> ` Var ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) = \<Gamma> ` Var ` set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b) \<union> \<Gamma> ` Var ` bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
    when "a = (l,b)" for a l b and A::"('fun,'var,'a) labeled_stateful_strand"
    using that by fast+

  have "?A \<and> ?B \<and> ?C"
  proof (induction A)
    case (Cons a A)
    obtain l b where a: "a = (l,b)" by (metis surj_pair)

    show ?case
      using Cons.IH wt_subst_sstp_vars_type_subset[OF assms, of b] *[OF a, of A]
      by (metis Un_mono)
  qed simp
  thus ?A ?B ?C by metis+
qed

lemma (in stateful_typed_model) fv_pair_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subset:
  assumes "d \<in> set D"
  shows "fv (pair (snd d)) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
using assms unfolding pair_def by (induct D) (auto simp add: unlabel_def)

lemma (in stateful_typed_model) labeled_sat_ineq_lift:
  assumes "\<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>dbproj i D. d \<notin> set Di]\<rbrakk>\<^sub>d \<I>"
    (is "?R1 D")
  and "\<forall>(j,p) \<in> {(i,t,s)} \<union> set D \<union> set Di. \<forall>(k,q) \<in> {(i,t,s)} \<union> set D \<union> set Di.
          (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k" (is "?R2 D")
  shows "\<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]\<rbrakk>\<^sub>d \<I>"
using assms
proof (induction D)
  case (Cons dl D)
  obtain d l where dl: "dl = (l,d)" by (metis surj_pair)

  have 1: "?R1 D"
  proof (cases "i = l")
    case True thus ?thesis using Cons.prems(1) dl by (cases "dl \<in> set Di") auto
  next
    case False thus ?thesis using Cons.prems(1) dl by auto
  qed

  have "set D \<subseteq> set (dl#D)" by auto
  hence 2: "?R2 D" using Cons.prems(2) by blast

  have "i \<noteq> l \<or> dl \<in> set Di \<or> \<lbrakk>M; [\<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd dl))]\<rangle>\<^sub>s\<^sub>t]\<rbrakk>\<^sub>d \<I>"
    using Cons.prems(1) dl by (auto simp add: ineq_model_def)
  moreover have "\<exists>\<delta>. Unifier \<delta> (pair (t,s)) (pair d) \<Longrightarrow> i = l"
    using Cons.prems(2) dl by force
  ultimately have 3: "dl \<in> set Di \<or> \<lbrakk>M; [\<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd dl))]\<rangle>\<^sub>s\<^sub>t]\<rbrakk>\<^sub>d \<I>"
    using strand_sem_not_unif_is_sat_ineq[of "pair (t,s)" "pair d"] dl by fastforce

  show ?case using Cons.IH[OF 1 2] 3 dl by auto
qed simp

lemma (in stateful_typed_model) labeled_sat_ineq_dbproj:
  assumes "\<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d \<notin> set Di]\<rbrakk>\<^sub>d \<I>"
    (is "?P D")
  shows "\<lbrakk>M; map (\<lambda>d. \<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>dbproj i D. d \<notin> set Di]\<rbrakk>\<^sub>d \<I>"
    (is "?Q D")
using assms
proof (induction D)
  case (Cons di D)
  obtain d j where di: "di = (j,d)" by (metis surj_pair)

  have "?P D" using Cons.prems by (cases "di \<in> set Di") auto
  hence IH: "?Q D" by (metis Cons.IH)

  show ?case using di IH
  proof (cases "i = j \<and> di \<notin> set Di")
    case True
    have 1: "\<lbrakk>M; [\<forall>X\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd di))]\<rangle>\<^sub>s\<^sub>t]\<rbrakk>\<^sub>d \<I>"
      using Cons.prems True by auto
    have 2: "dbproj i (di#D) = di#dbproj i D" using True dbproj_Cons(1) di by auto
    show ?thesis using 1 2 IH by auto
  qed auto
qed simp

lemma (in stateful_typed_model) labeled_sat_ineq_dbproj_sem_equiv:
  assumes "\<forall>(j,p) \<in> ((\<lambda>(t, s). (i, t, s)) ` set F') \<union> set D.
           \<forall>(k,q) \<in> ((\<lambda>(t, s). (i, t, s)) ` set F') \<union> set D.
            (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k"
  and "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (map snd D) \<inter> set X = {}"
  shows "\<lbrakk>M; map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd D))\<rbrakk>\<^sub>d \<I> \<longleftrightarrow>
         \<lbrakk>M; map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))\<rbrakk>\<^sub>d \<I>"
proof -
  let ?A = "set (map snd D) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
  let ?B = "set (map snd (dbproj i D)) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
  let ?C = "set (map snd D) - set (map snd (dbproj i D))"
  let ?F = "(\<lambda>(t, s). (i, t, s)) ` set F'"
  let ?P = "\<lambda>\<delta>. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"

  have 1: "\<forall>(t, t') \<in> set (map snd D). (fv t \<union> fv t') \<inter> set X = {}"
          "\<forall>(t, t') \<in> set (map snd (dbproj i D)). (fv t \<union> fv t') \<inter> set X = {}"
    using assms(2) dbproj_subset[of i D] unfolding unlabel_def by force+

  have 2: "?B \<subseteq> ?A" by auto

  have 3: "\<not>Unifier \<delta> (pair f) (pair d)"
    when f: "f \<in> set F'" and d: "d \<in> set (map snd D) - set (map snd (dbproj i D))"
    for f d and \<delta>::"('fun,'var) subst"
  proof -
    obtain k where k: "(k,d) \<in> set D - set (dbproj i D)"
      using d by force

    have "(i,f) \<in> ((\<lambda>(t, s). (i, t, s)) ` set F') \<union> set D"
         "(k,d) \<in> ((\<lambda>(t, s). (i, t, s)) ` set F') \<union> set D"
      using f k by auto
    hence "i = k" when "Unifier \<delta> (pair f) (pair d)" for \<delta>
      using assms(1) that by blast
    moreover have "k \<noteq> i" using k d by simp
    ultimately show ?thesis by metis
  qed

  have "f \<cdot>\<^sub>p \<delta> \<noteq> d \<cdot>\<^sub>p \<delta>"
    when "f \<in> set F'" "d \<in> ?C" for f d and \<delta>::"('fun,'var) subst"
    by (metis fun_pair_eq_subst 3[OF that])
  hence "f \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<I>) \<notin> ?C \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t (\<delta> \<circ>\<^sub>s \<I>)"
    when "f \<in> set F'" for f and \<delta>::"('fun,'var) subst"
    using that by blast
  moreover have "?C \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta> \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I> = ?C \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
    when "?P \<delta>" for \<delta>
    using assms(2) that pairs_substI[of \<delta> "(set (map snd D) - set (map snd (dbproj i D)))"]
    by blast
  ultimately have 4: "f \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<I>) \<notin> ?C \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
    when "f \<in> set F'" "?P \<delta>" for f and \<delta>::"('fun,'var) subst"
    by (metis that subst_pairs_compose)

  { fix f and \<delta>::"('fun,'var) subst"
    assume "f \<in> set F'" "?P \<delta>"
    hence "f \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<I>) \<notin> ?C \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>" by (metis 4)
    hence "f \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<I>) \<notin> ?A - ?B" by force
  } hence 5: "\<forall>f\<in>set F'. \<forall>\<delta>. ?P \<delta> \<longrightarrow> f \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<I>) \<notin> ?A - ?B" by metis

  show ?thesis
    using negchecks_model_db_subset[OF 2]
          negchecks_model_db_supset[OF 2 5]
          tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_sem_equiv[OF 1(1)]
          tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_sem_equiv[OF 1(2)]
          tr_NegChecks_constr_iff(1)
          strand_sem_eq_defs(2)
    by (metis (no_types, lifting))
qed

lemma (in stateful_typed_model) labeled_sat_eqs_list_all:
  assumes "\<forall>(j, p) \<in> {(i,t,s)} \<union> set D. \<forall>(k,q) \<in> {(i,t,s)} \<union> set D.
              (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k" (is "?P D")
  and "\<lbrakk>M; map (\<lambda>d. \<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t) D\<rbrakk>\<^sub>d \<I>" (is "?Q D")
  shows "list_all (\<lambda>d. fst d = i) D"
using assms
proof (induction D rule: List.rev_induct)
  case (snoc di D)
  obtain d j where di: "di = (j,d)" by (metis surj_pair)
  have "pair (t,s) \<cdot> \<I> = pair d \<cdot> \<I>" using di snoc.prems(2) by auto
  hence "\<exists>\<delta>. Unifier \<delta> (pair (t,s)) (pair d)" by auto
  hence 1: "i = j" using snoc.prems(1) di by fastforce

  have "set D \<subseteq> set (D@[di])" by auto
  hence 2: "?P D" using snoc.prems(1) by blast

  have 3: "?Q D" using snoc.prems(2) by auto

  show ?case using di 1 snoc.IH[OF 2 3] by simp
qed simp

lemma (in stateful_typed_model) labeled_sat_eqs_subseqs:
  assumes "Di \<in> set (subseqs D)"
  and "\<forall>(j, p) \<in> {(i,t,s)} \<union> set D. \<forall>(k, q) \<in> {(i,t,s)} \<union> set D.
          (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k" (is "?P D")
  and "\<lbrakk>M; map (\<lambda>d. \<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t) Di\<rbrakk>\<^sub>d \<I>"
  shows "Di \<in> set (subseqs (dbproj i D))"
proof -
  have "set Di \<subseteq> set D" by (rule subseqs_subset[OF assms(1)])
  hence "?P Di" using assms(2) by blast
  thus ?thesis using labeled_sat_eqs_list_all[OF _ assms(3)] subseqs_mem_dbproj[OF assms(1)] by simp
qed

lemma (in stateful_typed_model) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p:
  assumes "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel S)"
  shows "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S))"
using assms
proof (induction S)
  case (Cons a S)
  have prems: "tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a)" "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel S)"
    using Cons.prems unlabel_Cons(2)[of a S] by simp_all
  hence IH: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S))" by (metis Cons.IH)

  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  with Cons show ?case
  proof (cases b)
    case (Equality c t t')
    hence "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#S) = a#dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S" by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_Cons(3) a)
    thus ?thesis using a IH prems by fastforce
  next
    case (NegChecks X F G)
    hence "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#S) = a#dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S" by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_Cons(7) a)
    thus ?thesis using a IH prems by fastforce
  qed auto
qed simp

lemma (in stateful_typed_model) setops\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq:
  "setops\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)) = setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
proof (induction A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons.IH by (cases b) (simp_all add: setops\<^sub>s\<^sub>s\<^sub>t_def)
qed simp


subsection \<open>Locale Setup and Definitions\<close>
locale labeled_stateful_typed_model =
  stateful_typed_model arity public Ana \<Gamma> Pair
+ labeled_typed_model arity public Ana \<Gamma> label_witness1 label_witness2
  for arity::"'fun \<Rightarrow> nat"
  and public::"'fun \<Rightarrow> bool"
  and Ana::"('fun,'var) term \<Rightarrow> (('fun,'var) term list \<times> ('fun,'var) term list)"
  and \<Gamma>::"('fun,'var) term \<Rightarrow> ('fun,'atom::finite) term_type"
  and Pair::"'fun"
  and label_witness1::"'lbl"
  and label_witness2::"'lbl"
begin

definition lpair where
  "lpair lp \<equiv> case lp of (i,p) \<Rightarrow> (i,pair p)"

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_pair_image[simp]:
  "lpair ` (setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,send\<langle>t\<rangle>)) = {}"
  "lpair ` (setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,receive\<langle>t\<rangle>)) = {}"
  "lpair ` (setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,\<langle>ac: t \<doteq> t'\<rangle>)) = {}"
  "lpair ` (setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,insert\<langle>t,s\<rangle>)) = {(i, pair (t,s))}"
  "lpair ` (setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,delete\<langle>t,s\<rangle>)) = {(i, pair (t,s))}"
  "lpair ` (setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,\<langle>ac: t \<in> s\<rangle>)) = {(i, pair (t,s))}"
  "lpair ` (setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>)) = ((\<lambda>(t,s). (i, pair (t,s))) ` set F')"
unfolding lpair_def by force+

definition par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t where
  "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>::('fun,'var,'lbl) labeled_stateful_strand) (Secrets::('fun,'var) terms) \<equiv>
    (\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow>
              GSMP_disjoint (trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>))
                            (trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>)) Secrets) \<and>
    ground Secrets \<and> (\<forall>s \<in> Secrets. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Secrets) \<and>
    (\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>.
      (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j)"

definition declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t where
  "declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I> \<equiv> {t. \<langle>\<star>, receive\<langle>t\<rangle>\<rangle> \<in> set \<A>} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"

definition strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t ("_ leaks _ under _") where
  "(\<A>::('fun,'var,'lbl) labeled_stateful_strand) leaks Secrets under \<I> \<equiv>
    (\<exists>t \<in> Secrets - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>. \<exists>n. \<I> \<Turnstile>\<^sub>s (proj_unl n \<A>@[send\<langle>t\<rangle>]))"

definition typing_cond\<^sub>s\<^sub>s\<^sub>t where
  "typing_cond\<^sub>s\<^sub>s\<^sub>t \<A> \<equiv> wf\<^sub>s\<^sub>s\<^sub>t \<A> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t \<A>) \<and> tfr\<^sub>s\<^sub>s\<^sub>t \<A>"

type_synonym ('a,'b,'c) labeleddbstate = "('c strand_label \<times> (('a,'b) term \<times> ('a,'b) term)) set"
type_synonym ('a,'b,'c) labeleddbstatelist = "('c strand_label \<times> (('a,'b) term \<times> ('a,'b) term)) list"

text \<open>
  For proving the compositionality theorem for stateful constraints the idea is to first define a
  variant of the reduction technique that was used to establish the stateful typing result. This
  variant performs database-state projections, and it allows us to reduce the compositionality
  problem for stateful constraints to ordinary constraints.
\<close>
fun tr\<^sub>p\<^sub>c::
  "('fun,'var,'lbl) labeled_stateful_strand \<Rightarrow> ('fun,'var,'lbl) labeleddbstatelist
   \<Rightarrow> ('fun,'var,'lbl) labeled_strand list"
where
  "tr\<^sub>p\<^sub>c [] D = [[]]"
| "tr\<^sub>p\<^sub>c ((i,send\<langle>t\<rangle>)#A) D = map ((#) (i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>c A D)"
| "tr\<^sub>p\<^sub>c ((i,receive\<langle>t\<rangle>)#A) D = map ((#) (i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>c A D)"
| "tr\<^sub>p\<^sub>c ((i,\<langle>ac: t \<doteq> t'\<rangle>)#A) D = map ((#) (i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>c A D)"
| "tr\<^sub>p\<^sub>c ((i,insert\<langle>t,s\<rangle>)#A) D = tr\<^sub>p\<^sub>c A (List.insert (i,(t,s)) D)"
| "tr\<^sub>p\<^sub>c ((i,delete\<langle>t,s\<rangle>)#A) D = (
    concat (map (\<lambda>Di. map (\<lambda>B. (map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
                               (map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t))
                                    [d\<leftarrow>dbproj i D. d \<notin> set Di])@B)
                          (tr\<^sub>p\<^sub>c A [d\<leftarrow>D. d \<notin> set Di]))
                (subseqs (dbproj i D))))"
| "tr\<^sub>p\<^sub>c ((i,\<langle>ac: t \<in> s\<rangle>)#A) D =
    concat (map (\<lambda>B. map (\<lambda>d. (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#B) (dbproj i D)) (tr\<^sub>p\<^sub>c A D))"
| "tr\<^sub>p\<^sub>c ((i,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F' \<rangle>)#A) D =
    map ((@) (map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D))))) (tr\<^sub>p\<^sub>c A D)"


subsection \<open>Small Lemmata\<close>
lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_nil:
  assumes "ground Sec" "\<forall>s \<in> Sec. \<forall>s'\<in>subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Sec"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t [] Sec"
using assms unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by simp

lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subset:
  assumes A: "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A Sec"
    and BA: "set B \<subseteq> set A"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t B Sec"
proof -
  let ?L = "\<lambda>n A. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl n A)"

  have "?L n B \<subseteq> ?L n A" for n
    using trms\<^sub>s\<^sub>s\<^sub>t_mono[OF proj_set_mono(2)[OF BA]] setops\<^sub>s\<^sub>s\<^sub>t_mono[OF proj_set_mono(2)[OF BA]]
    by blast
  hence "GSMP_disjoint (?L m B) (?L n B) Sec" when nm: "m \<noteq> n" for n m::'lbl
    using GSMP_disjoint_subset[of "?L m A" "?L n A" Sec "?L m B" "?L n B"] A nm
    unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by simp
  thus "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t B Sec"
    using A setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_mono[OF BA]
    unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by blast
qed

lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_split:
  assumes "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) Sec"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A Sec" "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t B Sec"
using par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subset[OF assms] by simp_all

lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_proj:
  assumes "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A Sec"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A) Sec"
using par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subset[OF assms] by simp

lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t:
  assumes A: "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A S"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) S"
proof (unfold par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def case_prod_unfold; intro conjI)
  show "ground S" "\<forall>s \<in> S. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> S"
    using A unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by fast+

  let ?M = "\<lambda>l B. (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l B) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l B))"
  let ?P = "\<lambda>B. \<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (?M l1 B) (?M l2 B) S"
  let ?Q = "\<lambda>B. \<forall>p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B. \<forall>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B.
    (\<exists>\<delta>. Unifier \<delta> (pair (snd p)) (pair (snd q))) \<longrightarrow> fst p = fst q"

  have "?P A" "?Q A" using A unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def case_prod_unfold by blast+
  thus "?P (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" "?Q (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
    by (metis setops\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq proj_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t,
        metis setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq)
qed

lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst:
  assumes A: "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A S"
    and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "subst_domain \<delta> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = {}"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) S"
proof (unfold par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def case_prod_unfold; intro conjI)
  show "ground S" "\<forall>s \<in> S. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> S"
    using A unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by fast+

  let ?N = "\<lambda>l B. trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l B) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l B)"
  define M where "M \<equiv> \<lambda>l (B::('fun,'var,'lbl) labeled_stateful_strand). ?N l B"
  let ?P = "\<lambda>p q. \<exists>\<delta>. Unifier \<delta> (pair (snd p)) (pair (snd q))"
  let ?Q = "\<lambda>B. \<forall>p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B. \<forall>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B. ?P p q \<longrightarrow> fst p = fst q"
  let ?R = "\<lambda>B. \<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (?N l1 B) (?N l2 B) S"

  have d: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l A) \<inter> subst_domain \<delta> = {}" for l
    using \<delta>(3) unfolding proj_def bvars\<^sub>s\<^sub>s\<^sub>t_def unlabel_def by auto

  have "GSMP_disjoint (M l1 A) (M l2 A) S" when l: "l1 \<noteq> l2" for l1 l2
    using l A unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def M_def by presburger
  moreover have "M l (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = (M l A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>" for l
    using fun_pair_subst_set[of \<delta> "setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l A)", symmetric]
          trms\<^sub>s\<^sub>s\<^sub>t_subst[OF d[of l]] setops\<^sub>s\<^sub>s\<^sub>t_subst[OF d[of l]] proj_subst[of l A \<delta>]
    unfolding M_def unlabel_subst by auto
  ultimately have "GSMP_disjoint (M l1 (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)) (M l2 (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)) S" when l: "l1 \<noteq> l2" for l1 l2
    using l GSMP_wt_subst_subset[OF _ \<delta>(1,2), of _ "M l1 A"]
          GSMP_wt_subst_subset[OF _ \<delta>(1,2), of _ "M l2 A"]
    unfolding GSMP_disjoint_def by fastforce
  thus "?R (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)" unfolding M_def by blast

  have "?Q A" using A unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by force
  thus "?Q (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)" using \<delta>(3)
  proof (induction A)
    case (Cons a A)
    obtain l b where a: "a = (l,b)" by (metis surj_pair)

    have 0: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A) = set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a)) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      unfolding bvars\<^sub>s\<^sub>s\<^sub>t_def unlabel_def by simp

    have "?Q A" "subst_domain \<delta> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = {}"
      using Cons.prems 0 unfolding setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto
    hence IH: "?Q (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)" using Cons.IH unfolding setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by blast

    have 1: "fst p = fst q"
      when p: "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
        and q: "q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
        and pq: "?P p q"
      for p q
      using a p q pq by (cases b) auto

    have 2: "fst p = fst q"
      when p: "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
        and q: "q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
        and pq: "?P p q"
      for p q
    proof -
      obtain p' X where p':
          "p' \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "fst p = fst p'"
          "X \<subseteq> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A)" "snd p = snd p' \<cdot>\<^sub>p rm_vars X \<delta>"
        using setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_subst[OF p] 0 by blast

      obtain q' Y where q':
          "q' \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a" "fst q = fst q'"
          "Y \<subseteq> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A)" "snd q = snd q' \<cdot>\<^sub>p rm_vars Y \<delta>"
        using setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_in_subst[OF q] 0 by blast

      have "pair (snd p) = pair (snd p') \<cdot> \<delta>"
           "pair (snd q) = pair (snd q') \<cdot> \<delta>"
        using fun_pair_subst[of "snd p'" "rm_vars X \<delta>"] fun_pair_subst[of "snd q'" "rm_vars Y \<delta>"]
              p'(3,4) q'(3,4) Cons.prems(2) rm_vars_apply'[of \<delta> X] rm_vars_apply'[of \<delta> Y]
        by fastforce+
      hence "\<exists>\<delta>. Unifier \<delta> (pair (snd p')) (pair (snd q'))"
        using pq Unifier_comp' by metis
      thus ?thesis using Cons.prems p'(1,2) q'(1,2) by simp
    qed

    show ?case by (metis 1 2 IH Un_iff setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_cons subst_lsst_cons)
  qed simp
qed

lemma wf_pair_negchecks_map':
  assumes "wf\<^sub>s\<^sub>t X (unlabel A)"
  shows "wf\<^sub>s\<^sub>t X (unlabel (map (\<lambda>G. (i,\<forall>Y\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) M@A))"
using assms by (induct M) auto

lemma wf_pair_eqs_ineqs_map':
  fixes A::"('fun,'var,'lbl) labeled_strand"
  assumes "wf\<^sub>s\<^sub>t X (unlabel A)"
          "Di \<in> set (subseqs (dbproj i D))"
          "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X"
  shows "wf\<^sub>s\<^sub>t X (unlabel (
            (map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
            (map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>dbproj i D. d \<notin> set Di])@A))"
proof -
  let ?f = "[d\<leftarrow>dbproj i D. d \<notin> set Di]"
  define c1 where c1: "c1 = map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di"
  define c2 where c2: "c2 = map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) ?f"
  define c3 where c3: "c3 = map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) (unlabel Di)"
  define c4 where c4: "c4 = map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) (unlabel ?f)"
  have ci_eqs: "c3 = unlabel c1" "c4 = unlabel c2" unfolding c1 c2 c3 c4 unlabel_def by auto
  have 1: "wf\<^sub>s\<^sub>t X (unlabel (c2@A))"
    using wf_fun_pair_ineqs_map[OF assms(1)] ci_eqs(2) unlabel_append[of c2 A] c4
    by metis
  have 2: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel Di) \<subseteq> X"
    using assms(3) subseqs_set_subset(1)[OF assms(2)]
    unfolding unlabel_def
    by fastforce
  { fix B::"('fun,'var) strand" assume "wf\<^sub>s\<^sub>t X B"
    hence "wf\<^sub>s\<^sub>t X (unlabel c1@B)" using 2 unfolding c1 unlabel_def by (induct Di) auto
  } thus ?thesis using 1 unfolding c1 c2 unlabel_def by simp
qed

lemma trms\<^sub>s\<^sub>s\<^sub>t_setops\<^sub>s\<^sub>s\<^sub>t_wt_instance_ex:
  defines "M \<equiv> \<lambda>A. trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
  assumes B: "\<forall>b \<in> set B. \<exists>a \<in> set A. \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "\<forall>t \<in> M B. \<exists>s \<in> M A. \<exists>\<delta>. t = s \<cdot> \<delta> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
proof
  let ?P = "\<lambda>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"

  fix t assume "t \<in> M B"
  then obtain b where b: "b \<in> set B" "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd b) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd b)"
    unfolding M_def unfolding unlabel_def trms\<^sub>s\<^sub>s\<^sub>t_def setops\<^sub>s\<^sub>s\<^sub>t_def by auto
  then obtain a \<delta> where a: "a \<in> set A" "b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using B by meson

  note \<delta>' = wt_subst_rm_vars[OF \<delta>(1)] wf_trms_subst_rm_vars'[OF \<delta>(2)]

  have "t \<in> M (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    using b(2) a
    unfolding M_def subst_apply_labeled_stateful_strand_def unlabel_def trms\<^sub>s\<^sub>s\<^sub>t_def setops\<^sub>s\<^sub>s\<^sub>t_def
    by auto
  moreover have "\<exists>s \<in> M A. \<exists>\<delta>. t = s \<cdot> \<delta> \<and> ?P \<delta>" when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst'[OF that] \<delta>' unfolding M_def by blast
  moreover have "\<exists>s \<in> M A. \<exists>\<delta>. t = s \<cdot> \<delta> \<and> ?P \<delta>" when t: "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  proof -
    obtain p where p: "p \<in> setops\<^sub>s\<^sub>s\<^sub>t (unlabel A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>)" "t = pair p" using t by blast
    then obtain q X where q: "q \<in> setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)" "p = q \<cdot>\<^sub>p rm_vars (set X) \<delta>"
      using setops\<^sub>s\<^sub>s\<^sub>t_subst'[OF p(1)] by blast
    hence "t = pair q \<cdot> rm_vars (set X) \<delta>"
      using fun_pair_subst[of q "rm_vars (set X) \<delta>"] p(2) by presburger
    thus ?thesis using \<delta>'[of "set X"] q(1) unfolding M_def by blast
  qed
  ultimately show "\<exists>s \<in> M A. \<exists>\<delta>. t = s \<cdot> \<delta> \<and> ?P \<delta>" unfolding M_def unlabel_subst by fast
qed

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_wt_instance_ex:
  assumes B: "\<forall>b \<in> set B. \<exists>a \<in> set A. \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "\<forall>p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B. \<exists>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<exists>\<delta>.
    fst p = fst q \<and> snd p = snd q \<cdot>\<^sub>p \<delta> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
proof
  let ?P = "\<lambda>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"

  fix p assume "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B"
  then obtain b where b: "b \<in> set B" "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p b" unfolding setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by blast
  then obtain a \<delta> where a: "a \<in> set A" "b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using B by meson
  hence p: "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    using b(2) unfolding setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def by auto

  obtain X q where q:
      "q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "fst p = fst q" "snd p = snd q \<cdot>\<^sub>p rm_vars X \<delta>"
    using setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_subst[OF p] by blast

  show "\<exists>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<exists>\<delta>. fst p = fst q \<and> snd p = snd q \<cdot>\<^sub>p \<delta> \<and> ?P \<delta>"
    using q wt_subst_rm_vars[OF \<delta>(1)] wf_trms_subst_rm_vars'[OF \<delta>(2)] by blast
qed


subsection \<open>Lemmata: Properties of the Constraint Translation Function\<close>
lemma tr_par_labeled_rcv_iff:
  "B \<in> set (tr\<^sub>p\<^sub>c A D) \<Longrightarrow> (i, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<in> set B \<longleftrightarrow> (i, receive\<langle>t\<rangle>) \<in> set A"
by (induct A D arbitrary: B rule: tr\<^sub>p\<^sub>c.induct) auto

lemma tr_par_declassified_eq:
  "B \<in> set (tr\<^sub>p\<^sub>c A D) \<Longrightarrow> declassified\<^sub>l\<^sub>s\<^sub>t B I = declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
using tr_par_labeled_rcv_iff unfolding declassified\<^sub>l\<^sub>s\<^sub>t_def declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by simp

lemma tr_par_ik_eq:
  assumes "B \<in> set (tr\<^sub>p\<^sub>c A D)"
  shows "ik\<^sub>s\<^sub>t (unlabel B) = ik\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
proof -
  have "{t. \<exists>i. (i, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<in> set B} = {t. \<exists>i. (i, receive\<langle>t\<rangle>) \<in> set A}"
    using tr_par_labeled_rcv_iff[OF assms] by simp
  moreover have
      "\<And>C. {t. \<exists>i. (i, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<in> set C} = {t. receive\<langle>t\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel C)}"
      "\<And>C. {t. \<exists>i. (i, receive\<langle>t\<rangle>) \<in> set C} = {t. receive\<langle>t\<rangle> \<in> set (unlabel C)}"
    unfolding unlabel_def by force+
  ultimately show ?thesis by (metis ik\<^sub>s\<^sub>s\<^sub>t_def ik\<^sub>s\<^sub>t_is_rcv_set)
qed

lemma tr_par_deduct_iff:
  assumes "B \<in> set (tr\<^sub>p\<^sub>c A D)"
  shows "ik\<^sub>s\<^sub>t (unlabel B) \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> t \<longleftrightarrow> ik\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> t"
using tr_par_ik_eq[OF assms] by metis

lemma tr_par_vars_subset:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A D)"
  shows "fv\<^sub>l\<^sub>s\<^sub>t A' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)" (is ?P)
  and "bvars\<^sub>l\<^sub>s\<^sub>t A' \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A)" (is ?Q)
proof -
  show ?P using assms
  proof (induction "unlabel A" arbitrary: A A' D rule: strand_sem_stateful_induct)
    case (ConsIn A' D ac t s AA A A')
    then obtain i B where iB: "A = (i,\<langle>ac: t \<in> s\<rangle>)#B" "AA = unlabel B"
      unfolding unlabel_def by moura
    then obtain A'' d where *:
        "d \<in> set (dbproj i D)"
        "A' = (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#A''"
        "A'' \<in> set (tr\<^sub>p\<^sub>c B D)"
      using ConsIn.prems(1) by moura
    hence "fv\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel B) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
          "fv (pair (snd d)) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
      apply (metis ConsIn.hyps(1)[OF iB(2)])
      using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_mono[OF dbproj_subset[of i D]]
            fv_pair_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subset[OF *(1)]
      by blast
    thus ?case using * iB unfolding pair_def by auto
  next
    case (ConsDel A' D t s AA A A')
    then obtain i B where iB: "A = (i,delete\<langle>t,s\<rangle>)#B" "AA = unlabel B"
      unfolding unlabel_def by moura

    define fltD1 where "fltD1 = (\<lambda>Di. filter (\<lambda>d. d \<notin> set Di) D)"
    define fltD2 where "fltD2 = (\<lambda>Di. filter (\<lambda>d. d \<notin> set Di) (dbproj i D))"
    define constr where "constr =
      (\<lambda>Di. (map (\<lambda>d. (i, \<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
            (map (\<lambda>d. (i, \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) (fltD2 Di)))"

    from iB obtain A'' Di where *:
        "Di \<in> set (subseqs (dbproj i D))" "A' = (constr Di)@A''" "A'' \<in> set (tr\<^sub>p\<^sub>c B (fltD1 Di))"
      using ConsDel.prems(1) unfolding constr_def fltD1_def fltD2_def by moura
    hence "fv\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t AA \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel (fltD1 Di))"
      unfolding constr_def fltD1_def by (metis ConsDel.hyps(1) iB(2))
    hence 1: "fv\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t AA \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
      using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_mono[of "unlabel (fltD1 Di)" "unlabel D"]
      unfolding unlabel_def fltD1_def by force

    have 2: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel Di) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel (fltD1 Di)) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
      using subseqs_set_subset(1)[OF *(1)]
      unfolding fltD1_def unlabel_def
      by auto

    have 5: "fv\<^sub>l\<^sub>s\<^sub>t A' = fv\<^sub>l\<^sub>s\<^sub>t (constr Di) \<union> fv\<^sub>l\<^sub>s\<^sub>t A''" using * unfolding unlabel_def by force

    have "fv\<^sub>l\<^sub>s\<^sub>t (constr Di) \<subseteq> fv t \<union> fv s \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel Di) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel (fltD1 Di))"
      unfolding unlabel_def constr_def fltD1_def fltD2_def pair_def by auto
    hence 3: "fv\<^sub>l\<^sub>s\<^sub>t (constr Di) \<subseteq> fv t \<union> fv s \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)" using 2 by blast

    have 4: "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) = fv t \<union> fv s \<union> fv\<^sub>s\<^sub>s\<^sub>t AA" using iB by auto

    have "fv\<^sub>s\<^sub>t (unlabel A') \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)" using 1 3 4 5 by blast
    thus ?case by metis
  next
    case (ConsNegChecks A' D X F F' AA A A')
    then obtain i B where iB: "A = (i,NegChecks X F F')#B" "AA = unlabel B"
      unfolding unlabel_def by moura

    define D' where "D' \<equiv> \<Union>(fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ` set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (unlabel (dbproj i D))))"
    define constr where "constr = map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"

    from iB obtain A'' where *: "A'' \<in> set (tr\<^sub>p\<^sub>c B D)" "A' = constr@A''"
      using ConsNegChecks.prems(1) unfolding constr_def by moura
    hence "fv\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t AA \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
      by (metis ConsNegChecks.hyps(1) iB(2))
    hence **: "fv\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t AA \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)" by auto

    have 1: "fv\<^sub>l\<^sub>s\<^sub>t constr \<subseteq> (D' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X"
      unfolding D'_def constr_def unlabel_def by auto

    have "set (unlabel (dbproj i D)) \<subseteq> set (unlabel D)" unfolding unlabel_def by auto
    hence 2: "D' \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
      using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_vars_subset'[of F' "unlabel (dbproj i D)"] fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_mono
      unfolding D'_def by blast

    have 3: "fv\<^sub>l\<^sub>s\<^sub>t A' \<subseteq> ((fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<union> fv\<^sub>l\<^sub>s\<^sub>t A''"
      using 1 2 *(2) unfolding unlabel_def by fastforce

    have 4: "fv\<^sub>s\<^sub>s\<^sub>t AA \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel A)" by (metis ConsNegChecks.hyps(2) fv\<^sub>s\<^sub>s\<^sub>t_cons_subset)

    have 5: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
      using ConsNegChecks.hyps(2) unfolding unlabel_def by force

    show ?case using ** 3 4 5 by blast
  qed (fastforce simp add: unlabel_def)+

  show ?Q using assms
    apply (induct "unlabel A" arbitrary: A A' D rule: strand_sem_stateful_induct)
    by (fastforce simp add: unlabel_def)+
qed

lemma tr_par_vars_disj:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A D)" "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
  and "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
  shows "fv\<^sub>l\<^sub>s\<^sub>t A' \<inter> bvars\<^sub>l\<^sub>s\<^sub>t A' = {}"
using assms tr_par_vars_subset by fast

lemma tr_par_trms_subset:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A D)"
  shows "trms\<^sub>l\<^sub>s\<^sub>t A' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D"
using assms
proof (induction A D arbitrary: A' rule: tr\<^sub>p\<^sub>c.induct)
  case 1 thus ?case by simp
next
  case (2 i t A D)
  then obtain A'' where A'': "A' = (i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)" by moura
  hence "trms\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D"
    by (metis "2.IH")
  thus ?case using A'' by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (3 i t A D)
  then obtain A'' where A'': "A' = (i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
    by moura
  hence "trms\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D"
    by (metis "3.IH")
  thus ?case using A'' by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (4 i ac t t' A D)
  then obtain A'' where A'': "A' = (i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
    by moura
  hence "trms\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D"
    by (metis "4.IH")
  thus ?case using A'' by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (5 i t s A D)
  hence "A' \<in> set (tr\<^sub>p\<^sub>c A (List.insert (i,t,s) D))" by simp
  hence "trms\<^sub>l\<^sub>s\<^sub>t A' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union>
                      pair ` snd ` set (List.insert (i,t,s) D)"
    by (metis "5.IH")
  thus ?case by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (6 i t s A D)
  from 6 obtain Di A'' B C where A'':
      "Di \<in> set (subseqs (dbproj i D))" "A'' \<in> set (tr\<^sub>p\<^sub>c A [d\<leftarrow>D. d \<notin> set Di])" "A' = (B@C)@A''"
      "B = map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di"
      "C = map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>dbproj i D. d \<notin> set Di]"
    by moura
  hence "trms\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union>
                       pair ` snd ` set [d\<leftarrow>D. d \<notin> set Di]"
    by (metis "6.IH")
  moreover have "set [d\<leftarrow>D. d \<notin> set Di] \<subseteq> set D" using set_filter by auto
  ultimately have
      "trms\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D"
    by blast
  hence "trms\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel ((i,delete\<langle>t,s\<rangle>)#A)) \<union>
                        pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ((i,delete\<langle>t,s\<rangle>)#A)) \<union>
                        pair ` snd ` set D"
    using setops\<^sub>s\<^sub>s\<^sub>t_cons_subset trms\<^sub>s\<^sub>s\<^sub>t_cons
    by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  moreover have "set Di \<subseteq> set D" "set [d\<leftarrow>dbproj i D . d \<notin> set Di] \<subseteq> set D"
    using subseqs_set_subset[OF A''(1)] by auto
  hence "trms\<^sub>s\<^sub>t (unlabel B) \<subseteq> insert (pair (t, s)) (pair ` snd ` set D)"
        "trms\<^sub>s\<^sub>t (unlabel C) \<subseteq> insert (pair (t, s)) (pair ` snd ` set D)"
    using A''(4,5) unfolding unlabel_def by auto
  hence "trms\<^sub>s\<^sub>t (unlabel (B@C)) \<subseteq> insert (pair (t,s)) (pair ` snd ` set D)"
    using unlabel_append[of B C] by auto
  moreover have "pair (t,s) \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (delete\<langle>t,s\<rangle>#unlabel A)" by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
  ultimately show ?case
    using A''(3) trms\<^sub>s\<^sub>t_append[of "unlabel (B@C)" "unlabel A'"] unlabel_append[of "B@C" A'']
    by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (7 i ac t s A D)
  from 7 obtain d A'' where A'':
      "d \<in> set (dbproj i D)" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
      "A' = (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#A''"
    by moura
  hence "trms\<^sub>l\<^sub>s\<^sub>t A'' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union>
                       pair ` snd ` set D"
    by (metis "7.IH")
  moreover have "trms\<^sub>s\<^sub>t (unlabel A') = {pair (t,s), pair (snd d)} \<union> trms\<^sub>s\<^sub>t (unlabel A'')"
    using A''(1,3) by auto
  ultimately show ?case using A''(1) by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
next
  case (8 i X F F' A D)
  define constr where "constr = map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"
  define B where "B \<equiv> \<Union>(trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ` set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D))))"

  from 8 obtain A'' where A'':
      "A'' \<in> set (tr\<^sub>p\<^sub>c A D)" "A' = constr@A''"
    unfolding constr_def by moura

  have "trms\<^sub>s\<^sub>t (unlabel A'') \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair`snd`set D"
    by (metis A''(1) "8.IH")
  moreover have "trms\<^sub>s\<^sub>t (unlabel constr) \<subseteq> B \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` snd ` set D"
    unfolding unlabel_def constr_def B_def by auto
  ultimately have "trms\<^sub>s\<^sub>t (unlabel A') \<subseteq> B \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union>
                                         pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D"
    using A'' unlabel_append[of constr A''] by auto
  moreover have "set (dbproj i D) \<subseteq> set D" by auto
  hence "B \<subseteq> pair ` set F' \<union> pair ` snd ` set D"
    using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_trms_subset'[of F' "map snd (dbproj i D)"]
    unfolding B_def by force
  moreover have
      "pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ((i, \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>)#A)) =
       pair ` set F' \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
    by auto
  ultimately show ?case by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
qed

lemma tr_par_wf_trms:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A [])" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t (unlabel A))"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>t A')"
using tr_par_trms_subset[OF assms(1)] setops\<^sub>s\<^sub>s\<^sub>t_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s(2)[OF assms(2)]
by auto

lemma tr_par_wf':
  assumes "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
  and "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X"
  and "wf'\<^sub>s\<^sub>s\<^sub>t X (unlabel A)" "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
  and "A' \<in> set (tr\<^sub>p\<^sub>c A D)"
  shows "wf\<^sub>l\<^sub>s\<^sub>t X A'"
proof -
  define P where
    "P = (\<lambda>(D::('fun,'var,'lbl) labeleddbstatelist) (A::('fun,'var,'lbl) labeled_stateful_strand).
          (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}) \<and>
          fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {})"

  have "P D A" using assms(1,4) by (simp add: P_def)
  with assms(5,3,2) show ?thesis
  proof (induction A arbitrary: X A' D)
    case Nil thus ?case by simp
  next
    case (Cons a A)
    obtain i s where i: "a = (i,s)" by (metis surj_pair)
    note prems = Cons.prems
    note IH = Cons.IH
    show ?case
    proof (cases s)
      case (Receive t)
      note si = Receive i
      then obtain A'' where A'': "A' = (i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)" "fv t \<subseteq> X"
        using prems unlabel_Cons(1)[of i s A] by moura
      have *: "wf'\<^sub>s\<^sub>s\<^sub>t X (unlabel A)"
              "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X"
              "P D A"
        using prems si apply (force, force)
        using prems(4) si unfolding P_def by fastforce
      show ?thesis using IH[OF A''(2) *] A''(1,3) by simp
    next
      case (Send t)
      note si = Send i
      then obtain A'' where A'': "A' = (i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
        using prems by moura
      have *: "wf'\<^sub>s\<^sub>s\<^sub>t (X \<union> fv t) (unlabel A)"
              "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X \<union> fv t"
              "P D A"
        using prems si apply (force, force)
        using prems(4) si unfolding P_def by fastforce
      show ?thesis using IH[OF A''(2) *] A''(1) by simp
    next
      case (Equality ac t t')
      note si = Equality i
      then obtain A'' where A'':
          "A' = (i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
          "ac = Assign \<Longrightarrow> fv t' \<subseteq> X"
        using prems unlabel_Cons(1)[of i s] by moura
      have *: "ac = Assign \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t (X \<union> fv t) (unlabel A)"
              "ac = Check \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t X (unlabel A)"
              "ac = Assign \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X \<union> fv t"
              "ac = Check \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X"
              "P D A"
        using prems si apply (force, force, force, force)
        using prems(4) si unfolding P_def by fastforce
      show ?thesis
        using IH[OF A''(2) *(1,3,5)] IH[OF A''(2) *(2,4,5)] A''(1,3)
        by (cases ac) simp_all
    next
      case (Insert t t')
      note si = Insert i
      hence A': "A' \<in> set (tr\<^sub>p\<^sub>c A (List.insert (i,t,t') D))" "fv t \<subseteq> X" "fv t' \<subseteq> X"
        using prems by auto
      have *: "wf'\<^sub>s\<^sub>s\<^sub>t X (unlabel A)" "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel (List.insert (i,t,t') D)) \<subseteq> X"
        using prems si by (auto simp add: unlabel_def)
      have **: "P (List.insert (i,t,t') D) A"
        using prems(4) si
        unfolding P_def unlabel_def
        by fastforce
      show ?thesis using IH[OF A'(1) * **] A'(2,3) by simp
    next
      case (Delete t t')
      note si = Delete i
      define constr where "constr = (\<lambda>Di.
        (map (\<lambda>d. (i,\<langle>check: (pair (t,t')) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
        (map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,t'), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>dbproj i D. d \<notin> set Di]))"
      from prems si obtain Di A'' where A'':
          "A' = constr Di@A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A [d\<leftarrow>D. d \<notin> set Di])"
          "Di \<in> set (subseqs (dbproj i D))"
        unfolding constr_def by auto
      have *: "wf'\<^sub>s\<^sub>s\<^sub>t X (unlabel A)"
              "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel (filter (\<lambda>d. d \<notin> set Di) D)) \<subseteq> X"
        using prems si apply simp
        using prems si by (fastforce simp add: unlabel_def)

      have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel (filter (\<lambda>d. d \<notin> set Di) D)) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D)"
        by (auto simp add: unlabel_def)
      hence **: "P [d\<leftarrow>D. d \<notin> set Di] A"
        using prems si unfolding P_def
        by fastforce

      have ***: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X" using prems si by auto
      show ?thesis
        using IH[OF A''(2) * **] A''(1) wf_pair_eqs_ineqs_map'[OF _ A''(3) ***]
        unfolding constr_def by simp
    next
      case (InSet ac t t')
      note si = InSet i
      then obtain d A'' where A'':
          "A' = (i,\<langle>ac: (pair (t,t')) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#A''"
          "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
          "d \<in> set D"
        using prems by moura
      have *:
          "ac = Assign \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t (X \<union> fv t \<union> fv t') (unlabel A)"
          "ac = Check \<Longrightarrow> wf'\<^sub>s\<^sub>s\<^sub>t X (unlabel A)"
          "ac = Assign \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X \<union> fv t \<union> fv t'"
          "ac = Check \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X"
          "P D A"
        using prems si apply (force, force, force, force)
        using prems(4) si unfolding P_def by fastforce
      have **: "fv (pair (snd d)) \<subseteq> X"
        using A''(3) prems(3) fv_pair_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subset
        by fast
      have ***: "fv (pair (t,t')) = fv t \<union> fv t'" unfolding pair_def by auto
      show ?thesis
        using IH[OF A''(2) *(1,3,5)] IH[OF A''(2) *(2,4,5)] A''(1) ** ***
        by (cases ac) (simp_all add: Un_assoc)
    next
      case (NegChecks Y F F')
      note si = NegChecks i
      then obtain A'' where A'':
          "A' = (map (\<lambda>G. (i,\<forall>Y\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D))))@A''"
          "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
        using prems by moura

      have *: "wf'\<^sub>s\<^sub>s\<^sub>t X (unlabel A)" "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<subseteq> X" using prems si by auto

      have "bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel ((i,\<forall>Y\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>)#A))"
           "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel ((i,\<forall>Y\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>)#A))"
        by auto
      hence **:  "P D A" using prems si unfolding P_def by blast

      show ?thesis using IH[OF A''(2) * **] A''(1) wf_pair_negchecks_map' by simp
    qed
  qed
qed

lemma tr_par_wf:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A [])"
    and "wf\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "wf\<^sub>l\<^sub>s\<^sub>t {} A'"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>t A')"
    and "fv\<^sub>l\<^sub>s\<^sub>t A' \<inter> bvars\<^sub>l\<^sub>s\<^sub>t A' = {}"
using tr_par_wf'[OF _ _ _ _ assms(1)]
      tr_par_wf_trms[OF assms(1,3)]
      tr_par_vars_disj[OF assms(1)]
      assms(2)
by fastforce+

lemma tr_par_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A D)" "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel A)"
  and "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}" (is "?P0 A D")
  and "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel D) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}" (is "?P1 A D")
  and "\<forall>t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D.
       \<forall>t' \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` snd ` set D.
          (\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t'" (is "?P3 A D")
  shows "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A')"
proof -
  have sublmm: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel A)" "?P0 A D" "?P1 A D" "?P3 A D"
    when p: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (a#A))" "?P0 (a#A) D" "?P1 (a#A) D" "?P3 (a#A) D"
    for a A D
  proof -
    show "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel A)" using p(1) by (simp add: unlabel_def tfr\<^sub>s\<^sub>s\<^sub>t_def)
    show "?P0 A D" using p(2) fv\<^sub>s\<^sub>s\<^sub>t_cons_subset unfolding unlabel_def by fastforce
    show "?P1 A D" using p(3) bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset unfolding unlabel_def by fastforce
    have "setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (unlabel (a#A))"
      using setops\<^sub>s\<^sub>s\<^sub>t_cons_subset unfolding unlabel_def by auto
    thus "?P3 A D" using p(4) by blast
  qed

  show ?thesis using assms
  proof (induction A D arbitrary: A' rule: tr\<^sub>p\<^sub>c.induct)
    case 1 thus ?case by simp
  next
    case (2 i t A D)
    note prems = "2.prems"
    note IH = "2.IH"
    from prems(1) obtain A'' where A'': "A' = (i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)" by moura
    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A'')"
      using IH[OF A''(2)] prems(5) sublmm[OF prems(2,3,4,5)]
      by meson
    thus ?case using A''(1) by simp
  next
    case (3 i t A D)
    note prems = "3.prems"
    note IH = "3.IH"
    from prems(1) obtain A'' where A'': "A' = (i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)" by moura
    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A'')"
      using IH[OF A''(2)] prems(5) sublmm[OF prems(2,3,4,5)]
      by meson
    thus ?case using A''(1) by simp
  next
    case (4 i ac t t' A D)
    note prems = "4.prems"
    note IH = "4.IH"
    from prems(1) obtain A'' where A'': "A' = (i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)" by moura
    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A'')"
      using IH[OF A''(2)] prems(5) sublmm[OF prems(2,3,4,5)]
      by meson
    thus ?case using A''(1) prems(2) by simp
  next
    case (5 i t s A D)
    note prems = "5.prems"
    note IH = "5.IH"
    from prems(1) have A': "A' \<in> set (tr\<^sub>p\<^sub>c A (List.insert (i,t,s) D))" by simp

    have 1: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel A)" using sublmm[OF prems(2,3,4,5)] by simp

    have "pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ((i,insert\<langle>t,s\<rangle>)#A)) \<union> pair`snd`set D =
          pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair`snd`set (List.insert (i,t,s) D)"
      by (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    hence 3: "?P3 A (List.insert (i,t,s) D)" using prems(5) by metis
    moreover have "?P1 A (List.insert (i,t,s) D)"
      using prems(3,4) bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset[of "unlabel A" "insert\<langle>t,s\<rangle>"]
      unfolding unlabel_def
      by fastforce
    ultimately have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A')"
      using IH[OF A' sublmm(1,2)[OF prems(2,3,4,5)] _ 3] by metis
    thus ?case using A'(1) by auto
  next
    case (6 i t s A D)
    note prems = "6.prems"
    note IH = "6.IH"

    define constr where constr: "constr \<equiv> (\<lambda>Di.
      (map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
      (map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) (filter (\<lambda>d. d \<notin> set Di) (dbproj i D))))"

    from prems(1) obtain Di A'' where A'':
        "A' = constr Di@A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A (filter (\<lambda>d. d \<notin> set Di) D))"
        "Di \<in> set (subseqs (dbproj i D))"
      unfolding constr by fastforce

    define Q1 where "Q1 \<equiv> (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
        \<forall>x \<in> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X. \<exists>a. \<Gamma> (Var x) = TAtom a)"
    define Q2 where "Q2 \<equiv> (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
        \<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))"

    have "pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair`snd`set [d\<leftarrow>D. d \<notin> set Di]
            \<subseteq> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ((i,delete\<langle>t,s\<rangle>)#A)) \<union> pair`snd`set D"
      using subseqs_set_subset[OF A''(3)] by (force simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    moreover have "\<forall>a\<in>M. \<forall>b\<in>M. P a b"
      when "M \<subseteq> N" "\<forall>a\<in>N. \<forall>b\<in>N. P a b"
      for M N::"('fun, 'var) terms" and  P
      using that by blast
    ultimately have *: "?P3 A (filter (\<lambda>d. d \<notin> set Di) D)"
      using prems(5) by presburger

    have **: "?P1 A (filter (\<lambda>d. d \<notin> set Di) D)"
      using prems(4) bvars\<^sub>s\<^sub>s\<^sub>t_cons_subset[of "unlabel A" "delete\<langle>t,s\<rangle>"]
      unfolding unlabel_def by fastforce

    have 1: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A'')"
      using IH[OF A''(3,2) sublmm(1,2)[OF prems(2,3,4,5)] ** *]
      by metis

    have 2: "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A'') \<or>
             (\<exists>d \<in> set Di. u = pair (t,s) \<and> u' = pair (snd d))"
      when "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A')" for ac u u'
      using that A''(1) unfolding constr unlabel_def by force
    have 3:
        "\<forall>X\<langle>\<or>\<noteq>: u\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A'') \<or>
         (\<exists>d \<in> set (filter (\<lambda>d. d \<notin> set Di) D). u = [(pair (t,s), pair (snd d))] \<and> Q2 u X)"
      when "\<forall>X\<langle>\<or>\<noteq>: u\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A')" for X u
      using that A''(1) unfolding Q2_def constr unlabel_def by force
    have 4: "\<forall>d\<in>set D. (\<exists>\<delta>. Unifier \<delta> (pair (t,s)) (pair (snd d)))
                       \<longrightarrow> \<Gamma> (pair (t,s)) = \<Gamma> (pair (snd d))"
      using prems(5) by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

    { fix ac u u'
      assume a: "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A')" "\<exists>\<delta>. Unifier \<delta> u u'"
      hence "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A'') \<or> (\<exists>d \<in> set Di. u = pair (t,s) \<and> u' = pair (snd d))"
        using 2 by metis
      moreover {
        assume "\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A'')"
        hence "tfr\<^sub>s\<^sub>t\<^sub>p (\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t)"
          using 1 Ball_set_list_all[of "unlabel A''" tfr\<^sub>s\<^sub>t\<^sub>p]
          by fast
      } moreover {
        fix d assume "d \<in> set Di" "u = pair (t,s)" "u' = pair (snd d)"
        hence "\<exists>\<delta>. Unifier \<delta> u u' \<Longrightarrow> \<Gamma> u = \<Gamma> u'"
          using 4 dbproj_subseq_subset A''(3)
          by fast
        hence "tfr\<^sub>s\<^sub>t\<^sub>p (\<langle>ac: u \<doteq> u'\<rangle>\<^sub>s\<^sub>t)"
          using Ball_set_list_all[of "unlabel A''" tfr\<^sub>s\<^sub>t\<^sub>p]
          by simp
        hence "\<Gamma> u = \<Gamma> u'" using tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of "unlabel A''"]
          using a(2) unfolding unlabel_def by auto
      } ultimately have "\<Gamma> u = \<Gamma> u'"
          using tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of "unlabel A''"] a(2)
          unfolding unlabel_def by auto
    } moreover {
      fix u U
      assume "\<forall>U\<langle>\<or>\<noteq>: u\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A')"
      hence "\<forall>U\<langle>\<or>\<noteq>: u\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel A'') \<or>
             (\<exists>d \<in> set (filter (\<lambda>d. d \<notin> set Di) D). u = [(pair (t,s), pair (snd d))] \<and> Q2 u U)"
        using 3 by metis
      hence "Q1 u U \<or> Q2 u U"
        using 1 4 subseqs_set_subset[OF A''(3)] tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of "unlabel A''"]
        unfolding Q1_def Q2_def
        by blast
    } ultimately show ?case
      using tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of "unlabel A'"] unfolding Q1_def Q2_def unlabel_def by blast
  next
    case (7 i ac t s A D)
    note prems = "7.prems"
    note IH = "7.IH"

    from prems(1) obtain d A'' where A'':
        "A' = (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#A''"
        "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
        "d \<in> set (dbproj i D)"
      by moura

    have 1: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A'')"
      using IH[OF A''(2) sublmm(1,2,3)[OF prems(2,3,4,5)] sublmm(4)[OF prems(2,3,4,5)]]
      by metis

    have 2: "\<Gamma> (pair (t,s)) = \<Gamma> (pair (snd d))"
      when "\<exists>\<delta>. Unifier \<delta> (pair (t,s)) (pair (snd d))"
      using that prems(2,5) A''(3) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

    show ?case using A''(1) 1 2 by fastforce
  next
    case (8 i X F F' A D)
    note prems = "8.prems"
    note IH = "8.IH"

    define constr where
      "constr = map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"

    define Q1 where "Q1 \<equiv> (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
        \<forall>x \<in> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) - set X. \<exists>a. \<Gamma> (Var x) = TAtom a)"

    define Q2 where "Q2 \<equiv> (\<lambda>(M::('fun,'var) terms) X.
        \<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))"

    have Q2_subset: "Q2 M' X" when "M' \<subseteq> M" "Q2 M X" for X M M'
      using that unfolding Q2_def by auto

    have Q2_supset: "Q2 (M \<union> M') X" when "Q2 M X" "Q2 M' X" for X M M'
      using that unfolding Q2_def by auto

    from prems obtain A'' where A'': "A' = constr@A''" "A'' \<in> set (tr\<^sub>p\<^sub>c A D)"
      using constr_def by moura

    have 0: "constr = [(i,\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]" when "F' = []" using that unfolding constr_def by simp

    have 1: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A'')"
      using IH[OF A''(2) sublmm(1,2,3)[OF prems(2,3,4,5)] sublmm(4)[OF prems(2,3,4,5)]]
      by metis

    have 2: "(F' = [] \<and> Q1 F X) \<or> Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') X"
      using prems(2) unfolding Q1_def Q2_def by simp

    have 3: "F' = [] \<Longrightarrow> Q1 F X \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel constr)"
      using 0 2 tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of "unlabel constr"] unfolding Q1_def by auto

    { fix c assume "c \<in> set (unlabel constr)"
      hence "\<exists>G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D))). c = \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t"
        unfolding constr_def unlabel_def by force
    } moreover {
      fix G
      assume G: "G \<in> set (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"
         and c: "\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t \<in> set (unlabel constr)"
         and e: "Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') X"

      have d_Q2: "Q2 (pair ` set (map snd D)) X" unfolding Q2_def
      proof (intro allI impI)
        fix f T assume "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (pair ` set (map snd D))"
        then obtain d where d: "d \<in> set (map snd D)" "Fun f T \<in> subterms (pair d)" by force
        hence "fv (pair d) \<inter> set X = {}"
          using prems(4) unfolding pair_def by (force simp add: unlabel_def)
        thus "T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X)"
          by (metis fv_disj_Fun_subterm_param_cases d(2))
      qed

      have "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F@G) \<subseteq> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F' \<union> pair ` set (map snd D)"
        using tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_trms_subset[OF G] by force
      hence "Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F@G)) X" using Q2_subset[OF _ Q2_supset[OF e d_Q2]] by metis
      hence "tfr\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)" by (metis Q2_def tfr\<^sub>s\<^sub>t\<^sub>p.simps(2))
    } ultimately have 4:
        "Q2 (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> pair ` set F') X \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel constr)"
      using Ball_set by blast

    have 5: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel constr)" using 2 3 4 by metis

    show ?case using 1 5 A''(1) by (simp add: unlabel_def)
  qed
qed

lemma tr_par_tfr:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A [])" and "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
    and "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
  shows "tfr\<^sub>s\<^sub>t (unlabel A')"
proof -
  have *: "trms\<^sub>l\<^sub>s\<^sub>t A' \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
    using tr_par_trms_subset[OF assms(1)] by simp
  hence "SMP (trms\<^sub>l\<^sub>s\<^sub>t A') \<subseteq> SMP (trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A))"
    using SMP_mono by simp
  moreover have "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A))"
    using assms(2) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by fast
  ultimately have 1: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>t A')" by (metis tfr_subset(2)[OF _ *])

  have **: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel A)" using assms(2) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by fast
  have "pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<subseteq>
        SMP (trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)) - Var`\<V>"
    using setops\<^sub>s\<^sub>s\<^sub>t_are_pairs unfolding pair_def by auto
  hence "\<Gamma> t = \<Gamma> t'"
    when "\<exists>\<delta>. Unifier \<delta> t t'" "t \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)" "t' \<in> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
    for t t'
    using that assms(2) unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  moreover have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (unlabel []) = {}" "pair ` snd ` set [] = {}" by auto
  ultimately have 2: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (unlabel A')"
    using tr_par_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p[OF assms(1) ** assms(3)] by simp

  show ?thesis by (metis 1 2 tfr\<^sub>s\<^sub>t_def)
qed

lemma tr_par_proj:
  assumes "B \<in> set (tr\<^sub>p\<^sub>c A D)"
  shows "proj n B \<in> set (tr\<^sub>p\<^sub>c (proj n A) (proj n D))"
using assms
proof (induction A D arbitrary: B rule: tr\<^sub>p\<^sub>c.induct)
  case (5 i t s S D)
  note prems = "5.prems"
  note IH = "5.IH"
  have IH': "proj n B \<in> set (tr\<^sub>p\<^sub>c (proj n S) (proj n (List.insert (i,t,s) D)))"
    using prems IH by auto
  show ?case
  proof (cases "(i = ln n) \<or> (i = \<star>)")
    case True thus ?thesis
      using IH' proj_list_insert(1,2)[of n "(t,s)" D] proj_list_Cons(1,2)[of n _ S]
      by auto
  next
    case False
    then obtain m where "i = ln m" "n \<noteq> m" by (cases i) simp_all
    thus ?thesis
      using IH' proj_list_insert(3)[of n _ "(t,s)" D] proj_list_Cons(3)[of n _ "insert\<langle>t,s\<rangle>" S]
      by auto
  qed
next
  case (6 i t s S D)
  note prems = "6.prems"
  note IH = "6.IH"
  define constr where "constr = (\<lambda>Di D.
      (map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
      (map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>dbproj i D. d \<notin> set Di]))"

  obtain Di B' where B':
      "B = constr Di D@B'"
      "Di \<in> set (subseqs (dbproj i D))"
      "B' \<in> set (tr\<^sub>p\<^sub>c S [d\<leftarrow>D. d \<notin> set Di])"
    using prems constr_def by fastforce
  hence "proj n B' \<in> set (tr\<^sub>p\<^sub>c (proj n S) (proj n [d\<leftarrow>D. d \<notin> set Di]))" using IH by simp
  hence IH': "proj n B' \<in> set (tr\<^sub>p\<^sub>c (proj n S) [d\<leftarrow>proj n D. d \<notin> set Di])" by (metis proj_filter)
  show ?case
  proof (cases "(i = ln n) \<or> (i = \<star>)")
    case True
    hence "proj n B = constr Di D@proj n B'" "Di \<in> set (subseqs (dbproj i (proj n D)))"
      using B'(1,2) proj_dbproj(1,2)[of n D] unfolding proj_def constr_def by auto
    moreover have "constr Di (proj n D) = constr Di D"
      using True proj_dbproj(1,2)[of n D] unfolding constr_def by presburger
    ultimately have "proj n B \<in> set (tr\<^sub>p\<^sub>c ((i, delete\<langle>t,s\<rangle>)#proj n S) (proj n D))"
      using IH' unfolding constr_def by force
    thus ?thesis by (metis proj_list_Cons(1,2) True)
  next
    case False
    then obtain m where m: "i = ln m" "n \<noteq> m" by (cases i) simp_all
    hence *: "(ln n) \<noteq> i" by simp
    have "proj n B = proj n B'" using B'(1) False unfolding constr_def proj_def by auto
    moreover have "[d\<leftarrow>proj n D. d \<notin> set Di] = proj n D"
      using proj_subseq[OF _ m(2)[symmetric]] m(1) B'(2) by simp
    ultimately show ?thesis using m(1) IH' proj_list_Cons(3)[OF m(2), of _ S] by auto
  qed
next
  case (7 i ac t s S D)
  note prems = "7.prems"
  note IH = "7.IH"
  define constr where "constr = (
    \<lambda>d::'lbl strand_label \<times> ('fun,'var) term \<times> ('fun,'var) term.
      (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t))"

  obtain d B' where B':
      "B = constr d#B'"
      "d \<in> set (dbproj i D)"
      "B' \<in> set (tr\<^sub>p\<^sub>c S D)"
    using prems constr_def by fastforce
  hence IH': "proj n B' \<in> set (tr\<^sub>p\<^sub>c (proj n S) (proj n D))" using IH by auto

  show ?case
  proof (cases "(i = ln n) \<or> (i = \<star>)")
    case True
    hence "proj n B = constr d#proj n B'" "d \<in> set (dbproj i (proj n D))"
      using B' proj_list_Cons(1,2)[of n _ B']
      unfolding constr_def
      by (force, metis proj_dbproj(1,2))
    hence "proj n B \<in> set (tr\<^sub>p\<^sub>c ((i, InSet ac t s)#proj n S) (proj n D))"
      using IH' unfolding constr_def by auto
    thus ?thesis using proj_list_Cons(1,2)[of n _ S] True by metis
  next
    case False
    then obtain m where m: "i = ln m" "n \<noteq> m" by (cases i) simp_all
    hence "proj n B = proj n B'" using B'(1) proj_list_Cons(3) unfolding constr_def by auto
    thus ?thesis
      using IH' m proj_list_Cons(3)[OF m(2), of "InSet ac t s" S]
      unfolding constr_def
      by auto
  qed
next
  case (8 i X F F' S D)
  note prems = "8.prems"
  note IH = "8.IH"

  define constr where
    "constr = (\<lambda>D. map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D))))"

  obtain B' where B':
      "B = constr D@B'"
      "B' \<in> set (tr\<^sub>p\<^sub>c S D)"
    using prems constr_def by fastforce
  hence IH': "proj n B' \<in> set (tr\<^sub>p\<^sub>c (proj n S) (proj n D))" using IH by auto

  show ?case
  proof (cases "(i = ln n) \<or> (i = \<star>)")
    case True
    hence "proj n B = constr (proj n D)@proj n B'"
      using B'(1,2) proj_dbproj(1,2)[of n D] unfolding proj_def constr_def by auto
    hence "proj n B \<in> set (tr\<^sub>p\<^sub>c ((i, NegChecks X F F')#proj n S) (proj n D))"
      using IH' unfolding constr_def by auto
    thus ?thesis using proj_list_Cons(1,2)[of n _ S] True by metis
  next
    case False
    then obtain m where m: "i = ln m" "n \<noteq> m" by (cases i) simp_all
    hence "proj n B = proj n B'" using B'(1) unfolding constr_def proj_def by auto
    thus ?thesis
      using IH' m proj_list_Cons(3)[OF m(2), of "NegChecks X F F'" S]
      unfolding constr_def
      by auto
  qed
qed (force simp add: proj_def)+

lemma tr_par_preserves_typing_cond:
  assumes "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A Sec" "typing_cond\<^sub>s\<^sub>s\<^sub>t (unlabel A)" "A' \<in> set (tr\<^sub>p\<^sub>c A [])"
  shows "typing_cond (unlabel A')"
proof -
  have "wf'\<^sub>s\<^sub>s\<^sub>t {} (unlabel A)"
       "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
       "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>s\<^sub>t (unlabel A))"
    using assms(2) unfolding typing_cond\<^sub>s\<^sub>s\<^sub>t_def by simp_all
  hence 1: "wf\<^sub>s\<^sub>t {} (unlabel A')"
           "fv\<^sub>s\<^sub>t (unlabel A') \<inter> bvars\<^sub>s\<^sub>t (unlabel A') = {}"
           "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t (unlabel A'))"
           "Ana_invar_subst (ik\<^sub>s\<^sub>t (unlabel A') \<union> assignment_rhs\<^sub>s\<^sub>t (unlabel A'))"
    using tr_par_wf[OF assms(3)] Ana_invar_subst' by metis+

  have 2: "tfr\<^sub>s\<^sub>t (unlabel A')" by (metis tr_par_tfr assms(2,3) typing_cond\<^sub>s\<^sub>s\<^sub>t_def)

  show ?thesis by (metis 1 2 typing_cond_def)
qed

lemma tr_par_preserves_par_comp:
  assumes "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A Sec" "A' \<in> set (tr\<^sub>p\<^sub>c A [])"
  shows "par_comp A' Sec"
proof -
  let ?M = "\<lambda>l. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l A)"
  let ?N = "\<lambda>l. trms_proj\<^sub>l\<^sub>s\<^sub>t l A'"

  have 0: "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (?M l1) (?M l2) Sec"
    using assms(1) unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by simp_all

  { fix l1 l2::'lbl assume *: "l1 \<noteq> l2"
    hence "GSMP_disjoint (?M l1) (?M l2) Sec" using 0(1) by metis
    moreover have "pair ` snd ` set (proj n []) = {}" for n::'lbl unfolding proj_def by simp
    hence "?N l1 \<subseteq> ?M l1" "?N l2 \<subseteq> ?M l2"
      using tr_par_trms_subset[OF tr_par_proj[OF assms(2)]] by (metis Un_empty_right)+
    ultimately have "GSMP_disjoint (?N l1) (?N l2) Sec"
      using GSMP_disjoint_subset by presburger
  } hence 1: "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (trms_proj\<^sub>l\<^sub>s\<^sub>t l1 A') (trms_proj\<^sub>l\<^sub>s\<^sub>t l2 A') Sec"
    using 0(1) by metis

  have 2: "ground Sec" "\<forall>s \<in> Sec. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Sec"
    using assms(1) unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by metis+

  show ?thesis using 1 2 unfolding par_comp_def by metis
qed

lemma tr_leaking_prefix_exists:
  assumes "A' \<in> set (tr\<^sub>p\<^sub>c A [])" "prefix B A'" "ik\<^sub>s\<^sub>t (proj_unl n B) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
  shows "\<exists>C D. prefix C B \<and> prefix D A \<and> C \<in> set (tr\<^sub>p\<^sub>c D []) \<and> (ik\<^sub>s\<^sub>t (proj_unl n C) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>)"
proof -
  let ?P = "\<lambda>B C C'. B = C@C' \<and> (\<forall>n t. (n, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<notin> set C') \<and>
                     (C = [] \<or> (\<exists>n t. suffix [(n,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] C))"
  have "\<exists>C C'. ?P B C C'"
  proof (induction B)
    case (Cons b B)
    then obtain C C' n s where *: "?P B C C'" "b = (n,s)" by moura
    show ?case
    proof (cases "C = []")
      case True
      note T = True
      show ?thesis
      proof (cases "\<exists>t. s = receive\<langle>t\<rangle>\<^sub>s\<^sub>t")
        case True
        hence "?P (b#B) [b] C'" using * T  by auto
        thus ?thesis by metis
      next
        case False
        hence "?P (b#B) [] (b#C')" using * T by auto
        thus ?thesis by metis
      qed
    next
      case False
      hence "?P (b#B) (b#C) C'" using * unfolding suffix_def by auto
      thus ?thesis by metis
    qed
  qed simp
  then obtain C C' where C:
      "B = C@C'" "\<forall>n t. (n, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<notin> set C'"
      "C = [] \<or> (\<exists>n t. suffix [(n,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] C)"
    by moura
  hence 1: "prefix C B" by simp
  hence 2: "prefix C A'" using assms(2) by simp

  have "\<And>m t. (m,receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<in> set B \<Longrightarrow> (m,receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<in> set C" using C by auto
  hence "\<And>t. receive\<langle>t\<rangle>\<^sub>s\<^sub>t \<in> set (proj_unl n B) \<Longrightarrow> receive\<langle>t\<rangle>\<^sub>s\<^sub>t \<in> set (proj_unl n C)"
    unfolding unlabel_def proj_def by force
  hence "ik\<^sub>s\<^sub>t (proj_unl n B) \<subseteq> ik\<^sub>s\<^sub>t (proj_unl n C)" using ik\<^sub>s\<^sub>t_is_rcv_set by auto
  hence 3: "ik\<^sub>s\<^sub>t (proj_unl n C) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" by (metis ideduct_mono[OF assms(3)] subst_all_mono)

  { fix D E m t assume  "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E" "prefix E A'" "A' \<in> set (tr\<^sub>p\<^sub>c A D)"
    hence "\<exists>F. prefix F A \<and> E \<in> set (tr\<^sub>p\<^sub>c F D)"
    proof (induction A D arbitrary: A' E rule: tr\<^sub>p\<^sub>c.induct)
      case (1 D) thus ?case by simp
    next
      case (2 i t' S D)
      note prems = "2.prems"
      note IH = "2.IH"
      obtain A'' where *: "A' = (i,send\<langle>t'\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c S D)"
        using prems(3) by auto
      have "E \<noteq> []" using prems(1) by auto
      then obtain E' where **: "E = (i,send\<langle>t'\<rangle>\<^sub>s\<^sub>t)#E'"
        using *(1) prems(2) by (cases E) auto
      hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'" "prefix E' A''"
        using *(1) prems(1,2) suffix_Cons[of _ _ E'] by auto
      then obtain F where "prefix F S" "E' \<in> set (tr\<^sub>p\<^sub>c F D)"
        using *(2) ** IH by metis
      hence "prefix ((i,Send t')#F) ((i,Send t')#S)" "E \<in> set (tr\<^sub>p\<^sub>c ((i,Send t')#F) D)"
        using ** by auto
      thus ?case by metis
    next
      case (3 i t' S D)
      note prems = "3.prems"
      note IH = "3.IH"
      obtain A'' where *: "A' = (i,receive\<langle>t'\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c S D)"
        using prems(3) by auto
      have "E \<noteq> []" using prems(1) by auto
      then obtain E' where **: "E = (i,receive\<langle>t'\<rangle>\<^sub>s\<^sub>t)#E'"
        using *(1) prems(2) by (cases E) auto
      show ?case
      proof (cases "(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) = (i, receive\<langle>t'\<rangle>\<^sub>s\<^sub>t)")
        case True
        note T = True
        show ?thesis
        proof (cases "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'")
          case True
          hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'" "prefix E' A''"
            using ** *(1) prems(1,2) by auto
          then obtain F where "prefix F S" "E' \<in> set (tr\<^sub>p\<^sub>c F D)"
            using *(2) ** IH by metis
          hence "prefix ((i,receive\<langle>t'\<rangle>)#F) ((i,receive\<langle>t'\<rangle>)#S)"
                "E \<in> set (tr\<^sub>p\<^sub>c ((i,receive\<langle>t'\<rangle>)#F) D)"
            using ** by auto
          thus ?thesis by metis
        next
          case False
          hence "E' = []"
            using **(1) T prems(1)
                  suffix_Cons[of "[(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]" "(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)" E']
            by auto
          hence "prefix [(i,receive\<langle>t'\<rangle>)] ((i,receive\<langle>t'\<rangle>) # S) \<and> E \<in> set (tr\<^sub>p\<^sub>c [(i,receive\<langle>t'\<rangle>)] D)"
            using * ** prems by auto
          thus ?thesis by metis
        qed
      next
        case False
        hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'" "prefix E' A''"
          using ** *(1) prems(1,2) suffix_Cons[of _ _ E'] by auto
        then obtain F where "prefix F S" "E' \<in> set (tr\<^sub>p\<^sub>c F D)" using *(2) ** IH by metis
        hence "prefix ((i,receive\<langle>t'\<rangle>)#F) ((i,receive\<langle>t'\<rangle>)#S)" "E \<in> set (tr\<^sub>p\<^sub>c ((i,receive\<langle>t'\<rangle>)#F) D)"
          using ** by auto
        thus ?thesis by metis
      qed
    next
      case (4 i ac t' t'' S D)
      note prems = "4.prems"
      note IH = "4.IH"
      obtain A'' where *: "A' = (i,\<langle>ac: t' \<doteq> t''\<rangle>\<^sub>s\<^sub>t)#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c S D)"
        using prems(3) by auto
      have "E \<noteq> []" using prems(1) by auto
      then obtain E' where **: "E = (i,\<langle>ac: t' \<doteq> t''\<rangle>\<^sub>s\<^sub>t)#E'"
        using *(1) prems(2) by (cases E) auto
      hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'" "prefix E' A''"
        using *(1) prems(1,2) suffix_Cons[of _ _ E'] by auto
      then obtain F where "prefix F S" "E' \<in> set (tr\<^sub>p\<^sub>c F D)"
        using *(2) ** IH by metis
      hence "prefix ((i,Equality ac t' t'')#F) ((i,Equality ac t' t'')#S)"
            "E \<in> set (tr\<^sub>p\<^sub>c ((i,Equality ac t' t'')#F) D)"
        using ** by auto
      thus ?case by metis
    next
      case (5 i t' s S D)
      note prems = "5.prems"
      note IH = "5.IH"
      have *: "A' \<in> set (tr\<^sub>p\<^sub>c S (List.insert (i,t',s) D))" using prems(3) by auto
      have "E \<noteq> []" using prems(1) by auto
      hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E" "prefix E A'"
        using *(1) prems(1,2) suffix_Cons[of _ _ E] by auto
      then obtain F where "prefix F S" "E \<in> set (tr\<^sub>p\<^sub>c F (List.insert (i,t',s) D))"
        using * IH by metis
      hence "prefix ((i,insert\<langle>t',s\<rangle>)#F) ((i,insert\<langle>t',s\<rangle>)#S)"
            "E \<in> set (tr\<^sub>p\<^sub>c ((i,insert\<langle>t',s\<rangle>)#F) D)"
        by auto
      thus ?case by metis
    next
      case (6 i t' s S D)
      note prems = "6.prems"
      note IH = "6.IH"

      define constr where "constr = (\<lambda>Di.
        (map (\<lambda>d. (i,\<langle>check: (pair (t',s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
        (map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t',s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t))
          (filter (\<lambda>d. d \<notin> set Di) (dbproj i D))))"

      obtain A'' Di where *:
          "A' = constr Di@A''" "A'' \<in> set (tr\<^sub>p\<^sub>c S (filter (\<lambda>d. d \<notin> set Di) D))"
          "Di \<in> set (subseqs (dbproj i D))"
        using prems(3) constr_def by auto
      have ***:  "(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<notin> set (constr Di)" using constr_def by auto
      have "E \<noteq> []" using prems(1) by auto
      then obtain E' where **: "E = constr Di@E'"
        using *(1) prems(1,2) ***
        by (metis (mono_tags, lifting) Un_iff list.set_intros(1) prefixI prefix_def
                                       prefix_same_cases set_append suffix_def)
      hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'" "prefix E' A''"
        using *(1) prems(1,2) suffix_append[of "[(m,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]" "constr Di" E'] ***
        by (metis (no_types, hide_lams) Nil_suffix append_Nil2 in_set_conv_decomp rev_exhaust
                                        snoc_suffix_snoc suffix_appendD,
            auto)
      then obtain F where "prefix F S" "E' \<in> set (tr\<^sub>p\<^sub>c F (filter (\<lambda>d. d \<notin> set Di) D))"
        using *(2,3) ** IH by metis
      hence "prefix ((i,delete\<langle>t',s\<rangle>)#F) ((i,delete\<langle>t',s\<rangle>)#S)"
            "E \<in> set (tr\<^sub>p\<^sub>c ((i,delete\<langle>t',s\<rangle>)#F) D)"
        using *(3) ** constr_def by auto
      thus ?case by metis
    next
      case (7 i ac t' s S D)
      note prems = "7.prems"
      note IH = "7.IH"

      define constr where "constr = (
        \<lambda>d::(('lbl strand_label \<times> ('fun,'var) term \<times> ('fun,'var) term)).
          (i,\<langle>ac: (pair (t',s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t))"

      obtain A'' d where *: "A' = constr d#A''" "A'' \<in> set (tr\<^sub>p\<^sub>c S D)" "d \<in> set (dbproj i D)"
        using prems(3) constr_def by auto
      have "E \<noteq> []" using prems(1) by auto
      then obtain E' where **: "E = constr d#E'" using *(1) prems(2) by (cases E) auto
      hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'" "prefix E' A''"
        using *(1) prems(1,2) suffix_Cons[of _ _ E'] using constr_def by auto
      then obtain F where "prefix F S" "E' \<in> set (tr\<^sub>p\<^sub>c F D)" using *(2) ** IH by metis
      hence "prefix ((i,InSet ac t' s)#F) ((i,InSet ac t' s)#S)"
            "E \<in> set (tr\<^sub>p\<^sub>c ((i,InSet ac t' s)#F) D)"
        using *(3) ** unfolding constr_def by auto
      thus ?case by metis
    next
      case (8 i X G G' S D)
      note prems = "8.prems"
      note IH = "8.IH"

      define constr where
        "constr = map (\<lambda>H. (i,\<forall>X\<langle>\<or>\<noteq>: (G@H)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G' (map snd (dbproj i D)))"

      obtain A'' where *: "A' = constr@A''" "A'' \<in> set (tr\<^sub>p\<^sub>c S D)"
        using prems(3) constr_def by auto
      have ***:  "(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t) \<notin> set constr" using constr_def by auto
      have "E \<noteq> []" using prems(1) by auto
      then obtain E' where **: "E = constr@E'"
        using *(1) prems(1,2) ***
        by (metis (mono_tags, lifting) Un_iff list.set_intros(1) prefixI prefix_def
                                       prefix_same_cases set_append suffix_def)
      hence "suffix [(m, receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] E'" "prefix E' A''"
        using *(1) prems(1,2) suffix_append[of "[(m,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]" constr E'] ***
        by (metis (no_types, hide_lams) Nil_suffix append_Nil2 in_set_conv_decomp rev_exhaust
                                        snoc_suffix_snoc suffix_appendD,
            auto)
      then obtain F where "prefix F S" "E' \<in> set (tr\<^sub>p\<^sub>c F D)" using *(2) ** IH by metis
      hence "prefix ((i,NegChecks X G G')#F) ((i,NegChecks X G G')#S)"
            "E \<in> set (tr\<^sub>p\<^sub>c ((i,NegChecks X G G')#F) D)"
        using ** constr_def by auto
      thus ?case by metis
    qed
  }
  moreover have "prefix [] A" "[] \<in> set (tr\<^sub>p\<^sub>c [] [])" by auto
  ultimately have 4: "\<exists>D. prefix D A \<and> C \<in> set (tr\<^sub>p\<^sub>c D [])" using C(3) assms(1) 2 by blast

  show ?thesis by (metis 1 3 4)
qed


subsection \<open>Theorem: Semantic Equivalence of Translation\<close>
context
begin

text \<open>
  An alternative version of the translation that does not perform database-state projections.
  It is used as an intermediate step in the proof of semantic equivalence.
\<close>
private fun tr'\<^sub>p\<^sub>c::
  "('fun,'var,'lbl) labeled_stateful_strand \<Rightarrow> ('fun,'var,'lbl) labeleddbstatelist
   \<Rightarrow> ('fun,'var,'lbl) labeled_strand list"
where
  "tr'\<^sub>p\<^sub>c [] D = [[]]"
| "tr'\<^sub>p\<^sub>c ((i,send\<langle>t\<rangle>)#A) D = map ((#) (i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)) (tr'\<^sub>p\<^sub>c A D)"
| "tr'\<^sub>p\<^sub>c ((i,receive\<langle>t\<rangle>)#A) D = map ((#) (i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)) (tr'\<^sub>p\<^sub>c A D)"
| "tr'\<^sub>p\<^sub>c ((i,\<langle>ac: t \<doteq> t'\<rangle>)#A) D = map ((#) (i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)) (tr'\<^sub>p\<^sub>c A D)"
| "tr'\<^sub>p\<^sub>c ((i,insert\<langle>t,s\<rangle>)#A) D = tr'\<^sub>p\<^sub>c A (List.insert (i,(t,s)) D)"
| "tr'\<^sub>p\<^sub>c ((i,delete\<langle>t,s\<rangle>)#A) D = (
    concat (map (\<lambda>Di. map (\<lambda>B. (map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di)@
                               (map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t))
                                    [d\<leftarrow>D. d \<notin> set Di])@B)
                          (tr'\<^sub>p\<^sub>c A [d\<leftarrow>D. d \<notin> set Di]))
                (subseqs D)))"
| "tr'\<^sub>p\<^sub>c ((i,\<langle>ac: t \<in> s\<rangle>)#A) D =
    concat (map (\<lambda>B. map (\<lambda>d. (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#B) D) (tr'\<^sub>p\<^sub>c A D))"
| "tr'\<^sub>p\<^sub>c ((i,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>)#A) D =
    map ((@) (map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd D)))) (tr'\<^sub>p\<^sub>c A D)"

subsubsection \<open>Part 1\<close>
private lemma tr'_par_iff_unlabel_tr:
  assumes "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D.
           \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D.
              p = q \<longrightarrow> i = j"
  shows "(\<exists>C \<in> set (tr'\<^sub>p\<^sub>c A D). B = unlabel C) \<longleftrightarrow> B \<in> set (tr (unlabel A) (unlabel D))"
    (is "?A \<longleftrightarrow> ?B")
proof
  { fix C have "C \<in> set (tr'\<^sub>p\<^sub>c A D) \<Longrightarrow> unlabel C \<in> set (tr (unlabel A) (unlabel D))" using assms
    proof (induction A D arbitrary: C rule: tr'\<^sub>p\<^sub>c.induct)
      case (5 i t s S D)
      hence "unlabel C \<in> set (tr (unlabel S) (unlabel (List.insert (i, t, s) D)))"
        by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      moreover have
          "insert (i,t,s) (set D) \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i,insert\<langle>t,s\<rangle>)#S) \<union> set D"
        by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      hence "\<forall>(j,p) \<in> insert (i,t,s) (set D). \<forall>(k,q) \<in> insert (i,t,s) (set D). p = q \<longrightarrow> j = k"
        using "5.prems"(2) by blast
      hence "unlabel (List.insert (i, t, s) D) = (List.insert (t, s) (unlabel D))"
        using map_snd_list_insert_distrib[of "(i,t,s)" D] unfolding unlabel_def by simp
      ultimately show ?case by auto
    next
      case (6 i t s S D)
      let ?f1 = "\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t"
      let ?g1 = "\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t"
      let ?f2 = "\<lambda>d. (i, ?f1 (snd d))"
      let ?g2 = "\<lambda>d. (i, ?g1 (snd d))"

      define constr1 where "constr1 = (\<lambda>Di. (map ?f1 Di)@(map ?g1 [d\<leftarrow>unlabel D. d \<notin> set Di]))"
      define constr2 where "constr2 = (\<lambda>Di. (map ?f2 Di)@(map ?g2 [d\<leftarrow>D. d \<notin> set Di]))"

      obtain C' Di where C':
          "Di \<in> set (subseqs D)"
          "C = constr2 Di@C'"
          "C' \<in> set (tr'\<^sub>p\<^sub>c S [d\<leftarrow>D. d \<notin> set Di])"
        using "6.prems"(1) unfolding constr2_def by moura

      have 0: "set [d\<leftarrow>D. d \<notin> set Di] \<subseteq> set D"
              "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S)"
        by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      hence 1:
          "\<forall>(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set [d\<leftarrow>D. d \<notin> set Di].
           \<forall>(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set [d\<leftarrow>D. d \<notin> set Di].
            p = q \<longrightarrow> j = k"
        using "6.prems"(2) by blast

      have "\<forall>(i,p) \<in> set D \<union> set Di. \<forall>(j,q) \<in> set D \<union> set Di. p = q \<longrightarrow> i = j"
        using "6.prems"(2) subseqs_set_subset(1)[OF C'(1)] by blast
      hence 2: "unlabel [d\<leftarrow>D. d \<notin> set Di] = [d\<leftarrow>unlabel D. d \<notin> set (unlabel Di)]"
        using unlabel_filter_eq[of D "set Di"] unfolding unlabel_def by simp

      have 3:
          "\<And>f g::('a \<times> 'a \<Rightarrow> 'c). \<And>A B::(('b \<times> 'a \<times> 'a) list).
              map snd ((map (\<lambda>d. (i, f (snd d))) A)@(map (\<lambda>d. (i, g (snd d))) B)) =
              map f (map snd A)@map g (map snd B)"
        by simp
      have "unlabel (constr2 Di) = constr1 (unlabel Di)"
        using 2 3[of ?f1 Di ?g1 "[d\<leftarrow>D. d \<notin> set Di]"]
        by (simp add: constr1_def constr2_def unlabel_def)
      hence 4: "unlabel C = constr1 (unlabel Di)@unlabel C'"
        using C'(2) unlabel_append by metis

      have "unlabel Di \<in> set (map unlabel (subseqs D))"
        using C'(1) unfolding unlabel_def by simp
      hence 5: "unlabel Di \<in> set (subseqs (unlabel D))"
        using map_subseqs[of snd D] unfolding unlabel_def by simp

      show ?case using "6.IH"[OF C'(1,3) 1] 2 4 5 unfolding constr1_def by auto
    next
      case (7 i ac t s S D)
      obtain C' d  where C':
          "C = (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#C'"
          "C' \<in> set (tr'\<^sub>p\<^sub>c S D)" "d \<in> set D"
        using "7.prems"(1) by moura

      have "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i,InSet ac t s)#S) \<union> set D"
        by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      hence "\<forall>(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D.
             \<forall>(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D.
              p = q \<longrightarrow> j = k"
        using "7.prems"(2) by blast
      hence "unlabel C' \<in> set (tr (unlabel S) (unlabel D))" using "7.IH"[OF C'(2)] by auto
      thus ?case using C' unfolding unlabel_def by force
    next
      case (8 i X F F' S D)
      obtain C' where C':
          "C = map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd D))@C'"
          "C' \<in> set (tr'\<^sub>p\<^sub>c S D)"
        using "8.prems"(1) by moura

      have "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i,NegChecks X F F')#S) \<union> set D"
        by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      hence "\<forall>(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D.
             \<forall>(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D.
              p = q \<longrightarrow> j = k"
        using "8.prems"(2) by blast
      hence "unlabel C' \<in> set (tr (unlabel S) (unlabel D))" using "8.IH"[OF C'(2)] by auto
      thus ?case using C' unfolding unlabel_def by auto
    qed (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
  } thus "?A \<Longrightarrow> ?B" by blast

  show "?B \<Longrightarrow> ?A" using assms
  proof (induction A arbitrary: B D)
    case (Cons a A)
    obtain ia sa where a: "a = (ia,sa)" by moura

    have "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A)" using a by (cases sa) (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
    hence 1: "\<forall>(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D.
              \<forall>(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D.
                p = q \<longrightarrow> j = k"
      using Cons.prems(2) by blast

    show ?case
    proof (cases sa)
      case (Send t)
      then obtain B' where B':
          "B = send\<langle>t\<rangle>\<^sub>s\<^sub>t#B'"
          "B' \<in> set (tr (unlabel A) (unlabel D))"
        using Cons.prems(1) a by auto
      thus ?thesis using Cons.IH[OF B'(2) 1] a B'(1) Send by auto
    next
      case (Receive t)
      then obtain B' where B':
          "B = receive\<langle>t\<rangle>\<^sub>s\<^sub>t#B'"
          "B' \<in> set (tr (unlabel A) (unlabel D))"
        using Cons.prems(1) a by auto
      thus ?thesis using Cons.IH[OF B'(2) 1] a B'(1) Receive by auto
    next
      case (Equality ac t t')
      then obtain B' where B':
          "B = \<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#B'"
          "B' \<in> set (tr (unlabel A) (unlabel D))"
        using Cons.prems(1) a by auto
      thus ?thesis using Cons.IH[OF B'(2) 1] a B'(1) Equality by auto
    next
      case (Insert t s)
      hence B: "B \<in> set (tr (unlabel A) (List.insert (t,s) (unlabel D)))"
        using Cons.prems(1) a by auto

      let ?P = "\<lambda>i. List.insert (t,s) (unlabel D) = unlabel (List.insert (i,t,s) D)"

      { obtain j where j: "?P j" "j = ia \<or> (j,t,s) \<in> set D"
          using labeled_list_insert_eq_ex_cases[of "(t,s)" D ia] by moura
        hence "j = ia" using Cons.prems(2) a Insert by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "?P ia" using j(1) by metis
      } hence j: "?P ia" by metis

      have 2: "\<forall>(k1, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set (List.insert (ia,t,s) D).
               \<forall>(k2, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set (List.insert (ia,t,s) D).
                 p = q \<longrightarrow> k1 = k2"
        using Cons.prems(2) a Insert by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

      show ?thesis using Cons.IH[OF _ 2] j(1) B Insert a by auto
    next
      case (Delete t s)
      define c where "c \<equiv> (\<lambda>(i::'lbl strand_label) Di.
        map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di@
        map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>D. d \<notin> set Di])"

      define d where "d \<equiv> (\<lambda>Di.
        map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t) Di@
        map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair d)]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>unlabel D. d \<notin> set Di])"

      obtain B' Di where B':
          "B = d Di@B'" "Di \<in> set (subseqs (unlabel D))"
          "B' \<in> set (tr (unlabel A) [d\<leftarrow>unlabel D. d \<notin> set Di])"
        using Cons.prems(1) a Delete unfolding d_def by auto

      obtain Di' where Di': "Di' \<in> set (subseqs D)" "unlabel Di' = Di"
        using unlabel_subseqsD[OF B'(2)] by moura

      have 2: "\<forall>(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set [d\<leftarrow>D. d \<notin> set Di'].
               \<forall>(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set [d\<leftarrow>D. d \<notin> set Di'].
                 p = q \<longrightarrow> j = k"
        using 1 subseqs_subset[OF Di'(1)]
              filter_is_subset[of "\<lambda>d. d \<notin> set Di'"]
        by blast

      have "set Di' \<subseteq> set D" by (rule subseqs_subset[OF Di'(1)])
      hence "\<forall>(j, p)\<in>set D \<union> set Di'. \<forall>(k, q)\<in>set D \<union> set Di'. p = q \<longrightarrow> j = k"
        using Cons.prems(2) by blast
      hence 3: "[d\<leftarrow>unlabel D. d \<notin> set Di] = unlabel [d\<leftarrow>D. d \<notin> set Di']"
        using Di'(2) unlabel_filter_eq[of D "set Di'"] unfolding unlabel_def by auto

      obtain C where C: "C \<in> set (tr'\<^sub>p\<^sub>c A [d\<leftarrow>D. d \<notin> set Di'])" "B' = unlabel C"
        using 3 Cons.IH[OF _ 2] B'(3) by auto
      hence 4: "c ia Di'@C \<in> set (tr'\<^sub>p\<^sub>c (a#A) D)" using Di'(1) a Delete unfolding c_def by auto

      have "unlabel (c ia Di') = d Di" using Di' 3 unfolding c_def d_def unlabel_def by auto
      hence 5: "B = unlabel (c ia Di'@C)" using B'(1) C(2) unlabel_append[of "c ia Di'" C] by simp

      show ?thesis using 4 5 by blast
    next
      case (InSet ac t s)
      then obtain B' d where B':
          "B = \<langle>ac: (pair (t,s)) \<doteq> (pair d)\<rangle>\<^sub>s\<^sub>t#B'"
          "B' \<in> set (tr (unlabel A) (unlabel D))"
          "d \<in> set (unlabel D)"
        using Cons.prems(1) a by auto
      thus ?thesis using Cons.IH[OF _ 1] a InSet unfolding unlabel_def by auto
    next
      case (NegChecks X F F')
      then obtain B' where B':
          "B = map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (unlabel D))@B'"
          "B' \<in> set (tr (unlabel A) (unlabel D))"
        using Cons.prems(1) a by auto
      thus ?thesis using Cons.IH[OF _ 1] a NegChecks unfolding unlabel_def by auto
    qed
  qed simp
qed

subsubsection \<open>Part 2\<close>
private lemma tr_par_iff_tr'_par:
  assumes "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D.
            (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j"
    (is "?R3 A D")
  and "\<forall>(l,t,s) \<in> set D. (fv t \<union> fv s) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}" (is "?R4 A D")
  and "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}" (is "?R5 A D")
  shows "(\<exists>B \<in> set (tr\<^sub>p\<^sub>c A D). \<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>) \<longleftrightarrow> (\<exists>C \<in> set (tr'\<^sub>p\<^sub>c A D). \<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I>)"
    (is "?P \<longleftrightarrow> ?Q")
proof
  { fix B assume "B \<in> set (tr\<^sub>p\<^sub>c A D)" "\<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>"
    hence ?Q using assms
    proof (induction A D arbitrary: B M rule: tr\<^sub>p\<^sub>c.induct)
      case (1 D) thus ?case by simp
    next
      case (2 i t S D)
      note prems = "2.prems"
      note IH = "2.IH"

      obtain B' where B': "B = (i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#B'" "B' \<in> set (tr\<^sub>p\<^sub>c S D)"
        using prems(1) by moura

      have 1: "\<lbrakk>M; unlabel B'\<rbrakk>\<^sub>d \<I>" using prems(2) B'(1) by simp
      have 4: "?R3 S D" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      have 7: "M \<turnstile> t \<cdot> \<I>" using prems(2) B'(1) by simp

      obtain C where C: "C \<in> set (tr'\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I>"
        using IH[OF B'(2) 1 4 5 6] by moura
      hence "((i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#C) \<in> set (tr'\<^sub>p\<^sub>c ((i,Send t)#S) D)" "\<lbrakk>M; unlabel ((i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#C)\<rbrakk>\<^sub>d \<I>"
        using 7 by auto
      thus ?case by metis
    next
      case (3 i t S D)
      note prems = "3.prems"
      note IH = "3.IH"

      obtain B' where B': "B = (i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#B'" "B' \<in> set (tr\<^sub>p\<^sub>c S D)" using prems(1) by moura

      have 1: "\<lbrakk>insert (t \<cdot> \<I>) M; unlabel B'\<rbrakk>\<^sub>d \<I> " using prems(2) B'(1) by simp
      have 4: "?R3 S D" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      obtain C where C: "C \<in> set (tr'\<^sub>p\<^sub>c S D)" "\<lbrakk>insert (t \<cdot> \<I>) M; unlabel C\<rbrakk>\<^sub>d \<I>"
        using IH[OF B'(2) 1 4 5 6] by moura
      hence "((i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#C) \<in> set (tr'\<^sub>p\<^sub>c ((i,receive\<langle>t\<rangle>)#S) D)"
            "\<lbrakk>insert (t \<cdot> \<I>) M; unlabel ((i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#C)\<rbrakk>\<^sub>d \<I>"
        by auto
      thus ?case by auto
    next
      case (4 i ac t t' S D)
      note prems = "4.prems"
      note IH = "4.IH"

      obtain B' where B': "B = (i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#B'" "B' \<in> set (tr\<^sub>p\<^sub>c S D)"
        using prems(1) by moura

      have 1: "\<lbrakk>M; unlabel B'\<rbrakk>\<^sub>d \<I> " using prems(2) B'(1) by simp
      have 4: "?R3 S D" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      have 7: "t \<cdot> \<I> = t' \<cdot> \<I>" using prems(2) B'(1) by simp

      obtain C where C: "C \<in> set (tr'\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I>"
        using IH[OF B'(2) 1 4 5 6] by moura
      hence "((i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#C) \<in> set (tr'\<^sub>p\<^sub>c ((i,Equality ac t t')#S) D)"
            "\<lbrakk>M; unlabel ((i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#C)\<rbrakk>\<^sub>d \<I>"
        using 7 by auto
      thus ?case by metis
    next
      case (5 i t s S D)
      note prems = "5.prems"
      note IH = "5.IH"

      have B: "B \<in> set (tr\<^sub>p\<^sub>c S (List.insert (i,t,s) D))" using prems(1) by simp

      have 1: "\<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I> " using prems(2) B(1) by simp
      have 4: "?R3 S (List.insert (i,t,s) D)" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S (List.insert (i,t,s) D)" using prems(4,5) by force
      have 6: "?R5 S D" using prems(5) by force

      show ?case using IH[OF B(1) 1 4 5 6] by simp
    next
      case (6 i t s S D)
      note prems = "6.prems"
      note IH = "6.IH"

      let ?cl1 = "\<lambda>Di. map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di"
      let ?cu1 = "\<lambda>Di. map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t) Di"
      let ?cl2 = "\<lambda>Di. map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>dbproj i D. d\<notin>set Di]"
      let ?cu2 = "\<lambda>Di. map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>dbproj i D. d\<notin>set Di]"

      let ?dl1 = "\<lambda>Di. map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di"
      let ?du1 = "\<lambda>Di. map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t) Di"
      let ?dl2 = "\<lambda>Di. map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>D. d\<notin>set Di]"
      let ?du2 = "\<lambda>Di. map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d\<notin>set Di]"

      define c where c: "c = (\<lambda>Di. ?cl1 Di@?cl2 Di)"
      define d where d: "d = (\<lambda>Di. ?dl1 Di@?dl2 Di)"

      obtain B' Di where B':
          "Di \<in> set (subseqs (dbproj i D))" "B = c Di@B'" "B' \<in> set (tr\<^sub>p\<^sub>c S [d\<leftarrow>D. d \<notin> set Di])"
        using prems(1) c by moura

      have 0: "ik\<^sub>s\<^sub>t (unlabel (c Di)) = {}" "ik\<^sub>s\<^sub>t (unlabel (d Di)) = {}"
              "unlabel (?cl1 Di) = ?cu1 Di" "unlabel (?cl2 Di) = ?cu2 Di"
              "unlabel (?dl1 Di) = ?du1 Di" "unlabel (?dl2 Di) = ?du2 Di"
        unfolding c d unlabel_def by force+

      have 1: "\<lbrakk>M; unlabel B'\<rbrakk>\<^sub>d \<I> " using prems(2) B'(2) 0(1) unfolding unlabel_def by auto

      { fix j p k q
        assume "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set [d\<leftarrow>D. d \<notin> set Di]"
               "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set [d\<leftarrow>D. d \<notin> set Di]"
        hence "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
              "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
          using dbproj_subseq_subset[OF B'(1)] by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence 4: "?R3 S [d\<leftarrow>D. d \<notin> set Di]" by blast

      have 5: "?R4 S (filter (\<lambda>d. d \<notin> set Di) D)" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      obtain C where C: "C \<in> set (tr'\<^sub>p\<^sub>c S [d\<leftarrow>D . d \<notin> set Di])" "\<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I>"
        using IH[OF B'(1,3) 1 4 5 6] by moura

      have 7: "\<lbrakk>M; unlabel (c Di)\<rbrakk>\<^sub>d \<I>" "\<lbrakk>M; unlabel B'\<rbrakk>\<^sub>d \<I>"
        using prems(2) B'(2) 0(1) strand_sem_split(3,4)[of M "unlabel (c Di)" "unlabel B'"]
        unfolding c unlabel_def by auto

      have "\<lbrakk>M; unlabel (?cl2 Di)\<rbrakk>\<^sub>d \<I>" using 7(1) 0(1) unfolding c unlabel_def by auto
      hence "\<lbrakk>M; ?cu2 Di\<rbrakk>\<^sub>d \<I>" by (metis 0(4))
      moreover {
        fix j p k q
        assume "(j, p) \<in> {(i, t, s)} \<union> set D \<union> set Di"
               "(k, q) \<in> {(i, t, s)} \<union> set D \<union> set Di"
        hence "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
              "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
          using dbproj_subseq_subset[OF B'(1)] by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence "\<forall>(j, p) \<in> {(i, t, s)} \<union> set D \<union> set Di.
               \<forall>(k, q) \<in> {(i, t, s)} \<union> set D \<union> set Di.
                (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k"
        by blast
      ultimately have "\<lbrakk>M; ?du2 Di\<rbrakk>\<^sub>d \<I>" using labeled_sat_ineq_lift by simp
      hence "\<lbrakk>M; unlabel (?dl2 Di)\<rbrakk>\<^sub>d \<I>" by (metis 0(6))
      moreover have "\<lbrakk>M; unlabel (?cl1 Di)\<rbrakk>\<^sub>d \<I>" using 7(1) unfolding c unlabel_def by auto
      hence "\<lbrakk>M; unlabel (?dl1 Di)\<rbrakk>\<^sub>d \<I>" by (metis 0(3,5))
      ultimately have "\<lbrakk>M; unlabel (d Di)\<rbrakk>\<^sub>d \<I>" using 0(2) unfolding c d unlabel_def by force
      hence 8: "\<lbrakk>M; unlabel (d Di@C)\<rbrakk>\<^sub>d \<I>" using 0(2) C(2) unfolding unlabel_def by auto

      have 9: "d Di@C \<in> set (tr'\<^sub>p\<^sub>c ((i,delete\<langle>t,s\<rangle>)#S) D)"
        using C(1) dbproj_subseq_in_subseqs[OF B'(1)]
        unfolding d unlabel_def by auto

      show ?case by (metis 8 9)
    next
      case (7 i ac t s S D)
      note prems = "7.prems"
      note IH = "7.IH"

      obtain B' d where B':
          "B = (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#B'"
          "B' \<in> set (tr\<^sub>p\<^sub>c S D)" "d \<in> set (dbproj i D)"
        using prems(1) by moura

      have 1: "\<lbrakk>M; unlabel B'\<rbrakk>\<^sub>d \<I> " using prems(2) B'(1) by simp

      { fix j p k q
        assume "(j,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D"
               "(k,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D"
        hence "(j,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, InSet ac t s)#S) \<union> set D"
              "(k,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, InSet ac t s)#S) \<union> set D"
          by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence 4: "?R3 S D" by blast

      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force
      have 7: "pair (t,s) \<cdot> \<I> = pair (snd d) \<cdot> \<I>" using prems(2) B'(1) by simp

      obtain C where C: "C \<in> set (tr'\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I>"
        using IH[OF B'(2) 1 4 5 6] by moura
      hence "((i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#C) \<in> set (tr'\<^sub>p\<^sub>c ((i,InSet ac t s)#S) D)"
            "\<lbrakk>M; unlabel ((i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#C)\<rbrakk>\<^sub>d \<I>"
        using 7 B'(3) by auto
      thus ?case by metis
    next
      case (8 i X F F' S D)
      note prems = "8.prems"
      note IH = "8.IH"

      let ?cl = "map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"
      let ?cu = "map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"

      let ?dl = "map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd D))"
      let ?du = "map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd D))"

      define c where c: "c = ?cl"
      define d where d: "d = ?dl"

      obtain B' where B': "B = c@B'" "B' \<in> set (tr\<^sub>p\<^sub>c S D)" using prems(1) c by moura

      have 0: "ik\<^sub>s\<^sub>t (unlabel c) = {}" "ik\<^sub>s\<^sub>t (unlabel d) = {}"
              "unlabel ?cl = ?cu" "unlabel ?dl = ?du"
        unfolding c d unlabel_def by force+

      have "ik\<^sub>s\<^sub>t (unlabel c) = {}" unfolding c unlabel_def by force
      hence 1: "\<lbrakk>M; unlabel B'\<rbrakk>\<^sub>d \<I> " using prems(2) B'(1) unfolding unlabel_def by auto

      have "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, NegChecks X F F')#S)" by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      hence 4: "?R3 S D" using prems(3) by blast

      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      obtain C where C: "C \<in> set (tr'\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I>"
        using IH[OF B'(2) 1 4 5 6] by moura

      have 7: "\<lbrakk>M; unlabel c\<rbrakk>\<^sub>d \<I>" "\<lbrakk>M; unlabel B'\<rbrakk>\<^sub>d \<I>"
        using prems(2) B'(1) 0(1) strand_sem_split(3,4)[of M "unlabel c" "unlabel B'"]
        unfolding c unlabel_def by auto

      have 8: "d@C \<in> set (tr'\<^sub>p\<^sub>c ((i,NegChecks X F F')#S) D)"
        using C(1) unfolding d unlabel_def by auto

      have "\<lbrakk>M; unlabel ?cl\<rbrakk>\<^sub>d \<I>" using 7(1) unfolding c unlabel_def by auto
      hence "\<lbrakk>M; ?cu\<rbrakk>\<^sub>d \<I>" by (metis 0(3))
      moreover {
        fix j p k q
        assume "(j, p) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D"
               "(k, q) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D"
        hence "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, NegChecks X F F')#S) \<union> set D"
              "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, NegChecks X F F')#S) \<union> set D"
          by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence "\<forall>(j, p) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D.
               \<forall>(k, q) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D.
                (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k"
        by blast
      moreover have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (map snd D) \<inter> set X = {}"
        using prems(4) by fastforce
      ultimately have "\<lbrakk>M; ?du\<rbrakk>\<^sub>d \<I>" using labeled_sat_ineq_dbproj_sem_equiv[of i] by simp
      hence "\<lbrakk>M; unlabel ?dl\<rbrakk>\<^sub>d \<I>" by (metis 0(4))
      hence "\<lbrakk>M; unlabel d\<rbrakk>\<^sub>d \<I>" using 0(2) unfolding c d unlabel_def by force
      hence 9: "\<lbrakk>M; unlabel (d@C)\<rbrakk>\<^sub>d \<I>" using 0(2) C(2) unfolding unlabel_def by auto

      show ?case by (metis 8 9)
    qed
  } thus "?P \<Longrightarrow> ?Q" by metis

  { fix C assume "C \<in> set (tr'\<^sub>p\<^sub>c A D)" "\<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I>"
    hence ?P using assms
    proof (induction A D arbitrary: C M rule: tr'\<^sub>p\<^sub>c.induct)
      case (1 D) thus ?case by simp
    next
      case (2 i t S D)
      note prems = "2.prems"
      note IH = "2.IH"

      obtain C' where C': "C = (i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#C'" "C' \<in> set (tr'\<^sub>p\<^sub>c S D)"
        using prems(1) by moura

      have 1: "\<lbrakk>M; unlabel C'\<rbrakk>\<^sub>d \<I> " using prems(2) C'(1) by simp
      have 4: "?R3 S D" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      have 7: "M \<turnstile> t \<cdot> \<I>" using prems(2) C'(1) by simp

      obtain B where B: "B \<in> set (tr\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>"
        using IH[OF C'(2) 1 4 5 6] by moura
      hence "((i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#B) \<in> set (tr\<^sub>p\<^sub>c ((i,Send t)#S) D)"
            "\<lbrakk>M; unlabel ((i,send\<langle>t\<rangle>\<^sub>s\<^sub>t)#B)\<rbrakk>\<^sub>d \<I>"
        using 7 by auto
      thus ?case by metis
    next
      case (3 i t S D)
      note prems = "3.prems"
      note IH = "3.IH"

      obtain C' where C': "C = (i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#C'" "C' \<in> set (tr'\<^sub>p\<^sub>c S D)"
        using prems(1) by moura

      have 1: "\<lbrakk>insert (t \<cdot> \<I>) M; unlabel C'\<rbrakk>\<^sub>d \<I> " using prems(2) C'(1) by simp
      have 4: "?R3 S D" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      obtain B where B: "B \<in> set (tr\<^sub>p\<^sub>c S D)" "\<lbrakk>insert (t \<cdot> \<I>) M; unlabel B\<rbrakk>\<^sub>d \<I>"
        using IH[OF C'(2) 1 4 5 6] by moura
      hence "((i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#B) \<in> set (tr\<^sub>p\<^sub>c ((i,receive\<langle>t\<rangle>)#S) D)"
            "\<lbrakk>insert (t \<cdot> \<I>) M; unlabel ((i,receive\<langle>t\<rangle>\<^sub>s\<^sub>t)#B)\<rbrakk>\<^sub>d \<I>"
        by auto
      thus ?case by auto
    next
      case (4 i ac t t' S D)
      note prems = "4.prems"
      note IH = "4.IH"

      obtain C' where C': "C = (i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#C'" "C' \<in> set (tr'\<^sub>p\<^sub>c S D)"
        using prems(1) by moura

      have 1: "\<lbrakk>M; unlabel C'\<rbrakk>\<^sub>d \<I> " using prems(2) C'(1) by simp
      have 4: "?R3 S D" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      have 7: "t \<cdot> \<I> = t' \<cdot> \<I>" using prems(2) C'(1) by simp

      obtain B where B: "B \<in> set (tr\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>"
        using IH[OF C'(2) 1 4 5 6] by moura
      hence "((i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#B) \<in> set (tr\<^sub>p\<^sub>c ((i,Equality ac t t')#S) D)"
            "\<lbrakk>M; unlabel ((i,\<langle>ac: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)#B)\<rbrakk>\<^sub>d \<I>"
        using 7 by auto
      thus ?case by metis
    next
      case (5 i t s S D)
      note prems = "5.prems"
      note IH = "5.IH"

      have C: "C \<in> set (tr'\<^sub>p\<^sub>c S (List.insert (i,t,s) D))" using prems(1) by simp

      have 1: "\<lbrakk>M; unlabel C\<rbrakk>\<^sub>d \<I> " using prems(2) C(1) by simp
      have 4: "?R3 S (List.insert (i,t,s) D)" using prems(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      have 5: "?R4 S (List.insert (i,t,s) D)" using prems(4,5) by force
      have 6: "?R5 S (List.insert (i,t,s) D)" using prems(5) by force

      show ?case using IH[OF C(1) 1 4 5 6] by simp
    next
      case (6 i t s S D)
      note prems = "6.prems"
      note IH = "6.IH"

      let ?dl1 = "\<lambda>Di. map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di"
      let ?du1 = "\<lambda>Di. map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t) Di"
      let ?dl2 = "\<lambda>Di. map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>dbproj i D. d\<notin>set Di]"
      let ?du2 = "\<lambda>Di. map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>dbproj i D. d\<notin>set Di]"

      let ?cl1 = "\<lambda>Di. map (\<lambda>d. (i,\<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)) Di"
      let ?cu1 = "\<lambda>Di. map (\<lambda>d. \<langle>check: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t) Di"
      let ?cl2 = "\<lambda>Di. map (\<lambda>d. (i,\<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t)) [d\<leftarrow>D. d\<notin>set Di]"
      let ?cu2 = "\<lambda>Di. map (\<lambda>d. \<forall>[]\<langle>\<or>\<noteq>: [(pair (t,s), pair (snd d))]\<rangle>\<^sub>s\<^sub>t) [d\<leftarrow>D. d\<notin>set Di]"

      define c where c: "c = (\<lambda>Di. ?cl1 Di@?cl2 Di)"
      define d where d: "d = (\<lambda>Di. ?dl1 Di@?dl2 Di)"

      obtain C' Di where C':
          "Di \<in> set (subseqs D)" "C = c Di@C'" "C' \<in> set (tr'\<^sub>p\<^sub>c S [d\<leftarrow>D. d \<notin> set Di])"
        using prems(1) c by moura

      have 0: "ik\<^sub>s\<^sub>t (unlabel (c Di)) = {}" "ik\<^sub>s\<^sub>t (unlabel (d Di)) = {}"
              "unlabel (?cl1 Di) = ?cu1 Di" "unlabel (?cl2 Di) = ?cu2 Di"
              "unlabel (?dl1 Di) = ?du1 Di" "unlabel (?dl2 Di) = ?du2 Di"
        unfolding c d unlabel_def by force+

      have 1: "\<lbrakk>M; unlabel C'\<rbrakk>\<^sub>d \<I> " using prems(2) C'(2) 0(1) unfolding unlabel_def by auto

      { fix j p k q
        assume "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set [d\<leftarrow>D. d \<notin> set Di]"
               "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set [d\<leftarrow>D. d \<notin> set Di]"
        hence "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
              "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
          by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence 4: "?R3 S [d\<leftarrow>D. d \<notin> set Di]" by blast

      have 5: "?R4 S (filter (\<lambda>d. d \<notin> set Di) D)" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      obtain B where B: "B \<in> set (tr\<^sub>p\<^sub>c S [d\<leftarrow>D. d \<notin> set Di])" "\<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>"
        using IH[OF C'(1,3) 1 4 5 6] by moura

      have 7: "\<lbrakk>M; unlabel (c Di)\<rbrakk>\<^sub>d \<I>" "\<lbrakk>M; unlabel C'\<rbrakk>\<^sub>d \<I>"
        using prems(2) C'(2) 0(1) strand_sem_split(3,4)[of M "unlabel (c Di)" "unlabel C'"]
        unfolding c unlabel_def by auto

      { fix j p k q
        assume "(j, p) \<in> {(i, t, s)} \<union> set D"
               "(k, q) \<in> {(i, t, s)} \<union> set D"
        hence "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
              "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, delete\<langle>t,s\<rangle>)#S) \<union> set D"
          by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence "\<forall>(j, p) \<in> {(i, t, s)} \<union> set D.
               \<forall>(k, q) \<in> {(i, t, s)} \<union> set D.
                (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k"
        by blast
      moreover have "\<lbrakk>M; unlabel (?cl1 Di)\<rbrakk>\<^sub>d \<I>" using 7(1) unfolding c unlabel_append by auto
      hence "\<lbrakk>M; ?cu1 Di\<rbrakk>\<^sub>d \<I>" by (metis 0(3))
      ultimately have *: "Di \<in> set (subseqs (dbproj i D))"
        using labeled_sat_eqs_subseqs[OF C'(1)] by simp
      hence 8: "d Di@B \<in> set (tr\<^sub>p\<^sub>c ((i,delete\<langle>t,s\<rangle>)#S) D)"
        using B(1) unfolding d unlabel_def by auto

      have "\<lbrakk>M; unlabel (?cl2 Di)\<rbrakk>\<^sub>d \<I>" using 7(1) 0(1) unfolding c unlabel_def by auto
      hence "\<lbrakk>M; ?cu2 Di\<rbrakk>\<^sub>d \<I>" by (metis 0(4))
      hence "\<lbrakk>M; ?du2 Di\<rbrakk>\<^sub>d \<I>" by (metis labeled_sat_ineq_dbproj)
      hence "\<lbrakk>M; unlabel (?dl2 Di)\<rbrakk>\<^sub>d \<I>" by (metis 0(6))
      moreover have "\<lbrakk>M; unlabel (?cl1 Di)\<rbrakk>\<^sub>d \<I>" using 7(1) unfolding c unlabel_def by auto
      hence "\<lbrakk>M; unlabel (?dl1 Di)\<rbrakk>\<^sub>d \<I>" by (metis 0(3,5))
      ultimately have "\<lbrakk>M; unlabel (d Di)\<rbrakk>\<^sub>d \<I>" using 0(2) unfolding c d unlabel_def by force
      hence 9: "\<lbrakk>M; unlabel (d Di@B)\<rbrakk>\<^sub>d \<I>" using 0(2) B(2) unfolding unlabel_def by auto

      show ?case by (metis 8 9)
    next
      case (7 i ac t s S D)
      note prems = "7.prems"
      note IH = "7.IH"

      obtain C' d where C':
          "C = (i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#C'"
          "C' \<in> set (tr'\<^sub>p\<^sub>c S D)" "d \<in> set D"
        using prems(1) by moura

      have 1: "\<lbrakk>M; unlabel C'\<rbrakk>\<^sub>d \<I> " using prems(2) C'(1) by simp

      { fix j p k q
        assume "(j,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D"
               "(k,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<union> set D"
        hence "(j,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, InSet ac t s)#S) \<union> set D"
              "(k,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, InSet ac t s)#S) \<union> set D"
          by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence 4: "?R3 S D" by blast

      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      obtain B where B: "B \<in> set (tr\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>"
        using IH[OF C'(2) 1 4 5 6] by moura

      have 7: "pair (t,s) \<cdot> \<I> = pair (snd d) \<cdot> \<I>" using prems(2) C'(1) by simp

      have "(i,t,s) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, InSet ac t s)#S) \<union> set D"
           "(fst d, snd d) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, InSet ac t s)#S) \<union> set D"
        using C'(3) by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      hence "\<exists>\<delta>. Unifier \<delta> (pair (t,s)) (pair (snd d)) \<Longrightarrow> i = fst d"
        using prems(3) by blast
      hence "fst d = i" using 7 by auto
      hence 8: "d \<in> set (dbproj i D)" using C'(3) by auto

      have 9: "((i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#B) \<in> set (tr\<^sub>p\<^sub>c ((i,InSet ac t s)#S) D)"
        using B 8 by auto
      have 10: "\<lbrakk>M; unlabel ((i,\<langle>ac: (pair (t,s)) \<doteq> (pair (snd d))\<rangle>\<^sub>s\<^sub>t)#B)\<rbrakk>\<^sub>d \<I>"
        using B 7 8 by auto

      show ?case by (metis 9 10)
    next
      case (8 i X F F' S D)
      note prems = "8.prems"
      note IH = "8.IH"

      let ?dl = "map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"
      let ?du = "map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd (dbproj i D)))"

      let ?cl = "map (\<lambda>G. (i,\<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t)) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd D))"
      let ?cu = "map (\<lambda>G. \<forall>X\<langle>\<or>\<noteq>: (F@G)\<rangle>\<^sub>s\<^sub>t) (tr\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F' (map snd D))"

      define c where c: "c = ?cl"
      define d where d: "d = ?dl"

      obtain C' where C': "C = c@C'" "C' \<in> set (tr'\<^sub>p\<^sub>c S D)" using prems(1) c by moura

      have 0: "ik\<^sub>s\<^sub>t (unlabel c) = {}" "ik\<^sub>s\<^sub>t (unlabel d) = {}"
              "unlabel ?cl = ?cu" "unlabel ?dl = ?du"
        unfolding c d unlabel_def by force+

      have "ik\<^sub>s\<^sub>t (unlabel c) = {}" unfolding c unlabel_def by force
      hence 1: "\<lbrakk>M; unlabel C'\<rbrakk>\<^sub>d \<I> " using prems(2) C'(1) unfolding unlabel_def by auto

      have "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, NegChecks X F F')#S)" by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
      hence 4: "?R3 S D" using prems(3) by blast

      have 5: "?R4 S D" using prems(4) by force
      have 6: "?R5 S D" using prems(5) by force

      obtain B where B: "B \<in> set (tr\<^sub>p\<^sub>c S D)" "\<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>"
        using IH[OF C'(2) 1 4 5 6] by moura

      have 7: "\<lbrakk>M; unlabel c\<rbrakk>\<^sub>d \<I>" "\<lbrakk>M; unlabel C'\<rbrakk>\<^sub>d \<I>"
        using prems(2) C'(1) 0(1) strand_sem_split(3,4)[of M "unlabel c" "unlabel C'"]
        unfolding c unlabel_def by auto

      have 8: "d@B \<in> set (tr\<^sub>p\<^sub>c ((i,NegChecks X F F')#S) D)"
        using B(1) unfolding d unlabel_def by auto

      have "\<lbrakk>M; unlabel ?cl\<rbrakk>\<^sub>d \<I>" using 7(1) unfolding c unlabel_def by auto
      hence "\<lbrakk>M; ?cu\<rbrakk>\<^sub>d \<I>" by (metis 0(3))
      moreover {
        fix j p k q
        assume "(j, p) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D"
               "(k, q) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D"
        hence "(j, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, NegChecks X F F')#S) \<union> set D"
              "(k, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((i, NegChecks X F F')#S) \<union> set D"
          by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
        hence "(\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<Longrightarrow> j = k" using prems(3) by blast
      } hence "\<forall>(j, p) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D.
               \<forall>(k, q) \<in> ((\<lambda>(t,s). (i,t,s)) ` set F') \<union> set D.
                (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> j = k"
        by blast
      moreover have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (map snd D) \<inter> set X = {}"
        using prems(4) by fastforce
      ultimately have "\<lbrakk>M; ?du\<rbrakk>\<^sub>d \<I>" using labeled_sat_ineq_dbproj_sem_equiv[of i] by simp
      hence "\<lbrakk>M; unlabel ?dl\<rbrakk>\<^sub>d \<I>" by (metis 0(4))
      hence "\<lbrakk>M; unlabel d\<rbrakk>\<^sub>d \<I>" using 0(2) unfolding c d unlabel_def by force
      hence 9: "\<lbrakk>M; unlabel (d@B)\<rbrakk>\<^sub>d \<I>" using 0(2) B(2) unfolding unlabel_def by auto

      show ?case by (metis 8 9)
    qed
  } thus "?Q \<Longrightarrow> ?P" by metis
qed


subsubsection \<open>Part 3\<close>
private lemma tr'_par_sem_equiv:
  assumes "\<forall>(l,t,s) \<in> set D. (fv t \<union> fv s) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
  and "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}" "ground M"
  and "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D.
        (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j" (is "?R A D")
  and \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<lbrakk>M; set (unlabel D) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; unlabel A\<rbrakk>\<^sub>s \<I> \<longleftrightarrow> (\<exists>B \<in> set (tr'\<^sub>p\<^sub>c A D). \<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>)"
        (is "?P \<longleftrightarrow> ?Q")
proof -
  have 1: "\<forall>(t,s) \<in> set (unlabel D). (fv t \<union> fv s) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
    using assms(1) unfolding unlabel_def by force

  have 2: "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D. p = q \<longrightarrow> i = j"
    using assms(4) subst_apply_term_empty by blast

  show ?thesis by (metis tr_sem_equiv'[OF 1 assms(2,3) \<I>] tr'_par_iff_unlabel_tr[OF 2])
qed


subsubsection \<open>Part 4\<close>
lemma tr_par_sem_equiv:
  assumes "\<forall>(l,t,s) \<in> set D. (fv t \<union> fv s) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}"
  and "fv\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A) = {}" "ground M"
  and "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> set D.
        (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j"
  and \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<lbrakk>M; set (unlabel D) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>; unlabel A\<rbrakk>\<^sub>s \<I> \<longleftrightarrow> (\<exists>B \<in> set (tr\<^sub>p\<^sub>c A D). \<lbrakk>M; unlabel B\<rbrakk>\<^sub>d \<I>)"
  (is "?P \<longleftrightarrow> ?Q")
using tr_par_iff_tr'_par[OF assms(4,1,2), of M \<I>] tr'_par_sem_equiv[OF assms] by metis

end


subsection \<open>Theorem: The Stateful Compositionality Result, on the Constraint Level\<close>
theorem par_comp_constr_stateful:
  assumes \<A>: "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> Sec" "typing_cond\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
  and \<I>: "\<I> \<Turnstile>\<^sub>s unlabel \<A>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<exists>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and> (\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s unlabel \<A>) \<and>
              ((\<forall>n. \<I>\<^sub>\<tau> \<Turnstile>\<^sub>s proj_unl n \<A>) \<or> (\<exists>\<A>'. prefix \<A>' \<A> \<and> (\<A>' leaks Sec under \<I>\<^sub>\<tau>)))"
proof -
  let ?P = "\<lambda>n A D.
       \<forall>(i, p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A) \<union> set D.
       \<forall>(j, q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A) \<union> set D.
          (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j"

  have 1: "\<forall>(l, t, t')\<in>set []. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) = {}"
          "fv\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) = {}" "ground {}"
    using \<A>(2) unfolding typing_cond\<^sub>s\<^sub>s\<^sub>t_def by simp_all

  have 2: "\<And>n. \<forall>(l, t, t')\<in>set []. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (proj_unl n \<A>) = {}"
          "\<And>n. fv\<^sub>s\<^sub>s\<^sub>t (proj_unl n \<A>) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (proj_unl n \<A>) = {}"
    using 1(1,2) sst_vars_proj_subset[of _ \<A>] by fast+

  have 3: "\<And>n. par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n \<A>) Sec"
    using par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_proj[OF \<A>(1)] by metis

  have 4:
      "\<lbrakk>{}; set (unlabel []) \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>'; unlabel \<A>\<rbrakk>\<^sub>s \<I>' \<longleftrightarrow>
        (\<exists>B\<in>set (tr\<^sub>p\<^sub>c \<A> []). \<lbrakk>{}; unlabel B\<rbrakk>\<^sub>d \<I>')"
    when \<I>': "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>'" for \<I>'
    using tr_par_sem_equiv[OF 1 _ \<I>'] \<A>(1)
    unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def constr_sem_d_def by auto

  obtain \<A>' where \<A>': "\<A>' \<in> set (tr\<^sub>p\<^sub>c \<A> [])" "\<I> \<Turnstile> \<langle>unlabel \<A>'\<rangle>"
    using 4[OF \<I>(2)] \<I>(1) unfolding constr_sem_d_def by moura

  obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>:
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)" "\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel \<A>'\<rangle>"
      "(\<forall>n. (\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>'\<rangle>)) \<or> (\<exists>\<A>''. prefix \<A>'' \<A>' \<and> (strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A>'' Sec \<I>\<^sub>\<tau>))"
    using par_comp_constr[OF tr_par_preserves_par_comp[OF \<A>(1) \<A>'(1)]
                             tr_par_preserves_typing_cond[OF \<A> \<A>'(1)]
                             \<A>'(2) \<I>(2)]
    by moura

  have \<I>\<^sub>\<tau>': "\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s unlabel \<A>" using 4[OF \<I>\<^sub>\<tau>(1)] \<A>'(1) \<I>\<^sub>\<tau>(4) unfolding constr_sem_d_def by auto

  show ?thesis
  proof (cases "\<forall>n. (\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>'\<rangle>)")
    case True
    { fix n assume "\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl n \<A>'\<rangle>"
      hence "\<lbrakk>{}; {}; unlabel (proj n \<A>)\<rbrakk>\<^sub>s \<I>\<^sub>\<tau>"
        using tr_par_proj[OF \<A>'(1), of n]
              tr_par_sem_equiv[OF 2(1,2) 1(3) _ \<I>\<^sub>\<tau>(1), of n] 3(1)
        unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def proj_def constr_sem_d_def by force
    } thus ?thesis using True \<I>\<^sub>\<tau>(1,2,3) \<I>\<^sub>\<tau>' by metis
  next
    case False
    then obtain \<A>''::"('fun,'var,'lbl) labeled_strand" where \<A>'':
        "prefix \<A>'' \<A>'" "strand_leaks\<^sub>l\<^sub>s\<^sub>t \<A>'' Sec \<I>\<^sub>\<tau>"
      using \<I>\<^sub>\<tau> by blast
    moreover {
      fix t l assume *: "\<lbrakk>{}; unlabel (proj l \<A>'')@[send\<langle>t\<rangle>\<^sub>s\<^sub>t]\<rbrakk>\<^sub>d \<I>\<^sub>\<tau>"
      have "\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel (proj l \<A>'')\<rangle>" "ik\<^sub>s\<^sub>t (unlabel (proj l \<A>'')) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<^sub>\<tau> \<turnstile> t \<cdot> \<I>\<^sub>\<tau>"
        using strand_sem_split(3,4)[OF *] unfolding constr_sem_d_def by auto
    } ultimately have "\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>'' \<I>\<^sub>\<tau>. \<exists>l.
            (\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel (proj l \<A>'')\<rangle>) \<and> ik\<^sub>s\<^sub>t (unlabel (proj l \<A>'')) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<^sub>\<tau> \<turnstile> t \<cdot> \<I>\<^sub>\<tau>"
      unfolding strand_leaks\<^sub>l\<^sub>s\<^sub>t_def constr_sem_d_def by metis
    then obtain s m where sm:
        "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t \<A>'' \<I>\<^sub>\<tau>"
        "\<I>\<^sub>\<tau> \<Turnstile> \<langle>unlabel (proj m \<A>'')\<rangle>"
        "ik\<^sub>s\<^sub>t (unlabel (proj m \<A>'')) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<^sub>\<tau> \<turnstile> s \<cdot> \<I>\<^sub>\<tau>"
      by moura

    \<comment> \<open>
      We now need to show that there is some prefix \<open>B\<close> of \<open>\<A>''\<close> that also leaks
      and where \<open>B \<in> set (tr C D)\<close> for some prefix \<open>C\<close> of \<open>\<A>\<close>
    \<close>
    obtain B::"('fun,'var,'lbl) labeled_strand"
        and C::"('fun,'var,'lbl) labeled_stateful_strand"
      where BC:
        "prefix B \<A>'" "prefix C \<A>" "B \<in> set (tr\<^sub>p\<^sub>c C [])"
        "ik\<^sub>s\<^sub>t (unlabel (proj m B)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<^sub>\<tau> \<turnstile> s \<cdot> \<I>\<^sub>\<tau>"
        "prefix B \<A>''"
      using tr_leaking_prefix_exists[OF \<A>'(1) \<A>''(1) sm(3)] prefix_order.order_trans[OF _ \<A>''(1)]
      by auto
    have "\<lbrakk>{}; unlabel (proj m B)\<rbrakk>\<^sub>d \<I>\<^sub>\<tau>"
      using sm(2) BC(5) unfolding prefix_def unlabel_def proj_def constr_sem_d_def by auto
    hence BC': "\<I>\<^sub>\<tau> \<Turnstile> \<langle>proj_unl m B@[send\<langle>s\<rangle>\<^sub>s\<^sub>t]\<rangle>"
      using BC(4) unfolding constr_sem_d_def by auto
    have BC'': "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>t B \<I>\<^sub>\<tau>"
      using BC(5) sm(1) unfolding prefix_def declassified\<^sub>l\<^sub>s\<^sub>t_def by auto
    have 5: "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n C) Sec" for n
      using \<A>(1) BC(2) par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_split(1)[THEN par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_proj]
      unfolding prefix_def by auto
    have "fv\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) = {}"
         "fv\<^sub>s\<^sub>s\<^sub>t (unlabel C) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
         "bvars\<^sub>s\<^sub>s\<^sub>t (unlabel C) \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
      using \<A>(2) BC(2) sst_vars_append_subset(1,2)[of "unlabel C"]
      unfolding typing_cond\<^sub>s\<^sub>s\<^sub>t_def prefix_def unlabel_def by auto
    hence "fv\<^sub>s\<^sub>s\<^sub>t (proj_unl n C) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (proj_unl n C) = {}" for n
      using sst_vars_proj_subset[of _ C] sst_vars_proj_subset[of _ \<A>]
      by blast
    hence 6:
        "\<forall>(l, t, t')\<in>set []. (fv t \<union> fv t') \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (proj_unl n C) = {}"
        "fv\<^sub>s\<^sub>s\<^sub>t (proj_unl n C) \<inter> bvars\<^sub>s\<^sub>s\<^sub>t (proj_unl n C) = {}"
        "ground {}"
      for n
      using 2 by auto
    have 7: "?P n C []" for n using 5 unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by simp
    have "s \<cdot> \<I>\<^sub>\<tau> = s" using \<I>\<^sub>\<tau>(1) BC'' \<A>(1) unfolding par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto
    hence "\<exists>n. (\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s proj_unl n C) \<and> ik\<^sub>s\<^sub>s\<^sub>t (proj_unl n C) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<^sub>\<tau> \<turnstile> s \<cdot> \<I>\<^sub>\<tau>"
      using tr_par_proj[OF BC(3), of m] BC'(1)
            tr_par_sem_equiv[OF 6 7 \<I>\<^sub>\<tau>(1), of m]
            tr_par_deduct_iff[OF tr_par_proj(1)[OF BC(3)], of \<I>\<^sub>\<tau> m s]
      unfolding proj_def constr_sem_d_def by auto
    hence "\<exists>n. \<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl n C@[Send s])" using strand_sem_append_stateful by simp
    moreover have "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t C \<I>\<^sub>\<tau>" by (metis tr_par_declassified_eq BC(3) BC'')
    ultimately show ?thesis using \<I>\<^sub>\<tau>(1,2,3) \<I>\<^sub>\<tau>' BC(2) unfolding strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by metis
  qed
qed


subsection \<open>Theorem: The Stateful Compositionality Result, on the Protocol Level\<close>
abbreviation wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t where
  "wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t V \<A> \<equiv> wf'\<^sub>s\<^sub>s\<^sub>t V (unlabel \<A>)"

text \<open>
  We state our result on the level of protocol traces (i.e., the constraints reachable in a
  symbolic execution of the actual protocol). Hence, we do not need to convert protocol strands
  to intruder constraints in the following well-formedness definitions.
\<close>
definition wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s::"('fun,'var,'lbl) labeled_stateful_strand set \<Rightarrow> bool" where
  "wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s \<S> \<equiv> (\<forall>\<A> \<in> \<S>. wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t {} \<A>) \<and> (\<forall>\<A> \<in> \<S>. \<forall>\<A>' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' = {})"

definition wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s'::
  "('fun,'var,'lbl) labeled_stateful_strand set \<Rightarrow> ('fun,'var,'lbl) labeled_stateful_strand \<Rightarrow> bool"
where
  "wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s' \<S> \<A> \<equiv> (\<forall>\<A>' \<in> \<S>. wf'\<^sub>s\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) (unlabel \<A>')) \<and>
                 (\<forall>\<A>' \<in> \<S>. \<forall>\<A>'' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>'' = {}) \<and>
                 (\<forall>\<A>' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}) \<and>
                 (\<forall>\<A>' \<in> \<S>. fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' = {})"

definition typing_cond_prot_stateful where
  "typing_cond_prot_stateful \<P> \<equiv>
    wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s \<P> \<and>
    tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` \<P>) \<union> pair ` \<Union>(setops\<^sub>s\<^sub>s\<^sub>t ` unlabel ` \<P>)) \<and>
    wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` \<P>)) \<and>
    (\<forall>S \<in> \<P>. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel S))"

definition par_comp_prot_stateful where
  "par_comp_prot_stateful \<P> Sec \<equiv>
    (\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow>
      GSMP_disjoint (\<Union>\<A> \<in> \<P>. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>))
                    (\<Union>\<A> \<in> \<P>. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>)) Sec) \<and>
    ground Sec \<and> (\<forall>s \<in> Sec. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> Sec) \<and>
    (\<forall>(i,p) \<in> \<Union>\<A> \<in> \<P>. setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<forall>(j,q) \<in> \<Union>\<A> \<in> \<P>. setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>.
      (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j) \<and>
    typing_cond_prot_stateful \<P>"

definition component_secure_prot_stateful where
  "component_secure_prot_stateful n P Sec attack \<equiv>
    (\<forall>\<A> \<in> P. suffix [(ln n, Send (Fun attack []))] \<A> \<longrightarrow>
     (\<forall>\<I>\<^sub>\<tau>. (interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)) \<longrightarrow>
            \<not>(\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl n \<A>)) \<and>
            (\<forall>\<A>'. prefix \<A>' \<A> \<longrightarrow>
                    (\<forall>t \<in> Sec-declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<not>(\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl n \<A>'@[Send t]))))))"

definition component_leaks_stateful where
  "component_leaks_stateful n \<A> Sec \<equiv>
    (\<exists>\<A>' \<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and> prefix \<A>' \<A> \<and>
             (\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. (\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl n \<A>'@[Send t]))))"

definition unsat_stateful where
  "unsat_stateful \<A> \<equiv> (\<forall>\<I>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<longrightarrow> \<not>(\<I> \<Turnstile>\<^sub>s unlabel \<A>))"

lemma wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s_eqs_wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s'[simp]: "wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s S = wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s' S []"
unfolding wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s_def wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s'_def unlabel_def wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t_def by simp

lemma par_comp_prot_impl_par_comp_stateful:
  assumes "par_comp_prot_stateful \<P> Sec" "\<A> \<in> \<P>"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> Sec"
proof -
  have *:
      "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow>
          GSMP_disjoint (\<Union>\<A> \<in> \<P>. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>))
                        (\<Union>\<A> \<in> \<P>. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>)) Sec"
    using assms(1) unfolding par_comp_prot_stateful_def by argo
  { fix l1 l2::'lbl assume **: "l1 \<noteq> l2"
    hence ***:
        "GSMP_disjoint (\<Union>\<A> \<in> \<P>. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>))
                       (\<Union>\<A> \<in> \<P>. trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>)) Sec"
      using * by auto
    have "GSMP_disjoint (trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>))
                        (trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>)) Sec"
      using GSMP_disjoint_subset[OF ***] assms(2) by auto
  } hence "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow>
              GSMP_disjoint (trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l1 \<A>))
                            (trms\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l2 \<A>)) Sec"
    by metis
  moreover have "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>.
                    (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j"
    using assms(1,2) unfolding par_comp_prot_stateful_def by blast
  ultimately show ?thesis
    using assms
    unfolding par_comp_prot_stateful_def par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def
    by fast
qed

lemma typing_cond_prot_impl_typing_cond_stateful:
  assumes "typing_cond_prot_stateful \<P>" "\<A> \<in> \<P>"
  shows "typing_cond\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
proof -
  have 1: "wf'\<^sub>s\<^sub>s\<^sub>t {} (unlabel \<A>)" "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    using assms unfolding typing_cond_prot_stateful_def wf\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>s_def by auto

  have "tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` \<P>) \<union> pair ` \<Union>(setops\<^sub>s\<^sub>s\<^sub>t ` unlabel ` \<P>))"
       "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` \<P>))"
       "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<subseteq> \<Union>(trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` \<P>)"
       "SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)) - Var`\<V> \<subseteq>
        SMP (\<Union>(trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` \<P>) \<union> pair ` \<Union>(setops\<^sub>s\<^sub>s\<^sub>t ` unlabel ` \<P>)) - Var`\<V>"
    using assms SMP_mono[of "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
                            "\<Union>(trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` \<P>) \<union> pair ` \<Union>(setops\<^sub>s\<^sub>s\<^sub>t ` unlabel ` \<P>)"]
    unfolding typing_cond_prot_stateful_def
    by (metis, metis, auto)
  hence 2: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>))" and 3: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by (meson subsetD)+

  have 4: "list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel \<A>)" using assms unfolding typing_cond_prot_stateful_def by auto

  show ?thesis using 1 2 3 4 unfolding typing_cond\<^sub>s\<^sub>s\<^sub>t_def tfr\<^sub>s\<^sub>s\<^sub>t_def by blast
qed

theorem par_comp_constr_prot_stateful:
  assumes P: "P = composed_prot Pi" "par_comp_prot_stateful P Sec" "\<forall>n. component_prot n (Pi n)"
  and left_secure: "component_secure_prot_stateful n (Pi n) Sec attack"
  shows "\<forall>\<A> \<in> P. suffix [(ln n, Send (Fun attack []))] \<A> \<longrightarrow>
                  unsat_stateful \<A> \<or> (\<exists>m. n \<noteq> m \<and> component_leaks_stateful m \<A> Sec)"
proof -
  { fix \<A> \<A>' assume \<A>: "\<A> = \<A>'@[(ln n, Send (Fun attack []))]" "\<A> \<in> P"
    let ?P = "\<exists>\<A>' \<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and> prefix \<A>' \<A> \<and>
                   (\<exists>t \<in> Sec-declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<exists>m. n \<noteq> m \<and> (\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl m \<A>'@[Send t])))"
    have tcp: "typing_cond_prot_stateful P" using P(2) unfolding par_comp_prot_stateful_def by simp
    have par_comp: "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> Sec" "typing_cond\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)"
      using par_comp_prot_impl_par_comp_stateful[OF P(2) \<A>(2)]
            typing_cond_prot_impl_typing_cond_stateful[OF tcp \<A>(2)]
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
            "\<forall>I. declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I = declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A) I"
        unfolding proj_def declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto
      hence "\<exists>B. prefix B (proj n \<A>) \<and> proj_unl n A = proj_unl n B \<and>
                 (\<forall>I. declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I = declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t B I)"
        using * by metis
    }
    ultimately have *:
        "\<forall>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<longrightarrow>
                  \<not>(\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl n \<A>)) \<and> (\<forall>\<A>'. prefix \<A>' \<A> \<longrightarrow>
                        (\<forall>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<not>(\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl n \<A>'@[Send t]))))"
      using left_secure
      unfolding component_secure_prot_stateful_def composed_prot_def suffix_def
      by metis
    { fix \<I> assume \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "\<I> \<Turnstile>\<^sub>s unlabel \<A>"
      obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>:
          "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
          "\<exists>\<A>'. prefix \<A>' \<A> \<and> (\<A>' leaks Sec under \<I>\<^sub>\<tau>)"
        using par_comp_constr_stateful[OF par_comp \<I>(2,1)] * by moura
      hence "\<exists>\<A>'. prefix \<A>' \<A> \<and> (\<exists>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>. \<exists>m.
                  n \<noteq> m \<and> (\<I>\<^sub>\<tau> \<Turnstile>\<^sub>s (proj_unl m \<A>'@[Send t])))"
        using \<I>\<^sub>\<tau>(4) * unfolding strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by metis
      hence ?P using \<I>\<^sub>\<tau>(1,2,3) by auto
    } hence "unsat_stateful \<A> \<or> (\<exists>m. n \<noteq> m \<and> component_leaks_stateful m \<A> Sec)"
      by (metis unsat_stateful_def component_leaks_stateful_def)
  } thus ?thesis unfolding suffix_def by metis
qed

end

subsection \<open>Automated Compositionality Conditions\<close>
definition comp_GSMP_disjoint where
  "comp_GSMP_disjoint public arity Ana \<Gamma> A' B' A B C \<equiv>
    let B\<delta> = B \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t (set A)))
    in has_all_wt_instances_of \<Gamma> (set A') (set A) \<and>
       has_all_wt_instances_of \<Gamma> (set B') (set B\<delta>) \<and>
       finite_SMP_representation arity Ana \<Gamma> A \<and>
       finite_SMP_representation arity Ana \<Gamma> B\<delta> \<and>
       (\<forall>t \<in> set A. \<forall>s \<in> set B\<delta>. \<Gamma> t = \<Gamma> s \<and> mgu t s \<noteq> None \<longrightarrow>
         (intruder_synth' public arity {} t \<and> intruder_synth' public arity {} s) \<or>
         (\<exists>u \<in> set C. is_wt_instance_of_cond \<Gamma> t u) \<and> (\<exists>u \<in> set C. is_wt_instance_of_cond \<Gamma> s u))"

definition comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t where
  "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> pair_fun A M C \<equiv>
  let L = remdups (map (the_LabelN \<circ> fst) (filter (Not \<circ> is_LabelS) A));
      MP0 = \<lambda>B. remdups (trms_list\<^sub>s\<^sub>s\<^sub>t B@map (pair' pair_fun) (setops_list\<^sub>s\<^sub>s\<^sub>t B));
      pr = \<lambda>l. MP0 (proj_unl l A)
  in length L > 1 \<and>
     list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) (MP0 (unlabel A)) \<and>
     list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) C \<and>
     has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set C)) (set C) \<and>
     is_TComp_var_instance_closed \<Gamma> C \<and>
     (\<forall>i \<in> set L. \<forall>j \<in> set L. i \<noteq> j \<longrightarrow>
        comp_GSMP_disjoint public arity Ana \<Gamma> (pr i) (pr j) (M i) (M j) C) \<and>
     (\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. i \<noteq> j \<longrightarrow>
        (let s = pair' pair_fun p; t = pair' pair_fun q
         in mgu s (t \<cdot> var_rename (max_var s)) = None))"

locale labeled_stateful_typed_model' =
  stateful_typed_model' arity public Ana \<Gamma> Pair
+ labeled_typed_model' arity public Ana \<Gamma> label_witness1 label_witness2
  for arity::"'fun \<Rightarrow> nat"
  and public::"'fun \<Rightarrow> bool"
  and Ana::"('fun,(('fun,'atom::finite) term_type \<times> nat)) term
            \<Rightarrow> (('fun,(('fun,'atom) term_type \<times> nat)) term list
               \<times> ('fun,(('fun,'atom) term_type \<times> nat)) term list)"
  and \<Gamma>::"('fun,(('fun,'atom) term_type \<times> nat)) term \<Rightarrow> ('fun,'atom) term_type"
  and Pair::"'fun"
  and label_witness1::"'lbl"
  and label_witness2::"'lbl"
begin

sublocale labeled_stateful_typed_model
by unfold_locales

lemma GSMP_disjoint_if_comp_GSMP_disjoint:
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
  assumes AB'_wf: "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) A'" "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) B'"
    and C_wf: "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) C"
    and AB'_disj: "comp_GSMP_disjoint public arity Ana \<Gamma> A' B' A B C"
  shows "GSMP_disjoint (set A') (set B') ((f (set C)) - {m. {} \<turnstile>\<^sub>c m})"
using GSMP_disjointI[of A' B' A B] AB'_wf AB'_disj C_wf
unfolding comp_GSMP_disjoint_def f_def wf\<^sub>t\<^sub>r\<^sub>m_code list_all_iff Let_def by fast

lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_if_comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t:
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
  assumes A: "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair A M C"
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t A ((f (set C)) - {m. {} \<turnstile>\<^sub>c m})"
proof (unfold par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def; intro conjI)
  let ?Sec = "(f (set C)) - {m. {} \<turnstile>\<^sub>c m}"
  let ?L = "remdups (map (the_LabelN \<circ> fst) (filter (Not \<circ> is_LabelS) A))"
  let ?N1 = "\<lambda>B. remdups (trms_list\<^sub>s\<^sub>s\<^sub>t B@map (pair' Pair) (setops_list\<^sub>s\<^sub>s\<^sub>t B))"
  let ?N2 = "\<lambda>B. trms\<^sub>s\<^sub>s\<^sub>t B \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t B"
  let ?pr = "\<lambda>l. ?N1 (proj_unl l A)"
  let ?\<alpha> = "\<lambda>p. var_rename (max_var (pair p))"

  have 0:
      "length ?L > 1"
      "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) (?N1 (unlabel A))"
      "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) C"
      "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set C)) (set C)"
      "is_TComp_var_instance_closed \<Gamma> C"
      "\<forall>i \<in> set ?L. \<forall>j \<in> set ?L. i \<noteq> j \<longrightarrow>
        comp_GSMP_disjoint public arity Ana \<Gamma> (?pr i) (?pr j) (M i) (M j) C"
      "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. i \<noteq> j \<longrightarrow> mgu (pair p) (pair q \<cdot> ?\<alpha> p) = None"
    using A unfolding comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def pair_code by meson+

  have L_in_iff: "l \<in> set ?L \<longleftrightarrow> (\<exists>a \<in> set A. is_LabelN l a)" for l by force

  have A_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel A))"
    using 0(2)
    unfolding pair_code wf\<^sub>t\<^sub>r\<^sub>m_code list_all_iff trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t setops_list\<^sub>s\<^sub>s\<^sub>t_is_setops\<^sub>s\<^sub>s\<^sub>t
    by auto
  hence A_proj_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l A) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l A))" for l
    using trms\<^sub>s\<^sub>s\<^sub>t_proj_subset(1)[of l A] setops\<^sub>s\<^sub>s\<^sub>t_proj_subset(1)[of l A] by blast
  hence A_proj_wf_trms': "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) (?N1 (proj_unl l A))" for l
    unfolding pair_code wf\<^sub>t\<^sub>r\<^sub>m_code list_all_iff trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t setops_list\<^sub>s\<^sub>s\<^sub>t_is_setops\<^sub>s\<^sub>s\<^sub>t
    by auto

  note C_wf_trms = 0(3)[unfolded list_all_iff wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric]]

  note 1 = has_all_wt_instances_ofD'[OF wf_trms_subterms[OF C_wf_trms] C_wf_trms 0(4)]

  have 2: "GSMP (?N2 (proj_unl l A)) \<subseteq> GSMP (?N2 (proj_unl l' A))" when "l \<notin> set ?L" for l l'
    using that L_in_iff GSMP_mono[of "?N2 (proj_unl l A)" "?N2 (proj_unl l' A)"]
          trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subset_if_no_label[of l A]
          setops\<^sub>s\<^sub>s\<^sub>t_unlabel_subset_if_no_label[of l A]
    unfolding list_ex_iff by fast

  have 3: "GSMP_disjoint (?N2 (proj_unl l1 A)) (?N2 (proj_unl l2 A)) ?Sec"
    when "l1 \<in> set ?L" "l2 \<in> set ?L" "l1 \<noteq> l2" for l1 l2
  proof -
    have "GSMP_disjoint (set (?N1 (proj_unl l1 A))) (set (?N1 (proj_unl l2 A))) ?Sec"
      using 0(6) that
            GSMP_disjoint_if_comp_GSMP_disjoint[
              OF A_proj_wf_trms'[of l1] A_proj_wf_trms'[of l2] 0(3),
              of "M l1" "M l2"]
      unfolding f_def by blast
    thus ?thesis
      unfolding pair_code trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t setops_list\<^sub>s\<^sub>s\<^sub>t_is_setops\<^sub>s\<^sub>s\<^sub>t
      by simp
  qed

  obtain a1 a2 where a: "a1 \<in> set ?L" "a2 \<in> set ?L" "a1 \<noteq> a2"
    using remdups_ex2[OF 0(1)] by moura

  show "ground ?Sec" unfolding f_def by fastforce

  { fix i p j q
    assume p: "(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" and q: "(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      and pq: "\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)"

    have "\<exists>\<delta>. Unifier \<delta> (pair p) (pair q \<cdot> ?\<alpha> p)"
      using pq vars_term_disjoint_imp_unifier[OF var_rename_fv_disjoint[of "pair p"], of _ "pair q"]
      by (metis (no_types, lifting) subst_subst_compose var_rename_inv_comp)
    hence "i = j" using 0(7) mgu_None_is_subst_neq[of "pair p" "pair q \<cdot> ?\<alpha> p"] p q by fast
  } thus "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j"
    by blast

  show "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (?N2 (proj_unl l1 A)) (?N2 (proj_unl l2 A)) ?Sec"
    using 2 3 3[OF a] unfolding GSMP_disjoint_def by blast

  show "\<forall>s \<in> ?Sec. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> ?Sec"
  proof (intro ballI)
    fix s s'
    assume s: "s \<in> ?Sec" and s': "s' \<sqsubseteq> s"
    then obtain t \<delta> where t: "t \<in> set C" "s = t \<cdot> \<delta>" "fv s = {}" "\<not>{} \<turnstile>\<^sub>c s"
        and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
      unfolding f_def by blast

    obtain m \<theta> where m: "m \<in> set C" "s' = m \<cdot> \<theta>" and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
      using TComp_var_and_subterm_instance_closed_has_subterms_instances[
              OF 0(5,4) C_wf_trms in_subterms_Union[OF t(1)] s'[unfolded t(2)] \<delta>]
      by blast
    thus "{} \<turnstile>\<^sub>c s' \<or> s' \<in> ?Sec"
      using ground_subterm[OF t(3) s']
      unfolding f_def by blast
  qed
qed

lemma par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_if_comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t':
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
  assumes a: "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair A M C"
    and B: "\<forall>b \<in> set B. \<exists>a \<in> set A. \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
      (is "\<forall>b \<in> set B. \<exists>a \<in> set A. \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> ?D \<delta>")
  shows "par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t B ((f (set C)) - {m. {} \<turnstile>\<^sub>c m})"
proof (unfold par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def; intro conjI)
  define N1 where "N1 \<equiv> \<lambda>B::('fun, ('fun,'atom) term_type \<times> nat) stateful_strand.
    remdups (trms_list\<^sub>s\<^sub>s\<^sub>t B@map (pair' Pair) (setops_list\<^sub>s\<^sub>s\<^sub>t B))"

  define N2 where "N2 \<equiv> \<lambda>B::('fun, ('fun,'atom) term_type \<times> nat) stateful_strand.
    trms\<^sub>s\<^sub>s\<^sub>t B \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t B"

  define L where "L \<equiv> \<lambda>A::('fun, ('fun,'atom) term_type \<times> nat, 'lbl) labeled_stateful_strand.
    remdups (map (the_LabelN \<circ> fst) (filter (Not \<circ> is_LabelS) A))"

  define \<alpha> where "\<alpha> \<equiv> \<lambda>p. var_rename (max_var (pair p::('fun, ('fun,'atom) term_type \<times> nat) term))
    ::('fun, ('fun,'atom) term_type \<times> nat) subst"

  let ?Sec = "(f (set C)) - {m. {} \<turnstile>\<^sub>c m}"

  have 0:
      "length (L A) > 1"
      "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) (N1 (unlabel A))"
      "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) C"
      "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set C)) (set C)"
      "is_TComp_var_instance_closed \<Gamma> C"
      "\<forall>i \<in> set (L A). \<forall>j \<in> set (L A). i \<noteq> j \<longrightarrow>
        comp_GSMP_disjoint public arity Ana \<Gamma> (N1 (proj_unl i A)) (N1 (proj_unl j A)) (M i) (M j) C"
      "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. i \<noteq> j \<longrightarrow> mgu (pair p) (pair q \<cdot> \<alpha> p) = None"
    using a unfolding comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def pair_code L_def N1_def \<alpha>_def by meson+

  note 1 = trms\<^sub>s\<^sub>s\<^sub>t_proj_subset(1) setops\<^sub>s\<^sub>s\<^sub>t_proj_subset(1)

  have N1_iff_N2: "set (N1 A) = N2 A" for A
    unfolding pair_code trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t setops_list\<^sub>s\<^sub>s\<^sub>t_is_setops\<^sub>s\<^sub>s\<^sub>t N1_def N2_def by simp

  have N2_proj_subset: "N2 (proj_unl l A) \<subseteq> N2 (unlabel A)"
    for l::'lbl and A::"('fun, ('fun,'atom) term_type \<times> nat, 'lbl) labeled_stateful_strand"
    using 1(1)[of l A] image_mono[OF 1(2)[of l A], of pair] unfolding N2_def by blast

  have L_in_iff: "l \<in> set (L A) \<longleftrightarrow> (\<exists>a \<in> set A. is_LabelN l a)" for l A
    unfolding L_def by force

  have L_B_subset_A: "l \<in> set (L A)" when l: "l \<in> set (L B)" for l
    using L_in_iff[of l B] L_in_iff[of l A] B l by fastforce

  note B_setops = setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_wt_instance_ex[OF B]

  have B_proj: "\<forall>b \<in> set (proj l B). \<exists>a \<in> set (proj l A). \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> ?D \<delta>" for l
    using proj_instance_ex[OF B] by fast

  have B': "\<forall>t \<in> N2 (unlabel B). \<exists>s \<in> N2 (unlabel A). \<exists>\<delta>. t = s \<cdot> \<delta> \<and> ?D \<delta>"
    using trms\<^sub>s\<^sub>s\<^sub>t_setops\<^sub>s\<^sub>s\<^sub>t_wt_instance_ex[OF B] unfolding N2_def by blast

  have B'_proj: "\<forall>t \<in> N2 (proj_unl l B). \<exists>s \<in> N2 (proj_unl l A). \<exists>\<delta>. t = s \<cdot> \<delta> \<and> ?D \<delta>" for l
    using trms\<^sub>s\<^sub>s\<^sub>t_setops\<^sub>s\<^sub>s\<^sub>t_wt_instance_ex[OF B_proj] unfolding N2_def by presburger

  have A_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (N2 (unlabel A))"
    using N1_iff_N2[of "unlabel A"] 0(2) unfolding wf\<^sub>t\<^sub>r\<^sub>m_code list_all_iff by auto
  hence A_proj_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (N2 (proj_unl l A))" for l
    using 1[of l] unfolding N2_def by blast
  hence A_proj_wf_trms': "list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) (N1 (proj_unl l A))" for l
    using N1_iff_N2[of "proj_unl l A"] unfolding wf\<^sub>t\<^sub>r\<^sub>m_code list_all_iff by presburger

  note C_wf_trms = 0(3)[unfolded list_all_iff wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric]]

  have 2: "GSMP (N2 (proj_unl l A)) \<subseteq> GSMP (N2 (proj_unl l' A))"
    when "l \<notin> set (L A)" for l l'
      and A::"('fun, ('fun,'atom) term_type \<times> nat, 'lbl) labeled_stateful_strand"
    using that L_in_iff[of _ A] GSMP_mono[of "N2 (proj_unl l A)" "N2 (proj_unl l' A)"]
          trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subset_if_no_label[of l A]
          setops\<^sub>s\<^sub>s\<^sub>t_unlabel_subset_if_no_label[of l A]
    unfolding list_ex_iff N2_def by fast

  have 3: "GSMP (N2 (proj_unl l B)) \<subseteq> GSMP (N2 (proj_unl l A))" (is "?X \<subseteq> ?Y") for l
  proof
    fix t assume "t \<in> ?X"
    hence t: "t \<in> SMP (N2 (proj_unl l B))" "fv t = {}" unfolding GSMP_def by simp_all
    have "t \<in> SMP (N2 (proj_unl l A))"
      using t(1) B'_proj[of l] SMP_wt_instances_subset[of "N2 (proj_unl l B)" "N2 (proj_unl l A)"]
      by metis
    thus "t \<in> ?Y" using t(2) unfolding GSMP_def by fast
  qed

  have "GSMP_disjoint (N2 (proj_unl l1 A)) (N2 (proj_unl l2 A)) ?Sec"
    when "l1 \<in> set (L A)" "l2 \<in> set (L A)" "l1 \<noteq> l2" for l1 l2
  proof -
    have "GSMP_disjoint (set (N1 (proj_unl l1 A))) (set (N1 (proj_unl l2 A))) ?Sec"
      using 0(6) that
            GSMP_disjoint_if_comp_GSMP_disjoint[
              OF A_proj_wf_trms'[of l1] A_proj_wf_trms'[of l2] 0(3),
              of "M l1" "M l2"]
      unfolding f_def by blast
    thus ?thesis using N1_iff_N2 by simp
  qed
  hence 4: "GSMP_disjoint (N2 (proj_unl l1 B)) (N2 (proj_unl l2 B)) ?Sec"
    when "l1 \<in> set (L A)" "l2 \<in> set (L A)" "l1 \<noteq> l2" for l1 l2
    using that 3 unfolding GSMP_disjoint_def by blast

  { fix i p j q
    assume p: "(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B" and q: "(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B"
      and pq: "\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)"

    obtain p' \<delta>p where p': "(i,p') \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "p = p' \<cdot>\<^sub>p \<delta>p" "pair p = pair p' \<cdot> \<delta>p"
      using p B_setops unfolding pair_def by auto

    obtain q' \<delta>q where q': "(j,q') \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "q = q' \<cdot>\<^sub>p \<delta>q" "pair q = pair q' \<cdot> \<delta>q"
      using q B_setops unfolding pair_def by auto

    obtain \<theta> where "Unifier \<theta> (pair p) (pair q)" using pq by blast
    hence "\<exists>\<delta>. Unifier \<delta> (pair p') (pair q' \<cdot> \<alpha> p')"
      using p'(3) q'(3) var_rename_inv_comp[of "pair q'"] subst_subst_compose
            vars_term_disjoint_imp_unifier[
              OF var_rename_fv_disjoint[of "pair p'"],
              of "\<delta>p \<circ>\<^sub>s \<theta>" "pair q'" "var_rename_inv (max_var_set (fv (pair p'))) \<circ>\<^sub>s \<delta>q \<circ>\<^sub>s \<theta>"]
      unfolding \<alpha>_def by fastforce
    hence "i = j"
      using mgu_None_is_subst_neq[of "pair p'" "pair q' \<cdot> \<alpha> p'"] p'(1) q'(1) 0(7)
      unfolding \<alpha>_def by fast
  } thus "\<forall>(i,p) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B. \<forall>(j,q) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B. (\<exists>\<delta>. Unifier \<delta> (pair p) (pair q)) \<longrightarrow> i = j"
    by blast

  obtain a1 a2 where a: "a1 \<in> set (L A)" "a2 \<in> set (L A)" "a1 \<noteq> a2"
    using remdups_ex2[OF 0(1)[unfolded L_def]] unfolding L_def by moura

  show "\<forall>l1 l2. l1 \<noteq> l2 \<longrightarrow> GSMP_disjoint (N2 (proj_unl l1 B)) (N2 (proj_unl l2 B)) ?Sec"
    using 2[of _ B] 4 4[OF a] L_B_subset_A unfolding GSMP_disjoint_def by blast

  show "ground ?Sec" unfolding f_def by fastforce

  show "\<forall>s \<in> ?Sec. \<forall>s' \<in> subterms s. {} \<turnstile>\<^sub>c s' \<or> s' \<in> ?Sec"
  proof (intro ballI)
    fix s s'
    assume s: "s \<in> ?Sec" and s': "s' \<sqsubseteq> s"
    then obtain t \<delta> where t: "t \<in> set C" "s = t \<cdot> \<delta>" "fv s = {}" "\<not>{} \<turnstile>\<^sub>c s"
        and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
      unfolding f_def by blast

    obtain m \<theta> where m: "m \<in> set C" "s' = m \<cdot> \<theta>" and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
      using TComp_var_and_subterm_instance_closed_has_subterms_instances[
              OF 0(5,4) C_wf_trms in_subterms_Union[OF t(1)] s'[unfolded t(2)] \<delta>]
      by blast
    thus "{} \<turnstile>\<^sub>c s' \<or> s' \<in> ?Sec"
      using ground_subterm[OF t(3) s']
      unfolding f_def by blast
  qed
qed

end

end
