(*
(C) Copyright Andreas Viktor Hess, DTU, 2015-2020

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

(*  Title:      Intruder_Deduction.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>Dolev-Yao Intruder Model\<close>
theory Intruder_Deduction
imports Messages More_Unification
begin

subsection \<open>Syntax for the Intruder Deduction Relations\<close>
consts INTRUDER_SYNTH::"('f,'v) terms \<Rightarrow> ('f,'v) term \<Rightarrow> bool" (infix "\<turnstile>\<^sub>c" 50)
consts INTRUDER_DEDUCT::"('f,'v) terms \<Rightarrow> ('f,'v) term \<Rightarrow> bool" (infix "\<turnstile>" 50)


subsection \<open>Intruder Model Locale\<close>
text \<open>
  The intruder model is parameterized over arbitrary function symbols (e.g, cryptographic operators)
  and variables. It requires three functions:
  - \<open>arity\<close> that assigns an arity to each function symbol.
  - \<open>public\<close> that partitions the function symbols into those that will be available to the intruder
    and those that will not.
  - \<open>Ana\<close>, the analysis interface, that defines how messages can be decomposed (e.g., decryption).
\<close>
locale intruder_model =
  fixes arity :: "'fun \<Rightarrow> nat"
    and public :: "'fun \<Rightarrow> bool"
    and Ana :: "('fun,'var) term \<Rightarrow> (('fun,'var) term list \<times> ('fun,'var) term list)"
  assumes Ana_keys_fv: "\<And>t K R. Ana t = (K,R) \<Longrightarrow> fv\<^sub>s\<^sub>e\<^sub>t (set K) \<subseteq> fv t"
    and Ana_keys_wf: "\<And>t k K R f T.
      Ana t = (K,R) \<Longrightarrow> (\<And>g S. Fun g S \<sqsubseteq> t \<Longrightarrow> length S = arity g)
                    \<Longrightarrow> k \<in> set K \<Longrightarrow> Fun f T \<sqsubseteq> k \<Longrightarrow> length T = arity f"
    and Ana_var[simp]: "\<And>x. Ana (Var x) = ([],[])"
    and Ana_fun_subterm: "\<And>f T K R. Ana (Fun f T) = (K,R) \<Longrightarrow> set R \<subseteq> set T"
    and Ana_subst: "\<And>t \<delta> K R. \<lbrakk>Ana t = (K,R); K \<noteq> [] \<or> R \<noteq> []\<rbrakk> \<Longrightarrow> Ana (t \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>,R \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
begin

lemma Ana_subterm: assumes "Ana t = (K,T)" shows "set T \<subset> subterms t"
using assms
by (cases t)
   (simp add: psubsetI,
    metis Ana_fun_subterm Fun_gt_params UN_I term.order_refl
          params_subterms psubsetI subset_antisym subset_trans)

lemma Ana_subterm': "s \<in> set (snd (Ana t)) \<Longrightarrow> s \<sqsubseteq> t"
using Ana_subterm by (cases "Ana t") auto

lemma Ana_vars: assumes "Ana t = (K,M)" shows "fv\<^sub>s\<^sub>e\<^sub>t (set K) \<subseteq> fv t" "fv\<^sub>s\<^sub>e\<^sub>t (set M) \<subseteq> fv t"
by (rule Ana_keys_fv[OF assms]) (use Ana_subterm[OF assms] subtermeq_vars_subset in auto)

abbreviation \<V> where "\<V> \<equiv> UNIV::'var set"
abbreviation \<Sigma>n ("\<Sigma>\<^sup>_") where "\<Sigma>\<^sup>n \<equiv> {f::'fun. arity f = n}"
abbreviation \<Sigma>npub ("\<Sigma>\<^sub>p\<^sub>u\<^sub>b\<^sup>_") where "\<Sigma>\<^sub>p\<^sub>u\<^sub>b\<^sup>n \<equiv> {f. public f} \<inter> \<Sigma>\<^sup>n"
abbreviation \<Sigma>npriv ("\<Sigma>\<^sub>p\<^sub>r\<^sub>i\<^sub>v\<^sup>_") where "\<Sigma>\<^sub>p\<^sub>r\<^sub>i\<^sub>v\<^sup>n \<equiv> {f. \<not>public f} \<inter> \<Sigma>\<^sup>n"
abbreviation \<Sigma>\<^sub>p\<^sub>u\<^sub>b where "\<Sigma>\<^sub>p\<^sub>u\<^sub>b \<equiv> (\<Union>n. \<Sigma>\<^sub>p\<^sub>u\<^sub>b\<^sup>n)"
abbreviation \<Sigma>\<^sub>p\<^sub>r\<^sub>i\<^sub>v where "\<Sigma>\<^sub>p\<^sub>r\<^sub>i\<^sub>v \<equiv> (\<Union>n. \<Sigma>\<^sub>p\<^sub>r\<^sub>i\<^sub>v\<^sup>n)"
abbreviation \<Sigma> where "\<Sigma> \<equiv> (\<Union>n. \<Sigma>\<^sup>n)"
abbreviation \<C> where "\<C> \<equiv> \<Sigma>\<^sup>0"
abbreviation \<C>\<^sub>p\<^sub>u\<^sub>b where "\<C>\<^sub>p\<^sub>u\<^sub>b \<equiv> {f. public f} \<inter> \<C>"
abbreviation \<C>\<^sub>p\<^sub>r\<^sub>i\<^sub>v where "\<C>\<^sub>p\<^sub>r\<^sub>i\<^sub>v \<equiv> {f. \<not>public f} \<inter> \<C>"
abbreviation \<Sigma>\<^sub>f where "\<Sigma>\<^sub>f \<equiv> \<Sigma> - \<C>"
abbreviation \<Sigma>\<^sub>f\<^sub>p\<^sub>u\<^sub>b where "\<Sigma>\<^sub>f\<^sub>p\<^sub>u\<^sub>b \<equiv> \<Sigma>\<^sub>f \<inter> \<Sigma>\<^sub>p\<^sub>u\<^sub>b"
abbreviation \<Sigma>\<^sub>f\<^sub>p\<^sub>r\<^sub>i\<^sub>v where "\<Sigma>\<^sub>f\<^sub>p\<^sub>r\<^sub>i\<^sub>v \<equiv> \<Sigma>\<^sub>f \<inter> \<Sigma>\<^sub>p\<^sub>r\<^sub>i\<^sub>v"

lemma disjoint_fun_syms: "\<Sigma>\<^sub>f \<inter> \<C> = {}" by auto
lemma id_union_univ: "\<Sigma>\<^sub>f \<union> \<C> = UNIV" "\<Sigma> = UNIV" by auto
lemma const_arity_eq_zero[dest]: "c \<in> \<C> \<Longrightarrow> arity c = 0" by simp
lemma const_pub_arity_eq_zero[dest]: "c \<in> \<C>\<^sub>p\<^sub>u\<^sub>b \<Longrightarrow> arity c = 0 \<and> public c" by simp
lemma const_priv_arity_eq_zero[dest]: "c \<in> \<C>\<^sub>p\<^sub>r\<^sub>i\<^sub>v \<Longrightarrow> arity c = 0 \<and> \<not>public c" by simp
lemma fun_arity_gt_zero[dest]: "f \<in> \<Sigma>\<^sub>f \<Longrightarrow> arity f > 0" by fastforce
lemma pub_fun_public[dest]: "f \<in> \<Sigma>\<^sub>f\<^sub>p\<^sub>u\<^sub>b \<Longrightarrow> public f" by fastforce
lemma pub_fun_arity_gt_zero[dest]: "f \<in> \<Sigma>\<^sub>f\<^sub>p\<^sub>u\<^sub>b \<Longrightarrow> arity f > 0" by fastforce

lemma \<Sigma>\<^sub>f_unfold: "\<Sigma>\<^sub>f = {f::'fun. arity f > 0}" by auto
lemma \<C>_unfold: "\<C> = {f::'fun. arity f = 0}" by auto
lemma \<C>pub_unfold: "\<C>\<^sub>p\<^sub>u\<^sub>b = {f::'fun. arity f = 0 \<and> public f}" by auto
lemma \<C>priv_unfold: "\<C>\<^sub>p\<^sub>r\<^sub>i\<^sub>v = {f::'fun. arity f = 0 \<and> \<not>public f}" by auto
lemma \<Sigma>npub_unfold: "(\<Sigma>\<^sub>p\<^sub>u\<^sub>b\<^sup>n) = {f::'fun. arity f = n \<and> public f}" by auto
lemma \<Sigma>npriv_unfold: "(\<Sigma>\<^sub>p\<^sub>r\<^sub>i\<^sub>v\<^sup>n) = {f::'fun. arity f = n \<and> \<not>public f}" by auto
lemma \<Sigma>fpub_unfold: "\<Sigma>\<^sub>f\<^sub>p\<^sub>u\<^sub>b = {f::'fun. arity f > 0 \<and> public f}" by auto
lemma \<Sigma>fpriv_unfold: "\<Sigma>\<^sub>f\<^sub>p\<^sub>r\<^sub>i\<^sub>v = {f::'fun. arity f > 0 \<and> \<not>public f}" by auto
lemma \<Sigma>n_m_eq: "\<lbrakk>(\<Sigma>\<^sup>n) \<noteq> {}; (\<Sigma>\<^sup>n) = (\<Sigma>\<^sup>m)\<rbrakk> \<Longrightarrow> n = m" by auto


subsection \<open>Term Well-formedness\<close>
definition "wf\<^sub>t\<^sub>r\<^sub>m t \<equiv> \<forall>f T. Fun f T \<sqsubseteq> t \<longrightarrow> length T = arity f"

abbreviation "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s T \<equiv> \<forall>t \<in> T. wf\<^sub>t\<^sub>r\<^sub>m t"

lemma Ana_keys_wf': "Ana t = (K,T) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> k \<in> set K \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m k"
using Ana_keys_wf unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by metis

lemma wf_trm_Var[simp]: "wf\<^sub>t\<^sub>r\<^sub>m (Var x)" unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by simp

lemma wf_trm_subst_range_Var[simp]: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)" by simp

lemma wf_trm_subst_range_iff: "(\<forall>x. wf\<^sub>t\<^sub>r\<^sub>m (\<theta> x)) \<longleftrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
by force

lemma wf_trm_subst_rangeD: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m (\<theta> x)"
by (metis wf_trm_subst_range_iff)

lemma wf_trm_subst_rangeI[intro]:
  "(\<And>x. wf\<^sub>t\<^sub>r\<^sub>m (\<delta> x)) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
by (metis wf_trm_subst_range_iff)

lemma wf_trmI[intro]:
  assumes "\<And>t. t \<in> set T \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m t" "length T = arity f"
  shows "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)"
using assms unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto

lemma wf_trm_subterm: "\<lbrakk>wf\<^sub>t\<^sub>r\<^sub>m t; s \<sqsubset> t\<rbrakk> \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m s"
unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by (induct t) auto

lemma wf_trm_subtermeq:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m t" "s \<sqsubseteq> t"
  shows "wf\<^sub>t\<^sub>r\<^sub>m s"
proof (cases "s = t")
  case False thus "wf\<^sub>t\<^sub>r\<^sub>m s" using assms(2) wf_trm_subterm[OF assms(1)] by simp
qed (metis assms(1))

lemma wf_trm_param:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)" "t \<in> set T"
  shows "wf\<^sub>t\<^sub>r\<^sub>m t"
by (meson assms subtermeqI'' wf_trm_subtermeq)

lemma wf_trm_param_idx:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)"
    and "i < length T"
  shows "wf\<^sub>t\<^sub>r\<^sub>m (T ! i)"
using wf_trm_param[OF assms(1), of "T ! i"] assms(2)
by fastforce

lemma wf_trm_subst:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m t = wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>)"
proof
  show "wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>)"
  proof (induction t)
    case (Fun f T)
    hence "\<And>t. t \<in> set T \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m t"
      by (meson wf\<^sub>t\<^sub>r\<^sub>m_def Fun_param_is_subterm term.order_trans)
    hence "\<And>t. t \<in> set T \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>)" using Fun.IH by auto
    moreover have "length (map (\<lambda>t. t \<cdot> \<delta>) T) = arity f"
      using Fun.prems unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
    ultimately show ?case by fastforce
  qed (simp add: wf_trm_subst_rangeD[OF assms])

  show "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m t"
  proof (induction t)
    case (Fun f T)
    hence "wf\<^sub>t\<^sub>r\<^sub>m t" when "t \<in> set (map (\<lambda>s. s \<cdot> \<delta>) T)" for t
      by (metis that wf\<^sub>t\<^sub>r\<^sub>m_def Fun_param_is_subterm term.order_trans subst_apply_term.simps(2)) 
    hence "wf\<^sub>t\<^sub>r\<^sub>m t" when "t \<in> set T" for t using that Fun.IH by auto
    moreover have "length (map (\<lambda>t. t \<cdot> \<delta>) T) = arity f"
      using Fun.prems unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
    ultimately show ?case by fastforce
  qed (simp add: assms)
qed

lemma wf_trm_subst_singleton:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m t'" shows "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> Var(v := t'))"
proof -
  have "wf\<^sub>t\<^sub>r\<^sub>m ((Var(v := t')) w)" for w using assms(2) unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by simp
  thus ?thesis using assms(1) wf_trm_subst[of "Var(v := t')" t, OF wf_trm_subst_rangeI] by simp
qed

lemma wf_trm_subst_rm_vars:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> rm_vars X \<delta>)"
using assms
proof (induction t)
  case (Fun f T)
  have "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>)" when "t \<in> set T" for t
    using that wf_trm_param[of f "map (\<lambda>t. t \<cdot> \<delta>) T"] Fun.prems
    by auto
  hence "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> rm_vars X \<delta>)" when "t \<in> set T" for t using that Fun.IH by simp
  moreover have "length T = arity f" using Fun.prems unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
  ultimately show ?case unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
qed simp

lemma wf_trm_subst_rm_vars': "wf\<^sub>t\<^sub>r\<^sub>m (\<delta> v) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m (rm_vars X \<delta> v)"
by auto

lemma wf_trms_subst:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
by (metis (no_types, lifting) assms imageE wf_trm_subst)

lemma wf_trms_subst_rm_vars:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (M \<cdot>\<^sub>s\<^sub>e\<^sub>t rm_vars X \<delta>)"
using assms wf_trm_subst_rm_vars by blast

lemma wf_trms_subst_rm_vars':
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (rm_vars X \<delta>))"
using assms by force  

lemma wf_trms_subst_compose:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<delta>))"
using assms subst_img_comp_subset' wf_trm_subst by blast 

lemma wf_trm_subst_compose:
  fixes \<delta>::"('fun, 'v) subst"
  assumes "wf\<^sub>t\<^sub>r\<^sub>m (\<theta> x)" "\<And>x. wf\<^sub>t\<^sub>r\<^sub>m (\<delta> x)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m ((\<theta> \<circ>\<^sub>s \<delta>) x)"
using wf_trm_subst[of \<delta> "\<theta> x", OF wf_trm_subst_rangeI[OF assms(2)]] assms(1)
      subst_subst_compose[of "Var x" \<theta> \<delta>]
      subst_apply_term.simps(1)[of x \<theta>]
      subst_apply_term.simps(1)[of x "\<theta> \<circ>\<^sub>s \<delta>"]
by argo

lemma wf_trms_Var_range:
  assumes "subst_range \<delta> \<subseteq> range Var"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
using assms by fastforce

lemma wf_trms_subst_compose_Var_range:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    and "subst_range \<delta> \<subseteq> range Var"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<delta> \<circ>\<^sub>s \<theta>))"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<delta>))"
using assms wf_trms_subst_compose wf_trms_Var_range by metis+

lemma wf_trm_subst_inv: "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m t"
unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by (induct t) auto

lemma wf_trms_subst_inv: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
using wf_trm_subst_inv by fast

lemma wf_trm_subterms: "wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subterms t)"
using wf_trm_subterm by blast

lemma wf_trms_subterms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subterms\<^sub>s\<^sub>e\<^sub>t M)"
using wf_trm_subterms by blast

lemma wf_trm_arity: "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T) \<Longrightarrow> length T = arity f"
unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by blast

lemma wf_trm_subterm_arity: "wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> Fun f T \<sqsubseteq> t \<Longrightarrow> length T = arity f"
unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by blast

lemma unify_list_wf_trm:
  assumes "Unification.unify E B = Some U" "\<forall>(s,t) \<in> set E. wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t"
  and "\<forall>(v,t) \<in> set B. wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "\<forall>(v,t) \<in> set U. wf\<^sub>t\<^sub>r\<^sub>m t"
using assms
proof (induction E B arbitrary: U rule: Unification.unify.induct)
  case (1 B U) thus ?case by auto
next
  case (2 f T g S E B U)
  have wf_fun: "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)" "wf\<^sub>t\<^sub>r\<^sub>m (Fun g S)" using "2.prems"(2) by auto
  from "2.prems"(1) obtain E' where *: "decompose (Fun f T) (Fun g S) = Some E'"
    and [simp]: "f = g" "length T = length S" "E' = zip T S"
    and **: "Unification.unify (E'@E) B = Some U"
    by (auto split: option.splits)
  hence "t \<sqsubset> Fun f T" "t' \<sqsubset> Fun g S" when "(t,t') \<in> set E'" for t t'
    using that by (metis zip_arg_subterm(1), metis zip_arg_subterm(2))
  hence "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m t'" when "(t,t') \<in> set E'" for t t'
    using wf_trm_subterm wf_fun \<open>f = g\<close> that by blast+
  thus ?case using "2.IH"[OF * ** _ "2.prems"(3)] "2.prems"(2) by fastforce
next
  case (3 v t E B)
  hence *: "\<forall>(w,x) \<in> set ((v, t) # B). wf\<^sub>t\<^sub>r\<^sub>m x"
      and **: "\<forall>(s,t) \<in> set E. wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m t"
    by auto

  show ?case
  proof (cases "t = Var v")
    case True thus ?thesis using "3.prems" "3.IH"(1) by auto
  next
    case False
    hence "v \<notin> fv t" using "3.prems"(1) by auto
    hence "Unification.unify (subst_list (subst v t) E) ((v, t)#B) = Some U"
      using \<open>t \<noteq> Var v\<close> "3.prems"(1) by auto
    moreover have "\<forall>(s, t) \<in> set (subst_list (subst v t) E). wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t"
      using wf_trm_subst_singleton[OF _ \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close>] "3.prems"(2)
      unfolding subst_list_def subst_def by auto
    ultimately show ?thesis using "3.IH"(2)[OF \<open>t \<noteq> Var v\<close> \<open>v \<notin> fv t\<close> _ _ *] by metis
  qed
next
  case (4 f T v E B U)
  hence *: "\<forall>(w,x) \<in> set ((v, Fun f T) # B). wf\<^sub>t\<^sub>r\<^sub>m x"
      and **: "\<forall>(s,t) \<in> set E. wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)"
    by auto

  have "v \<notin> fv (Fun f T)" using "4.prems"(1) by force
  hence "Unification.unify (subst_list (subst v (Fun f T)) E) ((v, Fun f T)#B) = Some U"
    using "4.prems"(1) by auto
  moreover have "\<forall>(s, t) \<in> set (subst_list (subst v (Fun f T)) E). wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t"
    using wf_trm_subst_singleton[OF _ \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)\<close>] "4.prems"(2)
    unfolding subst_list_def subst_def by auto
  ultimately show ?case using "4.IH"[OF \<open>v \<notin> fv (Fun f T)\<close> _ _ *] by metis
qed

lemma mgu_wf_trm:
  assumes "mgu s t = Some \<sigma>" "wf\<^sub>t\<^sub>r\<^sub>m s" "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "wf\<^sub>t\<^sub>r\<^sub>m (\<sigma> v)"
proof -
  from assms obtain \<sigma>' where "subst_of \<sigma>' = \<sigma>" "\<forall>(v,t) \<in> set \<sigma>'. wf\<^sub>t\<^sub>r\<^sub>m t"
    using unify_list_wf_trm[of "[(s,t)]" "[]"] by (auto split: option.splits)
  thus ?thesis
  proof (induction \<sigma>' arbitrary: \<sigma> v rule: List.rev_induct)
    case (snoc x \<sigma>' \<sigma> v)
    define \<theta> where "\<theta> = subst_of \<sigma>'"
    hence "wf\<^sub>t\<^sub>r\<^sub>m (\<theta> v)" for v using snoc.prems(2) snoc.IH[of \<theta>] by fastforce 
    moreover obtain w t where x: "x = (w,t)" by (metis surj_pair) 
    hence \<sigma>: "\<sigma> = Var(w := t) \<circ>\<^sub>s \<theta>" using snoc.prems(1) by (simp add: subst_def \<theta>_def)
    moreover have "wf\<^sub>t\<^sub>r\<^sub>m t" using snoc.prems(2) x by auto
    ultimately show ?case using wf_trm_subst[of _ t] unfolding subst_compose_def by auto
  qed (simp add: wf\<^sub>t\<^sub>r\<^sub>m_def)
qed

lemma mgu_wf_trms:
  assumes "mgu s t = Some \<sigma>" "wf\<^sub>t\<^sub>r\<^sub>m s" "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
using mgu_wf_trm[OF assms] by simp

subsection \<open>Definitions: Intruder Deduction Relations\<close>
text \<open>
  A standard Dolev-Yao intruder.
\<close>
inductive intruder_deduct::"('fun,'var) terms \<Rightarrow> ('fun,'var) term \<Rightarrow> bool"
where
  Axiom[simp]:   "t \<in> M \<Longrightarrow> intruder_deduct M t"
| Compose[simp]: "\<lbrakk>length T = arity f; public f; \<And>t. t \<in> set T \<Longrightarrow> intruder_deduct M t\<rbrakk>
                  \<Longrightarrow> intruder_deduct M (Fun f T)"
| Decompose:     "\<lbrakk>intruder_deduct M t; Ana t = (K, T); \<And>k. k \<in> set K \<Longrightarrow> intruder_deduct M k;
                   t\<^sub>i \<in> set T\<rbrakk>
                  \<Longrightarrow> intruder_deduct M t\<^sub>i"

text \<open>
  A variant of the intruder relation which limits the intruder to composition only.
\<close>
inductive intruder_synth::"('fun,'var) terms \<Rightarrow> ('fun,'var) term \<Rightarrow> bool"
where
  AxiomC[simp]:   "t \<in> M \<Longrightarrow> intruder_synth M t"
| ComposeC[simp]: "\<lbrakk>length T = arity f; public f; \<And>t. t \<in> set T \<Longrightarrow> intruder_synth M t\<rbrakk>
                    \<Longrightarrow> intruder_synth M (Fun f T)"

adhoc_overloading INTRUDER_DEDUCT intruder_deduct
adhoc_overloading INTRUDER_SYNTH intruder_synth

lemma intruder_deduct_induct[consumes 1, case_names Axiom Compose Decompose]:
  assumes "M \<turnstile> t" "\<And>t. t \<in> M \<Longrightarrow> P M t"
          "\<And>T f. \<lbrakk>length T = arity f; public f;
                  \<And>t. t \<in> set T \<Longrightarrow> M \<turnstile> t;
                  \<And>t. t \<in> set T \<Longrightarrow> P M t\<rbrakk> \<Longrightarrow> P M (Fun f T)"
          "\<And>t K T t\<^sub>i. \<lbrakk>M \<turnstile> t; P M t; Ana t = (K, T); \<And>k. k \<in> set K \<Longrightarrow> M \<turnstile> k;
                       \<And>k. k \<in> set K \<Longrightarrow> P M k; t\<^sub>i \<in> set T\<rbrakk> \<Longrightarrow> P M t\<^sub>i"
  shows "P M t"
using assms by (induct rule: intruder_deduct.induct) blast+

lemma intruder_synth_induct[consumes 1, case_names AxiomC ComposeC]:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  assumes "M \<turnstile>\<^sub>c t" "\<And>t. t \<in> M \<Longrightarrow> P M t"
          "\<And>T f. \<lbrakk>length T = arity f; public f;
                  \<And>t. t \<in> set T \<Longrightarrow> M \<turnstile>\<^sub>c t;
                  \<And>t. t \<in> set T \<Longrightarrow> P M t\<rbrakk> \<Longrightarrow> P M (Fun f T)"
  shows "P M t"
using assms by (induct rule: intruder_synth.induct) auto


subsection \<open>Definitions: Analyzed Knowledge and Public Ground Well-formed Terms (PGWTs)\<close>
definition analyzed::"('fun,'var) terms \<Rightarrow> bool" where
  "analyzed M \<equiv> \<forall>t. M \<turnstile> t \<longleftrightarrow> M \<turnstile>\<^sub>c t"

definition analyzed_in where
  "analyzed_in t M \<equiv> \<forall>K R. (Ana t = (K,R) \<and> (\<forall>k \<in> set K. M \<turnstile>\<^sub>c k)) \<longrightarrow> (\<forall>r \<in> set R. M \<turnstile>\<^sub>c r)"

definition decomp_closure::"('fun,'var) terms \<Rightarrow> ('fun,'var) terms \<Rightarrow> bool" where
  "decomp_closure M M' \<equiv> \<forall>t. M \<turnstile> t \<and> (\<exists>t' \<in> M. t \<sqsubseteq> t') \<longleftrightarrow> t \<in> M'"

inductive public_ground_wf_term::"('fun,'var) term \<Rightarrow> bool" where
  PGWT[simp]: "\<lbrakk>public f; arity f = length T;
                \<And>t. t \<in> set T \<Longrightarrow> public_ground_wf_term t\<rbrakk>
                  \<Longrightarrow> public_ground_wf_term (Fun f T)"

abbreviation "public_ground_wf_terms \<equiv> {t. public_ground_wf_term t}"

lemma public_const_deduct:
  assumes "c \<in> \<C>\<^sub>p\<^sub>u\<^sub>b"
  shows "M \<turnstile> Fun c []" "M \<turnstile>\<^sub>c Fun c []"
proof -
  have "arity c = 0" "public c" using const_arity_eq_zero \<open>c \<in> \<C>\<^sub>p\<^sub>u\<^sub>b\<close> by auto
  thus "M \<turnstile> Fun c []" "M \<turnstile>\<^sub>c Fun c []"
    using intruder_synth.ComposeC[OF _ \<open>public c\<close>, of "[]"]
          intruder_deduct.Compose[OF _ \<open>public c\<close>, of "[]"]
    by auto
qed

lemma public_const_deduct'[simp]:
  assumes "arity c = 0" "public c"
  shows "M \<turnstile> Fun c []" "M \<turnstile>\<^sub>c Fun c []"
using intruder_deduct.Compose[of "[]" c] intruder_synth.ComposeC[of "[]" c] assms by simp_all

lemma private_fun_deduct_in_ik:
  assumes t: "M \<turnstile> t" "Fun f T \<in> subterms t"
    and f: "\<not>public f"
  shows "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t M"
using t
proof (induction t rule: intruder_deduct.induct)
  case Decompose thus ?case by (meson Ana_subterm psubsetD term.order_trans)
qed (auto simp add: f in_subterms_Union)

lemma private_fun_deduct_in_ik':
  assumes t: "M \<turnstile> Fun f T"
    and f: "\<not>public f"
    and M: "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<Longrightarrow> Fun f T \<in> M"
  shows "Fun f T \<in> M"
by (rule M[OF private_fun_deduct_in_ik[OF t term.order_refl f]])

lemma pgwt_public: "\<lbrakk>public_ground_wf_term t; Fun f T \<sqsubseteq> t\<rbrakk> \<Longrightarrow> public f"
by (induct t rule: public_ground_wf_term.induct) auto

lemma pgwt_ground: "public_ground_wf_term t \<Longrightarrow> fv t = {}"
by (induct t rule: public_ground_wf_term.induct) auto

lemma pgwt_fun: "public_ground_wf_term t \<Longrightarrow> \<exists>f T. t = Fun f T"
using pgwt_ground[of t] by (cases t) auto

lemma pgwt_arity: "\<lbrakk>public_ground_wf_term t; Fun f T \<sqsubseteq> t\<rbrakk> \<Longrightarrow> arity f = length T"
by (induct t rule: public_ground_wf_term.induct) auto

lemma pgwt_wellformed: "public_ground_wf_term t \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m t"
by (induct t rule: public_ground_wf_term.induct) auto

lemma pgwt_deducible: "public_ground_wf_term t \<Longrightarrow> M \<turnstile>\<^sub>c t"
by (induct t rule: public_ground_wf_term.induct) auto

lemma pgwt_is_empty_synth: "public_ground_wf_term t \<longleftrightarrow> {} \<turnstile>\<^sub>c t"
proof -
  { fix M::"('fun,'var) term set" assume "M \<turnstile>\<^sub>c t" "M = {}" hence "public_ground_wf_term t"
      by (induct t rule: intruder_synth.induct) auto
  }
  thus ?thesis using pgwt_deducible by auto
qed

lemma ideduct_synth_subst_apply:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  assumes "{} \<turnstile>\<^sub>c t" "\<And>v. M \<turnstile>\<^sub>c \<theta> v"
  shows "M \<turnstile>\<^sub>c t \<cdot> \<theta>"
proof -
  { fix M'::"('fun,'var) term set" assume "M' \<turnstile>\<^sub>c t" "M' = {}" hence "M \<turnstile>\<^sub>c t \<cdot> \<theta>"
    proof (induction t rule: intruder_synth.induct)
      case (ComposeC T f M')
      hence "length (map (\<lambda>t. t \<cdot> \<theta>) T) = arity f" "\<And>x. x \<in> set (map (\<lambda>t. t \<cdot> \<theta>) T) \<Longrightarrow> M \<turnstile>\<^sub>c x"
        by auto
      thus ?case using intruder_synth.ComposeC[of "map (\<lambda>t. t \<cdot> \<theta>) T" f M] \<open>public f\<close> by fastforce
    qed simp
  }
  thus ?thesis using assms by metis
qed
  

subsection \<open>Lemmata: Monotonicity, deduction private constants, etc.\<close>
context
begin
lemma ideduct_mono:
  "\<lbrakk>M \<turnstile> t; M \<subseteq> M'\<rbrakk> \<Longrightarrow> M' \<turnstile> t"
proof (induction rule: intruder_deduct.induct)
  case (Decompose M t K T t\<^sub>i)
  have "\<forall>k. k \<in> set K \<longrightarrow> M' \<turnstile> k" using Decompose.IH \<open>M \<subseteq> M'\<close> by simp
  moreover have "M' \<turnstile> t" using Decompose.IH \<open>M \<subseteq> M'\<close> by simp
  ultimately show ?case using Decompose.hyps intruder_deduct.Decompose by blast
qed auto

lemma ideduct_synth_mono:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  shows "\<lbrakk>M \<turnstile>\<^sub>c t; M \<subseteq> M'\<rbrakk> \<Longrightarrow> M' \<turnstile>\<^sub>c t"
by (induct rule: intruder_synth.induct) auto

lemma ideduct_reduce:
  "\<lbrakk>M \<union> M' \<turnstile> t; \<And>t'. t' \<in> M' \<Longrightarrow> M \<turnstile> t'\<rbrakk> \<Longrightarrow> M \<turnstile> t"
proof (induction rule: intruder_deduct_induct)
  case Decompose thus ?case using intruder_deduct.Decompose by blast 
qed auto

lemma ideduct_synth_reduce:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  shows "\<lbrakk>M \<union> M' \<turnstile>\<^sub>c t; \<And>t'. t' \<in> M' \<Longrightarrow> M \<turnstile>\<^sub>c t'\<rbrakk> \<Longrightarrow> M \<turnstile>\<^sub>c t"
by (induct rule: intruder_synth_induct) auto

lemma ideduct_mono_eq:
  assumes "\<forall>t. M \<turnstile> t \<longleftrightarrow> M' \<turnstile> t" shows "M \<union> N \<turnstile> t \<longleftrightarrow> M' \<union> N \<turnstile> t"
proof
  show "M \<union> N \<turnstile> t \<Longrightarrow> M' \<union> N \<turnstile> t"
  proof (induction t rule: intruder_deduct_induct)
    case (Axiom t) thus ?case
    proof (cases "t \<in> M")
      case True
      hence "M \<turnstile> t" using intruder_deduct.Axiom by metis
      thus ?thesis using assms ideduct_mono[of M' t "M' \<union> N"] by simp
    qed auto
  next
    case (Compose T f) thus ?case using intruder_deduct.Compose by auto
  next
    case (Decompose t K T t\<^sub>i) thus ?case using intruder_deduct.Decompose[of "M' \<union> N" t K T] by auto
  qed

  show "M' \<union> N \<turnstile> t \<Longrightarrow> M \<union> N \<turnstile> t"
  proof (induction t rule: intruder_deduct_induct)
    case (Axiom t) thus ?case
    proof (cases "t \<in> M'")
      case True
      hence "M' \<turnstile> t" using intruder_deduct.Axiom by metis
      thus ?thesis using assms ideduct_mono[of M t "M \<union> N"] by simp
    qed auto
  next
    case (Compose T f) thus ?case using intruder_deduct.Compose by auto
  next
    case (Decompose t K T t\<^sub>i) thus ?case using intruder_deduct.Decompose[of "M \<union> N" t K T] by auto
  qed
qed

lemma deduct_synth_subterm:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  assumes "M \<turnstile>\<^sub>c t" "s \<in> subterms t" "\<forall>m \<in> M. \<forall>s \<in> subterms m. M \<turnstile>\<^sub>c s"
  shows "M \<turnstile>\<^sub>c s"
using assms by (induct t rule: intruder_synth.induct) auto

lemma deduct_if_synth[intro, dest]: "M \<turnstile>\<^sub>c t \<Longrightarrow> M \<turnstile> t"
by (induct rule: intruder_synth.induct) auto

private lemma ideduct_ik_eq: assumes "\<forall>t \<in> M. M' \<turnstile> t" shows "M' \<turnstile> t \<longleftrightarrow> M' \<union> M \<turnstile> t"
by (meson assms ideduct_mono ideduct_reduce sup_ge1)

private lemma synth_if_deduct_empty: "{} \<turnstile> t \<Longrightarrow> {} \<turnstile>\<^sub>c t"
proof (induction t rule: intruder_deduct_induct)
  case (Decompose t K M m)
  then obtain f T where "t = Fun f T" "m \<in> set T"
    using Ana_fun_subterm Ana_var by (cases t) fastforce+
  with Decompose.IH(1) show ?case by (induction rule: intruder_synth_induct) auto
qed auto

private lemma ideduct_deduct_synth_mono_eq:
  assumes "\<forall>t. M \<turnstile> t \<longleftrightarrow> M' \<turnstile>\<^sub>c t" "M \<subseteq> M'"
  and "\<forall>t. M' \<union> N \<turnstile> t \<longleftrightarrow> M' \<union> N \<union> D \<turnstile>\<^sub>c t"
  shows "M \<union> N \<turnstile> t \<longleftrightarrow> M' \<union> N \<union> D \<turnstile>\<^sub>c t"
proof -
  have "\<forall>m \<in> M'. M \<turnstile> m" using assms(1) by auto
  hence "\<forall>t. M \<turnstile> t \<longleftrightarrow> M' \<turnstile> t" by (metis assms(1,2) deduct_if_synth ideduct_reduce sup.absorb2)
  hence "\<forall>t. M' \<union> N \<turnstile> t \<longleftrightarrow> M \<union> N \<turnstile> t" by (meson ideduct_mono_eq)
  thus ?thesis by (meson assms(3))
qed

lemma ideduct_subst: "M \<turnstile> t \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<turnstile> t \<cdot> \<delta>"
proof (induction t rule: intruder_deduct_induct)
  case (Compose T f)
  hence "length (map (\<lambda>t. t \<cdot> \<delta>) T) = arity f" "\<And>t. t \<in> set T \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<turnstile> t \<cdot> \<delta>" by auto
  thus ?case using intruder_deduct.Compose[OF _ Compose.hyps(2), of "map (\<lambda>t. t \<cdot> \<delta>) T"] by auto
next
  case (Decompose t K M' m')
  hence "Ana (t \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>, M' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
        "\<And>k. k \<in> set (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>) \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<turnstile> k"
        "m' \<cdot> \<delta> \<in> set (M' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
    using Ana_subst[OF Decompose.hyps(2)] by fastforce+
  thus ?case using intruder_deduct.Decompose[OF Decompose.IH(1)] by metis
qed simp

lemma ideduct_synth_subst:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term" and \<delta>::"('fun,'var) subst"
  shows "M \<turnstile>\<^sub>c t \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<turnstile>\<^sub>c t \<cdot> \<delta>"
proof (induction t rule: intruder_synth_induct)
  case (ComposeC T f)
  hence "length (map (\<lambda>t. t \<cdot> \<delta>) T) = arity f" "\<And>t. t \<in> set T \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<turnstile>\<^sub>c t \<cdot> \<delta>" by auto
  thus ?case using intruder_synth.ComposeC[OF _ ComposeC.hyps(2), of "map (\<lambda>t. t \<cdot> \<delta>) T"] by auto
qed simp

lemma ideduct_vars:
  assumes "M \<turnstile> t"
  shows "fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
using assms 
proof (induction t rule: intruder_deduct_induct)
  case (Decompose t K T t\<^sub>i) thus ?case
    using Ana_vars(2) fv_subset by blast 
qed auto

lemma ideduct_synth_vars:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  assumes "M \<turnstile>\<^sub>c t"
  shows "fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
using assms by (induct t rule: intruder_synth_induct) auto

lemma ideduct_synth_priv_fun_in_ik:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  assumes "M \<turnstile>\<^sub>c t" "f \<in> funs_term t" "\<not>public f"
  shows "f \<in> \<Union>(funs_term ` M)"
using assms by (induct t rule: intruder_synth_induct) auto

lemma ideduct_synth_priv_const_in_ik:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  assumes "M \<turnstile>\<^sub>c Fun c []" "\<not>public c"
  shows "Fun c [] \<in> M"
using intruder_synth.cases[OF assms(1)] assms(2) by fast

lemma ideduct_synth_ik_replace:
  fixes M::"('fun,'var) terms" and t::"('fun,'var) term"
  assumes "\<forall>t \<in> M. N \<turnstile>\<^sub>c t"
    and "M \<turnstile>\<^sub>c t"
  shows "N \<turnstile>\<^sub>c t"
using assms(2,1) by (induct t rule: intruder_synth.induct) auto
end

subsection \<open>Lemmata: Analyzed Intruder Knowledge Closure\<close>
lemma deducts_eq_if_analyzed: "analyzed M \<Longrightarrow> M \<turnstile> t \<longleftrightarrow> M \<turnstile>\<^sub>c t"
unfolding analyzed_def by auto

lemma closure_is_superset: "decomp_closure M M' \<Longrightarrow> M \<subseteq> M'"
unfolding decomp_closure_def by force

lemma deduct_if_closure_deduct: "\<lbrakk>M' \<turnstile> t; decomp_closure M M'\<rbrakk> \<Longrightarrow> M \<turnstile> t"
proof (induction t rule: intruder_deduct.induct)
  case (Decompose M' t K T t\<^sub>i)
  thus ?case using intruder_deduct.Decompose[OF _ \<open>Ana t = (K,T)\<close> _ \<open>t\<^sub>i \<in> set T\<close>] by simp
qed (auto simp add: decomp_closure_def)

lemma deduct_if_closure_synth: "\<lbrakk>decomp_closure M M'; M' \<turnstile>\<^sub>c t\<rbrakk> \<Longrightarrow> M \<turnstile> t"
using deduct_if_closure_deduct by blast

lemma decomp_closure_subterms_composable:
  assumes "decomp_closure M M'"
  and "M' \<turnstile>\<^sub>c t'" "M' \<turnstile> t" "t \<sqsubseteq> t'"
  shows "M' \<turnstile>\<^sub>c t"
using \<open>M' \<turnstile>\<^sub>c t'\<close> assms
proof (induction t' rule: intruder_synth.induct)
  case (AxiomC t' M')
  have "M \<turnstile> t" using \<open>M' \<turnstile> t\<close> deduct_if_closure_deduct AxiomC.prems(1) by blast
  moreover
  { have "\<exists>s \<in> M. t' \<sqsubseteq> s" using \<open>t' \<in> M'\<close> AxiomC.prems(1) unfolding decomp_closure_def by blast
    hence "\<exists>s \<in> M. t \<sqsubseteq> s" using \<open>t \<sqsubseteq> t'\<close> term.order_trans by auto
  }
  ultimately have "t \<in> M'" using AxiomC.prems(1) unfolding decomp_closure_def by blast
  thus ?case by simp
next
  case (ComposeC T f M')
  let ?t' = "Fun f T"
  { assume "t = ?t'" have "M' \<turnstile>\<^sub>c t" using \<open>M' \<turnstile>\<^sub>c ?t'\<close> \<open>t = ?t'\<close> by simp }
  moreover
  { assume "t \<noteq> ?t'"
    have "\<exists>x \<in> set T. t \<sqsubseteq> x" using \<open>t \<sqsubseteq> ?t'\<close> \<open>t \<noteq> ?t'\<close> by simp
    hence "M' \<turnstile>\<^sub>c t" using ComposeC.IH ComposeC.prems(1,3) ComposeC.hyps(3) by blast
  }
  ultimately show ?case using cases_simp[of "t = ?t'" "M' \<turnstile>\<^sub>c t"] by simp
qed

lemma decomp_closure_analyzed:
  assumes "decomp_closure M M'"
  shows "analyzed M'"
proof -
  { fix t assume "M' \<turnstile> t" have "M' \<turnstile>\<^sub>c t" using \<open>M' \<turnstile> t\<close> assms
    proof (induction t rule: intruder_deduct.induct)
      case (Decompose M' t K T t\<^sub>i) 
      hence "M' \<turnstile> t\<^sub>i" using Decompose.hyps intruder_deduct.Decompose by blast
      moreover have "t\<^sub>i \<sqsubseteq> t"
        using Decompose.hyps(4) Ana_subterm[OF Decompose.hyps(2)] by blast
      moreover have "M' \<turnstile>\<^sub>c t" using Decompose.IH(1) Decompose.prems by blast
      ultimately show "M' \<turnstile>\<^sub>c t\<^sub>i" using decomp_closure_subterms_composable Decompose.prems by blast
    qed auto
  }
  moreover have "\<forall>t. M \<turnstile>\<^sub>c t \<longrightarrow> M \<turnstile> t" by auto
  ultimately show ?thesis by (auto simp add: decomp_closure_def analyzed_def)
qed

lemma analyzed_if_all_analyzed_in:
  assumes M: "\<forall>t \<in> M. analyzed_in t M"
  shows "analyzed M"
proof (unfold analyzed_def, intro allI iffI)
  fix t
  assume t: "M \<turnstile> t"
  thus "M \<turnstile>\<^sub>c t"
  proof (induction t rule: intruder_deduct_induct)
    case (Decompose t K T t\<^sub>i)
    { assume "t \<in> M"
      hence ?case
        using M Decompose.IH(2) Decompose.hyps(2,4)
        unfolding analyzed_in_def by fastforce
    } moreover {
      fix f S assume "t = Fun f S" "\<And>s. s \<in> set S \<Longrightarrow> M \<turnstile>\<^sub>c s"
      hence ?case using Ana_fun_subterm[of f S] Decompose.hyps(2,4) by blast
    } ultimately show ?case using intruder_synth.cases[OF Decompose.IH(1), of ?case] by blast
  qed simp_all
qed auto

lemma analyzed_is_all_analyzed_in:
  "(\<forall>t \<in> M. analyzed_in t M) \<longleftrightarrow> analyzed M"
proof
  show "analyzed M \<Longrightarrow> \<forall>t \<in> M. analyzed_in t M"
    unfolding analyzed_in_def analyzed_def
    by (auto intro: intruder_deduct.Decompose[OF intruder_deduct.Axiom])
qed (rule analyzed_if_all_analyzed_in)

lemma ik_has_synth_ik_closure:
  fixes M :: "('fun,'var) terms"
  shows "\<exists>M'. (\<forall>t. M \<turnstile> t \<longleftrightarrow> M' \<turnstile>\<^sub>c t) \<and> decomp_closure M M' \<and> (finite M \<longrightarrow> finite M')"
proof -
  let ?M' = "{t. M \<turnstile> t \<and> (\<exists>t' \<in> M. t \<sqsubseteq> t')}"

  have M'_closes: "decomp_closure M ?M'" unfolding decomp_closure_def by simp
  hence "M \<subseteq> ?M'" using closure_is_superset by simp

  have "\<forall>t. ?M' \<turnstile>\<^sub>c t \<longrightarrow> M \<turnstile> t" using deduct_if_closure_synth[OF M'_closes] by blast 
  moreover have "\<forall>t. M \<turnstile> t \<longrightarrow> ?M' \<turnstile> t" using ideduct_mono[OF _ \<open>M \<subseteq> ?M'\<close>] by simp
  moreover have "analyzed ?M'" using decomp_closure_analyzed[OF M'_closes] .
  ultimately have "\<forall>t. M \<turnstile> t \<longleftrightarrow> ?M' \<turnstile>\<^sub>c t" unfolding analyzed_def by blast
  moreover have "finite M \<longrightarrow> finite ?M'" by auto
  ultimately show ?thesis using M'_closes by blast
qed


subsection \<open>Intruder Variants: Numbered and Composition-Restricted Intruder Deduction Relations\<close>
text \<open>
  A variant of the intruder relation which restricts composition to only those terms that satisfy
  a given predicate Q.
\<close>
inductive intruder_deduct_restricted::
  "('fun,'var) terms \<Rightarrow> (('fun,'var) term \<Rightarrow> bool) \<Rightarrow> ('fun,'var) term \<Rightarrow> bool"
  ("\<langle>_;_\<rangle> \<turnstile>\<^sub>r _" 50)
where
  AxiomR[simp]:   "t \<in> M \<Longrightarrow> \<langle>M; Q\<rangle> \<turnstile>\<^sub>r t"
| ComposeR[simp]: "\<lbrakk>length T = arity f; public f; \<And>t. t \<in> set T \<Longrightarrow> \<langle>M; Q\<rangle> \<turnstile>\<^sub>r t; Q (Fun f T)\<rbrakk>
                    \<Longrightarrow> \<langle>M; Q\<rangle> \<turnstile>\<^sub>r Fun f T"
| DecomposeR:     "\<lbrakk>\<langle>M; Q\<rangle> \<turnstile>\<^sub>r t; Ana t = (K, T); \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; Q\<rangle> \<turnstile>\<^sub>r k; t\<^sub>i \<in> set T\<rbrakk>
                    \<Longrightarrow> \<langle>M; Q\<rangle> \<turnstile>\<^sub>r t\<^sub>i"

text \<open>
  A variant of the intruder relation equipped with a number representing the heigth of the
  derivation tree (i.e., \<open>\<langle>M; k\<rangle> \<turnstile>\<^sub>n t\<close> iff k is the maximum number of applications of the compose
  an decompose rules in any path of the derivation tree for \<open>M \<turnstile> t\<close>).
\<close>
inductive intruder_deduct_num::
  "('fun,'var) terms \<Rightarrow> nat \<Rightarrow> ('fun,'var) term \<Rightarrow> bool"
  ("\<langle>_; _\<rangle> \<turnstile>\<^sub>n _" 50)
where
  AxiomN[simp]:   "t \<in> M \<Longrightarrow> \<langle>M; 0\<rangle> \<turnstile>\<^sub>n t"
| ComposeN[simp]: "\<lbrakk>length T = arity f; public f; \<And>t. t \<in> set T \<Longrightarrow> \<langle>M; steps t\<rangle> \<turnstile>\<^sub>n t\<rbrakk>
                    \<Longrightarrow> \<langle>M; Suc (Max (insert 0 (steps ` set T)))\<rangle> \<turnstile>\<^sub>n Fun f T"
| DecomposeN:     "\<lbrakk>\<langle>M; n\<rangle> \<turnstile>\<^sub>n t; Ana t = (K, T); \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; steps k\<rangle> \<turnstile>\<^sub>n k; t\<^sub>i \<in> set T\<rbrakk>
                    \<Longrightarrow> \<langle>M; Suc (Max (insert n (steps ` set K)))\<rangle> \<turnstile>\<^sub>n t\<^sub>i"

lemma intruder_deduct_restricted_induct[consumes 1, case_names AxiomR ComposeR DecomposeR]:
  assumes "\<langle>M; Q\<rangle> \<turnstile>\<^sub>r t" "\<And>t. t \<in> M \<Longrightarrow> P M Q t"
          "\<And>T f. \<lbrakk>length T = arity f; public f;
                  \<And>t. t \<in> set T \<Longrightarrow> \<langle>M; Q\<rangle> \<turnstile>\<^sub>r t;
                  \<And>t. t \<in> set T \<Longrightarrow> P M Q t; Q (Fun f T)
                  \<rbrakk> \<Longrightarrow> P M Q (Fun f T)"
          "\<And>t K T t\<^sub>i. \<lbrakk>\<langle>M; Q\<rangle> \<turnstile>\<^sub>r t; P M Q t; Ana t = (K, T); \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; Q\<rangle> \<turnstile>\<^sub>r k;
                       \<And>k. k \<in> set K \<Longrightarrow> P M Q k; t\<^sub>i \<in> set T\<rbrakk> \<Longrightarrow> P M Q t\<^sub>i"
  shows "P M Q t"
using assms by (induct t rule: intruder_deduct_restricted.induct) blast+

lemma intruder_deduct_num_induct[consumes 1, case_names AxiomN ComposeN DecomposeN]:
  assumes "\<langle>M; n\<rangle> \<turnstile>\<^sub>n t" "\<And>t. t \<in> M \<Longrightarrow> P M 0 t"
          "\<And>T f steps.
              \<lbrakk>length T = arity f; public f;
               \<And>t. t \<in> set T \<Longrightarrow> \<langle>M; steps t\<rangle> \<turnstile>\<^sub>n t;
               \<And>t. t \<in> set T \<Longrightarrow> P M (steps t) t\<rbrakk>
              \<Longrightarrow> P M (Suc (Max (insert 0 (steps ` set T)))) (Fun f T)"
          "\<And>t K T t\<^sub>i steps n.
              \<lbrakk>\<langle>M; n\<rangle> \<turnstile>\<^sub>n t; P M n t; Ana t = (K, T);
               \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; steps k\<rangle> \<turnstile>\<^sub>n k;
               t\<^sub>i \<in> set T; \<And>k. k \<in> set K \<Longrightarrow> P M (steps k) k\<rbrakk>
              \<Longrightarrow> P M (Suc (Max (insert n (steps ` set K)))) t\<^sub>i"
  shows "P M n t"
using assms by (induct rule: intruder_deduct_num.induct) blast+

lemma ideduct_restricted_mono:
  "\<lbrakk>\<langle>M; P\<rangle> \<turnstile>\<^sub>r t; M \<subseteq> M'\<rbrakk> \<Longrightarrow> \<langle>M'; P\<rangle> \<turnstile>\<^sub>r t"
proof (induction rule: intruder_deduct_restricted_induct)
  case (DecomposeR t K T t\<^sub>i)
  have "\<forall>k. k \<in> set K \<longrightarrow> \<langle>M'; P\<rangle> \<turnstile>\<^sub>r k" using DecomposeR.IH \<open>M \<subseteq> M'\<close> by simp
  moreover have "\<langle>M'; P\<rangle> \<turnstile>\<^sub>r t" using DecomposeR.IH \<open>M \<subseteq> M'\<close> by simp
  ultimately show ?case
    using DecomposeR
          intruder_deduct_restricted.DecomposeR[OF _ DecomposeR.hyps(2) _ DecomposeR.hyps(4)]
    by blast
qed auto


subsection \<open>Lemmata: Intruder Deduction Equivalences\<close>
lemma deduct_if_restricted_deduct: "\<langle>M;P\<rangle> \<turnstile>\<^sub>r m \<Longrightarrow> M \<turnstile> m"
proof (induction m rule: intruder_deduct_restricted_induct)
  case (DecomposeR t K T t\<^sub>i) thus ?case using intruder_deduct.Decompose by blast
qed simp_all

lemma restricted_deduct_if_restricted_ik:
  assumes "\<langle>M;P\<rangle> \<turnstile>\<^sub>r m" "\<forall>m \<in> M. P m"
  and P: "\<forall>t t'. P t \<longrightarrow> t' \<sqsubseteq> t \<longrightarrow> P t'"
  shows "P m"
using assms(1)
proof (induction m rule: intruder_deduct_restricted_induct)
  case (DecomposeR t K T t\<^sub>i)
  obtain f S where "t = Fun f S" using Ana_var \<open>t\<^sub>i \<in> set T\<close> \<open>Ana t = (K, T)\<close> by (cases t) auto
  thus ?case using DecomposeR assms(2) P Ana_subterm by blast
qed (simp_all add: assms(2))

lemma deduct_restricted_if_synth:
  assumes P: "P m" "\<forall>t t'. P t \<longrightarrow> t' \<sqsubseteq> t \<longrightarrow> P t'"
  and m: "M \<turnstile>\<^sub>c m"
  shows "\<langle>M; P\<rangle> \<turnstile>\<^sub>r m"
using m P(1)
proof (induction m rule: intruder_synth_induct)
  case (ComposeC T f)
  hence "\<langle>M; P\<rangle> \<turnstile>\<^sub>r t" when t: "t \<in> set T" for t
    using t P(2) subtermeqI''[of _ T f]
    by fastforce
  thus ?case
    using intruder_deduct_restricted.ComposeR[OF ComposeC.hyps(1,2)] ComposeC.prems(1)
    by metis
qed simp

lemma deduct_zero_in_ik:
  assumes "\<langle>M; 0\<rangle> \<turnstile>\<^sub>n t" shows "t \<in> M"
proof -
  { fix k assume "\<langle>M; k\<rangle> \<turnstile>\<^sub>n t" hence "k > 0 \<or> t \<in> M" by (induct t) auto
  } thus ?thesis using assms by auto
qed

lemma deduct_if_deduct_num: "\<langle>M; k\<rangle> \<turnstile>\<^sub>n t \<Longrightarrow> M \<turnstile> t"
by (induct t rule: intruder_deduct_num.induct)
   (metis intruder_deduct.Axiom,
    metis intruder_deduct.Compose,
    metis intruder_deduct.Decompose)

lemma deduct_num_if_deduct: "M \<turnstile> t \<Longrightarrow> \<exists>k. \<langle>M; k\<rangle> \<turnstile>\<^sub>n t"
proof (induction t rule: intruder_deduct_induct)
  case (Compose T f)
  then obtain steps where *: "\<forall>t \<in> set T. \<langle>M; steps t\<rangle> \<turnstile>\<^sub>n t" by moura
  then obtain n where "\<forall>t \<in> set T. steps t \<le> n"
    using finite_nat_set_iff_bounded_le[of "steps ` set T"]
    by auto
  thus ?case using ComposeN[OF Compose.hyps(1,2), of M steps] * by force
next
  case (Decompose t K T t\<^sub>i)
  hence "\<And>u. u \<in> insert t (set K) \<Longrightarrow> \<exists>k. \<langle>M; k\<rangle> \<turnstile>\<^sub>n u" by auto
  then obtain steps where *: "\<langle>M; steps t\<rangle> \<turnstile>\<^sub>n t" "\<forall>t \<in> set K. \<langle>M; steps t\<rangle> \<turnstile>\<^sub>n t" by moura
  then obtain n where "steps t \<le> n" "\<forall>t \<in> set K. steps t \<le> n"
    using finite_nat_set_iff_bounded_le[of "steps ` insert t (set K)"]
    by auto
  thus ?case using DecomposeN[OF _ Decompose.hyps(2) _ Decompose.hyps(4), of M _ steps] * by force
qed (metis AxiomN)

lemma deduct_normalize:
  assumes M: "\<forall>m \<in> M. \<forall>f T. Fun f T \<sqsubseteq> m \<longrightarrow> P f T"
  and t: "\<langle>M; k\<rangle> \<turnstile>\<^sub>n t" "Fun f T \<sqsubseteq> t" "\<not>P f T"
  shows "\<exists>l \<le> k. (\<langle>M; l\<rangle> \<turnstile>\<^sub>n Fun f T) \<and> (\<forall>t \<in> set T. \<exists>j < l. \<langle>M; j\<rangle> \<turnstile>\<^sub>n t)"
using t
proof (induction t rule: intruder_deduct_num_induct)
  case (AxiomN t) thus ?case using M by auto
next
  case (ComposeN T' f' steps) thus ?case
  proof (cases "Fun f' T' = Fun f T")
    case True
    hence "\<langle>M; Suc (Max (insert 0 (steps ` set T')))\<rangle> \<turnstile>\<^sub>n Fun f T" "T = T'"
      using intruder_deduct_num.ComposeN[OF ComposeN.hyps] by auto
    moreover have "\<And>t. t \<in> set T \<Longrightarrow> \<langle>M; steps t\<rangle> \<turnstile>\<^sub>n t"
      using True ComposeN.hyps(3) by auto
    moreover have "\<And>t. t \<in> set T \<Longrightarrow> steps t < Suc (Max (insert 0 (steps ` set T)))"
      using Max_less_iff[of "insert 0 (steps ` set T)" "Suc (Max (insert 0 (steps ` set T)))"]
      by auto
    ultimately show ?thesis by auto
  next
    case False
    then obtain t' where t': "t' \<in> set T'" "Fun f T \<sqsubseteq> t'" using ComposeN by auto
    hence "\<exists>l \<le> steps t'. (\<langle>M; l\<rangle> \<turnstile>\<^sub>n Fun f T) \<and> (\<forall>t \<in> set T. \<exists>j < l. \<langle>M; j\<rangle> \<turnstile>\<^sub>n t)"
      using ComposeN.IH[OF _ _ ComposeN.prems(2)] by auto
    moreover have "steps t' < Suc (Max (insert 0 (steps ` set T')))"
      using Max_less_iff[of "insert 0 (steps ` set T')" "Suc (Max (insert 0 (steps ` set T')))"]
      using t'(1) by auto
    ultimately show ?thesis using ComposeN.hyps(3)[OF t'(1)]
      by (meson Suc_le_eq le_Suc_eq le_trans)
  qed
next
  case (DecomposeN t K T' t\<^sub>i steps n)
  hence *: "Fun f T \<sqsubseteq> t"
    using term.order_trans[of "Fun f T" t\<^sub>i t] Ana_subterm[of t K T']
    by blast
  have "\<exists>l \<le> n. (\<langle>M; l\<rangle> \<turnstile>\<^sub>n Fun f T) \<and> (\<forall>t' \<in> set T. \<exists>j < l. \<langle>M; j\<rangle> \<turnstile>\<^sub>n t')"
    using DecomposeN.IH(1)[OF * DecomposeN.prems(2)] by auto
  moreover have "n < Suc (Max (insert n (steps ` set K)))"
      using Max_less_iff[of "insert n (steps ` set K)" "Suc (Max (insert n (steps ` set K)))"]
      by auto
  ultimately show ?case using DecomposeN.hyps(4) by (meson Suc_le_eq le_Suc_eq le_trans)
qed

lemma deduct_inv:
  assumes "\<langle>M; n\<rangle> \<turnstile>\<^sub>n t"
  shows "t \<in> M \<or>
         (\<exists>f T. t = Fun f T \<and> public f \<and> length T = arity f \<and> (\<forall>t \<in> set T. \<exists>l < n. \<langle>M; l\<rangle> \<turnstile>\<^sub>n t)) \<or>
         (\<exists>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t M.
            (\<exists>l < n. \<langle>M; l\<rangle> \<turnstile>\<^sub>n m) \<and> (\<forall>k \<in> set (fst (Ana m)). \<exists>l < n. \<langle>M; l\<rangle> \<turnstile>\<^sub>n k) \<and>
            t \<in> set (snd (Ana m)))"
    (is "?P t n \<or> ?Q t n \<or> ?R t n")
using assms
proof (induction n arbitrary: t rule: nat_less_induct)
  case (1 n t) thus ?case
  proof (cases n)
    case 0
    hence "t \<in> M" using deduct_zero_in_ik "1.prems"(1) by metis
    thus ?thesis by auto
  next
    case (Suc n')
    hence "\<langle>M; Suc n'\<rangle> \<turnstile>\<^sub>n t"
          "\<forall>m < Suc n'. \<forall>x. (\<langle>M; m\<rangle> \<turnstile>\<^sub>n x) \<longrightarrow> ?P x m \<or> ?Q x m \<or> ?R x m"
      using "1.prems" "1.IH" by blast+
    hence "?P t (Suc n') \<or> ?Q t (Suc n') \<or> ?R t (Suc n')"
    proof (induction t rule: intruder_deduct_num_induct)
      case (AxiomN t) thus ?case by simp
    next
      case (ComposeN T f steps)
      have "\<And>t. t \<in> set T \<Longrightarrow> steps t < Suc (Max (insert 0 (steps ` set T)))"
          using Max_less_iff[of "insert 0 (steps ` set T)" "Suc (Max (insert 0 (steps ` set T)))"]
          by auto
      thus ?case using ComposeN.hyps by metis
    next
      case (DecomposeN t K T t\<^sub>i steps n)
      have 0: "n < Suc (Max (insert n (steps ` set K)))"
              "\<And>k. k \<in> set K \<Longrightarrow> steps k < Suc (Max (insert n (steps ` set K)))"
        using Max_less_iff[of "insert n (steps ` set K)" "Suc (Max (insert n (steps ` set K)))"]
        by auto

      have IH1: "?P t j \<or> ?Q t j \<or> ?R t j" when jt: "j < n" "\<langle>M; j\<rangle> \<turnstile>\<^sub>n t" for j t
        using jt DecomposeN.prems(1) 0(1)
        by simp

      have IH2: "?P t n \<or> ?Q t n \<or> ?R t n"
        using DecomposeN.IH(1) IH1
        by simp

      have 1: "\<forall>k \<in> set (fst (Ana t)). \<exists>l < Suc (Max (insert n (steps ` set K))). \<langle>M; l\<rangle> \<turnstile>\<^sub>n k"
        using DecomposeN.hyps(1,2,3) 0(2)
        by auto
    
      have 2: "t\<^sub>i \<in> set (snd (Ana t))"
        using DecomposeN.hyps(2,4)
        by fastforce
    
      have 3: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M" when "t \<in> set (snd (Ana m))" "m \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t M" for m
        using that(1) Ana_subterm[of m _ "snd (Ana m)"] in_subterms_subset_Union[OF that(2)]
        by (metis (no_types, lifting) prod.collapse psubsetD subsetCE subsetD) 
    
      have 4: "?R t\<^sub>i (Suc (Max (insert n (steps ` set K))))" when "?R t n"
        using that 0(1) 1 2 3 DecomposeN.hyps(1)
        by (metis (no_types, lifting)) 
    
      have 5: "?R t\<^sub>i (Suc (Max (insert n (steps ` set K))))" when "?P t n"
        using that 0(1) 1 2 DecomposeN.hyps(1)
        by blast
    
      have 6: ?case when *: "?Q t n"
      proof -
        obtain g S where g:
            "t = Fun g S" "public g" "length S = arity g" "\<forall>t \<in> set S. \<exists>l < n. \<langle>M; l\<rangle> \<turnstile>\<^sub>n t"
          using * by moura
        then obtain l where l: "l < n" "\<langle>M; l\<rangle> \<turnstile>\<^sub>n t\<^sub>i"
          using 0(1) DecomposeN.hyps(2,4) Ana_fun_subterm[of g S K T] by blast
    
        have **: "l < Suc (Max (insert n (steps ` set K)))" using l(1) 0(1) by simp
    
        show ?thesis using IH1[OF l] less_trans[OF _ **] by fastforce
      qed

      show ?case using IH2 4 5 6 by argo
    qed
    thus ?thesis using Suc by fast
  qed
qed

lemma restricted_deduct_if_deduct:
  assumes M: "\<forall>m \<in> M. \<forall>f T. Fun f T \<sqsubseteq> m \<longrightarrow> P (Fun f T)"
  and P_subterm: "\<forall>f T t. M \<turnstile> Fun f T \<longrightarrow> P (Fun f T) \<longrightarrow> t \<in> set T \<longrightarrow> P t"
  and P_Ana_key: "\<forall>t K T k. M \<turnstile> t \<longrightarrow> P t \<longrightarrow> Ana t = (K, T) \<longrightarrow> M \<turnstile> k \<longrightarrow> k \<in> set K \<longrightarrow> P k"
  and m: "M \<turnstile> m" "P m"
  shows "\<langle>M; P\<rangle> \<turnstile>\<^sub>r m"
proof -
  { fix k assume "\<langle>M; k\<rangle> \<turnstile>\<^sub>n m"
    hence ?thesis using m(2)
    proof (induction k arbitrary: m rule: nat_less_induct)
      case (1 n m) thus ?case
      proof (cases n)
        case 0
        hence "m \<in> M" using deduct_zero_in_ik "1.prems"(1) by metis
        thus ?thesis by auto
      next
        case (Suc n')
        hence "\<langle>M; Suc n'\<rangle> \<turnstile>\<^sub>n m"
              "\<forall>m < Suc n'. \<forall>x. (\<langle>M; m\<rangle> \<turnstile>\<^sub>n x) \<longrightarrow> P x \<longrightarrow> \<langle>M;P\<rangle> \<turnstile>\<^sub>r x"
          using "1.prems" "1.IH" by blast+
        thus ?thesis using "1.prems"(2)
        proof (induction m rule: intruder_deduct_num_induct)
          case (ComposeN T f steps)
          have *: "steps t < Suc (Max (insert 0 (steps ` set T)))" when "t \<in> set T" for t
            using Max_less_iff[of "insert 0 (steps ` set T)"] that
            by blast

          have **: "P t" when "t \<in> set T" for t
            using P_subterm ComposeN.prems(2) that
                  Fun_param_is_subterm[OF that]
                  intruder_deduct.Compose[OF ComposeN.hyps(1,2)]
                  deduct_if_deduct_num[OF ComposeN.hyps(3)]
            by blast

          have "\<langle>M; P\<rangle> \<turnstile>\<^sub>r t" when "t \<in> set T" for t
            using ComposeN.prems(1) ComposeN.hyps(3)[OF that] *[OF that] **[OF that]
            by blast
          thus ?case
            by (metis intruder_deduct_restricted.ComposeR[OF ComposeN.hyps(1,2)] ComposeN.prems(2))
        next
          case (DecomposeN t K T t\<^sub>i steps l)
          show ?case
          proof (cases "P t")
            case True
            hence "\<And>k. k \<in> set K \<Longrightarrow> P k"
              using P_Ana_key DecomposeN.hyps(1,2,3) deduct_if_deduct_num
              by blast
            moreover have
                "\<And>k m x. k \<in> set K \<Longrightarrow> m < steps k \<Longrightarrow> \<langle>M; m\<rangle> \<turnstile>\<^sub>n x \<Longrightarrow> P x \<Longrightarrow> \<langle>M;P\<rangle> \<turnstile>\<^sub>r x"
            proof -
              fix k m x assume *: "k \<in> set K" "m < steps k" "\<langle>M; m\<rangle> \<turnstile>\<^sub>n x" "P x"
              have "steps k \<in> insert l (steps ` set K)" using *(1) by simp
              hence "m < Suc (Max (insert l (steps ` set K)))"
                using less_trans[OF *(2), of "Suc (Max (insert l (steps ` set K)))"]
                      Max_less_iff[of "insert l (steps ` set K)"
                                      "Suc (Max (insert l (steps ` set K)))"]
                by auto
              thus "\<langle>M;P\<rangle> \<turnstile>\<^sub>r x" using DecomposeN.prems(1) *(3,4) by simp
            qed
            ultimately have "\<And>k. k \<in> set K \<Longrightarrow> \<langle>M; P\<rangle> \<turnstile>\<^sub>r k"
              using DecomposeN.IH(2) by auto
            moreover have "\<langle>M; P\<rangle> \<turnstile>\<^sub>r t"
              using True DecomposeN.prems(1) DecomposeN.hyps(1) le_imp_less_Suc
                    Max_less_iff[of "insert l (steps ` set K)" "Suc (Max (insert l (steps ` set K)))"]
              by blast
            ultimately show ?thesis
              using intruder_deduct_restricted.DecomposeR[OF _ DecomposeN.hyps(2)
                                                             _ DecomposeN.hyps(4)]
              by metis
          next
            case False
            obtain g S where gS: "t = Fun g S" using DecomposeN.hyps(2,4) by (cases t) moura+
            hence *: "Fun g S \<sqsubseteq> t" "\<not>P (Fun g S)" using False by force+
            have "\<exists>j<l. \<langle>M; j\<rangle> \<turnstile>\<^sub>n t\<^sub>i"
              using gS DecomposeN.hyps(2,4) Ana_fun_subterm[of g S K T]
                    deduct_normalize[of M "\<lambda>f T. P (Fun f T)", OF M DecomposeN.hyps(1) *]
              by force
            hence "\<exists>j<Suc (Max (insert l (steps ` set K))). \<langle>M; j\<rangle> \<turnstile>\<^sub>n t\<^sub>i"
              using Max_less_iff[of "insert l (steps ` set K)"
                                    "Suc (Max (insert l (steps ` set K)))"]
                    less_trans[of _ l "Suc (Max (insert l (steps ` set K)))"]
              by blast
            thus ?thesis using DecomposeN.prems(1,2) by meson
          qed
        qed auto
      qed
    qed
  } thus ?thesis using deduct_num_if_deduct m(1) by metis
qed

lemma restricted_deduct_if_deduct':
  assumes "\<forall>m \<in> M. P m"
    and "\<forall>t t'. P t \<longrightarrow> t' \<sqsubseteq> t \<longrightarrow> P t'"
    and "\<forall>t K T k. P t \<longrightarrow> Ana t = (K, T) \<longrightarrow> k \<in> set K \<longrightarrow> P k"
    and "M \<turnstile> m" "P m"
  shows "\<langle>M; P\<rangle> \<turnstile>\<^sub>r m"
using restricted_deduct_if_deduct[of M P m] assms
by blast

lemma private_const_deduct:
  assumes c: "\<not>public c" "M \<turnstile> (Fun c []::('fun,'var) term)"
  shows "Fun c [] \<in> M \<or>
         (\<exists>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. M \<turnstile> m \<and> (\<forall>k \<in> set (fst (Ana m)). M \<turnstile> m) \<and>
                             Fun c [] \<in> set (snd (Ana m)))"
proof -
  obtain n where "\<langle>M; n\<rangle> \<turnstile>\<^sub>n Fun c []"
    using c(2) deduct_num_if_deduct by moura
  hence "Fun c [] \<in> M \<or>
         (\<exists>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t M.
            (\<exists>l < n. \<langle>M; l\<rangle> \<turnstile>\<^sub>n m) \<and>
            (\<forall>k \<in> set (fst (Ana m)). \<exists>l < n. \<langle>M; l\<rangle> \<turnstile>\<^sub>n k) \<and> Fun c [] \<in> set (snd (Ana m)))"
    using deduct_inv[of M n "Fun c []"] c(1) by fast
  thus ?thesis using deduct_if_deduct_num[of M] by blast
qed

lemma private_fun_deduct_in_ik'':
  assumes t: "M \<turnstile> Fun f T" "Fun c [] \<in> set T" "\<forall>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. Fun f T \<notin> set (snd (Ana m))"
    and c: "\<not>public c" "Fun c [] \<notin> M" "\<forall>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. Fun c [] \<notin> set (snd (Ana m))"
  shows "Fun f T \<in> M"
proof -
  have *: "\<nexists>n. \<langle>M; n\<rangle> \<turnstile>\<^sub>n Fun c []"
    using private_const_deduct[OF c(1)] c(2,3) deduct_if_deduct_num
    by blast

  obtain n where n: "\<langle>M; n\<rangle> \<turnstile>\<^sub>n Fun f T"
    using t(1) deduct_num_if_deduct
    by blast

  show ?thesis
    using deduct_inv[OF n] t(2,3) *
    by blast
qed

end

subsection \<open>Executable Definitions for Code Generation\<close>
fun intruder_synth' where
  "intruder_synth' pu ar M (Var x) = (Var x \<in> M)"
| "intruder_synth' pu ar M (Fun f T) = (
    Fun f T \<in> M \<or> (pu f \<and> length T = ar f \<and> list_all (intruder_synth' pu ar M) T))"

definition "wf\<^sub>t\<^sub>r\<^sub>m' ar t \<equiv> (\<forall>s \<in> subterms t. is_Fun s \<longrightarrow> ar (the_Fun s) = length (args s))"

definition "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' ar M \<equiv> (\<forall>t \<in> M. wf\<^sub>t\<^sub>r\<^sub>m' ar t)"

definition "analyzed_in' An pu ar t M \<equiv> (case An t of
    (K,T) \<Rightarrow> (\<forall>k \<in> set K. intruder_synth' pu ar M k) \<longrightarrow> (\<forall>s \<in> set T. intruder_synth' pu ar M s))"

lemma (in intruder_model) intruder_synth'_induct[consumes 1, case_names Var Fun]:
  assumes "intruder_synth' public arity M t"
          "\<And>x. intruder_synth' public arity M (Var x) \<Longrightarrow> P (Var x)"
          "\<And>f T. (\<And>z. z \<in> set T \<Longrightarrow> intruder_synth' public arity M z \<Longrightarrow> P z) \<Longrightarrow>
                  intruder_synth' public arity M (Fun f T) \<Longrightarrow> P (Fun f T) "
  shows "P t"
using assms by (induct public arity M t rule: intruder_synth'.induct) auto

lemma (in intruder_model) wf\<^sub>t\<^sub>r\<^sub>m_code[code_unfold]:
  "wf\<^sub>t\<^sub>r\<^sub>m t = wf\<^sub>t\<^sub>r\<^sub>m' arity t"
unfolding wf\<^sub>t\<^sub>r\<^sub>m_def wf\<^sub>t\<^sub>r\<^sub>m'_def
by auto

lemma (in intruder_model) wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[code_unfold]:
  "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M = wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity M"
using wf\<^sub>t\<^sub>r\<^sub>m_code
unfolding wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s'_def
by auto

lemma (in intruder_model) intruder_synth_code[code_unfold]:
  "intruder_synth M t = intruder_synth' public arity M t"
  (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
  proof (induction t rule: intruder_synth_induct)
    case (AxiomC t) thus ?case by (cases t) auto
  qed (fastforce simp add: list_all_iff)

  show "?B \<Longrightarrow> ?A"
  proof (induction t rule: intruder_synth'_induct)
    case (Fun f T) thus ?case
    proof (cases "Fun f T \<in> M")
      case False
      hence "public f" "length T = arity f" "list_all (intruder_synth' public arity M) T"
        using Fun.hyps by fastforce+
      thus ?thesis
        using Fun.IH intruder_synth.ComposeC[of T f M] Ball_set[of T]
        by blast
    qed simp
  qed simp
qed

lemma (in intruder_model) analyzed_in_code[code_unfold]:
  "analyzed_in t M = analyzed_in' Ana public arity t M"
using intruder_synth_code[of M]
unfolding analyzed_in_def analyzed_in'_def
by fastforce

end
