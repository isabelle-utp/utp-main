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

(*  Title:      Typing_Result.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>The Typing Result\<close>
text \<open>\label{sec:Typing-Result}\<close>

theory Typing_Result
imports Typed_Model
begin

subsection \<open>The Typing Result for the Composition-Only Intruder\<close>
context typed_model
begin

subsubsection \<open>Well-typedness and Type-Flaw Resistance Preservation\<close>
context
begin

private lemma LI_preserves_tfr_stp_all_single:
  assumes "(S,\<theta>) \<leadsto> (S',\<theta>')" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
  and "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)"
  shows "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'"
using assms
proof (induction rule: LI_rel.induct)
  case (Compose S X f S' \<theta>)
  hence "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'" by simp_all
  moreover have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (map Send X)" by (induct X) auto
  ultimately show ?case by simp
next
  case (Unify S f Y \<delta> X S' \<theta>)
  hence "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S')" by simp

  have "fv\<^sub>s\<^sub>t (S@Send (Fun f X)#S') \<inter> bvars\<^sub>s\<^sub>t (S@S') = {}"
    using Unify.prems(1) by (auto simp add: wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)
  moreover have "fv (Fun f X) \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f X)#S')" by auto
  moreover have "fv (Fun f Y) \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f X)#S')"
    using Unify.hyps(2) fv_subset_if_in_strand_ik'[of "Fun f Y" S] by force
  ultimately have bvars_disj:
      "bvars\<^sub>s\<^sub>t (S@S') \<inter> fv (Fun f X) = {}" "bvars\<^sub>s\<^sub>t (S@S') \<inter> fv (Fun f Y) = {}"
    by blast+

  have "wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)" using Unify.prems(5) by simp
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m (Fun f Y)"
  proof -
    obtain x where "x \<in> set S" "Fun f Y \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t\<^sub>p x)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p x)"
      using Unify.hyps(2) Unify.prems(5) by force+
    thus ?thesis using wf_trm_subterm by auto
  qed
  moreover have
      "Fun f X \<in> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))" "Fun f Y \<in> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))"
    using SMP_append[of S "Send (Fun f X)#S'"] SMP_Cons[of "Send (Fun f X)" S']
          SMP_ikI[OF Unify.hyps(2)]
    by auto
  hence "\<Gamma> (Fun f X) = \<Gamma> (Fun f Y)"
    using Unify.prems(4) mgu_gives_MGU[OF Unify.hyps(3)[symmetric]]
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  ultimately have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" using mgu_wt_if_same_type[OF Unify.hyps(3)[symmetric]] by metis
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using mgu_wf_trm[OF Unify.hyps(3)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f Y)\<close>]
    by (metis wf_trm_subst_range_iff)
  moreover have "bvars\<^sub>s\<^sub>t (S@S') \<inter> range_vars \<delta> = {}"
    using mgu_vars_bounded[OF Unify.hyps(3)[symmetric]] bvars_disj by fast
  ultimately show ?case using tfr_stp_all_wt_subst_apply[OF \<open>list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S')\<close>] by metis
next
  case (Equality S \<delta> t t' a S' \<theta>)
  have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S')" "\<Gamma> t = \<Gamma> t'"
    using tfr_stp_all_same_type[of S a t t' S']
          tfr_stp_all_split(5)[of S _ S']
          MGU_is_Unifier[OF mgu_gives_MGU[OF Equality.hyps(2)[symmetric]]]
          Equality.prems(3)
    by blast+
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m t'" using Equality.prems(5) by auto
  ultimately have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
    using mgu_wt_if_same_type[OF Equality.hyps(2)[symmetric]]
    by metis
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using mgu_wf_trm[OF Equality.hyps(2)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m t'\<close>]
    by (metis wf_trm_subst_range_iff)
  moreover have "fv\<^sub>s\<^sub>t (S@Equality a t t'#S') \<inter> bvars\<^sub>s\<^sub>t (S@Equality a t t'#S') = {}"
    using Equality.prems(1) by (auto simp add: wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)
  hence "bvars\<^sub>s\<^sub>t (S@S') \<inter> fv t = {}" "bvars\<^sub>s\<^sub>t (S@S') \<inter> fv t' = {}" by auto
  hence "bvars\<^sub>s\<^sub>t (S@S') \<inter> range_vars \<delta> = {}"
    using mgu_vars_bounded[OF Equality.hyps(2)[symmetric]] by fast
  ultimately show ?case using tfr_stp_all_wt_subst_apply[OF \<open>list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S')\<close>] by metis
qed

private lemma LI_in_SMP_subset_single:
  assumes "(S,\<theta>) \<leadsto> (S',\<theta>')" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
          "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  and "trms\<^sub>s\<^sub>t S \<subseteq> SMP M"
  shows "trms\<^sub>s\<^sub>t S' \<subseteq> SMP M"
using assms
proof (induction rule: LI_rel.induct)
  case (Compose S X f S' \<theta>)
  hence "SMP (trms\<^sub>s\<^sub>t [Send (Fun f X)]) \<subseteq> SMP M"
  proof -
    have "SMP (trms\<^sub>s\<^sub>t [Send (Fun f X)]) \<subseteq> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))"
      using trms\<^sub>s\<^sub>t_append SMP_mono by auto
    thus ?thesis
      using SMP_union[of "trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S')" M]
            SMP_subset_union_eq[OF Compose.prems(6)]
      by auto
  qed
  thus ?case using Compose.prems(6) by auto
next
  case (Unify S f Y \<delta> X S' \<theta>)
  have "Fun f X \<in> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))" by auto
  moreover have "MGU \<delta> (Fun f X) (Fun f Y)"
    by (metis mgu_gives_MGU[OF Unify.hyps(3)[symmetric]])
  moreover have
        "\<And>x. x \<in> set S \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p x)" "wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)"
    using Unify.prems(4) by force+
  moreover have "Fun f Y \<in> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))"
    by (meson SMP_ikI Unify.hyps(2) contra_subsetD ik_append_subset(1))
  ultimately have "wf\<^sub>t\<^sub>r\<^sub>m (Fun f Y)" "\<Gamma> (Fun f X) = \<Gamma> (Fun f Y)"
    using ik\<^sub>s\<^sub>t_subterm_exD[OF \<open>Fun f Y \<in> ik\<^sub>s\<^sub>t S\<close>] \<open>tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))\<close>
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by (metis (full_types) SMP_wf_trm Unify.prems(4), blast)
  hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" by (metis mgu_wt_if_same_type[OF Unify.hyps(3)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)\<close>])
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using mgu_wf_trm[OF Unify.hyps(3)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f Y)\<close>] by simp
  ultimately have "trms\<^sub>s\<^sub>t ((S@Send (Fun f X)#S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> SMP M"
    using SMP.Substitution Unify.prems(6) wt_subst_SMP_subset by metis
  thus ?case by auto
next
  case (Equality S \<delta> t t' a S' \<theta>)
  hence "\<Gamma> t = \<Gamma> t'"
    using tfr_stp_all_same_type MGU_is_Unifier[OF mgu_gives_MGU[OF Equality.hyps(2)[symmetric]]]
    by metis
  moreover have "t \<in> SMP (trms\<^sub>s\<^sub>t (S@Equality a t t'#S'))" "t' \<in> SMP (trms\<^sub>s\<^sub>t (S@Equality a t t'#S'))"
    using Equality.prems(1) by auto
  moreover have "MGU \<delta> t t'" using mgu_gives_MGU[OF Equality.hyps(2)[symmetric]] by metis
  moreover have "\<And>x. x \<in> set S \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p x)" "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m t'"
    using Equality.prems(4) by force+
  ultimately have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" by (metis mgu_wt_if_same_type[OF Equality.hyps(2)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close>])
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using mgu_wf_trm[OF Equality.hyps(2)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m t'\<close>] by simp
  ultimately have "trms\<^sub>s\<^sub>t ((S@Equality a t t'#S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> SMP M"
    using SMP.Substitution Equality.prems wt_subst_SMP_subset by metis
  thus ?case by auto
qed

private lemma LI_preserves_tfr_single:
  assumes "(S,\<theta>) \<leadsto> (S',\<theta>')" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
          "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)"
          "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S') \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S')"
using assms
proof (induction rule: LI_rel.induct)
  case (Compose S X f S' \<theta>)
  let ?SMPmap = "SMP (trms\<^sub>s\<^sub>t (S@map Send X@S')) - (Var`\<V>)"
  have "?SMPmap \<subseteq> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S')) - (Var`\<V>)"
    using SMP_fun_map_snd_subset[of X f]
          SMP_append[of "map Send X" S'] SMP_Cons[of "Send (Fun f X)" S']
          SMP_append[of S "Send (Fun f X)#S'"] SMP_append[of S "map Send X@S'"]
    by auto
  hence "\<forall>s \<in> ?SMPmap. \<forall>t \<in> ?SMPmap. (\<exists>\<delta>. Unifier \<delta> s t) \<longrightarrow> \<Gamma> s = \<Gamma> t"
    using Compose unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by (meson subsetCE)
  thus ?case
    using LI_preserves_trm_wf[OF r_into_rtrancl[OF LI_rel.Compose[OF Compose.hyps]], of S']
          Compose.prems(5)
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
next
  case (Unify S f Y \<delta> X S' \<theta>)
  let ?SMP\<delta> = "SMP (trms\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>)) - (Var`\<V>)"

  have "SMP (trms\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>)) \<subseteq> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))"
  proof
    fix s assume "s \<in> SMP (trms\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>))" thus "s \<in> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))"
      using LI_in_SMP_subset_single[
              OF LI_rel.Unify[OF Unify.hyps] Unify.prems(1,2,4,5,6)
                 MP_subset_SMP(2)[of "S@Send (Fun f X)#S'"]]
      by (metis SMP_union SMP_subset_union_eq Un_iff)
  qed
  hence "\<forall>s \<in> ?SMP\<delta>. \<forall>t \<in> ?SMP\<delta>. (\<exists>\<delta>. Unifier \<delta> s t) \<longrightarrow> \<Gamma> s = \<Gamma> t"
    using Unify.prems(4) unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by (meson Diff_iff subsetCE)
  thus ?case
    using LI_preserves_trm_wf[OF r_into_rtrancl[OF LI_rel.Unify[OF Unify.hyps]], of S']
          Unify.prems(5)
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
next
  case (Equality S \<delta> t t' a S' \<theta>)
  let ?SMP\<delta> = "SMP (trms\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>)) - (Var`\<V>)"

  have "SMP (trms\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>)) \<subseteq> SMP (trms\<^sub>s\<^sub>t (S@Equality a t t'#S'))"
  proof
    fix s assume "s \<in> SMP (trms\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>))" thus "s \<in> SMP (trms\<^sub>s\<^sub>t (S@Equality a t t'#S'))"
      using LI_in_SMP_subset_single[
              OF LI_rel.Equality[OF Equality.hyps] Equality.prems(1,2,4,5,6)
                 MP_subset_SMP(2)[of "S@Equality a t t'#S'"]]
      by (metis SMP_union SMP_subset_union_eq Un_iff)
  qed
  hence "\<forall>s \<in> ?SMP\<delta>. \<forall>t \<in> ?SMP\<delta>. (\<exists>\<delta>. Unifier \<delta> s t) \<longrightarrow> \<Gamma> s = \<Gamma> t"
    using Equality.prems unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by (meson Diff_iff subsetCE)
  thus ?case
    using LI_preserves_trm_wf[OF r_into_rtrancl[OF LI_rel.Equality[OF Equality.hyps]], of _ S']
          Equality.prems
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
qed

private lemma LI_preserves_welltypedness_single:
  assumes "(S,\<theta>) \<leadsto> (S',\<theta>')" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
  and "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>' \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>')"
using assms
proof (induction rule: LI_rel.induct)
  case (Unify S f Y \<delta> X S' \<theta>)
  have "wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)" using Unify.prems(5) unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by simp
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m (Fun f Y)"
  proof -
    obtain x where "x \<in> set S" "Fun f Y \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t\<^sub>p x)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p x)"
      using Unify.hyps(2) Unify.prems(5) unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by force
    thus ?thesis using wf_trm_subterm by auto
  qed
  moreover have
      "Fun f X \<in> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))" "Fun f Y \<in> SMP (trms\<^sub>s\<^sub>t (S@Send (Fun f X)#S'))"
    using SMP_append[of S "Send (Fun f X)#S'"] SMP_Cons[of "Send (Fun f X)" S']
          SMP_ikI[OF Unify.hyps(2)]
    by auto
  hence "\<Gamma> (Fun f X) = \<Gamma> (Fun f Y)"
    using Unify.prems(4) mgu_gives_MGU[OF Unify.hyps(3)[symmetric]]
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  ultimately have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" using mgu_wt_if_same_type[OF Unify.hyps(3)[symmetric]] by metis

  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    by (meson mgu_wf_trm[OF Unify.hyps(3)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f Y)\<close>]
              wf_trm_subst_range_iff)
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<delta>))"
    using wf_trm_subst_range_iff wf_trm_subst \<open>wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)\<close>
    unfolding subst_compose_def
    by (metis (no_types, lifting))
  thus ?case by (metis wt_subst_compose[OF \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<close> \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>\<close>])
next
  case (Equality S \<delta> t t' a S' \<theta>)
  have "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m t'" using Equality.prems(5) by simp_all
  moreover have "\<Gamma> t = \<Gamma> t'"
    using \<open>list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@Equality a t t'#S')\<close>
          MGU_is_Unifier[OF mgu_gives_MGU[OF Equality.hyps(2)[symmetric]]]
    by auto
  ultimately have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" using mgu_wt_if_same_type[OF Equality.hyps(2)[symmetric]] by metis

  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    by (meson mgu_wf_trm[OF Equality.hyps(2)[symmetric] \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m t'\<close>] wf_trm_subst_range_iff)
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<delta>))"
    using wf_trm_subst_range_iff wf_trm_subst \<open>wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)\<close>
    unfolding subst_compose_def
    by (metis (no_types, lifting))
  thus ?case by (metis wt_subst_compose[OF \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<close> \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>\<close>])
qed metis

lemma LI_preserves_welltypedness:
  assumes "(S,\<theta>) \<leadsto>\<^sup>* (S',\<theta>')" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    and "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>'" (is "?A \<theta>'")
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>')" (is "?B \<theta>'")
proof -
  have "?A \<theta>' \<and> ?B \<theta>'" using assms
  proof (induction S \<theta> rule: converse_rtrancl_induct2)
    case (step S1 \<theta>1 S2 \<theta>2)
    hence "?A \<theta>2 \<and> ?B \<theta>2" using LI_preserves_welltypedness_single by presburger
    moreover have "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S2 \<theta>2"
      by (fact LI_preserves_wellformedness[OF r_into_rtrancl[OF step.hyps(1)] step.prems(1)])
    moreover have "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S2)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S2)"
      using LI_preserves_tfr_single[OF step.hyps(1)] step.prems by presburger+
    moreover have "list_all tfr\<^sub>s\<^sub>t\<^sub>p S2"
      using LI_preserves_tfr_stp_all_single[OF step.hyps(1)] step.prems by fastforce
    ultimately show ?case using step.IH by presburger
  qed simp
  thus "?A \<theta>'" "?B \<theta>'" by simp_all
qed

lemma LI_preserves_tfr:
  assumes "(S,\<theta>) \<leadsto>\<^sup>* (S',\<theta>')" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    and "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S')" (is "?A S'")
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S')" (is "?B S'")
    and "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'" (is "?C S'")
proof -
  have "?A S' \<and> ?B S' \<and> ?C S'" using assms
  proof (induction S \<theta> rule: converse_rtrancl_induct2)
    case (step S1 \<theta>1 S2 \<theta>2)
    have "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S2 \<theta>2" "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S2)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S2)" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S2"
      using LI_preserves_wellformedness[OF r_into_rtrancl[OF step.hyps(1)] step.prems(1)]
            LI_preserves_tfr_single[OF step.hyps(1) step.prems(1,2)]
            LI_preserves_tfr_stp_all_single[OF step.hyps(1) step.prems(1,2)]
            step.prems(3,4,5,6)
      by metis+
    moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>2" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>2)"
      using LI_preserves_welltypedness[OF r_into_rtrancl[OF step.hyps(1)] step.prems]
      by simp_all
    ultimately show ?case using step.IH by presburger
  qed blast
  thus "?A S'" "?B S'" "?C S'" by simp_all
qed
end

subsubsection \<open>Simple Constraints are Well-typed Satisfiable\<close>
text \<open>Proving the existence of a well-typed interpretation\<close>
context
begin
lemma wt_interpretation_exists:
  obtains \<I>::"('fun,'var) subst"
  where "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "subst_range \<I> \<subseteq> public_ground_wf_terms"
proof
  define \<I> where "\<I> = (\<lambda>x. (SOME t. \<Gamma> (Var x) = \<Gamma> t \<and> public_ground_wf_term t))"

  { fix x t assume "\<I> x = t"
    hence "\<Gamma> (Var x) = \<Gamma> t \<and> public_ground_wf_term t"
      using someI_ex[of "\<lambda>t. \<Gamma> (Var x) = \<Gamma> t \<and> public_ground_wf_term t",
                     OF type_pgwt_inhabited[of "Var x"]]
      unfolding \<I>_def wf\<^sub>t\<^sub>r\<^sub>m_def by simp
  } hence props: "\<I> v = t \<Longrightarrow> \<Gamma> (Var v) = \<Gamma> t \<and> public_ground_wf_term t" for v t by metis

  have "\<I> v \<noteq> Var v" for v using props pgwt_ground by (simp add: empty_fv_not_var)
  hence "subst_domain \<I> = UNIV" by auto
  moreover have "ground (subst_range \<I>)" by (simp add: props pgwt_ground)
  ultimately show "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" by metis
  show "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def using props by simp
  show "subst_range \<I> \<subseteq> public_ground_wf_terms" by (auto simp add: props)
qed

lemma wt_grounding_subst_exists:
  "\<exists>\<theta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<and> fv (t \<cdot> \<theta>) = {}"
proof -
  obtain \<theta> where \<theta>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "subst_range \<theta> \<subseteq> public_ground_wf_terms"
    using wt_interpretation_exists by blast
  show ?thesis using pgwt_wellformed interpretation_grounds[OF \<theta>(1)] \<theta>(2,3) by blast
qed

private fun fresh_pgwt::"'fun set \<Rightarrow> ('fun,'atom) term_type \<Rightarrow> ('fun,'var) term"  where
  "fresh_pgwt S (TAtom a) =
    Fun (SOME c. c \<notin> S \<and> \<Gamma> (Fun c []) = TAtom a \<and> public c) []"
| "fresh_pgwt S (TComp f T) = Fun f (map (fresh_pgwt S) T)"

private lemma fresh_pgwt_same_type:
  assumes "finite S" "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "\<Gamma> (fresh_pgwt S (\<Gamma> t)) = \<Gamma> t"
proof -
  let ?P = "\<lambda>\<tau>::('fun,'atom) term_type. wf\<^sub>t\<^sub>r\<^sub>m \<tau> \<and> (\<forall>f T. TComp f T \<sqsubseteq> \<tau> \<longrightarrow> 0 < arity f)"
  { fix \<tau> assume "?P \<tau>" hence "\<Gamma> (fresh_pgwt S \<tau>) = \<tau>"
    proof (induction \<tau>)
      case (Var a)
      let ?P = "\<lambda>c. c \<notin> S \<and> \<Gamma> (Fun c []) = Var a \<and> public c"
      let ?Q = "\<lambda>c. \<Gamma> (Fun c []) = Var a \<and> public c"
      have " {c. ?Q c} - S = {c. ?P c}" by auto
      hence "infinite {c. ?P c}"
        using Diff_infinite_finite[OF assms(1) infinite_typed_consts[of a]]
        by metis
      hence "\<exists>c. ?P c" using not_finite_existsD by blast
      thus ?case using someI_ex[of ?P] by auto
    next
      case (Fun f T)
      have f: "0 < arity f" using Fun.prems fun_type_inv by auto
      have "\<And>t. t \<in> set T \<Longrightarrow> ?P t"
        using Fun.prems wf_trm_subtermeq term.le_less_trans Fun_param_is_subterm
        by metis
      hence "\<And>t. t \<in> set T \<Longrightarrow> \<Gamma> (fresh_pgwt S t) = t" using Fun.prems Fun.IH by auto
      hence "map \<Gamma> (map (fresh_pgwt S) T) = T"  by (induct T) auto
      thus ?case using fun_type[OF f] by simp
    qed
  } thus ?thesis using assms(1) \<Gamma>_wf'[OF assms(2)] \<Gamma>_wf(1) by auto
qed

private lemma fresh_pgwt_empty_synth:
  assumes "finite S" "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "{} \<turnstile>\<^sub>c fresh_pgwt S (\<Gamma> t)"
proof -
  let ?P = "\<lambda>\<tau>::('fun,'atom) term_type. wf\<^sub>t\<^sub>r\<^sub>m \<tau> \<and> (\<forall>f T. TComp f T \<sqsubseteq> \<tau> \<longrightarrow> 0 < arity f)"
  { fix \<tau> assume "?P \<tau>" hence "{} \<turnstile>\<^sub>c fresh_pgwt S \<tau>"
    proof (induction \<tau>)
      case (Var a)
      let ?P = "\<lambda>c. c \<notin> S \<and> \<Gamma> (Fun c []) = Var a \<and> public c"
      let ?Q = "\<lambda>c. \<Gamma> (Fun c []) = Var a \<and> public c"
      have " {c. ?Q c} - S = {c. ?P c}" by auto
      hence "infinite {c. ?P c}"
        using Diff_infinite_finite[OF assms(1) infinite_typed_consts[of a]]
        by metis
      hence "\<exists>c. ?P c" using not_finite_existsD by blast
      thus ?case
        using someI_ex[of ?P] intruder_synth.ComposeC[of "[]" _ "{}"] const_type_inv
        by auto
    next
      case (Fun f T)
      have f: "0 < arity f" "length T = arity f" "public f"
        using Fun.prems fun_type_inv unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
      have "\<And>t. t \<in> set T \<Longrightarrow> ?P t"
        using Fun.prems wf_trm_subtermeq term.le_less_trans Fun_param_is_subterm
        by metis
      hence "\<And>t. t \<in> set T \<Longrightarrow> {} \<turnstile>\<^sub>c fresh_pgwt S t" using Fun.prems Fun.IH by auto
      moreover have "length (map (fresh_pgwt S) T) = arity f" using f(2) by auto
      ultimately show ?case using intruder_synth.ComposeC[of "map (fresh_pgwt S) T" f] f by auto
    qed
  } thus ?thesis using assms(1) \<Gamma>_wf'[OF assms(2)] \<Gamma>_wf(1) by auto
qed

private lemma fresh_pgwt_has_fresh_const:
  assumes "finite S" "wf\<^sub>t\<^sub>r\<^sub>m t"
  obtains c where "Fun c [] \<sqsubseteq> fresh_pgwt S (\<Gamma> t)" "c \<notin> S"
proof -
  let ?P = "\<lambda>\<tau>::('fun,'atom) term_type. wf\<^sub>t\<^sub>r\<^sub>m \<tau> \<and> (\<forall>f T. TComp f T \<sqsubseteq> \<tau> \<longrightarrow> 0 < arity f)"
  { fix \<tau> assume "?P \<tau>" hence "\<exists>c. Fun c [] \<sqsubseteq> fresh_pgwt S \<tau> \<and> c \<notin> S"
    proof (induction \<tau>)
      case (Var a)
      let ?P = "\<lambda>c. c \<notin> S \<and> \<Gamma> (Fun c []) = Var a \<and> public c"
      let ?Q = "\<lambda>c. \<Gamma> (Fun c []) = Var a \<and> public c"
      have " {c. ?Q c} - S = {c. ?P c}" by auto
      hence "infinite {c. ?P c}"
        using Diff_infinite_finite[OF assms(1) infinite_typed_consts[of a]]
        by metis
      hence "\<exists>c. ?P c" using not_finite_existsD by blast
      thus ?case using someI_ex[of ?P] by auto
    next
      case (Fun f T)
      have f: "0 < arity f" "length T = arity f" "public f" "T \<noteq> []"
        using Fun.prems fun_type_inv unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
      obtain t' where t': "t' \<in> set T" by (meson all_not_in_conv f(4) set_empty)
      have "\<And>t. t \<in> set T \<Longrightarrow> ?P t"
        using Fun.prems wf_trm_subtermeq term.le_less_trans Fun_param_is_subterm
        by metis
      hence "\<And>t. t \<in> set T \<Longrightarrow> \<exists>c. Fun c [] \<sqsubseteq> fresh_pgwt S t \<and> c \<notin> S"
        using Fun.prems Fun.IH by auto
      then obtain c where c: "Fun c [] \<sqsubseteq> fresh_pgwt S t'" "c \<notin> S" using t' by metis
      thus ?case using t' by auto
    qed
  } thus ?thesis using that assms \<Gamma>_wf'[OF assms(2)] \<Gamma>_wf(1) by blast
qed

private lemma fresh_pgwt_subterm_fresh:
  assumes "finite S" "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m s" "funs_term s \<subseteq> S"
  shows "s \<notin> subterms (fresh_pgwt S (\<Gamma> t))"
proof -
  let ?P = "\<lambda>\<tau>::('fun,'atom) term_type. wf\<^sub>t\<^sub>r\<^sub>m \<tau> \<and> (\<forall>f T. TComp f T \<sqsubseteq> \<tau> \<longrightarrow> 0 < arity f)"
  { fix \<tau> assume "?P \<tau>" hence "s \<notin> subterms (fresh_pgwt S \<tau>)"
    proof (induction \<tau>)
      case (Var a)
      let ?P = "\<lambda>c. c \<notin> S \<and> \<Gamma> (Fun c []) = Var a \<and> public c"
      let ?Q = "\<lambda>c. \<Gamma> (Fun c []) = Var a \<and> public c"
      have " {c. ?Q c} - S = {c. ?P c}" by auto
      hence "infinite {c. ?P c}"
        using Diff_infinite_finite[OF assms(1) infinite_typed_consts[of a]]
        by metis
      hence "\<exists>c. ?P c" using not_finite_existsD by blast
      thus ?case using someI_ex[of ?P] assms(4) by auto
    next
      case (Fun f T)
      have f: "0 < arity f" "length T = arity f" "public f"
        using Fun.prems fun_type_inv unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
      have "\<And>t. t \<in> set T \<Longrightarrow> ?P t"
        using Fun.prems wf_trm_subtermeq term.le_less_trans Fun_param_is_subterm
        by metis
      hence "\<And>t. t \<in> set T \<Longrightarrow> s \<notin> subterms (fresh_pgwt S t)" using Fun.prems Fun.IH by auto
      moreover have "s \<noteq> fresh_pgwt S (Fun f T)"
      proof -
        obtain c where c: "Fun c [] \<sqsubseteq> fresh_pgwt S (Fun f T)" "c \<notin> S"
          using fresh_pgwt_has_fresh_const[OF assms(1)] type_wfttype_inhabited Fun.prems
          by metis
        hence "\<not>Fun c [] \<sqsubseteq> s" using assms(4) subtermeq_imp_funs_term_subset by force
        thus ?thesis using c(1) by auto
      qed
      ultimately show ?case by auto
    qed
  } thus ?thesis using assms(1) \<Gamma>_wf'[OF assms(2)] \<Gamma>_wf(1) by auto
qed

private lemma wt_fresh_pgwt_term_exists:
  assumes "finite T" "wf\<^sub>t\<^sub>r\<^sub>m s" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s T"
  obtains t where "\<Gamma> t = \<Gamma> s" "{} \<turnstile>\<^sub>c t" "\<forall>s \<in> T. \<forall>u \<in> subterms s. u \<notin> subterms t"
proof -
  have finite_S: "finite (\<Union>(funs_term ` T))" using assms(1) by auto

  have 1: "\<Gamma> (fresh_pgwt (\<Union>(funs_term ` T)) (\<Gamma> s)) = \<Gamma> s"
    using fresh_pgwt_same_type[OF finite_S assms(2)] by auto

  have 2: "{} \<turnstile>\<^sub>c fresh_pgwt (\<Union>(funs_term ` T)) (\<Gamma> s)"
    using fresh_pgwt_empty_synth[OF finite_S assms(2)] by auto

  have 3: "\<forall>v \<in> T. \<forall>u \<in> subterms v. u \<notin> subterms (fresh_pgwt (\<Union>(funs_term ` T)) (\<Gamma> s))"
    using fresh_pgwt_subterm_fresh[OF finite_S assms(2)] assms(3)
          wf_trm_subtermeq subtermeq_imp_funs_term_subset
    by force

  show ?thesis by (rule that[OF 1 2 3])
qed

lemma wt_bij_finite_subst_exists:
  assumes "finite (S::'var set)" "finite (T::('fun,'var) terms)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s T"
  shows "\<exists>\<sigma>::('fun,'var) subst.
              subst_domain \<sigma> = S
            \<and> bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)
            \<and> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>) \<subseteq> {t. {} \<turnstile>\<^sub>c t} - T
            \<and> (\<forall>s \<in> subst_range \<sigma>. \<forall>u \<in> subst_range \<sigma>. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u)
            \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>
            \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
using assms
proof (induction rule: finite_induct)
  case empty
  have "subst_domain Var = {}"
       "bij_betw Var (subst_domain Var) (subst_range Var)"
       "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range Var) \<subseteq> {t. {} \<turnstile>\<^sub>c t} - T"
       "\<forall>s \<in> subst_range Var. \<forall>u \<in> subst_range Var. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u"
       "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var"
       "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)"
    unfolding bij_betw_def
    by auto
  thus ?case by (force simp add: subst_domain_def)
next
  case (insert x S)
  then obtain \<sigma> where \<sigma>:
      "subst_domain \<sigma> = S" "bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)"
      "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>) \<subseteq> {t. {} \<turnstile>\<^sub>c t} - T"
      "\<forall>s \<in> subst_range \<sigma>. \<forall>u \<in> subst_range \<sigma>. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u"
      "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
    by (auto simp del: subst_range.simps)

  have *: "finite (T \<union> subst_range \<sigma>)"
    using insert.prems(1) insert.hyps(1) \<sigma>(1) by simp
  have **: "wf\<^sub>t\<^sub>r\<^sub>m (Var x)" by simp
  have ***: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (T \<union> subst_range \<sigma>)" using assms(3) \<sigma>(6) by blast
  obtain t where t:
      "\<Gamma> t = \<Gamma> (Var x)" "{} \<turnstile>\<^sub>c t"
      "\<forall>s \<in> T \<union> subst_range \<sigma>. \<forall>u \<in> subterms s. u \<notin> subterms t"
    using wt_fresh_pgwt_term_exists[OF * ** ***] by auto

  obtain \<theta> where \<theta>: "\<theta> \<equiv> \<lambda>y. if x = y then t else \<sigma> y" by simp

  have t_ground: "fv t = {}" using t(2) pgwt_ground[of t] pgwt_is_empty_synth[of t] by auto
  hence x_dom: "x \<notin> subst_domain \<sigma>" "x \<in> subst_domain \<theta>" using insert.hyps(2) \<sigma>(1) \<theta> by auto
  moreover have "subst_range \<sigma> \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>)" by auto
  hence ground_imgs: "ground (subst_range \<sigma>)"
    using \<sigma>(3) pgwt_ground pgwt_is_empty_synth
    by force
  ultimately have x_img: "\<sigma> x \<notin> subst_range \<sigma>"
    using ground_subst_dom_iff_img
    by (auto simp add: subst_domain_def)

  have "ground (insert t (subst_range \<sigma>))"
    using ground_imgs x_dom t_ground
    by auto
  have \<theta>_dom: "subst_domain \<theta> = insert x (subst_domain \<sigma>)"
    using \<theta> t_ground by (auto simp add: subst_domain_def)
  have \<theta>_img: "subst_range \<theta> = insert t (subst_range \<sigma>)"
  proof
    show "subst_range \<theta> \<subseteq> insert t (subst_range \<sigma>)"
    proof
      fix t' assume "t' \<in> subst_range \<theta>"
      then obtain y where "y \<in> subst_domain \<theta>" "t' = \<theta> y" by auto
      thus "t' \<in> insert t (subst_range \<sigma>)" using \<theta> by (auto simp add: subst_domain_def)
    qed
    show "insert t (subst_range \<sigma>) \<subseteq> subst_range \<theta>"
    proof
      fix t' assume t': "t' \<in> insert t (subst_range \<sigma>)"
      hence "fv t' = {}" using ground_imgs x_img t_ground by auto
      hence "t' \<noteq> Var x" by auto
      show "t' \<in> subst_range \<theta>"
      proof (cases "t' = t")
        case False
        hence "t' \<in> subst_range \<sigma>" using t' by auto
        then obtain y where "\<sigma> y \<in> subst_range \<sigma>" "t' = \<sigma> y" by auto
        hence "y \<in> subst_domain \<sigma>" "t' \<noteq> Var y"
          using ground_subst_dom_iff_img[OF ground_imgs(1)]
          by (auto simp add: subst_domain_def simp del: subst_range.simps)
        hence "x \<noteq> y" using x_dom by auto
        hence "\<theta> y = \<sigma> y" unfolding \<theta> by auto
        thus ?thesis using \<open>t' \<noteq> Var y\<close> \<open>t' = \<sigma> y\<close> subst_imgI[of \<theta> y] by auto
      qed (metis subst_imgI \<theta> \<open>t' \<noteq> Var x\<close>)
    qed
  qed
  hence \<theta>_ground_img: "ground (subst_range \<theta>)"
    using ground_imgs t_ground
    by auto

  have "subst_domain \<theta> = insert x S" using \<theta>_dom \<sigma>(1) by auto
  moreover have "bij_betw \<theta> (subst_domain \<theta>) (subst_range \<theta>)"
  proof (intro bij_betwI')
    fix y z assume *: "y \<in> subst_domain \<theta>" "z \<in> subst_domain \<theta>"
    hence "fv (\<theta> y) = {}" "fv (\<theta> z) = {}" using \<theta>_ground_img by auto
    { assume "\<theta> y = \<theta> z" hence "y = z"
      proof (cases "\<theta> y \<in> subst_range \<sigma> \<and> \<theta> z \<in> subst_range \<sigma>")
        case True
        hence **: "y \<in> subst_domain \<sigma>" "z \<in> subst_domain \<sigma>"
          using \<theta> \<theta>_dom True * t(3) by (metis Un_iff term.order_refl insertE)+
        hence "y \<noteq> x" "z \<noteq> x" using x_dom by auto
        hence "\<theta> y = \<sigma> y" "\<theta> z = \<sigma> z" using \<theta> by auto
        thus ?thesis using \<open>\<theta> y = \<theta> z\<close> \<sigma>(2) ** unfolding bij_betw_def inj_on_def by auto
      qed (metis \<theta> * \<open>\<theta> y = \<theta> z\<close> \<theta>_dom ground_imgs(1) ground_subst_dom_iff_img insertE)
    }
    thus "(\<theta> y = \<theta> z) = (y = z)" by auto
  next
    fix y assume "y \<in> subst_domain \<theta>" thus "\<theta> y \<in> subst_range \<theta>" by auto
  next
    fix t assume "t \<in> subst_range \<theta>" thus "\<exists>z \<in> subst_domain \<theta>. t = \<theta> z" by auto
  qed
  moreover have "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>) \<subseteq> {t. {} \<turnstile>\<^sub>c t}  - T"
  proof -
    { fix s assume "s \<sqsubseteq> t"
      hence "s \<in> {t. {} \<turnstile>\<^sub>c t}  - T"
        using t(2,3)
        by (metis Diff_eq_empty_iff Diff_iff Un_upper1 term.order_refl
                  deduct_synth_subterm mem_Collect_eq)
    } thus ?thesis using \<sigma>(3) \<theta> \<theta>_img by auto
  qed
  moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" using \<theta> t(1) \<sigma>(5) unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by auto
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    using \<theta> \<sigma>(6) t(2) pgwt_is_empty_synth pgwt_wellformed
          wf_trm_subst_range_iff[of \<sigma>] wf_trm_subst_range_iff[of \<theta>]
    by metis
  moreover have "\<forall>s\<in>subst_range \<theta>. \<forall>u\<in>subst_range \<theta>. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u"
    using \<sigma>(4) \<theta>_img t(3) by (auto simp del: subst_range.simps)
  ultimately show ?case by blast
qed

private lemma wt_bij_finite_tatom_subst_exists_single:
  assumes "finite (S::'var set)" "finite (T::('fun,'var) terms)"
  and "\<And>x. x \<in> S \<Longrightarrow> \<Gamma> (Var x) = TAtom a"
  shows "\<exists>\<sigma>::('fun,'var) subst. subst_domain \<sigma> = S
                      \<and> bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)
                      \<and> subst_range \<sigma> \<subseteq> ((\<lambda>c. Fun c []) `  {c. \<Gamma> (Fun c []) = TAtom a \<and>
                                                            public c \<and> arity c = 0}) - T
                      \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>
                      \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
proof -
  let ?U = "{c. \<Gamma> (Fun c []) = TAtom a \<and> public c \<and> arity c = 0}"

  obtain \<sigma> where \<sigma>:
      "subst_domain \<sigma> = S" "bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)"
      "subst_range \<sigma> \<subseteq> ((\<lambda>c. Fun c []) ` ?U) - T"
    using bij_finite_const_subst_exists'[OF assms(1,2) infinite_typed_consts'[of a]]
    by auto

  { fix x assume "x \<notin> subst_domain \<sigma>" hence "\<Gamma> (Var x) = \<Gamma> (\<sigma> x)" by auto }
  moreover
  { fix x assume "x \<in> subst_domain \<sigma>"
    hence "\<exists>c \<in> ?U. \<sigma> x = Fun c [] \<and> arity c = 0" using \<sigma> by auto
    hence "\<Gamma> (\<sigma> x) = TAtom a" "wf\<^sub>t\<^sub>r\<^sub>m (\<sigma> x)" using assms(3) const_type wf_trmI[of "[]"] by auto
    hence "\<Gamma> (Var x) = \<Gamma> (\<sigma> x)" "wf\<^sub>t\<^sub>r\<^sub>m (\<sigma> x)" using assms(3) \<sigma>(1) by force+
  }
  ultimately have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
    using wf_trm_subst_range_iff[of \<sigma>]
    unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
    by force+
  thus ?thesis using \<sigma> by auto
qed

lemma wt_bij_finite_tatom_subst_exists:
  assumes "finite (S::'var set)" "finite (T::('fun,'var) terms)"
  and "\<And>x. x \<in> S \<Longrightarrow> \<exists>a. \<Gamma> (Var x) = TAtom a"
  shows "\<exists>\<sigma>::('fun,'var) subst. subst_domain \<sigma> = S
                      \<and> bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)
                      \<and> subst_range \<sigma> \<subseteq> ((\<lambda>c. Fun c []) `  \<C>\<^sub>p\<^sub>u\<^sub>b) - T
                      \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>
                      \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
using assms
proof (induction rule: finite_induct)
  case empty
  have "subst_domain Var = {}"
       "bij_betw Var (subst_domain Var) (subst_range Var)"
       "subst_range Var \<subseteq> ((\<lambda>c. Fun c []) `  \<C>\<^sub>p\<^sub>u\<^sub>b) - T"
       "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var"
       "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)"
    unfolding bij_betw_def
    by auto
  thus ?case by (auto simp add: subst_domain_def)
next
  case (insert x S)
  then obtain a where a: "\<Gamma> (Var x) = TAtom a" by fastforce

  from insert obtain \<sigma> where \<sigma>:
      "subst_domain \<sigma> = S" "bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)"
      "subst_range \<sigma> \<subseteq> ((\<lambda>c. Fun c []) `  \<C>\<^sub>p\<^sub>u\<^sub>b) - T" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
    by auto

  let ?S' = "{y \<in> S. \<Gamma> (Var y) = TAtom a}"
  let ?T' = "T \<union> subst_range \<sigma>"

  have *: "finite (insert x ?S')" using insert by simp
  have **: "finite ?T'" using insert.prems(1) insert.hyps(1) \<sigma>(1) by simp
  have ***: "\<And>y. y \<in> insert x ?S' \<Longrightarrow> \<Gamma> (Var y) = TAtom a" using a by auto

  obtain \<delta> where \<delta>:
      "subst_domain \<delta> = insert x ?S'" "bij_betw \<delta> (subst_domain \<delta>) (subst_range \<delta>)"
      "subst_range \<delta> \<subseteq> ((\<lambda>c. Fun c []) `  \<C>\<^sub>p\<^sub>u\<^sub>b) - ?T'" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using wt_bij_finite_tatom_subst_exists_single[OF * ** ***] const_type_inv[of _ "[]" a]
    by blast

  obtain \<theta> where \<theta>: "\<theta> \<equiv> \<lambda>y. if x = y then \<delta> y else \<sigma> y" by simp

  have x_dom: "x \<notin> subst_domain \<sigma>" "x \<in> subst_domain \<delta>" "x \<in> subst_domain \<theta>"
    using insert.hyps(2) \<sigma>(1) \<delta>(1) \<theta> by (auto simp add: subst_domain_def)
  moreover have ground_imgs: "ground (subst_range \<sigma>)" "ground (subst_range \<delta>)"
    using pgwt_ground \<sigma>(3) \<delta>(3) by auto
  ultimately have x_img: "\<sigma> x \<notin> subst_range \<sigma>" "\<delta> x \<in> subst_range \<delta>"
    using ground_subst_dom_iff_img by (auto simp add: subst_domain_def)

  have "ground (insert (\<delta> x) (subst_range \<sigma>))" using ground_imgs x_dom by auto
  have \<theta>_dom: "subst_domain \<theta> = insert x (subst_domain \<sigma>)"
    using \<delta>(1) \<theta> by (auto simp add: subst_domain_def)
  have \<theta>_img: "subst_range \<theta> = insert (\<delta> x) (subst_range \<sigma>)"
  proof
    show "subst_range \<theta> \<subseteq> insert (\<delta> x) (subst_range \<sigma>)"
    proof
      fix t assume "t \<in> subst_range \<theta>"
      then obtain y where "y \<in> subst_domain \<theta>" "t = \<theta> y" by auto
      thus "t \<in> insert (\<delta> x) (subst_range \<sigma>)" using \<theta> by (auto simp add: subst_domain_def)
    qed
    show "insert (\<delta> x) (subst_range \<sigma>) \<subseteq> subst_range \<theta>"
    proof
      fix t assume t: "t \<in> insert (\<delta> x) (subst_range \<sigma>)"
      hence "fv t = {}" using ground_imgs x_img(2) by auto
      hence "t \<noteq> Var x" by auto
      show "t \<in> subst_range \<theta>"
      proof (cases "t = \<delta> x")
        case True thus ?thesis using subst_imgI \<theta> \<open>t \<noteq> Var x\<close> by metis
      next
        case False
        hence "t \<in> subst_range \<sigma>" using t by auto
        then obtain y where "\<sigma> y \<in> subst_range \<sigma>" "t = \<sigma> y" by auto
        hence "y \<in> subst_domain \<sigma>" "t \<noteq> Var y"
          using ground_subst_dom_iff_img[OF ground_imgs(1)]
          by (auto simp add: subst_domain_def simp del: subst_range.simps)
        hence "x \<noteq> y" using x_dom by auto
        hence "\<theta> y = \<sigma> y" unfolding \<theta> by auto
        thus ?thesis using \<open>t \<noteq> Var y\<close> \<open>t = \<sigma> y\<close> subst_imgI[of \<theta> y] by auto
      qed
    qed
  qed
  hence \<theta>_ground_img: "ground (subst_range \<theta>)" using ground_imgs x_img by auto

  have "subst_domain \<theta> = insert x S" using \<theta>_dom \<sigma>(1) by auto
  moreover have "bij_betw \<theta> (subst_domain \<theta>) (subst_range \<theta>)"
  proof (intro bij_betwI')
    fix y z assume *: "y \<in> subst_domain \<theta>" "z \<in> subst_domain \<theta>"
    hence "fv (\<theta> y) = {}" "fv (\<theta> z) = {}" using \<theta>_ground_img by auto
    { assume "\<theta> y = \<theta> z" hence "y = z"
      proof (cases "\<theta> y \<in> subst_range \<sigma> \<and> \<theta> z \<in> subst_range \<sigma>")
        case True
        hence **: "y \<in> subst_domain \<sigma>" "z \<in> subst_domain \<sigma>"
          using \<theta> \<theta>_dom x_img(2) \<delta>(3) True
          by (metis (no_types) *(1) DiffE Un_upper2 insertE subsetCE,
              metis (no_types) *(2) DiffE Un_upper2 insertE subsetCE)
        hence "y \<noteq> x" "z \<noteq> x" using x_dom by auto
        hence "\<theta> y = \<sigma> y" "\<theta> z = \<sigma> z" using \<theta> by auto
        thus ?thesis using \<open>\<theta> y = \<theta> z\<close> \<sigma>(2) ** unfolding bij_betw_def inj_on_def by auto
      qed (metis \<theta> * \<open>\<theta> y = \<theta> z\<close> \<theta>_dom ground_imgs(1) ground_subst_dom_iff_img insertE)
    }
    thus "(\<theta> y = \<theta> z) = (y = z)" by auto
  next
    fix y assume "y \<in> subst_domain \<theta>" thus "\<theta> y \<in> subst_range \<theta>" by auto
  next
    fix t assume "t \<in> subst_range \<theta>" thus "\<exists>z \<in> subst_domain \<theta>. t = \<theta> z" by auto
  qed
  moreover have "subst_range \<theta> \<subseteq> (\<lambda>c. Fun c []) ` \<C>\<^sub>p\<^sub>u\<^sub>b - T"
    using \<sigma>(3) \<delta>(3) \<theta> by (auto simp add: subst_domain_def)
  moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" using \<sigma>(4) \<delta>(4) \<theta> unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by auto
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    using \<theta> \<sigma>(5) \<delta>(5) wf_trm_subst_range_iff[of \<delta>]
          wf_trm_subst_range_iff[of \<sigma>] wf_trm_subst_range_iff[of \<theta>]
    by presburger
  ultimately show ?case by blast
qed

theorem wt_sat_if_simple:
  assumes "simple S" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)"
  and \<I>': "\<forall>X F. Inequality X F \<in> set S \<longrightarrow> ineq_model \<I>' X F"
         "ground (subst_range \<I>')"
         "subst_domain \<I>' = {x \<in> vars\<^sub>s\<^sub>t S. \<exists>X F. Inequality X F \<in> set S \<and> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X}"
  and tfr_stp_all: "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  shows "\<exists>\<I>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<rangle>) \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
proof -
  from \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>\<close> have "wf\<^sub>s\<^sub>t {} S" "subst_idem \<theta>" and S_\<theta>_disj: "\<forall>v \<in> vars\<^sub>s\<^sub>t S. \<theta> v = Var v"
    using subst_idemI[of \<theta>] unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by force+

  obtain \<I>::"('fun,'var) subst"
    where \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "subst_range \<I> \<subseteq> public_ground_wf_terms"
    using wt_interpretation_exists by blast
  hence \<I>_deduct: "\<And>x M. M \<turnstile>\<^sub>c \<I> x" and \<I>_wf_trm: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    using pgwt_deducible pgwt_wellformed by fastforce+

  let ?P = "\<lambda>\<delta> X. subst_domain \<delta> = set X \<and> ground (subst_range \<delta>)"
  let ?Sineqsvars = "{x \<in> vars\<^sub>s\<^sub>t S. \<exists>X F. Inequality X F \<in> set S \<and> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<and> x \<notin> set X}"
  let ?Strms = "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)"

  have finite_vars: "finite ?Sineqsvars" "finite ?Strms" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s ?Strms"
    using wf_trm_subtermeq assms(5) by fastforce+

  define Q1 where "Q1 = (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
    \<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. \<exists>a. \<Gamma> (Var x) = TAtom a)"

  define Q2 where "Q2 = (\<lambda>(F::(('fun,'var) term \<times> ('fun,'var) term) list) X.
    \<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))"

  define Q1' where "Q1' = (\<lambda>(t::('fun,'var) term) (t'::('fun,'var) term) X.
    \<forall>x \<in> (fv t \<union> fv t') - set X. \<exists>a. \<Gamma> (Var x) = TAtom a)"

  define Q2' where "Q2' = (\<lambda>(t::('fun,'var) term) (t'::('fun,'var) term) X.
    \<forall>f T. Fun f T \<in> subterms t \<union> subterms t' \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))"

  have ex_P: "\<forall>X. \<exists>\<delta>. ?P \<delta> X" using interpretation_subst_exists' by blast

  have tfr_ineq: "\<forall>X F. Inequality X F \<in> set S \<longrightarrow> Q1 F X \<or> Q2 F X"
    using tfr_stp_all Q1_def Q2_def tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def[of S] by blast

  have S_fv_bvars_disj: "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}" using \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>\<close> unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by metis
  hence ineqs_vars_not_bound: "\<forall>X F x. Inequality X F \<in> set S \<longrightarrow> x \<in> ?Sineqsvars \<longrightarrow> x \<notin> set X"
    using strand_fv_bvars_disjoint_unfold by blast

  have \<theta>_vars_S_bvars_disj: "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> set X = {}"
    when "Inequality X F \<in> set S" for F X
    using wf_constr_bvars_disj[OF \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>\<close>]
          strand_fv_bvars_disjointD(1)[OF S_fv_bvars_disj that]
    by blast

  obtain \<sigma>::"('fun,'var) subst"
    where \<sigma>_fv_dom: "subst_domain \<sigma> = ?Sineqsvars"
    and \<sigma>_subterm_inj: "subterm_inj_on \<sigma> (subst_domain \<sigma>)"
    and \<sigma>_fresh_pub_img: "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>) \<subseteq> {t. {} \<turnstile>\<^sub>c t} - ?Strms"
    and \<sigma>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>"
    and \<sigma>_wf_trm: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
    using wt_bij_finite_subst_exists[OF finite_vars]
          subst_inj_on_is_bij_betw subterm_inj_on_alt_def'
    by moura

  have \<sigma>_bij_dom_img: "bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)"
    by (metis \<sigma>_subterm_inj subst_inj_on_is_bij_betw subterm_inj_on_alt_def)

  have "finite (subst_domain \<sigma>)" by(metis \<sigma>_fv_dom finite_vars(1))
  hence \<sigma>_finite_img: "finite (subst_range \<sigma>)" using \<sigma>_bij_dom_img bij_betw_finite by blast

  have \<sigma>_img_subterms: "\<forall>s \<in> subst_range \<sigma>. \<forall>u \<in> subst_range \<sigma>. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u"
    by (metis \<sigma>_subterm_inj subterm_inj_on_alt_def')

  have "subst_range \<sigma> \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>)" by auto
  hence "subst_range \<sigma> \<subseteq> public_ground_wf_terms - ?Strms"
      and \<sigma>_pgwt_img:
        "subst_range \<sigma> \<subseteq> public_ground_wf_terms"
        "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>) \<subseteq> public_ground_wf_terms"
    using \<sigma>_fresh_pub_img pgwt_is_empty_synth by blast+

  have \<sigma>_img_ground: "ground (subst_range \<sigma>)"
    using \<sigma>_pgwt_img pgwt_ground by auto
  hence \<sigma>_inj: "inj \<sigma>"
    using \<sigma>_bij_dom_img subst_inj_is_bij_betw_dom_img_if_ground_img by auto

  have \<sigma>_ineqs_fv_dom: "\<And>X F. Inequality X F \<in> set S \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> subst_domain \<sigma>"
    using \<sigma>_fv_dom by fastforce

  have \<sigma>_dom_bvars_disj: "\<forall>X F. Inequality X F \<in> set S \<longrightarrow> subst_domain \<sigma> \<inter> set X = {}"
    using ineqs_vars_not_bound \<sigma>_fv_dom by fastforce

  have \<I>'1: "\<forall>X F \<delta>. Inequality X F \<in> set S \<longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> subst_domain \<I>'"
    using \<I>'(3) ineqs_vars_not_bound by fastforce

  have \<I>'2: "\<forall>X F. Inequality X F \<in> set S \<longrightarrow> subst_domain \<I>' \<inter> set X = {}"
    using \<I>'(3) ineqs_vars_not_bound by blast

  have doms_eq: "subst_domain \<I>' = subst_domain \<sigma>" using \<I>'(3) \<sigma>_fv_dom by simp

  have \<sigma>_ineqs_neq: "ineq_model \<sigma> X F" when "Inequality X F \<in> set S" for X F
  proof -
    obtain a::"'fun" where a: "a \<notin> \<Union>(funs_term ` subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>))"
      using exists_fun_notin_funs_terms[OF subterms_union_finite[OF \<sigma>_finite_img]]
      by moura
    hence a': "\<And>T. Fun a T \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>)"
              "\<And>S. Fun a [] \<in> set (Fun a []#S)" "Fun a [] \<notin> Var ` set X"
      by (meson a UN_I term.set_intros(1), auto)

    define t where "t \<equiv> Fun a (Fun a []#map fst F)"
    define t' where "t' \<equiv> Fun a (Fun a []#map snd F)"

    note F_in = that

    have t_fv: "fv t \<union> fv t' \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
      unfolding t_def t'_def by force

    have t_subterms: "subterms t \<union> subterms t' \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<union> {t, t', Fun a []}"
      unfolding t_def t'_def by force

    have "t \<cdot> \<delta> \<cdot> \<sigma> \<noteq> t' \<cdot> \<delta> \<cdot> \<sigma>" when "?P \<delta> X" for \<delta>
    proof -
      have tfr_assms: "Q1 F X \<or> Q2 F X" using tfr_ineq F_in by metis

      have "Q1 F X \<Longrightarrow> \<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. \<exists>c. \<sigma> x = Fun c []"
      proof
        fix x assume "Q1 F X" and x: "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X"
        then obtain a where "\<Gamma> (Var x) = TAtom a" unfolding Q1_def by moura
        hence a: "\<Gamma> (\<sigma> x) = TAtom a" using \<sigma>_wt unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by simp

        have "x \<in> subst_domain \<sigma>" using \<sigma>_ineqs_fv_dom x F_in by auto
        then obtain f T where fT: "\<sigma> x = Fun f T" by (meson \<sigma>_img_ground ground_img_obtain_fun)
        hence "T = []" using \<sigma>_wf_trm a TAtom_term_cases by fastforce
        thus "\<exists>c. \<sigma> x = Fun c []" using fT by metis
      qed
      hence 1: "Q1 F X \<Longrightarrow> \<forall>x \<in> (fv t \<union> fv t') - set X. \<exists>c. \<sigma> x = Fun c []"
        using t_fv by auto

      have 2: "\<not>Q1 F X \<Longrightarrow> Q2 F X" by (metis tfr_assms)

      have 3: "subst_domain \<sigma> \<inter> set X = {}" using \<sigma>_dom_bvars_disj F_in by auto

      have 4: "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>) \<inter> (subterms t \<union> subterms t') = {}"
      proof -
        define M1 where "M1 \<equiv> {t, t', Fun a []}"
        define M2 where "M2 \<equiv> ?Strms"

        have "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<subseteq> M2"
          using F_in unfolding M2_def by force
        moreover have "subterms t \<union> subterms t' \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<union> M1"
          using t_subterms unfolding M1_def by blast
        ultimately have *: "subterms t \<union> subterms t' \<subseteq> M2 \<union> M1"
          by auto

        have "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>) \<inter> M1 = {}"
             "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<sigma>) \<inter> M2 = {}"
          using a' \<sigma>_fresh_pub_img
          unfolding t_def t'_def M1_def M2_def
          by blast+
        thus ?thesis using * by blast
      qed

      have 5: "(fv t \<union> fv t') - subst_domain \<sigma> \<subseteq> set X"
        using \<sigma>_ineqs_fv_dom[OF F_in] t_fv
        by auto

      have 6: "\<forall>\<delta>. ?P \<delta> X \<longrightarrow> t \<cdot> \<delta> \<cdot> \<I>' \<noteq> t' \<cdot> \<delta> \<cdot> \<I>'"
        by (metis t_def t'_def \<I>'(1) F_in ineq_model_singleE ineq_model_single_iff)

      have 7: "fv t \<union> fv t' - set X \<subseteq> subst_domain \<I>'" using \<I>'1 F_in t_fv by force

      have 8: "subst_domain \<I>' \<inter> set X = {}" using \<I>'2 F_in by auto

      have 9: "Q1' t t' X" when "Q1 F X"
        using that t_fv
        unfolding Q1_def Q1'_def t_def t'_def
        by blast

      have 10: "Q2' t t' X" when "Q2 F X" unfolding Q2'_def
      proof (intro allI impI)
        fix f T assume "Fun f T \<in> subterms t \<union> subterms t'"
        moreover {
          assume "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F)"
          hence "T = [] \<or> (\<exists>s\<in>set T. s \<notin> Var ` set X)" by (metis Q2_def that)
        } moreover {
          assume "Fun f T = t" hence "T = [] \<or> (\<exists>s\<in>set T. s \<notin> Var ` set X)"
            unfolding t_def using a'(2,3) by simp
        } moreover {
          assume "Fun f T = t'" hence "T = [] \<or> (\<exists>s\<in>set T. s \<notin> Var ` set X)"
            unfolding t'_def using a'(2,3) by simp
        } moreover {
          assume "Fun f T = Fun a []" hence "T = [] \<or> (\<exists>s\<in>set T. s \<notin> Var ` set X)" by simp
        } ultimately show "T = [] \<or> (\<exists>s\<in>set T. s \<notin> Var ` set X)" using t_subterms by blast
      qed

      note 11 = \<sigma>_subterm_inj \<sigma>_img_ground 3 4 5

      note 12 = 6 7 8 \<I>'(2) doms_eq

      show "t \<cdot> \<delta> \<cdot> \<sigma> \<noteq> t' \<cdot> \<delta> \<cdot> \<sigma>"
        using 1 2 9 10 that sat_ineq_subterm_inj_subst[OF 11 _ 12]
        unfolding Q1'_def Q2'_def by metis
    qed
    thus ?thesis by (metis t_def t'_def ineq_model_singleI ineq_model_single_iff)
  qed

  have \<sigma>_ineqs_fv_dom': "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq> subst_domain \<sigma>"
    when "Inequality X F \<in> set S" and "?P \<delta> X" for F \<delta> X
    using \<sigma>_ineqs_fv_dom[OF that(1)]
  proof (induction F)
    case (Cons g G)
    obtain t t' where g: "g = (t,t')" by (metis surj_pair)
    hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (g#G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)  = fv (t \<cdot> \<delta>) \<union> fv (t' \<cdot> \<delta>) \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
          "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (g#G) = fv t \<union> fv t' \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G"
      by (simp_all add: subst_apply_pairs_def)
    moreover have "fv (t \<cdot> \<delta>) = fv t - subst_domain \<delta>" "fv (t' \<cdot> \<delta>) = fv t' - subst_domain \<delta>"
      using g that(2) by (simp_all add: subst_fv_unfold_ground_img range_vars_alt_def)
    moreover have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq> subst_domain \<sigma>" using Cons by auto
    ultimately show ?case using Cons.prems that(2) by auto
  qed (simp add: subst_apply_pairs_def)

  have \<sigma>_ineqs_ground: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<sigma>) = {}"
    when "Inequality X F \<in> set S" and "?P \<delta> X" for F \<delta> X
    using \<sigma>_ineqs_fv_dom'[OF that]
  proof (induction F)
    case (Cons g G)
    obtain t t' where g: "g = (t,t')" by (metis surj_pair)
    hence "fv (t \<cdot> \<delta>) \<subseteq> subst_domain \<sigma>" "fv (t' \<cdot> \<delta>) \<subseteq> subst_domain \<sigma>"
      using Cons.prems by (auto simp add: subst_apply_pairs_def)
    hence "fv (t \<cdot> \<delta> \<cdot> \<sigma>) = {}" "fv (t' \<cdot> \<delta> \<cdot> \<sigma>) = {}"
      using subst_fv_dom_ground_if_ground_img[OF _ \<sigma>_img_ground] by metis+
    thus ?case using g Cons by (auto simp add: subst_apply_pairs_def)
  qed (simp add: subst_apply_pairs_def)

  from \<sigma>_pgwt_img \<sigma>_ineqs_neq have \<sigma>_deduct: "M \<turnstile>\<^sub>c \<sigma> x" when "x \<in> subst_domain \<sigma>" for x M
    using that pgwt_deducible by fastforce

  { fix M::"('fun,'var) terms"
    have "\<lbrakk>M; S\<rbrakk>\<^sub>c (\<theta> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<I>)"
      using \<open>wf\<^sub>s\<^sub>t {} S\<close> \<open>simple S\<close> S_\<theta>_disj \<sigma>_ineqs_neq \<sigma>_ineqs_fv_dom' \<theta>_vars_S_bvars_disj
    proof (induction S arbitrary: M rule: wf\<^sub>s\<^sub>t_simple_induct)
      case (ConsSnd v S)
      hence S_sat: "\<lbrakk>M; S\<rbrakk>\<^sub>c (\<theta> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<I>)" and "\<theta> v = Var v" by auto
      hence "\<And>M. M \<turnstile>\<^sub>c Var v \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<I>)"
        using \<I>_deduct \<sigma>_deduct
        by (metis ideduct_synth_subst_apply subst_apply_term.simps(1)
                  subst_subst_compose trm_subst_ident')
      thus ?case using strand_sem_append(1)[OF S_sat] by (metis strand_sem_c.simps(1,2))
    next
      case (ConsIneq X F S)
      have dom_disj: "subst_domain \<theta> \<inter> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F = {}"
        using ConsIneq.prems(1) subst_dom_vars_in_subst
        by force
      hence *: "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta> = F" by blast

      have **: "ineq_model \<sigma> X F" by (meson ConsIneq.prems(2) in_set_conv_decomp)

      have "\<And>x. x \<in> vars\<^sub>s\<^sub>t S \<Longrightarrow> x \<in> vars\<^sub>s\<^sub>t (S@[Inequality X F])"
           "\<And>x. x \<in> set S \<Longrightarrow> x \<in> set (S@[Inequality X F])" by auto
      hence IH: "\<lbrakk>M; S\<rbrakk>\<^sub>c (\<theta> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<I>)" by (metis ConsIneq.IH ConsIneq.prems(1,2,3,4))

      have "ineq_model (\<sigma> \<circ>\<^sub>s \<I>) X F"
      proof -
        have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq> subst_domain \<sigma>" when "?P \<delta> X" for \<delta>
          using ConsIneq.prems(3)[OF _ that] by simp
        hence "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> subst_domain \<sigma>"
          using fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_subset ex_P
          by (metis Diff_subset_conv Un_commute)
        thus ?thesis by (metis ineq_model_ground_subst[OF _ \<sigma>_img_ground **])
      qed
      hence "ineq_model (\<theta> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<I>) X F"
        using * ineq_model_subst' subst_compose_assoc ConsIneq.prems(4)
        by (metis UnCI list.set_intros(1) set_append)
      thus ?case using IH by (auto simp add: ineq_model_def)
    qed auto
  }
  moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<I>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<I>))"
    by (metis wt_subst_compose \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<close> \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>\<close> \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<close>,
        metis assms(4) \<I>_wf_trm \<sigma>_wf_trm wf_trm_subst subst_img_comp_subset')
  ultimately show ?thesis
    using interpretation_comp(1)[OF \<open>interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<close>, of "\<theta> \<circ>\<^sub>s \<sigma>"]
          subst_idem_support[OF \<open>subst_idem \<theta>\<close>, of "\<sigma> \<circ>\<^sub>s \<I>"] subst_compose_assoc
    unfolding constr_sem_c_def by metis
qed
end


subsubsection \<open>Theorem: Type-flaw resistant constraints are well-typed satisfiable (composition-only)\<close>
text \<open>
  There exists well-typed models of satisfiable type-flaw resistant constraints in the
  semantics where the intruder is limited to composition only (i.e., he cannot perform
  decomposition/analysis of deducible messages).
\<close>
theorem wt_attack_if_tfr_attack:
  assumes "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and "\<I> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<rangle>"
    and "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>"
    and "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
    and "tfr\<^sub>s\<^sub>t S"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
  obtains \<I>\<^sub>\<tau> where "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>"
    and "\<I>\<^sub>\<tau> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<rangle>"
    and "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
proof -
  have tfr: "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    using assms(5,6) unfolding tfr\<^sub>s\<^sub>t_def by metis+
  obtain S' \<theta>' where *: "simple S'" "(S,\<theta>) \<leadsto>\<^sup>* (S',\<theta>')" "\<lbrakk>{}; S'\<rbrakk>\<^sub>c \<I>"
    using LI_completeness[OF assms(3,2)] unfolding constr_sem_c_def
    by (meson term.order_refl)
  have **: "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S' \<theta>'" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>'" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S')" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>')"
    using LI_preserves_welltypedness[OF *(2) assms(3,4,7) tfr]
          LI_preserves_wellformedness[OF *(2) assms(3)]
          LI_preserves_tfr[OF *(2) assms(3,4,7) tfr]
    by metis+

  define A where "A \<equiv> {x \<in> vars\<^sub>s\<^sub>t S'. \<exists>X F. Inequality X F \<in> set S' \<and> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<and> x \<notin> set X}"
  define B where "B \<equiv> UNIV - A"

  let ?\<I> = "rm_vars B \<I>"

  have gr\<I>: "ground (subst_range \<I>)" "ground (subst_range ?\<I>)"
    using assms(1) rm_vars_img_subset[of B \<I>] by (auto simp add: subst_domain_def)

  { fix X F
    assume "Inequality X F \<in> set S'"
    hence *: "ineq_model \<I> X F"
      using strand_sem_c_imp_ineq_model[OF *(3)]
      by (auto simp del: subst_range.simps)
    hence "ineq_model ?\<I> X F"
    proof -
      { fix \<delta>
        assume 1: "subst_domain \<delta> = set X" "ground (subst_range \<delta>)"
            and 2: "list_ex (\<lambda>f. fst f \<cdot> \<delta> \<circ>\<^sub>s \<I> \<noteq> snd f \<cdot> \<delta> \<circ>\<^sub>s \<I>) F"
        have "list_ex (\<lambda>f. fst f \<cdot> \<delta> \<circ>\<^sub>s rm_vars B \<I> \<noteq> snd f \<cdot> \<delta> \<circ>\<^sub>s rm_vars B \<I>) F" using 2
        proof (induction F)
          case (Cons g G)
          obtain t t' where g: "g = (t,t')" by (metis surj_pair)
          thus ?case
            using Cons Unifier_ground_rm_vars[OF gr\<I>(1), of "t \<cdot> \<delta>" B "t' \<cdot> \<delta>"]
            by auto
        qed simp
      } thus ?thesis using * unfolding ineq_model_def by simp
    qed
  } moreover have "subst_domain \<I> = UNIV" using assms(1) by metis
  hence "subst_domain ?\<I> = A" using rm_vars_dom[of B \<I>] B_def by blast
  ultimately obtain \<I>\<^sub>\<tau> where
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "\<I>\<^sub>\<tau> \<Turnstile>\<^sub>c \<langle>S', \<theta>'\<rangle>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
    using wt_sat_if_simple[OF *(1) **(1,2,5,4) _ gr\<I>(2) _ **(3)] A_def
    by (auto simp del: subst_range.simps)
  thus ?thesis using that LI_soundness[OF assms(3) *(2)] by metis
qed

text \<open>
  Contra-positive version: if a type-flaw resistant constraint does not have a well-typed model
  then it is unsatisfiable
\<close>
corollary secure_if_wt_secure:
  assumes "\<not>(\<exists>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> (\<I>\<^sub>\<tau> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<rangle>) \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>)"
  and     "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "tfr\<^sub>s\<^sub>t S"
  and     "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
  shows "\<not>(\<exists>\<I>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<rangle>))"
using wt_attack_if_tfr_attack[OF _ _ assms(2,3,4,5,6)] assms(1) by metis

end


subsection \<open>Lifting the Composition-Only Typing Result to the Full Intruder Model\<close>
context typed_model
begin

subsubsection \<open>Analysis Invariance\<close>
definition (in typed_model) Ana_invar_subst where
  "Ana_invar_subst \<M> \<equiv>
    (\<forall>f T K M \<delta>. Fun f T \<in> (subterms\<^sub>s\<^sub>e\<^sub>t \<M>) \<longrightarrow>
                 Ana (Fun f T) = (K, M) \<longrightarrow> Ana (Fun f T \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>))"

lemma (in typed_model) Ana_invar_subst_subset:
  assumes "Ana_invar_subst M" "N \<subseteq> M"
  shows "Ana_invar_subst N"
using assms unfolding Ana_invar_subst_def by blast

lemma (in typed_model) Ana_invar_substD:
  assumes "Ana_invar_subst \<M>"
  and "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t \<M>" "Ana (Fun f T) = (K, M)"
  shows "Ana (Fun f T \<cdot> \<I>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>)"
using assms Ana_invar_subst_def by blast

end


subsubsection \<open>Preliminary Definitions\<close>
text \<open>Strands extended with "decomposition steps"\<close>
datatype (funs\<^sub>e\<^sub>s\<^sub>t\<^sub>p: 'a, vars\<^sub>e\<^sub>s\<^sub>t\<^sub>p: 'b) extstrand_step =
  Step   "('a,'b) strand_step"
| Decomp "('a,'b) term"

context typed_model
begin

context
begin
private fun trms\<^sub>e\<^sub>s\<^sub>t\<^sub>p where
  "trms\<^sub>e\<^sub>s\<^sub>t\<^sub>p (Step x) = trms\<^sub>s\<^sub>t\<^sub>p x"
| "trms\<^sub>e\<^sub>s\<^sub>t\<^sub>p (Decomp t) = {t}"

private abbreviation trms\<^sub>e\<^sub>s\<^sub>t where "trms\<^sub>e\<^sub>s\<^sub>t S \<equiv> \<Union>(trms\<^sub>e\<^sub>s\<^sub>t\<^sub>p ` set S)"

private type_synonym ('a,'b) extstrand = "('a,'b) extstrand_step list"
private type_synonym ('a,'b) extstrands = "('a,'b) extstrand set"

private definition decomp::"('fun,'var) term \<Rightarrow> ('fun,'var) strand" where
  "decomp t \<equiv> (case (Ana t) of (K,T) \<Rightarrow> send\<langle>t\<rangle>\<^sub>s\<^sub>t#map Send K@map Receive T)"

private fun to_st where
  "to_st [] = []"
| "to_st (Step x#S) = x#(to_st S)"
| "to_st (Decomp t#S) = (decomp t)@(to_st S)"

private fun to_est where
  "to_est [] = []"
| "to_est (x#S) = Step x#to_est S"

private abbreviation "ik\<^sub>e\<^sub>s\<^sub>t A \<equiv> ik\<^sub>s\<^sub>t (to_st A)"
private abbreviation "wf\<^sub>e\<^sub>s\<^sub>t V A \<equiv> wf\<^sub>s\<^sub>t V (to_st A)"
private abbreviation "assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<equiv> assignment_rhs\<^sub>s\<^sub>t (to_st A)"
private abbreviation "vars\<^sub>e\<^sub>s\<^sub>t A \<equiv> vars\<^sub>s\<^sub>t (to_st A)"
private abbreviation "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t A \<equiv> wfrestrictedvars\<^sub>s\<^sub>t (to_st A)"
private abbreviation "bvars\<^sub>e\<^sub>s\<^sub>t A \<equiv> bvars\<^sub>s\<^sub>t (to_st A)"
private abbreviation "fv\<^sub>e\<^sub>s\<^sub>t A \<equiv> fv\<^sub>s\<^sub>t (to_st A)"
private abbreviation "funs\<^sub>e\<^sub>s\<^sub>t A \<equiv> funs\<^sub>s\<^sub>t (to_st A)"

private definition wf\<^sub>s\<^sub>t\<^sub>s'::"('fun,'var) strands \<Rightarrow> ('fun,'var) extstrand \<Rightarrow> bool" where
  "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A> \<equiv> (\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>) (dual\<^sub>s\<^sub>t S)) \<and>
                 (\<forall>S \<in> \<S>. \<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}) \<and>
                 (\<forall>S \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t \<A> = {}) \<and>
                 (\<forall>S \<in> \<S>. fv\<^sub>s\<^sub>t (to_st \<A>) \<inter> bvars\<^sub>s\<^sub>t S = {})"

private definition wf\<^sub>s\<^sub>t\<^sub>s::"('fun,'var) strands \<Rightarrow> bool" where
  "wf\<^sub>s\<^sub>t\<^sub>s \<S> \<equiv> (\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t {} (dual\<^sub>s\<^sub>t S)) \<and> (\<forall>S \<in> \<S>. \<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {})"

private inductive well_analyzed::"('fun,'var) extstrand \<Rightarrow> bool" where
  Nil[simp]: "well_analyzed []"
| Step: "well_analyzed A \<Longrightarrow> well_analyzed (A@[Step x])"
| Decomp: "\<lbrakk>well_analyzed A; t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) - (Var ` \<V>)\<rbrakk>
    \<Longrightarrow> well_analyzed (A@[Decomp t])"

private fun subst_apply_extstrandstep (infix "\<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p" 51) where
  "subst_apply_extstrandstep (Step x) \<theta> = Step (x \<cdot>\<^sub>s\<^sub>t\<^sub>p \<theta>)"
| "subst_apply_extstrandstep (Decomp t) \<theta> = Decomp (t \<cdot> \<theta>)"

private lemma subst_apply_extstrandstep'_simps[simp]:
  "(Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta> = Step (send\<langle>t \<cdot> \<theta>\<rangle>\<^sub>s\<^sub>t)"
  "(Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta> = Step (receive\<langle>t \<cdot> \<theta>\<rangle>\<^sub>s\<^sub>t)"
  "(Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta> = Step (\<langle>a: (t \<cdot> \<theta>) \<doteq> (t' \<cdot> \<theta>)\<rangle>\<^sub>s\<^sub>t)"
  "(Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta> = Step (\<forall>X\<langle>\<or>\<noteq>: (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)\<rangle>\<^sub>s\<^sub>t)"
by simp_all

private lemma vars\<^sub>e\<^sub>s\<^sub>t\<^sub>p_subst_apply_simps[simp]:
  "vars\<^sub>e\<^sub>s\<^sub>t\<^sub>p ((Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>)"
  "vars\<^sub>e\<^sub>s\<^sub>t\<^sub>p ((Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>)"
  "vars\<^sub>e\<^sub>s\<^sub>t\<^sub>p ((Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta>) = fv (t \<cdot> \<theta>) \<union> fv (t' \<cdot> \<theta>)"
  "vars\<^sub>e\<^sub>s\<^sub>t\<^sub>p ((Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)) \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta>) = set X \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<theta>)"
by auto

private definition subst_apply_extstrand (infix "\<cdot>\<^sub>e\<^sub>s\<^sub>t" 51) where "S \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> \<equiv> map (\<lambda>x. x \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta>) S"

private abbreviation update\<^sub>s\<^sub>t::"('fun,'var) strands \<Rightarrow> ('fun,'var) strand \<Rightarrow> ('fun,'var) strands"
where
  "update\<^sub>s\<^sub>t \<S> S \<equiv> (case S of Nil \<Rightarrow> \<S> - {S} | Cons _ S' \<Rightarrow> insert S' (\<S> - {S}))"

private inductive_set decomps\<^sub>e\<^sub>s\<^sub>t::
  "('fun,'var) terms \<Rightarrow> ('fun,'var) terms \<Rightarrow> ('fun,'var) subst \<Rightarrow> ('fun,'var) extstrands"
(* \<M>: intruder knowledge
   \<N>: additional messages
*)
for \<M> and \<N> and \<I> where
  Nil: "[] \<in> decomps\<^sub>e\<^sub>s\<^sub>t \<M> \<N> \<I>"
| Decomp: "\<lbrakk>\<D> \<in> decomps\<^sub>e\<^sub>s\<^sub>t \<M> \<N> \<I>; Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<M> \<union> \<N>);
            Ana (Fun f T) = (K,M); M \<noteq> [];
            (\<M> \<union> ik\<^sub>e\<^sub>s\<^sub>t \<D>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c Fun f T \<cdot> \<I>;
            \<And>k. k \<in> set K \<Longrightarrow> (\<M> \<union> ik\<^sub>e\<^sub>s\<^sub>t \<D>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>\<rbrakk>
            \<Longrightarrow> \<D>@[Decomp (Fun f T)] \<in> decomps\<^sub>e\<^sub>s\<^sub>t \<M> \<N> \<I>"

private fun decomp_rm\<^sub>e\<^sub>s\<^sub>t::"('fun,'var) extstrand \<Rightarrow> ('fun,'var) extstrand" where
  "decomp_rm\<^sub>e\<^sub>s\<^sub>t [] = []"
| "decomp_rm\<^sub>e\<^sub>s\<^sub>t (Decomp t#S) = decomp_rm\<^sub>e\<^sub>s\<^sub>t S"
| "decomp_rm\<^sub>e\<^sub>s\<^sub>t (Step x#S) = Step x#(decomp_rm\<^sub>e\<^sub>s\<^sub>t S)"

private inductive sem\<^sub>e\<^sub>s\<^sub>t_d::"('fun,'var) terms \<Rightarrow> ('fun,'var) subst \<Rightarrow> ('fun,'var) extstrand \<Rightarrow> bool"
where
  Nil[simp]: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> []"
| Send: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> S \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t S \<union> M\<^sub>0) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I> \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> (S@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
| Receive: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> S \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> (S@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
| Equality: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> S \<Longrightarrow> t \<cdot> \<I> = t' \<cdot> \<I> \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> (S@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)])"
| Inequality: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> S
    \<Longrightarrow> ineq_model \<I> X F
    \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> (S@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)])"
| Decompose: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> S \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t S \<union> M\<^sub>0) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I> \<Longrightarrow> Ana t = (K, M)
    \<Longrightarrow> (\<And>k. k \<in> set K \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t S \<union> M\<^sub>0) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> k \<cdot> \<I>) \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> (S@[Decomp t])"

private inductive sem\<^sub>e\<^sub>s\<^sub>t_c::"('fun,'var) terms \<Rightarrow> ('fun,'var) subst \<Rightarrow> ('fun,'var) extstrand \<Rightarrow> bool"
where
  Nil[simp]: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> []"
| Send: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> S \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t S \<union> M\<^sub>0) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I> \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> (S@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
| Receive: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> S \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> (S@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
| Equality: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> S \<Longrightarrow> t \<cdot> \<I> = t' \<cdot> \<I> \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> (S@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)])"
| Inequality: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> S
    \<Longrightarrow> ineq_model \<I> X F
    \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> (S@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)])"
| Decompose: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> S \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t S \<union> M\<^sub>0) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I> \<Longrightarrow> Ana t = (K, M)
    \<Longrightarrow> (\<And>k. k \<in> set K \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t S \<union> M\<^sub>0) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>) \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> (S@[Decomp t])"


subsubsection \<open>Preliminary Lemmata\<close>
private lemma wf\<^sub>s\<^sub>t\<^sub>s_wf\<^sub>s\<^sub>t\<^sub>s':
  "wf\<^sub>s\<^sub>t\<^sub>s \<S> = wf\<^sub>s\<^sub>t\<^sub>s' \<S> []"
by (simp add: wf\<^sub>s\<^sub>t\<^sub>s_def wf\<^sub>s\<^sub>t\<^sub>s'_def)

private lemma decomp_ik:
  assumes "Ana t = (K,M)"
  shows "ik\<^sub>s\<^sub>t (decomp t) = set M"
using ik_rcv_map[of _ M] ik_rcv_map'[of _ M]
by (auto simp add: decomp_def inv_def assms)

private lemma decomp_assignment_rhs_empty:
  assumes "Ana t = (K,M)"
  shows "assignment_rhs\<^sub>s\<^sub>t (decomp t) = {}"
by (auto simp add: decomp_def inv_def assms)

private lemma decomp_tfr\<^sub>s\<^sub>t\<^sub>p:
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p (decomp t)"
by (auto simp add: decomp_def list_all_def)

private lemma trms\<^sub>e\<^sub>s\<^sub>t_ikI:
  "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<Longrightarrow> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>e\<^sub>s\<^sub>t A)"
proof (induction A rule: to_st.induct)
  case (2 x S) thus ?case by (cases x) auto
next
  case (3 t' A)
  obtain K M where Ana: "Ana t' = (K,M)" by (metis surj_pair)
  show ?case using 3 decomp_ik[OF Ana] Ana_subterm[OF Ana] by auto
qed simp

private lemma trms\<^sub>e\<^sub>s\<^sub>t_ik_assignment_rhsI:
  "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<Longrightarrow> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>e\<^sub>s\<^sub>t A)"
proof (induction A rule: to_st.induct)
  case (2 x S) thus ?case
  proof (cases x)
    case (Equality ac t t') thus ?thesis using 2 by (cases ac) auto
  qed auto
next
  case (3 t' A)
  obtain K M where Ana: "Ana t' = (K,M)" by (metis surj_pair)
  show ?case
    using 3 decomp_ik[OF Ana] decomp_assignment_rhs_empty[OF Ana] Ana_subterm[OF Ana]
    by auto
qed simp

private lemma trms\<^sub>e\<^sub>s\<^sub>t_ik_subtermsI:
  assumes "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A)"
  shows "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>e\<^sub>s\<^sub>t A)"
proof -
  obtain t' where "t' \<in> ik\<^sub>e\<^sub>s\<^sub>t A" "t \<sqsubseteq> t'" using trms\<^sub>e\<^sub>s\<^sub>t_ikI assms by auto
  thus ?thesis by (meson contra_subsetD in_subterms_subset_Union trms\<^sub>e\<^sub>s\<^sub>t_ikI)
qed

private lemma trms\<^sub>e\<^sub>s\<^sub>tD:
  assumes "t \<in> trms\<^sub>e\<^sub>s\<^sub>t A"
  shows "t \<in> trms\<^sub>s\<^sub>t (to_st A)"
using assms
proof (induction A)
  case (Cons a A)
  obtain K M where Ana: "Ana t = (K,M)" by (metis surj_pair)
  hence "t \<in> trms\<^sub>s\<^sub>t (decomp t)" unfolding decomp_def by force
  thus ?case using Cons.IH Cons.prems by (cases a) auto
qed simp

private lemma subst_apply_extstrand_nil[simp]:
  "[] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> = []"
by (simp add: subst_apply_extstrand_def)

private lemma subst_apply_extstrand_singleton[simp]:
  "[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> = [Step (Receive (t \<cdot> \<theta>))]"
  "[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> = [Step (Send (t \<cdot> \<theta>))]"
  "[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> = [Step (Equality a (t \<cdot> \<theta>) (t' \<cdot> \<theta>))]"
  "[Decomp t] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> = [Decomp (t \<cdot> \<theta>)]"
unfolding subst_apply_extstrand_def by auto

private lemma extstrand_subst_hom:
  "(S@S') \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> = (S \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>)@(S' \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>)" "(x#S) \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta> = (x \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta>)#(S \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>)"
unfolding subst_apply_extstrand_def by auto

private lemma decomp_vars:
  "wfrestrictedvars\<^sub>s\<^sub>t (decomp t) = fv t" "vars\<^sub>s\<^sub>t (decomp t) = fv t" "bvars\<^sub>s\<^sub>t (decomp t) = {}"
  "fv\<^sub>s\<^sub>t (decomp t) = fv t"
proof -
  obtain K M where Ana: "Ana t = (K,M)" by (metis surj_pair)
  hence "decomp t = send\<langle>t\<rangle>\<^sub>s\<^sub>t#map Send K@map Receive M"
    unfolding decomp_def by simp
  moreover have "\<Union>(set (map fv K)) = fv\<^sub>s\<^sub>e\<^sub>t (set K)" "\<Union>(set (map fv M)) = fv\<^sub>s\<^sub>e\<^sub>t (set M)" by auto
  moreover have "fv\<^sub>s\<^sub>e\<^sub>t (set K) \<subseteq> fv t" "fv\<^sub>s\<^sub>e\<^sub>t (set M) \<subseteq> fv t"
    using Ana_subterm[OF Ana(1)] Ana_keys_fv[OF Ana(1)]
    by (simp_all add: UN_least psubsetD subtermeq_vars_subset)
  ultimately show
      "wfrestrictedvars\<^sub>s\<^sub>t (decomp t) = fv t" "vars\<^sub>s\<^sub>t (decomp t) = fv t" "bvars\<^sub>s\<^sub>t (decomp t) = {}"
      "fv\<^sub>s\<^sub>t (decomp t) = fv t"
    by auto
qed

private lemma bvars\<^sub>e\<^sub>s\<^sub>t_cons: "bvars\<^sub>e\<^sub>s\<^sub>t (x#X) = bvars\<^sub>e\<^sub>s\<^sub>t [x] \<union> bvars\<^sub>e\<^sub>s\<^sub>t X"
by (cases x) auto

private lemma bvars\<^sub>e\<^sub>s\<^sub>t_append: "bvars\<^sub>e\<^sub>s\<^sub>t (A@B) = bvars\<^sub>e\<^sub>s\<^sub>t A \<union> bvars\<^sub>e\<^sub>s\<^sub>t B"
proof (induction A)
  case (Cons x A) thus ?case using bvars\<^sub>e\<^sub>s\<^sub>t_cons[of x "A@B"] bvars\<^sub>e\<^sub>s\<^sub>t_cons[of x A] by force
qed simp

private lemma fv\<^sub>e\<^sub>s\<^sub>t_cons: "fv\<^sub>e\<^sub>s\<^sub>t (x#X) = fv\<^sub>e\<^sub>s\<^sub>t [x] \<union> fv\<^sub>e\<^sub>s\<^sub>t X"
by (cases x) auto

private lemma fv\<^sub>e\<^sub>s\<^sub>t_append: "fv\<^sub>e\<^sub>s\<^sub>t (A@B) = fv\<^sub>e\<^sub>s\<^sub>t A \<union> fv\<^sub>e\<^sub>s\<^sub>t B"
proof (induction A)
  case (Cons x A) thus ?case using fv\<^sub>e\<^sub>s\<^sub>t_cons[of x "A@B"] fv\<^sub>e\<^sub>s\<^sub>t_cons[of x A] by auto
qed simp

private lemma bvars_decomp: "bvars\<^sub>e\<^sub>s\<^sub>t (A@[Decomp t]) = bvars\<^sub>e\<^sub>s\<^sub>t A" "bvars\<^sub>e\<^sub>s\<^sub>t (Decomp t#A) = bvars\<^sub>e\<^sub>s\<^sub>t A"
using bvars\<^sub>e\<^sub>s\<^sub>t_append decomp_vars(3) by fastforce+

private lemma bvars_decomp_rm: "bvars\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) = bvars\<^sub>e\<^sub>s\<^sub>t A"
using bvars_decomp by (induct A rule: decomp_rm\<^sub>e\<^sub>s\<^sub>t.induct) simp_all+

private lemma fv_decomp_rm: "fv\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<subseteq> fv\<^sub>e\<^sub>s\<^sub>t A"
by (induct A rule: decomp_rm\<^sub>e\<^sub>s\<^sub>t.induct) auto

private lemma ik_assignment_rhs_decomp_fv:
  assumes "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
  shows "fv\<^sub>e\<^sub>s\<^sub>t (A@[Decomp t]) = fv\<^sub>e\<^sub>s\<^sub>t A"
proof -
  have "fv\<^sub>e\<^sub>s\<^sub>t (A@[Decomp t]) = fv\<^sub>e\<^sub>s\<^sub>t A \<union> fv t" using fv\<^sub>e\<^sub>s\<^sub>t_append decomp_vars by simp
  moreover have "fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<subseteq> fv\<^sub>e\<^sub>s\<^sub>t A" by force
  moreover have "fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
    using fv_subset_subterms[OF assms(1)] by simp
  ultimately show ?thesis by blast
qed

private lemma wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_decomp_rm\<^sub>e\<^sub>s\<^sub>t_subset:
  "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<subseteq> wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t A"
by (induct A rule: decomp_rm\<^sub>e\<^sub>s\<^sub>t.induct) auto+

private lemma wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_eq_wfrestrictedvars\<^sub>s\<^sub>t:
  "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t A = wfrestrictedvars\<^sub>s\<^sub>t (to_st A)"
by simp

private lemma decomp_set_unfold:
  assumes "Ana t = (K, M)"
  shows "set (decomp t) = {send\<langle>t\<rangle>\<^sub>s\<^sub>t} \<union> (Send ` set K) \<union> (Receive ` set M)"
using assms unfolding decomp_def by auto

private lemma ik\<^sub>e\<^sub>s\<^sub>t_finite: "finite (ik\<^sub>e\<^sub>s\<^sub>t A)"
by (rule finite_ik\<^sub>s\<^sub>t)

private lemma assignment_rhs\<^sub>e\<^sub>s\<^sub>t_finite: "finite (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
by (rule finite_assignment_rhs\<^sub>s\<^sub>t)

private lemma to_est_append: "to_est (A@B) = to_est A@to_est B"
by (induct A rule: to_est.induct) auto

private lemma to_st_to_est_inv: "to_st (to_est A) = A"
by (induct A rule: to_est.induct) auto

private lemma to_st_append: "to_st (A@B) = (to_st A)@(to_st B)"
by (induct A rule: to_st.induct) auto

private lemma to_st_cons: "to_st (a#B) = (to_st [a])@(to_st B)"
using to_st_append[of "[a]" B] by simp

private lemma wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_split:
  "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t (x#S) = wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t [x] \<union> wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t S"
  "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t (S@S') = wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t S \<union> wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t S'"
using to_st_cons[of x S] to_st_append[of S S'] by auto

private lemma ik\<^sub>e\<^sub>s\<^sub>t_append: "ik\<^sub>e\<^sub>s\<^sub>t (A@B) = ik\<^sub>e\<^sub>s\<^sub>t A \<union> ik\<^sub>e\<^sub>s\<^sub>t B"
by (metis ik_append to_st_append)

private lemma assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append:
  "assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@B) = assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t B"
by (metis assignment_rhs_append to_st_append)

private lemma ik\<^sub>e\<^sub>s\<^sub>t_cons: "ik\<^sub>e\<^sub>s\<^sub>t (a#A) = ik\<^sub>e\<^sub>s\<^sub>t [a] \<union> ik\<^sub>e\<^sub>s\<^sub>t A"
by (metis ik_append to_st_cons)

private lemma ik\<^sub>e\<^sub>s\<^sub>t_append_subst:
  "ik\<^sub>e\<^sub>s\<^sub>t (A@B \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>) = ik\<^sub>e\<^sub>s\<^sub>t (A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>) \<union> ik\<^sub>e\<^sub>s\<^sub>t (B \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>)"
  "ik\<^sub>e\<^sub>s\<^sub>t (A@B) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
by (metis ik\<^sub>e\<^sub>s\<^sub>t_append extstrand_subst_hom(1), simp add: image_Un to_st_append)

private lemma assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append_subst:
  "assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@B \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>) = assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t (B \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>)"
  "assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@B) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
by (metis assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append extstrand_subst_hom(1), use assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append in blast)

private lemma ik\<^sub>e\<^sub>s\<^sub>t_cons_subst:
  "ik\<^sub>e\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>) = ik\<^sub>e\<^sub>s\<^sub>t ([a \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<theta>]) \<union> ik\<^sub>e\<^sub>s\<^sub>t (A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<theta>)"
  "ik\<^sub>e\<^sub>s\<^sub>t (a#A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = (ik\<^sub>e\<^sub>s\<^sub>t [a] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
by (metis ik\<^sub>e\<^sub>s\<^sub>t_cons extstrand_subst_hom(2), metis image_Un ik\<^sub>e\<^sub>s\<^sub>t_cons)

private lemma decomp_rm\<^sub>e\<^sub>s\<^sub>t_append: "decomp_rm\<^sub>e\<^sub>s\<^sub>t (S@S') = (decomp_rm\<^sub>e\<^sub>s\<^sub>t S)@(decomp_rm\<^sub>e\<^sub>s\<^sub>t S')"
by (induct S rule: decomp_rm\<^sub>e\<^sub>s\<^sub>t.induct) auto

private lemma decomp_rm\<^sub>e\<^sub>s\<^sub>t_single[simp]:
  "decomp_rm\<^sub>e\<^sub>s\<^sub>t [Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)] = [Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
  "decomp_rm\<^sub>e\<^sub>s\<^sub>t [Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)] = [Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
  "decomp_rm\<^sub>e\<^sub>s\<^sub>t [Decomp t] = []"
by auto

private lemma decomp_rm\<^sub>e\<^sub>s\<^sub>t_ik_subset: "ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t S) \<subseteq> ik\<^sub>e\<^sub>s\<^sub>t S"
proof (induction S rule: decomp_rm\<^sub>e\<^sub>s\<^sub>t.induct)
  case (3 x S) thus ?case by (cases x) auto
qed auto

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_ik_subset: "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I> \<Longrightarrow> ik\<^sub>e\<^sub>s\<^sub>t D \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (M \<union> N)"
proof (induction D rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
  case (Decomp D f T K M')
  have "ik\<^sub>s\<^sub>t (decomp (Fun f T)) \<subseteq> subterms (Fun f T)"
       "ik\<^sub>s\<^sub>t (decomp (Fun f T)) = ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun f T)]"
    using decomp_ik[OF Decomp.hyps(3)] Ana_subterm[OF Decomp.hyps(3)]
    by auto
  hence "ik\<^sub>s\<^sub>t (to_st [Decomp (Fun f T)]) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (M \<union> N)"
    using in_subterms_subset_Union[OF Decomp.hyps(2)]
    by blast
  thus ?case using ik\<^sub>e\<^sub>s\<^sub>t_append[of D "[Decomp (Fun f T)]"] using Decomp.IH by auto
qed simp

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_decomp_rm\<^sub>e\<^sub>s\<^sub>t_empty: "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I> \<Longrightarrow> decomp_rm\<^sub>e\<^sub>s\<^sub>t D = []"
by (induct D rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct) (auto simp add: decomp_rm\<^sub>e\<^sub>s\<^sub>t_append)

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_append:
  assumes "A \<in> decomps\<^sub>e\<^sub>s\<^sub>t S N \<I>" "B \<in> decomps\<^sub>e\<^sub>s\<^sub>t S N \<I>"
  shows "A@B \<in> decomps\<^sub>e\<^sub>s\<^sub>t S N \<I>"
using assms(2)
proof (induction B rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
  case Nil show ?case using assms(1) by simp
next
  case (Decomp B f X K T)
  hence "S \<union> ik\<^sub>e\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> S \<union> ik\<^sub>e\<^sub>s\<^sub>t (A@B) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using ik\<^sub>e\<^sub>s\<^sub>t_append by auto
  thus ?case
    using decomps\<^sub>e\<^sub>s\<^sub>t.Decomp[OF Decomp.IH(1) Decomp.hyps(2,3,4)]
          ideduct_synth_mono[OF Decomp.hyps(5)]
          ideduct_synth_mono[OF Decomp.hyps(6)]
    by auto
qed

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_subterms:
  assumes "A' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A') \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (M \<union> N)"
using assms
proof (induction A' rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
  case (Decomp D f X K T)
  hence "Fun f X \<in> subterms\<^sub>s\<^sub>e\<^sub>t (M \<union> N)" by auto
  hence "subterms\<^sub>s\<^sub>e\<^sub>t (set X) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (M \<union> N)"
    using in_subterms_subset_Union[of "Fun f X" "M \<union> N"] params_subterms_Union[of X f]
    by blast
  moreover have "ik\<^sub>s\<^sub>t (to_st [Decomp (Fun f X)]) = set T" using Decomp.hyps(3) decomp_ik by simp
  hence "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>s\<^sub>t (to_st [Decomp (Fun f X)])) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (set X)"
    using Ana_fun_subterm[OF Decomp.hyps(3)] by auto
  ultimately show ?case
    using ik\<^sub>e\<^sub>s\<^sub>t_append[of D "[Decomp (Fun f X)]"] Decomp.IH
    by auto
qed simp

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_assignment_rhs_empty:
  assumes "A' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>"
  shows "assignment_rhs\<^sub>e\<^sub>s\<^sub>t A' = {}"
using assms
by (induction A' rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
   (simp_all add: decomp_assignment_rhs_empty assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append)

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_finite_ik_append:
  assumes "finite M" "M \<subseteq> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>"
  shows "\<exists>D \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>. ik\<^sub>e\<^sub>s\<^sub>t D = (\<Union>m \<in> M. ik\<^sub>e\<^sub>s\<^sub>t m)"
using assms
proof (induction M rule: finite_induct)
  case empty
  moreover have "[] \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>" "ik\<^sub>s\<^sub>t (to_st []) = {}" using decomps\<^sub>e\<^sub>s\<^sub>t.Nil by auto
  ultimately show ?case by blast
next
  case (insert m M)
  then obtain D where "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>" "ik\<^sub>e\<^sub>s\<^sub>t D = (\<Union>m\<in>M. ik\<^sub>s\<^sub>t (to_st m))" by moura
  moreover have "m \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>" using insert.prems(1) by blast
  ultimately show ?case using decomps\<^sub>e\<^sub>s\<^sub>t_append[of D A N \<I> m] ik\<^sub>e\<^sub>s\<^sub>t_append[of D m] by blast
qed

private lemma decomp_snd_exists[simp]: "\<exists>D. decomp t = send\<langle>t\<rangle>\<^sub>s\<^sub>t#D"
by (metis (mono_tags, lifting) decomp_def prod.case surj_pair)

private lemma decomp_nonnil[simp]: "decomp t \<noteq> []"
using decomp_snd_exists[of t] by fastforce

private lemma to_st_nil_inv[dest]: "to_st A = [] \<Longrightarrow> A = []"
by (induct A rule: to_st.induct) auto

private lemma well_analyzedD:
  assumes "well_analyzed A" "Decomp t \<in> set A"
  shows "\<exists>f T. t = Fun f T"
using assms
proof (induction A rule: well_analyzed.induct)
  case (Decomp A t')
  hence "\<exists>f T. t' = Fun f T" by (cases t') auto
  moreover have "Decomp t \<in> set A \<or> t = t'" using Decomp by auto
  ultimately show ?case using Decomp.IH by auto
qed auto

private lemma well_analyzed_inv:
  assumes "well_analyzed (A@[Decomp t])"
  shows "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) - (Var ` \<V>)"
using assms well_analyzed.cases[of "A@[Decomp t]"] by fastforce

private lemma well_analyzed_split_left_single: "well_analyzed (A@[a]) \<Longrightarrow> well_analyzed A"
by (induction "A@[a]" rule: well_analyzed.induct) auto

private lemma well_analyzed_split_left: "well_analyzed (A@B) \<Longrightarrow> well_analyzed A"
proof (induction B rule: List.rev_induct)
  case (snoc b B) thus ?case using well_analyzed_split_left_single[of "A@B" b] by simp
qed simp

private lemma well_analyzed_append:
  assumes "well_analyzed A" "well_analyzed B"
  shows "well_analyzed (A@B)"
using assms(2,1)
proof (induction B rule: well_analyzed.induct)
  case (Step B x) show ?case using well_analyzed.Step[OF Step.IH[OF Step.prems]] by simp
next
  case (Decomp B t) thus ?case
    using well_analyzed.Decomp[OF Decomp.IH[OF Decomp.prems]] ik\<^sub>e\<^sub>s\<^sub>t_append assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append
    by auto
qed simp_all

private lemma well_analyzed_singleton:
  "well_analyzed [Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]" "well_analyzed [Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
  "well_analyzed [Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]" "well_analyzed [Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]"
  "\<not>well_analyzed [Decomp t]"
proof -
  show "well_analyzed [Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]" "well_analyzed [Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
       "well_analyzed [Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]" "well_analyzed [Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]"
    using well_analyzed.Step[OF well_analyzed.Nil]
    by simp_all

  show "\<not>well_analyzed [Decomp t]" using well_analyzed.cases[of "[Decomp t]"] by auto
qed

private lemma well_analyzed_decomp_rm\<^sub>e\<^sub>s\<^sub>t_fv: "well_analyzed A \<Longrightarrow> fv\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) = fv\<^sub>e\<^sub>s\<^sub>t A"
proof
  assume "well_analyzed A" thus "fv\<^sub>e\<^sub>s\<^sub>t A \<subseteq> fv\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A)"
  proof (induction A rule: well_analyzed.induct)
    case Decomp thus ?case using ik_assignment_rhs_decomp_fv decomp_rm\<^sub>e\<^sub>s\<^sub>t_append by auto
  next
    case (Step A x)
    have "fv\<^sub>e\<^sub>s\<^sub>t (A@[Step x]) = fv\<^sub>e\<^sub>s\<^sub>t A \<union> fv\<^sub>s\<^sub>t\<^sub>p x"
         "fv\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t (A@[Step x])) = fv\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> fv\<^sub>s\<^sub>t\<^sub>p x"
      using fv\<^sub>e\<^sub>s\<^sub>t_append decomp_rm\<^sub>e\<^sub>s\<^sub>t_append by auto
    thus ?case using Step by auto
  qed simp
qed (rule fv_decomp_rm)

private lemma sem\<^sub>e\<^sub>s\<^sub>t_d_split_left: assumes "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> (\<A>@\<A>')" shows "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> \<A>"
using assms sem\<^sub>e\<^sub>s\<^sub>t_d.cases by (induction \<A>' rule: List.rev_induct) fastforce+

private lemma sem\<^sub>e\<^sub>s\<^sub>t_d_eq_sem_st: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> \<A> = \<lbrakk>M\<^sub>0; to_st \<A>\<rbrakk>\<^sub>d' \<I>"
proof
  show "\<lbrakk>M\<^sub>0; to_st \<A>\<rbrakk>\<^sub>d' \<I> \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> \<A>"
  proof (induction \<A> arbitrary: M\<^sub>0 rule: List.rev_induct)
    case Nil show ?case using to_st_nil_inv by simp
  next
    case (snoc a \<A>)
    hence IH: "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> \<A>" and *: "\<lbrakk>ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0; to_st [a]\<rbrakk>\<^sub>d' \<I>"
      using to_st_append by (auto simp add: sup.commute)
    thus ?case using snoc
    proof (cases a)
      case (Step b) thus ?thesis
      proof (cases b)
        case (Send t) thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_d.Send[OF IH] * Step by auto
      next
        case (Receive t) thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_d.Receive[OF IH] Step by auto
      next
        case (Equality a t t') thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_d.Equality[OF IH] * Step by auto
      next
        case (Inequality X F) thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_d.Inequality[OF IH] * Step by auto
      qed
    next
      case (Decomp t)
      obtain K M where Ana: "Ana t = (K,M)" by moura
      have "to_st [a] = decomp t" using Decomp by auto
      hence "to_st [a] = send\<langle>t\<rangle>\<^sub>s\<^sub>t#map Send K@map Receive M"
        using Ana unfolding decomp_def by auto
      hence **: "ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" and "\<lbrakk>ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0; map Send K\<rbrakk>\<^sub>d' \<I>"
        using * by auto
      hence "\<And>k. k \<in> set K \<Longrightarrow> ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> k \<cdot> \<I>"
        using *
        by (metis (full_types) strand_sem_d.simps(2) strand_sem_eq_defs(2) strand_sem_Send_split(2))
      thus ?thesis using Decomp sem\<^sub>e\<^sub>s\<^sub>t_d.Decompose[OF IH ** Ana] by metis
    qed
  qed

  show "sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> \<A> \<Longrightarrow> \<lbrakk>M\<^sub>0; to_st \<A>\<rbrakk>\<^sub>d' \<I>"
  proof (induction rule: sem\<^sub>e\<^sub>s\<^sub>t_d.induct)
    case Nil thus ?case by simp
  next
    case (Send M\<^sub>0 \<I> \<A> t) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[send\<langle>t\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]"]
      by (simp add: sup.commute)
  next
    case (Receive M\<^sub>0 \<I> \<A> t) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[receive\<langle>t\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"]
      by (simp add: sup.commute)
  next
    case (Equality M\<^sub>0 \<I> \<A> t t' a) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]"]
      by (simp add: sup.commute)
  next
    case (Inequality M\<^sub>0 \<I> \<A> X F) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]"]
      by (simp add: sup.commute)
  next
    case (Decompose M\<^sub>0 \<I> \<A> t K M)
    have "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); decomp t\<rbrakk>\<^sub>d' \<I>"
    proof -
      have "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); [send\<langle>t\<rangle>\<^sub>s\<^sub>t]\<rbrakk>\<^sub>d' \<I>"
        using Decompose.hyps(2) by (auto simp add: sup.commute)
      moreover have "\<And>k. k \<in> set K \<Longrightarrow> M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> k \<cdot> \<I>"
        using Decompose by (metis sup.commute)
      hence "\<And>k. k \<in> set K \<Longrightarrow> \<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); [Send k]\<rbrakk>\<^sub>d' \<I>" by auto
      hence "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); map Send K\<rbrakk>\<^sub>d' \<I>"
        using strand_sem_Send_map(2)[of K, of "M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" \<I>] strand_sem_eq_defs(2)
        by auto
      moreover have "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); map Receive M\<rbrakk>\<^sub>d' \<I>"
        by (metis strand_sem_Receive_map(2) strand_sem_eq_defs(2))
      ultimately have
          "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); send\<langle>t\<rangle>\<^sub>s\<^sub>t#map Send K@map Receive M\<rbrakk>\<^sub>d' \<I>"
        by auto
      thus ?thesis using Decompose.hyps(3) unfolding decomp_def by auto
    qed
    hence "\<lbrakk>M\<^sub>0; to_st \<A>@decomp t\<rbrakk>\<^sub>d' \<I>"
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "decomp t"] Decompose.IH
      by simp
    thus ?case using to_st_append[of \<A> "[Decomp t]"] by simp
  qed
qed

private lemma sem\<^sub>e\<^sub>s\<^sub>t_c_eq_sem_st: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> \<A> = \<lbrakk>M\<^sub>0; to_st \<A>\<rbrakk>\<^sub>c' \<I>"
proof
  show "\<lbrakk>M\<^sub>0; to_st \<A>\<rbrakk>\<^sub>c' \<I> \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> \<A>"
  proof (induction \<A> arbitrary: M\<^sub>0 rule: List.rev_induct)
    case Nil show ?case using to_st_nil_inv by simp
  next
    case (snoc a \<A>)
    hence IH: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> \<A>" and *: "\<lbrakk>ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0; to_st [a]\<rbrakk>\<^sub>c' \<I>"
      using to_st_append
      by (auto simp add: sup.commute)
    thus ?case using snoc
    proof (cases a)
      case (Step b) thus ?thesis
      proof (cases b)
        case (Send t) thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_c.Send[OF IH] * Step by auto
      next
        case (Receive t) thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_c.Receive[OF IH] Step by auto
      next
        case (Equality t) thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_c.Equality[OF IH] * Step by auto
      next
        case (Inequality t) thus ?thesis using sem\<^sub>e\<^sub>s\<^sub>t_c.Inequality[OF IH] * Step by auto
      qed
    next
      case (Decomp t)
      obtain K M where Ana: "Ana t = (K,M)" by moura
      have "to_st [a] = decomp t" using Decomp by auto
      hence "to_st [a] = send\<langle>t\<rangle>\<^sub>s\<^sub>t#map Send K@map Receive M"
        using Ana unfolding decomp_def by auto
      hence **: "ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>" and "\<lbrakk>ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0; map Send K\<rbrakk>\<^sub>c' \<I>"
        using * by auto
      hence "\<And>k. k \<in> set K \<Longrightarrow> ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>"
        using * strand_sem_Send_split(1) strand_sem_eq_defs(1)
        by auto
      thus ?thesis using Decomp sem\<^sub>e\<^sub>s\<^sub>t_c.Decompose[OF IH ** Ana] by metis
    qed
  qed

  show "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> \<A> \<Longrightarrow> \<lbrakk>M\<^sub>0; to_st \<A>\<rbrakk>\<^sub>c' \<I>"
  proof (induction rule: sem\<^sub>e\<^sub>s\<^sub>t_c.induct)
    case Nil thus ?case by simp
  next
    case (Send M\<^sub>0 \<I> \<A> t) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[send\<langle>t\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]"]
      by (simp add: sup.commute)
  next
    case (Receive M\<^sub>0 \<I> \<A> t) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[receive\<langle>t\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"]
      by (simp add: sup.commute)
  next
    case (Equality M\<^sub>0 \<I> \<A> t t' a) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]"]
      by (simp add: sup.commute)
  next
    case (Inequality M\<^sub>0 \<I> \<A> X F) thus ?case
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "[\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]"]
            to_st_append[of \<A> "[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]"]
      by (auto simp add: sup.commute)
  next
    case (Decompose M\<^sub>0 \<I> \<A> t K M)
    have "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); decomp t\<rbrakk>\<^sub>c' \<I>"
    proof -
      have "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); [send\<langle>t\<rangle>\<^sub>s\<^sub>t]\<rbrakk>\<^sub>c' \<I>"
        using Decompose.hyps(2) by (auto simp add: sup.commute)
      moreover have "\<And>k. k \<in> set K \<Longrightarrow> M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>"
        using Decompose by (metis sup.commute)
      hence "\<And>k. k \<in> set K \<Longrightarrow> \<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); [Send k]\<rbrakk>\<^sub>c' \<I>" by auto
      hence "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); map Send K\<rbrakk>\<^sub>c' \<I>"
        using strand_sem_Send_map(1)[of K, of "M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" \<I>]
              strand_sem_eq_defs(1)
        by auto
      moreover have "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); map Receive M\<rbrakk>\<^sub>c' \<I>"
        by (metis strand_sem_Receive_map(1) strand_sem_eq_defs(1))
      ultimately have
          "\<lbrakk>M\<^sub>0 \<union> ik\<^sub>s\<^sub>t (to_st \<A>); send\<langle>t\<rangle>\<^sub>s\<^sub>t#map Send K@map Receive M\<rbrakk>\<^sub>c' \<I>"
        by auto
      thus ?thesis using Decompose.hyps(3) unfolding decomp_def by auto
    qed
    hence "\<lbrakk>M\<^sub>0; to_st \<A>@decomp t\<rbrakk>\<^sub>c' \<I>"
      using strand_sem_append'[of M\<^sub>0 "to_st \<A>" \<I> "decomp t"] Decompose.IH
      by simp
    thus ?case using to_st_append[of \<A> "[Decomp t]"] by simp
  qed
qed

private lemma sem\<^sub>e\<^sub>s\<^sub>t_c_decomp_rm\<^sub>e\<^sub>s\<^sub>t_deduct_aux:
  assumes "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> A" "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "t \<notin> ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
  shows "ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t"
using assms
proof (induction M\<^sub>0 \<I> A arbitrary: t rule: sem\<^sub>e\<^sub>s\<^sub>t_c.induct)
  case (Send M\<^sub>0 \<I> A t') thus ?case using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append ik\<^sub>e\<^sub>s\<^sub>t_append by auto
next
  case (Receive M\<^sub>0 \<I> A t')
  hence "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "t \<notin> ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append ik\<^sub>e\<^sub>s\<^sub>t_append by auto
  hence IH: "ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t" using Receive.IH by auto
  show ?case using ideduct_mono[OF IH] decomp_rm\<^sub>e\<^sub>s\<^sub>t_append ik\<^sub>e\<^sub>s\<^sub>t_append by auto
next
  case (Equality M\<^sub>0 \<I> A t') thus ?case using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append ik\<^sub>e\<^sub>s\<^sub>t_append by auto
next
  case (Inequality M\<^sub>0 \<I> A t') thus ?case using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append ik\<^sub>e\<^sub>s\<^sub>t_append by auto
next
  case (Decompose M\<^sub>0 \<I> A t' K M t)
  have *: "ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t' \<cdot> \<I>" using Decompose.hyps(2)
  proof (induction rule: intruder_synth_induct)
    case (AxiomC t'')
    moreover {
      assume "t'' \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "t'' \<notin> ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      hence ?case using Decompose.IH by auto
    }
    ultimately show ?case by force
  qed simp

  { fix k assume "k \<in> set K"
    hence "ik\<^sub>e\<^sub>s\<^sub>t A \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>" using Decompose.hyps by auto
    hence "ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> k \<cdot> \<I>"
    proof (induction rule: intruder_synth_induct)
      case (AxiomC t'')
      moreover {
        assume "t'' \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "t'' \<notin> ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
        hence ?case using Decompose.IH by auto
      }
      ultimately show ?case by force
    qed simp
  }
  hence **: "\<And>k. k \<in> set (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>) \<Longrightarrow> ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> k" by auto

  show ?case
  proof (cases "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>")
    case True thus ?thesis using Decompose.IH Decompose.prems(2) decomp_rm\<^sub>e\<^sub>s\<^sub>t_append by auto
  next
    case False
    hence "t \<in> ik\<^sub>s\<^sub>t (decomp t') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using Decompose.prems(1) ik\<^sub>e\<^sub>s\<^sub>t_append by auto
    hence ***: "t \<in> set (M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>)" using Decompose.hyps(3) decomp_ik by auto
    hence "M \<noteq> []" by auto
    hence ****: "Ana (t' \<cdot> \<I>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>)" using Ana_subst[OF Decompose.hyps(3)] by auto

    have "ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t" by (rule intruder_deduct.Decompose[OF * **** ** ***])
    thus ?thesis using ideduct_mono decomp_rm\<^sub>e\<^sub>s\<^sub>t_append by auto
  qed
qed simp

private lemma sem\<^sub>e\<^sub>s\<^sub>t_c_decomp_rm\<^sub>e\<^sub>s\<^sub>t_deduct:
  assumes "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> A" "ik\<^sub>e\<^sub>s\<^sub>t A \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t"
  shows "ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<union> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t"
using assms(2)
proof (induction t rule: intruder_synth_induct)
  case (AxiomC t)
  hence "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<or> t \<in> M\<^sub>0 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by auto
  moreover {
    assume "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "t \<in> ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    hence ?case using ideduct_mono[OF intruder_deduct.Axiom] by auto
  }
  moreover {
    assume "t \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "t \<notin> ik\<^sub>e\<^sub>s\<^sub>t (decomp_rm\<^sub>e\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    hence ?case using sem\<^sub>e\<^sub>s\<^sub>t_c_decomp_rm\<^sub>e\<^sub>s\<^sub>t_deduct_aux[OF assms(1)] by auto
  }
  ultimately show ?case by auto
qed simp

private lemma sem\<^sub>e\<^sub>s\<^sub>t_d_decomp_rm\<^sub>e\<^sub>s\<^sub>t_if_sem\<^sub>e\<^sub>s\<^sub>t_c: "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> A \<Longrightarrow> sem\<^sub>e\<^sub>s\<^sub>t_d M\<^sub>0 \<I> (decomp_rm\<^sub>e\<^sub>s\<^sub>t A)"
proof (induction M\<^sub>0 \<I> A rule: sem\<^sub>e\<^sub>s\<^sub>t_c.induct)
  case (Send M\<^sub>0 \<I> A t)
  thus ?case using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append sem\<^sub>e\<^sub>s\<^sub>t_d.Send[OF Send.IH] sem\<^sub>e\<^sub>s\<^sub>t_c_decomp_rm\<^sub>e\<^sub>s\<^sub>t_deduct by auto
next
  case (Receive t) thus ?case using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append sem\<^sub>e\<^sub>s\<^sub>t_d.Receive by auto
next
  case (Equality M\<^sub>0 \<I> A t)
  thus ?case
    using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append sem\<^sub>e\<^sub>s\<^sub>t_d.Equality[OF Equality.IH] sem\<^sub>e\<^sub>s\<^sub>t_c_decomp_rm\<^sub>e\<^sub>s\<^sub>t_deduct
    by auto
next
  case (Inequality M\<^sub>0 \<I> A t)
  thus ?case
    using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append sem\<^sub>e\<^sub>s\<^sub>t_d.Inequality[OF Inequality.IH] sem\<^sub>e\<^sub>s\<^sub>t_c_decomp_rm\<^sub>e\<^sub>s\<^sub>t_deduct
    by auto
next
  case Decompose thus ?case using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append by auto
qed auto

private lemma sem\<^sub>e\<^sub>s\<^sub>t_c_decomps\<^sub>e\<^sub>s\<^sub>t_append:
  assumes "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> A" "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>) \<I>"
  shows "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> (A@D)"
using assms(2,1)
proof (induction D rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
  case (Decomp D f T K M)
  hence *: "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> (A @ D)" "ik\<^sub>e\<^sub>s\<^sub>t (A@D) \<union> {} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c Fun f T \<cdot> \<I>"
           "\<And>k. k \<in> set K \<Longrightarrow> ik\<^sub>e\<^sub>s\<^sub>t (A @ D) \<union> {} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>"
    using ik\<^sub>e\<^sub>s\<^sub>t_append by auto
  show ?case using sem\<^sub>e\<^sub>s\<^sub>t_c.Decompose[OF *(1,2) Decomp.hyps(3) *(3)] by simp
qed auto

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_preserves_wf:
  assumes "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<I>" "wf\<^sub>e\<^sub>s\<^sub>t V A"
  shows "wf\<^sub>e\<^sub>s\<^sub>t V (A@D)"
using assms
proof (induction D rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
  case (Decomp D f T K M)
  have "wfrestrictedvars\<^sub>s\<^sub>t (decomp (Fun f T)) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
    using decomp_vars fv_subset_subterms[OF Decomp.hyps(2)] by fast
  hence "wfrestrictedvars\<^sub>s\<^sub>t (decomp (Fun f T)) \<subseteq> wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t A"
    using ik\<^sub>s\<^sub>t_assignment_rhs\<^sub>s\<^sub>t_wfrestrictedvars_subset[of "to_st A"] by blast
  hence "wfrestrictedvars\<^sub>s\<^sub>t (decomp (Fun f T)) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (to_st (A@D)) \<union> V"
    using to_st_append[of A D] strand_vars_split(2)[of "to_st A" "to_st D"]
    by (metis le_supI1)
  thus ?case
    using wf_append_suffix[OF Decomp.IH[OF Decomp.prems], of "decomp (Fun f T)"]
          to_st_append[of "A@D" "[Decomp (Fun f T)]"]
    by auto
qed auto

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_preserves_model_c:
  assumes "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<I>" "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> A"
  shows "sem\<^sub>e\<^sub>s\<^sub>t_c M\<^sub>0 \<I> (A@D)"
using assms
proof (induction D rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
  case (Decomp D f T K M) show ?case
    using sem\<^sub>e\<^sub>s\<^sub>t_c.Decompose[OF Decomp.IH[OF Decomp.prems] _ Decomp.hyps(3)]
          Decomp.hyps(5,6) ideduct_synth_mono ik\<^sub>e\<^sub>s\<^sub>t_append
    by (metis (mono_tags, lifting) List.append_assoc image_Un sup_ge1)
qed auto

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_exist_aux:
  assumes "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "M \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<turnstile> t" "\<not>(M \<union> (ik\<^sub>e\<^sub>s\<^sub>t D) \<turnstile>\<^sub>c t)"
  obtains D' where
    "D@D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@D') \<turnstile>\<^sub>c t" "M \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<subset> M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@D')"
proof -
  have "\<exists>D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>. M \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<turnstile>\<^sub>c t" using assms(2)
  proof (induction t rule: intruder_deduct_induct)
    case (Compose X f)
    from Compose.IH have "\<exists>D \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>. \<forall>x \<in> set X. M \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<turnstile>\<^sub>c x"
    proof (induction X)
      case (Cons t X)
      then obtain D' D'' where
          D': "D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "M \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<turnstile>\<^sub>c t" and
          D'': "D'' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "\<forall>x \<in> set X. M \<union> ik\<^sub>e\<^sub>s\<^sub>t D'' \<turnstile>\<^sub>c x"
        by moura
      hence "M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<turnstile>\<^sub>c t" "\<forall>x \<in> set X. M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<turnstile>\<^sub>c x"
        by (auto intro: ideduct_synth_mono simp add: ik\<^sub>e\<^sub>s\<^sub>t_append)
      thus ?case using decomps\<^sub>e\<^sub>s\<^sub>t_append[OF D'(1) D''(1)] by (metis set_ConsD)
    qed (auto intro: decomps\<^sub>e\<^sub>s\<^sub>t.Nil)
    thus ?case using intruder_synth.ComposeC[OF Compose.hyps(1,2)] by metis
  next
    case (Decompose t K T t\<^sub>i)
    have "\<exists>D \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>. \<forall>k \<in> set K. M \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<turnstile>\<^sub>c k" using Decompose.IH
    proof (induction K)
      case (Cons t X)
      then obtain D' D'' where
          D': "D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "M \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<turnstile>\<^sub>c t" and
          D'': "D'' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "\<forall>x \<in> set X. M \<union> ik\<^sub>e\<^sub>s\<^sub>t D'' \<turnstile>\<^sub>c x"
        using assms(1) by moura
      hence "M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<turnstile>\<^sub>c t" "\<forall>x \<in> set X. M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<turnstile>\<^sub>c x"
        by (auto intro: ideduct_synth_mono simp add: ik\<^sub>e\<^sub>s\<^sub>t_append)
      thus ?case using decomps\<^sub>e\<^sub>s\<^sub>t_append[OF D'(1) D''(1)] by auto
    qed auto
    then obtain D' where D': "D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "\<And>k. k \<in> set K \<Longrightarrow> M \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<turnstile>\<^sub>c k" by metis
    obtain D'' where D'': "D'' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "M \<union> ik\<^sub>e\<^sub>s\<^sub>t D'' \<turnstile>\<^sub>c t" by (metis Decompose.IH(1))
    obtain f X where fX: "t = Fun f X" "t\<^sub>i \<in> set X"
      using Decompose.hyps(2,4) by (cases t) (auto dest: Ana_fun_subterm)

    from decomps\<^sub>e\<^sub>s\<^sub>t_append[OF D'(1) D''(1)] D'(2) D''(2) have *:
        "D'@D'' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>" "\<And>k. k \<in> set K \<Longrightarrow> M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<turnstile>\<^sub>c k"
        "M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<turnstile>\<^sub>c t"
      by (auto intro: ideduct_synth_mono simp add: ik\<^sub>e\<^sub>s\<^sub>t_append)
    hence **: "\<And>k. k \<in> set K \<Longrightarrow> M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>"
      using ideduct_synth_subst by auto

    have "t\<^sub>i \<in> ik\<^sub>s\<^sub>t (decomp t)" using Decompose.hyps(2,4) ik_rcv_map unfolding decomp_def by auto
    with *(3) fX(1) Decompose.hyps(2) show ?case
    proof (induction t rule: intruder_synth_induct)
      case (AxiomC t)
      hence t_in_subterms: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (M \<union> N)"
        using decomps\<^sub>e\<^sub>s\<^sub>t_ik_subset[OF *(1)] subset_subterms_Union
        by auto
      have "M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D'@D'') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>"
        using ideduct_synth_subst[OF intruder_synth.AxiomC[OF AxiomC.hyps(1)]] by metis
      moreover have "T \<noteq> []" using decomp_ik[OF \<open>Ana t = (K,T)\<close>] \<open>t\<^sub>i \<in> ik\<^sub>s\<^sub>t (decomp t)\<close> by auto
      ultimately have "D'@D''@[Decomp (Fun f X)] \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>"
        using AxiomC decomps\<^sub>e\<^sub>s\<^sub>t.Decomp[OF *(1) _ _ _ _ **] subset_subterms_Union t_in_subterms
        by (simp add: subset_eq)
      moreover have "decomp t = to_st [Decomp (Fun f X)]" using AxiomC.prems(1,2) by auto
      ultimately show ?case
        by (metis AxiomC.prems(3) UnCI intruder_synth.AxiomC ik\<^sub>e\<^sub>s\<^sub>t_append to_st_append)
    qed (auto intro!: fX(2) *(1))
  qed (fastforce intro: intruder_synth.AxiomC assms(1))
  hence "\<exists>D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t M N \<I>. M \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@D') \<turnstile>\<^sub>c t"
    by (auto intro: ideduct_synth_mono simp add: ik\<^sub>e\<^sub>s\<^sub>t_append)
  thus thesis using that[OF decomps\<^sub>e\<^sub>s\<^sub>t_append[OF assms(1)]] assms ik\<^sub>e\<^sub>s\<^sub>t_append by moura
qed

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_ik_max_exist:
  assumes "finite A" "finite N"
  shows "\<exists>D \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>. \<forall>D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>. ik\<^sub>e\<^sub>s\<^sub>t D' \<subseteq> ik\<^sub>e\<^sub>s\<^sub>t D"
proof -
  let ?IK = "\<lambda>M. \<Union>D \<in> M. ik\<^sub>e\<^sub>s\<^sub>t D"
  have "?IK (decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>) \<subseteq> (\<Union>t \<in> A \<union> N. subterms t)" by (auto dest!: decomps\<^sub>e\<^sub>s\<^sub>t_ik_subset)
  hence "finite (?IK (decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>))"
    using subterms_union_finite[OF assms(1)] subterms_union_finite[OF assms(2)] infinite_super
    by auto
  then obtain M where M: "finite M" "M \<subseteq> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>" "?IK M = ?IK (decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>)"
    using finite_subset_Union by moura
  show ?thesis using decomps\<^sub>e\<^sub>s\<^sub>t_finite_ik_append[OF M(1,2)] M(3) by auto
qed

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_exist:
  assumes "finite A" "finite N"
  shows "\<exists>D \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>. \<forall>t. A \<turnstile> t \<longrightarrow> A \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<turnstile>\<^sub>c t"
proof (rule ccontr)
  assume neg: "\<not>(\<exists>D \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>. \<forall>t. A \<turnstile> t \<longrightarrow> A \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<turnstile>\<^sub>c t)"

  obtain D where D: "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>" "\<forall>D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>. ik\<^sub>e\<^sub>s\<^sub>t D' \<subseteq> ik\<^sub>e\<^sub>s\<^sub>t D"
    using decomps\<^sub>e\<^sub>s\<^sub>t_ik_max_exist[OF assms] by moura
  then obtain t where t: "A \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<turnstile> t" "\<not>(A \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<turnstile>\<^sub>c t)"
    using neg by (fastforce intro: ideduct_mono)

  obtain D' where D':
      "D@D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t A N \<I>" "A \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@D') \<turnstile>\<^sub>c t"
      "A \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<subset> A \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@D')"
    by (metis decomps\<^sub>e\<^sub>s\<^sub>t_exist_aux t D(1))
  hence "ik\<^sub>e\<^sub>s\<^sub>t D \<subset> ik\<^sub>e\<^sub>s\<^sub>t (D@D')" using ik\<^sub>e\<^sub>s\<^sub>t_append by auto
  moreover have "ik\<^sub>e\<^sub>s\<^sub>t (D@D') \<subseteq> ik\<^sub>e\<^sub>s\<^sub>t D" using D(2) D'(1) by auto
  ultimately show False by simp
qed

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_exist_subst:
  assumes "ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
  and "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> A" "wf\<^sub>e\<^sub>s\<^sub>t {} A" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  and "Ana_invar_subst (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
  and "well_analyzed A"
  shows "\<exists>D \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<I>. ik\<^sub>e\<^sub>s\<^sub>t (A@D) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>"
proof -
  have ik_eq: "ik\<^sub>e\<^sub>s\<^sub>t (A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>) = ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using assms(5,6)
  proof (induction A rule: List.rev_induct)
    case (snoc a A)
    hence "Ana_invar_subst (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
      using Ana_invar_subst_subset[OF snoc.prems(1)] ik\<^sub>e\<^sub>s\<^sub>t_append assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append
      unfolding Ana_invar_subst_def by simp
    with snoc have IH:
        "ik\<^sub>e\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>) = (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t ([a] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>)"
        "ik\<^sub>e\<^sub>s\<^sub>t (A@[a]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> = (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t [a] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
      using well_analyzed_split_left[OF snoc.prems(2)]
      by (auto simp add: to_st_append ik\<^sub>e\<^sub>s\<^sub>t_append_subst)

    have "ik\<^sub>e\<^sub>s\<^sub>t [a \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<I>] = ik\<^sub>e\<^sub>s\<^sub>t [a] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    proof (cases a)
      case (Step b) thus ?thesis by (cases b) auto
    next
      case (Decomp t)
      then obtain f T where t: "t = Fun f T" using well_analyzedD[OF snoc.prems(2)] by force
      obtain K M where Ana_t: "Ana (Fun f T) = (K,M)" by (metis surj_pair)
      moreover have "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t ((ik\<^sub>e\<^sub>s\<^sub>t (A@[a]) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@[a])))"
        using t Decomp snoc.prems(2)
        by (auto dest: well_analyzed_inv simp add: ik\<^sub>e\<^sub>s\<^sub>t_append assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append)
      hence "Ana (Fun f T \<cdot> \<I>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>)"
        using Ana_t snoc.prems(1)
        unfolding Ana_invar_subst_def by blast
      ultimately show ?thesis using Decomp t by (auto simp add: decomp_ik)
    qed
    thus ?case using IH unfolding subst_apply_extstrand_def by simp
  qed simp
  moreover have assignment_rhs_eq: "assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>) = assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    using assms(5,6)
  proof (induction A rule: List.rev_induct)
    case (snoc a A)
    hence "Ana_invar_subst (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
      using Ana_invar_subst_subset[OF snoc.prems(1)] ik\<^sub>e\<^sub>s\<^sub>t_append assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append
      unfolding Ana_invar_subst_def by simp
    hence "assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>) = assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using snoc.IH well_analyzed_split_left[OF snoc.prems(2)]
      by simp
    hence IH:
        "assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>) = (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t ([a] \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>)"
        "assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@[a]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> = (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t [a] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
      by (metis assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append_subst(1), metis assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append_subst(2))

    have "assignment_rhs\<^sub>e\<^sub>s\<^sub>t [a \<cdot>\<^sub>e\<^sub>s\<^sub>t\<^sub>p \<I>] = assignment_rhs\<^sub>e\<^sub>s\<^sub>t [a] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    proof (cases a)
      case (Step b) thus ?thesis by (cases b) auto
    next
      case (Decomp t)
      then obtain f T where t: "t = Fun f T" using well_analyzedD[OF snoc.prems(2)] by force
      obtain K M where Ana_t: "Ana (Fun f T) = (K,M)" by (metis surj_pair)
      moreover have "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t ((ik\<^sub>e\<^sub>s\<^sub>t (A@[a]) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@[a])))"
        using t Decomp snoc.prems(2)
        by (auto dest: well_analyzed_inv simp add: ik\<^sub>e\<^sub>s\<^sub>t_append assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append)
      hence "Ana (Fun f T \<cdot> \<I>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>)"
        using Ana_t snoc.prems(1) unfolding Ana_invar_subst_def by blast
      ultimately show ?thesis using Decomp t by (auto simp add: decomp_assignment_rhs_empty)
    qed
    thus ?case using IH unfolding subst_apply_extstrand_def by simp
  qed simp
  ultimately obtain D where D:
      "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) Var"
      "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D) \<turnstile>\<^sub>c t \<cdot> \<I>"
    using decomps\<^sub>e\<^sub>s\<^sub>t_exist[OF ik\<^sub>e\<^sub>s\<^sub>t_finite assignment_rhs\<^sub>e\<^sub>s\<^sub>t_finite, of "A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>" "A \<cdot>\<^sub>e\<^sub>s\<^sub>t \<I>"]
          ik\<^sub>e\<^sub>s\<^sub>t_append assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append assms(1)
    by force

  let ?P = "\<lambda>D D'. \<forall>t. (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D) \<turnstile>\<^sub>c t \<longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t"

  have "\<exists>D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<I>. ?P D D'" using D(1)
  proof (induction D rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
    case Nil
    have "ik\<^sub>e\<^sub>s\<^sub>t [] = ik\<^sub>e\<^sub>s\<^sub>t [] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by auto
    thus ?case by (metis decomps\<^sub>e\<^sub>s\<^sub>t.Nil)
  next
    case (Decomp D f T K M)
    obtain D' where D': "D' \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<I>" "?P D D'"
      using Decomp.IH by auto
    hence IH: "\<And>k. k \<in> set K \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c k"
              "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c Fun f T"
      using Decomp.hyps(5,6) by auto

    have D'_ik: "ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t ((ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
                "ik\<^sub>e\<^sub>s\<^sub>t D' \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
      using decomps\<^sub>e\<^sub>s\<^sub>t_ik_subset[OF D'(1)] by (metis subst_all_mono, metis)

    show ?case using IH(2,1) Decomp.hyps(2,3,4)
    proof (induction "Fun f T" arbitrary: f T K M rule: intruder_synth_induct)
      case (AxiomC f T)
      then obtain s where s: "s \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<union> ik\<^sub>e\<^sub>s\<^sub>t D'" "Fun f T = s \<cdot> \<I>" using AxiomC.prems by blast
      hence fT_s_in: "Fun f T \<in> (subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
                     "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
        using AxiomC D'_ik subset_subterms_Union[of "ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A"]
              subst_all_mono[OF subset_subterms_Union, of \<I>]
        by (metis (no_types) Un_iff image_eqI subset_Un_eq, metis (no_types) Un_iff subset_Un_eq)
      obtain Ks Ms where Ana_s: "Ana s = (Ks,Ms)" by moura

      have AD'_props: "wf\<^sub>e\<^sub>s\<^sub>t {} (A@D')" "\<lbrakk>{}; to_st (A@D')\<rbrakk>\<^sub>c \<I>"
        using decomps\<^sub>e\<^sub>s\<^sub>t_preserves_model_c[OF D'(1) assms(2)]
              decomps\<^sub>e\<^sub>s\<^sub>t_preserves_wf[OF D'(1) assms(3)]
              sem\<^sub>e\<^sub>s\<^sub>t_c_eq_sem_st strand_sem_eq_defs(1)
        by auto

      show ?case
      proof (cases s)
        case (Var x)
        \<comment> \<open>In this case \<open>\<I> x\<close> (is a subterm of something that) was derived from an
            "earlier intruder knowledge" because \<open>A\<close> is well-formed and has \<open>\<I>\<close> as a model.
            So either the intruder composed \<open>Fun f T\<close> himself (making \<open>Decomp (Fun f T)\<close>
            unnecessary) or \<open>Fun f T\<close> is an instance of something else in the intruder
            knowledge (in which case the "something" can be used in place of \<open>Fun f T\<close>)\<close>
        hence "Var x \<in> ik\<^sub>e\<^sub>s\<^sub>t (A@D')" "\<I> x = Fun f T" using s ik\<^sub>e\<^sub>s\<^sub>t_append by auto

        show ?thesis
        proof (cases "\<forall>m \<in> set M. ik\<^sub>e\<^sub>s\<^sub>t A \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c m")
          case True
          \<comment> \<open>All terms acquired by decomposing \<open>Fun f T\<close> are already derivable.
              Hence there is no need to consider decomposition of \<open>Fun f T\<close> at all.\<close>
          have *: "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@[Decomp (Fun f T)]) = (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<union> set M"
            using decomp_ik[OF \<open>Ana (Fun f T) = (K,M)\<close>] ik\<^sub>e\<^sub>s\<^sub>t_append[of D "[Decomp (Fun f T)]"]
            by auto

          { fix t' assume "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<union> set M \<turnstile>\<^sub>c t'"
            hence "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t'"
            proof (induction t' rule: intruder_synth_induct)
              case (AxiomC t') thus ?case
              proof
                assume "t' \<in> set M"
                moreover have "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) = ik\<^sub>e\<^sub>s\<^sub>t A \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by auto
                ultimately show ?case using True by auto
              qed (metis D'(2) intruder_synth.AxiomC)
            qed auto
          }
          thus ?thesis using D'(1) * by metis
        next
          case False
          \<comment> \<open>Some term acquired by decomposition of \<open>Fun f T\<close> cannot be derived in \<open>\<turnstile>\<^sub>c\<close>.
              \<open>Fun f T\<close> must therefore be an instance of something else in the intruder knowledge,
              because of well-formedness.\<close>
          then obtain t\<^sub>i where t\<^sub>i: "t\<^sub>i \<in> set T" "\<not>ik\<^sub>e\<^sub>s\<^sub>t (A@D') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t\<^sub>i"
            using Ana_fun_subterm[OF \<open>Ana (Fun f T) = (K,M)\<close>] by (auto simp add: ik\<^sub>e\<^sub>s\<^sub>t_append)
          obtain S where fS:
              "Fun f S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t (A@D')) \<or>
               Fun f S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@D'))"
              "\<I> x = Fun f S \<cdot> \<I>"
            using strand_sem_wf_ik_or_assignment_rhs_fun_subterm[
                    OF AD'_props \<open>Var x \<in> ik\<^sub>e\<^sub>s\<^sub>t (A@D')\<close> _ t\<^sub>i \<open>interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<close>]
                  \<open>\<I> x = Fun f T\<close>
            by moura
          hence fS_in: "Fun f S \<cdot> \<I> \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
                       "Fun f S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A)"
            using imageI[OF s(1), of "\<lambda>x. x \<cdot> \<I>"] Var
                  ik\<^sub>e\<^sub>s\<^sub>t_append[of A D'] assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append[of A D']
                  decomps\<^sub>e\<^sub>s\<^sub>t_subterms[OF D'(1)] decomps\<^sub>e\<^sub>s\<^sub>t_assignment_rhs_empty[OF D'(1)]
            by auto
          obtain KS MS where Ana_fS: "Ana (Fun f S) = (KS, MS)" by moura
          hence "K = KS \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>" "M = MS \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>"
            using Ana_invar_substD[OF assms(5) fS_in(2)]
                  s(2) fS(2) \<open>s = Var x\<close> \<open>Ana (Fun f T) = (K,M)\<close>
            by simp_all
          hence "MS \<noteq> []" using \<open>M \<noteq> []\<close> by simp
          have "\<And>k. k \<in> set KS \<Longrightarrow> ik\<^sub>e\<^sub>s\<^sub>t A \<union> ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c k \<cdot> \<I>"
            using AxiomC.prems(1) \<open>K = KS \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>\<close> by (simp add: image_Un)
          hence D'': "D'@[Decomp (Fun f S)] \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<I>"
            using decomps\<^sub>e\<^sub>s\<^sub>t.Decomp[OF D'(1) fS_in(2) Ana_fS \<open>MS \<noteq> []\<close>] AxiomC.prems(1)
                  intruder_synth.AxiomC[OF fS_in(1)]
            by simp
          moreover {
            fix t' assume "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@[Decomp (Fun f T)]) \<turnstile>\<^sub>c t'"
            hence "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t (D'@[Decomp (Fun f S)]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t'"
            proof (induction t' rule: intruder_synth_induct)
              case (AxiomC t')
              hence "t' \<in> (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t D \<or> t' \<in> ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun f T)]"
                by (simp add: ik\<^sub>e\<^sub>s\<^sub>t_append)
              thus ?case
              proof
                assume "t' \<in> ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun f T)]"
                hence "t' \<in> ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun f S)] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
                  using decomp_ik \<open>Ana (Fun f T) = (K,M)\<close> \<open>Ana (Fun f S) = (KS,MS)\<close> \<open>M = MS \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>\<close>
                  by simp
                thus ?case
                  using ideduct_synth_mono[
                          OF intruder_synth.AxiomC[of t' "ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun f S)] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"],
                          of "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t (D'@[Decomp (Fun f S)]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"]
                  by (auto simp add: ik\<^sub>e\<^sub>s\<^sub>t_append)
              next
                assume "t' \<in> (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t D"
                hence "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t'"
                  by (metis D'(2) intruder_synth.AxiomC)
                hence "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun f S)] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t'"
                  by (simp add: ideduct_synth_mono)
                thus ?case
                  using ik\<^sub>e\<^sub>s\<^sub>t_append[of D' "[Decomp (Fun f S)]"]
                        image_Un[of "\<lambda>x. x \<cdot> \<I>" "ik\<^sub>e\<^sub>s\<^sub>t D'" "ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun f S)]"]
                  by (simp add: sup_aci(2))
              qed
            qed auto
          }
          ultimately show ?thesis using D'' by auto
        qed
      next
        case (Fun g S) \<comment> \<open>Hence \<open>Decomp (Fun f T)\<close> can be substituted for \<open>Decomp (Fun g S)\<close>\<close>
        hence KM: "K = Ks \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>" "M = Ms \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<I>" "set K = set Ks \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "set M = set Ms \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
          using fT_s_in(2) \<open>Ana (Fun f T) = (K,M)\<close> Ana_s s(2)
                Ana_invar_substD[OF assms(5), of g S]
          by auto
        hence Ms_nonempty: "Ms \<noteq> []" using \<open>M \<noteq> []\<close> by auto
        { fix t' assume "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@[Decomp (Fun f T)]) \<turnstile>\<^sub>c t'"
          hence "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t (D'@[Decomp (Fun g S)]) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t'" using AxiomC
          proof (induction t' rule: intruder_synth_induct)
            case (AxiomC t')
            hence "t' \<in> ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<or> t' \<in> ik\<^sub>e\<^sub>s\<^sub>t D \<or> t' \<in> set M"
              by (simp add: decomp_ik ik\<^sub>e\<^sub>s\<^sub>t_append)
            thus ?case
            proof (elim disjE)
              assume "t' \<in> ik\<^sub>e\<^sub>s\<^sub>t D"
              hence *: "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t'" using D'(2) by simp
              show ?case by (auto intro: ideduct_synth_mono[OF *] simp add: ik\<^sub>e\<^sub>s\<^sub>t_append_subst(2))
            next
              assume "t' \<in> set M"
              hence "t' \<in> ik\<^sub>e\<^sub>s\<^sub>t [Decomp (Fun g S)] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
                using KM(2) Fun decomp_ik[OF Ana_s] by auto
              thus ?case by (simp add: image_Un ik\<^sub>e\<^sub>s\<^sub>t_append)
            qed (simp add: ideduct_synth_mono[OF intruder_synth.AxiomC])
          qed auto
        }
        thus ?thesis
          using s Fun Ana_s AxiomC.prems(1) KM(3) fT_s_in
                decomps\<^sub>e\<^sub>s\<^sub>t.Decomp[OF D'(1) _ _ Ms_nonempty, of g S Ks]
          by (metis AxiomC.hyps image_Un image_eqI intruder_synth.AxiomC)
      qed
    next
      case (ComposeC T f)
      have *: "\<And>m. m \<in> set M \<Longrightarrow> (ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c m"
        using Ana_fun_subterm[OF \<open>Ana (Fun f T) = (K, M)\<close>] ComposeC.hyps(3)
        by auto

      have **: "ik\<^sub>e\<^sub>s\<^sub>t (D@[Decomp (Fun f T)]) = ik\<^sub>e\<^sub>s\<^sub>t D \<union> set M"
        using decomp_ik[OF \<open>Ana (Fun f T) = (K, M)\<close>] ik\<^sub>e\<^sub>s\<^sub>t_append by auto

      { fix t' assume "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> ik\<^sub>e\<^sub>s\<^sub>t (D@[Decomp (Fun f T)]) \<turnstile>\<^sub>c t'"
        hence "(ik\<^sub>e\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t D' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<turnstile>\<^sub>c t'"
          by (induct rule: intruder_synth_induct) (auto simp add: D'(2) * **)
      }
      thus ?case using D'(1) by auto
    qed
  qed
  thus ?thesis using D(2) assms(1) by (auto simp add: ik\<^sub>e\<^sub>s\<^sub>t_append_subst(2))
qed

private lemma wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_nil: assumes "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>" shows "wf\<^sub>s\<^sub>t\<^sub>s' (update\<^sub>s\<^sub>t \<S> []) \<A>"
using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by auto

private lemma wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_snd:
  assumes "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>" "send\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
  shows "wf\<^sub>s\<^sub>t\<^sub>s' (update\<^sub>s\<^sub>t \<S> (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S)) (\<A>@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def
proof (intro conjI)
  let ?S = "send\<langle>t\<rangle>\<^sub>s\<^sub>t#S"
  let ?A = "\<A>@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"

  have \<S>: "\<And>S'. S' \<in> update\<^sub>s\<^sub>t \<S> ?S \<Longrightarrow> S' = S \<or> S' \<in> \<S>" by auto

  have 1: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>) (dual\<^sub>s\<^sub>t S)" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by auto
  moreover have 2: "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A = wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A> \<union> fv t"
    using wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_split(2) by (auto simp add: Un_assoc)
  ultimately have 3: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" by (metis wf_vars_mono)

  have 4: "\<forall>S \<in> \<S>. \<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by simp

  have "wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" using 1 2 3 assms(2) by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" by (metis 3 \<S>)

  have "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 4 assms(2) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by force+
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. \<forall>S' \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" by (metis 4 \<S>)

  have "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>s\<^sub>t S' = {}" "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t ?S = {}"
    using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by metis+
  hence 5: "fv\<^sub>e\<^sub>s\<^sub>t ?A = fv\<^sub>e\<^sub>s\<^sub>t \<A> \<union> fv t" "bvars\<^sub>e\<^sub>s\<^sub>t ?A = bvars\<^sub>e\<^sub>s\<^sub>t \<A>" "\<forall>S' \<in> \<S>. fv t \<inter> bvars\<^sub>s\<^sub>t S' = {}"
    using to_st_append by fastforce+

  have *: "\<forall>S \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}"
    using 5 assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fast
  hence "fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" using assms(2) by metis
  hence "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by (metis * \<S>)

  have **: "\<forall>S \<in> \<S>. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 5 assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fast
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t ?S = {}" using assms(2) by metis
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by fastforce
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by (metis ** \<S>)
qed

private lemma wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_rcv:
  assumes "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>" "receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
  shows "wf\<^sub>s\<^sub>t\<^sub>s' (update\<^sub>s\<^sub>t \<S> (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S)) (\<A>@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def
proof (intro conjI)
  let ?S = "receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S"
  let ?A = "\<A>@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]"

  have \<S>: "\<And>S'. S' \<in> update\<^sub>s\<^sub>t \<S> ?S \<Longrightarrow> S' = S \<or> S' \<in> \<S>" by auto

  have 1: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>) (dual\<^sub>s\<^sub>t S)" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by auto
  moreover have 2: "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A = wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A> \<union> fv t"
    using wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_split(2) by (auto simp add: Un_assoc)
  ultimately have 3: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" by (metis wf_vars_mono)

  have 4: "\<forall>S \<in> \<S>. \<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by simp

  have "wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" using 1 2 3 assms(2) by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" by (metis 3 \<S>)

  have "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 4 assms(2) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by force+
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. \<forall>S' \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" by (metis 4 \<S>)

  have "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>s\<^sub>t S' = {}" "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t ?S = {}"
    using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by metis+
  hence 5: "fv\<^sub>e\<^sub>s\<^sub>t ?A = fv\<^sub>e\<^sub>s\<^sub>t \<A> \<union> fv t" "bvars\<^sub>e\<^sub>s\<^sub>t ?A = bvars\<^sub>e\<^sub>s\<^sub>t \<A>" "\<forall>S' \<in> \<S>. fv t \<inter> bvars\<^sub>s\<^sub>t S' = {}"
    using to_st_append by fastforce+

  have *: "\<forall>S \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}"
    using 5 assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fast
  hence "fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" using assms(2) by metis
  hence "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by (metis * \<S>)

  have **: "\<forall>S \<in> \<S>. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 5 assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fast
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t ?S = {}" using assms(2) by metis
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by fastforce
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by (metis ** \<S>)
qed

private lemma wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_eq:
  assumes "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>" "\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
  shows "wf\<^sub>s\<^sub>t\<^sub>s' (update\<^sub>s\<^sub>t \<S> (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S)) (\<A>@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)])"
unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def
proof (intro conjI)
  let ?S = "\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S"
  let ?A = "\<A>@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]"

  have \<S>: "\<And>S'. S' \<in> update\<^sub>s\<^sub>t \<S> ?S \<Longrightarrow> S' = S \<or> S' \<in> \<S>" by auto

  have 1: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>) (dual\<^sub>s\<^sub>t S)" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by auto
  moreover have 2:
      "a = Assign \<Longrightarrow> wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A = wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A> \<union> fv t \<union> fv t'"
      "a = Check \<Longrightarrow> wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A = wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>"
    using wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_split(2) by (auto simp add: Un_assoc)
  ultimately have 3: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)"
    by (cases a) (metis wf_vars_mono, metis)

  have 4: "\<forall>S \<in> \<S>. \<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by simp

  have "wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" using 1 2 3 assms(2) by (cases a) auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" by (metis 3 \<S>)

  have "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 4 assms(2) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by force+
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. \<forall>S' \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" by (metis 4 \<S>)

  have "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>s\<^sub>t S' = {}" "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t ?S = {}"
    using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by metis+
  hence 5: "fv\<^sub>e\<^sub>s\<^sub>t ?A = fv\<^sub>e\<^sub>s\<^sub>t \<A> \<union> fv t \<union> fv t'" "bvars\<^sub>e\<^sub>s\<^sub>t ?A = bvars\<^sub>e\<^sub>s\<^sub>t \<A>"
           "\<forall>S' \<in> \<S>. fv t \<inter> bvars\<^sub>s\<^sub>t S' = {}" "\<forall>S' \<in> \<S>. fv t' \<inter> bvars\<^sub>s\<^sub>t S' = {}"
    using to_st_append by fastforce+

  have *: "\<forall>S \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}"
    using 5 assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fast
  hence "fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" using assms(2) by metis
  hence "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by (metis * \<S>)

  have **: "\<forall>S \<in> \<S>. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 5 assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fast
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t ?S = {}" using assms(2) by metis
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by fastforce
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by (metis ** \<S>)
qed

private lemma wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_ineq:
  assumes "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>" "\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
  shows "wf\<^sub>s\<^sub>t\<^sub>s' (update\<^sub>s\<^sub>t \<S> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S)) (\<A>@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)])"
unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def
proof (intro conjI)
  let ?S = "\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S"
  let ?A = "\<A>@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]"

  have \<S>: "\<And>S'. S' \<in> update\<^sub>s\<^sub>t \<S> ?S \<Longrightarrow> S' = S \<or> S' \<in> \<S>" by auto

  have 1: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>) (dual\<^sub>s\<^sub>t S)" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by auto
  moreover have 2: "wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A = wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>"
    using wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_split(2) by (auto simp add: Un_assoc)
  ultimately have 3: "\<forall>S \<in> \<S>. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" by metis

  have 4: "\<forall>S \<in> \<S>. \<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by simp

  have "wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" using 1 2 3 assms(2) by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t ?A) (dual\<^sub>s\<^sub>t S)" by (metis 3 \<S>)

  have "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}"
       "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 4 assms(2) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by force+
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. \<forall>S' \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>s\<^sub>t S' = {}" by (metis 4 \<S>)

  have "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>s\<^sub>t S' = {}" "\<forall>S' \<in> \<S>. fv\<^sub>s\<^sub>t S' \<inter> bvars\<^sub>s\<^sub>t ?S = {}"
    using assms unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by metis+
  moreover have "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X \<subseteq> fv\<^sub>s\<^sub>t (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t # S)" by auto
  ultimately have 5:
      "\<forall>S' \<in> \<S>. (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X) \<inter> bvars\<^sub>s\<^sub>t S' = {}"
      "fv\<^sub>e\<^sub>s\<^sub>t ?A = fv\<^sub>e\<^sub>s\<^sub>t \<A> \<union> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X)" "bvars\<^sub>e\<^sub>s\<^sub>t ?A = set X \<union> bvars\<^sub>e\<^sub>s\<^sub>t \<A>"
      "\<forall>S \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> set X = {}"
    using to_st_append
    by (blast, force, force, force)

  have *: "\<forall>S \<in> \<S>. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" using 5(3,4) assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by blast
  hence "fv\<^sub>s\<^sub>t ?S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" using assms(2) by metis
  hence "fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t ?A = {}" by (metis * \<S>)

  have **: "\<forall>S \<in> \<S>. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using 5(1,2) assms(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fast
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t ?S = {}" using assms(2) by metis
  hence "fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by auto
  thus "\<forall>S \<in> update\<^sub>s\<^sub>t \<S> ?S. fv\<^sub>e\<^sub>s\<^sub>t ?A \<inter> bvars\<^sub>s\<^sub>t S = {}" by (metis ** \<S>)
qed

private lemma trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq:
  assumes "x#S \<in> \<S>"
  shows "\<Union>(trms\<^sub>s\<^sub>t ` update\<^sub>s\<^sub>t \<S> (x#S)) \<union> trms\<^sub>s\<^sub>t\<^sub>p x = \<Union>(trms\<^sub>s\<^sub>t ` \<S>)" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
  proof
    have "trms\<^sub>s\<^sub>t\<^sub>p x \<subseteq> trms\<^sub>s\<^sub>t (x#S)" by auto
    hence "\<And>t'. t' \<in> ?B \<Longrightarrow> t' \<in> trms\<^sub>s\<^sub>t\<^sub>p x \<Longrightarrow> t' \<in> ?A" by simp
    moreover {
      fix t' assume t': "t' \<in> ?B" "t' \<notin> trms\<^sub>s\<^sub>t\<^sub>p x"
      then obtain S' where S': "t' \<in> trms\<^sub>s\<^sub>t S'" "S' \<in> \<S>" by auto
      hence "S' = x#S \<or> S' \<in> update\<^sub>s\<^sub>t \<S> (x#S)" by auto
      moreover {
        assume "S' = x#S"
        hence "t' \<in> trms\<^sub>s\<^sub>t S" using S' t' by simp
        hence "t' \<in> ?A" by auto
      }
      ultimately have "t' \<in> ?A" using t' S' by auto
    }
    ultimately show "\<And>t'. t' \<in> ?B \<Longrightarrow> t' \<in> ?A" by metis
  qed

  show "?A \<subseteq> ?B"
  proof
    have "\<And>t'. t' \<in> ?A \<Longrightarrow> t' \<in> trms\<^sub>s\<^sub>t\<^sub>p x \<Longrightarrow> trms\<^sub>s\<^sub>t\<^sub>p x \<subseteq> ?B"
      using assms by force+
    moreover {
      fix t' assume t': "t' \<in> ?A" "t' \<notin> trms\<^sub>s\<^sub>t\<^sub>p x"
      then obtain S' where "t' \<in> trms\<^sub>s\<^sub>t S'" "S' \<in> update\<^sub>s\<^sub>t \<S> (x#S)" by auto
      hence "S' = S \<or> S' \<in> \<S>" by auto
      moreover have "trms\<^sub>s\<^sub>t S \<subseteq> ?B" using assms trms\<^sub>s\<^sub>t_cons[of x S] by blast
      ultimately have "t' \<in> ?B" using t' by fastforce
    }
    ultimately show "\<And>t'. t' \<in> ?A \<Longrightarrow> t' \<in> ?B" by blast
  qed
qed

private lemma trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_snd:
  assumes "send\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>" "\<S>' = update\<^sub>s\<^sub>t \<S> (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S)" "\<A>' = \<A>@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(trms\<^sub>s\<^sub>t ` \<S>)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>) = (\<Union>(trms\<^sub>s\<^sub>t ` \<S>')) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>')"
proof -
  have "(trms\<^sub>e\<^sub>s\<^sub>t \<A>') = (trms\<^sub>e\<^sub>s\<^sub>t \<A>) \<union> {t}" "\<Union>(trms\<^sub>s\<^sub>t ` \<S>') \<union> {t} = \<Union>(trms\<^sub>s\<^sub>t ` \<S>)"
    using to_st_append trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq[OF assms(1)] assms(2,3) by auto
  thus ?thesis
    by (metis (no_types, lifting) Un_insert_left Un_insert_right sup_bot.right_neutral)
qed

private lemma trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_rcv:
  assumes "receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>" "\<S>' = update\<^sub>s\<^sub>t \<S> (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S)" "\<A>' = \<A>@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(trms\<^sub>s\<^sub>t ` \<S>)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>) = (\<Union>(trms\<^sub>s\<^sub>t ` \<S>')) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>')"
proof -
  have "(trms\<^sub>e\<^sub>s\<^sub>t \<A>') = (trms\<^sub>e\<^sub>s\<^sub>t \<A>) \<union> {t}" "\<Union>(trms\<^sub>s\<^sub>t ` \<S>') \<union> {t} = \<Union>(trms\<^sub>s\<^sub>t ` \<S>)"
    using to_st_append trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq[OF assms(1)] assms(2,3) by auto
  thus ?thesis
    by (metis (no_types, lifting) Un_insert_left Un_insert_right sup_bot.right_neutral)
qed

private lemma trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_eq:
  assumes "\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>" "\<S>' = update\<^sub>s\<^sub>t \<S> (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S)" "\<A>' = \<A>@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(trms\<^sub>s\<^sub>t ` \<S>)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>) = (\<Union>(trms\<^sub>s\<^sub>t ` \<S>')) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>')"
proof -
  have "(trms\<^sub>e\<^sub>s\<^sub>t \<A>') = (trms\<^sub>e\<^sub>s\<^sub>t \<A>) \<union> {t,t'}" "\<Union>(trms\<^sub>s\<^sub>t ` \<S>') \<union> {t,t'} = \<Union>(trms\<^sub>s\<^sub>t ` \<S>)"
    using to_st_append trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq[OF assms(1)] assms(2,3) by auto
  thus ?thesis
    by (metis (no_types, lifting) Un_insert_left Un_insert_right sup_bot.right_neutral)
qed

private lemma trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_ineq:
  assumes "\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>" "\<S>' = update\<^sub>s\<^sub>t \<S> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S)" "\<A>' = \<A>@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(trms\<^sub>s\<^sub>t ` \<S>)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>) = (\<Union>(trms\<^sub>s\<^sub>t ` \<S>')) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>')"
proof -
  have "(trms\<^sub>e\<^sub>s\<^sub>t \<A>') = (trms\<^sub>e\<^sub>s\<^sub>t \<A>) \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F" "\<Union>(trms\<^sub>s\<^sub>t ` \<S>') \<union> trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F = \<Union>(trms\<^sub>s\<^sub>t ` \<S>)"
    using to_st_append trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq[OF assms(1)] assms(2,3) by auto
  thus ?thesis by (simp add: Un_commute sup_left_commute)
qed

private lemma ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset:
  assumes "x#S \<in> \<S>"
  shows "\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` (update\<^sub>s\<^sub>t \<S> (x#S))) \<subseteq> \<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)" (is ?A)
        "\<Union>(assignment_rhs\<^sub>s\<^sub>t ` (update\<^sub>s\<^sub>t \<S> (x#S))) \<subseteq> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)" (is ?B)
proof -
  { fix t assume "t \<in> \<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` (update\<^sub>s\<^sub>t \<S> (x#S)))"
    then obtain S' where S': "S' \<in> update\<^sub>s\<^sub>t \<S> (x#S)" "t \<in> ik\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t S')" by auto

    have *: "ik\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t S) \<subseteq> ik\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t (x#S))"
      using ik_append[of "dual\<^sub>s\<^sub>t [x]" "dual\<^sub>s\<^sub>t S"] dual\<^sub>s\<^sub>t_append[of "[x]" S]
      by auto

    hence "t \<in> \<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)"
    proof (cases "S' = S")
      case True thus ?thesis using * assms S' by auto
    next
      case False thus ?thesis using S' by auto
    qed
  }
  moreover
  { fix t assume "t \<in> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` (update\<^sub>s\<^sub>t \<S> (x#S)))"
    then obtain S' where S': "S' \<in> update\<^sub>s\<^sub>t \<S> (x#S)" "t \<in> assignment_rhs\<^sub>s\<^sub>t S'" by auto

    have "assignment_rhs\<^sub>s\<^sub>t S \<subseteq> assignment_rhs\<^sub>s\<^sub>t (x#S)"
      using assignment_rhs_append[of "[x]" S] by simp
    hence "t \<in> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)"
      using assms S' by (cases "S' = S") auto
  }
  ultimately show ?A ?B by (metis subsetI)+
qed

private lemma ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_snd:
  assumes "send\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
          "\<S>' = update\<^sub>s\<^sub>t \<S> (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S)"
          "\<A>' = \<A>@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
         (\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?A)
        "(\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
         (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?B)
proof -
  { fix t' assume t'_in: "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>')"
    hence "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>) \<union> {t}" using assms ik\<^sub>e\<^sub>s\<^sub>t_append by auto
    moreover have "t \<in> \<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)" using assms(1) by force
    ultimately have "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) by auto
  }
  moreover
  { fix t' assume t'_in: "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>')"
    hence "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using assms assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append by auto
    hence "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) by auto
  }
  ultimately show ?A ?B by (metis subsetI)+
qed

private lemma ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_rcv:
  assumes "receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
          "\<S>' = update\<^sub>s\<^sub>t \<S> (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S)"
          "\<A>' = \<A>@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
         (\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?A)
        "(\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
         (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?B)
proof -
  { fix t' assume t'_in: "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>')"
    hence "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)" using assms ik\<^sub>e\<^sub>s\<^sub>t_append by auto
    hence "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) by auto
  }
  moreover
  { fix t' assume t'_in: "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>')"
    hence "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using assms assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append by auto
    hence "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) by auto
  }
  ultimately show ?A ?B by (metis subsetI)+
qed

private lemma ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_eq:
  assumes "\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
          "\<S>' = update\<^sub>s\<^sub>t \<S> (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S)"
          "\<A>' = \<A>@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
         (\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?A)
        "(\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
         (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?B)
proof -
  have 1: "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)"
    when "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>')"
    for t'
  proof -
    have "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)" using that assms ik\<^sub>e\<^sub>s\<^sub>t_append by auto
    thus ?thesis using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) by auto
  qed

  have 2: "t'' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)"
    when "t'' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>')" "a = Assign"
    for t''
  proof -
    have "t'' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>) \<union> {t'}"
      using that assms assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append by auto
    moreover have "t' \<in> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)" using assms(1) that by force
    ultimately show ?thesis using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) that by auto
  qed

  have 3: "assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>' = assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>" (is ?C)
          "(\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<subseteq> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>))" (is ?D)
    when "a = Check"
  proof -
    show ?C using that assms(2,3) by (simp add: assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append)
    show ?D using assms(1,2,3) ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset(2) by auto
  qed

  show ?A using 1 2 by (metis subsetI)
  show ?B using 1 2 3 by (cases a) blast+
qed

private lemma ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_ineq:
  assumes "\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>"
          "\<S>' = update\<^sub>s\<^sub>t \<S> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S)"
          "\<A>' = \<A>@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]"
  shows "(\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
          (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?A)
        "(\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>') \<subseteq>
         (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)" (is ?B)
proof -
  { fix t' assume t'_in: "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>')"
    hence "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>')) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)" using assms ik\<^sub>e\<^sub>s\<^sub>t_append by auto
    hence "t' \<in> (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>)) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) by auto
  }
  moreover
  { fix t' assume t'_in: "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>')"
    hence "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>')) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using assms assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append by auto
    hence "t' \<in> (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>)) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)"
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset[OF assms(1)] assms(2) by auto
  }
  ultimately show ?A ?B by (metis subsetI)+
qed


subsubsection \<open>Transition Systems Definitions\<close>
inductive pts_symbolic::
  "(('fun,'var) strands \<times> ('fun,'var) strand) \<Rightarrow>
   (('fun,'var) strands \<times> ('fun,'var) strand) \<Rightarrow> bool"
(infix "\<Rightarrow>\<^sup>\<bullet>" 50) where
  Nil[simp]:        "[] \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet> (update\<^sub>s\<^sub>t \<S> [],\<A>)"
| Send[simp]:       "send\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet> (update\<^sub>s\<^sub>t \<S> (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S),\<A>@[receive\<langle>t\<rangle>\<^sub>s\<^sub>t])"
| Receive[simp]:    "receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet> (update\<^sub>s\<^sub>t \<S> (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S),\<A>@[send\<langle>t\<rangle>\<^sub>s\<^sub>t])"
| Equality[simp]:   "\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet> (update\<^sub>s\<^sub>t \<S> (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S),\<A>@[\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t])"
| Inequality[simp]: "\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet> (update\<^sub>s\<^sub>t \<S> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S),\<A>@[\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t])"

private inductive pts_symbolic_c::
  "(('fun,'var) strands \<times> ('fun,'var) extstrand) \<Rightarrow>
   (('fun,'var) strands \<times> ('fun,'var) extstrand) \<Rightarrow> bool"
(infix "\<Rightarrow>\<^sup>\<bullet>\<^sub>c" 50) where
  Nil[simp]:        "[] \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (update\<^sub>s\<^sub>t \<S> [],\<A>)"
| Send[simp]:       "send\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (update\<^sub>s\<^sub>t \<S> (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S),\<A>@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
| Receive[simp]:    "receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (update\<^sub>s\<^sub>t \<S> (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S),\<A>@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
| Equality[simp]:   "\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (update\<^sub>s\<^sub>t \<S> (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S),\<A>@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)])"
| Inequality[simp]: "\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S \<in> \<S> \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (update\<^sub>s\<^sub>t \<S> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S),\<A>@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)])"
| Decompose[simp]:  "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)
                     \<Longrightarrow> (\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (\<S>,\<A>@[Decomp (Fun f T)])"

abbreviation pts_symbolic_rtrancl (infix "\<Rightarrow>\<^sup>\<bullet>\<^sup>*" 50) where "a \<Rightarrow>\<^sup>\<bullet>\<^sup>* b \<equiv> pts_symbolic\<^sup>*\<^sup>* a b"
private abbreviation pts_symbolic_c_rtrancl (infix "\<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>*" 50) where "a \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* b \<equiv> pts_symbolic_c\<^sup>*\<^sup>* a b"

lemma pts_symbolic_induct[consumes 1, case_names Nil Send Receive Equality Inequality]:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet> (\<S>',\<A>')"
  and "\<lbrakk>[] \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> []; \<A>' = \<A>\<rbrakk> \<Longrightarrow> P"
  and "\<And>t S. \<lbrakk>send\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[receive\<langle>t\<rangle>\<^sub>s\<^sub>t]\<rbrakk> \<Longrightarrow> P"
  and "\<And>t S. \<lbrakk>receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[send\<langle>t\<rangle>\<^sub>s\<^sub>t]\<rbrakk> \<Longrightarrow> P"
  and "\<And>a t t' S. \<lbrakk>\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t]\<rbrakk> \<Longrightarrow> P"
  and "\<And>X F S. \<lbrakk>\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]\<rbrakk> \<Longrightarrow> P"
  shows "P"
apply (rule pts_symbolic.cases[OF assms(1)])
using assms(2,3,4,5,6) by simp_all

private lemma pts_symbolic_c_induct[consumes 1, case_names Nil Send Receive Equality Inequality Decompose]:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (\<S>',\<A>')"
  and "\<lbrakk>[] \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> []; \<A>' = \<A>\<rbrakk> \<Longrightarrow> P"
  and "\<And>t S. \<lbrakk>send\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)]\<rbrakk> \<Longrightarrow> P"
  and "\<And>t S. \<lbrakk>receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]\<rbrakk> \<Longrightarrow> P"
  and "\<And>a t t' S. \<lbrakk>\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)]\<rbrakk> \<Longrightarrow> P"
  and "\<And>X F S. \<lbrakk>\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S \<in> \<S>; \<S>' = update\<^sub>s\<^sub>t \<S> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S); \<A>' = \<A>@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)]\<rbrakk> \<Longrightarrow> P"
  and "\<And>f T. \<lbrakk>Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A> \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>); \<S>' = \<S>; \<A>' = \<A>@[Decomp (Fun f T)]\<rbrakk> \<Longrightarrow> P"
  shows "P"
apply (rule pts_symbolic_c.cases[OF assms(1)])
using assms(2,3,4,5,6,7) by simp_all

private lemma pts_symbolic_c_preserves_wf_prot:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')" "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>"
  shows "wf\<^sub>s\<^sub>t\<^sub>s' \<S>' \<A>'"
using assms
proof (induction rule: rtranclp_induct2)
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  from step.hyps(2) step.IH[OF step.prems] show ?case
  proof (induction rule: pts_symbolic_c_induct)
    case Decompose
    hence "fv\<^sub>e\<^sub>s\<^sub>t \<A>2 = fv\<^sub>e\<^sub>s\<^sub>t \<A>1" "bvars\<^sub>e\<^sub>s\<^sub>t \<A>2 = bvars\<^sub>e\<^sub>s\<^sub>t \<A>1"
      using bvars_decomp ik_assignment_rhs_decomp_fv by metis+
    thus ?case using Decompose unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def
      by (metis wf_vars_mono wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_split(2))
  qed (metis wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_nil, metis wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_snd,
       metis wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_rcv, metis wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_eq,
       metis wf\<^sub>s\<^sub>t\<^sub>s'_update\<^sub>s\<^sub>t_ineq)
qed metis

private lemma pts_symbolic_c_preserves_wf_is:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')" "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>" "wf\<^sub>s\<^sub>t V (to_st \<A>)"
  shows "wf\<^sub>s\<^sub>t V (to_st \<A>')"
using assms
proof (induction rule: rtranclp_induct2)
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  hence "(\<S>, \<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>2, \<A>2)" by auto
  hence *: "wf\<^sub>s\<^sub>t\<^sub>s' \<S>1 \<A>1" "wf\<^sub>s\<^sub>t\<^sub>s' \<S>2 \<A>2"
    using pts_symbolic_c_preserves_wf_prot[OF _ step.prems(1)] step.hyps(1)
    by auto

  from step.hyps(2) step.IH[OF step.prems] show ?case
  proof (induction rule: pts_symbolic_c_induct)
    case Nil thus ?case by auto
  next
    case (Send t S)
    hence "wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>1) (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#(dual\<^sub>s\<^sub>t S))"
      using *(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fastforce
    hence "fv t \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (to_st \<A>1) \<union> V"
      using wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_eq_wfrestrictedvars\<^sub>s\<^sub>t by auto
    thus ?case using Send wf_rcv_append''' to_st_append by simp
  next
    case (Receive t) thus ?case using wf_snd_append to_st_append by simp
  next
    case (Equality a t t' S)
    hence "wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>1) (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#(dual\<^sub>s\<^sub>t S))"
      using *(1) unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by fastforce
    hence "fv t' \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (to_st \<A>1) \<union> V" when "a = Assign"
      using wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_eq_wfrestrictedvars\<^sub>s\<^sub>t that by auto
    thus ?case using Equality wf_eq_append''' to_st_append by (cases a) auto
  next
    case (Inequality t t' S) thus ?case using wf_ineq_append'' to_st_append by simp
  next
    case (Decompose f T)
    hence "fv (Fun f T) \<subseteq> wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t \<A>1"
      by (metis fv_subterms_set fv_subset subset_trans
                ik\<^sub>s\<^sub>t_assignment_rhs\<^sub>s\<^sub>t_wfrestrictedvars_subset)
    hence "vars\<^sub>s\<^sub>t (decomp (Fun f T)) \<subseteq> wfrestrictedvars\<^sub>s\<^sub>t (to_st \<A>1) \<union> V"
      using decomp_vars[of "Fun f T"] wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_eq_wfrestrictedvars\<^sub>s\<^sub>t[of \<A>1] by auto
    thus ?case
      using to_st_append[of \<A>1 "[Decomp (Fun f T)]"]
            wf_append_suffix[OF Decompose.prems] Decompose.hyps(3)
      by (metis append_Nil2 decomp_vars(1,2) to_st.simps(1,3))
  qed
qed metis

private lemma pts_symbolic_c_preserves_tfr\<^sub>s\<^sub>e\<^sub>t:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')"
    and "tfr\<^sub>s\<^sub>e\<^sub>t ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>))"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>))"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>')) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>')) \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>')) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>'))"
using assms
proof (induction rule: rtranclp_induct2)
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  from step.hyps(2) step.IH[OF step.prems] show ?case
  proof (induction rule: pts_symbolic_c_induct)
    case Nil
    hence "\<Union>(trms\<^sub>s\<^sub>t ` \<S>1) = \<Union>(trms\<^sub>s\<^sub>t ` \<S>2)" by force
    thus ?case using Nil by metis
  next
    case (Decompose f T)
    obtain t where t: "t \<in> ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1" "Fun f T \<sqsubseteq> t"
      using Decompose.hyps(1) by auto
    have t_wf: "wf\<^sub>t\<^sub>r\<^sub>m t"
      using Decompose.prems wf_trm_subterm[of _ t]
            trms\<^sub>e\<^sub>s\<^sub>t_ik_assignment_rhsI[OF t(1)]
      unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def
      by (metis UN_E Un_iff)
    have "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>e\<^sub>s\<^sub>t \<A>1)" using trms\<^sub>e\<^sub>s\<^sub>t_ik_assignment_rhsI t by auto
    hence "Fun f T \<in> SMP (trms\<^sub>e\<^sub>s\<^sub>t \<A>1)"
      by (metis (no_types) SMP.MP SMP.Subterm UN_E t(2))
    hence "{Fun f T} \<subseteq> SMP (trms\<^sub>e\<^sub>s\<^sub>t \<A>1)" using SMP.Subterm[of "Fun f T"] by auto
    moreover have "trms\<^sub>e\<^sub>s\<^sub>t \<A>2 = insert (Fun f T) (trms\<^sub>e\<^sub>s\<^sub>t \<A>1)"
      using Decompose.hyps(3) by auto
    ultimately have *: "SMP (trms\<^sub>e\<^sub>s\<^sub>t \<A>1) = SMP (trms\<^sub>e\<^sub>s\<^sub>t \<A>2)"
      using SMP_subset_union_eq[of "{Fun f T}"]
      by (simp add: Un_commute)
    hence "SMP ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>1)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>1)) = SMP ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>2)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>2))"
      using Decompose.hyps(2) SMP_union by auto
    moreover have "\<forall>t \<in> trms\<^sub>e\<^sub>s\<^sub>t \<A>1. wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)"
      using Decompose.prems wf_trm_subterm t(2) t_wf unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by auto
    hence "\<forall>t \<in> trms\<^sub>e\<^sub>s\<^sub>t \<A>2. wf\<^sub>t\<^sub>r\<^sub>m t" by (metis * SMP.MP SMP_wf_trm)
    hence "\<forall>t \<in> (\<Union>(trms\<^sub>s\<^sub>t ` \<S>2)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>2). wf\<^sub>t\<^sub>r\<^sub>m t"
      using Decompose.prems Decompose.hyps(2) unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by force
    ultimately show ?thesis using Decompose.prems unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by presburger
  qed (metis trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_snd, metis trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_rcv,
       metis trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_eq, metis trms\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_eq_ineq)
qed metis

private lemma pts_symbolic_c_preserves_tfr\<^sub>s\<^sub>t\<^sub>p:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')" "\<forall>S \<in> \<S> \<union> {to_st \<A>}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  shows "\<forall>S \<in> \<S>' \<union> {to_st \<A>'}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
using assms
proof (induction rule: rtranclp_induct2)
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  from step.hyps(2) step.IH[OF step.prems] show ?case
  proof (induction rule: pts_symbolic_c_induct)
    case Nil
    have 1: "\<forall>S \<in> {to_st \<A>2}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Nil by simp
    have 2: "\<S>2 = \<S>1 - {[]}" "\<forall>S \<in> \<S>1. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"  using Nil by simp_all
    have "\<forall>S \<in> \<S>2. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    proof
      fix S assume "S \<in> \<S>2"
      hence "S \<in> \<S>1" using 2(1) by simp
      thus "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using 2(2) by simp
    qed
    thus ?case using 1 by auto
  next
    case (Send t S)
    have 1: "\<forall>S \<in> {to_st \<A>2}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Send by (simp add: to_st_append)
    have 2: "\<S>2 = insert S (\<S>1 - {send\<langle>t\<rangle>\<^sub>s\<^sub>t#S})" "\<forall>S \<in> \<S>1. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"  using Send by simp_all
    have 3: "\<forall>S \<in> \<S>2. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    proof
      fix S' assume "S' \<in> \<S>2"
      hence "S' \<in> \<S>1 \<or> S' = S" using 2(1) by auto
      moreover have "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Send.hyps 2(2) by auto
      ultimately show "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'" using 2(2) by blast
    qed
    thus ?case using 1 by auto
  next
    case (Receive t S)
    have 1: "\<forall>S \<in> {to_st \<A>2}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Receive by (simp add: to_st_append)
    have 2: "\<S>2 = insert S (\<S>1 - {receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S})" "\<forall>S \<in> \<S>1. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
      using Receive by simp_all
    have 3: "\<forall>S \<in> \<S>2. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    proof
      fix S' assume "S' \<in> \<S>2"
      hence "S' \<in> \<S>1 \<or> S' = S" using 2(1) by auto
      moreover have "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Receive.hyps 2(2) by auto
      ultimately show "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'" using 2(2) by blast
    qed
    show ?case using 1 3 by auto
  next
    case (Equality a t t' S)
    have 1: "to_st \<A>2 = to_st \<A>1@[\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t]" "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>1)"
      using Equality by (simp_all add: to_st_append)
    have 2: "list_all tfr\<^sub>s\<^sub>t\<^sub>p [\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t]" using Equality by fastforce
    have 3: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>2)"
      using tfr_stp_all_append[of "to_st \<A>1" "[\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t]"] 1 2 by metis
    hence 4: "\<forall>S \<in> {to_st \<A>2}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Equality by simp
    have 5: "\<S>2 = insert S (\<S>1 - {\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S})" "\<forall>S \<in> \<S>1. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
      using Equality by simp_all
    have 6: "\<forall>S \<in> \<S>2. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    proof
      fix S' assume "S' \<in> \<S>2"
      hence "S' \<in> \<S>1 \<or> S' = S" using 5(1) by auto
      moreover have "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Equality.hyps 5(2) by auto
      ultimately show "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'" using 5(2) by blast
    qed
    thus ?case using 4 by auto
  next
    case (Inequality X F S)
    have 1: "to_st \<A>2 = to_st \<A>1@[\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]" "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>1)"
      using Inequality by (simp_all add: to_st_append)
    have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S)" using Inequality(1,4) by blast
    hence 2: "list_all tfr\<^sub>s\<^sub>t\<^sub>p [\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]" by simp
    have 3: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>2)"
      using tfr_stp_all_append[of "to_st \<A>1" "[\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]"] 1 2 by metis
    hence 4: "\<forall>S \<in> {to_st \<A>2}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Inequality by simp
    have 5: "\<S>2 = insert S (\<S>1 - {\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S})" "\<forall>S \<in> \<S>1. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
      using Inequality by simp_all
    have 6: "\<forall>S \<in> \<S>2. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    proof
      fix S' assume "S' \<in> \<S>2"
      hence "S' \<in> \<S>1 \<or> S' = S" using 5(1) by auto
      moreover have "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Inequality.hyps 5(2) by auto
      ultimately show "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'" using 5(2) by blast
    qed
    thus ?case using 4 by auto
  next
    case (Decompose f T)
    hence 1: "\<forall>S \<in> \<S>2. list_all tfr\<^sub>s\<^sub>t\<^sub>p S" by blast
    have 2: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>1)" "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st [Decomp (Fun f T)])"
      using Decompose.prems decomp_tfr\<^sub>s\<^sub>t\<^sub>p by auto
    hence "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>1@to_st [Decomp (Fun f T)])" by auto
    hence "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>2)"
      using Decompose.hyps(3) to_st_append[of \<A>1 "[Decomp (Fun f T)]"]
      by auto
    thus ?case using 1 by blast
  qed
qed

private lemma pts_symbolic_c_preserves_well_analyzed:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')" "well_analyzed \<A>"
  shows "well_analyzed \<A>'"
using assms
proof (induction rule: rtranclp_induct2)
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  from step.hyps(2) step.IH[OF step.prems] show ?case
  proof (induction rule: pts_symbolic_c_induct)
    case Receive thus ?case by (metis well_analyzed_singleton(1) well_analyzed_append)
  next
    case Send thus ?case by (metis well_analyzed_singleton(2) well_analyzed_append)
  next
    case Equality thus ?case by (metis well_analyzed_singleton(3) well_analyzed_append)
  next
    case Inequality thus ?case by (metis well_analyzed_singleton(4) well_analyzed_append)
  next
    case (Decompose f T)
    hence "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1) - (Var`\<V>)" by auto
    thus ?case by (metis well_analyzed.Decomp Decompose.prems Decompose.hyps(3))
  qed simp
qed metis

private lemma pts_symbolic_c_preserves_Ana_invar_subst:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')"
    and "Ana_invar_subst (
          (\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>)) \<union>
          (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>)))"
  shows "Ana_invar_subst (
          (\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>') \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>')) \<union>
          (\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>') \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>')))"
using assms
proof (induction rule: rtranclp_induct2)
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  from step.hyps(2) step.IH[OF step.prems] show ?case
  proof (induction rule: pts_symbolic_c_induct)
    case Nil
    hence "\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>1) = \<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>2)"
          "\<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>1) = \<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>2)"
      by force+
    thus ?case using Nil by metis
  next
    case Send show ?case
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_snd[OF Send.hyps]
            Ana_invar_subst_subset[OF Send.prems]
      by (metis Un_mono)
  next
    case Receive show ?case
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_rcv[OF Receive.hyps]
            Ana_invar_subst_subset[OF Receive.prems]
      by (metis Un_mono)
  next
    case Equality show ?case
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_eq[OF Equality.hyps]
            Ana_invar_subst_subset[OF Equality.prems]
      by (metis Un_mono)
  next
    case Inequality show ?case
      using ik\<^sub>s\<^sub>t_update\<^sub>s\<^sub>t_subset_ineq[OF Inequality.hyps]
            Ana_invar_subst_subset[OF Inequality.prems]
      by (metis Un_mono)
  next
    case (Decompose f T)
    let ?X = "\<Union>(assignment_rhs\<^sub>s\<^sub>t`\<S>2) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>2"
    let ?Y = "\<Union>(assignment_rhs\<^sub>s\<^sub>t`\<S>1) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1"
    obtain K M where Ana: "Ana (Fun f T) = (K,M)" by moura
    hence *: "ik\<^sub>e\<^sub>s\<^sub>t \<A>2 = ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> set M" "assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>2 = assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1"
      using ik\<^sub>e\<^sub>s\<^sub>t_append assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append decomp_ik
            decomp_assignment_rhs_empty Decompose.hyps(3)
      by auto
    { fix g S assume "Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t`\<S>2) \<union> ik\<^sub>e\<^sub>s\<^sub>t \<A>2 \<union> ?X)"
      hence "Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>1) \<union> ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> set M \<union> ?X)"
        using * Decompose.hyps(2) by auto
      hence "Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>1))
            \<or> Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A>1)
            \<or> Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set M)
            \<or> Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<Union>(assignment_rhs\<^sub>s\<^sub>t`\<S>1))
            \<or> Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1)"
        using Decompose * Ana_fun_subterm[OF Ana] by auto
      moreover have "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1)"
        using trms\<^sub>e\<^sub>s\<^sub>t_ik_subtermsI Decompose.hyps(1) by auto
      hence "subterms (Fun f T) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1)"
        by (metis in_subterms_subset_Union)
      hence "subterms\<^sub>s\<^sub>e\<^sub>t (set M) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1)"
        by (meson Un_upper2 Ana_subterm[OF Ana] subterms_subset_set psubsetE subset_trans)
      ultimately have "Fun g S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t ` \<S>1) \<union> ik\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> ?Y)"
        by auto
    }
    thus ?case using Decompose unfolding Ana_invar_subst_def by metis
  qed
qed

private lemma pts_symbolic_c_preserves_constr_disj_vars:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')" "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>" "fv\<^sub>e\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>e\<^sub>s\<^sub>t \<A> = {}"
  shows "fv\<^sub>e\<^sub>s\<^sub>t \<A>' \<inter> bvars\<^sub>e\<^sub>s\<^sub>t \<A>' = {}"
using assms
proof (induction rule: rtranclp_induct2)
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  have *: "\<And>S. S \<in> \<S>1 \<Longrightarrow> fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t \<A>1 = {}" "\<And>S. S \<in> \<S>1 \<Longrightarrow> fv\<^sub>e\<^sub>s\<^sub>t \<A>1 \<inter> bvars\<^sub>s\<^sub>t S = {}"
    using pts_symbolic_c_preserves_wf_prot[OF step.hyps(1) step.prems(1)]
    unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def by auto
  from step.hyps(2) step.IH[OF step.prems]
  show ?case
  proof (induction rule: pts_symbolic_c_induct)
    case Nil thus ?case by auto
  next
    case (Send t S)
    hence "fv\<^sub>e\<^sub>s\<^sub>t \<A>2 = fv\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> fv t" "bvars\<^sub>e\<^sub>s\<^sub>t \<A>2 = bvars\<^sub>e\<^sub>s\<^sub>t \<A>1"
          "fv\<^sub>s\<^sub>t (send\<langle>t\<rangle>\<^sub>s\<^sub>t#S) = fv t \<union> fv\<^sub>s\<^sub>t S"
      using fv\<^sub>e\<^sub>s\<^sub>t_append bvars\<^sub>e\<^sub>s\<^sub>t_append by simp+
    thus ?case using *(1)[OF Send(1)] Send(4) by auto
  next
    case (Receive t S)
    hence "fv\<^sub>e\<^sub>s\<^sub>t \<A>2 = fv\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> fv t" "bvars\<^sub>e\<^sub>s\<^sub>t \<A>2 = bvars\<^sub>e\<^sub>s\<^sub>t \<A>1"
          "fv\<^sub>s\<^sub>t (receive\<langle>t\<rangle>\<^sub>s\<^sub>t#S) = fv t \<union> fv\<^sub>s\<^sub>t S"
      using fv\<^sub>e\<^sub>s\<^sub>t_append bvars\<^sub>e\<^sub>s\<^sub>t_append by simp+
    thus ?case using *(1)[OF Receive(1)] Receive(4) by auto
  next
    case (Equality a t t' S)
    hence "fv\<^sub>e\<^sub>s\<^sub>t \<A>2 = fv\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> fv t \<union> fv t'" "bvars\<^sub>e\<^sub>s\<^sub>t \<A>2 = bvars\<^sub>e\<^sub>s\<^sub>t \<A>1"
          "fv\<^sub>s\<^sub>t (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t#S) = fv t \<union> fv t' \<union> fv\<^sub>s\<^sub>t S"
      using fv\<^sub>e\<^sub>s\<^sub>t_append bvars\<^sub>e\<^sub>s\<^sub>t_append by fastforce+
    thus ?case using *(1)[OF Equality(1)] Equality(4) by auto
  next
    case (Inequality X F S)
    hence "fv\<^sub>e\<^sub>s\<^sub>t \<A>2 = fv\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X)" "bvars\<^sub>e\<^sub>s\<^sub>t \<A>2 = bvars\<^sub>e\<^sub>s\<^sub>t \<A>1 \<union> set X"
          "fv\<^sub>s\<^sub>t (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t#S) = (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X) \<union> fv\<^sub>s\<^sub>t S"
      using fv\<^sub>e\<^sub>s\<^sub>t_append bvars\<^sub>e\<^sub>s\<^sub>t_append strand_vars_split(3)[of "[\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t]" S]
      by auto+
    moreover have "fv\<^sub>e\<^sub>s\<^sub>t \<A>1 \<inter> set X = {}" using *(2)[OF Inequality(1)] by auto
    ultimately show ?case using *(1)[OF Inequality(1)] Inequality(4) by auto
  next
    case (Decompose f T)
    thus ?case
      using Decompose(3,4) bvars_decomp ik_assignment_rhs_decomp_fv[OF Decompose(1)] by auto
  qed
qed


subsubsection \<open>Theorem: The Typing Result Lifted to the Transition System Level\<close>
private lemma wf\<^sub>s\<^sub>t\<^sub>s'_decomp_rm:
  assumes "well_analyzed A" "wf\<^sub>s\<^sub>t\<^sub>s' S (decomp_rm\<^sub>e\<^sub>s\<^sub>t A)" shows "wf\<^sub>s\<^sub>t\<^sub>s' S A"
unfolding wf\<^sub>s\<^sub>t\<^sub>s'_def
proof (intro conjI)
  show "\<forall>S\<in>S. wf\<^sub>s\<^sub>t (wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t A) (dual\<^sub>s\<^sub>t S)"
    by (metis (no_types) assms(2) wf\<^sub>s\<^sub>t\<^sub>s'_def wfrestrictedvars\<^sub>e\<^sub>s\<^sub>t_decomp_rm\<^sub>e\<^sub>s\<^sub>t_subset
                wf_vars_mono le_iff_sup)

  show "\<forall>Sa\<in>S. \<forall>S'\<in>S. fv\<^sub>s\<^sub>t Sa \<inter> bvars\<^sub>s\<^sub>t S' = {}" by (metis assms(2) wf\<^sub>s\<^sub>t\<^sub>s'_def)

  show "\<forall>S\<in>S. fv\<^sub>s\<^sub>t S \<inter> bvars\<^sub>e\<^sub>s\<^sub>t A = {}" by (metis assms(2) wf\<^sub>s\<^sub>t\<^sub>s'_def bvars_decomp_rm)

  show "\<forall>S\<in>S. fv\<^sub>e\<^sub>s\<^sub>t A \<inter> bvars\<^sub>s\<^sub>t S = {}" by (metis assms wf\<^sub>s\<^sub>t\<^sub>s'_def well_analyzed_decomp_rm\<^sub>e\<^sub>s\<^sub>t_fv)
qed

private lemma decomps\<^sub>e\<^sub>s\<^sub>t_pts_symbolic_c:
  assumes "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<I>"
  shows "(S,A) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (S,A@D)"
using assms(1)
proof (induction D rule: decomps\<^sub>e\<^sub>s\<^sub>t.induct)
  case (Decomp B f X K T)
  have "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t A \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t A) \<subseteq>
        subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t (A@B) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@B))"
    using ik\<^sub>e\<^sub>s\<^sub>t_append[of A B] assignment_rhs\<^sub>e\<^sub>s\<^sub>t_append[of A B]
    by auto
  hence "Fun f X \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t (A@B) \<union> assignment_rhs\<^sub>e\<^sub>s\<^sub>t (A@B))" using Decomp.hyps by auto
  hence "(S,A@B) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (S,A@B@[Decomp (Fun f X)])"
    using pts_symbolic_c.Decompose[of f X "A@B"]
    by simp
  thus ?case
    using Decomp.IH rtrancl_into_rtrancl
          rtranclp_rtrancl_eq[of pts_symbolic_c "(S,A)" "(S,A@B)"]
    by auto
qed simp

private lemma pts_symbolic_to_pts_symbolic_c:
  assumes "(\<S>,to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d)) \<Rightarrow>\<^sup>\<bullet>\<^sup>* (\<S>',\<A>')" "sem\<^sub>e\<^sub>s\<^sub>t_d {} \<I> (to_est \<A>')" "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> \<A>\<^sub>d"
  and wf: "wf\<^sub>s\<^sub>t\<^sub>s' \<S> (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d)" "wf\<^sub>e\<^sub>s\<^sub>t {} \<A>\<^sub>d"
  and tar: "Ana_invar_subst ((\<Union>(ik\<^sub>s\<^sub>t` dual\<^sub>s\<^sub>t` \<S>) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d))
                            \<union> (\<Union>(assignment_rhs\<^sub>s\<^sub>t` \<S>) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d)))"
  and wa: "well_analyzed \<A>\<^sub>d"
  and \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<exists>\<A>\<^sub>d'. \<A>' = to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d') \<and> (\<S>,\<A>\<^sub>d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>\<^sub>d') \<and> sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> \<A>\<^sub>d'"
using assms(1,2)
proof (induction rule: rtranclp_induct2)
  case refl thus ?case using assms by auto
next
  case (step \<S>1 \<A>1 \<S>2 \<A>2)
  have "sem\<^sub>e\<^sub>s\<^sub>t_d {} \<I> (to_est \<A>1)" using step.hyps(2) step.prems
    by (induct rule: pts_symbolic_induct, metis, (metis sem\<^sub>e\<^sub>s\<^sub>t_d_split_left to_est_append)+)
  then obtain \<A>1d where
      \<A>1d: "\<A>1 = to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>1d)" "(\<S>, \<A>\<^sub>d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>1, \<A>1d)" "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> \<A>1d"
    using step.IH by moura

  show ?case using step.hyps(2)
  proof (induction rule: pts_symbolic_induct)
    case Nil
    hence "(\<S>, \<A>\<^sub>d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>2, \<A>1d)" using \<A>1d pts_symbolic_c.Nil[OF Nil.hyps(1), of \<A>1d] by simp
    thus ?case using \<A>1d Nil by auto
  next
    case (Send t S)
    hence "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> (\<A>1d@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)])" using sem\<^sub>e\<^sub>s\<^sub>t_c.Receive[OF \<A>1d(3)] by simp
    moreover have "(\<S>1, \<A>1d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (\<S>2, \<A>1d@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
      using Send.hyps(2) pts_symbolic_c.Send[OF Send.hyps(1), of \<A>1d] by simp
    moreover have "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t (\<A>1d@[Step (receive\<langle>t\<rangle>\<^sub>s\<^sub>t)])) = \<A>2"
      using Send.hyps(3) decomp_rm\<^sub>e\<^sub>s\<^sub>t_append \<A>1d(1) by (simp add: to_st_append)
    ultimately show ?case using \<A>1d(2) by auto
  next
    case (Equality a t t' S)
    hence "t \<cdot> \<I> = t' \<cdot> \<I>"
      using step.prems sem\<^sub>e\<^sub>s\<^sub>t_d_eq_sem_st[of "{}" \<I> "to_est \<A>2"]
            to_st_append to_est_append to_st_to_est_inv
      by auto
    hence "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> (\<A>1d@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)])" using sem\<^sub>e\<^sub>s\<^sub>t_c.Equality[OF \<A>1d(3)] by simp
    moreover have "(\<S>1, \<A>1d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (\<S>2, \<A>1d@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)])"
      using Equality.hyps(2) pts_symbolic_c.Equality[OF Equality.hyps(1), of \<A>1d] by simp
    moreover have "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t (\<A>1d@[Step (\<langle>a: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t)])) = \<A>2"
      using Equality.hyps(3) decomp_rm\<^sub>e\<^sub>s\<^sub>t_append \<A>1d(1) by (simp add: to_st_append)
    ultimately show ?case using \<A>1d(2) by auto
  next
    case (Inequality X F S)
    hence "ineq_model \<I> X F"
      using step.prems sem\<^sub>e\<^sub>s\<^sub>t_d_eq_sem_st[of "{}" \<I> "to_est \<A>2"]
            to_st_append to_est_append to_st_to_est_inv
      by auto
    hence "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> (\<A>1d@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)])" using sem\<^sub>e\<^sub>s\<^sub>t_c.Inequality[OF \<A>1d(3)] by simp
    moreover have "(\<S>1, \<A>1d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c (\<S>2, \<A>1d@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)])"
      using Inequality.hyps(2) pts_symbolic_c.Inequality[OF Inequality.hyps(1), of \<A>1d] by simp
    moreover have "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t (\<A>1d@[Step (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t)])) = \<A>2"
      using Inequality.hyps(3) decomp_rm\<^sub>e\<^sub>s\<^sub>t_append \<A>1d(1) by (simp add: to_st_append)
    ultimately show ?case using \<A>1d(2) by auto
  next
    case (Receive t S)
    hence "ik\<^sub>s\<^sub>t \<A>1 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>"
      using step.prems sem\<^sub>e\<^sub>s\<^sub>t_d_eq_sem_st[of "{}" \<I> "to_est \<A>2"]
            strand_sem_split(4)[of "{}" \<A>1 "[send\<langle>t\<rangle>\<^sub>s\<^sub>t]" \<I>]
            to_st_append to_est_append to_st_to_est_inv
      by auto
    moreover have "ik\<^sub>s\<^sub>t \<A>1 \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> ik\<^sub>e\<^sub>s\<^sub>t \<A>1d \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using \<A>1d(1) decomp_rm\<^sub>e\<^sub>s\<^sub>t_ik_subset by auto
    ultimately have *: "ik\<^sub>e\<^sub>s\<^sub>t \<A>1d \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<I>" using ideduct_mono by auto

    have "wf\<^sub>s\<^sub>t\<^sub>s' \<S> \<A>\<^sub>d" by (rule wf\<^sub>s\<^sub>t\<^sub>s'_decomp_rm[OF wa assms(4)])
    hence **: "wf\<^sub>e\<^sub>s\<^sub>t {} \<A>1d" by (rule pts_symbolic_c_preserves_wf_is[OF \<A>1d(2) _ assms(5)])

    have "Ana_invar_subst (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t`\<S>1) \<union> (ik\<^sub>e\<^sub>s\<^sub>t \<A>1d) \<union>
                           (\<Union>(assignment_rhs\<^sub>s\<^sub>t`\<S>1) \<union> (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1d)))"
      using tar \<A>1d(2) pts_symbolic_c_preserves_Ana_invar_subst by metis
    hence "Ana_invar_subst (ik\<^sub>e\<^sub>s\<^sub>t \<A>1d)" "Ana_invar_subst (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1d)"
      using Ana_invar_subst_subset by blast+
    moreover have "well_analyzed \<A>1d"
      using pts_symbolic_c_preserves_well_analyzed[OF \<A>1d(2) wa] by metis
    ultimately obtain D where D:
        "D \<in> decomps\<^sub>e\<^sub>s\<^sub>t (ik\<^sub>e\<^sub>s\<^sub>t \<A>1d) (assignment_rhs\<^sub>e\<^sub>s\<^sub>t \<A>1d) \<I>"
        "ik\<^sub>e\<^sub>s\<^sub>t (\<A>1d@D) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>"
      using decomps\<^sub>e\<^sub>s\<^sub>t_exist_subst[OF * \<A>1d(3) ** assms(8)] unfolding Ana_invar_subst_def by auto

    have "(\<S>, \<A>\<^sub>d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>1, \<A>1d@D)" using \<A>1d(2) decomps\<^sub>e\<^sub>s\<^sub>t_pts_symbolic_c[OF D(1), of \<S>1] by auto
    hence "(\<S>, \<A>\<^sub>d) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>2, \<A>1d@D@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
      using Receive(2) pts_symbolic_c.Receive[OF Receive.hyps(1), of "\<A>1d@D"] by auto
    moreover have "\<A>2 = to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t (\<A>1d@D@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)]))"
      using Receive.hyps(3) \<A>1d(1) decomps\<^sub>e\<^sub>s\<^sub>t_decomp_rm\<^sub>e\<^sub>s\<^sub>t_empty[OF D(1)]
            decomp_rm\<^sub>e\<^sub>s\<^sub>t_append to_st_append
      by auto
    moreover have "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> (\<A>1d@D@[Step (send\<langle>t\<rangle>\<^sub>s\<^sub>t)])"
      using D(2) sem\<^sub>e\<^sub>s\<^sub>t_c.Send[OF sem\<^sub>e\<^sub>s\<^sub>t_c_decomps\<^sub>e\<^sub>s\<^sub>t_append[OF \<A>1d(3) D(1)]] by simp
    ultimately show ?case by auto
  qed
qed

private lemma pts_symbolic_c_to_pts_symbolic:
  assumes "(\<S>,\<A>) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>',\<A>')" "sem\<^sub>e\<^sub>s\<^sub>t_c {} \<I> \<A>'"
  shows "(\<S>,to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>)) \<Rightarrow>\<^sup>\<bullet>\<^sup>* (\<S>',to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>'))"
        "sem\<^sub>e\<^sub>s\<^sub>t_d {} \<I> (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>')"
proof -
  show "(\<S>,to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>)) \<Rightarrow>\<^sup>\<bullet>\<^sup>* (\<S>',to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>'))" using assms(1)
  proof (induction rule: rtranclp_induct2)
    case (step \<S>1 \<A>1 \<S>2 \<A>2) show ?case using step.hyps(2,1) step.IH
    proof (induction rule: pts_symbolic_c_induct)
      case Nil thus ?case
        using pts_symbolic.Nil[OF Nil.hyps(1), of "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>1)"] by simp
    next
      case (Send t S) thus ?case
        using pts_symbolic.Send[OF Send.hyps(1), of "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>1)"]
        by (simp add: decomp_rm\<^sub>e\<^sub>s\<^sub>t_append to_st_append)
    next
      case (Receive t S) thus ?case
        using pts_symbolic.Receive[OF Receive.hyps(1), of "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>1)"]
        by (simp add: decomp_rm\<^sub>e\<^sub>s\<^sub>t_append to_st_append)
    next
      case (Equality a t t' S) thus ?case
        using pts_symbolic.Equality[OF Equality.hyps(1), of "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>1)"]
        by (simp add: decomp_rm\<^sub>e\<^sub>s\<^sub>t_append to_st_append)
    next
      case (Inequality t t' S) thus ?case
        using pts_symbolic.Inequality[OF Inequality.hyps(1), of "to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>1)"]
        by (simp add: decomp_rm\<^sub>e\<^sub>s\<^sub>t_append to_st_append)
    next
      case (Decompose t) thus ?case using decomp_rm\<^sub>e\<^sub>s\<^sub>t_append by simp
    qed
  qed simp
qed (rule sem\<^sub>e\<^sub>s\<^sub>t_d_decomp_rm\<^sub>e\<^sub>s\<^sub>t_if_sem\<^sub>e\<^sub>s\<^sub>t_c[OF assms(2)])

private lemma pts_symbolic_to_pts_symbolic_c_from_initial:
  assumes "(\<S>\<^sub>0,[]) \<Rightarrow>\<^sup>\<bullet>\<^sup>* (\<S>,\<A>)" "\<I> \<Turnstile> \<langle>\<A>\<rangle>" "wf\<^sub>s\<^sub>t\<^sub>s' \<S>\<^sub>0 []"
  and "Ana_invar_subst (\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>\<^sub>0) \<union> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>\<^sub>0))" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
  shows "\<exists>\<A>\<^sub>d. \<A> = to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d) \<and> (\<S>\<^sub>0,[]) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>,\<A>\<^sub>d) \<and> (\<I> \<Turnstile>\<^sub>c \<langle>to_st \<A>\<^sub>d\<rangle>)"
using assms pts_symbolic_to_pts_symbolic_c[of \<S>\<^sub>0 "[]" \<S> \<A> \<I>]
      sem\<^sub>e\<^sub>s\<^sub>t_c_eq_sem_st[of "{}" \<I>] sem\<^sub>e\<^sub>s\<^sub>t_d_eq_sem_st[of "{}" \<I>]
      to_st_to_est_inv[of \<A>] strand_sem_eq_defs
by (auto simp add: constr_sem_c_def constr_sem_d_def simp del: subst_range.simps)

private lemma pts_symbolic_c_to_pts_symbolic_from_initial:
  assumes "(\<S>\<^sub>0,[]) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>,\<A>)" "\<I> \<Turnstile>\<^sub>c \<langle>to_st \<A>\<rangle>"
  shows "(\<S>\<^sub>0,[]) \<Rightarrow>\<^sup>\<bullet>\<^sup>* (\<S>,to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>))" "\<I> \<Turnstile> \<langle>to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>)\<rangle>"
using assms pts_symbolic_c_to_pts_symbolic[of \<S>\<^sub>0 "[]" \<S> \<A> \<I>]
      sem\<^sub>e\<^sub>s\<^sub>t_c_eq_sem_st[of "{}" \<I>] sem\<^sub>e\<^sub>s\<^sub>t_d_eq_sem_st[of "{}" \<I>] strand_sem_eq_defs
by (auto simp add: constr_sem_c_def constr_sem_d_def)

private lemma to_st_trms_wf:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>e\<^sub>s\<^sub>t A)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t (to_st A))"
using assms
proof (induction A)
  case (Cons x A)
  hence IH: "\<forall>t \<in> trms\<^sub>s\<^sub>t (to_st A). wf\<^sub>t\<^sub>r\<^sub>m t" by auto
  with Cons show ?case
  proof (cases x)
    case (Decomp t)
    hence "wf\<^sub>t\<^sub>r\<^sub>m t" using Cons.prems by auto
    obtain K T where Ana_t: "Ana t = (K,T)" by moura
    hence "trms\<^sub>s\<^sub>t (decomp t) \<subseteq> {t} \<union> set K \<union> set T" using decomp_set_unfold[OF Ana_t] by force
    moreover have "\<forall>t \<in> set T. wf\<^sub>t\<^sub>r\<^sub>m t" using Ana_subterm[OF Ana_t] \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close> wf_trm_subterm by auto
    ultimately have "\<forall>t \<in> trms\<^sub>s\<^sub>t (decomp t). wf\<^sub>t\<^sub>r\<^sub>m t" using Ana_keys_wf'[OF Ana_t] \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close> by auto
    thus ?thesis using IH Decomp by auto
  qed auto
qed simp

private lemma to_st_trms_SMP_subset: "trms\<^sub>s\<^sub>t (to_st A) \<subseteq> SMP (trms\<^sub>e\<^sub>s\<^sub>t A)"
proof
  fix t assume "t \<in> trms\<^sub>s\<^sub>t (to_st A)" thus "t \<in> SMP (trms\<^sub>e\<^sub>s\<^sub>t A)"
  proof (induction A)
    case (Cons x A)
    hence *: "t \<in> trms\<^sub>s\<^sub>t (to_st [x]) \<union> trms\<^sub>s\<^sub>t (to_st A)" using to_st_append[of "[x]" A] by auto
    have **: "trms\<^sub>s\<^sub>t (to_st A) \<subseteq> trms\<^sub>s\<^sub>t (to_st (x#A))" "trms\<^sub>e\<^sub>s\<^sub>t A \<subseteq> trms\<^sub>e\<^sub>s\<^sub>t (x#A)"
      using to_st_append[of "[x]" A] by auto
    show ?case
    proof (cases "t \<in> trms\<^sub>s\<^sub>t (to_st A)")
      case True thus ?thesis using Cons.IH SMP_mono[OF **(2)] by auto
    next
      case False
      hence ***: "t \<in> trms\<^sub>s\<^sub>t (to_st [x])" using * by auto
      thus ?thesis
      proof (cases x)
        case (Decomp t')
        hence ****: "t \<in> trms\<^sub>s\<^sub>t (decomp t')" "t' \<in> trms\<^sub>e\<^sub>s\<^sub>t (x#A)" using *** by auto
        obtain K T where Ana_t': "Ana t' = (K,T)" by moura
        hence "t \<in> {t'} \<union> set K \<union> set T" using decomp_set_unfold[OF Ana_t'] ****(1) by force
        moreover
        { assume "t = t'" hence ?thesis using SMP.MP[OF ****(2)] by simp }
        moreover
        { assume "t \<in> set K" hence ?thesis using SMP.Ana[OF SMP.MP[OF ****(2)] Ana_t'] by auto }
        moreover
        { assume "t \<in> set T" "t \<noteq> t'"
          hence "t \<sqsubset> t'" using Ana_subterm[OF Ana_t'] by blast
          hence ?thesis using SMP.Subterm[OF SMP.MP[OF ****(2)]] by auto
        }
        ultimately show ?thesis using Decomp by auto
      qed auto
    qed
  qed simp
qed

private lemma to_st_trms_tfr\<^sub>s\<^sub>e\<^sub>t:
  assumes "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>e\<^sub>s\<^sub>t A)"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t (to_st A))"
proof -
  have *: "trms\<^sub>s\<^sub>t (to_st A) \<subseteq> SMP (trms\<^sub>e\<^sub>s\<^sub>t A)"
    using to_st_trms_wf to_st_trms_SMP_subset assms unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by auto
  have "trms\<^sub>s\<^sub>t (to_st A) = trms\<^sub>s\<^sub>t (to_st A) \<union> trms\<^sub>e\<^sub>s\<^sub>t A" by (blast dest!: trms\<^sub>e\<^sub>s\<^sub>tD)
  hence "SMP (trms\<^sub>e\<^sub>s\<^sub>t A) = SMP (trms\<^sub>s\<^sub>t (to_st A))" using SMP_subset_union_eq[OF *] by auto
  thus ?thesis using * assms unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by presburger
qed

theorem wt_attack_if_tfr_attack_pts:
  assumes "wf\<^sub>s\<^sub>t\<^sub>s \<S>\<^sub>0" "tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>s\<^sub>t ` \<S>\<^sub>0))" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>s\<^sub>t ` \<S>\<^sub>0))" "\<forall>S \<in> \<S>\<^sub>0. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  and "Ana_invar_subst (\<Union>(ik\<^sub>s\<^sub>t ` dual\<^sub>s\<^sub>t ` \<S>\<^sub>0) \<union> \<Union>(assignment_rhs\<^sub>s\<^sub>t ` \<S>\<^sub>0))"
  and "(\<S>\<^sub>0,[]) \<Rightarrow>\<^sup>\<bullet>\<^sup>* (\<S>,\<A>)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "\<I> \<Turnstile> \<langle>\<A>, Var\<rangle>"
  shows "\<exists>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> (\<I>\<^sub>\<tau> \<Turnstile> \<langle>\<A>, Var\<rangle>) \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
proof -
  have "(\<Union>(trms\<^sub>s\<^sub>t ` \<S>\<^sub>0)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t []) = \<Union>(trms\<^sub>s\<^sub>t ` \<S>\<^sub>0)" "to_st [] = []" "list_all tfr\<^sub>s\<^sub>t\<^sub>p []"
    using assms by simp_all
  hence *: "tfr\<^sub>s\<^sub>e\<^sub>t ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>\<^sub>0)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t []))"
           "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s ((\<Union>(trms\<^sub>s\<^sub>t ` \<S>\<^sub>0)) \<union> (trms\<^sub>e\<^sub>s\<^sub>t []))"
           "wf\<^sub>s\<^sub>t\<^sub>s' \<S>\<^sub>0 []" "\<forall>S \<in> \<S>\<^sub>0 \<union> {to_st []}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    using assms wf\<^sub>s\<^sub>t\<^sub>s_wf\<^sub>s\<^sub>t\<^sub>s' by (metis, metis, metis, simp)

  obtain \<A>\<^sub>d where \<A>\<^sub>d: "\<A> = to_st (decomp_rm\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d)" "(\<S>\<^sub>0,[]) \<Rightarrow>\<^sup>\<bullet>\<^sub>c\<^sup>* (\<S>,\<A>\<^sub>d)" "\<I> \<Turnstile>\<^sub>c \<langle>to_st \<A>\<^sub>d\<rangle>"
    using pts_symbolic_to_pts_symbolic_c_from_initial assms *(3) by metis
  hence "tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>s\<^sub>t ` \<S>) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d))" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>s\<^sub>t ` \<S>) \<union> (trms\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d))"
    using pts_symbolic_c_preserves_tfr\<^sub>s\<^sub>e\<^sub>t[OF _ *(1,2)] by blast+
  hence "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d)"
    unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by (metis DiffE DiffI SMP_union UnCI, metis UnCI)
  hence "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t (to_st \<A>\<^sub>d))" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t (to_st \<A>\<^sub>d))"
    by (metis to_st_trms_tfr\<^sub>s\<^sub>e\<^sub>t, metis to_st_trms_wf)
  moreover have "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r (to_st \<A>\<^sub>d) Var"
  proof -
    have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)" "subst_domain Var \<inter> vars\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d = {}"
         "range_vars Var \<inter> bvars\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d = {}"
      by (simp_all add: range_vars_alt_def)
    moreover have "wf\<^sub>e\<^sub>s\<^sub>t {} \<A>\<^sub>d"
      using pts_symbolic_c_preserves_wf_is[OF \<A>\<^sub>d(2) *(3), of "{}"]
      by auto
    moreover have "fv\<^sub>s\<^sub>t (to_st \<A>\<^sub>d) \<inter> bvars\<^sub>e\<^sub>s\<^sub>t \<A>\<^sub>d = {}"
      using pts_symbolic_c_preserves_constr_disj_vars[OF \<A>\<^sub>d(2)] assms(1) wf\<^sub>s\<^sub>t\<^sub>s_wf\<^sub>s\<^sub>t\<^sub>s'
      by fastforce
    ultimately show ?thesis unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by simp
  qed
  moreover have "list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>\<^sub>d)"
    using pts_symbolic_c_preserves_tfr\<^sub>s\<^sub>t\<^sub>p[OF \<A>\<^sub>d(2) *(4)] by blast
  moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)" by simp_all
  ultimately obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>:
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "\<I>\<^sub>\<tau> \<Turnstile>\<^sub>c \<langle>to_st \<A>\<^sub>d, Var\<rangle>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
    using wt_attack_if_tfr_attack[OF assms(7) \<A>\<^sub>d(3)]
          \<open>tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t (to_st \<A>\<^sub>d))\<close> \<open>list_all tfr\<^sub>s\<^sub>t\<^sub>p (to_st \<A>\<^sub>d)\<close>
    unfolding tfr\<^sub>s\<^sub>t_def by metis
  hence "\<I>\<^sub>\<tau> \<Turnstile> \<langle>\<A>, Var\<rangle>" using pts_symbolic_c_to_pts_symbolic_from_initial \<A>\<^sub>d by metis
  thus ?thesis using \<I>\<^sub>\<tau>(1,3,4) by metis
qed


subsubsection \<open>Corollary: The Typing Result on the Level of Constraints\<close>
text \<open>There exists well-typed models of satisfiable type-flaw resistant constraints\<close>
corollary wt_attack_if_tfr_attack_d:
  assumes "wf\<^sub>s\<^sub>t {} \<A>" "fv\<^sub>s\<^sub>t \<A> \<inter> bvars\<^sub>s\<^sub>t \<A> = {}" "tfr\<^sub>s\<^sub>t \<A>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t \<A>)"
  and "Ana_invar_subst (ik\<^sub>s\<^sub>t \<A> \<union> assignment_rhs\<^sub>s\<^sub>t \<A>)"
  and "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "\<I> \<Turnstile> \<langle>\<A>\<rangle>"
  shows "\<exists>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> (\<I>\<^sub>\<tau> \<Turnstile> \<langle>\<A>\<rangle>) \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
proof -
  { fix S A have "({S},A) \<Rightarrow>\<^sup>\<bullet>\<^sup>* ({},A@dual\<^sub>s\<^sub>t S)"
    proof (induction S arbitrary: A)
      case Nil thus ?case using pts_symbolic.Nil[of "{[]}"] by auto
    next
      case (Cons x S)
      hence "({S}, A@dual\<^sub>s\<^sub>t [x]) \<Rightarrow>\<^sup>\<bullet>\<^sup>* ({}, A@dual\<^sub>s\<^sub>t (x#S))"
        by (metis dual\<^sub>s\<^sub>t_append List.append_assoc List.append_Nil List.append_Cons)
      moreover have "({x#S}, A) \<Rightarrow>\<^sup>\<bullet> ({S}, A@dual\<^sub>s\<^sub>t [x])"
        using pts_symbolic.Send[of _ S "{x#S}"] pts_symbolic.Receive[of _ S "{x#S}"]
              pts_symbolic.Equality[of _ _ _ S "{x#S}"] pts_symbolic.Inequality[of _ _ S "{x#S}"]
        by (cases x) auto
      ultimately show ?case by simp
    qed
  }
  hence 0: "({dual\<^sub>s\<^sub>t \<A>},[]) \<Rightarrow>\<^sup>\<bullet>\<^sup>* ({},\<A>)" using dual\<^sub>s\<^sub>t_self_inverse by (metis List.append_Nil)

  have "fv\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t \<A>) \<inter> bvars\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t \<A>) = {}" using assms(2) dual\<^sub>s\<^sub>t_fv dual\<^sub>s\<^sub>t_bvars by metis+
  hence 1: "wf\<^sub>s\<^sub>t\<^sub>s {dual\<^sub>s\<^sub>t \<A>}" using assms(1,2) dual\<^sub>s\<^sub>t_self_inverse[of \<A>] unfolding wf\<^sub>s\<^sub>t\<^sub>s_def by auto

  have "\<Union>(trms\<^sub>s\<^sub>t ` {\<A>}) = trms\<^sub>s\<^sub>t \<A>" "\<Union>(trms\<^sub>s\<^sub>t ` {dual\<^sub>s\<^sub>t \<A>}) = trms\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t \<A>)" by auto
  hence "tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>s\<^sub>t ` {\<A>}))" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>s\<^sub>t ` {\<A>}))"
        "(\<Union>(trms\<^sub>s\<^sub>t ` {\<A>})) = \<Union>(trms\<^sub>s\<^sub>t ` {dual\<^sub>s\<^sub>t \<A>})"
    using assms(3,4) unfolding tfr\<^sub>s\<^sub>t_def
    by (metis, metis, metis dual\<^sub>s\<^sub>t_trms_eq)
  hence 2: "tfr\<^sub>s\<^sub>e\<^sub>t (\<Union>(trms\<^sub>s\<^sub>t ` {dual\<^sub>s\<^sub>t \<A>}))" and 3: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>(trms\<^sub>s\<^sub>t ` {dual\<^sub>s\<^sub>t \<A>}))" by metis+

  have 4: "\<forall>S \<in> {dual\<^sub>s\<^sub>t \<A>}. list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    using dual\<^sub>s\<^sub>t_tfr\<^sub>s\<^sub>t\<^sub>p assms(3) unfolding tfr\<^sub>s\<^sub>t_def by blast

  have "assignment_rhs\<^sub>s\<^sub>t \<A> = assignment_rhs\<^sub>s\<^sub>t (dual\<^sub>s\<^sub>t \<A>)"
    by (induct \<A> rule: assignment_rhs\<^sub>s\<^sub>t.induct) auto
  hence 5: "Ana_invar_subst (\<Union>(ik\<^sub>s\<^sub>t`dual\<^sub>s\<^sub>t`{dual\<^sub>s\<^sub>t \<A>}) \<union> \<Union>(assignment_rhs\<^sub>s\<^sub>t`{dual\<^sub>s\<^sub>t \<A>}))"
    using assms(5) dual\<^sub>s\<^sub>t_self_inverse[of \<A>] by auto

  show ?thesis by (rule wt_attack_if_tfr_attack_pts[OF 1 2 3 4 5 0 assms(6,7)])
qed

end

end

end

