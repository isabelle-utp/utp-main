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

(*  Title:      Lazy_Intruder.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>The Lazy Intruder\<close>
theory Lazy_Intruder
imports Strands_and_Constraints Intruder_Deduction
begin

context intruder_model
begin

subsection \<open>Definition of the Lazy Intruder\<close>
text \<open>The lazy intruder constraint reduction system, defined as a relation on constraint states\<close>
inductive_set LI_rel::
    "((('fun,'var) strand \<times> (('fun,'var) subst)) \<times>
       ('fun,'var) strand \<times> (('fun,'var) subst)) set"
  and LI_rel' (infix "\<leadsto>" 50)
  and LI_rel_trancl (infix "\<leadsto>\<^sup>+" 50)
  and LI_rel_rtrancl (infix "\<leadsto>\<^sup>*" 50)
where
  "A \<leadsto> B \<equiv> (A,B) \<in> LI_rel"
| "A \<leadsto>\<^sup>+ B \<equiv> (A,B) \<in> LI_rel\<^sup>+"
| "A \<leadsto>\<^sup>* B \<equiv> (A,B) \<in> LI_rel\<^sup>*"

| Compose: "\<lbrakk>simple S; length T = arity f; public f\<rbrakk>
            \<Longrightarrow> (S@Send (Fun f T)#S',\<theta>) \<leadsto> (S@(map Send T)@S',\<theta>)"
| Unify: "\<lbrakk>simple S; Fun f T' \<in> ik\<^sub>s\<^sub>t S; Some \<delta> = mgu (Fun f T) (Fun f T')\<rbrakk>
          \<Longrightarrow> (S@Send (Fun f T)#S',\<theta>) \<leadsto> ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>,\<theta> \<circ>\<^sub>s \<delta>)"
| Equality: "\<lbrakk>simple S; Some \<delta> = mgu t t'\<rbrakk>
          \<Longrightarrow> (S@Equality _ t t'#S',\<theta>) \<leadsto> ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>,\<theta> \<circ>\<^sub>s \<delta>)"


subsection \<open>Lemma: The Lazy Intruder is Well-founded\<close>
context
begin
private lemma LI_compose_measure_lt: "((S@(map Send T)@S',\<theta>\<^sub>1), (S@Send (Fun f T)#S',\<theta>\<^sub>2)) \<in> measure\<^sub>s\<^sub>t"
using strand_fv_card_map_fun_eq[of S f T S'] strand_size_map_fun_lt(2)[of T f]
by (simp add: measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)

private lemma LI_unify_measure_lt:
  assumes "Some \<delta> = mgu (Fun f T) t" "fv t \<subseteq> fv\<^sub>s\<^sub>t S"
  shows "(((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>,\<theta>\<^sub>1), (S@Send (Fun f T)#S',\<theta>\<^sub>2)) \<in> measure\<^sub>s\<^sub>t"
proof (cases "\<delta> = Var")
  assume "\<delta> = Var"
  hence "(S@S') \<cdot>\<^sub>s\<^sub>t \<delta> = S@S'" by blast
  thus ?thesis
    using strand_fv_card_rm_fun_le[of S S' f T]
    by (auto simp add: measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)
next
  assume "\<delta> \<noteq> Var"
  then obtain v where "v \<in> fv (Fun f T) \<union> fv t" "subst_elim \<delta> v"
    using mgu_eliminates[OF assms(1)[symmetric]] by metis
  hence v_in: "v \<in> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
    using assms(2) by (auto simp add: measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)
  
  have "range_vars \<delta> \<subseteq> fv (Fun f T) \<union> fv\<^sub>s\<^sub>t S"
    using assms(2) mgu_vars_bounded[OF assms(1)[symmetric]] by auto
  hence img_bound: "range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')" by auto

  have finite_fv: "finite (fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S'))" by auto

  have "v \<notin> fv\<^sub>s\<^sub>t ((S@Send (Fun f T)#S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
    using strand_fv_subst_subset_if_subst_elim[OF \<open>subst_elim \<delta> v\<close>] v_in by metis
  hence v_not_in: "v \<notin> fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)" by auto
  
  have "fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
    using strand_subst_fv_bounded_if_img_bounded[OF img_bound] by simp
  hence "fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<subset> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')" using v_in v_not_in by blast
  hence "card (fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)) < card (fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S'))"
    using psubset_card_mono[OF finite_fv] by simp
  thus ?thesis by (auto simp add: measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)
qed

private lemma LI_equality_measure_lt:
  assumes "Some \<delta> = mgu t t'"
  shows "(((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>,\<theta>\<^sub>1), (S@Equality a t t'#S',\<theta>\<^sub>2)) \<in> measure\<^sub>s\<^sub>t"
proof (cases "\<delta> = Var")
  assume "\<delta> = Var"
  hence "(S@S') \<cdot>\<^sub>s\<^sub>t \<delta> = S@S'" by blast
  thus ?thesis
    using strand_fv_card_rm_eq_le[of S S' a t t']
    by (auto simp add: measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)
next
  assume "\<delta> \<noteq> Var"
  then obtain v where "v \<in> fv t \<union> fv t'" "subst_elim \<delta> v"
    using mgu_eliminates[OF assms(1)[symmetric]] by metis
  hence v_in: "v \<in> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" using assms by auto
  
  have "range_vars \<delta> \<subseteq> fv t \<union> fv t' \<union> fv\<^sub>s\<^sub>t S"
    using assms mgu_vars_bounded[OF assms(1)[symmetric]] by auto
  hence img_bound: "range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" by auto

  have finite_fv: "finite (fv\<^sub>s\<^sub>t (S@Equality a t t'#S'))" by auto

  have "v \<notin> fv\<^sub>s\<^sub>t ((S@Equality a t t'#S') \<cdot>\<^sub>s\<^sub>t \<delta>)"
    using strand_fv_subst_subset_if_subst_elim[OF \<open>subst_elim \<delta> v\<close>] v_in by metis
  hence v_not_in: "v \<notin> fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)" by auto
  
  have "fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')"
    using strand_subst_fv_bounded_if_img_bounded[OF img_bound] by simp
  hence "fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>) \<subset> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" using v_in v_not_in by blast
  hence "card (fv\<^sub>s\<^sub>t ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>)) < card (fv\<^sub>s\<^sub>t (S@Equality a t t'#S'))"
    using psubset_card_mono[OF finite_fv] by simp
  thus ?thesis by (auto simp add: measure\<^sub>s\<^sub>t_def size\<^sub>s\<^sub>t_def)
qed

private lemma LI_in_measure: "(S\<^sub>1,\<theta>\<^sub>1) \<leadsto> (S\<^sub>2,\<theta>\<^sub>2) \<Longrightarrow> ((S\<^sub>2,\<theta>\<^sub>2),(S\<^sub>1,\<theta>\<^sub>1)) \<in> measure\<^sub>s\<^sub>t"
proof (induction rule: LI_rel.induct)
  case (Compose S T f S' \<theta>) thus ?case using LI_compose_measure_lt[of S T S'] by metis
next
  case (Unify S f U \<delta> T S' \<theta>)
  hence "fv (Fun f U) \<subseteq> fv\<^sub>s\<^sub>t S"
    using fv_snd_rcv_strand_subset(2)[of S] by force
  thus ?case using LI_unify_measure_lt[OF Unify.hyps(3), of S S'] by metis
qed (metis LI_equality_measure_lt)

private lemma LI_in_measure_trans: "(S\<^sub>1,\<theta>\<^sub>1) \<leadsto>\<^sup>+ (S\<^sub>2,\<theta>\<^sub>2) \<Longrightarrow> ((S\<^sub>2,\<theta>\<^sub>2),(S\<^sub>1,\<theta>\<^sub>1)) \<in> measure\<^sub>s\<^sub>t"
by (induction rule: trancl.induct, metis surjective_pairing LI_in_measure)
   (metis (no_types, lifting) surjective_pairing LI_in_measure measure\<^sub>s\<^sub>t_trans trans_def)

private lemma LI_converse_wellfounded_trans: "wf ((LI_rel\<^sup>+)\<inverse>)"
proof -
  have "(LI_rel\<^sup>+)\<inverse> \<subseteq> measure\<^sub>s\<^sub>t" using LI_in_measure_trans by auto
  thus ?thesis using measure\<^sub>s\<^sub>t_wellfounded wf_subset by metis
qed

private lemma LI_acyclic_trans: "acyclic (LI_rel\<^sup>+)"
using wf_acyclic[OF LI_converse_wellfounded_trans] acyclic_converse by metis

private lemma LI_acyclic: "acyclic LI_rel"
using LI_acyclic_trans acyclic_subset by (simp add: acyclic_def)

lemma LI_no_infinite_chain: "\<not>(\<exists>f. \<forall>i. f i \<leadsto>\<^sup>+ f (Suc i))"
proof -
  have "\<not>(\<exists>f. \<forall>i. (f (Suc i), f i) \<in> (LI_rel\<^sup>+)\<inverse>)"
    using wf_iff_no_infinite_down_chain LI_converse_wellfounded_trans by metis
  thus ?thesis by simp
qed

private lemma LI_unify_finite:
  assumes "finite M"
  shows "finite {((S@Send (Fun f T)#S',\<theta>), ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>,\<theta> \<circ>\<^sub>s \<delta>)) | \<delta> T'. 
                   simple S \<and> Fun f T' \<in> M \<and> Some \<delta> = mgu (Fun f T) (Fun f T')}"
using assms
proof (induction M rule: finite_induct)
  case (insert m M) thus ?case
  proof (cases m)
    case (Fun g U)
    let ?a = "\<lambda>\<delta>. ((S@Send (Fun f T)#S',\<theta>), ((S@S') \<cdot>\<^sub>s\<^sub>t \<delta>,\<theta> \<circ>\<^sub>s \<delta>))"
    let ?A = "\<lambda>B. {?a \<delta> | \<delta> T'. simple S \<and> Fun f T' \<in> B \<and> Some \<delta> = mgu (Fun f T) (Fun f T')}"

    have "?A (insert m M) = (?A M) \<union> (?A {m})" by auto
    moreover have "finite (?A {m})"
    proof (cases "\<exists>\<delta>. Some \<delta> = mgu (Fun f T) (Fun g U)")
      case True
      then obtain \<delta> where \<delta>: "Some \<delta> = mgu (Fun f T) (Fun g U)" by blast
      
      have A_m_eq: "\<And>\<delta>'. ?a \<delta>' \<in> ?A {m} \<Longrightarrow> ?a \<delta> = ?a \<delta>'"
      proof -
        fix \<delta>' assume "?a \<delta>' \<in> ?A {m}"
        hence "\<exists>\<sigma>. Some \<sigma> = mgu (Fun f T) (Fun g U) \<and> ?a \<sigma> = ?a \<delta>'"
          using \<open>m = Fun g U\<close> by auto
        thus "?a \<delta> = ?a \<delta>'" by (metis \<delta> option.inject)
      qed

      have "?A {m} = {} \<or> ?A {m} = {?a \<delta>}"
      proof (cases "simple S \<and> ?A {m} \<noteq> {}")
        case True
        hence "simple S" "?A {m} \<noteq> {}" by meson+
        hence "?A {m} = {?a \<delta> | \<delta>. Some \<delta> = mgu (Fun f T) (Fun g U)}" using \<open>m = Fun g U\<close> by auto
        hence "?a \<delta> \<in> ?A {m}" using \<delta> by auto
       show ?thesis
        proof (rule ccontr)
          assume "\<not>(?A {m} = {} \<or> ?A {m} = {?a \<delta>})"
          then obtain B where B: "?A {m} = insert (?a \<delta>) B" "?a \<delta> \<notin> B" "B \<noteq> {}"
            using \<open>?A {m} \<noteq> {}\<close> \<open>?a \<delta> \<in> ?A {m}\<close> by (metis (no_types, lifting) Set.set_insert)
          then obtain b where b: "?a \<delta> \<noteq> b" "b \<in> B" by (metis (no_types, lifting) ex_in_conv)
          then obtain \<delta>' where \<delta>': "b = ?a \<delta>'" using B(1) by blast
          moreover have "?a \<delta>' \<in> ?A {m}" using B(1) b(2) \<delta>' by auto
          hence "?a \<delta> = ?a \<delta>'" by (blast dest!: A_m_eq)
          ultimately show False using b(1) by simp
        qed
      qed auto
      thus ?thesis by (metis (no_types, lifting) finite.emptyI finite_insert) 
    next
      case False
      hence "?A {m} = {}" using \<open>m = Fun g U\<close> by blast
      thus ?thesis by (metis finite.emptyI)
    qed
    ultimately show ?thesis using insert.IH by auto
  qed simp
qed fastforce
end


subsection \<open>Lemma: The Lazy Intruder Preserves Well-formedness\<close>
context
begin
private lemma LI_preserves_subst_wf_single:
  assumes "(S\<^sub>1,\<theta>\<^sub>1) \<leadsto> (S\<^sub>2,\<theta>\<^sub>2)" "fv\<^sub>s\<^sub>t S\<^sub>1 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>1 = {}" "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<^sub>1"
  and "subst_domain \<theta>\<^sub>1 \<inter> vars\<^sub>s\<^sub>t S\<^sub>1 = {}" "range_vars \<theta>\<^sub>1 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>1 = {}"
  shows "fv\<^sub>s\<^sub>t S\<^sub>2 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>2 = {}" "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<^sub>2"
  and "subst_domain \<theta>\<^sub>2 \<inter> vars\<^sub>s\<^sub>t S\<^sub>2 = {}" "range_vars \<theta>\<^sub>2 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>2 = {}"
using assms
proof (induction rule: LI_rel.induct)
  case (Compose S X f S' \<theta>)
  { case 1 thus ?case using vars_st_snd_map by auto }
  { case 2 thus ?case using vars_st_snd_map by auto }
  { case 3 thus ?case using vars_st_snd_map by force }
  { case 4 thus ?case using vars_st_snd_map by auto }
next
  case (Unify S f U \<delta> T S' \<theta>)
  hence "fv (Fun f U) \<subseteq> fv\<^sub>s\<^sub>t S" using fv_subset_if_in_strand_ik' by blast
  hence *: "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
    using mgu_vars_bounded[OF Unify.hyps(3)[symmetric]]
    unfolding range_vars_alt_def by (fastforce simp del: subst_range.simps)

  have "fv\<^sub>s\<^sub>t (S@S') \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')" "vars\<^sub>s\<^sub>t (S@S') \<subseteq> vars\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
    by auto
  hence **: "fv\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
            "vars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> vars\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
    using subst_sends_strand_fv_to_img[of "S@S'" \<delta>]
          strand_subst_vars_union_bound[of "S@S'" \<delta>] *
    by blast+

  have "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" by (fact mgu_gives_wellformed_subst[OF Unify.hyps(3)[symmetric]])
  
  { case 1
    have "bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
      using bvars_subst_ident[of "S@S'" \<delta>] by auto
    thus ?case using 1 ** by blast
  }
  { case 2
    hence "subst_domain \<theta> \<inter> subst_domain \<delta> = {}" "subst_domain \<theta> \<inter> range_vars \<delta> = {}"
      using * by blast+
    thus ?case by (metis wf_subst_compose[OF \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<close> \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>\<close>])
  }
  { case 3
    hence "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}" using ** by blast
    moreover have "v \<in> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')" when "v \<in> subst_domain \<delta>" for v
      using * that by blast
    hence "subst_domain \<delta> \<inter> fv\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}"
      using mgu_eliminates_dom[OF Unify.hyps(3)[symmetric],
                THEN strand_fv_subst_subset_if_subst_elim, of _ "S@Send (Fun f T)#S'"]
      unfolding subst_elim_def by auto
    moreover have "bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
      using bvars_subst_ident[of "S@S'" \<delta>] by auto
    hence "subst_domain \<delta> \<inter> bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}" using 3(1) * by blast
    ultimately show ?case
      using ** * subst_domain_compose[of \<theta> \<delta>] vars\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>t[of "S@S' \<cdot>\<^sub>s\<^sub>t \<delta>"]
      by blast
  }
  { case 4
    have ***: "bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
      using bvars_subst_ident[of "S@S'" \<delta>] by auto
    hence "range_vars \<delta> \<inter> bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}" using 4(1) * by blast
    thus ?case using subst_img_comp_subset[of \<theta> \<delta>] 4(4) *** by blast
  }
next
  case (Equality S \<delta> t t' a S' \<theta>)
  hence *: "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')"
    using mgu_vars_bounded[OF Equality.hyps(2)[symmetric]]
    unfolding range_vars_alt_def by fastforce

  have "fv\<^sub>s\<^sub>t (S@S') \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" "vars\<^sub>s\<^sub>t (S@S') \<subseteq> vars\<^sub>s\<^sub>t (S@Equality a t t'#S')"
    by auto
  hence **: "fv\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')"
            "vars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> vars\<^sub>s\<^sub>t (S@Equality a t t'#S')"
    using subst_sends_strand_fv_to_img[of "S@S'" \<delta>]
          strand_subst_vars_union_bound[of "S@S'" \<delta>] *
    by blast+

  have "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" by (fact mgu_gives_wellformed_subst[OF Equality.hyps(2)[symmetric]])
  
  { case 1
    have "bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>s\<^sub>t (S@Equality a t t'#S')"
      using bvars_subst_ident[of "S@S'" \<delta>] by auto
    thus ?case using 1 ** by blast
  }
  { case 2
    hence "subst_domain \<theta> \<inter> subst_domain \<delta> = {}" "subst_domain \<theta> \<inter> range_vars \<delta> = {}"
      using * by blast+
    thus ?case by (metis wf_subst_compose[OF \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<close> \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>\<close>])
  }
  { case 3
    hence "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}" using ** by blast
    moreover have "v \<in> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" when "v \<in> subst_domain \<delta>" for v
      using * that by blast
    hence "subst_domain \<delta> \<inter> fv\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}"
      using mgu_eliminates_dom[OF Equality.hyps(2)[symmetric],
                THEN strand_fv_subst_subset_if_subst_elim, of _ "S@Equality a t t'#S'"]
      unfolding subst_elim_def by auto
    moreover have "bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>s\<^sub>t (S@Equality a t t'#S')"
      using bvars_subst_ident[of "S@S'" \<delta>] by auto
    hence "subst_domain \<delta> \<inter> bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}" using 3(1) * by blast
    ultimately show ?case
      using ** * subst_domain_compose[of \<theta> \<delta>] vars\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>t[of "S@S' \<cdot>\<^sub>s\<^sub>t \<delta>"]
      by blast
  }
  { case 4
    have ***: "bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>s\<^sub>t (S@Equality a t t'#S')"
      using bvars_subst_ident[of "S@S'" \<delta>] by auto
    hence "range_vars \<delta> \<inter> bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}" using 4(1) * by blast
    thus ?case using subst_img_comp_subset[of \<theta> \<delta>] 4(4) *** by blast
  }
qed

private lemma LI_preserves_subst_wf:
  assumes "(S\<^sub>1,\<theta>\<^sub>1) \<leadsto>\<^sup>* (S\<^sub>2,\<theta>\<^sub>2)" "fv\<^sub>s\<^sub>t S\<^sub>1 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>1 = {}" "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<^sub>1"
  and "subst_domain \<theta>\<^sub>1 \<inter> vars\<^sub>s\<^sub>t S\<^sub>1 = {}" "range_vars \<theta>\<^sub>1 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>1 = {}"
  shows "fv\<^sub>s\<^sub>t S\<^sub>2 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>2 = {}" "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<^sub>2"
  and "subst_domain \<theta>\<^sub>2 \<inter> vars\<^sub>s\<^sub>t S\<^sub>2 = {}" "range_vars \<theta>\<^sub>2 \<inter> bvars\<^sub>s\<^sub>t S\<^sub>2 = {}"
using assms
proof (induction S\<^sub>2 \<theta>\<^sub>2 rule: rtrancl_induct2)
  case (step S\<^sub>i \<theta>\<^sub>i S\<^sub>j \<theta>\<^sub>j)
  { case 1 thus ?case using LI_preserves_subst_wf_single[OF \<open>(S\<^sub>i,\<theta>\<^sub>i) \<leadsto> (S\<^sub>j,\<theta>\<^sub>j)\<close>] step.IH by metis }
  { case 2 thus ?case using LI_preserves_subst_wf_single[OF \<open>(S\<^sub>i,\<theta>\<^sub>i) \<leadsto> (S\<^sub>j,\<theta>\<^sub>j)\<close>] step.IH by metis }
  { case 3 thus ?case using LI_preserves_subst_wf_single[OF \<open>(S\<^sub>i,\<theta>\<^sub>i) \<leadsto> (S\<^sub>j,\<theta>\<^sub>j)\<close>] step.IH by metis }
  { case 4 thus ?case using LI_preserves_subst_wf_single[OF \<open>(S\<^sub>i,\<theta>\<^sub>i) \<leadsto> (S\<^sub>j,\<theta>\<^sub>j)\<close>] step.IH by metis }
qed metis

lemma LI_preserves_wellformedness:
  assumes "(S\<^sub>1,\<theta>\<^sub>1) \<leadsto>\<^sup>* (S\<^sub>2,\<theta>\<^sub>2)" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1"
  shows "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>2 \<theta>\<^sub>2"
proof -
  have *: "wf\<^sub>s\<^sub>t {} S\<^sub>j"
    when "(S\<^sub>i, \<theta>\<^sub>i) \<leadsto> (S\<^sub>j, \<theta>\<^sub>j)" "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>i \<theta>\<^sub>i" for S\<^sub>i \<theta>\<^sub>i S\<^sub>j \<theta>\<^sub>j
    using that
  proof (induction rule: LI_rel.induct)
    case (Unify S f U \<delta> T S' \<theta>)
    have "fv (Fun f T) \<union> fv (Fun f U) \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')" using Unify.hyps(2) by force
    hence "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
      using mgu_vars_bounded[OF Unify.hyps(3)[symmetric]] by (metis subset_trans)
    hence "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t (S@Send (Fun f T)#S') = {}"
      using Unify.prems unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by blast
    thus ?case
      using wf_unify[OF _ Unify.hyps(2) MGU_is_Unifier[OF mgu_gives_MGU], of "{}",
                     OF _ Unify.hyps(3)[symmetric], of S'] Unify.prems(1)
      by (auto simp add: wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)
  next
    case (Equality S \<delta> t t' a S' \<theta>)
    have "fv t \<union> fv t' \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" using Equality.hyps(2) by force
    hence "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')"
      using mgu_vars_bounded[OF Equality.hyps(2)[symmetric]] by (metis subset_trans)
    hence "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t (S@Equality a t t'#S') = {}"
      using Equality.prems unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by blast
    thus ?case
      using wf_equality[OF _ Equality.hyps(2)[symmetric], of "{}" S a S'] Equality.prems(1)
      by (auto simp add: wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)
  qed (metis wf_send_compose wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)

  show ?thesis using assms
  proof (induction rule: rtrancl_induct2)
    case (step S\<^sub>i \<theta>\<^sub>i S\<^sub>j \<theta>\<^sub>j) thus ?case
      using LI_preserves_subst_wf_single[OF \<open>(S\<^sub>i,\<theta>\<^sub>i) \<leadsto> (S\<^sub>j,\<theta>\<^sub>j)\<close>] *[OF \<open>(S\<^sub>i,\<theta>\<^sub>i) \<leadsto> (S\<^sub>j,\<theta>\<^sub>j)\<close>]
      by (metis wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)
  qed simp
qed

lemma LI_preserves_trm_wf:
  assumes "(S,\<theta>) \<leadsto>\<^sup>* (S',\<theta>')" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S')"
proof -
  { fix S \<theta> S' \<theta>'
    assume "(S,\<theta>) \<leadsto> (S',\<theta>')" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)"
    hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S')"
    proof (induction rule: LI_rel.induct)
      case (Compose S T f S' \<theta>)
      hence "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)"
        and *: "t \<in> set S \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p t)" "t \<in> set S' \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p t)" for t
        by auto
      hence "wf\<^sub>t\<^sub>r\<^sub>m t" when "t \<in> set T" for t using that unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
      hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p t)" when "t \<in> set (map Send T)" for t
        using that unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
      thus ?case using * by force
    next
      case (Unify S f U \<delta> T S' \<theta>)
      have "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)" "wf\<^sub>t\<^sub>r\<^sub>m (Fun f U)"
        using Unify.prems(1) Unify.hyps(2) wf_trm_subterm[of _ "Fun f U"]
        by (simp, force)
      hence range_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
        using mgu_wf_trm[OF Unify.hyps(3)[symmetric]] by simp

      { fix s assume "s \<in> set (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>)"
        hence "\<exists>s' \<in> set (S@S'). s = s' \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s')"
          using Unify.prems(1) by (auto simp add: subst_apply_strand_def)
        moreover {
          fix s' assume s': "s = s' \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s')" "s' \<in> set (S@S')"
          from s'(2) have "trms\<^sub>s\<^sub>t\<^sub>p (s' \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = trms\<^sub>s\<^sub>t\<^sub>p s' \<cdot>\<^sub>s\<^sub>e\<^sub>t (rm_vars (set (bvars\<^sub>s\<^sub>t\<^sub>p s')) \<delta>)"
          proof (induction s')
            case (Inequality X F) thus ?case by (induct F) (auto simp add: subst_apply_pairs_def)
          qed auto
          hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s)"
            using wf_trm_subst[OF wf_trms_subst_rm_vars'[OF range_wf]] \<open>wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s')\<close> s'(1)
            by simp
        }
        ultimately have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s)" by auto
      }
      thus ?case by auto
    next
      case (Equality S \<delta> t t' a S' \<theta>)
      hence "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m t'" by simp_all
      hence range_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
        using mgu_wf_trm[OF Equality.hyps(2)[symmetric]] by simp

      { fix s assume "s \<in> set (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>)"
        hence "\<exists>s' \<in> set (S@S'). s = s' \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s')"
          using Equality.prems(1) by (auto simp add: subst_apply_strand_def)
        moreover {
          fix s' assume s': "s = s' \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s')" "s' \<in> set (S@S')"
          from s'(2) have "trms\<^sub>s\<^sub>t\<^sub>p (s' \<cdot>\<^sub>s\<^sub>t\<^sub>p \<delta>) = trms\<^sub>s\<^sub>t\<^sub>p s' \<cdot>\<^sub>s\<^sub>e\<^sub>t (rm_vars (set (bvars\<^sub>s\<^sub>t\<^sub>p s')) \<delta>)"
          proof (induction s')
            case (Inequality X F) thus ?case by (induct F) (auto simp add: subst_apply_pairs_def)
          qed auto
          hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s)"
            using wf_trm_subst[OF wf_trms_subst_rm_vars'[OF range_wf]] \<open>wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s')\<close> s'(1)
            by simp
        }
        ultimately have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t\<^sub>p s)" by auto
      }
      thus ?case by auto
    qed
  }
  with assms show ?thesis by (induction rule: rtrancl_induct2) metis+
qed
end

subsection \<open>Theorem: Soundness of the Lazy Intruder\<close>
context
begin
private lemma LI_soundness_single:
  assumes "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1" "(S\<^sub>1,\<theta>\<^sub>1) \<leadsto> (S\<^sub>2,\<theta>\<^sub>2)" "\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>2,\<theta>\<^sub>2\<rangle>"
  shows "\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1,\<theta>\<^sub>1\<rangle>"
using assms(2,1,3)
proof (induction rule: LI_rel.induct)
  case (Compose S T f S' \<theta>)
  hence *: "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; map Send T\<rbrakk>\<^sub>c \<I>" "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>"
    unfolding constr_sem_c_def by force+

  have "ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c Fun f T \<cdot> \<I>"
    using *(2) Compose.hyps(2) ComposeC[OF _ Compose.hyps(3), of "map (\<lambda>x. x \<cdot> \<I>) T"]
    unfolding subst_compose_def by force
  thus "\<I> \<Turnstile>\<^sub>c \<langle>S@Send (Fun f T)#S',\<theta>\<rangle>"
    using *(1,3) \<open>\<I> \<Turnstile>\<^sub>c \<langle>S@map Send T@S',\<theta>\<rangle>\<close>
    by (auto simp add: constr_sem_c_def)
next
  case (Unify S f U \<delta> T S' \<theta>)
  have "(\<theta> \<circ>\<^sub>s \<delta>) supports \<I>" "\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>"
    using Unify.prems(2) unfolding constr_sem_c_def by metis+
  then obtain \<sigma> where \<sigma>: "\<theta> \<circ>\<^sub>s \<delta> \<circ>\<^sub>s \<sigma> = \<I>" unfolding subst_compose_def by auto

  have \<theta>fun_id: "Fun f U \<cdot> \<theta> = Fun f U" "Fun f T \<cdot> \<theta> = Fun f T"
    using Unify.prems(1) trm_subst_ident[of "Fun f U" \<theta>]
          fv_subset_if_in_strand_ik[of "Fun f U" S] Unify.hyps(2)
          fv_snd_rcv_strand_subset(2)[of S]
          strand_vars_split(1)[of S "Send (Fun f T)#S'"]
    unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def apply blast
    using Unify.prems(1) trm_subst_ident[of "Fun f T" \<theta>]
    unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by fastforce
  hence \<theta>\<delta>_disj:
      "subst_domain \<theta> \<inter> subst_domain \<delta> = {}"
      "subst_domain \<theta> \<inter> range_vars \<delta> = {}"
      "subst_domain \<theta> \<inter> range_vars \<theta> = {}" 
    using trm_subst_disj mgu_vars_bounded[OF Unify.hyps(3)[symmetric]] apply (blast,blast)
    using Unify.prems(1) unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by blast
  hence \<theta>\<delta>_support: "\<theta> supports \<I>" "\<delta> supports \<I>"
    by (simp_all add: subst_support_comp_split[OF \<open>(\<theta> \<circ>\<^sub>s \<delta>) supports \<I>\<close>])

  have "fv (Fun f T) \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')" "fv (Fun f U) \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
    using Unify.hyps(2) by force+
  hence \<delta>_vars_bound: "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Send (Fun f T)#S')"
    using mgu_vars_bounded[OF Unify.hyps(3)[symmetric]] by blast

  have "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; [Send (Fun f T)]\<rbrakk>\<^sub>c \<I>"
  proof -
    from Unify.hyps(2) have "Fun f U \<cdot> \<I> \<in> ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by blast
    hence "Fun f U \<cdot> \<I> \<in> ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by blast
    moreover have "Unifier \<delta> (Fun f T) (Fun f U)"
      by (fact MGU_is_Unifier[OF mgu_gives_MGU[OF Unify.hyps(3)[symmetric]]])
    ultimately have "Fun f T \<cdot> \<I> \<in> ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using \<sigma> by (metis \<theta>fun_id subst_subst_compose) 
    thus ?thesis by simp
  qed

  have "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>"
  proof -
    have "(S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta> = S@S' \<cdot>\<^sub>s\<^sub>t \<delta>" "(S@S') \<cdot>\<^sub>s\<^sub>t \<theta> = S@S'"
    proof -
      have "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@S') = {}"
        using Unify.prems(1) by (auto simp add: wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)
      hence "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}"
        using \<theta>\<delta>_disj(2) strand_subst_vars_union_bound[of "S@S'" \<delta>] by blast
      thus "(S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta> = S@S' \<cdot>\<^sub>s\<^sub>t \<delta>" "(S@S') \<cdot>\<^sub>s\<^sub>t \<theta> = S@S'"
        using strand_subst_comp \<open>subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@S') = {}\<close> by (blast,blast)
    qed
    moreover have "subst_idem \<delta>" by (fact mgu_gives_subst_idem[OF Unify.hyps(3)[symmetric]])
    moreover have
        "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t (S@S') = {}"
        "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}"
        "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t (S@S') = {}"
      using wf_constr_bvars_disj[OF Unify.prems(1)]
            wf_constr_bvars_disj'[OF Unify.prems(1) \<delta>_vars_bound]
      by auto
    ultimately have "\<lbrakk>{}; S@S'\<rbrakk>\<^sub>c \<I>"
      using \<open>\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>\<close> \<sigma>
            strand_sem_subst(1)[of \<theta> "S@S' \<cdot>\<^sub>s\<^sub>t \<delta>" "{}" "\<delta> \<circ>\<^sub>s \<sigma>"]
            strand_sem_subst(2)[of \<theta> "S@S'" "{}" "\<delta> \<circ>\<^sub>s \<sigma>"] 
            strand_sem_subst_subst_idem[of \<delta> "S@S'" "{}" \<sigma>]
      unfolding constr_sem_c_def
      by (metis subst_compose_assoc)
    thus "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>" by auto
  qed
  
  show "\<I> \<Turnstile>\<^sub>c \<langle>S@Send (Fun f T)#S',\<theta>\<rangle>"
    using \<theta>\<delta>_support(1) \<open>\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; [Send (Fun f T)]\<rbrakk>\<^sub>c \<I>\<close> \<open>\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>\<close> \<open>\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>\<close>
    by (auto simp add: constr_sem_c_def)
next
  case (Equality S \<delta> t t' a S' \<theta>)
  have "(\<theta> \<circ>\<^sub>s \<delta>) supports \<I>" "\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>"
    using Equality.prems(2) unfolding constr_sem_c_def by metis+
  then obtain \<sigma> where \<sigma>: "\<theta> \<circ>\<^sub>s \<delta> \<circ>\<^sub>s \<sigma> = \<I>" unfolding subst_compose_def by auto

  have "fv t \<subseteq> vars\<^sub>s\<^sub>t (S@Equality a t t'#S')" "fv t' \<subseteq> vars\<^sub>s\<^sub>t (S@Equality a t t'#S')"
    by auto
  moreover have "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@Equality a t t'#S') = {}"
    using Equality.prems(1) unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def by auto
  ultimately have \<theta>fun_id: "t \<cdot> \<theta> = t" "t' \<cdot> \<theta> = t'"
    using trm_subst_ident[of t \<theta>] trm_subst_ident[of t' \<theta>]
    by auto
  hence \<theta>\<delta>_disj:
      "subst_domain \<theta> \<inter> subst_domain \<delta> = {}"
      "subst_domain \<theta> \<inter> range_vars \<delta> = {}"
      "subst_domain \<theta> \<inter> range_vars \<theta> = {}" 
    using trm_subst_disj mgu_vars_bounded[OF Equality.hyps(2)[symmetric]] apply (blast,blast)
    using Equality.prems(1) unfolding wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by blast
  hence \<theta>\<delta>_support: "\<theta> supports \<I>" "\<delta> supports \<I>"
    by (simp_all add: subst_support_comp_split[OF \<open>(\<theta> \<circ>\<^sub>s \<delta>) supports \<I>\<close>])

  have "fv t \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" "fv t' \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')" by auto
  hence \<delta>_vars_bound: "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t (S@Equality a t t'#S')"
    using mgu_vars_bounded[OF Equality.hyps(2)[symmetric]] by blast

  have "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; [Equality a t t']\<rbrakk>\<^sub>c \<I>"
  proof -
    have "t \<cdot> \<delta> = t' \<cdot> \<delta>"
      using MGU_is_Unifier[OF mgu_gives_MGU[OF Equality.hyps(2)[symmetric]]]
      by metis
    hence "t \<cdot> (\<theta> \<circ>\<^sub>s \<delta>) = t' \<cdot> (\<theta> \<circ>\<^sub>s \<delta>)" by (metis \<theta>fun_id subst_subst_compose)
    hence "t \<cdot> \<I> = t' \<cdot> \<I>" by (metis \<sigma> subst_subst_compose) 
    thus ?thesis by simp
  qed

  have "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>"
  proof -
    have "(S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta> = S@S' \<cdot>\<^sub>s\<^sub>t \<delta>" "(S@S') \<cdot>\<^sub>s\<^sub>t \<theta> = S@S'"
    proof -
      have "subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@S') = {}"
        using Equality.prems(1)
        by (fastforce simp add: wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def simp del: subst_range.simps)
      hence "subst_domain \<theta> \<inter> fv\<^sub>s\<^sub>t (S@S') = {}" by blast
      hence "subst_domain \<theta> \<inter> fv\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}"
        using \<theta>\<delta>_disj(2) subst_sends_strand_fv_to_img[of "S@S'" \<delta>] by blast
      thus "(S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>t \<theta> = S@S' \<cdot>\<^sub>s\<^sub>t \<delta>" "(S@S') \<cdot>\<^sub>s\<^sub>t \<theta> = S@S'"
        using strand_subst_comp \<open>subst_domain \<theta> \<inter> vars\<^sub>s\<^sub>t (S@S') = {}\<close> by (blast,blast)
    qed
    moreover have
        "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t (S@S') = {}"
        "(subst_domain \<theta> \<union> range_vars \<theta>) \<inter> bvars\<^sub>s\<^sub>t (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>) = {}"
        "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> bvars\<^sub>s\<^sub>t (S@S') = {}"
      using wf_constr_bvars_disj[OF Equality.prems(1)]
            wf_constr_bvars_disj'[OF Equality.prems(1) \<delta>_vars_bound]
      by auto
    ultimately have "\<lbrakk>{}; S@S'\<rbrakk>\<^sub>c \<I>"
      using \<open>\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>\<close> \<sigma>
            strand_sem_subst(1)[of \<theta> "S@S' \<cdot>\<^sub>s\<^sub>t \<delta>" "{}" "\<delta> \<circ>\<^sub>s \<sigma>"]
            strand_sem_subst(2)[of \<theta> "S@S'" "{}" "\<delta> \<circ>\<^sub>s \<sigma>"] 
            strand_sem_subst_subst_idem[of \<delta> "S@S'" "{}" \<sigma>]
            mgu_gives_subst_idem[OF Equality.hyps(2)[symmetric]]
      unfolding constr_sem_c_def
      by (metis subst_compose_assoc)
    thus "\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>" "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>" by auto
  qed
  
  show "\<I> \<Turnstile>\<^sub>c \<langle>S@Equality a t t'#S',\<theta>\<rangle>"
    using \<theta>\<delta>_support(1) \<open>\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; [Equality a t t']\<rbrakk>\<^sub>c \<I>\<close> \<open>\<lbrakk>{}; S\<rbrakk>\<^sub>c \<I>\<close> \<open>\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>\<close>
    by (auto simp add: constr_sem_c_def)
qed

theorem LI_soundness:
  assumes "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1" "(S\<^sub>1,\<theta>\<^sub>1) \<leadsto>\<^sup>* (S\<^sub>2,\<theta>\<^sub>2)" "\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>2, \<theta>\<^sub>2\<rangle>"
  shows "\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>"
using assms(2,1,3)
proof (induction S\<^sub>2 \<theta>\<^sub>2 rule: rtrancl_induct2)
  case (step S\<^sub>i \<theta>\<^sub>i S\<^sub>j \<theta>\<^sub>j) thus ?case
    using LI_preserves_wellformedness[OF \<open>(S\<^sub>1, \<theta>\<^sub>1) \<leadsto>\<^sup>* (S\<^sub>i, \<theta>\<^sub>i)\<close> \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1\<close>]
          LI_soundness_single[OF _ \<open>(S\<^sub>i, \<theta>\<^sub>i) \<leadsto> (S\<^sub>j, \<theta>\<^sub>j)\<close> \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>j, \<theta>\<^sub>j\<rangle>\<close>]
          step.IH[OF \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1\<close>]
    by metis
qed metis
end

subsection \<open>Theorem: Completeness of the Lazy Intruder\<close>
context
begin
private lemma LI_completeness_single:
  assumes "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1" "\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>" "\<not>simple S\<^sub>1"
  shows "\<exists>S\<^sub>2 \<theta>\<^sub>2. (S\<^sub>1,\<theta>\<^sub>1) \<leadsto> (S\<^sub>2,\<theta>\<^sub>2) \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>2, \<theta>\<^sub>2\<rangle>)"
using not_simple_elim[OF \<open>\<not>simple S\<^sub>1\<close>]
proof -
  { \<comment> \<open>In this case \<open>S\<^sub>1\<close> isn't simple because it contains an equality constraint,
        so we can simply proceed with the reduction by computing the MGU for the equation\<close>
    assume "\<exists>S' S'' a t t'. S\<^sub>1 = S'@Equality a t t'#S'' \<and> simple S'"
    then obtain S a t t' S' where S\<^sub>1: "S\<^sub>1 = S@Equality a t t'#S'" "simple S" by moura
    hence *: "wf\<^sub>s\<^sub>t {} S" "\<I> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<^sub>1\<rangle>" "\<theta>\<^sub>1 supports \<I>" "t \<cdot> \<I> = t' \<cdot> \<I>"
      using \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close> \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1\<close> wf_eq_fv[of "{}" S t t' S']
            fv_snd_rcv_strand_subset(5)[of S]
      by (auto simp add: constr_sem_c_def wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)

    from * have "Unifier \<I> t t'" by simp
    then obtain \<delta> where \<delta>:
        "Some \<delta> = mgu t t'" "subst_idem \<delta>" "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv t \<union> fv t'"
      using mgu_always_unifies mgu_gives_subst_idem mgu_vars_bounded by metis+
    
    have "\<delta> \<preceq>\<^sub>\<circ> \<I>"
      using mgu_gives_MGU[OF \<delta>(1)[symmetric]]
      by (metis \<open>Unifier \<I> t t'\<close>)
    hence "\<delta> supports \<I>" using subst_support_if_mgt_subst_idem[OF _ \<delta>(2)] by metis
    hence "(\<theta>\<^sub>1 \<circ>\<^sub>s \<delta>) supports \<I>" using subst_support_comp \<open>\<theta>\<^sub>1 supports \<I>\<close> by metis
    
    have "\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>"
    proof -
      have "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t S\<^sub>1" using \<delta>(3) S\<^sub>1(1) by auto
      hence "\<lbrakk>{}; S\<^sub>1 \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>"
        using \<open>subst_idem \<delta>\<close> \<open>\<delta> \<preceq>\<^sub>\<circ> \<I>\<close> \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close> strand_sem_subst
              wf_constr_bvars_disj'(1)[OF assms(1)]
        unfolding subst_idem_def constr_sem_c_def
        by (metis (no_types) subst_compose_assoc)
      thus "\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>" using S\<^sub>1(1) by force
    qed
    moreover have "(S@Equality a t t'#S', \<theta>\<^sub>1) \<leadsto> (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>, \<theta>\<^sub>1 \<circ>\<^sub>s \<delta>)"
      using LI_rel.Equality[OF \<open>simple S\<close> \<delta>(1)] S\<^sub>1 by metis
    ultimately have ?thesis
      using S\<^sub>1(1) \<open>(\<theta>\<^sub>1 \<circ>\<^sub>s \<delta>) supports \<I>\<close>
      by (auto simp add: constr_sem_c_def)
  } moreover {
    \<comment> \<open>In this case \<open>S\<^sub>1\<close> isn't simple because it contains a deduction constraint for a composed
        term, so we must look at how this composed term is derived under the interpretation \<open>\<I>\<close>\<close>
    assume "\<exists>S' S'' f T. S\<^sub>1 = S'@Send (Fun f T)#S'' \<and> simple S'"
    with assms obtain S f T S' where S\<^sub>1: "S\<^sub>1 = S@Send (Fun f T)#S'" "simple S" by moura
    hence "wf\<^sub>s\<^sub>t {} S" "\<I> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<^sub>1\<rangle>" "\<theta>\<^sub>1 supports \<I>"
      using \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close> \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1\<close>
      by (auto simp add: constr_sem_c_def wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r_def)
  
    \<comment> \<open>Lemma for a common subcase\<close>
    have fun_sat: "\<I> \<Turnstile>\<^sub>c \<langle>S@(map Send T)@S', \<theta>\<^sub>1\<rangle>" when T: "\<And>t. t \<in> set T \<Longrightarrow> ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>"
    proof -
      have "\<And>t. t \<in> set T \<Longrightarrow> \<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; [Send t]\<rbrakk>\<^sub>c \<I>" using T by simp
      hence "\<lbrakk>ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; map Send T\<rbrakk>\<^sub>c \<I>" using \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close> strand_sem_Send_map by metis
      moreover have "\<lbrakk>ik\<^sub>s\<^sub>t (S@(map Send T)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>; S'\<rbrakk>\<^sub>c \<I>"
        using \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close> S\<^sub>1
        by (auto simp add: constr_sem_c_def)
      ultimately show ?thesis
        using \<open>\<I> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<^sub>1\<rangle>\<close> \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close>
        by (force simp add: constr_sem_c_def)
    qed
  
    from S\<^sub>1 \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close> have "ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c Fun f T \<cdot> \<I>" by (auto simp add: constr_sem_c_def)
    hence ?thesis
    proof cases
      \<comment> \<open>Case 1: \<open>\<I>(f(T))\<close> has been derived using the \<open>AxiomC\<close> rule.\<close>
      case AxiomC
      hence ex_t: "\<exists>t. t \<in> ik\<^sub>s\<^sub>t S \<and> Fun f T \<cdot> \<I> = t \<cdot> \<I>" by auto
      show ?thesis
      proof (cases "\<forall>T'. Fun f T' \<in> ik\<^sub>s\<^sub>t S \<longrightarrow> Fun f T \<cdot> \<I> \<noteq> Fun f T' \<cdot> \<I>")
        \<comment> \<open>Case 1.1: \<open>f(T)\<close> is equal to a variable in the intruder knowledge under \<open>\<I>\<close>.
            Hence there must exists a deduction constraint in the simple prefix of the constraint
            in which this variable occurs/"is sent" for the first time. Since this variable itself
            cannot have been derived from the \<open>AxiomC\<close> rule (because it must be equal under the
            interpretation to \<open>f(T)\<close>, which is by assumption not in the intruder knowledge under
            \<open>\<I>\<close>) it must be the case that we can derive it using the \<open>ComposeC\<close> rule. Hence we can
            apply the \<open>Compose\<close> rule of the lazy intruder to \<open>f(T)\<close>.\<close>
        case True
        have "\<exists>v. Var v \<in> ik\<^sub>s\<^sub>t S \<and> Fun f T \<cdot> \<I> = \<I> v"
        proof -
          obtain t where "t \<in> ik\<^sub>s\<^sub>t S" "Fun f T \<cdot> \<I> = t \<cdot> \<I>" using ex_t by moura
          thus ?thesis
            using \<open>\<forall>T'. Fun f T' \<in> ik\<^sub>s\<^sub>t S \<longrightarrow> Fun f T \<cdot> \<I> \<noteq> Fun f T' \<cdot> \<I>\<close>
            by (cases t) auto
        qed
        hence "\<exists>v \<in> wfrestrictedvars\<^sub>s\<^sub>t S. Fun f T \<cdot> \<I> = \<I> v"
          using vars_subset_if_in_strand_ik2[of _ S] by fastforce
        then obtain v S\<^sub>p\<^sub>r\<^sub>e S\<^sub>s\<^sub>u\<^sub>f
          where S: "S = S\<^sub>p\<^sub>r\<^sub>e@Send (Var v)#S\<^sub>s\<^sub>u\<^sub>f" "Fun f T \<cdot> \<I> = \<I> v"
                   "\<not>(\<exists>w \<in> wfrestrictedvars\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e. Fun f T \<cdot> \<I> = \<I> w)"
          using \<open>wf\<^sub>s\<^sub>t {} S\<close> wf_simple_strand_first_Send_var_split[OF _ \<open>simple S\<close>, of "Fun f T" \<I>]
          by auto
        hence "\<forall>w. Var w \<in> ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<longrightarrow> \<I> v \<noteq> Var w \<cdot> \<I>" by auto
        moreover have "\<forall>T'. Fun f T' \<in> ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<longrightarrow> Fun f T \<cdot> \<I> \<noteq> Fun f T' \<cdot> \<I>"
          using \<open>\<forall>T'. Fun f T' \<in> ik\<^sub>s\<^sub>t S \<longrightarrow> Fun f T \<cdot> \<I> \<noteq> Fun f T' \<cdot> \<I>\<close> S(1)
          by (meson contra_subsetD ik_append_subset(1))
        hence "\<forall>g T'. Fun g T' \<in> ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<longrightarrow> \<I> v \<noteq> Fun g T' \<cdot> \<I>" using S(2) by simp
        ultimately have "\<forall>t \<in> ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e. \<I> v \<noteq> t \<cdot> \<I>" by (metis term.exhaust)
        hence "\<I> v \<notin> (ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" by auto
  
        have "ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c \<I> v"
          using S\<^sub>1(1) S(1) \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close>
          by (auto simp add: constr_sem_c_def)
        hence "ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c Fun f T \<cdot> \<I>" using \<open>Fun f T \<cdot> \<I> = \<I> v\<close> by metis
        hence "length T = arity f" "public f" "\<And>t. t \<in> set T \<Longrightarrow> ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>"
          using \<open>Fun f T \<cdot> \<I> = \<I> v\<close> \<open>\<I> v \<notin> ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<close>
                intruder_synth.simps[of "ik\<^sub>s\<^sub>t S\<^sub>p\<^sub>r\<^sub>e \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "\<I> v"]
          by auto
        hence *: "\<And>t. t \<in> set T \<Longrightarrow> ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c t \<cdot> \<I>"
          using S(1) by (auto intro: ideduct_synth_mono)
        hence "\<I> \<Turnstile>\<^sub>c \<langle>S@(map Send T)@S', \<theta>\<^sub>1\<rangle>" by (metis fun_sat)
        moreover have "(S@Send (Fun f T)#S', \<theta>\<^sub>1) \<leadsto> (S@map Send T@S', \<theta>\<^sub>1)"
          by (metis LI_rel.Compose[OF \<open>simple S\<close> \<open>length T = arity f\<close> \<open>public f\<close>])
        ultimately show ?thesis using S\<^sub>1 by auto
      next
        \<comment> \<open>Case 1.2: \<open>\<I>(f(T))\<close> can be derived from an interpreted composed term in the intruder
            knowledge. Use the \<open>Unify\<close> rule on this composed term to further reduce the constraint.\<close>
        case False
        then obtain T' where t: "Fun f T' \<in> ik\<^sub>s\<^sub>t S" "Fun f T \<cdot> \<I> = Fun f T' \<cdot> \<I>"
          by auto
        hence "fv (Fun f T') \<subseteq> fv\<^sub>s\<^sub>t S\<^sub>1"
          using S\<^sub>1(1) fv_subset_if_in_strand_ik'[OF t(1)]
                fv_snd_rcv_strand_subset(2)[of S]
          by auto
        from t have "Unifier \<I> (Fun f T) (Fun f T')" by simp
        then obtain \<delta> where \<delta>:
            "Some \<delta> = mgu (Fun f T) (Fun f T')" "subst_idem \<delta>"
            "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv (Fun f T) \<union> fv (Fun f T')"
          using mgu_always_unifies mgu_gives_subst_idem mgu_vars_bounded by metis+
        
        have "\<delta> \<preceq>\<^sub>\<circ> \<I>"
          using mgu_gives_MGU[OF \<delta>(1)[symmetric]]
          by (metis \<open>Unifier \<I> (Fun f T) (Fun f T')\<close>)
        hence "\<delta> supports \<I>" using subst_support_if_mgt_subst_idem[OF _ \<delta>(2)] by metis
        hence "(\<theta>\<^sub>1 \<circ>\<^sub>s \<delta>) supports \<I>" using subst_support_comp \<open>\<theta>\<^sub>1 supports \<I>\<close> by metis
        
        have "\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>"
        proof -
          have "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv\<^sub>s\<^sub>t S\<^sub>1"
            using \<delta>(3) S\<^sub>1(1) \<open>fv (Fun f T') \<subseteq> fv\<^sub>s\<^sub>t S\<^sub>1\<close>
            unfolding range_vars_alt_def by (fastforce simp del: subst_range.simps)
          hence "\<lbrakk>{}; S\<^sub>1 \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>"
            using \<open>subst_idem \<delta>\<close> \<open>\<delta> \<preceq>\<^sub>\<circ> \<I>\<close> \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close> strand_sem_subst
                  wf_constr_bvars_disj'(1)[OF assms(1)]
            unfolding subst_idem_def constr_sem_c_def
            by (metis (no_types) subst_compose_assoc)
          thus "\<lbrakk>{}; S@S' \<cdot>\<^sub>s\<^sub>t \<delta>\<rbrakk>\<^sub>c \<I>" using S\<^sub>1(1) by force
        qed
        moreover have "(S@Send (Fun f T)#S', \<theta>\<^sub>1) \<leadsto> (S@S' \<cdot>\<^sub>s\<^sub>t \<delta>, \<theta>\<^sub>1 \<circ>\<^sub>s \<delta>)"
          using LI_rel.Unify[OF \<open>simple S\<close> t(1) \<delta>(1)] S\<^sub>1 by metis
        ultimately show ?thesis
          using S\<^sub>1(1) \<open>(\<theta>\<^sub>1 \<circ>\<^sub>s \<delta>) supports \<I>\<close>
          by (auto simp add: constr_sem_c_def)
      qed
    next
      \<comment> \<open>Case 2: \<open>\<I>(f(T))\<close> has been derived using the \<open>ComposeC\<close> rule.
          Simply use the \<open>Compose\<close> rule of the lazy intruder to proceed with the reduction.\<close>
      case (ComposeC T' g)
      hence "f = g" "length T = arity f" "public f"
        and "\<And>x. x \<in> set T \<Longrightarrow> ik\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile>\<^sub>c x \<cdot> \<I>"
        by auto
      hence "\<I> \<Turnstile>\<^sub>c \<langle>S@(map Send T)@S', \<theta>\<^sub>1\<rangle>" using fun_sat by metis
      moreover have "(S\<^sub>1, \<theta>\<^sub>1) \<leadsto> (S@(map Send T)@S', \<theta>\<^sub>1)"
        using S\<^sub>1 LI_rel.Compose[OF \<open>simple S\<close> \<open>length T = arity f\<close> \<open>public f\<close>]
        by metis
      ultimately show ?thesis by metis
    qed
  } moreover have "\<And>A B X F. S\<^sub>1 = A@Inequality X F#B \<Longrightarrow> ineq_model \<I> X F"
    using assms(2) by (auto simp add: constr_sem_c_def)
  ultimately show ?thesis using not_simple_elim[OF \<open>\<not>simple S\<^sub>1\<close>] by metis
qed

theorem LI_completeness:
  assumes "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1" "\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>"
  shows "\<exists>S\<^sub>2 \<theta>\<^sub>2. (S\<^sub>1,\<theta>\<^sub>1) \<leadsto>\<^sup>* (S\<^sub>2,\<theta>\<^sub>2) \<and> simple S\<^sub>2 \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>2, \<theta>\<^sub>2\<rangle>)"
proof (cases "simple S\<^sub>1")
  case False
  let ?Stuck = "\<lambda>S\<^sub>2 \<theta>\<^sub>2. \<not>(\<exists>S\<^sub>3 \<theta>\<^sub>3. (S\<^sub>2,\<theta>\<^sub>2) \<leadsto> (S\<^sub>3,\<theta>\<^sub>3) \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>3, \<theta>\<^sub>3\<rangle>))"
  let ?Sats = "{((S,\<theta>),(S',\<theta>')). (S,\<theta>) \<leadsto> (S',\<theta>') \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S, \<theta>\<rangle>) \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S', \<theta>'\<rangle>)}"

  have simple_if_stuck:
      "\<And>S\<^sub>2 \<theta>\<^sub>2. \<lbrakk>(S\<^sub>1,\<theta>\<^sub>1) \<leadsto>\<^sup>+ (S\<^sub>2,\<theta>\<^sub>2); \<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>2, \<theta>\<^sub>2\<rangle>; ?Stuck S\<^sub>2 \<theta>\<^sub>2\<rbrakk> \<Longrightarrow> simple S\<^sub>2"
    using LI_completeness_single
          LI_preserves_wellformedness
          \<open>wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1\<close>
          trancl_into_rtrancl
    by metis

  have base: "\<exists>b. ((S\<^sub>1,\<theta>\<^sub>1),b) \<in> ?Sats"
    using LI_completeness_single[OF assms False] assms(2)
    by auto

  have *: "\<And>S \<theta> S' \<theta>'. ((S,\<theta>),(S',\<theta>')) \<in> ?Sats\<^sup>+ \<Longrightarrow> (S,\<theta>) \<leadsto>\<^sup>+ (S',\<theta>') \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S', \<theta>'\<rangle>)"
  proof -
    fix S \<theta> S' \<theta>'
    assume "((S,\<theta>),(S',\<theta>')) \<in> ?Sats\<^sup>+"
    thus "(S,\<theta>) \<leadsto>\<^sup>+ (S',\<theta>') \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S', \<theta>'\<rangle>)"
      by (induct rule: trancl_induct2) auto
  qed

  have "\<exists>S\<^sub>2 \<theta>\<^sub>2. ((S\<^sub>1,\<theta>\<^sub>1),(S\<^sub>2,\<theta>\<^sub>2)) \<in> ?Sats\<^sup>+ \<and> ?Stuck S\<^sub>2 \<theta>\<^sub>2"
  proof (rule ccontr)
    assume "\<not>(\<exists>S\<^sub>2 \<theta>\<^sub>2. ((S\<^sub>1,\<theta>\<^sub>1),(S\<^sub>2,\<theta>\<^sub>2)) \<in> ?Sats\<^sup>+ \<and> ?Stuck S\<^sub>2 \<theta>\<^sub>2)"
    hence sat_not_stuck: "\<And>S\<^sub>2 \<theta>\<^sub>2. ((S\<^sub>1,\<theta>\<^sub>1),(S\<^sub>2,\<theta>\<^sub>2)) \<in> ?Sats\<^sup>+ \<Longrightarrow> \<not>?Stuck S\<^sub>2 \<theta>\<^sub>2" by blast

    have "\<forall>S \<theta>. ((S\<^sub>1,\<theta>\<^sub>1),(S,\<theta>)) \<in> ?Sats\<^sup>+ \<longrightarrow> (\<exists>b. ((S,\<theta>),b) \<in> ?Sats)"
    proof (intro allI impI)
      fix S \<theta> assume a: "((S\<^sub>1,\<theta>\<^sub>1),(S,\<theta>)) \<in> ?Sats\<^sup>+"
      have "\<And>b. ((S\<^sub>1,\<theta>\<^sub>1),b) \<in> ?Sats\<^sup>+ \<Longrightarrow> \<exists>c. b \<leadsto> c \<and> ((S\<^sub>1,\<theta>\<^sub>1),c) \<in> ?Sats\<^sup>+"
      proof -
        fix b assume in_sat: "((S\<^sub>1,\<theta>\<^sub>1),b) \<in> ?Sats\<^sup>+"
        hence "\<exists>c. (b,c) \<in> ?Sats" using * sat_not_stuck by (cases b) blast
        thus "\<exists>c. b \<leadsto> c \<and> ((S\<^sub>1,\<theta>\<^sub>1),c) \<in> ?Sats\<^sup>+"
          using trancl_into_trancl[OF in_sat] by blast
      qed
      hence "\<exists>S' \<theta>'. (S,\<theta>) \<leadsto> (S',\<theta>') \<and> ((S\<^sub>1,\<theta>\<^sub>1),(S',\<theta>')) \<in> ?Sats\<^sup>+" using a by auto
      then obtain S' \<theta>' where S'\<theta>': "(S,\<theta>) \<leadsto> (S',\<theta>')" "((S\<^sub>1,\<theta>\<^sub>1),(S',\<theta>')) \<in> ?Sats\<^sup>+" by auto
      hence "\<I> \<Turnstile>\<^sub>c \<langle>S', \<theta>'\<rangle>" using * by blast
      moreover have "(S\<^sub>1, \<theta>\<^sub>1) \<leadsto>\<^sup>+ (S,\<theta>)" using a trancl_mono by blast
      ultimately have "((S,\<theta>),(S',\<theta>')) \<in> ?Sats" using S'\<theta>'(1) * a by blast
      thus "\<exists>b. ((S,\<theta>),b) \<in> ?Sats" using S'\<theta>'(2) by blast 
    qed
    hence "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> ?Sats"
      using infinite_chain_intro'[OF base] by blast
    moreover have "?Sats \<subseteq> LI_rel\<^sup>+" by auto
    hence "\<not>(\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> ?Sats)"
      using LI_no_infinite_chain infinite_chain_mono by blast
    ultimately show False by auto
  qed
  hence "\<exists>S\<^sub>2 \<theta>\<^sub>2. (S\<^sub>1, \<theta>\<^sub>1) \<leadsto>\<^sup>+ (S\<^sub>2, \<theta>\<^sub>2) \<and> simple S\<^sub>2 \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>2, \<theta>\<^sub>2\<rangle>)"
    using simple_if_stuck * by blast
  thus ?thesis by (meson trancl_into_rtrancl)
qed (blast intro: \<open>\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle>\<close>)
end


subsection \<open>Corollary: Soundness and Completeness as a Single Theorem\<close>
corollary LI_soundness_and_completeness:
  assumes "wf\<^sub>c\<^sub>o\<^sub>n\<^sub>s\<^sub>t\<^sub>r S\<^sub>1 \<theta>\<^sub>1"
  shows "\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>1, \<theta>\<^sub>1\<rangle> \<longleftrightarrow> (\<exists>S\<^sub>2 \<theta>\<^sub>2. (S\<^sub>1,\<theta>\<^sub>1) \<leadsto>\<^sup>* (S\<^sub>2,\<theta>\<^sub>2) \<and> simple S\<^sub>2 \<and> (\<I> \<Turnstile>\<^sub>c \<langle>S\<^sub>2, \<theta>\<^sub>2\<rangle>))"
by (metis LI_soundness[OF assms] LI_completeness[OF assms])

end

end
