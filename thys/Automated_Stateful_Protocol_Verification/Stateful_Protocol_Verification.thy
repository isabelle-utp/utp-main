(*
(C) Copyright Andreas Viktor Hess, DTU, 2020
(C) Copyright Sebastian A. Mödersheim, DTU, 2020
(C) Copyright Achim D. Brucker, University of Exeter, 2020
(C) Copyright Anders Schlichtkrull, DTU, 2020

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

(*  Title:      Stateful_Protocol_Verification.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>Stateful Protocol Verification\<close>
theory Stateful_Protocol_Verification
imports Stateful_Protocol_Model Term_Implication
begin

subsection \<open>Fixed-Point Intruder Deduction Lemma\<close>
context stateful_protocol_model
begin

abbreviation pubval_terms::"('fun,'atom,'sets) prot_terms" where
  "pubval_terms \<equiv> {t. \<exists>f \<in> funs_term t. is_Val f \<and> public f}"

abbreviation abs_terms::"('fun,'atom,'sets) prot_terms" where
  "abs_terms \<equiv> {t. \<exists>f \<in> funs_term t. is_Abs f}"

definition intruder_deduct_GSMP::
  "[('fun,'atom,'sets) prot_terms,
    ('fun,'atom,'sets) prot_terms,
    ('fun,'atom,'sets) prot_term]
    \<Rightarrow> bool" ("\<langle>_;_\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P _" 50)
where
  "\<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t \<equiv> intruder_deduct_restricted M (\<lambda>t. t \<in> GSMP T - (pubval_terms \<union> abs_terms)) t"

lemma intruder_deduct_GSMP_induct[consumes 1, case_names AxiomH ComposeH DecomposeH]:
  assumes "\<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t" "\<And>t. t \<in> M \<Longrightarrow> P M t"
          "\<And>S f. \<lbrakk>length S = arity f; public f;
                  \<And>s. s \<in> set S \<Longrightarrow> \<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P s;
                  \<And>s. s \<in> set S \<Longrightarrow> P M s;
                  Fun f S \<in> GSMP T - (pubval_terms \<union> abs_terms)
                  \<rbrakk> \<Longrightarrow> P M (Fun f S)"
          "\<And>t K T' t\<^sub>i. \<lbrakk>\<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t; P M t; Ana t = (K, T'); \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P k;
                        \<And>k. k \<in> set K \<Longrightarrow> P M k; t\<^sub>i \<in> set T'\<rbrakk> \<Longrightarrow> P M t\<^sub>i"
  shows "P M t"
proof -
  let ?Q = "\<lambda>t. t \<in> GSMP T - (pubval_terms \<union> abs_terms)"
  show ?thesis
    using intruder_deduct_restricted_induct[of M ?Q t "\<lambda>M Q t. P M t"] assms
    unfolding intruder_deduct_GSMP_def
    by blast
qed

lemma pubval_terms_subst:
  assumes "t \<cdot> \<theta> \<in> pubval_terms" "\<theta> ` fv t \<inter> pubval_terms = {}"
  shows "t \<in> pubval_terms"
using assms(1,2)
proof (induction t)
  case (Fun f T)
  let ?P = "\<lambda>f. is_Val f \<and> public f"
  from Fun show ?case
  proof (cases "?P f")
    case False
    then obtain t where t: "t \<in> set T" "t \<cdot> \<theta> \<in> pubval_terms"
      using Fun.prems by auto
    hence "\<theta> ` fv t \<inter> pubval_terms = {}" using Fun.prems(2) by auto
    thus ?thesis using Fun.IH[OF t] t(1) by auto
  qed force
qed simp

lemma abs_terms_subst:
  assumes "t \<cdot> \<theta> \<in> abs_terms" "\<theta> ` fv t \<inter> abs_terms = {}"
  shows "t \<in> abs_terms"
using assms(1,2)
proof (induction t)
  case (Fun f T)
  let ?P = "\<lambda>f. is_Abs f"
  from Fun show ?case
  proof (cases "?P f")
    case False
    then obtain t where t: "t \<in> set T" "t \<cdot> \<theta> \<in> abs_terms"
      using Fun.prems by auto
    hence "\<theta> ` fv t \<inter> abs_terms = {}" using Fun.prems(2) by auto
    thus ?thesis using Fun.IH[OF t] t(1) by auto
  qed force
qed simp

lemma pubval_terms_subst':
  assumes "t \<cdot> \<theta> \<in> pubval_terms" "\<forall>n. Val (n,True) \<notin> \<Union>(funs_term ` (\<theta> ` fv t))"
  shows "t \<in> pubval_terms"
proof -
  have "\<not>public f"
    when fs: "f \<in> funs_term s" "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" "is_Val f"
    for f s
  proof -
    obtain T where T: "Fun f T \<in> subterms s" using funs_term_Fun_subterm[OF fs(1)] by moura
    hence "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" using fs(2) in_subterms_subset_Union by blast
    thus ?thesis using assms(2) funs_term_Fun_subterm'[of f T] fs(3) by (cases f) force+
  qed
  thus ?thesis using pubval_terms_subst[OF assms(1)] by force
qed

lemma abs_terms_subst':
  assumes "t \<cdot> \<theta> \<in> abs_terms" "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<theta> ` fv t))"
  shows "t \<in> abs_terms"
proof -
  have "\<not>is_Abs f" when fs: "f \<in> funs_term s" "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" for f s
  proof -
    obtain T where T: "Fun f T \<in> subterms s" using funs_term_Fun_subterm[OF fs(1)] by moura  
    hence "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" using fs(2) in_subterms_subset_Union by blast
    thus ?thesis using assms(2) funs_term_Fun_subterm'[of f T] by (cases f) auto
  qed
  thus ?thesis using abs_terms_subst[OF assms(1)] by force
qed

lemma pubval_terms_subst_range_disj:
  "subst_range \<theta> \<inter> pubval_terms = {} \<Longrightarrow> \<theta> ` fv t \<inter> pubval_terms = {}"
proof (induction t)
  case (Var x) thus ?case by (cases "x \<in> subst_domain \<theta>") auto
qed auto

lemma abs_terms_subst_range_disj:
  "subst_range \<theta> \<inter> abs_terms = {} \<Longrightarrow> \<theta> ` fv t \<inter> abs_terms = {}"
proof (induction t)
  case (Var x) thus ?case by (cases "x \<in> subst_domain \<theta>") auto
qed auto

lemma pubval_terms_subst_range_comp:
  assumes "subst_range \<theta> \<inter> pubval_terms = {}" "subst_range \<delta> \<inter> pubval_terms = {}"
  shows "subst_range (\<theta> \<circ>\<^sub>s \<delta>) \<inter> pubval_terms = {}"
proof -
  { fix t f assume t:
      "t \<in> subst_range (\<theta> \<circ>\<^sub>s \<delta>)" "f \<in> funs_term t" "is_Val f" "public f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" by auto
    have "\<theta> x \<notin> pubval_terms" using assms(1) by (cases "\<theta> x \<in> subst_range \<theta>") force+
    hence "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> pubval_terms"
      using assms(2) pubval_terms_subst[of "\<theta> x" \<delta>] pubval_terms_subst_range_disj
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3,4) x by blast
  } thus ?thesis by fast
qed

lemma pubval_terms_subst_range_comp':
  assumes "(\<theta> ` X) \<inter> pubval_terms = {}" "(\<delta> ` fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)) \<inter> pubval_terms = {}"
  shows "((\<theta> \<circ>\<^sub>s \<delta>) ` X) \<inter> pubval_terms = {}"
proof -
  { fix t f assume t:
      "t \<in> (\<theta> \<circ>\<^sub>s \<delta>) ` X" "f \<in> funs_term t" "is_Val f" "public f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" "x \<in> X" by auto
    have "\<theta> x \<notin> pubval_terms" using assms(1) x(2) by force
    moreover have "fv (\<theta> x) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)" using x(2) by (auto simp add: fv_subset)
    hence "\<delta> ` fv (\<theta> x) \<inter> pubval_terms = {}" using assms(2) by auto
    ultimately have "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> pubval_terms"
      using pubval_terms_subst[of "\<theta> x" \<delta>]
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3,4) x by blast
  } thus ?thesis by fast
qed

lemma abs_terms_subst_range_comp:
  assumes "subst_range \<theta> \<inter> abs_terms = {}" "subst_range \<delta> \<inter> abs_terms = {}"
  shows "subst_range (\<theta> \<circ>\<^sub>s \<delta>) \<inter> abs_terms = {}"
proof -
  { fix t f assume t: "t \<in> subst_range (\<theta> \<circ>\<^sub>s \<delta>)" "f \<in> funs_term t" "is_Abs f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" by auto
    have "\<theta> x \<notin> abs_terms" using assms(1) by (cases "\<theta> x \<in> subst_range \<theta>") force+
    hence "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> abs_terms"
      using assms(2) abs_terms_subst[of "\<theta> x" \<delta>] abs_terms_subst_range_disj
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3) x by blast
  } thus ?thesis by fast
qed

lemma abs_terms_subst_range_comp':
  assumes "(\<theta> ` X) \<inter> abs_terms = {}" "(\<delta> ` fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)) \<inter> abs_terms = {}"
  shows "((\<theta> \<circ>\<^sub>s \<delta>) ` X) \<inter> abs_terms = {}"
proof -
  { fix t f assume t:
      "t \<in> (\<theta> \<circ>\<^sub>s \<delta>) ` X" "f \<in> funs_term t" "is_Abs f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" "x \<in> X" by auto
    have "\<theta> x \<notin> abs_terms" using assms(1) x(2) by force
    moreover have "fv (\<theta> x) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)" using x(2) by (auto simp add: fv_subset)
    hence "\<delta> ` fv (\<theta> x) \<inter> abs_terms = {}" using assms(2) by auto
    ultimately have "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> abs_terms"
      using abs_terms_subst[of "\<theta> x" \<delta>]
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3) x by blast
  } thus ?thesis by fast
qed

context
begin
private lemma Ana_abs_aux1:
  fixes \<delta>::"(('fun,'atom,'sets) prot_fun, nat, ('fun,'atom,'sets) prot_var) gsubst"
    and \<alpha>::"nat \<times> bool \<Rightarrow> 'sets set"
  assumes "Ana\<^sub>f f = (K,T)"
  shows "(K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
proof -
  { fix k assume "k \<in> set K"
    hence "k \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)" by force
    hence "k \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = k \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
    proof (induction k)
      case (Fun g S)
      have "\<And>s. s \<in> set S \<Longrightarrow> s \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = s \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
        using Fun.IH in_subterms_subset_Union[OF Fun.prems] Fun_param_in_subterms[of _ S g]
        by (meson contra_subsetD)
      thus ?case using Ana\<^sub>f_assm1_alt[OF assms Fun.prems] by (cases g) auto
    qed simp
  } thus ?thesis unfolding abs_apply_list_def by force
qed

private lemma Ana_abs_aux2:
  fixes \<alpha>::"nat \<times> bool \<Rightarrow> 'sets set"
    and K::"(('fun,'atom,'sets) prot_fun, nat) term list"
    and M::"nat list"
    and T::"('fun,'atom,'sets) prot_term list"
  assumes "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K) \<union> set M. i < length T"
    and "(K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>n. T ! n \<cdot>\<^sub>\<alpha> \<alpha>)"
  shows "(K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T)" (is "?A1 = ?A2")
    and "(map ((!) T) M) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = map ((!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T)) M" (is "?B1 = ?B2")
proof -
  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i" when "i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K)" for i
    using that assms(1) by auto
  hence "k \<cdot> (\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>) = k \<cdot> (\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i)" when "k \<in> set K" for k
    using that term_subst_eq_conv[of k "\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>" "\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i"]
    by auto
  thus "?A1 = ?A2" using assms(2) by (force simp add: abs_apply_terms_def)

  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T ! i" when "i \<in> set M" for i
    using that assms(1) by auto
  thus "?B1 = ?B2" by (force simp add: abs_apply_list_def)
qed

private lemma Ana_abs_aux1_set:
  fixes \<delta>::"(('fun,'atom,'sets) prot_fun, nat, ('fun,'atom,'sets) prot_var) gsubst"
    and \<alpha>::"nat \<times> bool \<Rightarrow> 'sets set"
  assumes "Ana\<^sub>f f = (K,T)"
  shows "(set K \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = set K \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
proof -
  { fix k assume "k \<in> set K"
    hence "k \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)" by force
    hence "k \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = k \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
    proof (induction k)
      case (Fun g S)
      have "\<And>s. s \<in> set S \<Longrightarrow> s \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = s \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
        using Fun.IH in_subterms_subset_Union[OF Fun.prems] Fun_param_in_subterms[of _ S g]
        by (meson contra_subsetD)
      thus ?case using Ana\<^sub>f_assm1_alt[OF assms Fun.prems] by (cases g) auto
    qed simp
  } thus ?thesis unfolding abs_apply_terms_def by force
qed

private lemma Ana_abs_aux2_set:
  fixes \<alpha>::"nat \<times> bool \<Rightarrow> 'sets set"
    and K::"(('fun,'atom,'sets) prot_fun, nat) terms"
    and M::"nat set"
    and T::"('fun,'atom,'sets) prot_term list"
  assumes "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t K \<union> M. i < length T"
    and "(K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = K \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<lambda>n. T ! n \<cdot>\<^sub>\<alpha> \<alpha>)"
  shows "(K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T)" (is "?A1 = ?A2")
    and "((!) T ` M) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ` M" (is "?B1 = ?B2")
proof -
  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i" when "i \<in> fv\<^sub>s\<^sub>e\<^sub>t K" for i
    using that assms(1) by auto
  hence "k \<cdot> (\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>) = k \<cdot> (\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i)" when "k \<in> K" for k
    using that term_subst_eq_conv[of k "\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>" "\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i"]
    by auto
  thus "?A1 = ?A2" using assms(2) by (force simp add: abs_apply_terms_def)

  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T ! i" when "i \<in> M" for i
    using that assms(1) by auto
  thus "?B1 = ?B2" by (force simp add: abs_apply_terms_def)
qed

lemma Ana_abs:
  fixes t::"('fun,'atom,'sets) prot_term"
  assumes "Ana t = (K, T)"
  shows "Ana (t \<cdot>\<^sub>\<alpha> \<alpha>) = (K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>, T \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)"
  using assms
proof (induction t rule: Ana.induct)
  case (1 f S)
  obtain K' T' where *: "Ana\<^sub>f f = (K',T')" by moura
  show ?case using 1
  proof (cases "arity\<^sub>f f = length S \<and> arity\<^sub>f f > 0")
    case True
    hence "K = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) S" "T = map ((!) S) T'"
        and **: "arity\<^sub>f f = length (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)" "arity\<^sub>f f > 0"
      using 1 * by auto
    hence "K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)"
          "T \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = map ((!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)) T'"
      using Ana\<^sub>f_assm2_alt[OF *] Ana_abs_aux2[OF _ Ana_abs_aux1[OF *], of T' S \<alpha>]
      unfolding abs_apply_list_def
      by auto
    moreover have "Fun (Fu f) S \<cdot>\<^sub>\<alpha> \<alpha> = Fun (Fu f) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)" by simp
    ultimately show ?thesis using Ana_Fu_intro[OF ** *] by metis
  qed (auto simp add: abs_apply_list_def)
qed (simp_all add: abs_apply_list_def)
end

lemma deduct_FP_if_deduct:
  fixes M IK FP::"('fun,'atom,'sets) prot_terms"
  assumes IK: "IK \<subseteq> GSMP M - (pubval_terms \<union> abs_terms)" "\<forall>t \<in> IK \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>. FP \<turnstile>\<^sub>c t"
    and t: "IK \<turnstile> t" "t \<in> GSMP M - (pubval_terms \<union> abs_terms)"
  shows "FP \<turnstile> t \<cdot>\<^sub>\<alpha> \<alpha>"
proof -
  let ?P = "\<lambda>f. is_Val f \<longrightarrow> \<not>public f"
  let ?GSMP = "GSMP M - (pubval_terms \<union> abs_terms)"

  have 1: "\<forall>m \<in> IK. m \<in> ?GSMP"
    using IK(1) by blast

  have 2: "\<forall>t t'. t \<in> ?GSMP \<longrightarrow> t' \<sqsubseteq> t \<longrightarrow> t' \<in> ?GSMP"
  proof (intro allI impI)
    fix t t' assume t: "t \<in> ?GSMP" "t' \<sqsubseteq> t"
    hence "t' \<in> GSMP M" using ground_subterm unfolding GSMP_def by auto
    moreover have "\<not>public f"
      when "f \<in> funs_term t" "is_Val f" for f
      using t(1) that by auto
    hence "\<not>public f"
      when "f \<in> funs_term t'" "is_Val f" for f
      using that subtermeq_imp_funs_term_subset[OF t(2)] by auto
    moreover have "\<not>is_Abs f" when "f \<in> funs_term t" for f using t(1) that by auto
    hence "\<not>is_Abs f" when "f \<in> funs_term t'" for f
      using that subtermeq_imp_funs_term_subset[OF t(2)] by auto
    ultimately show "t' \<in> ?GSMP" by simp
  qed

  have 3: "\<forall>t K T k. t \<in> ?GSMP \<longrightarrow> Ana t = (K, T) \<longrightarrow> k \<in> set K \<longrightarrow> k \<in> ?GSMP"
  proof (intro allI impI)
    fix t K T k assume t: "t \<in> ?GSMP" "Ana t = (K, T)" "k \<in> set K"
    hence "k \<in> GSMP M" using GSMP_Ana_key by blast
    moreover have "\<forall>f \<in> funs_term t. ?P f" using t(1) by auto
    with t(2,3) have "\<forall>f \<in> funs_term k. ?P f"
    proof (induction t arbitrary: k rule: Ana.induct)
      case 1 thus ?case by (metis Ana_Fu_keys_not_pubval_terms surj_pair)
    qed auto
    moreover have "\<forall>f \<in> funs_term t. \<not>is_Abs f" using t(1) by auto
    with t(2,3) have "\<forall>f \<in> funs_term k. \<not>is_Abs f"
    proof (induction t arbitrary: k rule: Ana.induct)
      case 1 thus ?case by (metis Ana_Fu_keys_not_abs_terms surj_pair)
    qed auto
    ultimately show "k \<in> ?GSMP" by simp
  qed

  have "\<langle>IK; M\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t"
    unfolding intruder_deduct_GSMP_def
    by (rule restricted_deduct_if_deduct'[OF 1 2 3 t])
  thus ?thesis
  proof (induction t rule: intruder_deduct_GSMP_induct)
    case (AxiomH t)
    show ?case using IK(2) abs_in[OF AxiomH.hyps] by force
  next
    case (ComposeH T f)
    have *: "Fun f T \<cdot>\<^sub>\<alpha> \<alpha> = Fun f (map (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) T)"
      using ComposeH.hyps(2,4)
      by (cases f) auto

    have **: "length (map (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) T) = arity f"
      using ComposeH.hyps(1)
      by auto

    show ?case
      using intruder_deduct.Compose[OF ** ComposeH.hyps(2)] ComposeH.IH(1) *
      by auto
  next
    case (DecomposeH t K T' t\<^sub>i)
    have *: "Ana (t \<cdot>\<^sub>\<alpha> \<alpha>) = (K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>, T' \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)"
      using Ana_abs[OF DecomposeH.hyps(2)]
      by metis

    have **: "t\<^sub>i \<cdot>\<^sub>\<alpha> \<alpha> \<in> set (T' \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)"
      using DecomposeH.hyps(4) abs_in abs_list_set_is_set_abs_set[of T']
      by auto

    have ***: "FP \<turnstile> k"
      when k: "k \<in> set (K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)" for k
    proof -
      obtain k' where k': "k' \<in> set K" "k = k' \<cdot>\<^sub>\<alpha> \<alpha>"
        by (metis (no_types) k abs_apply_terms_def imageE abs_list_set_is_set_abs_set)

      show "FP \<turnstile> k"
        using DecomposeH.IH k' by blast
    qed

    show ?case
      using intruder_deduct.Decompose[OF _ * _ **]
            DecomposeH.IH(1) ***(1)
      by blast
  qed
qed

end


subsection \<open>Computing and Checking Term Implications and Messages\<close>
context stateful_protocol_model
begin

abbreviation (input) "absc s \<equiv> (Fun (Abs s) []::('fun, 'atom, 'sets) prot_term)"

fun absdbupd where
  "absdbupd [] _ a = a"
| "absdbupd (insert\<langle>Var y, Fun (Set s) T\<rangle>#D) x a = (
    if x = y then absdbupd D x (insert s a) else absdbupd D x a)"
| "absdbupd (delete\<langle>Var y, Fun (Set s) T\<rangle>#D) x a = (
    if x = y then absdbupd D x (a - {s}) else absdbupd D x a)"
| "absdbupd (_#D) x a = absdbupd D x a"

lemma absdbupd_cons_cases:
  "absdbupd (insert\<langle>Var x, Fun (Set s) T\<rangle>#D) x d = absdbupd D x (insert s d)"
  "absdbupd (delete\<langle>Var x, Fun (Set s) T\<rangle>#D) x d = absdbupd D x (d - {s})"
  "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T) \<Longrightarrow> absdbupd (insert\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
  "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T) \<Longrightarrow> absdbupd (delete\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
proof -
  assume *: "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T)"
  let ?P = "absdbupd (insert\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
  let ?Q = "absdbupd (delete\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
  { fix y f T assume "t = Fun f T \<or> u = Var y" hence ?P ?Q by auto
  } moreover {
    fix y f T assume "t = Var y" "u = Fun f T" hence ?P using * by (cases f) auto
  } moreover {
    fix y f T assume "t = Var y" "u = Fun f T" hence ?Q using * by (cases f) auto
  } ultimately show ?P ?Q by (metis term.exhaust)+
qed simp_all

lemma absdbupd_filter: "absdbupd S x d = absdbupd (filter is_Update S) x d"
by (induction S x d rule: absdbupd.induct) simp_all

lemma absdbupd_append:
  "absdbupd (A@B) x d = absdbupd B x (absdbupd A x d)"
proof (induction A arbitrary: d)
  case (Cons a A) thus ?case
  proof (cases a)
    case (Insert t u) thus ?thesis
    proof (cases "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T)")
      case False
      then obtain s T where "t = Var x" "u = Fun (Set s) T" by moura
      thus ?thesis by (simp add: Insert Cons.IH absdbupd_cons_cases(1))
    qed (simp_all add: Cons.IH absdbupd_cons_cases(3))
  next
    case (Delete t u) thus ?thesis
    proof (cases "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T)")
      case False
      then obtain s T where "t = Var x" "u = Fun (Set s) T" by moura
      thus ?thesis by (simp add: Delete Cons.IH absdbupd_cons_cases(2))
    qed (simp_all add: Cons.IH absdbupd_cons_cases(4))
  qed simp_all
qed simp

lemma absdbupd_wellformed_transaction:
  assumes T: "wellformed_transaction T"
  shows "absdbupd (unlabel (transaction_strand T)) = absdbupd (unlabel (transaction_updates T))"
proof -
  define S0 where "S0 \<equiv> unlabel (transaction_strand T)"
  define S1 where "S1 \<equiv> unlabel (transaction_receive T)"
  define S2 where "S2 \<equiv> unlabel (transaction_selects T)"
  define S3 where "S3 \<equiv> unlabel (transaction_checks T)"
  define S4 where "S4 \<equiv> unlabel (transaction_updates T)"
  define S5 where "S5 \<equiv> unlabel (transaction_send T)"

  note S_defs = S0_def S1_def S2_def S3_def S4_def S5_def

  have 0: "list_all is_Receive S1"
          "list_all is_Assignment S2"
          "list_all is_Check S3"
          "list_all is_Update S4"
          "list_all is_Send S5"
    using T unfolding wellformed_transaction_def S_defs by metis+

  have "filter is_Update S1 = []"
       "filter is_Update S2 = []"
       "filter is_Update S3 = []"
       "filter is_Update S4 = S4"
       "filter is_Update S5 = []"
    using list_all_filter_nil[OF 0(1), of is_Update]
          list_all_filter_nil[OF 0(2), of is_Update]
          list_all_filter_nil[OF 0(3), of is_Update]
          list_all_filter_eq[OF 0(4)]
          list_all_filter_nil[OF 0(5), of is_Update]
    by blast+
  moreover have "S0 = S1@S2@S3@S4@S5"
    unfolding S_defs transaction_strand_def unlabel_def by auto
  ultimately have "filter is_Update S0 = S4"
    using filter_append[of is_Update] list_all_append[of is_Update]
    by simp
  thus ?thesis
    using absdbupd_filter[of S0]
    unfolding S_defs by presburger
qed

fun abs_substs_set::
  "[('fun,'atom,'sets) prot_var list,
    'sets set list,
    ('fun,'atom,'sets) prot_var \<Rightarrow> 'sets set,
    ('fun,'atom,'sets) prot_var \<Rightarrow> 'sets set]
  \<Rightarrow> ((('fun,'atom,'sets) prot_var \<times> 'sets set) list) list"
where
  "abs_substs_set [] _ _ _ = [[]]"
| "abs_substs_set (x#xs) as posconstrs negconstrs = (
    let bs = filter (\<lambda>a. posconstrs x \<subseteq> a \<and> a \<inter> negconstrs x = {}) as
    in concat (map (\<lambda>b. map (\<lambda>\<delta>. (x, b)#\<delta>) (abs_substs_set xs as posconstrs negconstrs)) bs))"

definition abs_substs_fun::
  "[(('fun,'atom,'sets) prot_var \<times> 'sets set) list,
    ('fun,'atom,'sets) prot_var]
  \<Rightarrow> 'sets set"
where
  "abs_substs_fun \<delta> x = (case find (\<lambda>b. fst b = x) \<delta> of Some (_,a) \<Rightarrow> a | None \<Rightarrow> {})"

lemmas abs_substs_set_induct = abs_substs_set.induct[case_names Nil Cons]

fun transaction_poschecks_comp::
  "(('fun,'atom,'sets) prot_fun, ('fun,'atom,'sets) prot_var) stateful_strand
  \<Rightarrow> (('fun,'atom,'sets) prot_var \<Rightarrow> 'sets set)"
where
  "transaction_poschecks_comp [] = (\<lambda>_. {})"
| "transaction_poschecks_comp (\<langle>_: Var x \<in> Fun (Set s) []\<rangle>#T) = (
    let f = transaction_poschecks_comp T in f(x := insert s (f x)))"
| "transaction_poschecks_comp (_#T) = transaction_poschecks_comp T"

fun transaction_negchecks_comp::
  "(('fun,'atom,'sets) prot_fun, ('fun,'atom,'sets) prot_var) stateful_strand
  \<Rightarrow> (('fun,'atom,'sets) prot_var \<Rightarrow> 'sets set)"
where
  "transaction_negchecks_comp [] = (\<lambda>_. {})"
| "transaction_negchecks_comp (\<langle>Var x not in Fun (Set s) []\<rangle>#T) = (
    let f = transaction_negchecks_comp T in f(x := insert s (f x)))"
| "transaction_negchecks_comp (_#T) = transaction_negchecks_comp T"

definition transaction_check_pre where
  "transaction_check_pre FP TI T \<delta> \<equiv>
    let C = set (unlabel (transaction_checks T));
        S = set (unlabel (transaction_selects T));
        xs = fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T));
        \<theta> = \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x
    in (\<forall>x \<in> set (transaction_fresh T). \<delta> x = {}) \<and>
       (\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)) \<and>
       (\<forall>u \<in> S \<union> C.
          (is_InSet u \<longrightarrow> (
            let x = the_elem_term u; s = the_set_term u
            in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<in> \<delta> (the_Var x))) \<and>
          ((is_NegChecks u \<and> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p u = [] \<and> the_eqs u = [] \<and> length (the_ins u) = 1) \<longrightarrow> (
            let x = fst (hd (the_ins u)); s = snd (hd (the_ins u))
            in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<notin> \<delta> (the_Var x))))"

definition transaction_check_post where
  "transaction_check_post FP TI T \<delta> \<equiv>
    let xs = fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T));
        \<theta> = \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x;
        u = \<lambda>\<delta> x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)
    in (\<forall>x \<in> set xs - set (transaction_fresh T). \<delta> x \<noteq> u \<delta> x \<longrightarrow> List.member TI (\<delta> x, u \<delta> x)) \<and>
       (\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> (u \<delta>)))"

definition transaction_check_comp::
  "[('fun,'atom,'sets) prot_term list,
    'sets set list,
    ('sets set \<times> 'sets set) list,
    ('fun,'atom,'sets,'lbl) prot_transaction]
  \<Rightarrow> ((('fun,'atom,'sets) prot_var \<times> 'sets set) list) list"
where
  "transaction_check_comp FP OCC TI T \<equiv>
    let S = unlabel (transaction_strand T);
        C = unlabel (transaction_selects T@transaction_checks T);
        xs = filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S);
        posconstrs = transaction_poschecks_comp C;
        negconstrs = transaction_negchecks_comp C;
        pre_check = transaction_check_pre FP TI T
    in filter (\<lambda>\<delta>. pre_check (abs_substs_fun \<delta>)) (abs_substs_set xs OCC posconstrs negconstrs)"

definition transaction_check::
  "[('fun,'atom,'sets) prot_term list,
    'sets set list,
    ('sets set \<times> 'sets set) list,
    ('fun,'atom,'sets,'lbl) prot_transaction]
  \<Rightarrow> bool"
where
  "transaction_check FP OCC TI T \<equiv>
    list_all (\<lambda>\<delta>. transaction_check_post FP TI T (abs_substs_fun \<delta>)) (transaction_check_comp FP OCC TI T)"

lemma abs_subst_fun_cons:
  "abs_substs_fun ((x,b)#\<delta>) = (abs_substs_fun \<delta>)(x := b)"
unfolding abs_substs_fun_def by fastforce

lemma abs_substs_cons:
  assumes "\<delta> \<in> set (abs_substs_set xs as poss negs)" "b \<in> set as" "poss x \<subseteq> b" "b \<inter> negs x = {}"
  shows "(x,b)#\<delta> \<in> set (abs_substs_set (x#xs) as poss negs)"
using assms by auto

lemma abs_substs_cons':
  assumes \<delta>: "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs)"
    and b: "b \<in> set as" "poss x \<subseteq> b" "b \<inter> negs x = {}"
  shows "\<delta>(x := b) \<in> abs_substs_fun ` set (abs_substs_set (x#xs) as poss negs)"
proof -
  obtain \<theta> where \<theta>: "\<delta> = abs_substs_fun \<theta>" "\<theta> \<in> set (abs_substs_set xs as poss negs)"
    using \<delta> by moura
  have "abs_substs_fun ((x, b)#\<theta>) \<in> abs_substs_fun ` set (abs_substs_set (x#xs) as poss negs)"
    using abs_substs_cons[OF \<theta>(2) b] by blast
  thus ?thesis
    using \<theta>(1) abs_subst_fun_cons[of x b \<theta>] by argo
qed

lemma abs_substs_has_all_abs:
  assumes "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<in> set as"
    and "\<forall>x. x \<in> set xs \<longrightarrow> poss x \<subseteq> \<delta> x"
    and "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<inter> negs x = {}"
    and "\<forall>x. x \<notin> set xs \<longrightarrow> \<delta> x = {}"
  shows "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs)"
using assms
proof (induction xs arbitrary: \<delta>)
  case (Cons x xs)
  define \<theta> where "\<theta> \<equiv> \<lambda>y. if y \<in> set xs then \<delta> y else {}"

  have "\<theta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs)"
    using Cons.prems Cons.IH by (simp add: \<theta>_def)
  moreover have "\<delta> x \<in> set as" "poss x \<subseteq> \<delta> x" "\<delta> x \<inter> negs x = {}"
    using Cons.prems(1,2,3) by fastforce+
  ultimately have 0: "\<theta>(x := \<delta> x) \<in> abs_substs_fun ` set (abs_substs_set (x#xs) as poss negs)"
    by (metis abs_substs_cons')

  have "\<delta> = \<theta>(x := \<delta> x)"
  proof
    fix y show "\<delta> y = (\<theta>(x := \<delta> x)) y"
    proof (cases "y \<in> set (x#xs)")
      case False thus ?thesis using Cons.prems(4) by (fastforce simp add: \<theta>_def)
    qed (auto simp add: \<theta>_def)
  qed
  thus ?case by (metis 0)
qed (auto simp add: abs_substs_fun_def)

lemma abs_substs_abss_bounded:
  assumes "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs)"
    and "x \<in> set xs"
  shows "\<delta> x \<in> set as"
    and "poss x \<subseteq> \<delta> x"
    and "\<delta> x \<inter> negs x = {}"
using assms
proof (induct xs as poss negs arbitrary: \<delta> rule: abs_substs_set_induct)
  case (Cons y xs as poss negs)
  { case 1 thus ?case using Cons.hyps(1) unfolding abs_substs_fun_def by fastforce }

  { case 2 thus ?case
    proof (cases "x = y")
      case False
      then obtain \<delta>' where \<delta>':
          "\<delta>' \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs)" "\<delta>' x = \<delta> x"
        using 2 unfolding abs_substs_fun_def by force
      moreover have "x \<in> set xs" using 2(2) False by simp
      moreover have "\<exists>b. b \<in> set as \<and> poss y \<subseteq> b \<and> b \<inter> negs y = {}"
        using 2 False by auto
      ultimately show ?thesis using Cons.hyps(2) by fastforce
    qed (auto simp add: abs_substs_fun_def)
  }

  { case 3 thus ?case
    proof (cases "x = y")
      case False
      then obtain \<delta>' where \<delta>':
          "\<delta>' \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs)" "\<delta>' x = \<delta> x"
        using 3 unfolding abs_substs_fun_def by force
      moreover have "x \<in> set xs" using 3(2) False by simp
      moreover have "\<exists>b. b \<in> set as \<and> poss y \<subseteq> b \<and> b \<inter> negs y = {}"
        using 3 False by auto
      ultimately show ?thesis using Cons.hyps(3) by fastforce
    qed (auto simp add: abs_substs_fun_def)
  }
qed (simp_all add: abs_substs_fun_def)

lemma transaction_poschecks_comp_unfold:
  "transaction_poschecks_comp C x = {s. \<exists>a. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> set C}"
proof (induction C)
  case (Cons c C) thus ?case
  proof (cases "\<exists>a y s. c = \<langle>a: Var y \<in> Fun (Set s) []\<rangle>")
    case True
    then obtain a y s where c: "c = \<langle>a: Var y \<in> Fun (Set s) []\<rangle>" by moura

    define f where "f \<equiv> transaction_poschecks_comp C"

    have "transaction_poschecks_comp (c#C) = f(y := insert s (f y))"
      using c by (simp add: f_def Let_def)
    moreover have "f x = {s. \<exists>a. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> set C}"
      using Cons.IH unfolding f_def by blast
    ultimately show ?thesis using c by auto
  next
    case False
    hence "transaction_poschecks_comp (c#C) = transaction_poschecks_comp C" (is ?P)
      using transaction_poschecks_comp.cases[of "c#C" ?P] by force
    thus ?thesis using False Cons.IH by auto
  qed
qed simp

lemma transaction_poschecks_comp_notin_fv_empty:
  assumes "x \<notin> fv\<^sub>s\<^sub>s\<^sub>t C"
  shows "transaction_poschecks_comp C x = {}"
using assms transaction_poschecks_comp_unfold[of C x] by fastforce

lemma transaction_negchecks_comp_unfold:
  "transaction_negchecks_comp C x = {s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set C}"
proof (induction C)
  case (Cons c C) thus ?case
  proof (cases "\<exists>y s. c = \<langle>Var y not in Fun (Set s) []\<rangle>")
    case True
    then obtain y s where c: "c = \<langle>Var y not in Fun (Set s) []\<rangle>" by moura

    define f where "f \<equiv> transaction_negchecks_comp C"

    have "transaction_negchecks_comp (c#C) = f(y := insert s (f y))"
      using c by (simp add: f_def Let_def)
    moreover have "f x = {s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set C}"
      using Cons.IH unfolding f_def by blast
    ultimately show ?thesis using c by auto
  next
    case False
    hence "transaction_negchecks_comp (c#C) = transaction_negchecks_comp C" (is ?P)
      using transaction_negchecks_comp.cases[of "c#C" ?P] 
      by force
    thus ?thesis using False Cons.IH by fastforce
  qed
qed simp  

lemma transaction_negchecks_comp_notin_fv_empty:
  assumes "x \<notin> fv\<^sub>s\<^sub>s\<^sub>t C"
  shows "transaction_negchecks_comp C x = {}"
using assms transaction_negchecks_comp_unfold[of C x] by fastforce

lemma transaction_check_preI[intro]:
  fixes T
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
    and "S \<equiv> set (unlabel (transaction_selects T))"
    and "C \<equiv> set (unlabel (transaction_checks T))"
  assumes a0: "\<forall>x \<in> set (transaction_fresh T). \<delta> x = {}"
    and a1: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> \<delta> x \<in> set OCC"
    and a2: "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)"
    and a3: "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> S \<union> C \<longrightarrow> s \<in> \<delta> x"
    and a4: "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> S \<union> C \<longrightarrow> s \<notin> \<delta> x"
  shows "transaction_check_pre FP TI T \<delta>"
proof -
  let ?P = "\<lambda>u. is_InSet u \<longrightarrow> (
    let x = the_elem_term u; s = the_set_term u
    in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<in> \<delta> (the_Var x))"

  let ?Q = "\<lambda>u. (is_NegChecks u \<and> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p u = [] \<and> the_eqs u = [] \<and> length (the_ins u) = 1) \<longrightarrow> (
    let x = fst (hd (the_ins u)); s = snd (hd (the_ins u))
    in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<notin> \<delta> (the_Var x))"

  have 1: "?P u" when u: "u \<in> S \<union> C" for u
    apply (unfold Let_def, intro impI, elim conjE)
    using u a3 Fun_Set_InSet_iff[of u] by metis

  have 2: "?Q u" when u: "u \<in> S \<union> C" for u
    apply (unfold Let_def, intro impI, elim conjE)
    using u a4 Fun_Set_NotInSet_iff[of u] by metis

  show ?thesis
    using a0 a1 a2 1 2 fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
    unfolding transaction_check_pre_def \<theta>_def S_def C_def Let_def
    by blast
qed

lemma transaction_check_pre_InSetE:
  assumes T: "transaction_check_pre FP TI T \<delta>"
    and u: "u = \<langle>a: Var x \<in> Fun (Set s) []\<rangle>"
           "u \<in> set (unlabel (transaction_selects T)) \<union> set (unlabel (transaction_checks T))"
  shows "s \<in> \<delta> x"
proof -
  have "is_InSet u \<longrightarrow> is_Var (the_elem_term u) \<and> is_Fun_Set (the_set_term u) \<longrightarrow>
        the_Set (the_Fun (the_set_term u)) \<in> \<delta> (the_Var (the_elem_term u))"
    using T u unfolding transaction_check_pre_def Let_def by blast
  thus ?thesis using Fun_Set_InSet_iff[of u a x s] u by argo
qed

lemma transaction_check_pre_NotInSetE:
  assumes T: "transaction_check_pre FP TI T \<delta>"
    and u: "u = \<langle>Var x not in Fun (Set s) []\<rangle>"
           "u \<in> set (unlabel (transaction_selects T)) \<union> set (unlabel (transaction_checks T))"
  shows "s \<notin> \<delta> x"
proof -
  have "is_NegChecks u \<and> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p u = [] \<and> the_eqs u = [] \<and> length (the_ins u) = 1 \<longrightarrow>
         is_Var (fst (hd (the_ins u))) \<and> is_Fun_Set (snd (hd (the_ins u))) \<longrightarrow>
         the_Set (the_Fun (snd (hd (the_ins u)))) \<notin> \<delta> (the_Var (fst (hd (the_ins u))))"
    using T u unfolding transaction_check_pre_def Let_def by blast
  thus ?thesis using Fun_Set_NotInSet_iff[of u  x s] u by argo
qed

lemma transaction_check_compI[intro]:
  assumes T: "transaction_check_pre FP TI T \<delta>"
    and T_adm: "admissible_transaction T"
    and x1: "\<forall>x. (x \<in> fv_transaction T - set (transaction_fresh T) \<and> fst x = TAtom Value)
                  \<longrightarrow> \<delta> x \<in> set OCC"
    and x2: "\<forall>x. (x \<notin> fv_transaction T - set (transaction_fresh T) \<or> fst x \<noteq> TAtom Value)
                  \<longrightarrow> \<delta> x = {}"
  shows "\<delta> \<in> abs_substs_fun ` set (transaction_check_comp FP OCC TI T)"
proof -
  define S where "S \<equiv> unlabel (transaction_strand T)"
  define C where "C \<equiv> unlabel (transaction_selects T@transaction_checks T)"
  define C' where "C' \<equiv> set (unlabel (transaction_selects T)) \<union>
                        set (unlabel (transaction_checks T))"

  let ?xs = "fv_list\<^sub>s\<^sub>s\<^sub>t S"

  define poss where "poss \<equiv> transaction_poschecks_comp C"
  define negs where "negs \<equiv> transaction_negchecks_comp C"
  define ys where "ys \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) ?xs"

  have C_C'_eq: "set C = C'"
    using unlabel_append[of "transaction_selects T" "transaction_checks T"]
    unfolding C_def C'_def by simp

  have ys: "{x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value} = set ys"
    using fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of S]
    unfolding ys_def S_def by force
  
  have "\<delta> x \<in> set OCC"
    when x: "x \<in> set ys" for x
    using x1 x ys by blast
  moreover have "\<delta> x = {}"
    when x: "x \<notin> set ys" for x
    using x2 x ys by blast
  moreover have "poss x \<subseteq> \<delta> x" when x: "x \<in> set ys" for x
  proof -
    have "s \<in> \<delta> x" when u: "u = \<langle>a: Var x \<in> Fun (Set s) []\<rangle>" "u \<in> C'" for u a s
      using T u transaction_check_pre_InSetE[of FP TI T \<delta>]
      unfolding C'_def by blast
    thus ?thesis
      using transaction_poschecks_comp_unfold[of C x] C_C'_eq
      unfolding poss_def by blast
  qed
  moreover have "\<delta> x \<inter> negs x = {}" when x: "x \<in> set ys" for x
  proof (cases "x \<in> fv\<^sub>s\<^sub>s\<^sub>t C")
    case True
    hence "s \<notin> \<delta> x" when u: "u = \<langle>Var x not in Fun (Set s) []\<rangle>" "u \<in> C'" for u s
      using T u transaction_check_pre_NotInSetE[of FP TI T \<delta>]
      unfolding C'_def by blast
    thus ?thesis
      using transaction_negchecks_comp_unfold[of C x] C_C'_eq
      unfolding negs_def by blast
  next
    case False
    hence "negs x = {}"
      using x C_C'_eq transaction_negchecks_comp_notin_fv_empty
      unfolding negs_def by blast
    thus ?thesis by blast
  qed
  ultimately have "\<delta> \<in> abs_substs_fun ` set (abs_substs_set ys OCC poss negs)"
    using abs_substs_has_all_abs[of ys \<delta> OCC poss negs] 
    by fast
  thus ?thesis
    using T
    unfolding transaction_check_comp_def Let_def S_def C_def ys_def poss_def negs_def
    by fastforce
qed

context
begin
private lemma transaction_check_comp_in_aux:
  fixes T
  defines "S \<equiv> set (unlabel (transaction_selects T))"
    and "C \<equiv> set (unlabel (transaction_checks T))"
  assumes T_adm: "admissible_transaction T"
    and a1: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          select\<langle>Var x, Fun (Set s) []\<rangle> \<in> S \<longrightarrow> s \<in> \<alpha> x)"
    and a2: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha> x)"
    and a3: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha> x)"
  shows "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> S \<union> C \<longrightarrow> s \<in> \<alpha> x" (is ?A)
    and "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> S \<union> C \<longrightarrow> s \<notin> \<alpha> x" (is ?B)
proof -
  have T_valid: "wellformed_transaction T"
      and T_adm_S: "admissible_transaction_selects T"
      and T_adm_C: "admissible_transaction_checks T"
    using T_adm unfolding admissible_transaction_def by blast+

  note * = admissible_transaction_strand_step_cases(2,3)[OF T_adm]

  have 1: "fst x = TAtom Value" "x \<in> fv_transaction T - set (transaction_fresh T)"
    when x: "\<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> S \<union> C" for a x s
    using * x unfolding S_def C_def by fast+

  have 2: "fst x = TAtom Value" "x \<in> fv_transaction T - set (transaction_fresh T)"
    when x: "\<langle>Var x not in Fun (Set s) []\<rangle> \<in> S \<union> C" for x s
    using * x unfolding S_def C_def by fast+

  have 3: "select\<langle>Var x, Fun (Set s) []\<rangle> \<in> S"
    when x: "select\<langle>Var x, Fun (Set s) []\<rangle> \<in> S \<union> C" for x s
    using * x unfolding S_def C_def by fast

  have 4: "\<langle>Var x in Fun (Set s) []\<rangle> \<in> C"
    when x: "\<langle>Var x in Fun (Set s) []\<rangle> \<in> S \<union> C" for x s
    using * x unfolding S_def C_def by fast

  have 5: "\<langle>Var x not in Fun (Set s) []\<rangle> \<in> C"
    when x: "\<langle>Var x not in Fun (Set s) []\<rangle> \<in> S \<union> C" for x s
    using * x unfolding S_def C_def by fast

  show ?A
  proof (intro allI impI)
    fix a x s assume u: "\<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> S \<union> C"
    thus "s \<in> \<alpha> x" using 1 3 4 a1 a2 by (cases a) metis+
  qed

  show ?B
  proof (intro allI impI)
    fix x s assume u: "\<langle>Var x not in Fun (Set s) []\<rangle> \<in> S \<union> C"
    thus "s \<notin> \<alpha> x" using 2 5 a3 by meson
  qed
qed

lemma transaction_check_comp_in:
  fixes T
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
    and "S \<equiv> set (unlabel (transaction_selects T))"
    and "C \<equiv> set (unlabel (transaction_checks T))"
  assumes T_adm: "admissible_transaction T"
    and a1: "\<forall>x \<in> set (transaction_fresh T). \<alpha> x = {}"
    and a2: "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>)"
    and a3: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<forall>s.
          select\<langle>Var x, Fun (Set s) []\<rangle> \<in> S \<longrightarrow> s \<in> \<alpha> x"
    and a4: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<forall>s.
          \<langle>Var x in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha> x"
    and a5: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<forall>s.
          \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha> x"
    and a6: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
          fst x = TAtom Value \<longrightarrow> \<alpha> x \<in> set OCC"
  shows "\<exists>\<delta> \<in> abs_substs_fun ` set (transaction_check_comp FP OCC TI T). \<forall>x \<in> fv_transaction T.
          fst x = TAtom Value \<longrightarrow> \<alpha> x = \<delta> x"
proof -
  let ?xs = "fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T))"
  let ?ys = "filter (\<lambda>x. x \<notin> set (transaction_fresh T)) ?xs"

  define \<alpha>' where "\<alpha>' \<equiv> \<lambda>x.
    if x \<in> fv_transaction T - set (transaction_fresh T) \<and> fst x = TAtom Value
    then \<alpha> x
    else {}"

  have T_valid: "wellformed_transaction T"
    using T_adm unfolding admissible_transaction_def by blast

  have \<theta>\<alpha>_Fun: "is_Fun (t \<cdot> \<theta> \<alpha>) \<longleftrightarrow> is_Fun (t \<cdot> \<theta> \<alpha>')" for t
    unfolding \<alpha>'_def \<theta>_def
    by (induct t) auto

  have "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>')"
  proof (intro ballI impI)
    fix t assume t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"

    have 1: "intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>)"
      using t a2
      by auto

    obtain r where r:
        "r \<in> set (unlabel (transaction_receive T))"
        "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p r"
      using t by auto
    hence "r = receive\<langle>t\<rangle>"
      using wellformed_transaction_unlabel_cases(1)[OF T_valid]
      by fastforce
    hence 2: "fv t \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)" using r by force

    have "fv t \<subseteq> fv_transaction T"
      by (metis (no_types, lifting) 2 transaction_strand_def sst_vars_append_subset(1)
                unlabel_append subset_Un_eq sup.bounded_iff)
    moreover have "fv t \<inter> set (transaction_fresh T) = {}"
      using 2 T_valid vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_receive T)"]
      unfolding wellformed_transaction_def
      by fast
    ultimately have "\<theta> \<alpha> x = \<theta> \<alpha>' x" when "x \<in> fv t" for x
      using that unfolding \<alpha>'_def \<theta>_def by fastforce
    hence 3: "t \<cdot> \<theta> \<alpha> = t \<cdot> \<theta> \<alpha>'"
      using term_subst_eq by blast

    show "intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>')" using 1 3 by simp
  qed
  moreover have
      "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          select\<langle>Var x, Fun (Set s) []\<rangle> \<in> S \<longrightarrow> s \<in> \<alpha>' x)"
      "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha>' x)"
      "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha>' x)"
    using a3 a4 a5
    unfolding \<alpha>'_def \<theta>_def S_def C_def
    by meson+
  hence "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> S \<union> C \<longrightarrow> s \<in> \<alpha>' x"
        "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> S \<union> C \<longrightarrow> s \<notin> \<alpha>' x"
    using transaction_check_comp_in_aux[OF T_adm, of \<alpha>']
    unfolding S_def C_def
    by fast+
  ultimately have 4: "transaction_check_pre FP TI T \<alpha>'"
    using a6 transaction_check_preI[of T \<alpha>' OCC FP TI]
    unfolding \<alpha>'_def \<theta>_def S_def C_def by simp

  have 5: "\<forall>x \<in> fv_transaction T. fst x = TAtom Value \<longrightarrow> \<alpha> x = \<alpha>' x"
    using a1 by (auto simp add: \<alpha>'_def)

  have 6: "\<alpha>' \<in> abs_substs_fun ` set (transaction_check_comp FP OCC TI T)"
    using transaction_check_compI[OF 4 T_adm] a6
    unfolding \<alpha>'_def
    by auto

  show ?thesis using 5 6 by blast
qed
end

end


subsection \<open>Automatically Checking Protocol Security in a Typed Model\<close>
context stateful_protocol_model
begin

definition abs_intruder_knowledge ("\<alpha>\<^sub>i\<^sub>k") where
  "\<alpha>\<^sub>i\<^sub>k S \<I> \<equiv> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<I>)"

definition abs_value_constants ("\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s") where
  "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s S \<I> \<equiv> {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []} \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<I>)"

definition abs_term_implications ("\<alpha>\<^sub>t\<^sub>i") where
  "\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I> \<equiv> {(s,t) | s t x.
    s \<noteq> t \<and> x \<in> fv_transaction T \<and> x \<notin> set (transaction_fresh T) \<and>
    Fun (Abs s) [] = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<and>
    Fun (Abs t) [] = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>)}"

lemma abs_intruder_knowledge_append:
  "\<alpha>\<^sub>i\<^sub>k (A@B) \<I> =
    (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>) \<union>
    (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>)"
by (metis unlabel_append abs_set_union image_Un ik\<^sub>s\<^sub>s\<^sub>t_append abs_intruder_knowledge_def)

lemma abs_value_constants_append:
  fixes A B::"('a,'b,'c,'d) prot_strand"
  shows "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (A@B) \<I> =
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []} \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>) \<union>
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []} \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>)"
proof -
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>s\<^sub>s\<^sub>t (unlabel (A@B)) \<I>)"
  define M where "M \<equiv> \<lambda>a::('a,'b,'c,'d) prot_strand.
                            {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t a) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []}"

  have "M (A@B) = M A \<union> M B"
    using unlabel_append[of A B] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A" "unlabel B"]
          image_Un[of "\<lambda>x. x \<cdot> \<I>" "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"]
    unfolding M_def by force
  hence "M (A@B) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0 = (M A \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0) \<union> (M B \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0)" by (simp add: abs_set_union)
  thus ?thesis unfolding abs_value_constants_def a0_def M_def by blast
qed

lemma transaction_renaming_subst_has_no_pubconsts_abss:
  fixes \<alpha>::"('fun,'atom,'sets) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P A"
  shows "subst_range \<alpha> \<inter> pubval_terms = {}" (is ?A)
    and "subst_range \<alpha> \<inter> abs_terms = {}" (is ?B)
proof -
  { fix t assume "t \<in> subst_range \<alpha>"
    then obtain x where "t = Var x" 
      using transaction_renaming_subst_is_renaming[OF assms]
      by force
    hence "t \<notin> pubval_terms" "t \<notin> abs_terms" by simp_all
  } thus ?A ?B by auto
qed

lemma transaction_fresh_subst_has_no_pubconsts_abss:
  fixes \<sigma>::"('fun,'atom,'sets) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T \<A>"
  shows "subst_range \<sigma> \<inter> pubval_terms = {}" (is ?A)
    and "subst_range \<sigma> \<inter> abs_terms = {}" (is ?B)
proof -
  { fix t assume "t \<in> subst_range \<sigma>"
    then obtain n where "t = Fun (Val (n,False)) []" 
      using assms unfolding transaction_fresh_subst_def
      by force
    hence "t \<notin> pubval_terms" "t \<notin> abs_terms" by simp_all
  } thus ?A ?B by auto
qed

lemma reachable_constraints_no_pubconsts_abss:
  assumes "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. \<forall>n. Val (n,True) \<notin> \<Union>(funs_term ` trms_transaction T)"
           "\<forall>T \<in> set P. \<forall>n. Abs n \<notin> \<Union>(funs_term ` trms_transaction T)"
           "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
           "\<forall>T \<in> set P. bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) = {}"
    and \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
           "\<forall>n. Val (n,True) \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
  shows "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (\<Union>T \<in> set P. trms_transaction T) - (pubval_terms \<union> abs_terms)"
    (is "?A \<subseteq> ?B")
using assms(1) \<I>(4,5)
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<sigma> \<alpha>)
  define trms_P where "trms_P \<equiv> (\<Union>T \<in> set P. trms_transaction T)"
  define T' where "T' \<equiv> transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>"

  have \<I>': "\<forall>n. Val (n,True) \<notin> \<Union> (funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. Abs n \<notin> \<Union> (funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
    using step.prems fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
    by auto

  have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>)"
    using transaction_renaming_subst_wt[OF step.hyps(4)]
          transaction_fresh_subst_wt[OF step.hyps(3)]
    by (metis step.hyps(2) P(3) wt_subst_compose)
  hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>))" for X
    using wt_subst_rm_vars[of "\<sigma> \<circ>\<^sub>s \<alpha>" "set X"]
    by metis
  hence wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t ((rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>)) \<circ>\<^sub>s \<I>)" for X
    using \<I>(2) wt_subst_compose by fast

  have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<sigma> \<circ>\<^sub>s \<alpha>))"
    using transaction_fresh_subst_range_wf_trms[OF step.hyps(3)]
          transaction_renaming_subst_range_wf_trms[OF step.hyps(4)]
    by (metis wf_trms_subst_compose)
  hence wftrms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range ((rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>)) \<circ>\<^sub>s \<I>))" for X
    using wf_trms_subst_compose[OF wf_trms_subst_rm_vars' \<I>(3)] by fast

  have "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> ?B"
  proof
    fix t assume "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    hence "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq by blast
    then obtain s X where s:
        "s \<in> trms_transaction T"
        "t = s \<cdot> rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>"
        "set X \<subseteq> bvars_transaction T"
      using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst'' unfolding T'_def by blast

    define \<theta> where "\<theta> \<equiv> rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>)"

    have 1: "s \<in> trms_P" using step.hyps(2) s(1) unfolding trms_P_def by auto

    have s_nin: "s \<notin> pubval_terms" "s \<notin> abs_terms"
      using 1 P(1,2) funs_term_Fun_subterm
      unfolding trms_P_def is_Val_def is_Abs_def
      by fastforce+

    have 2: "(\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')) \<inter> pubval_terms = {}"
            "(\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')) \<inter> abs_terms = {}"
            "subst_range (\<sigma> \<circ>\<^sub>s \<alpha>) \<inter> pubval_terms = {}"
            "subst_range (\<sigma> \<circ>\<^sub>s \<alpha>) \<inter> abs_terms = {}"
            "subst_range \<theta> \<inter> pubval_terms = {}"
            "subst_range \<theta> \<inter> abs_terms = {}"
            "(\<theta> ` fv s) \<inter> pubval_terms = {}"
            "(\<theta> ` fv s) \<inter> abs_terms = {}"
      unfolding T'_def \<theta>_def
      using step.prems funs_term_Fun_subterm
      apply (fastforce simp add: is_Val_def,
             fastforce simp add: is_Abs_def)
      using pubval_terms_subst_range_comp[OF 
              transaction_fresh_subst_has_no_pubconsts_abss(1)[OF step.hyps(3)]
              transaction_renaming_subst_has_no_pubconsts_abss(1)[OF step.hyps(4)]]
            abs_terms_subst_range_comp[OF 
              transaction_fresh_subst_has_no_pubconsts_abss(2)[OF step.hyps(3)]
              transaction_renaming_subst_has_no_pubconsts_abss(2)[OF step.hyps(4)]]
      unfolding is_Val_def is_Abs_def
      by force+
    
    have "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> pubval_terms = {}"
         "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> abs_terms = {}"
    proof -
      have "\<theta> = \<sigma> \<circ>\<^sub>s \<alpha>" "bvars_transaction T = {}" "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"
        using s(3) P(4) step.hyps(2) rm_vars_empty
              vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel T'"]
              bvars\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel (transaction_strand T)" "\<sigma> \<circ>\<^sub>s \<alpha>"]
              unlabel_subst[of "transaction_strand T" "\<sigma> \<circ>\<^sub>s \<alpha>"]
        unfolding \<theta>_def T'_def by simp_all
      hence "fv (s \<cdot> \<theta>) \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"
        using trms\<^sub>s\<^sub>s\<^sub>t_fv_subst_subset[OF s(1), of \<theta>] unlabel_subst[of "transaction_strand T" \<theta>]
        unfolding T'_def by auto
      moreover have "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
        using fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"]
              unlabel_append[of \<A> "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"]
              fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of T']
        by simp_all
      hence "\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<inter> pubval_terms = {}" "\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<inter> abs_terms = {}"
        using 2(1,2) by blast+
      ultimately show "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> pubval_terms = {}" "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> abs_terms = {}"
        by blast+
    qed
    hence \<sigma>\<alpha>\<I>_disj: "((\<theta> \<circ>\<^sub>s \<I>) ` fv s) \<inter> pubval_terms = {}" 
                    "((\<theta> \<circ>\<^sub>s \<I>) ` fv s) \<inter> abs_terms = {}" 
      using pubval_terms_subst_range_comp'[of \<theta> "fv s" \<I>]
            abs_terms_subst_range_comp'[of \<theta> "fv s" \<I>]
            2(7,8)
      by (simp_all add: subst_apply_fv_unfold)
    
    have 3: "t \<notin> pubval_terms" "t \<notin> abs_terms"
      using s(2) s_nin \<sigma>\<alpha>\<I>_disj
            pubval_terms_subst[of s "rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>"]
            pubval_terms_subst_range_disj[of "rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>" s]
            abs_terms_subst[of s "rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>"]
            abs_terms_subst_range_disj[of "rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>" s]
      unfolding \<theta>_def
      by blast+

    have "t \<in> SMP trms_P" "fv t = {}"
      by (metis s(2) SMP.Substitution[OF SMP.MP[OF 1] wt wftrms, of X], 
          metis s(2) subst_subst_compose[of s "rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>)" \<I>]
                     interpretation_grounds[OF \<I>(1), of "s \<cdot> rm_vars (set X) (\<sigma> \<circ>\<^sub>s \<alpha>)"])
    hence 4: "t \<in> GSMP trms_P" unfolding GSMP_def by simp
    
    show "t \<in> ?B" using 3 4 by (auto simp add: trms_P_def)
  qed
  thus ?case
    using step.IH[OF \<I>'] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
          image_Un[of "\<lambda>x. x \<cdot> \<I>" "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"]
    by (simp add: T'_def)
qed simp

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_aux:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
           "t = Fun (Val n) [] \<or> t = Var x"
    and neq:
      "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<noteq>
       t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>)"
  shows "\<exists>y \<in> fv_transaction T - set (transaction_fresh T).
          t \<cdot> \<I> = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<and> \<Gamma>\<^sub>v y = TAtom Value"
proof -
  let ?\<A>' = "\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"
  let ?\<B> = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
  let ?\<B>' = "?\<B> \<cdot>\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>"
  let ?\<B>'' = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  have T_adm: "admissible_transaction T"
    using T P(1) by blast
  hence T_valid: "wellformed_transaction T"
    unfolding admissible_transaction_def by blast

  have T_adm_upds: "admissible_transaction_updates T"
    by (metis P(1) T admissible_transaction_def)

  have T_fresh_vars_value_typed: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using T P(1) protocol_transaction_vars_TAtom_typed(3)[of T] P(1) by simp

  have wt_\<sigma>\<alpha>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>)"
    using wt_subst_compose transaction_fresh_subst_wt[OF \<sigma> T_fresh_vars_value_typed]
          transaction_renaming_subst_wt[OF \<alpha>]
    by blast

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)
  hence t_wf: "wf\<^sub>t\<^sub>r\<^sub>m t" using t by auto

  have \<A>_no_val_bvars: "\<not>TAtom Value \<sqsubseteq> \<Gamma>\<^sub>v x"
    when "x \<in> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for x
    using P(1) reachable_constraints_no_bvars \<A>_reach
          vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] that
    unfolding admissible_transaction_def by fast

  have x': "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" when "t = Var x"
    using that t by (simp add: var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t)

  have "\<exists>f \<in> funs_term (t \<cdot> \<I>). is_Val f"
    using abs_eq_if_no_Val neq by metis
  hence "\<exists>n T. Fun (Val n) T \<sqsubseteq> t \<cdot> \<I>"
    using funs_term_Fun_subterm
    unfolding is_Val_def by fast
  hence "TAtom Value \<sqsubseteq> \<Gamma> (Var x)" when "t = Var x"
    using wt_subst_trm''[OF \<I>_wt, of "Var x"] that
          subtermeq_imp_subtermtypeeq[of "t \<cdot> \<I>"] wf_trm_subst[OF \<I>_wf, of t] t_wf
    by fastforce
  hence x_val: "\<Gamma>\<^sub>v x = TAtom Value" when "t = Var x"
    using reachable_constraints_vars_TAtom_typed[OF \<A>_reach P x'] that
    by fastforce
  hence x_fv: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" when "t = Var x" using x'
    using reachable_constraints_Value_vars_are_fv[OF \<A>_reach P x'] that
    by blast
  then obtain m where m: "t \<cdot> \<I> = Fun (Val m) []"
    using constraint_model_Value_term_is_Val[
            OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P, of x]
          t(2) x_val
    by force
  hence 0: "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) m \<noteq> \<alpha>\<^sub>0 (db\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>@?\<B>'') \<I>) m"
    using neq by (simp add: unlabel_def)

  have t_val: "\<Gamma> t = TAtom Value" using x_val t by force

  obtain u s where s: "t \<cdot> \<I> = u \<cdot> \<I>" "insert\<langle>u,s\<rangle> \<in> set ?\<B>' \<or> delete\<langle>u,s\<rangle> \<in> set ?\<B>'"
    using to_abs_neq_imp_db_update[OF 0] m
    by (metis (no_types, lifting) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst subst_lsst_unlabel)
  then obtain u' s' where s':
      "u = u' \<cdot> \<sigma> \<circ>\<^sub>s \<alpha>" "s = s' \<cdot> \<sigma> \<circ>\<^sub>s \<alpha>"
      "insert\<langle>u',s'\<rangle> \<in> set ?\<B> \<or> delete\<langle>u',s'\<rangle> \<in> set ?\<B>"
    using stateful_strand_step_subst_inv_cases(4,5)
    by blast
  hence s'': "insert\<langle>u',s'\<rangle> \<in> set (unlabel (transaction_strand T)) \<or>
              delete\<langle>u',s'\<rangle> \<in> set (unlabel (transaction_strand T))"
    using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(4,5)[of u' s' "transaction_strand T"]
    by simp_all
  then obtain y where y: "y \<in> fv_transaction T" "u' = Var y"
    using transaction_inserts_are_Value_vars[OF T_valid T_adm_upds, of u' s']
          transaction_deletes_are_Value_vars[OF T_valid T_adm_upds, of u' s']
          stateful_strand_step_fv_subset_cases(4,5)[of u' s' "unlabel (transaction_strand T)"]
    by auto
  hence 1: "t \<cdot> \<I> = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" using y s(1) s'(1) by (metis subst_apply_term.simps(1)) 

  have 2: "y \<notin> set (transaction_fresh T)" when "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<noteq> \<sigma> y"
    using transaction_fresh_subst_grounds_domain[OF \<sigma>, of y] subst_compose[of \<sigma> \<alpha> y] that
    by (auto simp add: subst_ground_ident)

  have 3: "y \<notin> set (transaction_fresh T)" when "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    using 2 that \<sigma> unfolding transaction_fresh_subst_def by fastforce

  have 4: "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<exists>B. prefix B \<A> \<and> x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B))"
    by (metis welltyped_constraint_model_prefix[OF \<I>]
              constraint_model_Value_var_in_constr_prefix[OF \<A>_reach _ P])

  have 5: "\<Gamma>\<^sub>v y = TAtom Value"
    using 1 t_val
          wt_subst_trm''[OF wt_\<sigma>\<alpha>, of "Var y"]
          wt_subst_trm''[OF \<I>_wt, of t]
          wt_subst_trm''[OF \<I>_wt, of "(\<sigma> \<circ>\<^sub>s \<alpha>) y"]
    by (auto simp del: subst_subst_compose)

  have "y \<notin> set (transaction_fresh T)"
  proof (cases "t = Var x")
    case True (* \<I> x occurs in \<A> but not in subst_range \<sigma>, so y cannot be fresh *)
    hence *: "\<I> x = Fun (Val m) []" "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" "\<I> x = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>"
      using m t(1) 1 x_fv x' by (force, blast, force)

    obtain B where B: "prefix B \<A>" "\<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      using *(2) 4 x_val[OF True] by fastforce
    hence "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      using transaction_fresh_subst_range_fresh(1)[OF \<sigma>] trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)[of B]
      unfolding prefix_def by fast
    thus ?thesis using *(1,3) B(2) 2 by (metis subst_imgI term.distinct(1))
  next
    case False
    hence "t \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t by simp
    thus ?thesis using 1 3 by argo
  qed
  thus ?thesis using 1 5 y(1) by fast
qed

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Var:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "\<I> x \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>) \<in>
            timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)} (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)"
proof -
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>)"
  define a3 where "a3 \<equiv> \<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>"

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have T_adm: "admissible_transaction T" by (metis P(1) T)

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  have "\<Gamma>\<^sub>v x = Var Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = Var (prot_atom.Atom a))"
    using reachable_constraints_vars_TAtom_typed[OF \<A>_reach P, of x]
          x vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"]
    by auto

  hence "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> a0} a3"
  proof
    assume x_val: "\<Gamma>\<^sub>v x = TAtom Value"
    show "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> a0} a3"
    proof (cases "\<I> x \<cdot>\<^sub>\<alpha> a0 = \<I> x \<cdot>\<^sub>\<alpha> a0'")
      case False
      hence "\<exists>y \<in> fv_transaction T - set (transaction_fresh T).
              \<I> x = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<and> \<Gamma>\<^sub>v y = TAtom Value"
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_aux[OF \<A>_reach T \<I> \<sigma> \<alpha> P fv\<^sub>s\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t[OF x], of _ x]
        unfolding a0_def a0'_def
        by fastforce
      then obtain y where y:
          "y \<in> fv_transaction T - set (transaction_fresh T)"
          "\<I> x = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>"
          "\<I> x \<cdot>\<^sub>\<alpha> a0 = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"
          "\<I> x \<cdot>\<^sub>\<alpha> a0' = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'"
          "\<Gamma>\<^sub>v y = TAtom Value"
        by metis
      then obtain n where n: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val (n,False)) []"
        using \<Gamma>\<^sub>v_TAtom''(2)[of y] x x_val
              transaction_var_becomes_Val[
                OF reachable_constraints.step[OF \<A>_reach T \<sigma> \<alpha>] \<I> \<sigma> \<alpha> P T, of y]
        by force

      have "a0 (n,False) \<noteq> a0' (n,False)"
           "y \<in> fv_transaction T"
           "y \<notin> set (transaction_fresh T)"
           "absc (a0 (n,False)) = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"
           "absc (a0' (n,False)) = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'"
        using y n False by force+
      hence 1: "(a0 (n,False), a0' (n,False)) \<in> a3" 
        unfolding a0_def a0'_def a3_def abs_term_implications_def
        by blast
      
      have 2: "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> set \<langle>a0 (n,False) --\<guillemotright> a0' (n,False)\<rangle>\<langle>\<I> x \<cdot>\<^sub>\<alpha> a0\<rangle>"
        using y n timpl_apply_const by auto

      show ?thesis
        using timpl_closure.TI[OF timpl_closure.FP 1] 2
              term_variants_pred_iff_in_term_variants[
                of "(\<lambda>_. [])(Abs (a0 (n, False)) := [Abs (a0' (n, False))])"]
        unfolding timpl_closure_set_def timpl_apply_term_def
        by auto
    qed (auto intro: timpl_closure_setI)
  next
    assume "\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)"
    then obtain a where x_atom: "\<Gamma>\<^sub>v x = TAtom (Atom a)" by moura

    obtain f T where fT: "\<I> x = Fun f T"
      using interpretation_grounds[OF \<I>_interp, of "Var x"]
      by (cases "\<I> x") auto

    have fT_atom: "\<Gamma> (Fun f T) = TAtom (Atom a)"
      using wt_subst_trm''[OF \<I>_wt, of "Var x"] x_atom fT
      by simp

    have T: "T = []"
      using fT wf_trm_subst[OF \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s, of "Var x"] const_type_inv_wf[OF fT_atom]
      by fastforce

    have f: "\<not>is_Val f" using fT_atom unfolding is_Val_def by auto

    have "\<I> x \<cdot>\<^sub>\<alpha> b = \<I> x" for b
      using T fT abs_term_apply_const(2)[OF f]
      by auto
    thus "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> a0} a3"
      by (auto intro: timpl_closure_setI)
  qed
  thus ?thesis by (metis a0_def a0'_def a3_def)
qed

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Val:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and n: "Fun (Val n) [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "Fun (Val n) [] \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>) \<in>
            timpl_closure_set {Fun (Val n) [] \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)} (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)"
proof -
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"
  define a3 where "a3 \<equiv> \<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>"

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have T_adm: "admissible_transaction T" by (metis P(1) T)

  have "Fun (Abs (a0' n)) [] \<in> timpl_closure_set {Fun (Abs (a0 n)) []} a3"
  proof (cases "a0 n = a0' n")
    case False
    then obtain x where x:
        "x \<in> fv_transaction T - set (transaction_fresh T)" "Fun (Val n) [] = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I>"
      using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_aux[OF \<A>_reach T \<I> \<sigma> \<alpha> P n]
      by (fastforce simp add: a0_def a0'_def T'_def)
    hence "absc (a0 n) = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0" "absc (a0' n) = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'" by simp_all
    hence 1: "(a0 n, a0' n) \<in> a3"
      using False x(1)
      unfolding a0_def a0'_def a3_def abs_term_implications_def T'_def
      by blast
    show ?thesis
      using timpl_apply_Abs[of "[]" "[]" "a0 n" "a0' n"]
            timpl_closure.TI[OF timpl_closure.FP[of "Fun (Abs (a0 n)) []" a3] 1]
            term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs (a0 n) := [Abs (a0' n)])"]
      unfolding timpl_closure_set_def timpl_apply_term_def
      by force
  qed (auto intro: timpl_closure_setI)
  thus ?thesis by (simp add: a0_def a0'_def a3_def T'_def)
qed

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_ik:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and t: "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>) \<in>
            timpl_closure_set {t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)} (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)"
proof -
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>)"
  define a3 where "a3 \<equiv> \<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>"

  let ?U = "\<lambda>T a. map (\<lambda>s. s \<cdot> \<I> \<cdot>\<^sub>\<alpha> a) T"

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have T_adm: "admissible_transaction T" by (metis P(1) T)

  have "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" "wf\<^sub>t\<^sub>r\<^sub>m t" using \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s t ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset by force+
  hence "\<forall>t0 \<in> subterms t. t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} a3"
  proof (induction t)
    case (Var x) thus ?case
      using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Var[OF \<A>_reach T \<I> \<sigma> \<alpha> P, of x]
            ik\<^sub>s\<^sub>s\<^sub>t_var_is_fv[of x "unlabel \<A>"] vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"]
      by (simp add: a0_def a0'_def a3_def)
  next
    case (Fun f S)
    have IH: "\<forall>t0 \<in> subterms t. t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} a3"
      when "t \<in> set S" for t
      using that Fun.prems(1) wf_trm_param[OF Fun.prems(2)] Fun.IH
      by (meson in_subterms_subset_Union params_subterms subsetCE)
    hence "t \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t \<cdot>\<^sub>\<alpha> a0} a3"
      when "t \<in> set (map (\<lambda>s. s \<cdot> \<I>) S)" for t
      using that by auto
    hence "t \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure (t \<cdot>\<^sub>\<alpha> a0) a3"
      when "t \<in> set (map (\<lambda>s. s \<cdot> \<I>) S)" for t
      using that timpl_closureton_is_timpl_closure by auto
    hence "(t \<cdot>\<^sub>\<alpha> a0, t \<cdot>\<^sub>\<alpha> a0') \<in> timpl_closure' a3"
      when "t \<in> set (map (\<lambda>s. s \<cdot> \<I>) S)" for t
      using that timpl_closure_is_timpl_closure' by auto
    hence IH': "((?U S a0) ! i, (?U S a0') ! i) \<in> timpl_closure' a3"
      when "i < length (map (\<lambda>s. s \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0) S)" for i
      using that by auto

    show ?case
    proof (cases "\<exists>n. f = Val n")
      case True
      then obtain n where "Fun f S = Fun (Val n) []"
        using Fun.prems(2) unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by force
      moreover have "Fun f S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
        using ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset Fun.prems(1) by blast
      ultimately show ?thesis
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Val[OF \<A>_reach T \<I> \<sigma> \<alpha> P]
        by (simp add: a0_def a0'_def a3_def)
    next
      case False
      hence "Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a = Fun f (map (\<lambda>t. t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a) S)" for a by (cases f) simp_all
      hence "(Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0, Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0') \<in> timpl_closure' a3"
        using timpl_closure_FunI[OF IH']
        by simp
      hence "Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} a3"
        using timpl_closureton_is_timpl_closure
              timpl_closure_is_timpl_closure'
        by metis
      thus ?thesis using IH by simp
    qed
  qed
  thus ?thesis by (simp add: a0_def a0'_def a3_def)
qed

lemma transaction_prop1:
  assumes "\<delta> \<in> abs_substs_fun ` set (transaction_check_comp FP OCC TI T)"
    and "x \<in> fv_transaction T"
    and "x \<notin> set (transaction_fresh T)"
    and "\<delta> x \<noteq> absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"
    and "transaction_check FP OCC TI T"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "(\<delta> x, absdbupd (unlabel (transaction_updates T)) x (\<delta> x)) \<in> (set TI)\<^sup>+"
proof -
  let ?upd = "\<lambda>x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"

  have 0: "fv_transaction T = set (fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T)))"
    by (metis fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]) 

  have 1: "transaction_check_post FP TI T \<delta>"
    using assms(1,5)
    unfolding transaction_check_def list_all_iff
    by blast

  have "(\<delta> x, ?upd x) \<in> set TI \<longleftrightarrow> (\<delta> x, ?upd x) \<in> (set TI)\<^sup>+"
    using TI using assms(4) by blast
  thus ?thesis
    using assms(2,3,4) 0 1 in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
    unfolding transaction_check_post_def List.member_def
    by (metis (no_types, lifting) DiffI) 
qed

lemma transaction_prop2:
  assumes \<delta>: "\<delta> \<in> abs_substs_fun ` set (transaction_check_comp FP OCC TI T)"
    and x: "x \<in> fv_transaction T" "fst x = TAtom Value"
    and T_check: "transaction_check FP OCC TI T"
    and T_adm: "admissible_transaction T"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "x \<notin> set (transaction_fresh T) \<Longrightarrow> \<delta> x \<in> set OCC" (is "?A' \<Longrightarrow> ?A")
    and "absdbupd (unlabel (transaction_updates T)) x (\<delta> x) \<in> set OCC" (is ?B)
proof -
  let ?xs = "fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T))"
  let ?ys = "filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) ?xs"
  let ?C = "unlabel (transaction_selects T@transaction_checks T)"
  let ?poss = "transaction_poschecks_comp ?C"
  let ?negs = "transaction_negchecks_comp ?C"
  let ?\<delta>upd = "\<lambda>y. absdbupd (unlabel (transaction_updates T)) y (\<delta> y)"

  have T_wf: "wellformed_transaction T"
    and T_occ: "admissible_transaction_occurs_checks T"
    using T_adm by (metis admissible_transaction_def)+

  have 0: "{x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value} = set ?ys"
    using fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
    by force

  have 1: "transaction_check_pre FP TI T \<delta>"
    using \<delta> unfolding transaction_check_comp_def Let_def by fastforce

  have 2: "transaction_check_post FP TI T \<delta>"
    using \<delta> T_check unfolding transaction_check_def list_all_iff by blast

  have 3: "\<delta> \<in> abs_substs_fun ` set (abs_substs_set ?ys OCC ?poss ?negs)"
    using \<delta> unfolding transaction_check_comp_def Let_def by force

  show A: ?A when ?A' using that 0 3 x abs_substs_abss_bounded by blast

  have 4: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
    when x': "x \<in> set (transaction_fresh T)"
    using T_wf x' unfolding wellformed_transaction_def by fast

  have "intruder_synth_mod_timpls FP TI (occurs (absc (?\<delta>upd x)))"
    when x': "x \<in> set (transaction_fresh T)"
    using 2 x' x T_occ
    unfolding transaction_check_post_def admissible_transaction_occurs_checks_def
    by fastforce
  hence "timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c occurs (absc (?\<delta>upd x))"
    when x': "x \<in> set (transaction_fresh T)"
    using x' intruder_synth_mod_timpls_is_synth_timpl_closure_set[
            OF TI, of FP "occurs (absc (?\<delta>upd x))"]
    by argo
  hence "Abs (?\<delta>upd x) \<in> \<Union>(funs_term ` timpl_closure_set (set FP) (set TI))"
    when x': "x \<in> set (transaction_fresh T)"
    using x' ideduct_synth_priv_fun_in_ik[
            of "timpl_closure_set (set FP) (set TI)" "occurs (absc (?\<delta>upd x))"]
    by simp
  hence "\<exists>t \<in> timpl_closure_set (set FP) (set TI). Abs (?\<delta>upd x) \<in> funs_term t"
    when x': "x \<in> set (transaction_fresh T)"
    using x' by force
  hence 5: "?\<delta>upd x \<in> set OCC" when x': "x \<in> set (transaction_fresh T)"
    using x' OCC by fastforce

  have 6: "?\<delta>upd x \<in> set OCC" when x': "x \<notin> set (transaction_fresh T)"
  proof (cases "\<delta> x = ?\<delta>upd x")
    case False
    hence "(\<delta> x, ?\<delta>upd x) \<in> (set TI)\<^sup>+" "\<delta> x \<in> set OCC"
      using A 2 x' x TI
      unfolding transaction_check_post_def fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t Let_def
                in_trancl_closure_iff_in_trancl_fun[symmetric]
                List.member_def
      by blast+
    thus ?thesis using timpl_closure_set_absc_subset_in[OF OCC(2)] by blast
  qed (simp add: A x' x(1))

  show ?B by (metis 5 6)
qed

lemma transaction_prop3:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
  shows "\<forall>x \<in> set (transaction_fresh T). (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc {}" (is ?A)
    and "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T).
            intruder_synth_mod_timpls FP TI (t \<cdot> (\<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))" (is ?B)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
         \<forall>s. select\<langle>Var x,Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_selects T))
                 \<longrightarrow> (\<exists>ss. (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss)" (is ?C)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
         \<forall>s. \<langle>Var x in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
                 \<longrightarrow> (\<exists>ss. (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss)" (is ?D)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
         \<forall>s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
                 \<longrightarrow> (\<exists>ss. (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<notin> ss)" (is ?E)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
         (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<in> absc ` set OCC" (is ?F)
proof -
  let ?T' = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"

  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@?T') \<I>)"
  define fv_AT' where "fv_AT' \<equiv> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@?T')"

  have T_adm: "admissible_transaction T"
    using T P(1) by blast
  hence T_valid: "wellformed_transaction T"
    unfolding admissible_transaction_def by blast

  have T_adm':
      "admissible_transaction_selects T"
      "admissible_transaction_checks T"
      "admissible_transaction_updates T"
    using T_adm unfolding admissible_transaction_def by simp_all

  have \<I>': "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
           "\<forall>n. Val (n,True) \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. Val (n,True) \<notin> \<Union>(funs_term ` (\<I> ` fv_AT'))"
           "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<I> ` fv_AT'))"
    using \<I> admissible_transaction_occurs_checks_prop'[
            OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P]
          admissible_transaction_occurs_checks_prop'[
            OF reachable_constraints.step[OF \<A>_reach T \<sigma> \<alpha>] \<I> P]
    unfolding welltyped_constraint_model_def constraint_model_def is_Val_def is_Abs_def fv_AT'_def
    by fastforce+

  have \<P>': "\<forall>T \<in> set P. \<forall>n. Val (n,True) \<notin> \<Union>(funs_term ` trms_transaction T)"
           "\<forall>T \<in> set P. \<forall>n. Abs n \<notin> \<Union>(funs_term ` trms_transaction T)"
           "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    and "\<forall>T \<in> set P. \<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    using protocol_transaction_vars_TAtom_typed
          protocol_transactions_no_pubconsts
          protocol_transactions_no_abss
          funs_term_Fun_subterm P
    by fast+
  hence T_no_pubconsts: "\<forall>n. Val (n,True) \<notin> \<Union>(funs_term ` trms_transaction T)"
    and T_no_abss: "\<forall>n. Abs n \<notin> \<Union>(funs_term ` trms_transaction T)"
    and T_fresh_vars_value_typed: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    and T_fv_const_typed: "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    using T by simp_all

  have wt_\<sigma>\<alpha>\<I>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)"
      using \<I>'(2) wt_subst_compose transaction_fresh_subst_wt[OF \<sigma> T_fresh_vars_value_typed]
            transaction_renaming_subst_wt[OF \<alpha>]
      by blast

  have 1: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = \<sigma> y" when "y \<in> set (transaction_fresh T)" for y
    using transaction_fresh_subst_grounds_domain[OF \<sigma> that] subst_compose[of \<sigma> \<alpha> y]
    by (simp add: subst_ground_ident)

  have 2: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" when "y \<in> set (transaction_fresh T)" for y
    using 1[OF that] that \<sigma> unfolding transaction_fresh_subst_def by auto

  have 3: "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<exists>B. prefix B \<A> \<and> x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B))"
    by (metis welltyped_constraint_model_prefix[OF \<I>]
              constraint_model_Value_var_in_constr_prefix[OF \<A>_reach _ P])

  have 4: "\<exists>n. (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val n) []"
    when "y \<in> fv_transaction T" "\<Gamma>\<^sub>v y = TAtom Value" for y
    using transaction_var_becomes_Val[OF reachable_constraints.step[OF \<A>_reach T \<sigma> \<alpha>] \<I> \<sigma> \<alpha> P T]
          that T_fv_const_typed \<Gamma>\<^sub>v_TAtom''[of y]
    by metis

  have \<I>_is_T_model: "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) (set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)) (unlabel ?T') \<I>"
    using \<I> unlabel_append[of \<A> ?T'] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>" \<I> "[]"]
          strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "unlabel ?T'" \<I>]
    by (simp add: welltyped_constraint_model_def constraint_model_def db\<^sub>s\<^sub>s\<^sub>t_def)

  have T_rcv_no_val_bvars: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<inter> subst_domain (\<sigma> \<circ>\<^sub>s \<alpha>) = {}"
    using transaction_no_bvars[OF T_adm] bvars_transaction_unfold[of T] by blast

  show ?A
  proof
    fix y assume y: "y \<in> set (transaction_fresh T)"
    then obtain yn where yn: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val yn) []" "Fun (Val yn) [] \<in> subst_range \<sigma>"
      by (metis transaction_fresh_subst_sends_to_val'[OF \<sigma>])

    { \<comment> \<open>since \<open>y\<close> is fresh \<open>(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>\<close> cannot be part of the database state of \<open>\<I> \<A>\<close>\<close>
      fix t' s assume t': "insert\<langle>t',s\<rangle> \<in> set (unlabel \<A>)" "t' \<cdot> \<I> = Fun (Val yn) []"
      then obtain z where t'_z: "t' = Var z" using 2[OF y] yn(1) by (cases t') auto
      hence z: "z \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" "\<I> z = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" using t' yn(1) by force+
      hence z': "\<Gamma>\<^sub>v z = TAtom Value"
        by (metis \<Gamma>.simps(1) \<Gamma>_consts_simps(2) t'(2) t'_z wt_subst_trm'' \<I>'(2))

      obtain B where B: "prefix B \<A>" "\<I> z \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)" using z z' 3 by fastforce
      hence "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
        using transaction_fresh_subst_range_fresh(1)[OF \<sigma>] trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)[of B]
        unfolding prefix_def by fast
      hence False using B(2) 1[OF y] z yn(1) by (metis subst_imgI term.distinct(1)) 
    } hence "\<nexists>s. ((\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using db\<^sub>s\<^sub>s\<^sub>t_in_cases[of "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" _ "unlabel \<A>" \<I> "[]"] yn(1)
      by (force simp add: db\<^sub>s\<^sub>s\<^sub>t_def)
    thus "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc {}"
      using to_abs_empty_iff_notin_db[of yn "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I> []"] yn(1)
      by (simp add: db\<^sub>s\<^sub>s\<^sub>t_def)
  qed

  show receives_covered: ?B
  proof
    fix t assume t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
    hence t_in_T: "t \<in> trms_transaction T"
      using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)[of "transaction_receive T"]
      unfolding transaction_strand_def by fast

    have t_rcv: "receive\<langle>t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha>\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
      using subst_lsst_unlabel_member[of "receive\<langle>t\<rangle>" "transaction_receive T" "\<sigma> \<circ>\<^sub>s \<alpha>"]
            wellformed_transaction_unlabel_cases(1)[OF T_valid] trms\<^sub>s\<^sub>s\<^sub>t_in[OF t]
      by fastforce
    hence *: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I>"
      using wellformed_transaction_sem_receives[OF T_valid \<I>_is_T_model]
      by simp

    have t_fv: "fv (t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha>) \<subseteq> fv_AT'"
      using fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
            fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>"]
            t_rcv fv_transaction_subst_unfold[of T " \<sigma> \<circ>\<^sub>s \<alpha>"]
      unfolding fv_AT'_def by force

    have **: "\<forall>t \<in> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
      using FP(3) by (auto simp add: a0_def abs_intruder_knowledge_def)

    note lms1 = pubval_terms_subst[OF _ pubval_terms_subst_range_disj[
                  OF transaction_fresh_subst_has_no_pubconsts_abss(1)[OF \<sigma>], of t]]
                pubval_terms_subst[OF _ pubval_terms_subst_range_disj[
                  OF transaction_renaming_subst_has_no_pubconsts_abss(1)[OF \<alpha>], of "t \<cdot> \<sigma>"]]

    note lms2 = abs_terms_subst[OF _ abs_terms_subst_range_disj[
                  OF transaction_fresh_subst_has_no_pubconsts_abss(2)[OF \<sigma>], of t]]
                abs_terms_subst[OF _ abs_terms_subst_range_disj[
                  OF transaction_renaming_subst_has_no_pubconsts_abss(2)[OF \<alpha>], of "t \<cdot> \<sigma>"]]

    have "t \<in> (\<Union>T\<in>set P. trms_transaction T)" "fv (t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I>) = {}"
      using t_in_T T interpretation_grounds[OF \<I>'(1)] by fast+
    moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>))"
      using wf_trm_subst_rangeI[of \<sigma>, OF transaction_fresh_subst_is_wf_trm[OF \<sigma>]]
            wf_trm_subst_rangeI[of \<alpha>, OF transaction_renaming_subst_is_wf_trm[OF \<alpha>]]
            wf_trms_subst_compose[of \<sigma> \<alpha>, THEN wf_trms_subst_compose[OF _ \<I>'(3)]]
      by blast
    moreover
    have "t \<notin> pubval_terms"
      using t_in_T T_no_pubconsts funs_term_Fun_subterm
      unfolding is_Val_def by fastforce
    hence "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<notin> pubval_terms"
      using lms1
      by auto
    hence "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<notin> pubval_terms"
      using \<I>'(6) t_fv pubval_terms_subst'[of "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha>" \<I>]
      by auto
    moreover have "t \<notin> abs_terms"
      using t_in_T T_no_abss funs_term_Fun_subterm
      unfolding is_Abs_def by force
    hence "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<notin> abs_terms"
      using lms2
      by auto
    hence "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<notin> abs_terms"
      using \<I>'(7) t_fv abs_terms_subst'[of "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha>" \<I>]
      by auto
    ultimately have ***:
        "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<in> GSMP (\<Union>T\<in>set P. trms_transaction T) - (pubval_terms \<union> abs_terms)"
      using SMP.Substitution[OF SMP.MP[of t "\<Union>T\<in>set P. trms_transaction T"], of "\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>"]
            subst_subst_compose[of t "\<sigma> \<circ>\<^sub>s \<alpha>" \<I>] wt_\<sigma>\<alpha>\<I>
      unfolding GSMP_def by fastforce

    have "\<forall>T\<in>set P. bvars_transaction T = {}"
      using transaction_no_bvars P unfolding list_all_iff by blast
    hence ****:
        "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (\<Union>T\<in>set P. trms_transaction T) - (pubval_terms \<union> abs_terms)"
      using reachable_constraints_no_pubconsts_abss[OF \<A>_reach \<P>' _ \<I>'(1,2,3,4,5)]
            ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel \<A>"]
      by blast

    show "intruder_synth_mod_timpls FP TI (t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))"
      using deduct_FP_if_deduct[OF **** ** * ***] deducts_eq_if_analyzed[OF FP(1)]
            intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI, of FP]
      unfolding a0_def by force
  qed

  show ?C
  proof (intro ballI allI impI)
    fix y s
    assume y: "y \<in> fv_transaction T - set (transaction_fresh T)"
       and s: "select\<langle>Var y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_selects T))"
    hence "select\<langle>Var y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_strand T))"
      unfolding transaction_strand_def unlabel_def by auto
    hence y_val: "\<Gamma>\<^sub>v y = TAtom Value"
      using transaction_selects_are_Value_vars[OF T_valid T_adm'(1)]
      by fastforce

    have "select\<langle>(\<sigma> \<circ>\<^sub>s \<alpha>) y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_selects T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>)))"
      using subst_lsst_unlabel_member[OF s]
      by fastforce
    hence "((\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using wellformed_transaction_sem_selects[
              OF T_valid \<I>_is_T_model,
              of "(\<sigma> \<circ>\<^sub>s \<alpha>) y" "Fun (Set s) []"]
      by simp
    thus "\<exists>ss. (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss"
      using to_abs_alt_def[of "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>"] 4[of y] y y_val by auto
  qed

  show ?D
  proof (intro ballI allI impI)
    fix y s
    assume y: "y \<in> fv_transaction T - set (transaction_fresh T)"
       and s: "\<langle>Var y in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))"
    hence "\<langle>Var y in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_strand T))"
      unfolding transaction_strand_def unlabel_def by auto
    hence y_val: "\<Gamma>\<^sub>v y = TAtom Value"
      using transaction_inset_checks_are_Value_vars[OF T_valid T_adm'(2)]
      by fastforce

    have "\<langle>(\<sigma> \<circ>\<^sub>s \<alpha>) y in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>)))"
      using subst_lsst_unlabel_member[OF s]
      by fastforce
    hence "((\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using wellformed_transaction_sem_pos_checks[
              OF T_valid \<I>_is_T_model,
              of "(\<sigma> \<circ>\<^sub>s \<alpha>) y" "Fun (Set s) []"]
      by simp
    thus "\<exists>ss. (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss"
      using to_abs_alt_def[of "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>"] 4[of y] y y_val by auto
  qed

  show ?E
  proof (intro ballI allI impI)
    fix y s
    assume y: "y \<in> fv_transaction T - set (transaction_fresh T)"
       and s: "\<langle>Var y not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))"
    hence "\<langle>Var y not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_strand T))"
      unfolding transaction_strand_def unlabel_def by auto
    hence y_val: "\<Gamma>\<^sub>v y = TAtom Value"
      using transaction_notinset_checks_are_Value_vars[OF T_valid T_adm'(2)]
      by fastforce

    have "\<langle>(\<sigma> \<circ>\<^sub>s \<alpha>) y not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>)))"
      using subst_lsst_unlabel_member[OF s]
      by fastforce
    hence "((\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>, Fun (Set s) []) \<notin> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using wellformed_transaction_sem_neg_checks(2)[
              OF T_valid \<I>_is_T_model,
              of "[]" "(\<sigma> \<circ>\<^sub>s \<alpha>) y" "Fun (Set s) []"]
      by simp
    moreover have "list_all admissible_transaction_updates P"
      using Ball_set[of P "admissible_transaction"] P(1)
            Ball_set[of P admissible_transaction_updates]
      unfolding admissible_transaction_def
      by fast
    moreover have "list_all wellformed_transaction P"
      using P(1) Ball_set[of P "admissible_transaction"] Ball_set[of P wellformed_transaction]
      unfolding admissible_transaction_def
      by blast
    ultimately have "((\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>, Fun (Set s) S) \<notin> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" for S
      using reachable_constraints_db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_args_empty[OF \<A>_reach] 
      unfolding admissible_transaction_updates_def
      by auto
    thus "\<exists>ss. (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<notin> ss"
      using to_abs_alt_def[of "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>"] 4[of y] y y_val by auto
  qed

  show ?F
  proof (intro ballI impI)
    fix y assume y: "y \<in> fv_transaction T - set (transaction_fresh T)" "\<Gamma>\<^sub>v y = TAtom Value"
    then obtain yn where yn: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val yn) []" using 4 by moura
    hence y_abs: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = Fun (Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn)) []" by simp

    have *: "\<forall>r \<in> set (unlabel (transaction_selects T)). \<exists>x s. r = select\<langle>Var x, Fun (Set s) []\<rangle>"
      using admissible_transaction_strand_step_cases(2)[OF T_adm] by fast

    have "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or> y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_selects T)"
      using wellformed_transaction_fv_in_receives_or_selects[OF T_valid] y by blast
    thus "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<in> absc ` set OCC"
    proof
      assume "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
      then obtain t where t: "receive\<langle>t\<rangle> \<in> set (unlabel (transaction_receive T))" "y \<in> fv t"
        using wellformed_transaction_unlabel_cases(1)[OF T_valid]
        by (force simp add: unlabel_def)
      
      have **: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<in> subterms (t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)"
               "timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
        using fv_subterms_substI[OF t(2), of "\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>"] subst_compose[of "\<sigma> \<circ>\<^sub>s \<alpha>" \<I> y]
              subterms_subst_subset[of "\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>" t] receives_covered t(1)
        unfolding intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI, symmetric]
        by auto

      have "Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn) \<in> \<Union>(funs_term ` (timpl_closure_set (set FP) (set TI)))"
        using y_abs abs_subterms_in[OF **(1), of "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"]
              ideduct_synth_priv_fun_in_ik[
                OF **(2) funs_term_Fun_subterm'[of "Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn)" "[]"]]
        by force
      hence "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<in> subterms\<^sub>s\<^sub>e\<^sub>t (timpl_closure_set (set FP) (set TI))"
        using y_abs wf_trms_subterms[OF timpl_closure_set_wf_trms[OF FP(2), of "set TI"]]
              funs_term_Fun_subterm[of "Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn)"]
        unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by fastforce
      hence "funs_term ((\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))
              \<subseteq> (\<Union>t \<in> timpl_closure_set (set FP) (set TI). funs_term t)"
        using funs_term_subterms_eq(2)[of "timpl_closure_set (set FP) (set TI)"] by blast
      thus ?thesis using y_abs OCC(1) by fastforce
    next
      assume "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_selects T)"
      then obtain l s where "(l,select\<langle>Var y, Fun (Set s) []\<rangle>) \<in> set (transaction_selects T)"
        using * by (auto simp add: unlabel_def)
      then obtain U where U:
          "prefix (U@[(l,select\<langle>Var y, Fun (Set s) []\<rangle>)]) (transaction_selects T)"
        using in_set_conv_decomp[of "(l, select\<langle>Var y,Fun (Set s) []\<rangle>)" "transaction_selects T"]
        by (auto simp add: prefix_def)
      hence "select\<langle>Var y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_selects T))"
        by (force simp add: prefix_def unlabel_def)
      hence "select\<langle>(\<sigma> \<circ>\<^sub>s \<alpha>) y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_selects T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
        using subst_lsst_unlabel_member
        by fastforce
      hence "(Fun (Val yn) [], Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
        using yn wellformed_transaction_sem_selects[
                OF T_valid \<I>_is_T_model, of "(\<sigma> \<circ>\<^sub>s \<alpha>) y" "Fun (Set s) []"]
        by fastforce
      hence "Fun (Val yn) [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
        using db\<^sub>s\<^sub>s\<^sub>t_in_cases[of "Fun (Val yn) []"]
        by (fastforce simp add: db\<^sub>s\<^sub>s\<^sub>t_def)
      thus ?thesis
        using OCC(3) yn abs_in[of "Fun (Val yn) []" _ "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"]
        unfolding abs_value_constants_def
        by (metis (mono_tags, lifting) mem_Collect_eq subsetCE) 
    qed
  qed
qed

lemma transaction_prop4:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and x: "x \<in> set (transaction_fresh T)"
    and y: "y \<in> fv_transaction T - set (transaction_fresh T)" "\<Gamma>\<^sub>v y = TAtom Value"
  shows "(\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))" (is ?A)
    and "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))" (is ?B)
proof -
  let ?T' = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"

  from \<I> have \<I>': "welltyped_constraint_model \<I> \<A>"
    using welltyped_constraint_model_prefix by auto

  have T_P_addm: "admissible_transaction T'" when T': "T' \<in> set P " for T'
    by (meson T' P)

  have T_adm: "admissible_transaction T"
    by (metis (full_types) P T)

  from T_adm have T_valid: "wellformed_transaction T"
    unfolding admissible_transaction_def by blast

  have be: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    using T_P_addm \<A>_reach reachable_constraints_no_bvars transaction_no_bvars(2) by blast

  have T_no_bvars: "fv_transaction T = vars_transaction T"
    using transaction_no_bvars[OF T_adm] by simp

  have \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" by (metis \<I> welltyped_constraint_model_def)

  obtain xn where xn: "\<sigma> x = Fun (Val xn) []"
    using \<sigma> x unfolding transaction_fresh_subst_def by force

  then have xnxn: "(\<sigma> \<circ>\<^sub>s \<alpha>) x = Fun (Val xn) []"
    unfolding subst_compose_def by auto

  from xn xnxn have a0: "(\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = Fun (Val xn) []"
    by auto

  have b0: "\<Gamma>\<^sub>v x = TAtom Value"
    using P x T protocol_transaction_vars_TAtom_typed(3)
    by metis

  note 0 = a0 b0

  have xT: "x \<in> fv_transaction T"
    using x transaction_fresh_vars_subset[OF T_valid]
    by fast

  have \<sigma>_x_nin_A: "\<sigma> x \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  proof -
    have "\<sigma> x \<in> subst_range \<sigma>"
      by (metis \<sigma> transaction_fresh_subst_sends_to_val x)
    moreover
    have "(\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
      using \<sigma> transaction_fresh_subst_def[of \<sigma> T \<A>] by auto
    ultimately
    show ?thesis
      by auto
  qed

  have *: "y \<notin> set (transaction_fresh T)"
     using assms by auto

  have **: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or> y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_selects T)"
    using * y wellformed_transaction_fv_in_receives_or_selects[OF T_valid]
    by blast

  have y_fv: "y \<in> fv_transaction T" using y fv_transaction_unfold by blast
  
  have y_val: "fst y = TAtom Value" using y(2) \<Gamma>\<^sub>v_TAtom''(2) by blast

  have "list_all (\<lambda>x. fst x = Var Value) (transaction_fresh T)"
    using x T_adm unfolding admissible_transaction_def by fast
  hence x_val: "fst x = TAtom Value" using x unfolding list_all_iff by blast

  have "\<sigma> x \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
  proof (rule ccontr)
    assume "\<not>\<sigma> x \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
    then have a: "\<sigma> x \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
      by auto

    then have \<sigma>_x_I_in_A: "\<sigma> x \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using reachable_constraints_subterms_subst[OF \<A>_reach \<I>' P] by blast

    have "\<exists>u. u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<and> \<I> u = \<sigma> x"
    proof -
      from \<sigma>_x_I_in_A have "\<exists>tu. tu \<in> \<Union> (subterms ` (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<and> tu \<cdot> \<I> = \<sigma> x \<cdot> \<I>"
        by force
      then obtain tu where tu: "tu \<in> \<Union> (subterms ` (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<and> tu \<cdot> \<I> = \<sigma> x \<cdot> \<I>"
        by auto
      then have "tu \<noteq> \<sigma> x"
        using \<sigma>_x_nin_A by auto
      moreover
      have "tu \<cdot> \<I> = \<sigma> x"
        using tu by (simp add: xn)
      ultimately
      have "\<exists>u. tu = Var u"
        unfolding xn by (cases tu) auto
      then obtain u where "tu = Var u"
        by auto
      have "u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<and> \<I> u = \<sigma> x"
      proof -
        have "u \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
          using \<open>tu = Var u\<close> tu var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t by fastforce 
        then have "u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
          using be vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] by blast
        moreover
        have "\<I> u = \<sigma> x"
          using \<open>tu = Var u\<close> \<open>tu \<cdot> \<I> = \<sigma> x\<close> by auto
        ultimately
        show ?thesis
          by auto
      qed
      then show "\<exists>u. u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<and> \<I> u = \<sigma> x"
        by metis
    qed
    then obtain u where u:
      "u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" "\<I> u = \<sigma> x"
      by auto
    then have u_TA: "\<Gamma>\<^sub>v u = TAtom Value"
      using P(1) T x_val \<Gamma>\<^sub>v_TAtom''(2)[of x]
            wt_subst_trm''[OF \<I>_wt, of "Var u"] wt_subst_trm''[of \<sigma> "Var x"] 
            transaction_fresh_subst_wt[OF \<sigma>] protocol_transaction_vars_TAtom_typed(3)
      by force
    have "\<exists>B. prefix B \<A> \<and> u \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      using u u_TA
      by (metis welltyped_constraint_model_prefix[OF \<I>]
                constraint_model_Value_var_in_constr_prefix[OF \<A>_reach _ P])
    then obtain B where "prefix B \<A> \<and> u \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      by blast
    moreover have "\<Union>(subterms ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t xs) \<subseteq> \<Union>(subterms ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ys)"
      when "prefix xs ys"
      for xs ys::"('fun,'atom,'sets,'lbl) prot_strand"
      using that subterms\<^sub>s\<^sub>e\<^sub>t_mono trms\<^sub>s\<^sub>s\<^sub>t_mono unlabel_mono set_mono_prefix by metis
    ultimately have "\<I> u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      by blast
    then have "\<sigma> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      using u by auto
    then show "False"
      using \<sigma>_x_nin_A by auto
  qed
  then show ?A
    unfolding subst_compose_def xn by auto

  from ** show ?B
  proof
    define T' where "T' \<equiv> transaction_receive T"
    define \<theta> where "\<theta> \<equiv> \<sigma> \<circ>\<^sub>s \<alpha>"

    assume y: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
    hence "Var y \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')" by (metis T'_def fv\<^sub>s\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t)
    then obtain z where z: "z \<in> set (unlabel T')" "Var y \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p z)"
      by (induct T') auto

    have "is_Receive z"
      using T_adm Ball_set[of "unlabel T'" is_Receive] z(1)
      unfolding admissible_transaction_def wellformed_transaction_def T'_def
      by blast
    then obtain ty where "z = receive\<langle>ty\<rangle>" by (cases z) auto
    hence ty: "receive\<langle>ty \<cdot> \<theta>\<rangle> \<in> set (unlabel (T' \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" "\<theta> y \<in> subterms (ty \<cdot> \<theta>)"
      using z subst_mono unfolding subst_apply_labeled_stateful_strand_def unlabel_def by force+
    hence y_deduct: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> ty \<cdot> \<theta> \<cdot> \<I>"
      using transaction_receive_deduct[OF T_adm _ \<sigma> \<alpha>]
      by (metis \<I> T'_def \<theta>_def welltyped_constraint_model_def)

    obtain zn where zn: "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val (zn, False)) []"
      using transaction_var_becomes_Val[
              OF reachable_constraints.step[OF \<A>_reach T \<sigma> \<alpha>] \<I> \<sigma> \<alpha> P T, of y]
            transaction_fresh_subst_transaction_renaming_subst_range(2)[OF \<sigma> \<alpha> *]
            y_fv y_val
      by (metis subst_apply_term.simps(1))

    have "(\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
      using private_fun_deduct_in_ik[OF y_deduct, of "Val (zn, False)"]
      by (metis \<theta>_def ty(2) zn subst_mono public.simps(3) snd_eqD)
    thus ?B
      using ik\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel \<A>" \<I>] unlabel_subst[of \<A> \<I>]
            subterms\<^sub>s\<^sub>e\<^sub>t_mono[OF ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>)"]]
      by fastforce
  next
    assume y': "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_selects T)"
    then obtain s where s: "select\<langle>Var y,s\<rangle> \<in> set (unlabel (transaction_selects T))"
                           "fst y = TAtom Value"
      using admissible_transaction_strand_step_cases(1,2)[OF T_adm] by fastforce

    obtain z zn where zn: "(\<sigma> \<circ>\<^sub>s \<alpha>) y = Var z" "\<I> z = Fun (Val zn) []"
      using transaction_var_becomes_Val[
              OF reachable_constraints.step[OF \<A>_reach T \<sigma> \<alpha>] \<I> \<sigma> \<alpha> P T]
            transaction_fresh_subst_transaction_renaming_subst_range(2)[OF \<sigma> \<alpha> *]
            y_fv T_no_bvars(1) s(2)
      by (metis subst_apply_term.simps(1))

    have transaction_selects_db_here:
        "\<And>n s. select\<langle>Var (TAtom Value, n), Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_selects T))
                \<Longrightarrow> (\<alpha> (TAtom Value, n) \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using transaction_selects_db[OF T_adm _ \<sigma> \<alpha>] \<I>
      unfolding welltyped_constraint_model_def by auto

    have "\<exists>n. y = (Var Value, n)"
      using T \<Gamma>\<^sub>v_TAtom_inv(2) y_fv y(2)
      by blast
    moreover
    have "admissible_transaction_selects T"
      using T_adm admissible_transaction_def
      by blast
    then have "is_Fun_Set (the_set_term (select\<langle>Var y,s\<rangle>))"
      using s unfolding admissible_transaction_selects_def
      by auto
    then have "\<exists>ss. s = Fun (Set ss) []"
      using is_Fun_Set_exi
      by auto
    ultimately
    obtain n ss where nss: "y = (TAtom Value, n)" "s = Fun (Set ss) []"
      by auto
    then have "select\<langle>Var (TAtom Value, n), Fun (Set ss) []\<rangle> \<in> set (unlabel (transaction_selects T))"
      using s by auto
    then have in_db: "(\<alpha> (TAtom Value, n) \<cdot> \<I>, Fun (Set ss) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using transaction_selects_db_here[of n ss] by auto
    have "(\<I> z, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
    proof -
      have "(\<alpha> y \<cdot> \<I>, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
        using in_db nss by auto
      moreover 
      have "\<alpha> y = Var z"
        using zn
        by (metis (no_types, hide_lams) \<sigma> subst_compose_def subst_imgI subst_to_var_is_var
                  term.distinct(1) transaction_fresh_subst_def var_comp(2)) 
      then have "\<alpha> y \<cdot> \<I> = \<I> z"
        by auto
      ultimately
      show "(\<I> z, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
        by auto
    qed
    then have "\<exists>t' s'. insert\<langle>t',s'\<rangle> \<in> set (unlabel \<A>) \<and> \<I> z = t' \<cdot> \<I> \<and> s = s' \<cdot> \<I>"
      using db\<^sub>s\<^sub>s\<^sub>t_in_cases[of "\<I> z" s "unlabel \<A>" \<I> "[]"] unfolding db\<^sub>s\<^sub>s\<^sub>t_def by auto
    then obtain t' s' where t's': "insert\<langle>t',s'\<rangle> \<in> set (unlabel \<A>) \<and> \<I> z = t' \<cdot> \<I> \<and> s = s' \<cdot> \<I>"
      by auto
    then have "t' \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      by force
    then have "t' \<cdot> \<I> \<in> (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      by auto
    then have "\<I> z \<in> (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using t's' by auto
    then have "\<I> z \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
      using reachable_constraints_subterms_subst[
              OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P]
      by auto
    then show ?B
      using zn(1) by simp
  qed
qed

lemma transaction_prop5:
  fixes T \<sigma> \<alpha> \<A> \<I> T' a0 a0' \<theta>
  defines "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"
    and "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
    and "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"
    and "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@T')"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and step: "list_all (transaction_check FP OCC TI) P"
  shows "\<exists>\<delta> \<in> abs_substs_fun ` set (transaction_check_comp FP OCC TI T).
         \<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x) \<and>
            (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (absdbupd (unlabel (transaction_updates T)) x (\<delta> x))"
proof -
  define comp0 where "comp0 \<equiv> abs_substs_fun ` set (transaction_check_comp FP OCC TI T)"
  define check0 where "check0 \<equiv> transaction_check FP OCC TI T"
  define upd where "upd \<equiv> \<lambda>\<delta> x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"
  define b0 where "b0 \<equiv> \<lambda>x. THE b. absc b = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"

  note all_defs = comp0_def check0_def a0_def a0'_def upd_def b0_def \<theta>_def T'_def

  have \<theta>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<delta>)" for \<delta>
    unfolding \<theta>_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
    by fastforce

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  have \<I>_is_T_model: "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) (set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)) (unlabel T') \<I>"
    using \<I> unlabel_append[of \<A> T'] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>" \<I> "[]"]
          strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "unlabel T'" \<I>]
    by (simp add: welltyped_constraint_model_def constraint_model_def db\<^sub>s\<^sub>s\<^sub>t_def)

  have T_adm: "admissible_transaction T"
    using T P(1) Ball_set[of P "admissible_transaction"]
    by blast
  hence T_valid: "wellformed_transaction T"
    unfolding admissible_transaction_def by blast

  have T_no_bvars: "fv_transaction T = vars_transaction T" "bvars_transaction T = {}"
    using transaction_no_bvars[OF T_adm] by simp_all

  have T_vars_const_typed: "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    and T_fresh_vars_value_typed: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using T P protocol_transaction_vars_TAtom_typed(2,3)[of T] by simp_all

  have wt_\<sigma>\<alpha>\<I>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)" and wt_\<sigma>\<alpha>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>)"
    using \<I>_wt wt_subst_compose transaction_fresh_subst_wt[OF \<sigma> T_fresh_vars_value_typed]
          transaction_renaming_subst_wt[OF \<alpha>]
    by blast+

  have T_vars_vals: "\<forall>x \<in> fv_transaction T. \<exists>n. (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = Fun (Val (n, False)) []"
  proof
    fix x assume x: "x \<in> fv_transaction T"
    show "\<exists>n. (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = Fun (Val (n, False)) []"
    proof (cases "x \<in> subst_domain \<sigma>")
      case True
      then obtain n where "\<sigma> x = Fun (Val (n, False)) []"
        using \<sigma> unfolding transaction_fresh_subst_def
        by moura
      thus ?thesis by (simp add: subst_compose_def)
    next
      case False
      hence *: "(\<sigma> \<circ>\<^sub>s \<alpha>) x = \<alpha> x" by (auto simp add: subst_compose_def)
      
      obtain y where y: "\<Gamma>\<^sub>v x = \<Gamma>\<^sub>v y" "\<alpha> x = Var y"
        using transaction_renaming_subst_wt[OF \<alpha>]
              transaction_renaming_subst_is_renaming[OF \<alpha>]
        by (metis \<Gamma>.simps(1) prod.exhaust wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
      hence "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"
        using x * T_no_bvars(2) unlabel_subst[of "transaction_strand T" "\<sigma> \<circ>\<^sub>s \<alpha>"]
              fv\<^sub>s\<^sub>s\<^sub>t_subst_fv_subset[of x "unlabel (transaction_strand T)" "\<sigma> \<circ>\<^sub>s \<alpha>"]
        by auto
      hence "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
        using fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>"]
              fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
        by auto
      thus ?thesis
        using x y * T P (* T_vars_const_typed *)
              constraint_model_Value_term_is_Val[
                OF reachable_constraints.step[OF \<A>_reach T \<sigma> \<alpha>] \<I>[unfolded T'_def] P(1), of y]
              admissible_transaction_Value_vars[of T]
        by simp
    qed
  qed

  have T_vars_absc: "\<forall>x \<in> fv_transaction T. \<exists>!n. (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc n"
    using T_vars_vals by fastforce
  hence "(absc \<circ> b0) x = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0" when "x \<in> fv_transaction T" for x
    using that unfolding b0_def by fastforce
  hence T_vars_absc': "t \<cdot> (absc \<circ> b0) = t \<cdot> (\<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"
    when "fv t \<subseteq> fv_transaction T" "\<nexists>n T. Fun (Val n) T \<in> subterms t" for t
    using that(1) abs_term_subst_eq'[OF _ that(2), of "\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>" a0 "absc \<circ> b0"]
          subst_compose[of "\<sigma> \<circ>\<^sub>s \<alpha>" \<I>] subst_subst_compose[of t "\<sigma> \<circ>\<^sub>s \<alpha>" \<I>]
    by fastforce

  have "\<exists>\<delta> \<in> comp0. \<forall>x \<in> fv_transaction T. fst x = TAtom Value \<longrightarrow> b0 x = \<delta> x"
  proof -
    let ?S = "set (unlabel (transaction_selects T))"
    let ?C = "set (unlabel (transaction_checks T))"
    let ?xs = "fv_transaction T - set (transaction_fresh T)"

    note * = transaction_prop3[OF \<A>_reach T \<I>[unfolded T'_def] \<sigma> \<alpha> FP OCC TI P(1)]

    have **:
        "\<forall>x \<in> set (transaction_fresh T). b0 x = {}"
        "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> b0)"
          (is ?B)
    proof -
      show ?B
      proof (intro ballI impI)
        fix t assume t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
        hence t': "fv t \<subseteq> fv_transaction T" "\<nexists>n T. Fun (Val n) T \<in> subterms t"
          using trms_transaction_unfold[of T] vars_transaction_unfold[of T]
                trms\<^sub>s\<^sub>s\<^sub>t_fv_vars\<^sub>s\<^sub>s\<^sub>t_subset[of t "unlabel (transaction_strand T)"]
                transactions_have_no_Value_consts'[OF T_adm]
                wellformed_transaction_send_receive_fv_subset(1)[OF T_valid t(1)]
          by blast+
        
        have "intruder_synth_mod_timpls FP TI (t \<cdot> (absc \<circ> b0))"
          using t(1) t' *(2) T_vars_absc'
          by (metis a0_def)
        moreover have "(absc \<circ> b0) x = (\<theta> b0) x" when "x \<in> fv t" for x
          using that T P admissible_transaction_Value_vars[of T]
                \<open>fv t \<subseteq> fv_transaction T\<close> \<Gamma>\<^sub>v_TAtom''(2)[of x]
          unfolding \<theta>_def by fastforce
        hence "t \<cdot> (absc \<circ> b0) = t \<cdot> \<theta> b0"
          using term_subst_eq[of t "absc \<circ> b0" "\<theta> b0"] by argo
        ultimately show "intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> b0)"
          using intruder_synth.simps[of "set FP"] by (cases "t \<cdot> \<theta> b0") metis+
      qed
    qed (simp add: *(1) a0_def b0_def)

    have ***: "\<forall>x \<in> ?xs. \<forall>s. select\<langle>Var x,Fun (Set s) []\<rangle> \<in> ?S \<longrightarrow> s \<in> b0 x"
              "\<forall>x \<in> ?xs. \<forall>s. \<langle>Var x in Fun (Set s) []\<rangle> \<in> ?C \<longrightarrow> s \<in> b0 x"
              "\<forall>x \<in> ?xs. \<forall>s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> ?C \<longrightarrow> s \<notin> b0 x"
              "\<forall>x \<in> ?xs. fst x = TAtom Value \<longrightarrow> b0 x \<in> set OCC"
      unfolding a0_def b0_def
      using *(3,4) apply (force, force)
      using *(5) apply force
      using *(6) admissible_transaction_Value_vars[OF bspec[OF P T]] by force

    show ?thesis
      using transaction_check_comp_in[OF T_adm **[unfolded \<theta>_def] ***]
      unfolding comp0_def
      by metis
  qed
  hence 1: "\<exists>\<delta> \<in> comp0. \<forall>x \<in> fv_transaction T.
              fst x = TAtom Value \<longrightarrow> (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x)"
    using T_vars_absc unfolding b0_def a0_def by fastforce

  obtain \<delta> where \<delta>:
      "\<delta> \<in> comp0" "\<forall>x \<in> fv_transaction T. fst x = TAtom Value \<longrightarrow> (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x)"
    using 1 by moura

  have 2: "\<theta> x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) = absc (absdbupd (unlabel A) x d)"
    when "\<theta> x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 D = absc d"
    and "\<forall>t u. insert\<langle>t,u\<rangle> \<in> set (unlabel A) \<longrightarrow> (\<exists>y s. t = Var y \<and> u = Fun (Set s) [])"
    and "\<forall>t u. delete\<langle>t,u\<rangle> \<in> set (unlabel A) \<longrightarrow> (\<exists>y s. t = Var y \<and> u = Fun (Set s) [])"
    and "\<forall>y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I> \<longrightarrow> x = y"
    and "\<forall>y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<exists>n. \<theta> y \<cdot> \<I> = Fun (Val n) []"
    and x: "\<theta> x \<cdot> \<I> = Fun (Val n) []"
    and D: "\<forall>d \<in> set D. \<exists>s. snd d = Fun (Set s) []"
    for A::"('fun,'atom,'sets,'nat) prot_strand" and x \<theta> D n d
    using that(2,3,4,5)
  proof (induction A rule: List.rev_induct)
    case (snoc a A)
    then obtain l b where a: "a = (l,b)" by (metis surj_pair)

    have IH: "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = absdbupd (unlabel A) x d"
      using snoc unlabel_append[of A "[a]"] a x
      by (simp del: unlabel_append)

    have b_prems: "\<forall>y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p b. \<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I> \<longrightarrow> x = y"
                  "\<forall>y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p b. \<exists>n. \<theta> y \<cdot> \<I> = Fun (Val n) []"
      using snoc.prems(3,4) a by (simp_all add: unlabel_def)

    have *: "filter is_Update (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) =
             filter is_Update (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
            "filter is_Update (unlabel (A@[a])) = filter is_Update (unlabel A)"
      when "\<not>is_Update b"
      using that a
      by (cases b, simp_all add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def unlabel_def subst_apply_labeled_stateful_strand_def)+

    note ** = IH a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_append[of A "[a]" \<theta>]

    note *** = * absdbupd_filter[of "unlabel (A@[a])"]
               absdbupd_filter[of "unlabel A"]
               db\<^sub>s\<^sub>s\<^sub>t_filter[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"]
               db\<^sub>s\<^sub>s\<^sub>t_filter[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"]

    note **** = **(2,3) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_snoc[of A a \<theta>]
                unlabel_append[of "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>" "[dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]"]
                db\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)" "unlabel [dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]" \<I> D]

    have "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = absdbupd (unlabel (A@[a])) x d" using ** ***
    proof (cases b)
      case (Insert t t')
      then obtain y s m where y: "t = Var y" "t' = Fun (Set s) []" "\<theta> y \<cdot> \<I> = Fun (Val m) []"
        using snoc.prems(1) b_prems(2) a by (fastforce simp add: unlabel_def)
      hence a': "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D =
                 List.insert ((Fun (Val m) [], Fun (Set s) [])) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)"
                "unlabel [dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>] = [insert\<langle>\<theta> y, Fun (Set s) []\<rangle>]"
                "unlabel [a] = [insert\<langle>Var y, Fun (Set s) []\<rangle>]"
        using **** Insert by simp_all

      show ?thesis
      proof (cases "x = y")
        case True
        hence "\<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I>" by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n =
               insert s (\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n)"
          by (metis (no_types, lifting) y(3) a'(1) x dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_insert')
        thus ?thesis using True IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      next
        case False
        hence "\<theta> x \<cdot> \<I> \<noteq> \<theta> y \<cdot> \<I>" using b_prems(1) y Insert by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n"
          by (metis (no_types, lifting) y(3) a'(1) x dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_insert)
        thus ?thesis using False IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      qed
    next
      case (Delete t t')
      then obtain y s m where y: "t = Var y" "t' = Fun (Set s) []" "\<theta> y \<cdot> \<I> = Fun (Val m) []"
        using snoc.prems(2) b_prems(2) a by (fastforce simp add: unlabel_def)
      hence a': "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D =
                 List.removeAll ((Fun (Val m) [], Fun (Set s) [])) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)"
                "unlabel [dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>] = [delete\<langle>\<theta> y, Fun (Set s) []\<rangle>]"
                "unlabel [a] = [delete\<langle>Var y, Fun (Set s) []\<rangle>]"
        using **** Delete by simp_all

      have "\<exists>s S. snd d = Fun (Set s) []" when "d \<in> set (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)" for d
        using snoc.prems(1,2) db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_ex[OF that _ _ D] by (simp add: unlabel_def)
      moreover {
        fix t::"('fun,'atom,'sets) prot_term"
          and D::"(('fun,'atom,'sets) prot_term \<times> ('fun,'atom,'sets) prot_term) list"
        assume "\<forall>d \<in> set D. \<exists>s. snd d = Fun (Set s) []"
        hence "removeAll (t, Fun (Set s) []) D = filter (\<lambda>d. \<nexists>S. d = (t, Fun (Set s) S)) D"
          by (induct D) auto
      } ultimately have a'':
          "List.removeAll ((Fun (Val m) [], Fun (Set s) [])) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D) =
           filter (\<lambda>d. \<nexists>S. d = (Fun (Val m) [], Fun (Set s) S)) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)"
        by simp

      show ?thesis
      proof (cases "x = y")
        case True
        hence "\<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I>" by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n =
               (\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n) - {s}"
          using y(3) a'' a'(1) x by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_remove_all')
        thus ?thesis using True IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      next
        case False
        hence "\<theta> x \<cdot> \<I> \<noteq> \<theta> y \<cdot> \<I>" using b_prems(1) y Delete by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n"
          by (metis (no_types, lifting) y(3) a'(1) x dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_remove_all)
        thus ?thesis using False IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      qed
    qed simp_all
    thus ?case by (simp add: x)
  qed (simp add: that(1))

  have 3: "x = y"
    when xy: "(\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" "x \<in> fv_transaction T" "y \<in> fv_transaction T"
    for x y
  proof -
    have "x \<notin> set (transaction_fresh T) \<Longrightarrow> y \<notin> set (transaction_fresh T) \<Longrightarrow> ?thesis"
      using xy admissible_transaction_strand_sem_fv_ineq[OF T_adm \<I>_is_T_model[unfolded T'_def]]
      by fast
    moreover {
      assume *: "x \<in> set (transaction_fresh T)" "y \<in> set (transaction_fresh T)"
      then obtain xn yn where "\<sigma> x = Fun (Val xn) []" "\<sigma> y = Fun (Val yn) []"
        by (metis transaction_fresh_subst_sends_to_val[OF \<sigma>])
      hence "\<sigma> x = \<sigma> y" using that(1) by (simp add: subst_compose)
      moreover have "inj_on \<sigma> (subst_domain \<sigma>)" "x \<in> subst_domain \<sigma>" "y \<in> subst_domain \<sigma>"
        using * \<sigma> unfolding transaction_fresh_subst_def by auto
      ultimately have ?thesis unfolding inj_on_def by blast
    } moreover have False when "x \<in> set (transaction_fresh T)" "y \<notin> set (transaction_fresh T)"
      using that(2) xy T_no_bvars admissible_transaction_Value_vars[OF bspec[OF P T], of y]
            transaction_prop4[OF \<A>_reach T \<I>[unfolded T'_def] \<sigma> \<alpha> P that(1), of y]
      by auto
    moreover have False when "x \<notin> set (transaction_fresh T)" "y \<in> set (transaction_fresh T)"
      using that(1) xy T_no_bvars admissible_transaction_Value_vars[OF bspec[OF P T], of x]
            transaction_prop4[OF \<A>_reach T \<I>[unfolded T'_def] \<sigma> \<alpha> P that(2), of x]
      by fastforce
    ultimately show ?thesis by metis
  qed

  have 4: "\<exists>y s. t = Var y \<and> u = Fun (Set s) []"
    when "insert\<langle>t,u\<rangle> \<in> set (unlabel (transaction_strand T))" for t u
    using that admissible_transaction_strand_step_cases(4)[OF T_adm] T_valid
    by blast

  have 5: "\<exists>y s. t = Var y \<and> u = Fun (Set s) []"
    when "delete\<langle>t,u\<rangle> \<in> set (unlabel (transaction_strand T))" for t u
    using that admissible_transaction_strand_step_cases(4)[OF T_adm] T_valid
    by blast

  have 6: "\<exists>n. (\<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val (n, False)) []" when "y \<in> fv_transaction T" for y
    using that by (simp add: T_vars_vals)

  have "list_all wellformed_transaction P" "list_all admissible_transaction_updates P"
    using P(1) Ball_set[of P "admissible_transaction"] Ball_set[of P wellformed_transaction]
          Ball_set[of P admissible_transaction_updates]
    unfolding admissible_transaction_def by fastforce+
  hence 7: "\<exists>s. snd d = Fun (Set s) []" when "d \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" for d
    using that reachable_constraints_db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_args_empty[OF \<A>_reach]
    unfolding admissible_transaction_updates_def by (cases d) simp

  have "(\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (upd \<delta> x)"
    when x: "x \<in> fv_transaction T" "fst x = TAtom Value" for x
  proof -
    have "(\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I> (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))
           = absc (absdbupd (unlabel (transaction_strand T)) x (\<delta> x))"
      using 2[of "\<sigma> \<circ>\<^sub>s \<alpha>" x "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>" "\<delta> x" "transaction_strand T"]
            3[OF _ x(1)] 4 5 6[OF that(1)] 6 7 x \<delta>(2)
      unfolding all_defs by blast
    thus ?thesis
      using x db\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] absdbupd_wellformed_transaction[OF T_valid]
      unfolding all_defs db\<^sub>s\<^sub>s\<^sub>t_def by force
  qed
  thus ?thesis using \<delta> \<Gamma>\<^sub>v_TAtom''(2) unfolding all_defs by blast
qed

lemma transaction_prop6:
  fixes T \<sigma> \<alpha> \<A> \<I> T' a0 a0'
  defines "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"
    and "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
    and "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@T')"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and step: "list_all (transaction_check FP OCC TI) P"
  shows "\<forall>t \<in> timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>).
          timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t" (is ?A)
    and "timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>) \<subseteq> absc ` set OCC" (is ?B)
    and "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T). is_Fun (t \<cdot> (\<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0') \<longrightarrow>
          timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t \<cdot> (\<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'" (is ?C)
    and "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
          (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> absc ` set OCC" (is ?D)
proof -
  define comp0 where "comp0 \<equiv> abs_substs_fun ` set (transaction_check_comp FP OCC TI T)"
  define check0 where "check0 \<equiv> transaction_check FP OCC TI T"

  define upd where "upd \<equiv> \<lambda>\<delta> x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"

  define \<theta> where "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"

  have T_adm: "admissible_transaction T" using T P(1) by metis
  hence T_valid: "wellformed_transaction T" by (metis admissible_transaction_def)

  have \<theta>_prop: "\<theta> \<sigma> x = absc (\<sigma> x)" when "\<Gamma>\<^sub>v x = TAtom Value" for \<sigma> x
    using that \<Gamma>\<^sub>v_TAtom''(2)[of x] unfolding \<theta>_def by simp

  (* The set-membership status of all value constants in T under \<I>, \<sigma>, \<alpha> are covered by the check *)
  have 0: "\<exists>\<delta> \<in> comp0. \<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x) \<and>
            (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (upd \<delta> x)"
    using transaction_prop5[OF \<A>_reach T \<I>[unfolded T'_def] \<sigma> \<alpha> FP OCC TI P step]
    unfolding a0_def a0'_def T'_def upd_def comp0_def
    by blast

  (* All set-membership changes are covered by the term implication graph *)
  have 1: "(\<delta> x, upd \<delta> x) \<in> (set TI)\<^sup>+"
    when "\<delta> \<in> comp0" "\<delta> x \<noteq> upd \<delta> x" "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
    for x \<delta> 
    using T that step Ball_set[of P "transaction_check FP OCC TI"]
          transaction_prop1[of \<delta> FP OCC TI T x] TI
    unfolding upd_def comp0_def
    by blast

  (* All set-membership changes are covered by the fixed point *)
  have 2: (* "\<delta> x \<in> set OCC" *) "upd \<delta> x \<in> set OCC"
    when "\<delta> \<in> comp0" "x \<in> fv_transaction T" "fst x = TAtom Value" for x \<delta>
    using T that step Ball_set[of P "transaction_check FP OCC TI"]
          T_adm FP OCC TI transaction_prop2[of \<delta> FP OCC TI T x]
    unfolding upd_def comp0_def
    by blast+
  
  obtain \<delta> where \<delta>:
      "\<delta> \<in> comp0"
      "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
        (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x) \<and>
        (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (upd \<delta> x)"
    using 0 by moura

  have "\<exists>x. ab = (\<delta> x, upd \<delta> x) \<and> x \<in> fv_transaction T - set (transaction_fresh T) \<and> \<delta> x \<noteq> upd \<delta> x"
    when ab: "ab \<in> \<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>" for ab
  proof -
    obtain a b where ab': "ab = (a,b)" by (metis surj_pair)
    then obtain x where x:
        "a \<noteq> b" "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
        "absc a = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0" "absc b = (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'"
      using ab unfolding abs_term_implications_def a0_def a0'_def T'_def by blast
    hence "absc a = absc (\<delta> x)" "absc b = absc (upd \<delta> x)"
      using \<delta>(2) admissible_transaction_Value_vars[OF bspec[OF P T] x(2)]
      by metis+
    thus ?thesis using x ab' by blast
  qed
  hence \<alpha>\<^sub>t\<^sub>i_TI_subset: "\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I> \<subseteq> {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}" using 1[OF \<delta>(1)] by blast
  
  have "timpl_closure_set (timpl_closure_set (set FP) (set TI)) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>) \<turnstile>\<^sub>c t"
    when t: "t \<in> timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)" for t
    using timpl_closure_set_is_timpl_closure_union[of "\<alpha>\<^sub>i\<^sub>k \<A> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>"]
          intruder_synth_timpl_closure_set FP(3) t
    by blast
  thus ?A
    using ideduct_synth_mono[OF _ timpl_closure_set_mono[OF
            subset_refl[of "timpl_closure_set (set FP) (set TI)"]
            \<alpha>\<^sub>t\<^sub>i_TI_subset]]
          timpl_closure_set_timpls_trancl_eq'[of "timpl_closure_set (set FP) (set TI)" "set TI"]
    unfolding timpl_closure_set_idem
    by force

  have "timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>) \<subseteq>
        timpl_closure_set (absc ` set OCC) {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    using timpl_closure_set_mono[OF _ \<alpha>\<^sub>t\<^sub>i_TI_subset] OCC(3) by blast
  thus ?B using OCC(2) timpl_closure_set_timpls_trancl_subset' by blast

  have "transaction_check_post FP TI T \<delta>"
    using T \<delta>(1) step
    unfolding transaction_check_def comp0_def list_all_iff
    by blast
  hence 3: "timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t \<cdot> \<theta> (upd \<delta>)"
    when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "is_Fun (t \<cdot> \<theta> (upd \<delta>))" for t
    using that
    unfolding transaction_check_post_def upd_def \<theta>_def
              intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI, symmetric]
    by meson

  have 4: "\<forall>x \<in> fv t. (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>) x \<cdot>\<^sub>\<alpha> a0' = \<theta> (upd \<delta>) x"
    when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" for t
    using wellformed_transaction_send_receive_fv_subset(2)[OF T_valid that]
          \<delta>(2) subst_compose[of "\<sigma> \<circ>\<^sub>s \<alpha>" \<I>] \<theta>_prop
          admissible_transaction_Value_vars[OF bspec[OF P T]]
    by fastforce
  
  have 5: "\<nexists>n T. Fun (Val n) T \<in> subterms t" when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" for t
    using that transactions_have_no_Value_consts'[OF T_adm] trms_transaction_unfold[of T]
    by blast

  show ?D using 2[OF \<delta>(1)] \<delta>(2) \<Gamma>\<^sub>v_TAtom''(2) unfolding a0'_def T'_def by blast

  show ?C using 3 abs_term_subst_eq'[OF 4 5] by simp
qed

lemma reachable_constraints_covered_step:
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and transactions_covered: "list_all (transaction_check FP OCC TI) P"
  shows "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>.
          timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t" (is ?A)
    and "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)) \<I> \<subseteq> absc ` set OCC" (is ?B)
proof -
  note step_props = transaction_prop6[OF \<A>_reach T \<I> \<sigma> \<alpha> FP(1,2,3) OCC TI P transactions_covered]

  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"

  define vals where "vals \<equiv> \<lambda>S::('fun,'atom,'sets,'lbl) prot_constr.
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []}"

  define vals_sym where "vals_sym \<equiv> \<lambda>S::('fun,'atom,'sets,'lbl) prot_constr.
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S). (\<exists>n. t = Fun (Val n) []) \<or> (\<exists>m. t = Var (TAtom Value,m))}"

  have \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" by (metis \<I> welltyped_constraint_model_def)

  have \<I>_grounds: "fv (t \<cdot> \<I>) = {}" for t
    using \<I> interpretation_grounds[of \<I>]
    unfolding welltyped_constraint_model_def constraint_model_def by auto

  have T_fresh_vars_value_typed: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using protocol_transaction_vars_TAtom_typed[OF bspec[OF P(1) T]] by simp_all

  have wt_\<sigma>\<alpha>\<I>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)" and wt_\<sigma>\<alpha>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>)"
    using \<I>_wt wt_subst_compose transaction_fresh_subst_wt[OF \<sigma> T_fresh_vars_value_typed]
          transaction_renaming_subst_wt[OF \<alpha>]
    by blast+

  have "\<forall>T\<in>set P. bvars_transaction T = {}"
    using P unfolding list_all_iff admissible_transaction_def by metis
  hence \<A>_no_bvars: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    using reachable_constraints_no_bvars[OF \<A>_reach] by metis

  have \<I>_vals: "\<exists>n. \<I> (TAtom Value, m) = Fun (Val n) []"
    when "(TAtom Value, m) \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for m
    using constraint_model_Value_term_is_Val'[
            OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P(1)]
          \<A>_no_bvars vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] that
    by blast

  have vals_sym_vals: "t \<cdot> \<I> \<in> vals \<A>" when t: "t \<in> vals_sym \<A>" for t
  proof (cases t)
    case (Var x)
    then obtain m where *: "x = (TAtom Value,m)" using t unfolding vals_sym_def by blast
    moreover have "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t unfolding vals_sym_def by blast
    hence "t \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "\<exists>n. \<I> (Var Value, m) = Fun (Val n) []"
      using Var * \<I>_vals[of m] var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t[of x "unlabel \<A>"]
            \<Gamma>\<^sub>v_TAtom[of Value m] reachable_constraints_Value_vars_are_fv[OF \<A>_reach P(1), of x]
      by blast+
    ultimately show ?thesis using Var unfolding vals_def by auto
  next
    case (Fun f T)
    then obtain n where "f = Val n" "T = []" using t unfolding vals_sym_def by blast
    moreover have "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t unfolding vals_sym_def by blast
    hence "t \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using Fun by blast
    ultimately show ?thesis using Fun unfolding vals_def by auto
  qed

  have vals_vals_sym: "\<exists>s. s \<in> vals_sym \<A> \<and> t = s \<cdot> \<I>" when "t \<in> vals \<A>" for t
    using that constraint_model_Val_is_Value_term[OF \<I>]
    unfolding vals_def vals_sym_def by fast

  have T_adm: "admissible_transaction T" and T_valid: "wellformed_transaction T"
    apply (metis P(1) T)
    using P(1) T Ball_set[of P "admissible_transaction"]
    unfolding admissible_transaction_def by fastforce

  have 0:
      "\<alpha>\<^sub>i\<^sub>k (\<A>@T') \<I> = (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (\<A>@T') \<I> = vals \<A> \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' \<union> vals T' \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    by (metis abs_intruder_knowledge_append a0'_def,
        metis abs_value_constants_append[of \<A> T' \<I>] a0'_def vals_def)

  have 1: "(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' =
           (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    by (metis T'_def dual_transaction_ik_is_transaction_send''[OF T_valid])

  have 2: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<inter> subst_domain \<sigma> = {}"
          "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<inter> subst_domain \<alpha> = {}"
    using T_adm unfolding admissible_transaction_def
    by blast+

  have "vals T' \<subseteq> (\<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
  proof
    fix t assume "t \<in> vals T'"
    then obtain s n where s:
        "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')" "t = s \<cdot> \<I>" "t = Fun (Val n) []"
      unfolding vals_def by fast
    then obtain u where u:
        "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
        "s = u \<cdot> (\<sigma> \<circ>\<^sub>s \<alpha>)"
      using transaction_fresh_subst_transaction_renaming_subst_trms[OF \<sigma> \<alpha> 2]
            trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>"]
      unfolding T'_def by blast

    have *: "t = u \<cdot> (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)" by (metis subst_subst_compose s(2) u(2)) 
    then obtain x where x: "u = Var x"
      using s(3) transactions_have_no_Value_consts(1)[OF T_adm u(1)] by (cases u) force+
    hence **: "x \<in> vars_transaction T"
      by (metis u(1) var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t)

    have "\<Gamma>\<^sub>v x = TAtom Value"
      using * x s(3) wt_subst_trm''[OF wt_\<sigma>\<alpha>\<I>, of u]
      by simp
    thus "t \<in> (\<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using transaction_Value_vars_are_fv[OF T_adm **] x *
      by (metis subst_comp_set_image rev_image_eqI subst_apply_term.simps(1))
  qed
  hence 3: "vals T' \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' \<subseteq> ((\<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    by (simp add: abs_apply_terms_def image_mono)

  have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)"
    when "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for t
    using that abs_in[OF imageI[OF that]]
          \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_ik[OF \<A>_reach T \<I> \<sigma> \<alpha> P(1)]
          timpl_closure_set_mono[of "{t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0}" "\<alpha>\<^sub>i\<^sub>k \<A> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>"]
    unfolding a0_def a0'_def T'_def abs_intruder_knowledge_def by fast
  hence A: "\<alpha>\<^sub>i\<^sub>k (\<A>@T') \<I> \<subseteq>
              timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>) \<union>
              (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    using 0(1) 1 by (auto simp add: abs_apply_terms_def)

  have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)"
    when t: "t \<in> vals_sym \<A>" for t
  proof -
    have "(\<exists>n. t = Fun (Val n) [] \<and> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<or>
          (\<exists>n. t = Var (TAtom Value,n) \<and> (TAtom Value,n) \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      (is "?P \<or> ?Q")
      using t var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t[of _ "unlabel \<A>"]
            \<Gamma>\<^sub>v_TAtom[of Value] reachable_constraints_Value_vars_are_fv[OF \<A>_reach P(1)]
      unfolding vals_sym_def by fast
    thus ?thesis
    proof
      assume ?P
      then obtain n where n: "t = Fun (Val n) []" "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" by moura
      thus ?thesis 
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Val[OF \<A>_reach T \<I> \<sigma> \<alpha> P(1), of n]
        unfolding a0_def a0'_def T'_def by fastforce
    next
      assume ?Q
      thus ?thesis
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Var[OF \<A>_reach T \<I> \<sigma> \<alpha> P(1)]
        unfolding a0_def a0'_def T'_def by fastforce
    qed
  qed
  moreover have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 \<in> \<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>"
    when "t \<in> vals_sym \<A>" for t
    using that abs_in vals_sym_vals
    unfolding a0_def abs_value_constants_def vals_sym_def vals_def
    by (metis (mono_tags, lifting))
  ultimately have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)"
    when t: "t \<in> vals_sym \<A>" for t
    using t timpl_closure_set_mono[of "{t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0}" "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>"]
    by blast
  hence "t \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>)"
    when t: "t \<in> vals \<A>" for t
    using vals_vals_sym[OF t] by blast
  hence B: "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (\<A>@T') \<I> \<subseteq>
              timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T \<sigma> \<alpha> \<I>) \<union>
              ((\<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    using 0(2) 3
    by (simp add: abs_apply_terms_def image_subset_iff)

  have 4: "fv (t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<cdot>\<^sub>\<alpha> a) = {}" for t a
    using \<I>_grounds[of "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha>"] abs_fv[of "t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I>" a]
    by argo

  have "is_Fun (t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0')" for t
    using 4[of t a0'] by force
  thus ?A
    using A step_props(1,3)
    unfolding T'_def a0_def a0'_def abs_apply_terms_def
    by blast

  show ?B
    using B step_props(2,4) admissible_transaction_Value_vars[OF bspec[OF P T]]
    by (auto simp add: T'_def a0_def a0'_def abs_apply_terms_def)
qed

lemma reachable_constraints_covered:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and transactions_covered: "list_all (transaction_check FP OCC TI) P"
  shows "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
using \<A>_reach \<I>
proof (induction rule: reachable_constraints.induct)
  case init
  { case 1 show ?case by (simp add: abs_intruder_knowledge_def) }
  { case 2 show ?case by (simp add: abs_value_constants_def) }
next
  case (step \<A> T \<sigma> \<alpha>)
  { case 1
    hence "welltyped_constraint_model \<I> \<A>"
      by (metis welltyped_constraint_model_prefix)
    hence IH: "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
              "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
      using step.IH by metis+
    show ?case
      using reachable_constraints_covered_step[
              OF step.hyps(1,2) "1.prems" step.hyps(3,4) FP(1,2) IH(1)
                 FP(3) OCC IH(2) TI P transactions_covered]
      by metis
  }
  { case 2
    hence "welltyped_constraint_model \<I> \<A>"
      by (metis welltyped_constraint_model_prefix)
    hence IH: "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
              "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
      using step.IH by metis+
    show ?case
      using reachable_constraints_covered_step[
              OF step.hyps(1,2) "2.prems" step.hyps(3,4) FP(1,2) IH(1)
                 FP(3) OCC IH(2) TI P transactions_covered]
      by metis
  }
qed

lemma attack_in_fixpoint_if_attack_in_ik:
  fixes FP::"('fun,'atom,'sets) prot_terms"
  assumes "\<forall>t \<in> IK \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a. FP \<turnstile>\<^sub>c t"
    and "attack\<langle>n\<rangle> \<in> IK"
  shows "attack\<langle>n\<rangle> \<in> FP"
proof -
  have "attack\<langle>n\<rangle> \<cdot>\<^sub>\<alpha> a \<in> IK \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a" by (rule abs_in[OF assms(2)])
  hence "FP \<turnstile>\<^sub>c attack\<langle>n\<rangle> \<cdot>\<^sub>\<alpha> a" using assms(1) by blast
  moreover have "attack\<langle>n\<rangle> \<cdot>\<^sub>\<alpha> a = attack\<langle>n\<rangle>" by simp
  ultimately have "FP \<turnstile>\<^sub>c attack\<langle>n\<rangle>" by metis
  thus ?thesis using ideduct_synth_priv_const_in_ik[of FP "Attack n"] by simp
qed

lemma attack_in_fixpoint_if_attack_in_timpl_closure_set:
  fixes FP::"('fun,'atom,'sets) prot_terms"
  assumes "attack\<langle>n\<rangle> \<in> timpl_closure_set FP TI"
  shows "attack\<langle>n\<rangle> \<in> FP"
proof -
  have "\<forall>f \<in> funs_term (attack\<langle>n\<rangle>). \<not>is_Abs f" by auto
  thus ?thesis using timpl_closure_set_no_Abs_in_set[OF assms] by blast
qed

theorem prot_secure_if_fixpoint_covered_typed:
  assumes FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and transactions_covered: "list_all (transaction_check FP OCC TI) P"
    and attack_notin_FP: "attack\<langle>n\<rangle> \<notin> set FP"
    and \<A>: "\<A> \<in> reachable_constraints P"
  shows "\<nexists>\<I>. welltyped_constraint_model \<I> (\<A>@[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)])" (is "\<nexists>\<I>. ?P \<I>")
proof
  assume "\<exists>\<I>. ?P \<I>"
  then obtain \<I> where \<I>: "welltyped_constraint_model \<I> (\<A>@[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)])"
    by moura
  hence \<I>': "constr_sem_stateful \<I> (unlabel (\<A>@[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)]))"
            "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    unfolding welltyped_constraint_model_def constraint_model_def by metis+

  have 0: "attack\<langle>n\<rangle> \<notin> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    using welltyped_constraint_model_prefix[OF \<I>]
          reachable_constraints_covered(1)[OF \<A> _ FP OCC TI P transactions_covered]
          attack_in_fixpoint_if_attack_in_ik[
            of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" "timpl_closure_set (set FP) (set TI)" n]
          attack_in_fixpoint_if_attack_in_timpl_closure_set
          attack_notin_FP
    unfolding abs_intruder_knowledge_def by blast

  have 1: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> attack\<langle>n\<rangle>"
    using \<I> strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" _ \<I>]
    unfolding welltyped_constraint_model_def constraint_model_def by force

  have 2: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
    using reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s[OF _ \<A>] admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1)
          ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel \<A>"] wf_trms_subst[OF \<I>'(3)]
    by fast

  have 3: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>). \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x"
    using reachable_constraints_vars_TAtom_typed[OF \<A> P(1)]
          fv_ik_subset_vars_sst'[of "unlabel \<A>"]
    by fastforce

  have 4: "attack\<langle>n\<rangle> \<notin> set (snd (Ana t)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" when t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" for t
  proof
    assume "attack\<langle>n\<rangle> \<in> set (snd (Ana t)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    then obtain s where s: "s \<in> set (snd (Ana t))" "s \<cdot> \<I> = attack\<langle>n\<rangle>" by moura

    obtain x where x: "s = Var x"
      by (cases s) (use s reachable_constraints_no_Ana_Attack[OF \<A> P(1) t] in auto)

    have "x \<in> fv t" using x Ana_subterm'[OF s(1)] vars_iff_subtermeq by force
    hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t fv_subterms by fastforce
    hence "\<Gamma>\<^sub>v x \<noteq> TAtom AttackType" using 3 by fastforce
    thus False using s(2) x wt_subst_trm''[OF \<I>'(4), of "Var x"] by fastforce
  qed

  have 5: "attack\<langle>n\<rangle> \<notin> set (snd (Ana t))" when t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)" for t
  proof
    assume "attack\<langle>n\<rangle> \<in> set (snd (Ana t))"
    then obtain s where s:
        "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<I> ` fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))" "attack\<langle>n\<rangle> \<in> set (snd (Ana s))"
      using Ana_subst_subterms_cases[OF t] 4 by fast
    then obtain x where x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" "s \<sqsubseteq> \<I> x" by moura
    hence "\<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
      using var_is_subterm[of x] subterms_subst_subset'[of \<I> "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"]
      by force
    hence *: "wf\<^sub>t\<^sub>r\<^sub>m (\<I> x)" "wf\<^sub>t\<^sub>r\<^sub>m s"
      using wf_trms_subterms[OF 2] wf_trm_subtermeq[OF _ x(2)]
      by auto

    show False
      using term.order_trans[
              OF subtermeq_imp_subtermtypeeq[OF *(2) Ana_subterm'[OF s(2)]]
                 subtermeq_imp_subtermtypeeq[OF *(1) x(2)]]
            3 x(1) wt_subst_trm''[OF \<I>'(4), of "Var x"]
      by force
  qed

  show False
    using 0 private_const_deduct[OF _ 1] 5
    by simp
qed

end


subsection \<open>Theorem: A Protocol is Secure if it is Covered by a Fixed-Point\<close>
context stateful_protocol_model
begin

theorem prot_secure_if_fixpoint_covered:
  fixes P
  assumes FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and M:
      "has_all_wt_instances_of \<Gamma> (\<Union>T \<in> set P. trms_transaction T) N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and transactions_covered: "list_all (transaction_check FP OCC TI) P"
    and attack_notin_FP: "attack\<langle>n\<rangle> \<notin> set FP"
    and A: "\<A> \<in> reachable_constraints P"
  shows "\<nexists>\<I>. constraint_model \<I> (\<A>@[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)])"
    (is "\<nexists>\<I>. ?P \<A> \<I>")
proof
  assume "\<exists>\<I>. ?P \<A> \<I>"
  then obtain \<I> where I:
      "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
      "constr_sem_stateful \<I> (unlabel (\<A>@[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)]))"
    unfolding constraint_model_def by moura

  let ?n = "[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)]"
  let ?A = "\<A>@?n"

  have "\<forall>T \<in> set P. wellformed_transaction T"
       "\<forall>T \<in> set P. admissible_transaction_terms T"
    using P(1) unfolding admissible_transaction_def by blast+
  moreover have "\<forall>T \<in> set P. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
    using P(1) unfolding admissible_transaction_def admissible_transaction_terms_def by blast
  ultimately have 0: "wf\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    using reachable_constraints_tfr[OF _ M P A] reachable_constraints_wf[OF _ _ A] by metis+
  
  have 1: "wf\<^sub>s\<^sub>s\<^sub>t (unlabel ?A)" "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel ?A)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?A)"
  proof -
    show "wf\<^sub>s\<^sub>s\<^sub>t (unlabel ?A)"
      using 0(1) wf\<^sub>s\<^sub>s\<^sub>t_append_suffix'[of "{}" "unlabel \<A>" "unlabel ?n"] unlabel_append[of \<A> ?n]
      by simp

    show "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?A)"
      using 0(3) trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel ?n"] unlabel_append[of \<A> ?n]
      by fastforce

    have "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?n \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ?n). \<exists>c. t = Fun c []"
         "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?n \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ?n). Ana t = ([],[])"
      by (simp_all add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    hence "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>) \<union>
                  (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?n \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel ?n)))"
      using 0(2) tfr_consts_mono unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by blast
    hence "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@?n) \<union> pair ` setops\<^sub>s\<^sub>s\<^sub>t (unlabel (\<A>@?n)))"
      using unlabel_append[of \<A> ?n] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel ?n"]
            setops\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel ?n"]
      by (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)
    thus "tfr\<^sub>s\<^sub>s\<^sub>t (unlabel ?A)"
      using 0(2) unlabel_append[of ?A ?n]
      unfolding tfr\<^sub>s\<^sub>s\<^sub>t_def by auto
  qed

  obtain \<I>\<^sub>\<tau> where I':
      "welltyped_constraint_model \<I>\<^sub>\<tau> ?A"
    using stateful_typing_result[OF 1 I(1,3)]
    by (metis welltyped_constraint_model_def constraint_model_def)

  note a = FP OCC TI P(1) transactions_covered attack_notin_FP A

  show False
    using prot_secure_if_fixpoint_covered_typed[OF a] I'
    by force
qed

end


subsection \<open>Automatic Fixed-Point Computation\<close>
context stateful_protocol_model
begin

definition compute_fixpoint_fun' where
  "compute_fixpoint_fun' P (n::nat option) enable_traces S0 \<equiv>
    let sy = intruder_synth_mod_timpls;

        FP' = \<lambda>S. fst (fst S);
        TI' = \<lambda>S. snd (fst S);
        OCC' = \<lambda>S. remdups (
          (map (\<lambda>t. the_Abs (the_Fun (args t ! 1)))
               (filter (\<lambda>t. is_Fun t \<and> the_Fun t = OccursFact) (FP' S)))@
          (map snd (TI' S)));

        equal_states = \<lambda>S S'. set (FP' S) = set (FP' S') \<and> set (TI' S) = set (TI' S');

        trace' = \<lambda>S. snd S;

        close = \<lambda>M f. let g = remdups \<circ> f in while (\<lambda>A. set (g A) \<noteq> set A) g M;
        close' = \<lambda>M f. let g = remdups \<circ> f in while (\<lambda>A. set (g A) \<noteq> set A) g M;
        trancl_minus_refl = \<lambda>TI.
          let aux = \<lambda>ts p. map (\<lambda>q. (fst p,snd q)) (filter ((=) (snd p) \<circ> fst) ts)
          in filter (\<lambda>p. fst p \<noteq> snd p) (close' TI (\<lambda>ts. concat (map (aux ts) ts)@ts));
        snd_Ana = \<lambda>N M TI. let N' = filter (\<lambda>t. \<forall>k \<in> set (fst (Ana t)). sy M TI k) N in
          filter (\<lambda>t. \<not>sy M TI t)
                 (concat (map (\<lambda>t. filter (\<lambda>s. s \<in> set (snd (Ana t))) (args t)) N'));
        Ana_cl = \<lambda>FP TI.
          close FP (\<lambda>M. (M@snd_Ana M M TI));
        TI_cl = \<lambda>FP TI.
          close FP (\<lambda>M. (M@filter (\<lambda>t. \<not>sy M TI t)
                                  (concat (map (\<lambda>m. concat (map (\<lambda>(a,b). \<langle>a --\<guillemotright> b\<rangle>\<langle>m\<rangle>) TI)) M))));
        Ana_cl' = \<lambda>FP TI.
          let N = \<lambda>M. comp_timpl_closure_list (filter (\<lambda>t. \<exists>k\<in>set (fst (Ana t)). \<not>sy M TI k) M) TI
          in close FP (\<lambda>M. M@snd_Ana (N M) M TI);

        \<Delta> = \<lambda>S. transaction_check_comp (FP' S) (OCC' S) (TI' S);
        result = \<lambda>S T \<delta>.
          let not_fresh = \<lambda>x. x \<notin> set (transaction_fresh T);
              xs = filter not_fresh (fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T)));
              u = \<lambda>\<delta> x. absdbupd (unlabel (transaction_strand T)) x (\<delta> x)
          in (remdups (filter (\<lambda>t. \<not>sy (FP' S) (TI' S) t)
                              (map (\<lambda>t. the_msg t \<cdot> (absc \<circ> u \<delta>))
                                   (filter is_Send (unlabel (transaction_send T))))),
              remdups (filter (\<lambda>s. fst s \<noteq> snd s) (map (\<lambda>x. (\<delta> x, u \<delta> x)) xs)));
        update_state = \<lambda>S. if list_ex (\<lambda>t. is_Fun t \<and> is_Attack (the_Fun t)) (FP' S) then S
          else let results = map (\<lambda>T. map (\<lambda>\<delta>. result S T (abs_substs_fun \<delta>)) (\<Delta> S T)) P;
                   newtrace_flt = (\<lambda>n. let x = results ! n; y = map fst x; z = map snd x
                    in set (concat y) - set (FP' S) \<noteq> {} \<or> set (concat z) - set (TI' S) \<noteq> {});
                   trace =
                    if enable_traces
                    then trace' S@[filter newtrace_flt [0..<length results]]
                    else [];
                   U = concat results;
                   V = ((remdups (concat (map fst U)@FP' S),
                         remdups (filter (\<lambda>x. fst x \<noteq> snd x) (concat (map snd U)@TI' S))),
                        trace);
                   W = ((Ana_cl (TI_cl (FP' V) (TI' V)) (TI' V),
                         trancl_minus_refl (TI' V)),
                        trace' V)
          in if \<not>equal_states W S then W
          else ((Ana_cl' (FP' W) (TI' W), TI' W), trace' W);

        S = ((\<lambda>h. case n of None \<Rightarrow> while (\<lambda>S. \<not>equal_states S (h S)) h | Some m \<Rightarrow> h ^^ m)
             update_state S0)
    in ((FP' S, OCC' S, TI' S), trace' S)"

definition compute_fixpoint_fun where
  "compute_fixpoint_fun P \<equiv> fst (compute_fixpoint_fun' P None False (([],[]),[]))"

end


subsection \<open>Locales for Protocols Proven Secure through Fixed-Point Coverage\<close>
type_synonym ('f,'a,'s) fixpoint_triple =
  "('f,'a,'s) prot_term list \<times> 's set list \<times> ('s set \<times> 's set) list"

context stateful_protocol_model
begin

definition "attack_notin_fixpoint (FPT::('fun,'atom,'sets) fixpoint_triple) \<equiv>
  list_all (\<lambda>t. \<forall>f \<in> funs_term t. \<not>is_Attack f) (fst FPT)"

definition "protocol_covered_by_fixpoint (FPT::('fun,'atom,'sets) fixpoint_triple) P \<equiv>
  let (FP, OCC, TI) = FPT
  in list_all (transaction_check FP OCC TI) P"

definition "analyzed_fixpoint (FPT::('fun,'atom,'sets) fixpoint_triple) \<equiv>
  let (FP, _, TI) = FPT
  in analyzed_closed_mod_timpls FP TI"

definition "wellformed_protocol' (P::('fun,'atom,'sets,'lbl) prot) N \<equiv>
  list_all admissible_transaction P \<and>
  has_all_wt_instances_of \<Gamma> (\<Union>T \<in> set P. trms_transaction T) (set N) \<and>
  comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> N \<and>
  list_all (\<lambda>T. list_all (comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> Pair) (unlabel (transaction_strand T))) P"

definition "wellformed_protocol (P::('fun,'atom,'sets,'lbl) prot) \<equiv>
  let f = \<lambda>M. remdups (concat (map subterms_list M@map (fst \<circ> Ana) M));
      N0 = remdups (concat (map (trms_list\<^sub>s\<^sub>s\<^sub>t \<circ> unlabel \<circ> transaction_strand) P));
      N = while (\<lambda>A. set (f A) \<noteq> set A) f N0
  in wellformed_protocol' P N"

definition "wellformed_fixpoint (FPT::('fun,'atom,'sets) fixpoint_triple) \<equiv>
  let (FP, OCC, TI) = FPT; OCC' = set OCC
  in list_all (\<lambda>t. wf\<^sub>t\<^sub>r\<^sub>m' arity t \<and> fv t = {}) FP \<and>
     list_all (\<lambda>a. a \<in> OCC') (map snd TI) \<and>
     list_all (\<lambda>(a,b). list_all (\<lambda>(c,d). b = c \<and> a \<noteq> d \<longrightarrow> List.member TI (a,d)) TI) TI \<and>
     list_all (\<lambda>p. fst p \<noteq> snd p) TI \<and>
     list_all (\<lambda>t. \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> OCC') FP"

lemma protocol_covered_by_fixpoint_I1[intro]:
  assumes "list_all (protocol_covered_by_fixpoint FPT) P"
  shows "protocol_covered_by_fixpoint FPT (concat P)"
using assms by (auto simp add: protocol_covered_by_fixpoint_def list_all_iff)

lemma protocol_covered_by_fixpoint_I2[intro]:
  assumes "protocol_covered_by_fixpoint FPT P1"
    and "protocol_covered_by_fixpoint FPT P2"
  shows "protocol_covered_by_fixpoint FPT (P1@P2)"
using assms by (auto simp add: protocol_covered_by_fixpoint_def)

lemma protocol_covered_by_fixpoint_I3[intro]:
  assumes "\<forall>T \<in> set P. \<forall>\<delta>::('fun,'atom,'sets) prot_var \<Rightarrow> 'sets set.
    transaction_check_pre FP TI T \<delta> \<longrightarrow> transaction_check_post FP TI T \<delta>"
  shows "protocol_covered_by_fixpoint (FP,OCC,TI) P"
using assms
unfolding protocol_covered_by_fixpoint_def transaction_check_def transaction_check_comp_def
          list_all_iff Let_def case_prod_unfold Product_Type.fst_conv Product_Type.snd_conv
by fastforce

lemmas protocol_covered_by_fixpoint_intros =
  protocol_covered_by_fixpoint_I1
  protocol_covered_by_fixpoint_I2
  protocol_covered_by_fixpoint_I3

lemma prot_secure_if_prot_checks:
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun, 'atom, 'sets) fixpoint_triple"
  assumes attack_notin_fixpoint: "attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered: "protocol_covered_by_fixpoint FP_OCC_TI P"
    and analyzed_fixpoint: "analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol: "wellformed_protocol' P N"
    and wellformed_fixpoint: "wellformed_fixpoint FP_OCC_TI"
  shows "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>. constraint_model \<I> (\<A>@[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)])"
proof -
  define FP where "FP \<equiv> let (FP,_,_) = FP_OCC_TI in FP"
  define OCC where "OCC \<equiv> let (_,OCC,_) = FP_OCC_TI in OCC"
  define TI where "TI \<equiv> let (_,_,TI) = FP_OCC_TI in TI"

  have attack_notin_FP: "attack\<langle>n\<rangle> \<notin> set FP"
    using attack_notin_fixpoint[unfolded attack_notin_fixpoint_def]
    unfolding list_all_iff FP_def by force

  have 1: "\<forall>(a,b) \<in> set TI. \<forall>(c,d) \<in> set TI. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> set TI"
    using wellformed_fixpoint
    unfolding wellformed_fixpoint_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] Let_def TI_def
              list_all_iff member_def case_prod_unfold
    by auto

  have 0: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    and 2: "\<forall>(a,b) \<in> set TI. a \<noteq> b"
    and 3: "snd ` set TI \<subseteq> set OCC"
    and 4: "\<forall>t \<in> set FP. \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
    and 5: "ground (set FP)"
    using wellformed_fixpoint
    unfolding wellformed_fixpoint_def wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric] is_Abs_def the_Abs_def
              list_all_iff Let_def case_prod_unfold set_map FP_def OCC_def TI_def
    by (fast, fast, blast, fastforce, simp)

  have 8: "finite (set N)"
    and 9: "has_all_wt_instances_of \<Gamma> (\<Union>T \<in> set P. trms_transaction T) (set N)"
    and 10: "tfr\<^sub>s\<^sub>e\<^sub>t (set N)"
    and 11: "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and 12: "\<forall>T \<in> set P. admissible_transaction T"
    using wellformed_protocol tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t[of N]
    unfolding Let_def list_all_iff wellformed_protocol_def wellformed_protocol'_def
              wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p[symmetric]
    by fast+

  have 13: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set N)"
    using wellformed_protocol
    unfolding wellformed_protocol_def wellformed_protocol'_def
              wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric] comp_tfr\<^sub>s\<^sub>e\<^sub>t_def list_all_iff
              finite_SMP_representation_def
    by blast

  note TI0 = trancl_eqI'[OF 1 2]

  have "analyzed (timpl_closure_set (set FP) (set TI))"
    using analyzed_fixpoint[unfolded analyzed_fixpoint_def]
          analyzed_closed_mod_timpls_is_analyzed_timpl_closure_set[OF TI0 0]
    unfolding FP_def TI_def
    by force
  note FP0 = this 0 5

  note OCC0 = funs_term_OCC_TI_subset(1)[OF 4 3]
              timpl_closure_set_supset'[OF funs_term_OCC_TI_subset(2)[OF 4 3]]

  note M0 = 9 8 10 13

  have "list_all (transaction_check FP OCC TI) P"
    using transactions_covered[unfolded protocol_covered_by_fixpoint_def]
    unfolding FP_def OCC_def TI_def
    by force
  note P0 = 12 11 this attack_notin_FP

  show ?thesis by (metis prot_secure_if_fixpoint_covered[OF FP0 OCC0 TI0 M0 P0])
qed

end

locale secure_stateful_protocol =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun, 'atom, 'sets) fixpoint_triple"
    and P_SMP::"('fun, 'atom, 'sets) prot_term list"
  assumes attack_notin_fixpoint: "pm.attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered: "pm.protocol_covered_by_fixpoint FP_OCC_TI P"
    and analyzed_fixpoint: "pm.analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol: "pm.wellformed_protocol' P P_SMP"
    and wellformed_fixpoint: "pm.wellformed_fixpoint FP_OCC_TI"
begin

theorem protocol_secure:
  "\<forall>\<A> \<in> pm.reachable_constraints P. \<nexists>\<I>. pm.constraint_model \<I> (\<A>@[(l, send\<langle>attack\<langle>n\<rangle>\<rangle>)])"
by (rule pm.prot_secure_if_prot_checks[OF
            attack_notin_fixpoint transactions_covered
            analyzed_fixpoint wellformed_protocol wellformed_fixpoint])

end

locale secure_stateful_protocol' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun, 'atom, 'sets) fixpoint_triple"
  assumes attack_notin_fixpoint': "pm.attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered': "pm.protocol_covered_by_fixpoint FP_OCC_TI P"
    and analyzed_fixpoint': "pm.analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol': "pm.wellformed_protocol P"
    and wellformed_fixpoint': "pm.wellformed_fixpoint FP_OCC_TI"
begin

sublocale secure_stateful_protocol
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P
  FP_OCC_TI
  "let f = \<lambda>M. remdups (concat (map subterms_list M@map (fst \<circ> pm.Ana) M));
       N0 = remdups (concat (map (trms_list\<^sub>s\<^sub>s\<^sub>t \<circ> unlabel \<circ> transaction_strand) P))
   in while (\<lambda>A. set (f A) \<noteq> set A) f N0"
apply unfold_locales
using attack_notin_fixpoint' transactions_covered' analyzed_fixpoint'
      wellformed_protocol'[unfolded pm.wellformed_protocol_def Let_def] wellformed_fixpoint'
unfolding Let_def by blast+

end

locale secure_stateful_protocol'' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
  assumes checks: "let FPT = pm.compute_fixpoint_fun P
    in pm.attack_notin_fixpoint FPT \<and> pm.protocol_covered_by_fixpoint FPT P \<and>
       pm.analyzed_fixpoint FPT \<and> pm.wellformed_protocol P \<and> pm.wellformed_fixpoint FPT"
begin

sublocale secure_stateful_protocol'
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P "pm.compute_fixpoint_fun P"
using checks[unfolded Let_def case_prod_unfold] by unfold_locales meson+

end

locale secure_stateful_protocol''' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun, 'atom, 'sets) fixpoint_triple"
    and P_SMP::"('fun, 'atom, 'sets) prot_term list"
  assumes checks': "let P' = P; FPT = FP_OCC_TI; P'_SMP = P_SMP
                    in pm.attack_notin_fixpoint FPT \<and>
                       pm.protocol_covered_by_fixpoint FPT P' \<and>
                       pm.analyzed_fixpoint FPT \<and>
                       pm.wellformed_protocol' P' P'_SMP \<and>
                       pm.wellformed_fixpoint FPT"
begin

sublocale secure_stateful_protocol
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P FP_OCC_TI P_SMP
using checks'[unfolded Let_def case_prod_unfold] by unfold_locales meson+

end

locale secure_stateful_protocol'''' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun, 'atom, 'sets, 'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun, 'atom, 'sets) fixpoint_triple"
  assumes checks'': "let P' = P; FPT = FP_OCC_TI
                     in pm.attack_notin_fixpoint FPT \<and>
                        pm.protocol_covered_by_fixpoint FPT P' \<and>
                        pm.analyzed_fixpoint FPT \<and>
                        pm.wellformed_protocol P' \<and>
                        pm.wellformed_fixpoint FPT"
begin

sublocale secure_stateful_protocol'
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P FP_OCC_TI
using checks''[unfolded Let_def case_prod_unfold] by unfold_locales meson+

end


subsection \<open>Automatic Protocol Composition\<close>
context stateful_protocol_model
begin

definition wellformed_composable_protocols where
  "wellformed_composable_protocols (P::('fun,'atom,'sets,'lbl) prot list) N \<equiv>
    let
      Ts = concat P;
      steps = concat (map transaction_strand Ts);
      MP0 = \<Union>T \<in> set Ts. trms_transaction T \<union> pair' Pair ` setops_transaction T
    in
      list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) N \<and>
      has_all_wt_instances_of \<Gamma> MP0 (set N) \<and>
      comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> N \<and>
      list_all (comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> Pair \<circ> snd) steps \<and>
      list_all (\<lambda>T. wellformed_transaction T) Ts \<and>
      list_all (\<lambda>T. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)) Ts \<and>
      list_all (\<lambda>T. list_all (\<lambda>x. \<Gamma>\<^sub>v x = TAtom Value) (transaction_fresh T)) Ts"

definition composable_protocols where
  "composable_protocols (P::('fun,'atom,'sets,'lbl) prot list) Ms S \<equiv>
    let
      Ts = concat P;
      steps = concat (map transaction_strand Ts);
      MP0 = \<Union>T \<in> set Ts. trms_transaction T \<union> pair' Pair ` setops_transaction T;
      M_fun = (\<lambda>l. case find ((=) l \<circ> fst) Ms of Some M \<Rightarrow> snd M | None \<Rightarrow> [])
    in comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair steps M_fun S"

lemma composable_protocols_par_comp_constr:
  fixes S f
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "Sec \<equiv> (f (set S)) - {m. intruder_synth {} m}"
  assumes Ps_pc: "wellformed_composable_protocols Ps N" "composable_protocols Ps Ms S"
  shows "\<forall>\<A> \<in> reachable_constraints (concat Ps). \<forall>\<I>. constraint_model \<I> \<A> \<longrightarrow>
            (\<exists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> \<A> \<and>
                  ((\<forall>n. welltyped_constraint_model \<I>\<^sub>\<tau> (proj n \<A>)) \<or>
                   (\<exists>\<A>'. prefix \<A>' \<A> \<and> strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>)))"
    (is "\<forall>\<A> \<in> _. \<forall>_. _ \<longrightarrow> ?Q \<A> \<I>")
proof (intro allI ballI impI)
  fix \<A> \<I>
  assume \<A>: "\<A> \<in> reachable_constraints (concat Ps)" and \<I>: "constraint_model \<I> \<A>"

  let ?Ts = "concat Ps"
  let ?steps = "concat (map transaction_strand ?Ts)"
  let ?MP0 = "\<Union>T \<in> set ?Ts. trms_transaction T \<union> pair' Pair ` setops_transaction T"
  let ?M_fun = "\<lambda>l. case find ((=) l \<circ> fst) Ms of Some M \<Rightarrow> snd M | None \<Rightarrow> []"

  have M:
      "has_all_wt_instances_of \<Gamma> ?MP0 (set N)"
      "finite (set N)" "tfr\<^sub>s\<^sub>e\<^sub>t (set N)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set N)"
    using Ps_pc tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t[of N]
    unfolding composable_protocols_def wellformed_composable_protocols_def
              Let_def list_all_iff wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric]
    by fast+

  have P:
      "\<forall>T \<in> set ?Ts. wellformed_transaction T"
      "\<forall>T \<in> set ?Ts. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
      "\<forall>T \<in> set ?Ts. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
      "\<forall>T \<in> set ?Ts. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
      "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair ?steps ?M_fun S"
    using Ps_pc tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p
    unfolding wellformed_composable_protocols_def composable_protocols_def
              Let_def list_all_iff unlabel_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric]
    by (meson, meson, meson, fastforce, blast)

  show "?Q \<A> \<I>"
    using reachable_constraints_par_comp_constr[OF M P \<A> \<I>]
    unfolding Sec_def f_def by fast
qed

end

end
