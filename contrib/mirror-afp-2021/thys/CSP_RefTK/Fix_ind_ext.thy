(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : More Fixpoint and k-Induction Schemata
 *
 * Copyright (c) 2020 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter \<open> Advanced Induction Schemata \<close>

theory Fix_ind_ext

imports HOLCF

begin

section\<open>k-fixpoint-induction\<close>

lemma nat_k_induct: 
  fixes k::nat
  assumes "\<forall>i<k. P i" and "\<forall>n\<^sub>0. (\<forall>i<k. P (n\<^sub>0+i)) \<longrightarrow> P (n\<^sub>0+k)"
  shows "P (n::nat)"
proof(induct rule:nat_less_induct)
  case (1 n)
  then show ?case 
    apply(cases "n < k") 
     using assms(1) apply blast
    using assms(2)[rule_format, of "n-k"] by auto
qed

thm fix_ind fix_ind2 

lemma fix_ind_k:
  fixes k::nat
  assumes adm: "adm P"
  assumes base_k_steps: "\<forall>i<k. P (iterate i\<cdot>f\<cdot>\<bottom>)"
  assumes step: "\<And>x. (\<forall>i<k.  P (iterate i\<cdot>f\<cdot>x)) \<Longrightarrow> P (iterate k\<cdot>f\<cdot>x)"
  shows "P (fix\<cdot>f)"
  unfolding fix_def2 apply (rule admD [OF adm chain_iterate])
  apply(rule nat_k_induct[of k], simp add: base_k_steps) 
  using step by (subst (1 2) add.commute, unfold iterate_iterate[symmetric]) blast 

lemma nat_k_skip_induct:
  fixes k::nat
  assumes "k \<ge> 1" and "\<forall>i<k. P i" and "\<forall>n\<^sub>0. P (n\<^sub>0) \<longrightarrow> P (n\<^sub>0+k)"
  shows "P (n::nat)"
proof(induct rule:nat_less_induct)
  case (1 n)
  then show ?case 
    apply(cases "n < k") 
     using assms(2) apply blast
    using assms(3)[rule_format, of "n-k"] assms(1) by auto
qed

lemma fix_ind_k_skip:
  fixes k::nat
  assumes k_1: "k \<ge> 1"
  assumes adm: "adm P"
  assumes base_k_steps: "\<forall>i<k. P (iterate i\<cdot>f\<cdot>\<bottom>)"
  assumes step: "\<And>x. P x \<Longrightarrow> P (iterate k\<cdot>f\<cdot>x)"
  shows "P (fix\<cdot>f)"
  unfolding fix_def2 apply (rule admD [OF adm chain_iterate])
  apply(rule nat_k_skip_induct[of k]) 
  using k_1 base_k_steps apply auto
  using step by (subst add.commute, unfold iterate_iterate[symmetric]) blast

thm parallel_fix_ind

section\<open>Parallel fixpoint-induction\<close>

lemma parallel_fix_ind_inc:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes base_fst: "\<And>y. P \<bottom> y" and base_snd: "\<And>x. P x \<bottom>"
  assumes step: "\<And>x y. P x y \<Longrightarrow> P (G\<cdot>x) y \<Longrightarrow> P x (H\<cdot>y) \<Longrightarrow> P (G\<cdot>x) (H\<cdot>y)"
  shows "P (fix\<cdot>G) (fix\<cdot>H)"
proof -
  from adm have adm': "adm (case_prod P)"
    unfolding split_def .
  have "P (iterate i\<cdot>G\<cdot>\<bottom>) (iterate j\<cdot>H\<cdot>\<bottom>)" for i j
  proof(induct "i+j" arbitrary:i j rule:nat_less_induct)
    case 1
    { fix i' j'
      assume i:"i = Suc i'" and j:"j = Suc j'"
      have "P (iterate i'\<cdot>G\<cdot>\<bottom>) (iterate j'\<cdot>H\<cdot>\<bottom>)" 
       and "P (iterate i'\<cdot>G\<cdot>\<bottom>) (iterate j\<cdot>H\<cdot>\<bottom>)" 
       and "P (iterate i\<cdot>G\<cdot>\<bottom>) (iterate j'\<cdot>H\<cdot>\<bottom>)"
        using "1.hyps" add_strict_mono i j apply blast 
        using "1.hyps" i apply auto[1] 
        using "1.hyps" j by auto
      hence ?case by (simp add: i j step)
    }
    thus ?case
      apply(cases i, simp add:base_fst)
      apply(cases j, simp add:base_snd)
      by assumption
  qed
  then have "\<And>i. case_prod P (iterate i\<cdot>G\<cdot>\<bottom>, iterate i\<cdot>H\<cdot>\<bottom>)"
    by simp
  then have "case_prod P (\<Squnion>i. (iterate i\<cdot>G\<cdot>\<bottom>, iterate i\<cdot>H\<cdot>\<bottom>))"
    by - (rule admD [OF adm'], simp, assumption)
  then have "P (\<Squnion>i. iterate i\<cdot>G\<cdot>\<bottom>) (\<Squnion>i. iterate i\<cdot>H\<cdot>\<bottom>)"
    by (simp add: lub_Pair)  
  then show "P (fix\<cdot>G) (fix\<cdot>H)"
    by (simp add: fix_def2)
qed

end