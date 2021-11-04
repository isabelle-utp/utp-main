(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : Assertions on DF and LF and their Relations
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

chapter\<open>Basic CSP\_RefTk-Theories\<close>

theory Assertions_ext
  imports "HOL-CSP.Assertions"
begin

section \<open>Preliminaries\<close>

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold : "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A = ((\<sqinter> z \<in> A \<rightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<sqinter> SKIP)"
  by(simp add: DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule trans, rule fix_eq, simp)

section \<open>All refinements definitions\<close>

thm failure_divergence_refine_def[simplified le_ref_def] trace_refine_def failure_refine_def

definition divergence_refine :: "'a process \<Rightarrow> 'a process \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>D" 60)
  where "P \<sqsubseteq>\<^sub>D Q \<equiv> D Q \<subseteq> D P"

definition trace_divergence_refine :: "'a process \<Rightarrow> 'a process \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>D\<^sub>T" 60)
  where "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<equiv> P \<sqsubseteq>\<^sub>T Q \<and> P \<sqsubseteq>\<^sub>D Q"

section \<open>Relations between refinements\<close>

lemma le_F_T: "P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q"
  by (simp add: F_subset_imp_T_subset failure_refine_def trace_refine_def) 

lemma FD_F: "P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q"
  by (simp add: failure_divergence_refine_def failure_refine_def le_ref_def)
  
lemma FD_D: "P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q"
  by (simp add: divergence_refine_def failure_divergence_refine_def le_ref_def)

lemma DT_D: "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q"
  by (simp add: trace_divergence_refine_def)

lemma DT_T: "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q"
  by (simp add: trace_divergence_refine_def)

lemma F_D_FD:"P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q"
  by (simp add: divergence_refine_def failure_divergence_refine_def failure_refine_def le_ref_def)

lemma D_T_DT:"P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q"
  by (simp add: trace_divergence_refine_def)

section \<open>Some obvious refinements\<close>

lemma bot_FD[simp]: "\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Q"
  by (simp add: failure_divergence_refine_def)

corollary bot_F[simp]: "\<bottom> \<sqsubseteq>\<^sub>F Q"
      and bot_D[simp]: "\<bottom> \<sqsubseteq>\<^sub>D Q"
      and bot_T[simp]: "\<bottom> \<sqsubseteq>\<^sub>T Q"
      and bot_DT[simp]: "\<bottom> \<sqsubseteq>\<^sub>D\<^sub>T Q"
  by (simp_all add: FD_F FD_D le_F_T D_T_DT)

lemma STOP_leDT[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T STOP"
  by (simp add: D_STOP D_T_DT Nil_elem_T T_STOP divergence_refine_def trace_refine_def)

\<comment>\<open>For refinement proofs, we need admissibility and monotony starting with idempotency and 
  transitivity\<close>

section \<open>Idempotency\<close>

lemma idem_F[simp]: "P \<sqsubseteq>\<^sub>F P"
  by (simp add: failure_refine_def) 

lemma idem_D[simp]: "P \<sqsubseteq>\<^sub>D P"
  by (simp add: divergence_refine_def)

lemma idem_T[simp]: "P \<sqsubseteq>\<^sub>T P"
  by (simp add: trace_refine_def)

lemma idem_FD[simp]: "P \<sqsubseteq>\<^sub>F\<^sub>D P"
  by (simp add: failure_divergence_refine_def)

lemma idem_DT[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T P"
  by (simp add: trace_divergence_refine_def)

section \<open>Transitivity\<close>

lemma trans_F: "P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F S \<Longrightarrow> P \<sqsubseteq>\<^sub>F S"
  by (meson failure_refine_def order_trans)

lemma trans_D: "P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D S \<Longrightarrow> P \<sqsubseteq>\<^sub>D S"
  by (meson divergence_refine_def order_trans)

lemma trans_T: "P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>T S \<Longrightarrow> P \<sqsubseteq>\<^sub>T S"
  by (meson trace_refine_def order_trans)

lemma trans_FD: "P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D S \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D S"
  by (meson failure_divergence_refine_def order_trans)

lemma trans_DT: "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T S \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T S"
  by (meson trace_divergence_refine_def order_trans trans_D trans_T)

section \<open>Admissibility\<close>

lemma le_F_adm: "cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>F v x)"
proof(auto simp add:cont2contlubE adm_def failure_refine_def)
  fix Y a b
  assume 1:"cont u" 
     and 2:"monofun v" 
     and 3:"chain Y" 
     and 4:"\<forall>i. F (v (Y i)) \<subseteq> F (u (Y i))" 
     and 5:" (a, b) \<in> F (v (\<Squnion>x. Y x))"
  hence "v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)" for i by (simp add: is_ub_thelub monofunE)
  hence "F (v (\<Squnion>i. Y i)) \<subseteq> F (u (Y i))" for i using 4 le_approx_lemma_F by blast   
  then show "(a, b) \<in> F (\<Squnion>i. u (Y i))"
    using F_LUB[OF ch2ch_cont[OF 1 3]] limproc_is_thelub[OF ch2ch_cont[OF 1 3]] 5 by force
qed

lemma le_T_adm: "cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>T v x)"
proof(auto simp add:cont2contlubE adm_def trace_refine_def)
  fix Y x
  assume 1:"cont u" 
     and 2:"monofun v" 
     and 3:"chain Y" 
     and 4:"\<forall>i. T (v (Y i)) \<subseteq> T (u (Y i))" 
     and 5:" x \<in> T (v (\<Squnion>i. Y i))"
  hence "v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)" for i by (simp add: is_ub_thelub monofunE)
  hence "T (v (\<Squnion>i. Y i)) \<subseteq> T (u (Y i))" for i using 4 le_approx_lemma_T by blast  
  then show "x \<in> T (\<Squnion>i. u (Y i))"
    using T_LUB[OF ch2ch_cont[OF 1 3]] limproc_is_thelub[OF ch2ch_cont[OF 1 3]] 5 by force
qed

lemma le_D_adm: "cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>D v x)"
proof(auto simp add:cont2contlubE adm_def divergence_refine_def)
  fix Y x
  assume 1:"cont u" 
     and 2:"monofun v" 
     and 3:"chain Y" 
     and 4:"\<forall>i. D (v (Y i)) \<subseteq> D (u (Y i))" 
     and 5:" x \<in> D (v (\<Squnion>i. Y i))"
  hence "v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)" for i by (simp add: is_ub_thelub monofunE)
  hence "D (v (\<Squnion>i. Y i)) \<subseteq> D (u (Y i))" for i using 4 le_approx1 by blast  
  then show "x \<in> D (\<Squnion>i. u (Y i))"
    using D_LUB[OF ch2ch_cont[OF 1 3]] limproc_is_thelub[OF ch2ch_cont[OF 1 3]] 5 by force
qed

lemma le_DT_adm: "cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>D\<^sub>T v x)"
  using adm_conj[OF le_T_adm[of u v] le_D_adm[of u v]] by (simp add:trace_divergence_refine_def)

lemmas le_FD_adm = le_adm[simplified failure_divergence_refine_def[symmetric]]

section \<open>Monotonicity\<close>

lemma mono_det_D[simp]: "\<lbrakk>P \<sqsubseteq>\<^sub>D P'; S \<sqsubseteq>\<^sub>D S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<sqsubseteq>\<^sub>D (P' \<box> S')"
  by (metis D_det Un_mono divergence_refine_def)

lemma mono_det_T[simp]: "\<lbrakk>P \<sqsubseteq>\<^sub>T P'; S \<sqsubseteq>\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<sqsubseteq>\<^sub>T (P' \<box> S')"
  by (metis T_det Un_mono trace_refine_def)

corollary mono_det_DT[simp]: "\<lbrakk>P \<sqsubseteq>\<^sub>D\<^sub>T P'; S \<sqsubseteq>\<^sub>D\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<sqsubseteq>\<^sub>D\<^sub>T (P' \<box> S')"
  by (simp_all add: trace_divergence_refine_def)

lemmas mono_det_FD[simp]= mono_det_FD[simplified failure_divergence_refine_def[symmetric]]

\<comment>\<open>Deterministic choice monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close>\<close>


lemma mono_ndet_F[simp]: "\<lbrakk>P \<sqsubseteq>\<^sub>F P'; S \<sqsubseteq>\<^sub>F S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>F (P' \<sqinter> S')"
  by (metis F_ndet Un_mono failure_refine_def) 

lemma mono_ndet_D[simp]: "\<lbrakk>P \<sqsubseteq>\<^sub>D P'; S \<sqsubseteq>\<^sub>D S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D (P' \<sqinter> S')"
  by (metis D_ndet Un_mono divergence_refine_def)

lemma mono_ndet_T[simp]: "\<lbrakk>P \<sqsubseteq>\<^sub>T P'; S \<sqsubseteq>\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>T (P' \<sqinter> S')"
  by (metis T_ndet Un_mono trace_refine_def) 

corollary mono_ndet_DT[simp]: "\<lbrakk>P \<sqsubseteq>\<^sub>D\<^sub>T P'; S \<sqsubseteq>\<^sub>D\<^sub>T S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D\<^sub>T (P' \<sqinter> S')"
  by (auto simp add: trace_divergence_refine_def)

lemmas mono_ndet_FD[simp]= 
                 mono_ndet_FD[simplified failure_divergence_refine_def[symmetric]]

lemma mono_ndet_F_left[simp]: "P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>F Q"
  by (simp add: F_ndet failure_refine_def order_trans) 

lemma mono_ndet_D_left[simp]: "P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D Q"
  by (simp add: D_ndet divergence_refine_def order_trans) 

lemma mono_ndet_T_left[simp]: "P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>T Q"
  by (simp add: T_ndet trace_refine_def order_trans) 

corollary mono_ndet_DT_left[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq>\<^sub>D\<^sub>T Q"
     and mono_ndet_F_right[simp]: "P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>F Q"
     and mono_ndet_D_right[simp]: "P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>D Q"
     and mono_ndet_T_right[simp]: "P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>T Q"
     and mono_ndet_DT_right[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> (S \<sqinter> P) \<sqsubseteq>\<^sub>D\<^sub>T Q"
  by (simp_all add: trace_divergence_refine_def Ndet_commute) 
  
lemmas 
mono_ndet_FD_left[simp] = 
             mono_ndet_FD_left[simplified failure_divergence_refine_def[symmetric]] and
mono_ndet_FD_right[simp] = 
             mono_ndet_FD_right[simplified failure_divergence_refine_def[symmetric]]

lemma mono_ndet_det_FD[simp]: "(P \<sqinter> S) \<sqsubseteq>\<^sub>F\<^sub>D (P \<box> S)"
  by (metis det_id failure_divergence_refine_def mono_det_FD mono_ndet_FD_left 
            mono_ndet_FD_right order_refl) 

corollary mono_ndet_det_F[simp]: "(P \<sqinter> S) \<sqsubseteq>\<^sub>F (P \<box> S)"
      and mono_ndet_det_D[simp]: "(P \<sqinter> S) \<sqsubseteq>\<^sub>D (P \<box> S)"
      and mono_ndet_det_T[simp]: "(P \<sqinter> S) \<sqsubseteq>\<^sub>T (P \<box> S)"
      and mono_ndet_det_DT[simp]: "(P \<sqinter> S) \<sqsubseteq>\<^sub>D\<^sub>T (P \<box> S)" 
  by (simp_all add: FD_F FD_D le_F_T D_T_DT) 


lemma mono_seq_F_right[simp]: "S \<sqsubseteq>\<^sub>F S' \<Longrightarrow> (P `;` S) \<sqsubseteq>\<^sub>F (P `;` S')"
  apply (auto simp: failure_refine_def F_seq append_single_T_imp_tickFree)
  using NF_ND by fastforce+

lemma mono_seq_D_right[simp]: "S \<sqsubseteq>\<^sub>D S' \<Longrightarrow> (P `;` S) \<sqsubseteq>\<^sub>D (P `;` S')"
  by (auto simp: divergence_refine_def D_seq)

lemma  mono_seq_T_right[simp]: "S \<sqsubseteq>\<^sub>T S' \<Longrightarrow> (P `;` S)  \<sqsubseteq>\<^sub>T (P `;` S')"
  apply (auto simp: trace_refine_def T_seq append_single_T_imp_tickFree)
  using D_T by fastforce+

corollary mono_seq_DT_right[simp]: "S \<sqsubseteq>\<^sub>D\<^sub>T S' \<Longrightarrow> (P `;` S)  \<sqsubseteq>\<^sub>D\<^sub>T (P `;` S')"
  by (simp add: trace_divergence_refine_def)

lemma mono_seq_DT_left[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> (P `;` S)  \<sqsubseteq>\<^sub>D\<^sub>T (P' `;` S)"
  apply (auto simp: trace_divergence_refine_def divergence_refine_def trace_refine_def D_seq T_seq)
  by (metis (no_types, lifting) Nil_elem_T Process.F_T T_F append.right_neutral 
            is_processT5_S3 subset_eq) 

\<comment>\<open>left sequence monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close>, \<open>\<sqsubseteq>\<^sub>D\<close> and \<open>\<sqsubseteq>\<^sub>T\<close>\<close>

corollary mono_seq_DT[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> S \<sqsubseteq>\<^sub>D\<^sub>T S' \<Longrightarrow> (P `;` S)  \<sqsubseteq>\<^sub>D\<^sub>T (P' `;` S')"
  using mono_seq_DT_left mono_seq_DT_right trans_DT by blast
  
lemmas mono_seq_FD[simp]= mono_seq_FD[simplified failure_divergence_refine_def[symmetric]]


lemma mono_mprefix_F_process[simp]: "\<forall>x. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>F Mprefix A Q"
  by (auto simp: failure_refine_def F_Mprefix)

lemma mono_mprefix_D_process[simp]: "\<forall>x. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>D Mprefix A Q"
  by (auto simp: divergence_refine_def D_Mprefix)

lemma mono_mprefix_T_process[simp]: "\<forall>x. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>T Mprefix A Q"
  by (auto simp: trace_refine_def T_Mprefix)

corollary mono_mprefix_DT_process[simp]: "\<forall>x. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> Mprefix A P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A Q"
  by (simp add: trace_divergence_refine_def)
  
lemmas 
mono_mprefix_FD_process[simp] = 
                mono_mprefix_FD[simplified failure_divergence_refine_def[symmetric]]

lemma mono_mprefix_DT_set[simp]: "A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A P"
  by (auto simp add:T_Mprefix D_Mprefix trace_divergence_refine_def 
                    trace_refine_def divergence_refine_def)

corollary mono_mprefix_D_set[simp]: "A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>D Mprefix A P"
      and mono_mprefix_T_set[simp]: "A \<subseteq> B \<Longrightarrow> Mprefix B P \<sqsubseteq>\<^sub>T Mprefix A P"
  by (simp_all add: DT_D DT_T)

\<comment>\<open>Mprefix set monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close> and \<open>\<sqsubseteq>\<^sub>F\<^sub>D\<close> where it holds for deterministic choice\<close>


lemma mono_hide_F[simp]: "P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \\ A \<sqsubseteq>\<^sub>F Q \\ A"
  apply(cases "A={}", simp_all add: hide_set_empty failure_refine_def F_hiding, intro conjI, blast)
proof(subst (2) Un_commute, rule subsetI, rule UnCI, auto, goal_cases)
  case (1 b t u)
  then obtain a where a:"a \<in> A" by blast
  define f where A:"f = rec_nat t (\<lambda>i t. t @ [ev a])" 
  hence AA:"f (Suc i) = (f i) @ [ev a]" for i by simp
  hence B:"strict_mono f" by (simp add:strict_mono_def lift_Suc_mono_less_iff)
  from A have C:"t \<in> range f" by (metis (mono_tags, lifting) old.nat.simps(6) range_eqI)
  { fix i
    have "f i \<in> D Q \<and> tickFree (f i) \<and> trace_hide (f i) (ev ` A) = (trace_hide t (ev ` A))"
    proof(induct i)
      case 0
      then show ?case by (simp add: 1(4) 1(7) A)
    next
      case (Suc i)
      then show ?case 
        apply (simp add:AA a) 
        using is_processT7[rule_format, of "f i" Q "[ev a]"] front_tickFree_single by blast 
    qed
  } 
  with B C have "isInfHiddenRun f P A \<and> t \<in> range f" 
    by (metis 1(1) D_T F_subset_imp_T_subset subsetD)
  with 1 show ?case by metis
next
  case (2 b u f x)
  then show ?case using F_subset_imp_T_subset by blast 
qed 

lemma mono_hide_T[simp]: "P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P \\ A \<sqsubseteq>\<^sub>T Q \\ A"
  apply(cases "A={}", simp add: hide_set_empty, simp add:trace_refine_def T_hiding, intro conjI)
proof(goal_cases)
  case 1
  then show ?case
  proof(subst Un_commute, rule_tac subsetI, rule_tac UnCI, auto, goal_cases)
    case 11:(1 t a)
    hence tt:"t \<in> T P" by (meson Process.F_T subset_eq) 
    with 11(1) inf_hidden[of A t P] obtain f where "isInfHiddenRun f P A \<and> t \<in> range f" by auto
    with 11(4)[rule_format, of t "[]"] show ?case
      by (metis 11(1) tt append_Nil2 front_tickFree_Nil is_processT2_TR 
                nonTickFree_n_frontTickFree tick_T_F)
  qed
next
  case 2
  then show ?case
  proof(subst Un_commute, auto, goal_cases)
    case 21:(1 t u a)
    define f where A:"f = rec_nat t (\<lambda>i t. t @ [ev a])" 
    hence AA:"f (Suc i) = (f i) @ [ev a]" for i by simp
    hence B:"strict_mono f" by (simp add:strict_mono_def lift_Suc_mono_less_iff)
    from A have C:"t \<in> range f" 
      by (metis (mono_tags, lifting) old.nat.simps(6) range_eqI)
    { fix i
      have "f i \<in> D Q \<and> tickFree (f i) \<and> trace_hide (f i) (ev ` A) = (trace_hide t (ev ` A))"
      proof(induct i)
        case 0
        then show ?case   by (simp add: 21(4) 21(7) A)
      next
        case (Suc i)
        then show ?case 
          apply (simp add:AA 21(6)) 
          using is_processT7[rule_format, of "f i" Q "[ev a]"] front_tickFree_single by blast 
      qed
    } 
    with B C have "isInfHiddenRun f P A \<and> t \<in> range f" by (metis 21(1) D_T subsetD)
    with 21 show ?case by metis
  next
    case 22:(2 b u f x)
    then show ?case by blast
  qed
qed

lemma mono_hide_DT[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \\ A \<sqsubseteq>\<^sub>D\<^sub>T Q \\ A"
proof -
  assume as:"P \<sqsubseteq>\<^sub>D\<^sub>T Q"
  then have "P \\ A \<sqsubseteq>\<^sub>D Q \\ A"
    apply(auto simp:trace_divergence_refine_def divergence_refine_def 
                    trace_refine_def D_hiding T_hiding)
    by blast+
  with DT_T[THEN mono_hide_T, OF as] show ?thesis by (simp add: trace_divergence_refine_def) 
qed

lemmas mono_hide_FD[simp] = 
                 mono_hide_FD[simplified failure_divergence_refine_def[symmetric]]

\<comment>\<open>Obviously, Hide monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>D\<close>\<close>


lemma mono_sync_DT[simp]: "P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> (P \<lbrakk> A \<rbrakk> Q) \<sqsubseteq>\<^sub>D\<^sub>T (P' \<lbrakk> A \<rbrakk> Q')"
  by (simp add:trace_divergence_refine_def divergence_refine_def trace_refine_def T_sync D_sync) 
     blast

lemmas mono_sync_FD[simp] = 
                 mono_sync_FD[simplified failure_divergence_refine_def[symmetric]]

\<comment>\<open>synchronization monotony doesn't hold for \<open>\<sqsubseteq>\<^sub>F\<close>, \<open>\<sqsubseteq>\<^sub>D\<close> and \<open>\<sqsubseteq>\<^sub>T\<close>\<close>


lemma mono_mndet_F_process[simp]: "\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>F Q x \<Longrightarrow> mndet A P \<sqsubseteq>\<^sub>F mndet A Q"
  by (cases "A = {}", auto simp: failure_refine_def F_mndet write0_def F_Mprefix) 

lemma mono_mndet_D_process[simp]: "\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>D Q x \<Longrightarrow> mndet A P \<sqsubseteq>\<^sub>D mndet A Q"
  by (cases "A = {}", auto simp: divergence_refine_def D_mndet write0_def D_Mprefix)

lemma mono_mndet_T_process[simp]: "\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>T Q x \<Longrightarrow> mndet A P \<sqsubseteq>\<^sub>T mndet A Q"
  by (cases "A = {}", auto simp: trace_refine_def T_mndet write0_def T_Mprefix)

corollary mono_mndet_DT_process[simp]: "\<forall>x\<in>A. P x \<sqsubseteq>\<^sub>D\<^sub>T Q x \<Longrightarrow> mndet A P \<sqsubseteq>\<^sub>D\<^sub>T mndet A Q"
  by (simp add: trace_divergence_refine_def)
  
lemmas 
mono_mndet_FD_process[simp] = 
              mono_mndet_FD[simplified failure_divergence_refine_def[symmetric]]

lemmas 
mono_mndet_FD_set[simp] = 
              mndet_FD_subset[simplified failure_divergence_refine_def[symmetric]]

corollary mono_mndet_F_set[simp]: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> mndet B P \<sqsubseteq>\<^sub>F mndet A P"
      and mono_mndet_D_set[simp]: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> mndet B P \<sqsubseteq>\<^sub>D mndet A P"
      and mono_mndet_T_set[simp]: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> mndet B P \<sqsubseteq>\<^sub>T mndet A P"
      and mono_mndet_DT_set[simp]: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> mndet B P \<sqsubseteq>\<^sub>D\<^sub>T mndet A P"
  by (simp_all add: FD_F FD_D le_F_T D_T_DT)

lemmas 
Mprefix_refines_Mndet_FD[simp] = 
                          Mprefix_refines_Mndet[simplified failure_divergence_refine_def[symmetric]]

corollary Mprefix_refines_Mndet_F[simp]: "mndet A P \<sqsubseteq>\<^sub>F Mprefix A P"
      and Mprefix_refines_Mndet_D[simp]: "mndet A P \<sqsubseteq>\<^sub>D Mprefix A P"
      and Mprefix_refines_Mndet_T[simp]: "mndet A P \<sqsubseteq>\<^sub>T Mprefix A P"
      and Mprefix_refines_Mndet_DT[simp]: "mndet A P \<sqsubseteq>\<^sub>D\<^sub>T Mprefix A P"
  by (simp_all add: FD_F FD_D le_F_T D_T_DT) 


section \<open>Reference processes and their unfolding rules\<close>

thm DF_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def RUN_def CHAOS_def

definition CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P :: "'a set \<Rightarrow> 'a process" 
  where   "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> \<mu> X. (SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))"


thm DF_unfold DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold

lemma RUN_unfold : "RUN A = (\<box> z \<in> A \<rightarrow> RUN A)"
  by(simp add: RUN_def, rule trans, rule fix_eq, simp)

lemma CHAOS_unfold : "CHAOS A = (STOP \<sqinter> (\<box> z \<in> A \<rightarrow> CHAOS A))"
  by(simp add: CHAOS_def, rule trans, rule fix_eq, simp)
                                              
lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<equiv> SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)"
  unfolding CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def using fix_eq[of "\<Lambda> X. (SKIP \<sqinter> STOP \<sqinter> (\<box> x \<in> A \<rightarrow> X))"] by simp

section \<open>Process events and reference processes events\<close>

definition events_of where "events_of P \<equiv> (\<Union>t\<in>T P. {a. ev a \<in> set t})"

lemma events_DF: "events_of (DF A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> T (DF A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> T (\<sqinter>z\<in>A \<rightarrow>  DF A)" using DF_unfold by metis
    then obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> T (DF A)" 
      by (cases "A={}", auto simp add:T_mndet write0_def T_Mprefix T_STOP)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>T (DF A). ev x \<in> set xa"
    apply(subst DF_unfold, cases "A={}", auto simp add:T_mndet write0_def T_Mprefix)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "events_of (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> T (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> T ((\<sqinter>z\<in>A \<rightarrow>  DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<sqinter> SKIP)" using DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold by metis
    with Cons obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> T (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" 
      by (cases "A={}", auto simp add:T_mndet write0_def T_Mprefix T_STOP T_SKIP T_ndet)  
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>T (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A). ev x \<in> set xa"
    apply(subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}")
     apply(auto simp add:T_mndet write0_def T_Mprefix T_SKIP T_ndet)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_RUN: "events_of (RUN A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> T (RUN A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> T (\<box>z\<in>A \<rightarrow>  RUN A)" using RUN_unfold by metis
    then obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> T (RUN A)" by (auto simp add:T_Mprefix)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>T (RUN A). ev x \<in> set xa"
    apply(subst RUN_unfold, simp add: T_Mprefix)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_CHAOS: "events_of (CHAOS A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> T (CHAOS A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> T (STOP \<sqinter> (\<box> z \<in> A \<rightarrow> CHAOS A))" using CHAOS_unfold by metis
    then obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> T (CHAOS A)" 
      by (auto simp add:T_ndet T_Mprefix T_STOP)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>T (CHAOS A). ev x \<in> set xa"
    apply(subst CHAOS_unfold, simp add:T_ndet T_Mprefix T_STOP)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "events_of (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = A"
proof(auto simp add:events_of_def)
  fix x t
  show "t \<in> T (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<Longrightarrow> ev x \<in> set t \<Longrightarrow> x \<in> A"
  proof(induct t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons(2) have "a # t \<in> T (SKIP \<sqinter> STOP \<sqinter> (\<box> z \<in> A \<rightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))" 
      using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold by metis
    with Cons obtain aa where "a = ev aa \<and> aa \<in> A \<and> t \<in> T (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" 
      by (auto simp add:T_ndet T_Mprefix T_STOP T_SKIP)
    with Cons show ?case by auto
  qed
next
  fix x
  show "x \<in> A \<Longrightarrow> \<exists>xa\<in>T (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A). ev x \<in> set xa"
    apply(subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:T_ndet T_Mprefix T_STOP T_SKIP)
    by (metis Nil_elem_T list.sel(1) list.sel(3) list.set_intros(1))
qed

lemma events_div: "D(P) \<noteq> {} \<Longrightarrow>  events_of (P) = UNIV"
proof(auto simp add:events_of_def)
  fix x xa
  assume 1: "x \<in> D P"
  show "\<exists>x\<in>T P. ev xa \<in> set x"
  proof(cases "tickFree x")
    case True  
    hence "x@[ev xa] \<in> T P"
      using 1 NT_ND front_tickFree_single is_processT7 by blast   
    then show ?thesis by force 
  next
    case False
    hence "(butlast x)@[ev xa] \<in> T P"
      by (metis "1" D_T D_imp_front_tickFree append_single_T_imp_tickFree butlast_snoc 
                front_tickFree_single nonTickFree_n_frontTickFree process_charn) 
    then show ?thesis by force
  qed
qed


thm DF_subset

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_subset_FD: "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P B \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  apply(subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, rule le_FD_adm, simp_all add:monofunI, subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
  by (rule mono_ndet_FD, simp_all) (meson mono_mndet_FD_process mono_mndet_FD_set trans_FD) 

lemma RUN_subset_DT: "A \<subseteq> B \<Longrightarrow> RUN B \<sqsubseteq>\<^sub>D\<^sub>T RUN A"
  apply(subst RUN_def, rule fix_ind, rule le_DT_adm, simp_all add:monofunI, subst RUN_unfold)
  by (meson mono_mprefix_DT_process mono_mprefix_DT_set trans_DT)

lemma CHAOS_subset_FD: "A \<subseteq> B \<Longrightarrow> CHAOS B \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A"
  apply(subst CHAOS_def, rule fix_ind, rule le_FD_adm, simp_all add:monofunI, subst CHAOS_unfold)
  by (auto simp add: failure_divergence_refine_def le_ref_def 
                     D_Mprefix D_ndet F_STOP F_Mprefix F_ndet) 

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_subset_FD: "A \<subseteq> B \<Longrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P B \<sqsubseteq>\<^sub>F\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  apply(subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, rule le_FD_adm) 
     apply(simp_all add:monofunI, subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
  by (auto simp add: failure_divergence_refine_def le_ref_def 
                     D_Mprefix D_ndet F_STOP F_Mprefix F_ndet)

section \<open>Relations between refinements on reference processes\<close>

lemma CHAOS_has_all_tickFree_failures: 
      "tickFree a \<Longrightarrow> {x. ev x \<in> set a} \<subseteq> A \<Longrightarrow> (a,b) \<in> F (CHAOS A)"
proof(induct a)
  case Nil
  then show ?case 
    by (subst CHAOS_unfold, simp add:F_ndet F_STOP)
next
  case (Cons a0 al)
  hence "tickFree al"
    by (metis append.left_neutral append_Cons front_tickFree_charn front_tickFree_mono)
  with Cons show ?case 
    apply (subst CHAOS_unfold, simp add:F_ndet F_STOP F_Mprefix events_of_def)
    using event_set by blast
qed

lemma CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures: 
  assumes as:"(events_of P) \<subseteq> A" 
  shows "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F P"
proof -
  have "front_tickFree a \<Longrightarrow> set a \<subseteq> (\<Union>t\<in>T P. set t) \<Longrightarrow> (a,b) \<in> F (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" for a b
  proof(induct a)
    case Nil
    then show ?case 
      by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_ndet F_STOP)
  next
    case (Cons a0 al)
    hence "front_tickFree al"
      by (metis append.left_neutral append_Cons front_tickFree_charn front_tickFree_mono)
    with Cons show ?case 
      apply (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_ndet F_STOP F_SKIP F_Mprefix events_of_def as)
      apply(cases "a0=tick")
       apply (metis append.simps(2) front_tickFree_charn 
                    front_tickFree_mono list.distinct(1) tickFree_Cons)
      using event_set image_iff as[simplified events_of_def] by fastforce
  qed
  thus ?thesis 
    by (simp add: F_T SUP_upper failure_refine_def process_charn subrelI) 
qed

corollary CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures_ev: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P (events_of P) \<sqsubseteq>\<^sub>F P" 
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures_Un: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F P"
  by (simp_all add: CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures)


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_F: "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F DF A"
  by (simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, simp_all add:le_F_adm monofunI, subst DF_unfold, simp) 

lemma DF_RUN_refine_F: "DF A  \<sqsubseteq>\<^sub>F RUN A"
  apply (simp add:DF_def, rule fix_ind, simp_all add:le_F_adm monofunI, subst RUN_unfold)
  by (meson Mprefix_refines_Mndet_F mono_mndet_F_process trans_F)

lemma CHAOS_DF_refine_F: "CHAOS A  \<sqsubseteq>\<^sub>F DF A"
  apply (simp add:CHAOS_def DF_def, rule parallel_fix_ind, simp_all add: monofunI)
   apply (rule le_F_adm, simp_all add: monofun_snd)
  by (cases "A={}", auto simp add:adm_def failure_refine_def F_mndet 
                                  F_Mprefix write0_def F_ndet F_STOP)

corollary CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_CHAOS_refine_F: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F CHAOS A"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_F: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  by (simp_all add: CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures events_CHAOS events_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P 
                    trans_F[OF CHAOS_DF_refine_F DF_RUN_refine_F])


lemma div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "D(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {}"
proof(simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def fix_def) 
  define Y where "Y \<equiv> \<lambda>i. iterate i\<cdot>(\<Lambda> x. (\<sqinter>xa\<in>A \<rightarrow>  x) \<sqinter> SKIP)\<cdot>\<bottom>"
  hence a:"chain Y" by simp
  have "D (Y (Suc i)) = {d. d \<noteq> [] \<and> hd d  \<in> (ev ` A) \<and> tl d \<in> D(Y i)}" for i
    by (cases "A={}", auto simp add:Y_def D_STOP D_SKIP D_mndet write0_def D_Mprefix D_ndet) 
  hence b:"d \<in> D(Y i) \<Longrightarrow> length d \<ge> i" for d i
    by (induct i arbitrary:d, simp_all add: Nitpick.size_list_simp(2))
  { fix x
    assume c:"\<forall> i. x \<in> D (Y i)"
    from b have "x \<notin> D (Y (Suc (length x)))" using Suc_n_not_le_n by blast
    with c have False by simp
  }
  with a show "D (\<Squnion>i. Y i) = {}"
  using D_LUB[OF a] limproc_is_thelub[OF a] by auto
qed

lemma div_free_DF: "D(DF A) = {}"
proof - 
  have "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>D DF A"
    by (simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, simp_all add:le_D_adm monofunI, subst DF_unfold, simp) 
  then show ?thesis using divergence_refine_def div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P by blast 
qed

lemma div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "D (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {}"
proof -
  have "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  proof (simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind, simp_all add:le_D_adm monofunI, subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
    fix x
    assume 1:"x \<sqsubseteq>\<^sub>D CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
    have a:"((\<sqinter>xa\<in>A \<rightarrow>  x) \<sqinter> SKIP) = (SKIP \<sqinter> SKIP \<sqinter> (\<sqinter>xa\<in>A \<rightarrow>  x))" 
      by (simp add: Ndet_commute ndet_id)
    from 1 have b:"(SKIP \<sqinter> SKIP \<sqinter> (\<sqinter>xa\<in>A \<rightarrow>  x)) \<sqsubseteq>\<^sub>D (SKIP \<sqinter> STOP \<sqinter> (\<box>xa\<in>A \<rightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))"
      by (meson DT_D Mprefix_refines_Mndet_D STOP_leDT idem_D 
                mono_mprefix_D_process mono_ndet_D trans_D)
    from a b show "((\<sqinter>xa\<in>A \<rightarrow>  x) |-| SKIP) \<sqsubseteq>\<^sub>D (SKIP |-| STOP |-| Mprefix A (\<lambda>x. CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A))" 
      by simp
  qed
  then show ?thesis using divergence_refine_def div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P by blast 
qed

lemma div_free_CHAOS: "D(CHAOS A) = {}"
proof - 
  have "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>D CHAOS A"
    apply (simp add:CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, rule fix_ind)
    by (simp_all add:le_D_adm monofunI, subst CHAOS_unfold, simp) 
  then show ?thesis using divergence_refine_def div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P by blast 
qed

lemma div_free_RUN: "D(RUN A) = {}"
proof - 
  have "CHAOS A  \<sqsubseteq>\<^sub>D RUN A"
    by (simp add:CHAOS_def, rule fix_ind, simp_all add:le_D_adm monofunI, subst RUN_unfold, simp) 
  then show ?thesis using divergence_refine_def div_free_CHAOS by blast 
qed

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_FD: "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F\<^sub>D DF A"
      and DF_RUN_refine_FD: "DF A  \<sqsubseteq>\<^sub>F\<^sub>D RUN A"
      and CHAOS_DF_refine_FD: "CHAOS A  \<sqsubseteq>\<^sub>F\<^sub>D DF A"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_CHAOS_refine_FD: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F\<^sub>D CHAOS A"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_FD: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A  \<sqsubseteq>\<^sub>F\<^sub>D DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A"
  using div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P[of A] div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P[of A] div_free_DF[of A] div_free_RUN[of A] 
        div_free_CHAOS[of A] 
        F_D_FD[OF DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_F, of A] F_D_FD[OF DF_RUN_refine_F, of A] 
        F_D_FD[OF CHAOS_DF_refine_F, of A] F_D_FD[OF CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_CHAOS_refine_F, of A] 
        F_D_FD[OF CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_F, of A]
  by (auto simp add:divergence_refine_def) 


lemma traces_CHAOS_sub: "T(CHAOS A) \<subseteq> {s. set s \<subseteq> ev ` A}"
proof(auto)
  fix s sa
  assume "s \<in> T (CHAOS A)" and "sa \<in> set s"
  then show "sa \<in> ev ` A"
    apply (induct s, simp) 
    by (subst (asm) (2) CHAOS_unfold, cases "A={}", auto simp add:T_ndet T_STOP T_Mprefix)  
qed

lemma traces_RUN_sub: "{s. set s \<subseteq> ev ` A} \<subseteq> T(RUN A)"
proof(auto)
  fix s
  assume "set s \<subseteq> ev ` A"
  then show "s \<in> T (RUN A)"
    by (induct s, simp add: Nil_elem_T) (subst RUN_unfold, auto simp add:T_Mprefix)
qed

corollary RUN_all_tickfree_traces1: "T(RUN A) = {s. set s \<subseteq> ev ` A}" 
      and DF_all_tickfree_traces1: "T(DF A) = {s. set s \<subseteq> ev ` A}" 
      and CHAOS_all_tickfree_traces1: "T(CHAOS A) = {s. set s \<subseteq> ev ` A}"
  using DF_RUN_refine_F[THEN le_F_T, simplified trace_refine_def]
        CHAOS_DF_refine_F[THEN le_F_T,simplified trace_refine_def] 
        traces_CHAOS_sub traces_RUN_sub by blast+

corollary RUN_all_tickfree_traces2: "tickFree s \<Longrightarrow> s \<in> T(RUN UNIV)" 
      and DF_all_tickfree_traces2: "tickFree s \<Longrightarrow> s \<in> T(DF UNIV)" 
      and CHAOS_all_tickfree_trace2: "tickFree s \<Longrightarrow> s \<in> T(CHAOS UNIV)"
    apply(simp_all add:tickFree_def RUN_all_tickfree_traces1 
                       DF_all_tickfree_traces1 CHAOS_all_tickfree_traces1)
  by (metis event_set insertE subsetI)+

lemma traces_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub: "T(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) \<subseteq> {s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})}"
proof(auto simp add:is_processT2_TR)
  fix s sa
  assume "s \<in> T (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)" and "sa \<in> set s" and "sa \<notin> ev ` A"
  then show "sa = tick"
    apply (induct s, simp) 
    by (subst (asm) (2) CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}", auto simp add:T_ndet T_STOP T_SKIP T_Mprefix)  
qed

lemma traces_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub: 
                      "{s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})} \<subseteq> T(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A::'a process)"
proof(auto)
  fix s
  assume a:"front_tickFree s" and b:"set s \<subseteq> insert tick (ev ` A)"
  have c:"front_tickFree ((tick::'a event) # s) \<Longrightarrow> s = []" for s
    by (metis butlast.simps(2) butlast_snoc front_tickFree_charn list.distinct(1) tickFree_Cons) 
  with a b show "s \<in> T (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A)"
    apply (induct s, simp add: Nil_elem_T, subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}") 
     apply (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, cases "A={}")
      apply(auto simp add:T_Mprefix T_mndet write0_def T_SKIP T_ndet T_STOP)
    apply (metis append_Cons append_Nil front_tickFree_charn front_tickFree_mono)
    by (metis append_Cons append_Nil front_tickFree_mono)
  qed

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1: 
                              "T(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})}" 
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1: 
                              "T(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = {s. front_tickFree s \<and> set s \<subseteq> (ev ` A \<union> {tick})}"
  using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_refine_F[THEN le_F_T, simplified trace_refine_def]
        traces_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub traces_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_sub by blast+

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2: "front_tickFree s \<Longrightarrow> s \<in> T(DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)" 
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2: "front_tickFree s \<Longrightarrow> s \<in> T(CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)"
   apply(simp_all add:tickFree_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1 
                      CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces1)
  by (metis event_set subsetI)+

corollary DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_traces: "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>T P"
      and CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_traces: "CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>T P"
  apply (simp add:trace_refine_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2 is_processT2_TR subsetI) 
  by (simp add:trace_refine_def CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_all_front_tickfree_traces2 is_processT2_TR subsetI) 

end
