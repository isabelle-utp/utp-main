\<comment>\<open> ******************************************************************** 
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : Theorems on DF and LF
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

theory Properties
  imports "Assertions_ext"
begin

section \<open>Deadlock Free\<close>

thm deadlock_free_def

lemma deadlock_free_implies_div_free: "deadlock_free P \<Longrightarrow> D P = {}"
  by (simp add: deadlock_free_def div_free_DF failure_divergence_refine_def le_ref_def)

lemma deadlock_free_implies_non_terminating: "deadlock_free (P::'a process) \<Longrightarrow> \<forall>s\<in>T P. tickFree s"
  unfolding deadlock_free_def apply(drule FD_F, drule le_F_T) unfolding trace_refine_def 
  using DF_all_tickfree_traces1[of "(UNIV::'a set)"] tickFree_def by fastforce 

definition deadlock_free_v2 :: "'a process \<Rightarrow> bool"
  where   "deadlock_free_v2 P \<equiv> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F P"

lemma deadlock_free_v2_is_right: 
  "deadlock_free_v2 (P::'a process) \<longleftrightarrow> (\<forall>s\<in>T P. tickFree s \<longrightarrow> (s, UNIV::'a event set) \<notin> F P)"
proof
  assume a:"deadlock_free_v2 P"
  have "tickFree s \<longrightarrow> (s, UNIV) \<notin> F (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)" for s::"'a event list"
  proof(induct s)
    case Nil
    then show ?case by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_mndet write0_def F_Mprefix F_ndet F_SKIP)
  next
    case (Cons a s)
    then show ?case 
      by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, simp add:F_mndet write0_def F_Mprefix F_ndet F_SKIP)
  qed
  with a show "\<forall>s\<in>T P. tickFree s \<longrightarrow> (s, UNIV) \<notin> F P"
    using deadlock_free_v2_def failure_refine_def by blast
next 
  assume as1:"\<forall>s\<in>T P. tickFree s \<longrightarrow> (s, UNIV) \<notin> F P"
  have as2:"front_tickFree s \<Longrightarrow> (\<exists>aa \<in> UNIV. ev aa \<notin> b) \<Longrightarrow> (s, b) \<in> F (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P (UNIV::'a set))" 
       for s b
  proof(induct s)
    case Nil
    then show ?case
      by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold, auto simp add:F_mndet write0_def F_Mprefix F_ndet F_SKIP)
  next
    case (Cons hda tla)
    then show ?case 
    proof(simp add:DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def fix_def)
      define Y where "Y \<equiv> \<lambda>i. iterate i\<cdot>(\<Lambda> x. (\<sqinter>xa\<in>(UNIV::'a set) \<rightarrow>  x) \<sqinter> SKIP)\<cdot>\<bottom>"
      assume a:"front_tickFree (hda # tla)" and b:"front_tickFree tla \<Longrightarrow> (tla, b) \<in> F (\<Squnion>i. Y i)"
             and c:"\<exists>aa. ev aa \<notin> b"
      from Y_def have cc:"chain Y" by simp
      from b have d:"front_tickFree tla \<Longrightarrow> \<exists>aa\<in>UNIV. ev aa \<notin> b \<Longrightarrow>(tla, b) \<in> F (Y i)" for i 
        using F_LUB[OF cc] limproc_is_thelub[OF cc] by simp
      from Y_def have e:"F(mndet UNIV (\<lambda>x. Y i) \<sqinter> SKIP) \<subseteq> F (Y (Suc i))" for i by(simp)
      from a have f:"tla \<noteq> [] \<Longrightarrow> hda \<noteq> tick" "front_tickFree tla"
        apply (metis butlast.simps(2) butlast_snoc front_tickFree_charn 
                      list.distinct(1) tickFree_Cons)
        by (metis a append_Cons append_Nil front_tickFree_Nil front_tickFree_mono) 
      have g:"(hda#tla, b) \<in> F (Y (Suc i))" for i
        using f c e[of i] d[of i] 
        by (auto simp: F_mndet write0_def F_Mprefix Y_def F_ndet F_SKIP) (metis event.exhaust)+ 
      have h:"(hda#tla, b) \<in> F (Y 0)"
        using NF_ND cc g po_class.chainE proc_ord2a by blast
      from a b c show "(hda#tla, b) \<in> F (\<Squnion>i. Y i)"
        using F_LUB[OF cc] is_ub_thelub[OF cc] 
        by (metis D_LUB_2 cc g limproc_is_thelub po_class.chainE proc_ord2a process_charn) 
    qed   
  qed
  show "deadlock_free_v2 P"
  proof(auto simp add:deadlock_free_v2_def failure_refine_def)
    fix s b
    assume as3:"(s, b) \<in> F P"
    hence a1:"s \<in> T P" "front_tickFree s" 
       using F_T apply blast
      using as3 is_processT2 by blast
    show "(s, b) \<in> F (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV)" 
    proof(cases "tickFree s")
      case FT_True:True
      hence a2:"(s, UNIV) \<notin> F P"
        using a1 as1 by blast
      then show ?thesis 
        by (metis FT_True UNIV_I UNIV_eq_I a1(2) as2 as3 emptyE event.exhaust 
                  is_processT6_S1 tickFree_implies_front_tickFree_single) 
    next
      case FT_False: False                                                                 
      then show ?thesis 
        by (meson T_F_spec UNIV_witness a1(2) append_single_T_imp_tickFree 
                  as2 emptyE is_processT5_S7)
    qed 
  qed
qed  

lemma deadlock_free_v2_implies_div_free: "deadlock_free_v2 P \<Longrightarrow> D P = {}"
  by (metis F_T append_single_T_imp_tickFree deadlock_free_v2_is_right ex_in_conv 
            nonTickFree_n_frontTickFree process_charn)

corollary deadlock_free_v2_FD: "deadlock_free_v2 P = DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"
  unfolding deadlock_free_v2_def 
  using deadlock_free_v2_implies_div_free FD_F F_D_FD deadlock_free_v2_def divergence_refine_def 
  by fastforce 

lemma all_events_refusal: 
                        "(s, {tick} \<union> ev ` (events_of P)) \<in> F P \<Longrightarrow> (s, UNIV::'a event set) \<in> F P"
proof -
  assume a1:"(s, {tick} \<union> ev ` events_of P) \<in> F P"
  { assume "(s, UNIV) \<notin> F P"
    then obtain c where "c \<notin> {tick} \<union> ev ` events_of P \<and> s @ [c] \<in> T P"
      using is_processT5_S1[of s "{tick} \<union> ev ` events_of P" P 
            "UNIV - ({tick} \<union> ev ` events_of P)", simplified] F_T a1 by auto
    hence False by (simp add:events_of_def, cases c) fastforce+
  }  
  with a1 show "(s, UNIV) \<in> F P" by blast 
qed

corollary deadlock_free_v2_is_right_wrt_events:
  "deadlock_free_v2 (P::'a process) \<longleftrightarrow> 
                                  (\<forall>s\<in>T P. tickFree s \<longrightarrow> (s, {tick} \<union> ev ` (events_of P)) \<notin> F P)"
  unfolding deadlock_free_v2_is_right using all_events_refusal apply auto 
  using is_processT4 by blast 

lemma deadlock_free_is_deadlock_free_v2:
  "deadlock_free P \<Longrightarrow> deadlock_free_v2 P"
  using DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_DF_refine_FD deadlock_free_def deadlock_free_v2_FD trans_FD by blast 


section \<open>Non-terminating Runs\<close>

definition non_terminating  :: "'a process \<Rightarrow> bool"
  where   "non_terminating P \<equiv> RUN UNIV \<sqsubseteq>\<^sub>T P"

corollary non_terminating_refine_DF: "non_terminating P = DF UNIV \<sqsubseteq>\<^sub>T P"
  and non_terminating_refine_CHAOS: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>T P"
  by (simp_all add: DF_all_tickfree_traces1 RUN_all_tickfree_traces1 CHAOS_all_tickfree_traces1 
                    non_terminating_def trace_refine_def)

lemma non_terminating_is_right: "non_terminating (P::'a process) \<longleftrightarrow> (\<forall>s\<in>T P. tickFree s)"
  apply (rule iffI)
  by (auto simp add:non_terminating_def trace_refine_def tickFree_def RUN_all_tickfree_traces1)[1]
     (auto simp add:non_terminating_def trace_refine_def RUN_all_tickfree_traces2)

lemma nonterminating_implies_div_free: "non_terminating P \<Longrightarrow> D P = {}"
  unfolding non_terminating_is_right
  by (metis NT_ND equals0I front_tickFree_charn process_charn tickFree_Cons tickFree_append) 

lemma non_terminating_implies_F: "non_terminating P \<Longrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F P"
  apply(auto simp add: non_terminating_is_right failure_refine_def)
  using CHAOS_has_all_tickFree_failures F_T by blast 

corollary non_terminating_F: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>F P"
  by (auto simp add:non_terminating_implies_F non_terminating_refine_CHAOS le_F_T)

corollary non_terminating_FD: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"
  unfolding non_terminating_F
  using div_free_CHAOS nonterminating_implies_div_free FD_F F_D_FD divergence_refine_def 
        non_terminating_F by fastforce 


section \<open>Lifelock Freeness\<close>

thm lifelock_free_def

corollary lifelock_free_is_non_terminating: "lifelock_free P = non_terminating P"
  unfolding lifelock_free_def non_terminating_FD by rule

lemma div_free_divergence_refine:
  "D P = {} \<longleftrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>D P" 
  "D P = {} \<longleftrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>D P" 
  "D P = {} \<longleftrightarrow> RUN UNIV \<sqsubseteq>\<^sub>D P" 
  "D P = {} \<longleftrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>D P" 
  "D P = {} \<longleftrightarrow> DF UNIV \<sqsubseteq>\<^sub>D P" 
  by (simp_all add: div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P div_free_CHAOS div_free_RUN div_free_DF div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P 
                    divergence_refine_def)

definition lifelock_free_v2 :: "'a process \<Rightarrow> bool"
  where   "lifelock_free_v2 P \<equiv> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"

lemma div_free_is_lifelock_free_v2: "lifelock_free_v2 P \<longleftrightarrow> D P = {}"
  using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures_Un FD_D F_D_FD div_free_divergence_refine(1) lifelock_free_v2_def 
  by blast
  
lemma lifelock_free_is_lifelock_free_v2: "lifelock_free P \<Longrightarrow> lifelock_free_v2 P"
  by (simp add: FD_D div_free_divergence_refine(2) div_free_is_lifelock_free_v2 lifelock_free_def)

corollary deadlock_free_v2_is_lifelock_free_v2: "deadlock_free_v2 P \<Longrightarrow> lifelock_free_v2 P"
  by (simp add: deadlock_free_v2_implies_div_free div_free_is_lifelock_free_v2)


section \<open>New laws\<close>

lemma non_terminating_seq: "non_terminating P \<Longrightarrow> (P `;` Q) = P"
  apply(auto simp add: non_terminating_is_right Process_eq_spec D_seq F_seq F_T is_processT7)
      using process_charn apply blast
    using process_charn apply blast
   using F_T is_processT5_S2a apply fastforce
  using D_T front_tickFree_Nil by blast

lemma non_terminating_inter: "non_terminating P \<Longrightarrow> lifelock_free_v2 Q \<Longrightarrow> non_terminating (P \<lbrakk>C\<rbrakk> Q)"
  apply(auto simp add: non_terminating_is_right div_free_is_lifelock_free_v2 T_sync) 
  apply (metis equals0D ftf_syn1 ftf_syn21 insertI1 tickFree_def)
  apply (meson NT_ND is_processT7_S tickFree_append)
  by (metis D_T empty_iff ftf_syn1 ftf_syn21 insertI1 tickFree_def)


end
