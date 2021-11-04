(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : A Normalization Theory
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

chapter\<open> Normalisation of Deterministic CSP Processes \<close>

theory Process_norm

imports "Properties" "Fix_ind_ext"

begin

section\<open>Deterministic normal-forms with explicit state\<close>

abbreviation "P_dnorm Tr Up \<equiv> (\<mu> X. (\<lambda> s. \<box> e \<in> (Tr s) \<rightarrow> X (Up s e)))"

notation P_dnorm ("P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>_,_\<rbrakk>" 60)

lemma dnorm_cont[simp]:
  fixes Tr::"'state::type \<Rightarrow> 'event::type set" and Up::"'state \<Rightarrow> 'event \<Rightarrow> 'state"
  shows "cont (\<lambda>X. (\<lambda>s. \<box> e \<in> (Tr s) \<rightarrow> X (Ur s e)))" (is "cont ?f")
proof -
  have  "cont (\<lambda>X. ?f X s)" for s by (simp add:cont_fun) 
  then show ?thesis by simp
qed

section\<open>Interleaving product lemma\<close>

lemma dnorm_inter:  
  fixes Tr\<^sub>1 ::"'state\<^sub>1::type \<Rightarrow> 'event::type set" and Tr\<^sub>2::"'state\<^sub>2::type \<Rightarrow> 'event set" 
    and Up\<^sub>1 ::"'state\<^sub>1 \<Rightarrow> 'event \<Rightarrow> 'state\<^sub>1" and Up\<^sub>2::"'state\<^sub>2 \<Rightarrow> 'event \<Rightarrow> 'state\<^sub>2"
  defines P: "P \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>1,Up\<^sub>1\<rbrakk>" (is "P \<equiv> fix\<cdot>(\<Lambda> X. ?P X)")
  defines Q: "Q \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>2,Up\<^sub>2\<rbrakk>" (is "Q \<equiv> fix\<cdot>(\<Lambda> X. ?Q X)")

  assumes indep: \<open>\<forall>s\<^sub>1 s\<^sub>2. Tr\<^sub>1 s\<^sub>1 \<inter> Tr\<^sub>2 s\<^sub>2 = {}\<close>

  defines Tr: "Tr \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2). Tr\<^sub>1 s\<^sub>1 \<union> Tr\<^sub>2 s\<^sub>2)"
  defines Up: "Up \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2) e. if e \<in> Tr\<^sub>1 s\<^sub>1 then (Up\<^sub>1 s\<^sub>1 e,s\<^sub>2)
                                else if e \<in> Tr\<^sub>2 s\<^sub>2 then (s\<^sub>1, Up\<^sub>2 s\<^sub>2 e)
                                else (s\<^sub>1,s\<^sub>2))"  
  defines S: "S \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr,Up\<rbrakk>" (is "S \<equiv> fix\<cdot>(\<Lambda> X. ?S X)")
  
  shows "(P s\<^sub>1 ||| Q s\<^sub>2) = S (s\<^sub>1,s\<^sub>2)"
proof -
  have P_rec: "P = ?P P" using fix_eq[of "(\<Lambda> X. ?P X)"] P by simp 
  have Q_rec: "Q = ?Q Q" using fix_eq[of "(\<Lambda> X. ?Q X)"] Q by simp 
  have S_rec: "S = ?S S" using fix_eq[of "(\<Lambda> X. ?S X)"] S by simp
  have dir1: "\<forall> s\<^sub>1 s\<^sub>2. (P s\<^sub>1 ||| Q s\<^sub>2) \<sqsubseteq> S (s\<^sub>1, s\<^sub>2)"
  proof(subst P, subst Q, 
        induct rule:parallel_fix_ind_inc[of "\<lambda>x y. \<forall> s\<^sub>1 s\<^sub>2. (x s\<^sub>1 ||| y s\<^sub>2) \<sqsubseteq> S (s\<^sub>1,s\<^sub>2)"])
      case adm:1                                       
      then show ?case
        by (intro adm_all adm_below) (simp_all add: cont2cont_fun)
    next
      case base_fst:(2 y)
      then show ?case by (metis Inter_commute app_strict minimal par_Int_bot) 
    next
      case base_snd:(3 x)
      then show ?case by (simp add: par_Int_bot)
    next
      case step:(4 x y)
      then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        show "?C s\<^sub>1 s\<^sub>2"
          apply(simp)
          apply(subst mprefix_Par_Int[where C="{}", simplified])
          apply(subst S_rec, simp add: Tr Up mprefix_Un_distr)
          apply(intro mono_det_ref mono_mprefix_ref)
          using step(3)[simplified] indep apply simp
          using step(2)[simplified] indep by fastforce
      qed
    qed     
  have dir2: "\<forall> s\<^sub>1 s\<^sub>2.  S (s\<^sub>1, s\<^sub>2) \<sqsubseteq> (P s\<^sub>1 ||| Q s\<^sub>2)"
    proof(subst S, induct rule:fix_ind_k[of "\<lambda>x. \<forall> s\<^sub>1 s\<^sub>2. x (s\<^sub>1,s\<^sub>2) \<sqsubseteq> (P s\<^sub>1 ||| Q s\<^sub>2)" 1])
      case adm:1
      show ?case  by (intro adm_all adm_below) (simp_all add: cont_fun) 
    next
      case base_k_steps:2
      then show ?case by simp
    next
      case step:(3 x)
      then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        have P_rec_sym:"Mprefix (Tr\<^sub>1 s\<^sub>1) (\<lambda>e. P (Up\<^sub>1 s\<^sub>1 e)) = P s\<^sub>1" using P_rec by metis
        have Q_rec_sym:"Mprefix (Tr\<^sub>2 s\<^sub>2) (\<lambda>e. Q (Up\<^sub>2 s\<^sub>2 e)) = Q s\<^sub>2" using Q_rec by metis
        show "?C s\<^sub>1 s\<^sub>2"
          apply(simp add: Tr Up mprefix_Un_distr)
          apply(subst P_rec, subst Q_rec, subst mprefix_Par_Int[where C="{}", simplified])
          apply(intro mono_det_ref mono_mprefix_ref)
          apply(subst Q_rec_sym, simp add:step[simplified])
          apply(subst P_rec_sym) using step[simplified] indep by fastforce
      qed
    qed
  from dir1 dir2 show ?thesis using below_antisym by blast
qed

section \<open>Synchronous product lemma\<close>
lemma dnorm_par:  
  fixes Tr\<^sub>1 ::"'state\<^sub>1::type \<Rightarrow> 'event::type set" and Tr\<^sub>2::"'state\<^sub>2::type \<Rightarrow> 'event set" 
    and Up\<^sub>1 ::"'state\<^sub>1 \<Rightarrow> 'event \<Rightarrow> 'state\<^sub>1" and Up\<^sub>2::"'state\<^sub>2 \<Rightarrow> 'event \<Rightarrow> 'state\<^sub>2"
  defines P: "P \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>1,Up\<^sub>1\<rbrakk>" (is "P \<equiv> fix\<cdot>(\<Lambda> X. ?P X)")
  defines Q: "Q \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>2,Up\<^sub>2\<rbrakk>" (is "Q \<equiv> fix\<cdot>(\<Lambda> X. ?Q X)")

  defines Tr: "Tr \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2). Tr\<^sub>1 s\<^sub>1 \<inter> Tr\<^sub>2 s\<^sub>2)"
  defines Up: "Up \<equiv> (\<lambda>(s\<^sub>1,s\<^sub>2) e. (Up\<^sub>1 s\<^sub>1 e, Up\<^sub>2 s\<^sub>2 e))"  
  defines S: "S \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr,Up\<rbrakk>" (is "S \<equiv> fix\<cdot>(\<Lambda> X. ?S X)")
  
  shows "(P s\<^sub>1 || Q s\<^sub>2) = S (s\<^sub>1,s\<^sub>2)"
proof -
  have P_rec: "P = ?P P" using fix_eq[of "(\<Lambda> X. ?P X)"] P by simp 
  have Q_rec: "Q = ?Q Q" using fix_eq[of "(\<Lambda> X. ?Q X)"] Q by simp 
  have S_rec: "S = ?S S" using fix_eq[of "(\<Lambda> X. ?S X)"] S by simp
  have dir1: "\<forall> s\<^sub>1 s\<^sub>2. (P s\<^sub>1 || Q s\<^sub>2) \<sqsubseteq> S (s\<^sub>1, s\<^sub>2)"
  proof(subst P, subst Q, 
        induct rule:parallel_fix_ind[of "\<lambda>x y. \<forall> s\<^sub>1 s\<^sub>2. (x s\<^sub>1 || y s\<^sub>2) \<sqsubseteq> S (s\<^sub>1,s\<^sub>2)"])
      case adm:1
      then show ?case
        by (intro adm_all adm_below) (simp_all add: cont2cont_fun)
    next
      case base:2
      then show ?case by (simp add: par_Int_bot)
    next
      case step:(3 x y)
      then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        show "?C s\<^sub>1 s\<^sub>2"
          apply(simp)
          apply(subst mprefix_Par_distr[where C="UNIV", simplified])
          apply(subst S_rec, simp add: Tr Up mprefix_Un_distr)
          by (simp add:step mono_mprefix_ref)
      qed
    qed     
  have dir2: "\<forall> s\<^sub>1 s\<^sub>2.  S (s\<^sub>1, s\<^sub>2) \<sqsubseteq> (P s\<^sub>1 || Q s\<^sub>2)"
    proof(subst S, induct rule:fix_ind_k[of "\<lambda>x. \<forall> s\<^sub>1 s\<^sub>2. x (s\<^sub>1,s\<^sub>2) \<sqsubseteq> (P s\<^sub>1 || Q s\<^sub>2)" 1])
      case adm:1
      show ?case  by (intro adm_all adm_below) (simp_all add: cont_fun) 
    next
      case base_k_steps:2
      then show ?case by simp
    next
      case step:(3 x)
      then show ?case (is "\<forall> s\<^sub>1 s\<^sub>2. ?C s\<^sub>1 s\<^sub>2")
      proof(intro allI)
        fix s\<^sub>1 s\<^sub>2
        have P_rec_sym:"Mprefix (Tr\<^sub>1 s\<^sub>1) (\<lambda>e. P (Up\<^sub>1 s\<^sub>1 e)) = P s\<^sub>1" using P_rec by metis
        have Q_rec_sym:"Mprefix (Tr\<^sub>2 s\<^sub>2) (\<lambda>e. Q (Up\<^sub>2 s\<^sub>2 e)) = Q s\<^sub>2" using Q_rec by metis
        show "?C s\<^sub>1 s\<^sub>2"
          apply(simp add: Tr Up)
          apply(subst P_rec, subst Q_rec, subst mprefix_Par_distr[where C="UNIV", simplified])
          apply(rule mono_mprefix_ref) 
          using step by auto
      qed
    qed
  from dir1 dir2 show ?thesis using below_antisym by blast
qed

section\<open>Consequences\<close>
\<comment>\<open>reachable states from one starting state\<close>
inductive_set \<RR> for Tr ::"'state::type \<Rightarrow> 'event::type set" 
                and Up::"'state \<Rightarrow> 'event \<Rightarrow> 'state" 
                and s\<^sub>0::'state 
  where rbase: "s\<^sub>0 \<in> \<RR> Tr Up s\<^sub>0"
      | rstep: "s \<in> \<RR> Tr Up s\<^sub>0 \<Longrightarrow> e \<in> Tr s  \<Longrightarrow> Up s e \<in> \<RR> Tr Up s\<^sub>0"



\<comment>\<open>Deadlock freeness\<close>
lemma deadlock_free_dnorm_ :
  fixes Tr ::"'state::type \<Rightarrow> 'event::type set" 
    and Up ::"'state \<Rightarrow> 'event \<Rightarrow> 'state" 
    and s\<^sub>0::'state 
  assumes non_reachable_sink: "\<forall>s \<in> \<RR> Tr Up s\<^sub>0. Tr s \<noteq> {}"
  defines P: "P \<equiv> P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr,Up\<rbrakk>" (is "P \<equiv> fix\<cdot>(\<Lambda> X. ?P X)")
  shows  "s \<in> \<RR> Tr Up s\<^sub>0 \<Longrightarrow> deadlock_free_v2 (P s)"
proof(unfold deadlock_free_v2_FD DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def, induct arbitrary:s rule:fix_ind)
  show "adm (\<lambda>a. \<forall>x. x \<in> \<RR> Tr Up s\<^sub>0 \<longrightarrow> a \<sqsubseteq>\<^sub>F\<^sub>D P x)" by (simp add: le_FD_adm monofun_def) 
next
  fix s :: "'state" 
  show "s \<in> \<RR> Tr Up s\<^sub>0 \<Longrightarrow> \<bottom> \<sqsubseteq>\<^sub>F\<^sub>D P s" by simp
next
  fix s :: "'state"  and x :: "'event process"
  have P_rec: "P = ?P P" using fix_eq[of "(\<Lambda> X. ?P X)"] P by simp 
  assume 1 : "\<And>s. s \<in> \<RR> Tr Up s\<^sub>0 \<Longrightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D P s" 
   and   2 : "s \<in> \<RR> Tr Up s\<^sub>0 "
  from   1 2 show "(\<Lambda> x. (\<sqinter>xa\<in>UNIV \<rightarrow>  x) \<sqinter> SKIP)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D P s"
    apply(simp add:failure_divergence_refine_def)
    apply(subst P_rec, rule_tac trans_FD[simplified failure_divergence_refine_def, 
                       rotated, OF Mprefix_refines_Mndet])
    apply(rule_tac CSP.mono_ndet_FD_left)      
    by (metis CSP.mono_ndet_FD_right rstep empty_not_UNIV mndet_distrib mono_mndet_FD 
              non_reachable_sink sup_top_left)
qed



lemmas deadlock_free_dnorm = deadlock_free_dnorm_[rotated, OF rbase, rule_format]

end

