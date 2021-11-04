(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : Example on Structural Parameterisation: Dining Philosophers
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
 * TrHIS SOFTrWARE IS PROVIDED BY TrHE COPYRIGHTr HOLDERS AND CONTrRIBUTrORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTrIES, INCLUDING, BUTr NOTr
 * LIMITrED TrO, TrHE IMPLIED WARRANTrIES OF MERCHANTrABILITrY AND FITrNESS FOR
 * A PARTrICULAR PURPOSE ARE DISCLAIMED. IN NO EVENTr SHALL TrHE COPYRIGHTr
 * OWNER OR CONTrRIBUTrORS BE LIABLE FOR ANY DIRECTr, INDIRECTr, INCIDENTrAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTrIAL DAMAGES (INCLUDING, BUTr NOTr
 * LIMITrED TrO, PROCUREMENTr OF SUBSTrITrUTrE GOODS OR SERVICES; LOSS OF USE,
 * DATrA, OR PROFITrS; OR BUSINESS INTrERRUPTrION) HOWEVER CAUSED AND ON ANY
 * TrHEORY OF LIABILITrY, WHETrHER IN CONTrRACTr, STrRICTr LIABILITrY, OR TrORTr
 * (INCLUDING NEGLIGENCE OR OTrHERWISE) ARISING IN ANY WAY OUTr OF TrHE USE
 * OF TrHIS SOFTrWARE, EVEN IF ADVISED OF TrHE POSSIBILITrY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

section\<open> Generalized Dining Philosophers \<close>

theory     DiningPhilosophers
 imports   "Process_norm"
begin

subsection \<open>Preliminary lemmas for proof automation\<close>

lemma Suc_mod: "n > 1 \<Longrightarrow> i \<noteq> Suc i mod n"
  by (metis One_nat_def mod_Suc mod_if mod_mod_trivial n_not_Suc_n)

lemmas suc_mods = Suc_mod Suc_mod[symmetric]

lemma l_suc: "n > 1 \<Longrightarrow> \<not> n \<le> Suc 0"
  by simp

lemma minus_suc: "n > 0 \<Longrightarrow> n - Suc 0 \<noteq> n"
  by linarith

lemma numeral_4_eq_4:"4 = Suc (Suc (Suc (Suc 0)))"
  by simp

lemma numeral_5_eq_5:"5 = Suc (Suc (Suc (Suc (Suc 0))))"
  by simp

subsection\<open>The dining processes definition\<close>

locale DiningPhilosophers =

  fixes N::nat
  assumes N_g1[simp] : "N > 1"

begin

datatype dining_event  = picks (phil:nat) (fork:nat)
                       | putsdown (phil:nat) (fork:nat)

definition RPHIL::  "nat \<Rightarrow> dining_event process"
 where "RPHIL i = (\<mu> X. (picks i i \<rightarrow> (picks i (i-1) \<rightarrow> (putsdown i (i-1) \<rightarrow> (putsdown i i \<rightarrow> X)))))"

definition LPHIL0::  "dining_event process"
  where "LPHIL0 = (\<mu> X. (picks 0 (N-1) \<rightarrow> (picks 0 0 \<rightarrow> (putsdown 0 0 \<rightarrow> (putsdown 0 (N-1) \<rightarrow> X)))))"

definition FORK  :: "nat \<Rightarrow> dining_event process"
  where "FORK i = (\<mu> X.   (picks i i \<rightarrow> (putsdown i i \<rightarrow> X))
                        \<box> (picks ((i+1) mod N) i \<rightarrow> (putsdown ((i+1) mod N) i \<rightarrow> X)))"


abbreviation "foldPHILs n \<equiv> fold (\<lambda> i P. P ||| RPHIL i) [1..< n] (LPHIL0)"
abbreviation "foldFORKs n \<equiv> fold (\<lambda> i P. P ||| FORK i) [1..< n] (FORK 0)"

abbreviation "PHILs \<equiv> foldPHILs N"
abbreviation "FORKs \<equiv> foldFORKs N"

corollary FORKs_def2: "FORKs = fold (\<lambda> i P. P ||| FORK i) [0..< N] SKIP"
  using N_g1 by (subst (2) upt_rec, auto) (metis (no_types, lifting) Inter_commute Inter_skip1)

corollary "N = 3 \<Longrightarrow> PHILs = (LPHIL0 ||| RPHIL 1 ||| RPHIL 2)"
  by (subst upt_rec, auto simp add:numeral_2_eq_2)+


definition DINING :: "dining_event process"
  where "DINING = (FORKs || PHILs)"

subsubsection \<open>Unfolding rules\<close>

lemma RPHIL_rec:
  "RPHIL i = (picks i i \<rightarrow> (picks i (i-1) \<rightarrow> (putsdown i (i-1) \<rightarrow> (putsdown i i  \<rightarrow> RPHIL i))))"
  by (simp add:RPHIL_def write0_def, subst fix_eq, simp)

lemma LPHIL0_rec:
  "LPHIL0 = (picks 0 (N-1) \<rightarrow> (picks 0 0 \<rightarrow> (putsdown 0 0 \<rightarrow> (putsdown 0 (N-1) \<rightarrow> LPHIL0))))"
  by (simp add:LPHIL0_def write0_def, subst fix_eq, simp)

lemma FORK_rec: "FORK i = (  (picks i i \<rightarrow> (putsdown i i \<rightarrow> (FORK i)))
                          \<box> (picks ((i+1) mod N) i \<rightarrow> (putsdown ((i+1) mod N) i \<rightarrow> (FORK i))))"
  by (simp add:FORK_def write0_def, subst fix_eq, simp)

subsection \<open>Translation into normal form\<close>

lemma N_pos[simp]: "N > 0"
  using N_g1 neq0_conv by blast

lemmas N_pos_simps[simp] = suc_mods[OF N_g1] l_suc[OF N_g1] minus_suc[OF N_pos]

text \<open>The one-fork process\<close>

type_synonym fork_id = nat
type_synonym fork_state = nat

definition fork_transitions:: "fork_id \<Rightarrow> fork_state \<Rightarrow> dining_event set" ("Tr\<^sub>f")
  where "Tr\<^sub>f i s = (if s = 0        then {picks i i} \<union> {picks ((i+1) mod N) i}
                    else if s = 1   then {putsdown i i}
                    else if s = 2   then {putsdown ((i+1) mod N) i}
                    else                 {})"
declare Un_insert_right[simp del] Un_insert_left[simp del]

lemma ev_fork_idx[simp]: "e \<in> Tr\<^sub>f i s \<Longrightarrow> fork e = i"
  by (auto simp add:fork_transitions_def split:if_splits)

definition fork_state_update:: "fork_id \<Rightarrow> fork_state \<Rightarrow> dining_event \<Rightarrow> fork_state" ("Up\<^sub>f")
  where "Up\<^sub>f i s e = ( if e = (picks i i)                   then 1
                      else if e = (picks ((i+1) mod N) i)  then 2
                      else                                      0 )"

definition FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m:: "fork_id \<Rightarrow> fork_state \<Rightarrow> dining_event process"
  where "FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>f i ,Up\<^sub>f i\<rbrakk>"

lemma FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec:  "FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i = (\<lambda> s. \<box> e \<in> (Tr\<^sub>f i s) \<rightarrow> FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i (Up\<^sub>f i s e))"
  using fix_eq[of "\<Lambda> X. (\<lambda>s. Mprefix (Tr\<^sub>f i s) (\<lambda>e. X (Up\<^sub>f i s e)))"] FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def by simp

lemma FORK_refines_FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m: "FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0 \<sqsubseteq> FORK i"
proof(unfold FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
      induct rule:fix_ind_k_skip[where k=2 and f="\<Lambda> x.(\<lambda>s. Mprefix (Tr\<^sub>f i s) (\<lambda>e. x (Up\<^sub>f i s e)))"])
  show "(1::nat) \<le> 2" by simp
next
  show "adm (\<lambda>a. a 0 \<sqsubseteq> FORK i)" by (simp add: cont_fun)
next
  case base_k_steps:3
  show ?case (is "\<forall>j<2. (iterate j\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> FORK i")
  proof -
    have less_2:"\<And>j. (j::nat) < 2 = (j = 0 \<or> j = 1)" by linarith
    moreover have "(iterate 0\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> FORK i" by simp
    moreover have "(iterate 1\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> FORK i"
      by (subst FORK_rec)
         (simp add: write0_def
                    fork_transitions_def
                    mprefix_Un_distr mono_det_ref mono_mprefix_ref)
    ultimately show ?thesis by simp
  qed
next
  case step:(4 x)
  then show ?case (is "(iterate 2\<cdot>?f\<cdot>x) 0 \<sqsubseteq> FORK i")
    by (subst FORK_rec)
       (simp add: write0_def numeral_2_eq_2
                  fork_transitions_def fork_state_update_def
                  mprefix_Un_distr mono_det_ref mono_mprefix_ref)
qed

lemma FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_refines_FORK: "FORK i \<sqsubseteq> FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0"
proof(unfold FORK_def,
      induct rule:fix_ind_k_skip[where k=1])
  show "(1::nat) \<le> 1" by simp
next
  show "adm (\<lambda>a. a \<sqsubseteq> FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0)" by simp
next
  case base_k_steps:3
  show ?case by simp
next
  case step:(4 x)
  then show ?case (is "iterate 1\<cdot>?f\<cdot>x \<sqsubseteq> FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0")
    apply (subst FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec)
    apply (simp add: write0_def
                     fork_transitions_def fork_state_update_def
                     mprefix_Un_distr)
    by (subst (1 2) FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec)
       (simp add: fork_transitions_def fork_state_update_def
                  mprefix_Un_distr mono_det_ref mono_mprefix_ref)
qed

lemma FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_is_FORK: "FORK i = FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0"
  using FORK_refines_FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_refines_FORK below_antisym by blast


text \<open>The all-forks process in normal form\<close>

type_synonym forks_state = "nat list"

definition forks_transitions:: "nat \<Rightarrow> forks_state \<Rightarrow> dining_event set" ("Tr\<^sub>F")
  where "Tr\<^sub>F n fs = (\<Union>i<n. Tr\<^sub>f i (fs!i))"

lemma forks_transitions_take: "Tr\<^sub>F n fs = Tr\<^sub>F n (take n fs)"
  by (simp add:forks_transitions_def)

definition forks_state_update:: "forks_state \<Rightarrow> dining_event \<Rightarrow> forks_state" ("Up\<^sub>F")
  where "Up\<^sub>F fs e = (let i=(fork e) in fs[i:=(Up\<^sub>f i (fs!i) e)])"

lemma forks_update_take: "take n (Up\<^sub>F fs e) = Up\<^sub>F (take n fs) e"
  unfolding forks_state_update_def
  by (metis nat_less_le nat_neq_iff nth_take order_refl take_update_cancel take_update_swap)

definition FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m:: "nat \<Rightarrow> forks_state \<Rightarrow> dining_event process"
  where "FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>F n ,Up\<^sub>F\<rbrakk>"

lemma FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec:  "FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n = (\<lambda> fs. \<box> e \<in> (Tr\<^sub>F n fs) \<rightarrow> FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (Up\<^sub>F fs e))"
  using fix_eq[of "\<Lambda> X. (\<lambda>fs. Mprefix (Tr\<^sub>F n fs) (\<lambda>e. X (Up\<^sub>F fs e)))"] FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def by simp

lemma FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_0: "FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0 fs = STOP"
  by (subst FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add:forks_transitions_def Mprefix_STOP)

lemma FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir1: "length fs > 0 \<Longrightarrow> FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m 1 fs \<sqsubseteq> (FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0 (fs!0))"
proof(unfold FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
      induct arbitrary:fs rule:fix_ind_k[where k=1
                                         and f="\<Lambda> x. (\<lambda>fs. Mprefix (Tr\<^sub>F 1 fs) (\<lambda>e. x (Up\<^sub>F fs e)))"])
  case adm:1
  then show ?case by (simp add:cont_fun)
next
  case base_k_steps:2
  then show ?case by simp
next
  case step:(3 X)
  hence "(\<Union>i<Suc 0. Tr\<^sub>f i (fs ! i)) = Tr\<^sub>f 0 (fs ! 0)" by auto
  with step show ?case
    apply (subst FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add:forks_state_update_def forks_transitions_def)
    apply (intro mono_mprefix_ref, safe)
    by (metis ev_fork_idx step.prems list_update_nonempty nth_list_update_eq)
qed

lemma FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir2: "length fs > 0 \<Longrightarrow> (FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0 (fs!0)) \<sqsubseteq> FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m 1 fs"
proof(unfold FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
      induct arbitrary:fs rule:fix_ind_k[where k=1
                                         and f="\<Lambda> x. (\<lambda>s. Mprefix (Tr\<^sub>f 0 s) (\<lambda>e. x (Up\<^sub>f 0 s e)))"])
  case adm:1
  then show ?case by (simp add:cont_fun)
next
  case base_k_steps:2
  then show ?case by simp
next
  case step:(3 X)
  have "(\<Union>i<Suc 0. Tr\<^sub>f i (fs ! i)) = Tr\<^sub>f 0 (fs ! 0)" by auto
  with step show ?case
    apply (subst FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add:forks_state_update_def forks_transitions_def)
    apply (intro mono_mprefix_ref, safe)
    by (metis ev_fork_idx step.prems list_update_nonempty nth_list_update_eq)
qed

lemma FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1: "length fs > 0 \<Longrightarrow> (FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0 (fs!0)) = FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m 1 fs"
  using FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir1 FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir2 below_antisym by blast

lemma FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_unfold:
"0 < n \<Longrightarrow> length fs = Suc n \<Longrightarrow>
                              FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) fs = (FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (butlast fs)|||(FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (fs!n)))"
proof(rule below_antisym)
  show "0 < n \<Longrightarrow> length fs = Suc n \<Longrightarrow>
                               FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) fs \<sqsubseteq> (FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (butlast fs)|||FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (fs!n))"
  proof(subst FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
        induct arbitrary:fs
               rule:fix_ind_k[where k=1
                              and f="\<Lambda> x. (\<lambda>fs. Mprefix (Tr\<^sub>F (Suc n) fs) (\<lambda>e. x (Up\<^sub>F fs e)))"])
    case adm:1
    then show ?case by (simp add:cont_fun)
  next
    case base_k_steps:2
    then show ?case by simp
  next
    case step:(3 X)
    have indep:"\<forall>s\<^sub>1 s\<^sub>2. Tr\<^sub>F n s\<^sub>1 \<inter> Tr\<^sub>f n s\<^sub>2 = {}"
      by (auto simp add:forks_transitions_def fork_transitions_def)
    from step show ?case
      apply (auto simp add:indep dnorm_inter FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def)
      apply (subst fix_eq, simp add:forks_transitions_def Un_commute lessThan_Suc nth_butlast)
    proof(rule mono_mprefix_ref, safe, goal_cases)
      case (1 e)
      from 1(4) have a:"fork e = n"
        by (auto simp add:fork_transitions_def split:if_splits)
      show ?case
        using 1(1)[rule_format, of "(Up\<^sub>F fs e)"]
        apply (simp add: 1 a butlast_list_update forks_state_update_def)
        by (metis 1(4) ev_fork_idx lessThan_iff less_not_refl)
    next
      case (2 e m)
      hence a:"e \<notin> Tr\<^sub>f n (fs ! n)"
        using ev_fork_idx by fastforce
      hence c:"Up\<^sub>F fs e ! n = fs ! n"
        by (metis 2(4) ev_fork_idx forks_state_update_def nth_list_update_neq)
      have d:"Up\<^sub>F (butlast fs) e = butlast (Up\<^sub>F fs e)"
        apply(simp add:forks_state_update_def)
        by (metis butlast_conv_take forks_state_update_def forks_update_take length_list_update)
      from 2 a show ?case
        using 2(1)[rule_format, of "(Up\<^sub>F fs e)"] c d forks_state_update_def by auto
    qed
  qed
next
  have indep:"\<forall>s\<^sub>1 s\<^sub>2. Tr\<^sub>F n s\<^sub>1 \<inter> Tr\<^sub>f n s\<^sub>2 = {}"
    by (auto simp add:forks_transitions_def fork_transitions_def)
  show "0 < n \<Longrightarrow> length fs = Suc n \<Longrightarrow>
                              (FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (butlast fs)|||FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (fs!n)) \<sqsubseteq> FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) fs"
    apply (subst FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def, auto simp add:indep dnorm_inter FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def)
  proof(rule fix_ind[where
        P="\<lambda>a. 0 < n \<longrightarrow> (\<forall>x. length x = Suc n \<longrightarrow> a (butlast x, x ! n) \<sqsubseteq> FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) x)",
        rule_format], simp_all, goal_cases)
    case base:1
    then show ?case by (simp add:cont_fun)
  next
    case step:(2 X fs)
    then show ?case
      apply (unfold FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def, subst fix_eq, simp add:forks_transitions_def
                                                          Un_commute lessThan_Suc nth_butlast)
    proof(rule mono_mprefix_ref, safe, goal_cases)
      case (1 e)
      from 1(6) have a:"fork e = n"
        by (auto simp add:fork_transitions_def split:if_splits)
      show ?case
        using 1(1)[rule_format, of "(Up\<^sub>F fs e)"]
        apply (simp add: 1 a butlast_list_update forks_state_update_def)
        using a ev_fork_idx by blast
    next
      case (2 e m)
      have a:"Up\<^sub>F (butlast fs) e = butlast (Up\<^sub>F fs e)"
        apply(simp add:forks_state_update_def)
        by (metis butlast_conv_take forks_state_update_def forks_update_take length_list_update)
      from 2 show ?case
        using 2(1)[rule_format, of "(Up\<^sub>F fs e)"] a forks_state_update_def by auto
    qed
  qed
qed

lemma ft: "0 < n \<Longrightarrow> FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (replicate n 0) = foldFORKs n"
proof (induct n, simp)
  case (Suc n)
  then show ?case
    apply (auto simp add: FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_unfold FORK\<^sub>n\<^sub>o\<^sub>r\<^sub>m_is_FORK)
    apply (metis Suc_le_D butlast_snoc replicate_Suc replicate_append_same)
    by (metis FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1 One_nat_def leI length_replicate less_Suc0 nth_replicate replicate_Suc)
qed

corollary FORKs_is_FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m: "FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m N (replicate N 0) = FORKs"
  using ft N_pos by simp

text \<open>The one-philosopher process in normal form:\<close>

type_synonym phil_id = nat
type_synonym phil_state = nat

definition rphil_transitions:: "phil_id \<Rightarrow> phil_state \<Rightarrow> dining_event set" ("Tr\<^sub>r\<^sub>p")
  where "Tr\<^sub>r\<^sub>p i s = ( if      s = 0  then {picks i i}
                     else if s = 1  then {picks i (i-1)}
                     else if s = 2  then {putsdown i (i-1)}
                     else if s = 3  then {putsdown i i}
                     else                {})"

definition lphil0_transitions:: "phil_state \<Rightarrow> dining_event set" ("Tr\<^sub>l\<^sub>p")
    where "Tr\<^sub>l\<^sub>p s = ( if s = 0       then {picks 0 (N-1)}
                     else if s = 1  then {picks 0 0}
                     else if s = 2  then {putsdown 0 0}
                     else if s = 3  then {putsdown 0 (N-1)}
                     else                {})"

corollary rphil_phil: "e \<in> Tr\<^sub>r\<^sub>p i s \<Longrightarrow> phil e = i"
      and lphil0_phil: "e \<in> Tr\<^sub>l\<^sub>p s \<Longrightarrow> phil e = 0"
  by (simp_all add:rphil_transitions_def lphil0_transitions_def split:if_splits)

definition rphil_state_update:: "fork_id \<Rightarrow> fork_state \<Rightarrow> dining_event \<Rightarrow> fork_state" ("Up\<^sub>r\<^sub>p")
  where "Up\<^sub>r\<^sub>p i s e = ( if e = (picks i i)               then 1
                       else if e = (picks i (i-1))      then 2
                       else if e = (putsdown i (i-1))   then 3
                       else                                  0 )"

definition lphil0_state_update:: "fork_state \<Rightarrow> dining_event \<Rightarrow> fork_state" ("Up\<^sub>l\<^sub>p")
  where "Up\<^sub>l\<^sub>p s e = ( if e = (picks 0 (N-1))         then 1
                     else if e = (picks 0 0)        then 2
                     else if e = (putsdown 0 0)     then 3
                     else                                0 )"

definition RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m:: "fork_id \<Rightarrow> fork_state \<Rightarrow> dining_event process"
  where "RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m i = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>r\<^sub>p i,Up\<^sub>r\<^sub>p i\<rbrakk>"

definition LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m:: "fork_state \<Rightarrow> dining_event process"
  where "LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>l\<^sub>p,Up\<^sub>l\<^sub>p\<rbrakk>"

lemma RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec:  "RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m i = (\<lambda> s. \<box> e \<in> (Tr\<^sub>r\<^sub>p i s) \<rightarrow> RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m i (Up\<^sub>r\<^sub>p i s e))"
  using fix_eq[of "\<Lambda> X. (\<lambda>s. Mprefix (Tr\<^sub>r\<^sub>p i s) (\<lambda>e. X (Up\<^sub>r\<^sub>p i s e)))"] RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def by simp

lemma LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec:  "LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m = (\<lambda> s. \<box> e \<in> (Tr\<^sub>l\<^sub>p s) \<rightarrow> LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Up\<^sub>l\<^sub>p s e))"
  using fix_eq[of "\<Lambda> X. (\<lambda>s. Mprefix (Tr\<^sub>l\<^sub>p s) (\<lambda>e. X (Up\<^sub>l\<^sub>p s e)))"] LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def by simp

lemma RPHIL_refines_RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m:
  assumes i_pos: "i > 0"
  shows "RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0 \<sqsubseteq> RPHIL i"
proof(unfold RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
      induct rule:fix_ind_k_skip[where k=4
                                 and f="\<Lambda> x. (\<lambda>s. Mprefix (Tr\<^sub>r\<^sub>p i s) (\<lambda>e. x (Up\<^sub>r\<^sub>p i s e)))"])
  show "(1::nat) \<le> 4" by simp
next
  show "adm (\<lambda>a. a 0 \<sqsubseteq> RPHIL i)" by (simp add: cont_fun)
next
  case base_k_steps:3
  show ?case (is "\<forall>j<4. (iterate j\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> RPHIL i")
  proof -
    have less_2:"\<And>j. (j::nat) < 4 = (j = 0 \<or> j = 1  \<or> j = 2  \<or> j = 3)" by linarith
    moreover have "(iterate 0\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> RPHIL i" by simp
    moreover have "(iterate 1\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> RPHIL i"
      by (subst RPHIL_rec)
         (simp add: write0_def rphil_transitions_def mono_mprefix_ref)
    moreover have "(iterate 2\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> RPHIL i"
      by (subst RPHIL_rec)
         (simp add: numeral_2_eq_2 write0_def rphil_transitions_def
                    rphil_state_update_def mono_mprefix_ref)
    moreover have "(iterate 3\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> RPHIL i"
      by (subst RPHIL_rec)
         (simp add: numeral_3_eq_3 write0_def rphil_transitions_def
                    rphil_state_update_def mono_mprefix_ref minus_suc[OF i_pos])
    ultimately show ?thesis by simp
  qed
next
  case step:(4 x)
  then show ?case (is "(iterate 4\<cdot>?f\<cdot>x) 0 \<sqsubseteq> RPHIL i")
    apply (subst RPHIL_rec)
    apply (simp add: write0_def numeral_4_eq_4 rphil_transitions_def rphil_state_update_def)
    apply (rule mono_mprefix_ref, auto simp:minus_suc[OF i_pos])+
    using minus_suc[OF i_pos] by auto
qed

lemma LPHIL0_refines_LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m: "LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0 \<sqsubseteq> LPHIL0"
proof(unfold LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
      induct rule:fix_ind_k_skip[where k=4 and f="\<Lambda> x. (\<lambda>s. Mprefix (Tr\<^sub>l\<^sub>p s) (\<lambda>e. x (Up\<^sub>l\<^sub>p s e)))"])
  show "(1::nat) \<le> 4" by simp
next
  show "adm (\<lambda>a. a 0 \<sqsubseteq> LPHIL0)" by (simp add: cont_fun)
next
  case base_k_steps:3
  show ?case (is "\<forall>j<4. (iterate j\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> LPHIL0")
  proof -
    have less_2:"\<And>j. (j::nat) < 4 = (j = 0 \<or> j = 1  \<or> j = 2  \<or> j = 3)" by linarith
    moreover have "(iterate 0\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> LPHIL0" by simp
    moreover have "(iterate 1\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> LPHIL0"
      by (subst LPHIL0_rec)
         (simp add: write0_def lphil0_transitions_def mono_mprefix_ref)
    moreover have "(iterate 2\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> LPHIL0"
      by (subst LPHIL0_rec)
         (simp add: numeral_2_eq_2 write0_def lphil0_transitions_def
                    lphil0_state_update_def mono_mprefix_ref)
    moreover have "(iterate 3\<cdot>?f\<cdot>\<bottom>) 0 \<sqsubseteq> LPHIL0"
      by (subst LPHIL0_rec)
         (simp add: numeral_3_eq_3 write0_def lphil0_transitions_def
                    lphil0_state_update_def mono_mprefix_ref)
    ultimately show ?thesis by simp
  qed
next
  case step:(4 x)
  then show ?case (is "(iterate 4\<cdot>?f\<cdot>x) 0 \<sqsubseteq> LPHIL0")
    by (subst LPHIL0_rec)
       (simp add: write0_def numeral_4_eq_4 lphil0_transitions_def
                  lphil0_state_update_def mono_mprefix_ref)
qed

lemma RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_refines_RPHIL:
  assumes i_pos: "i > 0"
  shows "RPHIL i \<sqsubseteq> RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0"
proof(unfold RPHIL_def,
      induct rule:fix_ind_k_skip[where k=1])
  show "(1::nat) \<le> 1" by simp
next
  show "adm (\<lambda>a. a \<sqsubseteq> RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0)" by simp
next
  case base_k_steps:3
  show ?case by simp
next
  case step:(4 x)
  then show ?case
    apply (subst RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def rphil_transitions_def rphil_state_update_def)
    apply (rule mono_mprefix_ref, simp)
    apply (subst RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def rphil_transitions_def rphil_state_update_def)
    apply (rule mono_mprefix_ref, simp add:minus_suc[OF i_pos])
    apply (subst RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def rphil_transitions_def rphil_state_update_def)
    apply (rule mono_mprefix_ref, simp add:minus_suc[OF i_pos])
    apply (subst RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def rphil_transitions_def rphil_state_update_def)
    apply (rule mono_mprefix_ref, simp add:minus_suc[OF i_pos])
    using minus_suc[OF i_pos] by auto
qed

lemma LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_refines_LPHIL0: "LPHIL0 \<sqsubseteq> LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0"
proof(unfold LPHIL0_def,
      induct rule:fix_ind_k_skip[where k=1])
  show "(1::nat) \<le> 1" by simp
next
  show "adm (\<lambda>a. a \<sqsubseteq> LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0)" by simp
next
  case base_k_steps:3
  show ?case by simp
next
  case step:(4 x)
  then show ?case (is "iterate 1\<cdot>?f\<cdot>x \<sqsubseteq> LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0")
    apply (subst LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def lphil0_transitions_def lphil0_state_update_def)
    apply (rule mono_mprefix_ref, simp)
    apply (subst LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def lphil0_transitions_def lphil0_state_update_def)
    apply (rule mono_mprefix_ref, simp)
    apply (subst LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def lphil0_transitions_def lphil0_state_update_def)
    apply (rule mono_mprefix_ref, simp)
    apply (subst LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add: write0_def lphil0_transitions_def lphil0_state_update_def)
    apply (rule mono_mprefix_ref, simp)
    done
qed

lemma RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_is_RPHIL: "i > 0 \<Longrightarrow> RPHIL i = RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m i 0"
  using RPHIL_refines_RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_refines_RPHIL below_antisym by blast

lemma LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_is_LPHIL0: "LPHIL0 = LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m 0"
  using LPHIL0_refines_LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_refines_LPHIL0 below_antisym by blast

subsection \<open>The normal form for the global philosopher network\<close>

type_synonym phils_state = "nat list"

definition phils_transitions:: "nat \<Rightarrow> phils_state \<Rightarrow> dining_event set" ("Tr\<^sub>P")
  where "Tr\<^sub>P n ps = Tr\<^sub>l\<^sub>p (ps!0) \<union> (\<Union>i\<in>{1..< n}. Tr\<^sub>r\<^sub>p i (ps!i))"

corollary phils_phil: "0 < n \<Longrightarrow> e \<in> Tr\<^sub>P n s \<Longrightarrow> phil e < n"
  by (auto simp add:phils_transitions_def lphil0_phil rphil_phil)

lemma phils_transitions_take: "0 < n \<Longrightarrow> Tr\<^sub>P n ps = Tr\<^sub>P n (take n ps)"
  by (auto simp add:phils_transitions_def)

definition phils_state_update:: "phils_state \<Rightarrow> dining_event \<Rightarrow> phils_state" ("Up\<^sub>P")
  where "Up\<^sub>P ps e = (let i=(phil e) in if i = 0 then ps[i:=(Up\<^sub>l\<^sub>p (ps!i) e)]
                                       else          ps[i:=(Up\<^sub>r\<^sub>p i (ps!i) e)])"

lemma phils_update_take: "take n (Up\<^sub>P ps e) = Up\<^sub>P (take n ps) e"
  by (cases e) (simp_all add: phils_state_update_def lphil0_state_update_def
                              rphil_state_update_def take_update_swap)

definition PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m:: "nat \<Rightarrow> phils_state \<Rightarrow> dining_event process"
  where "PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>P n,Up\<^sub>P\<rbrakk>"

lemma PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec:  "PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n = (\<lambda> ps. \<box> e \<in> (Tr\<^sub>P n ps) \<rightarrow> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (Up\<^sub>P ps e))"
  using fix_eq[of "\<Lambda> X. (\<lambda>ps. Mprefix (Tr\<^sub>P n ps) (\<lambda>e. X (Up\<^sub>P ps e)))"] PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def by simp

lemma PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir1: "length ps > 0 \<Longrightarrow> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m 1 ps \<sqsubseteq> (LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m (ps!0))"
proof(unfold PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
      induct arbitrary:ps
             rule:fix_ind_k[where k=1
                            and f="\<Lambda> x. (\<lambda>ps. Mprefix (Tr\<^sub>P 1 ps) (\<lambda>e. x (Up\<^sub>P ps e)))"])
  case adm:1
  then show ?case by (simp add:cont_fun)
next
  case base_k_steps:2
  then show ?case by simp
next
  case step:(3 X)
  then show ?case
    apply (subst LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add:phils_state_update_def phils_transitions_def)
    proof (intro mono_mprefix_ref, safe, goal_cases)
      case (1 e)
      with 1(2) show ?case
        using 1(1)[rule_format, of "ps[0 := Up\<^sub>l\<^sub>p (ps ! 0) e]"]
        by (simp add:lphil0_transitions_def split:if_splits)
    qed
qed

lemma PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir2: "length ps > 0 \<Longrightarrow> (LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m (ps!0)) \<sqsubseteq> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m 1 ps"
proof(unfold LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
      induct arbitrary:ps rule:fix_ind_k[where k=1
                                         and f="\<Lambda> x. (\<lambda>s. Mprefix (Tr\<^sub>l\<^sub>p s) (\<lambda>e. x (Up\<^sub>l\<^sub>p s e)))"])
  case adm:1
  then show ?case by (simp add:cont_fun)
next
  case base_k_steps:2
  then show ?case by simp
next
  case step:(3 X)
  then show ?case
    apply (subst PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_rec, simp add:phils_state_update_def phils_transitions_def)
    proof (intro mono_mprefix_ref, safe, goal_cases)
      case (1 e)
      with 1(2) show ?case
        using 1(1)[rule_format, of "ps[0 := Up\<^sub>l\<^sub>p (ps ! 0) e]"]
        by (simp add:lphil0_transitions_def split:if_splits)
    qed
qed

lemma PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1: "length ps > 0 \<Longrightarrow> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m 1 ps = (LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m (ps!0))"
  using PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir1 PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1_dir2 below_antisym by blast

lemma PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_unfold:
  assumes n_pos:"0 < n"
  shows "length ps = Suc n \<Longrightarrow>
                            PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) ps = (PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (butlast ps)|||(RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (ps!n)))"
proof(rule below_antisym)
  show "length ps = Suc n \<Longrightarrow> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) ps \<sqsubseteq> (PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (butlast ps)|||RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (ps!n))"
  proof(subst PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def,
        induct arbitrary:ps
               rule:fix_ind_k[where k=1
                              and f="\<Lambda> x. (\<lambda>ps. Mprefix (Tr\<^sub>P (Suc n) ps) (\<lambda>e. x (Up\<^sub>P ps e)))"])
    case adm:1
    then show ?case by (simp add:cont_fun)
  next
    case base_k_steps:2
    then show ?case by simp
  next
    case step:(3 X)
    have indep:"\<forall>s\<^sub>1 s\<^sub>2. Tr\<^sub>P n s\<^sub>1 \<inter> Tr\<^sub>r\<^sub>p n s\<^sub>2 = {}"
      using phils_phil rphil_phil n_pos by blast
    from step have tra:"(Tr\<^sub>P (Suc n) ps) =(Tr\<^sub>P n (butlast ps) \<union> Tr\<^sub>r\<^sub>p n (ps ! n))"
      by (auto simp add:n_pos phils_transitions_def nth_butlast Suc_leI
                        atLeastLessThanSuc Un_commute Un_assoc)
    from step show ?case
      apply (auto simp add:indep dnorm_inter PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def)
      apply (subst fix_eq, auto simp add:tra)
    proof(rule mono_mprefix_ref, safe, goal_cases)
      case (1 e)
      hence c:"Up\<^sub>P ps e ! n = ps ! n"
        using 1(3) phils_phil phils_state_update_def step n_pos
        by (cases "phil e", auto) (metis exists_least_iff nth_list_update_neq)
      have d:"Up\<^sub>P (butlast ps) e = butlast (Up\<^sub>P ps e)"
        by (cases "phil e", auto simp add:phils_state_update_def butlast_list_update
                                          lphil0_state_update_def rphil_state_update_def)
      have e:"length (Up\<^sub>P ps e) = Suc n"
        by (metis (full_types) step(2) length_list_update phils_state_update_def)
      from 1 show ?case
        using 1(1)[rule_format, of "(Up\<^sub>P ps e)"] c d e by auto
    next
      case (2 e)
      have e:"length (Up\<^sub>P ps e) = Suc n"
        by (metis (full_types) step(2) length_list_update phils_state_update_def)
      from 2 show ?case
        using 2(1)[rule_format, of "(Up\<^sub>P ps e)", OF e] n_pos
        apply(auto simp add: butlast_list_update rphil_phil phils_state_update_def)
        by (meson disjoint_iff_not_equal indep)
    qed
  qed
next
  have indep:"\<forall>s\<^sub>1 s\<^sub>2. Tr\<^sub>P n s\<^sub>1 \<inter> Tr\<^sub>r\<^sub>p n s\<^sub>2 = {}"
    using phils_phil rphil_phil using n_pos by blast

  show "length ps = Suc n \<Longrightarrow> (PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (butlast ps)|||RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (ps!n)) \<sqsubseteq> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) ps"
    apply (subst PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def, auto simp add:indep dnorm_inter RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def)
  proof(rule fix_ind[where
        P="\<lambda>a. \<forall>x. length x = Suc n \<longrightarrow> a (butlast x, x ! n) \<sqsubseteq> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m (Suc n) x", rule_format],
        simp_all, goal_cases base step)
    case base
    then show ?case by (simp add:cont_fun)
  next
    case (step X ps)
    hence tra:"(Tr\<^sub>P (Suc n) ps) =(Tr\<^sub>P n (butlast ps) \<union> Tr\<^sub>r\<^sub>p n (ps ! n))"
      by (auto simp add:n_pos phils_transitions_def nth_butlast
                        Suc_leI atLeastLessThanSuc Un_commute Un_assoc)
    from step show ?case
      apply (auto simp add:indep dnorm_inter PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def)
      apply (subst fix_eq, auto simp add:tra)
    proof(rule mono_mprefix_ref, safe, goal_cases)
      case (1 e)
      hence c:"Up\<^sub>P ps e ! n = ps ! n"
        using 1(3) phils_phil phils_state_update_def step n_pos
        by (cases "phil e", auto) (metis exists_least_iff nth_list_update_neq)
      have d:"Up\<^sub>P (butlast ps) e = butlast (Up\<^sub>P ps e)"
        by (cases "phil e", auto simp add:phils_state_update_def butlast_list_update
                                          lphil0_state_update_def rphil_state_update_def)
      have e:"length (Up\<^sub>P ps e) = Suc n"
        by (metis (full_types) step(3) length_list_update phils_state_update_def)
      from 1 show ?case
        using 1(2)[rule_format, of "(Up\<^sub>P ps e)", OF e] c d by auto
    next
      case (2 e)
      have e:"length (Up\<^sub>P ps e) = Suc n"
        by (metis (full_types) 2(3) length_list_update phils_state_update_def)
      from 2 show ?case
        using 2(2)[rule_format, of "(Up\<^sub>P ps e)", OF e] n_pos
        apply(auto simp add: butlast_list_update rphil_phil phils_state_update_def)
        by (meson disjoint_iff_not_equal indep)
    qed
  qed
qed

lemma pt: "0 < n \<Longrightarrow> PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (replicate n 0) = foldPHILs n"
proof (induct n, simp)
  case (Suc n)
  then show ?case
    apply (auto simp add: PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_unfold LPHIL0\<^sub>n\<^sub>o\<^sub>r\<^sub>m_is_LPHIL0)
     apply (metis Suc_le_eq butlast.simps(2) butlast_snoc RPHIL\<^sub>n\<^sub>o\<^sub>r\<^sub>m_is_RPHIL
                    nat_neq_iff replicate_append_same replicate_empty)
    by (metis One_nat_def leI length_replicate less_Suc0 PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_1 nth_Cons_0 replicate_Suc)
qed

corollary PHILs_is_PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m: "PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m N (replicate N 0) = PHILs"
  using pt N_pos by simp

subsection \<open>The complete process system under normal form\<close>

definition dining_transitions:: "nat \<Rightarrow> phils_state \<times> forks_state \<Rightarrow> dining_event set" ("Tr\<^sub>D")
  where "Tr\<^sub>D n = (\<lambda>(ps,fs). (Tr\<^sub>P n ps) \<inter> (Tr\<^sub>F n fs))"

definition dining_state_update::
  "phils_state \<times> forks_state \<Rightarrow> dining_event \<Rightarrow> phils_state \<times> forks_state" ("Up\<^sub>D")
  where "Up\<^sub>D = (\<lambda>(ps,fs) e. (Up\<^sub>P ps e, Up\<^sub>F fs e))"

definition DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m:: "nat \<Rightarrow> phils_state \<times> forks_state \<Rightarrow> dining_event process"
  where "DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m n = P\<^sub>n\<^sub>o\<^sub>r\<^sub>m\<lbrakk>Tr\<^sub>D n, Up\<^sub>D\<rbrakk>"

lemma ltsDining_rec:  "DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m n = (\<lambda> s. \<box> e \<in> (Tr\<^sub>D n s) \<rightarrow> DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m n (Up\<^sub>D s e))"
  using fix_eq[of "\<Lambda> X. (\<lambda>s. Mprefix (Tr\<^sub>D n s) (\<lambda>e. X (Up\<^sub>D s e)))"] DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def by simp

lemma DINING_is_DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m: "DINING = DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m N (replicate N 0, replicate N 0)"
proof -
  have "DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m N (replicate N 0, replicate N 0) =
                                        (PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m N (replicate N 0) || FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m N (replicate N 0))"
    unfolding DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def dining_transitions_def
              dining_state_update_def dnorm_par by simp
  thus ?thesis
    using PHILs_is_PHILs\<^sub>n\<^sub>o\<^sub>r\<^sub>m FORKs_is_FORKs\<^sub>n\<^sub>o\<^sub>r\<^sub>m DINING_def
    by (simp add: par_comm)
qed

subsection \<open>And finally: Philosophers may dine ! Always !\<close>

corollary lphil_states:"Up\<^sub>l\<^sub>p r e = 0 \<or> Up\<^sub>l\<^sub>p r e = 1 \<or> Up\<^sub>l\<^sub>p r e = 2 \<or> Up\<^sub>l\<^sub>p r e = 3"
      and rphil_states:"Up\<^sub>r\<^sub>p i r e = 0 \<or> Up\<^sub>r\<^sub>p i r e = 1 \<or> Up\<^sub>r\<^sub>p i r e = 2 \<or> Up\<^sub>r\<^sub>p i r e = 3"
  unfolding lphil0_state_update_def rphil_state_update_def by auto

lemma dining_events:
"e \<in> Tr\<^sub>D N s \<Longrightarrow>
        (\<exists>i\<in>{1..<N}. e = picks i i \<or> e = picks i (i-1)  \<or> e = putsdown i i \<or> e = putsdown i (i-1))
     \<or> (e = picks 0 0 \<or> e = picks 0 (N-1) \<or> e = putsdown 0 0 \<or> e = putsdown 0 (N-1))"
  by (auto simp add:dining_transitions_def phils_transitions_def rphil_transitions_def
                    lphil0_transitions_def split:prod.splits if_splits)

definition "inv_dining ps fs \<equiv>
            (\<forall>i. Suc i < N \<longrightarrow>  ((fs!(Suc i) = 1) \<longleftrightarrow> ps!Suc i \<noteq> 0)) \<and> (fs!(N-1) = 2 \<longleftrightarrow> ps!0 \<noteq> 0)
          \<and> (\<forall>i < N - 1.                 fs!i = 2 \<longleftrightarrow>  ps!Suc i = 2)  \<and>   (fs!0 = 1 \<longleftrightarrow> ps!0 = 2)
          \<and> (\<forall>i < N. fs!i = 0 \<or> fs!i = 1 \<or> fs!i = 2)
          \<and> (\<forall>i < N. ps!i = 0 \<or> ps!i = 1 \<or> ps!i = 2 \<or> ps!i = 3)
          \<and> length fs = N \<and> length ps = N"

lemma inv_DINING: "s \<in> \<RR> (Tr\<^sub>D N) Up\<^sub>D (replicate N 0, replicate N 0) \<Longrightarrow> inv_dining (fst s) (snd s)"
proof(induct rule:\<RR>.induct)
  case rbase
  show ?case
    unfolding inv_dining_def
    by (simp add:dining_transitions_def phils_transitions_def forks_transitions_def
                 lphil0_transitions_def rphil_transitions_def fork_transitions_def)
next
  case (rstep s e)
  from rstep(2,3) show ?case
    apply(auto simp add:dining_transitions_def phils_transitions_def forks_transitions_def
                       lphil0_transitions_def rphil_transitions_def fork_transitions_def
                       lphil0_state_update_def rphil_state_update_def fork_state_update_def
                       dining_state_update_def phils_state_update_def forks_state_update_def
                   split:if_splits prod.split)
    unfolding inv_dining_def
  proof(goal_cases)
    case (1 ps fs)
    then show ?case
      by (simp add:nth_list_update) force
  next
    case (2 ps fs)
    then show ?case
      by (auto simp add:nth_list_update)
  next
    case (3 ps fs)
    then show ?case
      using N_g1 by auto
  next
    case (4 ps fs)
    then show ?case
      by (simp add:nth_list_update) force
  next
    case (5 ps fs)
    then show ?case
      using N_g1 by linarith
  next
    case (6 ps fs)
    then show ?case
      by (auto simp add:nth_list_update)
  next
    case (7 ps fs i)
    then show ?case
      apply (simp add:nth_list_update, intro impI conjI, simp_all)
      by  auto[1] (metis N_pos Suc_pred less_antisym, metis zero_neq_numeral)
  next
    case (8 ps fs i)
    then show ?case
      apply (simp add:nth_list_update, intro impI conjI allI, simp_all)
      by (metis "8"(1) zero_neq_one)+
  next
    case (9 ps fs i)
    then show ?case
      apply (simp add:nth_list_update, intro impI conjI allI, simp_all)
      by (metis N_pos Suc_pred less_antisym) (metis n_not_Suc_n numeral_2_eq_2)
  next
    case (10 ps fs i)
    then show ?case
      apply (simp add:nth_list_update, intro impI conjI allI, simp_all)
      by (metis "10"(1) "10"(5) One_nat_def n_not_Suc_n numeral_2_eq_2)+
  qed
qed

lemma inv_implies_DF:"inv_dining ps fs \<Longrightarrow> Tr\<^sub>D N (ps, fs) \<noteq> {}"
  unfolding inv_dining_def
  apply(simp add:dining_transitions_def phils_transitions_def forks_transitions_def
                 lphil0_transitions_def
             split: if_splits prod.splits)
proof(elim conjE, intro conjI impI, goal_cases)
  case 1
  hence "putsdown 0 (N - Suc 0) \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
     by (auto simp add:fork_transitions_def)
  then show ?case
    by blast
next
  case 2
  hence "putsdown 0 0 \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
     by (auto simp add:fork_transitions_def)
  then show ?case
    by (simp add:fork_transitions_def) force
next
  case 3
  hence a:"fs!0 = 0 \<Longrightarrow> picks 0 0 \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
     by (auto simp add:fork_transitions_def)
  from 3 have b1:"ps!1 = 2 \<Longrightarrow> putsdown 1 0 \<in> (\<Union>x\<in>{Suc 0..<N}. Tr\<^sub>r\<^sub>p x (ps ! x))"
    using N_g1 by (auto simp add:rphil_transitions_def)
  from 3 have b2:"fs!0 = 2 \<Longrightarrow> putsdown 1 0 \<in> Tr\<^sub>f 0 (fs ! 0)"
    using N_g1 by (auto simp add:fork_transitions_def) fastforce
  from 3 have c:"fs!0 \<noteq> 0 \<Longrightarrow> ps!1 = 2"
    by (metis N_pos N_pos_simps(3) One_nat_def diff_is_0_eq neq0_conv)
  from 3 have d:"fs!0 \<noteq> 0 \<Longrightarrow> fs!0 = 2"
    using N_pos by meson
  then show ?case
    apply(cases "fs!0 = 0")
    using a apply (simp add: fork_transitions_def Un_insert_left)
    using b1[OF c] b2[OF d] N_pos by blast
next
  case 4
  then show ?case
    using 4(5)[rule_format, of 0, OF N_pos] apply(elim disjE)
  proof(goal_cases)
    case 41:1 (* fs!0 = 0 *)
    then show ?case
    using 4(5)[rule_format, of 1, OF N_g1] apply(elim disjE)
    proof(goal_cases)
      case 411:1 (* fs!1 = 0 *)
      from 411 have a0: "ps!1 = 0"
        by (metis N_g1 One_nat_def neq0_conv)
      from 411 have a1: "picks 1 1 \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
        apply (auto simp add:fork_transitions_def)
        by (metis (mono_tags, lifting) N_g1 Int_Collect One_nat_def lessThan_iff)
      from 411 have a2: "ps!1 = 0 \<Longrightarrow> picks 1 1 \<in> (\<Union>i\<in>{Suc 0..<N}. Tr\<^sub>r\<^sub>p i (ps ! i))"
        apply (auto simp add:rphil_transitions_def)
        using N_g1 by linarith
      from 411 show ?case
        using a0 a1 a2 by blast
    next
      case 412:2 (* fs!1 = 1 *)
      hence "ps!1 = 1 \<or> ps!1 = 3"
        by (metis N_g1 One_nat_def less_numeral_extra(3) zero_less_diff)
      with 412 show ?case
      proof(elim disjE, goal_cases)
        case 4121:1 (* ps!1 = 1 *)
        from 4121 have b1: "picks 1 0 \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
          apply (auto simp add:fork_transitions_def)
          by (metis (full_types) Int_Collect N_g1 N_pos One_nat_def lessThan_iff mod_less)
        from 4121 have b2: "picks 1 0 \<in> (\<Union>i\<in>{Suc 0..<N}. Tr\<^sub>r\<^sub>p i (ps ! i))"
          apply (auto simp add:rphil_transitions_def)
          using N_g1 by linarith
        from 4121 show ?case
          using b1 b2 by blast
      next
        case 4122:2 (* ps!1 = 3 *)
        from 4122 have b3: "putsdown 1 1 \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
          apply (auto simp add:fork_transitions_def)
          using N_g1 by linarith
        from 4122 have b4: "putsdown 1 1 \<in> (\<Union>i\<in>{Suc 0..<N}. Tr\<^sub>r\<^sub>p i (ps ! i))"
          apply (auto simp add:rphil_transitions_def)
          using N_g1 by linarith
        then show ?case
          using b3 b4 by blast
      qed
    next
      case 413:3 (* fs!1 = 2 *)
      then show ?case
      proof(cases "N = 2")
        case True
        with 413 show ?thesis by simp
      next
        case False
        from False 413 have c0: "ps!2 = 2"
          by (metis N_g1 Suc_1 Suc_diff_1 nat_neq_iff not_gr0 zero_less_diff)
        from False 413 have c1: "putsdown 2 1 \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
          apply (auto simp add:fork_transitions_def)
          using N_g1 apply linarith
          using N_g1 by auto
        from False 413 have c2: "ps!2 = 2 \<Longrightarrow> putsdown 2 1 \<in> (\<Union>i\<in>{Suc 0..<N}. Tr\<^sub>r\<^sub>p i (ps ! i))"
          apply (auto simp add:rphil_transitions_def)
          using N_g1 by linarith
        from 413 False show ?thesis
          using c0 c1 c2 by blast
      qed
    qed
  next
    case 42:2 (* fs!0 = 1 *)
    then show ?case by blast
  next
    case 43:3 (* fs!0 = 2*)
    from 43 have d0: "ps!1 = 2"
      by (metis One_nat_def gr0I)
    from 43 have d1: "putsdown 1 0 \<in> (\<Union>i<N. Tr\<^sub>f i (fs ! i))"
      by (auto simp add:fork_transitions_def)
    from 43 have d2: "ps!1 = 2 \<Longrightarrow> putsdown 1 0 \<in> (\<Union>i\<in>{Suc 0..<N}. Tr\<^sub>r\<^sub>p i (ps ! i))"
      apply (auto simp add:rphil_transitions_def)
      using N_g1 by linarith
    from 43 show ?case
      using d0 d1 d2 by blast
  qed
next
  case 5
  then show ?case
    using 5(6)[rule_format, of 0] by simp
qed

corollary DF_DINING: "deadlock_free_v2 DINING"
  unfolding DINING_is_DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m DINING\<^sub>n\<^sub>o\<^sub>r\<^sub>m_def
  using inv_DINING inv_implies_DF by (subst deadlock_free_dnorm) auto

end

end
























