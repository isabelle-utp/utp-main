(* Title: RTS/Common/Semantics.thy *)
(* Author: Susannah Mansky, UIUC 2020 *)

section "Semantics model"

theory Semantics
imports Main
begin

text "General model for small-step semantics:"
locale Semantics =
 fixes
  small :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state set" and
  endset :: "'state set"
 assumes
  endset_final: "\<sigma> \<in> endset \<Longrightarrow> \<forall>P. small P \<sigma> = {}"

context Semantics begin

subsection "Extending @{term small} to multiple steps"

primrec small_nstep :: "'prog \<Rightarrow> 'state \<Rightarrow> nat \<Rightarrow> 'state set" where
small_nstep_base:
 "small_nstep P \<sigma> 0 = {\<sigma>}" |
small_nstep_Rec:
 "small_nstep P \<sigma> (Suc n) =
  { \<sigma>2. \<exists>\<sigma>1. \<sigma>1 \<in> small_nstep P \<sigma> n \<and> \<sigma>2 \<in> small P \<sigma>1 }"

lemma small_nstep_Rec2:
 "small_nstep P \<sigma> (Suc n) =
  { \<sigma>2. \<exists>\<sigma>1. \<sigma>1 \<in> small P \<sigma> \<and> \<sigma>2 \<in> small_nstep P \<sigma>1 n }"
proof(induct n arbitrary: \<sigma>)
  case (Suc n)
  have right: "\<And>\<sigma>'. \<sigma>' \<in> small_nstep P \<sigma> (Suc(Suc n))
    \<Longrightarrow> \<exists>\<sigma>1. \<sigma>1 \<in> small P \<sigma> \<and> \<sigma>' \<in> small_nstep P \<sigma>1 (Suc n)"
  proof -
    fix \<sigma>'
    assume "\<sigma>' \<in> small_nstep P \<sigma> (Suc(Suc n))"
    then obtain \<sigma>1 where Sucnstep: "\<sigma>1 \<in> small_nstep P \<sigma> (Suc n)" "\<sigma>' \<in> small P \<sigma>1" by fastforce
    obtain \<sigma>12 where nstep: "\<sigma>12 \<in> small P \<sigma> \<and> \<sigma>1 \<in> small_nstep P \<sigma>12 n"
      using Suc Sucnstep(1) by fastforce
    then show "\<exists>\<sigma>1. \<sigma>1 \<in> small P \<sigma> \<and> \<sigma>' \<in> small_nstep P \<sigma>1 (Suc n)"
     using Sucnstep by fastforce
  qed
  have left: "\<And>\<sigma>' . \<exists>\<sigma>1. \<sigma>1 \<in> small P \<sigma> \<and> \<sigma>' \<in> small_nstep P \<sigma>1 (Suc n)
    \<Longrightarrow> \<sigma>' \<in> small_nstep P \<sigma> (Suc(Suc n))"
  proof -
    fix \<sigma>' 
    assume "\<exists>\<sigma>1. \<sigma>1 \<in> small P \<sigma> \<and> \<sigma>' \<in> small_nstep P \<sigma>1 (Suc n)"
    then obtain \<sigma>1 where Sucnstep: "\<sigma>1 \<in> small P \<sigma>" "\<sigma>' \<in> small_nstep P \<sigma>1 (Suc n)"
      by fastforce
    obtain \<sigma>12 where nstep: "\<sigma>12 \<in> small_nstep P \<sigma>1 n \<and> \<sigma>' \<in> small P \<sigma>12"
      using Sucnstep(2) by auto
    then show "\<sigma>' \<in> small_nstep P \<sigma> (Suc(Suc n))" using Suc Sucnstep by fastforce
  qed
  show ?case using right left by fast
qed(simp)

lemma small_nstep_SucD:
assumes "\<sigma>' \<in> small_nstep P \<sigma> (Suc n)"
shows "\<exists>\<sigma>1. \<sigma>1 \<in> small P \<sigma> \<and> \<sigma>' \<in> small_nstep P \<sigma>1 n"
  using small_nstep_Rec2 case_prodD assms by fastforce

lemma small_nstep_Suc_nend: "\<sigma>' \<in> small_nstep P \<sigma> (Suc n1) \<Longrightarrow> \<sigma> \<notin> endset"
  using endset_final small_nstep_SucD by fastforce

subsection "Extending @{term small} to a big-step semantics"

definition big :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state set" where
"big P \<sigma> \<equiv> { \<sigma>'. \<exists>n. \<sigma>' \<in> small_nstep P \<sigma> n \<and> \<sigma>' \<in> endset }"

lemma bigI:
 "\<lbrakk> \<sigma>' \<in> small_nstep P \<sigma> n; \<sigma>' \<in> endset \<rbrakk> \<Longrightarrow> \<sigma>' \<in> big P \<sigma>"
by (fastforce simp add: big_def)

lemma bigD:
 "\<lbrakk> \<sigma>' \<in> big P \<sigma> \<rbrakk> \<Longrightarrow> \<exists>n. \<sigma>' \<in> small_nstep P \<sigma> n \<and> \<sigma>' \<in> endset"
by (simp add: big_def)

lemma big_def2:
 "\<sigma>' \<in> big P \<sigma> \<longleftrightarrow> (\<exists>n. \<sigma>' \<in> small_nstep P \<sigma> n \<and> \<sigma>' \<in> endset)"
proof(rule iffI)
  assume "\<sigma>' \<in> big P \<sigma>"
  then show "\<exists>n. \<sigma>' \<in> small_nstep P \<sigma> n \<and> \<sigma>' \<in> endset" using bigD big_def by auto
next
  assume "\<exists>n. \<sigma>' \<in> small_nstep P \<sigma> n \<and> \<sigma>' \<in> endset"
  then show "\<sigma>' \<in> big P \<sigma>" using big_def big_def by auto
qed

lemma big_stepD:
assumes big: "\<sigma>' \<in> big P \<sigma>" and nend: "\<sigma> \<notin> endset"
shows "\<exists>\<sigma>1. \<sigma>1 \<in> small P \<sigma> \<and> \<sigma>' \<in> big P \<sigma>1"
proof -
  obtain n where n: "\<sigma>' \<in> small_nstep P \<sigma> n" "\<sigma>' \<in> endset"
    using big_def2 big by auto
  then show ?thesis using small_nstep_SucD nend big_def2 by(cases n, simp) blast
qed

(***)

lemma small_nstep_det_last_eq:
assumes det: "\<forall>\<sigma>. small P \<sigma> = {} \<or> (\<exists>\<sigma>'. small P \<sigma> = {\<sigma>'})"
shows "\<lbrakk> \<sigma>' \<in> big P \<sigma>; \<sigma>' \<in> small_nstep P \<sigma> n; \<sigma>' \<in> small_nstep P \<sigma> n' \<rbrakk> \<Longrightarrow> n = n'"
proof(induct n arbitrary: n' \<sigma> \<sigma>')
  case 0
  have "\<sigma>' = \<sigma>" using "0.prems"(2) small_nstep_base by blast
  then have endset: "\<sigma> \<in> endset" using "0.prems"(1) bigD by blast
  show ?case
  proof(cases n')
    case Suc then show ?thesis using "0.prems"(3) small_nstep_SucD endset_final[OF endset] by blast
  qed(simp)
next
  case (Suc n1)
  then have endset: "\<sigma>' \<in> endset" using Suc.prems(1) bigD by blast
  have nend: "\<sigma> \<notin> endset" using small_nstep_Suc_nend[OF Suc.prems(2)] by simp
  then have neq: "\<sigma>' \<noteq> \<sigma>" using endset by auto
  obtain \<sigma>1 where \<sigma>1: "\<sigma>1 \<in> small P \<sigma>" "\<sigma>' \<in> small_nstep P \<sigma>1 n1"
    using small_nstep_SucD[OF Suc.prems(2)] by clarsimp
  then have big: "\<sigma>' \<in> big P \<sigma>1" using endset by(auto simp: big_def)
  show ?case
  proof(cases n')
    case 0 then show ?thesis using neq Suc.prems(3) using small_nstep_base by blast
  next
    case Suc': (Suc n1')
    then obtain \<sigma>1' where \<sigma>1': "\<sigma>1' \<in> small P \<sigma>" "\<sigma>' \<in> small_nstep P \<sigma>1' n1'"
      using small_nstep_SucD[where \<sigma>=\<sigma> and \<sigma>'=\<sigma>' and n=n1'] Suc.prems(3) by blast
    then have "\<sigma>1=\<sigma>1'" using \<sigma>1(1) det by auto
    then show ?thesis using Suc.hyps(1)[OF big \<sigma>1(2)] \<sigma>1'(2) Suc' by blast
  qed
qed

end \<comment> \<open> Semantics \<close>


end