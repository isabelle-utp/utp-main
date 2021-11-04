(* Title: RTS/Common/CollectionSemantics.thy *)
(* Author: Susannah Mansky, UIUC 2020 *)

section "Collection Semantics"

theory CollectionSemantics
imports Semantics
begin

text "General model for small step semantics instrumented
 with an information collection mechanism:"
locale CollectionSemantics = Semantics +
 constrains
  small :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state set" and
  endset :: "'state set"
 fixes
  collect :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> 'coll" and
  combine :: "'coll \<Rightarrow> 'coll \<Rightarrow> 'coll" and
  collect_id :: "'coll"
 assumes
  combine_assoc: "combine (combine c1 c2) c3 = combine c1 (combine c2 c3)" and
  collect_idl[simp]: "combine collect_id c = c" and
  collect_idr[simp]: "combine c collect_id = c"

context CollectionSemantics begin

subsection "Small-Step Collection Semantics"

definition csmall :: "'prog \<Rightarrow> 'state \<Rightarrow> ('state \<times> 'coll) set" where
"csmall P \<sigma> \<equiv> { (\<sigma>', coll). \<sigma>' \<in> small P \<sigma> \<and> collect P \<sigma> \<sigma>' = coll }"

lemma small_det_csmall_det:
assumes "\<forall>\<sigma>. small P \<sigma> = {} \<or> (\<exists>\<sigma>'. small P \<sigma> = {\<sigma>'})"
shows "\<forall>\<sigma>. csmall P \<sigma> = {} \<or> (\<exists>o'. csmall P \<sigma> = {o'})"
using assms by(fastforce simp: csmall_def)

subsection "Extending @{term csmall} to multiple steps"

primrec csmall_nstep :: "'prog \<Rightarrow> 'state \<Rightarrow> nat \<Rightarrow> ('state \<times> 'coll) set" where
csmall_nstep_base:
 "csmall_nstep P \<sigma> 0 = {(\<sigma>, collect_id)}" |
csmall_nstep_Rec:
 "csmall_nstep P \<sigma> (Suc n) =
  { (\<sigma>2, coll). \<exists>\<sigma>1 coll1 coll2. (\<sigma>1, coll1) \<in> csmall_nstep P \<sigma> n
                      \<and> (\<sigma>2, coll2) \<in> csmall P \<sigma>1 \<and> combine coll1 coll2 = coll }"

lemma small_nstep_csmall_nstep_equiv:
 "small_nstep P \<sigma> n
       = { \<sigma>'. \<exists>coll. (\<sigma>', coll) \<in> csmall_nstep P \<sigma> n }"
proof (induct n) qed(simp_all add: csmall_def)

lemma csmall_nstep_exists:
 "\<sigma>' \<in> big P \<sigma> \<Longrightarrow> \<exists>n coll. (\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<and> \<sigma>' \<in> endset"
proof(drule bigD) qed(clarsimp simp: small_nstep_csmall_nstep_equiv)

lemma csmall_det_csmall_nstep_det:
assumes "\<forall>\<sigma>. csmall P \<sigma> = {} \<or> (\<exists>o'. csmall P \<sigma> = {o'})"
shows "\<forall>\<sigma>. csmall_nstep P \<sigma> n = {} \<or> (\<exists>o'. csmall_nstep P \<sigma> n = {o'})"
using assms
proof(induct n)
  case (Suc n) then show ?case by fastforce
qed(simp)

lemma csmall_nstep_Rec2:
 "csmall_nstep P \<sigma> (Suc n) =
  { (\<sigma>2, coll). \<exists>\<sigma>1 coll1 coll2. (\<sigma>1, coll1) \<in> csmall P \<sigma>
                      \<and> (\<sigma>2, coll2) \<in> csmall_nstep P \<sigma>1 n \<and> combine coll1 coll2 = coll }"
proof(induct n arbitrary: \<sigma>)
  case (Suc n)
  have right: "\<And>\<sigma>' coll'. (\<sigma>', coll') \<in> csmall_nstep P \<sigma> (Suc(Suc n))
    \<Longrightarrow> \<exists>\<sigma>1 coll1 coll2. (\<sigma>1, coll1) \<in> csmall P \<sigma>
                      \<and> (\<sigma>', coll2) \<in> csmall_nstep P \<sigma>1 (Suc n) \<and> combine coll1 coll2 = coll'"
  proof -
    fix \<sigma>' coll'
    assume "(\<sigma>', coll') \<in> csmall_nstep P \<sigma> (Suc(Suc n))"
    then obtain \<sigma>1 coll1 coll2 where Sucnstep: "(\<sigma>1, coll1) \<in> csmall_nstep P \<sigma> (Suc n)"
                        "(\<sigma>', coll2) \<in> csmall P \<sigma>1" "combine coll1 coll2 = coll'" by fastforce
    obtain \<sigma>12 coll12 coll22 where nstep: "(\<sigma>12, coll12) \<in> csmall P \<sigma>
                        \<and> (\<sigma>1, coll22) \<in> csmall_nstep P \<sigma>12 n \<and> combine coll12 coll22 = coll1"
      using Suc Sucnstep(1) by fastforce
    then show "\<exists>\<sigma>1 coll1 coll2. (\<sigma>1, coll1) \<in> csmall P \<sigma>
                      \<and> (\<sigma>', coll2) \<in> csmall_nstep P \<sigma>1 (Suc n) \<and> combine coll1 coll2 = coll'"
     using combine_assoc[of coll12 coll22 coll2] Sucnstep by fastforce
  qed
  have left: "\<And>\<sigma>' coll'. \<exists>\<sigma>1 coll1 coll2. (\<sigma>1, coll1) \<in> csmall P \<sigma>
                      \<and> (\<sigma>', coll2) \<in> csmall_nstep P \<sigma>1 (Suc n) \<and> combine coll1 coll2 = coll'
    \<Longrightarrow> (\<sigma>', coll') \<in> csmall_nstep P \<sigma> (Suc(Suc n))"
  proof -
    fix \<sigma>' coll'
    assume "\<exists>\<sigma>1 coll1 coll2. (\<sigma>1, coll1) \<in> csmall P \<sigma>
                      \<and> (\<sigma>', coll2) \<in> csmall_nstep P \<sigma>1 (Suc n) \<and> combine coll1 coll2 = coll'"
    then obtain \<sigma>1 coll1 coll2 where Sucnstep: "(\<sigma>1, coll1) \<in> csmall P \<sigma>"
                      "(\<sigma>', coll2) \<in> csmall_nstep P \<sigma>1 (Suc n)" "combine coll1 coll2 = coll'"
      by fastforce
    obtain \<sigma>12 coll12 coll22 where nstep: "(\<sigma>12, coll12) \<in> csmall_nstep P \<sigma>1 n
                        \<and> (\<sigma>', coll22) \<in> csmall P \<sigma>12 \<and> combine coll12 coll22 = coll2"
      using Sucnstep(2) by auto
    then show "(\<sigma>', coll') \<in> csmall_nstep P \<sigma> (Suc(Suc n))"
      using combine_assoc[of coll1 coll12 coll22] Suc Sucnstep by fastforce
  qed
  show ?case using right left by fast
qed(simp)

lemma csmall_nstep_SucD:
assumes "(\<sigma>',coll') \<in> csmall_nstep P \<sigma> (Suc n)"
shows "\<exists>\<sigma>1 coll1. (\<sigma>1, coll1) \<in> csmall P \<sigma>
   \<and> (\<exists>coll. coll' = combine coll1 coll \<and> (\<sigma>',coll) \<in> csmall_nstep P \<sigma>1 n)"
  using csmall_nstep_Rec2 CollectionSemantics_axioms case_prodD assms by fastforce

lemma csmall_nstep_Suc_nend: "o' \<in> csmall_nstep P \<sigma> (Suc n1) \<Longrightarrow> \<sigma> \<notin> endset"
  using endset_final csmall_nstep_SucD CollectionSemantics.csmall_def CollectionSemantics_axioms
  by fastforce

lemma small_to_csmall_nstep_pres:
assumes Qpres: "\<And>P \<sigma> \<sigma>'. Q P \<sigma> \<Longrightarrow> \<sigma>' \<in> small P \<sigma> \<Longrightarrow> Q P \<sigma>'"
shows "Q P \<sigma> \<Longrightarrow> (\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<Longrightarrow> Q P \<sigma>'"
proof(induct n arbitrary: \<sigma> \<sigma>' coll)
  case (Suc n)
  then obtain \<sigma>1 coll1 coll2 where nstep: "(\<sigma>1, coll1) \<in> csmall_nstep P \<sigma> n
                      \<and> (\<sigma>', coll2) \<in> csmall P \<sigma>1 \<and> combine coll1 coll2 = coll" by clarsimp
  then show ?case using Suc Qpres[where P=P and \<sigma>=\<sigma>1 and \<sigma>'=\<sigma>'] by(auto simp: csmall_def)
qed(simp)

lemma csmall_to_csmall_nstep_prop:
assumes cond: "\<And>P \<sigma> \<sigma>' coll. (\<sigma>', coll) \<in> csmall P \<sigma> \<Longrightarrow> R P coll \<Longrightarrow> Q P \<sigma> \<Longrightarrow> R' P \<sigma> \<sigma>' coll"
  and Rcomb: "\<And>P coll1 coll2. R P (combine coll1 coll2) = (R P coll1 \<and> R P coll2)"
  and Qpres: "\<And>P \<sigma> \<sigma>'. Q P \<sigma> \<Longrightarrow> \<sigma>' \<in> small P \<sigma> \<Longrightarrow> Q P \<sigma>'"
  and Rtrans': "\<And>P \<sigma> \<sigma>1 \<sigma>' coll1 coll2.
                        R' P \<sigma> \<sigma>1 coll1 \<and> R' P \<sigma>1 \<sigma>' coll2 \<Longrightarrow> R' P \<sigma> \<sigma>' (combine coll1 coll2)"
  and base: "\<And>\<sigma>. R' P \<sigma> \<sigma> collect_id"
shows "(\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<Longrightarrow> R P coll \<Longrightarrow> Q P \<sigma> \<Longrightarrow> R' P \<sigma> \<sigma>' coll"
proof(induct n arbitrary: \<sigma> \<sigma>' coll)
  case (Suc n)
  then obtain \<sigma>1 coll1 coll2 where nstep: "(\<sigma>1, coll1) \<in> csmall_nstep P \<sigma> n
                      \<and> (\<sigma>', coll2) \<in> csmall P \<sigma>1 \<and> combine coll1 coll2 = coll" by clarsimp
  then have "Q P \<sigma>1" using small_to_csmall_nstep_pres[where Q=Q] Qpres Suc by blast
  then show ?case using nstep assms Suc by auto blast
qed(simp add: base)

lemma csmall_to_csmall_nstep_prop2:
assumes cond: "\<And>P P' \<sigma> \<sigma>' coll. (\<sigma>', coll) \<in> csmall P \<sigma>
             \<Longrightarrow> R P P' coll \<Longrightarrow> Q \<sigma> \<Longrightarrow> (\<sigma>', coll) \<in> csmall P' \<sigma>"
  and Rcomb: "\<And>P P' coll1 coll2. R P P' (combine coll1 coll2) = (R P P' coll1 \<and> R P P' coll2)"
  and Qpres: "\<And>P \<sigma> \<sigma>'. Q \<sigma> \<Longrightarrow> \<sigma>' \<in> small P \<sigma> \<Longrightarrow> Q \<sigma>'"
shows "(\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<Longrightarrow> R P P' coll \<Longrightarrow> Q \<sigma> \<Longrightarrow> (\<sigma>', coll) \<in> csmall_nstep P' \<sigma> n"
proof(induct n arbitrary: \<sigma> \<sigma>' coll)
  case (Suc n)
  then obtain \<sigma>1 coll1 coll2 where nstep: "(\<sigma>1, coll1) \<in> csmall_nstep P \<sigma> n
                      \<and> (\<sigma>', coll2) \<in> csmall P \<sigma>1 \<and> combine coll1 coll2 = coll" by clarsimp
  then have "Q \<sigma>1" using small_to_csmall_nstep_pres[where Q="\<lambda>P. Q"] Qpres Suc by blast
  then show ?case using nstep assms Suc by auto blast
qed(simp)

subsection "Extending @{term csmall} to a big-step semantics"

definition cbig :: "'prog \<Rightarrow> 'state \<Rightarrow> ('state \<times> 'coll) set" where
"cbig P \<sigma> \<equiv>
  { (\<sigma>', coll). \<exists>n. (\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<and> \<sigma>' \<in> endset }"

lemma cbigD:
 "\<lbrakk> (\<sigma>',coll') \<in> cbig P \<sigma> \<rbrakk> \<Longrightarrow> \<exists>n. (\<sigma>',coll') \<in> csmall_nstep P \<sigma> n \<and> \<sigma>' \<in> endset"
  by(simp add: cbig_def)

lemma cbigD':
 "\<lbrakk> o' \<in> cbig P \<sigma> \<rbrakk> \<Longrightarrow> \<exists>n. o' \<in> csmall_nstep P \<sigma> n \<and> fst o' \<in> endset"
  by(cases o', simp add: cbig_def)

lemma cbig_def2:
 "(\<sigma>', coll) \<in> cbig P \<sigma> \<longleftrightarrow> (\<exists>n. (\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<and> \<sigma>' \<in> endset)"
proof(rule iffI)
  assume "(\<sigma>', coll) \<in> cbig P \<sigma>"
  then show "\<exists>n. (\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<and> \<sigma>' \<in> endset" using bigD cbig_def by auto
next
  assume "\<exists>n. (\<sigma>', coll) \<in> csmall_nstep P \<sigma> n \<and> \<sigma>' \<in> endset"
  then show "(\<sigma>', coll) \<in> cbig P \<sigma>" using big_def cbig_def small_nstep_csmall_nstep_equiv by auto
qed

lemma cbig_big_equiv:
 "(\<exists>coll. (\<sigma>', coll) \<in> cbig P \<sigma>) \<longleftrightarrow> \<sigma>' \<in> big P \<sigma>"
proof(rule iffI)
  assume "\<exists>coll. (\<sigma>', coll) \<in> cbig P \<sigma>"
  then show "\<sigma>' \<in> big P \<sigma>" by (auto simp: big_def cbig_def small_nstep_csmall_nstep_equiv)
next
  assume "\<sigma>' \<in> big P \<sigma>"
  then show "\<exists>coll. (\<sigma>', coll) \<in> cbig P \<sigma>" by (fastforce simp: cbig_def dest: csmall_nstep_exists)
qed

lemma cbig_big_implies:
 "(\<sigma>', coll) \<in> cbig P \<sigma> \<Longrightarrow> \<sigma>' \<in> big P \<sigma>"
using cbig_big_equiv by blast

lemma csmall_to_cbig_prop:
assumes "\<And>P \<sigma> \<sigma>' coll. (\<sigma>', coll) \<in> csmall P \<sigma> \<Longrightarrow> R P coll \<Longrightarrow> Q P \<sigma> \<Longrightarrow> R' P \<sigma> \<sigma>' coll"
  and "\<And>P coll1 coll2. R P (combine coll1 coll2) = (R P coll1 \<and> R P coll2)"
  and "\<And>P \<sigma> \<sigma>'. Q P \<sigma> \<Longrightarrow> \<sigma>' \<in> small P \<sigma> \<Longrightarrow> Q P \<sigma>'"
  and "\<And>P \<sigma> \<sigma>1 \<sigma>' coll1 coll2.
                        R' P \<sigma> \<sigma>1 coll1 \<and> R' P \<sigma>1 \<sigma>' coll2 \<Longrightarrow> R' P \<sigma> \<sigma>' (combine coll1 coll2)"
  and "\<And>\<sigma>. R' P \<sigma> \<sigma> collect_id"
shows "(\<sigma>', coll) \<in> cbig P \<sigma> \<Longrightarrow> R P coll \<Longrightarrow> Q P \<sigma> \<Longrightarrow> R' P \<sigma> \<sigma>' coll"
using assms csmall_to_csmall_nstep_prop[where R=R and Q=Q and R'=R' and \<sigma>=\<sigma>]
  by(auto simp: cbig_def2)

lemma csmall_to_cbig_prop2:
assumes "\<And>P P' \<sigma> \<sigma>' coll. (\<sigma>', coll) \<in> csmall P \<sigma> \<Longrightarrow> R P P' coll \<Longrightarrow> Q \<sigma> \<Longrightarrow> (\<sigma>', coll) \<in> csmall P' \<sigma>"
  and "\<And>P P' coll1 coll2. R P P' (combine coll1 coll2) = (R P P' coll1 \<and> R P P' coll2)"
  and Qpres: "\<And>P \<sigma> \<sigma>'. Q \<sigma> \<Longrightarrow> \<sigma>' \<in> small P \<sigma> \<Longrightarrow> Q \<sigma>'"
shows "(\<sigma>', coll) \<in> cbig P \<sigma> \<Longrightarrow> R P P' coll \<Longrightarrow> Q \<sigma> \<Longrightarrow> (\<sigma>', coll) \<in> cbig P' \<sigma>"
using assms csmall_to_csmall_nstep_prop2[where R=R and Q=Q] by(auto simp: cbig_def2) blast

lemma cbig_stepD:
assumes cbig: "(\<sigma>',coll') \<in> cbig P \<sigma>" and nend: "\<sigma> \<notin> endset"
shows "\<exists>\<sigma>1 coll1. (\<sigma>1, coll1) \<in> csmall P \<sigma>
   \<and> (\<exists>coll. coll' = combine coll1 coll \<and> (\<sigma>',coll) \<in> cbig P \<sigma>1)"
proof -
  obtain n where n: "(\<sigma>', coll') \<in> csmall_nstep P \<sigma> n" "\<sigma>' \<in> endset"
    using cbig_def2 cbig by auto
  then show ?thesis using csmall_nstep_SucD nend cbig_def2 by(cases n, simp) blast
qed

(****)

lemma csmall_nstep_det_last_eq:
assumes det: "\<forall>\<sigma>. small P \<sigma> = {} \<or> (\<exists>\<sigma>'. small P \<sigma> = {\<sigma>'})"
shows "\<lbrakk> (\<sigma>',coll') \<in> cbig P \<sigma>; (\<sigma>',coll') \<in> csmall_nstep P \<sigma> n; (\<sigma>',coll'') \<in> csmall_nstep P \<sigma> n' \<rbrakk>
 \<Longrightarrow> n = n'"
proof(induct n arbitrary: n' \<sigma> \<sigma>' coll' coll'')
  case 0
  have "\<sigma>' = \<sigma>" using "0.prems"(2) csmall_nstep_base by blast
  then have endset: "\<sigma> \<in> endset" using "0.prems"(1) cbigD by blast
  show ?case
  proof(cases n')
    case Suc then show ?thesis using "0.prems"(3) csmall_nstep_Suc_nend endset by blast
  qed(simp)
next
  case (Suc n1)
  then have endset: "\<sigma>' \<in> endset" using Suc.prems(1) cbigD by blast
  have nend: "\<sigma> \<notin> endset" using csmall_nstep_Suc_nend[OF Suc.prems(2)] by simp
  then have neq: "\<sigma>' \<noteq> \<sigma>" using endset by auto
  obtain \<sigma>1 coll coll1 where \<sigma>1: "(\<sigma>1,coll1) \<in> csmall P \<sigma>" "coll' = combine coll1 coll"
     "(\<sigma>',coll) \<in> csmall_nstep P \<sigma>1 n1"
    using csmall_nstep_SucD[OF Suc.prems(2)] by clarsimp
  then have cbig: "(\<sigma>',coll) \<in> cbig P \<sigma>1" using endset by(auto simp: cbig_def)
  show ?case
  proof(cases n')
    case 0 then show ?thesis using neq Suc.prems(3) using csmall_nstep_base by simp
  next
    case Suc': (Suc n1')
    then obtain \<sigma>1' coll2 coll1' where \<sigma>1': "(\<sigma>1',coll1') \<in> csmall P \<sigma>" "coll'' = combine coll1' coll2"
      "(\<sigma>',coll2) \<in> csmall_nstep P \<sigma>1' n1'"
      using csmall_nstep_SucD[where \<sigma>=\<sigma> and \<sigma>'=\<sigma>' and coll'=coll'' and n=n1'] Suc.prems(3) by blast
    then have "\<sigma>1=\<sigma>1'" using \<sigma>1 det csmall_def by auto
    then show ?thesis using Suc.hyps(1)[OF cbig \<sigma>1(3)] \<sigma>1'(3) Suc' by blast
  qed
qed

end \<comment> \<open> CollectionSemantics \<close>

end