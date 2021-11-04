(*  Title:      JinjaDCI/J/Equivalence.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/Equivalence.thy by Tobias Nipkow
*)

section \<open> Equivalence of Big Step and Small Step Semantics \<close>

theory Equivalence imports TypeSafe WWellForm begin

subsection\<open>Small steps simulate big step\<close>

subsubsection "Init"

text "The reduction of initialization expressions doesn't touch or use
 their on-hold expressions (the subexpression to the right of @{text \<leftarrow>})
 until the initialization operation completes. This function is used to prove
 this and related properties. It is then used for general reduction of
 initialization expressions separately from their on-hold expressions by
 using the on-hold expression @{term unit}, then putting the real on-hold
 expression back in at the end."

fun init_switch :: "'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a exp" where
"init_switch (INIT C (Cs,b) \<leftarrow> e\<^sub>i) e = (INIT C (Cs,b) \<leftarrow> e)" |
"init_switch (RI(C,e');Cs \<leftarrow> e\<^sub>i) e = (RI(C,e');Cs \<leftarrow> e)" |
"init_switch e' e = e'"

fun INIT_class :: "'a exp \<Rightarrow> cname option" where
"INIT_class (INIT C (Cs,b) \<leftarrow> e) = (if C = last (C#Cs) then Some C else None)" |
"INIT_class (RI(C,e\<^sub>0);Cs \<leftarrow> e) = Some (last (C#Cs))" |
"INIT_class _ = None"

lemma init_red_init:
"\<lbrakk> init_exp_of e\<^sub>0 = \<lfloor>e\<rfloor>; P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle> \<rbrakk>
  \<Longrightarrow> (init_exp_of e\<^sub>1 = \<lfloor>e\<rfloor> \<and> (INIT_class e\<^sub>0 = \<lfloor>C\<rfloor> \<longrightarrow> INIT_class e\<^sub>1 = \<lfloor>C\<rfloor>))
   \<or> (e\<^sub>1 = e \<and> b\<^sub>1 = icheck P (the(INIT_class e\<^sub>0)) e) \<or> (\<exists>a. e\<^sub>1 = throw a)"
 by(erule red.cases, auto)

lemma init_exp_switch[simp]:
"init_exp_of e\<^sub>0 = \<lfloor>e\<rfloor> \<Longrightarrow> init_exp_of (init_switch e\<^sub>0 e') = \<lfloor>e'\<rfloor>"
 by(cases e\<^sub>0, simp_all)

lemma init_red_sync:
"\<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>; init_exp_of e\<^sub>0 = \<lfloor>e\<rfloor>; e\<^sub>1 \<noteq> e \<rbrakk>
  \<Longrightarrow> (\<And>e'. P \<turnstile> \<langle>init_switch e\<^sub>0 e',s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow> \<langle>init_switch e\<^sub>1 e',s\<^sub>1,b\<^sub>1\<rangle>)"
proof(induct rule: red.cases) qed(simp_all add: red_reds.intros)

lemma init_red_sync_end:
"\<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>; init_exp_of e\<^sub>0 = \<lfloor>e\<rfloor>; e\<^sub>1 = e; throw_of e = None \<rbrakk>
  \<Longrightarrow> (\<And>e'. \<not>sub_RI e' \<Longrightarrow> P \<turnstile> \<langle>init_switch e\<^sub>0 e',s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow> \<langle>e',s\<^sub>1,icheck P (the(INIT_class e\<^sub>0)) e'\<rangle>)"
proof(induct rule: red.cases) qed(simp_all add: red_reds.intros)

lemma init_reds_sync_unit':
 "\<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v',s\<^sub>1,b\<^sub>1\<rangle>; init_exp_of e\<^sub>0 = \<lfloor>unit\<rfloor>; INIT_class e\<^sub>0 = \<lfloor>C\<rfloor> \<rbrakk>
  \<Longrightarrow> (\<And>e'. \<not>sub_RI e' \<Longrightarrow> P \<turnstile> \<langle>init_switch e\<^sub>0 e',s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>1,icheck P (the(INIT_class e\<^sub>0)) e'\<rangle>)"
proof(induct rule:converse_rtrancl_induct3)
case refl then show ?case by simp
next
  case (step e0 s0 b0 e1 s1 b1)
  have "(init_exp_of e1 = \<lfloor>unit\<rfloor> \<and> (INIT_class e0 = \<lfloor>C\<rfloor> \<longrightarrow> INIT_class e1 = \<lfloor>C\<rfloor>))
          \<or> (e1 = unit \<and> b1 = icheck P (the(INIT_class e0)) unit) \<or> (\<exists>a. e1 = throw a)"
    using init_red_init[OF step.prems(1) step.hyps(1)] by simp
  then show ?case
  proof(rule disjE)
    assume assm: "init_exp_of e1 = \<lfloor>unit\<rfloor> \<and> (INIT_class e0 = \<lfloor>C\<rfloor> \<longrightarrow> INIT_class e1 = \<lfloor>C\<rfloor>)"
    then have red: "P \<turnstile> \<langle>init_switch e0 e',s0,b0\<rangle> \<rightarrow> \<langle>init_switch e1 e',s1,b1\<rangle>"
      using init_red_sync[OF step.hyps(1) step.prems(1)] by simp
    have reds: "P \<turnstile> \<langle>init_switch e1 e',s1,b1\<rangle> \<rightarrow>* \<langle>e',s\<^sub>1,icheck P (the (INIT_class e0)) e'\<rangle>"
      using step.hyps(3)[OF _ _ step.prems(3)] assm step.prems(2) by simp
    show ?thesis by(rule converse_rtrancl_into_rtrancl[OF red reds])
  next
    assume "(e1 = unit \<and> b1 = icheck P (the(INIT_class e0)) unit) \<or> (\<exists>a. e1 = throw a)"
    then show ?thesis
    proof(rule disjE)
      assume assm: "e1 = unit \<and> b1 = icheck P (the(INIT_class e0)) unit" then have e1: "e1 = unit" by simp
      have sb: "s1 = s\<^sub>1" "b1 = b\<^sub>1" using reds_final_same[OF step.hyps(2)] assm
        by(simp_all add: final_def)
      then have step': "P \<turnstile> \<langle>init_switch e0 e',s0,b0\<rangle> \<rightarrow> \<langle>e',s\<^sub>1,icheck P (the (INIT_class e0)) e'\<rangle>"
        using init_red_sync_end[OF step.hyps(1) step.prems(1) e1 _ step.prems(3)] by auto
      then have "P \<turnstile> \<langle>init_switch e0 e',s0,b0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>1,icheck P (the (INIT_class e0)) e'\<rangle>"
        using r_into_rtrancl by auto
      then show ?thesis using step assm sb by simp
    next
      assume "\<exists>a. e1 = throw a" then obtain a where "e1 = throw a" by clarsimp
      then have tof: "throw_of e1 = \<lfloor>a\<rfloor>" by simp
      then show ?thesis using reds_throw[OF step.hyps(2) tof] by simp
    qed
  qed
qed

lemma init_reds_sync_unit_throw':
 "\<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>; init_exp_of e\<^sub>0 = \<lfloor>unit\<rfloor> \<rbrakk>
  \<Longrightarrow> (\<And>e'. P \<turnstile> \<langle>init_switch e\<^sub>0 e',s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>)"
proof(induct rule:converse_rtrancl_induct3)
case refl then show ?case by simp
next
  case (step e0 s0 b0 e1 s1 b1)
  have "init_exp_of e1 = \<lfloor>unit\<rfloor> \<and> (\<forall>C. INIT_class e0 = \<lfloor>C\<rfloor> \<longrightarrow> INIT_class e1 = \<lfloor>C\<rfloor>) \<or>
  e1 = unit \<and> b1 = icheck P (the (INIT_class e0)) unit \<or> (\<exists>a. e1 = throw a)"
    using init_red_init[OF step.prems(1) step.hyps(1)] by auto
  then show ?case
  proof(rule disjE)
    assume assm: "init_exp_of e1 = \<lfloor>unit\<rfloor> \<and> (\<forall>C. INIT_class e0 = \<lfloor>C\<rfloor> \<longrightarrow> INIT_class e1 = \<lfloor>C\<rfloor>)"
    then have "P \<turnstile> \<langle>init_switch e0 e',s0,b0\<rangle> \<rightarrow> \<langle>init_switch e1 e',s1,b1\<rangle>"
      using step init_red_sync[OF step.hyps(1) step.prems] by simp
    then show ?thesis using step assm by (meson converse_rtrancl_into_rtrancl)
  next
    assume "e1 = unit \<and> b1 = icheck P (the (INIT_class e0)) unit \<or> (\<exists>a. e1 = throw a)"
    then show ?thesis
    proof(rule disjE)
      assume "e1 = unit \<and> b1 = icheck P (the (INIT_class e0)) unit"
      then show ?thesis using step using final_def reds_final_same by blast
    next
      assume assm: "\<exists>a. e1 = throw a"
      then have "P \<turnstile> \<langle>init_switch e0 e',s0,b0\<rangle> \<rightarrow> \<langle>e1,s1,b1\<rangle>"
        using init_red_sync[OF step.hyps(1) step.prems] by clarsimp
      then show ?thesis using step by simp
    qed
  qed
qed

lemma init_reds_sync_unit:
assumes "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v',s\<^sub>1,b\<^sub>1\<rangle>" and "init_exp_of e\<^sub>0 = \<lfloor>unit\<rfloor>" and "INIT_class e\<^sub>0 = \<lfloor>C\<rfloor>"
  and "\<not>sub_RI e'"
shows "P \<turnstile> \<langle>init_switch e\<^sub>0 e',s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>1,icheck P (the(INIT_class e\<^sub>0)) e'\<rangle>"
using init_reds_sync_unit'[OF assms] by clarsimp

lemma init_reds_sync_unit_throw:
assumes "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>" and "init_exp_of e\<^sub>0 = \<lfloor>unit\<rfloor>"
shows "P \<turnstile> \<langle>init_switch e\<^sub>0 e',s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>"
using init_reds_sync_unit_throw'[OF assms] by clarsimp

\<comment> \<open> init reds lemmas \<close>

lemma InitSeqReds:
assumes "P \<turnstile> \<langle>INIT C ([C],b) \<leftarrow> unit,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v',s\<^sub>1,b\<^sub>1\<rangle>"
 and "P \<turnstile> \<langle>e,s\<^sub>1,icheck P C e\<rangle> \<rightarrow>* \<langle>e\<^sub>2,s\<^sub>2,b\<^sub>2\<rangle>" and "\<not>sub_RI e"
shows "P \<turnstile> \<langle>INIT C ([C],b) \<leftarrow> e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2,s\<^sub>2,b\<^sub>2\<rangle>"
using assms
proof -
  have "P \<turnstile> \<langle>init_switch (INIT C ([C],b) \<leftarrow> unit) e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e,s\<^sub>1,icheck P C e\<rangle>"
    using init_reds_sync_unit[OF assms(1) _ _ assms(3)] by simp
  then show ?thesis using assms(2) by simp
qed

lemma InitSeqThrowReds:
assumes "P \<turnstile> \<langle>INIT C ([C],b) \<leftarrow> unit,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>"
shows "P \<turnstile> \<langle>INIT C ([C],b) \<leftarrow> e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>"
using assms
proof -
  have "P \<turnstile> \<langle>init_switch (INIT C ([C],b) \<leftarrow> unit) e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>"
    using init_reds_sync_unit_throw[OF assms(1)] by simp
  then show ?thesis by simp
qed

lemma InitNoneReds:
 "\<lbrakk> sh C = None;
    P \<turnstile> \<langle>INIT C' (C # Cs,False) \<leftarrow> e,(h, l, sh(C \<mapsto> (sblank P C, Prepared))),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<rbrakk>
\<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule InitNoneRed)
apply assumption
done
(*>*)

lemma InitDoneReds:
 "\<lbrakk> sh C = Some(sfs,Done); P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<rbrakk>
\<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule RedInitDone)
apply assumption
done
(*>*)

lemma InitProcessingReds:
 "\<lbrakk> sh C = Some(sfs,Processing); P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<rbrakk>
\<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule RedInitProcessing)
apply assumption
done
(*>*)

lemma InitErrorReds:
 "\<lbrakk> sh C = Some(sfs,Error); P \<turnstile> \<langle>RI (C,THROW NoClassDefFoundError);Cs \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<rbrakk>
\<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule RedInitError)
apply assumption
done
(*>*)

lemma InitObjectReds:
 "\<lbrakk> sh C = Some(sfs,Prepared); C = Object; sh' = sh(C \<mapsto> (sfs,Processing));
    P \<turnstile> \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh'),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<rbrakk>
\<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule (2) InitObjectRed)
apply assumption
done
(*>*)

lemma InitNonObjectReds:
 "\<lbrakk> sh C = Some(sfs,Prepared); C \<noteq> Object; class P C = Some (D,r);
    sh' = sh(C \<mapsto> (sfs,Processing));
    P \<turnstile> \<langle>INIT C' (D#C#Cs,False) \<leftarrow> e,(h,l,sh'),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<rbrakk>
\<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule (3) InitNonObjectSuperRed)
apply assumption
done
(*>*)

lemma RedsInitRInit:
 "P \<turnstile> \<langle>RI (C,C\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>
\<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedInitRInit)
apply assumption
done
(*>*)

lemmas rtrancl_induct3 =
  rtrancl_induct[of "(ax,ay,az)" "(bx,by,bz)", split_format (complete), consumes 1, case_names refl step]

lemma RInitReds:
 "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>
\<Longrightarrow> P \<turnstile> \<langle>RI (C,e);Cs \<leftarrow> e\<^sub>0, s, b\<rangle> \<rightarrow>* \<langle>RI (C,e');Cs \<leftarrow> e\<^sub>0, s', b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule RInitRed)
done
(*>*)

lemma RedsRInit:
 "\<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1),b\<^sub>1\<rangle>;
    sh\<^sub>1 C = Some (sfs, i); sh\<^sub>2 = sh\<^sub>1(C \<mapsto> (sfs,Done)); C' = last(C#Cs);
    P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h\<^sub>1,l\<^sub>1,sh\<^sub>2),b\<^sub>1\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<rbrakk>
\<Longrightarrow> P \<turnstile> \<langle>RI (C, e\<^sub>0);Cs \<leftarrow> e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule RInitReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule (2) RedRInit)
apply assumption
done
(*>*)

lemma RInitInitThrowReds:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Throw a, (h',l',sh'),b'\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Error));
     P \<turnstile> \<langle>RI (D,Throw a);Cs \<leftarrow> e\<^sub>0, (h',l',sh''),b'\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>RI (C,e);D#Cs \<leftarrow> e\<^sub>0,s,b\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule RInitReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule (1) RInitInitThrow)
apply assumption
done
(*>*)

lemma RInitThrowReds:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Throw a, (h',l',sh'),b'\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Error)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>RI (C,e);Nil \<leftarrow> e\<^sub>0,s,b\<rangle> \<rightarrow>* \<langle>Throw a, (h',l',sh''),b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule RInitReds)
apply(erule RInitThrow)
apply assumption
done
(*>*)

subsubsection "New"

lemma NewInitDoneReds:
  "\<lbrakk> sh C = Some (sfs, Done); new_Addr h = Some a;
     P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>blank P C) \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh),False\<rangle> \<rightarrow>* \<langle>addr a,(h',l,sh),False\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule NewInitDoneRed)
apply(rule r_into_rtrancl)
apply(erule (2) RedNew)
done
(*>*)

lemma NewInitDoneReds2:
  "\<lbrakk> sh C = Some (sfs, Done); new_Addr h = None; is_class P C \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh),False\<rangle> \<rightarrow>* \<langle>THROW OutOfMemory, (h,l,sh), False\<rangle>"
(*<*)
apply(rule_tac converse_rtrancl_into_rtrancl)
 apply(erule NewInitDoneRed)
apply(rule r_into_rtrancl)
apply(erule (1) RedNewFail)
done
(*>*)

lemma NewInitReds:
 "\<lbrakk> \<nexists>sfs. shp s C = Some (sfs, Done);
    P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,s,False\<rangle> \<rightarrow>* \<langle>Val v',(h',l',sh'),b'\<rangle>;
    new_Addr h' = Some a; P \<turnstile> C has_fields FDTs; h'' = h'(a\<mapsto>blank P C); is_class P C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,s,False\<rangle> \<rightarrow>* \<langle>addr a,(h'',l',sh'),False\<rangle>"
(*<*)
apply(rule_tac b = "(INIT C ([C],False) \<leftarrow> new C,s,False)" in converse_rtrancl_into_rtrancl)
 apply(cases s, simp)
 apply (simp add: NewInitRed)
apply(erule InitSeqReds, simp_all)
apply(rule r_into_rtrancl, rule RedNew)
  apply simp+
done
(*>*)

lemma NewInitOOMReds:
 "\<lbrakk> \<nexists>sfs. shp s C = Some (sfs, Done);
    P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,s,False\<rangle> \<rightarrow>* \<langle>Val v',(h',l',sh'),b'\<rangle>;
    new_Addr h' = None; is_class P C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,s,False\<rangle> \<rightarrow>* \<langle>THROW OutOfMemory,(h',l',sh'),False\<rangle>"
(*<*)
apply(rule_tac b = "(INIT C ([C],False) \<leftarrow> new C,s,False)" in converse_rtrancl_into_rtrancl)
 apply(cases s, simp)
 apply (simp add: NewInitRed)
apply(erule InitSeqReds, simp_all)
apply(rule r_into_rtrancl, rule RedNewFail)
 apply simp+
done
(*>*)

lemma NewInitThrowReds:
 "\<lbrakk> \<nexists>sfs. shp s C = Some (sfs, Done); is_class P C;
    P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,s,False\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,s,False\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule_tac b = "(INIT C ([C],False) \<leftarrow> new C,s,False)" in converse_rtrancl_into_rtrancl)
 apply(cases s, simp)
 apply (simp add: NewInitRed)
apply(erule InitSeqThrowReds)
done
(*>*)

subsubsection "Cast"

lemma CastReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s,b\<rangle> \<rightarrow>* \<langle>Cast C e',s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CastRed)
done
(*>*)

lemma CastRedsNull:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>null,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s,b\<rangle> \<rightarrow>* \<langle>null,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(rule RedCastNull)
done
(*>*)

lemma CastRedsAddr:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s',b'\<rangle>; hp s' a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(cases s',simp)
apply(erule (1) RedCast)
done
(*>*)

lemma CastRedsFail:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s',b'\<rangle>; hp s' a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s,b\<rangle> \<rightarrow>* \<langle>THROW ClassCast,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(cases s',simp)
apply(erule (1) RedCastFail)
done
(*>*)

lemma CastRedsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(rule red_reds.CastThrow)
done
(*>*)

subsubsection "LAss"

lemma LAssReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle> V:=e,s,b\<rangle> \<rightarrow>* \<langle> V:=e',s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule LAssRed)
done
(*>*)

lemma LAssRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Val v,(h',l',sh'),b'\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle> V:=e,s,b\<rangle> \<rightarrow>* \<langle>unit,(h',l'(V\<mapsto>v),sh'),b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule LAssReds)
apply(rule RedLAss)
done
(*>*)

lemma LAssRedsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle> V:=e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule LAssReds)
apply(rule red_reds.LAssThrow)
done
(*>*)

subsubsection "BinOp"

lemma BinOp1Reds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle> e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s,b\<rangle> \<rightarrow>* \<langle>e' \<guillemotleft>bop\<guillemotright> e\<^sub>2, s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule BinOpRed1)
done
(*>*)

lemma BinOp2Reds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s,b\<rangle> \<rightarrow>* \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule BinOpRed2)
done
(*>*)

lemma BinOpRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v\<^sub>2,s\<^sub>2,b\<^sub>2\<rangle>; binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule BinOp1Reds)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp2Reds)
apply(rule RedBinOp)
apply simp
done
(*>*)

lemma BinOpRedsThrow1:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s,b\<rangle> \<rightarrow>* \<langle>throw e', s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp1Reds)
apply(rule red_reds.BinOpThrow1)
done
(*>*)

lemma BinOpRedsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0, b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule BinOp1Reds)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp2Reds)
apply(rule red_reds.BinOpThrow2)
done
(*>*)

subsubsection "FAcc"

lemma FAccReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}, s,b\<rangle> \<rightarrow>* \<langle>e'\<bullet>F{D}, s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule FAccRed)
done
(*>*)

lemma FAccRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s',b'\<rangle>; hp s' a = Some(C,fs); fs(F,D) = Some v;
    P \<turnstile> C has F,NonStatic:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s,b\<rangle> \<rightarrow>* \<langle>Val v,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(cases s',simp)
apply(erule (2) RedFAcc)
done
(*>*)

lemma FAccRedsNull:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>null,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s,b\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(rule RedFAccNull)
done
(*>*)

lemma FAccRedsNone:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s',b'\<rangle>;
     hp s' a = Some(C,fs);
    \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s,b\<rangle> \<rightarrow>* \<langle>THROW NoSuchFieldError,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(cases s',simp)
apply(erule RedFAccNone, simp)
done
(*>*)

lemma FAccRedsStatic:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s',b'\<rangle>;
     hp s' a = Some(C,fs);
    P \<turnstile> C has F,Static:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s,b\<rangle> \<rightarrow>* \<langle>THROW IncompatibleClassChangeError,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(cases s',simp)
apply(erule (1) RedFAccStatic)
done
(*>*)

lemma FAccRedsThrow:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(rule red_reds.FAccThrow)
done
(*>*)

subsubsection "SFAcc"

lemma SFAccReds:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     shp s D = Some(sfs,Done); sfs F = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s,True\<rangle> \<rightarrow>* \<langle>Val v,s,False\<rangle>"
(*<*)
apply(rule r_into_rtrancl)
apply(cases s,simp)
apply(erule (2) RedSFAcc)
done
(*>*)

lemma SFAccRedsNone:
  "\<not>(\<exists>b t. P \<turnstile> C has F,b:t in D)
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s,b\<rangle> \<rightarrow>* \<langle>THROW NoSuchFieldError,s,False\<rangle>"
(*<*)
apply(rule r_into_rtrancl)
apply(cases s,simp)
apply(rule RedSFAccNone, simp)
done
(*>*)

lemma SFAccRedsNonStatic:
  "P \<turnstile> C has F,NonStatic:t in D
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s,b\<rangle> \<rightarrow>* \<langle>THROW IncompatibleClassChangeError,s,False\<rangle>"
(*<*)
apply(rule r_into_rtrancl)
apply(cases s,simp)
apply(erule RedSFAccNonStatic)
done
(*>*)

lemma SFAccInitDoneReds:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     shp s D = Some (sfs,Done);
     sfs F = Some v \<rbrakk>
 \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}, s,b\<rangle> \<rightarrow>* \<langle>Val v, s,False\<rangle>"
(*<*)
apply(cases b)
\<comment> \<open> case True \<close>
 apply(rule r_into_rtrancl)
 apply(cases s, simp)
 apply(erule (2) RedSFAcc)
\<comment> \<open> case False \<close>
apply(rule_tac b = "(C\<bullet>\<^sub>sF{D},s,True)" in converse_rtrancl_into_rtrancl)
 apply(cases s, simp)
 apply(drule (2) SFAccInitDoneRed)
apply(erule SFAccReds, simp+)
done
(*>*)

lemma SFAccInitReds:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. shp s D = Some (sfs,Done);
     P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,s,False\<rangle> \<rightarrow>* \<langle>Val v',s',b'\<rangle>;
     shp s' D = Some (sfs,i); sfs F = Some v \<rbrakk>
 \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s,False\<rangle> \<rightarrow>* \<langle>Val v,s',False\<rangle>"
(*<*)
apply(rule_tac b = "(INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF{D},s,False)" in converse_rtrancl_into_rtrancl)
 apply(cases s, simp)
 apply(simp add: SFAccInitRed)
apply(rule InitSeqReds, simp_all)
apply(subgoal_tac "\<exists>T. P \<turnstile> C has F,Static:T in D")
 prefer 2 apply fast
apply(rule r_into_rtrancl)
apply(cases s', simp)
apply(erule (2) RedSFAcc)
done
(*>*)

lemma SFAccInitThrowReds:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. shp s D = Some (sfs,Done);
     P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,s,False\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<rbrakk>
 \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s,False\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule_tac b = "(INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF{D},s,False)" in converse_rtrancl_into_rtrancl)
 apply(cases s, simp)
 apply (simp add: SFAccInitRed)
apply(erule InitSeqThrowReds)
done
(*>*)

subsubsection "FAss"

lemma FAssReds1:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}:=e\<^sub>2, s,b\<rangle> \<rightarrow>* \<langle>e'\<bullet>F{D}:=e\<^sub>2, s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule FAssRed1)
done
(*>*)

lemma FAssReds2:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Val v\<bullet>F{D}:=e, s,b\<rangle> \<rightarrow>* \<langle>Val v\<bullet>F{D}:=e', s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule FAssRed2)
done
(*>*)

lemma FAssRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>;
    P \<turnstile> C has F,NonStatic:t in D; Some(C,fs) = h\<^sub>2 a \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>unit, (h\<^sub>2(a\<mapsto>(C,fs((F,D)\<mapsto>v))),l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule RedFAss)
 apply simp+
done
(*>*)

lemma FAssRedsNull:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NullPointer, s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule RedFAssNull)
done
(*>*)

lemma FAssRedsThrow1:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}:=e\<^sub>2, s,b\<rangle> \<rightarrow>* \<langle>throw e', s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds1)
apply(rule red_reds.FAssThrow1)
done
(*>*)

lemma FAssRedsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule red_reds.FAssThrow2)
done
(*>*)

lemma FAssRedsNone:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>;
     h\<^sub>2 a = Some(C,fs); \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NoSuchFieldError, (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule RedFAssNone)
 apply simp+
done
(*>*)

lemma FAssRedsStatic:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C has F,Static:t in D \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW IncompatibleClassChangeError, (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule RedFAssStatic)
 apply simp+
done
(*>*)

subsubsection "SFAss"

lemma SFAssReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e,s,b\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sF{D}:=e',s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule SFAssRed)
done
(*>*)

lemma SFAssRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>;
    P \<turnstile> C has F,Static:t in D; sh\<^sub>2 D = \<lfloor>(sfs,Done)\<rfloor> \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>unit, (h\<^sub>2,l\<^sub>2,sh\<^sub>2(D\<mapsto>(sfs(F\<mapsto>v), Done))),False\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule SFAssReds)
apply(cases b\<^sub>2)
\<comment> \<open> case True \<close>
 apply(rule r_into_rtrancl)
 apply(drule_tac l = l\<^sub>2 in RedSFAss, simp_all)
\<comment> \<open> case False \<close>
apply(rule converse_rtrancl_into_rtrancl)
 apply(drule_tac sh = sh\<^sub>2 in SFAssInitDoneRed, simp_all)
apply(rule r_into_rtrancl)
apply(drule_tac l = l\<^sub>2 in RedSFAss, simp_all)
done
(*>*)

lemma SFAssRedsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SFAssReds)
apply(rule red_reds.SFAssThrow)
done
(*>*)

lemma SFAssRedsNone:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>;
     \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NoSuchFieldError, (h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SFAssReds)
apply(rule RedSFAssNone)
apply simp
done
(*>*)

lemma SFAssRedsNonStatic:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>;
     P \<turnstile> C has F,NonStatic:t in D \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SFAssReds)
apply(rule RedSFAssNonStatic)
apply simp
done
(*>*)

lemma SFAssInitReds:
 "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>;
    P \<turnstile> C has F,Static:t in D;
    \<nexists>sfs. sh\<^sub>2 D = Some (sfs, Done);
    P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>Val v',(h',l',sh'),b'\<rangle>;
    sh' D = Some(sfs,i);
    sfs' = sfs(F\<mapsto>v); sh'' = sh'(D\<mapsto>(sfs',i)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>unit,(h',l',sh''),False\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule SFAssReds)
apply(rule_tac converse_rtrancl_into_rtrancl)
 apply(erule (1) SFAssInitRed)
apply(erule InitSeqReds, simp_all)
apply(subgoal_tac "\<exists>T. P \<turnstile> C has F,Static:T in D")
 prefer 2 apply fast
apply(simp,rule r_into_rtrancl)
apply(erule (2) RedSFAss)
apply simp
done
(*>*)

lemma SFAssInitThrowReds:
 "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>;
    P \<turnstile> C has F,Static:t in D;
    \<nexists>sfs. sh\<^sub>2 D = Some (sfs, Done);
    P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule SFAssReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(erule (1) SFAssInitRed)
apply(erule InitSeqThrowReds)
done
(*>*)

subsubsection";;"

lemma  SeqReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e;;e\<^sub>2, s,b\<rangle> \<rightarrow>* \<langle>e';;e\<^sub>2, s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule SeqRed)
done
(*>*)

lemma SeqRedsThrow:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e;;e\<^sub>2, s,b\<rangle> \<rightarrow>* \<langle>throw e', s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SeqReds)
apply(rule red_reds.SeqThrow)
done
(*>*)

lemma SeqReds2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2',s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1;;e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2',s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule SeqReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedSeq)
apply assumption
done
(*>*)


subsubsection"If"

lemma CondReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s,b\<rangle> \<rightarrow>* \<langle>if (e') e\<^sub>1 else e\<^sub>2,s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CondRed)
done
(*>*)

lemma CondRedsThrow:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(rule red_reds.CondThrow)
done
(*>*)

lemma CondReds2T:
  "\<lbrakk>P \<turnstile> \<langle>e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>1, s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondT)
apply assumption
done
(*>*)

lemma CondReds2F:
  "\<lbrakk>P \<turnstile> \<langle>e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>false,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2, s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondF)
apply assumption
done
(*>*)


subsubsection "While"

lemma WhileFReds:
  "P \<turnstile> \<langle>b,s,b\<^sub>0\<rangle> \<rightarrow>* \<langle>false,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s,b\<^sub>0\<rangle> \<rightarrow>* \<langle>unit,s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(rule RedCondF)
done
(*>*)

lemma WhileRedsThrow:
  "P \<turnstile> \<langle>b,s,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s',b'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(rule red_reds.CondThrow)
done
(*>*)

lemma WhileTReds:
  "\<lbrakk> P \<turnstile> \<langle>b,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>2,b\<^sub>2\<rangle>; P \<turnstile> \<langle>while (b) c,s\<^sub>2,b\<^sub>2\<rangle> \<rightarrow>* \<langle>e,s\<^sub>3,b\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e,s\<^sub>3,b\<^sub>3\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondT)
apply(rule rtrancl_trans)
 apply(erule SeqReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedSeq)
apply assumption
done
(*>*)

lemma WhileTRedsThrow:
  "\<lbrakk> P \<turnstile> \<langle>b,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondT)
apply(rule rtrancl_into_rtrancl)
 apply(erule SeqReds)
apply(rule red_reds.SeqThrow)
done
(*>*)

subsubsection"Throw"

lemma ThrowReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>throw e,s,b\<rangle> \<rightarrow>* \<langle>throw e',s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule ThrowRed)
done
(*>*)

lemma ThrowRedsNull:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>null,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>throw e,s,b\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule ThrowReds)
apply(rule RedThrowNull)
done
(*>*)

lemma ThrowRedsThrow:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>throw e,s,b\<rangle> \<rightarrow>* \<langle>throw a,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule ThrowReds)
apply(rule red_reds.ThrowThrow)
done
(*>*)

subsubsection "InitBlock"

lemma InitBlockReds_aux:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow>
  \<forall>h l sh h' l' sh' v. s = (h,l(V\<mapsto>v),sh) \<longrightarrow> s' = (h',l',sh') \<longrightarrow>
  P \<turnstile> \<langle>{V:T := Val v; e},(h,l,sh),b\<rangle> \<rightarrow>* \<langle>{V:T := Val(the(l' V)); e'},(h',l'(V:=(l V)),sh'),b'\<rangle>"
(*<*)
apply(erule converse_rtrancl_induct3)
 apply(fastforce simp: fun_upd_same simp del:fun_upd_apply)
apply clarify
apply(rename_tac e0 X Y x3 b0 e1 h1 l1 sh1 b1 h0 l0 sh0 h2 l2 sh2 v0)
apply(subgoal_tac "V \<in> dom l1")
 prefer 2
 apply(drule red_lcl_incr)
 apply simp
apply clarsimp
apply(rename_tac v1)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule InitBlockRed)
  apply assumption
 apply simp
apply(erule_tac x = "l1(V := l0 V)" in allE)
apply(erule_tac x = v1 in allE)
apply(erule impE)
 apply(rule ext)
 apply(simp add:fun_upd_def)
apply(simp add:fun_upd_def)
done
(*>*)

lemma InitBlockReds:
 "P \<turnstile> \<langle>e, (h,l(V\<mapsto>v),sh),b\<rangle> \<rightarrow>* \<langle>e', (h',l',sh'),b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>{V:T := Val v; e}, (h,l,sh),b\<rangle> \<rightarrow>* \<langle>{V:T := Val(the(l' V)); e'}, (h',l'(V:=(l V)),sh'),b'\<rangle>"
(*<*)by(blast dest:InitBlockReds_aux)(*>*)

lemma InitBlockRedsFinal:
  "\<lbrakk> P \<turnstile> \<langle>e,(h,l(V\<mapsto>v),sh),b\<rangle> \<rightarrow>* \<langle>e',(h',l',sh'),b'\<rangle>; final e' \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>{V:T := Val v; e},(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',(h', l'(V := l V),sh'),b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule InitBlockReds)
apply(fast elim!:finalE intro:RedInitBlock InitBlockThrow)
done
(*>*)


subsubsection "Block"

lemmas converse_rtranclE3 = converse_rtranclE [of "(xa,xb,xc)" "(za,zb,zc)", split_rule]

lemma BlockRedsFinal:
assumes reds: "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>" and fin: "final e\<^sub>2"
shows "\<And>h\<^sub>0 l\<^sub>0 sh\<^sub>0. s\<^sub>0 = (h\<^sub>0,l\<^sub>0(V:=None),sh\<^sub>0) \<Longrightarrow> P \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0,sh\<^sub>0),b\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2(V:=l\<^sub>0 V),sh\<^sub>2),b\<^sub>2\<rangle>"
(*<*)
using reds
proof (induct rule:converse_rtrancl_induct3)
  case refl thus ?case
    by(fastforce intro:finalE[OF fin] RedBlock BlockThrow
                simp del:fun_upd_apply)
next
  case (step e\<^sub>0 s\<^sub>0 b\<^sub>0 e\<^sub>1 s\<^sub>1 b\<^sub>1)
  have red: "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>"
   and reds: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
   and IH: "\<And>h l sh. s\<^sub>1 = (h,l(V := None),sh)
                \<Longrightarrow> P \<turnstile> \<langle>{V:T; e\<^sub>1},(h,l,sh),b\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2, l\<^sub>2(V := l V),sh\<^sub>2),b\<^sub>2\<rangle>"
   and s\<^sub>0: "s\<^sub>0 = (h\<^sub>0, l\<^sub>0(V := None),sh\<^sub>0)" by fact+
  obtain h\<^sub>1 l\<^sub>1 sh\<^sub>1 where s\<^sub>1: "s\<^sub>1 = (h\<^sub>1,l\<^sub>1,sh\<^sub>1)"
    using prod_cases3 by blast
  show ?case
  proof cases
    assume "assigned V e\<^sub>0"
    then obtain v e where e\<^sub>0: "e\<^sub>0 = V := Val v;; e"
      by (unfold assigned_def)blast
    from red e\<^sub>0 s\<^sub>0 have e\<^sub>1: "e\<^sub>1 = unit;;e" and s\<^sub>1: "s\<^sub>1 = (h\<^sub>0, l\<^sub>0(V \<mapsto> v),sh\<^sub>0)" and b\<^sub>1: "b\<^sub>1 = b\<^sub>0"
      by auto
    from e\<^sub>1 fin have "e\<^sub>1 \<noteq> e\<^sub>2" by (auto simp:final_def)
    then obtain e' s' b' where red1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
      and reds': "P \<turnstile> \<langle>e',s',b'\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
      using converse_rtranclE3[OF reds] by blast
    from red1 e\<^sub>1 b\<^sub>1 have es': "e' = e" "s' = s\<^sub>1" "b' = b\<^sub>0" by auto
    show ?case using e\<^sub>0 s\<^sub>1 es' reds'
      by(auto intro!: InitBlockRedsFinal[OF _ fin] simp del:fun_upd_apply)
  next
    assume unass: "\<not> assigned V e\<^sub>0"
    show ?thesis
    proof (cases "l\<^sub>1 V")
      assume None: "l\<^sub>1 V = None"
      hence "P \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0,sh\<^sub>0),b\<^sub>0\<rangle> \<rightarrow> \<langle>{V:T; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V),sh\<^sub>1),b\<^sub>1\<rangle>"
        using s\<^sub>0 s\<^sub>1 red by(simp add: BlockRedNone[OF _ _ unass])
      moreover
      have "P \<turnstile> \<langle>{V:T; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V),sh\<^sub>1),b\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2, l\<^sub>2(V := l\<^sub>0 V),sh\<^sub>2),b\<^sub>2\<rangle>"
        using IH[of _ "l\<^sub>1(V := l\<^sub>0 V)"] s\<^sub>1 None by(simp add:fun_upd_idem)
      ultimately show ?case by(rule converse_rtrancl_into_rtrancl)
    next
      fix v assume Some: "l\<^sub>1 V = Some v"
      hence "P \<turnstile> \<langle>{V:T;e\<^sub>0},(h\<^sub>0,l\<^sub>0,sh\<^sub>0),b\<^sub>0\<rangle> \<rightarrow> \<langle>{V:T := Val v; e\<^sub>1},(h\<^sub>1,l\<^sub>1(V := l\<^sub>0 V),sh\<^sub>1),b\<^sub>1\<rangle>"
        using s\<^sub>0 s\<^sub>1 red by(simp add: BlockRedSome[OF _ _ unass])
      moreover
      have "P \<turnstile> \<langle>{V:T := Val v; e\<^sub>1},(h\<^sub>1,l\<^sub>1(V:= l\<^sub>0 V),sh\<^sub>1),b\<^sub>1\<rangle> \<rightarrow>*
                \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2(V:=l\<^sub>0 V),sh\<^sub>2),b\<^sub>2\<rangle>"
        using InitBlockRedsFinal[OF _ fin,of _ _ "l\<^sub>1(V:=l\<^sub>0 V)" V]
              Some reds s\<^sub>1 by(simp add:fun_upd_idem)
      ultimately show ?case by(rule converse_rtrancl_into_rtrancl)
    qed
  qed
qed
(*>*)


subsubsection "try-catch"

lemma TryReds:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>try e catch(C V) e\<^sub>2,s,b\<rangle> \<rightarrow>* \<langle>try e' catch(C V) e\<^sub>2,s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule TryRed)
done
(*>*)

lemma TryRedsVal:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Val v,s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>try e catch(C V) e\<^sub>2,s,b\<rangle> \<rightarrow>* \<langle>Val v,s',b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule TryReds)
apply(rule RedTry)
done
(*>*)

lemma TryCatchRedsFinal:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw a,(h\<^sub>1,l\<^sub>1,sh\<^sub>1),b\<^sub>1\<rangle>;  h\<^sub>1 a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C;
     P \<turnstile> \<langle>e\<^sub>2, (h\<^sub>1, l\<^sub>1(V \<mapsto> Addr a),sh\<^sub>1),b\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2', (h\<^sub>2,l\<^sub>2,sh\<^sub>2), b\<^sub>2\<rangle>; final e\<^sub>2' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2, s\<^sub>0, b\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2', (h\<^sub>2, l\<^sub>2(V := l\<^sub>1 V),sh\<^sub>2),b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule TryReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedTryCatch)
  apply fastforce
 apply assumption
apply(rule InitBlockRedsFinal)
 apply assumption
apply(simp)
done
(*>*)

lemma TryRedsFail:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s,b\<rangle> \<rightarrow>* \<langle>Throw a,(h,l,sh),b'\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s,b\<rangle> \<rightarrow>* \<langle>Throw a,(h,l,sh),b'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule TryReds)
apply(fastforce intro!: RedTryFail)
done
(*>*)

subsubsection "List"

lemma ListReds1:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e#es,s,b\<rangle> [\<rightarrow>]* \<langle>e' # es,s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule ListRed1)
done
(*>*)

lemma ListReds2:
  "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Val v # es,s,b\<rangle> [\<rightarrow>]* \<langle>Val v # es',s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule ListRed2)
done
(*>*)

lemma ListRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1,b\<^sub>1\<rangle> [\<rightarrow>]* \<langle>es',s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e#es,s\<^sub>0,b\<^sub>0\<rangle> [\<rightarrow>]* \<langle>Val v # es',s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule ListReds1)
apply(erule ListReds2)
done
(*>*)

subsubsection"Call"

text\<open> First a few lemmas on what happens to free variables during redction. \<close>

lemma assumes wf: "wwf_J_prog P"
shows Red_fv: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> fv e' \<subseteq> fv e"
  and  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> fvs es' \<subseteq> fvs es"
(*<*)
proof (induct rule:red_reds_inducts)
  case (RedCall h a C fs M Ts T pns body D vs l sh b)
  hence "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)
  with RedCall.hyps show ?case by fastforce
next
  case (RedSCall C M Ts T pns body D vs)
  hence "fv body \<subseteq> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)
  with RedSCall.hyps show ?case by fastforce
qed auto
(*>*)


lemma Red_dom_lcl:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fv e" and
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fvs es"
(*<*)
proof (induct rule:red_reds_inducts)
  case RedLAss thus ?case by(force split:if_splits)
next
  case CallParams thus ?case by(force split:if_splits)
next
  case BlockRedNone thus ?case by clarsimp (fastforce split:if_splits)
next
  case BlockRedSome thus ?case by clarsimp (fastforce split:if_splits)
next
  case InitBlockRed thus ?case by clarsimp (fastforce split:if_splits)
qed auto
(*>*)

lemma Reds_dom_lcl:
  "\<lbrakk> wwf_J_prog P; P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',(h',l',sh'),b'\<rangle> \<rbrakk> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fv e"
(*<*)
apply(erule converse_rtrancl_induct_red)
 apply blast
apply(blast dest: Red_fv Red_dom_lcl)
done
(*>*)

text\<open> Now a few lemmas on the behaviour of blocks during reduction. \<close>

lemma override_on_upd_lemma:
  "(override_on f (g(a\<mapsto>b)) A)(a := g a) = override_on f g (insert a A)"
(*<*)
apply(rule ext)
apply(simp add:override_on_def)
done

declare fun_upd_apply[simp del] map_upds_twist[simp del]
(*>*)


lemma blocksReds:
  "\<And>l. \<lbrakk> length Vs = length Ts; length vs = length Ts; distinct Vs;
         P \<turnstile> \<langle>e, (h,l(Vs [\<mapsto>] vs),sh),b\<rangle> \<rightarrow>* \<langle>e', (h',l',sh'),b'\<rangle> \<rbrakk>
        \<Longrightarrow> P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l,sh),b\<rangle> \<rightarrow>* \<langle>blocks(Vs,Ts,map (the \<circ> l') Vs,e'), (h',override_on l' l (set Vs),sh'),b'\<rangle>"
(*<*)
proof(induct Vs Ts vs e rule:blocks_induct)
  case (1 V Vs T Ts v vs e) show ?case
    using InitBlockReds[OF "1.hyps"[of "l(V\<mapsto>v)"]] "1.prems"
    by(auto simp:override_on_upd_lemma)
qed auto
(*>*)


lemma blocksFinal:
 "\<And>l. \<lbrakk> length Vs = length Ts; length vs = length Ts; final e \<rbrakk> \<Longrightarrow>
       P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l,sh),b\<rangle> \<rightarrow>* \<langle>e, (h,l,sh),b\<rangle>"
(*<*)
proof(induct Vs Ts vs e rule:blocks_induct)
  case 1
  show ?case using "1.prems" InitBlockReds[OF "1.hyps"]
    by(fastforce elim!:finalE elim: rtrancl_into_rtrancl[OF _ RedInitBlock]
                                   rtrancl_into_rtrancl[OF _ InitBlockThrow])
qed auto
(*>*)


lemma blocksRedsFinal:
assumes wf: "length Vs = length Ts" "length vs = length Ts" "distinct Vs"
    and reds: "P \<turnstile> \<langle>e, (h,l(Vs [\<mapsto>] vs),sh),b\<rangle> \<rightarrow>* \<langle>e', (h',l',sh'),b'\<rangle>"
    and fin: "final e'" and l'': "l'' = override_on l' l (set Vs)"
shows "P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l,sh),b\<rangle> \<rightarrow>* \<langle>e', (h',l'',sh'),b'\<rangle>"
(*<*)
proof -
  let ?bv = "blocks(Vs,Ts,map (the o l') Vs,e')"
  have "P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l,sh),b\<rangle> \<rightarrow>* \<langle>?bv, (h',l'',sh'),b'\<rangle>"
    using l'' by simp (rule blocksReds[OF wf reds])
  also have "P \<turnstile> \<langle>?bv, (h',l'',sh'),b'\<rangle> \<rightarrow>* \<langle>e', (h',l'',sh'),b'\<rangle>"
    using wf by(fastforce intro:blocksFinal fin)
  finally show ?thesis .
qed
(*>*)

text\<open> An now the actual method call reduction lemmas. \<close>

lemma CallRedsObj:
 "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s,b\<rangle> \<rightarrow>* \<langle>e'\<bullet>M(es),s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CallObj)
done
(*>*)


lemma CallRedsParams:
 "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val v)\<bullet>M(es),s,b\<rangle> \<rightarrow>* \<langle>(Val v)\<bullet>M(es'),s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CallParams)
done
(*>*)


lemma CallRedsFinal:
assumes wwf: "wwf_J_prog P"
and "P \<turnstile> \<langle>e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b\<^sub>1\<rangle>"
      "P \<turnstile> \<langle>es,s\<^sub>1,b\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
      "h\<^sub>2 a = Some(C,fs)" "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D"
      "size vs = size pns"
and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Addr a, pns[\<mapsto>]vs]"
and body: "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2),b\<^sub>2\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
and "final ef"
shows "P \<turnstile> \<langle>e\<bullet>M(es), s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2,sh\<^sub>3),b\<^sub>3\<rangle>"
(*<*)
proof -
  have wf: "size Ts = size pns \<and> distinct pns \<and> this \<notin> set pns"
    and wt: "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  from body[THEN Red_lcl_add, of l\<^sub>2]
  have body': "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2(this\<mapsto> Addr a, pns[\<mapsto>]vs),sh\<^sub>2),b\<^sub>2\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
    by (simp add:l\<^sub>2')
  have "dom l\<^sub>3 \<subseteq> {this} \<union> set pns"
    using Reds_dom_lcl[OF wwf body] wt l\<^sub>2' set_take_subset by force
  hence eql\<^sub>2: "override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns) = l\<^sub>2"
    by(fastforce simp add:map_add_def override_on_def fun_eq_iff)
  have "P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>(addr a)\<bullet>M(es),s\<^sub>1,b\<^sub>1\<rangle>" by(rule CallRedsObj)(rule assms(2))
  also have "P \<turnstile> \<langle>(addr a)\<bullet>M(es),s\<^sub>1,b\<^sub>1\<rangle> \<rightarrow>*
                 \<langle>(addr a)\<bullet>M(map Val vs),(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
    by(rule CallRedsParams)(rule assms(3))
  also have "P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle> \<rightarrow>
                 \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
    by(rule RedCall)(auto simp: assms wf, rule assms(5))
  also (rtrancl_into_rtrancl) have "P \<turnstile> \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>
                 \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns),sh\<^sub>3),b\<^sub>3\<rangle>"
    by(rule blocksRedsFinal, insert assms wf body', simp_all)
  finally show ?thesis using eql\<^sub>2 by simp
qed
(*>*)


lemma CallRedsThrowParams:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b\<^sub>1\<rangle>;  P \<turnstile> \<langle>es,s\<^sub>1,b\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs\<^sub>1 @ throw a # es\<^sub>2,s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(rule CallThrowParams)
apply simp
done
(*>*)


lemma CallRedsThrowObj:
  "P \<turnstile> \<langle>e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1,b\<^sub>1\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsObj)
apply(rule CallThrowObj)
done
(*>*)


lemma CallRedsNull:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1,b\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1,b\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(rule RedCallNull)
done
(*>*)

lemma CallRedsNone:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b\<^sub>1\<rangle>;  P \<turnstile> \<langle>es,s\<^sub>1,b\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,b\<^sub>2\<rangle>;
     hp s\<^sub>2 a = Some(C,fs);
    \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s,b\<rangle> \<rightarrow>* \<langle>THROW NoSuchMethodError,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(cases s\<^sub>2,simp)
apply(erule RedCallNone, simp)
done
(*>*)

lemma CallRedsStatic:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b\<^sub>1\<rangle>;  P \<turnstile> \<langle>es,s\<^sub>1,b\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,b\<^sub>2\<rangle>;
     hp s\<^sub>2 a = Some(C,fs);
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = m in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s,b\<rangle> \<rightarrow>* \<langle>THROW IncompatibleClassChangeError,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(cases s\<^sub>2,simp)
apply(erule RedCallStatic, simp)
done
(*>*)

subsection\<open>SCall\<close>

lemma SCallRedsParams:
 "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s,b\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sM(es'),s',b'\<rangle>"
(*<*)
apply(erule rtrancl_induct3)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule SCallParams)
done
(*>*)

lemma SCallRedsFinal:
assumes wwf: "wwf_J_prog P"
and "P \<turnstile> \<langle>es,s\<^sub>0,b\<^sub>0\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
      "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D"
      "sh\<^sub>2 D = Some(sfs,Done) \<or> (M = clinit \<and> sh\<^sub>2 D = \<lfloor>(sfs, Processing)\<rfloor>)"
      "size vs = size pns"
and l\<^sub>2': "l\<^sub>2' = [pns[\<mapsto>]vs]"
and body: "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
and "final ef"
shows "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es), s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2,sh\<^sub>3),b\<^sub>3\<rangle>"
(*<*)
proof -
  have wf: "size Ts = size pns \<and> distinct pns"
    and wt: "fv body \<subseteq> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  from body[THEN Red_lcl_add, of l\<^sub>2]
  have body': "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2(pns[\<mapsto>]vs),sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
    by (simp add:l\<^sub>2')
  have "dom l\<^sub>3 \<subseteq> set pns"
    using Reds_dom_lcl[OF wwf body] wt l\<^sub>2' set_take_subset by force
  hence eql\<^sub>2: "override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns) = l\<^sub>2"
    by(fastforce simp add:map_add_def override_on_def fun_eq_iff)
  have b2T: "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sM(map Val vs), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),True\<rangle>"
  proof(cases b\<^sub>2)
    case True then show ?thesis by simp
  next
    case False then show ?thesis using assms(3,4) by(auto elim: SCallInitDoneRed)
  qed
  have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
    by(rule SCallRedsParams)(rule assms(2))
  also have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle> \<rightarrow>* \<langle>blocks(pns, Ts, vs, body), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>"
    by(auto intro!: rtrancl_into_rtrancl[OF b2T] RedSCall assms(3) simp: assms wf)
  also (rtrancl_trans) have "P \<turnstile> \<langle>blocks(pns, Ts, vs, body), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>
                 \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns),sh\<^sub>3),b\<^sub>3\<rangle>"
    by(rule blocksRedsFinal, insert assms wf body', simp_all)
  finally show ?thesis using eql\<^sub>2 by simp
qed
(*>*)

lemma SCallRedsThrowParams:
  "\<lbrakk> P \<turnstile> \<langle>es,s\<^sub>0,b\<^sub>0\<rangle> [\<rightarrow>]* \<langle>map Val vs\<^sub>1 @ throw a # es\<^sub>2,s\<^sub>2,b\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>2,b\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SCallRedsParams)
apply(rule SCallThrowParams)
apply simp
done
(*>*)

lemma SCallRedsNone:
  "\<lbrakk> P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,False\<rangle>;
    \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s,b\<rangle> \<rightarrow>* \<langle>THROW NoSuchMethodError,s\<^sub>2,False\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SCallRedsParams)
apply(cases s\<^sub>2,simp)
apply(rule RedSCallNone, simp)
done
(*>*)

lemma SCallRedsNonStatic:
  "\<lbrakk> P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,False\<rangle>;
     P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = m in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s,b\<rangle> \<rightarrow>* \<langle>THROW IncompatibleClassChangeError,s\<^sub>2,False\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SCallRedsParams)
apply(cases s\<^sub>2,simp)
apply(rule RedSCallNonStatic, simp)
done
(*>*)

lemma SCallInitThrowReds:
assumes wwf: "wwf_J_prog P"
and "P \<turnstile> \<langle>es,s\<^sub>0,b\<^sub>0\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>"
      "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D"
      "\<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done)"
      "M \<noteq> clinit"
and "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>throw a,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
shows "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es), s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>throw a,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
(*<*)
proof -
  have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>"
    by(rule SCallRedsParams)(rule assms(2))
  also have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle> \<rightarrow> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>"
    using SCallInitRed[OF assms(3)] assms(4-5) by auto
  also (rtrancl_into_rtrancl) have "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>
                 \<rightarrow>* \<langle>throw a,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
    by(rule InitSeqThrowReds[OF assms(6)])
  finally show ?thesis by simp
qed
(*>*)

lemma SCallInitReds:
assumes wwf: "wwf_J_prog P"
and "P \<turnstile> \<langle>es,s\<^sub>0,b\<^sub>0\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>"
      "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D"
      "\<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done)"
      "M \<noteq> clinit"
and "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>Val v',(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
and "size vs = size pns"
and l\<^sub>2': "l\<^sub>2' = [pns[\<mapsto>]vs]"
and body: "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
and "final ef"
shows "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2,sh\<^sub>3),b\<^sub>3\<rangle>"
(*<*)
proof -
  have wf: "size Ts = size pns \<and> distinct pns"
    and wt: "fv body \<subseteq> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  from body[THEN Red_lcl_add, of l\<^sub>2]
  have body': "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2(pns[\<mapsto>]vs),sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
    by (simp add:l\<^sub>2')
  have "dom l\<^sub>3 \<subseteq> set pns"
    using Reds_dom_lcl[OF wwf body] wt l\<^sub>2' set_take_subset by force
  hence eql\<^sub>2: "override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns) = l\<^sub>2"
    by(fastforce simp add:map_add_def override_on_def fun_eq_iff)
  have "icheck P D (C\<bullet>\<^sub>sM(map Val vs)::'a exp)" using assms(3) by auto
  then have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),icheck P D (C\<bullet>\<^sub>sM(map Val vs))\<rangle>
       \<rightarrow> \<langle>blocks(pns, Ts, vs, body), (h\<^sub>2, l\<^sub>2, sh\<^sub>2), False\<rangle>"
    by (metis (full_types) assms(3) assms(7) local.wf red_reds.RedSCall)
  also have "P \<turnstile> \<langle>blocks(pns, Ts, vs, body), (h\<^sub>2, l\<^sub>2, sh\<^sub>2), False\<rangle>
         \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns),sh\<^sub>3),b\<^sub>3\<rangle>"
    by(rule blocksRedsFinal, insert assms wf body', simp_all)
  finally have trueReds: "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),icheck P D (C\<bullet>\<^sub>sM(map Val vs))\<rangle>
                   \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns),sh\<^sub>3),b\<^sub>3\<rangle>" by simp
  have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>"
    by(rule SCallRedsParams)(rule assms(2))
  also have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle> \<rightarrow> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>"
    using SCallInitRed[OF assms(3)] assms(4-5) by auto
  also (rtrancl_into_rtrancl) have "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>1,l\<^sub>1,sh\<^sub>1),False\<rangle>
                 \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns),sh\<^sub>3),b\<^sub>3\<rangle>"
    using InitSeqReds[OF assms(6) trueReds] assms(5) by simp
  finally show ?thesis using eql\<^sub>2 by simp
qed
(*>*)

lemma SCallInitProcessingReds:
assumes wwf: "wwf_J_prog P"
and "P \<turnstile> \<langle>es,s\<^sub>0,b\<^sub>0\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
      "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D"
      "sh\<^sub>2 D = Some(sfs,Processing)"
and "size vs = size pns"
and l\<^sub>2': "l\<^sub>2' = [pns[\<mapsto>]vs]"
and body: "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
and "final ef"
shows "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2,sh\<^sub>3),b\<^sub>3\<rangle>"
(*<*)
proof -
  have wf: "size Ts = size pns \<and> distinct pns"
    and wt: "fv body \<subseteq> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  from body[THEN Red_lcl_add, of l\<^sub>2]
  have body': "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2(pns[\<mapsto>]vs),sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3,sh\<^sub>3),b\<^sub>3\<rangle>"
    by (simp add:l\<^sub>2')
  have "dom l\<^sub>3 \<subseteq> set pns"
    using Reds_dom_lcl[OF wwf body] wt l\<^sub>2' set_take_subset by force
  hence eql\<^sub>2: "override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns) = l\<^sub>2"
    by(fastforce simp add:map_add_def override_on_def fun_eq_iff)
  have b2T: "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sM(map Val vs), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),True\<rangle>"
  proof(cases b\<^sub>2)
    case True then show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases "M = clinit")
      case True then show ?thesis using False assms(3) red_reds.SCallInitDoneRed assms(4)
        by (simp add: r_into_rtrancl)
    next
      case nclinit: False
      have icheck: "icheck P D (C\<bullet>\<^sub>sM(map Val vs))" using assms(3) by auto
      have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),b\<^sub>2\<rangle>
         \<rightarrow> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
        using SCallInitRed[OF assms(3)] assms(4) False nclinit by simp
      also have "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>
         \<rightarrow> \<langle>INIT D (Nil,True) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
        using RedInitProcessing assms(4) by simp
      also have "P \<turnstile> \<langle>INIT D (Nil,True) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>
         \<rightarrow> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2, l\<^sub>2, sh\<^sub>2),True\<rangle>"
        using RedInit[of "C\<bullet>\<^sub>sM(map Val vs)" D _ _ _ P] icheck nclinit
         by (metis (full_types) nsub_RI_Vals sub_RI.simps(12))
      finally show ?thesis by simp
    qed
  qed
  have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow>* \<langle>C\<bullet>\<^sub>sM(map Val vs),(h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle>"
    by(rule SCallRedsParams)(rule assms(2))
  also have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),b\<^sub>2\<rangle> \<rightarrow>* \<langle>blocks(pns, Ts, vs, body), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>"
    by(auto intro!: rtrancl_into_rtrancl[OF b2T] RedSCall assms(3) simp: assms wf)
  also (rtrancl_trans) have "P \<turnstile> \<langle>blocks(pns, Ts, vs, body), (h\<^sub>2,l\<^sub>2,sh\<^sub>2),False\<rangle>
                 \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 (set pns),sh\<^sub>3),b\<^sub>3\<rangle>"
    by(rule blocksRedsFinal, insert assms wf body', simp_all)
  finally show ?thesis using eql\<^sub>2 by simp
qed
(*>*)

(***********************************)

subsubsection "The main Theorem"

lemma assumes wwf: "wwf_J_prog P"
shows big_by_small: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
   \<Longrightarrow> (\<And>b. iconf (shp s) e \<Longrightarrow> P,shp s \<turnstile>\<^sub>b (e,b) \<surd> \<Longrightarrow> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',False\<rangle>)"
and bigs_by_smalls: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>
   \<Longrightarrow> (\<And>b. iconfs (shp s) es \<Longrightarrow> P,shp s \<turnstile>\<^sub>b (es,b) \<surd> \<Longrightarrow> P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',False\<rangle>)"
(*<*)
proof (induct rule: eval_evals.inducts)
  case New show ?case
  proof(cases b)
    case True then show ?thesis using RedNew[OF New.hyps(2-4)] by auto
  next
    case False then show ?thesis using New.hyps(1) NewInitDoneReds[OF _ New.hyps(2-4)] by auto
  qed
next
  case NewFail show ?case
  proof(cases b)
    case True then show ?thesis using RedNewFail[OF NewFail.hyps(2)] NewFail.hyps(3) by fastforce
  next
    case False
    then show ?thesis using NewInitDoneReds2[OF _ NewFail.hyps(2)] NewFail by fastforce
  qed
next
  case (NewInit sh C h l v' h' l' sh' a FDTs h'') show ?case
  proof(cases b)
    case True
    then obtain sfs where shC: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
      using NewInit.hyps(1) NewInit.prems by(clarsimp simp: bconf_def initPD_def)
    then have s': "(h',l',sh') = (h,l,sh)" using NewInit.hyps(2) init_ProcessingE by clarsimp
    then show ?thesis using RedNew[OF NewInit.hyps(4-6)] True by auto
  next
    case False
    then have init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h, l, sh),False\<rangle> \<rightarrow>* \<langle>Val v',(h', l', sh'),False\<rangle>"
      using NewInit.hyps(3) by(auto simp: bconf_def)
    then show ?thesis using NewInit NewInitReds[OF _ init NewInit.hyps(4-6)] False
     has_fields_is_class[OF NewInit.hyps(5)] by auto
  qed
next
  case (NewInitOOM sh C h l v' h' l' sh') show ?case
  proof(cases b)
    case True
    then obtain sfs where shC: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
      using NewInitOOM.hyps(1) NewInitOOM.prems by(clarsimp simp: bconf_def initPD_def)
    then have s': "(h',l',sh') = (h,l,sh)" using NewInitOOM.hyps(2) init_ProcessingE by clarsimp
    then show ?thesis using RedNewFail[OF NewInitOOM.hyps(4)] True r_into_rtrancl NewInitOOM.hyps(5)
      by auto
  next
    case False
    then have init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h, l, sh),False\<rangle> \<rightarrow>* \<langle>Val v',(h', l', sh'),False\<rangle>"
      using NewInitOOM.hyps(3) by(auto simp: bconf_def)
    then show ?thesis using NewInitOOM.hyps(1) NewInitOOMReds[OF _ init NewInitOOM.hyps(4)] False
      NewInitOOM.hyps(5) by auto
  qed
next
  case (NewInitThrow sh C h l a s') show ?case
  proof(cases b)
    case True
    then obtain sfs where shC: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
      using NewInitThrow.hyps(1) NewInitThrow.prems by(clarsimp simp: bconf_def initPD_def)
    then show ?thesis using NewInitThrow.hyps(2) init_ProcessingE by blast
  next
    case False
    then have init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h, l, sh),b\<rangle> \<rightarrow>* \<langle>throw a,s',False\<rangle>"
      using NewInitThrow.hyps(3) by(auto simp: bconf_def)
    then show ?thesis using NewInitThrow NewInitThrowReds[of "(h,l,sh)" C P a s'] False by auto
  qed
next
  case Cast then show ?case by(fastforce intro:CastRedsAddr)
next
  case CastNull then show ?case by(fastforce intro: CastRedsNull)
next
  case CastFail thus ?case by(fastforce intro!:CastRedsFail)
next
  case CastThrow thus ?case by(fastforce dest!:eval_final intro:CastRedsThrow)
next
  case Val then show ?case using exI[of _ b] by(simp add: bconf_def)
next
  case (BinOp e\<^sub>1 s\<^sub>0 v\<^sub>1 s\<^sub>1 e\<^sub>2 v\<^sub>2 s\<^sub>2 bop v)
  show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>1" using None BinOp.prems by auto
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using None BinOp.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1,False\<rangle>" using iconf BinOp.hyps(2) by auto
    have binop: "P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule BinOp1Reds[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf binop] None BinOp by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>Val v\<^sub>2,s\<^sub>2,False\<rangle>" using BinOp.hyps(4)[OF iconf2'] by auto
    then show ?thesis using BinOpRedsVal[OF b1 b2 BinOp.hyps(5)] by fast
  next
    case (Some a)
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) BinOp.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have binop: "P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>1,b1\<rangle>" by(rule BinOp1Reds[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf binop] BinOp by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using BinOp.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,b1) \<surd>" using Red_preserves_bconf[OF wwf binop BinOp.prems] by simp
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>Val v\<^sub>2,s\<^sub>2,False\<rangle>" using BinOp.hyps(4)[OF iconf2'] by auto
    then show ?thesis using BinOpRedsVal[OF b1 b2 BinOp.hyps(5)] by fast
  qed
next
  case (BinOpThrow1 e\<^sub>1 s\<^sub>0 e s\<^sub>1 bop e\<^sub>2) show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have "iconf (shp s\<^sub>0) e\<^sub>1" and "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using BinOpThrow1.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>1,False\<rangle>" using BinOpThrow1.hyps(2) by auto
    then have "P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>1,False\<rangle>"
      using BinOpThrow1 None by(auto dest!:eval_final simp: BinOpRedsThrow1[OF b1])
    then show ?thesis by fast
  next
    case (Some a)
    then show ?thesis using eval_final_same[OF BinOpThrow1.hyps(1)] val_of_spec[OF Some] by auto
  qed
next
  case (BinOpThrow2 e\<^sub>1 s\<^sub>0 v\<^sub>1 s\<^sub>1 e\<^sub>2 e s\<^sub>2 bop)
  show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>1" using None BinOpThrow2.prems by auto
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using None BinOpThrow2.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1,False\<rangle>" using iconf BinOpThrow2.hyps(2) by auto
    have binop: "P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule BinOp1Reds[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf binop] None BinOpThrow2 by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,False\<rangle>" using BinOpThrow2.hyps(4)[OF iconf2'] by auto
    then show ?thesis using BinOpRedsThrow2[OF b1 b2] by fast
  next
    case (Some a)
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) BinOpThrow2.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have binop: "P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>1,b1\<rangle>" by(rule BinOp1Reds[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf binop] BinOpThrow2 by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using BinOpThrow2.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,b1) \<surd>" using Red_preserves_bconf[OF wwf binop BinOpThrow2.prems] by simp
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2,False\<rangle>" using BinOpThrow2.hyps(4)[OF iconf2'] by auto
    then show ?thesis using BinOpRedsThrow2[OF b1 b2] by fast
  qed
next
  case Var thus ?case by(auto dest:RedVar simp: bconf_def)
next
  case LAss thus ?case by(auto dest: LAssRedsVal)
next
  case LAssThrow thus ?case by(auto dest!:eval_final dest: LAssRedsThrow)
next
  case FAcc thus ?case by(fastforce intro:FAccRedsVal)
next
  case FAccNull thus ?case by(auto dest:FAccRedsNull)
next
  case FAccThrow thus ?case by(auto dest!:eval_final dest:FAccRedsThrow)
next
  case FAccNone then show ?case by(fastforce intro: FAccRedsNone)
next
  case FAccStatic then show ?case by(fastforce intro: FAccRedsStatic)
next
  case SFAcc show ?case
  proof(cases b)
    case True then show ?thesis using RedSFAcc SFAcc.hyps by auto
  next
    case False then show ?thesis using SFAcc.hyps SFAccInitDoneReds[OF SFAcc.hyps(1)] by auto
  qed
next
  case (SFAccInit C F t D sh h l v' h' l' sh' sfs i v) show ?case
  proof(cases b)
    case True
    then obtain sfs where shC: "sh D = \<lfloor>(sfs, Processing)\<rfloor>"
      using SFAccInit.hyps(2) SFAccInit.prems by(clarsimp simp: bconf_def initPD_def)
    then have s': "(h',l',sh') = (h,l,sh)" using SFAccInit.hyps(3) init_ProcessingE by clarsimp
    then show ?thesis using RedSFAcc SFAccInit.hyps True by auto
  next
    case False
    then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh),False\<rangle> \<rightarrow>* \<langle>Val v',(h', l', sh'),False\<rangle>"
      using SFAccInit.hyps(4) by(auto simp: bconf_def)
    then show ?thesis using SFAccInit SFAccInitReds[OF _ _ init] False by auto
  qed
next
  case (SFAccInitThrow C F t D sh h l a s') show ?case
  proof(cases b)
    case True
    then obtain sfs where shC: "sh D = \<lfloor>(sfs, Processing)\<rfloor>"
      using SFAccInitThrow.hyps(2) SFAccInitThrow.prems(2) by(clarsimp simp: bconf_def initPD_def)
    then show ?thesis using SFAccInitThrow.hyps(3) init_ProcessingE by blast
  next
    case False
    then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh),b\<rangle> \<rightarrow>* \<langle>throw a,s',False\<rangle>"
      using SFAccInitThrow.hyps(4) by(auto simp: bconf_def)
    then show ?thesis using SFAccInitThrow SFAccInitThrowReds False by auto
  qed
next
  case SFAccNone then show ?case by(fastforce intro: SFAccRedsNone)
next
  case SFAccNonStatic then show ?case by(fastforce intro: SFAccRedsNonStatic)
next
  case (FAss e\<^sub>1 s\<^sub>0 a s\<^sub>1 e\<^sub>2 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs F t D fs' h\<^sub>2')
  show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>1" using None FAss.prems by auto
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using None FAss.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,False\<rangle>" using iconf FAss.hyps(2) by auto
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>F{D} := e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] None FAss by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using FAss.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsVal[OF b1 b2 FAss.hyps(6) FAss.hyps(5)[THEN sym]] FAss.hyps(7,8) by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) FAss.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>F{D} := e\<^sub>2,s\<^sub>1,b1\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] FAss by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using FAss.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,b1) \<surd>" using Red_preserves_bconf[OF wwf fass FAss.prems] by simp
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using FAss.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsVal[OF b1 b2] FAss.hyps(5)[THEN sym] FAss.hyps(6-8) by fast
  qed
next
  case (FAssNull e\<^sub>1 s\<^sub>0 s\<^sub>1 e\<^sub>2 v s\<^sub>2 F D)
  show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>1" using FAssNull.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using FAssNull.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1,False\<rangle>" using FAssNull.hyps(2)[OF iconf] by auto
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null\<bullet>F{D} := e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] None FAssNull by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2,False\<rangle>" using FAssNull.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsNull[OF b1 b2] by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) FAssNull.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null\<bullet>F{D} := e\<^sub>2,s\<^sub>1,b1\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] FAssNull by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using FAssNull.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,b1) \<surd>" using Red_preserves_bconf[OF wwf fass FAssNull.prems] by simp
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2,False\<rangle>" using FAssNull.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsNull[OF b1 b2] by fast
  qed
next
  case (FAssThrow1 e\<^sub>1 s\<^sub>0 e' s\<^sub>1 F D e\<^sub>2) show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have "iconf (shp s\<^sub>0) e\<^sub>1" and "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using FAssThrow1.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>1,False\<rangle>" using FAssThrow1.hyps(2) by auto
    then have "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>1,False\<rangle>"
      using FAssThrow1 None by(auto dest!:eval_final simp: FAssRedsThrow1[OF b1])
    then show ?thesis by fast
  next
    case (Some a)
    then show ?thesis using eval_final_same[OF FAssThrow1.hyps(1)] val_of_spec[OF Some] by auto
  qed
next
  case (FAssThrow2 e\<^sub>1 s\<^sub>0 v s\<^sub>1 e\<^sub>2 e' s\<^sub>2 F D)
  show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>1" using None FAssThrow2.prems by auto
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using None FAssThrow2.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,False\<rangle>" using iconf FAssThrow2.hyps(2) by auto
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<bullet>F{D} := e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] None FAssThrow2 by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>2,False\<rangle>" using FAssThrow2.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsThrow2[OF b1 b2] by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) FAssThrow2.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<bullet>F{D} := e\<^sub>2,s\<^sub>1,b1\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] FAssThrow2 by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using FAssThrow2.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,b1) \<surd>" using Red_preserves_bconf[OF wwf fass FAssThrow2.prems] by simp
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>2,False\<rangle>" using FAssThrow2.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsThrow2[OF b1 b2] by fast
  qed
next
  case (FAssNone e\<^sub>1 s\<^sub>0 a s\<^sub>1 e\<^sub>2 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs F D)
  show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>1" using None FAssNone.prems by auto
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using None FAssNone.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,False\<rangle>" using iconf FAssNone.hyps(2) by auto
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>F{D} := e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] None FAssNone by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using FAssNone.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsNone[OF b1 b2 FAssNone.hyps(5,6)] by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) FAssNone.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>F{D} := e\<^sub>2,s\<^sub>1,b1\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] FAssNone by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using FAssNone.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,b1) \<surd>" using Red_preserves_bconf[OF wwf fass FAssNone.prems] by simp
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using FAssNone.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsNone[OF b1 b2 FAssNone.hyps(5,6)] by fast
  qed
next
  case (FAssStatic e\<^sub>1 s\<^sub>0 a s\<^sub>1 e\<^sub>2 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs F t D)
  show ?case
  proof(cases "val_of e\<^sub>1")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>1" using None FAssStatic.prems by auto
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using None FAssStatic.prems by auto
    then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,False\<rangle>" using iconf FAssStatic.hyps(2) by auto
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>F{D} := e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] None FAssStatic by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using FAssStatic.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsStatic[OF b1 b2 FAssStatic.hyps(5,6)] by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) FAssStatic.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D} := e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>F{D} := e\<^sub>2,s\<^sub>1,b1\<rangle>" by(rule FAssReds1[OF b1])
    then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf fass] FAssStatic by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using FAssStatic.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,b1) \<surd>" using Red_preserves_bconf[OF wwf fass FAssStatic.prems] by simp
    then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using FAssStatic.hyps(4)[OF iconf2'] by auto
    then show ?thesis using FAssRedsStatic[OF b1 b2 FAssStatic.hyps(5,6)] by fast
  qed
next
  case (SFAss e\<^sub>2 s\<^sub>0 v h\<^sub>1 l\<^sub>1 sh\<^sub>1 C F t D sfs sfs' sh\<^sub>1')
  show ?case
  proof(cases "val_of e\<^sub>2")
    case None
    then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using SFAss.prems(2) by simp
    then have b1: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>" using SFAss by auto
    thus ?thesis using SFAssRedsVal[OF b1 SFAss.hyps(3,4)] SFAss.hyps(5,6) by fast
  next
    case (Some a)
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),b1\<rangle>"
      by (metis (no_types, lifting) SFAss.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    thus ?thesis using SFAssRedsVal[OF b1 SFAss.hyps(3,4)] SFAss.hyps(5,6) by fast
  qed
next
  case (SFAssInit e\<^sub>2 s\<^sub>0 v h\<^sub>1 l\<^sub>1 sh\<^sub>1 C F t D v' h' l' sh' sfs i sfs' sh'')
  then have iconf: "iconf (shp s\<^sub>0) e\<^sub>2" by simp
  show ?case
  proof(cases "val_of e\<^sub>2")
    case None
    then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using SFAssInit.prems(2) by simp
    then have reds: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
      using SFAssInit.hyps(2)[OF iconf bconf] by auto
    then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>Val v',(h', l', sh'),False\<rangle>"
      using SFAssInit.hyps(6) by(auto simp: bconf_def)
    then show ?thesis using SFAssInit SFAssInitReds[OF reds SFAssInit.hyps(3) _ init] by auto
  next
    case (Some v2) show ?thesis
    proof(cases b)
      case False
      then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" by(simp add: bconf_def)
      then have reds: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
        using SFAssInit.hyps(2)[OF iconf bconf] by auto
      then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>Val v',(h', l', sh'),False\<rangle>"
        using SFAssInit.hyps(6) by(auto simp: bconf_def)
      then show ?thesis using SFAssInit SFAssInitReds[OF reds SFAssInit.hyps(3) _ init] by auto
    next
      case True
      have e\<^sub>2: "e\<^sub>2 = Val v2" using val_of_spec[OF Some] by simp
      then have vs: "v2 = v \<and> s\<^sub>0 = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)" using eval_final_same[OF SFAssInit.hyps(1)] by simp
      then obtain sfs where shC: "sh\<^sub>1 D = \<lfloor>(sfs, Processing)\<rfloor>"
        using SFAssInit.hyps(3,4) SFAssInit.prems(2) Some True
          by(cases e\<^sub>2, auto simp: bconf_def initPD_def dest: sees_method_fun)
      then have s': "(h',l',sh') = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)" using SFAssInit.hyps(5) init_ProcessingE by clarsimp
      then show ?thesis using SFAssInit.hyps(3,7-9) True e\<^sub>2 red_reds.RedSFAss vs by auto
    qed
  qed
next
  case (SFAssInitThrow e\<^sub>2 s\<^sub>0 v h\<^sub>1 l\<^sub>1 sh\<^sub>1 C F t D a s')
  then have iconf: "iconf (shp s\<^sub>0) e\<^sub>2" by simp
  show ?case
  proof(cases "val_of e\<^sub>2")
    case None
    then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using SFAssInitThrow.prems(2) by simp
    then have reds: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
      using SFAssInitThrow.hyps(2)[OF iconf bconf] by auto
    then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>throw a,s',False\<rangle>"
      using SFAssInitThrow.hyps(6) by(auto simp: bconf_def)
    then show ?thesis using SFAssInitThrow SFAssInitThrowReds[OF reds _ _ init] by auto
  next
    case (Some v2) show ?thesis
    proof(cases b)
      case False
      then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" by(simp add: bconf_def)
      then have reds: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
        using SFAssInitThrow.hyps(2)[OF iconf bconf] by auto
      then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>throw a,s',False\<rangle>"
        using SFAssInitThrow.hyps(6) by(auto simp: bconf_def)
      then show ?thesis using SFAssInitThrow SFAssInitThrowReds[OF reds _ _ init] by auto
    next
      case True
      obtain v2 where e\<^sub>2: "e\<^sub>2 = Val v2" using val_of_spec[OF Some] by simp
      then have vs: "v2 = v \<and> s\<^sub>0 = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)"
        using eval_final_same[OF SFAssInitThrow.hyps(1)] by simp
      then obtain sfs where shC: "sh\<^sub>1 D = \<lfloor>(sfs, Processing)\<rfloor>"
       using SFAssInitThrow.hyps(4) SFAssInitThrow.prems(2) Some True
        by(cases e\<^sub>2, auto simp: bconf_def initPD_def dest: sees_method_fun)
      then show ?thesis using SFAssInitThrow.hyps(5) init_ProcessingE by blast
    qed
  qed
next
  case (SFAssThrow e\<^sub>2 s\<^sub>0 e' s\<^sub>2 C F D)
  show ?case
  proof(cases "val_of e\<^sub>2")
    case None
    then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using SFAssThrow.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>2,False\<rangle>" using SFAssThrow by auto
    thus ?thesis using SFAssRedsThrow[OF b1] by fast
  next
    case (Some a)
    then show ?thesis using eval_final_same[OF SFAssThrow.hyps(1)] val_of_spec[OF Some] by auto
  qed
next
  case (SFAssNone e\<^sub>2 s\<^sub>0 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C F D)
  show ?case
  proof(cases "val_of e\<^sub>2")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>2" using SFAssNone by simp
    then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using SFAssNone.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using SFAssNone.hyps(2) iconf by auto
    thus ?thesis using SFAssRedsNone[OF b1 SFAssNone.hyps(3)] by fast
  next
    case (Some a)
    then obtain b1 where b1: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),b1\<rangle>"
      by (metis (no_types, lifting) SFAssNone.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    thus ?thesis using SFAssRedsNone[OF b1 SFAssNone.hyps(3)] by fast
  qed
next
  case (SFAssNonStatic e\<^sub>2 s\<^sub>0 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C F t D) show ?case
  proof(cases "val_of e\<^sub>2")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e\<^sub>2" using SFAssNonStatic by simp
    then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using SFAssNonStatic.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>" using SFAssNonStatic.hyps(2) iconf by auto
    thus ?thesis using SFAssRedsNonStatic[OF b1 SFAssNonStatic.hyps(3)] by fast
  next
    case (Some a)
    then obtain b' where b1: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),b'\<rangle>"
      by (metis (no_types, lifting) SFAssNonStatic.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    thus ?thesis using SFAssRedsNonStatic[OF b1 SFAssNonStatic.hyps(3)] by fast
  qed
next
  case (CallObjThrow e s\<^sub>0 e' s\<^sub>1 M ps) show ?case
  proof(cases "val_of e")
    case None
    then have "iconf (shp s\<^sub>0) e" and "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using CallObjThrow.prems by auto
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>1,False\<rangle>" using CallObjThrow.hyps(2) by auto
    then have "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>1,False\<rangle>"
      using CallObjThrow None by(auto dest!:eval_final simp: CallRedsThrowObj[OF b1])
    then show ?thesis by fast
  next
    case (Some a)
    then show ?thesis using eval_final_same[OF CallObjThrow.hyps(1)] val_of_spec[OF Some] by auto
  qed
next
  case (CallNull e s\<^sub>0 s\<^sub>1 ps vs s\<^sub>2 M) show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e" using CallNull.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using CallNull.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1,False\<rangle>" using CallNull.hyps(2)[OF iconf] by auto
    have call: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null\<bullet>M(ps),s\<^sub>1,False\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf call] None CallNull by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,False) \<surd>" by(simp add: bconfs_def)
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,False\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,False\<rangle>" using CallNull.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsNull[OF b1 b2] by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) CallNull.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>null\<bullet>M(ps),s\<^sub>1,b1\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf fass] CallNull by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using CallNull.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,b1) \<surd>" using Red_preserves_bconf[OF wwf fass CallNull.prems] by simp
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,b1\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,False\<rangle>" using CallNull.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsNull[OF b1 b2] by fast
  qed
next
  case (CallParamsThrow e s\<^sub>0 v s\<^sub>1 es vs ex es' s\<^sub>2 M) show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e" using CallParamsThrow.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using CallParamsThrow.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,False\<rangle>" using CallParamsThrow.hyps(2)[OF iconf] by auto
    have call: "P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<bullet>M(es),s\<^sub>1,False\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) es" using Red_preserves_iconf[OF wwf call] None CallParamsThrow by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (es,False) \<surd>" by(simp add: bconfs_def)
    then have b2: "P \<turnstile> \<langle>es,s\<^sub>1,False\<rangle> [\<rightarrow>]* \<langle>map Val vs @ throw ex # es',s\<^sub>2,False\<rangle>"
      using CallParamsThrow.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsThrowParams[OF b1 b2] by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) CallParamsThrow.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v\<bullet>M(es),s\<^sub>1,b1\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) es" using Red_preserves_iconf[OF wwf fass] CallParamsThrow by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (es,b) \<surd>" using CallParamsThrow.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (es,b1) \<surd>" using Red_preserves_bconf[OF wwf fass CallParamsThrow.prems] by simp
    then have b2: "P \<turnstile> \<langle>es,s\<^sub>1,b1\<rangle> [\<rightarrow>]* \<langle>map Val vs @ throw ex # es',s\<^sub>2,False\<rangle>"
      using CallParamsThrow.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsThrowParams[OF b1 b2] by fast
  qed
next
  case (CallNone e s\<^sub>0 a s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M) show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e" using CallNone.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using CallNone.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,False\<rangle>" using CallNone.hyps(2)[OF iconf] by auto
    have call: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>M(ps),s\<^sub>1,False\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf call] None CallNone by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,False) \<surd>" by(simp add: bconfs_def)
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,False\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using CallNone.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsNone[OF b1 b2 _ CallNone.hyps(6)] CallNone.hyps(5) by fastforce
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) CallNone.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fass: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>M(ps),s\<^sub>1,b1\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf fass] CallNone by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using CallNone.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,b1) \<surd>" using Red_preserves_bconf[OF wwf fass CallNone.prems] by simp
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,b1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using CallNone.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsNone[OF b1 b2 _ CallNone.hyps(6)] CallNone.hyps(5) by fastforce
  qed
next
  case (CallStatic e s\<^sub>0 a s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M Ts T m D) show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e" using CallStatic.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using CallStatic.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,False\<rangle>" using CallStatic.hyps(2)[OF iconf] by auto
    have call: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>M(ps),s\<^sub>1,False\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf call] None CallStatic by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,False) \<surd>" by(simp add: bconfs_def)
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,False\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using CallStatic.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsStatic[OF b1 b2 _ CallStatic.hyps(6)] CallStatic.hyps(5) by fastforce
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) CallStatic.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have call: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>M(ps),s\<^sub>1,b1\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf call] CallStatic by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using CallStatic.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,b1) \<surd>" using Red_preserves_bconf[OF wwf call CallStatic.prems] by simp
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,b1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using CallStatic.hyps(4)[OF iconf2'] by auto
    then show ?thesis using CallRedsStatic[OF b1 b2 _ CallStatic.hyps(6)] CallStatic.hyps(5) by fastforce
  qed
next
  case (Call e s\<^sub>0 a s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M Ts T pns body D l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3) show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e" using Call.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using Call.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,False\<rangle>" using Call.hyps(2)[OF iconf] by auto
    have call: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>M(ps),s\<^sub>1,False\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2: "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf call] None Call by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,False) \<surd>" by(simp add: bconfs_def)
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,False\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using Call.hyps(4)[OF iconf2] by simp
    have iconf3: "iconf (shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2)) body"
      by(rule nsub_RI_iconf[OF sees_wwf_nsub_RI[OF wwf Call.hyps(6)]])
    have "P,shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2) \<turnstile>\<^sub>b (body,False) \<surd>" by(simp add: bconf_def)
    then have b3: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2', sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
      using Call.hyps(10)[OF iconf3] by simp
    show ?thesis by(rule CallRedsFinal[OF wwf b1 b2 Call.hyps(5-8) b3 eval_final[OF Call.hyps(9)]])
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) Call.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have call: "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>addr a\<bullet>M(ps),s\<^sub>1,b1\<rangle>" by(rule CallRedsObj[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) ps" using Red_preserves_iconf[OF wwf call] Call by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using Call.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (ps,b1) \<surd>" using Red_preserves_bconf[OF wwf call Call.prems] by simp
    then have b2: "P \<turnstile> \<langle>ps,s\<^sub>1,b1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using Call.hyps(4)[OF iconf2'] by auto
    have iconf3: "iconf (shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2)) body"
      by(rule nsub_RI_iconf[OF sees_wwf_nsub_RI[OF wwf Call.hyps(6)]])
    have "P,shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2) \<turnstile>\<^sub>b (body,False) \<surd>" by(simp add: bconf_def)
    then have b3: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2', sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
      using Call.hyps(10)[OF iconf3] by simp
    show ?thesis by(rule CallRedsFinal[OF wwf b1 b2 Call.hyps(5-8) b3 eval_final[OF Call.hyps(9)]])
  qed
next
  case (SCallParamsThrow es s\<^sub>0 vs ex es' s\<^sub>2 C M) show ?case
  proof(cases "map_vals_of es")
    case None
    then have iconf: "iconfs (shp s\<^sub>0) es" using SCallParamsThrow.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (es,b) \<surd>" using SCallParamsThrow.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>es,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs @ throw ex # es',s\<^sub>2,False\<rangle>"
      using SCallParamsThrow.hyps(2)[OF iconf] by simp
    show ?thesis using SCallRedsThrowParams[OF b1] by simp
  next
    case (Some vs')
    then have "es = map Val vs'" by(rule map_vals_of_spec)
    then show ?thesis using evals_finals_same[OF _ SCallParamsThrow.hyps(1)] map_Val_nthrow_neq
      by auto
  qed
next
  case (SCallNone ps s\<^sub>0 vs s\<^sub>2 C M) show ?case
  proof(cases "map_vals_of ps")
    case None
    then have iconf: "iconfs (shp s\<^sub>0) ps" using SCallNone.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using SCallNone.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,False\<rangle>" using SCallNone.hyps(2)[OF iconf] by auto
    then show ?thesis using SCallRedsNone[OF b1 SCallNone.hyps(3)] SCallNone.hyps(1) by simp
  next
    case (Some vs')
    then have ps: "ps = map Val vs'" by(rule map_vals_of_spec)
    then have s\<^sub>0: "s\<^sub>0 = s\<^sub>2" using SCallNone.hyps(1) evals_finals_same by blast
    then show ?thesis using RedSCallNone[OF SCallNone.hyps(3)] ps by(cases s\<^sub>2, auto)
  qed
next
  case (SCallNonStatic ps s\<^sub>0 vs s\<^sub>2 C M Ts T m D) show ?case
  proof(cases "map_vals_of ps")
    case None
    then have iconf: "iconfs (shp s\<^sub>0) ps" using SCallNonStatic.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using SCallNonStatic.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2,False\<rangle>" using SCallNonStatic.hyps(2)[OF iconf] by auto
    then show ?thesis using SCallRedsNonStatic[OF b1 SCallNonStatic.hyps(3)] SCallNonStatic.hyps(1) by simp
  next
    case (Some vs')
    then have ps: "ps = map Val vs'" by(rule map_vals_of_spec)
    then have s\<^sub>0: "s\<^sub>0 = s\<^sub>2" using SCallNonStatic.hyps(1) evals_finals_same by blast
    then show ?thesis using RedSCallNonStatic[OF SCallNonStatic.hyps(3)] ps by(cases s\<^sub>2, auto)
  qed
next
  case (SCallInitThrow ps s\<^sub>0 vs h\<^sub>1 l\<^sub>1 sh\<^sub>1 C M Ts T pns body D a s') show ?case
  proof(cases "map_vals_of ps")
    case None
    then have iconf: "iconfs (shp s\<^sub>0) ps" using SCallInitThrow.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using SCallInitThrow.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
      using SCallInitThrow.hyps(2)[OF iconf] by auto
    have bconf2: "P,shp (h\<^sub>1, l\<^sub>1, sh\<^sub>1) \<turnstile>\<^sub>b (INIT D ([D],False) \<leftarrow> unit,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>throw a,s',False\<rangle>"
      using SCallInitThrow.hyps(7) by auto
    then show ?thesis using SCallInitThrowReds[OF wwf b1 SCallInitThrow.hyps(3-5)]
      by(cases s', auto)
  next
    case (Some vs')
    have ps: "ps = map Val vs'" by(rule map_vals_of_spec[OF Some])
    then have vs: "vs = vs' \<and> s\<^sub>0 = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)"
      using evals_finals_same[OF _ SCallInitThrow.hyps(1)] map_Val_eq by auto
    show ?thesis
    proof(cases b)
      case True
      obtain sfs where shC: "sh\<^sub>1 D = \<lfloor>(sfs, Processing)\<rfloor>"
        using SCallInitThrow.hyps(3,4) SCallInitThrow.prems(2) True Some vs
          by(auto simp: bconf_def initPD_def dest: sees_method_fun)
      then show ?thesis using init_ProcessingE[OF _ SCallInitThrow.hyps(6)] by blast
    next
      case False
      then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>" using ps vs by simp
      have bconf2: "P,shp (h\<^sub>1, l\<^sub>1, sh\<^sub>1) \<turnstile>\<^sub>b (INIT D ([D],False) \<leftarrow> unit,False) \<surd>" by(simp add: bconf_def)
      then have b2: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>throw a,s',False\<rangle>"
        using SCallInitThrow.hyps(7) by auto
      then show ?thesis using SCallInitThrowReds[OF wwf b1 SCallInitThrow.hyps(3-5)] by(cases s', auto)
    qed
  qed
next
  case (SCallInit ps s\<^sub>0 vs h\<^sub>1 l\<^sub>1 sh\<^sub>1 C M Ts T pns body D v' h\<^sub>2 l\<^sub>2 sh\<^sub>2 l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3) show ?case
  proof(cases "map_vals_of ps")
    case None
    then have iconf: "iconfs (shp s\<^sub>0) ps" using SCallInit.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using SCallInit.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
      using SCallInit.hyps(2)[OF iconf] by auto
    have bconf2: "P,shp (h\<^sub>1, l\<^sub>1, sh\<^sub>1) \<turnstile>\<^sub>b (INIT D ([D],False) \<leftarrow> unit,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>Val v',(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using SCallInit.hyps(7) by auto
    have iconf3: "iconf (shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2)) body"
      by(rule nsub_RI_iconf[OF sees_wwf_nsub_RI[OF wwf SCallInit.hyps(3)]])
    have "P,shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2) \<turnstile>\<^sub>b (body,False) \<surd>" by(simp add: bconf_def)
    then have b3: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2', sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
      using SCallInit.hyps(11)[OF iconf3] by simp
    show ?thesis by(rule SCallInitReds[OF wwf b1 SCallInit.hyps(3-5) b2 SCallInit.hyps(8-9)
                           b3 eval_final[OF SCallInit.hyps(10)]])
  next
    case (Some vs')
    then have ps: "ps = map Val vs'" by(rule map_vals_of_spec)
    then have vs: "vs = vs' \<and> s\<^sub>0 = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)"
      using evals_finals_same[OF _ SCallInit.hyps(1)] map_Val_eq by auto
    show ?thesis
    proof(cases b)
      case True
      then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),b\<rangle>" using ps vs by simp
      obtain sfs where shC: "sh\<^sub>1 D = \<lfloor>(sfs, Processing)\<rfloor>"
        using SCallInit.hyps(3,4) SCallInit.prems(2) True Some vs
          by(auto simp: bconf_def initPD_def dest: sees_method_fun)
      then have s': "(h\<^sub>1, l\<^sub>1, sh\<^sub>1) = (h\<^sub>2, l\<^sub>2, sh\<^sub>2)" using init_ProcessingE[OF _ SCallInit.hyps(6)] by simp
      have iconf3: "iconf (shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2)) body"
        by(rule nsub_RI_iconf[OF sees_wwf_nsub_RI[OF wwf SCallInit.hyps(3)]])
      have "P,shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2) \<turnstile>\<^sub>b (body,False) \<surd>" by(simp add: bconf_def)
      then have b3: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2', sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
        using SCallInit.hyps(11)[OF iconf3] by simp
      then have b3': "P \<turnstile> \<langle>body,(h\<^sub>1, l\<^sub>2', sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
        using s' by simp
      then show ?thesis using SCallInitProcessingReds[OF wwf b1 SCallInit.hyps(3) shC
                           SCallInit.hyps(8-9) b3' eval_final[OF SCallInit.hyps(10)]] s' by simp
    next
      case False
      then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>" using ps vs by simp
      have bconf2: "P,shp (h\<^sub>1, l\<^sub>1, sh\<^sub>1) \<turnstile>\<^sub>b (INIT D ([D],False) \<leftarrow> unit,False) \<surd>" by(simp add: bconf_def)
      then have b2: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>Val v',(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
        using SCallInit.hyps(7) by auto
      have iconf3: "iconf (shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2)) body"
        by(rule nsub_RI_iconf[OF sees_wwf_nsub_RI[OF wwf SCallInit.hyps(3)]])
      have "P,shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2) \<turnstile>\<^sub>b (body,False) \<surd>" by(simp add: bconf_def)
      then have b3: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2', sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
        using SCallInit.hyps(11)[OF iconf3] by simp
      show ?thesis by(rule SCallInitReds[OF wwf b1 SCallInit.hyps(3-5) b2 SCallInit.hyps(8-9)
                             b3 eval_final[OF SCallInit.hyps(10)]])
    qed
  qed
next
  case (SCall ps s\<^sub>0 vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C M Ts T pns body D sfs l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3) show ?case
  proof(cases "map_vals_of ps")
    case None
    then have iconf: "iconfs (shp s\<^sub>0) ps" using SCall.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (ps,b) \<surd>" using SCall.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
      using SCall.hyps(2)[OF iconf] by auto
    have iconf3: "iconf (shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2)) body"
      by(rule nsub_RI_iconf[OF sees_wwf_nsub_RI[OF wwf SCall.hyps(3)]])
    have "P,shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2) \<turnstile>\<^sub>b (body,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2', sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
      using SCall.hyps(8)[OF iconf3] by simp
    show ?thesis by(rule SCallRedsFinal[OF wwf b1 SCall.hyps(3-6) b2 eval_final[OF SCall.hyps(7)]])
  next
    case (Some vs')
    then have ps: "ps = map Val vs'" by(rule map_vals_of_spec)
    then have vs: "vs = vs' \<and> s\<^sub>0 = (h\<^sub>2, l\<^sub>2, sh\<^sub>2)"
      using evals_finals_same[OF _ SCall.hyps(1)] map_Val_eq by auto
    then have b1: "P \<turnstile> \<langle>ps,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2, l\<^sub>2, sh\<^sub>2),b\<rangle>" using ps by simp
    have iconf3: "iconf (shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2)) body"
      by(rule nsub_RI_iconf[OF sees_wwf_nsub_RI[OF wwf SCall.hyps(3)]])
    have "P,shp (h\<^sub>2, l\<^sub>2', sh\<^sub>2) \<turnstile>\<^sub>b (body,False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2', sh\<^sub>2),False\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3),False\<rangle>"
      using SCall.hyps(8)[OF iconf3] by simp
    show ?thesis by(rule SCallRedsFinal[OF wwf b1 SCall.hyps(3-6) b2 eval_final[OF SCall.hyps(7)]])
  qed
next
  case (Block e\<^sub>0 h\<^sub>0 l\<^sub>0 V sh\<^sub>0 e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 T)
  have iconf: "iconf (shp (h\<^sub>0, l\<^sub>0(V := None), sh\<^sub>0)) e\<^sub>0"
    using Block.prems(1) by (auto simp: assigned_def)
  have bconf: "P,shp (h\<^sub>0, l\<^sub>0(V := None), sh\<^sub>0) \<turnstile>\<^sub>b (e\<^sub>0,b) \<surd>" using Block.prems(2)
    by(auto simp: bconf_def)
  then have b': "P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0, l\<^sub>0(V := None), sh\<^sub>0),b\<rangle> \<rightarrow>* \<langle>e\<^sub>1,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
    using Block.hyps(2)[OF iconf] by auto
  have fin: "final e\<^sub>1" using Block by(auto dest: eval_final)
  thus ?case using BlockRedsFinal[OF b' fin] by simp
next
  case (Seq e\<^sub>0 s\<^sub>0 v s\<^sub>1 e\<^sub>1 e\<^sub>2 s\<^sub>2)
  then have iconf: "iconf (shp s\<^sub>0) e\<^sub>0" using Seq.prems(1)
    by(auto dest: val_of_spec lass_val_of_spec)
  have b1: "\<exists>b1. P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b1\<rangle>"
  proof(cases "val_of e\<^sub>0")
    case None show ?thesis
    proof(cases "lass_val_of e\<^sub>0")
      case lNone:None
      then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e\<^sub>0,b) \<surd>" using Seq.prems(2) None by simp
      then have "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,False\<rangle>" using iconf Seq.hyps(2) by auto
      then show ?thesis by fast
    next
      case (Some p)
      obtain V' v' where p: "p = (V',v')" and e\<^sub>0: "e\<^sub>0 = V':=Val v'"
        using lass_val_of_spec[OF Some] by(cases p, auto)
      obtain h l sh h' l' sh' where s\<^sub>0: "s\<^sub>0 = (h,l,sh)" and s\<^sub>1: "s\<^sub>1 = (h',l',sh')" by(cases s\<^sub>0, cases s\<^sub>1)
      then have eval: "P \<turnstile> \<langle>e\<^sub>0,(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h',l',sh')\<rangle>" using Seq.hyps(1) by simp
      then have s\<^sub>1': "Val v = unit \<and> h' = h \<and> l' = l(V' \<mapsto> v') \<and> sh' = sh"
        using lass_val_of_eval[OF Some eval] p e\<^sub>0 by simp
      then have "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<rangle> \<rightarrow> \<langle>Val v,s\<^sub>1,b\<rangle>" using e\<^sub>0 s\<^sub>0 s\<^sub>1 by(auto intro: RedLAss)
      then show ?thesis by auto
    qed
  next
    case (Some a)
    then have "e\<^sub>0 = Val v" and "s\<^sub>0 = s\<^sub>1" using Seq.hyps(1) eval_cases(3) val_of_spec by blast+
    then show ?thesis using Seq by auto
  qed
  then obtain b1 where b1': "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b1\<rangle>" by clarsimp
  have seq: "P \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v;;e\<^sub>1,s\<^sub>1,b1\<rangle>" by(rule SeqReds[OF b1'])
  then have iconf2: "iconf (shp s\<^sub>1) e\<^sub>1" using Red_preserves_iconf[OF wwf seq] Seq nsub_RI_iconf
    by auto
  have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (Val v;; e\<^sub>1,b1) \<surd>" by(rule Red_preserves_bconf[OF wwf seq Seq.prems])
  then have bconf2: "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>1,b1) \<surd>" by simp
  have b2: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1,b1\<rangle> \<rightarrow>* \<langle>e\<^sub>2,s\<^sub>2,False\<rangle>" by(rule Seq.hyps(4)[OF iconf2 bconf2])
  then show ?case using SeqReds2[OF b1' b2] by fast
next
  case (SeqThrow e\<^sub>0 s\<^sub>0 a s\<^sub>1 e\<^sub>1 b)
  have notVal: "val_of e\<^sub>0 = None" "lass_val_of e\<^sub>0 = None"
    using SeqThrow.hyps(1) eval_throw_nonVal eval_throw_nonLAss by auto
  thus ?case using SeqThrow notVal by(auto dest!:eval_final dest: SeqRedsThrow)
next
  case (CondT e s\<^sub>0 s\<^sub>1 e\<^sub>1 e' s\<^sub>2 e\<^sub>2)
  then have iconf: "iconf (shp s\<^sub>0) e" using CondT.prems(1) by auto
  have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using CondT.prems(2) by auto
  then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1,False\<rangle>" using iconf CondT.hyps(2) by auto
  have cond: "P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>if (true) e\<^sub>1 else e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule CondReds[OF b1])
  then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>1" using Red_preserves_iconf[OF wwf cond] CondT nsub_RI_iconf
    by auto
  have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>1,False) \<surd>" by(simp add: bconf_def)
  then have b2: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2,False\<rangle>" using CondT.hyps(4)[OF iconf2'] by auto
  then show ?case using CondReds2T[OF b1 b2] by fast
next
  case (CondF e s\<^sub>0 s\<^sub>1 e\<^sub>2 e' s\<^sub>2 e\<^sub>1)
  then have iconf: "iconf (shp s\<^sub>0) e" using CondF.prems(1) by auto
  have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using CondF.prems(2) by auto
  then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>false,s\<^sub>1,False\<rangle>" using iconf CondF.hyps(2) by auto
  have cond: "P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>if (false) e\<^sub>1 else e\<^sub>2,s\<^sub>1,False\<rangle>" by(rule CondReds[OF b1])
  then have iconf2': "iconf (shp s\<^sub>1) e\<^sub>2" using Red_preserves_iconf[OF wwf cond] CondF nsub_RI_iconf
    by auto
  have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
  then have b2: "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2,False\<rangle>" using CondF.hyps(4)[OF iconf2'] by auto
  then show ?case using CondReds2F[OF b1 b2] by fast
next
  case CondThrow thus ?case by(auto dest!:eval_final dest:CondRedsThrow)
next
  case (WhileF e s\<^sub>0 s\<^sub>1 c)
  then have iconf: "iconf (shp s\<^sub>0) e" using nsub_RI_iconf by auto
  then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using WhileF.prems(2) by(simp add: bconf_def)
  then have b': "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>false,s\<^sub>1,False\<rangle>" using WhileF.hyps(2) iconf by auto
  thus ?case using WhileFReds[OF b'] by fast
next
  case (WhileT e s\<^sub>0 s\<^sub>1 c v\<^sub>1 s\<^sub>2 e\<^sub>3 s\<^sub>3)
  then have iconf: "iconf (shp s\<^sub>0) e" using nsub_RI_iconf by auto
  then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using WhileT.prems(2) by(simp add: bconf_def)
  then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1,False\<rangle>" using WhileT.hyps(2) iconf by auto
  have iconf2: "iconf (shp s\<^sub>1) c" using WhileT.prems(1) nsub_RI_iconf by auto
  have bconf2: "P,shp s\<^sub>1 \<turnstile>\<^sub>b (c,False) \<surd>" by(simp add: bconf_def)
  then have b2: "P \<turnstile> \<langle>c,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>2,False\<rangle>" using WhileT.hyps(4) iconf2 by auto
  have iconf3: "iconf (shp s\<^sub>2) (while (e) c)" using WhileT.prems(1) by auto
  have "P,shp s\<^sub>2 \<turnstile>\<^sub>b (while (e) c,False) \<surd>" by(simp add: bconf_def)
  then have b3: "P \<turnstile> \<langle>while (e) c,s\<^sub>2,False\<rangle> \<rightarrow>* \<langle>e\<^sub>3,s\<^sub>3,False\<rangle>" using WhileT.hyps(6) iconf3 by auto
  show ?case using WhileTReds[OF b1 b2 b3] by fast
next
  case WhileCondThrow thus ?case
    by (metis (no_types, lifting) WhileRedsThrow iconf.simps(16) bconf_While bconf_def nsub_RI_iconf)
next
  case (WhileBodyThrow e s\<^sub>0 s\<^sub>1 c e' s\<^sub>2)
  then have iconf: "iconf (shp s\<^sub>0) e" using nsub_RI_iconf by auto
  then have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using WhileBodyThrow.prems(2) by(simp add: bconf_def)
  then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1,False\<rangle>" using WhileBodyThrow.hyps(2) iconf by auto
  have iconf2: "iconf (shp s\<^sub>1) c" using WhileBodyThrow.prems(1) nsub_RI_iconf by auto
  have bconf2: "P,shp s\<^sub>1 \<turnstile>\<^sub>b (c,False) \<surd>" by(simp add: bconf_def)
  then have b2: "P \<turnstile> \<langle>c,s\<^sub>1,False\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>2,False\<rangle>" using WhileBodyThrow.hyps(4) iconf2 by auto
  show ?case using WhileTRedsThrow[OF b1 b2] by fast
next
  case Throw thus ?case by (meson ThrowReds iconf.simps(17) bconf_Throw)
next
  case ThrowNull thus ?case by (meson ThrowRedsNull iconf.simps(17) bconf_Throw)
next
  case ThrowThrow thus ?case by (meson ThrowRedsThrow iconf.simps(17) bconf_Throw)
next
  case Try thus ?case by (meson TryRedsVal iconf.simps(18) bconf_Try)
next
  case (TryCatch e\<^sub>1 s\<^sub>0 a h\<^sub>1 l\<^sub>1 sh\<^sub>1 D fs C e\<^sub>2 V e\<^sub>2' h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  then have b1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Throw a,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>" by auto
  have Try: "P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>try (Throw a) catch(C V) e\<^sub>2,(h\<^sub>1, l\<^sub>1, sh\<^sub>1),False\<rangle>"
    by(rule TryReds[OF b1])
  have iconf: "iconf sh\<^sub>1 e\<^sub>2" using Red_preserves_iconf[OF wwf Try] TryCatch nsub_RI_iconf
    by auto
  have bconf: "P,shp (h\<^sub>1, l\<^sub>1(V \<mapsto> Addr a), sh\<^sub>1) \<turnstile>\<^sub>b (e\<^sub>2,False) \<surd>" by(simp add: bconf_def)
  then have b2: "P \<turnstile> \<langle>e\<^sub>2,(h\<^sub>1, l\<^sub>1(V \<mapsto> Addr a), sh\<^sub>1),False\<rangle> \<rightarrow>* \<langle>e\<^sub>2',(h\<^sub>2, l\<^sub>2, sh\<^sub>2),False\<rangle>"
    using TryCatch.hyps(6) iconf by auto
  thus ?case using TryCatchRedsFinal[OF b1] TryCatch.hyps(3-5) by (meson eval_final)
next
  case TryThrow thus ?case by (meson TryRedsFail iconf.simps(18) bconf_Try)
next
  case Nil thus ?case by(auto simp: bconfs_def)
next
  case (Cons e s\<^sub>0 v s\<^sub>1 es es' s\<^sub>2) show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e" using Cons.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using Cons.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,False\<rangle>" using Cons.hyps(2) iconf by auto
    have cons: "P \<turnstile> \<langle>e # es,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>Val v # es,s\<^sub>1,False\<rangle>" by(rule ListReds1[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) es" using Reds_preserves_iconf[OF wwf cons] None Cons by auto
    have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (es,False) \<surd>" by(simp add: bconfs_def)
    then have b2: "P \<turnstile> \<langle>es,s\<^sub>1,False\<rangle> [\<rightarrow>]* \<langle>es',s\<^sub>2,False\<rangle>" using Cons.hyps(4)[OF iconf2'] by auto
    show ?thesis using ListRedsVal[OF b1 b2] by auto
  next
    case (Some a)
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1,b1\<rangle>"
      by (metis (no_types, lifting) Cons.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have cons: "P \<turnstile> \<langle>e # es,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>Val v # es,s\<^sub>1,b1\<rangle>" by(rule ListReds1[OF b1])
    then have iconf2': "iconfs (shp s\<^sub>1) es" using Reds_preserves_iconf[OF wwf cons] Cons by auto
    have bconf2: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (es,b) \<surd>" using Cons.prems Some by simp
    then have "P,shp s\<^sub>1 \<turnstile>\<^sub>b (es,b1) \<surd>" using Reds_preserves_bconf[OF wwf cons Cons.prems] by simp
    then have b2: "P \<turnstile> \<langle>es,s\<^sub>1,b1\<rangle> [\<rightarrow>]* \<langle>es',s\<^sub>2,False\<rangle>" using Cons.hyps(4)[OF iconf2'] by auto
    show ?thesis using ListRedsVal[OF b1 b2] by auto
  qed
next
  case (ConsThrow e s\<^sub>0 e' s\<^sub>1 es) show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s\<^sub>0) e" using ConsThrow.prems(1) by simp
    have bconf: "P,shp s\<^sub>0 \<turnstile>\<^sub>b (e,b) \<surd>" using ConsThrow.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s\<^sub>0,b\<rangle> \<rightarrow>* \<langle>throw e',s\<^sub>1,False\<rangle>" using ConsThrow.hyps(2) iconf by auto
    have cons: "P \<turnstile> \<langle>e # es,s\<^sub>0,b\<rangle> [\<rightarrow>]* \<langle>throw e' # es,s\<^sub>1,False\<rangle>" by(rule ListReds1[OF b1])
    then show ?thesis by fast
  next
    case (Some a)
    then show ?thesis using eval_final_same[OF ConsThrow.hyps(1)] val_of_spec[OF Some] by auto
  qed
next
  case (InitFinal e s e' s' C b')
  then have "\<not>sub_RI e" by simp
  then show ?case using InitFinal RedInit[of e C b' s b P]
    by (meson converse_rtrancl_into_rtrancl nsub_RI_iconf red_preserves_bconf RedInit)
next
  case (InitNone sh C C' Cs e h l e' s')
  then have init: "P \<turnstile> \<langle>INIT C' (C # Cs,False) \<leftarrow> e,(h, l, sh(C \<mapsto> (sblank P C, Prepared))),b\<rangle> \<rightarrow>* \<langle>e',s',False\<rangle>"
    by(simp add: bconf_def)
  show ?case by(rule InitNoneReds[OF InitNone.hyps(1) init])
next
  case (InitDone sh C sfs C' Cs e h l e' s')
  then have "iconf (shp (h, l, sh)) (INIT C' (Cs,True) \<leftarrow> e)" using InitDone.hyps(1)
  proof(cases Cs)
    case Nil
    then have "C = C'" "\<not>sub_RI e" using InitDone.prems(1) by simp+
    then show ?thesis using Nil InitDone.hyps(1) by(simp add: initPD_def)
  qed(auto)
  then have init: "P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h, l, sh),b\<rangle> \<rightarrow>* \<langle>e',s',False\<rangle>"
    using InitDone by(simp add: bconf_def)
  show ?case by(rule InitDoneReds[OF InitDone.hyps(1) init])
next
  case (InitProcessing sh C sfs C' Cs e h l e' s')
  then have "iconf (shp (h, l, sh)) (INIT C' (Cs,True) \<leftarrow> e)" using InitProcessing.hyps(1)
  proof(cases Cs)
    case Nil
    then have "C = C'" "\<not>sub_RI e" using InitProcessing.prems(1) by simp+
    then show ?thesis using Nil InitProcessing.hyps(1) by(simp add: initPD_def)
  qed(auto)
  then have init: "P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h, l, sh),b\<rangle> \<rightarrow>* \<langle>e',s',False\<rangle>"
    using InitProcessing by(simp add: bconf_def)
  show ?case by(rule InitProcessingReds[OF InitProcessing.hyps(1) init])
next
  case InitError thus ?case by(fastforce intro: InitErrorReds simp: bconf_def)
next
  case InitObject thus ?case by(fastforce intro: InitObjectReds simp: bconf_def)
next
  case InitNonObject thus ?case by(fastforce intro: InitNonObjectReds simp: bconf_def)
next
  case InitRInit thus ?case by(fastforce intro: RedsInitRInit simp: bconf_def)
next
  case (RInit e s v h' l' sh' C sfs i sh'' C' Cs e' e\<^sub>1 s\<^sub>1)
  then have iconf2: "iconf (shp (h', l', sh'')) (INIT C' (Cs,True) \<leftarrow> e')"
    by(auto simp: initPD_def fun_upd_same list_nonempty_induct)
  show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s) e" using RInit.prems(1) by simp
    have bconf: "P,shp s \<turnstile>\<^sub>b (e,b) \<surd>" using RInit.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Val v,(h',l',sh'),False\<rangle>" using RInit.hyps(2)[OF iconf] by auto
    have "P,shp (h', l', sh'') \<turnstile>\<^sub>b (INIT C' (Cs,True) \<leftarrow> e',False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e',(h',l',sh''),False\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s\<^sub>1,False\<rangle>"
      using RInit.hyps(7)[OF iconf2] by auto
    then show ?thesis using RedsRInit[OF b1 RInit.hyps(3-5) b2] by fast
  next
    case (Some a')
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Val v,(h',l',sh'),b1\<rangle>"
      by (metis (no_types, lifting) RInit.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fin: "final e" by(simp add: val_of_spec[OF Some])
    have "\<not>b" using RInit.prems(2) Some by(simp add: bconf_def)
    then have nb1: "\<not>b1" using reds_final_same[OF b1 fin] by simp
    have "P,shp (h', l', sh'') \<turnstile>\<^sub>b (INIT C' (Cs,True) \<leftarrow> e',b1) \<surd>" using nb1
      by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e',(h', l', sh''),b1\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s\<^sub>1,False\<rangle>"
      using RInit.hyps(7)[OF iconf2] by auto
    then show ?thesis using RedsRInit[OF b1 RInit.hyps(3-5) b2] by fast
  qed
next
  case (RInitInitFail e s a h' l' sh' C sfs i sh'' D Cs e' e\<^sub>1 s\<^sub>1)
  have fin: "final (throw a)" using eval_final[OF RInitInitFail.hyps(1)] by simp
  then obtain a' where a': "throw a = Throw a'" by auto
  have iconf2: "iconf (shp (h', l', sh'')) (RI (D,Throw a') ; Cs \<leftarrow> e')"
    using RInitInitFail.prems(1) by auto
  show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s) e" using RInitInitFail.prems(1) by simp
    have bconf: "P,shp s \<turnstile>\<^sub>b (e,b) \<surd>" using RInitInitFail.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Throw a',(h',l',sh'),False\<rangle>"
      using RInitInitFail.hyps(2)[OF iconf] a' by auto
    have "P,shp (h', l', sh'') \<turnstile>\<^sub>b (RI (D,Throw a') ; Cs \<leftarrow> e',False) \<surd>" by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>RI (D,Throw a') ; Cs \<leftarrow> e',(h',l',sh''),False\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s\<^sub>1,False\<rangle>"
      using RInitInitFail.hyps(6) iconf2 a' by auto
    show ?thesis using RInitInitThrowReds[OF b1 RInitInitFail.hyps(3-4) b2] by fast
  next
    case (Some a1)
    then obtain b1 where b1: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Throw a',(h',l',sh'),b1\<rangle>" using a'
      by (metis (no_types, lifting) RInitInitFail.hyps(1) eval_cases(3) rtrancl.rtrancl_refl val_of_spec)
    have fin: "final e" by(simp add: val_of_spec[OF Some])
    have "\<not>b" using RInitInitFail.prems(2) Some by(simp add: bconf_def)
    then have nb1: "\<not>b1" using reds_final_same[OF b1 fin] by simp
    have "P,shp (h', l', sh'') \<turnstile>\<^sub>b (RI (D,Throw a') ; Cs \<leftarrow> e',b1) \<surd>" using nb1
      by(simp add: bconf_def)
    then have b2: "P \<turnstile> \<langle>RI (D,Throw a') ; Cs \<leftarrow> e',(h', l', sh''),b1\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s\<^sub>1,False\<rangle>"
      using RInitInitFail.hyps(6) iconf2 a' by auto
    show ?thesis using RInitInitThrowReds[OF b1 RInitInitFail.hyps(3-4) b2] by fast
  qed
next
  case (RInitFailFinal e s a h' l' sh' C sfs i sh'' e')
  have fin: "final (throw a)" using eval_final[OF RInitFailFinal.hyps(1)] by simp
  then obtain a' where a': "throw a = Throw a'" by auto
  show ?case
  proof(cases "val_of e")
    case None
    then have iconf: "iconf (shp s) e" using RInitFailFinal.prems(1) by simp
    have bconf: "P,shp s \<turnstile>\<^sub>b (e,b) \<surd>" using RInitFailFinal.prems(2) None by simp
    then have b1: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>Throw a',(h',l',sh'),False\<rangle>"
      using RInitFailFinal.hyps(2)[OF iconf] a' by auto
    show ?thesis using RInitThrowReds[OF b1 RInitFailFinal.hyps(3-4)] a' by fast
  next
    case (Some a1)
    then show ?thesis using eval_final_same[OF RInitFailFinal.hyps(1)] val_of_spec[OF Some] by auto
  qed
qed
(*>*)


subsection\<open>Big steps simulates small step\<close>

text\<open> This direction was carried out by Norbert Schirmer and Daniel
Wasserrab (and modified to include statics and DCI by Susannah Mansky). \<close>

text \<open> The big step equivalent of @{text RedWhile}: \<close> 

lemma unfold_while: 
  "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>  =  P \<turnstile> \<langle>if(b) (c;;while(b) c) else (unit),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
(*<*)
proof
  assume "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  thus "P \<turnstile> \<langle>if (b) (c;; while (b) c) else unit,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    by cases (fastforce intro: eval_evals.intros)+
next
  assume "P \<turnstile> \<langle>if (b) (c;; while (b) c) else unit,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  thus "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  proof (cases)
    fix a
    assume e': "e' = throw a"
    assume "P \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"  
    hence "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>" by (rule WhileCondThrow)
    with e' show ?thesis by simp
  next
    fix s\<^sub>1
    assume eval_false: "P \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>"
    and eval_unit: "P \<turnstile> \<langle>unit,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    with eval_unit have "s' = s\<^sub>1" "e' = unit" by (auto elim: eval_cases)
    moreover from eval_false have "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"
      by - (rule WhileF, simp)
    ultimately show ?thesis by simp
  next
    fix s\<^sub>1
    assume eval_true: "P \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>"
    and eval_rest: "P \<turnstile> \<langle>c;; while (b) c,s\<^sub>1\<rangle>\<Rightarrow>\<langle>e',s'\<rangle>"
    from eval_rest show ?thesis
    proof (cases)
      fix s\<^sub>2 v\<^sub>1
      assume "P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>" "P \<turnstile> \<langle>while (b) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
      with eval_true show "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by (rule WhileT)
    next
      fix a
      assume "P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>" "e' = throw a"
      with eval_true show "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"        
        by (iprover intro: WhileBodyThrow)
    qed
  qed
qed
(*>*)


lemma blocksEval:
  "\<And>Ts vs l l'. \<lbrakk>size ps = size Ts; size ps = size vs; P \<turnstile> \<langle>blocks(ps,Ts,vs,e),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<rbrakk>
    \<Longrightarrow> \<exists> l''. P \<turnstile> \<langle>e,(h,l(ps[\<mapsto>]vs),sh)\<rangle> \<Rightarrow> \<langle>e',(h',l'',sh')\<rangle>"
(*<*)
proof (induct ps)
  case Nil then show ?case by fastforce
next
  case (Cons p ps')
  have length_eqs: "length (p # ps') = length Ts" 
                   "length (p # ps') = length vs" by fact+
  then obtain T Ts' where Ts: "Ts = T#Ts'" by (cases "Ts") simp
  obtain v vs' where vs: "vs = v#vs'" using length_eqs by (cases "vs") simp
  have "P \<turnstile> \<langle>blocks (p # ps', Ts, vs, e),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h', l',sh')\<rangle>" by fact
  with Ts vs 
  have "P \<turnstile> \<langle>{p:T := Val v; blocks (ps', Ts', vs', e)},(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h', l',sh')\<rangle>"
    by simp
  then obtain l''' where
    eval_ps': "P \<turnstile> \<langle>blocks (ps', Ts', vs', e),(h, l(p\<mapsto>v), sh)\<rangle> \<Rightarrow> \<langle>e',(h', l''', sh')\<rangle>"
    and l''': "l'=l'''(p:=l p)"
    by (auto elim!: eval_cases)
  then obtain l'' where 
    hyp: "P \<turnstile> \<langle>e,(h, l(p\<mapsto>v)(ps'[\<mapsto>]vs'), sh)\<rangle> \<Rightarrow> \<langle>e',(h', l'', sh')\<rangle>"
    using length_eqs Ts vs Cons.hyps [OF _ _ eval_ps'] by auto
  from hyp
  show "\<exists>l''. P \<turnstile> \<langle>e,(h, l(p # ps'[\<mapsto>]vs), sh)\<rangle> \<Rightarrow> \<langle>e',(h', l'', sh')\<rangle>"
    using Ts vs by auto
qed
(*>*)

lemma
assumes wf: "wwf_J_prog P"
shows eval_restrict_lcl:
  "P \<turnstile> \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<Longrightarrow> (\<And>W. fv e \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e,(h,l|`W,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l'|`W,sh')\<rangle>)"
and "P \<turnstile> \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle> \<Longrightarrow> (\<And>W. fvs es \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>es,(h,l|`W,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l'|`W,sh')\<rangle>)"
(*<*)
proof(induct rule:eval_evals_inducts)
  case (Block e\<^sub>0 h\<^sub>0 l\<^sub>0 V sh\<^sub>0 e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 T)
  have IH: "\<And>W. fv e\<^sub>0 \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None)|`W,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1|`W,sh\<^sub>1)\<rangle>" by fact
  have "fv({V:T; e\<^sub>0}) \<subseteq> W" by fact+
  hence "fv e\<^sub>0 - {V} \<subseteq> W" by simp_all
  hence "fv e\<^sub>0 \<subseteq> insert V W" by fast
  from IH[OF this]
  have "P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0, (l\<^sub>0|`W)(V := None), sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1, l\<^sub>1|`insert V W, sh\<^sub>1)\<rangle>"
    by fastforce
  from eval_evals.Block[OF this] show ?case by fastforce
next
  case Seq thus ?case by simp (blast intro:eval_evals.Seq)
next
  case New thus ?case by(simp add:eval_evals.intros)
next
  case NewFail thus ?case by(simp add:eval_evals.intros)
next
  case (NewInit sh C h l v' h' l' sh' a h'')
  have "fv(INIT C ([C],False) \<leftarrow> unit) \<subseteq> W" by simp
  then have "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h, l |` W, sh)\<rangle> \<Rightarrow> \<langle>Val v',(h', l' |` W, sh')\<rangle>"
    by (simp add: NewInit.hyps(3))
  thus ?case using NewInit.hyps(1,4-6) eval_evals.NewInit by blast
next
  case (NewInitOOM sh C h l v' h' l' sh')
  have "fv(INIT C ([C],False) \<leftarrow> unit) \<subseteq> W" by simp
  then have "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h, l |` W, sh)\<rangle> \<Rightarrow> \<langle>Val v',(h', l' |` W, sh')\<rangle>"
    by (simp add: NewInitOOM.hyps(3))
  thus ?case
    using NewInitOOM.hyps(1,4,5) eval_evals.NewInitOOM by auto
next
  case NewInitThrow thus ?case by(simp add:eval_evals.intros)
next
  case Cast thus ?case by simp (blast intro:eval_evals.Cast)
next
  case CastNull thus ?case by simp (blast intro:eval_evals.CastNull)
next
  case CastFail thus ?case by simp (blast intro:eval_evals.CastFail)
next
  case CastThrow thus ?case by(simp add:eval_evals.intros)
next
  case Val thus ?case by(simp add:eval_evals.intros)
next
  case BinOp thus ?case by simp (blast intro:eval_evals.BinOp)
next
  case BinOpThrow1 thus ?case by simp (blast intro:eval_evals.BinOpThrow1)
next
  case BinOpThrow2 thus ?case by simp (blast intro:eval_evals.BinOpThrow2)
next
  case Var thus ?case by(simp add:eval_evals.intros)
next
  case (LAss e h\<^sub>0 l\<^sub>0 sh\<^sub>0 v h l sh l' V)
  have IH: "\<And>W. fv e \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0|`W,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>Val v,(h,l|`W,sh)\<rangle>"
   and [simp]: "l' = l(V \<mapsto> v)" by fact+
  have "fv (V:=e) \<subseteq> W" by fact
  hence fv: "fv e \<subseteq> W" and VinW: "V \<in> W" by auto
  from eval_evals.LAss[OF IH[OF fv] refl, of V] VinW
  show ?case by simp
next
  case LAssThrow thus ?case by(fastforce intro: eval_evals.LAssThrow)
next
  case FAcc thus ?case by simp (blast intro: eval_evals.FAcc)
next
  case FAccNull thus ?case by(fastforce intro: eval_evals.FAccNull)
next
  case FAccThrow thus ?case by(fastforce intro: eval_evals.FAccThrow)
next
  case FAccNone thus ?case by(metis eval_evals.FAccNone fv.simps(7))
next
  case FAccStatic thus ?case by(metis eval_evals.FAccStatic fv.simps(7))
next
  case SFAcc thus ?case by simp (blast intro: eval_evals.SFAcc)
next
  case SFAccInit thus ?case by simp (blast intro: eval_evals.SFAccInit)
next
  case SFAccInitThrow thus ?case by simp (blast intro: eval_evals.SFAccInitThrow)
next
  case SFAccNone thus ?case by simp (blast intro: eval_evals.SFAccNone)
next
  case SFAccNonStatic thus ?case by simp (blast intro: eval_evals.SFAccNonStatic)
next
  case FAss thus ?case by simp (blast intro: eval_evals.FAss)
next
  case FAssNull thus ?case by simp (blast intro: eval_evals.FAssNull)
next
  case FAssThrow1 thus ?case by simp (blast intro: eval_evals.FAssThrow1)
next
  case FAssThrow2 thus ?case by simp (blast intro: eval_evals.FAssThrow2)
next
  case FAssNone thus ?case by simp (blast intro: eval_evals.FAssNone)
next
  case FAssStatic thus ?case by simp (blast intro: eval_evals.FAssStatic)
next
  case SFAss thus ?case by simp (blast intro: eval_evals.SFAss)
next
  case SFAssInit thus ?case by simp (blast intro: eval_evals.SFAssInit)
next
  case SFAssInitThrow thus ?case by simp (blast intro: eval_evals.SFAssInitThrow)
next
  case SFAssThrow thus ?case by simp (blast intro: eval_evals.SFAssThrow)
next
  case SFAssNone thus ?case by simp (blast intro: eval_evals.SFAssNone)
next
  case SFAssNonStatic thus ?case by simp (blast intro: eval_evals.SFAssNonStatic)
next
  case CallObjThrow thus ?case by simp (blast intro: eval_evals.intros)
next
  case CallNull thus ?case by simp (blast intro: eval_evals.CallNull)
next
  case (CallNone e h l sh a h' l' sh' ps vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M)
  have f1: "P \<turnstile> \<langle>e,(h, l |` W, sh)\<rangle> \<Rightarrow> \<langle>addr a,(h', l' |` W, sh')\<rangle>"
    by (metis (no_types) fv.simps(11) le_sup_iff local.CallNone(2) local.CallNone(7))
  have "P \<turnstile> \<langle>ps,(h', l' |` W, sh')\<rangle> [\<Rightarrow>] \<langle>map Val vs, (h\<^sub>2, l\<^sub>2 |` W, sh\<^sub>2)\<rangle>"
    using local.CallNone(4) local.CallNone(7) by auto
  then show ?case
    using f1 eval_evals.CallNone local.CallNone(5) local.CallNone(6) by auto
next
  case CallStatic thus ?case
    by (metis (no_types, lifting) eval_evals.CallStatic fv.simps(11) le_sup_iff)
next
  case CallParamsThrow thus ?case
    by simp (blast intro: eval_evals.CallParamsThrow)
next
  case (Call e h\<^sub>0 l\<^sub>0 sh\<^sub>0 a h\<^sub>1 l\<^sub>1 sh\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M Ts T pns body
      D l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  have IHe: "\<And>W. fv e \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0|`W,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>addr a,(h\<^sub>1,l\<^sub>1|`W,sh\<^sub>1)\<rangle>"
   and IHps: "\<And>W. fvs ps \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>ps,(h\<^sub>1,l\<^sub>1|`W,sh\<^sub>1)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2|`W,sh\<^sub>2)\<rangle>"
   and IHbd: "\<And>W. fv body \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2'|`W,sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3|`W,sh\<^sub>3)\<rangle>"
   and h\<^sub>2a: "h\<^sub>2 a = Some (C, fs)"
   and "method": "P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (pns, body) in D"
   and same_len: "size vs = size pns"
   and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Addr a, pns [\<mapsto>] vs]" by fact+
  have "fv (e\<bullet>M(ps)) \<subseteq> W" by fact
  hence fve: "fv e  \<subseteq> W" and fvps: "fvs(ps) \<subseteq> W" by auto
  have wfmethod: "size Ts = size pns \<and> this \<notin> set pns" and
       fvbd: "fv body \<subseteq> {this} \<union> set pns"
    using "method" wf by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  show ?case
    using IHbd[OF fvbd] l\<^sub>2' same_len wfmethod h\<^sub>2a
      eval_evals.Call[OF IHe[OF fve] IHps[OF fvps] _ "method" same_len l\<^sub>2']
    by (simp add:subset_insertI)
next
  case (SCallNone ps h l sh vs h' l' sh' C M)
  have "P \<turnstile> \<langle>ps,(h, l |` W, sh)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h', l' |` W, sh')\<rangle>"
    using SCallNone.hyps(2) SCallNone.prems by auto
  then show ?case using SCallNone.hyps(3) eval_evals.SCallNone by auto
next
  case SCallNonStatic thus ?case by (metis eval_evals.SCallNonStatic fv.simps(12))
next
  case SCallParamsThrow thus ?case
    by simp (blast intro: eval_evals.SCallParamsThrow)
next
  case SCallInitThrow thus ?case by simp (blast intro: eval_evals.SCallInitThrow)
next
  case SCallInit thus ?case by simp (blast intro: eval_evals.SCallInit)
next
  case (SCall ps h\<^sub>0 l\<^sub>0 sh\<^sub>0 vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C M Ts T pns body D sfs l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  have IHps: "\<And>W. fvs ps \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>ps,(h\<^sub>0,l\<^sub>0|`W,sh\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2|`W,sh\<^sub>2)\<rangle>"
   and IHbd: "\<And>W. fv body \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2'|`W,sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3|`W,sh\<^sub>3)\<rangle>"
   and sh\<^sub>2D: "sh\<^sub>2 D = Some (sfs, Done) \<or> M = clinit \<and> sh\<^sub>2 D = \<lfloor>(sfs, Processing)\<rfloor>"
   and "method": "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns, body) in D"
   and same_len: "size vs = size pns"
   and l\<^sub>2': "l\<^sub>2' = [pns [\<mapsto>] vs]" by fact+
  have "fv (C\<bullet>\<^sub>sM(ps)) \<subseteq> W" by fact
  hence fvps: "fvs(ps) \<subseteq> W" by auto
  have wfmethod: "size Ts = size pns" and fvbd: "fv body \<subseteq> set pns"
    using "method" wf by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  show ?case
    using IHbd[OF fvbd] l\<^sub>2' same_len wfmethod sh\<^sub>2D
      eval_evals.SCall[OF IHps[OF fvps] "method" _ same_len l\<^sub>2']
    by (simp add:subset_insertI)
next
  case SeqThrow thus ?case by simp (blast intro: eval_evals.SeqThrow)
next
  case CondT thus ?case by simp (blast intro: eval_evals.CondT)
next
  case CondF thus ?case by simp (blast intro: eval_evals.CondF)
next
  case CondThrow thus ?case by simp (blast intro: eval_evals.CondThrow)
next
  case WhileF thus ?case by simp (blast intro: eval_evals.WhileF)
next
  case WhileT thus ?case by simp (blast intro: eval_evals.WhileT)
next
  case WhileCondThrow thus ?case by simp (blast intro: eval_evals.WhileCondThrow)
next
  case WhileBodyThrow thus ?case by simp (blast intro: eval_evals.WhileBodyThrow)
next
  case Throw thus ?case by simp (blast intro: eval_evals.Throw)
next
  case ThrowNull thus ?case by simp (blast intro: eval_evals.ThrowNull)
next
  case ThrowThrow thus ?case by simp (blast intro: eval_evals.ThrowThrow)
next
  case Try thus ?case by simp (blast intro: eval_evals.Try)
next
  case (TryCatch e\<^sub>1 h\<^sub>0 l\<^sub>0 sh\<^sub>0 a h\<^sub>1 l\<^sub>1 sh\<^sub>1 D fs C e\<^sub>2 V e\<^sub>2' h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  have IH\<^sub>1: "\<And>W. fv e\<^sub>1 \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1,(h\<^sub>0,l\<^sub>0|`W,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1|`W,sh\<^sub>1)\<rangle>"
   and IH\<^sub>2: "\<And>W. fv e\<^sub>2 \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>2,(h\<^sub>1,l\<^sub>1(V\<mapsto>Addr a)|`W,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2|`W,sh\<^sub>2)\<rangle>"
   and lookup: "h\<^sub>1 a = Some(D, fs)" and subtype: "P \<turnstile> D \<preceq>\<^sup>* C" by fact+
  have "fv (try e\<^sub>1 catch(C V) e\<^sub>2) \<subseteq> W" by fact
  hence fv\<^sub>1: "fv e\<^sub>1 \<subseteq> W" and fv\<^sub>2: "fv e\<^sub>2 \<subseteq> insert V W" by auto
  have IH\<^sub>2': "P \<turnstile> \<langle>e\<^sub>2,(h\<^sub>1,(l\<^sub>1|`W)(V \<mapsto> Addr a),sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2|`insert V W,sh\<^sub>2)\<rangle>"
    using IH\<^sub>2[OF fv\<^sub>2] fun_upd_restrict[of l\<^sub>1 W] (*FIXME just l|W instead of l|(W-V) in simp rule??*) by simp
  with eval_evals.TryCatch[OF IH\<^sub>1[OF fv\<^sub>1] _ subtype IH\<^sub>2'] lookup
  show ?case by fastforce
next
  case TryThrow thus ?case by simp (blast intro: eval_evals.TryThrow)
next
  case Nil thus ?case by (simp add: eval_evals.Nil)
next
  case Cons thus ?case by simp (blast intro: eval_evals.Cons)
next
  case ConsThrow thus ?case by simp (blast intro: eval_evals.ConsThrow)
next
  case InitFinal thus ?case by (simp add: eval_evals.InitFinal)
next
  case InitNone thus ?case by(blast intro: eval_evals.InitNone)
next
  case InitDone thus ?case
    by (simp add: InitDone.hyps(2) InitDone.prems eval_evals.InitDone)
next
  case InitProcessing thus ?case by (simp add: eval_evals.InitProcessing)
next
  case InitError thus ?case using eval_evals.InitError by auto
next
  case InitObject thus ?case by(simp add: eval_evals.InitObject)
next
  case InitNonObject thus ?case by(simp add: eval_evals.InitNonObject)
next
  case InitRInit thus ?case by(simp add: eval_evals.InitRInit)
next
  case (RInit e h l sh v h' l' sh' C sfs i sh'' C' Cs e' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  have f1: "fv e \<subseteq> W \<and> fv (INIT C' (Cs,True) \<leftarrow> e') \<subseteq> W"
    using RInit.prems by auto
  then have f2: "P \<turnstile> \<langle>e,(h, l |` W, sh)\<rangle> \<Rightarrow> \<langle>Val v,(h', l' |` W, sh')\<rangle>"
    using RInit.hyps(2) by blast
  have "P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e', (h', l' |` W, sh'')\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1, l\<^sub>1 |` W, sh\<^sub>1)\<rangle>"
    using f1 by (meson RInit.hyps(7))
  then show ?case
    using f2 RInit.hyps(3) RInit.hyps(4) RInit.hyps(5) eval_evals.RInit by blast
next
  case (RInitInitFail e h l sh a h' l' sh' C sfs i sh'' D Cs e' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  have f1: "fv e \<subseteq> W" "fv e' \<subseteq> W"
    using RInitInitFail.prems by auto
  then have f2: "P \<turnstile> \<langle>e,(h, l |` W, sh)\<rangle> \<Rightarrow> \<langle>throw a,(h', l' |` W, sh')\<rangle>"
    using RInitInitFail.hyps(2) by blast
  then have f2': "fv (throw a) \<subseteq> W"
    using eval_final[OF f2] by auto
  then have f1': "fv (RI (D,throw a);Cs \<leftarrow> e') \<subseteq> W"
    using f1 by auto
  have "P \<turnstile> \<langle>RI (D,throw a);Cs \<leftarrow> e', (h', l' |` W, sh'')\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1, l\<^sub>1 |` W, sh\<^sub>1)\<rangle>"
    using f1' by (meson RInitInitFail.hyps(6))
  then show ?case
    using f2 by (simp add: RInitInitFail.hyps(3,4) eval_evals.RInitInitFail)
next
  case (RInitFailFinal e h l sh a h' l' sh' sh'' C)
  have f1: "fv e \<subseteq> W"
    using RInitFailFinal.prems by auto
  then have f2: "P \<turnstile> \<langle>e,(h, l |` W, sh)\<rangle> \<Rightarrow> \<langle>throw a,(h', l' |` W, sh')\<rangle>"
    using RInitFailFinal.hyps(2) by blast
  then have f2': "fv (throw a) \<subseteq> W"
    using eval_final[OF f2] by auto
  then show ?case using f2 RInitFailFinal.hyps(3,4) eval_evals.RInitFailFinal by blast
qed
(*>*)


lemma eval_notfree_unchanged:
  "P \<turnstile> \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<Longrightarrow> (\<And>V. V \<notin> fv e \<Longrightarrow> l' V = l V)"
and "P \<turnstile> \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle> \<Longrightarrow> (\<And>V. V \<notin> fvs es \<Longrightarrow> l' V = l V)"
(*<*)
proof(induct rule:eval_evals_inducts)
  case LAss thus ?case by(simp add:fun_upd_apply)
next
  case Block thus ?case
    by (simp only:fun_upd_apply split:if_splits) fastforce
next
  case TryCatch thus ?case
    by (simp only:fun_upd_apply split:if_splits) fastforce
next
  case (RInitInitFail e h l sh a h' l' sh' C sfs i sh'' D Cs e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  have "fv (throw a) = {}"
    using RInitInitFail.hyps(1) eval_final final_fv by blast 
  then have "fv e \<union> fv (RI (D,throw a) ; Cs \<leftarrow> unit) \<subseteq> fv (RI (C,e) ; D#Cs \<leftarrow> unit)" 
    by auto
  then show ?case using RInitInitFail.hyps(2,6) RInitInitFail.prems by fastforce
qed simp_all
(*>*)


lemma eval_closed_lcl_unchanged:
  "\<lbrakk> P \<turnstile> \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>; fv e = {} \<rbrakk> \<Longrightarrow> l' = l"
(*<*)by(fastforce dest:eval_notfree_unchanged simp add:fun_eq_iff [where 'b="val option"])(*>*)


lemma list_eval_Throw: 
assumes eval_e: "P \<turnstile> \<langle>throw x,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P \<turnstile> \<langle>map Val vs @ throw x # es',s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
(*<*)
proof -
  from eval_e 
  obtain a where e': "e' = Throw a"
    by (cases) (auto dest!: eval_final)
  {
    fix es
    have "\<And>vs. es = map Val vs @ throw x # es' 
           \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle>[\<Rightarrow>]\<langle>map Val vs @ e' # es',s'\<rangle>"
    proof (induct es type: list)
      case Nil thus ?case by simp
    next
      case (Cons e es vs)
      have e_es: "e # es = map Val vs @ throw x # es'" by fact
      show "P \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
      proof (cases vs)
        case Nil
        with e_es obtain "e=throw x" "es=es'" by simp
        moreover from eval_e e'
        have "P \<turnstile> \<langle>throw x # es,s\<rangle> [\<Rightarrow>] \<langle>Throw a # es,s'\<rangle>"
          by (iprover intro: ConsThrow)
        ultimately show ?thesis using Nil e' by simp
      next
        case (Cons v vs')
        have vs: "vs = v # vs'" by fact
        with e_es obtain 
          e: "e=Val v" and es:"es= map Val vs' @ throw x # es'"
          by simp
        from e 
        have "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"
          by (iprover intro: eval_evals.Val)
        moreover from es 
        have "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs' @ e' # es',s'\<rangle>"
          by (rule Cons.hyps)
        ultimately show 
          "P \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
          using vs by (auto intro: eval_evals.Cons)
      qed
    qed
  }
  thus ?thesis
    by simp
qed
(*>*)

\<comment> \<open> separate evaluation of first subexp of a sequence \<close>
lemma seq_ext:
assumes IH: "\<And>e' s'. P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 and seq: "P \<turnstile> \<langle>e'' ;; e\<^sub>0,s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P \<turnstile> \<langle>e ;; e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
proof(rule eval_cases(14)[OF seq]) \<comment> \<open> Seq \<close>
  fix v' s\<^sub>1 assume e'': "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>" and estep: "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  have "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>" using e'' IH by simp
  then show ?thesis using estep Seq by simp
next
  fix e\<^sub>t assume e'': "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>throw e\<^sub>t,s'\<rangle>" and e': "e' = throw e\<^sub>t"
  have "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw e\<^sub>t,s'\<rangle>" using e'' IH by simp
  then show ?thesis using eval_evals.SeqThrow e' by simp
qed

\<comment> \<open> separate evaluation of @{text RI} subexp, val case \<close>
lemma rinit_Val_ext:
assumes ri: "P \<turnstile> \<langle>RI (C,e'') ; Cs \<leftarrow> e\<^sub>0,s''\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>"
 and IH: "\<And>e' s'. P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P \<turnstile> \<langle>RI (C,e) ; Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>"
proof(rule eval_cases(20)[OF ri]) \<comment> \<open> RI \<close>
  fix v'' h' l' sh' sfs i
  assume e''step: "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>Val v'',(h', l', sh')\<rangle>"
     and shC: "sh' C = \<lfloor>(sfs, i)\<rfloor>"
     and init: "P \<turnstile> \<langle>INIT (if Cs = [] then C else last Cs) (Cs,True) \<leftarrow> e\<^sub>0,(h', l', sh'(C \<mapsto> (sfs, Done)))\<rangle> \<Rightarrow>
        \<langle>Val v',s\<^sub>1\<rangle>"
  have "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v'',(h', l', sh')\<rangle>" using IH[OF e''step] by simp
  then show ?thesis using RInit init shC by auto
next
  fix a h' l' sh' sfs i D Cs'
  assume e''step: "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>throw a,(h', l', sh')\<rangle>"
     and riD: "P \<turnstile> \<langle>RI (D,throw a) ; Cs' \<leftarrow> e\<^sub>0,(h', l', sh'(C \<mapsto> (sfs, Error)))\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>"
  have "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw a,(h', l', sh')\<rangle>" using IH[OF e''step] by simp
  then show ?thesis using riD rinit_throwE by blast
qed(simp)

\<comment> \<open> separate evaluation of @{text RI} subexp, throw case \<close>
lemma rinit_throw_ext:
assumes ri: "P \<turnstile> \<langle>RI (C,e'') ; Cs \<leftarrow> e\<^sub>0,s''\<rangle> \<Rightarrow> \<langle>throw e\<^sub>t,s'\<rangle>"
 and IH: "\<And>e' s'. P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P \<turnstile> \<langle>RI (C,e) ; Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>throw e\<^sub>t,s'\<rangle>"
proof(rule eval_cases(20)[OF ri]) \<comment> \<open> RI \<close>
  fix v h' l' sh' sfs i
  assume e''step: "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>Val v,(h', l', sh')\<rangle>"
     and shC: "sh' C = \<lfloor>(sfs, i)\<rfloor>"
     and init: "P \<turnstile> \<langle>INIT (if Cs = [] then C else last Cs) (Cs,True) \<leftarrow> e\<^sub>0,(h', l', sh'(C \<mapsto> (sfs, Done)))\<rangle> \<Rightarrow>
        \<langle>throw e\<^sub>t,s'\<rangle>"
  have "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v,(h', l', sh')\<rangle>" using IH[OF e''step] by simp
  then show ?thesis using RInit init shC by auto
next
  fix a h' l' sh' sfs i D Cs'
  assume e''step: "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>throw a,(h', l', sh')\<rangle>"
     and shC: "sh' C = \<lfloor>(sfs, i)\<rfloor>"
     and riD: "P \<turnstile> \<langle>RI (D,throw a) ; Cs' \<leftarrow> e\<^sub>0,(h', l', sh'(C \<mapsto> (sfs, Error)))\<rangle> \<Rightarrow> \<langle>throw e\<^sub>t,s'\<rangle>"
     and cons: "Cs = D # Cs'"
  have estep': "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw a,(h', l', sh')\<rangle>" using IH[OF e''step] by simp
  then show ?thesis using RInitInitFail cons riD shC by simp
next
  fix a h' l' sh' sfs i
  assume "throw e\<^sub>t = throw a"
     and "s' = (h', l', sh'(C \<mapsto> (sfs, Error)))"
     and "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>throw a,(h', l', sh')\<rangle>"
     and "sh' C = \<lfloor>(sfs, i)\<rfloor>"
     and "Cs = []"
  then show ?thesis using RInitFailFinal IH by auto
qed

\<comment> \<open> separate evaluation of @{text RI} subexp \<close>
lemma rinit_ext:
assumes IH: "\<And>e' s'. P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "\<And>e' s'. P \<turnstile> \<langle>RI (C,e'') ; Cs \<leftarrow> e\<^sub>0,s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
 \<Longrightarrow> P \<turnstile> \<langle>RI (C,e) ; Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
proof -
  fix e' s' assume ri'': "P \<turnstile> \<langle>RI (C,e'') ; Cs \<leftarrow> e\<^sub>0,s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  then have "final e'" using eval_final by simp
  then show "P \<turnstile> \<langle>RI (C,e) ; Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  proof(rule finalE)
    fix v assume "e' = Val v" then show ?thesis using rinit_Val_ext[OF _ IH] ri'' by simp
  next
    fix a assume "e' = throw a" then show ?thesis using rinit_throw_ext[OF _ IH] ri'' by simp
  qed
qed

\<comment> \<open> @{text INIT} and @{text RI} return either @{text Val} with @{text Done} or
 @{text Processing} flag or @{text Throw} with @{text Error} flag \<close>
lemma
shows eval_init_return: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
  \<Longrightarrow> iconf (shp s) e
  \<Longrightarrow> (\<exists>Cs b. e = INIT C' (Cs,b) \<leftarrow> unit) \<or> (\<exists>C e\<^sub>0 Cs e\<^sub>i. e = RI(C,e\<^sub>0);Cs@[C'] \<leftarrow> unit)
     \<or> (\<exists>e\<^sub>0. e = RI(C',e\<^sub>0);Nil \<leftarrow> unit)
  \<Longrightarrow> (val_of e' = Some v \<longrightarrow> (\<exists>sfs i. shp s' C' = \<lfloor>(sfs,i)\<rfloor> \<and> (i = Done \<or> i = Processing)))
   \<and> (throw_of e' = Some a \<longrightarrow> (\<exists>sfs i. shp s' C' = \<lfloor>(sfs,Error)\<rfloor>))"
and "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> True"
proof(induct rule: eval_evals.inducts)
  case (InitFinal e s e' s' C b) then show ?case
    by(fastforce simp: initPD_def dest: eval_final_same)
next
  case (InitDone sh C sfs C' Cs e h l e' s')
  then have "final e'" using eval_final by simp
  then show ?case
  proof(rule finalE)
    fix v assume e': "e' = Val v" then show ?thesis using InitDone initPD_def
    proof(cases Cs) qed(auto)
  next
    fix a assume e': "e' = throw a" then show ?thesis using InitDone initPD_def
    proof(cases Cs) qed(auto)
  qed
next
  case (InitProcessing sh C sfs C' Cs e h l e' s')
  then have "final e'" using eval_final by simp
  then show ?case
  proof(rule finalE)
    fix v assume e': "e' = Val v" then show ?thesis using InitProcessing initPD_def
    proof(cases Cs) qed(auto)
  next
    fix a assume e': "e' = throw a" then show ?thesis using InitProcessing initPD_def
    proof(cases Cs) qed(auto)
  qed
next
  case (InitError sh C sfs Cs e h l e' s' C') show ?case
  proof(cases Cs)
    case Nil then show ?thesis using InitError by simp
  next
    case (Cons C2 list)
    then have "final e'" using InitError eval_final by simp
    then show ?thesis
    proof(rule finalE)
      fix v assume e': "e' = Val v" then show ?thesis
      using InitError
      proof -
        obtain ccss :: "char list list" and bb :: bool where
          "INIT C' (C # Cs,False) \<leftarrow> e = INIT C' (ccss,bb) \<leftarrow> unit"
          using InitError.prems(2) by blast
        then show ?thesis using InitError.hyps(2) e' by(auto dest!: rinit_throwE)
      qed
    next
      fix a assume e': "e' = throw a"
      then show ?thesis using Cons InitError cons_to_append[of list] by clarsimp
    qed
  qed
next
  case (InitRInit C Cs h l sh e' s' C') show ?case
  proof(cases Cs)
    case Nil then show ?thesis using InitRInit by simp
  next
    case (Cons C' list) then show ?thesis
      using InitRInit Cons cons_to_append[of list] by clarsimp
  qed
next
  case (RInit e s v h' l' sh' C sfs i sh'' C' Cs e' e\<^sub>1 s\<^sub>1)
  then have final: "final e\<^sub>1" using eval_final by simp
  then show ?case
  proof(cases Cs)
    case Nil show ?thesis using final
    proof(rule finalE)
      fix v assume e': "e\<^sub>1 = Val v" show ?thesis
      using RInit Nil by(auto simp: fun_upd_same initPD_def)
    next
      fix a assume e': "e\<^sub>1 = throw a" show ?thesis
      using RInit Nil by(auto simp: fun_upd_same initPD_def)
    qed
  next
    case (Cons a list) show ?thesis
    proof(rule finalE[OF final])
      fix v assume e': "e\<^sub>1 = Val v" then show ?thesis
      using RInit Cons by clarsimp (metis last.simps last_appendR list.distinct(1))
    next
      fix a assume e': "e\<^sub>1 = throw a" then show ?thesis
      using RInit Cons by clarsimp (metis last.simps last_appendR list.distinct(1))
    qed
  qed
next
  case (RInitInitFail e s a h' l' sh' C sfs i sh'' D Cs e' e\<^sub>1 s\<^sub>1)
  then have final: "final e\<^sub>1" using eval_final by simp
  then show ?case
  proof(rule finalE)
    fix v assume e': "e\<^sub>1 = Val v" then show ?thesis
    using RInitInitFail by clarsimp (meson exp.distinct(101) rinit_throwE)
  next
    fix a' assume e': "e\<^sub>1 = Throw a'"
    then have "iconf (sh'(C \<mapsto> (sfs, Error))) a"
      using RInitInitFail.hyps(1) eval_final by fastforce
    then show ?thesis using RInitInitFail e'
      by clarsimp (meson Cons_eq_append_conv list.inject)
  qed
qed(auto simp: fun_upd_same)

lemma init_Val_PD: "P \<turnstile> \<langle>INIT C' (Cs,b) \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>Val v,s'\<rangle>
  \<Longrightarrow> iconf (shp s) (INIT C' (Cs,b) \<leftarrow> unit)
  \<Longrightarrow> \<exists>sfs i. shp s' C' = \<lfloor>(sfs,i)\<rfloor> \<and> (i = Done \<or> i = Processing)"
 by(drule_tac v = v in eval_init_return, simp+)

lemma init_throw_PD: "P \<turnstile> \<langle>INIT C' (Cs,b) \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>
  \<Longrightarrow> iconf (shp s) (INIT C' (Cs,b) \<leftarrow> unit)
  \<Longrightarrow> \<exists>sfs i. shp s' C' = \<lfloor>(sfs,Error)\<rfloor>"
 by(drule_tac a = a in eval_init_return, simp+)

lemma rinit_Val_PD: "P \<turnstile> \<langle>RI(C,e\<^sub>0);Cs \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>Val v,s'\<rangle>
  \<Longrightarrow> iconf (shp s) (RI(C,e\<^sub>0);Cs \<leftarrow> unit) \<Longrightarrow> last(C#Cs) = C'
  \<Longrightarrow> \<exists>sfs i. shp s' C' = \<lfloor>(sfs,i)\<rfloor> \<and> (i = Done \<or> i = Processing)"
apply(drule_tac C' = C' and v = v in eval_init_return, simp_all)
apply (metis append_butlast_last_id)
done

lemma rinit_throw_PD: "P \<turnstile> \<langle>RI(C,e\<^sub>0);Cs \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>
  \<Longrightarrow> iconf (shp s) (RI(C,e\<^sub>0);Cs \<leftarrow> unit) \<Longrightarrow> last(C#Cs) = C'
  \<Longrightarrow> \<exists>sfs i. shp s' C' = \<lfloor>(sfs,Error)\<rfloor>"
apply(drule_tac C' = C' and a = a in eval_init_return, simp_all)
apply (metis append_butlast_last_id)
done

\<comment> \<open> combining the above to get evaluation of @{text INIT} in a sequence \<close>

(* Hiermit kann man die ganze pair-Splitterei in den automatischen Taktiken
abschalten. Wieder anschalten siehe nach dem Beweis. *)
(*<*)
declare split_paired_All [simp del] split_paired_Ex [simp del]
(*>*)

lemma eval_init_seq': "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
  \<Longrightarrow> (\<exists>C Cs b e\<^sub>i. e = INIT C (Cs,b) \<leftarrow> e\<^sub>i) \<or> (\<exists>C e\<^sub>0 Cs e\<^sub>i. e = RI(C,e\<^sub>0);Cs \<leftarrow> e\<^sub>i)
  \<Longrightarrow> (\<exists>C Cs b e\<^sub>i. e = INIT C (Cs,b) \<leftarrow> e\<^sub>i \<and> P \<turnstile> \<langle>(INIT C (Cs,b) \<leftarrow> unit);; e\<^sub>i,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>)
     \<or> (\<exists>C e\<^sub>0 Cs e\<^sub>i. e = RI(C,e\<^sub>0);Cs \<leftarrow> e\<^sub>i \<and> P \<turnstile> \<langle>(RI(C,e\<^sub>0);Cs \<leftarrow> unit);; e\<^sub>i,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>)"
and "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> True"
proof(induct rule: eval_evals.inducts)
  case InitFinal then show ?case by(auto simp: Seq[OF eval_evals.InitFinal[OF Val[where v=Unit]]])
next
  case (InitNone sh) then show ?case
   using seq_ext[OF eval_evals.InitNone[where sh=sh and e=unit, OF InitNone.hyps(1)]] by fastforce
next
  case (InitDone sh) then show ?case
   using seq_ext[OF eval_evals.InitDone[where sh=sh and e=unit, OF InitDone.hyps(1)]] by fastforce
next
  case (InitProcessing sh) then show ?case
   using seq_ext[OF eval_evals.InitProcessing[where sh=sh and e=unit, OF InitProcessing.hyps(1)]]
     by fastforce
next
  case (InitError sh) then show ?case
   using seq_ext[OF eval_evals.InitError[where sh=sh and e=unit, OF InitError.hyps(1)]] by fastforce
next
  case (InitObject sh) then show ?case
   using seq_ext[OF eval_evals.InitObject[where sh=sh and e=unit, OF InitObject.hyps(1)]]
     by fastforce
next
  case (InitNonObject sh) then show ?case
   using seq_ext[OF eval_evals.InitNonObject[where sh=sh and e=unit, OF InitNonObject.hyps(1)]]
     by fastforce
next
  case (InitRInit C Cs e h l sh e' s' C') then show ?case
   using seq_ext[OF eval_evals.InitRInit[where e=unit]] by fastforce
next
  case RInit then show ?case
   using seq_ext[OF eval_evals.RInit[where e=unit, OF RInit.hyps(1)]] by fastforce
next
  case RInitInitFail then show ?case
   using seq_ext[OF eval_evals.RInitInitFail[where e=unit, OF RInitInitFail.hyps(1)]] by fastforce
next
  case RInitFailFinal
  then show ?case using eval_evals.RInitFailFinal eval_evals.SeqThrow by auto
qed(auto)

lemma eval_init_seq: "P \<turnstile> \<langle>INIT C (Cs,b) \<leftarrow> e,(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
 \<Longrightarrow> P \<turnstile> \<langle>(INIT C (Cs,b) \<leftarrow> unit);; e,(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 by(auto dest: eval_init_seq')


text \<open> The key lemma: \<close>
lemma
assumes wf: "wwf_J_prog P"
shows extend_1_eval: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e'',s'',b''\<rangle> \<Longrightarrow> P,shp s \<turnstile>\<^sub>b (e,b) \<surd>
   \<Longrightarrow> (\<And>s' e'.  P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>)"
and extend_1_evals: "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es'',s'',b''\<rangle> \<Longrightarrow> P,shp s \<turnstile>\<^sub>b (es,b) \<surd>
   \<Longrightarrow> (\<And>s' es'. P \<turnstile> \<langle>es'',s''\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>)"
proof (induct rule: red_reds.inducts)
  case (RedNew h a C FDTs h' l sh)
  then have e':"e' = addr a" and s':"s' = (h(a \<mapsto> blank P C), l, sh)"
    using eval_cases(3) by fastforce+
  obtain sfs i where shC: "sh C = \<lfloor>(sfs, i)\<rfloor>" and "i = Done \<or> i = Processing"
   using RedNew by (clarsimp simp: bconf_def initPD_def)
  then show ?case
  proof(cases i)
    case Done then show ?thesis using RedNew shC e' s' New by simp
  next
    case Processing
    then have shC': "\<nexists>sfs. sh C = Some(sfs,Done)" and shP: "sh C = Some(sfs,Processing)"
      using shC by simp+
    then have init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>unit,(h,l,sh)\<rangle>"
      by(simp add: InitFinal InitProcessing Val)
    have "P \<turnstile> \<langle>new C,(h, l, sh)\<rangle> \<Rightarrow> \<langle>addr a,(h(a \<mapsto> blank P C),l,sh)\<rangle>"
      using RedNew shC' by(auto intro: NewInit[OF _ init])
    then show ?thesis using e' s' by simp
  qed(auto)
next
  case (RedNewFail h C l sh)
  then have e':"e' = THROW OutOfMemory" and s':"s' = (h, l, sh)"
    using eval_final_same final_def by fastforce+
  obtain sfs i where shC: "sh C = \<lfloor>(sfs, i)\<rfloor>" and "i = Done \<or> i = Processing"
   using RedNewFail by (clarsimp simp: bconf_def initPD_def)
  then show ?case
  proof(cases i)
    case Done then show ?thesis using RedNewFail shC e' s' NewFail by simp
  next
    case Processing
    then have shC': "\<nexists>sfs. sh C = Some(sfs,Done)" and shP: "sh C = Some(sfs,Processing)"
      using shC by simp+
    then have init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>unit,(h,l,sh)\<rangle>"
      by(simp add: InitFinal InitProcessing Val)
    have "P \<turnstile> \<langle>new C,(h, l, sh)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l,sh)\<rangle>"
      using RedNewFail shC' by(auto intro: NewInitOOM[OF _ init])
    then show ?thesis using e' s' by simp
  qed(auto)
next
  case (NewInitRed sh C h l)
  then have seq: "P \<turnstile> \<langle>(INIT C ([C],False) \<leftarrow> unit);; new C,(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using eval_init_seq by simp
  then show ?case
  proof(rule eval_cases(14)) \<comment> \<open> Seq \<close>
    fix v s\<^sub>1 assume init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>"
      and new: "P \<turnstile> \<langle>new C,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    obtain h\<^sub>1 l\<^sub>1 sh\<^sub>1 where s\<^sub>1: "s\<^sub>1 = (h\<^sub>1,l\<^sub>1,sh\<^sub>1)" by(cases s\<^sub>1)
    then obtain sfs i where shC: "sh\<^sub>1 C = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Done \<or> i = Processing"
      using init_Val_PD[OF init] by auto
    show ?thesis
    proof(rule eval_cases(1)[OF new]) \<comment> \<open> New \<close>
      fix sha ha a FDTs la
      assume s\<^sub>1a: "s\<^sub>1 = (ha, la, sha)" and e': "e' = addr a"
         and s': "s' = (ha(a \<mapsto> blank P C), la, sha)"
         and addr: "new_Addr ha = \<lfloor>a\<rfloor>" and fields: "P \<turnstile> C has_fields FDTs"
      then show ?thesis using NewInit[OF _ _ addr fields] NewInitRed.hyps init by simp
    next
      fix sha ha la
      assume "s\<^sub>1 = (ha, la, sha)" and "e' = THROW OutOfMemory"
         and "s' = (ha, la, sha)" and "new_Addr ha = None"
      then show ?thesis using NewInitOOM NewInitRed.hyps init by simp
    next
      fix sha ha la v' h' l' sh' a FDTs
      assume s\<^sub>1a: "s\<^sub>1 = (ha, la, sha)" and e': "e' = addr a"
         and s': "s' = (h'(a \<mapsto> blank P C), l', sh')"
         and shaC: "\<forall>sfs. sha C \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(ha, la, sha)\<rangle> \<Rightarrow> \<langle>Val v',(h', l', sh')\<rangle>"
         and addr: "new_Addr h' = \<lfloor>a\<rfloor>" and fields: "P \<turnstile> C has_fields FDTs"
      then have i: "i = Processing" using iDP shC s\<^sub>1 by simp
      then have "(h', l', sh') = (ha, la, sha)" using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shC by blast
      then show ?thesis using NewInit NewInitRed.hyps s\<^sub>1a addr fields init shaC e' s' by auto
    next
      fix sha ha la v' h' l' sh'
      assume s\<^sub>1a: "s\<^sub>1 = (ha, la, sha)" and e': "e' = THROW OutOfMemory"
         and s': "s' = (h', l', sh')" and "\<forall>sfs. sha C \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(ha, la, sha)\<rangle> \<Rightarrow> \<langle>Val v',(h', l', sh')\<rangle>"
         and addr: "new_Addr h' = None"
      then have i: "i = Processing" using iDP shC s\<^sub>1 by simp
      then have "(h', l', sh') = (ha, la, sha)" using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shC by blast
      then show ?thesis
        using NewInitOOM NewInitRed.hyps e' addr s' s\<^sub>1a init by auto
    next
      fix sha ha la a
      assume s\<^sub>1a: "s\<^sub>1 = (ha, la, sha)"
         and "\<forall>sfs. sha C \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(ha, la, sha)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
      then have i: "i = Processing" using iDP shC s\<^sub>1 by simp
      then show ?thesis using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shC by blast
    qed
  next
    fix e assume e': "e' = throw e"
      and init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>throw e,s'\<rangle>"
    obtain h' l' sh' where s': "s' = (h',l',sh')" by(cases s')
    then obtain sfs i where shC: "sh' C = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Error"
      using init_throw_PD[OF init] by auto
    then show ?thesis by (simp add: NewInitRed.hyps NewInitThrow e' init)
  qed
next
  case CastRed then show ?case
    by(fastforce elim!: eval_cases intro: eval_evals.intros intro!: CastFail)
next
  case RedCastNull
  then show ?case
    by simp (iprover elim: eval_cases intro: eval_evals.intros)
next
  case RedCast
  then show ?case
    by (auto elim: eval_cases intro: eval_evals.intros)
next
  case RedCastFail
  then show ?case
    by (auto elim!: eval_cases intro: eval_evals.intros)
next
  case BinOpRed1 then show ?case
    by(fastforce elim!: eval_cases intro: eval_evals.intros simp: val_no_step)
next
  case BinOpRed2
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case RedBinOp
  thus ?case
    by simp (iprover elim: eval_cases intro: eval_evals.intros)
next
  case RedVar
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case LAssRed thus ?case
    by(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedLAss
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAccRed thus ?case
    by(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedFAcc then show ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedFAccNull then show ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case RedFAccNone thus ?case
    by(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedFAccStatic thus ?case
    by(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (RedSFAcc C F t D sh sfs i v h l)
  then have e':"e' = Val v" and s':"s' = (h, l, sh)"
    using eval_cases(3) by fastforce+
  have "i = Done \<or> i = Processing" using RedSFAcc by (clarsimp simp: bconf_def initPD_def)
  then show ?case
  proof(cases i)
    case Done then show ?thesis using RedSFAcc e' s' SFAcc by simp
  next
    case Processing
    then have shC': "\<nexists>sfs. sh D = Some(sfs,Done)" and shP: "sh D = Some(sfs,Processing)"
      using RedSFAcc by simp+
    then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>unit,(h,l,sh)\<rangle>"
      by(simp add: InitFinal InitProcessing Val)
    have "P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h, l, sh)\<rangle> \<Rightarrow> \<langle>Val v,(h,l,sh)\<rangle>"
      by(rule SFAccInit[OF RedSFAcc.hyps(1) shC' init shP RedSFAcc.hyps(3)])
    then show ?thesis using e' s' by simp
  qed(auto)
next
  case (SFAccInitRed C F t D sh h l)
  then have seq: "P \<turnstile> \<langle>(INIT D ([D],False) \<leftarrow> unit);; C\<bullet>\<^sub>sF{D},(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using eval_init_seq by simp
  then show ?case
  proof(rule eval_cases(14)) \<comment> \<open> Seq \<close>
    fix v s\<^sub>1 assume init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>"
      and acc: "P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    obtain h\<^sub>1 l\<^sub>1 sh\<^sub>1 where s\<^sub>1: "s\<^sub>1 = (h\<^sub>1,l\<^sub>1,sh\<^sub>1)" by(cases s\<^sub>1)
    then obtain sfs i where shD: "sh\<^sub>1 D = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Done \<or> i = Processing"
      using init_Val_PD[OF init] by auto
    show ?thesis
    proof(rule eval_cases(8)[OF acc]) \<comment> \<open> SFAcc \<close>
      fix t sha sfs v ha la
      assume "s\<^sub>1 = (ha, la, sha)" and "e' = Val v"
         and "s' = (ha, la, sha)" and "P \<turnstile> C has F,Static:t in D"
         and "sha D = \<lfloor>(sfs, Done)\<rfloor>" and "sfs F = \<lfloor>v\<rfloor>"
      then show ?thesis using SFAccInit SFAccInitRed.hyps(2) init by auto
    next
      fix t sha ha la v' h' l' sh' sfs i' v
      assume s\<^sub>1a: "s\<^sub>1 = (ha, la, sha)" and e': "e' = Val v"
         and s': "s' = (h', l', sh')" and field: "P \<turnstile> C has F,Static:t in D"
         and "\<forall>sfs. sha D \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(ha, la, sha)\<rangle> \<Rightarrow> \<langle>Val v',(h', l', sh')\<rangle>"
         and shD': "sh' D = \<lfloor>(sfs, i')\<rfloor>" and sfsF: "sfs F = \<lfloor>v\<rfloor>"
      then have i: "i = Processing" using iDP shD s\<^sub>1 by simp
      then have "(h', l', sh') = (ha, la, sha)" using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shD by blast
      then show ?thesis using SFAccInit SFAccInitRed.hyps(2) e' s' field init s\<^sub>1a sfsF shD' by auto
    next
      fix t sha ha la a
      assume s\<^sub>1a: "s\<^sub>1 = (ha, la, sha)" and "e' = throw a"
         and "P \<turnstile> C has F,Static:t in D" and "\<forall>sfs. sha D \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(ha, la, sha)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
      then have i: "i = Processing" using iDP shD s\<^sub>1 by simp
      then show ?thesis using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shD by blast
    next
      assume "\<forall>b t. \<not> P \<turnstile> C has F,b:t in D"
      then show ?thesis using SFAccInitRed.hyps(1) by blast
    next
      fix t assume field: "P \<turnstile> C has F,NonStatic:t in D"
      then show ?thesis using has_field_fun[OF SFAccInitRed.hyps(1) field] by simp
    qed
  next
    fix e assume e': "e' = throw e"
     and init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>throw e,s'\<rangle>"
    obtain h' l' sh' where s': "s' = (h',l',sh')" by(cases s')
    then obtain sfs i where shC: "sh' D = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Error"
      using init_throw_PD[OF init] by auto
    then show ?thesis
      using SFAccInitRed.hyps(1) SFAccInitRed.hyps(2) SFAccInitThrow e' init by auto
  qed
next
  case RedSFAccNone thus ?case
    by(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedSFAccNonStatic thus ?case
    by(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (FAssRed1 e s b e1 s1 b1 F D e\<^sub>2)
  obtain h' l' sh' where "s'=(h',l',sh')" by(cases s')
  with FAssRed1 show ?case
    by(fastforce elim!: eval_cases(9)[where e\<^sub>1=e1] intro: eval_evals.intros simp: val_no_step
                 intro!: FAss FAssNull FAssNone FAssStatic FAssThrow2)
next
  case FAssRed2
  obtain h' l' sh' where "s'=(h',l',sh')" by(cases s')
  with FAssRed2 show ?case
    by(auto elim!: eval_cases intro: eval_evals.intros
            intro!: FAss FAssNull FAssNone FAssStatic FAssThrow2 Val)
next
  case RedFAss
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case RedFAssNull
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case RedFAssNone
  then show ?case
    by(auto elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case RedFAssStatic
  then show ?case
    by(auto elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case (SFAssRed e s b e'' s'' b'' C F D)
  obtain h l sh where [simp]: "s = (h,l,sh)" by(cases s)
  obtain h' l' sh' where [simp]: "s'=(h',l',sh')" by(cases s')
  have "val_of e = None" using val_no_step SFAssRed.hyps(1) by(meson option.exhaust)
  then have bconf: "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using SFAssRed by simp
  show ?case using SFAssRed.prems(2) SFAssRed bconf
  proof cases
    case 2 with SFAssRed bconf show ?thesis by(auto intro!: SFAssInit)
  next
    case 3 with SFAssRed bconf show ?thesis by(auto intro!: SFAssInitThrow)
  qed(auto intro: eval_evals.intros intro!: SFAss SFAssInit SFAssNone SFAssNonStatic)
next
  case (RedSFAss C F t D sh sfs i sfs' v sh' h l)
  let ?sfs' = "sfs(F \<mapsto> v)"
  have e':"e' = unit" and s':"s' = (h, l, sh(D \<mapsto> (?sfs', i)))"
    using RedSFAss eval_cases(3) by fastforce+
  have "i = Done \<or> i = Processing" using RedSFAss by(clarsimp simp: bconf_def initPD_def)
  then show ?case
  proof(cases i)
    case Done then show ?thesis using RedSFAss e' s' SFAss Val by auto
  next
    case Processing
    then have shC': "\<nexists>sfs. sh D = Some(sfs,Done)" and shP: "sh D = Some(sfs,Processing)"
      using RedSFAss by simp+
    then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>unit,(h,l,sh)\<rangle>"
      by(simp add: InitFinal InitProcessing Val)
    have "P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D} := Val v,(h, l, sh)\<rangle> \<Rightarrow> \<langle>unit,(h,l,sh(D \<mapsto> (?sfs', i)))\<rangle>"
      using Processing by(auto intro: SFAssInit[OF Val RedSFAss.hyps(1) shC' init shP])
    then show ?thesis using e' s' by simp
  qed(auto)
next
  case (SFAssInitRed C F t D sh v h l)
  then have seq: "P \<turnstile> \<langle>(INIT D ([D],False) \<leftarrow> unit);; C\<bullet>\<^sub>sF{D} := Val v,(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using eval_init_seq by simp
  then show ?case
  proof(rule eval_cases(14)) \<comment> \<open> Seq \<close>
    fix v' s\<^sub>1 assume init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>"
      and acc: "P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D} := Val v,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    obtain h\<^sub>1 l\<^sub>1 sh\<^sub>1 where s\<^sub>1: "s\<^sub>1 = (h\<^sub>1,l\<^sub>1,sh\<^sub>1)" by(cases s\<^sub>1)
    then obtain sfs i where shD: "sh\<^sub>1 D = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Done \<or> i = Processing"
      using init_Val_PD[OF init] by auto
    show ?thesis
    proof(rule eval_cases(10)[OF acc]) \<comment> \<open> SFAss \<close>
      fix va h\<^sub>1 l\<^sub>1 sh\<^sub>1 t sfs
      assume e': "e' = unit" and s': "s' = (h\<^sub>1, l\<^sub>1, sh\<^sub>1(D \<mapsto> (sfs(F \<mapsto> va), Done)))"
         and val: "P \<turnstile> \<langle>Val v,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val va,(h\<^sub>1, l\<^sub>1, sh\<^sub>1)\<rangle>"
         and field: "P \<turnstile> C has F,Static:t in D" and shD': "sh\<^sub>1 D = \<lfloor>(sfs, Done)\<rfloor>"
      have "v = va" and "s\<^sub>1 = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)" using eval_final_same[OF val] by auto
      then show ?thesis using SFAssInit field SFAssInitRed.hyps(2) shD' e' s' init val
        by (metis eval_final eval_finalId)
    next
      fix va h\<^sub>1 l\<^sub>1 sh\<^sub>1 t v' h' l' sh' sfs i'
      assume e': "e' = unit" and s': "s' = (h', l', sh'(D \<mapsto> (sfs(F \<mapsto> va), i')))"
         and val: "P \<turnstile> \<langle>Val v,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val va,(h\<^sub>1, l\<^sub>1, sh\<^sub>1)\<rangle>"
         and field: "P \<turnstile> C has F,Static:t in D" and nDone: "\<forall>sfs. sh\<^sub>1 D \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>Val v',(h', l', sh')\<rangle>"
         and shD': "sh' D = \<lfloor>(sfs, i')\<rfloor>"
      have v: "v = va" and s\<^sub>1a: "s\<^sub>1 = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)" using eval_final_same[OF val] by auto
      then have i: "i = Processing" using iDP shD s\<^sub>1 nDone by simp
      then have "(h\<^sub>1, l\<^sub>1, sh\<^sub>1) = (h', l', sh')" using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shD by blast
      then show ?thesis using SFAssInit SFAssInitRed.hyps(2) e' s' field init v s\<^sub>1a shD' val
        by (metis eval_final eval_finalId)
    next
      fix va h\<^sub>1 l\<^sub>1 sh\<^sub>1 t a
      assume "e' = throw a" and val: "P \<turnstile> \<langle>Val v,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val va,(h\<^sub>1, l\<^sub>1, sh\<^sub>1)\<rangle>"
         and "P \<turnstile> C has F,Static:t in D" and nDone: "\<forall>sfs. sh\<^sub>1 D \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1, l\<^sub>1, sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
      have v: "v = va" and s\<^sub>1a: "s\<^sub>1 = (h\<^sub>1, l\<^sub>1, sh\<^sub>1)" using eval_final_same[OF val] by auto
      then have i: "i = Processing" using iDP shD s\<^sub>1 nDone by simp
      then have "(h\<^sub>1, l\<^sub>1, sh\<^sub>1) = s'" using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shD by blast
      then show ?thesis using init' init_ProcessingE s\<^sub>1 s\<^sub>1a shD i by blast
    next
      fix e'' assume val:"P \<turnstile> \<langle>Val v,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e'',s'\<rangle>"
      then show ?thesis using eval_final_same[OF val] by simp
    next
      assume "\<forall>b t. \<not> P \<turnstile> C has F,b:t in D"
      then show ?thesis using SFAssInitRed.hyps(1) by blast
    next
      fix t assume field: "P \<turnstile> C has F,NonStatic:t in D"
      then show ?thesis using has_field_fun[OF SFAssInitRed.hyps(1) field] by simp
    qed
  next
    fix e assume e': "e' = throw e"
     and init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>throw e,s'\<rangle>"
    obtain h' l' sh' where s': "s' = (h',l',sh')" by(cases s')
    then obtain sfs i where shC: "sh' D = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Error"
      using init_throw_PD[OF init] by auto
    then show ?thesis using SFAssInitRed.hyps(1) SFAssInitRed.hyps(2) SFAssInitThrow Val
      by (metis e' init)
  qed
next
  case (RedSFAssNone C F D v s b) then show ?case
    by(cases s) (auto elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case (RedSFAssNonStatic C F t D v s b) then show ?case
    by(cases s) (auto elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case CallObj
  note val_no_step[simp]
  from CallObj.prems(2) CallObj show ?case
  proof cases
    case 2 with CallObj show ?thesis by(fastforce intro!: CallParamsThrow)
  next
    case 3 with CallObj show ?thesis by(fastforce intro!: CallNull)
  next
    case 4 with CallObj show ?thesis by(fastforce intro!: CallNone)
  next
    case 5 with CallObj show ?thesis by(fastforce intro!: CallStatic)
  qed(fastforce intro!: CallObjThrow Call)+
next
  case (CallParams es s b es'' s'' b'' v M s')
  then obtain h' l' sh' where "s' = (h',l',sh')" by(cases s')
  with CallParams show ?case
   by(auto elim!: eval_cases intro!: CallNone eval_finalId CallStatic Val)
     (auto intro!: CallParamsThrow CallNull Call Val)
next
  case (RedCall h a C fs M Ts T pns body D vs l sh b)
  have "P \<turnstile> \<langle>addr a,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>" by (rule eval_evals.intros)
  moreover
  have finals: "finals(map Val vs)" by simp
  with finals have "P \<turnstile> \<langle>map Val vs,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l,sh)\<rangle>"
    by (iprover intro: eval_finalsId)
  moreover have "h a = Some (C, fs)" using RedCall by simp
  moreover have "method": "P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (pns, body) in D" by fact
  moreover have same_len\<^sub>1: "length Ts = length pns"
   and this_distinct: "this \<notin> set pns" and fv: "fv (body) \<subseteq> {this} \<union> set pns"
    using "method" wf by (fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  have same_len: "length vs = length pns" by fact
  moreover
  obtain l\<^sub>2' where l\<^sub>2': "l\<^sub>2' = [this\<mapsto>Addr a,pns[\<mapsto>]vs]" by simp
  moreover
  obtain h\<^sub>3 l\<^sub>3 sh\<^sub>3 where s': "s' = (h\<^sub>3,l\<^sub>3,sh\<^sub>3)" by (cases s')
  have eval_blocks:
    "P \<turnstile> \<langle>(blocks (this # pns, Class D # Ts, Addr a # vs, body)),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  hence id: "l\<^sub>3 = l" using fv s' same_len\<^sub>1 same_len
    by(fastforce elim: eval_closed_lcl_unchanged)
  from eval_blocks obtain l\<^sub>3' where "P \<turnstile> \<langle>body,(h,l\<^sub>2',sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3',sh\<^sub>3)\<rangle>"
  proof -
    from same_len\<^sub>1 have "length(this#pns) = length(Class D#Ts)" by simp
    moreover from same_len\<^sub>1 same_len
    have same_len\<^sub>2: "length (this#pns) = length (Addr a#vs)" by simp
    moreover from eval_blocks
    have "P \<turnstile> \<langle>blocks (this#pns,Class D#Ts,Addr a#vs,body),(h,l,sh)\<rangle>
              \<Rightarrow>\<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle>" using s' same_len\<^sub>1 same_len\<^sub>2 by simp
    ultimately obtain l''
      where "P \<turnstile> \<langle>body,(h,l(this # pns[\<mapsto>]Addr a # vs),sh)\<rangle>\<Rightarrow>\<langle>e',(h\<^sub>3, l'',sh\<^sub>3)\<rangle>"
      by (blast dest:blocksEval)
    from eval_restrict_lcl[OF wf this fv] this_distinct same_len\<^sub>1 same_len
    have "P \<turnstile> \<langle>body,(h,[this # pns[\<mapsto>]Addr a # vs],sh)\<rangle> \<Rightarrow>
               \<langle>e',(h\<^sub>3, l''|`(set(this#pns)),sh\<^sub>3)\<rangle>" using wf method
      by(simp add:subset_insert_iff insert_Diff_if)
    thus ?thesis by(fastforce intro!:that simp add: l\<^sub>2')
  qed
  ultimately
  have "P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l,sh\<^sub>3)\<rangle>" by (rule Call)
  with s' id show ?case by simp
next
  case RedCallNull
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros eval_finalsId)
next
  case (RedCallNone h a C fs M vs l sh b)
  then have tes: "THROW NoSuchMethodError = e' \<and> (h,l,sh) = s'"
    using eval_final_same by simp
  have "P \<turnstile> \<langle>addr a,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>" and "P \<turnstile> \<langle>map Val vs,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l,sh)\<rangle>"
    using eval_finalId eval_finalsId by auto
  then show ?case using RedCallNone CallNone tes by auto
next
  case (RedCallStatic h a C fs M Ts T m D vs l sh b)
  then have tes: "THROW IncompatibleClassChangeError = e' \<and> (h,l,sh) = s'"
    using eval_final_same by simp
  have "P \<turnstile> \<langle>addr a,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>" and "P \<turnstile> \<langle>map Val vs,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l,sh)\<rangle>"
    using eval_finalId eval_finalsId by auto
  then show ?case using RedCallStatic CallStatic tes by fastforce
next
  case (SCallParams es s b es'' s'' b' C M s')
  obtain h' l' sh' where s'[simp]: "s' = (h',l',sh')" by(cases s')
  obtain h l sh where s[simp]: "s = (h,l,sh)" by(cases s)
  have es: "map_vals_of es = None" using vals_no_step SCallParams.hyps(1) by (meson not_Some_eq)
  have bconf: "P,sh \<turnstile>\<^sub>b (es,b) \<surd>" using s SCallParams.prems(1) by (simp add: bconf_SCall[OF es])
  from SCallParams.prems(2) SCallParams bconf show ?case
  proof cases
    case 2 with SCallParams bconf show ?thesis by(auto intro!: SCallNone)
  next
    case 3 with SCallParams bconf show ?thesis by(auto intro!: SCallNonStatic)
  next
    case 4 with SCallParams bconf show ?thesis by(auto intro!: SCallInitThrow)
  next
    case 5 with SCallParams bconf show ?thesis by(auto intro!: SCallInit)
  qed(auto intro!: SCallParamsThrow SCall)
next
  case (RedSCall C M Ts T pns body D vs s)
  then obtain h l sh where s:"s = (h,l,sh)" by(cases s)
  then obtain sfs i where shC: "sh D = \<lfloor>(sfs, i)\<rfloor>" and "i = Done \<or> i = Processing"
   using RedSCall by(auto simp: bconf_def initPD_def dest: sees_method_fun)
  have finals: "finals(map Val vs)" by simp
  with finals have mVs: "P \<turnstile> \<langle>map Val vs,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l,sh)\<rangle>"
    by (iprover intro: eval_finalsId)
  obtain sfs i where shC: "sh D = \<lfloor>(sfs, i)\<rfloor>"
   using RedSCall s by(auto simp: bconf_def initPD_def dest: sees_method_fun)
  then have iDP: "i = Done \<or> i = Processing" using RedSCall s
    by (auto simp: bconf_def initPD_def dest: sees_method_fun[OF RedSCall.hyps(1)])
  have "method": "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns, body) in D" by fact
  have same_len\<^sub>1: "length Ts = length pns" and fv: "fv (body) \<subseteq> set pns"
    using "method" wf by (fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  have same_len: "length vs = length pns" by fact
  obtain l\<^sub>2' where l\<^sub>2': "l\<^sub>2' = [pns[\<mapsto>]vs]" by simp
  obtain h\<^sub>3 l\<^sub>3 sh\<^sub>3 where s': "s' = (h\<^sub>3,l\<^sub>3,sh\<^sub>3)" by (cases s')
  have eval_blocks:
    "P \<turnstile> \<langle>(blocks (pns, Ts, vs, body)),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using RedSCall.prems(2) s by simp
  hence id: "l\<^sub>3 = l" using fv s' same_len\<^sub>1 same_len
    by(fastforce elim: eval_closed_lcl_unchanged)
  from eval_blocks obtain l\<^sub>3' where body: "P \<turnstile> \<langle>body,(h,l\<^sub>2',sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3',sh\<^sub>3)\<rangle>"
  proof -
    from eval_blocks
    have "P \<turnstile> \<langle>blocks (pns,Ts,vs,body),(h,l,sh)\<rangle>
              \<Rightarrow>\<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle>" using s' same_len same_len\<^sub>1 by simp
    then obtain l''
      where "P \<turnstile> \<langle>body,(h,l(pns[\<mapsto>]vs),sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l'',sh\<^sub>3)\<rangle>"
      by (blast dest:blocksEval[OF same_len\<^sub>1[THEN sym] same_len[THEN sym]])
    from eval_restrict_lcl[OF wf this fv] same_len\<^sub>1 same_len
    have "P \<turnstile> \<langle>body,(h,[pns[\<mapsto>]vs],sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l''|`(set(pns)),sh\<^sub>3)\<rangle>" using wf method
      by(simp add:subset_insert_iff insert_Diff_if)
    thus ?thesis by(fastforce intro!:that simp add: l\<^sub>2')
  qed
  show ?case using iDP
  proof(cases i)
    case Done
    then have shC': "sh D = \<lfloor>(sfs, Done)\<rfloor> \<or> M = clinit \<and> sh D = \<lfloor>(sfs, Processing)\<rfloor>"
      using shC by simp
    have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l,sh\<^sub>3)\<rangle>"
     by (rule SCall[OF mVs method shC' same_len l\<^sub>2' body])
    with s s' id show ?thesis by simp
  next
    case Processing
    then have shC': "\<nexists>sfs. sh D = Some(sfs,Done)" and shP: "sh D = Some(sfs,Processing)"
      using shC by simp+
    then have init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>unit,(h,l,sh)\<rangle>"
      by(simp add: InitFinal InitProcessing Val)
    have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l,sh\<^sub>3)\<rangle>"
    proof(cases "M = clinit")
      case False show ?thesis by(rule SCallInit[OF mVs method shC' False init same_len l\<^sub>2' body])
    next
      case True
      then have shC': "sh D = \<lfloor>(sfs, Done)\<rfloor> \<or> M = clinit \<and> sh D = \<lfloor>(sfs, Processing)\<rfloor>"
        using shC Processing by simp
      have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l,sh\<^sub>3)\<rangle>"
       by (rule SCall[OF mVs method shC' same_len l\<^sub>2' body])
      with s s' id show ?thesis by simp
    qed
    with s s' id show ?thesis by simp
  qed(auto)
next
  case (SCallInitRed C M Ts T pns body D sh vs h l)
  then have seq: "P \<turnstile> \<langle>(INIT D ([D],False) \<leftarrow> unit);; C\<bullet>\<^sub>sM(map Val vs),(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using eval_init_seq by simp
  then show ?case
  proof(rule eval_cases(14)) \<comment> \<open> Seq \<close>
    fix v' s\<^sub>1 assume init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>"
      and call: "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    obtain h\<^sub>1 l\<^sub>1 sh\<^sub>1 where s\<^sub>1: "s\<^sub>1 = (h\<^sub>1,l\<^sub>1,sh\<^sub>1)" by(cases s\<^sub>1)
    then obtain sfs i where shD: "sh\<^sub>1 D = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Done \<or> i = Processing"
      using init_Val_PD[OF init] by auto
    show ?thesis
    proof(rule eval_cases(12)[OF call]) \<comment> \<open> SCall \<close>
      fix vsa ex es' assume "P \<turnstile> \<langle>map Val vs,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vsa @ throw ex # es',s'\<rangle>"
      then show ?thesis using evals_finals_same by (meson finals_def map_Val_nthrow_neq)
    next
      assume "\<forall>b Ts T a ba x. \<not> P \<turnstile> C sees M, b :  Ts\<rightarrow>T = (a, ba) in x"
      then show ?thesis using SCallInitRed.hyps(1) by auto
    next
      fix Ts T m D assume "P \<turnstile> C sees M, NonStatic :  Ts\<rightarrow>T = m in D"
      then show ?thesis using sees_method_fun[OF SCallInitRed.hyps(1)] by blast
    next
      fix vsa h1 l1 sh1 Ts T pns body D' a
      assume "e' = throw a" and vals: "P \<turnstile> \<langle>map Val vs,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vsa,(h1, l1, sh1)\<rangle>"
         and method: "P \<turnstile> C sees M, Static :  Ts\<rightarrow>T = (pns, body) in D'"
         and nDone: "\<forall>sfs. sh1 D' \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT D' ([D'],False) \<leftarrow> unit,(h1, l1, sh1)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
      have vs: "vs = vsa" and s\<^sub>1a: "s\<^sub>1 = (h1, l1, sh1)"
        using evals_finals_same[OF _ vals] map_Val_eq by auto
      have D: "D = D'" using sees_method_fun[OF SCallInitRed.hyps(1) method] by simp
      then have i: "i = Processing" using iDP shD s\<^sub>1 s\<^sub>1a nDone by simp
      then show ?thesis using D init' init_ProcessingE s\<^sub>1 s\<^sub>1a shD by blast
    next
      fix vsa h1 l1 sh1 Ts T pns' body' D' v' h\<^sub>2 l\<^sub>2 sh\<^sub>2 h\<^sub>3 l\<^sub>3 sh\<^sub>3
      assume s': "s' = (h\<^sub>3, l\<^sub>2, sh\<^sub>3)"
         and vals: "P \<turnstile> \<langle>map Val vs,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vsa,(h1, l1, sh1)\<rangle>"
         and method: "P \<turnstile> C sees M, Static :  Ts\<rightarrow>T = (pns', body') in D'"
         and nDone: "\<forall>sfs. sh1 D' \<noteq> \<lfloor>(sfs, Done)\<rfloor>"
         and init': "P \<turnstile> \<langle>INIT D' ([D'],False) \<leftarrow> unit,(h1, l1, sh1)\<rangle> \<Rightarrow> \<langle>Val v',(h\<^sub>2, l\<^sub>2, sh\<^sub>2)\<rangle>"
         and len: "length vsa = length pns'"
         and bstep: "P \<turnstile> \<langle>body',(h\<^sub>2, [pns' [\<mapsto>] vsa], sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3)\<rangle>"
      have vs: "vs = vsa" and s\<^sub>1a: "s\<^sub>1 = (h1, l1, sh1)"
        using evals_finals_same[OF _ vals] map_Val_eq by auto
      have D: "D = D'" and pns: "pns = pns'" and body: "body = body'"
        using sees_method_fun[OF SCallInitRed.hyps(1) method] by auto
      then have i: "i = Processing" using iDP shD s\<^sub>1 s\<^sub>1a nDone by simp
      then have s2: "(h\<^sub>2, l\<^sub>2, sh\<^sub>2) = s\<^sub>1" using D init' init_ProcessingE s\<^sub>1 s\<^sub>1a shD by blast
      then show ?thesis
        using eval_finalId SCallInit[OF eval_finalsId[of "map Val vs" P "(h,l,sh)"]
          SCallInitRed.hyps(1)] init init' len bstep nDone D pns body s' s\<^sub>1 s\<^sub>1a shD vals vs
          SCallInitRed.hyps(2-3) s2 by auto
    next
      fix vsa h\<^sub>2 l\<^sub>2 sh\<^sub>2 Ts T pns' body' D' sfs h\<^sub>3 l\<^sub>3 sh\<^sub>3
      assume s': "s' = (h\<^sub>3, l\<^sub>2, sh\<^sub>3)" and vals: "P \<turnstile> \<langle>map Val vs,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vsa,(h\<^sub>2, l\<^sub>2, sh\<^sub>2)\<rangle>"
         and method: "P \<turnstile> C sees M, Static :  Ts\<rightarrow>T = (pns', body') in D'"
         and "sh\<^sub>2 D' = \<lfloor>(sfs, Done)\<rfloor> \<or> M = clinit \<and> sh\<^sub>2 D' = \<lfloor>(sfs, Processing)\<rfloor>"
         and len: "length vsa = length pns'"
         and bstep: "P \<turnstile> \<langle>body',(h\<^sub>2, [pns' [\<mapsto>] vsa], sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l\<^sub>3, sh\<^sub>3)\<rangle>"
      have vs: "vs = vsa" and s\<^sub>1a: "s\<^sub>1 = (h\<^sub>2, l\<^sub>2, sh\<^sub>2)"
        using evals_finals_same[OF _ vals] map_Val_eq by auto
      have D: "D = D'" and pns: "pns = pns'" and body: "body = body'"
        using sees_method_fun[OF SCallInitRed.hyps(1) method] by auto
      then show ?thesis using SCallInit[OF eval_finalsId[of "map Val vs" P "(h,l,sh)"]
        SCallInitRed.hyps(1)] bstep SCallInitRed.hyps(2-3) len s' s\<^sub>1a vals vs init by auto
    qed
  next
    fix e assume e': "e' = throw e"
     and init: "P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h, l, sh)\<rangle> \<Rightarrow> \<langle>throw e,s'\<rangle>"
    obtain h' l' sh' where s': "s' = (h',l',sh')" by(cases s')
    then obtain sfs i where shC: "sh' D = \<lfloor>(sfs, i)\<rfloor>" and iDP: "i = Error"
      using init_throw_PD[OF init] by auto
    then show ?thesis using SCallInitRed.hyps(2-3) init e'
      SCallInitThrow[OF eval_finalsId[of "map Val vs" _] SCallInitRed.hyps(1)]
     by auto
  qed
next
  case (RedSCallNone C M vs s b)
  then have tes: "THROW NoSuchMethodError = e' \<and> s = s'"
    using eval_final_same by simp
  have "P \<turnstile> \<langle>map Val vs,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<rangle>" using eval_finalsId by simp
  then show ?case using RedSCallNone eval_evals.SCallNone tes by auto
next
  case (RedSCallNonStatic C M Ts T m D vs s b)
  then have tes: "THROW IncompatibleClassChangeError = e' \<and> s = s'"
    using eval_final_same by simp
  have "P \<turnstile> \<langle>map Val vs,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<rangle>" using eval_finalsId by simp
  then show ?case using RedSCallNonStatic eval_evals.SCallNonStatic tes by auto
next
  case InitBlockRed
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros eval_finalId
                  simp: assigned_def map_upd_triv fun_upd_same)
next
  case (RedInitBlock V T v u s b)
  then have "P \<turnstile> \<langle>Val u,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by simp
  then obtain s': "s'=s" and e': "e'=Val u" by cases simp
  obtain h l sh where s: "s=(h,l,sh)" by (cases s)
  have "P \<turnstile> \<langle>{V:T :=Val v; Val u},(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val u,(h, (l(V\<mapsto>v))(V:=l V), sh)\<rangle>"
    by (fastforce intro!: eval_evals.intros)
  then have "P \<turnstile> \<langle>{V:T := Val v; Val u},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
  then show ?case by simp
next
  case BlockRedNone
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros 
                 simp add: fun_upd_same fun_upd_idem)
next
  case BlockRedSome
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros 
                 simp add:  fun_upd_same fun_upd_idem)
next
 case (RedBlock V T v s b) 
 then have "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by simp
 then obtain s': "s'=s" and e': "e'=Val v" 
    by cases simp
  obtain h l sh where s: "s=(h,l,sh)" by (cases s)
 have "P \<turnstile> \<langle>Val v,(h,l(V:=None),sh)\<rangle> \<Rightarrow> \<langle>Val v,(h,l(V:=None),sh)\<rangle>" 
   by (rule eval_evals.intros)
 hence "P \<turnstile> \<langle>{V:T;Val v},(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h,(l(V:=None))(V:=l V),sh)\<rangle>"
   by (rule eval_evals.Block)
 then have "P \<turnstile> \<langle>{V:T; Val v},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
 then show ?case by simp
next
  case (SeqRed e s b e1 s1 b1 e\<^sub>2) show ?case
  proof(cases "val_of e")
    case None show ?thesis
    proof(cases "lass_val_of e")
      case lNone:None
      then have bconf: "P,shp s \<turnstile>\<^sub>b (e,b) \<surd>" using SeqRed.prems(1) None by simp
      then show ?thesis using SeqRed using seq_ext by fastforce
    next
      case (Some p)
      obtain V' v' where p: "p = (V',v')" and e: "e = V':=Val v'"
        using lass_val_of_spec[OF Some] by(cases p, auto)
      obtain h l sh h' l' sh' where s: "s = (h,l,sh)" and s1: "s1 = (h',l',sh')" by(cases s, cases s1)
      then have red: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e1,(h',l',sh'),b1\<rangle>" using SeqRed.hyps(1) by simp
      then have s\<^sub>1': "e1 = unit \<and> h' = h \<and> l' = l(V' \<mapsto> v') \<and> sh' = sh"
        using lass_val_of_red[OF Some red] p e by simp
      then have eval: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e1,s1\<rangle>" using e s s1 LAss Val by auto
      then show ?thesis
        by (metis SeqRed.prems(2) eval_final eval_final_same seq_ext)
    qed
  next
    case (Some a) then show ?thesis using SeqRed.hyps(1) val_no_step by blast
  qed
next
  case RedSeq
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case CondRed
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros simp: val_no_step) 
next
  case RedCondT
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedCondF
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedWhile
  thus ?case
    by (auto simp add: unfold_while intro:eval_evals.intros elim:eval_cases)
next
  case ThrowRed then show ?case by(fastforce elim: eval_cases simp: eval_evals.intros)
next
  case RedThrowNull
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case TryRed thus ?case
    by(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedTryCatch
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (RedTryFail s a D fs C V e\<^sub>2 b)
  thus ?case
    by (cases s)(auto elim!: eval_cases intro: eval_evals.intros)
next
  case ListRed1
  thus ?case
    by (fastforce elim: evals_cases intro: eval_evals.intros simp: val_no_step)
next
  case ListRed2
  thus ?case
    by (fastforce elim!: evals_cases eval_cases 
                 intro: eval_evals.intros eval_finalId)
next
  case (RedInit e1 C b s1 b') then show ?case using InitFinal by simp
next
  case (InitNoneRed sh C C' Cs e h l b)
  show ?case using InitNone InitNoneRed.hyps InitNoneRed.prems(2) by auto
next
  case (RedInitDone sh C sfs C' Cs e h l b)
  show ?case using InitDone RedInitDone.hyps RedInitDone.prems(2) by auto
next
  case (RedInitProcessing sh C sfs C' Cs e h l b)
  show ?case using InitProcessing RedInitProcessing.hyps RedInitProcessing.prems(2) by auto
next
  case (RedInitError sh C sfs C' Cs e h l b)
  show ?case using InitError RedInitError.hyps RedInitError.prems(2) by auto
next
  case (InitObjectRed sh C sfs sh' C' Cs e h l b) show ?case using InitObject InitObjectRed by auto
next
  case (InitNonObjectSuperRed sh C sfs D r sh' C' Cs e h l b)
  show ?case using InitNonObject InitNonObjectSuperRed by auto
next
  case (RedInitRInit C' C Cs e h l sh b)
  show ?case using InitRInit RedInitRInit by auto
next
  case (RInitRed e s b e'' s'' b'' C Cs e\<^sub>0)
  then have IH: "\<And>e' s'. P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by simp
  show ?case using RInitRed rinit_ext[OF IH] by simp
next
  case (RedRInit sh C sfs i sh' C' Cs v e h l b s' e')
  then have init: "P \<turnstile> \<langle>(INIT C' (Cs,True) \<leftarrow> e), (h, l, sh(C \<mapsto> (sfs, Done)))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using RedRInit by simp
  then show ?case using RInit RedRInit.hyps(1) RedRInit.hyps(3) Val by fastforce
next
  case BinOpThrow2
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAssThrow2
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case SFAssThrow
  then show ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (CallThrowParams es vs e es' v M s b)
  have val: "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (rule eval_evals.intros)
  have eval_e: "P \<turnstile> \<langle>throw (e),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using CallThrowParams by simp
  then obtain xa where e': "e' = Throw xa" by (cases) (auto dest!: eval_final)
  with list_eval_Throw [OF eval_e]
  have vals: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ Throw xa # es',s'\<rangle>"
    using CallThrowParams.hyps(1) eval_e list_eval_Throw by blast
  then have "P \<turnstile> \<langle>Val v\<bullet>M(es),s\<rangle> \<Rightarrow> \<langle>Throw xa,s'\<rangle>"
   using eval_evals.CallParamsThrow[OF val vals] by simp
  thus ?case using e' by simp
next
  case (SCallThrowParams es vs e es' C M s b)
  have eval_e: "P \<turnstile> \<langle>throw (e),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using SCallThrowParams by simp
  then obtain xa where e': "e' = Throw xa" by (cases) (auto dest!: eval_final)
  then have "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ Throw xa # es',s'\<rangle>"
    using SCallThrowParams.hyps(1) eval_e list_eval_Throw by blast
  then have "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<rangle> \<Rightarrow> \<langle>Throw xa,s'\<rangle>"
    by (rule eval_evals.SCallParamsThrow)
  thus ?case using e' by simp
next
  case (BlockThrow V T a s b)
  then have "P \<turnstile> \<langle>Throw a, s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by simp
  then obtain s': "s' = s" and e': "e' = Throw a"
    by cases (auto elim!:eval_cases)
  obtain h l sh where s: "s=(h,l,sh)" by (cases s)
  have "P \<turnstile> \<langle>Throw a, (h,l(V:=None),sh)\<rangle> \<Rightarrow> \<langle>Throw a, (h,l(V:=None),sh)\<rangle>"
    by (simp add:eval_evals.intros eval_finalId)
  hence "P\<turnstile>\<langle>{V:T;Throw a},(h,l,sh)\<rangle> \<Rightarrow> \<langle>Throw a, (h,(l(V:=None))(V:=l V),sh)\<rangle>"
    by (rule eval_evals.Block)
  then have "P \<turnstile> \<langle>{V:T; Throw a},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
  then show ?case by simp
next
  case (InitBlockThrow V T v a s b)
  then have "P \<turnstile> \<langle>Throw a,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by simp
  then obtain s': "s' = s" and e': "e' = Throw a"
    by cases (auto elim!:eval_cases)
  obtain h l sh where s: "s = (h,l,sh)" by (cases s)
  have "P \<turnstile> \<langle>{V:T :=Val v; Throw a},(h,l,sh)\<rangle> \<Rightarrow> \<langle>Throw a, (h, (l(V\<mapsto>v))(V:=l V),sh)\<rangle>"
    by(fastforce intro:eval_evals.intros)
  then have "P \<turnstile> \<langle>{V:T := Val v; Throw a},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
  then show ?case by simp
next
  case (RInitInitThrow sh C sfs i sh' a D Cs e h l b)
  have IH: "\<And>e' s'. P \<turnstile> \<langle>RI (D,Throw a) ; Cs \<leftarrow> e,(h, l, sh(C \<mapsto> (sfs, Error)))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow>
    P \<turnstile> \<langle>RI (C,Throw a) ; D # Cs \<leftarrow> e,(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using RInitInitFail[OF eval_finalId] RInitInitThrow by simp
  then show ?case using RInitInitThrow.hyps(2) RInitInitThrow.prems(2) by auto
next
  case (RInitThrow sh C sfs i sh' a e h l b)
  then have e': "e' = Throw a" and s': "s' = (h,l,sh')"
    using eval_final_same final_def by fastforce+
  show ?case using RInitFailFinal RInitThrow.hyps(1) RInitThrow.hyps(2) e' eval_finalId s' by auto
qed(auto elim: eval_cases simp: eval_evals.intros)
(*>*)

(*<*)
(* ... und wieder anschalten: *)
declare split_paired_All [simp] split_paired_Ex [simp]
(*>*)

text \<open> Its extension to @{text"\<rightarrow>*"}: \<close> 

lemma extend_eval:
assumes wf: "wwf_J_prog P"
and reds: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e'',s'',b''\<rangle>" and eval_rest:  "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
and iconf: "iconf (shp s) e" and bconf: "P,shp s \<turnstile>\<^sub>b (e::expr,b) \<surd>"
shows "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
(*<*)
using reds eval_rest iconf bconf
proof (induct rule: converse_rtrancl_induct3)
  case refl then show ?case by simp
next
  case (step e1 s1 b1 e2 s2 b2)
  then have ic: "iconf (shp s2) e2" using Red_preserves_iconf local.wf by blast
  then have ec: "P,shp s2 \<turnstile>\<^sub>b (e2,b2) \<surd>"
    using Red_preserves_bconf local.wf step.hyps(1) step.prems(2) step.prems(3) by blast
  show ?case using step ic ec extend_1_eval[OF wf step.hyps(1)] by simp
qed
(*>*)


lemma extend_evals:
assumes wf: "wwf_J_prog P"
and reds: "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es'',s'',b''\<rangle>" and eval_rest:  "P \<turnstile> \<langle>es'',s''\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
and iconf: "iconfs (shp s) es" and bconf: "P,shp s \<turnstile>\<^sub>b (es::expr list,b) \<surd>"
shows "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
(*<*)
using reds eval_rest iconf bconf
proof (induct rule: converse_rtrancl_induct3)
  case refl then show ?case by simp
next
  case (step es1 s1 b1 es2 s2 b2)
  then have ic: "iconfs (shp s2) es2" using Reds_preserves_iconf local.wf by blast
  then have ec: "P,shp s2 \<turnstile>\<^sub>b (es2,b2) \<surd>"
    using Reds_preserves_bconf local.wf step.hyps(1) step.prems(2) step.prems(3) by blast
  show ?case using step ic ec extend_1_evals[OF wf step.hyps(1)] by simp
qed
(*>*)

text \<open> Finally, small step semantics can be simulated by big step semantics:
\<close>

theorem
assumes wf: "wwf_J_prog P"
shows small_by_big:
 "\<lbrakk>P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>; iconf (shp s) e; P,shp s \<turnstile>\<^sub>b (e,b) \<surd>; final e'\<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
and "\<lbrakk>P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle>; iconfs (shp s) es; P,shp s \<turnstile>\<^sub>b (es,b) \<surd>; finals es'\<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
(*<*)
proof -
  note wf 
  moreover assume "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
  moreover assume "final e'"
  then have "P \<turnstile> \<langle>e',s'\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    by (simp add: eval_finalId)
  moreover assume "iconf (shp s) e"
  moreover assume "P,shp s \<turnstile>\<^sub>b (e,b) \<surd>"
  ultimately show "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    by (rule extend_eval)
next
  assume fins: "finals es'"
  note wf 
  moreover assume "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle>"
  moreover have "P \<turnstile> \<langle>es',s'\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>" using fins
    by (rule eval_finalsId)
  moreover assume "iconfs (shp s) es"
  moreover assume "P,shp s \<turnstile>\<^sub>b (es,b) \<surd>"
  ultimately show "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
    by (rule extend_evals)
qed
(*>*)

subsection "Equivalence"

text\<open> And now, the crowning achievement: \<close>

corollary big_iff_small:
"\<lbrakk> wwf_J_prog P; iconf (shp s) e; P,shp s \<turnstile>\<^sub>b (e::expr,b) \<surd> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>  =  (P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',False\<rangle> \<and> final e')"
(*<*)by(blast dest: big_by_small eval_final small_by_big)(*>*)

corollary big_iff_small_WT:
  "wwf_J_prog P \<Longrightarrow> P,E \<turnstile> e::T \<Longrightarrow> P,shp s \<turnstile>\<^sub>b (e,b) \<surd> \<Longrightarrow>
  P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>  =  (P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',False\<rangle> \<and> final e')"
(*<*)by(blast dest: big_iff_small WT_nsub_RI nsub_RI_iconf)(*>*)


subsection \<open> Lifting type safety to @{text"\<Rightarrow>"} \<close>

text\<open> \dots and now to the big step semantics, just for fun. \<close>

lemma eval_preserves_sconf:
fixes s::state and s'::state
assumes  "wf_J_prog P" and "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" and "iconf (shp s) e"
 and "P,E \<turnstile> e::T" and "P,E \<turnstile> s\<surd>"
shows "P,E \<turnstile> s'\<surd>"
(*<*)
proof -
  have "P,shp s \<turnstile>\<^sub>b (e,False) \<surd>" by(simp add: bconf_def)
  with assms show ?thesis
    by(blast intro:Red_preserves_sconf Red_preserves_iconf Red_preserves_bconf big_by_small
                   WT_implies_WTrt wf_prog_wwf_prog)
qed
(*>*)


lemma eval_preserves_type:
fixes s::state
assumes wf: "wf_J_prog P"
 and "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" and "P,E \<turnstile> s\<surd>" and "iconf (shp s) e" and "P,E \<turnstile> e::T"
shows "\<exists>T'. P \<turnstile> T' \<le> T \<and> P,E,hp s',shp s' \<turnstile> e':T'"
(*<*)
proof -
  have "P,shp s \<turnstile>\<^sub>b (e,False) \<surd>" by(simp add: bconf_def)
  with assms show ?thesis by(blast dest:big_by_small[OF wf_prog_wwf_prog[OF wf]]
                                        WT_implies_WTrt Red_preserves_type[OF wf])
qed
(*>*)


end
