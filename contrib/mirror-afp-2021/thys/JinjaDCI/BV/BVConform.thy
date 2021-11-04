(*  Title:      JinjaDCI/BV/BVConform.thy

    Author:     Cornelia Pusch, Gerwin Klein, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory BV/BVConform.thy by Cornelia Pusch and Gerwin Klein

The invariant for the type safety proof.
*)

section \<open> BV Type Safety Invariant \<close>

theory BVConform
imports BVSpec "../JVM/JVMExec" "../Common/Conform"
begin

subsection \<open> @{text "correct_state"} definitions \<close>

definition confT :: "'c prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty err \<Rightarrow> bool" 
    ("_,_ \<turnstile> _ :\<le>\<^sub>\<top> _" [51,51,51,51] 50)
where
  "P,h \<turnstile> v :\<le>\<^sub>\<top> E \<equiv> case E of Err \<Rightarrow> True | OK T \<Rightarrow> P,h \<turnstile> v :\<le> T"

notation (ASCII)
  confT  ("_,_ |- _ :<=T _" [51,51,51,51] 50)

abbreviation
  confTs :: "'c prog \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> ty\<^sub>l \<Rightarrow> bool" 
      ("_,_ \<turnstile> _ [:\<le>\<^sub>\<top>] _" [51,51,51,51] 50) where
  "P,h \<turnstile> vs [:\<le>\<^sub>\<top>] Ts \<equiv> list_all2 (confT P h) vs Ts"

notation (ASCII)
  confTs  ("_,_ |- _ [:<=T] _" [51,51,51,51] 50)

fun Called_context :: "jvm_prog \<Rightarrow> cname \<Rightarrow> instr \<Rightarrow> bool" where
"Called_context P C\<^sub>0 (New C') = (C\<^sub>0=C')" |
"Called_context P C\<^sub>0 (Getstatic C F D) =  ((C\<^sub>0=D) \<and> (\<exists>t. P \<turnstile> C has F,Static:t in D))" |
"Called_context P C\<^sub>0 (Putstatic C F D) = ((C\<^sub>0=D) \<and> (\<exists>t. P \<turnstile> C has F,Static:t in D))" |
"Called_context P C\<^sub>0 (Invokestatic C M n)
   = (\<exists>Ts T m D. (C\<^sub>0=D) \<and> P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D)" |
"Called_context P _ _ = False"

abbreviation Called_set :: "instr set" where
"Called_set \<equiv> {i. \<exists>C. i = New C} \<union> {i. \<exists>C M n. i = Invokestatic C M n}
                 \<union> {i. \<exists>C F D. i = Getstatic C F D} \<union> {i. \<exists>C F D. i = Putstatic C F D}"

lemma Called_context_Called_set:
 "Called_context P D i \<Longrightarrow> i \<in> Called_set" by(cases i, auto)

fun valid_ics :: "jvm_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> cname \<times> mname \<times> pc \<times> init_call_status \<Rightarrow> bool"
  ("_,_,_ \<turnstile>\<^sub>i _" [51,51,51,51] 50) where
"valid_ics P h sh (C,M,pc,Calling C' Cs)
 = (let ins = instrs_of P C M in Called_context P (last (C'#Cs)) (ins!pc)
    \<and> is_class P C')" |
"valid_ics P h sh (C,M,pc,Throwing Cs a)
 =(let ins = instrs_of P C M in \<exists>C1. Called_context P C1 (ins!pc)
    \<and> (\<exists>obj. h a = Some obj))" |
"valid_ics P h sh (C,M,pc,Called Cs)
 = (let ins = instrs_of P C M
    in \<exists>C1 sobj. Called_context P C1 (ins!pc) \<and> sh C1 = Some sobj)" |
"valid_ics P _ _ _ = True"

definition conf_f  :: "jvm_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> ty\<^sub>i \<Rightarrow> bytecode \<Rightarrow> frame \<Rightarrow> bool"
where
  "conf_f P h sh \<equiv> \<lambda>(ST,LT) is (stk,loc,C,M,pc,ics).
  P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is \<and> P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"

lemma conf_f_def2:
  "conf_f P h sh (ST,LT) is (stk,loc,C,M,pc,ics) \<equiv>
  P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is \<and> P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
  by (simp add: conf_f_def)

primrec conf_fs :: "[jvm_prog,heap,sheap,ty\<^sub>P,cname,mname,nat,ty,frame list] \<Rightarrow> bool"
where
  "conf_fs P h sh \<Phi> C\<^sub>0 M\<^sub>0 n\<^sub>0 T\<^sub>0 [] = True"
| "conf_fs P h sh \<Phi> C\<^sub>0 M\<^sub>0 n\<^sub>0 T\<^sub>0 (f#frs) =
  (let (stk,loc,C,M,pc,ics) = f in
  (\<exists>ST LT b Ts T mxs mxl\<^sub>0 is xt.
    \<Phi> C M ! pc = Some (ST,LT) \<and> 
    (P \<turnstile> C sees M,b:Ts \<rightarrow> T = (mxs,mxl\<^sub>0,is,xt) in C) \<and>
    ((\<exists>D Ts' T' m D'. M\<^sub>0 \<noteq> clinit \<and> ics = No_ics \<and>
       is!pc = Invoke M\<^sub>0 n\<^sub>0 \<and> ST!n\<^sub>0 = Class D \<and>
       P \<turnstile> D sees M\<^sub>0,NonStatic:Ts' \<rightarrow> T' = m in D' \<and> P \<turnstile> C\<^sub>0 \<preceq>\<^sup>* D' \<and> P \<turnstile> T\<^sub>0 \<le> T') \<or>
     (\<exists>D Ts' T' m. M\<^sub>0 \<noteq> clinit \<and> ics = No_ics \<and>
       is!pc = Invokestatic D M\<^sub>0 n\<^sub>0 \<and>
       P \<turnstile> D sees M\<^sub>0,Static:Ts' \<rightarrow> T' = m in C\<^sub>0 \<and> P \<turnstile> T\<^sub>0 \<le> T') \<or>
     (M\<^sub>0 = clinit \<and> (\<exists>Cs. ics = Called Cs))) \<and>
    conf_f P h sh (ST, LT) is f \<and> conf_fs P h sh \<Phi> C M (size Ts) T frs))"

fun ics_classes :: "init_call_status \<Rightarrow> cname list" where
"ics_classes (Calling C Cs) = Cs" |
"ics_classes (Throwing Cs a) = Cs" |
"ics_classes (Called Cs) = Cs" |
"ics_classes _ = []"

fun frame_clinit_classes :: "frame \<Rightarrow> cname list" where
"frame_clinit_classes (stk,loc,C,M,pc,ics) = (if M=clinit then [C] else []) @ ics_classes ics"

abbreviation clinit_classes :: "frame list \<Rightarrow> cname list" where
"clinit_classes frs \<equiv> concat (map frame_clinit_classes frs)"

definition distinct_clinit :: "frame list \<Rightarrow> bool" where
"distinct_clinit frs \<equiv> distinct (clinit_classes frs)"

definition conf_clinit :: "jvm_prog \<Rightarrow> sheap \<Rightarrow> frame list \<Rightarrow> bool" where
"conf_clinit P sh frs
   \<equiv> distinct_clinit frs \<and>
      (\<forall>C \<in> set(clinit_classes frs). is_class P C \<and> (\<exists>sfs. sh C = Some(sfs, Processing)))"

(*************************)

definition correct_state :: "[jvm_prog,ty\<^sub>P,jvm_state] \<Rightarrow> bool"  ("_,_ \<turnstile> _ \<surd>"  [61,0,0] 61)
where
  "correct_state P \<Phi> \<equiv> \<lambda>(xp,h,frs,sh).
  case xp of
     None \<Rightarrow> (case frs of
             [] \<Rightarrow> True
             | (f#fs) \<Rightarrow> P\<turnstile> h\<surd> \<and> P,h\<turnstile>\<^sub>s sh\<surd> \<and> conf_clinit P sh frs \<and>
             (let (stk,loc,C,M,pc,ics) = f
              in \<exists>b Ts T mxs mxl\<^sub>0 is xt \<tau>.
                    (P \<turnstile> C sees M,b:Ts\<rightarrow>T = (mxs,mxl\<^sub>0,is,xt) in C) \<and>
                    \<Phi> C M ! pc = Some \<tau> \<and>
                    conf_f P h sh \<tau> is f \<and> conf_fs P h sh \<Phi> C M (size Ts) T fs))
  | Some x \<Rightarrow> frs = []" 

notation
  correct_state  ("_,_ |- _ [ok]"  [61,0,0] 61)

subsection \<open> Values and @{text "\<top>"} \<close>

lemma confT_Err [iff]: "P,h \<turnstile> x :\<le>\<^sub>\<top> Err" 
  by (simp add: confT_def)

lemma confT_OK [iff]:  "P,h \<turnstile> x :\<le>\<^sub>\<top> OK T = (P,h \<turnstile> x :\<le> T)"
  by (simp add: confT_def)

lemma confT_cases:
  "P,h \<turnstile> x :\<le>\<^sub>\<top> X = (X = Err \<or> (\<exists>T. X = OK T \<and> P,h \<turnstile> x :\<le> T))"
  by (cases X) auto

lemma confT_hext [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> x :\<le>\<^sub>\<top> T"
  by (cases T) (blast intro: conf_hext)+

lemma confT_widen [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; P \<turnstile> T \<le>\<^sub>\<top> T' \<rbrakk> \<Longrightarrow> P,h \<turnstile> x :\<le>\<^sub>\<top> T'"
  by (cases T', auto intro: conf_widen)


subsection \<open> Stack and Registers \<close>

lemmas confTs_Cons1 [iff] = list_all2_Cons1 [of "confT P h"] for P h

lemma confTs_confT_sup:
  "\<lbrakk> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT; n < size LT; LT!n = OK T; P \<turnstile> T \<le> T' \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> (loc!n) :\<le> T'"
(*<*)
  apply (frule list_all2_lengthD)
  apply (drule list_all2_nthD, simp)
  apply simp
  apply (erule conf_widen, assumption+)
  done
(*>*)

lemma confTs_hext [intro?]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
  by (fast elim: list_all2_mono confT_hext)    

lemma confTs_widen [intro?, trans]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> P \<turnstile> LT [\<le>\<^sub>\<top>] LT' \<Longrightarrow> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'"
  by (rule list_all2_trans, rule confT_widen)

lemma confTs_map [iff]:
  "\<And>vs. (P,h \<turnstile> vs [:\<le>\<^sub>\<top>] map OK Ts) = (P,h \<turnstile> vs [:\<le>] Ts)"
  by (induct Ts) (auto simp: list_all2_Cons2)

lemma reg_widen_Err [iff]:
  "\<And>LT. (P \<turnstile> replicate n Err [\<le>\<^sub>\<top>] LT) = (LT = replicate n Err)"
  by (induct n) (auto simp: list_all2_Cons1)
    
lemma confTs_Err [iff]:
  "P,h \<turnstile> replicate n v [:\<le>\<^sub>\<top>] replicate n Err"
  by (induct n) auto

subsection \<open> valid @{text "init_call_status"} \<close>

lemma valid_ics_shupd:
assumes "P,h,sh \<turnstile>\<^sub>i (C, M, pc, ics)" and "distinct (C'#ics_classes ics)"
shows "P,h,sh(C' \<mapsto> (sfs, i')) \<turnstile>\<^sub>i (C, M, pc, ics)"
using assms by(cases ics; clarsimp simp: fun_upd_apply) fastforce
  
subsection \<open> correct-frame \<close>

lemma conf_f_Throwing:
assumes "conf_f P h sh (ST, LT) is (stk, loc, C, M, pc, Called Cs)"
  and "is_class P C'" and "h xcp = Some obj" and "sh C' = Some(sfs,Processing)"
shows "conf_f P h sh (ST, LT) is (stk, loc, C, M, pc, Throwing (C' # Cs) xcp)"
using assms by(auto simp: conf_f_def2)

lemma conf_f_shupd:
assumes "conf_f P h sh (ST,LT) ins f"
 and "i = Processing
       \<or> (distinct (C#ics_classes (ics_of f)) \<and> (curr_method f = clinit \<longrightarrow> C \<noteq> curr_class f))"
shows "conf_f P h (sh(C \<mapsto> (sfs, i))) (ST,LT) ins f"
using assms
 by(cases f, cases "ics_of f"; clarsimp simp: conf_f_def2 fun_upd_apply) fastforce+

lemma conf_f_shupd':
assumes "conf_f P h sh (ST,LT) ins f"
 and "sh C = Some(sfs,i)"
shows "conf_f P h (sh(C \<mapsto> (sfs', i))) (ST,LT) ins f"
using assms
 by(cases f, cases "ics_of f"; clarsimp simp: conf_f_def2 fun_upd_apply) fastforce+

subsection \<open> correct-frames \<close>

lemmas [simp del] = fun_upd_apply

lemma conf_fs_hext:
  "\<And>C M n T\<^sub>r. 
  \<lbrakk> conf_fs P h sh \<Phi> C M n T\<^sub>r frs; h \<unlhd> h' \<rbrakk> \<Longrightarrow> conf_fs P h' sh \<Phi> C M n T\<^sub>r frs"
(*<*)
apply (induct frs)
 apply simp
apply clarify
apply (simp (no_asm_use))
apply clarify
apply (unfold conf_f_def)
apply (simp (no_asm_use))
apply clarify
apply (fastforce elim!: confs_hext confTs_hext)
done
(*>*)


lemma conf_fs_shupd:
assumes "conf_fs P h sh \<Phi> C\<^sub>0 M n T frs"
 and dist: "distinct (C#clinit_classes frs)"
shows "conf_fs P h (sh(C \<mapsto> (sfs, i))) \<Phi> C\<^sub>0 M n T frs"
using assms proof(induct frs arbitrary: C\<^sub>0 C M n T)
  case (Cons f' frs')
  then obtain stk' loc' C' M' pc' ics' where f': "f' = (stk',loc',C',M',pc',ics')" by(cases f')
  with assms Cons obtain ST LT b Ts T1 mxs mxl\<^sub>0 ins xt where
    ty: "\<Phi> C' M' ! pc' = Some (ST,LT)" and
    meth: "P \<turnstile> C' sees M',b:Ts \<rightarrow> T1 = (mxs,mxl\<^sub>0,ins,xt) in C'" and
    conf: "conf_f P h sh (ST, LT) ins f'" and
    confs: "conf_fs P h sh \<Phi> C' M' (size Ts) T1 frs'" by clarsimp

  from f' Cons.prems(2) have
   "distinct (C#ics_classes (ics_of f')) \<and> (curr_method f' = clinit \<longrightarrow> C \<noteq> curr_class f')"
     by fastforce
  with conf_f_shupd[where C=C, OF conf] have
    conf': "conf_f P h (sh(C \<mapsto> (sfs, i))) (ST, LT) ins f'" by simp

  from Cons.prems(2) have dist': "distinct (C # clinit_classes frs')"
    by(auto simp: distinct_length_2_or_more)
  from Cons.hyps[OF confs dist'] have
    confs': "conf_fs P h (sh(C \<mapsto> (sfs, i))) \<Phi> C' M' (length Ts) T1 frs'" by simp

  from conf' confs' ty meth f' Cons.prems show ?case by(fastforce dest: sees_method_fun)
qed(simp)

lemma conf_fs_shupd':
assumes "conf_fs P h sh \<Phi> C\<^sub>0 M n T frs"
 and shC: "sh C = Some(sfs,i)"
shows "conf_fs P h (sh(C \<mapsto> (sfs', i))) \<Phi> C\<^sub>0 M n T frs"
using assms proof(induct frs arbitrary: C\<^sub>0 C M n T sfs i sfs')
  case (Cons f' frs')
  then obtain stk' loc' C' M' pc' ics' where f': "f' = (stk',loc',C',M',pc',ics')" by(cases f')
  with assms Cons obtain ST LT b Ts T1 mxs mxl\<^sub>0 ins xt where
    ty: "\<Phi> C' M' ! pc' = Some (ST,LT)" and
    meth: "P \<turnstile> C' sees M',b:Ts \<rightarrow> T1 = (mxs,mxl\<^sub>0,ins,xt) in C'" and
    conf: "conf_f P h sh (ST, LT) ins f'" and
    confs: "conf_fs P h sh \<Phi> C' M' (size Ts) T1 frs'" and
    shC': "sh C = Some(sfs,i)" by clarsimp

  have conf': "conf_f P h (sh(C \<mapsto> (sfs', i))) (ST, LT) ins f'" by(rule conf_f_shupd'[OF conf shC'])

  from Cons.hyps[OF confs shC'] have
    confs': "conf_fs P h (sh(C \<mapsto> (sfs', i))) \<Phi> C' M' (length Ts) T1 frs'" by simp

  from conf' confs' ty meth f' Cons.prems show ?case by(fastforce dest: sees_method_fun)
qed(simp)

subsection \<open> correctness wrt @{term clinit} use \<close>

lemma conf_clinit_Cons:
assumes "conf_clinit P sh (f#frs)"
shows "conf_clinit P sh frs"
proof -
  from assms have dist: "distinct_clinit (f#frs)"
   by(cases "curr_method f = clinit", auto simp: conf_clinit_def)
  then have dist': "distinct_clinit frs" by(simp add: distinct_clinit_def)

  with assms show ?thesis by(cases frs; fastforce simp: conf_clinit_def)
qed

lemma conf_clinit_Cons_Cons:
 "conf_clinit P sh (f'#f#frs) \<Longrightarrow> conf_clinit P sh (f'#frs)"
 by(auto simp: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_diff:
assumes "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)"
shows "conf_clinit P sh ((stk',loc',C,M,pc',ics)#frs)"
using assms by(cases "M = clinit", simp_all add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_diff':
assumes "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)"
shows "conf_clinit P sh ((stk',loc',C,M,pc',No_ics)#frs)"
using assms by(cases "M = clinit", simp_all add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Called_Throwing:
 "conf_clinit P sh ((stk', loc', C', clinit, pc', ics') # (stk, loc, C, M, pc, Called Cs) # fs)
  \<Longrightarrow> conf_clinit P sh ((stk, loc, C, M, pc, Throwing (C' # Cs) xcp) # fs)"
 by(simp add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Throwing:
 "conf_clinit P sh ((stk, loc, C, M, pc, Throwing (C'#Cs) xcp) # fs)
  \<Longrightarrow> conf_clinit P sh ((stk, loc, C, M, pc, Throwing Cs xcp) # fs)"
 by(simp add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Called:
 "\<lbrakk> conf_clinit P sh ((stk, loc, C, M, pc, Called (C'#Cs)) # frs);
    P \<turnstile> C' sees clinit,Static: [] \<rightarrow> Void=(mxs',mxl',ins',xt') in C' \<rbrakk>
  \<Longrightarrow> conf_clinit P sh (create_init_frame P C' # (stk, loc, C, M, pc, Called Cs) # frs)"
 by(simp add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Cons_nclinit:
assumes "conf_clinit P sh frs" and nclinit: "M \<noteq> clinit"
shows "conf_clinit P sh ((stk, loc, C, M, pc, No_ics) # frs)"
proof -
  from nclinit
  have "clinit_classes ((stk, loc, C, M, pc, No_ics) # frs) = clinit_classes frs" by simp
  with assms show ?thesis by(simp add: conf_clinit_def distinct_clinit_def)
qed

lemma conf_clinit_Invoke:
assumes "conf_clinit P sh ((stk, loc, C, M, pc, ics) # frs)" and "M' \<noteq> clinit"
shows "conf_clinit P sh ((stk', loc', C', M', pc', No_ics) # (stk, loc, C, M, pc, No_ics) # frs)"
 using assms conf_clinit_Cons_nclinit conf_clinit_diff' by auto

lemma conf_clinit_nProc_dist:
assumes "conf_clinit P sh frs"
  and "\<forall>sfs. sh C \<noteq> Some(sfs,Processing)"
shows "distinct (C # clinit_classes frs)"
using assms by(auto simp: conf_clinit_def distinct_clinit_def)


lemma conf_clinit_shupd:
assumes "conf_clinit P sh frs"
 and dist: "distinct (C#clinit_classes frs)"
shows "conf_clinit P (sh(C \<mapsto> (sfs, i))) frs"
using assms by(simp add: conf_clinit_def fun_upd_apply)

lemma conf_clinit_shupd':
assumes "conf_clinit P sh frs"
 and "sh C = Some(sfs,i)"
shows "conf_clinit P (sh(C \<mapsto> (sfs', i))) frs"
using assms by(fastforce simp: conf_clinit_def fun_upd_apply)

lemma conf_clinit_shupd_Called:
assumes "conf_clinit P sh ((stk,loc,C,M,pc,Calling C' Cs)#frs)"
 and dist: "distinct (C'#clinit_classes ((stk,loc,C,M,pc,Calling C' Cs)#frs))"
 and cls: "is_class P C'"
shows "conf_clinit P (sh(C' \<mapsto> (sfs, Processing))) ((stk,loc,C,M,pc,Called (C'#Cs))#frs)"
using assms by(clarsimp simp: conf_clinit_def fun_upd_apply distinct_clinit_def)

lemma conf_clinit_shupd_Calling:
assumes "conf_clinit P sh ((stk,loc,C,M,pc,Calling C' Cs)#frs)"
 and dist: "distinct (C'#clinit_classes ((stk,loc,C,M,pc,Calling C' Cs)#frs))"
 and cls: "is_class P C'"
shows "conf_clinit P (sh(C' \<mapsto> (sfs, Processing)))
         ((stk,loc,C,M,pc,Calling (fst(the(class P C'))) (C'#Cs))#frs)"
using assms by(clarsimp simp: conf_clinit_def fun_upd_apply distinct_clinit_def)

subsection \<open> correct state \<close>

lemma correct_state_Cons:
assumes cr: "P,\<Phi> |- (xp,h,f#frs,sh) [ok]"
shows "P,\<Phi> |- (xp,h,frs,sh) [ok]"
proof -
  from cr have dist: "conf_clinit P sh (f#frs)"
   by(simp add: correct_state_def)
  then have "conf_clinit P sh frs" by(rule conf_clinit_Cons)

  with cr show ?thesis by(cases frs; fastforce simp: correct_state_def)
qed

lemma correct_state_shupd:
assumes cs: "P,\<Phi> |- (xp,h,frs,sh) [ok]" and shC: "sh C = Some(sfs,i)"
 and dist: "distinct (C#clinit_classes frs)"
shows "P,\<Phi> |- (xp,h,frs,sh(C \<mapsto> (sfs, i'))) [ok]"
using assms
proof(cases xp)
  case None with assms show ?thesis
  proof(cases frs)
    case (Cons f' frs')
    let ?sh = "sh(C \<mapsto> (sfs, i'))"

    obtain stk' loc' C' M' pc' ics' where f': "f' = (stk',loc',C',M',pc',ics')" by(cases f')
    with cs Cons None obtain b Ts T mxs mxl\<^sub>0 ins xt ST LT where
         meth: "P \<turnstile> C' sees M',b:Ts\<rightarrow>T = (mxs,mxl\<^sub>0,ins,xt) in C'"
     and ty: "\<Phi> C' M' ! pc' = Some (ST,LT)" and conf: "conf_f P h sh (ST,LT) ins f'"
     and confs: "conf_fs P h sh \<Phi> C' M' (size Ts) T frs'"
     and confc: "conf_clinit P sh frs"
     and h_ok: "P\<turnstile> h\<surd>" and sh_ok: "P,h \<turnstile>\<^sub>s sh \<surd>"
    by(auto simp: correct_state_def)

    from Cons dist have dist': "distinct (C#clinit_classes frs')"
     by(auto simp: distinct_length_2_or_more)

    from shconf_upd_obj[OF sh_ok shconfD[OF sh_ok shC]] have sh_ok': "P,h \<turnstile>\<^sub>s ?sh \<surd>"
      by simp

    from conf f' valid_ics_shupd Cons dist have conf': "conf_f P h ?sh (ST,LT) ins f'"
     by(auto simp: conf_f_def2 fun_upd_apply)
    have confs': "conf_fs P h ?sh \<Phi> C' M' (size Ts) T frs'" by(rule conf_fs_shupd[OF confs dist'])

    have confc': "conf_clinit P ?sh frs" by(rule conf_clinit_shupd[OF confc dist])

    with h_ok sh_ok' meth ty conf' confs' f' Cons None show ?thesis
     by(fastforce simp: correct_state_def)
  qed(simp add: correct_state_def)
qed(simp add: correct_state_def)

lemma correct_state_Throwing_ex:
assumes correct: "P,\<Phi> \<turnstile> (xp,h,(stk,loc,C,M,pc,ics)#frs,sh)\<surd>"
shows "\<And>Cs a. ics = Throwing Cs a \<Longrightarrow> \<exists>obj. h a = Some obj"
using correct by(clarsimp simp: correct_state_def conf_f_def)

end
