
(*  Title:      JinjaDCI/JVM/JVMExec.thy
    Author: Cornelia Pusch, Gerwin Klein, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen, 2019-20

    Based on the Jinja theory JVM/JVMExec.thy by Cornelia Pusch and Gerwin Klein
*)

section \<open> Program Execution in the JVM in full small step style \<close>

theory JVMExec
imports JVMExecInstr
begin

abbreviation
  instrs_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> instr list" where
  "instrs_of P C M == fst(snd(snd(snd(snd(snd(snd(method P C M)))))))"

fun curr_instr :: "jvm_prog \<Rightarrow> frame \<Rightarrow> instr" where
"curr_instr P (stk,loc,C,M,pc,ics) = instrs_of P C M ! pc"

\<comment> \<open> execution of single step of the initialization procedure \<close>
fun exec_Calling :: "[cname, cname list, jvm_prog, heap, val list, val list,
                  cname, mname, pc, frame list, sheap] \<Rightarrow> jvm_state"
where
"exec_Calling C Cs P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
  (case sh C of
        None \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling C Cs)#frs, sh(C := Some (sblank P C, Prepared)))
      | Some (obj, iflag) \<Rightarrow>
          (case iflag of
              Done \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called Cs)#frs, sh)
            | Processing \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called Cs)#frs, sh)
            | Error \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc,
                                   Throwing Cs (addr_of_sys_xcpt NoClassDefFoundError))#frs, sh)
            | Prepared \<Rightarrow>
                let sh' = sh(C:=Some(fst(the(sh C)), Processing));
                    D = fst(the(class P C))
                 in if C = Object
                    then (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called (C#Cs))#frs, sh')
                    else (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D (C#Cs))#frs, sh')
          )
  )"

\<comment> \<open> single step of execution without error handling \<close>
fun exec_step :: "[jvm_prog, heap, val list, val list,
                  cname, mname, pc, init_call_status, frame list, sheap] \<Rightarrow> jvm_state"
where
"exec_step P h stk loc C M pc (Calling C' Cs) frs sh
   = exec_Calling C' Cs P h stk loc C M pc frs sh" |
"exec_step P h stk loc C M pc (Called (C'#Cs)) frs sh
   = (None, h, create_init_frame P C'#(stk, loc, C, M, pc, Called Cs)#frs, sh)" |
"exec_step P h stk loc C M pc (Throwing (C'#Cs) a) frs sh
   = (None, h, (stk,loc,C,M,pc,Throwing Cs a)#frs, sh(C':=Some(fst(the(sh C')), Error)))" |
"exec_step P h stk loc C M pc (Throwing [] a) frs sh
   = (\<lfloor>a\<rfloor>, h, (stk,loc,C,M,pc,No_ics)#frs, sh)" |
"exec_step P h stk loc C M pc ics frs sh
   = exec_instr (instrs_of P C M ! pc) P h stk loc C M pc ics frs sh"

\<comment> \<open> execution including error handling \<close>
fun exec :: "jvm_prog \<times> jvm_state \<Rightarrow> jvm_state option" \<comment> \<open>single step execution\<close> where
"exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) =
   (let (xp', h', frs', sh') = exec_step P h stk loc C M pc ics frs sh
     in case xp' of
            None \<Rightarrow> Some (None,h',frs',sh')
          | Some x \<Rightarrow> Some (find_handler P x h ((stk,loc,C,M,pc,ics)#frs) sh)
   )"
| "exec _ = None"

\<comment> \<open>relational view\<close>
inductive_set
  exec_1 :: "jvm_prog \<Rightarrow> (jvm_state \<times> jvm_state) set"
  and exec_1' :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool" 
    ("_ \<turnstile>/ _ -jvm\<rightarrow>\<^sub>1/ _" [61,61,61] 60)
  for P :: jvm_prog
where
  "P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>' \<equiv> (\<sigma>,\<sigma>') \<in> exec_1 P"
| exec_1I: "exec (P,\<sigma>) = Some \<sigma>' \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>'"

\<comment> \<open>reflexive transitive closure:\<close>
definition exec_all :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool"
    ("(_ \<turnstile>/ _ -jvm\<rightarrow>/ _)" [61,61,61]60) where
  exec_all_def1: "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' \<longleftrightarrow> (\<sigma>,\<sigma>') \<in> (exec_1 P)\<^sup>*"

notation (ASCII)
  exec_all  ("_ |-/ _ -jvm->/ _" [61,61,61]60)


lemma exec_1_eq:
  "exec_1 P = {(\<sigma>,\<sigma>'). exec (P,\<sigma>) = Some \<sigma>'}"
(*<*)by (auto intro: exec_1I elim: exec_1.cases)(*>*)

lemma exec_1_iff:
  "P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>' = (exec (P,\<sigma>) = Some \<sigma>')"
(*<*)by (simp add: exec_1_eq)(*>*)

lemma exec_all_def:
  "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' = ((\<sigma>,\<sigma>') \<in> {(\<sigma>,\<sigma>'). exec (P,\<sigma>) = Some \<sigma>'}\<^sup>*)"
(*<*)by (simp add: exec_all_def1 exec_1_eq)(*>*)

lemma jvm_refl[iff]: "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>"
(*<*)by(simp add: exec_all_def)(*>*)

lemma jvm_trans[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*)by(simp add: exec_all_def)(*>*)

lemma jvm_one_step1[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*) by (simp add: exec_all_def1) (*>*)

lemma jvm_one_step2[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow>\<^sub>1 \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*) by (simp add: exec_all_def1) (*>*)

lemma exec_all_conf:
  "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<or> P \<turnstile> \<sigma>'' -jvm\<rightarrow> \<sigma>'"
(*<*)by(simp add: exec_all_def single_valued_def single_valued_confluent)(*>*)

lemma exec_1_exec_all_conf:
 "\<lbrakk> exec (P, \<sigma>) = Some \<sigma>'; P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''; \<sigma> \<noteq> \<sigma>'' \<rbrakk>
 \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>''"
 by(auto elim: converse_rtranclE simp: exec_1_eq exec_all_def)

lemma exec_all_finalD: "P \<turnstile> (x, h, [], sh) -jvm\<rightarrow> \<sigma> \<Longrightarrow> \<sigma> = (x, h, [], sh)"
(*<*)
proof -
  assume "P \<turnstile> (x, h, [], sh) -jvm\<rightarrow> \<sigma>"
  then have "((x, h, [], sh), \<sigma>) \<in> {(\<sigma>, \<sigma>'). exec (P, \<sigma>) = \<lfloor>\<sigma>'\<rfloor>}\<^sup>*"
    by(simp only: exec_all_def)
  then show ?thesis proof(rule converse_rtranclE) qed simp+
qed
(*>*)

lemma exec_all_deterministic:
  "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> (x,h,[],sh); P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> (x,h,[],sh)"
(*<*)
proof -
  assume assms: "P \<turnstile> \<sigma> -jvm\<rightarrow> (x,h,[],sh)" "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
  show ?thesis using exec_all_conf[OF assms]
    by(blast dest!: exec_all_finalD)
qed
(*>*)

subsection "Preservation of preallocated"

lemma exec_Calling_prealloc_pres:
assumes "preallocated h"
  and "exec_Calling C Cs P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = (xp',h',frs',sh')"
shows "preallocated h'"
using assms
proof(cases "sh C")
  case (Some a)
  then obtain sfs i where sfsi:"a = (sfs, i)" by(cases a)
  then show ?thesis using Some assms
  proof(cases i)
    case Prepared
    then show ?thesis using sfsi Some assms by(cases "method P C clinit", auto split: if_split_asm)
  next
    case Error
    then show ?thesis using sfsi Some assms by(cases "method P C clinit", auto)
  qed(auto)
qed(auto)

lemma exec_step_prealloc_pres:
assumes pre: "preallocated h"
  and "exec_step P h stk loc C M pc ics frs sh = (xp',h',frs',sh')"
shows "preallocated h'"
proof(cases ics)
  case No_ics
  then show ?thesis using exec_instr_prealloc_pres assms by auto
next
  case Calling
  then show ?thesis using exec_Calling_prealloc_pres assms by auto
next
  case (Called Cs)
  then show ?thesis using exec_instr_prealloc_pres assms by(cases Cs, auto)
next
  case (Throwing Cs a)
  then show ?thesis using assms by(cases Cs, auto)
qed

lemma exec_prealloc_pres:
assumes pre: "preallocated h"
  and "exec (P, xp, h, frs, sh) = Some(xp',h',frs',sh')"
shows "preallocated h'"
using assms
proof(cases "\<exists>x. xp = \<lfloor>x\<rfloor> \<or> frs = []")
  case False
  then obtain f1 frs1 where frs: "frs = f1#frs1" by(cases frs, simp+)
  then obtain stk1 loc1 C1 M1 pc1 ics1 where f1: "f1 = (stk1,loc1,C1,M1,pc1,ics1)" by(cases f1)
  let ?i = "instrs_of P C1 M1 ! pc1"
  obtain xp2 h2 frs2 sh2
     where exec_step: "exec_step P h stk1 loc1 C1 M1 pc1 ics1 frs1 sh = (xp2,h2,frs2,sh2)"
    by(cases "exec_step P h stk1 loc1 C1 M1 pc1 ics1 frs1 sh")
  then show ?thesis using exec_step_prealloc_pres[OF pre exec_step] f1 frs False assms
  proof(cases xp2)
    case (Some a)
    show ?thesis
      using find_handler_prealloc_pres[OF pre, where a=a]
            exec_step_prealloc_pres[OF pre]
            exec_step f1 frs Some False assms
       by(auto split: bool.splits init_call_status.splits list.splits)
  qed(auto split: init_call_status.splits)
qed(auto)

subsection "Start state"

text \<open> The @{term Start} class is defined based on a given initial class
 and method. It has two methods: one that calls the initial method in the
 initial class, which is called by the starting program, and @{term clinit},
 as required for the class to be well-formed. \<close>
definition start_method :: "cname \<Rightarrow> mname \<Rightarrow> jvm_method mdecl" where
"start_method C M = (start_m, Static, [], Void, (1,0,[Invokestatic C M 0,Return],[]))"
abbreviation start_clinit :: "jvm_method mdecl" where
"start_clinit \<equiv> (clinit, Static, [], Void, (1,0,[Push Unit,Return],[]))"
definition start_class :: "cname \<Rightarrow> mname \<Rightarrow> jvm_method cdecl" where
"start_class C M = (Start, Object, [], [start_method C M, start_clinit])"

text \<open>
  The start configuration of the JVM in program @{text P}:
  in the start heap, we call the ``start'' method of the
  ``Start''; this method performs @{text Invokestatic} on the
  class and method given to create the start program's @{term Start} class.
  This allows the initialization procedure to be called on the
  initial class in a natural way before the initial method is performed. 
  There is no @{text this} pointer of the frame as @{term start} is @{term Static}.
  The start sheap has every class pre-prepared; this decision is not
  necessary.
  The starting program includes the added @{term Start} class, given a 
  method @{text M} of class @{text C}, added to program @{text P}.
\<close>
definition start_state :: "jvm_prog \<Rightarrow> jvm_state" where
  "start_state P = (None, start_heap P, [([], [], Start, start_m, 0, No_ics)], start_sheap)"
abbreviation start_prog :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> jvm_prog" where
"start_prog P C M \<equiv> start_class C M # P"

end