
(*  Title:      JinjaDCI/JVM/JVMExecInstr.thy
    Author: Cornelia Pusch, Gerwin Klein, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen

    Based on the Jinja theory JVM/JVMExecInstr.thy by Cornelia Pusch and Gerwin Klein
*)

section \<open> Program Execution in the JVM \<close>

theory JVMExecInstr
imports JVMInstructions JVMExceptions
begin

 \<comment> \<open> frame calling the class initialization method for the given class
 in the given program \<close>
fun create_init_frame :: "[jvm_prog, cname] \<Rightarrow> frame" where
"create_init_frame P C =
  (let (D,b,Ts,T,(mxs,mxl\<^sub>0,ins,xt)) = method P C clinit
   in ([],(replicate mxl\<^sub>0 undefined),D,clinit,0,No_ics)
  )"

primrec exec_instr :: "[instr, jvm_prog, heap, val list, val list,
                  cname, mname, pc, init_call_status, frame list, sheap] \<Rightarrow> jvm_state"
where
  exec_instr_Load:
"exec_instr (Load n) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
   (None, h, ((loc ! n) # stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_instr_Store:
"exec_instr (Store n) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
   (None, h, (tl stk, loc[n:=hd stk], C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_instr_Push:
"exec_instr (Push v) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
   (None, h, (v # stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

|  exec_instr_New:
"exec_instr (New C) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
   (case (ics, sh C) of
          (Called Cs, _) \<Rightarrow>
            (case new_Addr h of
                  None \<Rightarrow> (\<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, No_ics)#frs, sh)
                | Some a \<Rightarrow> (None, h(a\<mapsto>blank P C), (Addr a#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, No_ics)#frs, sh)
            )
        | (_, Some(obj, Done)) \<Rightarrow>
            (case new_Addr h of
                  None \<Rightarrow> (\<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
                | Some a \<Rightarrow> (None, h(a\<mapsto>blank P C), (Addr a#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)
            )
        | _ \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling C [])#frs, sh)
   )"

| exec_instr_Getfield:
"exec_instr (Getfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let v      = hd stk;
       (D,fs) = the(h(the_Addr v));
       (D',b,t) = field P C F;
       xp'    = if v=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>
                else if \<not>(\<exists>t b. P \<turnstile> D has F,b:t in C)
                     then \<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>
                     else case b of Static \<Rightarrow> \<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>
                                  | NonStatic \<Rightarrow> None
   in case xp' of None \<Rightarrow> (xp', h, (the(fs(F,C))#(tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1, ics)#frs, sh)
                | Some x \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh))"

| exec_instr_Getstatic:
"exec_instr (Getstatic C F D) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let (D',b,t) = field P D F;
       xp'    = if \<not>(\<exists>t b. P \<turnstile> C has F,b:t in D)
                then \<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>
                else case b of NonStatic \<Rightarrow> \<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>
                             | Static \<Rightarrow> None
   in (case (xp', ics, sh D') of
            (Some a, _) \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
          | (_, Called Cs, _) \<Rightarrow> let (sfs, i) = the(sh D');
                                       v = the(sfs F)
                                    in (xp', h, (v#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, No_ics)#frs, sh)
          | (_, _, Some (sfs, Done)) \<Rightarrow> let v = the (sfs F)
                                        in (xp', h, (v#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)
          | _ \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D' [])#frs, sh)
      )
  )"

| exec_instr_Putfield:
"exec_instr (Putfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let v    = hd stk;
       r    = hd (tl stk);
       a    = the_Addr r;
       (D,fs) = the (h a);
       (D',b,t) = field P C F;
       xp'    = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>
                else if \<not>(\<exists>t b. P \<turnstile> D has F,b:t in C)
                     then \<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>
                     else case b of Static \<Rightarrow> \<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>
                                  | NonStatic \<Rightarrow> None;
       h'  = h(a \<mapsto> (D, fs((F,C) \<mapsto> v)))
   in case xp' of None \<Rightarrow> (xp', h', (tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1, ics)#frs, sh)
                | Some x \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
  )"

| exec_instr_Putstatic:
"exec_instr (Putstatic C F D) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let (D',b,t) = field P D F;
       xp'    = if \<not>(\<exists>t b. P \<turnstile> C has F,b:t in D)
                then \<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>
                else case b of NonStatic \<Rightarrow> \<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>
                             | Static \<Rightarrow> None
   in (case (xp', ics, sh D') of
            (Some a, _) \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
          | (_, Called Cs, _)
       \<Rightarrow> let (sfs, i) = the(sh D')
          in (xp', h, (tl stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, No_ics)#frs, sh(D':=Some ((sfs(F \<mapsto> hd stk)), i)))
          | (_, _, Some (sfs, Done))
       \<Rightarrow> (xp', h, (tl stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh(D':=Some ((sfs(F \<mapsto> hd stk)), Done)))
          | _ \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D' [])#frs, sh)
      )
  )"

| exec_instr_Checkcast:
"exec_instr (Checkcast C) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
   (if cast_ok P C h (hd stk)
     then (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)
     else (\<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
   )"

| exec_instr_Invoke:
"exec_instr (Invoke M n) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let ps  = take n stk;
       r   = stk!n;
       C   = fst(the(h(the_Addr r)));
       (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt)= method P C M;
       xp' = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>
             else if \<not>(\<exists>Ts T m D b. P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D)
                  then \<lfloor>addr_of_sys_xcpt NoSuchMethodError\<rfloor>
                  else case b of Static \<Rightarrow> \<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>
                               | NonStatic \<Rightarrow> None;
       f'  = ([],[r]@(rev ps)@(replicate mxl\<^sub>0 undefined),D,M,0,No_ics)
   in case xp' of None \<Rightarrow> (xp', h, f'#(stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
                | Some a \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
  )"

| exec_instr_Invokestatic:
"exec_instr (Invokestatic C M n) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let ps  = take n stk;
       (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt)= method P C M;
       xp' = if \<not>(\<exists>Ts T m D b. P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D)
             then \<lfloor>addr_of_sys_xcpt NoSuchMethodError\<rfloor>
             else case b of NonStatic \<Rightarrow> \<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>
                          | Static \<Rightarrow> None;
       f'  = ([],(rev ps)@(replicate mxl\<^sub>0 undefined),D,M,0,No_ics)
   in (case (xp', ics, sh D) of
            (Some a, _) \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
          | (_, Called Cs, _) \<Rightarrow> (xp', h, f'#(stk, loc, C\<^sub>0, M\<^sub>0, pc, No_ics)#frs, sh)
          | (_, _, Some (sfs, Done)) \<Rightarrow> (xp', h, f'#(stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)
          | _ \<Rightarrow> (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D [])#frs, sh)
      )
  )"

| exec_instr_Return:
 "exec_instr Return P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc ics frs sh =
    (case frs of
         [] \<Rightarrow> let sh' =  (case M\<^sub>0 = clinit of True \<Rightarrow> sh(C\<^sub>0:=Some(fst(the(sh C\<^sub>0)), Done))
                                             | _ \<Rightarrow> sh
                           )
                in (None, h, [], sh')
       | (stk',loc',C',m',pc',ics')#frs'
            \<Rightarrow> let (D,b,Ts,T,(mxs,mxl\<^sub>0,ins,xt)) = method P C\<^sub>0 M\<^sub>0;
                   offset = case b of NonStatic \<Rightarrow> 1 | Static \<Rightarrow> 0;
                   (sh'', stk'', pc'') = (case M\<^sub>0 = clinit of True \<Rightarrow> (sh(C\<^sub>0:=Some(fst(the(sh C\<^sub>0)), Done)), stk', pc')
                                                | _ \<Rightarrow> (sh, (hd stk\<^sub>0)#(drop (length Ts + offset) stk'), Suc pc')
                                        )
               in (None, h, (stk'',loc',C',m',pc'',ics')#frs', sh'')
    )"

| exec_instr_Pop:
"exec_instr Pop P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh = (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_instr_IAdd:
"exec_instr IAdd P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
    (None, h, (Intg (the_Intg (hd (tl stk)) + the_Intg (hd stk))#(tl (tl stk)), loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_instr_IfFalse:
"exec_instr (IfFalse i) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let pc' = if hd stk = Bool False then nat(int pc+i) else pc+1
   in (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, pc', ics)#frs, sh))"

| exec_instr_CmpEq:
"exec_instr CmpEq P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
    (None, h, (Bool (hd (tl stk) = hd stk) # tl (tl stk), loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_instr_Goto:
"exec_instr (Goto i) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
   (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, nat(int pc+i), ics)#frs, sh)"

| exec_instr_Throw:
"exec_instr Throw P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh =
  (let xp' = if hd stk = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>
             else \<lfloor>the_Addr(hd stk)\<rfloor>
   in (xp', h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh))"



text "Given a preallocated heap, a thrown exception is either a system exception or
   thrown directly by @{term Throw}."
lemma exec_instr_xcpts:
assumes "\<sigma>' = exec_instr i P h stk loc C M pc ics' frs sh"
  and "fst \<sigma>' = Some a"
shows "i = (JVMInstructions.Throw) \<or> a \<in> {a. \<exists>x \<in> sys_xcpts. a = addr_of_sys_xcpt x}"
using assms
proof(cases i)
  case (New C1) then show ?thesis using assms
  proof(cases "sh C1")
    case (Some a)
    then obtain sfs i where sfsi: "a = (sfs,i)" by(cases a)
    then show ?thesis using Some New assms
    proof(cases i) qed(cases ics', auto)+
  qed(cases ics', auto)
next
  case (Getfield F1 C1)
  obtain D' b t where field: "field P C1 F1 = (D',b,t)" by(cases "field P C1 F1")
  obtain D fs where addr: "the (h (the_Addr (hd stk))) = (D,fs)" by(cases "the (h (the_Addr (hd stk)))")
  show ?thesis using addr field Getfield assms
  proof(cases "hd stk = Null")
    case nNull:False then show ?thesis using addr field Getfield assms
    proof(cases "\<nexists>t b. P \<turnstile> (cname_of h (the_Addr (hd stk))) has F1,b:t in C1")
      case exists:False show ?thesis
      proof(cases "fst(snd(field P C1 F1))")
        case Static
        then show ?thesis using exists nNull addr field Getfield assms
         by(auto simp: sys_xcpts_def split_beta split: staticb.splits)
      next
        case NonStatic
        then show ?thesis using exists nNull addr field Getfield assms
         by(auto simp: sys_xcpts_def split_beta split: staticb.splits)
      qed
    qed(auto)
  qed(auto)
next
  case (Getstatic C1 F1 D1)
  obtain D' b t where field: "field P D1 F1 = (D',b,t)" by(cases "field P D1 F1")
  show ?thesis using field Getstatic assms
  proof(cases "\<nexists>t b. P \<turnstile> C1 has F1,b:t in D1")
    case exists:False then show ?thesis using field Getstatic assms
    proof(cases "fst(snd(field P D1 F1))")
      case Static
      then obtain sfs i where "the(sh D') = (sfs, i)" by(cases "the(sh D')")
      then show ?thesis using exists field Static Getstatic assms by(cases ics'; cases i, auto)
    qed(auto)
  qed(auto)
next
  case (Putfield F1 C1)
  let ?r = "hd(tl stk)"
  obtain D' b t where field: "field P C1 F1 = (D',b,t)" by(cases "field P C1 F1")
  obtain D fs where addr: "the (h (the_Addr ?r)) = (D,fs)"
    by(cases "the (h (the_Addr ?r))")
  show ?thesis using addr field Putfield assms
  proof(cases "?r = Null")
    case nNull:False then show ?thesis using addr field Putfield assms
    proof(cases "\<nexists>t b. P \<turnstile> (cname_of h (the_Addr ?r)) has F1,b:t in C1")
      case exists:False show ?thesis
      proof(cases b)
        case Static
        then show ?thesis using exists nNull addr field Putfield assms
         by(auto simp: sys_xcpts_def split_beta split: staticb.splits)
      next
        case NonStatic
        then show ?thesis using exists nNull addr field Putfield assms
         by(auto simp: sys_xcpts_def split_beta split: staticb.splits)
      qed
    qed(auto)
  qed(auto)
next
  case (Putstatic C1 F1 D1)
  obtain D' b t where field: "field P D1 F1 = (D',b,t)" by(cases "field P D1 F1")
  show ?thesis using field Putstatic assms
  proof(cases "\<nexists>t b. P \<turnstile> C1 has F1,b:t in D1")
    case exists:False then show ?thesis using field Putstatic assms
    proof(cases b)
      case Static
      then obtain sfs i where "the(sh D') = (sfs, i)" by(cases "the(sh D')")
      then show ?thesis using exists field Static Putstatic assms by(cases ics'; cases i, auto)
    qed(auto)
  qed(auto)
next
  case (Checkcast C1) then show ?thesis using assms by(cases "cast_ok P C1 h (hd stk)", auto)
next
  case (Invoke M n)
  let ?r = "stk!n"
  let ?C = "cname_of h (the_Addr ?r)"
  show ?thesis using Invoke assms
  proof(cases "?r = Null")
    case nNull:False then show ?thesis using Invoke assms
    proof(cases "\<not>(\<exists>Ts T m D b. P \<turnstile> ?C sees M,b:Ts \<rightarrow> T = m in D)")
      case exists:False then show ?thesis using nNull Invoke assms
      proof(cases "fst(snd(method P ?C M))")
        case Static
        then show ?thesis using exists nNull Invoke assms
         by(auto simp: sys_xcpts_def split_beta split: staticb.splits)
      next
        case NonStatic
        then show ?thesis using exists nNull Invoke assms
         by(auto simp: sys_xcpts_def split_beta split: staticb.splits)
      qed
    qed(auto)
  qed(auto)
next
  case (Invokestatic C1 M n)
  show ?thesis using Invokestatic assms
  proof(cases "\<not>(\<exists>Ts T m D b. P \<turnstile> C1 sees M,b:Ts \<rightarrow> T = m in D)")
    case exists:False then show ?thesis using Invokestatic assms
    proof(cases "fst(snd(method P C1 M))")
      case Static
      then obtain sfs i where "the(sh (fst(method P C1 M))) = (sfs, i)"
        by(cases "the(sh (fst(method P C1 M)))")
      then show ?thesis using exists Static Invokestatic assms
        by(auto split: init_call_status.splits init_state.splits)
    qed(auto)
  qed(auto)
next
  case Return then show ?thesis using assms
  proof(cases frs)
    case (Cons f frs') then show ?thesis using Return assms
      by(cases f, cases "method P C M", cases "M=clinit", auto)
  qed(auto)
next
  case (IfFalse x17) then show ?thesis using assms
  proof(cases "hd stk")
    case (Bool b) then show ?thesis using IfFalse assms by(cases b, auto)
  qed(auto)
qed(auto)

lemma exec_instr_prealloc_pres:
assumes "preallocated h"
  and "exec_instr i P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh = (xp',h',frs',sh')"
shows "preallocated h'"
using assms
proof(cases i)
  case (New C1)
  then obtain sfs i where sfsi: "the(sh C1) = (sfs,i)" by(cases "the(sh C1)")
  then show ?thesis using preallocated_new[of h] New assms
    by(cases "blank P C1", auto dest: new_Addr_SomeD split: init_call_status.splits init_state.splits)
next
  case (Getfield F1 C1) then show ?thesis using assms
    by(cases "the (h (the_Addr (hd stk)))", cases "field P C1 F1", auto)
next
  case (Getstatic C1 F1 D1)
  then obtain sfs i where sfsi: "the(sh (fst (field P D1 F1))) = (sfs, i)"
   by(cases "the(sh (fst (field P D1 F1)))")
  then show ?thesis using Getstatic assms
   by(cases "field P D1 F1", auto split: init_call_status.splits init_state.splits)
next
  case (Putfield F1 C1) then show ?thesis using preallocated_new preallocated_upd_obj assms
    by(cases "the (h (the_Addr (hd (tl stk))))", cases "field P C1 F1", auto, metis option.collapse)
next
  case (Putstatic C1 F1 D1)
  then obtain sfs i where sfsi: "the(sh (fst (field P D1 F1))) = (sfs, i)"
   by(cases "the(sh (fst (field P D1 F1)))")
  then show ?thesis using Putstatic assms
   by(cases "field P D1 F1", auto split: init_call_status.splits init_state.splits)
next
  case (Checkcast C1)
  then show ?thesis using assms
  proof(cases "hd stk = Null")
    case False then show ?thesis
     using Checkcast assms
       by(cases "P \<turnstile> cname_of h (the_Addr (hd stk)) \<preceq>\<^sup>* C1", auto simp: cast_ok_def)
  qed(simp add: cast_ok_def)
next
  case (Invoke M n)
  then show ?thesis using assms by(cases "method P (cname_of h (the_Addr (stk ! n))) M", auto)
next
  case (Invokestatic C1 M n)
  show ?thesis
  proof(cases "sh (fst (method P C1 M))")
    case None then show ?thesis using Invokestatic assms
     by(cases "method P C1 M", auto split: init_call_status.splits)
  next
    case (Some a)
    then obtain sfs i where sfsi: "a = (sfs, i)" by(cases a)
    then show ?thesis using Some Invokestatic assms
    proof(cases i) qed(cases "method P C1 M", auto split: init_call_status.splits)+
  qed
next
  case Return
  then show ?thesis using assms by(cases "method P C\<^sub>0 M\<^sub>0", auto simp: split_beta split: list.splits)
next
  case (IfFalse x17) then show ?thesis using assms by(auto split: val.splits bool.splits)
next
  case Throw then show ?thesis using assms by(auto split: val.splits)
qed(auto)

end
