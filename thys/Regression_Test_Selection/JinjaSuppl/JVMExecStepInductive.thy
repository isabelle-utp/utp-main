(*  Title:      RTS/JinjaSuppl/JVMExecStepInductive.thy
    Author:     Susannah Mansky
    2020, UIUC

    Program Execution in the JVM as an inductive
*)

section "Inductive JVM execution"

theory JVMExecStepInductive
imports JinjaDCI.JVMExec
begin

datatype step_input = StepI instr |
                      StepC cname "cname list" | StepC2 cname "cname list" |
                      StepT "cname list" addr


inductive exec_step_ind :: "[step_input, jvm_prog, heap, val list, val list,
                  cname, mname, pc, init_call_status, frame list, sheap,jvm_state] \<Rightarrow> bool"
where
  exec_step_ind_Load:
"exec_step_ind (StepI (Load n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (None, h, ((loc ! n) # stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_Store:
"exec_step_ind (StepI (Store n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (None, h, (tl stk, loc[n:=hd stk], C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_Push:
"exec_step_ind (StepI (Push v)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (None, h, (v # stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

|  exec_step_ind_NewOOM_Called:
"new_Addr h = None
  \<Longrightarrow> exec_step_ind (StepI (New C)) P h stk loc C\<^sub>0 M\<^sub>0 pc (Called Cs) frs sh
   (\<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, No_ics)#frs, sh)"

|  exec_step_ind_NewOOM_Done:
"\<lbrakk> sh C = Some(obj, Done); new_Addr h = None; \<forall>Cs. ics \<noteq> Called Cs \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (New C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (\<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

|  exec_step_ind_New_Called:
"new_Addr h = Some a
  \<Longrightarrow> exec_step_ind (StepI (New C)) P h stk loc C\<^sub>0 M\<^sub>0 pc (Called Cs) frs sh
   (None, h(a\<mapsto>blank P C), (Addr a#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, No_ics)#frs, sh)"

|  exec_step_ind_New_Done:
"\<lbrakk> sh C = Some(obj, Done); new_Addr h = Some a; \<forall>Cs. ics \<noteq> Called Cs \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (New C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (None, h(a\<mapsto>blank P C), (Addr a#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

|  exec_step_ind_New_Init:
"\<lbrakk> \<forall>obj. sh C \<noteq> Some(obj, Done); \<forall>Cs. ics \<noteq> Called Cs \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (New C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling C [])#frs, sh)"

| exec_step_ind_Getfield_Null:
"hd stk = Null
  \<Longrightarrow> exec_step_ind (StepI (Getfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Getfield_NoField:
"\<lbrakk> v = hd stk; (D,fs) = the(h(the_Addr v)); v \<noteq> Null; \<not>(\<exists>t b. P \<turnstile> D has F,b:t in C) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Getfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (\<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Getfield_Static:
"\<lbrakk> v = hd stk; (D,fs) = the(h(the_Addr v)); v \<noteq> Null; P \<turnstile> D has F,Static:t in C \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Getfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (\<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Getfield:
"\<lbrakk> v = hd stk; (D,fs) = the(h(the_Addr v)); (D',b,t) = field P C F; v \<noteq> Null;
   P \<turnstile> D has F,NonStatic:t in C \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Getfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (None, h, (the(fs(F,C))#(tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1, ics)#frs, sh)"

| exec_step_ind_Getstatic_NoField:
"\<not>(\<exists>t b. P \<turnstile> C has F,b:t in D)
  \<Longrightarrow> exec_step_ind (StepI (Getstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Getstatic_NonStatic:
"P \<turnstile> C has F,NonStatic:t in D
  \<Longrightarrow> exec_step_ind (StepI (Getstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Getstatic_Called:
"\<lbrakk> (D',b,t) = field P D F; P \<turnstile> C has F,Static:t in D;
   v = the ((fst(the(sh D'))) F) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Getstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc (Called Cs) frs sh
    (None, h, (v#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, No_ics)#frs, sh)"

| exec_step_ind_Getstatic_Done:
"\<lbrakk> (D',b,t) = field P D F; P \<turnstile> C has F,Static:t in D;
   \<forall>Cs. ics \<noteq> Called Cs; sh D' = Some(sfs,Done);
   v = the (sfs F) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Getstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (v#stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_Getstatic_Init:
"\<lbrakk> (D',b,t) = field P D F; P \<turnstile> C has F,Static:t in D;
   \<forall>sfs. sh D' \<noteq> Some(sfs,Done); \<forall>Cs. ics \<noteq> Called Cs \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Getstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D' [])#frs, sh)"

| exec_step_ind_Putfield_Null:
"hd(tl stk) = Null
  \<Longrightarrow> exec_step_ind (StepI (Putfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
  (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Putfield_NoField:
"\<lbrakk> r = hd(tl stk); a = the_Addr r; (D,fs) = the (h a); r \<noteq> Null; \<not>(\<exists>t b. P \<turnstile> D has F,b:t in C) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Putfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
  (\<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Putfield_Static:
"\<lbrakk> r = hd(tl stk); a = the_Addr r; (D,fs) = the (h a); r \<noteq> Null; P \<turnstile> D has F,Static:t in C \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Putfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
  (\<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Putfield:
"\<lbrakk> v = hd stk; r = hd(tl stk); a = the_Addr r; (D,fs) = the (h a); (D',b,t) = field P C F;
   r \<noteq> Null; P \<turnstile> D has F,NonStatic:t in C \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Putfield F C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
  (None, h(a \<mapsto> (D, fs((F,C) \<mapsto> v))), (tl (tl stk), loc, C\<^sub>0, M\<^sub>0, pc+1, ics)#frs, sh)"

| exec_step_ind_Putstatic_NoField:
"\<not>(\<exists>t b. P \<turnstile> C has F,b:t in D)
  \<Longrightarrow> exec_step_ind (StepI (Putstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt NoSuchFieldError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Putstatic_NonStatic:
"P \<turnstile> C has F,NonStatic:t in D
  \<Longrightarrow> exec_step_ind (StepI (Putstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Putstatic_Called:
"\<lbrakk> (D',b,t) = field P D F; P \<turnstile> C has F,Static:t in D; the(sh D') = (sfs,i) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Putstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc (Called Cs) frs sh
    (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, No_ics)#frs, sh(D':=Some ((sfs(F \<mapsto> hd stk)), i)))"

| exec_step_ind_Putstatic_Done:
"\<lbrakk> (D',b,t) = field P D F; P \<turnstile> C has F,Static:t in D;
   \<forall>Cs. ics \<noteq> Called Cs; sh D' = Some (sfs, Done) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Putstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh(D':=Some ((sfs(F \<mapsto> hd stk)), Done)))"

| exec_step_ind_Putstatic_Init:
"\<lbrakk> (D',b,t) = field P D F; P \<turnstile> C has F,Static:t in D;
   \<forall>sfs. sh D' \<noteq> Some (sfs, Done); \<forall>Cs. ics \<noteq> Called Cs \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Putstatic C F D)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D' [])#frs, sh)"

| exec_step_ind_Checkcast:
"cast_ok P C h (hd stk)
  \<Longrightarrow> exec_step_ind (StepI (Checkcast C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_Checkcast_Error:
"\<not>cast_ok P C h (hd stk)
  \<Longrightarrow> exec_step_ind (StepI (Checkcast C)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invoke_Null:
"stk!n = Null
  \<Longrightarrow> exec_step_ind (StepI (Invoke M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invoke_NoMethod:
"\<lbrakk> r = stk!n; C = fst(the(h(the_Addr r))); r \<noteq> Null;
   \<not>(\<exists>Ts T m D b. P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invoke M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt NoSuchMethodError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invoke_Static:
"\<lbrakk> r = stk!n; C = fst(the(h(the_Addr r)));
   (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt)= method P C M; r \<noteq> Null;
   P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invoke M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invoke:
"\<lbrakk> ps = take n stk; r = stk!n; C = fst(the(h(the_Addr r)));
   (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt)= method P C M; r \<noteq> Null;
   P \<turnstile> C sees M,NonStatic:Ts \<rightarrow> T = m in D;
   f' = ([],[r]@(rev ps)@(replicate mxl\<^sub>0 undefined),D,M,0,No_ics) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invoke M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, f'#(stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invokestatic_NoMethod:
"\<lbrakk> (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt)= method P C M; \<not>(\<exists>Ts T m D b. P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invokestatic C M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt NoSuchMethodError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invokestatic_NonStatic:
"\<lbrakk> (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt)= method P C M; P \<turnstile> C sees M,NonStatic:Ts \<rightarrow> T = m in D \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invokestatic C M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt IncompatibleClassChangeError\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invokestatic_Called:
"\<lbrakk> ps  = take n stk; (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt) = method P C M;
   P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D;
   f'  = ([],(rev ps)@(replicate mxl\<^sub>0 undefined),D,M,0,No_ics) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invokestatic C M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc (Called Cs) frs sh
    (None, h, f'#(stk, loc, C\<^sub>0, M\<^sub>0, pc, No_ics)#frs, sh)"

| exec_step_ind_Invokestatic_Done:
"\<lbrakk> ps  = take n stk; (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt) = method P C M;
   P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D;
   \<forall>Cs. ics \<noteq> Called Cs; sh D = Some (sfs, Done);
   f'  = ([],(rev ps)@(replicate mxl\<^sub>0 undefined),D,M,0,No_ics) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invokestatic C M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, f'#(stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Invokestatic_Init:
"\<lbrakk> (D,b,Ts,T,mxs,mxl\<^sub>0,ins,xt) = method P C M;
   P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D;
   \<forall>sfs. sh D \<noteq> Some (sfs, Done); \<forall>Cs. ics \<noteq> Called Cs \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepI (Invokestatic C M n)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D [])#frs, sh)"

| exec_step_ind_Return_Last_Init:
 "exec_step_ind (StepI Return) P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 clinit pc ics [] sh
    (None, h, [], sh(C\<^sub>0:=Some(fst(the(sh C\<^sub>0)), Done)))"

| exec_step_ind_Return_Last:
 "M\<^sub>0 \<noteq> clinit
   \<Longrightarrow> exec_step_ind (StepI Return) P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc ics [] sh (None, h, [], sh)"

| exec_step_ind_Return_Init:
 "\<lbrakk> (D,b,Ts,T,m) = method P C\<^sub>0 clinit \<rbrakk>
   \<Longrightarrow> exec_step_ind (StepI Return) P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 clinit pc ics ((stk',loc',C',m',pc',ics')#frs') sh
     (None, h, (stk',loc',C',m',pc',ics')#frs', sh(C\<^sub>0:=Some(fst(the(sh C\<^sub>0)), Done)))"

| exec_step_ind_Return_NonStatic:
 "\<lbrakk> (D,NonStatic,Ts,T,m) = method P C\<^sub>0 M\<^sub>0; M\<^sub>0 \<noteq> clinit \<rbrakk>
   \<Longrightarrow> exec_step_ind (StepI Return) P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc ics ((stk',loc',C',m',pc',ics')#frs') sh
     (None, h, ((hd stk\<^sub>0)#(drop (length Ts + 1) stk'),loc',C',m',Suc pc',ics')#frs', sh)"

| exec_step_ind_Return_Static:
 "\<lbrakk> (D,Static,Ts,T,m) = method P C\<^sub>0 M\<^sub>0; M\<^sub>0 \<noteq> clinit \<rbrakk>
   \<Longrightarrow> exec_step_ind (StepI Return) P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 M\<^sub>0 pc ics ((stk',loc',C',m',pc',ics')#frs') sh
     (None, h, ((hd stk\<^sub>0)#(drop (length Ts) stk'),loc',C',m',Suc pc',ics')#frs', sh)"

| exec_step_ind_Pop:
"exec_step_ind (StepI Pop) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
  (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_IAdd:
"exec_step_ind (StepI IAdd) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
  (None, h, (Intg (the_Intg (hd (tl stk)) + the_Intg (hd stk))#(tl (tl stk)), loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_IfFalse_False:
"hd stk = Bool False
  \<Longrightarrow> exec_step_ind (StepI (IfFalse i)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, nat(int pc+i), ics)#frs, sh)"

| exec_step_ind_IfFalse_nFalse:
"hd stk \<noteq> Bool False
  \<Longrightarrow> exec_step_ind (StepI (IfFalse i)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (tl stk, loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_CmpEq:
"exec_step_ind (StepI CmpEq) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (Bool (hd (tl stk) = hd stk) # tl (tl stk), loc, C\<^sub>0, M\<^sub>0, Suc pc, ics)#frs, sh)"

| exec_step_ind_Goto:
"exec_step_ind (StepI (Goto i)) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
   (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, nat(int pc+i), ics)#frs, sh)"

| exec_step_ind_Throw:
"hd stk \<noteq> Null
  \<Longrightarrow> exec_step_ind (StepI Throw) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>the_Addr (hd stk)\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Throw_Null:
"hd stk = Null
  \<Longrightarrow> exec_step_ind (StepI Throw) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, ics)#frs, sh)"

| exec_step_ind_Init_None_Called:
"\<lbrakk> sh C = None \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepC C Cs) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling C Cs)#frs, sh(C := Some (sblank P C, Prepared)))"

| exec_step_ind_Init_Done:
"sh C = Some (sfs, Done)
  \<Longrightarrow> exec_step_ind (StepC C Cs) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called Cs)#frs, sh)"

| exec_step_ind_Init_Processing:
"sh C = Some (sfs, Processing)
  \<Longrightarrow> exec_step_ind (StepC C Cs) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called Cs)#frs, sh)"

| exec_step_ind_Init_Error:
"\<lbrakk> sh C = Some (sfs, Error) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepC C Cs) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Throwing Cs (addr_of_sys_xcpt NoClassDefFoundError))#frs, sh)"

| exec_step_ind_Init_Prepared_Object:
"\<lbrakk> sh C = Some (sfs, Prepared);
   sh' = sh(C:=Some(fst(the(sh C)), Processing));
   C = Object \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepC C Cs) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called (C#Cs))#frs, sh')"

| exec_step_ind_Init_Prepared_nObject:
"\<lbrakk> sh C = Some (sfs, Prepared);
   sh' = sh(C:=Some(fst(the(sh C)), Processing));
   C \<noteq> Object; D = fst(the(class P C)) \<rbrakk>
  \<Longrightarrow> exec_step_ind (StepC C Cs) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D (C#Cs))#frs, sh')"

| exec_step_ind_Init:
"exec_step_ind (StepC2 C Cs) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, create_init_frame P C#(stk, loc, C\<^sub>0, M\<^sub>0, pc, Called Cs)#frs, sh)"

| exec_step_ind_InitThrow:
"exec_step_ind (StepT (C#Cs) a) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (None, h, (stk,loc,C\<^sub>0,M\<^sub>0,pc,Throwing Cs a)#frs, (sh(C \<mapsto> (fst(the(sh C)), Error))))"

| exec_step_ind_InitThrow_End:
"exec_step_ind (StepT [] a) P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh
    (\<lfloor>a\<rfloor>, h, (stk,loc,C\<^sub>0,M\<^sub>0,pc,No_ics)#frs, sh)"

(** ******* **)

inductive_cases exec_step_ind_cases [cases set]:
 "exec_step_ind (StepI (Load n)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Store n)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Push v)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (New C)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Getfield F C)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Getstatic C F D)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Putfield F C)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Putstatic C F D)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Checkcast C)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Invoke M n)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Invokestatic C M n)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI Return) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI Pop) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI IAdd) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (IfFalse i)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI CmpEq) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI (Goto i)) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepI Throw) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepC C' Cs) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepC2 C' Cs) P h stk loc C M pc ics frs sh \<sigma>"
 "exec_step_ind (StepT Cs a) P h stk loc C M pc ics frs sh \<sigma>"


\<comment> \<open> Deriving @{term step_input} for @{term exec_step_ind} from @{term exec_step} arguments \<close>
fun exec_step_input :: "[jvm_prog, cname, mname, pc, init_call_status] \<Rightarrow> step_input" where
"exec_step_input P C M pc (Calling C' Cs) = StepC C' Cs" |
"exec_step_input P C M pc (Called (C'#Cs)) = StepC2 C' Cs" |
"exec_step_input P C M pc (Throwing Cs a) = StepT Cs a" |
"exec_step_input P C M pc ics = StepI (instrs_of P C M ! pc)"

lemma exec_step_input_StepTD[simp]:
assumes "exec_step_input P C M pc ics = StepT Cs a" shows "ics = Throwing Cs a"
using assms proof(cases ics)
  case (Called Cs) with assms show ?thesis by(cases Cs; simp)
qed(auto)

lemma exec_step_input_StepCD[simp]:
assumes "exec_step_input P C M pc ics = StepC C' Cs" shows "ics = Calling C' Cs"
using assms proof(cases ics)
  case (Called Cs) with assms show ?thesis by(cases Cs; simp)
qed(auto)

lemma exec_step_input_StepC2D[simp]:
assumes "exec_step_input P C M pc ics = StepC2 C' Cs" shows "ics = Called (C'#Cs)"
using assms proof(cases ics)
  case (Called Cs) with assms show ?thesis by(cases Cs; simp)
qed(auto)

lemma exec_step_input_StepID:
assumes "exec_step_input P C M pc ics = StepI i"
shows "(ics = Called [] \<or> ics = No_ics) \<and> instrs_of P C M ! pc = i"
using assms proof(cases ics)
  case (Called Cs) with assms show ?thesis by(cases Cs; simp)
qed(auto)

subsection "Equivalence of @{term exec_step} and @{term exec_step_input}"

lemma exec_step_imp_exec_step_ind:
assumes es: "exec_step P h stk loc C M pc ics frs sh = (xp', h', frs', sh')"
shows "exec_step_ind (exec_step_input P C M pc ics) P h stk loc C M pc ics frs sh (xp', h', frs', sh')"
proof(cases "exec_step_input P C M pc ics")
  case (StepT Cs a)
  then have "ics = Throwing Cs a" by simp
  then show ?thesis using exec_step_ind_InitThrow exec_step_ind_InitThrow_End StepT es
   by(cases Cs, auto)
next
  case (StepC C1 Cs)
  then have ics: "ics = Calling C1 Cs" by simp
  obtain D b Ts T m where lets: "method P C1 clinit = (D,b,Ts,T,m)" by(cases "method P C1 clinit")
  then obtain mxs mxl\<^sub>0 ins xt where m: "m = (mxs,mxl\<^sub>0,ins,xt)" by(cases m)
  show ?thesis
  proof(cases "sh C1")
    case None then show ?thesis
     using exec_step_ind_Init_None_Called ics assms by auto
  next
    case (Some a)
    then obtain sfs i where sfsi: "a = (sfs,i)" by(cases a)
    then show ?thesis using exec_step_ind_Init_Done exec_step_ind_Init_Processing
      exec_step_ind_Init_Error m lets Some ics assms
    proof(cases i)
      case Prepared
      show ?thesis
      using exec_step_ind_Init_Prepared_Object[where P=P] exec_step_ind_Init_Prepared_nObject
       sfsi m lets Prepared Some ics assms by(auto split: if_split_asm)
    qed(auto)
  qed
next
  case (StepC2 C1 Cs)
  then have ics: "ics = Called (C1#Cs)" by simp
  then show ?thesis using exec_step_ind_Init assms by auto
next
  case (StepI i)
  then have
    ics: "ics = Called [] \<or> ics = No_ics" and
    exec_instr: "exec_instr i P h stk loc C M pc ics frs sh = (xp', h', frs', sh')"
    using assms by(auto dest!: exec_step_input_StepID)
  show ?thesis
  proof(cases i)
    case (Load x1) then show ?thesis using exec_instr exec_step_ind_Load StepI by auto
  next
    case (Store x2) then show ?thesis using exec_instr exec_step_ind_Store StepI by auto
  next
    case (Push x3) then show ?thesis using exec_instr exec_step_ind_Push StepI by auto
  next
    case (New C1)
    then obtain sfs i where sfsi: "the(sh C1) = (sfs,i)" by(cases "the(sh C1)")
    then show ?thesis using exec_step_ind_New_Called exec_step_ind_NewOOM_Called
       exec_step_ind_New_Done exec_step_ind_NewOOM_Done
       exec_step_ind_New_Init sfsi New StepI exec_instr ics by(auto split: init_state.splits)
  next
    case (Getfield F1 C1)
    then obtain D fs D' b t where lets: "the(h(the_Addr (hd stk))) = (D,fs)"
      "field P C1 F1 = (D',b,t)" by(cases "the(h(the_Addr (hd stk)))", cases "field P C1 F1")
    then have "\<And>b' t'. P \<turnstile> D has F1,b':t' in C1 \<Longrightarrow> (D', b, t) = (C1, b', t')"
      using field_def2 has_field_idemp has_field_sees by fastforce
    then show ?thesis using exec_step_ind_Getfield_Null exec_step_ind_Getfield_NoField
       exec_step_ind_Getfield_Static exec_step_ind_Getfield lets Getfield StepI exec_instr
      by(auto split: if_split_asm staticb.splits) metis+
  next
    case (Getstatic C1 F1 D1)
    then obtain D' b t where lets: "field P D1 F1 = (D',b,t)" by(cases "field P D1 F1")
    then have field: "\<And>b' t'. P \<turnstile> C1 has F1,b':t' in D1 \<Longrightarrow> (D', b, t) = (D1, b', t')"
      using field_def2 has_field_idemp has_field_sees by fastforce
    show ?thesis
    proof(cases b)
      case NonStatic then show ?thesis
       using exec_step_ind_Getstatic_NoField exec_step_ind_Getstatic_NonStatic
        field lets Getstatic exec_instr StepI by(auto split: if_split_asm) fastforce
    next
      case Static show ?thesis
      proof(cases "ics = Called []")
        case True then show ?thesis using exec_step_ind_Getstatic_NoField
          exec_step_ind_Getstatic_Called exec_step_ind_Getstatic_Init
          Static field lets Getstatic exec_instr StepI ics
         by(auto simp: split_beta split: if_split_asm) metis
      next
        case False
        then have nCalled: "\<forall>Cs. ics \<noteq> Called Cs" using ics by simp
        show ?thesis
        proof(cases "sh D1")
          case None
          then have nDone: "\<forall>sfs. sh D1 \<noteq> Some(sfs, Done)" by simp
          then show ?thesis using exec_step_ind_Getstatic_NoField
            exec_step_ind_Getstatic_Init[where sh=sh, OF _ _ nDone nCalled]
            field lets None False Static Getstatic exec_instr StepI ics
           by(auto split: if_split_asm) metis
        next
          case (Some a)
          then obtain sfs i where sfsi: "a=(sfs,i)" by(cases a)
          show ?thesis using exec_step_ind_Getstatic_NoField
            exec_step_ind_Getstatic_Init sfsi False Static Some field lets Getstatic exec_instr
          proof(cases "i = Done")
            case True then show ?thesis using exec_step_ind_Getstatic_NoField
              exec_step_ind_Getstatic_Done[OF _ _ nCalled] exec_step_ind_Getstatic_Init
              sfsi False Static Some field lets Getstatic exec_instr StepI ics
             by(auto split: if_split_asm) metis
          next
            case nD: False
            then have nDone: "\<forall>sfs. sh D1 \<noteq> Some(sfs, Done)" using sfsi Some by simp
            show ?thesis using nD
            proof(cases i)
              case Processing then show ?thesis using exec_step_ind_Getstatic_NoField
                exec_step_ind_Getstatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some field lets Getstatic exec_instr StepI ics
               by(auto split: if_split_asm) metis
            next
              case Prepared then show ?thesis using exec_step_ind_Getstatic_NoField
                exec_step_ind_Getstatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some field lets Getstatic exec_instr StepI ics
               by(auto split: if_split_asm) metis
            next
              case Error then show ?thesis using exec_step_ind_Getstatic_NoField
                exec_step_ind_Getstatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some field lets Getstatic exec_instr StepI ics
               by(auto split: if_split_asm) metis
            qed(simp)
          qed
        qed
      qed
    qed
  next
    case (Putfield F1 C1)
    then obtain D fs D' b t where lets: "the(h(the_Addr (hd(tl stk)))) = (D,fs)"
      "field P C1 F1 = (D',b,t)" by(cases "the(h(the_Addr (hd(tl stk))))", cases "field P C1 F1")
    then have "\<And>b' t'. P \<turnstile> D has F1,b':t' in C1 \<Longrightarrow> (D', b, t) = (C1, b', t')"
      using field_def2 has_field_idemp has_field_sees by fastforce
    then show ?thesis using exec_step_ind_Putfield_Null exec_step_ind_Putfield_NoField
       exec_step_ind_Putfield_Static exec_step_ind_Putfield lets Putfield exec_instr StepI
      by(auto split: if_split_asm staticb.splits) metis+
  next
    case (Putstatic C1 F1 D1)
    then obtain D' b t where lets: "field P D1 F1 = (D',b,t)" by(cases "field P D1 F1")
    then have field: "\<And>b' t'. P \<turnstile> C1 has F1,b':t' in D1 \<Longrightarrow> (D', b, t) = (D1, b', t')"
      using field_def2 has_field_idemp has_field_sees by fastforce
    show ?thesis
    proof(cases b)
      case NonStatic then show ?thesis
       using exec_step_ind_Putstatic_NoField exec_step_ind_Putstatic_NonStatic
        field lets Putstatic exec_instr StepI by(auto split: if_split_asm) fastforce
    next
      case Static show ?thesis
      proof(cases "ics = Called []")
        case True then show ?thesis using exec_step_ind_Putstatic_NoField
          exec_step_ind_Putstatic_Called exec_step_ind_Putstatic_Init
          Static field lets Putstatic exec_instr StepI ics
         by(cases "the(sh D1)", auto split: if_split_asm) metis
      next
        case False
        then have nCalled: "\<forall>Cs. ics \<noteq> Called Cs" using ics by simp
        show ?thesis
        proof(cases "sh D1")
          case None
          then have nDone: "\<forall>sfs. sh D1 \<noteq> Some(sfs, Done)" by simp
          then show ?thesis using exec_step_ind_Putstatic_NoField
            exec_step_ind_Putstatic_Init[where sh=sh, OF _ _ nDone nCalled]
            field lets None False Static Putstatic exec_instr StepI ics
           by(auto split: if_split_asm) metis
        next
          case (Some a)
          then obtain sfs i where sfsi: "a=(sfs,i)" by(cases a)
          show ?thesis using exec_step_ind_Putstatic_NoField
            exec_step_ind_Putstatic_Init sfsi False Static Some field lets Putstatic exec_instr
          proof(cases "i = Done")
            case True then show ?thesis using exec_step_ind_Putstatic_NoField
              exec_step_ind_Putstatic_Done[OF _ _ nCalled] exec_step_ind_Putstatic_Init
              sfsi False Static Some field lets Putstatic exec_instr StepI ics
             by(auto split: if_split_asm) metis
          next
            case nD: False
            then have nDone: "\<forall>sfs. sh D1 \<noteq> Some(sfs, Done)" using sfsi Some by simp
            show ?thesis using nD
            proof(cases i)
              case Processing then show ?thesis using exec_step_ind_Putstatic_NoField
                exec_step_ind_Putstatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some field lets Putstatic exec_instr StepI ics
               by(auto split: if_split_asm) metis
            next
              case Prepared then show ?thesis using exec_step_ind_Putstatic_NoField
                exec_step_ind_Putstatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some field lets Putstatic exec_instr StepI ics
               by(auto split: if_split_asm) metis
            next
              case Error then show ?thesis using exec_step_ind_Putstatic_NoField
                exec_step_ind_Putstatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some field lets Putstatic exec_instr StepI ics
               by(auto split: if_split_asm) metis
            qed(simp)
          qed
        qed
      qed
    qed
  next
    case Checkcast then show ?thesis
     using exec_step_ind_Checkcast exec_step_ind_Checkcast_Error exec_instr StepI
       by(auto split: if_split_asm)
  next
    case (Invoke M1 n) show ?thesis
    proof(cases "stk!n = Null")
      case True then show ?thesis using exec_step_ind_Invoke_Null Invoke exec_instr StepI
       by clarsimp
    next
      case False
      let ?C = "cname_of h (the_Addr (stk ! n))"
      obtain D b Ts T m where method: "method P ?C M1 = (D,b,Ts,T,m)" by(cases "method P ?C M1")
      then obtain mxs mxl\<^sub>0 ins xt where "m = (mxs,mxl\<^sub>0,ins,xt)" by(cases m)
      then show ?thesis using exec_step_ind_Invoke_NoMethod
        exec_step_ind_Invoke_Static exec_step_ind_Invoke method False Invoke exec_instr StepI
       by(auto split: if_split_asm staticb.splits)
    qed
  next
    case (Invokestatic C1 M1 n)
    obtain D b Ts T m where lets: "method P C1 M1 = (D,b,Ts,T,m)" by(cases "method P C1 M1")
    then obtain mxs mxl\<^sub>0 ins xt where m: "m = (mxs,mxl\<^sub>0,ins,xt)" by(cases m)
    have method: "\<And>b' Ts' t' m' D'. P \<turnstile> C1 sees M1,b':Ts' \<rightarrow> t' = m' in D'
     \<Longrightarrow> (D,b,Ts,T,m) = (D',b',Ts',t',m')" using lets by auto
    show ?thesis
    proof(cases b)
      case NonStatic then show ?thesis
       using exec_step_ind_Invokestatic_NoMethod exec_step_ind_Invokestatic_NonStatic
        m method lets Invokestatic exec_instr StepI  by(auto split: if_split_asm)
    next
      case Static show ?thesis
      proof(cases "ics = Called []")
        case True then show ?thesis using exec_step_ind_Invokestatic_NoMethod
          exec_step_ind_Invokestatic_Called exec_step_ind_Invokestatic_Init
          Static m method lets Invokestatic exec_instr StepI ics
         by(auto split: if_split_asm)
      next
        case False
        then have nCalled: "\<forall>Cs. ics \<noteq> Called Cs" using ics by simp
        show ?thesis
        proof(cases "sh D")
          case None
          then have nDone: "\<forall>sfs. sh D \<noteq> Some(sfs, Done)" by simp
          show ?thesis using exec_step_ind_Invokestatic_NoMethod
            exec_step_ind_Invokestatic_Init[where sh=sh, OF _ _ nDone nCalled]
            method m lets None False Static Invokestatic exec_instr StepI ics
           by(auto split: if_split_asm)
        next
          case (Some a)
          then obtain sfs i where sfsi: "a=(sfs,i)" by(cases a)
          show ?thesis using exec_step_ind_Invokestatic_NoMethod
            exec_step_ind_Invokestatic_Init sfsi False Static Some method lets Invokestatic exec_instr
          proof(cases "i = Done")
            case True then show ?thesis using exec_step_ind_Invokestatic_NoMethod
              exec_step_ind_Invokestatic_Done[OF _ _ _ nCalled] exec_step_ind_Invokestatic_Init
              sfsi False Static Some m method lets Invokestatic exec_instr StepI ics
             by(auto split: if_split_asm)
          next
            case nD: False
            then have nDone: "\<forall>sfs. sh D \<noteq> Some(sfs, Done)" using sfsi Some by simp
            show ?thesis using nD
            proof(cases i)
              case Processing then show ?thesis using exec_step_ind_Invokestatic_NoMethod
                exec_step_ind_Invokestatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some m method lets Invokestatic exec_instr StepI ics
               by(auto split: if_split_asm)
            next
              case Prepared then show ?thesis using exec_step_ind_Invokestatic_NoMethod
                exec_step_ind_Invokestatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some m method lets Invokestatic exec_instr StepI ics
               by(auto split: if_split_asm)
            next
              case Error then show ?thesis using exec_step_ind_Invokestatic_NoMethod
                exec_step_ind_Invokestatic_Init[where sh=sh, OF _ _ nDone nCalled]
                sfsi False Static Some m method lets Invokestatic exec_instr StepI ics
               by(auto split: if_split_asm)
            qed(simp)
          qed
        qed
      qed
    qed
  next
    case Return
    obtain D b Ts T m where method: "method P C M = (D,b,Ts,T,m)" by(cases "method P C M")
    then obtain mxs mxl\<^sub>0 ins xt where "m = (mxs,mxl\<^sub>0,ins,xt)" by(cases m)
    then show ?thesis using exec_step_ind_Return_Last_Init exec_step_ind_Return_Last
      exec_step_ind_Return_Init exec_step_ind_Return_NonStatic exec_step_ind_Return_Static
       method Return exec_instr StepI ics
      by(auto split: if_split_asm staticb.splits bool.splits list.splits)
  next
    case Pop then show ?thesis using exec_instr StepI exec_step_ind_Pop by auto
  next
    case IAdd then show ?thesis using exec_instr StepI exec_step_ind_IAdd by auto
  next
    case Goto then show ?thesis using exec_instr StepI exec_step_ind_Goto by auto
  next
    case CmpEq then show ?thesis using exec_instr StepI exec_step_ind_CmpEq by auto
  next
    case (IfFalse x17) then show ?thesis
     using exec_instr StepI exec_step_ind_IfFalse_nFalse exec_step_ind_IfFalse_False
       exec_instr StepI by(auto split: val.splits staticb.splits)
  next
    case Throw then show ?thesis
     using exec_instr StepI exec_step_ind_Throw exec_step_ind_Throw_Null
       by(auto split: val.splits)
  qed
qed

lemma exec_step_ind_imp_exec_step:
assumes esi: "exec_step_ind si P h stk loc C M pc ics frs sh (xp', h', frs', sh')"
  and si: "exec_step_input P C M pc ics = si"
shows "exec_step P h stk loc C M pc ics frs sh = (xp', h', frs', sh')"
proof -
  have StepI:
   "\<And>P C M pc Cs i . exec_step_input P C M pc (Called Cs) = StepI i
           \<Longrightarrow> instrs_of P C M ! pc = i \<and> Cs = []"
  proof -
    fix P C M pc Cs i show "exec_step_input P C M pc (Called Cs) = StepI i
           \<Longrightarrow> instrs_of P C M ! pc = i \<and> Cs = []" by(cases Cs; simp)
  qed
  have StepC:
   "\<And>P C M pc ics C' Cs. exec_step_input P C M pc ics = StepC C' Cs \<Longrightarrow> ics = Calling C' Cs"
     by simp
  have StepT:
   "\<And>P C M pc ics Cs a. exec_step_input P C M pc ics = StepT Cs a \<Longrightarrow> ics = Throwing Cs a"
     by simp
  show ?thesis using assms
  proof(induct rule: exec_step_ind.induct)
    case (exec_step_ind_NewOOM_Done sh C obj h ics P stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case by(cases ics, auto)
  next
    case (exec_step_ind_New_Done sh C obj h a ics P stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case by(cases ics, auto)
  next
    case (exec_step_ind_New_Init sh C ics P h stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case by(cases ics, auto split: init_state.splits)
  next
    case (exec_step_ind_Getfield_NoField v stk D fs h P F C loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases "the (h (the_Addr (hd stk)))", cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Getfield_Static v stk D fs h P F t C loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case
     by(cases "the (h (the_Addr (hd stk)))", cases "fst(snd(field P C F))",
        cases ics, auto simp: split_beta dest: has_field_sees[OF has_field_idemp] dest!: StepI)
  next
    case (exec_step_ind_Getfield v stk D fs h D' b t P C F loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case
     by(cases "the (h (the_Addr (hd stk)))",
        cases ics; fastforce simp: split_beta dest: has_field_sees[OF has_field_idemp] dest!: StepI)
  next
    case (exec_step_ind_Getstatic_NonStatic P C F t D h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case
     by(cases ics; fastforce simp: split_beta split: staticb.splits
                             dest: has_field_sees[OF has_field_idemp] dest!: StepI)
  next
    case exec_step_ind_Getstatic_Called
    then show ?case by(fastforce simp: split_beta split: staticb.splits dest!: StepI
                                 dest: has_field_sees[OF has_field_idemp])
  next
    case (exec_step_ind_Getstatic_Done D' b t P D F C ics sh sfs v h stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case by(cases ics, auto simp: split_beta split: staticb.splits
                                       dest: has_field_sees[OF has_field_idemp])
  next
    case (exec_step_ind_Getstatic_Init D' b t P D F C sh ics h stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case
       by(cases ics, auto simp: split_beta split: init_state.splits staticb.splits
                          dest: has_field_sees[OF has_field_idemp])
  next
    case (exec_step_ind_Putfield_NoField r stk a D fs h P F C loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases "the (h (the_Addr (hd(tl stk))))", cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Putfield_Static r stk a D fs h P F t C loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case
     by(cases "the (h (the_Addr (hd(tl stk))))", cases "fst(snd(field P C F))",
        cases ics, auto simp: split_beta dest: has_field_sees[OF has_field_idemp] dest!: StepI)
  next
    case (exec_step_ind_Putfield v stk r a D fs h D' b t P C F loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case
     by(cases "the (h (the_Addr (hd(tl stk))))",
        cases ics; fastforce simp: split_beta dest: has_field_sees[OF has_field_idemp] dest!: StepI)
  next
    case (exec_step_ind_Putstatic_NonStatic P C F t D h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case
     by(cases ics; fastforce simp: split_beta split: staticb.splits
                             dest: has_field_sees[OF has_field_idemp] dest!: StepI)
  next
    case exec_step_ind_Putstatic_Called
    then show ?case by(fastforce simp: split_beta split: staticb.splits dest!: StepI
                                 dest: has_field_sees[OF has_field_idemp])
  next
    case (exec_step_ind_Putstatic_Done D' b t P D F C ics sh sfs h stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case by(cases ics, auto simp: split_beta split: staticb.splits
                                       dest: has_field_sees[OF has_field_idemp])
  next
    case (exec_step_ind_Putstatic_Init D' b t P D F C sh ics h stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case
     by(cases ics, auto simp: split_beta split: staticb.splits init_state.splits
                        dest: has_field_sees[OF has_field_idemp])
  next
    case (exec_step_ind_Invoke ps n stk r C h D b Ts T mxs mxl\<^sub>0 ins xt P M m f' loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics; fastforce dest!: StepI)
  next
    case (exec_step_ind_Invokestatic_Called ps n stk D b Ts T mxs mxl\<^sub>0 ins xt P C M m ics ics' sh)
    then show ?case by(cases ics; fastforce dest!: StepI)
  next
    case (exec_step_ind_Invokestatic_Done ps n stk D b Ts T mxs mxl\<^sub>0 ins xt P C M m ics sh sfs f')
    then show ?case by(cases ics; fastforce)
  next
    case (exec_step_ind_Invokestatic_Init D b Ts T mxs mxl\<^sub>0 ins xt P C M m sh ics n h stk loc C\<^sub>0 M\<^sub>0 pc frs)
    then show ?case by(cases ics; fastforce split: init_state.splits)
  next
    case (exec_step_ind_Return_NonStatic D Ts T m P C\<^sub>0 M\<^sub>0 h stk\<^sub>0 loc\<^sub>0 pc ics stk' loc' C' m' pc' ics' frs' sh)
    then show ?case by(cases "method P C\<^sub>0 M\<^sub>0", cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Return_Static D Ts T m P C\<^sub>0 M\<^sub>0 h stk\<^sub>0 loc\<^sub>0 pc ics stk' loc' C' m' pc' ics' frs' sh)
    then show ?case by(cases "method P C\<^sub>0 M\<^sub>0", cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_IfFalse_nFalse stk i P h loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases "hd stk"; cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Throw_Null stk P h loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases "hd stk"; cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Init C Cs P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then have "ics = Called (C#Cs)" by simp
    then show ?case by auto
  (***)
  next
    case (exec_step_ind_Load n P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Store n P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Push v P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_NewOOM_Called h C P stk loc C\<^sub>0 M\<^sub>0 pc frs sh ics')
    then show ?case by(auto dest!: StepI)
  next
    case (exec_step_ind_New_Called h a C P stk loc C\<^sub>0 M\<^sub>0 pc frs sh ics')
    then show ?case by(auto dest!: StepI)
  next
    case (exec_step_ind_Getfield_Null stk F C P h loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Getstatic_NoField P C F D h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Putfield_Null stk F C P h loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Putstatic_NoField P C F D h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Checkcast P C h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Checkcast_Error P C h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Invoke_Null stk n M P h loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Invoke_NoMethod r stk n C h P M loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Invoke_Static r stk n C h D b Ts T mxs mxl\<^sub>0 ins xt P M m loc C\<^sub>0 M\<^sub>0 pc ics)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Invokestatic_NoMethod D b Ts T mxs mxl\<^sub>0 ins xt P C M n h stk loc C\<^sub>0 M\<^sub>0 pc ics)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Invokestatic_NonStatic D b Ts T mxs mxl\<^sub>0 ins xt P C M m n h stk loc C\<^sub>0 M\<^sub>0 pc ics)
    then show ?case by(cases ics, auto dest!: StepI)
  next
  case (exec_step_ind_Return_Last_Init P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 pc ics sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Return_Last M\<^sub>0 P h stk\<^sub>0 loc\<^sub>0 C\<^sub>0 pc ics sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
  case (exec_step_ind_Return_Init D b Ts T m P C\<^sub>0 h stk\<^sub>0 loc\<^sub>0 pc ics stk' loc' C' m' pc' ics')
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Pop P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_IAdd P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_IfFalse_False stk i P h loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_CmpEq P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Goto i P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Throw stk P h loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(cases ics, auto dest!: StepI)
  next
    case (exec_step_ind_Init_None_Called sh C Cs P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs)
    then show ?case by(auto dest!: StepC)
  next
    case (exec_step_ind_Init_Done sh C sfs Cs P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs)
    then show ?case by(auto dest!: StepC)
  next
    case (exec_step_ind_Init_Processing sh C sfs Cs P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs)
    then show ?case by(auto dest!: StepC)
  next
    case (exec_step_ind_Init_Error sh C sfs Cs P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs)
    then show ?case by(auto dest!: StepC)
  next
    case (exec_step_ind_Init_Prepared_Object sh C sfs sh' Cs P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs)
    then show ?case by(auto dest!: StepC)
  next
    case (exec_step_ind_Init_Prepared_nObject sh C sfs sh' D P Cs h stk loc C\<^sub>0 M\<^sub>0 pc ics frs)
    then show ?case by(auto dest!: StepC)
  next
    case (exec_step_ind_InitThrow C Cs a P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(auto dest!: StepT)
  next
    case (exec_step_ind_InitThrow_End a P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
    then show ?case by(auto dest!: StepT)
  qed
qed

\<comment> \<open> @{term exec_step} and @{term exec_step_ind} reach the same result given equivalent input \<close>
lemma exec_step_ind_equiv:
 "exec_step P h stk loc C M pc ics frs sh = (xp', h', frs', sh')
   = exec_step_ind (exec_step_input P C M pc ics) P h stk loc C M pc ics frs sh (xp', h', frs', sh')"
 using exec_step_imp_exec_step_ind exec_step_ind_imp_exec_step by auto

end
