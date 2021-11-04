(*  Title:       X86 instruction semantics and basic block symbolic execution
    Authors:     Freek Verbeek, Abhijith Bharadwaj, Joshua Bockenek, Ian Roessle, Timmy Weerwag, Binoy Ravindran
    Year:        2020
    Maintainer:  Freek Verbeek (freek@vt.edu)
*)

section "Small examples"

theory Examples
  imports SymbolicExecution 
begin

context unknowns
begin
  
  text \<open>
  A simple hand-crafted example showing some basic instructions. 
\<close>


schematic_goal example1:
  assumes[simp]: "fetch 0x0  = PUSH (Reg ''rbp'') 1"
      and[simp]: "fetch 0x1  = SUB  (Reg ''rsp'') (Imm 30) 2"
      and[simp]: "fetch 0x2  = MOV  (QWORD PTR [22 + ''rsp'']\<^sub>2) (Imm 42) 3"
      and[simp]: "fetch 0x3  = MOV  (QWORD PTR [30 + ''rsp'']\<^sub>2) (Imm 43) 4"
      and[simp]: "fetch 0x4  = ADD  (Reg ''rsp'') (Imm 30) 5"
      and[simp]: "fetch 0x5  = POP  (Reg ''rbp'') 6"
      and[simp]: "fetch 0x6  = RET 1"
    shows "run 0x6 fetch (\<sigma> with [setRip 0x0]) ?\<sigma>'"
  apply se_step+
  apply (subst eq_def,simp)
  done

thm example1




text \<open>Demonstrates little-endian memory and register-aliasing\<close>

text\<open>
\begin{verbatim}
  RAX +   0    1    2     3     4     5     6     7
        | FF | EE | DD  | CC  | BB  | AA  | 00  | 00  |
  
  EDI := 0xCCDDEEFF
  EBX := 0xAABB
  RCX := 0xAABBCCDDAABB
\end{verbatim}
\<close>

schematic_goal example2:
  assumes[simp]: "fetch 0x0   = MOV  (QWORD PTR [''rax'']\<^sub>1) (Imm 0xAABBCCDDEEFF) 1"
      and[simp]: "fetch 0x1   = MOV  (Reg ''edi'')          (DWORD PTR [''rax'']\<^sub>1) 2"
      and[simp]: "fetch 0x2   = MOV  (Reg ''ebx'')          (DWORD PTR [4 + ''rax'']\<^sub>2) 3"
      and[simp]: "fetch 0x3   = MOV  (Reg ''rcx'')          (QWORD PTR [''rax'']\<^sub>1) 4"
      and[simp]: "fetch 0x4   = MOV   (Reg ''cx'')          (WORD PTR  [4 + ''rax'']\<^sub>2) 5"
    shows "run 0x4 fetch (\<sigma> with [setRip 0x0]) ?\<sigma>'" 
  apply se_step+
  apply (subst eq_def,simp)
  done

thm example2

text \<open>
  This example show how assumptions over regions are generated.
  Since no relation over rax and rbx is known in the initial state, they will be assumed to be
  separate by default.
\<close>
schematic_goal example3:
  assumes[simp]: "fetch 0x0   = MOV  (QWORD PTR [''rax'']\<^sub>1) (Imm 0xAABBCCDDEEFF) 1"
      and[simp]: "fetch 0x1   = MOV  (QWORD PTR [''rbx'']\<^sub>1) (Imm 0x112233445566) 2"
      and[simp]: "fetch 0x2   = MOV  (Reg ''rcx'')          (DWORD PTR [2 + ''rax'']\<^sub>2) 3"
      and[simp]: "fetch 0x3   = MOV  (Reg ''cx'')           (WORD PTR  [4 + ''rbx'']\<^sub>2) 4"
      and[simp]: "fetch 0x4   = MOV  (Reg ''cl'')           (BYTE PTR  [''rax'']\<^sub>1) 5"
    shows "assumptions ?A \<Longrightarrow> run 0x4 fetch (\<sigma> with [setRip 0x0]) ?\<sigma>'" 
  apply se_step+
  apply (subst eq_def,simp)
  done

thm example3

end







end
