(*  Title:       X86 instruction semantics and basic block symbolic execution
    Authors:     Freek Verbeek, Abhijith Bharadwaj, Joshua Bockenek, Ian Roessle, Timmy Weerwag, Binoy Ravindran
    Year:        2020
    Maintainer:  Freek Verbeek (freek@vt.edu)
*)

section "Example: word count program from GNU"

theory Example_WC
  imports SymbolicExecution X86_Parse
begin


text \<open>
  The wordcount (wc) program, specifically, the functions getword and counter.
  We compiled the source code found here:\\ 
  
      \url{https://www.gnu.org/software/cflow/manual/html_node/Source-of-wc-command.html}\\

  The source code is also found in the directory \texttt{./examples/wc}.

  The assembly below has been obtained by running in \texttt{./examples/wc}:
  \begin{verbatim}
    gcc wc.c -o wc
    objdump -M intel -d --no-show-raw-insn wc
  \end{verbatim}


  This example:
  \begin{itemize}
  \item contains a lot of memory accesses and demonstrates how a memory model is generated through assumptions;
  \item contains external function calls and demonstrates how to deal with that.
  \end{itemize}


  First, we define definitions named ``EXTERNAL\_FUNCTION\_*'' for each external function. The definitions
  are added to the simplifier.

  We model a C file (of C-type ``FILE'') as a pointer to a part of memory that contains the contents.
  We assume the contents are 0-terminated.

  Function \texttt{feof} takes as input (via \texttt{rdi}) a FILE*. It reads one byte from **rdi, i.e., the next byte of the file.
  It returns true iff the byte equals 0.\\

  Function \texttt{fopen} writes into memory both 1.) the contents of a file (the string "Hello"), and 2.) a pointer to the
  beginning of that file. It returns a pointer to that pointer.\\

  Function \texttt{getc} reads the next byte of the FILE (same is feof) and increments the pointer.\\
 
  Function \texttt{isword} simply returns true, and functions report and fclose simply do nothing.\\
\<close>


context unknowns
begin

definition EXTERNAL_FUNCTION_feof :: "state \<Rightarrow> state"
  where "EXTERNAL_FUNCTION_feof \<sigma> \<equiv> 
          let ptr = ucast (operand_read \<sigma> (QWORD PTR [''rdi'']\<^sub>1));
              val = mem_read \<sigma> ptr 1 in
            (semantics_RET  o 
             semantics_MOV (Reg ''eax'') (Imm (fromBool (val = 0))))
              \<sigma>"

declare EXTERNAL_FUNCTION_feof_def [simp]

definition EXTERNAL_FUNCTION__IO_getc :: "state \<Rightarrow> state"
  where "EXTERNAL_FUNCTION__IO_getc \<sigma> \<equiv>
          let ptr = ucast (operand_read \<sigma> (QWORD PTR [''rdi'']\<^sub>1));
              val = mem_read \<sigma> ptr 1 in
            (semantics_RET  o 
              semantics_MOV (Reg ''rax'') (Imm (if val = 0 then -1 else val)) o
              semantics_INC (QWORD PTR [''rdi'']\<^sub>1))
              \<sigma>"

declare EXTERNAL_FUNCTION__IO_getc_def [simp]

definition "EXTERNAL_FUNCTION_fopen \<sigma> = 
      semantics_RET (\<sigma> with [''rax'' :=\<^sub>r 100,
                             \<lbrakk>100,8\<rbrakk> :=\<^sub>m 108,
                             \<lbrakk>108,6\<rbrakk> :=\<^sub>m 0x006E6C6C6548])"

declare EXTERNAL_FUNCTION_fopen_def [simp]

definition EXTERNAL_FUNCTION_isword :: "state \<Rightarrow> state"
  where "EXTERNAL_FUNCTION_isword = operand_write (Reg ''rax'') 1 o semantics_RET"

declare EXTERNAL_FUNCTION_isword_def [simp]

definition EXTERNAL_FUNCTION_fclose :: "state \<Rightarrow> state"
  where "EXTERNAL_FUNCTION_fclose = semantics_RET"

declare EXTERNAL_FUNCTION_fclose_def [simp]

definition EXTERNAL_FUNCTION_report :: "state \<Rightarrow> state"
  where "EXTERNAL_FUNCTION_report = semantics_RET"

declare EXTERNAL_FUNCTION_report_def [simp]

end


text \<open>
  Below, one can see that, e.g. 810 denotes an external call (see address 0xc1b).
  For each external call, we replace the actual .got.plt section with a special
  instruction @{term ExternalFunc} followed by a name. These special instructions
  are interpreted as executing the related definition above.
\<close>

context unknowns
begin
  x86_64_parser wc_objdump \<open>
    7d0: EXTERNAL_FUNCTION fclose
    810: EXTERNAL_FUNCTION feof
    820: EXTERNAL_FUNCTION _IO_getc
    830: EXTERNAL_FUNCTION fopen
    bd5: EXTERNAL_FUNCTION isword
    b93: EXTERNAL_FUNCTION report

    c01: push   rbp
    c02: mov    rbp,rsp
    c05: sub    rsp,0x20
    c09: mov    QWORD PTR [rbp-0x18],rdi
    c0d: mov    DWORD PTR [rbp-0x4],0x0
    c14: mov    rax,QWORD PTR [rbp-0x18]
    c18: mov    rdi,rax
    c1b: call   810 <feof@plt>
    c20: test   eax,eax
    c22: je     c7d <getword+0x7c>
    c24: mov    eax,0x0
    c29: jmp    cf1 <getword+0xf0>
    c2e: mov    eax,DWORD PTR [rbp-0x8]
    c31: movzx  eax,al
    c34: mov    edi,eax
    c36: call   bd5 <isword>
    c3b: test   eax,eax
    c3d: je     c53 <getword+0x52>
    c3f: mov    rax,QWORD PTR [rip+0x201402]        # 202048 <wcount>
    c46: add    rax,0x1
    c4a: mov    QWORD PTR [rip+0x2013f7],rax        # 202048 <wcount>
    c51: jmp    c92 <getword+0x91>
    c53: mov    rax,QWORD PTR [rip+0x2013f6]        # 202050 <ccount>
    c5a: add    rax,0x1
    c5e: mov    QWORD PTR [rip+0x2013eb],rax        # 202050 <ccount>
    c65: cmp    DWORD PTR [rbp-0x8],0xa
    c69: jne    c7d <getword+0x7c>
    c6b: mov    rax,QWORD PTR [rip+0x2013e6]        # 202058 <lcount>
    c72: add    rax,0x1
    c76: mov    QWORD PTR [rip+0x2013db],rax        # 202058 <lcount>
    c7d: mov    rax,QWORD PTR [rbp-0x18]
    c81: mov    rdi,rax
    c84: call   820 <_IO_getc@plt>
    c89: mov    DWORD PTR [rbp-0x8],eax
    c8c: cmp    DWORD PTR [rbp-0x8],0xffffffff
    c90: jne    c2e <getword+0x2d>
    c92: jmp    cde <getword+0xdd>
    c94: mov    rax,QWORD PTR [rip+0x2013b5]        # 202050 <ccount>
    c9b: add    rax,0x1
    c9f: mov    QWORD PTR [rip+0x2013aa],rax        # 202050 <ccount>
    ca6: cmp    DWORD PTR [rbp-0x8],0xa
    caa: jne    cbe <getword+0xbd>
    cac: mov    rax,QWORD PTR [rip+0x2013a5]        # 202058 <lcount>
    cb3: add    rax,0x1
    cb7: mov    QWORD PTR [rip+0x20139a],rax        # 202058 <lcount>
    cbe: mov    eax,DWORD PTR [rbp-0x8]
    cc1: movzx  eax,al
    cc4: mov    edi,eax
    cc6: call   bd5 <isword>
    ccb: test   eax,eax
    ccd: je     ce6 <getword+0xe5>
    ccf: mov    rax,QWORD PTR [rbp-0x18]
    cd3: mov    rdi,rax
    cd6: call   820 <_IO_getc@plt>
    cdb: mov    DWORD PTR [rbp-0x8],eax
    cde: cmp    DWORD PTR [rbp-0x8],0xffffffff
    ce2: jne    c94 <getword+0x93>
    ce4: jmp    ce7 <getword+0xe6>
    ce6: nop
    ce7: cmp    DWORD PTR [rbp-0x8],0xffffffff
    ceb: setne  al
    cee: movzx  eax,al
    cf1: leave  
    cf2: ret


    cf3: push   rbp
    cf4: mov    rbp,rsp
    cf7: sub    rsp,0x20
    cfb: mov    QWORD PTR [rbp-0x18],rdi
    cff: mov    rax,QWORD PTR [rbp-0x18]
    d03: lea    rsi,[rip+0x1ff]        # f09 <_IO_stdin_used+0x19>
    d0a: mov    rdi,rax
    d0d: call   830 <fopen@plt>
    d12: mov    QWORD PTR [rbp-0x8],rax
    d16: cmp    QWORD PTR [rbp-0x8],0x0
    d1b: jne    d35 <counter+0x42>
    d1d: mov    rax,QWORD PTR [rbp-0x18]
    d21: mov    rsi,rax
    d24: lea    rdi,[rip+0x1e0]        # f0b <_IO_stdin_used+0x1b>
    d2b: mov    eax,0x0
    d30: call   ac6 <perrf>
    d35: mov    QWORD PTR [rip+0x201318],0x0        # 202058 <lcount>
    d40: mov    rax,QWORD PTR [rip+0x201311]        # 202058 <lcount>
    d47: mov    QWORD PTR [rip+0x2012fa],rax        # 202048 <wcount>
    d4e: mov    rax,QWORD PTR [rip+0x2012f3]        # 202048 <wcount>
    d55: mov    QWORD PTR [rip+0x2012f4],rax        # 202050 <ccount>
    d5c: nop
    d5d: mov    rax,QWORD PTR [rbp-0x8]
    d61: mov    rdi,rax
    d64: call   c01 <getword>
    d69: test   eax,eax
    d6b: jne    d5d <counter+0x6a>
    d6d: mov    rax,QWORD PTR [rbp-0x8]
    d71: mov    rdi,rax
    d74: call   7d0 <fclose@plt>
    d79: mov    rcx,QWORD PTR [rip+0x2012d8]        # 202058 <lcount>
    d80: mov    rdx,QWORD PTR [rip+0x2012c1]        # 202048 <wcount>
    d87: mov    rsi,QWORD PTR [rip+0x2012c2]        # 202050 <ccount>
    d8e: mov    rax,QWORD PTR [rbp-0x18]
    d92: mov    rdi,rax
    d95: call   b93 <report>
    d9a: mov    rdx,QWORD PTR [rip+0x20128f]        # 202030 <total_ccount>
    da1: mov    rax,QWORD PTR [rip+0x2012a8]        # 202050 <ccount>
    da8: add    rax,rdx
    dab: mov    QWORD PTR [rip+0x20127e],rax        # 202030 <total_ccount>
    db2: mov    rdx,QWORD PTR [rip+0x20127f]        # 202038 <total_wcount>
    db9: mov    rax,QWORD PTR [rip+0x201288]        # 202048 <wcount>
    dc0: add    rax,rdx
    dc3: mov    QWORD PTR [rip+0x20126e],rax        # 202038 <total_wcount>
    dca: mov    rdx,QWORD PTR [rip+0x20126f]        # 202040 <total_lcount>
    dd1: mov    rax,QWORD PTR [rip+0x201280]        # 202058 <lcount>
    dd8: add    rax,rdx
    ddb: mov    QWORD PTR [rip+0x20125e],rax        # 202040 <total_lcount>
    de2: nop
    de3: leave  
    de4: ret
  \<close>
end

context wc_objdump
begin
find_theorems fetch


text \<open>Note: this theorems takes roughly 15 minutes to prove.\<close>
schematic_goal counter:
  assumes "\<sigma>\<^sub>I = \<sigma> with [setRip 0xcf3]" 
  shows "assumptions ?A \<Longrightarrow> run 0xde4 fetch \<sigma>\<^sub>I ?\<sigma>'"
  apply (subst assms)
  (* you can simply run 

  apply (se_step)+

  However, we have broken it down so that some intermediate states are visible.
  Specifically, one can see the result of running getc, which fetches the next character.
  *)

  apply (repeat_n 8 se_step)
  \<comment> \<open>rip = 0x830 (2096), calling fopen\<close>
  apply se_step

  apply (repeat_n 12 se_step)
  \<comment> \<open>rip = 0xc01 (3073), calling getword\<close>
  apply se_step


  (* GETWORD BEGIN *)
  apply (repeat_n 13 se_step)
  \<comment> \<open>rip = 0xc84 (2080), calling getc\<close>
  apply se_step

  apply (repeat_n 32 se_step)
  \<comment> \<open>rip = 0xc84 (2080), calling getc\<close>
  apply se_step

  apply (repeat_n 18 se_step)
  \<comment> \<open>rip = 0xc84 (2080), calling getc\<close>
  apply se_step

  apply (repeat_n 18 se_step)
  \<comment> \<open>rip = 0xc84 (2080), calling getc\<close>
  apply se_step

  apply (repeat_n 18 se_step)
  \<comment> \<open>rip = 0xc84 (2080), calling getc\<close>
  apply se_step

  apply (repeat_n 18 se_step)
  \<comment> \<open>rip = 0xc84 (2080), calling getc\<close>
  apply se_step

  apply (repeat_n 9 se_step)
  (* GETWORD END*)

  apply (repeat_n 5 se_step)
  \<comment> \<open>rip = 0x7d0 (2000), calling fclose\<close>
  apply se_step

  apply (repeat_n 6 se_step)
  \<comment> \<open>rip = 0xb93 (2963), calling report\<close>
  apply se_step

  apply (repeat_n 15 se_step)
  apply (subst eq_def,simp)
  done

thm counter


text \<open>
The file opened by "fopen" contains the zero-terminated string "Hello": 0x006E6C6C6548.
After each call of getc, register RAX contains the read characters' ASCII code.

After termination, we can see the contents of the following global variables, set by function getword:
\begin{verbatim}
  Word count:      wcount = 1      (0x202048 = 2105416) 
  Character count: ccount = 5      (0x202050 = 2105424) 
  Line count:      lcount = lcount (0x202058 = 2105432) 
\end{verbatim}

  The totals accumulate to:
\begin{verbatim}
  Word count:      total_wcount = total_wcount + 5 (0x202038 = 2105400) 
  Character count: total_ccount = total_ccount + 5 (0x202030 = 2105392) 
  Line count:      total_lcount = total_lcount     (0x202040 = 2105408) 
\end{verbatim}
\<close>



end
end