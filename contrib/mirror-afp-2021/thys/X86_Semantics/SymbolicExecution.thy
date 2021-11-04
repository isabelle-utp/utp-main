(*  Title:       X86 instruction semantics and basic block symbolic execution
    Authors:     Freek Verbeek, Abhijith Bharadwaj, Joshua Bockenek, Ian Roessle, Timmy Weerwag, Binoy Ravindran
    Year:        2020
    Maintainer:  Freek Verbeek (freek@vt.edu)
*)

section "A symbolic execution engine"


theory SymbolicExecution
  imports X86_InstructionSemantics StateCleanUp
begin



definition eq (infixl "\<triangleq>" 50)
  where "(\<triangleq>) \<equiv> (=)"

context unknowns
begin 


inductive run :: "64 word \<Rightarrow> (64 word \<Rightarrow> I) \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where 
    "rip \<sigma> = a\<^sub>f \<Longrightarrow> fetch (rip \<sigma>) = i \<Longrightarrow> \<sigma>' \<triangleq> step i \<sigma> \<Longrightarrow> run a\<^sub>f fetch \<sigma> \<sigma>'"
  | "rip \<sigma> \<noteq> a\<^sub>f \<Longrightarrow> fetch (rip \<sigma>) = i \<Longrightarrow> run a\<^sub>f fetch (step i \<sigma>) \<sigma>' \<Longrightarrow> run a\<^sub>f fetch \<sigma> \<sigma>'"


method fetch_and_execute = (
   ((rule run.intros(2),(simp (no_asm) add: state_simps;fail))
    | (rule run.intros(1),(simp (no_asm) add: state_simps;fail))),
   (simp (no_asm) add: state_simps),                                             \<comment> \<open>fetch instruction\<close>
   (simp (no_asm_simp) add: step_def semantics_simps state_simps BitByte_simps), \<comment> \<open>simplification\<close>
   (subst clean_state_updates[symmetric],simp (no_asm))                          \<comment> \<open>cleaning up\<close>
 )

method resolve_mem_reads = (
  subst mem_read_mem_write_separate,
  ((simp (no_asm_simp) add: separate_simps state_simps; fail) 
   | (rule assumptions_impI,simp (no_asm_simp),subst (asm) assumptions_conjE, erule conjE)),
  (simp (no_asm_simp) add: semantics_simps state_simps BitByte_simps separate_simps)?
 )

method se_step = 
  fetch_and_execute,
  ((resolve_mem_reads)+;(subst clean_state_updates[symmetric],simp (no_asm)))?,
  clean_up

method se_step_no_clean = 
  fetch_and_execute,
  ((resolve_mem_reads)+;(subst clean_state_updates[symmetric],simp (no_asm)))?

end


abbreviation RSP0 
  where "RSP0 \<sigma> \<equiv> regs \<sigma> ''rsp''"
abbreviation RBP0 
  where "RBP0 \<sigma> \<equiv> regs \<sigma> ''rbp''"
abbreviation RAX0 
  where "RAX0 \<sigma> \<equiv> regs \<sigma> ''rax''"
abbreviation RBX0 
  where "RBX0 \<sigma> \<equiv> regs \<sigma> ''rbx''"
abbreviation RCX0 
  where "RCX0 \<sigma> \<equiv> regs \<sigma> ''rcx''"
abbreviation RDX0 
  where "RDX0 \<sigma> \<equiv> regs \<sigma> ''rdx''"
abbreviation RDI0 
  where "RDI0 \<sigma> \<equiv> regs \<sigma> ''rdi''"
abbreviation RSI0 
  where "RSI0 \<sigma> \<equiv> regs \<sigma> ''rsi''"
abbreviation R150 
  where "R150 \<sigma> \<equiv> regs \<sigma> ''r15''"
abbreviation R140
  where "R140 \<sigma> \<equiv> regs \<sigma> ''r14''"
abbreviation R130 
  where "R130 \<sigma> \<equiv> regs \<sigma> ''r13''"
abbreviation R120 
  where "R120 \<sigma> \<equiv> regs \<sigma> ''r12''"
abbreviation R110 
  where "R110 \<sigma> \<equiv> regs \<sigma> ''r11''"
abbreviation R100 
  where "R100 \<sigma> \<equiv> regs \<sigma> ''r10''"
abbreviation R90 
  where "R90 \<sigma> \<equiv> regs \<sigma> ''r9''"
abbreviation R80 
  where "R80 \<sigma> \<equiv> regs \<sigma> ''r8''"



text \<open>Repeat a command up to n times, in deterministic fashion (a la the REPEAT\_DETERM tactic).\<close>

method_setup repeat_n = \<open>
  Scan.lift Parse.nat -- Method.text_closure >>
    (fn (n,text) => fn ctxt => fn using => 
      let
        val ctxt_tac = Method.evaluate_runtime text ctxt using;
        fun repeat_n 0 ctxt_st = Seq.make_results (Seq.succeed ctxt_st)
          | repeat_n i ctxt_st = case Seq.pull (ctxt_tac ctxt_st) of
                            SOME (Seq.Result ctxt_st', _) => repeat_n (i-1) ctxt_st'
                          | _ => Seq.make_results (Seq.succeed ctxt_st)
      in
        repeat_n n
      end)
\<close>

end
