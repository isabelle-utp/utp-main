(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP_one_place_buffer
imports
  "../CIMP"
begin

(*>*)
section\<open>Example: a one-place buffer \label{sec:one_place_buffer}\<close>

text\<open>

To demonstrate the CIMP reasoning infrastructure, we treat the trivial
one-place buffer example of @{cite [cite_macro=citet]
\<open>\S3.3\<close> "DBLP:journals/toplas/LamportS84"}. Note that the
semantics for our language is different to @{cite
[cite_macro=citeauthor] "DBLP:journals/toplas/LamportS84"}'s, who
treated a historical variant of CSP (i.e., not the one in @{cite
"Hoare:1985"}).

We introduce some syntax for fixed-topology (static channel-based)
scenarios.

\<close>

abbreviation
  rcv_syn :: "'location \<Rightarrow> 'channel \<Rightarrow> ('val \<Rightarrow> 'state \<Rightarrow> 'state)
           \<Rightarrow> (unit, 'location, 'channel \<times> 'val, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleright>_" [0,0,81] 81)
where
  "\<lbrace>l\<rbrace> ch\<triangleright>f \<equiv> \<lbrace>l\<rbrace> Response (\<lambda>q s. if fst q = ch then {(f (snd q) s, ())} else {})"

abbreviation
  snd_syn :: "'location \<Rightarrow> 'channel \<Rightarrow> ('state \<Rightarrow> 'val)
          \<Rightarrow> (unit, 'location, 'channel \<times> 'val, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleleft>_" [0,0,81] 81)
where
  "\<lbrace>l\<rbrace> ch\<triangleleft>f \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (ch, f s)) (\<lambda>ans s. {s})"

text\<open>

These definitions largely follow @{cite [cite_macro=citet]
"DBLP:journals/toplas/LamportS84"}. We have three processes
communicating over two channels. We enumerate program locations.

\<close>

datatype ex_chname = \<xi>12 | \<xi>23
type_synonym ex_val = nat
type_synonym ex_ch = "ex_chname \<times> ex_val"
datatype ex_loc = r12 | r23 | s23 | s12
datatype ex_proc = p1 | p2 | p3

type_synonym ex_pgm = "(unit, ex_loc, ex_ch, ex_val) com"
type_synonym ex_pred = "(unit, ex_loc, ex_proc, ex_ch, ex_val) state_pred"
type_synonym ex_state = "(unit, ex_loc, ex_proc, ex_ch, ex_val) system_state"
type_synonym ex_sys = "(unit, ex_loc, ex_proc, ex_ch, ex_val) system"
type_synonym ex_history = "(ex_ch \<times> unit) list"

text\<open>

We further specialise these for our particular example.

\<close>

primrec
  ex_coms :: "ex_proc \<Rightarrow> ex_pgm"
where
  "ex_coms p1 = \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>id"
| "ex_coms p2 = LOOP DO \<lbrace>r12\<rbrace> \<xi>12\<triangleright>(\<lambda>v _. v) ;; \<lbrace>s23\<rbrace> \<xi>23\<triangleleft>id OD"
| "ex_coms p3 = \<lbrace>r23\<rbrace> \<xi>23\<triangleright>(\<lambda>v _. v)"

text\<open>

Each process starts with an arbitrary initial local state.

\<close>

abbreviation ex_init :: "(ex_proc \<Rightarrow> ex_val) \<Rightarrow> bool" where
  "ex_init \<equiv> \<langle>True\<rangle>"

abbreviation sys :: ex_sys where
  "sys \<equiv> \<lparr>PGMs = ex_coms, INIT = ex_init, FAIR = \<langle>True\<rangle>\<rparr>" (* FIXME add fairness hypotheses *)

text\<open>

The following adapts Kai Engelhardt's, from his notes titled
\emph{Proving an Asynchronous Message Passing Program Correct},
2011. The history variable tracks the causality of the system, which I
feel is missing in Lamport's treatment. We tack on Lamport's invariant
so we can establish \<open>Etern_pred\<close>.

\<close>

abbreviation
  filter_on_channel :: "ex_chname \<Rightarrow> ex_state \<Rightarrow> ex_val list" ("\<downharpoonright>_" [100] 101)
where
  "\<downharpoonright>ch \<equiv> map (snd \<circ> fst) \<circ> filter ((=) ch \<circ> fst \<circ> fst) \<circ> HST"

definition IL :: ex_pred where
  "IL = pred_conjoin [
       at p1 s12 \<^bold>\<longrightarrow> LIST_NULL \<downharpoonright>\<xi>12
     , terminated p1 \<^bold>\<longrightarrow> \<downharpoonright>\<xi>12 \<^bold>= (\<lambda>s. [s\<down> p1])
     , at p2 r12 \<^bold>\<longrightarrow> \<downharpoonright>\<xi>12 \<^bold>= \<downharpoonright>\<xi>23
     , at p2 s23 \<^bold>\<longrightarrow> \<downharpoonright>\<xi>12 \<^bold>= \<downharpoonright>\<xi>23 \<^bold>@ (\<lambda>s. [s\<down> p2]) \<^bold>\<and> (\<lambda>s. s\<down> p1 = s\<down> p2)
     , at p3 r23 \<^bold>\<longrightarrow> LIST_NULL \<downharpoonright>\<xi>23
     , terminated p3 \<^bold>\<longrightarrow> \<downharpoonright>\<xi>23 \<^bold>= (\<lambda>s. [s\<down> p2]) \<^bold>\<and> (\<lambda>s. s\<down> p1 = s\<down> p3)
     ]"

text\<open>

If @{const p3} terminates, then it has @{const p1}'s value. This is
stronger than @{cite [cite_macro=citeauthor]
"DBLP:journals/toplas/LamportS84"}'s as we don't ask that the first
process has also terminated.

\<close>

definition Etern_pred :: ex_pred where
  "Etern_pred = (terminated p3 \<^bold>\<longrightarrow> (\<lambda>s. s\<down> p1 = s\<down> p3))"

text\<open>

Proofs from here down.

\<close>

lemma correct_system:
  assumes "IL sh"
  shows "Etern_pred sh"
using assms unfolding Etern_pred_def IL_def by simp

lemma IL_p1: "ex_coms, p1, lconst {} \<turnstile> \<lbrace>IL\<rbrace> \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>(\<lambda>s. s)"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p'; clarsimp simp: IL_def atLs_def)
done

lemma IL_p2: "ex_coms, p2, lconst {r12} \<turnstile> \<lbrace>IL\<rbrace> \<lbrace>s23\<rbrace> \<xi>23\<triangleleft>(\<lambda>s. s)"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p'; clarsimp simp: IL_def)
done

lemma IL: "sys \<Turnstile>\<^bsub>pre\<^esub> IL"
apply (rule VCG)
 apply (clarsimp simp: IL_def atLs_def dest!: initial_stateD)
apply (rename_tac p)
apply (case_tac p; clarsimp simp: IL_p1 IL_p2)
done

lemma IL_valid: "sys \<Turnstile> \<box>\<lceil>IL\<rceil>"
by (rule valid_prerun_lift[OF IL])

(*<*)

end
(*>*)
