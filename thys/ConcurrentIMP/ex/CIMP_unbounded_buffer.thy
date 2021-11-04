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

theory CIMP_unbounded_buffer
imports
  "../CIMP"
  "HOL-Library.Prefix_Order"
begin

abbreviation (input)
  Receive :: "'location \<Rightarrow> 'channel \<Rightarrow> ('val \<Rightarrow> 'state \<Rightarrow> 'state)
             \<Rightarrow> (unit, 'location, 'channel \<times> 'val, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleright>_" [0,0,81] 81)
where
  "\<lbrace>l\<rbrace> ch\<triangleright>f \<equiv> \<lbrace>l\<rbrace> Response (\<lambda>q s. if fst q = ch then {(f (snd q) s, ())} else {})"

abbreviation (input)
  Send :: "'location \<Rightarrow> 'channel \<Rightarrow> ('state \<Rightarrow> 'val) \<times> ('state \<Rightarrow> 'state)
          \<Rightarrow> (unit, 'location, 'channel \<times> 'val, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleleft>_" [0,0,81] 81)
where
  "\<lbrace>l\<rbrace> ch\<triangleleft>f \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (ch, fst f s)) (\<lambda>ans s. {snd f s})"

(*>*)
section\<open>Example: an unbounded buffer \label{sec:unbounded_buffer}\<close>

text\<open>

This is more literally Kai Engelhardt's example from his notes titled
\emph{Proving an Asynchronous Message Passing Program Correct}, 2011.

\<close>

datatype ex_chname = \<xi>12 | \<xi>23
type_synonym ex_val = nat
type_synonym ex_ls = "ex_val list"
type_synonym ex_ch = "ex_chname \<times> ex_val"
datatype ex_loc = c1 | r12 | r23 | s23 | s12
datatype ex_proc = p1 | p2 | p3

type_synonym ex_pgm = "(unit, ex_loc, ex_ch, ex_ls) com"
type_synonym ex_pred = "(unit, ex_loc, ex_proc, ex_ch, ex_ls) state_pred"
type_synonym ex_state = "(unit, ex_loc, ex_proc, ex_ch, ex_ls) system_state"
type_synonym ex_sys = "(unit, ex_loc, ex_proc, ex_ch, ex_ls) system"
type_synonym ex_history = "(ex_ch \<times> unit) list"

text\<open>

The local state for the producer process contains all values produced; consider that ghost state.

\<close>

abbreviation (input) snoc :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where "snoc x xs \<equiv> xs @ [x]"

primrec ex_coms :: "ex_proc \<Rightarrow> ex_pgm" where
  "ex_coms p1 = LOOP DO \<lbrace>c1\<rbrace> LocalOp (\<lambda>xs. {snoc x xs |x. True}) ;; \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>(last, id) OD"
| "ex_coms p2 = LOOP DO \<lbrace>r12\<rbrace> \<xi>12\<triangleright>snoc
                      \<oplus> \<lbrace>c1\<rbrace> IF (\<lambda>s. length s > 0) THEN \<lbrace>s23\<rbrace> \<xi>12\<triangleleft>(hd, tl) FI
                     OD"
| "ex_coms p3 = LOOP DO \<lbrace>r23\<rbrace> \<xi>23\<triangleright>snoc OD"

abbreviation ex_init :: "(ex_proc \<Rightarrow> ex_ls) \<Rightarrow> bool" where
  "ex_init s \<equiv> \<forall>p. s p = []"

abbreviation sys :: ex_sys where
  "sys \<equiv> \<lparr>PGMs = ex_coms, INIT = ex_init, FAIR = \<langle>True\<rangle>\<rparr>" (* FIXME add fairness hypotheses *)

abbreviation
  filter_on_channel :: "ex_chname \<Rightarrow> ex_state \<Rightarrow> ex_val list" ("\<downharpoonright>_" [100] 101)
where
  "\<downharpoonright>ch \<equiv> map (snd \<circ> fst) \<circ> filter ((=) ch \<circ> fst \<circ> fst) \<circ> HST"

definition I_pred :: ex_pred where
  "I_pred = pred_conjoin [
       at p1 c1 \<^bold>\<longrightarrow> \<downharpoonright>\<xi>12 \<^bold>= (\<lambda>s. s\<down> p1)
     , at p1 s12 \<^bold>\<longrightarrow> (\<lambda>s. length (s\<down> p1) > 0 \<and> butlast (s\<down> p1) = (\<downharpoonright>\<xi>12) s)
     , \<downharpoonright>\<xi>12 \<^bold>\<le> (\<lambda>s. s\<down> p1)
     , \<downharpoonright>\<xi>12 \<^bold>= \<downharpoonright>\<xi>23 \<^bold>@ (\<lambda>s. s\<down> p2)
     , at p2 s23 \<^bold>\<longrightarrow> (\<lambda>s. length (s\<down> p2) > 0)
     , (\<lambda>s. s\<down> p3) \<^bold>= \<downharpoonright>\<xi>23
     ]"

text\<open>

The local state of @{const "p3"} is some prefix of the local state of
@{const "p1"}.

\<close>

definition Etern_pred :: ex_pred where
  "Etern_pred \<equiv> \<lambda>s. s\<down> p3 \<le> s\<down> p1"

lemma correct_system:
  assumes "I_pred s"
  shows "Etern_pred s"
using assms unfolding Etern_pred_def I_pred_def less_eq_list_def prefix_def by clarsimp

lemma p1_c1[simplified, intro]:
  "ex_coms, p1, lconst {s12} \<turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>c1\<rbrace> LocalOp (\<lambda>xs. { snoc x xs |x. True })"
apply (rule vcg.intros)
apply (clarsimp simp: I_pred_def atS_def)
done

lemma p1_s12[simplified, intro]:
  "ex_coms, p1, lconst {c1} \<turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>(last, id)"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p'; clarsimp)
apply (clarsimp simp: I_pred_def atS_def)
apply (metis Prefix_Order.prefix_snoc append.assoc append_butlast_last_id)
done

lemma p2_s23[simplified, intro]:
  "ex_coms, p2, lconst {c1, r12} \<turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>s23\<rbrace> \<xi>12\<triangleleft>(hd, tl)"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p'; clarsimp)
done

lemma p2_pi4[intro]:
  "ex_coms, p2, lcond {s23} {c1, r12} (\<lambda>s. s \<noteq> []) \<turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>c1\<rbrace> IF (\<lambda>s. s \<noteq> []) THEN c' FI"
apply (rule vcg.intros)
apply (clarsimp simp: I_pred_def atS_def split: lcond_splits)
done

lemma I: "sys \<Turnstile>\<^bsub>pre\<^esub> I_pred"
apply (rule VCG)
 apply (clarsimp dest!: initial_stateD simp: I_pred_def atS_def)
apply (rename_tac p)
apply (case_tac p; auto)
done

lemma I_valid: "sys \<Turnstile> \<box>\<lceil>I_pred\<rceil>"
by (rule valid_prerun_lift[OF I])

(*<*)

end
(*>*)
