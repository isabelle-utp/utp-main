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

theory Proofs
imports
  TSO
  Phases
  MarkObject
  StrongTricolour
  Valid_Refs
  Worklists
  Global_Noninterference
  Noninterference
  Initial_Conditions
begin

(*>*)
section\<open>Top-level safety \label{sec:top-level-correctness}\<close>

lemma (in gc) I:
  "\<lbrace> I \<rbrace> gc"
apply (simp add: I_defs)
apply (rule valid_pre)
apply ( rule valid_conj_lift valid_all_lift | fastforce )+
done

lemma (in sys) I:
  "\<lbrace> I \<rbrace> sys"
apply (simp add: I_defs)
apply (rule valid_pre)
apply ( rule valid_conj_lift valid_all_lift | fastforce )+
done

text\<open>

We need to separately treat the two cases of a single mutator and
multiple mutators. In the latter case we have the additional
obligation of showing mutual non-interference amongst mutators.

\<close>

lemma mut_invsL[intro]:
  "\<lbrace>I\<rbrace> mutator m \<lbrace>mut_m.invsL m'\<rbrace>"
proof(cases "m = m'")
  case True
  interpret mut_m m' by unfold_locales
  from True show ?thesis
    apply (simp add: I_defs)
    apply (rule valid_pre)
    apply ( rule valid_conj_lift | fastforce )+
    done
next
  case False
  then interpret mut_m' m' m by unfold_locales blast
  from False show ?thesis
    apply (simp add: I_defs)
    apply (rule valid_pre)
    apply ( rule valid_conj_lift | fastforce )+
    done
qed

(* FIXME split mutators_phase_inv from global invs to local invs. Move to StrongTricolour or similar. note dependence on I *)
lemma mutators_phase_inv[intro]:
  "\<lbrace> I \<rbrace> mutator m  \<lbrace> LSTP (mut_m.mutator_phase_inv m') \<rbrace>"
proof(cases "m = m'")
  case True
  interpret mut_m m' by unfold_locales
  from True show ?thesis
    apply (simp add: I_defs)
    apply (rule valid_pre)
    apply ( rule valid_conj_lift valid_all_lift | fastforce )+
    done
next
  case False
  then interpret mut_m' m' m by unfold_locales blast
  from False show ?thesis
    apply (simp add: I_defs)
    apply (rule valid_pre)
    apply ( rule valid_conj_lift valid_all_lift | fastforce )+
    done
qed

lemma (in mut_m) I:
  "\<lbrace> I \<rbrace> mutator m"
apply (simp add: I_def gc.invsL_def invs_def Local_Invariants.invsL_def)
apply (rule valid_pre)
apply ( rule valid_conj_lift valid_all_lift | fastforce )+
apply (simp add: I_defs)
done

context gc_system
begin

theorem I: "gc_system \<Turnstile>\<^bsub>pre\<^esub> I"
apply (rule VCG)
 apply (rule init_inv)
apply (rename_tac p)
apply (case_tac p, simp_all)
  apply (rule mut_m.I[unfolded valid_proc_def, simplified])
 apply (rule gc.I[unfolded valid_proc_def, simplified])
apply (rule sys.I[unfolded valid_proc_def, simplified])
done

text\<open>

\label{sec:proofs-headline-safety}

Our headline safety result follows directly.

\<close>

corollary safety: "gc_system \<Turnstile>\<^bsub>pre\<^esub> LSTP valid_refs"
using I unfolding I_def invs_def valid_refs_def prerun_valid_def
apply clarsimp
apply (drule_tac x=\<sigma> in spec)
apply (drule (1) mp)
apply (rule alwaysI)
apply (erule_tac i=i in alwaysE)
apply (clarsimp simp: valid_refs_invD(1))
done

end

text\<open>

The GC is correct for the remaining fixed-but-arbitrary initial
conditions.

\<close>

interpretation gc_system_interpretation: gc_system undefined .

(* unused_thms Main Sublist CIMP - *)


section\<open> A concrete system state \label{sec:concrete-system-state} \<close>

text\<open>

We demonstrate that our definitions are not vacuous by exhibiting a
concrete initial state that satisfies the initial conditions. The heap
is shown in Figure~\ref{fig:concrete-heap}. We use Isabelle's notation
for types of a given size.

\begin{figure}
  \centering
  \includegraphics{heap.pdf}
  \caption{A concrete system state.}
  \label{fig:concrete-heap}
\end{figure}

\<close>
(*<*)

end
(*>*)
