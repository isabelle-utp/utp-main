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

theory Global_Invariants
imports
  Proofs_Basis
begin

(*>*)
section\<open>Global Invariants \label{sec:global-invariants}\<close>


subsection\<open>The valid references invariant\<close>

text\<open>

The key safety property of a GC is that it does not free objects that
are reachable from mutator roots. The GC also requires that there are
objects for all references reachable from grey objects.

\<close>

definition valid_refs_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
 "valid_refs_inv = (\<^bold>\<forall>m x. mut_m.reachable m x \<^bold>\<or> grey_reachable x \<^bold>\<longrightarrow> valid_ref x)"

text\<open>

The remainder of the invariants support the inductive argument that
this one holds.

\<close>


subsection\<open>The strong-tricolour invariant \label{sec:strong-tricolour-invariant} \<close>

text\<open>

As the GC algorithm uses both insertion and deletion barriers, it
preserves the \emph{strong tricolour-invariant}:

\<close>

abbreviation points_to_white :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" (infix "points'_to'_white" 51) where
  "x points_to_white y \<equiv> x points_to y \<^bold>\<and> white y"

definition strong_tricolour_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "strong_tricolour_inv = (\<^bold>\<forall>b w. black b \<^bold>\<longrightarrow> \<^bold>\<not>b points_to_white w)"

text\<open>

Intuitively this invariant says that there are no pointers from
completely processed objects to the unexplored space; i.e., the grey
references properly separate the two. In contrast the weak tricolour
invariant allows such pointers, provided there is a grey reference
that protects the unexplored object.

\<close>

definition has_white_path_to :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" (infix "has'_white'_path'_to" 51) where
  "x has_white_path_to y = (\<lambda>s. (\<lambda>x y. (x points_to_white y) s)\<^sup>*\<^sup>* x y)"

definition grey_protects_white :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" (infix "grey'_protects'_white" 51) where
  "g grey_protects_white w = (grey g \<^bold>\<and> g has_white_path_to w)"

definition weak_tricolour_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "weak_tricolour_inv =
     (\<^bold>\<forall>b w. black b \<^bold>\<and> b points_to_white w \<^bold>\<longrightarrow> (\<^bold>\<exists>g. g grey_protects_white w))"

lemma "strong_tricolour_inv s \<Longrightarrow> weak_tricolour_inv s"
by (clarsimp simp: strong_tricolour_inv_def weak_tricolour_inv_def grey_protects_white_def) (* FIXME elide *)

text\<open>

The key invariant that the mutators establish as they perform \<open>get_roots\<close>: they protect their white-reachable references with grey
objects.

\<close>

definition in_snapshot :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "in_snapshot r = (black r \<^bold>\<or> (\<^bold>\<exists>g. g grey_protects_white r))"

definition (in mut_m) reachable_snapshot_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "reachable_snapshot_inv = (\<^bold>\<forall>r. reachable r \<^bold>\<longrightarrow> in_snapshot r)"


subsection\<open>Phase invariants \label{sec:phase-invariants}\<close>

text (in mut_m) \<open>

The phase structure of this GC algorithm greatly complicates this
safety proof. The following assertions capture this structure in
several relations.

We begin by relating the mutators' @{const
"mut_ghost_hs_phase"} to @{const "sys_ghost_hs_phase"},
which tracks the GC's. Each mutator can be at most one handshake step
behind the GC. If any mutator is behind then the GC is stalled on a
pending handshake. We include the handshake type as
\<open>get_work\<close> can occur any number of times.

\<close>

definition hp_step_rel :: "(bool \<times> hs_type \<times> hs_phase \<times> hs_phase) set" where
  "hp_step_rel =
  { True }  \<times> ({ (ht_NOOP, hp, hp) |hp. hp \<in> {hp_Idle, hp_IdleInit, hp_InitMark, hp_Mark} }
            \<union> { (ht_GetRoots, hp_IdleMarkSweep, hp_IdleMarkSweep)
              , (ht_GetWork,  hp_IdleMarkSweep, hp_IdleMarkSweep) })
\<union> { False } \<times> { (ht_NOOP,     hp_Idle,          hp_IdleMarkSweep)
              , (ht_NOOP,     hp_IdleInit,      hp_Idle)
              , (ht_NOOP,     hp_InitMark,      hp_IdleInit)
              , (ht_NOOP,     hp_Mark,          hp_InitMark)
              , (ht_GetRoots, hp_IdleMarkSweep, hp_Mark)
              , (ht_GetWork,  hp_IdleMarkSweep, hp_IdleMarkSweep) }"

definition handshake_phase_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "handshake_phase_inv = (\<^bold>\<forall>m.
     sys_ghost_hs_in_sync m \<^bold>\<otimes> sys_hs_type \<^bold>\<otimes> sys_ghost_hs_phase \<^bold>\<otimes> mut_m.mut_ghost_hs_phase m \<^bold>\<in> \<langle>hp_step_rel\<rangle>
  \<^bold>\<and> (sys_hs_pending m \<^bold>\<longrightarrow> \<^bold>\<not>sys_ghost_hs_in_sync m))"

text \<open>

In some phases we need to know that the insertion and deletion
barriers are installed, in order to preserve the snapshot. These can
ignore TSO effects as the process doing the marking holds the TSO lock
until the mark is committed to the shared memory (see
\S\ref{def:valid_W_inv}).

Note that it is not easy to specify precisely when the snapshot (of
objects the GC will retain) is taken due to the raggedness of the
initialisation.

Read the following as ``when mutator \<open>m\<close> is past the
specified handshake, and has yet to reach the next one, ... holds.''

\<close>

abbreviation marked_insertion :: "('field, 'payload, 'ref) mem_store_action \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "marked_insertion w \<equiv> \<lambda>s. case w of mw_Mutate r f (Some r') \<Rightarrow> marked r' s | _ \<Rightarrow> True"

abbreviation marked_deletion :: "('field, 'payload, 'ref) mem_store_action \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "marked_deletion w \<equiv> \<lambda>s. case w of mw_Mutate r f opt_r' \<Rightarrow> obj_at_field_on_heap (\<lambda>r'. marked r' s) r f s | _ \<Rightarrow> True"

context mut_m
begin

definition marked_insertions :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "marked_insertions = (\<^bold>\<forall>w. tso_pending_store (mutator m) w \<^bold>\<longrightarrow> marked_insertion w)"

definition marked_deletions :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "marked_deletions = (\<^bold>\<forall>w. tso_pending_store (mutator m) w \<^bold>\<longrightarrow> marked_deletion w)"

primrec mutator_phase_inv_aux :: "hs_phase \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "mutator_phase_inv_aux hp_Idle          = \<langle>True\<rangle>"
| "mutator_phase_inv_aux hp_IdleInit      = no_black_refs"
| "mutator_phase_inv_aux hp_InitMark      = marked_insertions"
| "mutator_phase_inv_aux hp_Mark          = (marked_insertions \<^bold>\<and> marked_deletions)"
| "mutator_phase_inv_aux hp_IdleMarkSweep = (marked_insertions \<^bold>\<and> marked_deletions \<^bold>\<and> reachable_snapshot_inv)"

abbreviation mutator_phase_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "mutator_phase_inv \<equiv> mutator_phase_inv_aux \<^bold>$ mut_ghost_hs_phase"

end

abbreviation mutators_phase_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "mutators_phase_inv \<equiv> (\<^bold>\<forall>m. mut_m.mutator_phase_inv m)"

text\<open>

This is what the GC guarantees. Read this as ``when the GC is at or
past the specified handshake, ... holds.''

\<close>

primrec sys_phase_inv_aux :: "hs_phase \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "sys_phase_inv_aux hp_Idle          = ( (If sys_fA \<^bold>= sys_fM Then black_heap Else white_heap) \<^bold>\<and> no_grey_refs )"
| "sys_phase_inv_aux hp_IdleInit      = no_black_refs"
| "sys_phase_inv_aux hp_InitMark      = (sys_fA \<^bold>\<noteq> sys_fM \<^bold>\<longrightarrow> no_black_refs)"
| "sys_phase_inv_aux hp_Mark          = \<langle>True\<rangle>"
| "sys_phase_inv_aux hp_IdleMarkSweep = ( (sys_phase \<^bold>= \<langle>ph_Idle\<rangle> \<^bold>\<or> tso_pending_store gc (mw_Phase ph_Idle)) \<^bold>\<longrightarrow> no_grey_refs )"

abbreviation sys_phase_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "sys_phase_inv \<equiv> sys_phase_inv_aux \<^bold>$ sys_ghost_hs_phase"


subsubsection\<open>Writes to shared GC variables\<close>

text\<open>

Relate @{const "sys_ghost_hs_phase"}, @{const "gc_phase"},
@{const "sys_phase"} and writes to the phase in the GC's TSO buffer.

The first relation treats the case when the GC's TSO buffer does not
contain any writes to the phase.

The second relation exhibits the data race on the phase variable: we
need to precisely track the possible states of the GC's TSO buffer.

\<close>

definition handshake_phase_rel :: "hs_phase \<Rightarrow> bool \<Rightarrow> gc_phase \<Rightarrow> bool" where
  "handshake_phase_rel hp in_sync ph =
     (case hp of
       hp_Idle          \<Rightarrow> ph = ph_Idle
     | hp_IdleInit      \<Rightarrow> ph = ph_Idle \<or> (in_sync \<and> ph = ph_Init)
     | hp_InitMark      \<Rightarrow> ph = ph_Init \<or> (in_sync \<and> ph = ph_Mark)
     | hp_Mark          \<Rightarrow> ph = ph_Mark
     | hp_IdleMarkSweep \<Rightarrow> ph = ph_Mark \<or> (in_sync \<and> ph \<in> { ph_Idle, ph_Sweep }))"

definition phase_rel :: "(bool \<times> hs_phase \<times> gc_phase \<times> gc_phase \<times> ('field, 'payload, 'ref) mem_store_action list) set" where
  "phase_rel =
     ({ (in_sync, hp, ph, ph, []) |in_sync hp ph. handshake_phase_rel hp in_sync ph }
    \<union> ({True} \<times> { (hp_IdleInit, ph_Init, ph_Idle, [mw_Phase ph_Init]),
                  (hp_InitMark, ph_Mark, ph_Init, [mw_Phase ph_Mark]),
                  (hp_IdleMarkSweep, ph_Sweep, ph_Mark, [mw_Phase ph_Sweep]),
                  (hp_IdleMarkSweep, ph_Idle, ph_Mark, [mw_Phase ph_Sweep, mw_Phase ph_Idle]),
                  (hp_IdleMarkSweep, ph_Idle, ph_Sweep, [mw_Phase ph_Idle]) }))"

definition phase_rel_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "phase_rel_inv = ((\<^bold>\<forall>m. sys_ghost_hs_in_sync m) \<^bold>\<otimes> sys_ghost_hs_phase \<^bold>\<otimes> gc_phase \<^bold>\<otimes> sys_phase \<^bold>\<otimes> tso_pending_phase gc \<^bold>\<in> \<langle>phase_rel\<rangle>)"

text\<open>

Similarly we track the validity of @{const "sys_fM"} (respectively,
@{const "sys_fA"}) wrt @{const "gc_fM"} (@{const "sys_fA"}) and the
handshake phase. We also include the TSO lock to rule out the GC
having any pending marks during the @{const "hp_Idle"} handshake
phase.

\<close>

definition fM_rel :: "(bool \<times> hs_phase \<times> gc_mark \<times> gc_mark \<times> ('field, 'payload, 'ref) mem_store_action list \<times> bool) set" where
  "fM_rel =
      { (in_sync, hp, fM, fM, [], l) |fM hp in_sync l. hp = hp_Idle \<longrightarrow> \<not>in_sync }
    \<union> { (in_sync, hp_Idle, fM, fM', [], l) |fM fM' in_sync l. in_sync }
    \<union> { (in_sync, hp_Idle, \<not>fM, fM, [mw_fM (\<not>fM)], False) |fM in_sync. in_sync }"

definition fM_rel_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "fM_rel_inv = ((\<^bold>\<forall>m. sys_ghost_hs_in_sync m) \<^bold>\<otimes> sys_ghost_hs_phase \<^bold>\<otimes> gc_fM \<^bold>\<otimes> sys_fM \<^bold>\<otimes> tso_pending_fM gc \<^bold>\<otimes> (sys_mem_lock \<^bold>= \<langle>Some gc\<rangle>) \<^bold>\<in> \<langle>fM_rel\<rangle>)"

definition fA_rel :: "(bool \<times> hs_phase \<times> gc_mark \<times> gc_mark \<times> ('field, 'payload, 'ref) mem_store_action list) set" where
  "fA_rel =
      { (in_sync, hp_Idle,          fA,  fM, []) |fA fM in_sync. \<not>in_sync \<longrightarrow> fA = fM }
    \<union> { (in_sync, hp_IdleInit,      fA, \<not>fA, []) |fA in_sync. True }
    \<union> { (in_sync, hp_InitMark,      fA, \<not>fA, [mw_fA (\<not>fA)]) |fA in_sync. in_sync }
    \<union> { (in_sync, hp_InitMark,      fA,  fM, []) |fA fM in_sync. \<not>in_sync \<longrightarrow> fA \<noteq> fM }
    \<union> { (in_sync, hp_Mark,          fA,  fA, []) |fA in_sync. True }
    \<union> { (in_sync, hp_IdleMarkSweep, fA,  fA, []) |fA in_sync. True }"

definition fA_rel_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "fA_rel_inv = ((\<^bold>\<forall>m. sys_ghost_hs_in_sync m) \<^bold>\<otimes> sys_ghost_hs_phase \<^bold>\<otimes> sys_fA \<^bold>\<otimes> gc_fM \<^bold>\<otimes> tso_pending_fA gc \<^bold>\<in> \<langle>fA_rel\<rangle>)"


subsection\<open>Worklist invariants \label{def:valid_W_inv}\<close>

text\<open>

The worklists track the grey objects. The following invariant asserts
that grey objects are marked on the heap except for a few steps near
the end of @{const "mark_object_fn"}, the processes' worklists and
@{const "ghost_honorary_grey"}s are disjoint, and that pending marks
are sensible.

The safety of the collector does not to depend on disjointness; we
include it as proof that the single-threading of grey objects in the
implementation is sound.

Note that the phase invariants of \S\ref{sec:phase-invariants} limit
the scope of this invariant.

\<close>

definition valid_W_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "valid_W_inv =
    ((\<^bold>\<forall>p r. r in_W p \<^bold>\<or> (sys_mem_lock \<^bold>\<noteq> \<langle>Some p\<rangle> \<^bold>\<and> r in_ghost_honorary_grey p) \<^bold>\<longrightarrow> marked r)
  \<^bold>\<and> (\<^bold>\<forall>p q. \<langle>p \<noteq> q\<rangle> \<^bold>\<longrightarrow> WL p \<^bold>\<inter> WL q \<^bold>= \<langle>{}\<rangle>)
  \<^bold>\<and> (\<^bold>\<forall>p q r. \<^bold>\<not>(r in_ghost_honorary_grey p \<^bold>\<and> r in_W q))
  \<^bold>\<and> (EMPTY sys_ghost_honorary_grey)
  \<^bold>\<and> (\<^bold>\<forall>p r fl. tso_pending_store p (mw_Mark r fl)
       \<^bold>\<longrightarrow> \<langle>fl\<rangle> \<^bold>= sys_fM
         \<^bold>\<and> r in_ghost_honorary_grey p
         \<^bold>\<and> tso_locked_by p
         \<^bold>\<and> white r
         \<^bold>\<and> tso_pending_mark p \<^bold>= \<langle>[mw_Mark r fl]\<rangle> ))"


subsection\<open>Coarse invariants about the stores a process can issue\<close>

abbreviation gc_writes :: "('field, 'payload, 'ref) mem_store_action \<Rightarrow> bool" where
  "gc_writes w \<equiv> case w of mw_Mark _ _ \<Rightarrow> True | mw_Phase _ \<Rightarrow> True | mw_fM _ \<Rightarrow> True | mw_fA _ \<Rightarrow> True | _ \<Rightarrow> False"

abbreviation mut_writes :: "('field, 'payload, 'ref) mem_store_action \<Rightarrow> bool" where
  "mut_writes w \<equiv> case w of mw_Mutate _ _ _ \<Rightarrow> True | mw_Mark _ _ \<Rightarrow> True | _ \<Rightarrow> False"

definition tso_store_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "tso_store_inv =
    ((\<^bold>\<forall>w.   tso_pending_store gc          w \<^bold>\<longrightarrow> \<langle>gc_writes w\<rangle>)
   \<^bold>\<and> (\<^bold>\<forall>m w. tso_pending_store (mutator m) w \<^bold>\<longrightarrow> \<langle>mut_writes w\<rangle>))"


subsection\<open>The global invariants collected\<close>

definition invs :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "invs =
   (handshake_phase_inv
  \<^bold>\<and> phase_rel_inv
  \<^bold>\<and> strong_tricolour_inv
  \<^bold>\<and> sys_phase_inv
  \<^bold>\<and> tso_store_inv
  \<^bold>\<and> valid_refs_inv
  \<^bold>\<and> valid_W_inv
  \<^bold>\<and> mutators_phase_inv
  \<^bold>\<and> fA_rel_inv \<^bold>\<and> fM_rel_inv)"


subsection\<open>Initial conditions \label{sec:initial-conditions}\<close>

text\<open>

We ask that the GC and system initially agree on some things:
\begin{itemize}

\item All objects on the heap are marked (have their flags equal to
  @{const "sys_fM"}, and there are no grey references, i.e. the heap
  is uniformly black.

\item The GC and system have the same values for @{term "fA"}, @{term
  "fM"}, etc. and the phase is @{term "Idle"}.

\item No process holds the TSO lock and all write buffers are empty.

\item All root-reachable references are backed by objects.

\end{itemize}
Note that these are merely sufficient initial conditions and can be
weakened.

\<close>

locale gc_system =
  fixes initial_mark :: gc_mark
begin

definition gc_initial_state :: "('field, 'mut, 'payload, 'ref) lst_pred" where
  "gc_initial_state s =
    (fM s = initial_mark
   \<and> phase s = ph_Idle
   \<and> ghost_honorary_grey s = {}
   \<and> W s = {})"

definition mut_initial_state :: "('field, 'mut, 'payload, 'ref) lst_pred" where
  "mut_initial_state s =
    (ghost_hs_phase s = hp_IdleMarkSweep
   \<and> ghost_honorary_grey s = {}
   \<and> ghost_honorary_root s = {}
   \<and> W s = {})"

definition sys_initial_state :: "('field, 'mut, 'payload, 'ref) lst_pred" where
  "sys_initial_state s =
    ((\<forall>m. \<not>hs_pending s m \<and> ghost_hs_in_sync s m)
   \<and> ghost_hs_phase s = hp_IdleMarkSweep \<and> hs_type s = ht_GetRoots
   \<and> obj_mark ` ran (heap s) \<subseteq> {initial_mark}
   \<and> fA s = initial_mark
   \<and> fM s = initial_mark
   \<and> phase s = ph_Idle
   \<and> ghost_honorary_grey s = {}
   \<and> W s = {}
   \<and> (\<forall>p. mem_store_buffers s p = [])
   \<and> mem_lock s = None)"

abbreviation
  "root_reachable y \<equiv> \<^bold>\<exists>m x. \<langle>x\<rangle> \<^bold>\<in> mut_m.mut_roots m \<^bold>\<and> x reaches y"

definition valid_refs :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "valid_refs = (\<^bold>\<forall>y. root_reachable y \<^bold>\<longrightarrow> valid_ref y)"

definition gc_system_init :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "gc_system_init =
      ((\<lambda>s. gc_initial_state (s gc))
     \<^bold>\<and> (\<lambda>s. \<forall>m. mut_initial_state (s (mutator m)))
     \<^bold>\<and> (\<lambda>s. sys_initial_state (s sys))
     \<^bold>\<and> valid_refs)"

text\<open>

The system consists of the programs and these constraints on the initial state.

\<close>

abbreviation gc_system :: "('field, 'mut, 'payload, 'ref) gc_system" where
  "gc_system \<equiv> \<lparr>PGMs = gc_coms, INIT = gc_system_init, FAIR = \<langle>True\<rangle>\<rparr>" (* FIXME add fairness hypotheses *)

end

(*<*)

end
(*>*)
