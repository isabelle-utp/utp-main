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

theory Model
imports
  ConcurrentIMP.CIMP
  "HOL-Library.Sublist"
begin

(* From 40e16c534243 by Makarius. Doesn't seem to have a huge impact on run time now (2021-01-07) *)
declare subst_all [simp del] [[simproc del: defined_all]]

(*>*)
section\<open>A model of a Schism garbage collector \label{sec:gc-model}\<close>

text \<open>

The following formalises Figures~2.8 (\<open>mark_object_fn\<close>),
2.9 (load and store but not alloc), and 2.15 (garbage collector) of
@{cite [cite_macro=citet] "Pizlo201xPhd"}; see also @{cite
[cite_macro=citet] "Pizlo+2010PLDI"}.

We additionally need to model TSO memory, the handshakes and
compare-and-swap (\texttt{CAS}).  We closely model things where
interference is possible and abstract everything else.

@{bold \<open>@{emph \<open>NOTE\<close>}: this model is for TSO
\emph{only}. We elide any details irrelevant for that memory
model.\<close>}

We begin by defining the types of the various parts. Our program
locations are labelled with strings for readability. We enumerate the
names of the processes in our system. The safety proof treats an
arbitary (unbounded) number of mutators.

\<close>

type_synonym location = string

datatype 'mut process_name = mutator 'mut | gc | sys

text \<open>

The garbage collection process can be in one of the following phases.

\<close>

datatype gc_phase
  = ph_Idle
  | ph_Init
  | ph_Mark
  | ph_Sweep

text \<open>

The garbage collector instructs mutators to perform certain actions,
and blocks until the mutators signal these actions are done. The
mutators always respond with their work list (a set of
references). The handshake can be of one of the specified types.

\<close>

datatype hs_type
  = ht_NOOP
  | ht_GetRoots
  | ht_GetWork

text\<open>

We track how many \texttt{noop} and \texttt{get\_roots} handshakes
each process has participated in as ghost state. See
\S\ref{sec:gc_handshakes}.

\<close>

datatype hs_phase
  = hp_Idle \<comment> \<open>done 1 noop\<close>
  | hp_IdleInit
  | hp_InitMark
  | hp_Mark \<comment> \<open>done 4 noops\<close>
  | hp_IdleMarkSweep \<comment> \<open>done get roots\<close>

definition
  hs_step :: "hs_phase \<Rightarrow> hs_phase"
where
  "hs_step ph = (case ph of
       hp_Idle          \<Rightarrow> hp_IdleInit
     | hp_IdleInit      \<Rightarrow> hp_InitMark
     | hp_InitMark      \<Rightarrow> hp_Mark
     | hp_Mark          \<Rightarrow> hp_IdleMarkSweep
     | hp_IdleMarkSweep \<Rightarrow> hp_Idle)"

text \<open>

An object consists of a garbage collection mark and two partial
maps. Firstly the types:

\<^item> @{typ "'field"} is the abstract type of fields.
\<^item> @{typ "'ref"} is the abstract type of object references.
\<^item> @{typ "'mut"} is the abstract type of the mutators' names.

The maps:

\<^item> \<open>obj_fields\<close> maps @{typ "'field"}s to object
  references (or @{const "None"} signifying \texttt{NULL} or type
  error).
\<^item> \<open>obj_payload\<close> maps a @{typ "'field"} to non-reference
  data. For convenience we similarly allow that to be \texttt{NULL}.

\<close>

type_synonym gc_mark = bool

record ('field, 'payload, 'ref) object =
  obj_mark :: "gc_mark"
  obj_fields :: "'field \<rightharpoonup> 'ref"
  obj_payload :: "'field \<rightharpoonup> 'payload"

text\<open>

The TSO store buffers track store actions, represented by \<open>('field, 'ref) mem_store_action\<close>.

\<close>

datatype ('field, 'payload, 'ref) mem_store_action
  = mw_Mark 'ref gc_mark
  | mw_Mutate 'ref 'field "'ref option"
  | mw_Mutate_Payload 'ref 'field "'payload option"
  | mw_fA gc_mark
  | mw_fM gc_mark
  | mw_Phase gc_phase

text\<open>

An action is a request by a mutator or the garbage collector to the
system.

\<close>

datatype ('field, 'ref) mem_load_action
  = mr_Ref 'ref 'field
  | mr_Payload 'ref 'field
  | mr_Mark 'ref
  | mr_Phase
  | mr_fM
  | mr_fA

datatype ('field, 'mut, 'payload, 'ref) request_op
  = ro_MFENCE
  | ro_Load "('field, 'ref) mem_load_action"
  | ro_Store "('field, 'payload, 'ref) mem_store_action"
  | ro_Lock
  | ro_Unlock
  | ro_Alloc
  | ro_Free 'ref
  | ro_hs_gc_load_pending 'mut
  | ro_hs_gc_store_type hs_type
  | ro_hs_gc_store_pending 'mut
  | ro_hs_gc_load_W
  | ro_hs_mut_load_pending
  | ro_hs_mut_load_type
  | ro_hs_mut_done "'ref set"

abbreviation "LoadfM \<equiv> ro_Load mr_fM"
abbreviation "LoadMark r \<equiv> ro_Load (mr_Mark r)"
abbreviation "LoadPayload r f \<equiv> ro_Load (mr_Payload r f)"
abbreviation "LoadPhase \<equiv> ro_Load mr_Phase"
abbreviation "LoadRef r f \<equiv> ro_Load (mr_Ref r f)"

abbreviation "StorefA m \<equiv> ro_Store (mw_fA m)"
abbreviation "StorefM m \<equiv> ro_Store (mw_fM m)"
abbreviation "StoreMark r m \<equiv> ro_Store (mw_Mark r m)"
abbreviation "StorePayload r f pl \<equiv> ro_Store (mw_Mutate_Payload r f pl)"
abbreviation "StorePhase ph \<equiv> ro_Store (mw_Phase ph)"
abbreviation "StoreRef r f r' \<equiv> ro_Store (mw_Mutate r f r')"

type_synonym ('field, 'mut, 'payload, 'ref) request
  = "'mut process_name \<times> ('field, 'mut, 'payload, 'ref) request_op"

datatype ('field, 'payload, 'ref) response
  = mv_Bool "bool"
  | mv_Mark "gc_mark option"
  | mv_Payload "'payload option" \<comment>\<open> the requested reference might be invalid \<close>
  | mv_Phase "gc_phase"
  | mv_Ref "'ref option"
  | mv_Refs "'ref set"
  | mv_Void
  | mv_hs_type hs_type

text\<open>

The following record is the type of all processes's local states. For
the mutators and the garbage collector, consider these to be local
variables or registers.

The system's \<open>fA\<close>, \<open>fM\<close>, \<open>phase\<close> and \<open>heap\<close> variables are subject to the TSO memory model, as are all heap
operations.

\<close>

record ('field, 'mut, 'payload, 'ref) local_state =
  \<comment> \<open>System-specific fields\<close>
  heap :: "'ref \<rightharpoonup> ('field, 'payload, 'ref) object"
  \<comment> \<open>TSO memory state\<close>
  mem_store_buffers :: "'mut process_name \<Rightarrow> ('field, 'payload, 'ref) mem_store_action list"
  mem_lock :: "'mut process_name option"
  \<comment> \<open>Handshake state\<close>
  hs_pending :: "'mut \<Rightarrow> bool"
  \<comment> \<open>Ghost state\<close>
  ghost_hs_in_sync :: "'mut \<Rightarrow> bool"
  ghost_hs_phase :: "hs_phase"

  \<comment> \<open>Mutator-specific temporaries\<close>
  new_ref :: "'ref option"
  roots :: "'ref set"
  ghost_honorary_root :: "'ref set"
  payload_value :: "'payload option"
  mutator_data :: "'field \<rightharpoonup> 'payload"
  mutator_hs_pending :: "bool"

  \<comment> \<open>Garbage collector-specific temporaries\<close>
  field_set :: "'field set"
  mut :: "'mut"
  muts :: "'mut set"

  \<comment> \<open>Local variables used by multiple processes\<close>
  fA :: "gc_mark"
  fM :: "gc_mark"
  cas_mark :: "gc_mark option"
  field :: "'field"
  mark :: "gc_mark option"
  phase :: "gc_phase"
  tmp_ref :: "'ref"
  ref :: "'ref option"
  refs :: "'ref set"
  W :: "'ref set"
  \<comment> \<open>Handshake state\<close>
  hs_type :: "hs_type"
  \<comment> \<open>Ghost state\<close>
  ghost_honorary_grey :: "'ref set"

text\<open>We instantiate CIMP's types as follows:\<close>

type_synonym ('field, 'mut, 'payload, 'ref) gc_com
  = "(('field, 'payload, 'ref) response, location, ('field, 'mut, 'payload, 'ref) request, ('field, 'mut, 'payload, 'ref) local_state) com"
type_synonym ('field, 'mut, 'payload, 'ref) gc_loc_comp
  = "(('field, 'payload, 'ref) response, location, ('field, 'mut, 'payload, 'ref) request, ('field, 'mut, 'payload, 'ref) local_state) loc_comp"
type_synonym ('field, 'mut, 'payload, 'ref) gc_pred
  = "(('field, 'payload, 'ref) response, location, 'mut process_name, ('field, 'mut, 'payload, 'ref) request, ('field, 'mut, 'payload, 'ref) local_state) state_pred"
type_synonym ('field, 'mut, 'payload, 'ref) gc_system
  = "(('field, 'payload, 'ref) response, location, 'mut process_name, ('field, 'mut, 'payload, 'ref) request, ('field, 'mut, 'payload, 'ref) local_state) system"

type_synonym ('field, 'mut, 'payload, 'ref) gc_event
  = "('field, 'mut, 'payload, 'ref) request \<times> ('field, 'payload, 'ref) response"
type_synonym ('field, 'mut, 'payload, 'ref) gc_history
  = "('field, 'mut, 'payload, 'ref) gc_event list"

type_synonym ('field, 'mut, 'payload, 'ref) lst_pred
  = "('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> bool"

type_synonym ('field, 'mut, 'payload, 'ref) lsts
  = "'mut process_name \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state"

type_synonym ('field, 'mut, 'payload, 'ref) lsts_pred
  = "('field, 'mut, 'payload, 'ref) lsts \<Rightarrow> bool"

text\<open>

We use one locale per process to define a namespace for definitions
local to these processes. Mutator definitions are parametrised by the
mutator's identifier \<open>m\<close>. We never interpret these locales; we
typically use their contents by prefixing identifiers with the locale
name. This might be considered an abuse. The attributes depend on
locale scoping somewhat, which is a mixed blessing.

If we have more than one mutator then we need to show that mutators do
not mutually interfere. To that end we define an extra locale that
contains these proofs.

\<close>

locale mut_m = fixes m :: "'mut"
locale mut_m' = mut_m + fixes m' :: "'mut" assumes mm'[iff]: "m \<noteq> m'"
locale gc
locale sys


subsection\<open>Object marking \label{sec:gc-marking}\<close>

text\<open>

Both the mutators and the garbage collector mark references, which
indicates that a reference is live in the current round of
collection. This operation is defined in @{cite [cite_macro=citet]
\<open>Figure~2.8\<close> "Pizlo201xPhd"}. These definitions are
parameterised by the name of the process.

\<close>

context
  fixes p :: "'mut process_name"
begin

abbreviation lock_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" where
  "lock_syn l \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (p, ro_Lock)) (\<lambda>_ s. {s})"
notation lock_syn ("\<lbrace>_\<rbrace> lock")

abbreviation unlock_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" where
  "unlock_syn l \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (p, ro_Unlock)) (\<lambda>_ s. {s})"
notation unlock_syn ("\<lbrace>_\<rbrace> unlock")

abbreviation
  load_mark_syn :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref)
              \<Rightarrow> ((gc_mark option \<Rightarrow> gc_mark option)
                 \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state
                 \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "load_mark_syn l r upd \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (p, LoadMark (r s))) (\<lambda>mv s. { upd \<langle>m\<rangle> s |m. mv = mv_Mark m })"
notation load_mark_syn ("\<lbrace>_\<rbrace> load'_mark")

abbreviation load_fM_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" where
  "load_fM_syn l \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (p, ro_Load mr_fM)) (\<lambda>mv s. { s\<lparr>fM := m\<rparr> |m. mv = mv_Mark (Some m) })"
notation load_fM_syn ("\<lbrace>_\<rbrace> load'_fM")

abbreviation
  load_phase :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "load_phase l \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (p, LoadPhase)) (\<lambda>mv s. { s\<lparr>phase := ph\<rparr> |ph. mv = mv_Phase ph })"
notation load_phase ("\<lbrace>_\<rbrace> load'_phase")

abbreviation
  store_mark_syn :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref) \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> bool) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "store_mark_syn l r fl \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (p, StoreMark (r s) (fl s))) (\<lambda>_ s. { s\<lparr> ghost_honorary_grey := {r s} \<rparr> })"
notation store_mark_syn ("\<lbrace>_\<rbrace> store'_mark")

abbreviation
  add_to_W_syn :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "add_to_W_syn l r \<equiv> \<lbrace>l\<rbrace> \<lfloor>\<lambda>s. s\<lparr> W := W s \<union> {r s}, ghost_honorary_grey := {} \<rparr>\<rfloor>"
notation add_to_W_syn ("\<lbrace>_\<rbrace> add'_to'_W")

text\<open>

The reference we're marking is given in @{const "ref"}. If the current
process wins the \texttt{CAS} race then the reference is marked and
added to the local work list @{const "W"}.

TSO means we cannot avoid having the mark store pending in a store
buffer; in other words, we cannot have objects atomically transition
from white to grey. The following scheme blackens a white object, and
then reverts it to grey. The @{const "ghost_honorary_grey"} variable
is used to track objects undergoing this transition.

As CIMP provides no support for function calls, we prefix each
statement's label with a string from its callsite.

\<close>

definition
  mark_object_fn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "mark_object_fn l =
     \<lbrace>l @ ''_mo_null''\<rbrace> IF \<^bold>\<not> (NULL ref) THEN
       \<lbrace>l @ ''_mo_mark''\<rbrace> load_mark (the \<circ> ref) mark_update ;;
       \<lbrace>l @ ''_mo_fM''\<rbrace> load_fM ;;
       \<lbrace>l @ ''_mo_mtest''\<rbrace> IF mark \<^bold>\<noteq> Some \<circ> fM THEN
         \<lbrace>l @ ''_mo_phase''\<rbrace> load_phase ;;
         \<lbrace>l @ ''_mo_ptest''\<rbrace> IF phase \<^bold>\<noteq> \<langle>ph_Idle\<rangle> THEN
           \<comment> \<open>CAS: claim object\<close>
           \<lbrace>l @ ''_mo_co_lock''\<rbrace> lock ;;
           \<lbrace>l @ ''_mo_co_cmark''\<rbrace> load_mark (the \<circ> ref) cas_mark_update ;;
           \<lbrace>l @ ''_mo_co_ctest''\<rbrace> IF cas_mark \<^bold>= mark THEN
             \<lbrace>l @ ''_mo_co_mark''\<rbrace> store_mark (the \<circ> ref) fM
           FI ;;
           \<lbrace>l @ ''_mo_co_unlock''\<rbrace> unlock ;;
           \<lbrace>l @ ''_mo_co_won''\<rbrace> IF cas_mark \<^bold>= mark THEN
             \<lbrace>l @ ''_mo_co_W''\<rbrace> add_to_W (the \<circ> ref)
           FI
         FI
       FI
     FI"

end

text\<open>

The worklists (field @{term "W"}) are not subject to TSO. As we later
show (\S\ref{def:valid_W_inv}), these are disjoint and hence
operations on these are private to each process, with the sole
exception of when the GC requests them from the mutators. We describe
that mechanism next.

\<close>

subsection\<open>Handshakes \label{sec:gc_handshakes}\<close>

text\<open>

The garbage collector needs to synchronise with the mutators.
Here we do so by having the GC busy-wait: it sets a \<open>pending\<close> flag for each mutator
and then waits for each to respond.

The system side of the interface collects the responses from the
mutators into a single worklist, which acts as a proxy for the garbage
collector's local worklist during \<open>get_roots\<close> and \<open>get_work\<close> handshakes.
We carefully model the effect these handshakes have on the processes' TSO buffers.

The system and mutators track handshake phases using ghost state; see
\S\ref{sec:phase-invariants}.

The handshake type and handshake pending bit are not subject to TSO as we expect
a realistic implementation of handshakes would involve synchronisation.

\<close>

abbreviation hp_step :: "hs_type \<Rightarrow> hs_phase \<Rightarrow> hs_phase" where
  "hp_step ht \<equiv>
     case ht of
         ht_NOOP \<Rightarrow> hs_step
       | ht_GetRoots \<Rightarrow> hs_step
       | ht_GetWork \<Rightarrow> id"

context sys
begin

definition
  handshake :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "handshake =
     \<lbrace>''sys_hs_gc_set_type''\<rbrace> Response
        (\<lambda>req s. { (s\<lparr> hs_type := ht,
                       ghost_hs_in_sync := \<langle>False\<rangle>,
                       ghost_hs_phase := hp_step ht (ghost_hs_phase s) \<rparr>,
                    mv_Void)
                 |ht. req = (gc, ro_hs_gc_store_type ht) })
   \<oplus> \<lbrace>''sys_hs_gc_mut_reqs''\<rbrace> Response
        (\<lambda>req s. { (s\<lparr> hs_pending := (hs_pending s)(m := True) \<rparr>, mv_Void)
                 |m. req = (gc, ro_hs_gc_store_pending m) })
   \<oplus> \<lbrace>''sys_hs_gc_done''\<rbrace> Response
        (\<lambda>req s. { (s, mv_Bool (\<not>hs_pending s m))
                 |m. req = (gc, ro_hs_gc_load_pending m) })
   \<oplus> \<lbrace>''sys_hs_gc_load_W''\<rbrace> Response
        (\<lambda>req s. { (s\<lparr> W := {} \<rparr>, mv_Refs (W s))
                 |_::unit. req = (gc, ro_hs_gc_load_W) })
   \<oplus> \<lbrace>''sys_hs_mut_pending''\<rbrace> Response
        (\<lambda>req s. { (s, mv_Bool (hs_pending s m))
                 |m. req = (mutator m, ro_hs_mut_load_pending) })
   \<oplus> \<lbrace>''sys_hs_mut''\<rbrace> Response
        (\<lambda>req s. { (s, mv_hs_type (hs_type s))
                 |m. req = (mutator m, ro_hs_mut_load_type) })
   \<oplus> \<lbrace>''sys_hs_mut_done''\<rbrace> Response
        (\<lambda>req s. { (s\<lparr> hs_pending := (hs_pending s)(m := False),
                       W := W s \<union> W',
                       ghost_hs_in_sync := (ghost_hs_in_sync s)(m := True) \<rparr>,
                    mv_Void)
                 |m W'. req = (mutator m, ro_hs_mut_done W') })"

end

text\<open>

The mutators' side of the interface. Also updates the ghost state
tracking the handshake state for @{const "ht_NOOP"} and @{const
"ht_GetRoots"} but not @{const "ht_GetWork"}.

Again we could make these subject to TSO, but that would be over specification.

\<close>

context mut_m
begin

abbreviation mark_object_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> mark'_object" [0] 71) where
  "\<lbrace>l\<rbrace> mark_object \<equiv> mark_object_fn (mutator m) l"

abbreviation mfence_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> MFENCE" [0] 71) where
  "\<lbrace>l\<rbrace> MFENCE \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, ro_MFENCE)) (\<lambda>_ s. {s})"

abbreviation hs_load_pending_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> hs'_load'_pending'_" [0] 71) where
  "\<lbrace>l\<rbrace> hs_load_pending_ \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, ro_hs_mut_load_pending)) (\<lambda>mv s. { s\<lparr> mutator_hs_pending := b \<rparr> |b. mv = mv_Bool b })"

abbreviation hs_load_type_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> hs'_load'_type" [0] 71) where
  "\<lbrace>l\<rbrace> hs_load_type \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, ro_hs_mut_load_type)) (\<lambda>mv s. { s\<lparr> hs_type := ht \<rparr> |ht. mv = mv_hs_type ht})"

abbreviation hs_noop_done_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> hs'_noop'_done'_") where
  "\<lbrace>l\<rbrace> hs_noop_done_ \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, ro_hs_mut_done {}))
                                   (\<lambda>_ s. {s\<lparr> ghost_hs_phase := hs_step (ghost_hs_phase s) \<rparr>})"

abbreviation hs_get_roots_done_syn :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref set) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> hs'_get'_roots'_done'_")  where
  "\<lbrace>l\<rbrace> hs_get_roots_done_ wl \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, ro_hs_mut_done (wl s)))
                                           (\<lambda>_ s. {s\<lparr> W := {}, ghost_hs_phase := hs_step (ghost_hs_phase s) \<rparr>})"

abbreviation hs_get_work_done_syn :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref set) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> hs'_get'_work'_done")  where
  "\<lbrace>l\<rbrace> hs_get_work_done wl \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, ro_hs_mut_done (wl s)))
                                         (\<lambda>_ s. {s\<lparr> W := {} \<rparr>})"

definition
  handshake :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "handshake =
      \<lbrace>''hs_load_pending''\<rbrace> hs_load_pending_ ;;
      \<lbrace>''hs_pending''\<rbrace> IF mutator_hs_pending
      THEN
        \<lbrace>''hs_mfence''\<rbrace> MFENCE ;;
        \<lbrace>''hs_load_ht''\<rbrace> hs_load_type ;;
        \<lbrace>''hs_noop''\<rbrace> IF hs_type \<^bold>= \<langle>ht_NOOP\<rangle>
        THEN
          \<lbrace>''hs_noop_done''\<rbrace> hs_noop_done_
        ELSE \<lbrace>''hs_get_roots''\<rbrace> IF hs_type \<^bold>= \<langle>ht_GetRoots\<rangle>
        THEN
          \<lbrace>''hs_get_roots_refs''\<rbrace> \<acute>refs := \<acute>roots ;;
          \<lbrace>''hs_get_roots_loop''\<rbrace> WHILE \<^bold>\<not>EMPTY refs DO
            \<lbrace>''hs_get_roots_loop_choose_ref''\<rbrace> \<acute>ref :\<in> Some ` \<acute>refs ;;
            \<lbrace>''hs_get_roots_loop''\<rbrace> mark_object ;;
            \<lbrace>''hs_get_roots_loop_done''\<rbrace> \<acute>refs := (\<acute>refs - {the \<acute>ref})
          OD ;;
          \<lbrace>''hs_get_roots_done''\<rbrace> hs_get_roots_done_ W
        ELSE \<lbrace>''hs_get_work''\<rbrace> IF hs_type \<^bold>= \<langle>ht_GetWork\<rangle>
        THEN
          \<lbrace>''hs_get_work_done''\<rbrace> hs_get_work_done W
        FI FI FI
      FI"

end

text\<open>

The garbage collector's side of the interface.

\<close>

context gc
begin

abbreviation set_hs_type :: "location \<Rightarrow> hs_type \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> set'_hs'_type")  where
  "\<lbrace>l\<rbrace> set_hs_type ht \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, ro_hs_gc_store_type ht)) (\<lambda>_ s. {s})"

abbreviation set_hs_pending :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'mut) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> set'_hs'_pending")  where
  "\<lbrace>l\<rbrace> set_hs_pending m \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, ro_hs_gc_store_pending (m s))) (\<lambda>_ s. {s})"

abbreviation load_W :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> load'_W") where
  "\<lbrace>l\<rbrace> load_W \<equiv> \<lbrace>l @ ''_load_W''\<rbrace> Request (\<lambda>s. (gc, ro_hs_gc_load_W))
                                          (\<lambda>resp s. {s\<lparr>W := W'\<rparr> |W'. resp = mv_Refs W'})"

abbreviation mfence :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> MFENCE")  where
  "\<lbrace>l\<rbrace> MFENCE \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, ro_MFENCE)) (\<lambda>_ s. {s})"

definition
  handshake_init :: "location \<Rightarrow> hs_type \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> handshake'_init")
where
  "\<lbrace>l\<rbrace> handshake_init req =
     \<lbrace>l @ ''_init_type''\<rbrace> set_hs_type req ;;
     \<lbrace>l @ ''_init_muts''\<rbrace> \<acute>muts := UNIV ;;
     \<lbrace>l @ ''_init_loop''\<rbrace> WHILE \<^bold>\<not> (EMPTY muts) DO
       \<lbrace>l @ ''_init_loop_choose_mut''\<rbrace> \<acute>mut :\<in> \<acute>muts ;;
       \<lbrace>l @ ''_init_loop_set_pending''\<rbrace> set_hs_pending mut ;;
       \<lbrace>l @ ''_init_loop_done''\<rbrace> \<acute>muts := (\<acute>muts - {\<acute>mut})
     OD"

definition
  handshake_done :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> handshake'_done")
where
  "\<lbrace>l\<rbrace> handshake_done =
     \<lbrace>l @ ''_done_muts''\<rbrace> \<acute>muts := UNIV ;;
     \<lbrace>l @ ''_done_loop''\<rbrace> WHILE \<^bold>\<not>EMPTY muts DO
       \<lbrace>l @ ''_done_loop_choose_mut''\<rbrace> \<acute>mut :\<in> \<acute>muts ;;
       \<lbrace>l @ ''_done_loop_rendezvous''\<rbrace> Request
               (\<lambda>s. (gc, ro_hs_gc_load_pending (mut s)))
               (\<lambda>mv s. { s\<lparr> muts := muts s - { mut s |done. mv = mv_Bool done \<and> done } \<rparr>})
     OD"

definition
  handshake_noop :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> handshake'_noop")
where
  "\<lbrace>l\<rbrace> handshake_noop =
         \<lbrace>l @ ''_mfence''\<rbrace> MFENCE ;;
         \<lbrace>l\<rbrace> handshake_init ht_NOOP ;;
         \<lbrace>l\<rbrace> handshake_done"

definition
  handshake_get_roots :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> handshake'_get'_roots")
where
  "\<lbrace>l\<rbrace> handshake_get_roots =
         \<lbrace>l\<rbrace> handshake_init ht_GetRoots ;;
         \<lbrace>l\<rbrace> handshake_done ;;
         \<lbrace>l\<rbrace> load_W"

definition
  handshake_get_work :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> handshake'_get'_work")
where
  "\<lbrace>l\<rbrace> handshake_get_work =
         \<lbrace>l\<rbrace> handshake_init ht_GetWork ;;
         \<lbrace>l\<rbrace> handshake_done ;;
         \<lbrace>l\<rbrace> load_W"

end


subsection\<open>The system process\<close>

text \<open>

The system process models the environment in which the garbage
collector and mutators execute.  We translate the x86-TSO memory model
due to @{cite [cite_macro=citet] "DBLP:journals/cacm/SewellSONM10"}
into a CIMP process. It is a reactive system: it receives requests and
returns values, but initiates no communication itself. It can,
however, autonomously commit a store pending in a TSO store buffer.

The memory bus can be locked by atomic compare-and-swap (\texttt{CAS})
instructions (and others in general). A processor is not blocked
(i.e., it can read from memory) when it holds the lock, or no-one
does.

\<close>

definition
  not_blocked :: "('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'mut process_name \<Rightarrow> bool"
where
  "not_blocked s p = (case mem_lock s of None \<Rightarrow> True | Some p' \<Rightarrow> p = p')"

text\<open>

We compute the view a processor has of memory by applying all its
pending stores.

\<close>

definition
  do_store_action :: "('field, 'payload, 'ref) mem_store_action \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state"
where
  "do_store_action wact =
     (\<lambda>s. case wact of
       mw_Mark r gc_mark    \<Rightarrow> s\<lparr>heap := (heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_mark := gc_mark\<rparr>) (heap s r))\<rparr>
     | mw_Mutate r f new_r  \<Rightarrow> s\<lparr>heap := (heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := new_r) \<rparr>) (heap s r))\<rparr>
     | mw_Mutate_Payload r f pl \<Rightarrow> s\<lparr>heap := (heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_payload := (obj_payload obj)(f := pl) \<rparr>) (heap s r))\<rparr>
     | mw_fM gc_mark        \<Rightarrow> s\<lparr>fM := gc_mark\<rparr>
     | mw_fA gc_mark        \<Rightarrow> s\<lparr>fA := gc_mark\<rparr>
     | mw_Phase gc_phase    \<Rightarrow> s\<lparr>phase := gc_phase\<rparr>)"

definition
  fold_stores :: "('field, 'payload, 'ref) mem_store_action list \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state"
where
  "fold_stores ws = fold (\<lambda>w. (\<circ>) (do_store_action w)) ws id"

abbreviation
  processors_view_of_memory :: "'mut process_name \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state"
where
  "processors_view_of_memory p s \<equiv> fold_stores (mem_store_buffers s p) s"

definition
  do_load_action :: "('field, 'ref) mem_load_action
                   \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state
                   \<Rightarrow> ('field, 'payload, 'ref) response"
where
  "do_load_action ract =
     (\<lambda>s. case ract of
       mr_Ref r f \<Rightarrow> mv_Ref (Option.bind (heap s r) (\<lambda>obj. obj_fields obj f))
     | mr_Payload r f \<Rightarrow> mv_Payload (Option.bind (heap s r) (\<lambda>obj. obj_payload obj f))
     | mr_Mark r  \<Rightarrow> mv_Mark (map_option obj_mark (heap s r))
     | mr_Phase   \<Rightarrow> mv_Phase (phase s)
     | mr_fM      \<Rightarrow> mv_Mark (Some (fM s))
     | mr_fA      \<Rightarrow> mv_Mark (Some (fA s)))"

definition
  sys_load :: "'mut process_name
              \<Rightarrow> ('field, 'ref) mem_load_action
              \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state
              \<Rightarrow> ('field, 'payload, 'ref) response"
where
  "sys_load p ract = do_load_action ract \<circ> processors_view_of_memory p"

context sys
begin

text\<open>

The semantics of TSO memory following @{cite [cite_macro=citet]
\<open>\S3\<close> "DBLP:journals/cacm/SewellSONM10"}. This differs
from the earlier @{cite [cite_macro=citet]
"DBLP:conf/tphol/OwensSS09"} by allowing the TSO lock to be taken by a
process with a non-empty store buffer. We omit their treatment of
registers; these are handled by the local states of the other
processes. The system can autonomously take the oldest store in the
store buffer for processor \<open>p\<close> and commit it to memory,
provided \<open>p\<close> either holds the lock or no processor does.

\<close>

definition
  mem_TSO :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "mem_TSO =
        \<lbrace>''tso_load''\<rbrace> Response (\<lambda>req s. { (s, sys_load p mr s)
                                         |p mr. req = (p, ro_Load mr) \<and> not_blocked s p })
      \<oplus> \<lbrace>''tso_store''\<rbrace> Response (\<lambda>req s. { (s\<lparr> mem_store_buffers := (mem_store_buffers s)(p := mem_store_buffers s p @ [w]) \<rparr>, mv_Void)
                                          |p w. req = (p, ro_Store w) })
      \<oplus> \<lbrace>''tso_mfence''\<rbrace> Response (\<lambda>req s. { (s, mv_Void)
                                           |p. req = (p, ro_MFENCE) \<and> mem_store_buffers s p = [] })
      \<oplus> \<lbrace>''tso_lock''\<rbrace> Response (\<lambda>req s. { (s\<lparr> mem_lock := Some p \<rparr>, mv_Void)
                                         |p. req = (p, ro_Lock) \<and> mem_lock s = None })
      \<oplus> \<lbrace>''tso_unlock''\<rbrace> Response (\<lambda>req s. { (s\<lparr> mem_lock := None \<rparr>, mv_Void)
                                         |p. req = (p, ro_Unlock) \<and> mem_lock s = Some p \<and> mem_store_buffers s p = [] })
      \<oplus> \<lbrace>''tso_dequeue_store_buffer''\<rbrace> LocalOp (\<lambda>s. { (do_store_action w s)\<lparr> mem_store_buffers := (mem_store_buffers s)(p := ws) \<rparr>
                                                    | p w ws. mem_store_buffers s p = w # ws \<and> not_blocked s p \<and> p \<noteq> sys })"

text\<open>

We track which references are allocated using the domain of @{const
"heap"}.

\label{sec:sys_alloc}

For now we assume that the system process magically allocates and
deallocates references.

We also arrange for the object to be marked atomically (see
\S\ref{sec:mut_alloc}) which morally should be done by the mutator. In
practice allocation pools enable this kind of atomicity (wrt the sweep
loop in the GC described in \S\ref{sec:gc-model-gc}).

Note that the \texttt{abort} in @{cite [cite_macro=citet]
\<open>Figure~2.9: Alloc\<close> "Pizlo201xPhd"} means the atomic
fails and the mutator can revert to activity outside of
\texttt{Alloc}, avoiding deadlock. We instead signal the exhaustion of
the heap explicitly, i.e., the @{const "ro_Alloc"} action cannot fail.

\<close>

definition
  alloc :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "alloc = \<lbrace>''alloc''\<rbrace> Response (\<lambda>req s.
      if dom (heap s) = UNIV
      then {(s, mv_Ref None) |_::unit. snd req = ro_Alloc }
      else { ( s\<lparr> heap := (heap s)(r := Some \<lparr> obj_mark = fA s, obj_fields = Map.empty, obj_payload = Map.empty \<rparr>) \<rparr>, mv_Ref (Some r) )
           |r. r \<notin> dom (heap s) \<and> snd req = ro_Alloc })"

text\<open>

References are freed by removing them from @{const "heap"}.

\<close>

definition
  free :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "free = \<lbrace>''sys_free''\<rbrace> Response (\<lambda>req s.
      { (s\<lparr>heap := (heap s)(r := None)\<rparr>, mv_Void) |r. snd req = ro_Free r })"

text\<open>

The top-level system process.

\<close>

definition
  com :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "com =
    LOOP DO
        mem_TSO
      \<oplus> alloc
      \<oplus> free
      \<oplus> handshake
    OD"

end


subsection\<open>Mutators\<close>

text\<open>

The mutators need to cooperate with the garbage collector. In
particular, when the garbage collector is not idle the mutators use a
\emph{write barrier} (see \S\ref{sec:gc-marking}).

The local state for each mutator tracks a working set of references,
which abstracts from how the process's registers and stack are
traversed to discover roots.

\<close>

context mut_m
begin

text\<open>

\label{sec:mut_alloc}

Allocation is defined in @{cite [cite_macro=citet]
\<open>Figure~2.9\<close> "Pizlo201xPhd"}. See \S\ref{sec:sys_alloc}
for how we abstract it.

\<close>

abbreviation alloc :: "('field, 'mut, 'payload, 'ref) gc_com" where
  "alloc \<equiv>
    \<lbrace>''alloc''\<rbrace> Request (\<lambda>s. (mutator m, ro_Alloc))
                        (\<lambda>mv s. { s\<lparr> roots := roots s \<union> set_option opt_r \<rparr> |opt_r. mv = mv_Ref opt_r })"

text\<open>

The mutator can always discard any references it holds.

\<close>

abbreviation discard :: "('field, 'mut, 'payload, 'ref) gc_com" where
  "discard \<equiv>
    \<lbrace>''discard_refs''\<rbrace> LocalOp (\<lambda>s. { s\<lparr> roots := roots' \<rparr> |roots'. roots' \<subseteq> roots s })"

text\<open>

Load and store are defined in @{cite [cite_macro=citet]
\<open>Figure~2.9\<close> "Pizlo201xPhd"}.

Dereferencing a reference can increase the set of mutator roots.

\<close>

abbreviation load :: "('field, 'mut, 'payload, 'ref) gc_com" where
  "load \<equiv>
    \<lbrace>''mut_load_choose''\<rbrace> LocalOp (\<lambda>s. { s\<lparr> tmp_ref := r, field := f \<rparr> |r f. r \<in> roots s }) ;;
    \<lbrace>''mut_load''\<rbrace> Request (\<lambda>s. (mutator m, LoadRef (tmp_ref s) (field s)))
                           (\<lambda>mv s. { s\<lparr> roots := roots s \<union> set_option r \<rparr>
                                   |r. mv = mv_Ref r })"

text\<open>

\label{sec:write-barriers}

Storing a reference involves marking both the old and new references,
i.e., both \emph{insertion} and \emph{deletion} barriers are
installed. The deletion barrier preserves the \emph{weak tricolour
invariant}, and the insertion barrier preserves the \emph{strong
tricolour invariant}; see \S\ref{sec:strong-tricolour-invariant} for
further discussion.

Note that the the mutator reads the overwritten reference but does not
store it in its roots.

\<close>

abbreviation
  mut_deref :: "location
          \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref)
          \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'field)
          \<Rightarrow> (('ref option \<Rightarrow> 'ref option) \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> deref")
where
  "\<lbrace>l\<rbrace> deref r f upd \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, LoadRef (r s) (f s)))
                                   (\<lambda>mv s. { upd \<langle>opt_r'\<rangle> (s\<lparr>ghost_honorary_root := set_option opt_r'\<rparr>) |opt_r'. mv = mv_Ref opt_r' })"

(*
Does not work in local theory mode:

syntax
  "_mut_fassign" :: "location \<Rightarrow> idt \<Rightarrow> 'ref \<Rightarrow> 'field \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> \<acute>_ := \<acute>_ \<rightarrow> _" [0, 0, 70] 71)
translations
  "\<lbrace>l\<rbrace> \<acute>q := \<acute>r\<rightarrow>f"    => "CONST mut_deref l r \<guillemotleft>f\<guillemotright> (_update_name q)"

 \<acute>ref := \<acute>tmp_ref\<rightarrow>\<acute>field ;;
*)

abbreviation
  store_ref :: "location
              \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref)
              \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'field)
              \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref option)
              \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> store'_ref")
where
  "\<lbrace>l\<rbrace> store_ref r f r' \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (mutator m, StoreRef (r s) (f s) (r' s))) (\<lambda>_ s. {s\<lparr>ghost_honorary_root := {}\<rparr>})"

definition
  store :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "store =
     \<comment> \<open>Choose vars for \<open>ref\<rightarrow>field := new_ref\<close>\<close>
     \<lbrace>''store_choose''\<rbrace> LocalOp (\<lambda>s. { s\<lparr> tmp_ref := r, field := f, new_ref := r' \<rparr>
                                     |r f r'. r \<in> roots s \<and> r' \<in> Some ` roots s \<union> {None} }) ;;
     \<comment> \<open>Mark the reference we're about to overwrite. Does not update roots.\<close>
     \<lbrace>''deref_del''\<rbrace> deref tmp_ref field ref_update ;;
     \<lbrace>''store_del''\<rbrace> mark_object ;;
     \<comment> \<open>Mark the reference we're about to insert.\<close>
     \<lbrace>''lop_store_ins''\<rbrace> \<acute>ref := \<acute>new_ref ;;
     \<lbrace>''store_ins''\<rbrace> mark_object ;;
     \<lbrace>''store_ins''\<rbrace> store_ref tmp_ref field new_ref"

text\<open>

Load and store payload data.

\<close>

abbreviation load_payload :: "('field, 'mut, 'payload, 'ref) gc_com" where
  "load_payload \<equiv>
    \<lbrace>''mut_load_payload_choose''\<rbrace> LocalOp (\<lambda>s. { s\<lparr> tmp_ref := r, field := f \<rparr> |r f. r \<in> roots s }) ;;
    \<lbrace>''mut_load_payload''\<rbrace> Request (\<lambda>s. (mutator m, LoadPayload (tmp_ref s) (field s)))
                                   (\<lambda>mv s. { s\<lparr> mutator_data := (mutator_data s)(var := pl) \<rparr>
                                           |var pl. mv = mv_Payload pl })"

abbreviation store_payload :: "('field, 'mut, 'payload, 'ref) gc_com" where
  "store_payload \<equiv>
    \<lbrace>''mut_store_payload_choose''\<rbrace> LocalOp (\<lambda>s. { s\<lparr> tmp_ref := r, field := f, payload_value := pl s \<rparr> |r f pl. r \<in> roots s }) ;;
    \<lbrace>''mut_store_payload''\<rbrace> Request (\<lambda>s. (mutator m, StorePayload (tmp_ref s) (field s) (payload_value s)))
                                   (\<lambda>mv s. { s\<lparr> mutator_data := (mutator_data s)(f := pl) \<rparr>
                                           |f pl. mv = mv_Payload pl })"

text\<open>

A mutator makes a non-deterministic choice amongst its possible
actions. For completeness we allow mutators to issue \texttt{MFENCE}
instructions. We leave \texttt{CAS} (etc) to future work. Neither has
a significant impact on the rest of the development.

\<close>
(*
FIXME add SKIP before alloc, mfence. handshake needs work too: want to
commit to checking for handshakes in a strongly fair way. A SKIP
at the top level of \<open>handshake\<close> + a noop transition + appropriate fairness constraints might work.

FIXME is mut local computation strong enough? only works on mutator data; not roots.
*)

definition
  com :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "com =
    LOOP DO
        \<lbrace>''mut_local_computation''\<rbrace> LocalOp (\<lambda>s. {s\<lparr>mutator_data := f (mutator_data s)\<rparr> |f. True})
      \<oplus> alloc
      \<oplus> discard
      \<oplus> load
      \<oplus> store
      \<oplus> load_payload
      \<oplus> store_payload
      \<oplus> \<lbrace>''mut_mfence''\<rbrace> MFENCE
      \<oplus> handshake
    OD"

end


subsection \<open>Garbage collector \label{sec:gc-model-gc}\<close>

text\<open>

We abstract the primitive actions of the garbage collector thread.

\<close>

abbreviation
  gc_deref :: "location
             \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref)
             \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'field)
             \<Rightarrow> (('ref option \<Rightarrow> 'ref option) \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "gc_deref l r f upd \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, LoadRef (r s) (f s)))
                                    (\<lambda>mv s. { upd \<langle>r'\<rangle> s |r'. mv = mv_Ref r' })"

abbreviation
  gc_load_mark :: "location
                \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref)
                \<Rightarrow> ((gc_mark option \<Rightarrow> gc_mark option) \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> ('field, 'mut, 'payload, 'ref) local_state)
                \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "gc_load_mark l r upd \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, LoadMark (r s))) (\<lambda>mv s. { upd \<langle>m\<rangle> s |m. mv = mv_Mark m })"

syntax
  "_gc_fassign" :: "location \<Rightarrow> idt \<Rightarrow> 'ref \<Rightarrow> 'field \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> \<acute>_ := \<acute>_ \<rightarrow> _" [0, 0, 0, 70] 71)
  "_gc_massign" :: "location \<Rightarrow> idt \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> \<acute>_ := \<acute>_ \<rightarrow> flag" [0, 0, 0] 71)
translations
  "\<lbrace>l\<rbrace> \<acute>q := \<acute>r\<rightarrow>f"    => "CONST gc_deref l r \<guillemotleft>f\<guillemotright> (_update_name q)"
  "\<lbrace>l\<rbrace> \<acute>m := \<acute>r\<rightarrow>flag" => "CONST gc_load_mark l r (_update_name m)"

context gc
begin

abbreviation store_fA_syn :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> gc_mark) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> store'_fA") where
  "\<lbrace>l\<rbrace> store_fA f \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, StorefA (f s))) (\<lambda>_ s. {s})"

abbreviation load_fM_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> load'_fM") where
  "\<lbrace>l\<rbrace> load_fM \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, LoadfM)) (\<lambda>mv s. { s\<lparr>fM := m\<rparr> |m. mv = mv_Mark (Some m) })"

abbreviation store_fM_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> store'_fM") where
  "\<lbrace>l\<rbrace> store_fM \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, StorefM (fM s))) (\<lambda>_ s. {s})"

abbreviation store_phase_syn :: "location \<Rightarrow> gc_phase \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> store'_phase") where
  "\<lbrace>l\<rbrace> store_phase ph \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, StorePhase ph)) (\<lambda>_ s. {s\<lparr> phase := ph \<rparr>})"

abbreviation mark_object_syn :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> mark'_object") where
  "\<lbrace>l\<rbrace> mark_object \<equiv> mark_object_fn gc l"

abbreviation free_syn :: "location \<Rightarrow> (('field, 'mut, 'payload, 'ref) local_state \<Rightarrow> 'ref) \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com" ("\<lbrace>_\<rbrace> free") where
  "\<lbrace>l\<rbrace> free r \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (gc, ro_Free (r s))) (\<lambda>_ s. {s})"

text\<open>

The following CIMP program encodes the garbage collector algorithm
proposed in Figure~2.15 of @{cite [cite_macro=citet] "Pizlo201xPhd"}.

\<close>

definition (in gc)
  com :: "('field, 'mut, 'payload, 'ref) gc_com"
where
  "com =
     LOOP DO
       \<lbrace>''idle_noop''\<rbrace> handshake_noop ;; \<comment> \<open>\<open>hp_Idle\<close>\<close>

       \<lbrace>''idle_load_fM''\<rbrace> load_fM ;;
       \<lbrace>''idle_invert_fM''\<rbrace> \<acute>fM := (\<not> \<acute>fM) ;;
       \<lbrace>''idle_store_fM''\<rbrace> store_fM ;;

       \<lbrace>''idle_flip_noop''\<rbrace> handshake_noop ;; \<comment> \<open>\<open>hp_IdleInit\<close>\<close>

       \<lbrace>''idle_phase_init''\<rbrace> store_phase ph_Init ;;

       \<lbrace>''init_noop''\<rbrace> handshake_noop ;; \<comment> \<open>\<open>hp_InitMark\<close>\<close>

       \<lbrace>''init_phase_mark''\<rbrace> store_phase ph_Mark ;;
       \<lbrace>''mark_load_fM''\<rbrace> load_fM ;;
       \<lbrace>''mark_store_fA''\<rbrace> store_fA fM ;;

       \<lbrace>''mark_noop''\<rbrace> handshake_noop ;; \<comment> \<open>\<open>hp_Mark\<close>\<close>

       \<lbrace>''mark_loop_get_roots''\<rbrace> handshake_get_roots ;; \<comment> \<open>\<open>hp_IdleMarkSweep\<close>\<close>

       \<lbrace>''mark_loop''\<rbrace> WHILE \<^bold>\<not>EMPTY W DO
         \<lbrace>''mark_loop_inner''\<rbrace> WHILE \<^bold>\<not>EMPTY W DO
           \<lbrace>''mark_loop_choose_ref''\<rbrace> \<acute>tmp_ref :\<in> \<acute>W ;;
           \<lbrace>''mark_loop_fields''\<rbrace> \<acute>field_set := UNIV ;;
           \<lbrace>''mark_loop_mark_object_loop''\<rbrace> WHILE \<^bold>\<not>EMPTY field_set DO
             \<lbrace>''mark_loop_mark_choose_field''\<rbrace> \<acute>field :\<in> \<acute>field_set ;;
             \<lbrace>''mark_loop_mark_deref''\<rbrace> \<acute>ref := \<acute>tmp_ref\<rightarrow>\<acute>field ;;
             \<lbrace>''mark_loop''\<rbrace> mark_object ;;
             \<lbrace>''mark_loop_mark_field_done''\<rbrace> \<acute>field_set := (\<acute>field_set - {\<acute>field})
           OD ;;
           \<lbrace>''mark_loop_blacken''\<rbrace> \<acute>W := (\<acute>W - {\<acute>tmp_ref})
         OD ;;
         \<lbrace>''mark_loop_get_work''\<rbrace> handshake_get_work
       OD ;;

       \<comment> \<open>sweep\<close>

       \<lbrace>''mark_end''\<rbrace> store_phase ph_Sweep ;;
       \<lbrace>''sweep_load_fM''\<rbrace> load_fM ;;
       \<lbrace>''sweep_refs''\<rbrace> \<acute>refs := UNIV ;;
       \<lbrace>''sweep_loop''\<rbrace> WHILE \<^bold>\<not>EMPTY refs DO
         \<lbrace>''sweep_loop_choose_ref''\<rbrace> \<acute>tmp_ref :\<in> \<acute>refs ;;
         \<lbrace>''sweep_loop_load_mark''\<rbrace> \<acute>mark := \<acute>tmp_ref\<rightarrow>flag ;;
         \<lbrace>''sweep_loop_check''\<rbrace> IF \<^bold>\<not>NULL mark \<^bold>\<and> the \<circ> mark \<^bold>\<noteq> fM THEN
           \<lbrace>''sweep_loop_free''\<rbrace> free tmp_ref
         FI ;;
         \<lbrace>''sweep_loop_ref_done''\<rbrace> \<acute>refs := (\<acute>refs - {\<acute>tmp_ref})
       OD ;;
       \<lbrace>''sweep_idle''\<rbrace> store_phase ph_Idle
     OD"

end

primrec
  gc_coms :: "'mut process_name \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_com"
where
  "gc_coms (mutator m) = mut_m.com m"
| "gc_coms gc = gc.com"
| "gc_coms sys = sys.com"
(*<*)

end
(*>*)
