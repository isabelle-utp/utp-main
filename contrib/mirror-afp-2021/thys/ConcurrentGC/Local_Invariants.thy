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

theory Local_Invariants
imports
  Proofs_Basis
begin

(*>*)
section\<open> Local invariants \label{sec:local-invariants}\<close>


subsection\<open>TSO invariants\<close>

context gc
begin

text \<open>

The GC holds the TSO lock only during the \texttt{CAS} in \<open>mark_object\<close>.

\<close>

locset_definition tso_lock_locs :: "location set" where
  "tso_lock_locs = (\<Union>l\<in>{ ''mo_co_cmark'', ''mo_co_ctest'', ''mo_co_mark'', ''mo_co_unlock'' }. suffixed l)"

definition tso_lock_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "tso_lock_invL =
    (atS_gc tso_lock_locs      (tso_locked_by gc)
   \<^bold>\<and> atS_gc (- tso_lock_locs) (\<^bold>\<not> tso_locked_by gc))"

end

context mut_m
begin

text \<open>

A mutator holds the TSO lock only during the \texttt{CAS}s in \<open>mark_object\<close>.

\<close>

locset_definition "tso_lock_locs =
  (\<Union>l\<in>{ ''mo_co_cmark'', ''mo_co_ctest'', ''mo_co_mark'', ''mo_co_unlock'' }. suffixed l)"

definition tso_lock_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "tso_lock_invL =
    (atS_mut tso_lock_locs     (tso_locked_by (mutator m))
   \<^bold>\<and> atS_mut (-tso_lock_locs) (\<^bold>\<not>tso_locked_by (mutator m)))"

end


subsection\<open>Handshake phases \label{sec:local-handshake-phases}\<close>

text\<open>

Connect @{const "sys_ghost_hs_phase"} with locations in the GC.

\<close>

context gc
begin

locset_definition "idle_locs = prefixed ''idle''"
locset_definition "init_locs = prefixed ''init''"
locset_definition "mark_locs = prefixed ''mark''"
locset_definition "sweep_locs = prefixed ''sweep''"
locset_definition "mark_loop_locs = prefixed ''mark_loop''"

locset_definition "hp_Idle_locs =
    (prefixed ''idle_noop'' - { idle_noop_mfence, idle_noop_init_type })
  \<union> { idle_load_fM, idle_invert_fM, idle_store_fM, idle_flip_noop_mfence, idle_flip_noop_init_type }"

locset_definition "hp_IdleInit_locs =
    (prefixed ''idle_flip_noop'' - { idle_flip_noop_mfence, idle_flip_noop_init_type })
  \<union> { idle_phase_init, init_noop_mfence, init_noop_init_type }"

locset_definition "hp_InitMark_locs =
    (prefixed ''init_noop'' - { init_noop_mfence, init_noop_init_type })
  \<union> { init_phase_mark, mark_load_fM, mark_store_fA, mark_noop_mfence, mark_noop_init_type }"

locset_definition "hp_IdleMarkSweep_locs =
    { idle_noop_mfence, idle_noop_init_type, mark_end }
  \<union> sweep_locs
  \<union> (mark_loop_locs - { mark_loop_get_roots_init_type })"

locset_definition "hp_Mark_locs =
    (prefixed ''mark_noop'' - { mark_noop_mfence, mark_noop_init_type })
  \<union> { mark_loop_get_roots_init_type }"

abbreviation
  "hs_noop_prefixes \<equiv> {''idle_noop'', ''idle_flip_noop'', ''init_noop'', ''mark_noop'' }"

locset_definition "hs_noop_locs =
  (\<Union>l \<in> hs_noop_prefixes. prefixed l - (suffixed ''_noop_mfence'' \<union> suffixed ''_noop_init_type''))"

locset_definition "hs_get_roots_locs =
  prefixed ''mark_loop_get_roots'' - {mark_loop_get_roots_init_type}"

locset_definition "hs_get_work_locs =
  prefixed ''mark_loop_get_work'' - {mark_loop_get_work_init_type}"

abbreviation "hs_prefixes \<equiv>
  hs_noop_prefixes \<union> { ''mark_loop_get_roots'', ''mark_loop_get_work'' }"

locset_definition "hs_init_loop_locs = (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_init_loop''))"
locset_definition "hs_done_loop_locs = (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_done_loop''))"
locset_definition "hs_done_locs = (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_done''))"
locset_definition "hs_none_pending_locs = - (hs_init_loop_locs \<union> hs_done_locs)"
locset_definition "hs_in_sync_locs =
  (- ( (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_init'')) \<union> hs_done_locs ))
  \<union> (\<Union>l \<in> hs_prefixes. {l @ ''_init_type''})"

locset_definition "hs_out_of_sync_locs =
  (\<Union>l \<in> hs_prefixes. {l @ ''_init_muts''})"

locset_definition "hs_mut_in_muts_locs =
  (\<Union>l \<in> hs_prefixes. {l @ ''_init_loop_set_pending'', l @ ''_init_loop_done''})"

locset_definition "hs_init_loop_done_locs =
  (\<Union>l \<in> hs_prefixes. {l @ ''_init_loop_done''})"

locset_definition "hs_init_loop_not_done_locs =
  (hs_init_loop_locs - (\<Union>l \<in> hs_prefixes. {l @ ''_init_loop_done''}))"

definition handshake_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "handshake_invL =
     (atS_gc hs_noop_locs         (sys_hs_type \<^bold>= \<langle>ht_NOOP\<rangle>)
    \<^bold>\<and> atS_gc hs_get_roots_locs    (sys_hs_type \<^bold>= \<langle>ht_GetRoots\<rangle>)
    \<^bold>\<and> atS_gc hs_get_work_locs     (sys_hs_type \<^bold>= \<langle>ht_GetWork\<rangle>)
    \<^bold>\<and> atS_gc hs_mut_in_muts_locs      (gc_mut \<^bold>\<in> gc_muts)
    \<^bold>\<and> atS_gc hs_init_loop_locs        (\<^bold>\<forall>m. \<^bold>\<not>\<langle>m\<rangle> \<^bold>\<in> gc_muts \<^bold>\<longrightarrow> sys_hs_pending m
                                                                  \<^bold>\<or> sys_ghost_hs_in_sync m)
    \<^bold>\<and> atS_gc hs_init_loop_not_done_locs (\<^bold>\<forall>m.   \<langle>m\<rangle> \<^bold>\<in> gc_muts \<^bold>\<longrightarrow> \<^bold>\<not>sys_hs_pending m
                                                                 \<^bold>\<and> \<^bold>\<not>sys_ghost_hs_in_sync m)
    \<^bold>\<and> atS_gc hs_init_loop_done_locs     ( (sys_hs_pending \<^bold>$ gc_mut
                                        \<^bold>\<or> sys_ghost_hs_in_sync \<^bold>$ gc_mut)
                                      \<^bold>\<and> (\<^bold>\<forall>m. \<langle>m\<rangle> \<^bold>\<in> gc_muts \<^bold>\<and> \<langle>m\<rangle> \<^bold>\<noteq> gc_mut
                                                                 \<^bold>\<longrightarrow> \<^bold>\<not>sys_hs_pending m
                                                                   \<^bold>\<and> \<^bold>\<not>sys_ghost_hs_in_sync m) )
    \<^bold>\<and> atS_gc hs_done_locs       (\<^bold>\<forall>m. sys_hs_pending m \<^bold>\<or> sys_ghost_hs_in_sync m)
    \<^bold>\<and> atS_gc hs_done_loop_locs  (\<^bold>\<forall>m. \<^bold>\<not>\<langle>m\<rangle> \<^bold>\<in> gc_muts \<^bold>\<longrightarrow> \<^bold>\<not>sys_hs_pending m)
    \<^bold>\<and> atS_gc hs_none_pending_locs (\<^bold>\<forall>m. \<^bold>\<not>sys_hs_pending m)
    \<^bold>\<and> atS_gc hs_in_sync_locs      (\<^bold>\<forall>m. sys_ghost_hs_in_sync m)
    \<^bold>\<and> atS_gc hs_out_of_sync_locs  (\<^bold>\<forall>m. \<^bold>\<not>sys_hs_pending m
                                         \<^bold>\<and> \<^bold>\<not>sys_ghost_hs_in_sync m)

    \<^bold>\<and> atS_gc hp_Idle_locs          (sys_ghost_hs_phase \<^bold>= \<langle>hp_Idle\<rangle>)
    \<^bold>\<and> atS_gc hp_IdleInit_locs      (sys_ghost_hs_phase \<^bold>= \<langle>hp_IdleInit\<rangle>)
    \<^bold>\<and> atS_gc hp_InitMark_locs      (sys_ghost_hs_phase \<^bold>= \<langle>hp_InitMark\<rangle>)
    \<^bold>\<and> atS_gc hp_IdleMarkSweep_locs (sys_ghost_hs_phase \<^bold>= \<langle>hp_IdleMarkSweep\<rangle>)
    \<^bold>\<and> atS_gc hp_Mark_locs          (sys_ghost_hs_phase \<^bold>= \<langle>hp_Mark\<rangle>))"

text\<open>

Tie the garbage collector's control location to the value of @{const
"gc_phase"}.

\<close>

locset_definition no_pending_phase_locs :: "location set" where
  "no_pending_phase_locs =
       (idle_locs - { idle_noop_mfence })
     \<union> (init_locs - { init_noop_mfence })
     \<union> (mark_locs - { mark_load_fM, mark_store_fA, mark_noop_mfence })"

definition phase_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "phase_invL =
   (atS_gc idle_locs             (gc_phase \<^bold>= \<langle>ph_Idle\<rangle>)
  \<^bold>\<and> atS_gc init_locs             (gc_phase \<^bold>= \<langle>ph_Init\<rangle>)
  \<^bold>\<and> atS_gc mark_locs             (gc_phase \<^bold>= \<langle>ph_Mark\<rangle>)
  \<^bold>\<and> atS_gc sweep_locs            (gc_phase \<^bold>= \<langle>ph_Sweep\<rangle>)
  \<^bold>\<and> atS_gc no_pending_phase_locs (LIST_NULL (tso_pending_phase gc)))"

end

text\<open>

Local handshake phase invariant for the mutators.

\<close>

context mut_m
begin

locset_definition "hs_noop_locs = prefixed ''hs_noop_''"
locset_definition "hs_get_roots_locs = prefixed ''hs_get_roots_''"
locset_definition "hs_get_work_locs = prefixed ''hs_get_work_''"
locset_definition "no_pending_mutations_locs =
     { hs_load_ht }
  \<union> (prefixed ''hs_noop'')
  \<union> (prefixed ''hs_get_roots'')
  \<union> (prefixed ''hs_get_work'')"
locset_definition "hs_pending_loaded_locs = (prefixed ''hs_'' - { hs_load_pending })"
locset_definition "hs_pending_locs = (prefixed ''hs_'' - { hs_load_pending, hs_pending })"
locset_definition "ht_loaded_locs = (prefixed ''hs_'' - { hs_load_pending, hs_pending, hs_mfence, hs_load_ht })"

definition handshake_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "handshake_invL =
  (atS_mut hs_noop_locs                (sys_hs_type \<^bold>= \<langle>ht_NOOP\<rangle>)
 \<^bold>\<and> atS_mut hs_get_roots_locs          (sys_hs_type \<^bold>= \<langle>ht_GetRoots\<rangle>)
 \<^bold>\<and> atS_mut hs_get_work_locs           (sys_hs_type \<^bold>= \<langle>ht_GetWork\<rangle>)
 \<^bold>\<and> atS_mut ht_loaded_locs             (mut_hs_pending \<^bold>\<longrightarrow> mut_hs_type \<^bold>= sys_hs_type)
 \<^bold>\<and> atS_mut hs_pending_loaded_locs     (mut_hs_pending \<^bold>\<longrightarrow> sys_hs_pending m)
 \<^bold>\<and> atS_mut hs_pending_locs            (mut_hs_pending)
 \<^bold>\<and> atS_mut no_pending_mutations_locs  (LIST_NULL (tso_pending_mutate (mutator m))))"

end


text\<open>

Validity of @{const "sys_fM"} wrt @{const "gc_fM"} and the handshake
phase. Effectively we use @{const "gc_fM"} as ghost state. We also
include the TSO lock to rule out the GC having any pending marks
during the @{const "hp_Idle"} handshake phase.

\<close>

context gc
begin

locset_definition "fM_eq_locs = (- { idle_store_fM, idle_flip_noop_mfence })"
locset_definition "fM_tso_empty_locs = (- { idle_flip_noop_mfence })"
locset_definition "fA_tso_empty_locs = (- { mark_noop_mfence })"

locset_definition
  "fA_eq_locs = { idle_load_fM, idle_invert_fM }
              \<union> prefixed ''idle_noop''
              \<union> (mark_locs - { mark_load_fM, mark_store_fA, mark_noop_mfence })
              \<union> sweep_locs"

locset_definition
  "fA_neq_locs = { idle_phase_init, idle_store_fM, mark_load_fM, mark_store_fA }
               \<union> prefixed ''idle_flip_noop''
               \<union> init_locs"

definition fM_fA_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "fM_fA_invL =
   (atS_gc fM_eq_locs                (gc_fM \<^bold>= sys_fM)
  \<^bold>\<and> at_gc idle_store_fM              (gc_fM \<^bold>\<noteq> sys_fM)
  \<^bold>\<and> at_gc idle_flip_noop_mfence      (sys_fM \<^bold>\<noteq> gc_fM \<^bold>\<longrightarrow> \<^bold>\<not>LIST_NULL (tso_pending_fM gc))
  \<^bold>\<and> atS_gc fM_tso_empty_locs         (LIST_NULL (tso_pending_fM gc))

  \<^bold>\<and> atS_gc fA_eq_locs                (gc_fM \<^bold>= sys_fA)
  \<^bold>\<and> atS_gc fA_neq_locs               (gc_fM \<^bold>\<noteq> sys_fA)
  \<^bold>\<and> at_gc mark_noop_mfence           (gc_fM \<^bold>\<noteq> sys_fA \<^bold>\<longrightarrow> \<^bold>\<not>LIST_NULL (tso_pending_fA gc))
  \<^bold>\<and> atS_gc fA_tso_empty_locs         (LIST_NULL (tso_pending_fA gc)))"

end


subsection\<open>Mark Object\<close>

text\<open>

Local invariants for @{const "mark_object_fn"}. Invoking this code in
phases where @{const "sys_fM"} is constant marks the reference in
@{const "ref"}. When @{const "sys_fM"} could vary this code is not
called. The two cases are distinguished by @{term "p_ph_enabled"}.

Each use needs to provide extra facts to justify validity of
references, etc.  We do not include a post-condition for @{const
"mark_object_fn"} here as it is different at each call site.

\<close>

locale mark_object =
  fixes p :: "'mut process_name"
  fixes l :: "location"
  fixes p_ph_enabled :: "('field, 'mut, 'payload, 'ref) lsts_pred"
  assumes p_ph_enabled_eq_imp: "eq_imp (\<lambda>(_::unit) s. s p) p_ph_enabled"
begin

abbreviation (input) "p_cas_mark s \<equiv> cas_mark (s p)"
abbreviation (input) "p_mark s \<equiv> mark (s p)"
abbreviation (input) "p_fM s \<equiv> fM (s p)"
abbreviation (input) "p_ghost_hs_phase s \<equiv> ghost_hs_phase (s p)"
abbreviation (input) "p_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s p)"
abbreviation (input) "p_ghost_hs_in_sync s \<equiv> ghost_hs_in_sync (s p)"
abbreviation (input) "p_phase s \<equiv> phase (s p)"
abbreviation (input) "p_ref s \<equiv> ref (s p)"
abbreviation (input) "p_the_ref \<equiv> the \<circ> p_ref"
abbreviation (input) "p_W s \<equiv> W (s p)"

abbreviation at_p :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_pred" where
  "at_p l' P \<equiv> at p (l @ l') \<^bold>\<longrightarrow> LSTP P"

abbreviation (input) "p_en_cond P \<equiv> p_ph_enabled \<^bold>\<longrightarrow> P"

abbreviation (input) "p_valid_ref \<equiv> \<^bold>\<not>NULL p_ref \<^bold>\<and> valid_ref \<^bold>$ p_the_ref"
abbreviation (input) "p_tso_no_pending_mark \<equiv> LIST_NULL (tso_pending_mark p)"
abbreviation (input) "p_tso_no_pending_mutate \<equiv> LIST_NULL (tso_pending_mutate p)"

(* FIXME rename: these are assertions? *)
abbreviation (input)
  "p_valid_W_inv \<equiv> ((p_cas_mark \<^bold>\<noteq> p_mark \<^bold>\<or> p_tso_no_pending_mark) \<^bold>\<longrightarrow> marked \<^bold>$ p_the_ref)
                \<^bold>\<and> (tso_pending_mark p \<^bold>\<in> (\<lambda>s. {[], [mw_Mark (p_the_ref s) (p_fM s)]}) )"

abbreviation (input)
  "p_mark_inv \<equiv> \<^bold>\<not>NULL p_mark
            \<^bold>\<and> ((\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = p_mark s) (p_the_ref s) s)
              \<^bold>\<or> marked \<^bold>$ p_the_ref)"

abbreviation (input)
  "p_cas_mark_inv \<equiv> (\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = p_cas_mark s) (p_the_ref s) s)"

abbreviation (input) "p_valid_fM \<equiv> p_fM \<^bold>= sys_fM"

abbreviation (input)
  "p_ghg_eq_ref \<equiv> p_ghost_honorary_grey \<^bold>= pred_singleton (the \<circ> p_ref)"
abbreviation (input)
  "p_ghg_inv \<equiv> If p_cas_mark \<^bold>= p_mark Then p_ghg_eq_ref Else EMPTY p_ghost_honorary_grey"

definition mark_object_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
  "mark_object_invL =
   (at_p ''_mo_null''        \<langle>True\<rangle>
  \<^bold>\<and> at_p ''_mo_mark''        (p_valid_ref)
  \<^bold>\<and> at_p ''_mo_fM''          (p_valid_ref \<^bold>\<and> p_en_cond (p_mark_inv))
  \<^bold>\<and> at_p ''_mo_mtest''       (p_valid_ref \<^bold>\<and> p_en_cond (p_mark_inv \<^bold>\<and> p_valid_fM))
  \<^bold>\<and> at_p ''_mo_phase''       (p_valid_ref \<^bold>\<and> p_mark \<^bold>\<noteq> Some \<circ> p_fM \<^bold>\<and> p_en_cond (p_mark_inv \<^bold>\<and> p_valid_fM))
  \<^bold>\<and> at_p ''_mo_ptest''       (p_valid_ref \<^bold>\<and> p_mark \<^bold>\<noteq> Some \<circ> p_fM \<^bold>\<and> p_en_cond (p_mark_inv \<^bold>\<and> p_valid_fM))
  \<^bold>\<and> at_p ''_mo_co_lock''     (p_valid_ref \<^bold>\<and> p_mark_inv \<^bold>\<and> p_valid_fM \<^bold>\<and> p_mark \<^bold>\<noteq> Some \<circ> p_fM \<^bold>\<and> p_tso_no_pending_mark)
  \<^bold>\<and> at_p ''_mo_co_cmark''    (p_valid_ref \<^bold>\<and> p_mark_inv \<^bold>\<and> p_valid_fM \<^bold>\<and> p_mark \<^bold>\<noteq> Some \<circ> p_fM \<^bold>\<and> p_tso_no_pending_mark)
  \<^bold>\<and> at_p ''_mo_co_ctest''    (p_valid_ref \<^bold>\<and> p_mark_inv \<^bold>\<and> p_valid_fM \<^bold>\<and> p_mark \<^bold>\<noteq> Some \<circ> p_fM \<^bold>\<and> p_cas_mark_inv \<^bold>\<and> p_tso_no_pending_mark)
  \<^bold>\<and> at_p ''_mo_co_mark''     (p_cas_mark \<^bold>= p_mark \<^bold>\<and> p_valid_ref \<^bold>\<and> p_valid_fM \<^bold>\<and> white \<^bold>$ p_the_ref \<^bold>\<and> p_tso_no_pending_mark)
  \<^bold>\<and> at_p ''_mo_co_unlock''   (p_ghg_inv \<^bold>\<and> p_valid_ref \<^bold>\<and> p_valid_fM \<^bold>\<and> p_valid_W_inv)
  \<^bold>\<and> at_p ''_mo_co_won''      (p_ghg_inv \<^bold>\<and> p_valid_ref \<^bold>\<and> p_valid_fM \<^bold>\<and> marked \<^bold>$ p_the_ref \<^bold>\<and> p_tso_no_pending_mutate)
  \<^bold>\<and> at_p ''_mo_co_W''        (p_ghg_eq_ref \<^bold>\<and> p_valid_ref \<^bold>\<and> p_valid_fM \<^bold>\<and> marked \<^bold>$ p_the_ref \<^bold>\<and> p_tso_no_pending_mutate))"

end

text\<open>

The uses of @{const "mark_object_fn"} in the GC and during the root
marking are straightforward.

\<close>

interpretation gc_mark: mark_object "gc" "gc.mark_loop" "\<langle>True\<rangle>"
by standard (simp add: eq_imp_def)

lemmas (in gc) gc_mark_mark_object_invL_def2[inv] = gc_mark.mark_object_invL_def[unfolded loc_defs, simplified, folded loc_defs]

interpretation mut_get_roots: mark_object "mutator m" "mut_m.hs_get_roots_loop" "\<langle>True\<rangle>" for m
by standard (simp add: eq_imp_def)

lemmas (in mut_m) mut_get_roots_mark_object_invL_def2[inv] = mut_get_roots.mark_object_invL_def[unfolded loc_defs, simplified, folded loc_defs]

text\<open>

The most interesting cases are the two asynchronous uses of @{const
"mark_object_fn"} in the mutators: we need something that holds even
before we read the phase. In particular we need to avoid interference
by an @{const "fM"} flip.

\<close>

interpretation mut_store_del: mark_object "mutator m" "''store_del''" "mut_m.mut_ghost_hs_phase m \<^bold>\<noteq> \<langle>hp_Idle\<rangle>" for m (* FIXME store del, why the string? *)
by standard (simp add: eq_imp_def)

lemmas (in mut_m) mut_store_del_mark_object_invL_def2[inv] = mut_store_del.mark_object_invL_def[simplified, folded loc_defs]

interpretation mut_store_ins: mark_object "mutator m" "mut_m.store_ins"  "mut_m.mut_ghost_hs_phase m \<^bold>\<noteq> \<langle>hp_Idle\<rangle>" for m
by standard (simp add: eq_imp_def)

lemmas (in mut_m) mut_store_ins_mark_object_invL_def2[inv] = mut_store_ins.mark_object_invL_def[unfolded loc_defs, simplified, folded loc_defs]

text\<open>

Local invariant for the mutator's uses of \<open>mark_object\<close>.

\<close>

context mut_m
begin

locset_definition "hs_get_roots_loop_locs = prefixed ''hs_get_roots_loop''"
locset_definition "hs_get_roots_loop_mo_locs =
  prefixed ''hs_get_roots_loop_mo'' \<union> {hs_get_roots_loop_done}"

abbreviation "mut_async_mark_object_prefixes \<equiv> { ''store_del'', ''store_ins'' }"

locset_definition "hs_not_hp_Idle_locs =
  (\<Union>pref\<in>mut_async_mark_object_prefixes.
     \<Union>l\<in>{''mo_co_lock'', ''mo_co_cmark'', ''mo_co_ctest'', ''mo_co_mark'', ''mo_co_unlock'', ''mo_co_won'', ''mo_co_W''}. {pref @ ''_'' @ l})"

locset_definition "async_mo_ptest_locs =
  (\<Union>pref\<in>mut_async_mark_object_prefixes. {pref @ ''_mo_ptest''})"

locset_definition "mo_ptest_locs =
  (\<Union>pref\<in>mut_async_mark_object_prefixes. {pref @ ''_mo_ptest''})"

locset_definition "mo_valid_ref_locs =
  (prefixed ''store_del'' \<union> prefixed ''store_ins'' \<union> {deref_del, lop_store_ins})"

(*>*)
text\<open>

This local invariant for the mutators illustrates the handshake
structure: we can rely on the insertion barrier earlier than on the
deletion barrier. Both need to be installed before \<open>get_roots\<close>
to ensure we preserve the strong tricolour invariant. All black
objects at that point are allocated: we need to know that the
insertion barrier is installed to preserve it. This limits when \<open>fA\<close> can be set.

It is interesting to contrast the two barriers. Intuitively a mutator
can locally guarantee that it, in the relevant phases, will insert
only marked references. Less often can it be sure that the reference
it is overwriting is marked. We also need to consider stores pending
in TSO buffers: it is key that after the \<open>''init_noop''\<close>
handshake there are no pending white insertions
(mutations that insert unmarked references). This ensures the deletion barrier
does its job.

\<close>

locset_definition
  "ghost_honorary_grey_empty_locs =
     (- (\<Union>pref\<in>{ ''hs_get_roots_loop'', ''store_del'', ''store_ins'' }.
        \<Union>l\<in>{ ''mo_co_unlock'', ''mo_co_won'', ''mo_co_W'' }. {pref @ ''_'' @ l}))"

locset_definition
  "ghost_honorary_root_empty_locs =
     (- (prefixed ''store_del'' \<union> {lop_store_ins} \<union> prefixed ''store_ins''))"

locset_definition "ghost_honorary_root_nonempty_locs = prefixed ''store_del'' - {store_del_mo_null}"
locset_definition "not_idle_locs = suffixed ''_mo_ptest''"
locset_definition "ins_barrier_locs = prefixed ''store_ins''"
locset_definition "del_barrier1_locs = prefixed ''store_del_mo'' \<union> {lop_store_ins}"

definition mark_object_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "mark_object_invL =
   (atS_mut hs_get_roots_loop_locs        (mut_refs \<^bold>\<subseteq> mut_roots \<^bold>\<and> (\<^bold>\<forall>r. \<langle>r\<rangle> \<^bold>\<in> mut_roots \<^bold>- mut_refs \<^bold>\<longrightarrow> marked r))
  \<^bold>\<and> atS_mut hs_get_roots_loop_mo_locs     (\<^bold>\<not>NULL mut_ref \<^bold>\<and> mut_the_ref \<^bold>\<in> mut_roots)
  \<^bold>\<and> at_mut hs_get_roots_loop_done         (marked \<^bold>$ mut_the_ref)
  \<^bold>\<and> at_mut hs_get_roots_loop_mo_ptest     (mut_phase \<^bold>\<noteq> \<langle>ph_Idle\<rangle>)
  \<^bold>\<and> at_mut hs_get_roots_done              (\<^bold>\<forall>r. \<langle>r\<rangle> \<^bold>\<in> mut_roots \<^bold>\<longrightarrow> marked r)

  \<^bold>\<and> atS_mut mo_valid_ref_locs             ( (\<^bold>\<not>NULL mut_new_ref \<^bold>\<longrightarrow> mut_the_new_ref \<^bold>\<in> mut_roots)
                                          \<^bold>\<and> (mut_tmp_ref \<^bold>\<in> mut_roots) )
  \<^bold>\<and> at_mut store_del_mo_null              (\<^bold>\<not>NULL mut_ref \<^bold>\<longrightarrow> mut_the_ref \<^bold>\<in> mut_ghost_honorary_root)
  \<^bold>\<and> atS_mut ghost_honorary_root_nonempty_locs   (mut_the_ref \<^bold>\<in> mut_ghost_honorary_root)

  \<^bold>\<and> atS_mut not_idle_locs                 (mut_phase \<^bold>\<noteq> \<langle>ph_Idle\<rangle> \<^bold>\<longrightarrow> mut_ghost_hs_phase \<^bold>\<noteq> \<langle>hp_Idle\<rangle>)
  \<^bold>\<and> atS_mut hs_not_hp_Idle_locs           (mut_ghost_hs_phase \<^bold>\<noteq> \<langle>hp_Idle\<rangle>)

  \<^bold>\<and> atS_mut mo_ptest_locs                 (mut_phase \<^bold>= \<langle>ph_Idle\<rangle> \<^bold>\<longrightarrow> (mut_ghost_hs_phase \<^bold>\<in> \<langle>{hp_Idle, hp_IdleInit}\<rangle>
                                                                          \<^bold>\<or> (mut_ghost_hs_phase \<^bold>= \<langle>hp_IdleMarkSweep\<rangle>
                                                                                \<^bold>\<and> sys_phase \<^bold>= \<langle>ph_Idle\<rangle>)))
  \<^bold>\<and> atS_mut ghost_honorary_grey_empty_locs (EMPTY mut_ghost_honorary_grey)
\<comment> \<open>insertion barrier\<close>
  \<^bold>\<and> at_mut store_ins                      ( (mut_ghost_hs_phase \<^bold>\<in> \<langle>{hp_InitMark, hp_Mark}\<rangle>
                                            \<^bold>\<or> (mut_ghost_hs_phase \<^bold>= \<langle>hp_IdleMarkSweep\<rangle> \<^bold>\<and> sys_phase \<^bold>\<noteq> \<langle>ph_Idle\<rangle>))
                                           \<^bold>\<and> \<^bold>\<not>NULL mut_new_ref
                                           \<^bold>\<longrightarrow> marked \<^bold>$ mut_the_new_ref )
  \<^bold>\<and> atS_mut ins_barrier_locs              ( ( (mut_ghost_hs_phase \<^bold>= \<langle>hp_Mark\<rangle>
                                              \<^bold>\<or> (mut_ghost_hs_phase \<^bold>= \<langle>hp_IdleMarkSweep\<rangle> \<^bold>\<and> sys_phase \<^bold>\<noteq> \<langle>ph_Idle\<rangle>))
                                            \<^bold>\<and> (\<lambda>s. \<forall>opt_r'. \<not>tso_pending_store (mutator m) (mw_Mutate (mut_tmp_ref s) (mut_field s) opt_r') s)
                                            \<^bold>\<longrightarrow> (\<lambda>s. obj_at_field_on_heap (\<lambda>r'. marked r' s) (mut_tmp_ref s) (mut_field s) s) )
                                          \<^bold>\<and> (mut_ref \<^bold>= mut_new_ref) )
\<comment> \<open>deletion barrier\<close>
  \<^bold>\<and> atS_mut del_barrier1_locs             ( (mut_ghost_hs_phase \<^bold>= \<langle>hp_Mark\<rangle>
                                            \<^bold>\<or> (mut_ghost_hs_phase \<^bold>= \<langle>hp_IdleMarkSweep\<rangle> \<^bold>\<and> sys_phase \<^bold>\<noteq> \<langle>ph_Idle\<rangle>))
                                           \<^bold>\<and> (\<lambda>s. \<forall>opt_r'. \<not>tso_pending_store (mutator m) (mw_Mutate (mut_tmp_ref s) (mut_field s) opt_r') s)
                                          \<^bold>\<longrightarrow> (\<lambda>s. obj_at_field_on_heap (\<lambda>r. mut_ref s = Some r \<or> marked r s) (mut_tmp_ref s) (mut_field s) s))
  \<^bold>\<and> at_mut lop_store_ins                  ( (mut_ghost_hs_phase \<^bold>= \<langle>hp_Mark\<rangle>
                                             \<^bold>\<or> (mut_ghost_hs_phase \<^bold>= \<langle>hp_IdleMarkSweep\<rangle> \<^bold>\<and> sys_phase \<^bold>\<noteq> \<langle>ph_Idle\<rangle>))
                                           \<^bold>\<and> \<^bold>\<not>NULL mut_ref
                                          \<^bold>\<longrightarrow> marked \<^bold>$ mut_the_ref )
\<comment>\<open>after \<open>init_noop\<close>. key: no pending white insertions \<open>at_mut hs_noop_done\<close> which we get from @{const \<open>handshake_invL\<close>}.\<close>
  \<^bold>\<and> at_mut mut_load                         (mut_tmp_ref \<^bold>\<in> mut_roots)
  \<^bold>\<and> atS_mut ghost_honorary_root_empty_locs  (EMPTY mut_ghost_honorary_root) )"

end


subsection\<open>The infamous termination argument\<close>

text\<open>

We need to know that if the GC does not receive any further work to do
at \<open>get_roots\<close> and \<open>get_work\<close>, then there are no grey
objects left. Essentially this encodes the stability property that
grey objects must exist for mutators to create grey objects.

Note that this is not invariant across the scan: it is possible for
the GC to hold all the grey references. The two handshakes transform
the GC's local knowledge that it has no more work to do into a global
property, or gives it more work.

\<close>

(* FIXME this is an assertion? *)
definition (in mut_m) gc_W_empty_mut_inv :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "gc_W_empty_mut_inv =
      ((EMPTY sys_W \<^bold>\<and> sys_ghost_hs_in_sync m \<^bold>\<and> \<^bold>\<not>EMPTY (WL (mutator m)))
   \<^bold>\<longrightarrow> (\<^bold>\<exists>m'. \<^bold>\<not>sys_ghost_hs_in_sync m' \<^bold>\<and> \<^bold>\<not>EMPTY (WL (mutator m'))))"

context gc
begin

locset_definition gc_W_empty_locs :: "location set" where
  "gc_W_empty_locs =
       idle_locs \<union> init_locs \<union> sweep_locs \<union> {mark_load_fM, mark_store_fA, mark_end}
     \<union> prefixed ''mark_noop''
     \<union> prefixed ''mark_loop_get_roots''
     \<union> prefixed ''mark_loop_get_work''"

locset_definition "get_roots_UN_get_work_locs = hs_get_roots_locs \<union> hs_get_work_locs"
locset_definition "black_heap_locs = {sweep_idle, idle_noop_mfence, idle_noop_init_type}"
locset_definition "no_grey_refs_locs = black_heap_locs \<union> sweep_locs \<union> {mark_end}"

definition gc_W_empty_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "gc_W_empty_invL =
   (atS_gc get_roots_UN_get_work_locs   (\<^bold>\<forall>m. mut_m.gc_W_empty_mut_inv m)
  \<^bold>\<and> at_gc mark_loop_get_roots_load_W    (EMPTY sys_W \<^bold>\<longrightarrow> no_grey_refs)
  \<^bold>\<and> at_gc mark_loop_get_work_load_W     (EMPTY sys_W \<^bold>\<longrightarrow> no_grey_refs)
  \<^bold>\<and> at_gc mark_loop                     (EMPTY gc_W \<^bold>\<longrightarrow> no_grey_refs)
  \<^bold>\<and> atS_gc no_grey_refs_locs            no_grey_refs
  \<^bold>\<and> atS_gc gc_W_empty_locs              (EMPTY gc_W))"

end


subsection\<open>Sweep loop invariants\<close>

context gc
begin

locset_definition "sweep_loop_locs = prefixed ''sweep_loop''"
locset_definition "sweep_loop_not_choose_ref_locs = (prefixed ''sweep_loop_'' - {sweep_loop_choose_ref})"

definition sweep_loop_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "sweep_loop_invL =
   (at_gc sweep_loop_check            ( (\<^bold>\<not>NULL gc_mark \<^bold>\<longrightarrow> (\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = gc_mark s) (gc_tmp_ref s) s))
                                      \<^bold>\<and> ( NULL gc_mark \<^bold>\<and> valid_ref \<^bold>$ gc_tmp_ref \<^bold>\<longrightarrow> marked \<^bold>$ gc_tmp_ref ) )
  \<^bold>\<and> at_gc sweep_loop_free             ( \<^bold>\<not>NULL gc_mark \<^bold>\<and> the \<circ> gc_mark \<^bold>\<noteq> gc_fM \<^bold>\<and> (\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = gc_mark s) (gc_tmp_ref s) s) )
  \<^bold>\<and> at_gc sweep_loop_ref_done         (valid_ref \<^bold>$ gc_tmp_ref \<^bold>\<longrightarrow> marked \<^bold>$ gc_tmp_ref)
  \<^bold>\<and> atS_gc sweep_loop_locs            (\<^bold>\<forall>r. \<^bold>\<not>\<langle>r\<rangle> \<^bold>\<in> gc_refs \<^bold>\<and> valid_ref r \<^bold>\<longrightarrow> marked r)
  \<^bold>\<and> atS_gc black_heap_locs            (\<^bold>\<forall>r. valid_ref r \<^bold>\<longrightarrow> marked r)
  \<^bold>\<and> atS_gc sweep_loop_not_choose_ref_locs (gc_tmp_ref \<^bold>\<in> gc_refs))"

text\<open>

For showing that the GC's use of @{const "mark_object_fn"} is correct.

When we take grey @{const "tmp_ref"} to black, all of the objects it
points to are marked, ergo the new black does not point to white, and
so we preserve the strong tricolour invariant.

\<close>

definition obj_fields_marked :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "obj_fields_marked =
     (\<^bold>\<forall>f. \<langle>f\<rangle> \<^bold>\<in> (- gc_field_set) \<^bold>\<longrightarrow> (\<lambda>s. obj_at_field_on_heap (\<lambda>r. marked r s) (gc_tmp_ref s) f s))"

locset_definition "mark_loop_mo_locs = prefixed ''mark_loop_mo''"
locset_definition "obj_fields_marked_good_ref_locs = mark_loop_mo_locs \<union> {mark_loop_mark_field_done}"

locset_definition
  "ghost_honorary_grey_empty_locs =
     (- { mark_loop_mo_co_unlock, mark_loop_mo_co_won, mark_loop_mo_co_W })"

locset_definition
  "obj_fields_marked_locs =
     {mark_loop_mark_object_loop, mark_loop_mark_choose_field, mark_loop_mark_deref, mark_loop_mark_field_done, mark_loop_blacken}
   \<union> mark_loop_mo_locs"

definition obj_fields_marked_invL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
[inv]: "obj_fields_marked_invL =
    (atS_gc obj_fields_marked_locs       (obj_fields_marked \<^bold>\<and> gc_tmp_ref \<^bold>\<in> gc_W)
  \<^bold>\<and> atS_gc obj_fields_marked_good_ref_locs (\<lambda>s. obj_at_field_on_heap (\<lambda>r. gc_ref s = Some r \<or> marked r s) (gc_tmp_ref s) (gc_field s) s)
  \<^bold>\<and> atS_gc mark_loop_mo_locs            (\<^bold>\<forall>y. \<^bold>\<not>NULL gc_ref \<^bold>\<and> (\<lambda>s. ((gc_the_ref s) reaches y) s) \<^bold>\<longrightarrow> valid_ref y)
  \<^bold>\<and> at_gc mark_loop_fields              (gc_tmp_ref \<^bold>\<in> gc_W)
  \<^bold>\<and> at_gc mark_loop_mark_field_done     (\<^bold>\<not>NULL gc_ref \<^bold>\<longrightarrow> marked \<^bold>$ gc_the_ref)
  \<^bold>\<and> at_gc mark_loop_blacken             (EMPTY gc_field_set)
  \<^bold>\<and> atS_gc ghost_honorary_grey_empty_locs (EMPTY gc_ghost_honorary_grey))"

end


subsection\<open> The local innvariants collected \<close>

definition (in gc) invsL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
  "invsL =
   (fM_fA_invL
  \<^bold>\<and> gc_mark.mark_object_invL
  \<^bold>\<and> gc_W_empty_invL
  \<^bold>\<and> handshake_invL
  \<^bold>\<and> obj_fields_marked_invL
  \<^bold>\<and> phase_invL
  \<^bold>\<and> sweep_loop_invL
  \<^bold>\<and> tso_lock_invL)"

definition (in mut_m) invsL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
  "invsL =
   (mark_object_invL
  \<^bold>\<and> mut_get_roots.mark_object_invL m
  \<^bold>\<and> mut_store_ins.mark_object_invL m
  \<^bold>\<and> mut_store_del.mark_object_invL m
  \<^bold>\<and> handshake_invL
  \<^bold>\<and> tso_lock_invL)"

definition invsL :: "('field, 'mut, 'payload, 'ref) gc_pred" where
  "invsL = (gc.invsL \<^bold>\<and> (\<^bold>\<forall>m. mut_m.invsL m))"
(*<*)

end
(*>*)
