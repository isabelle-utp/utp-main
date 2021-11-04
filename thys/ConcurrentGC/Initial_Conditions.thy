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

theory Initial_Conditions
imports
  Local_Invariants_Lemmas
  Global_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open>Initial conditions \label{sec:initial-conditions-proofs}\<close>

context gc_system
begin

lemma init_strong_tricolour_inv:
  "\<lbrakk> obj_mark ` ran (sys_heap \<lparr>GST = s, HST = []\<rparr>\<down>) \<subseteq> {gc_fM \<lparr>GST = s, HST = []\<rparr>\<down>}; sys_fM \<lparr>GST = s, HST = []\<rparr>\<down> = gc_fM \<lparr>GST = s, HST = []\<rparr>\<down> \<rbrakk>
     \<Longrightarrow> strong_tricolour_inv \<lparr>GST = s, HST = []\<rparr>\<down>"
unfolding strong_tricolour_inv_def ran_def white_def by (auto split: obj_at_splits)

lemma init_no_grey_refs:
  "\<lbrakk> gc_W \<lparr>GST = s, HST = []\<rparr>\<down> = {}; \<forall>m. W (\<lparr>GST = s, HST = []\<rparr>\<down> (mutator m)) = {}; sys_W \<lparr>GST = s, HST = []\<rparr>\<down> = {};
     gc_ghost_honorary_grey \<lparr>GST = s, HST = []\<rparr>\<down> = {}; \<forall>m. ghost_honorary_grey (\<lparr>GST = s, HST = []\<rparr>\<down> (mutator m)) = {}; sys_ghost_honorary_grey \<lparr>GST = s, HST = []\<rparr>\<down> = {} \<rbrakk>
     \<Longrightarrow> no_grey_refs \<lparr>GST = s, HST = []\<rparr>\<down>"
unfolding no_grey_refs_def grey_def WL_def by (metis equals0D process_name.exhaust sup_bot.left_neutral)

lemma valid_refs_imp_valid_refs_inv:
  "\<lbrakk> valid_refs s; no_grey_refs s; \<forall>p. sys_mem_store_buffers p s = []; \<forall>m. ghost_honorary_root (s (mutator m)) = {} \<rbrakk>
     \<Longrightarrow> valid_refs_inv s"
unfolding valid_refs_inv_def valid_refs_def mut_m.reachable_def mut_m.tso_store_refs_def
using no_grey_refs_not_grey_reachableD by fastforce

lemma no_grey_refs_imp_valid_W_inv:
  "\<lbrakk> no_grey_refs s; \<forall>p. sys_mem_store_buffers p s = [] \<rbrakk>
     \<Longrightarrow> valid_W_inv s"
unfolding valid_W_inv_def no_grey_refs_def grey_def WL_def by auto

lemma valid_refs_imp_reachable_snapshot_inv:
  "\<lbrakk> valid_refs s; obj_mark ` ran (sys_heap s) \<subseteq> {sys_fM s}; \<forall>p. sys_mem_store_buffers p s = []; \<forall>m. ghost_honorary_root (s (mutator m)) = {} \<rbrakk>
     \<Longrightarrow> mut_m.reachable_snapshot_inv m s"
unfolding mut_m.reachable_snapshot_inv_def in_snapshot_def valid_refs_def black_def mut_m.reachable_def mut_m.tso_store_refs_def
apply clarsimp
apply (auto simp: image_subset_iff ran_def split: obj_at_splits)
done

lemma init_inv_sys: "\<forall>s. initial_state gc_system s \<longrightarrow> invs \<lparr>GST = s, HST = []\<rparr>\<down>"
apply (clarsimp dest!: initial_stateD
              simp: gc_system_init_def invs_def gc_initial_state_def mut_initial_state_def sys_initial_state_def
                    inv
                    handshake_phase_rel_def handshake_phase_inv_def hp_step_rel_def phase_rel_inv_def phase_rel_def
                    tso_store_inv_def
                    init_no_grey_refs init_strong_tricolour_inv no_grey_refs_imp_valid_W_inv
                    valid_refs_imp_reachable_snapshot_inv
                    valid_refs_imp_valid_refs_inv
                    mut_m.marked_deletions_def mut_m.marked_insertions_def
                    fA_rel_inv_def fA_rel_def fM_rel_inv_def fM_rel_def
                    all_conj_distrib)
done

lemma init_inv_mut: "\<forall>s. initial_state gc_system s \<longrightarrow> mut_m.invsL m \<lparr>GST = s, HST = []\<rparr>"
apply (clarsimp dest!: initial_stateD)
apply (drule fun_cong[where x="mutator m"])
apply (clarsimp simp: all_com_interned_defs)
unfolding mut_m.invsL_def mut_m.mut_get_roots_mark_object_invL_def2 mut_m.mut_store_del_mark_object_invL_def2 mut_m.mut_store_ins_mark_object_invL_def2
          mut_m.mark_object_invL_def mut_m.handshake_invL_def mut_m.tso_lock_invL_def
          gc_system_init_def mut_initial_state_def sys_initial_state_def
apply (intro conjI; simp add: locset_cache atS_simps; simp add: mut_m.loc_defs)
done

lemma init_inv_gc: "\<forall>s. initial_state gc_system s \<longrightarrow> gc.invsL \<lparr>GST = s, HST = []\<rparr>"
apply (clarsimp dest!: initial_stateD)
apply (drule fun_cong[where x=gc])
apply (clarsimp simp: all_com_interned_defs)
unfolding gc.invsL_def gc.fM_fA_invL_def gc.handshake_invL_def gc.obj_fields_marked_invL_def gc.phase_invL_def gc.sweep_loop_invL_def
          gc.tso_lock_invL_def gc.gc_W_empty_invL_def gc.gc_mark_mark_object_invL_def2
apply (intro conjI; simp add: locset_cache atS_simps init_no_grey_refs; simp add: gc.loc_defs)
apply (simp_all add: gc_system_init_def gc_initial_state_def mut_initial_state_def sys_initial_state_def
                     gc_system.init_no_grey_refs)
 apply blast
apply (clarsimp simp: image_subset_iff ranI split: obj_at_splits)
done

end

(* FIXME really deserves to be somewhere very public but there's no shared theory immediately above Local and Global invs by design *)

definition I :: "('field, 'mut, 'payload, 'ref) gc_pred" where
  "I = (invsL \<^bold>\<and> LSTP invs)"

lemmas I_defs = gc.invsL_def mut_m.invsL_def invsL_def invs_def I_def

context gc_system
begin

theorem init_inv: "\<forall>s. initial_state gc_system s \<longrightarrow> I \<lparr>GST = s, HST = []\<rparr>"
unfolding I_def invsL_def by (simp add: init_inv_sys init_inv_gc init_inv_mut)

end

(*<*)

end
(*>*)
