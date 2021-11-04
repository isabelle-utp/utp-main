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

theory MarkObject
imports
  Global_Invariants_Lemmas
  Local_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open> Mark Object \<close>

text\<open>

These are the most intricate proofs in this development.

\<close>

context mut_m
begin

lemma mark_object_invL[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> mark_object_invL
      \<^bold>\<and> mut_get_roots.mark_object_invL m
      \<^bold>\<and> mut_store_del.mark_object_invL m
      \<^bold>\<and> mut_store_ins.mark_object_invL m
      \<^bold>\<and> LSTP (phase_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mark_object_invL \<rbrace>"
proof (vcg_jackhammer, vcg_name_cases)
  case (store_ins_mo_ptest s s' obj) then show ?case
    apply -
    apply (drule handshake_phase_invD)
    apply (drule phase_rel_invD)
    apply (clarsimp simp: phase_rel_def)
    apply (cases "sys_ghost_hs_phase s\<down>"; simp add: hp_step_rel_def; elim disjE; simp; force)
    done
next case (store_ins_mo_phase s s') then show ?case
    apply -
    apply (drule handshake_phase_invD)
    apply (drule phase_rel_invD)
    apply (clarsimp simp: phase_rel_def)
    apply (case_tac "sys_ghost_hs_phase s\<down>"; simp add: hp_step_rel_def; elim disjE; simp; force)
    done
next case (store_del_mo_phase s s' y) then show ?case
    apply -
    apply (drule handshake_phase_invD)
    apply (drule phase_rel_invD)
    apply (clarsimp simp: phase_rel_def)
    apply (case_tac "sys_ghost_hs_phase s\<down>"; simp add: hp_step_rel_def; elim disjE; simp; force)
    done
next case (deref_del s s' opt_r') then show ?case
    apply -
    apply (rule obj_at_field_on_heapE[OF obj_at_field_on_heap_no_pending_stores[where m=m]])
    apply auto
    done
next case (hs_get_roots_loop_mo_phase s s' y) then show ?case
    apply -
    apply (drule handshake_phase_invD)
    apply (drule phase_rel_invD)
    apply (clarsimp simp: phase_rel_def hp_step_rel_def)
    done
qed fastforce+

lemma mut_store_ins_mark_object_invL[intro]:
  "\<lbrace> mut_store_ins.mark_object_invL m \<^bold>\<and> mark_object_invL \<^bold>\<and> handshake_invL \<^bold>\<and> tso_lock_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mut_store_ins.mark_object_invL m \<rbrace>"
proof(vcg_jackhammer, vcg_name_cases)
     case store_ins_mo_null then show ?case by (metis reachableI(1) valid_refs_invD(8))
next case store_ins_mo_mark then show ?case by (clarsimp split: obj_at_splits)
next case (store_ins_mo_ptest s s' obj) then show ?case by (simp add: valid_W_inv_no_mark_stores_invD filter_empty_conv) metis
next case store_ins_mo_co_won then show ?case by metis
next case store_ins_mo_mtest then show ?case by metis
next case store_ins_mo_co_ctest0 then show ?case by (metis whiteI)
next case (store_ins_mo_co_ctest s s' obj) then show ?case
      apply (elim disjE; clarsimp split: obj_at_splits)
      apply metis
      done
qed

lemma mut_store_del_mark_object_invL[intro]:
  "\<lbrace> mut_store_del.mark_object_invL m \<^bold>\<and> mark_object_invL \<^bold>\<and> handshake_invL \<^bold>\<and> tso_lock_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mut_store_del.mark_object_invL m \<rbrace>"
proof(vcg_jackhammer, vcg_name_cases)
     case store_del_mo_co_ctest0 then show ?case by blast
next case store_del_mo_co_ctest  then show ?case by (clarsimp split: obj_at_splits)
next case store_del_mo_ptest     then show ?case by (auto dest: valid_W_inv_no_mark_stores_invD)
next case store_del_mo_mark      then show ?case by (clarsimp split: obj_at_splits)
next case store_del_mo_null      then show ?case by (auto dest: valid_refs_invD)
qed

lemma mut_get_roots_mark_object_invL[intro]:
  "\<lbrace> mut_get_roots.mark_object_invL m \<^bold>\<and> mark_object_invL \<^bold>\<and> handshake_invL \<^bold>\<and> tso_lock_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> mut_get_roots.mark_object_invL m \<rbrace>"
proof(vcg_jackhammer, vcg_name_cases)
     case hs_get_roots_loop_mo_co_ctest0 then show ?case by blast
next case hs_get_roots_loop_mo_co_ctest  then show ?case by (clarsimp split: obj_at_splits)
next case hs_get_roots_loop_mo_ptest     then show ?case by (auto dest: valid_W_inv_no_mark_stores_invD split: obj_at_splits)
next case hs_get_roots_loop_mo_mark      then show ?case by (clarsimp split: obj_at_splits)
next case hs_get_roots_loop_mo_null      then show ?case by (auto dest: valid_W_inv_no_mark_stores_invD split: obj_at_splits)
qed

end

lemma (in mut_m') mut_mark_object_invL[intro]:
  notes obj_at_field_on_heap_splits[split]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> mark_object_invL \<rbrace> mutator m'"
by (vcg_chainsaw mark_object_invL_def)


subsection\<open> @{term "obj_fields_marked_inv"} \<close>

context gc
begin

lemma gc_mark_mark_object_invL[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_mark.mark_object_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> tso_lock_invL
        \<^bold>\<and> LSTP valid_W_inv \<rbrace>
     gc
   \<lbrace> gc_mark.mark_object_invL \<rbrace>"
by vcg_jackhammer (auto dest: valid_W_inv_no_mark_stores_invD split: obj_at_splits)

lemma obj_fields_marked_invL[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> phase_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> gc_mark.mark_object_invL
       \<^bold>\<and> LSTP (tso_store_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     gc
   \<lbrace> obj_fields_marked_invL \<rbrace>"
proof(vcg_jackhammer, vcg_name_cases)
     case (mark_loop_mark_field_done s s') then show ?case by - (rule obj_fields_marked_mark_field_done, auto)
next case (mark_loop_mark_deref s s')
  then have "grey (gc_tmp_ref s\<down>) s\<down>" by blast
  with mark_loop_mark_deref show ?case
apply (clarsimp split: obj_at_field_on_heap_splits)
apply (rule conjI)
    apply (metis (no_types) case_optionE obj_at_def valid_W_invE(3))
apply clarsimp
apply (erule valid_refs_invD; auto simp: obj_at_def ranI reaches_step(2))
done
qed

end

context sys
begin

lemma mut_store_ins_mark_object_invL[intro]:
  notes mut_m_not_idle_no_fM_writeD[where m=m, dest!]
  notes not_blocked_def[simp]
  notes fun_upd_apply[simp]
  notes if_split_asm[split del]
  shows
  "\<lbrace> mut_m.tso_lock_invL m \<^bold>\<and> mut_m.mark_object_invL m \<^bold>\<and> mut_store_ins.mark_object_invL m
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv) \<rbrace>
     sys
   \<lbrace> mut_store_ins.mark_object_invL m \<rbrace>"
proof(vcg_chainsaw mut_m.mark_object_invL_def mut_m.tso_lock_invL_def mut_m.mut_store_ins_mark_object_invL_def2, vcg_name_cases "mutator m")
     case (store_ins_mo_fM s s' p w ws ref fl) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits if_splits)
      apply (metis (no_types, lifting) valid_W_invD(1))
      done
next case (store_ins_mo_mtest s s' p w ws y ya) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits if_splits)
      done
next case (store_ins_mo_phase s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits if_splits)
      done
next case (store_ins_mo_ptest s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (store_ins_mo_co_lock s s' p w ws y) then show ?case
      apply (intro conjI impI notI; clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write split: mem_store_action.splits obj_at_splits)
      apply metis
      done
next case (store_ins_mo_co_cmark s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write split: mem_store_action.splits obj_at_splits)
      done
next case (store_ins_mo_co_ctest s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write split: mem_store_action.splits obj_at_splits)
      done
next case (store_ins_mo_co_mark s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write split: mem_store_action.splits obj_at_splits)
      done
next case (store_ins_mo_co_unlock s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write split: mem_store_action.splits obj_at_splits)
      done
next case (store_ins_mo_co_won s s' p w ws y) then show ?case
      apply (intro conjI impI notI; clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD(1) split: mem_store_action.splits obj_at_splits)
      done
next case (store_ins_mo_co_W s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD(1) split: mem_store_action.splits obj_at_splits)
      apply auto
      done
qed

lemma mut_store_del_mark_object_invL[intro]:
  notes mut_m_not_idle_no_fM_writeD[where m=m, dest!]
  notes not_blocked_def[simp]
  notes fun_upd_apply[simp]
  notes if_split_asm[split del]
  shows
  "\<lbrace> mut_m.tso_lock_invL m \<^bold>\<and> mut_m.mark_object_invL m \<^bold>\<and> mut_store_del.mark_object_invL m
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv) \<rbrace>
     sys
   \<lbrace> mut_store_del.mark_object_invL m \<rbrace>"
proof(vcg_chainsaw mut_m.mark_object_invL_def mut_m.tso_lock_invL_def mut_m.mut_store_del_mark_object_invL_def2, vcg_name_cases "mutator m")
     case (store_del_mo_fM s s' p w ws y ya) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits if_splits)
      apply (metis (no_types, lifting) valid_W_invD(1))
      done
next case (store_del_mo_mtest s s' p w ws y ya) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits if_splits)
      done
next case (store_del_mo_phase s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (store_del_mo_ptest s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (store_del_mo_co_lock s s' p w ws y) then show ?case
      apply (intro conjI impI notI; clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write split: mem_store_action.splits obj_at_splits)
      apply metis
      done
next case (store_del_mo_co_cmark s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (store_del_mo_co_ctest s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (store_del_mo_co_mark s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (store_del_mo_co_unlock s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply (metis (mono_tags, lifting) filter_empty_conv valid_W_invD(1))
      done
next case (store_del_mo_co_won s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply auto
      done
next case (store_del_mo_co_W s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def filter_empty_conv mut_m_not_idle_no_fM_write valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply auto
      done
qed

lemma mut_get_roots_mark_object_invL[intro]:
  notes not_blocked_def[simp]
  notes p_not_sys[simp]
  notes mut_m.handshake_phase_invD[where m=m, dest!]
  notes fun_upd_apply[simp]
  notes if_split_asm[split del]
  shows
  "\<lbrace> mut_m.tso_lock_invL m \<^bold>\<and> mut_m.handshake_invL m \<^bold>\<and> mut_get_roots.mark_object_invL m
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv) \<rbrace>
     sys
   \<lbrace> mut_get_roots.mark_object_invL m \<rbrace>"
proof(vcg_chainsaw mut_m.tso_lock_invL_def mut_m.handshake_invL_def mut_m.mut_get_roots_mark_object_invL_def2, vcg_name_cases "mutator m")
     case (hs_get_roots_loop_mo_fM s s' p w ws y ya) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits if_splits)
       apply (metis (no_types, lifting) valid_W_invD(1))
      apply (force simp: fM_rel_inv_def fM_rel_def hp_step_rel_def filter_empty_conv valid_W_invD)+
      done
next case (hs_get_roots_loop_mo_mtest s s' p w ws y ya) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply (force simp: fM_rel_inv_def fM_rel_def hp_step_rel_def filter_empty_conv valid_W_invD)+
      done
next case (hs_get_roots_loop_mo_phase s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply (force simp: fM_rel_inv_def fM_rel_def hp_step_rel_def filter_empty_conv valid_W_invD)+
      done
next case (hs_get_roots_loop_mo_ptest s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply (force simp: fM_rel_inv_def fM_rel_def hp_step_rel_def filter_empty_conv valid_W_invD)+
      done
next case (hs_get_roots_loop_mo_co_lock s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply (force simp: fM_rel_inv_def fM_rel_def hp_step_rel_def filter_empty_conv valid_W_invD)+
      done
next case (hs_get_roots_loop_mo_co_cmark s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (hs_get_roots_loop_mo_co_ctest s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (hs_get_roots_loop_mo_co_mark s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (hs_get_roots_loop_mo_co_unlock s s' w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      done
next case (hs_get_roots_loop_mo_co_won s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply (force simp: fM_rel_inv_def fM_rel_def hp_step_rel_def filter_empty_conv valid_W_invD)+
      done
next case (hs_get_roots_loop_mo_co_W s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def valid_W_invD split: mem_store_action.splits obj_at_splits)
      apply (force simp: fM_rel_inv_def fM_rel_def hp_step_rel_def filter_empty_conv valid_W_invD)+
      done
qed

lemma gc_mark_mark_object_invL[intro]:
  notes fun_upd_apply[simp]
  notes if_split_asm[split del]
  shows
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.phase_invL \<^bold>\<and> gc_mark.mark_object_invL \<^bold>\<and> gc.tso_lock_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv) \<rbrace>
     sys
   \<lbrace> gc_mark.mark_object_invL \<rbrace>"
proof(vcg_chainsaw gc.gc_mark_mark_object_invL_def2 gc.tso_lock_invL_def gc.phase_invL_def gc.fM_fA_invL_def gc.handshake_invL_def, vcg_name_cases "gc")
     case (mark_loop_mo_fM s s' p w ws y ya) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits if_splits)
      apply (auto split: obj_at_splits)
      done
next case (mark_loop_mo_mtest s s' p w ws y ya) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      apply (auto split: obj_at_splits)
      done
next case (mark_loop_mo_phase s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      apply (auto split: obj_at_splits)
      done
next case (mark_loop_mo_ptest s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      apply (auto split: obj_at_splits)
      done
next case (mark_loop_mo_co_lock s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      apply (auto split: obj_at_splits)
      done
next case (mark_loop_mo_co_cmark s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      done
next case (mark_loop_mo_co_ctest s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      done
next case (mark_loop_mo_co_mark s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      done
next case (mark_loop_mo_co_unlock s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys
                     split: mem_store_action.splits)
      apply auto
      done
next case (mark_loop_mo_co_won s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      apply (auto split: obj_at_splits)
      done
next case (mark_loop_mo_co_W s s' p w ws y) then show ?case
      apply (clarsimp simp: do_store_action_def not_blocked_def fM_rel_def filter_empty_conv p_not_sys valid_W_invD
                     split: mem_store_action.splits)
      apply (auto split: obj_at_splits)
      done
qed

end

lemma (in mut_m') mut_get_roots_mark_object_invL[intro]:
  "\<lbrace> mut_get_roots.mark_object_invL m \<rbrace> mutator m'"
by vcg_chainsaw

lemma (in mut_m') mut_store_ins_mark_object_invL[intro]:
  "\<lbrace> mut_store_ins.mark_object_invL m \<rbrace> mutator m'"
by vcg_chainsaw

lemma (in mut_m') mut_store_del_mark_object_invL[intro]:
  "\<lbrace> mut_store_del.mark_object_invL m \<rbrace> mutator m'"
by vcg_chainsaw

lemma (in gc) mut_get_roots_mark_object_invL[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> mut_m.handshake_invL m \<^bold>\<and> mut_get_roots.mark_object_invL m \<rbrace> gc \<lbrace> mut_get_roots.mark_object_invL m \<rbrace>"
by (vcg_chainsaw mut_m.handshake_invL_def mut_m.mut_get_roots_mark_object_invL_def2)

lemma (in mut_m) gc_obj_fields_marked_invL[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.obj_fields_marked_invL
     \<^bold>\<and> LSTP (tso_store_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> gc.obj_fields_marked_invL \<rbrace>"
apply (vcg_chainsaw gc.obj_fields_marked_invL_def gc.handshake_invL_def)
(* FIXME rules *)
  apply (clarsimp simp: gc.obj_fields_marked_def fun_upd_apply)
  apply (rename_tac s s' ra x)
  apply (drule_tac x=x in spec)
  apply clarsimp
  apply (erule obj_at_field_on_heapE)
   apply (subgoal_tac "grey (gc_tmp_ref s\<down>) s\<down>")
    apply (drule_tac y="gc_tmp_ref s\<down>" in valid_refs_invD(7), simp+)
    apply (clarsimp simp: fun_upd_apply split: obj_at_splits; fail)
   apply (erule greyI)
  apply (clarsimp simp: fun_upd_apply split: obj_at_splits; fail)
 apply (clarsimp simp: fun_upd_apply split: obj_at_field_on_heap_splits; fail)
apply (clarsimp simp: fun_upd_apply)
done

lemma (in mut_m) gc_mark_mark_object_invL[intro]:
  "\<lbrace> gc_mark.mark_object_invL \<rbrace> mutator m"
by (vcg_chainsaw gc.gc_mark_mark_object_invL_def2)


(*<*)

end
(*>*)
