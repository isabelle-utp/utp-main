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

theory Phases
imports
  Global_Invariants_Lemmas
  Local_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open>Handshake phases\<close>

text\<open>

Reasoning about phases, handshakes.

Tie the garbage collector's control location to the value of @{const
"gc_phase"}.

\<close>

lemma (in gc) phase_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, tso_pending_phase gc s\<down>))
          phase_invL"
by (clarsimp simp: eq_imp_def inv)

lemmas gc_phase_invL_niE[nie] =
  iffD1[OF gc.phase_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) phase_invL[intro]:
  "\<lbrace> phase_invL \<^bold>\<and> LSTP phase_rel_inv \<rbrace> gc \<lbrace> phase_invL \<rbrace>"
by vcg_jackhammer (fastforce dest!: phase_rel_invD simp: phase_rel_def)

lemma (in sys) gc_phase_invL[intro]:
  notes fun_upd_apply[simp]
  notes if_splits[split]
  shows
  "\<lbrace> gc.phase_invL \<rbrace> sys"
by (vcg_chainsaw gc.phase_invL_def)

lemma (in mut_m) gc_phase_invL[intro]:
  "\<lbrace> gc.phase_invL \<rbrace> mutator m"
by (vcg_chainsaw gc.phase_invL_def[inv])

lemma (in gc) phase_rel_inv[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> phase_invL \<^bold>\<and> LSTP phase_rel_inv \<rbrace> gc \<lbrace> LSTP phase_rel_inv \<rbrace>"
unfolding phase_rel_inv_def by (vcg_jackhammer (no_thin_post_inv); simp add: phase_rel_def; blast)

lemma (in sys) phase_rel_inv[intro]:
  notes gc.phase_invL_def[inv]
  notes phase_rel_inv_def[inv]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP (phase_rel_inv \<^bold>\<and> tso_store_inv) \<rbrace> sys \<lbrace> LSTP phase_rel_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws) then show ?case
    apply (simp add: phase_rel_def p_not_sys split: if_splits)
    apply (elim disjE; auto split: if_splits)
    done
qed

lemma (in mut_m) phase_rel_inv[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> phase_rel_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP phase_rel_inv \<rbrace>"
unfolding phase_rel_inv_def
proof (vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (hs_noop_done s s') then show ?case
    by (auto dest!: handshake_phase_invD
             simp: handshake_phase_rel_def phase_rel_def hp_step_rel_def
            split: hs_phase.splits)
next case (hs_get_roots_done s s') then show ?case
    by (auto dest!: handshake_phase_invD
             simp: handshake_phase_rel_def phase_rel_def hp_step_rel_def
            split: hs_phase.splits)
next case (hs_get_work_done s s') then show ?case
    by (auto dest!: handshake_phase_invD
             simp: handshake_phase_rel_def phase_rel_def hp_step_rel_def
            split: hs_phase.splits)
qed

text\<open>

Connect @{const "sys_ghost_hs_phase"} with locations in the GC.

\<close>

lemma gc_handshake_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, sys_ghost_hs_phase s\<down>, hs_pending (s\<down> sys), ghost_hs_in_sync (s\<down> sys), sys_hs_type s\<down>))
          gc.handshake_invL"
by (simp add: gc.handshake_invL_def eq_imp_def)

lemmas gc_handshake_invL_niE[nie] =
  iffD1[OF gc_handshake_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in sys) gc_handshake_invL[intro]:
  "\<lbrace> gc.handshake_invL \<rbrace> sys"
by (vcg_chainsaw gc.handshake_invL_def)

lemma (in sys) handshake_phase_inv[intro]:
  "\<lbrace> LSTP handshake_phase_inv \<rbrace> sys"
unfolding handshake_phase_inv_def by (vcg_jackhammer (no_thin_post_inv))

lemma (in gc) handshake_invL[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<rbrace> gc"
by vcg_jackhammer fastforce+

lemma (in gc) handshake_phase_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> LSTP handshake_phase_inv \<rbrace> gc \<lbrace> LSTP handshake_phase_inv \<rbrace>"
unfolding handshake_phase_inv_def by (vcg_jackhammer (no_thin_post_inv)) (auto simp: handshake_phase_inv_def hp_step_rel_def)

text\<open>

Local handshake phase invariant for the mutators.

\<close>

lemma (in mut_m) handshake_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s (mutator m), s\<down> (mutator m), sys_hs_type s\<down>, sys_hs_pending m s\<down>, mem_store_buffers (s\<down> sys) (mutator m)))
          handshake_invL"
unfolding eq_imp_def handshake_invL_def by simp

lemmas mut_m_handshake_invL_niE[nie] =
  iffD1[OF mut_m.handshake_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in mut_m) handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> mutator m"
by vcg_jackhammer

lemma (in mut_m') handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> mutator m'"
by vcg_chainsaw

lemma (in gc) mut_handshake_invL[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> mut_m.handshake_invL m \<rbrace> gc \<lbrace> mut_m.handshake_invL m \<rbrace>"
by (vcg_chainsaw mut_m.handshake_invL_def)

lemma (in sys) mut_handshake_invL[intro]:
  notes if_splits[split]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> mut_m.handshake_invL m \<rbrace> sys"
by (vcg_chainsaw mut_m.handshake_invL_def)

lemma (in mut_m) gc_handshake_invL[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> gc.handshake_invL \<rbrace> mutator m \<lbrace> gc.handshake_invL \<rbrace>"
by (vcg_chainsaw gc.handshake_invL_def)

lemma (in mut_m) handshake_phase_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> LSTP handshake_phase_inv \<rbrace> mutator m \<lbrace> LSTP handshake_phase_inv \<rbrace>"
unfolding handshake_phase_inv_def by (vcg_jackhammer (no_thin_post_inv)) (auto simp: hp_step_rel_def)

text\<open>

Validity of @{const "sys_fM"} wrt @{const "gc_fM"} and the handshake
phase. Effectively we use @{const "gc_fM"} as ghost state. We also
include the TSO lock to rule out the GC having any pending marks
during the @{const "hp_Idle"} handshake phase.

\<close>

lemma gc_fM_fA_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, sys_fA s\<down>, sys_fM s\<down>, sys_mem_store_buffers gc s\<down>))
          gc.fM_fA_invL"
by (simp add: gc.fM_fA_invL_def eq_imp_def)

lemmas gc_fM_fA_invL_niE[nie] =
  iffD1[OF gc_fM_fA_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

context gc
begin

lemma fM_fA_invL[intro]:
  "\<lbrace> fM_fA_invL \<rbrace> gc"
by vcg_jackhammer

lemma fM_rel_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> tso_lock_invL \<^bold>\<and> LSTP fM_rel_inv \<rbrace>
     gc
   \<lbrace> LSTP fM_rel_inv \<rbrace>"
by (vcg_jackhammer (no_thin_post_inv); simp add: fM_rel_inv_def fM_rel_def)

lemma fA_rel_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> LSTP fA_rel_inv \<rbrace>
     gc
   \<lbrace> LSTP fA_rel_inv \<rbrace>"
by (vcg_jackhammer (no_thin_post_inv); simp add: fA_rel_inv_def; auto simp: fA_rel_def)

end

context mut_m
begin

lemma gc_fM_fA_invL[intro]:
  "\<lbrace> gc.fM_fA_invL \<rbrace> mutator m"
by (vcg_chainsaw gc.fM_fA_invL_def)

lemma fM_rel_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP fM_rel_inv \<rbrace> mutator m"
unfolding fM_rel_inv_def by (vcg_jackhammer (no_thin_post_inv); simp add: fM_rel_def; elim disjE; auto split: if_splits)

lemma fA_rel_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP fA_rel_inv \<rbrace> mutator m"
unfolding fA_rel_inv_def by (vcg_jackhammer (no_thin_post_inv); simp add: fA_rel_def; elim disjE; auto split: if_splits)

end


context gc
begin

lemma fA_neq_locs_diff_fA_tso_empty_locs:
  "fA_neq_locs - fA_tso_empty_locs = {}"
apply (simp add: fA_neq_locs_def fA_tso_empty_locs_def locset_cache)
apply (simp add: loc_defs)
done

end

context sys
begin

lemma gc_fM_fA_invL[intro]:
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> tso_store_inv) \<rbrace>
     sys
   \<lbrace> gc.fM_fA_invL \<rbrace>"
apply( vcg_chainsaw (no_thin) gc.fM_fA_invL_def
     ; (simp add: p_not_sys)?; (erule disjE)?; clarsimp split: if_splits )
proof(vcg_name_cases sys gc)
     case (tso_dequeue_store_buffer_mark_noop_mfence s s' ws) then show ?case by (clarsimp simp: fA_rel_inv_def fA_rel_def)
next case (tso_dequeue_store_buffer_fA_neq_locs s s' ws) then show ?case
  apply (clarsimp simp: fA_rel_inv_def fA_rel_def fM_rel_inv_def fM_rel_def)
  apply (drule (1) atS_dests(3), fastforce simp: atS_simps gc.fA_neq_locs_diff_fA_tso_empty_locs)
  done
next case (tso_dequeue_store_buffer_fA_eq_locs s s' ws) then show ?case by (clarsimp simp: fA_rel_inv_def fA_rel_def)
next case (tso_dequeue_store_buffer_idle_flip_noop_mfence s s' ws) then show ?case by (clarsimp simp: fM_rel_inv_def fM_rel_def)
next case (tso_dequeue_store_buffer_fM_eq_locs s s' ws) then show ?case by (clarsimp simp: fM_rel_inv_def fM_rel_def)
qed

lemma fM_rel_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP (fM_rel_inv \<^bold>\<and> tso_store_inv) \<rbrace> sys \<lbrace> LSTP fM_rel_inv \<rbrace>"
apply (vcg_jackhammer (no_thin_post_inv))
apply (clarsimp simp: do_store_action_def fM_rel_inv_def fM_rel_def p_not_sys
                split: mem_store_action.splits)
apply (intro allI conjI impI; clarsimp)
done

lemma fA_rel_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP (fA_rel_inv \<^bold>\<and> tso_store_inv) \<rbrace> sys \<lbrace> LSTP fA_rel_inv \<rbrace>"
apply (vcg_jackhammer (no_thin_post_inv))
apply (clarsimp simp: do_store_action_def fA_rel_inv_def fA_rel_def p_not_sys
                split: mem_store_action.splits)
apply (intro allI conjI impI; clarsimp)
done

end


subsubsection\<open>sys phase inv\<close>

context mut_m
begin

lemma sys_phase_inv[intro]:
  notes if_split_asm[split del]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL
             \<^bold>\<and> mark_object_invL
             \<^bold>\<and> mut_get_roots.mark_object_invL m
             \<^bold>\<and> mut_store_del.mark_object_invL m
             \<^bold>\<and> mut_store_ins.mark_object_invL m
        \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP sys_phase_inv \<rbrace>"
proof( (vcg_jackhammer (no_thin_post_inv)
       ; clarsimp simp: fA_rel_inv_def fM_rel_inv_def sys_phase_inv_aux_case heap_colours_colours
                 split: hs_phase.splits if_splits )
     , vcg_name_cases )
     case (alloc s s' rb) then show ?case
      by (clarsimp simp: fA_rel_def fM_rel_def no_black_refs_def
                  dest!: handshake_phase_invD phase_rel_invD
                  split: hs_phase.splits)
next case (store_ins_mo_co_mark0 s s' y) then show ?case
      by (fastforce simp: fA_rel_def fM_rel_def hp_step_rel_def
                   dest!: handshake_phase_invD phase_rel_invD)
next case (store_ins_mo_co_mark s s' y) then show ?case
      apply -
      apply (drule spec[where x=m])
      apply (rule conjI)
       apply (clarsimp simp: hp_step_rel_def phase_rel_def conj_disj_distribR[symmetric]
                      dest!: handshake_phase_invD phase_rel_invD)
       apply (elim disjE, simp_all add: no_grey_refs_not_rootD; fail)
      apply (clarsimp simp: hp_step_rel_def phase_rel_def
                     dest!: handshake_phase_invD phase_rel_invD)
      apply (elim disjE, simp_all add: no_grey_refs_not_rootD)[1]
      apply clarsimp
      apply (elim disjE, simp_all add: no_grey_refs_not_rootD filter_empty_conv)[1]
      apply fastforce
      done
next case (store_del_mo_co_mark0 s s' y) then show ?case
      apply (clarsimp simp: hp_step_rel_def dest!: handshake_phase_invD phase_rel_invD)
      apply (metis (no_types, lifting) mut_m.no_grey_refs_not_rootD mutator_phase_inv_aux.simps(5))
      done
next case (store_del_mo_co_mark s s' y) then show ?case
      apply -
      apply (drule spec[where x=m])
      apply (rule conjI)
       apply (clarsimp simp: hp_step_rel_def phase_rel_def conj_disj_distribR[symmetric] no_grey_refs_not_rootD
                      dest!: handshake_phase_invD phase_rel_invD; fail)
      apply (clarsimp simp: hp_step_rel_def phase_rel_def
                     dest!: handshake_phase_invD phase_rel_invD)
      apply (elim disjE, simp_all add: no_grey_refs_not_rootD)
      apply clarsimp
      apply (elim disjE, simp_all add: no_grey_refs_not_rootD filter_empty_conv)
      apply fastforce
      done
next case (hs_get_roots_done s s') then show ?case
      apply (clarsimp simp: hp_step_rel_def phase_rel_def filter_empty_conv
                     dest!: handshake_phase_invD phase_rel_invD)
      apply auto
      done
next case (hs_get_roots_loop_mo_co_mark s s' y) then show ?case
      apply -
      apply (drule spec[where x=m])
      apply (rule conjI)
       apply (clarsimp simp: hp_step_rel_def phase_rel_def conj_disj_distribR[symmetric]
                      dest!: handshake_phase_invD phase_rel_invD; fail)
      apply (clarsimp simp: hp_step_rel_def phase_rel_def
                     dest!: handshake_phase_invD phase_rel_invD)
      apply (elim disjE, simp_all add: no_grey_refs_not_rootD)
      apply clarsimp
      apply (elim disjE, simp_all add: no_grey_refs_not_rootD filter_empty_conv)[1]
      apply fastforce
      done
next case (hs_get_work_done s s') then show ?case
      apply (clarsimp simp: hp_step_rel_def phase_rel_def filter_empty_conv
                     dest!: handshake_phase_invD phase_rel_invD)
      apply auto
      done
qed (clarsimp simp: hp_step_rel_def dest!: handshake_phase_invD phase_rel_invD)+

end

lemma (in gc) sys_phase_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> handshake_invL \<^bold>\<and> obj_fields_marked_invL
       \<^bold>\<and> phase_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> LSTP (phase_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv) \<rbrace>
     gc
   \<lbrace> LSTP sys_phase_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
     case (mark_loop_get_work_load_W s s') then show ?case by (fastforce dest!: phase_rel_invD simp: phase_rel_def no_grey_refsD filter_empty_conv)
next case (mark_loop_blacken s s') then show ?case by (meson no_grey_refsD(1))
next case (mark_loop_mo_co_W s s') then show ?case by (meson no_grey_refsD(1))
next case (mark_loop_mo_co_mark s s') then show ?case by (meson no_grey_refsD(1))
next case (mark_loop_get_roots_load_W s s') then show ?case by (fastforce dest!: phase_rel_invD simp: phase_rel_def no_grey_refsD filter_empty_conv)
next case (mark_loop_get_roots_init_type s s') then show ?case by (fastforce dest!: phase_rel_invD simp: phase_rel_def no_grey_refsD filter_empty_conv)
next case (idle_noop_init_type s s') then show ?case using black_heap_no_greys by blast
qed

lemma no_grey_refs_no_marks[simp]:
  "\<lbrakk> no_grey_refs s; valid_W_inv s \<rbrakk> \<Longrightarrow> \<not>sys_mem_store_buffers p s = mw_Mark r fl # ws"
unfolding no_grey_refs_def by (metis greyI(1) list.set_intros(1) valid_W_invE(5))
(* FIXME suggests redundancy in valid_W_inv rules:  by (meson greyI(1) valid_W_invD(1)) *)

context sys
begin

lemma black_heap_dequeue_mark[iff]:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mark r fl # ws; black_heap s; valid_W_inv s \<rbrakk>
   \<Longrightarrow> black_heap (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
unfolding black_heap_def by (metis colours_distinct(4) valid_W_invD(1) white_valid_ref)

lemma white_heap_dequeue_fM[iff]:
  "black_heap s\<down>
     \<Longrightarrow> white_heap (s\<down>(sys := s\<down> sys\<lparr>fM := \<not> sys_fM s\<down>, mem_store_buffers := (mem_store_buffers (s\<down> sys))(gc := ws)\<rparr>))"
unfolding black_heap_def white_heap_def black_def white_def by clarsimp (* FIXME rules? *)

lemma black_heap_dequeue_fM[iff]:
  "\<lbrakk> white_heap s\<down>; no_grey_refs s\<down> \<rbrakk>
     \<Longrightarrow> black_heap (s\<down>(sys := s\<down> sys\<lparr>fM := \<not> sys_fM s\<down>, mem_store_buffers := (mem_store_buffers (s\<down> sys))(gc := ws)\<rparr>))"
unfolding black_heap_def white_heap_def no_grey_refs_def by auto

lemma sys_phase_inv[intro]:
  notes if_split_asm[split del]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP sys_phase_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv)
     , clarsimp simp: fA_rel_inv_def fM_rel_inv_def p_not_sys
     , vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws) then show ?case
    apply (clarsimp simp: do_store_action_def sys_phase_inv_aux_case
                   split: mem_store_action.splits hs_phase.splits if_splits)
    apply (clarsimp simp: fA_rel_def fM_rel_def; erule disjE; clarsimp simp: fA_rel_def fM_rel_def)+
     apply (metis (mono_tags, lifting) filter.simps(2) list.discI tso_store_invD(4))
    apply auto
    done
qed

end
(*<*)

end
(*>*)
