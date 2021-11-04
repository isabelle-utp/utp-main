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

theory Noninterference
imports
  Global_Invariants_Lemmas
  Local_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open> Noninterference \<close>

lemma mut_del_barrier1_subseteq_mut_mo_valid_ref_locs[locset_cache]: (* FIXME rename *)
  "mut_m.del_barrier1_locs \<subseteq> mut_m.mo_valid_ref_locs"
unfolding mut_m.del_barrier1_locs_def mut_m.mo_valid_ref_locs_def by (auto intro: append_prefixD)

lemma mut_del_barrier2_subseteq_mut_mo_valid_ref[locset_cache]: (* FIXME rename *)
  "mut_m.ins_barrier_locs \<subseteq> mut_m.mo_valid_ref_locs"
unfolding mut_m.ins_barrier_locs_def mut_m.mo_valid_ref_locs_def by (auto intro: append_prefixD)

context gc
begin

lemma obj_fields_marked_locs_subseteq_hp_IdleMarkSweep_locs:
  "obj_fields_marked_locs \<subseteq> hp_IdleMarkSweep_locs"
unfolding gc.obj_fields_marked_locs_def gc.hp_IdleMarkSweep_locs_def gc.mark_loop_locs_def gc.mark_loop_mo_locs_def
apply (clarsimp simp: locset_cache loc_defs)
apply (drule mp)
apply (auto intro: append_prefixD)
done

lemma obj_fields_marked_locs_subseteq_hs_in_sync_locs:
  "obj_fields_marked_locs \<subseteq> hs_in_sync_locs"
unfolding obj_fields_marked_locs_def hs_in_sync_locs_def hs_done_locs_def mark_loop_mo_locs_def
by (auto simp: loc_defs dest: prefix_same_cases)

lemma obj_fields_marked_good_ref_subseteq_hp_IdleMarkSweep_locs:
  "obj_fields_marked_good_ref_locs \<subseteq> hp_IdleMarkSweep_locs"
unfolding obj_fields_marked_good_ref_locs_def mark_loop_locs_def hp_IdleMarkSweep_locs_def mark_loop_mo_locs_def
apply (clarsimp simp: loc_defs)
apply (drule mp)
apply (auto intro: append_prefixD)
done

lemma mark_loop_mo_mark_loop_field_done_subseteq_hs_in_sync_locs:
  "obj_fields_marked_good_ref_locs \<subseteq> hs_in_sync_locs"
unfolding obj_fields_marked_good_ref_locs_def hs_in_sync_locs_def mark_loop_mo_locs_def hs_done_locs_def
by (auto simp: loc_defs dest: prefix_same_cases)

lemma no_grey_refs_locs_subseteq_hs_in_sync_locs:
  "no_grey_refs_locs \<subseteq> hs_in_sync_locs"
by (auto simp: no_grey_refs_locs_def black_heap_locs_def hs_in_sync_locs_def hs_done_locs_def sweep_locs_def loc_defs
         dest: prefix_same_cases)

lemma get_roots_UN_get_work_locs_subseteq_gc_W_empty_locs:
  "get_roots_UN_get_work_locs \<subseteq> gc_W_empty_locs"
unfolding get_roots_UN_get_work_locs_def
by (auto simp: hs_get_roots_locs_def hs_get_work_locs_def gc_W_empty_locs_def)

end

declare
  gc.obj_fields_marked_locs_subseteq_hp_IdleMarkSweep_locs[locset_cache]
  gc.obj_fields_marked_locs_subseteq_hs_in_sync_locs[locset_cache]
  gc.obj_fields_marked_good_ref_subseteq_hp_IdleMarkSweep_locs[locset_cache]
  gc.mark_loop_mo_mark_loop_field_done_subseteq_hs_in_sync_locs[locset_cache]
  gc.no_grey_refs_locs_subseteq_hs_in_sync_locs[locset_cache]
  gc.get_roots_UN_get_work_locs_subseteq_gc_W_empty_locs[locset_cache]

lemma handshake_obj_fields_markedD:
  "\<lbrakk> atS gc gc.obj_fields_marked_locs s; gc.handshake_invL s \<rbrakk> \<Longrightarrow> sys_ghost_hs_phase s\<down> = hp_IdleMarkSweep \<and> All (ghost_hs_in_sync (s\<down> sys))"
unfolding gc.handshake_invL_def
by (metis (no_types, lifting) atS_mono gc.obj_fields_marked_locs_subseteq_hp_IdleMarkSweep_locs gc.obj_fields_marked_locs_subseteq_hs_in_sync_locs)

lemma obj_fields_marked_good_ref_locs_hp_phaseD:
  "\<lbrakk> atS gc gc.obj_fields_marked_good_ref_locs s; gc.handshake_invL s \<rbrakk>
     \<Longrightarrow> sys_ghost_hs_phase s\<down> = hp_IdleMarkSweep \<and> All (ghost_hs_in_sync (s\<down> sys))"
unfolding gc.handshake_invL_def
by (metis (no_types, lifting) atS_mono gc.mark_loop_mo_mark_loop_field_done_subseteq_hs_in_sync_locs gc.obj_fields_marked_good_ref_subseteq_hp_IdleMarkSweep_locs)

lemma gc_marking_reaches_Mutate:
  assumes xys: "\<forall>y. (x reaches y) s \<longrightarrow> valid_ref y s"
  assumes xy: "(x reaches y) (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                             mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
  assumes sb: "sys_mem_store_buffers (mutator m) s = mw_Mutate r f opt_r' # ws"
  assumes vri: "valid_refs_inv s"
  shows "valid_ref y s"
proof -
  from xy xys
  have "\<exists>z. z \<in> {x} \<union> mut_m.tso_store_refs m s \<and> (z reaches y) s \<and> valid_ref y s"
  proof induct
    case (refl x) then show ?case by auto
  next
    case (step x y z) with sb vri show ?case
      apply (clarsimp simp: points_to_Mutate)
      apply (elim disjE)
         apply (metis (no_types, lifting) obj_at_cong reaches_def rtranclp.rtrancl_into_rtrancl)
        apply (metis (no_types, lifting) obj_at_def option.case(2) reaches_def rtranclp.rtrancl_into_rtrancl valid_refs_invD(4))
       apply clarsimp
       apply (elim disjE)
        apply (rule exI[where x=z])
        apply (clarsimp simp: mut_m.tso_store_refs_def)
        apply (rule valid_refs_invD(3)[where m=m and x=z], auto simp: mut_m.tso_store_refs_def; fail)[1]
       apply (metis (no_types, lifting) obj_at_cong reaches_def rtranclp.rtrancl_into_rtrancl)
      apply clarsimp
      apply (elim disjE)
       apply (rule exI[where x=z])
       apply (clarsimp simp: mut_m.tso_store_refs_def)
       apply (rule valid_refs_invD(3)[where m=m and x=z], auto simp: mut_m.tso_store_refs_def)[1]
      apply (metis (no_types, lifting) obj_at_def option.case(2) reaches_def rtranclp.rtrancl_into_rtrancl valid_refs_invD(4))
      done
  qed
  then show ?thesis by blast
qed

lemma (in sys) gc_obj_fields_marked_invL[intro]:
  notes filter_empty_conv[simp]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.obj_fields_marked_invL
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> gc.obj_fields_marked_invL \<rbrace>"
proof(vcg_jackhammer (keep_locs) (no_thin_post_inv), vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws) show ?case
  proof(cases w)
       case (mw_Mark ref mark) with tso_dequeue_store_buffer show ?thesis
apply -
apply (clarsimp simp: p_not_sys gc.obj_fields_marked_invL_def)
apply (intro conjI impI; clarsimp)

apply (frule (1) handshake_obj_fields_markedD)
apply (clarsimp simp: gc.obj_fields_marked_def)
apply (frule (1) valid_W_invD)
apply (drule_tac x=x in spec)
apply clarsimp
apply (erule obj_at_field_on_heapE)
 apply (force split: obj_at_splits)
apply (force split: obj_at_splits)

apply (erule obj_at_field_on_heapE)
 apply (clarsimp split: obj_at_splits; fail)
apply (clarsimp split: obj_at_splits)
 apply (metis valid_W_invD(1))
apply (metis valid_W_invD(1))

apply (force simp: valid_W_invD(1) split: obj_at_splits)
done
  next case (mw_Mutate r f opt_r') with tso_dequeue_store_buffer show ?thesis
apply -
apply (clarsimp simp: p_not_sys gc.obj_fields_marked_invL_def)
apply (erule disjE; clarsimp)
apply (rename_tac m)
apply (drule_tac m=m in mut_m.handshake_phase_invD; clarsimp simp: hp_step_rel_def)
apply (drule_tac x=m in spec)
apply (intro conjI impI; clarsimp simp: obj_at_field_on_heap_imp_valid_ref gc_marking_reaches_Mutate split: option.splits)

subgoal for m
apply (frule (1) handshake_obj_fields_markedD)
apply (elim disjE; auto simp: gc.obj_fields_marked_def split: option.splits)
done

subgoal for m r'
apply (frule (1) obj_fields_marked_good_ref_locs_hp_phaseD)
apply (elim disjE; clarsimp simp: marked_insertionD)
done
done
  next case (mw_Mutate_Payload r f pl) with tso_dequeue_store_buffer show ?thesis by - (erule gc_obj_fields_marked_invL_niE; clarsimp)
  next case (mw_fA mark) with tso_dequeue_store_buffer show ?thesis by - (erule gc_obj_fields_marked_invL_niE; clarsimp)
  next case (mw_fM mark) with tso_dequeue_store_buffer show ?thesis
        apply -
        apply (clarsimp simp: p_not_sys fM_rel_inv_def fM_rel_def gc.obj_fields_marked_invL_def)
        apply (erule disjE; clarsimp)
        apply (intro conjI impI; clarsimp)
          apply (metis (no_types, lifting) handshake_obj_fields_markedD hs_phase.distinct(7))
         apply (metis (no_types, lifting) hs_phase.distinct(7) obj_fields_marked_good_ref_locs_hp_phaseD)
        apply (metis (no_types, lifting) UnCI elem_set hs_phase.distinct(7) gc.obj_fields_marked_good_ref_locs_def obj_fields_marked_good_ref_locs_hp_phaseD option.simps(15) thin_locs_pre_keep_atSE)
        done
  next case (mw_Phase ph) with tso_dequeue_store_buffer show ?thesis
        by - (erule gc_obj_fields_marked_invL_niE; clarsimp)
  qed
qed


subsection\<open>The infamous termination argument\<close>

lemma (in mut_m) gc_W_empty_mut_inv_eq_imp:
  "eq_imp (\<lambda>m'. sys_W \<^bold>\<otimes> WL (mutator m') \<^bold>\<otimes> sys_ghost_hs_in_sync m')
          gc_W_empty_mut_inv"
by (simp add: eq_imp_def gc_W_empty_mut_inv_def)

lemmas gc_W_empty_mut_inv_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.gc_W_empty_mut_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma (in gc) gc_W_empty_invL_eq_imp:
  "eq_imp (\<lambda>(m', p) s. (AT s gc, s\<down> gc, sys_W s\<down>, WL p s\<down>, sys_ghost_hs_in_sync m' s\<down>))
          gc_W_empty_invL"
by (simp add: eq_imp_def gc_W_empty_invL_def mut_m.gc_W_empty_mut_inv_def no_grey_refs_def grey_def)

lemmas gc_W_empty_invL_niE[nie] =
  iffD1[OF gc.gc_W_empty_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode, rule_format], rotated -1]

lemma gc_W_empty_mut_inv_load_W:
  "\<lbrakk> \<forall>m. mut_m.gc_W_empty_mut_inv m s; \<forall>m. sys_ghost_hs_in_sync m s; WL gc s = {}; WL sys s = {} \<rbrakk>
     \<Longrightarrow> no_grey_refs s"
apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def no_grey_refs_def grey_def)
apply (rename_tac x xa)
apply (case_tac xa)
apply (simp_all add: WL_def)
done

context gc
begin

lemma gc_W_empty_mut_inv_hs_init[iff]:
  "mut_m.gc_W_empty_mut_inv m (s(sys := s sys\<lparr>hs_type := ht, ghost_hs_in_sync := \<langle>False\<rangle>\<rparr>))"
  "mut_m.gc_W_empty_mut_inv m (s(sys := s sys\<lparr>hs_type := ht, ghost_hs_in_sync := \<langle>False\<rangle>, ghost_hs_phase := hp' \<rparr>))"
by (simp_all add: mut_m.gc_W_empty_mut_inv_def)

lemma gc_W_empty_invL[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> LSTP valid_W_inv \<rbrace>
     gc
   \<lbrace> gc_W_empty_invL \<rbrace>"
apply (vcg_jackhammer; (clarsimp elim: gc_W_empty_mut_inv_load_W simp: WL_def)?)
proof vcg_name_cases
     case (mark_loop_get_work_done_loop s s') then show ?case
       by (simp add: WL_def gc_W_empty_mut_inv_load_W valid_W_inv_sys_ghg_empty_iff)
next case (mark_loop_get_roots_done_loop s s') then show ?case
       by (simp add: WL_def gc_W_empty_mut_inv_load_W valid_W_inv_sys_ghg_empty_iff)
qed

end

lemma (in sys) gc_gc_W_empty_invL[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> gc.gc_W_empty_invL \<rbrace> sys"
by vcg_chainsaw

lemma empty_WL_GC:
  "\<lbrakk> atS gc gc.get_roots_UN_get_work_locs s; gc.obj_fields_marked_invL s \<rbrakk> \<Longrightarrow> gc_ghost_honorary_grey s\<down> = {}"
unfolding gc.obj_fields_marked_invL_def
using atS_mono[OF _ gc.get_roots_UN_get_work_locs_subseteq_ghost_honorary_grey_empty_locs]
apply metis
done

lemma gc_hs_get_roots_get_workD:
  "\<lbrakk> atS gc gc.get_roots_UN_get_work_locs s; gc.handshake_invL s \<rbrakk>
     \<Longrightarrow> sys_ghost_hs_phase s\<down> = hp_IdleMarkSweep \<and> sys_hs_type s\<down> \<in> {ht_GetWork, ht_GetRoots}"
unfolding gc.handshake_invL_def
apply clarsimp
apply (metis (no_types, lifting) atS_mono atS_un gc.get_roots_UN_get_work_locs_def gc.hs_get_roots_locs_subseteq_hp_IdleMarkSweep_locs gc.hs_get_work_locs_subseteq_hp_IdleMarkSweep_locs)
done


context gc
begin

lemma handshake_sweep_mark_endD:
  "\<lbrakk> atS gc no_grey_refs_locs s; handshake_invL s; handshake_phase_inv s\<down> \<rbrakk>
     \<Longrightarrow> mut_m.mut_ghost_hs_phase m s\<down> = hp_IdleMarkSweep \<and> All (ghost_hs_in_sync (s\<down> sys))"
apply (simp add: gc.handshake_invL_def)
apply (elim conjE)
apply (drule mp, erule atS_mono[OF _ gc.no_grey_refs_locs_subseteq_hs_in_sync_locs])
apply (drule mut_m.handshake_phase_invD)
apply (simp only: gc.no_grey_refs_locs_def cong del: atS_state_weak_cong)
apply (clarsimp simp: atS_un)
apply (elim disjE)
  apply (drule mp, erule atS_mono[where ls'="gc.hp_IdleMarkSweep_locs"])
   apply (clarsimp simp: gc.black_heap_locs_def locset_cache)
  apply (clarsimp simp: hp_step_rel_def)
  apply blast
 apply (drule mp, erule atS_mono[where ls'="gc.hp_IdleMarkSweep_locs"])
  apply (clarsimp simp: hp_IdleMarkSweep_locs_def hp_step_rel_def)
 apply (clarsimp simp: hp_step_rel_def)
 apply blast
apply (clarsimp simp: atS_simps locset_cache hp_step_rel_def)
apply blast
done

lemma gc_W_empty_mut_mo_co_mark:
  "\<lbrakk> \<forall>x. mut_m.gc_W_empty_mut_inv x s\<down>; mutators_phase_inv s\<down>;
     mut_m.mut_ghost_honorary_grey m s\<down> = {};
     r \<in> mut_m.mut_roots m s\<down> \<union> mut_m.mut_ghost_honorary_root m s\<down>; white r s\<down>;
     atS gc get_roots_UN_get_work_locs s; gc.handshake_invL s; gc.obj_fields_marked_invL s;
     atS gc gc_W_empty_locs s \<longrightarrow> gc_W s\<down> = {};
     handshake_phase_inv s\<down>; valid_W_inv s\<down> \<rbrakk>
    \<Longrightarrow> mut_m.gc_W_empty_mut_inv m' (s\<down>(mutator m := s\<down> (mutator m)\<lparr>ghost_honorary_grey := {r}\<rparr>))"
apply (frule (1) gc_hs_get_roots_get_workD)
apply (frule_tac m=m in mut_m.handshake_phase_invD)
apply (clarsimp simp: hp_step_rel_def simp del: Un_iff)
apply (elim disjE, simp_all)
proof(goal_cases before_get_work past_get_work before_get_roots after_get_roots)
     case before_get_work then show ?thesis
      apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
      apply blast
      done
next case past_get_work then show ?thesis
      apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
      apply (frule spec[where x=m], clarsimp)
      apply (frule (2) mut_m.reachable_snapshot_inv_white_root)
      apply clarsimp
      apply (drule grey_protects_whiteD)
      apply (clarsimp simp: grey_def)
      apply (rename_tac g p)
      apply (case_tac p; clarsimp)
        (* mutator *)
        apply blast
       (* Can't be the GC *)
       apply (frule (1) empty_WL_GC)
       apply (drule mp, erule atS_mono[OF _ get_roots_UN_get_work_locs_subseteq_gc_W_empty_locs])
       apply (clarsimp simp: WL_def; fail)
      (* Can't be sys *)
      apply (clarsimp simp: WL_def valid_W_inv_sys_ghg_empty_iff; fail)
      done
next case before_get_roots then show ?case
      apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
      apply blast
      done
next case after_get_roots then show ?case
      apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
      apply (frule spec[where x=m], clarsimp)
      apply (frule (2) mut_m.reachable_snapshot_inv_white_root)
      apply clarsimp
      apply (drule grey_protects_whiteD)
      apply (clarsimp simp: grey_def)
      apply (rename_tac g p)
      apply (case_tac p; clarsimp)
        (* mutator *)
        apply blast
       (* Can't be the GC *)
       apply (frule (1) empty_WL_GC)
       apply (drule mp, erule atS_mono[OF _ get_roots_UN_get_work_locs_subseteq_gc_W_empty_locs])
       apply (clarsimp simp: WL_def; fail)
      (* Can't be sys *)
      apply (clarsimp simp: WL_def valid_W_inv_sys_ghg_empty_iff; fail)
      done
qed

lemma no_grey_refs_mo_co_mark:
  "\<lbrakk> mutators_phase_inv s\<down>;
     no_grey_refs s\<down>;
     gc.handshake_invL s;
     at gc mark_loop s \<or> at gc mark_loop_get_roots_load_W s \<or> at gc mark_loop_get_work_load_W s \<or> atS gc no_grey_refs_locs s;
     r \<in> mut_m.mut_roots m s\<down> \<union> mut_m.mut_ghost_honorary_root m s\<down>; white r s\<down>;
     handshake_phase_inv s\<down> \<rbrakk>
    \<Longrightarrow> no_grey_refs (s\<down>(mutator m := s\<down> (mutator m)\<lparr>ghost_honorary_grey := {r}\<rparr>))"
apply (elim disjE)
   apply (clarsimp simp: atS_simps gc.handshake_invL_def locset_cache)
   apply (frule mut_m.handshake_phase_invD)
   apply (clarsimp simp: hp_step_rel_def)
   apply (drule spec[where x=m])
   apply (clarsimp simp: conj_disj_distribR[symmetric])
   apply (simp add: handshake_in_syncD mut_m.no_grey_refs_not_rootD; fail)
  apply (clarsimp simp: atS_simps gc.handshake_invL_def locset_cache)
  apply (frule mut_m.handshake_phase_invD)
  apply (clarsimp simp: hp_step_rel_def)
  apply (drule spec[where x=m])
  apply (simp add: handshake_in_syncD mut_m.no_grey_refs_not_rootD; fail)
 apply (clarsimp simp: atS_simps gc.handshake_invL_def locset_cache)
 apply (frule mut_m.handshake_phase_invD)
 apply (clarsimp simp: hp_step_rel_def)
 apply (drule spec[where x=m])
 apply (simp add: handshake_in_syncD mut_m.no_grey_refs_not_rootD; fail)
apply (frule (2) handshake_sweep_mark_endD)
apply (drule spec[where x=m])
apply clarsimp
apply (simp add: handshake_in_syncD mut_m.no_grey_refs_not_rootD; fail)
done

end

context mut_m
begin

lemma gc_W_empty_invL[intro]:
  notes gc.gc_W_empty_mut_mo_co_mark[simp]
  notes gc.no_grey_refs_mo_co_mark[simp]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> mark_object_invL \<^bold>\<and> tso_lock_invL
             \<^bold>\<and> mut_get_roots.mark_object_invL m
             \<^bold>\<and> mut_store_del.mark_object_invL m
             \<^bold>\<and> mut_store_ins.mark_object_invL m
           \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.obj_fields_marked_invL
           \<^bold>\<and> gc.gc_W_empty_invL
             \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     mutator m
   \<lbrace> gc.gc_W_empty_invL \<rbrace>"
proof(vcg_chainsaw gc.gc_W_empty_invL_def, vcg_name_cases)
     case (hs_noop_done s s' x)       then show ?case
      unfolding gc.handshake_invL_def
      by (metis atS_un gc.get_roots_UN_get_work_locs_def hs_type.distinct(1) hs_type.distinct(3))
next case (hs_get_roots_done0 s s' x) then show ?case
      apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def WL_def)
      apply (metis (no_types, lifting))
      done
next case (hs_get_work_done0 s s' x)  then show ?case
      apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def WL_def)
      apply (metis (no_types, lifting))
      done
qed (simp_all add: no_grey_refs_def)

end

context gc
begin

lemma mut_store_old_mark_object_invL[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> sweep_loop_invL \<^bold>\<and> gc_W_empty_invL
      \<^bold>\<and> mut_m.mark_object_invL m
      \<^bold>\<and> mut_store_del.mark_object_invL m
      \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mut_m.mutator_phase_inv m) \<rbrace>
     gc
   \<lbrace> mut_store_del.mark_object_invL m \<rbrace>"
apply (vcg_chainsaw mut_m.mark_object_invL_def mut_m.mut_store_del_mark_object_invL_def2) \<comment> \<open>\<open>at gc sweep_loop_free s\<close>\<close>
  apply (metis (no_types, lifting) handshake_in_syncD mut_m.mutator_phase_inv_aux.simps(5) mut_m.no_grey_refs_not_rootD obj_at_cong white_def)+
done

lemma mut_store_ins_mark_object_invL[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> sweep_loop_invL \<^bold>\<and> gc_W_empty_invL
      \<^bold>\<and> mut_m.mark_object_invL m
      \<^bold>\<and> mut_store_ins.mark_object_invL m
      \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mut_m.mutator_phase_inv m) \<rbrace>
     gc
   \<lbrace> mut_store_ins.mark_object_invL m \<rbrace>"
apply (vcg_chainsaw mut_m.mark_object_invL_def mut_m.mut_store_ins_mark_object_invL_def2) \<comment> \<open>\<open>at gc sweep_loop_free s\<close>\<close>
  apply (metis (no_types, lifting) handshake_in_syncD mut_m.mutator_phase_inv_aux.simps(5) mut_m.no_grey_refs_not_rootD obj_at_cong white_def)+
done

lemma mut_mark_object_invL[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> handshake_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> mut_m.handshake_invL m \<^bold>\<and> mut_m.mark_object_invL m
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> sys_phase_inv) \<rbrace>
     gc
   \<lbrace> mut_m.mark_object_invL m \<rbrace>"
proof(vcg_chainsaw mut_m.handshake_invL_def mut_m.mark_object_invL_def, vcg_name_cases "mutator m") \<comment> \<open>\<open>at gc sweep_loop_free s\<close>\<close>
    case (ins_barrier_locs s s') then show ?case
      apply -
      apply (drule_tac x=m in spec)
      apply (clarsimp simp: fun_upd_apply dest!: handshake_in_syncD split: obj_at_field_on_heap_splits)
       apply (metis (no_types, lifting) mut_m.no_grey_refs_not_rootD obj_at_cong white_def)
      apply (metis (no_types) marked_not_white mut_m.no_grey_refs_not_rootD whiteI)
      done
next case (del_barrier1_locs s s') then show ?case
      apply -
      apply (drule_tac x=m in spec)
      apply (clarsimp simp: fun_upd_apply dest!: handshake_in_syncD split: obj_at_field_on_heap_splits)
       apply (metis (no_types, lifting) mut_m.no_grey_refs_not_rootD obj_at_cong white_def)
      apply (metis (no_types, lifting) marked_not_white mut_m.no_grey_refs_not_rootD obj_at_cong white_def)
      done
qed blast+

end

lemma mut_m_get_roots_no_fM_write:
  "\<lbrakk> mut_m.handshake_invL m s; handshake_phase_inv s\<down>; fM_rel_inv s\<down>; tso_store_inv s\<down> \<rbrakk>
     \<Longrightarrow> atS (mutator m) mut_m.hs_get_roots_locs s \<and> p \<noteq> sys \<longrightarrow> \<not>sys_mem_store_buffers p s\<down> = mw_fM fl # ws"
unfolding mut_m.handshake_invL_def
apply (elim conjE)
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (clarsimp simp: hp_step_rel_def fM_rel_def filter_empty_conv p_not_sys)
apply (metis (full_types) hs_phase.distinct(7) list.set_intros(1) tso_store_invD(4))
done

(* FIXME loads of cut-and-paste here *)
lemma (in sys) mut_mark_object_invL[intro]:
  notes filter_empty_conv[simp]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> mut_m.handshake_invL m \<^bold>\<and> mut_m.mark_object_invL m
     \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_store_inv) \<rbrace>
     sys
   \<lbrace> mut_m.mark_object_invL m \<rbrace>"
proof(vcg_chainsaw mut_m.mark_object_invL_def, vcg_name_cases "mutator m")
  case (hs_get_roots_loop_locs s s' p w ws x) then show ?case
      apply -
      apply (cases w; clarsimp split: obj_at_splits)
       apply (meson valid_W_invD(1))
      apply (simp add: atS_mono mut_m.hs_get_roots_loop_locs_subseteq_hs_get_roots_locs mut_m_get_roots_no_fM_write)
      done
next case (hs_get_roots_loop_done s s' p w ws y) then show ?case
      apply -
      apply (cases w; clarsimp simp: p_not_sys valid_W_invD split: obj_at_splits)
      apply (rename_tac fl obj)
      apply (drule_tac fl=fl and p=p and ws=ws in mut_m_get_roots_no_fM_write; clarsimp)
      apply (drule mp, erule atS_simps, loc_mem)
      apply blast
      done
next case (hs_get_roots_done s s' p w ws x) then show ?case
      apply -
      apply (cases w; clarsimp simp: p_not_sys valid_W_invD split: obj_at_splits)
       apply blast
      apply (rename_tac fl)
      apply (drule_tac fl=fl and p=p and ws=ws in mut_m_get_roots_no_fM_write; clarsimp)
      apply (drule mp, erule atS_simps, loc_mem)
      apply blast
      done
next case (mo_ptest_locs s s' p ws ph') then show ?case by (clarsimp simp: p_not_sys; elim disjE; clarsimp simp: phase_rel_def handshake_in_syncD dest!: phase_rel_invD)
next case (store_ins s s' p w ws y) then show ?case
      apply -
      apply (cases w; clarsimp simp: p_not_sys valid_W_invD split: obj_at_splits)
        apply (metis (no_types, lifting) hs_phase.distinct(3, 5) mut_m.mut_ghost_handshake_phase_idle mut_m_not_idle_no_fM_writeD store_ins(9))
       using valid_refs_invD(9) apply fastforce
      apply (elim disjE; clarsimp simp: phase_rel_def handshake_in_syncD dest!: phase_rel_invD)
      done
next case (del_barrier1_locs s s' p w ws) then show ?case
      proof(cases w)
       case (mw_Mutate r f opt_r') with del_barrier1_locs show ?thesis
apply (clarsimp simp: p_not_sys; elim disjE; clarsimp)
apply (intro conjI impI; clarsimp simp: obj_at_field_on_heap_imp_valid_ref split: option.splits)
 apply (intro conjI impI; clarsimp)
  apply (smt (z3) reachableI(1) valid_refs_invD(8))
 apply (metis (no_types, lifting) marked_insertionD mut_m.mutator_phase_inv_aux.simps(4) mut_m.mutator_phase_inv_aux.simps(5) obj_at_cong reachableI(1) valid_refs_invD(8))
(* brutal *)
apply (rename_tac ma x2)
apply (frule_tac m=m in mut_m.handshake_phase_invD)
apply (frule_tac m=ma in mut_m.handshake_phase_invD)
apply (frule spec[where x=m])
apply (drule_tac x=ma in spec)
apply (clarsimp simp: hp_step_rel_def)
apply (elim disjE; clarsimp simp: marked_insertionD mut_m.mut_ghost_handshake_phase_idle)
done
      next case (mw_fM fl) with del_barrier1_locs mut_m_not_idle_no_fM_writeD show ?thesis by fastforce
      next case (mw_Phase ph) with del_barrier1_locs show ?thesis by (clarsimp simp: p_not_sys; elim disjE; clarsimp simp: phase_rel_def handshake_in_syncD dest!: phase_rel_invD)
      qed (fastforce simp: valid_W_invD split: obj_at_field_on_heap_splits obj_at_splits)+
next case (ins_barrier_locs s s' p w ws) then show ?case
      proof(cases w)
       case (mw_Mutate r f opt_r') with ins_barrier_locs show ?thesis
apply (clarsimp simp: p_not_sys; elim disjE; clarsimp)
apply (intro conjI impI; clarsimp simp: obj_at_field_on_heap_imp_valid_ref split: option.splits)
 apply (intro conjI impI; clarsimp)
  apply (smt (z3) reachableI(1) valid_refs_invD(8))
 apply (metis (no_types, lifting) marked_insertionD mut_m.mutator_phase_inv_aux.simps(4) mut_m.mutator_phase_inv_aux.simps(5) obj_at_cong reachableI(1) valid_refs_invD(8))
(* brutal *)
apply (rename_tac ma x2)
apply (frule_tac m=m in mut_m.handshake_phase_invD)
apply (frule_tac m=ma in mut_m.handshake_phase_invD)
apply (frule spec[where x=m])
apply (drule_tac x=ma in spec)
apply (clarsimp simp: hp_step_rel_def)
apply (elim disjE; clarsimp simp: marked_insertionD mut_m.mut_ghost_handshake_phase_idle)
done
      next case (mw_fM fl) with ins_barrier_locs mut_m_not_idle_no_fM_writeD show ?thesis by fastforce
      next case (mw_Phase ph) with ins_barrier_locs show ?thesis by (clarsimp simp: p_not_sys; elim disjE; clarsimp simp: phase_rel_def handshake_in_syncD dest!: phase_rel_invD)
      qed (fastforce simp: valid_W_invD split: obj_at_field_on_heap_splits obj_at_splits)+
next case (lop_store_ins s s' p w ws y) then show ?case
      apply -
      apply (cases w; clarsimp simp: valid_W_invD(1) split: obj_at_splits)
        apply (metis (no_types, hide_lams) hs_phase.distinct(5,7) mut_m_not_idle_no_fM_write)
       apply (clarsimp simp: p_not_sys; elim disjE; clarsimp simp: phase_rel_def handshake_in_syncD dest!: phase_rel_invD; fail)+
      done
qed


(*<*)

end
(*>*)
