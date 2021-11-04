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

theory StrongTricolour
imports
  Global_Invariants_Lemmas
  Local_Invariants_Lemmas
  Tactics
begin

(*>*)

(* local lemma bucket *)

context mut_m
begin

(* marked insertions *)

lemma marked_insertions_store_ins[simp]:
  "\<lbrakk> marked_insertions s; (\<exists>r'. opt_r' = Some r') \<longrightarrow> marked (the opt_r') s \<rbrakk>
     \<Longrightarrow> marked_insertions
               (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := {}\<rparr>,
                   sys := s sys
                     \<lparr>mem_store_buffers := (mem_store_buffers (s sys))(mutator m := sys_mem_store_buffers (mutator m) s @ [mw_Mutate r f opt_r'])\<rparr>))"
by (auto simp: marked_insertions_def
        split: mem_store_action.splits option.splits)

lemma marked_insertions_alloc[simp]:
  "\<lbrakk> heap (s sys) r' = None; valid_refs_inv s \<rbrakk>
  \<Longrightarrow> marked_insertions (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> obj')\<rparr>))
  \<longleftrightarrow> marked_insertions s"
apply (clarsimp simp: marked_insertions_def split: mem_store_action.splits option.splits)
apply (rule iffI)
 apply clarsimp
 apply (rename_tac ref field x)
 apply (drule_tac x=ref in spec, drule_tac x=field in spec, drule_tac x=x in spec, clarsimp)
 apply (drule valid_refs_invD(6)[where x=r' and y=r'], simp_all)
done


(* marked_deletions *)

lemma marked_deletions_store_ins[simp]:
  "\<lbrakk> marked_deletions s; obj_at_field_on_heap (\<lambda>r'. marked r' s) r f s \<rbrakk>
     \<Longrightarrow> marked_deletions
               (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := {}\<rparr>,
                   sys := s sys
                     \<lparr>mem_store_buffers := (mem_store_buffers (s sys))(mutator m := sys_mem_store_buffers (mutator m) s @ [mw_Mutate r f opt_r'])\<rparr>))"
by (auto simp: marked_deletions_def
        split: mem_store_action.splits option.splits)

lemma marked_deletions_alloc[simp]:
  "\<lbrakk> marked_deletions s; heap (s sys) r' = None; valid_refs_inv s \<rbrakk>
  \<Longrightarrow> marked_deletions (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> obj')\<rparr>))"
apply (clarsimp simp: marked_deletions_def split: mem_store_action.splits)
apply (rename_tac ref field option)
apply (drule_tac x="mw_Mutate ref field option" in spec)
apply clarsimp
apply (case_tac "ref = r'")
 apply (auto simp: obj_at_field_on_heap_def split: option.splits)
done

end


subsection\<open>Sweep loop invariants\<close>

lemma (in gc) sweep_loop_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, sys_fM s\<down>, map_option obj_mark \<circ> sys_heap s\<down>))
          sweep_loop_invL"
apply (clarsimp simp: eq_imp_def inv)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r. valid_ref r s\<down> \<longleftrightarrow> valid_ref r s'\<down>")
 apply (subgoal_tac "\<forall>P r. obj_at (\<lambda>obj. P (obj_mark obj)) r s\<down> \<longleftrightarrow> obj_at (\<lambda>obj. P (obj_mark obj)) r s'\<down>")
  apply (frule_tac x="\<lambda>mark. Some mark = gc_mark s'\<down>" in spec)
  apply (frule_tac x="\<lambda>mark. mark = sys_fM s'\<down>" in spec)
  apply clarsimp
 apply (clarsimp simp: fun_eq_iff split: obj_at_splits)
 apply (rename_tac r)
 apply ( (drule_tac x=r in spec)+, auto)[1]
apply (clarsimp simp: fun_eq_iff split: obj_at_splits)
apply (rename_tac r)
apply (drule_tac x=r in spec, auto)[1]
apply (metis map_option_eq_Some)+
done

lemmas gc_sweep_loop_invL_niE[nie] =
  iffD1[OF gc.sweep_loop_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode, rule_format], rotated -1]

lemma (in gc) sweep_loop_invL[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> phase_invL \<^bold>\<and> sweep_loop_invL \<^bold>\<and> tso_lock_invL
         \<^bold>\<and> LSTP (phase_rel_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> sweep_loop_invL \<rbrace>"
proof(vcg_jackhammer, vcg_name_cases)
     case sweep_loop_ref_done  then show ?case by blast
next case sweep_loop_check     then show ?case
      apply (clarsimp split: obj_at_splits)
      apply (metis (no_types, lifting) option.collapse option.inject)
      done
next case sweep_loop_load_mark then show ?case by (clarsimp split: obj_at_splits)
qed

context gc
begin

lemma sweep_loop_locs_subseteq_sweep_locs:
  "sweep_loop_locs \<subseteq> sweep_locs"
by (auto simp: sweep_loop_locs_def sweep_locs_def intro: append_prefixD)

lemma sweep_locs_subseteq_fM_tso_empty_locs:
  "sweep_locs \<subseteq> fM_tso_empty_locs"
by (auto simp: sweep_locs_def fM_tso_empty_locs_def loc_defs)

lemma sweep_loop_locs_fM_eq_locs:
  "sweep_loop_locs \<subseteq> fM_eq_locs"
by (auto simp: sweep_loop_locs_def fM_eq_locs_def sweep_locs_def loc_defs)

lemma sweep_loop_locs_fA_eq_locs:
  "sweep_loop_locs \<subseteq> fA_eq_locs"
apply (simp add: sweep_loop_locs_def fA_eq_locs_def sweep_locs_def)
apply (intro subset_insertI2)
apply (auto intro: append_prefixD)
done

lemma black_heap_locs_subseteq_fM_tso_empty_locs:
  "black_heap_locs \<subseteq> fM_tso_empty_locs"
by (auto simp: black_heap_locs_def fM_tso_empty_locs_def loc_defs)

lemma black_heap_locs_fM_eq_locs:
  "black_heap_locs \<subseteq> fM_eq_locs"
by (simp add: black_heap_locs_def fM_eq_locs_def loc_defs)

lemma black_heap_locs_fA_eq_locs:
  "black_heap_locs \<subseteq> fA_eq_locs"
by (simp add: black_heap_locs_def fA_eq_locs_def sweep_locs_def loc_defs)

lemma fM_fA_invL_tso_emptyD:
  "\<lbrakk> atS gc ls s; fM_fA_invL s; ls \<subseteq> fM_tso_empty_locs \<rbrakk> \<Longrightarrow> tso_pending_fM gc s\<down> = []"
by (auto simp: fM_fA_invL_def dest: atS_mono)

lemma gc_sweep_loop_invL_locsE[rule_format]:
  "(atS gc (sweep_locs \<union> black_heap_locs) s \<longrightarrow> False) \<Longrightarrow> gc.sweep_loop_invL s"
apply (simp add: gc.sweep_loop_invL_def atS_un)
apply (auto simp: locset_cache atS_simps dest: atS_mono)
 apply (simp add: atS_mono gc.sweep_loop_locs_subseteq_sweep_locs; fail)
apply (clarsimp simp: atS_def)
apply (rename_tac x)
apply (drule_tac x=x in bspec)
apply (auto simp: sweep_locs_def sweep_loop_not_choose_ref_locs_def intro: append_prefixD)
done

end

lemma (in sys) gc_sweep_loop_invL[intro]:
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> gc.gc_W_empty_invL \<^bold>\<and> gc.sweep_loop_invL
       \<^bold>\<and> LSTP (tso_store_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> gc.sweep_loop_invL \<rbrace>"
proof(vcg_jackhammer (keep_locs) (no_thin_post_inv), vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws) then show ?case
  proof(cases w)
       case (mw_Mark r fl) with tso_dequeue_store_buffer show ?thesis
        apply -
        apply (rule gc.gc_sweep_loop_invL_locsE)
        apply (simp only: gc.gc_W_empty_invL_def gc.no_grey_refs_locs_def cong del: atS_state_weak_cong)
        apply (clarsimp simp: atS_un)
        apply (thin_tac "AT _ = _") (* FIXME speed the metis call up a bit *)
        apply (thin_tac "at _ _ _ \<longrightarrow> _")+
        apply (metis (mono_tags, lifting) filter.simps(2) loc_mem_tac_simps(4) no_grey_refs_no_pending_marks)
        done
  next case (mw_Mutate r f opt_r') with tso_dequeue_store_buffer show ?thesis by clarsimp (erule gc_sweep_loop_invL_niE; simp add: fun_eq_iff fun_upd_apply)
  next case (mw_Mutate_Payload r f pl) with tso_dequeue_store_buffer show ?thesis by clarsimp (erule gc_sweep_loop_invL_niE; simp add: fun_eq_iff fun_upd_apply)
  next case (mw_fA fl) with tso_dequeue_store_buffer show ?thesis by - (erule gc_sweep_loop_invL_niE; simp add: fun_eq_iff)
  next case (mw_fM fl) with tso_dequeue_store_buffer show ?thesis
        apply -
        apply (rule gc.gc_sweep_loop_invL_locsE)
        apply (case_tac p; clarsimp)
        apply (drule (1) gc.fM_fA_invL_tso_emptyD)
        apply simp_all
        using gc.black_heap_locs_subseteq_fM_tso_empty_locs gc.sweep_locs_subseteq_fM_tso_empty_locs apply blast
        done
  next case (mw_Phase ph) with tso_dequeue_store_buffer show ?thesis by - (erule gc_sweep_loop_invL_niE; simp add: fun_eq_iff)
  qed
qed

lemma (in mut_m) gc_sweep_loop_invL[intro]:
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.sweep_loop_invL
       \<^bold>\<and> LSTP (mutators_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> gc.sweep_loop_invL \<rbrace>"
proof( vcg_chainsaw (no_thin) gc.fM_fA_invL_def gc.sweep_loop_invL_def gc.handshake_invL_def, vcg_name_cases gc)
     case (sweep_loop_locs s s' rb) then show ?case by (metis (no_types, lifting) atS_mono gc.sweep_loop_locs_fA_eq_locs gc.sweep_loop_locs_fM_eq_locs)
next case (black_heap_locs s s' rb) then show ?case by (metis (no_types, lifting) atS_mono gc.black_heap_locs_fA_eq_locs gc.black_heap_locs_fM_eq_locs)
qed


subsection\<open> Mutator proofs \<close>

context mut_m
begin

(* reachable snapshot inv *)

lemma reachable_snapshot_inv_mo_co_mark[simp]:
  "\<lbrakk> ghost_honorary_grey (s p) = {}; reachable_snapshot_inv s \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(p := s p\<lparr> ghost_honorary_grey := {r} \<rparr>))"
unfolding in_snapshot_def reachable_snapshot_inv_def by (auto simp: fun_upd_apply)

lemma reachable_snapshot_inv_hs_get_roots_done:
  assumes sti: "strong_tricolour_inv s"
  assumes m: "\<forall>r \<in> mut_roots s. marked r s"
  assumes ghr: "mut_ghost_honorary_root s = {}"
  assumes t: "tso_pending_mutate (mutator m) s = []"
  assumes vri: "valid_refs_inv s"
  shows "reachable_snapshot_inv
               (s(mutator m := s (mutator m)\<lparr>W := {}, ghost_hs_phase := ghp'\<rparr>,
                  sys := s sys\<lparr>hs_pending := hp', W := sys_W s \<union> mut_W s, ghost_hs_in_sync := in'\<rparr>))"
  (is "reachable_snapshot_inv ?s'")
proof(rule, clarsimp)
  fix r assume "reachable r s"
  then show "in_snapshot r ?s'"
  proof (induct rule: reachable_induct)
    case (root x) with m show ?case
      apply (clarsimp simp: in_snapshot_def) (* FIXME intro rules *)
      apply (auto dest: marked_imp_black_or_grey)
      done
  next
    case (ghost_honorary_root x) with ghr show ?case by simp
  next
    case (tso_root x) with t show ?case
      apply (clarsimp simp: filter_empty_conv tso_store_refs_def)
      apply (rename_tac w; case_tac w; fastforce)
      done
  next
    case (reaches x y)
    from reaches vri have "valid_ref x s" "valid_ref y s"
      using reachable_points_to by fastforce+
    with reaches sti vri show ?case
      apply (clarsimp simp: in_snapshot_def)
      apply (elim disjE)
       apply (clarsimp simp: strong_tricolour_inv_def)
       apply (drule spec[where x=x])
       apply clarsimp
       apply (auto dest!: marked_imp_black_or_grey)[1]
      apply (cases "white y s")
      apply (auto dest: grey_protects_whiteE
                 dest!: marked_imp_black_or_grey)
        done
    qed
qed

lemma reachable_snapshot_inv_hs_get_work_done:
  "reachable_snapshot_inv s
    \<Longrightarrow> reachable_snapshot_inv
               (s(mutator m := s (mutator m)\<lparr>W := {}\<rparr>,
                   sys := s sys\<lparr>hs_pending := pending', W := sys_W s \<union> mut_W s,
                                ghost_hs_in_sync := (ghost_hs_in_sync (s sys))(m := True)\<rparr>))"
by (simp add: reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)

lemma reachable_snapshot_inv_deref_del:
  "\<lbrakk> reachable_snapshot_inv s; sys_load (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; r \<in> mut_roots s; mut_ghost_honorary_root s = {} \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := Option.set_option opt_r', ref := opt_r'\<rparr>))"
unfolding reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def by (clarsimp simp: fun_upd_apply)

lemma mutator_phase_inv[intro]:
  notes fun_upd_apply[simp]
  notes reachable_snapshot_inv_deref_del[simp]
  notes if_split_asm[split del]
  shows
  "\<lbrace> handshake_invL
       \<^bold>\<and> mark_object_invL
       \<^bold>\<and> mut_get_roots.mark_object_invL m
       \<^bold>\<and> mut_store_del.mark_object_invL m
       \<^bold>\<and> mut_store_ins.mark_object_invL m
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP mutator_phase_inv \<rbrace>"
proof( vcg_jackhammer (no_thin_post_inv)
    , simp_all add: mutator_phase_inv_aux_case split: hs_phase.splits
    , vcg_name_cases)
     case alloc then show ?case
    apply (drule_tac x=m in spec)
    apply (drule handshake_phase_invD)
    apply (clarsimp simp: fA_rel_inv_def fM_rel_inv_def fM_rel_def hp_step_rel_def split: if_split_asm)
    apply (intro conjI impI; simp)
     apply (elim disjE; force simp: fA_rel_def)
    apply (rule reachable_snapshot_inv_alloc, simp_all)
    apply (elim disjE; force simp: fA_rel_def)
    done
next case (store_ins s s') then show ?case
    apply (drule_tac x=m in spec)
    apply (drule handshake_phase_invD)
    apply (intro conjI impI; clarsimp)
      apply (rule marked_deletions_store_ins, assumption) (* FIXME shuffle the following into this lemma *)
      apply (cases "(\<forall>opt_r'. mw_Mutate (mut_tmp_ref s\<down>) (mut_field s\<down>) opt_r' \<notin> set (sys_mem_store_buffers (mutator m) s\<down>))"; clarsimp)
      apply (force simp: marked_deletions_def)
     apply (erule marked_insertions_store_ins)
     apply (drule phase_rel_invD)
     apply (clarsimp simp: phase_rel_def hp_step_rel_def; elim disjE; fastforce dest: reachable_blackD elim: blackD; fail)
    apply (rule marked_deletions_store_ins; clarsimp) (* FIXME as above *)
    apply (erule disjE; clarsimp)
     apply (drule phase_rel_invD)
     apply (clarsimp simp: phase_rel_def)
     apply (elim disjE; clarsimp)
      apply (fastforce simp: hp_step_rel_def)
     apply (clarsimp simp: hp_step_rel_def)
     apply (case_tac "sys_ghost_hs_phase s\<down>"; clarsimp) (* FIXME invert handshake_phase_rel *)
      apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
      apply (rule conjI, fast, clarsimp)
      apply (frule_tac r=x2a in blackD(1)[OF reachable_blackD], simp_all)[1]
      apply (rule_tac x="mut_tmp_ref s\<down>" in reachable_points_to; auto simp: ran_def split: obj_at_splits; fail)
     apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
     apply (rule conjI, fast, clarsimp)
     apply (frule_tac r=x2a in blackD(1)[OF reachable_blackD], simp_all)[1]
     apply (rule_tac x="mut_tmp_ref s\<down>" in reachable_points_to; auto simp: ran_def split: obj_at_splits; fail)
    apply (force simp: marked_deletions_def)
    done
next case (hs_noop_done s s') then show ?case
    apply -
    apply (drule_tac x=m in spec)
    apply (drule handshake_phase_invD)
    apply (simp add: fA_rel_def fM_rel_def hp_step_rel_def)
    apply (cases "mut_ghost_hs_phase s\<down>") (* FIXME invert handshake_step *)
    apply auto
    done
next case (hs_get_roots_done s s') then show ?case
    apply -
    apply (drule_tac x=m in spec)
    apply (drule handshake_phase_invD)
    apply (force simp: hp_step_rel_def reachable_snapshot_inv_hs_get_roots_done)
    done
next case (hs_get_work_done s s') then show ?case
    apply (drule_tac x=m in spec)
    apply (drule handshake_phase_invD)
    apply (force simp add: hp_step_rel_def reachable_snapshot_inv_hs_get_work_done)
    done
qed

end

lemma (in mut_m') mutator_phase_inv[intro]:
  notes mut_m.mark_object_invL_def[inv]
  notes mut_m.handshake_invL_def[inv]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> mut_m.handshake_invL m'
       \<^bold>\<and> mut_m.mark_object_invL m'
       \<^bold>\<and> mut_get_roots.mark_object_invL m'
       \<^bold>\<and> mut_store_del.mark_object_invL m'
       \<^bold>\<and> mut_store_ins.mark_object_invL m'
       \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m'
   \<lbrace> LSTP mutator_phase_inv \<rbrace>"
proof( vcg_jackhammer (no_thin_post_inv)
    , simp_all add: mutator_phase_inv_aux_case split: hs_phase.splits
    , vcg_name_cases)
     case (alloc s s' rb) then show ?case
      apply -
      apply (clarsimp simp: fA_rel_inv_def fM_rel_inv_def white_def)
      apply (drule spec[where x=m])
      apply (intro conjI impI; clarsimp)
       apply (clarsimp simp: hp_step_rel_def simp: fA_rel_def fM_rel_def dest!: handshake_phase_invD)
       apply (elim disjE, auto; fail)
      apply (rule reachable_snapshot_inv_alloc, simp_all)
      apply (clarsimp simp: hp_step_rel_def simp: fA_rel_def fM_rel_def dest!: handshake_phase_invD)
      apply (cases "sys_ghost_hs_phase s\<down>"; clarsimp; blast)
      done
next case (hs_get_roots_done s s') then show ?case
      apply -
      apply (drule spec[where x=m])
      apply (simp add: no_black_refs_def reachable_snapshot_inv_def in_snapshot_def)
      done
next case (hs_get_work_done s s') then show ?case
      apply -
      apply (drule spec[where x=m])
      apply (clarsimp simp: no_black_refs_def reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)
      done
qed

(* FIXME Some of \<open>mutator_phase_inv\<close>, the rest in Global Noninterference *)

lemma no_black_refs_sweep_loop_free[simp]:
  "no_black_refs s \<Longrightarrow> no_black_refs (s(sys := s sys\<lparr>heap := (sys_heap s)(gc_tmp_ref s := None)\<rparr>))"
unfolding no_black_refs_def by simp

lemma no_black_refs_load_W[simp]:
  "\<lbrakk> no_black_refs s; gc_W s = {} \<rbrakk>
     \<Longrightarrow> no_black_refs (s(gc := s gc\<lparr>W := sys_W s\<rparr>, sys := s sys\<lparr>W := {}\<rparr>))"
unfolding no_black_refs_def by simp

lemma marked_insertions_sweep_loop_free[simp]:
  "\<lbrakk> mut_m.marked_insertions m s; white r s \<rbrakk>
     \<Longrightarrow> mut_m.marked_insertions m (s(sys := (s sys)\<lparr>heap := (heap (s sys))(r := None)\<rparr>))"
unfolding mut_m.marked_insertions_def by (fastforce simp: fun_upd_apply split: mem_store_action.splits obj_at_splits option.splits)

lemma marked_deletions_sweep_loop_free[simp]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrakk> mut_m.marked_deletions m s; mut_m.reachable_snapshot_inv m s; no_grey_refs s; white r s \<rbrakk>
     \<Longrightarrow> mut_m.marked_deletions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := None)\<rparr>))"
unfolding mut_m.marked_deletions_def
apply (clarsimp split: mem_store_action.splits)
apply (rename_tac ref field option)
apply (drule_tac x="mw_Mutate ref field option" in spec)
apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
 apply (rule conjI)
  apply (clarsimp simp: mut_m.reachable_snapshot_inv_def)
  apply (drule spec[where x=r], clarsimp simp: in_snapshot_def)
  apply (drule mp, auto simp: mut_m.reachable_def mut_m.tso_store_refs_def split: mem_store_action.splits)[1] (* FIXME rule *)
  apply (drule grey_protects_whiteD)
  apply (clarsimp simp: no_grey_refs_def)
 apply (clarsimp; fail)
apply (rule conjI; clarsimp)
apply (rule conjI)
 apply (clarsimp simp: mut_m.reachable_snapshot_inv_def)
 apply (drule spec[where x=r], clarsimp simp: in_snapshot_def)
 apply (drule mp, auto simp: mut_m.reachable_def mut_m.tso_store_refs_def split: mem_store_action.splits)[1] (* FIXME rule *)
 apply (drule grey_protects_whiteD)
 apply (clarsimp simp: no_grey_refs_def)
unfolding white_def apply (clarsimp split: obj_at_splits)
done

context gc
begin

lemma obj_fields_marked_inv_blacken:
  "\<lbrakk> gc_field_set s = {}; obj_fields_marked s; (gc_tmp_ref s points_to w) s; white w s \<rbrakk> \<Longrightarrow> False"
by (simp add: obj_fields_marked_def obj_at_field_on_heap_def ran_def white_def split: option.splits obj_at_splits)

lemma obj_fields_marked_inv_has_white_path_to_blacken:
  "\<lbrakk> gc_field_set s = {}; gc_tmp_ref s \<in> gc_W s; (gc_tmp_ref s has_white_path_to w) s; obj_fields_marked s; valid_W_inv s \<rbrakk> \<Longrightarrow> w = gc_tmp_ref s"
by (metis (mono_tags, lifting) converse_rtranclpE gc.obj_fields_marked_inv_blacken has_white_path_to_def)

lemma mutator_phase_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> handshake_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> gc_mark.mark_object_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> LSTP (mut_m.mutator_phase_inv m) \<rbrace>"
proof( vcg_jackhammer (no_thin_post_inv)
     , simp_all add: mutator_phase_inv_aux_case white_def split: hs_phase.splits
     , vcg_name_cases )
     case (sweep_loop_free s s') then show ?case
       apply (intro allI conjI impI)
        apply (drule mut_m.handshake_phase_invD[where m=m], clarsimp simp: hp_step_rel_def; fail)
       apply (rule mut_m.reachable_snapshot_inv_sweep_loop_free, simp_all add: white_def)
       done
next case (mark_loop_get_work_load_W s s') then show ?case
      apply clarsimp
      apply (drule spec[where x=m])
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def) (* FIXME rule *)
      done
next case (mark_loop_blacken s s') then show ?case
      apply -
      apply (drule spec[where x=m])
      apply clarsimp
      apply (intro allI conjI impI; clarsimp)
       apply (drule mut_m.handshake_phase_invD[where m=m], clarsimp simp: hp_step_rel_def)
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)
      apply (metis (no_types, hide_lams) obj_fields_marked_inv_has_white_path_to_blacken)
      done
next case (mark_loop_mo_co_mark s s' y) then show ?case by (clarsimp simp: handshake_in_syncD mut_m.reachable_snapshot_inv_mo_co_mark)
next case (mark_loop_get_roots_load_W s s') then show ?case
      apply clarsimp
      apply (drule spec[where x=m])
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def) (* FIXME rule *)
      done
qed

end

lemma (in gc) strong_tricolour_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> gc_mark.mark_object_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> LSTP (strong_tricolour_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> LSTP strong_tricolour_inv \<rbrace>"
unfolding strong_tricolour_inv_def
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (mark_loop_blacken s s' x xa) then show ?case by (fastforce elim!: obj_fields_marked_inv_blacken)
qed

lemma (in mut_m) strong_tricolour[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> mark_object_invL
      \<^bold>\<and> mut_get_roots.mark_object_invL m
      \<^bold>\<and> mut_store_del.mark_object_invL m
      \<^bold>\<and> mut_store_ins.mark_object_invL m
      \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP strong_tricolour_inv \<rbrace>"
unfolding strong_tricolour_inv_def
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (alloc s s' x xa rb) then show ?case
apply (clarsimp simp: fA_rel_inv_def fM_rel_inv_def)
apply (drule handshake_phase_invD)
apply (drule spec[where x=m])
apply (clarsimp simp: sys_phase_inv_aux_case
               split: hs_phase.splits if_splits)

 apply (blast dest: heap_colours_colours)

 (* FIXME rule? *)
 apply (metis (no_types, lifting) black_def no_black_refsD obj_at_cong option.simps(3))
 apply (metis (no_types, lifting) black_def no_black_refsD obj_at_cong option.distinct(1))

 apply (clarsimp simp: hp_step_rel_def)
 apply (elim disjE; force simp: fA_rel_def fM_rel_def split: obj_at_splits)

 apply (clarsimp simp: hp_step_rel_def)
 apply (elim disjE; force simp: fA_rel_def fM_rel_def split: obj_at_splits)
done
qed

(*<*)

end
(*>*)
