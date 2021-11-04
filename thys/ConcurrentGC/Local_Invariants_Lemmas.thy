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

theory Local_Invariants_Lemmas
imports
  Local_Invariants
begin

declare subst_all [simp del] [[simproc del: defined_all]]

(*>*)
section\<open>Local invariants lemma bucket\<close>


subsection\<open> Location facts\<close>

(* FIXME loads more in StrongTricolour. These might be mostly about non-interference, in which case it might make sense to
   split those proofs off into a separate theory? *)

context mut_m
begin

lemma hs_get_roots_loop_locs_subseteq_hs_get_roots_locs:
  "hs_get_roots_loop_locs \<subseteq> hs_get_roots_locs"
unfolding hs_get_roots_loop_locs_def hs_get_roots_locs_def by (fastforce intro: append_prefixD)

lemma hs_pending_locs_subseteq_hs_pending_loaded_locs:
  "hs_pending_locs \<subseteq> hs_pending_loaded_locs"
unfolding hs_pending_locs_def hs_pending_loaded_locs_def by (fastforce intro: append_prefixD)

lemma ht_loaded_locs_subseteq_hs_pending_loaded_locs:
  "ht_loaded_locs \<subseteq> hs_pending_loaded_locs"
unfolding ht_loaded_locs_def hs_pending_loaded_locs_def by (fastforce intro: append_prefixD)

lemma hs_noop_locs_subseteq_hs_pending_loaded_locs:
  "hs_noop_locs \<subseteq> hs_pending_loaded_locs"
unfolding hs_noop_locs_def hs_pending_loaded_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_noop_locs_subseteq_hs_pending_locs:
  "hs_noop_locs \<subseteq> hs_pending_locs"
unfolding hs_noop_locs_def hs_pending_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_noop_locs_subseteq_ht_loaded_locs:
  "hs_noop_locs \<subseteq> ht_loaded_locs"
unfolding hs_noop_locs_def ht_loaded_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_get_roots_locs_subseteq_hs_pending_loaded_locs:
  "hs_get_roots_locs \<subseteq> hs_pending_loaded_locs"
unfolding hs_get_roots_locs_def hs_pending_loaded_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_get_roots_locs_subseteq_hs_pending_locs:
  "hs_get_roots_locs \<subseteq> hs_pending_locs"
unfolding hs_get_roots_locs_def hs_pending_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_get_roots_locs_subseteq_ht_loaded_locs:
  "hs_get_roots_locs \<subseteq> ht_loaded_locs"
unfolding hs_get_roots_locs_def ht_loaded_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_get_work_locs_subseteq_hs_pending_loaded_locs:
  "hs_get_work_locs \<subseteq> hs_pending_loaded_locs"
unfolding hs_get_work_locs_def hs_pending_loaded_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_get_work_locs_subseteq_hs_pending_locs:
  "hs_get_work_locs \<subseteq> hs_pending_locs"
unfolding hs_get_work_locs_def hs_pending_locs_def loc_defs by (fastforce intro: append_prefixD)

lemma hs_get_work_locs_subseteq_ht_loaded_locs:
  "hs_get_work_locs \<subseteq> ht_loaded_locs"
unfolding hs_get_work_locs_def ht_loaded_locs_def loc_defs by (fastforce intro: append_prefixD)

end

declare
  mut_m.hs_get_roots_loop_locs_subseteq_hs_get_roots_locs[locset_cache]
  mut_m.hs_pending_locs_subseteq_hs_pending_loaded_locs[locset_cache]
  mut_m.ht_loaded_locs_subseteq_hs_pending_loaded_locs[locset_cache]
  mut_m.hs_noop_locs_subseteq_hs_pending_loaded_locs[locset_cache]
  mut_m.hs_noop_locs_subseteq_hs_pending_locs[locset_cache]
  mut_m.hs_noop_locs_subseteq_ht_loaded_locs[locset_cache]
  mut_m.hs_get_roots_locs_subseteq_hs_pending_loaded_locs[locset_cache]
  mut_m.hs_get_roots_locs_subseteq_hs_pending_locs[locset_cache]
  mut_m.hs_get_roots_locs_subseteq_ht_loaded_locs[locset_cache]
  mut_m.hs_get_work_locs_subseteq_hs_pending_loaded_locs[locset_cache]
  mut_m.hs_get_work_locs_subseteq_hs_pending_locs[locset_cache]
  mut_m.hs_get_work_locs_subseteq_ht_loaded_locs[locset_cache]

context gc
begin

lemma get_roots_UN_get_work_locs_subseteq_ghost_honorary_grey_empty_locs:
  "get_roots_UN_get_work_locs \<subseteq> ghost_honorary_grey_empty_locs"
unfolding get_roots_UN_get_work_locs_def ghost_honorary_grey_empty_locs_def hs_get_roots_locs_def hs_get_work_locs_def loc_defs
by (fastforce intro: append_prefixD)

lemma hs_get_roots_locs_subseteq_hp_IdleMarkSweep_locs:
  "hs_get_roots_locs \<subseteq> hp_IdleMarkSweep_locs"
by (auto simp: hs_get_roots_locs_def hp_IdleMarkSweep_locs_def mark_loop_locs_def
        intro: append_prefixD)

lemma hs_get_work_locs_subseteq_hp_IdleMarkSweep_locs:
  "hs_get_work_locs \<subseteq> hp_IdleMarkSweep_locs"
apply (simp add: hs_get_work_locs_def hp_IdleMarkSweep_locs_def mark_loop_locs_def loc_defs)
apply clarsimp
apply (drule mp)
 apply (auto intro: append_prefixD)[1]
apply auto
done

end

declare
  gc.get_roots_UN_get_work_locs_subseteq_ghost_honorary_grey_empty_locs[locset_cache]
  gc.hs_get_roots_locs_subseteq_hp_IdleMarkSweep_locs[locset_cache]
  gc.hs_get_work_locs_subseteq_hp_IdleMarkSweep_locs[locset_cache]


subsection\<open> \<open>obj_fields_marked_inv\<close> \<close>

context gc
begin

lemma obj_fields_marked_eq_imp:
  "eq_imp (\<lambda>r'. gc_field_set \<^bold>\<otimes> gc_tmp_ref \<^bold>\<otimes> (\<lambda>s. map_option obj_fields (sys_heap s r')) \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r')) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> tso_pending_mutate gc)
          obj_fields_marked"
unfolding eq_imp_def obj_fields_marked_def obj_at_field_on_heap_def obj_at_def
apply (clarsimp simp: all_conj_distrib)
apply (rule iffI; clarsimp split: option.splits)
 apply (intro allI conjI impI)
   apply simp_all
  apply (metis (no_types, hide_lams) option.distinct(1) option.map_disc_iff)
 apply (metis (no_types, lifting) option.distinct(1) option.map_sel option.sel)
apply (intro allI conjI impI)
  apply simp_all
 apply (metis (no_types, hide_lams) option.distinct(1) option.map_disc_iff)
apply (metis (no_types, lifting) option.distinct(1) option.map_sel option.sel)
done

lemma obj_fields_marked_UNIV[iff]:
  "obj_fields_marked (s(gc := (s gc)\<lparr> field_set := UNIV \<rparr>))"
unfolding obj_fields_marked_def by (simp add: fun_upd_apply)

lemma obj_fields_marked_invL_eq_imp:
  "eq_imp (\<lambda>r' s. (AT s gc, s\<down> gc, map_option obj_fields (sys_heap s\<down> r'), map_option obj_mark (sys_heap s\<down> r'), sys_fM s\<down>, sys_W s\<down>, tso_pending_mutate gc s\<down>))
          obj_fields_marked_invL"
unfolding eq_imp_def inv obj_at_def obj_at_field_on_heap_def
apply (clarsimp simp: all_conj_distrib cong: option.case_cong)
apply (rule iffI)
 apply (intro conjI impI; clarsimp)
    apply (subst eq_impD[OF obj_fields_marked_eq_imp]; force)
   apply (clarsimp split: option.split_asm)
    apply (metis (no_types, lifting) None_eq_map_option_iff option.simps(3))
    apply (metis (no_types, lifting) option.distinct(1) option.map_sel option.sel)
    apply (metis (no_types, lifting) None_eq_map_option_iff option.simps(3))
    apply (metis (no_types, lifting) option.distinct(1) option.map_sel option.sel)
  apply (subst (asm) (2) eq_impD[OF reaches_eq_imp])
   prefer 2 apply (drule spec, drule mp, assumption)
   apply (metis (no_types) option.disc_eq_case(2) option.map_disc_iff)
  apply (metis option.set_map)
 apply (clarsimp split: option.splits)
  apply (metis (no_types, hide_lams) atS_simps(2) atS_un obj_fields_marked_good_ref_locs_def)
  apply (metis (no_types, hide_lams) map_option_eq_Some option.inject option.simps(9))
  apply (metis (no_types, hide_lams) map_option_eq_Some option.inject option.simps(9))
  apply (metis (no_types, hide_lams) map_option_eq_Some option.inject option.simps(9))
(* cut and paste *)
apply (intro conjI impI; clarsimp)
   apply (subst eq_impD[OF obj_fields_marked_eq_imp]; force)
  apply (clarsimp split: option.split_asm)
   apply (metis (no_types, lifting) None_eq_map_option_iff option.simps(3))
   apply (metis (no_types, lifting) option.distinct(1) option.map_sel option.sel)
   apply (metis (no_types, lifting) None_eq_map_option_iff option.simps(3))
   apply (metis (no_types, lifting) option.distinct(1) option.map_sel option.sel)
 apply (subst (asm) (2) eq_impD[OF reaches_eq_imp])
  prefer 2 apply (drule spec, drule mp, assumption)
  apply (metis (no_types, lifting) None_eq_map_option_iff option.case_eq_if)
 apply (metis option.set_map)
apply (clarsimp split: option.splits)
 apply (metis (no_types, hide_lams) atS_simps(2) atS_un obj_fields_marked_good_ref_locs_def)
 apply (metis (no_types, hide_lams) map_option_eq_Some option.inject option.simps(9))
 apply (metis (no_types, hide_lams) map_option_eq_Some option.inject option.simps(9))
 apply (metis (no_types, hide_lams) map_option_eq_Some option.inject option.simps(9))
done

lemma obj_fields_marked_mark_field_done[iff]:
  "\<lbrakk> obj_at_field_on_heap (\<lambda>r. marked r s) (gc_tmp_ref s) (gc_field s) s; obj_fields_marked s \<rbrakk>
     \<Longrightarrow> obj_fields_marked (s(gc := (s gc)\<lparr>field_set := gc_field_set s - {gc_field s}\<rparr>))"
unfolding obj_fields_marked_def obj_at_field_on_heap_def by (fastforce simp: fun_upd_apply split: option.splits obj_at_splits)+

end

lemmas gc_obj_fields_marked_inv_fun_upd[simp] = eq_imp_fun_upd[OF gc.obj_fields_marked_eq_imp, simplified eq_imp_simps, rule_format]
lemmas gc_obj_fields_marked_invL_niE[nie] = iffD1[OF gc.obj_fields_marked_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]


subsection\<open> mark object \<close>

context mark_object
begin

lemma mark_object_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s p, s\<down> p, sys_heap s\<down>, sys_fM s\<down>, sys_mem_store_buffers p s\<down>))
          mark_object_invL"
unfolding eq_imp_def
apply clarsimp
apply (rename_tac s s')
apply (cut_tac s="s\<down>" and s'="s'\<down>" in eq_impD[OF p_ph_enabled_eq_imp], simp)
apply (clarsimp simp: mark_object_invL_def obj_at_def white_def
                cong: option.case_cong)
done

lemmas mark_object_invL_niE[nie] =
  iffD1[OF mark_object_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

end

lemma mut_m_mark_object_invL_eq_imp:
  "eq_imp (\<lambda>r s. (AT s (mutator m), s\<down> (mutator m), sys_heap s\<down> r, sys_fM s\<down>, sys_phase s\<down>, tso_pending_mutate (mutator m) s\<down>))
          (mut_m.mark_object_invL m)"
apply (clarsimp simp: eq_imp_def mut_m.mark_object_invL_def fun_eq_iff[symmetric] obj_at_field_on_heap_def
                cong: option.case_cong)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r. marked r s\<down> \<longleftrightarrow> marked r s'\<down>")
 apply (subgoal_tac "\<forall>r. valid_null_ref r s\<down> \<longleftrightarrow> valid_null_ref r s'\<down>")
  apply (subgoal_tac "\<forall>r f opt_r'. mw_Mutate r f opt_r' \<notin> set (sys_mem_store_buffers (mutator m) s\<down>)
                               \<longleftrightarrow> mw_Mutate r f opt_r' \<notin> set (sys_mem_store_buffers (mutator m) s'\<down>)")
   apply (clarsimp cong: option.case_cong)
  apply (metis (mono_tags, lifting) filter_set member_filter)
 apply (clarsimp simp: obj_at_def valid_null_ref_def split: option.splits)
apply (clarsimp simp: obj_at_def valid_null_ref_def split: option.splits)
done

lemmas mut_m_mark_object_invL_niE[nie] =
  iffD1[OF mut_m_mark_object_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

(*<*)

end
(*>*)
