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

theory Worklists
imports
  Global_Invariants_Lemmas
  Local_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open>Worklist invariants \label{sec:worklist-invariants} \<close>

lemma valid_W_invD0:
  "\<lbrakk> r \<in> W (s p); valid_W_inv s; p \<noteq> q \<rbrakk> \<Longrightarrow> r \<notin> WL q s"
  "\<lbrakk> r \<in> W (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> r \<notin> ghost_honorary_grey (s q)"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> r \<notin> W (s q)"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); valid_W_inv s; p \<noteq> q \<rbrakk> \<Longrightarrow> r \<notin> WL q s"
using marked_not_white unfolding valid_W_inv_def WL_def by (auto 0 5 split: obj_at_splits)

lemma valid_W_distinct_simps:
  "\<lbrakk>r \<in> ghost_honorary_grey (s p); valid_W_inv s\<rbrakk> \<Longrightarrow> (r \<in> ghost_honorary_grey (s q)) \<longleftrightarrow> (p = q)"
  "\<lbrakk>r \<in> W (s p); valid_W_inv s\<rbrakk> \<Longrightarrow> (r \<in> W (s q)) \<longleftrightarrow> (p = q)"
  "\<lbrakk>r \<in> WL p s; valid_W_inv s\<rbrakk> \<Longrightarrow> (r \<in> WL q s) \<longleftrightarrow> (p = q)"
  using valid_W_invD0(4) apply fastforce
 using valid_W_invD0(1) apply fastforce
apply (metis UnE WL_def valid_W_invD0(1) valid_W_invD0(4))
done

lemma valid_W_inv_sys_mem_store_buffersD:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mutate r' f r'' # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
  "\<lbrakk> sys_mem_store_buffers p s = mw_fA fl' # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
  "\<lbrakk> sys_mem_store_buffers p s = mw_fM fl' # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
  "\<lbrakk> sys_mem_store_buffers p s = mw_Phase ph # ws; mw_Mark r fl \<in> set ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = [mw_Mark r fl]"
unfolding valid_W_inv_def white_def by (clarsimp dest!: spec[where x=p], blast)+

lemma valid_W_invE2:
  "\<lbrakk> r \<in> W (s p); valid_W_inv s; \<And>obj. obj_mark obj = sys_fM s \<Longrightarrow> P obj\<rbrakk> \<Longrightarrow> obj_at P r s"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); sys_mem_lock s \<noteq> Some p; valid_W_inv s; \<And>obj. obj_mark obj = sys_fM s \<Longrightarrow> P obj \<rbrakk> \<Longrightarrow> obj_at P r s"
unfolding valid_W_inv_def
apply (simp_all add:  split: obj_at_splits)
apply blast+
done

lemma (in sys) valid_W_inv[intro]:
  notes if_split_asm[split del]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP (fM_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP valid_W_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws) then show ?case
  proof(cases w)
       case (mw_Mark r fl) with tso_dequeue_store_buffer show ?thesis
apply (subst valid_W_inv_def)
apply clarsimp
apply (frule (1) valid_W_invD(1))
apply (clarsimp simp: all_conj_distrib white_def valid_W_inv_sys_ghg_empty_iff filter_empty_conv obj_at_simps)
apply (intro allI conjI impI)
apply (auto elim: valid_W_invE2)[3]
apply (meson Int_emptyI valid_W_distinct_simps(3))
apply (meson valid_W_invD0(2))
apply (meson valid_W_invD0(2))
using valid_W_invD(2) apply fastforce
apply auto[1]
using valid_W_invD(2) apply fastforce
done
  next case (mw_fM fl) with tso_dequeue_store_buffer show ?thesis
        apply (clarsimp simp: fM_rel_inv_def fM_rel_def p_not_sys)
        apply (elim disjE; clarsimp)
        apply (frule (1) no_grey_refs_no_pending_marks)
        apply (subst valid_W_inv_def)
        apply clarsimp
        apply (meson Int_emptyI no_grey_refsD(1) no_grey_refsD(3) valid_W_distinct_simps(3) valid_W_invD(2) valid_W_inv_sys_ghg_empty_iff valid_W_inv_sys_mem_store_buffersD(3))
        done
  qed simp_all
qed

(* Lemmas for key mark_object transitions *)

lemma valid_W_inv_ghg_disjoint:
  "\<lbrakk> white y s; sys_mem_lock s = Some p; valid_W_inv s; p0 \<noteq> p1 \<rbrakk>
     \<Longrightarrow> WL p0 (s(p := s p\<lparr>ghost_honorary_grey := {y}\<rparr>)) \<inter> WL p1 (s(p := s p\<lparr>ghost_honorary_grey := {y}\<rparr>)) = {}"
unfolding valid_W_inv_def WL_def by (auto 5 5 simp: fun_upd_apply)

lemma valid_W_inv_mo_co_mark:
  "\<lbrakk> valid_W_inv s; white y s; sys_mem_lock s = Some p; filter is_mw_Mark (sys_mem_store_buffers p s) = []; p \<noteq> sys \<rbrakk>
    \<Longrightarrow> valid_W_inv (s(p := s p\<lparr>ghost_honorary_grey := {y}\<rparr>, sys := s sys\<lparr>mem_store_buffers := (mem_store_buffers (s sys))(p := sys_mem_store_buffers p s @ [mw_Mark y (sys_fM s)])\<rparr>))"
apply (subst valid_W_inv_def)
apply (clarsimp simp: all_conj_distrib fun_upd_apply)
apply (intro allI conjI impI)
apply (auto simp: valid_W_invD valid_W_distinct_simps(3) valid_W_inv_sys_ghg_empty_iff valid_W_invD0 valid_W_inv_ghg_disjoint valid_W_inv_colours)
done

lemma valid_W_inv_mo_co_lock:
  "\<lbrakk> valid_W_inv s; sys_mem_lock s = None \<rbrakk>
    \<Longrightarrow> valid_W_inv (s(sys := s sys\<lparr>mem_lock := Some p\<rparr>))"
by (auto simp: valid_W_inv_def fun_upd_apply) (* FIXME some eager rule expects valid_W_inv *)

lemma valid_W_inv_mo_co_W:
  "\<lbrakk> valid_W_inv s; marked y s; ghost_honorary_grey (s p) = {y}; p \<noteq> sys \<rbrakk>
    \<Longrightarrow> valid_W_inv (s(p := s p\<lparr>W := insert y (W (s p)), ghost_honorary_grey := {}\<rparr>))"
apply (subst valid_W_inv_def)
apply (clarsimp simp: all_conj_distrib valid_W_invD0(2) fun_upd_apply)
apply (intro allI conjI impI)
apply (auto simp: valid_W_invD valid_W_invD0(2) valid_W_distinct_simps(3))
 using valid_W_distinct_simps(1) apply fastforce
apply (metis marked_not_white singletonD valid_W_invD(2))
done

lemma valid_W_inv_mo_co_unlock:
  "\<lbrakk> sys_mem_lock s = Some p; sys_mem_store_buffers p s = [];
     \<And>r. r \<in> ghost_honorary_grey (s p) \<Longrightarrow> marked r s;
     valid_W_inv s
   \<rbrakk> \<Longrightarrow> valid_W_inv (s(sys := mem_lock_update Map.empty (s sys)))"
unfolding valid_W_inv_def by (clarsimp simp: fun_upd_apply) (metis emptyE empty_set)

lemma (in gc) valid_W_inv[intro]:
  notes if_split_asm[split del]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> gc_mark.mark_object_invL \<^bold>\<and> gc_W_empty_invL
       \<^bold>\<and> obj_fields_marked_invL
       \<^bold>\<and> sweep_loop_invL \<^bold>\<and> tso_lock_invL
       \<^bold>\<and> LSTP valid_W_inv \<rbrace>
     gc
   \<lbrace> LSTP valid_W_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
     case (sweep_loop_free s s') then show ?case
      apply (subst valid_W_inv_def)
      apply (clarsimp simp: all_conj_distrib white_def valid_W_inv_sys_ghg_empty_iff)
      apply (meson disjoint_iff_not_equal no_grey_refsD(1) no_grey_refsD(2) no_grey_refsD(3) valid_W_invE(5))
      done
next case (mark_loop_get_work_load_W s s') then show ?case
      apply (subst valid_W_inv_def)
      apply (clarsimp simp: all_conj_distrib)
      apply (intro allI conjI impI; auto dest: valid_W_invD0 valid_W_invD simp: valid_W_distinct_simps split: if_splits process_name.splits)
      done
next case (mark_loop_blacken s s') then show ?case
      apply (subst valid_W_inv_def)
      apply (clarsimp simp: all_conj_distrib)
      apply (intro allI conjI impI; auto dest: valid_W_invD0 valid_W_invD simp: valid_W_distinct_simps split: if_splits process_name.splits)
      done
next case (mark_loop_mo_co_W s s' y)      then show ?case by - (erule valid_W_inv_mo_co_W; blast)
next case (mark_loop_mo_co_unlock s s' y) then show ?case by - (erule valid_W_inv_mo_co_unlock; simp split: if_splits)
next case (mark_loop_mo_co_mark s s' y)   then show ?case by - (erule valid_W_inv_mo_co_mark; blast)
next case (mark_loop_mo_co_lock s s' y)   then show ?case by - (erule valid_W_inv_mo_co_lock; assumption+)
next case (mark_loop_get_roots_load_W s s') then show ?case
(* FIXME ran out of patience. Something makes auto diverge on some subgoals *)
      apply (subst valid_W_inv_def)
      apply (clarsimp simp: all_conj_distrib valid_W_inv_sys_ghg_empty_iff)
      apply (intro allI conjI impI)
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
 apply (clarsimp split: process_name.splits)
 apply (meson Int_emptyI Un_iff process_name.distinct(4) valid_W_distinct_simps(3) valid_W_invD0(1))
apply (auto simp: valid_W_invD valid_W_invD0 split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
 using valid_W_invD(2) valid_W_inv_sys_ghg_empty_iff apply fastforce
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
apply (auto simp: valid_W_invD valid_W_invD0 valid_W_inv_sys_ghg_empty_iff split: process_name.splits; fail)[1]
done
qed

lemma (in mut_m) valid_W_inv[intro]:
  notes if_split_asm[split del]
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> mark_object_invL \<^bold>\<and> tso_lock_invL
      \<^bold>\<and> mut_get_roots.mark_object_invL m
      \<^bold>\<and> mut_store_del.mark_object_invL m
      \<^bold>\<and> mut_store_ins.mark_object_invL m
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP valid_W_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
     case (alloc s s' r) then show ?case
      apply (subst valid_W_inv_def)
      apply (clarsimp simp: all_conj_distrib split: if_split_asm)
      apply (intro allI conjI impI)
      apply (auto simp: valid_W_distinct_simps valid_W_invD0(3) valid_W_invD(2))
      done
next case (store_ins_mo_co_W s s' y)      then show ?case by - (erule valid_W_inv_mo_co_W; blast+)
next case (store_ins_mo_co_unlock s s' y) then show ?case by - (erule valid_W_inv_mo_co_unlock; simp split: if_splits)
next case (store_ins_mo_co_mark s s' y)   then show ?case by - (erule valid_W_inv_mo_co_mark; blast+)
next case (store_ins_mo_co_lock s s' y)   then show ?case by - (erule valid_W_inv_mo_co_lock; assumption+)
next case (store_del_mo_co_W s s' y)      then show ?case by - (erule valid_W_inv_mo_co_W; blast+)
next case (store_del_mo_co_unlock s s' y) then show ?case by - (erule valid_W_inv_mo_co_unlock; simp split: if_splits)
next case (store_del_mo_co_mark s s' y)   then show ?case by - (erule valid_W_inv_mo_co_mark; blast+)
next case (store_del_mo_co_lock s s' y)   then show ?case by - (erule valid_W_inv_mo_co_lock; assumption+)
next case (hs_get_roots_loop_mo_co_W s s' y)      then show ?case by - (erule valid_W_inv_mo_co_W; blast+)
next case (hs_get_roots_loop_mo_co_unlock s s' y) then show ?case by - (erule valid_W_inv_mo_co_unlock; simp split: if_splits)
next case (hs_get_roots_loop_mo_co_mark s s' y)   then show ?case by - (erule valid_W_inv_mo_co_mark; blast+)
next case (hs_get_roots_loop_mo_co_lock s s' y)   then show ?case by - (erule valid_W_inv_mo_co_lock; assumption+)
next case (hs_get_roots_done s s') then show ?case
      apply (subst valid_W_inv_def)
      apply (simp add: all_conj_distrib)
      apply (intro allI conjI impI; clarsimp simp: valid_W_inv_sys_ghg_empty_iff valid_W_invD(2) valid_W_invD0(2,3) filter_empty_conv dest!: valid_W_invE(5))
      apply (fastforce simp: valid_W_distinct_simps split: process_name.splits if_splits)
      done
next case (hs_get_work_done s s')  then show ?case
      apply (subst valid_W_inv_def)
      apply (simp add: all_conj_distrib)
      apply (intro allI conjI impI; clarsimp simp: valid_W_inv_sys_ghg_empty_iff valid_W_invD(2) valid_W_invD0(2,3) filter_empty_conv dest!: valid_W_invE(5))
      apply (fastforce simp: valid_W_distinct_simps split: process_name.splits if_splits)
      done
qed

(*<*)

end
(*>*)
