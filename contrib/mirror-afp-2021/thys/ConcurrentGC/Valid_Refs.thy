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

theory Valid_Refs
imports
  Global_Invariants_Lemmas
  Local_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open> Valid refs inv proofs \<close>

lemma valid_refs_inv_sweep_loop_free:
  assumes "valid_refs_inv s"
  assumes ngr: "no_grey_refs s"
  assumes rsi: "\<forall>m'. mut_m.reachable_snapshot_inv m' s"
  assumes "white r' s"
  shows "valid_refs_inv (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := None)\<rparr>))"
using assms unfolding valid_refs_inv_def grey_reachable_def no_grey_refs_def
apply (clarsimp dest!: reachable_sweep_loop_free)
apply (drule mut_m.reachable_blackD[OF ngr spec[OF rsi]])
apply (auto split: obj_at_splits)
done

lemma (in gc) valid_refs_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> gc_mark.mark_object_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> phase_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> LSTP valid_refs_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
     case (sweep_loop_free s s') then show ?case
apply -
apply (drule (1) handshake_in_syncD)
apply (rule valid_refs_inv_sweep_loop_free, assumption, assumption)
 apply (simp; fail)
apply (simp add: white_def) (* FIXME rule? *)
done
qed (auto simp: valid_refs_inv_def grey_reachable_def)

context mut_m
begin

lemma valid_refs_inv_discard_roots:
  "\<lbrakk> valid_refs_inv s; roots' \<subseteq> mut_roots s \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>roots := roots'\<rparr>))"
unfolding valid_refs_inv_def mut_m.reachable_def by (auto simp: fun_upd_apply)

lemma valid_refs_inv_load:
  "\<lbrakk> valid_refs_inv s; sys_load (mutator m) (mr_Ref r f) (s sys) = mv_Ref r'; r \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>roots := mut_roots s \<union> Option.set_option r'\<rparr>))"
unfolding valid_refs_inv_def by (simp add: fun_upd_apply)

lemma valid_refs_inv_alloc:
  "\<lbrakk> valid_refs_inv s; sys_heap s r' = None \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>roots := insert r' (mut_roots s)\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))"
unfolding valid_refs_inv_def mut_m.reachable_def
apply (clarsimp simp: fun_upd_apply)
apply (auto elim: converse_reachesE split: obj_at_splits)
done

lemma valid_refs_inv_store_ins:
  "\<lbrakk> valid_refs_inv s; r \<in> mut_roots s; (\<exists>r'. opt_r' = Some r') \<longrightarrow> the opt_r' \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr> ghost_honorary_root := {} \<rparr>,
                          sys := s sys\<lparr> mem_store_buffers := (mem_store_buffers (s sys))(mutator m := sys_mem_store_buffers (mutator m) s @ [mw_Mutate r f opt_r']) \<rparr>))"
apply (subst valid_refs_inv_def)
apply (auto simp: grey_reachable_def mut_m.reachable_def fun_upd_apply)
(* FIXME what's gone wrong here? *)
apply (subst (asm) tso_store_refs_simps; force)+
done

lemma valid_refs_inv_deref_del:
  "\<lbrakk> valid_refs_inv s; sys_load (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; r \<in> mut_roots s; mut_ghost_honorary_root s = {} \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := Option.set_option opt_r', ref := opt_r'\<rparr>))"
unfolding valid_refs_inv_def by (simp add: fun_upd_apply)

lemma valid_refs_inv_mo_co_mark:
  "\<lbrakk> r \<in> mut_roots s \<union> mut_ghost_honorary_root s; mut_ghost_honorary_grey s = {}; valid_refs_inv s \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>ghost_honorary_grey := {r}\<rparr>))"
unfolding valid_refs_inv_def
apply (clarsimp simp: grey_reachable_def fun_upd_apply)
apply (metis grey_reachable_def valid_refs_invD(1) valid_refs_invD(10) valid_refs_inv_def)
done

lemma valid_refs_inv[intro]:
  notes fun_upd_apply[simp]
  notes valid_refs_inv_discard_roots[simp]
  notes valid_refs_inv_load[simp]
  notes valid_refs_inv_alloc[simp]
  notes valid_refs_inv_store_ins[simp]
  notes valid_refs_inv_deref_del[simp]
  notes valid_refs_inv_mo_co_mark[simp]
  shows
  "\<lbrace> mark_object_invL
       \<^bold>\<and> mut_get_roots.mark_object_invL m
       \<^bold>\<and> mut_store_del.mark_object_invL m
       \<^bold>\<and> mut_store_ins.mark_object_invL m
       \<^bold>\<and> LSTP valid_refs_inv \<rbrace>
     mutator m
   \<lbrace> LSTP valid_refs_inv \<rbrace>"
proof(vcg_jackhammer (keep_locs) (no_thin_post_inv), vcg_name_cases)
next case (hs_get_roots_done s s') then show ?case by (clarsimp simp: valid_refs_inv_def grey_reachable_def)
next case (hs_get_work_done s s') then show ?case by (clarsimp simp: valid_refs_inv_def grey_reachable_def)
qed

end

lemma (in sys) valid_refs_inv[intro]:
  "\<lbrace> LSTP (valid_refs_inv \<^bold>\<and> tso_store_inv) \<rbrace> sys \<lbrace> LSTP valid_refs_inv \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws) then show ?case
    unfolding do_store_action_def
    apply (auto simp: p_not_sys valid_refs_inv_dequeue_Mutate valid_refs_inv_dequeue_Mutate_Payload fun_upd_apply split: mem_store_action.splits)
    done
qed

(*<*)

end
(*>*)
