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

theory Global_Noninterference
imports
  Global_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open> Global non-interference \<close>

text\<open> proofs that depend only on global invariants + lemmas \<close>

lemma (in sys) strong_tricolour_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP strong_tricolour_inv \<rbrace>"
unfolding strong_tricolour_inv_def
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws x xa) then show ?case
  proof(cases w)
       case (mw_Mark ref field) with tso_dequeue_store_buffer show ?thesis
        apply -
        apply clarsimp
        apply (frule (1) valid_W_invD)
        apply clarsimp
        apply (cases "x = ref"; clarsimp simp: grey_def white_def WL_def split: if_splits)
        apply (drule_tac x=x in spec; force split: obj_at_splits)
        done
  next case (mw_Mutate ref field opt_r') with tso_dequeue_store_buffer show ?thesis
        apply -
        apply (clarsimp simp: fM_rel_inv_def p_not_sys)
        apply (elim disjE; clarsimp simp: points_to_Mutate)
        apply (elim disjE; clarsimp)
        apply (case_tac "sys_ghost_hs_phase s\<down>"; clarsimp simp: hp_step_rel_def heap_colours_colours no_black_refsD)
        proof(goal_cases hp_InitMark hp_Mark hp_IdleMarkSweep)
             case (hp_InitMark m) then show ?case
              apply -
              apply (drule mut_m.handshake_phase_invD[where m=m])
              apply (drule_tac x=m in spec)
              apply (elim disjE; clarsimp simp: hp_step_rel_def)
              apply (elim disjE; clarsimp simp: mut_m.marked_insertions_def no_black_refsD marked_not_white)
              done
        next case (hp_Mark m) then show ?case
              apply -
              apply (drule mut_m.handshake_phase_invD[where m=m])
              apply (drule_tac x=m in spec)
              apply (elim disjE; clarsimp simp: hp_step_rel_def)
              apply (elim disjE; clarsimp simp: mut_m.marked_insertions_def no_black_refsD)
              apply blast+
              done
        next case (hp_IdleMarkSweep m) then show ?case
              apply -
              apply (drule mut_m.handshake_phase_invD[where m=m])
              apply (drule_tac x=m in spec)
              apply (elim disjE; clarsimp simp: hp_step_rel_def)
              apply (elim disjE; clarsimp simp: marked_not_white mut_m.marked_insertions_def)
              done
        qed
  next case (mw_fM fM) with tso_dequeue_store_buffer show ?thesis
        apply -
        apply (clarsimp simp: fM_rel_inv_def p_not_sys)
        apply (erule disjE)
         apply (clarsimp simp: fM_rel_def black_heap_def split: if_splits)
          apply (metis colours_distinct(2) white_valid_ref)
         apply (clarsimp simp: white_heap_def)
         apply ( (drule_tac x=xa in spec)+ )[1]
         apply (clarsimp simp: white_def split: obj_at_splits)
        apply (fastforce simp: white_def)
        done
  qed (clarsimp simp: fM_rel_inv_def p_not_sys)+
qed

lemma black_heap_reachable:
  assumes "mut_m.reachable m y s"
  assumes bh: "black_heap s"
  assumes vri: "valid_refs_inv s"
  shows "black y s"
using assms
apply (induct rule: reachable_induct)
apply (simp_all add: black_heap_def valid_refs_invD)
apply (metis (full_types) reachable_points_to valid_refs_inv_def)
done

lemma black_heap_valid_ref_marked_insertions:
  "\<lbrakk> black_heap s; valid_refs_inv s \<rbrakk> \<Longrightarrow> mut_m.marked_insertions m s"
by (auto simp: mut_m.marked_insertions_def black_heap_def black_def
        split: mem_store_action.splits option.splits
         dest: valid_refs_invD)

context sys
begin

lemma reachable_snapshot_inv_black_heap_no_grey_refs_dequeue_Mutate:
  assumes sb: "sys_mem_store_buffers (mutator m') s = mw_Mutate r f opt_r' # ws"
  assumes bh: "black_heap s"
  assumes ngr: "no_grey_refs s"
  assumes vri: "valid_refs_inv s"
  shows "mut_m.reachable_snapshot_inv m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                        mem_store_buffers := (mem_store_buffers (s sys))(mutator m' := ws)\<rparr>))" (is "mut_m.reachable_snapshot_inv m ?s'")
apply (rule mut_m.reachable_snapshot_invI)
apply (rule in_snapshotI)
apply (erule black_heap_reachable)
 using bh vri
 apply (simp add: black_heap_def fun_upd_apply; fail)
using bh ngr sb vri
apply (subst valid_refs_inv_def)
apply (clarsimp simp add: no_grey_refs_def grey_reachable_def fun_upd_apply)
apply (drule black_heap_reachable)
  apply (simp add: black_heap_def fun_upd_apply; fail)
 apply (clarsimp simp: valid_refs_inv_dequeue_Mutate; fail)
apply (clarsimp simp: in_snapshot_def in_snapshot_valid_ref fun_upd_apply)
done

lemma marked_deletions_dequeue_Mark:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mark r fl # ws; mut_m.marked_deletions m s; tso_store_inv s; valid_W_inv s \<rbrakk>
     \<Longrightarrow> mut_m.marked_deletions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
unfolding mut_m.marked_deletions_def
by (auto simp: fun_upd_apply obj_at_field_on_heap_def
        split: obj_at_splits option.splits mem_store_action.splits
         dest: valid_W_invD)

lemma marked_deletions_dequeue_Mutate:
  "\<lbrakk> sys_mem_store_buffers (mutator m') s = mw_Mutate r f opt_r' # ws; mut_m.marked_deletions m s; mut_m.marked_insertions m' s \<rbrakk>
     \<Longrightarrow> mut_m.marked_deletions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                 mem_store_buffers := (mem_store_buffers (s sys))((mutator m') := ws)\<rparr>))"
unfolding mut_m.marked_insertions_def mut_m.marked_deletions_def
apply (clarsimp simp: fun_upd_apply split: mem_store_action.splits option.splits)
apply (metis list.set_intros(2) obj_at_field_on_heap_imp_valid_ref(1))+
done

lemma grey_protects_white_dequeue_Mark:
  assumes fl: "fl = sys_fM s"
  assumes "r \<in> ghost_honorary_grey (s p)"
  shows "(\<exists>g. (g grey_protects_white w) (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>)))
      \<longleftrightarrow> (\<exists>g. (g grey_protects_white w) s)" (is "(\<exists>g. (g grey_protects_white w) ?s') \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume "\<exists>g. (g grey_protects_white w) ?s'"
  then obtain g where "(g grey_protects_white w) ?s'" by blast
  from this assms show ?rhs
  proof induct
    case (step x y z) then show ?case
      apply (cases "y = r"; clarsimp simp: fun_upd_apply)
       apply (metis black_dequeue_Mark colours_distinct(2) do_store_action_simps(1) greyI(1) grey_protects_whiteE(1) grey_protects_whiteI marked_imp_black_or_grey(2) valid_ref_valid_null_ref_simps(1) white_valid_ref)
      apply (metis black_dequeue_Mark colours_distinct(2) do_store_action_simps(1) grey_protects_whiteE(2) grey_protects_whiteI marked_imp_black_or_grey(2) valid_ref_valid_null_ref_simps(1) white_valid_ref)
      done
  qed (fastforce simp: fun_upd_apply)
next
  assume ?rhs
  then obtain g' where "(g' grey_protects_white w) s" ..
  then show "\<exists>g. (g grey_protects_white w) ?s'"
  proof induct
    case (refl g) with assms show ?case
apply -
apply (rule exI[where x=g])
apply (rule grey_protects_whiteI)
apply (subst grey_fun_upd; simp add: fun_upd_apply)
done (* FIXME something eta-ish going wrong here: fun_upd_apply triggers too early, why? Maybe the WL rules are borked too *)
  next
    case (step x y z) with assms show ?case
apply clarsimp
apply (rename_tac g)
apply (clarsimp simp add: grey_protects_white_def)
apply (case_tac "z = r")
 apply (rule exI[where x=r])
 apply (clarsimp simp add: grey_protects_white_def)
 apply (subst grey_fun_upd; force simp: fun_upd_apply)
apply (rule_tac x=g in exI)
apply (fastforce elim!: has_white_path_to_step)
done
  qed
qed

lemma reachable_snapshot_inv_dequeue_Mark:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mark r fl # ws; mut_m.reachable_snapshot_inv m s; valid_W_inv s \<rbrakk>
     \<Longrightarrow> mut_m.reachable_snapshot_inv m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
unfolding mut_m.reachable_snapshot_inv_def in_snapshot_def
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (subst (asm) arg_cong[where f=Not, OF grey_protects_white_dequeue_Mark, simplified]; simp add: colours_distinct(4) valid_W_invD(1) fun_upd_apply)
done

lemma marked_insertions_dequeue_Mark:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mark r fl # ws; mut_m.marked_insertions m s; tso_writes_inv s; valid_W_inv s \<rbrakk>
     \<Longrightarrow> mut_m.marked_insertions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
apply (clarsimp simp: mut_m.marked_insertions_def)
apply (cases "mutator m = p")
 apply clarsimp
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (auto simp: valid_W_invD split: mem_store_action.splits option.splits obj_at_splits; fail)
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (auto simp: valid_W_invD split: mem_store_action.splits option.splits obj_at_splits)
done

lemma marked_insertions_dequeue_Mutate:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mutate r f r' # ws; mut_m.marked_insertions m s \<rbrakk>
     \<Longrightarrow> mut_m.marked_insertions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := r')\<rparr>) (sys_heap s r)),
                                                    mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
unfolding mut_m.marked_insertions_def
apply (cases "mutator m = p")
 apply clarsimp
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (auto simp: fun_upd_apply split: mem_store_action.splits option.splits obj_at_splits; fail)[1]
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (auto simp: fun_upd_apply split: mem_store_action.splits option.splits obj_at_splits)[1]
done

(* shows the snapshot is preserved by the two marks. *)
lemma grey_protects_white_dequeue_Mutate:
  assumes sb: "sys_mem_store_buffers (mutator m) s = mw_Mutate r f opt_r' # ws"
  assumes mi: "mut_m.marked_insertions m s"
  assumes md: "mut_m.marked_deletions m s"
  shows "(\<exists>g. (g grey_protects_white w) (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                        mem_store_buffers := (mem_store_buffers (s sys))(mutator m := ws)\<rparr>)))
      \<longleftrightarrow> (\<exists>g. (g grey_protects_white w) s)" (is "(\<exists>g. (g grey_protects_white w) ?s') \<longleftrightarrow> ?rhs")
proof
  assume "(\<exists>g. (g grey_protects_white w) ?s')"
  then obtain g where "(g grey_protects_white w) ?s'" by blast
  from this mi sb show ?rhs
  proof(induct rule: grey_protects_white_induct)
       case (refl x) then show ?case by (fastforce simp: fun_upd_apply)
  next case (step x y z) then show ?case
        unfolding white_def
        apply (clarsimp simp: points_to_Mutate grey_protects_white_def)
        apply (auto dest: marked_insertionD simp: marked_not_white whiteI fun_upd_apply)
        done
  qed
next
  assume ?rhs then show "(\<exists>g. (g grey_protects_white w) ?s')"
  proof(clarsimp)
    fix g assume "(g grey_protects_white w) s"
    from this show ?thesis
    proof(induct rule: grey_protects_white_induct)
         case (refl x) then show ?case
          apply -
          apply (rule exI[where x=x])
          apply (clarsimp simp: grey_protects_white_def)
          apply (subst grey_fun_upd; simp add: fun_upd_apply) (* FIXME *)
          done
    next case (step x y z) with md sb show ?case
      apply clarsimp
      apply (clarsimp simp: grey_protects_white_def)
      apply (rename_tac g)

      apply (case_tac "y = r")
       defer
       apply (auto simp: points_to_Mutate fun_upd_apply elim!: has_white_path_to_step; fail)[1]
      apply (clarsimp simp: ran_def fun_upd_apply split: obj_at_split_asm) (* FIXME rule: witness field for r points_to c *)
      apply (rename_tac g obj aa)
      apply (case_tac "aa = f")
       defer
       apply (rule_tac x=g in exI)
       apply clarsimp
       apply (clarsimp simp: has_white_path_to_def fun_upd_apply)
       apply (erule rtranclp.intros)
       apply (auto simp: fun_upd_apply ran_def split: obj_at_splits; fail)[1]

      apply (clarsimp simp: has_white_path_to_def)
      apply (clarsimp simp: mut_m.marked_deletions_def) (* FIXME rule *)
      apply (drule spec[where x="mw_Mutate r f opt_r'"])
      apply (clarsimp simp: obj_at_field_on_heap_def)
      apply (simp add: white_def split: obj_at_splits)
      done
    qed
  qed
qed

(* write barrier installed but not all mutators are necessarily past get_roots *)
lemma reachable_snapshot_inv_dequeue_Mutate:
  notes grey_protects_white_dequeue_Mutate[simp]
  fixes s :: "('field, 'mut, 'payload, 'ref) lsts"
  assumes sb: "sys_mem_store_buffers (mutator m') s = mw_Mutate r f opt_r' # ws"
  assumes mi: "mut_m.marked_insertions m' s"
  assumes md: "mut_m.marked_deletions m' s"
  assumes rsi: "mut_m.reachable_snapshot_inv m s"
  assumes sti: "strong_tricolour_inv s"
  assumes vri: "valid_refs_inv s"
  shows "mut_m.reachable_snapshot_inv m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                        mem_store_buffers := (mem_store_buffers (s sys))(mutator m' := ws)\<rparr>))" (is "mut_m.reachable_snapshot_inv m ?s'")
proof(rule mut_m.reachable_snapshot_invI)
  fix y assume y: "mut_m.reachable m y ?s'"
  then have "(mut_m.reachable m y s \<or> mut_m.reachable m' y s) \<and> in_snapshot y ?s'"
  proof(induct rule: reachable_induct)
    case (root x) with mi md rsi sb show ?case
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def)
      apply (auto simp: fun_upd_apply)
      done
  next
    case (ghost_honorary_root x) with mi md rsi sb show ?case
      unfolding mut_m.reachable_snapshot_inv_def in_snapshot_def by (auto simp: fun_upd_apply)
  next
    case (tso_root x) with mi md rsi sb show ?case
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def)
       apply (rename_tac w)
       apply (case_tac w; simp) (* FIXME cut and paste here *)
        apply (rename_tac ref field option)
        apply (clarsimp simp: mut_m.marked_deletions_def mut_m.marked_insertions_def fun_upd_apply)
        apply (drule_tac x="mw_Mutate ref field option" in spec)
        apply (drule_tac x="mw_Mutate ref field option" in spec)
        apply (clarsimp simp: fun_upd_apply)
        apply (frule spec[where x=x])
        apply (subgoal_tac "mut_m.reachable m x s")
         apply (force simp: fun_upd_apply)
        apply (rule reachableI(2))
       apply (force simp: mut_m.tso_store_refs_def)
       apply (rename_tac ref field pl)
       apply (clarsimp simp: mut_m.marked_deletions_def mut_m.marked_insertions_def fun_upd_apply)
        apply (drule_tac x="mw_Mutate_Payload x field pl" in spec)
        apply (drule_tac x="mw_Mutate_Payload x field pl" in spec)
        apply (clarsimp simp: fun_upd_apply)
        apply (frule spec[where x=x])
        apply (subgoal_tac "mut_m.reachable m x s")
         apply (force simp: fun_upd_apply)
        apply (rule reachableI(2))
       apply (force simp: mut_m.tso_store_refs_def)
      apply (auto simp: fun_upd_apply)
      done
  next
    case (reaches x y)
    from reaches sb have y: "mut_m.reachable m y s \<or> mut_m.reachable m' y s"
      apply (clarsimp simp: points_to_Mutate mut_m.reachable_snapshot_inv_def in_snapshot_def)
      apply (elim disjE, (force dest!: reachable_points_to mutator_reachable_tso)+)[1]
      done
    moreover
    from y vri have "valid_ref y s" by auto
    with reaches mi md rsi sb sti y have "(black y s \<or> (\<exists>x. (x grey_protects_white y) s))"
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def)
      apply (clarsimp simp: fun_upd_apply)
      apply (drule spec[where x=y])
      apply (clarsimp simp: points_to_Mutate mut_m.marked_insertions_def mut_m.marked_deletions_def) (* FIXME lemmas *)
      apply (drule spec[where x="mw_Mutate r f opt_r'"])+
      apply clarsimp
      apply (elim disjE; clarsimp simp: reachable_points_to) (* FIXME probably want points_to_Mutate as an elim rule to make this robust, reduce duplication *)
       apply (drule (3) strong_tricolour_invD)
       apply (metis (no_types) grey_protects_whiteI marked_imp_black_or_grey(1))

       apply (metis (no_types) grey_protects_whiteE(2) grey_protects_whiteI marked_imp_black_or_grey(2))

       apply (elim disjE; clarsimp simp: reachable_points_to)
       apply (force simp: black_def)

       apply (elim disjE; clarsimp simp: reachable_points_to)
       apply (force simp: black_def)

       apply (elim disjE; clarsimp simp: reachable_points_to)
       apply (force simp: black_def)

       apply (drule (3) strong_tricolour_invD)
       apply (force simp: black_def)

       apply (elim disjE; clarsimp)
        apply (force simp: black_def fun_upd_apply)
       apply (metis (no_types) grey_protects_whiteE(2) grey_protects_whiteI marked_imp_black_or_grey(2))
       done
    moreover note mi md rsi sb
    ultimately show ?case
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def)
      apply (clarsimp simp: fun_upd_apply)
      done
  qed
  then show "in_snapshot y ?s'" by blast
qed

lemma mutator_phase_inv[intro]:
  "\<lbrace> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_store_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP (mut_m.mutator_phase_inv m) \<rbrace>"
proof(vcg_jackhammer (no_thin_post_inv), vcg_name_cases)
  case (tso_dequeue_store_buffer s s' p w ws) show ?case
  proof(cases w)
       case (mw_Mark ref field) with tso_dequeue_store_buffer show ?thesis
        by (clarsimp simp: mutator_phase_inv_aux_case
                           marked_deletions_dequeue_Mark marked_insertions_dequeue_Mark reachable_snapshot_inv_dequeue_Mark
                    split: hs_phase.splits)
  next case (mw_Mutate ref field opt_r') show ?thesis
       proof(cases "ghost_hs_phase (s\<down> (mutator m))")
            case hp_IdleInit
            with \<open>sys_mem_store_buffers p s\<down> = w # ws\<close> spec[OF \<open>mutators_phase_inv s\<down>\<close>, where x=m] mw_Mutate
            show ?thesis by simp
       next case hp_InitMark
            with \<open>sys_mem_store_buffers p s\<down> = w # ws\<close> spec[OF \<open>mutators_phase_inv s\<down>\<close>, where x=m] mw_Mutate
            show ?thesis by (simp add: marked_insertions_dequeue_Mutate)
       next case hp_Mark with tso_dequeue_store_buffer mw_Mutate show ?thesis
              apply -
              apply (clarsimp simp: mutator_phase_inv_aux_case p_not_sys split: hs_phase.splits)
              apply (erule disjE; clarsimp simp: marked_insertions_dequeue_Mutate)
              apply (rename_tac m')
              apply (frule mut_m.handshake_phase_invD[where m=m])
              apply (rule marked_deletions_dequeue_Mutate, simp_all)
              apply (drule_tac m=m' in mut_m.handshake_phase_invD, clarsimp simp: hp_step_rel_def)
              using hs_phase.distinct(11) hs_phase.distinct(15) hs_type.distinct(1) apply presburger
              done
       next case hp_IdleMarkSweep with tso_dequeue_store_buffer mw_Mutate show ?thesis
              apply -
              apply (clarsimp simp: mutator_phase_inv_aux_case p_not_sys
                             split: hs_phase.splits)
              apply (intro allI conjI impI; erule disjE; clarsimp simp: sys.marked_insertions_dequeue_Mutate)
               apply (rename_tac m')
               apply (rule marked_deletions_dequeue_Mutate, simp_all)[1]
               apply (drule_tac x=m' in spec)
               apply (frule mut_m.handshake_phase_invD[where m=m])
               apply (drule_tac m=m' in mut_m.handshake_phase_invD, clarsimp simp: hp_step_rel_def)
               apply (elim disjE; clarsimp split del: if_split_asm)
               apply (clarsimp simp: fA_rel_inv_def fM_rel_inv_def fA_rel_def fM_rel_def split del: if_split_asm)
               apply (meson black_heap_valid_ref_marked_insertions; fail)
              apply (rename_tac m')
              apply (frule_tac m=m  in mut_m.handshake_phase_invD)
              apply (drule_tac m=m' in mut_m.handshake_phase_invD, clarsimp simp: hp_step_rel_def)
              apply (elim disjE; clarsimp simp: reachable_snapshot_inv_black_heap_no_grey_refs_dequeue_Mutate reachable_snapshot_inv_dequeue_Mutate)
              apply (clarsimp simp: fA_rel_inv_def fM_rel_inv_def fA_rel_def fM_rel_def)
              apply blast
              done
      qed simp
  next case (mw_Mutate_Payload r f pl) with tso_dequeue_store_buffer show ?thesis
apply (clarsimp simp: mutator_phase_inv_aux_case fun_upd_apply split: hs_phase.splits)
apply (subst reachable_snapshot_fun_upd)
apply (simp_all add: fun_upd_apply)
apply (metis (no_types, lifting) list.set_intros(1) mem_store_action.simps(39) tso_store_inv_def)
done
  next case (mw_fA mark)     with tso_dequeue_store_buffer show ?thesis
        by (clarsimp simp: mutator_phase_inv_aux_case fun_upd_apply split: hs_phase.splits)
  next case (mw_fM mark)     with tso_dequeue_store_buffer show ?thesis
        using mut_m_not_idle_no_fM_writeD by fastforce
  next case (mw_Phase phase) with tso_dequeue_store_buffer show ?thesis
        by (clarsimp simp: mutator_phase_inv_aux_case fun_upd_apply split: hs_phase.splits)
  qed
qed

end

(*<*)

end
(*>*)
