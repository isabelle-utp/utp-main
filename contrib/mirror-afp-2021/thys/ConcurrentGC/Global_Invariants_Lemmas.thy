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

theory Global_Invariants_Lemmas
imports
  Global_Invariants
begin

declare subst_all [simp del] [[simproc del: defined_all]]

(*>*)
section\<open>Global invariants lemma bucket\<close>

(* FIXME this file should be about the invs. This split makes it easier to move things around, maybe. *)

declare mut_m.mutator_phase_inv_aux.simps[simp]
case_of_simps mutator_phase_inv_aux_case: mut_m.mutator_phase_inv_aux.simps
case_of_simps sys_phase_inv_aux_case: sys_phase_inv_aux.simps


subsection\<open>TSO invariants\<close>

lemma tso_store_inv_eq_imp:
  "eq_imp (\<lambda>p s. mem_store_buffers (s sys) p)
          tso_store_inv"
by (simp add: eq_imp_def tso_store_inv_def)

lemmas tso_store_inv_fun_upd[simp] = eq_imp_fun_upd[OF tso_store_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma tso_store_invD[simp]:
  "tso_store_inv s \<Longrightarrow> \<not>sys_mem_store_buffers gc s = mw_Mutate r f r' # ws"
  "tso_store_inv s \<Longrightarrow> \<not>sys_mem_store_buffers gc s = mw_Mutate_Payload r f pl # ws"
  "tso_store_inv s \<Longrightarrow> \<not>sys_mem_store_buffers (mutator m) s = mw_fA fl # ws"
  "tso_store_inv s \<Longrightarrow> \<not>sys_mem_store_buffers (mutator m) s = mw_fM fl # ws"
  "tso_store_inv s \<Longrightarrow> \<not>sys_mem_store_buffers (mutator m) s = mw_Phase ph # ws"
by (auto simp: tso_store_inv_def dest!: spec[where x=m])

lemma mut_do_store_action[simp]:
  "\<lbrakk> sys_mem_store_buffers (mutator m) s = w # ws; tso_store_inv s \<rbrakk> \<Longrightarrow> fA (do_store_action w (s sys)) = sys_fA s"
  "\<lbrakk> sys_mem_store_buffers (mutator m) s = w # ws; tso_store_inv s \<rbrakk> \<Longrightarrow> fM (do_store_action w (s sys)) = sys_fM s"
  "\<lbrakk> sys_mem_store_buffers (mutator m) s = w # ws; tso_store_inv s \<rbrakk> \<Longrightarrow> phase (do_store_action w (s sys)) = sys_phase s"
by (auto simp: do_store_action_def split: mem_store_action.splits)

lemma tso_store_inv_sys_load_Mut[simp]:
  assumes "tso_store_inv s"
  assumes "(ract, v) \<in> { (mr_fM, mv_Mark (Some (sys_fM s))), (mr_fA, mv_Mark (Some (sys_fA s))), (mr_Phase, mv_Phase (sys_phase s)) }"
  shows "sys_load (mutator m) ract (s sys) = v"
using assms
apply (clarsimp simp: sys_load_def fold_stores_def)
apply (rule fold_invariant[where P="\<lambda>fr. do_load_action ract (fr (s sys)) = v" and Q="mut_writes"])
  apply (fastforce simp: tso_store_inv_def)
 apply (auto simp: do_load_action_def split: mem_store_action.splits)
done

lemma tso_store_inv_sys_load_GC[simp]:
  assumes "tso_store_inv s"
  shows "sys_load gc (mr_Ref r f) (s sys) = mv_Ref (Option.bind (sys_heap s r) (\<lambda>obj. obj_fields obj f))" (is "?lhs = mv_Ref ?rhs")
using assms unfolding sys_load_def fold_stores_def
apply clarsimp
apply (rule fold_invariant[where P="\<lambda>fr. Option.bind (heap (fr (s sys)) r) (\<lambda>obj. obj_fields obj f) = ?rhs"
                             and Q="\<lambda>w. \<forall>r f r'. w \<noteq> mw_Mutate r f r'"])
  apply (fastforce simp: tso_store_inv_def)
 apply (auto simp: do_store_action_def map_option_case fun_upd_apply
            split: mem_store_action.splits option.splits)
done

lemma tso_no_pending_marksD[simp]:
  assumes "tso_pending_mark p s = []"
  shows "sys_load p (mr_Mark r) (s sys) = mv_Mark (map_option obj_mark (sys_heap s r))"
using assms unfolding sys_load_def fold_stores_def
apply clarsimp
apply (rule fold_invariant[where P="\<lambda>fr. map_option obj_mark (heap (fr (s sys)) r) = map_option obj_mark (sys_heap s r)"
                             and Q="\<lambda>w. \<forall>fl. w \<noteq> mw_Mark r fl"])
  apply (auto simp: map_option_case do_store_action_def filter_empty_conv fun_upd_apply
             split: mem_store_action.splits option.splits)
done

lemma no_pending_phase_sys_load[simp]:
  assumes "tso_pending_phase p s = []"
  shows "sys_load p mr_Phase (s sys) = mv_Phase (sys_phase s)"
using assms
apply (clarsimp simp: sys_load_def fold_stores_def)
apply (rule fold_invariant[where P="\<lambda>fr. phase (fr (s sys)) = sys_phase s" and Q="\<lambda>w. \<forall>ph. w \<noteq> mw_Phase ph"])
  apply (auto simp: do_store_action_def filter_empty_conv
             split: mem_store_action.splits)
done

lemma gc_no_pending_fM_write[simp]:
  assumes "tso_pending_fM gc s = []"
  shows "sys_load gc mr_fM (s sys) = mv_Mark (Some (sys_fM s))"
using assms
apply (clarsimp simp: sys_load_def fold_stores_def)
apply (rule fold_invariant[where P="\<lambda>fr. fM (fr (s sys)) = sys_fM s" and Q="\<lambda>w. \<forall>fl. w \<noteq> mw_fM fl"])
  apply (auto simp: do_store_action_def filter_empty_conv
             split: mem_store_action.splits)
done

lemma tso_store_refs_simps[simp]:
  "mut_m.tso_store_refs m (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>))
 = mut_m.tso_store_refs m s"
  "mut_m.tso_store_refs m (s(mutator m' := s (mutator m')\<lparr>ghost_honorary_root := {}\<rparr>,
                             sys := s sys\<lparr>mem_store_buffers := (mem_store_buffers (s sys))(mutator m' := sys_mem_store_buffers (mutator m') s @ [mw_Mutate r f opt_r'])\<rparr>))
 = mut_m.tso_store_refs m s \<union> (if m' = m then store_refs (mw_Mutate r f opt_r') else {})"
  "mut_m.tso_store_refs m (s(sys := s sys\<lparr>mem_store_buffers := (mem_store_buffers (s sys))(mutator m' := sys_mem_store_buffers (mutator m') s @ [mw_Mutate_Payload r f pl])\<rparr>))
 = mut_m.tso_store_refs m s \<union> (if m' = m then store_refs (mw_Mutate_Payload r f pl) else {})"
  "mut_m.tso_store_refs m (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := None)\<rparr>))
 = mut_m.tso_store_refs m s"
  "mut_m.tso_store_refs m (s(mutator m' := s (mutator m')\<lparr>roots := insert r (roots (s (mutator m')))\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r \<mapsto> obj)\<rparr>))
 = mut_m.tso_store_refs m s"
  "mut_m.tso_store_refs m (s(mutator m' := s (mutator m')\<lparr>ghost_honorary_root := Option.set_option opt_r', ref := opt_r'\<rparr>))
 = mut_m.tso_store_refs m s"
  "mut_m.tso_store_refs m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                          mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))
 = (if p = mutator m then \<Union>w \<in> set ws. store_refs w else mut_m.tso_store_refs m s)"
  "mut_m.tso_store_refs m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_payload := (obj_payload obj)(f := pl)\<rparr>) (sys_heap s r)),
                                          mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))
 = (if p = mutator m then \<Union>w \<in> set ws. store_refs w else mut_m.tso_store_refs m s)"
  "sys_mem_store_buffers p s = mw_Mark r fl # ws
\<Longrightarrow> mut_m.tso_store_refs m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))
 = mut_m.tso_store_refs m s"
unfolding mut_m.tso_store_refs_def by (auto simp: fun_upd_apply)

lemma fold_stores_points_to[rule_format, simplified conj_explode]:
  "heap (fold_stores ws (s sys)) r = Some obj \<and> obj_fields obj f = Some r'
     \<longrightarrow> (r points_to r') s \<or> (\<exists>w \<in> set ws. r' \<in> store_refs w)" (is "?P (fold_stores ws) obj")
unfolding fold_stores_def
apply (rule spec[OF fold_invariant[where P="\<lambda>fr. \<forall>obj. ?P fr obj" and Q="\<lambda>w. w \<in> set ws"]])
  apply fastforce
 apply (fastforce simp: ran_def split: obj_at_splits)
apply clarsimp
apply (drule (1) bspec)
apply (clarsimp simp: fun_upd_apply split: mem_store_action.split_asm if_splits)
done

lemma points_to_Mutate:
  "(x points_to y)
         (s(sys := (s sys)\<lparr> heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                            mem_store_buffers := (mem_store_buffers (s sys))(p := ws) \<rparr>))
  \<longleftrightarrow> (r \<noteq> x \<and> (x points_to y) s) \<or> (r = x \<and> valid_ref r s \<and> (opt_r' = Some y \<or> ( (x points_to y) s \<and> obj_at (\<lambda>obj. \<exists>f'. obj_fields obj f' = Some y \<and> f \<noteq> f') r s)))"
unfolding ran_def by (auto simp: fun_upd_apply split: obj_at_splits)


subsection\<open> FIXME mutator handshake facts \<close>

lemma \<comment> \<open>Sanity\<close>
  "hp' = hs_step hp \<Longrightarrow> \<exists>in' ht. (in', ht, hp', hp) \<in> hp_step_rel"
by (cases hp) (auto simp: hp_step_rel_def)

lemma \<comment> \<open>Sanity\<close>
  "(False, ht, hp', hp) \<in> hp_step_rel \<Longrightarrow> hp' = hp_step ht hp"
by (cases ht) (auto simp: hp_step_rel_def)

lemma (in mut_m) handshake_phase_invD:
  assumes "handshake_phase_inv s"
  shows "(sys_ghost_hs_in_sync m s, sys_hs_type s, sys_ghost_hs_phase s, mut_ghost_hs_phase s) \<in> hp_step_rel
       \<and> (sys_hs_pending m s \<longrightarrow> \<not>sys_ghost_hs_in_sync m s)"
using assms unfolding handshake_phase_inv_def by simp

lemma handshake_in_syncD:
  "\<lbrakk> All (ghost_hs_in_sync (s sys)); handshake_phase_inv s \<rbrakk>
     \<Longrightarrow> \<forall>m'. mut_m.mut_ghost_hs_phase m' s = sys_ghost_hs_phase s"
by clarsimp (auto simp: hp_step_rel_def dest!: mut_m.handshake_phase_invD)

lemmas fM_rel_invD = iffD1[OF fun_cong[OF fM_rel_inv_def[simplified atomize_eq]]]

text\<open>

Relate @{const "sys_ghost_hs_phase"}, @{const "gc_phase"},
@{const "sys_phase"} and writes to the phase in the GC's TSO buffer.

\<close>

simps_of_case handshake_phase_rel_simps[simp]: handshake_phase_rel_def (splits: hs_phase.split)

lemma phase_rel_invD:
  assumes "phase_rel_inv s"
  shows "(\<forall>m. sys_ghost_hs_in_sync m s, sys_ghost_hs_phase s, gc_phase s, sys_phase s, tso_pending_phase gc s) \<in> phase_rel"
using assms unfolding phase_rel_inv_def by simp

lemma mut_m_not_idle_no_fM_write:
  "\<lbrakk> ghost_hs_phase (s (mutator m)) \<noteq> hp_Idle; fM_rel_inv s; handshake_phase_inv s; tso_store_inv s; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> \<not>sys_mem_store_buffers p s = mw_fM fl # ws"
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (clarsimp simp: hp_step_rel_def fM_rel_def filter_empty_conv p_not_sys)
apply (metis list.set_intros(1) tso_store_invD(4))
done

lemma (in mut_m) mut_ghost_handshake_phase_idle:
  "\<lbrakk> mut_ghost_hs_phase s = hp_Idle; handshake_phase_inv s; phase_rel_inv s \<rbrakk>
     \<Longrightarrow> sys_phase s = ph_Idle"
apply (drule phase_rel_invD)
apply (drule handshake_phase_invD)
apply (auto simp: phase_rel_def hp_step_rel_def)
done

lemma mut_m_not_idle_no_fM_writeD:
  "\<lbrakk> sys_mem_store_buffers p s = mw_fM fl # ws; ghost_hs_phase (s (mutator m)) \<noteq> hp_Idle; fM_rel_inv s; handshake_phase_inv s; tso_store_inv s; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> False"
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (clarsimp simp: hp_step_rel_def fM_rel_def filter_empty_conv p_not_sys)
apply (metis list.set_intros(1) tso_store_invD(4))
done


subsection\<open>points to, reaches, reachable mut\<close>

lemma (in mut_m) reachable_eq_imp:
  "eq_imp (\<lambda>r'. mut_roots \<^bold>\<otimes> mut_ghost_honorary_root \<^bold>\<otimes> (\<lambda>s. \<Union>(ran ` obj_fields ` set_option (sys_heap s r')))
              \<^bold>\<otimes> tso_pending_mutate (mutator m))
          (reachable r)"
unfolding eq_imp_def reachable_def tso_store_refs_def
apply clarsimp
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r'. (\<exists>w\<in>set (sys_mem_store_buffers (mutator m) s). r' \<in> store_refs w) \<longleftrightarrow> (\<exists>w\<in>set (sys_mem_store_buffers (mutator m) s'). r' \<in> store_refs w)")
 apply (subgoal_tac "\<forall>x. (x reaches r) s \<longleftrightarrow> (x reaches r) s'")
  apply (clarsimp; fail)
 apply (auto simp: reaches_fields; fail)[1]
apply (drule arg_cong[where f=set])
apply (clarsimp simp: set_eq_iff)
apply (rule iffI)
 apply clarsimp
 apply (rename_tac s s' r' w)
 apply (drule_tac x=w in spec)
 apply (rule_tac x=w in bexI)
  apply (clarsimp; fail)
 apply (clarsimp split: mem_store_action.splits; fail)
apply clarsimp
apply (rename_tac s s' r' w)
apply (drule_tac x=w in spec)
apply (rule_tac x=w in bexI)
 apply (clarsimp; fail)
apply (clarsimp split: mem_store_action.splits; fail)
done

lemmas reachable_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.reachable_eq_imp, simplified eq_imp_simps, rule_format]

lemma reachableI[intro]:
  "x \<in> mut_m.mut_roots m s \<Longrightarrow> mut_m.reachable m x s"
  "x \<in> mut_m.tso_store_refs m s \<Longrightarrow> mut_m.reachable m x s"
by (auto simp: mut_m.reachable_def reaches_def)

lemma reachable_points_to[elim]:
  "\<lbrakk> (x points_to y) s; mut_m.reachable m x s \<rbrakk> \<Longrightarrow> mut_m.reachable m y s"
by (auto simp: mut_m.reachable_def reaches_def elim: rtranclp.intros(2))

lemma (in mut_m) mut_reachableE[consumes 1, case_names mut_root tso_store_refs]:
  "\<lbrakk> reachable y s;
     \<And>x. \<lbrakk> (x reaches y) s; x \<in> mut_roots s \<rbrakk> \<Longrightarrow> Q;
     \<And>x. \<lbrakk> (x reaches y) s; x \<in> mut_ghost_honorary_root s \<rbrakk> \<Longrightarrow> Q;
     \<And>x. \<lbrakk> (x reaches y) s; x \<in> tso_store_refs s \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (auto simp: reachable_def)

lemma reachable_induct[consumes 1, case_names root ghost_honorary_root tso_root reaches]:
  assumes r: "mut_m.reachable m y s"
  assumes root: "\<And>x. \<lbrakk> x \<in> mut_m.mut_roots m s \<rbrakk> \<Longrightarrow> P x"
  assumes ghost_honorary_root: "\<And>x. \<lbrakk> x \<in> mut_m.mut_ghost_honorary_root m s \<rbrakk> \<Longrightarrow> P x"
  assumes tso_root: "\<And>x. x \<in> mut_m.tso_store_refs m s \<Longrightarrow> P x"
  assumes reaches: "\<And>x y. \<lbrakk> mut_m.reachable m x s; (x points_to y) s; P x \<rbrakk> \<Longrightarrow> P y"
  shows "P y"
using r unfolding mut_m.reachable_def
proof(clarify)
  fix x
  assume "(x reaches y) s" and "x \<in> mut_m.mut_roots m s \<union> mut_m.mut_ghost_honorary_root m s \<union> mut_m.tso_store_refs m s"
  then show "P y"
  unfolding reaches_def proof induct
    case base with root ghost_honorary_root tso_root show ?case by blast
  next
    case (step y z) with reaches show ?case
      unfolding mut_m.reachable_def reaches_def by meson
  qed
qed

lemma mutator_reachable_tso:
  "sys_mem_store_buffers (mutator m) s = mw_Mutate r f opt_r' # ws
    \<Longrightarrow> mut_m.reachable m r s \<and> (\<forall>r'. opt_r' = Some r' \<longrightarrow> mut_m.reachable m r' s)"
  "sys_mem_store_buffers (mutator m) s = mw_Mutate_Payload r f pl # ws
    \<Longrightarrow> mut_m.reachable m r s"
by (auto simp: mut_m.tso_store_refs_def)


subsection\<open> Colours \<close>

lemma greyI[intro]:
  "r \<in> ghost_honorary_grey (s p) \<Longrightarrow> grey r s"
  "r \<in> W (s p) \<Longrightarrow> grey r s"
  "r \<in> WL p s \<Longrightarrow> grey r s"
unfolding grey_def WL_def by (case_tac [!] p) auto

lemma blackD[dest]:
  "black r s \<Longrightarrow> marked r s"
  "black r s \<Longrightarrow> r \<notin> WL p s"
unfolding black_def grey_def by simp_all

lemma whiteI[intro]: (* FIXME simp normal form of def *)
  "obj_at (\<lambda>obj. obj_mark obj = (\<not> sys_fM s)) r s \<Longrightarrow> white r s"
unfolding white_def by simp

lemma marked_not_white[dest]:
  "white r s \<Longrightarrow> \<not>marked r s"
unfolding white_def by (simp_all split: obj_at_splits)

lemma white_valid_ref[elim!]:
  "white r s \<Longrightarrow> valid_ref r s"
unfolding white_def by (simp_all split: obj_at_splits)

lemma not_white_marked[elim!]:
  "\<lbrakk>\<not> white r s; valid_ref r s\<rbrakk> \<Longrightarrow> marked r s"
unfolding white_def by (simp split: obj_at_splits)

lemma black_eq_imp:
  "eq_imp (\<lambda>_::unit. (\<lambda>s. r \<in> (\<Union>p. WL p s)) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r)))
          (black r)"
unfolding eq_imp_def black_def grey_def by (auto split: obj_at_splits)

lemma grey_eq_imp:
  "eq_imp (\<lambda>_::unit. (\<lambda>s. r \<in> (\<Union>p. WL p s)))
          (grey r)"
unfolding eq_imp_def grey_def by auto

lemma white_eq_imp:
  "eq_imp (\<lambda>_::unit. sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r)))
          (white r)"
unfolding eq_imp_def white_def by (auto split: obj_at_splits)

lemmas black_fun_upd[simp] = eq_imp_fun_upd[OF black_eq_imp, simplified eq_imp_simps, rule_format]
lemmas grey_fun_upd[simp] = eq_imp_fun_upd[OF grey_eq_imp, simplified eq_imp_simps, rule_format]
lemmas white_fun_upd[simp] = eq_imp_fun_upd[OF white_eq_imp, simplified eq_imp_simps, rule_format]


text\<open>coloured heaps\<close>

lemma black_heap_eq_imp:
  "eq_imp (\<lambda>r'. (\<lambda>s. \<Union>p. WL p s) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r')))
          black_heap"
apply (clarsimp simp: eq_imp_def black_heap_def black_def grey_def all_conj_distrib fun_eq_iff split: option.splits)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>x. marked x s \<longleftrightarrow> marked x s'")
 apply (subgoal_tac "\<forall>x. valid_ref x s \<longleftrightarrow> valid_ref x s'")
  apply (subgoal_tac "\<forall>x. (\<forall>p. x \<notin> WL p s) \<longleftrightarrow> (\<forall>p. x \<notin> WL p s')")
   apply clarsimp
  apply (auto simp: set_eq_iff)[1]
 apply clarsimp
 apply (rename_tac x)
 apply (rule eq_impD[OF obj_at_eq_imp])
 apply (drule_tac x=x in spec)
 apply (drule_tac f="map_option \<langle>True\<rangle>" in arg_cong)
 apply fastforce
apply clarsimp
apply (rule eq_impD[OF obj_at_eq_imp])
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (drule_tac f="map_option (\<lambda>fl. fl = sys_fM s)" in arg_cong)
apply simp
done

lemma white_heap_eq_imp:
  "eq_imp (\<lambda>r'. sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r')))
          white_heap"
apply (clarsimp simp: all_conj_distrib eq_imp_def white_def white_heap_def obj_at_def fun_eq_iff
               split: option.splits)
apply (rule iffI)
apply (metis (hide_lams, no_types) map_option_eq_Some)+
done

lemma no_black_refs_eq_imp:
  "eq_imp (\<lambda>r'. (\<lambda>s. (\<Union>p. WL p s)) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r')))
          no_black_refs"
apply (clarsimp simp add: eq_imp_def no_black_refs_def black_def grey_def all_conj_distrib fun_eq_iff set_eq_iff split: option.splits)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>x. marked x s \<longleftrightarrow> marked x s'")
 apply clarsimp
apply (clarsimp split: obj_at_splits)
apply (rename_tac x)
apply (drule_tac x=x in spec)+
apply (auto split: obj_at_splits)
done

lemmas black_heap_fun_upd[simp] = eq_imp_fun_upd[OF black_heap_eq_imp, simplified eq_imp_simps, rule_format]
lemmas white_heap_fun_upd[simp] = eq_imp_fun_upd[OF white_heap_eq_imp, simplified eq_imp_simps, rule_format]
lemmas no_black_refs_fun_upd[simp] = eq_imp_fun_upd[OF no_black_refs_eq_imp, simplified eq_imp_simps, rule_format]

lemma white_heap_imp_no_black_refs[elim!]:
  "white_heap s \<Longrightarrow> no_black_refs s"
apply (clarsimp simp: white_def white_heap_def no_black_refs_def black_def)
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (clarsimp split: obj_at_splits)
done

lemma black_heap_no_greys[elim]:
  "\<lbrakk> no_grey_refs s; \<forall>r. marked r s \<or> \<not>valid_ref r s \<rbrakk> \<Longrightarrow> black_heap s"
unfolding black_def black_heap_def no_grey_refs_def by fastforce

lemma heap_colours_colours:
  "black_heap s \<Longrightarrow> \<not>white r s"
  "white_heap s \<Longrightarrow> \<not>black r s"
by (auto simp: black_heap_def white_def white_heap_def
        dest!: spec[where x=r]
        split: obj_at_splits)


text\<open>The strong-tricolour invariant \<close>

lemma strong_tricolour_invD:
  "\<lbrakk> black x s; (x points_to y) s; valid_ref y s; strong_tricolour_inv s \<rbrakk>
     \<Longrightarrow> marked y s"
unfolding strong_tricolour_inv_def by fastforce

lemma no_black_refsD:
  "no_black_refs s \<Longrightarrow> \<not>black r s"
unfolding no_black_refs_def by simp

lemma has_white_path_to_induct[consumes 1, case_names refl step, induct set: has_white_path_to]:
  assumes "(x has_white_path_to y) s"
  assumes "\<And>x. P x x"
  assumes "\<And>x y z. \<lbrakk>(x has_white_path_to y) s; P x y; (y points_to z) s; white z s\<rbrakk> \<Longrightarrow> P x z"
  shows "P x y"
using assms unfolding has_white_path_to_def by (rule rtranclp.induct; blast)

lemma has_white_path_toD[dest]:
  "(x has_white_path_to y) s \<Longrightarrow> white y s \<or> x = y"
unfolding has_white_path_to_def by (fastforce elim: rtranclp.cases)

lemma has_white_path_to_refl[iff]:
  "(x has_white_path_to x) s"
unfolding has_white_path_to_def by simp

lemma has_white_path_to_step[intro]:
  "\<lbrakk>(x has_white_path_to y) s; (y points_to z) s; white z s\<rbrakk> \<Longrightarrow> (x has_white_path_to z) s"
  "\<lbrakk>(y has_white_path_to z) s; (x points_to y) s; white y s\<rbrakk> \<Longrightarrow> (x has_white_path_to z) s"
unfolding has_white_path_to_def
 apply (simp add: rtranclp.rtrancl_into_rtrancl)
apply (simp add: converse_rtranclp_into_rtranclp)
done

lemma has_white_path_toE[elim!]:
  "\<lbrakk> (x points_to y) s; white y s \<rbrakk> \<Longrightarrow> (x has_white_path_to y) s"
unfolding has_white_path_to_def by (auto elim: rtranclp.intros(2))

lemma has_white_path_to_reaches[elim]:
  "(x has_white_path_to y) s \<Longrightarrow> (x reaches y) s"
unfolding has_white_path_to_def reaches_def
by (induct rule: rtranclp.induct) (auto intro: rtranclp.intros(2))

lemma has_white_path_to_blacken[simp]:
  "(x has_white_path_to w) (s(gc := s gc\<lparr> W := gc_W s - rs \<rparr>)) \<longleftrightarrow> (x has_white_path_to w) s"
unfolding has_white_path_to_def by (simp add: fun_upd_apply)

lemma has_white_path_to_eq_imp': \<comment> \<open>Complicated condition takes care of \<open>alloc\<close>: collapses no object and object with no fields\<close>
  assumes "(x has_white_path_to y) s'"
  assumes "\<forall>r'. \<Union>(ran ` obj_fields ` set_option (sys_heap s' r')) = \<Union>(ran ` obj_fields ` set_option (sys_heap s r'))"
  assumes "\<forall>r'. map_option obj_mark (sys_heap s' r') = map_option obj_mark (sys_heap s r')"
  assumes "sys_fM s' = sys_fM s"
  shows "(x has_white_path_to y) s"
using assms
proof induct
  case (step x y z)
  then have "(y points_to z) s"
    by (cases "sys_heap s y")
       (auto 10 10 simp: ran_def obj_at_def split: option.splits dest!: spec[where x=y])
  with step show ?case
apply -
apply (rule has_white_path_to_step, assumption, assumption)
apply (clarsimp simp: white_def split: obj_at_splits)
apply (metis map_option_eq_Some option.sel)
done
qed simp

lemma has_white_path_to_eq_imp:
  "eq_imp (\<lambda>r'. sys_fM \<^bold>\<otimes> (\<lambda>s. \<Union>(ran ` obj_fields ` set_option (sys_heap s r'))) \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r')))
          (x has_white_path_to y)"
unfolding eq_imp_def
apply (clarsimp simp: all_conj_distrib)
apply (rule iffI)
 apply (erule has_white_path_to_eq_imp'; auto)
apply (erule has_white_path_to_eq_imp'; auto)
done

lemmas has_white_path_to_fun_upd[simp] = eq_imp_fun_upd[OF has_white_path_to_eq_imp, simplified eq_imp_simps, rule_format]


text\<open>grey protects white\<close>

lemma grey_protects_whiteD[dest]:
  "(g grey_protects_white w) s \<Longrightarrow> grey g s \<and> (g = w \<or> white w s)"
by (auto simp: grey_protects_white_def)

lemma grey_protects_whiteI[iff]:
  "grey g s \<Longrightarrow> (g grey_protects_white g) s"
by (simp add: grey_protects_white_def)

lemma grey_protects_whiteE[elim!]:
  "\<lbrakk> (g points_to w) s; grey g s; white w s \<rbrakk> \<Longrightarrow> (g grey_protects_white w) s"
  "\<lbrakk> (g grey_protects_white y) s; (y points_to w) s; white w s \<rbrakk> \<Longrightarrow> (g grey_protects_white w) s"
by (auto simp: grey_protects_white_def)

lemma grey_protects_white_reaches[elim]:
  "(g grey_protects_white w) s \<Longrightarrow> (g reaches w) s"
by (auto simp: grey_protects_white_def)

lemma grey_protects_white_induct[consumes 1, case_names refl step, induct set: grey_protects_white]:
  assumes "(g grey_protects_white w) s"
  assumes "\<And>x. grey x s \<Longrightarrow> P x x"
  assumes "\<And>x y z. \<lbrakk>(x has_white_path_to y) s; P x y; (y points_to z) s; white z s\<rbrakk> \<Longrightarrow> P x z"
  shows "P g w"
using assms unfolding grey_protects_white_def
apply -
apply (elim conjE)
apply (rotate_tac -1)
apply (induct rule: has_white_path_to_induct)
apply blast+
done


subsection\<open> @{term "valid_W_inv"} \<close>

lemma valid_W_inv_sys_ghg_empty_iff[elim!]:
  "valid_W_inv s \<Longrightarrow> sys_ghost_honorary_grey s = {}"
unfolding valid_W_inv_def by simp

lemma WLI[intro]:
  "r \<in> W (s p) \<Longrightarrow> r \<in> WL p s"
  "r \<in> ghost_honorary_grey (s p) \<Longrightarrow> r \<in> WL p s"
unfolding WL_def by simp_all

lemma WL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (ghost_honorary_grey (s p), W (s p)))
          (WL p)"
unfolding eq_imp_def WL_def by simp

lemmas WL_fun_upd[simp] = eq_imp_fun_upd[OF WL_eq_imp, simplified eq_imp_simps, rule_format]

lemma valid_W_inv_eq_imp:
  "eq_imp (\<lambda>(p, r). (\<lambda>s. W (s p)) \<^bold>\<otimes> (\<lambda>s. ghost_honorary_grey (s p)) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r)) \<^bold>\<otimes> sys_mem_lock \<^bold>\<otimes> tso_pending_mark p)
          valid_W_inv"
apply (clarsimp simp: eq_imp_def valid_W_inv_def fun_eq_iff all_conj_distrib white_def)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>p. WL p s = WL p s'")
 apply (subgoal_tac "\<forall>x. marked x s \<longleftrightarrow> marked x s'")
  apply (subgoal_tac "\<forall>x. obj_at (\<lambda>obj. obj_mark obj = (\<not>sys_fM s')) x s \<longleftrightarrow> obj_at (\<lambda>obj. obj_mark obj = (\<not>sys_fM s')) x s'")
   apply (subgoal_tac "\<forall>x xa xb. mw_Mark xa xb \<in> set (sys_mem_store_buffers x s) \<longleftrightarrow> mw_Mark xa xb \<in> set (sys_mem_store_buffers x s')")
    apply (simp; fail)
   apply clarsimp
   apply (rename_tac x xa xb)
   apply (drule_tac x=x in spec, drule arg_cong[where f=set], fastforce)
  apply (clarsimp split: obj_at_splits)
  apply (rename_tac x)
  apply ( (drule_tac x=x in spec)+ )[1]
  apply (case_tac "sys_heap s x", simp_all)
   apply (case_tac "sys_heap s' x", auto)[1]
 apply (clarsimp split: obj_at_splits)
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (case_tac "sys_heap s x", simp_all)
 apply (case_tac "sys_heap s' x", simp_all)
apply (simp add: WL_def)
done

lemmas valid_W_inv_fun_upd[simp] = eq_imp_fun_upd[OF valid_W_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma valid_W_invE[elim!]:
  "\<lbrakk> r \<in> W (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> marked r s"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk> \<Longrightarrow> marked r s"
  "\<lbrakk> r \<in> W (s p); valid_W_inv s \<rbrakk> \<Longrightarrow> valid_ref r s"
  "\<lbrakk> r \<in> ghost_honorary_grey (s p); sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk> \<Longrightarrow> valid_ref r s"
  "\<lbrakk> mw_Mark r fl \<in> set (sys_mem_store_buffers p s); valid_W_inv s \<rbrakk> \<Longrightarrow> r \<in> ghost_honorary_grey (s p)"
unfolding valid_W_inv_def
apply (simp_all add:  split: obj_at_splits)
apply blast+
done

lemma valid_W_invD:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mark r fl # ws; valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark ws = []"
  "\<lbrakk> mw_Mark r fl \<in> set (sys_mem_store_buffers p s); valid_W_inv s \<rbrakk>
     \<Longrightarrow> fl = sys_fM s \<and> r \<in> ghost_honorary_grey (s p) \<and> tso_locked_by p s \<and> white r s \<and> filter is_mw_Mark (sys_mem_store_buffers p s) = [mw_Mark r fl]"
unfolding valid_W_inv_def white_def by (clarsimp dest!: spec[where x=p], blast)+

lemma valid_W_inv_colours:
  "\<lbrakk>white x s; valid_W_inv s\<rbrakk> \<Longrightarrow> x \<notin> W (s p)"
using marked_not_white valid_W_invE(1) by force

lemma valid_W_inv_no_mark_stores_invD:
  "\<lbrakk> sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk>
     \<Longrightarrow> tso_pending p is_mw_Mark s = []"
by (auto dest: valid_W_invD(2) intro!: filter_False)

lemma valid_W_inv_sys_load[simp]:
  "\<lbrakk> sys_mem_lock s \<noteq> Some p; valid_W_inv s \<rbrakk>
     \<Longrightarrow> sys_load p (mr_Mark r) (s sys) = mv_Mark (map_option obj_mark (sys_heap s r))"
unfolding sys_load_def fold_stores_def
apply clarsimp
apply (rule fold_invariant[where P="\<lambda>fr. map_option obj_mark (heap (fr (s sys)) r) = map_option obj_mark (sys_heap s r)"
                             and Q="\<lambda>w. \<forall>r fl. w \<noteq> mw_Mark r fl"])
  apply (auto simp: map_option_case do_store_action_def filter_empty_conv fun_upd_apply
              dest: valid_W_invD(2)
             split: mem_store_action.splits option.splits)
done


subsection\<open> \<open>grey_reachable\<close> \<close>

lemma grey_reachable_eq_imp:
  "eq_imp (\<lambda>r'. (\<lambda>s. \<Union>p. WL p s) \<^bold>\<otimes> (\<lambda>s. Set.bind (Option.set_option (sys_heap s r')) (ran \<circ> obj_fields)))
          (grey_reachable r)"
by (auto simp: eq_imp_def grey_reachable_def grey_def set_eq_iff reaches_fields)

lemmas grey_reachable_fun_upd[simp] = eq_imp_fun_upd[OF grey_reachable_eq_imp, simplified eq_imp_simps, rule_format]

lemma grey_reachableI[intro]:
  "grey g s \<Longrightarrow> grey_reachable g s"
unfolding grey_reachable_def reaches_def by blast

lemma grey_reachableE:
  "\<lbrakk> (g points_to y) s; grey_reachable g s \<rbrakk> \<Longrightarrow> grey_reachable y s"
unfolding grey_reachable_def reaches_def by (auto elim: rtranclp.intros(2))


subsection\<open>valid refs inv\<close>

lemma valid_refs_invI:
  "\<lbrakk> \<And>m x y. \<lbrakk> (x reaches y) s; mut_m.root m x s \<or> grey x s \<rbrakk> \<Longrightarrow> valid_ref y s
   \<rbrakk> \<Longrightarrow> valid_refs_inv s"
by (auto simp: valid_refs_inv_def mut_m.reachable_def grey_reachable_def)

lemma valid_refs_inv_eq_imp:
  "eq_imp (\<lambda>(m', r'). (\<lambda>s. roots (s (mutator m'))) \<^bold>\<otimes> (\<lambda>s. ghost_honorary_root (s (mutator m'))) \<^bold>\<otimes> (\<lambda>s. map_option obj_fields (sys_heap s r')) \<^bold>\<otimes> tso_pending_mutate (mutator m') \<^bold>\<otimes> (\<lambda>s. \<Union>p. WL p s))
          valid_refs_inv"
apply (clarsimp simp: eq_imp_def valid_refs_inv_def grey_reachable_def all_conj_distrib)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r'. valid_ref r' s \<longleftrightarrow> valid_ref r' s'")
 apply (subgoal_tac "\<forall>r'. \<Union>(ran ` obj_fields ` set_option (sys_heap s r')) = \<Union>(ran ` obj_fields ` set_option (sys_heap s' r'))")
  apply (subst eq_impD[OF mut_m.reachable_eq_imp])
   defer
   apply (subst eq_impD[OF grey_eq_imp])
    defer
    apply (subst eq_impD[OF reaches_eq_imp])
     defer
     apply force
    apply (metis option.set_map)
   apply (clarsimp split: obj_at_splits)
   apply (metis (no_types, hide_lams) None_eq_map_option_iff option.exhaust)
  apply clarsimp
 apply clarsimp
apply clarsimp
done

lemmas valid_refs_inv_fun_upd[simp] = eq_imp_fun_upd[OF valid_refs_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma valid_refs_invD[elim]:
  "\<lbrakk> x \<in> mut_m.mut_roots m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> x \<in> mut_m.mut_roots m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
  "\<lbrakk> x \<in> mut_m.tso_store_refs m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> x \<in> mut_m.tso_store_refs m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
  "\<lbrakk> w \<in> set (sys_mem_store_buffers (mutator m) s); x \<in> store_refs w; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> w \<in> set (sys_mem_store_buffers (mutator m) s); x \<in> store_refs w; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
  "\<lbrakk> grey x s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> mut_m.reachable m x s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref x s"
  "\<lbrakk> mut_m.reachable m x s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s x = Some obj"
  "\<lbrakk> x \<in> mut_m.mut_ghost_honorary_root m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref y s"
  "\<lbrakk> x \<in> mut_m.mut_ghost_honorary_root m s; (x reaches y) s; valid_refs_inv s \<rbrakk> \<Longrightarrow> \<exists>obj. sys_heap s y = Some obj"
apply (simp_all add: valid_refs_inv_def grey_reachable_def mut_m.reachable_def mut_m.tso_store_refs_def
              split: obj_at_splits)
apply blast+
done


text\<open>reachable snapshot inv\<close>

context mut_m
begin

lemma reachable_snapshot_invI[intro]:
  "(\<And>y. reachable y s \<Longrightarrow> in_snapshot y s) \<Longrightarrow> reachable_snapshot_inv s"
by (simp add: reachable_snapshot_inv_def)

lemma reachable_snapshot_inv_eq_imp:
  "eq_imp (\<lambda>r'. mut_roots \<^bold>\<otimes> mut_ghost_honorary_root \<^bold>\<otimes> (\<lambda>s. r' \<in> (\<Union>p. WL p s)) \<^bold>\<otimes> sys_fM
            \<^bold>\<otimes> (\<lambda>s. \<Union>(ran ` obj_fields ` set_option (sys_heap s r'))) \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r'))
            \<^bold>\<otimes> tso_pending_mutate (mutator m))
          reachable_snapshot_inv"
unfolding eq_imp_def mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def black_def grey_def
apply (clarsimp simp: all_conj_distrib)
apply (rename_tac s s')
apply (subst (1) eq_impD[OF has_white_path_to_eq_imp])
 apply force
apply (subst eq_impD[OF reachable_eq_imp])
 apply force
apply (subgoal_tac "\<forall>x. obj_at (\<lambda>obj. obj_mark obj = sys_fM s') x s \<longleftrightarrow> obj_at (\<lambda>obj. obj_mark obj = sys_fM s') x s'")
 apply force
apply (clarsimp split: obj_at_splits)
apply (rename_tac x)
apply (drule_tac x=x in spec)+
apply (case_tac "sys_heap s x", simp_all)
apply (case_tac "sys_heap s' x", simp_all)
done

end

lemmas reachable_snapshot_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.reachable_snapshot_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma in_snapshotI[intro]:
  "black r s \<Longrightarrow> in_snapshot r s"
  "grey r s \<Longrightarrow> in_snapshot r s"
  "\<lbrakk> white w s; (g grey_protects_white w) s \<rbrakk> \<Longrightarrow> in_snapshot w s"
by (auto simp: in_snapshot_def)

lemma \<comment> \<open>Sanity\<close>
  "in_snapshot r s \<Longrightarrow> black r s \<or> grey r s \<or> white r s"
by (auto simp: in_snapshot_def)

lemma in_snapshot_valid_ref:
  "\<lbrakk> in_snapshot r s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref r s"
by (metis blackD(1) grey_protects_whiteD grey_protects_white_reaches in_snapshot_def obj_at_cong obj_at_def option.case(2) valid_refs_invD(7))

lemma reachableI2[intro]:
  "x \<in> mut_m.mut_ghost_honorary_root m s \<Longrightarrow> mut_m.reachable m x s"
unfolding mut_m.reachable_def reaches_def by blast

lemma tso_pending_mw_mutate_cong:
  "\<lbrakk> filter is_mw_Mutate (sys_mem_store_buffers p s) = filter is_mw_Mutate (sys_mem_store_buffers p s');
     \<And>r f r'. P r f r' \<longleftrightarrow> Q r f r' \<rbrakk>
     \<Longrightarrow> (\<forall>r f r'. mw_Mutate r f r' \<in> set (sys_mem_store_buffers p s)  \<longrightarrow> P r f r')
     \<longleftrightarrow> (\<forall>r f r'. mw_Mutate r f r' \<in> set (sys_mem_store_buffers p s') \<longrightarrow> Q r f r')"
by (intro iff_allI) (auto dest!: arg_cong[where f=set])

lemma (in mut_m) marked_insertions_eq_imp:
  "eq_imp (\<lambda>r'. sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r')) \<^bold>\<otimes> tso_pending_mw_mutate (mutator m))
          marked_insertions"
unfolding eq_imp_def marked_insertions_def obj_at_def
apply (clarsimp split: mem_store_action.splits)
apply (erule tso_pending_mw_mutate_cong)
apply (clarsimp split: option.splits obj_at_splits)
apply (rename_tac s s' opt x)
apply (drule_tac x=x in spec)
apply auto
done

lemmas marked_insertions_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.marked_insertions_eq_imp, simplified eq_imp_simps, rule_format]

lemma marked_insertionD[elim!]:
  "\<lbrakk> sys_mem_store_buffers (mutator m) s = mw_Mutate r f (Some r') # ws; mut_m.marked_insertions m s \<rbrakk>
     \<Longrightarrow> marked r' s"
by (auto simp: mut_m.marked_insertions_def)

lemma marked_insertions_store_buffer_empty[intro]:
  "tso_pending_mutate (mutator m) s = [] \<Longrightarrow> mut_m.marked_insertions m s"
unfolding mut_m.marked_insertions_def by (auto simp: filter_empty_conv split: mem_store_action.splits)

(* marked_deletions *)

lemma (in mut_m) marked_deletions_eq_imp:
  "eq_imp (\<lambda>r'. sys_fM \<^bold>\<otimes> (\<lambda>s. map_option obj_fields (sys_heap s r')) \<^bold>\<otimes> (\<lambda>s. map_option obj_mark (sys_heap s r')) \<^bold>\<otimes> tso_pending_mw_mutate (mutator m))
          marked_deletions"
unfolding eq_imp_def marked_deletions_def obj_at_field_on_heap_def ran_def
apply (clarsimp simp: all_conj_distrib)
apply (drule arg_cong[where f=set])
apply (subgoal_tac "\<forall>x. marked x s \<longleftrightarrow> marked x s'")
 apply (clarsimp cong: option.case_cong)
 apply (rule iffI; clarsimp simp: set_eq_iff split: option.splits mem_store_action.splits; blast)
apply clarsimp
apply (rename_tac s s' x)
apply (drule_tac x=x in spec)+
apply (force split: obj_at_splits)
done

lemmas marked_deletions_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.marked_deletions_eq_imp, simplified eq_imp_simps, rule_format]

lemma marked_deletions_store_buffer_empty[intro]:
  "tso_pending_mutate (mutator m) s = [] \<Longrightarrow> mut_m.marked_deletions m s"
unfolding mut_m.marked_deletions_def by (auto simp: filter_empty_conv split: mem_store_action.splits)


subsection\<open>Location-specific simplification rules\<close>

lemma obj_at_ref_sweep_loop_free[simp]:
  "obj_at P r (s(sys := (s sys)\<lparr>heap := (sys_heap s)(r' := None)\<rparr>)) \<longleftrightarrow> obj_at P r s \<and> r \<noteq> r'"
by (clarsimp simp: fun_upd_apply split: obj_at_splits)

lemma obj_at_alloc[simp]:
  "sys_heap s r' = None
  \<Longrightarrow> obj_at P r (s(m := mut_m_s', sys := (s sys)\<lparr> heap := sys_heap s(r' \<mapsto> obj) \<rparr>))
  \<longleftrightarrow> (obj_at P r s \<or> (r = r' \<and> P obj))"
unfolding ran_def by (simp add: fun_upd_apply split: obj_at_splits)

lemma valid_ref_valid_null_ref_simps[simp]:
  "valid_ref r (s(sys := do_store_action w (s sys)\<lparr>mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>)) \<longleftrightarrow> valid_ref r s"
  "valid_null_ref r' (s(sys := do_store_action w (s sys)\<lparr>mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>)) \<longleftrightarrow> valid_null_ref r' s"
  "valid_null_ref r' (s(mutator m := mut_s', sys := (s sys)\<lparr> heap := (heap (s sys))(r'' \<mapsto> obj) \<rparr>)) \<longleftrightarrow> valid_null_ref r' s \<or> r' = Some r''"
unfolding do_store_action_def valid_null_ref_def
by (auto simp: fun_upd_apply
        split: mem_store_action.splits obj_at_splits option.splits)

context mut_m
begin

lemma reachable_load[simp]:
  assumes "sys_load (mutator m) (mr_Ref r f) (s sys) = mv_Ref r'"
  assumes "r \<in> mut_roots s"
  shows "mut_m.reachable m' y (s(mutator m := s (mutator m)\<lparr> roots := mut_roots s \<union> Option.set_option r' \<rparr>)) \<longleftrightarrow> mut_m.reachable m' y s" (is "?lhs = ?rhs")
proof(cases "m' = m")
  case True show ?thesis
  proof(rule iffI)
    assume ?lhs with assms True show ?rhs
unfolding sys_load_def
apply clarsimp
apply (clarsimp simp: reachable_def reaches_def tso_store_refs_def sys_load_def fold_stores_def fun_upd_apply)
apply (elim disjE)
   apply blast
  defer
 apply blast
apply blast

apply (fold fold_stores_def)
apply clarsimp
apply (drule (1) fold_stores_points_to)
apply (erule disjE)
 apply (fastforce elim!: converse_rtranclp_into_rtranclp[rotated] split: obj_at_splits intro!: ranI)
apply (clarsimp split: mem_store_action.splits)
apply meson
done
  next
    assume ?rhs with True show ?lhs unfolding mut_m.reachable_def by (fastforce simp: fun_upd_apply)
  qed
qed (simp add: fun_upd_apply)

end

text\<open>WL\<close>

lemma WL_blacken[simp]:
  "gc_ghost_honorary_grey s = {}
    \<Longrightarrow> WL p (s(gc := s gc\<lparr> W := gc_W s - rs \<rparr>)) = WL p s - { r |r. p = gc \<and> r \<in> rs }"
unfolding WL_def by (auto simp: fun_upd_apply)

lemma WL_hs_done[simp]:
  "ghost_honorary_grey (s (mutator m)) = {}
     \<Longrightarrow> WL p (s(mutator m := s (mutator m)\<lparr> W := {}, ghost_hs_phase := hp' \<rparr>,
                 sys   := s sys\<lparr> hs_pending := hsp', W := sys_W s \<union> W (s (mutator m)),
                                 ghost_hs_in_sync := in' \<rparr>))
      = (case p of gc \<Rightarrow> WL gc s | mutator m' \<Rightarrow> (if m' = m then {} else WL (mutator m') s) | sys \<Rightarrow> WL sys s \<union> WL (mutator m) s)"
  "ghost_honorary_grey (s (mutator m)) = {}
     \<Longrightarrow> WL p (s(mutator m := s (mutator m)\<lparr> W := {} \<rparr>,
                 sys   := s sys\<lparr> hs_pending := hsp', W := sys_W s \<union> W (s (mutator m)),
                                 ghost_hs_in_sync := in' \<rparr>))
      = (case p of gc \<Rightarrow> WL gc s | mutator m' \<Rightarrow> (if m' = m then {} else WL (mutator m') s) | sys \<Rightarrow> WL sys s \<union> WL (mutator m) s)"
unfolding WL_def by (auto simp: fun_upd_apply split: process_name.splits)

lemma colours_load_W[iff]:
  "gc_W s = {} \<Longrightarrow> black r (s(gc := (s gc)\<lparr>W := W (s sys)\<rparr>, sys := (s sys)\<lparr>W := {}\<rparr>)) \<longleftrightarrow> black r s"
  "gc_W s = {} \<Longrightarrow> grey r (s(gc := (s gc)\<lparr>W := W (s sys)\<rparr>, sys := (s sys)\<lparr>W := {}\<rparr>)) \<longleftrightarrow> grey r s"
unfolding black_def grey_def WL_def
apply (simp_all add: fun_upd_apply)
apply safe
apply (case_tac [!] x)
apply blast+
done

lemma WL_load_W[simp]:
  "gc_W s = {}
    \<Longrightarrow> (WL p (s(gc := (s gc)\<lparr>W := sys_W s\<rparr>, sys := (s sys)\<lparr>W := {}\<rparr>)))
     = (case p of gc \<Rightarrow> WL gc s \<union> sys_W s | mutator m \<Rightarrow> WL (mutator m) s | sys \<Rightarrow> sys_ghost_honorary_grey s)"
unfolding WL_def by (auto simp: fun_upd_apply split: process_name.splits)

text\<open>no grey refs\<close>

lemma no_grey_refs_eq_imp:
  "eq_imp (\<lambda>(_::unit). (\<lambda>s. \<Union>p. WL p s))
          no_grey_refs"
by (auto simp add: eq_imp_def grey_def no_grey_refs_def set_eq_iff)

lemmas no_grey_refs_fun_upd[simp] = eq_imp_fun_upd[OF no_grey_refs_eq_imp, simplified eq_imp_simps, rule_format]

lemma no_grey_refs_no_pending_marks:
  "\<lbrakk> no_grey_refs s; valid_W_inv s \<rbrakk> \<Longrightarrow> tso_no_pending_marks s"
unfolding no_grey_refs_def by (auto intro!: filter_False dest: valid_W_invD(2))

lemma no_grey_refs_not_grey_reachableD:
  "no_grey_refs s \<Longrightarrow> \<not>grey_reachable x s"
by (clarsimp simp: no_grey_refs_def grey_reachable_def)

lemma no_grey_refsD:
  "no_grey_refs s \<Longrightarrow> r \<notin> W (s p)"
  "no_grey_refs s \<Longrightarrow> r \<notin> WL p s"
  "no_grey_refs s \<Longrightarrow> r \<notin> ghost_honorary_grey (s p)"
by (auto simp: no_grey_refs_def)

lemma no_grey_refs_marked[dest]:
  "\<lbrakk> marked r s; no_grey_refs s \<rbrakk> \<Longrightarrow> black r s"
by (auto simp: no_grey_refs_def black_def)

lemma no_grey_refs_bwD[dest]:
  "\<lbrakk> heap (s sys) r = Some obj; no_grey_refs s \<rbrakk> \<Longrightarrow> black r s \<or> white r s"
by (clarsimp simp: black_def grey_def no_grey_refs_def white_def split: obj_at_splits)

context mut_m
begin

lemma reachable_blackD:
  "\<lbrakk> no_grey_refs s; reachable_snapshot_inv s; reachable r s \<rbrakk> \<Longrightarrow> black r s"
by (simp add: no_grey_refs_def reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)

lemma no_grey_refs_not_reachable:
  "\<lbrakk> no_grey_refs s; reachable_snapshot_inv s; white r s \<rbrakk> \<Longrightarrow> \<not>reachable r s"
by (fastforce simp: no_grey_refs_def reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def
             split: obj_at_splits)

lemma no_grey_refs_not_rootD:
  "\<lbrakk> no_grey_refs s; reachable_snapshot_inv s; white r s \<rbrakk>
     \<Longrightarrow> r \<notin> mut_roots s \<and> r \<notin> mut_ghost_honorary_root s \<and> r \<notin> tso_store_refs s"
apply (drule (2) no_grey_refs_not_reachable)
apply (force simp: reachable_def reaches_def)
done

lemma reachable_snapshot_inv_white_root:
  "\<lbrakk> white w s; w \<in> mut_roots s \<or> w \<in> mut_ghost_honorary_root s; reachable_snapshot_inv s \<rbrakk> \<Longrightarrow> \<exists>g. (g grey_protects_white w) s"
unfolding reachable_snapshot_inv_def in_snapshot_def reachable_def grey_protects_white_def reaches_def by auto

end

(* colours *)

lemma black_dequeue_Mark[simp]:
  "black b (s(sys := (s sys)\<lparr> heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws) \<rparr>))
\<longleftrightarrow> (black b s \<and> b \<noteq> r) \<or> (b = r \<and> fl = sys_fM s \<and> valid_ref r s \<and> \<not>grey r s)"
unfolding black_def by (auto simp: fun_upd_apply split: obj_at_splits)

lemma colours_sweep_loop_free[iff]:
  "black r (s(sys := s sys\<lparr>heap := (heap (s sys))(r' := None)\<rparr>)) \<longleftrightarrow> (black r s \<and> r \<noteq> r')"
  "grey r (s(sys := s sys\<lparr>heap := (heap (s sys))(r' := None)\<rparr>)) \<longleftrightarrow> (grey r s)"
  "white r (s(sys := s sys\<lparr>heap := (heap (s sys))(r' := None)\<rparr>)) \<longleftrightarrow> (white r s \<and> r \<noteq> r')"
unfolding black_def grey_def white_def by (auto simp: fun_upd_apply split: obj_at_splits)

lemma colours_get_work_done[simp]:
  "black r (s(mutator m := (s (mutator m))\<lparr>W := {}\<rparr>,
              sys := (s sys)\<lparr> hs_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_hs_in_sync := his' \<rparr>)) \<longleftrightarrow> black r s"
  "grey r (s(mutator m := (s (mutator m))\<lparr>W := {}\<rparr>,
              sys := (s sys)\<lparr> hs_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_hs_in_sync := his' \<rparr>)) \<longleftrightarrow> grey r s"
  "white r (s(mutator m := (s (mutator m))\<lparr>W := {}\<rparr>,
              sys := (s sys)\<lparr> hs_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_hs_in_sync := his' \<rparr>)) \<longleftrightarrow> white r s"
unfolding black_def grey_def WL_def
apply (simp_all add: fun_upd_apply split: obj_at_splits)
 apply blast
apply (metis process_name.distinct(3))
done

lemma colours_get_roots_done[simp]:
  "black r (s(mutator m := (s (mutator m))\<lparr> W := {}, ghost_hs_phase := hs' \<rparr>,
              sys := (s sys)\<lparr> hs_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_hs_in_sync := his' \<rparr>)) \<longleftrightarrow> black r s"
  "grey r (s(mutator m := (s (mutator m))\<lparr> W := {}, ghost_hs_phase := hs' \<rparr>,
              sys := (s sys)\<lparr> hs_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_hs_in_sync := his' \<rparr>)) \<longleftrightarrow> grey r s"
  "white r (s(mutator m := (s (mutator m))\<lparr> W := {}, ghost_hs_phase := hs' \<rparr>,
              sys := (s sys)\<lparr> hs_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_hs_in_sync := his' \<rparr>)) \<longleftrightarrow> white r s"
unfolding black_def grey_def WL_def
apply (simp_all add: fun_upd_apply split: obj_at_splits)
 apply blast
apply (metis process_name.distinct(3))
done

lemma colours_flip_fM[simp]:
  "fl \<noteq> sys_fM s \<Longrightarrow> black b (s(sys := (s sys)\<lparr>fM := fl, mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>)) \<longleftrightarrow> white b s \<and> \<not>grey b s"
unfolding black_def white_def by (simp add: fun_upd_apply)

lemma colours_alloc[simp]:
  "heap (s sys) r' = None
     \<Longrightarrow> black r (s(mutator m := (s (mutator m))\<lparr> roots := roots' \<rparr>, sys := (s sys)\<lparr>heap := heap (s sys)(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> black r s \<or> (r' = r \<and> fl = sys_fM s \<and> \<not>grey r' s)"
  "grey r (s(mutator m := (s (mutator m))\<lparr> roots := roots' \<rparr>, sys := (s sys)\<lparr>heap := heap (s sys)(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> grey r s"
  "heap (s sys) r' = None
     \<Longrightarrow> white r (s(mutator m := (s (mutator m))\<lparr> roots := roots' \<rparr>, sys := (s sys)\<lparr>heap := heap (s sys)(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> white r s \<or> (r' = r \<and> fl \<noteq> sys_fM s)"
unfolding black_def white_def by (auto simp: fun_upd_apply split: obj_at_splits)

lemma heap_colours_alloc[simp]:
  "\<lbrakk> heap (s sys) r' = None; valid_refs_inv s \<rbrakk>
  \<Longrightarrow> black_heap (s(mutator m := s (mutator m)\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
  \<longleftrightarrow> black_heap s \<and> fl = sys_fM s"
  "heap (s sys) r' = None
  \<Longrightarrow> white_heap (s(mutator m := s (mutator m)\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
  \<longleftrightarrow> white_heap s \<and> fl \<noteq> sys_fM s"
unfolding black_heap_def white_def white_heap_def
apply (simp_all add: fun_upd_apply split: obj_at_splits)
 apply (rule iffI)
  apply (intro allI conjI impI)
   apply (rename_tac x)
   apply (drule_tac x=x in spec)
   apply clarsimp
  apply (drule spec[where x=r'], auto simp: reaches_def dest!: valid_refs_invD split: obj_at_splits)[2]
apply (rule iffI)
 apply (intro allI conjI impI)
  apply (rename_tac x obj)
  apply (drule_tac x=x in spec)
  apply clarsimp
 apply (drule spec[where x=r'], auto dest!: valid_refs_invD split: obj_at_splits)[2]
done

lemma grey_protects_white_hs_done[simp]:
  "(g grey_protects_white w) (s(mutator m := s (mutator m)\<lparr> W := {}, ghost_hs_phase := hs' \<rparr>,
                              sys := s sys\<lparr> hs_pending := hp', W := sys_W s \<union> W (s (mutator m)),
                                            ghost_hs_in_sync := his' \<rparr>))
  \<longleftrightarrow> (g grey_protects_white w) s"
unfolding grey_protects_white_def by (simp add: fun_upd_apply)

lemma grey_protects_white_alloc[simp]:
  "\<lbrakk> fl = sys_fM s; sys_heap s r = None \<rbrakk>
     \<Longrightarrow> (g grey_protects_white w) (s(mutator m := s (mutator m)\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> (g grey_protects_white w) s"
unfolding grey_protects_white_def has_white_path_to_def by simp

lemma (in mut_m) reachable_snapshot_inv_sweep_loop_free:
  fixes s :: "('field, 'mut, 'payload, 'ref) lsts"
  assumes nmr: "white r s"
  assumes ngs: "no_grey_refs s"
  assumes rsi: "reachable_snapshot_inv s"
  shows "reachable_snapshot_inv (s(sys := (s sys)\<lparr>heap := (heap (s sys))(r := None)\<rparr>))" (is "reachable_snapshot_inv ?s'")
proof
  fix y :: "'ref"
  assume rx: "reachable y ?s'"
  then have "black y s \<and> y \<noteq> r"
  proof(induct rule: reachable_induct)
    case (root x) with ngs nmr rsi show ?case
      by (auto simp: fun_upd_apply dest: reachable_blackD)
  next
    case (ghost_honorary_root x) with ngs nmr rsi show ?case
      unfolding reachable_def reaches_def by (auto simp: fun_upd_apply dest: reachable_blackD)
  next
    case (tso_root x) with ngs nmr rsi show ?case
      unfolding reachable_def reaches_def by (auto simp: fun_upd_apply dest: reachable_blackD)
  next
    case (reaches x y) with ngs nmr rsi show ?case
      unfolding reachable_def reaches_def
      apply (clarsimp simp: fun_upd_apply)
      apply (drule predicate2D[OF rtranclp_mono[where s="\<lambda>x y. (x points_to y) s", OF predicate2I], rotated])
       apply (clarsimp split: obj_at_splits if_splits)
      apply (rule conjI)
       apply (rule reachable_blackD, assumption, assumption)
       apply (simp add: reachable_def reaches_def)
       apply (blast intro: rtranclp.intros(2))
      apply clarsimp
      apply (frule (1) reachable_blackD[where r=r])
       apply (simp add: reachable_def reaches_def)
       apply (blast intro: rtranclp.intros(2))
      apply auto
      done
  qed
  then show "in_snapshot y ?s'"
    unfolding in_snapshot_def by simp
qed

lemma reachable_alloc[simp]:
  assumes rn: "sys_heap s r = None"
  shows "mut_m.reachable m r' (s(mutator m' := (s (mutator m'))\<lparr>roots := insert r (roots (s (mutator m')))\<rparr>, sys := (s sys)\<lparr>heap := (sys_heap s)(r \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> mut_m.reachable m r' s \<or> (m' = m \<and> r' = r)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs from this assms show ?rhs
  proof(induct rule: reachable_induct)
    case (reaches x y) then show ?case by clarsimp (fastforce simp: mut_m.reachable_def reaches_def elim: rtranclp.intros(2) split: obj_at_splits)
  qed (auto simp: fun_upd_apply split: if_splits)
next
  assume ?rhs then show ?lhs
  proof(rule disjE)
    assume "mut_m.reachable m r' s" then show ?thesis
    proof(induct rule: reachable_induct)
      case (tso_root x) then show ?case
        unfolding mut_m.reachable_def by fastforce
    next
      case (reaches x y) with rn show ?case
        unfolding mut_m.reachable_def by fastforce
    qed (auto simp: fun_upd_apply)
  next
    assume "m' = m \<and> r' = r" with rn show ?thesis
      unfolding mut_m.reachable_def by (fastforce simp: fun_upd_apply)
  qed
qed

context mut_m
begin

lemma reachable_snapshot_inv_alloc[simp, elim!]:
  fixes s :: "('field, 'mut, 'payload, 'ref) lsts"
  assumes rsi: "reachable_snapshot_inv s"
  assumes rn: "sys_heap s r = None"
  assumes fl: "fl = sys_fM s"
  assumes vri: "valid_refs_inv s"
  shows "reachable_snapshot_inv (s(mutator m' := (s (mutator m'))\<lparr>roots := insert r (roots (s (mutator m')))\<rparr>, sys := (s sys)\<lparr>heap := (sys_heap s)(r \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))"
(is "reachable_snapshot_inv ?s'")
using assms unfolding reachable_snapshot_inv_def in_snapshot_def
by (auto simp del: reachable_fun_upd)

lemma reachable_snapshot_inv_discard_roots[simp]:
  "\<lbrakk> reachable_snapshot_inv s; roots' \<subseteq> roots (s (mutator m)) \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := (s (mutator m))\<lparr>roots := roots'\<rparr>))"
unfolding reachable_snapshot_inv_def reachable_def in_snapshot_def grey_protects_white_def by (auto simp: fun_upd_apply)

lemma reachable_snapshot_inv_load[simp]:
  "\<lbrakk> reachable_snapshot_inv s; sys_load (mutator m) (mr_Ref r f) (s sys) = mv_Ref r'; r \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := s (mutator m)\<lparr> roots := mut_roots s \<union> Option.set_option r' \<rparr>))"
unfolding reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def by (simp add: fun_upd_apply)

lemma reachable_snapshot_inv_store_ins[simp]:
  "\<lbrakk> reachable_snapshot_inv s; r \<in> mut_roots s; (\<exists>r'. opt_r' = Some r') \<longrightarrow> the opt_r' \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := {}\<rparr>,
                                  sys := s sys\<lparr>  mem_store_buffers := (mem_store_buffers (s sys))(mutator m := sys_mem_store_buffers (mutator m) s @ [mw_Mutate r f opt_r']) \<rparr>))"
unfolding reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def reachable_def
apply clarsimp
apply (drule_tac x=x in spec)
apply (auto simp: fun_upd_apply)
(* FIXME what's gone wrong here? *)
apply (subst (asm) tso_store_refs_simps; force)+
done

end

lemma WL_mo_co_mark[simp]:
  "ghost_honorary_grey (s p) = {}
     \<Longrightarrow> WL p' (s(p := s p\<lparr> ghost_honorary_grey := rs \<rparr>)) = WL p' s \<union> { r |r. p' = p \<and> r \<in> rs}"
unfolding WL_def by (simp add: fun_upd_apply)

lemma ghost_honorary_grey_mo_co_mark[simp]:
  "\<lbrakk> ghost_honorary_grey (s p) = {} \<rbrakk> \<Longrightarrow> black b (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>)) \<longleftrightarrow> black b s \<and> b \<noteq> r"
  "\<lbrakk> ghost_honorary_grey (s p) = {} \<rbrakk> \<Longrightarrow> grey g (s(p := (s p)\<lparr>ghost_honorary_grey := {r}\<rparr>)) \<longleftrightarrow> grey g s \<or> g = r"
  "\<lbrakk> ghost_honorary_grey (s p) = {} \<rbrakk> \<Longrightarrow> white w (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>))  \<longleftrightarrow> white w s"
unfolding black_def grey_def by (auto simp: fun_upd_apply)

lemma ghost_honorary_grey_mo_co_W[simp]:
  "ghost_honorary_grey (s p') = {r}
     \<Longrightarrow> (WL p (s(p' := (s p')\<lparr>W := insert r (W (s p')), ghost_honorary_grey := {}\<rparr>))) = (WL p s)"
  "ghost_honorary_grey (s p') = {r}
     \<Longrightarrow> grey g (s(p' := (s p')\<lparr>W := insert r (W (s p')), ghost_honorary_grey := {}\<rparr>)) \<longleftrightarrow> grey g s"
unfolding grey_def WL_def by (auto simp: fun_upd_apply split: process_name.splits if_splits)

lemma reachable_sweep_loop_free:
  "mut_m.reachable m r (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := None)\<rparr>))
   \<Longrightarrow> mut_m.reachable m r s"
unfolding mut_m.reachable_def reaches_def by (clarsimp simp: fun_upd_apply) (metis (no_types, lifting) mono_rtranclp)

lemma reachable_deref_del[simp]:
  "\<lbrakk> sys_load (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; r \<in> mut_m.mut_roots m s; mut_m.mut_ghost_honorary_root m s = {} \<rbrakk>
   \<Longrightarrow> mut_m.reachable m' y (s(mutator m := s (mutator m)\<lparr> ghost_honorary_root := Option.set_option opt_r', ref := opt_r' \<rparr>))
   \<longleftrightarrow> mut_m.reachable m' y s"
unfolding mut_m.reachable_def reaches_def sys_load_def
apply (clarsimp simp: fun_upd_apply)
apply (rule iffI)
 apply clarsimp
 apply (elim disjE)
   apply metis
  apply (erule option_bind_invE; auto dest!: fold_stores_points_to)
 apply (auto elim!: converse_rtranclp_into_rtranclp[rotated]
              simp: mut_m.tso_store_refs_def)
done

lemma no_black_refs_dequeue[simp]:
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mark r fl # ws; no_black_refs s; valid_W_inv s \<rbrakk>
   \<Longrightarrow> no_black_refs (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
  "\<lbrakk> sys_mem_store_buffers p s = mw_Mutate r f r' # ws; no_black_refs s \<rbrakk>
     \<Longrightarrow> no_black_refs (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := r')\<rparr>) (sys_heap s r)),
                                      mem_store_buffers := (mem_store_buffers (s sys))(p := ws)\<rparr>))"
unfolding no_black_refs_def by (auto simp: fun_upd_apply dest: valid_W_invD)

lemma colours_blacken[simp]:
  "valid_W_inv s \<Longrightarrow> black b (s(gc := s gc\<lparr>W := gc_W s - {r}\<rparr>)) \<longleftrightarrow> black b s \<or> (r \<in> gc_W s \<and> b = r)"
  "\<lbrakk> r \<in> gc_W s; valid_W_inv s \<rbrakk> \<Longrightarrow> grey g (s(gc := s gc\<lparr>W := gc_W s - {r}\<rparr>)) \<longleftrightarrow> (grey g s \<and> g \<noteq> r)"
  (*  "white w (s(gc := s gc\<lparr>W := gc_W s - {r}\<rparr>)) \<longleftrightarrow> white w s" is redundant *)
unfolding black_def grey_def valid_W_inv_def
apply (simp_all add: all_conj_distrib split: obj_at_splits if_splits)
apply safe
apply (simp_all add: WL_def fun_upd_apply split: if_splits)
  apply (metis option.distinct(1))
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply metis
done
(* FIXME
apply (auto simp: black_def grey_def WL_def split: obj_at_splits)
apply metis+
done
*)

lemma no_black_refs_alloc[simp]:
  "\<lbrakk> heap (s sys) r' = None; no_black_refs s \<rbrakk>
     \<Longrightarrow> no_black_refs (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty, obj_payload = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> fl \<noteq> sys_fM s \<or> grey r' s"
unfolding no_black_refs_def by simp

lemma no_black_refs_mo_co_mark[simp]:
  "\<lbrakk> ghost_honorary_grey (s p) = {}; white r s \<rbrakk>
     \<Longrightarrow> no_black_refs (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>)) \<longleftrightarrow> no_black_refs s"
unfolding no_black_refs_def by auto

lemma grey_protects_white_mark[simp]:
  assumes ghg: "ghost_honorary_grey (s p) = {}"
  shows "(\<exists>g. (g grey_protects_white w) (s(p := s p\<lparr> ghost_honorary_grey := {r} \<rparr>)))
      \<longleftrightarrow> (\<exists>g'. (g' grey_protects_white w) s) \<or> (r has_white_path_to w) s" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain g where "(g grey_protects_white w) (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>))" by blast
  from this ghg show ?rhs by induct (auto simp: fun_upd_apply)
next
  assume ?rhs then show ?lhs
  proof(safe)
    fix g assume "(g grey_protects_white w) s"
    from this ghg show ?thesis
apply induct
 apply force
unfolding grey_protects_white_def
apply (auto simp: fun_upd_apply)
done
  next
    assume "(r has_white_path_to w) s" with ghg show ?thesis
      unfolding grey_protects_white_def has_white_path_to_def by (auto simp: fun_upd_apply)
  qed
qed

lemma valid_refs_inv_dequeue_Mutate:
  fixes s :: "('field, 'mut, 'payload, 'ref) lsts"
  assumes vri: "valid_refs_inv s"
  assumes sb: "sys_mem_store_buffers (mutator m') s = mw_Mutate r f opt_r' # ws"
  shows "valid_refs_inv (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                        mem_store_buffers := (mem_store_buffers (s sys))(mutator m' := ws)\<rparr>))" (is "valid_refs_inv ?s'")
proof(rule valid_refs_invI)
  fix m
  let ?root = "\<lambda>m x. mut_m.root m x \<^bold>\<or> grey x"
  fix x y assume xy: "(x reaches y) ?s'" and x: "?root m x ?s'"
  from xy have "(\<exists>m x. ?root m x s \<and> (x reaches y) s) \<and> valid_ref y ?s'"
  unfolding reaches_def proof induct
    case base with x sb vri show ?case
      apply -
      apply (subst obj_at_fun_upd)
       apply (auto simp: mut_m.tso_store_refs_def reaches_def fun_upd_apply split: if_splits intro: valid_refs_invD(5)[where m=m])
      apply (metis list.set_intros(2) rtranclp.rtrancl_refl)
      done (* FIXME rules *)
  next
    case (step y z)
    with sb vri show ?case
      apply -
      apply (subst obj_at_fun_upd, clarsimp simp: fun_upd_apply)
      apply (subst (asm) obj_at_fun_upd, fastforce simp: fun_upd_apply)
      apply (clarsimp simp: points_to_Mutate fun_upd_apply)
      apply (fastforce elim: rtranclp.intros(2) simp: mut_m.tso_store_refs_def reaches_def fun_upd_apply intro: exI[where x=m'] valid_refs_invD(5)[where m=m'])
      done
   qed
  then show "valid_ref y ?s'" by blast
qed

lemma valid_refs_inv_dequeue_Mutate_Payload:
  notes if_split_asm[split del]
  fixes s :: "('field, 'mut, 'payload, 'ref) lsts"
  assumes vri: "valid_refs_inv s"
  assumes sb: "sys_mem_store_buffers (mutator m') s = mw_Mutate_Payload r f pl # ws"
  shows "valid_refs_inv (s(sys := s sys\<lparr>heap := (sys_heap s)(r := map_option (\<lambda>obj. obj\<lparr>obj_payload := (obj_payload obj)(f := pl)\<rparr>) (sys_heap s r)),
                                        mem_store_buffers := (mem_store_buffers (s sys))(mutator m := ws)\<rparr>))" (is "valid_refs_inv ?s'")
apply (rule valid_refs_invI)
using assms
apply (clarsimp simp: valid_refs_invD fun_upd_apply split: obj_at_splits mem_store_action.splits)
apply auto
 apply (metis (mono_tags, lifting) UN_insert Un_iff list.simps(15) mut_m.tso_store_refs_def valid_refs_invD(4))
apply (metis case_optionE obj_at_def valid_refs_invD(7))
done

(*<*)

end
(*>*)
