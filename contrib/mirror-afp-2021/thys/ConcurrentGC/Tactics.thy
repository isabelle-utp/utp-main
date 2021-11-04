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

theory Tactics
imports
  Proofs_Basis
begin

(*>*)
section\<open> CIMP specialisation \label{sec:cimp-specialisation} \<close>

subsection\<open> Hoare triples \<close>

text\<open>

Specialise CIMP's pre/post validity to our system.

\<close>

definition
  valid_proc :: "('field, 'mut, 'payload, 'ref) gc_pred \<Rightarrow> 'mut process_name \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_pred \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace> = (\<forall>(c, afts) \<in> vcg_fragments (gc_coms p). gc_coms, p, afts \<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>)"

abbreviation
  valid_proc_inv_syn :: "('field, 'mut, 'payload, 'ref) gc_pred \<Rightarrow> 'mut process_name \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _" [100,0] 100)
where
  "\<lbrace>P\<rbrace> p \<equiv> \<lbrace>P\<rbrace> p \<lbrace>P\<rbrace>"

lemma valid_pre:
  assumes "\<lbrace>Q\<rbrace> p \<lbrace>R\<rbrace>"
  assumes "\<And>s. P s \<Longrightarrow> Q s"
  shows "\<lbrace>P\<rbrace> p \<lbrace>R\<rbrace>"
using assms
apply (clarsimp simp: valid_proc_def)
apply (drule (1) bspec)
apply (auto elim: vcg_pre)
done

lemma valid_conj_lift:
  assumes x: "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> p \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>P \<^bold>\<and> P'\<rbrace> p \<lbrace>Q \<^bold>\<and> Q'\<rbrace>"
apply (clarsimp simp: valid_proc_def)
apply (rule vcg_conj)
 apply (rule vcg_pre[OF spec[OF spec[OF x[unfolded Ball_def valid_proc_def split_paired_All]], simplified, rule_format]], simp, simp)
apply (rule vcg_pre[OF spec[OF spec[OF y[unfolded Ball_def valid_proc_def split_paired_All]], simplified, rule_format]], simp, simp)
done

lemma valid_all_lift:
  assumes "\<And>x. \<lbrace>P x\<rbrace> p \<lbrace>Q x\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> p \<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace>"
using assms by (fastforce simp: valid_proc_def intro: vcg_all_lift)


subsection\<open> Tactics \<close>

subsubsection\<open> Model-specific \<close>

text\<open>

The following is unfortunately overspecialised to the GC. One might
hope for general tactics that work on all CIMP programs.

The system responds to all requests. The schematic variable is
instantiated with the semantics of the responses. Thanks to Thomas
Sewell for the hackery.

\<close>

schematic_goal system_responds_actionE:
  "\<lbrakk> (\<lbrace>l\<rbrace> Response action, afts) \<in> fragments (gc_coms p) {}; v \<in> action x s;
     \<lbrakk> p = sys; ?P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
apply (cases p)
apply (simp_all add: all_com_interned_defs)
apply atomize

apply (drule_tac P="x \<or> y" and Q="v \<in> action p k" for x y p k in conjI, assumption)
apply (thin_tac "v \<in> action p k" for p k)
apply (simp only: conj_disj_distribR conj_assoc mem_Collect_eq cong: conj_cong)

apply (erule mp)
apply (thin_tac "p = sys")
apply (assumption)
done

schematic_goal system_responds_action_caseE:
  "\<lbrakk> (\<lbrace>l\<rbrace> Response action, afts) \<in> fragments (gc_coms p) {}; v \<in> action (pname, req) s;
     \<lbrakk> p = sys; case_request_op ?P1 ?P2 ?P3 ?P4 ?P5 ?P6 ?P7 ?P8 ?P9 ?P10 ?P11 ?P12 ?P13 ?P14 req \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
apply (erule(1) system_responds_actionE)
apply (cases req; simp only: request_op.simps prod.inject simp_thms fst_conv snd_conv if_cancel empty_def[symmetric] empty_iff)
apply (drule meta_mp[OF _ TrueI], erule meta_mp, erule_tac P="A \<and> B" for A B in triv)+
done

schematic_goal system_responds_action_specE:
  "\<lbrakk> (\<lbrace>l\<rbrace> Response action, afts) \<in> fragments (gc_coms p) {}; v \<in> action x s;
     \<lbrakk> p = sys; case_request_op ?P1 ?P2 ?P3 ?P4 ?P5 ?P6 ?P7 ?P8 ?P9 ?P10 ?P11 ?P12 ?P13 ?P14 (snd x) \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
apply (erule system_responds_action_caseE[where pname="fst x" and req="snd x"])
 apply simp
apply assumption
done


subsubsection \<open> Locations\<close>

(* FIXME not automation friendly but used in some non-interference proofs *)
lemma atS_dests:
  "\<lbrakk> atS p ls s; atS p ls' s \<rbrakk> \<Longrightarrow> atS p (ls \<union> ls') s"
  "\<lbrakk> \<not>atS p ls s; \<not>atS p ls' s \<rbrakk> \<Longrightarrow> \<not>atS p (ls \<union> ls') s"
  "\<lbrakk> \<not>atS p ls s; atS p ls' s \<rbrakk> \<Longrightarrow> atS p (ls' - ls) s"
  "\<lbrakk> \<not>atS p ls s; at p l s \<rbrakk> \<Longrightarrow> atS p ({l} - ls) s"
by (auto simp: atS_def)

lemma schematic_prem: "\<lbrakk>Q \<Longrightarrow> P; Q\<rbrakk> \<Longrightarrow> P"
by blast

(* One way of instantiating a schematic prem. *)
lemma TrueE: "\<lbrakk>True; P\<rbrakk> \<Longrightarrow> P"
by blast

lemma thin_locs_pre_discardE:
  "\<lbrakk>at p l' s \<longrightarrow> P; at p l s; l' \<noteq> l; Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>atS p ls s \<longrightarrow> P; at p l s; l \<notin> ls; Q\<rbrakk> \<Longrightarrow> Q"
unfolding atS_def by blast+

lemma thin_locs_pre_keep_atE:
  "\<lbrakk>at p l s \<longrightarrow> P; at p l s; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by blast

lemma thin_locs_pre_keep_atSE:
  "\<lbrakk>atS p ls s \<longrightarrow> P; at p l s; l \<in> ls; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding atS_def by blast

(* FIXME complete with symmetric rules on process names -- but probably not needed here *)
lemma thin_locs_post_discardE:
  "\<lbrakk>AT s' = (AT s)(p := lfn, q := lfn'); l' \<notin> lfn; p \<noteq> q\<rbrakk> \<Longrightarrow> at p l' s' \<longrightarrow> P"
  "\<lbrakk>AT s' = (AT s)(p := lfn); l' \<notin> lfn\<rbrakk> \<Longrightarrow> at p l' s' \<longrightarrow> P"
  "\<lbrakk>AT s' = (AT s)(p := lfn, q := lfn'); \<And>l. l \<in> lfn \<Longrightarrow> l \<notin> ls;  p \<noteq> q\<rbrakk> \<Longrightarrow> atS p ls s' \<longrightarrow> P"
  "\<lbrakk>AT s' = (AT s)(p := lfn); \<And>l. l \<in> lfn \<Longrightarrow> l \<notin> ls\<rbrakk> \<Longrightarrow> atS p ls s' \<longrightarrow> P"
unfolding atS_def by (auto simp: fun_upd_apply)

lemmas thin_locs_post_discard_conjE =
  conjI[OF thin_locs_post_discardE(1)]
  conjI[OF thin_locs_post_discardE(2)]
  conjI[OF thin_locs_post_discardE(3)]
  conjI[OF thin_locs_post_discardE(4)]

lemma thin_locs_post_keep_locsE:
  "\<lbrakk>(L \<longrightarrow> P) \<and> R; R \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> (L \<longrightarrow> P) \<and> Q"
  "L \<longrightarrow> P \<Longrightarrow> L \<longrightarrow> P"
by blast+

lemma thin_locs_post_keepE:
  "\<lbrakk>P \<and> R; R \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> (L \<longrightarrow> P) \<and> Q"
  "P \<Longrightarrow> L \<longrightarrow> P"
by blast+

(* FIXME checking the fun_upds are irrelevant is not necessary, but ensures the keep rule applies. *)
(* FIXME consider atS (mutator m) mut_hs_get_roots_loop_locs s' -- same again but replace at proc l s' with atS proc ls s' *)
(* FIXME in general we'd need to consider intersections *)
lemma ni_thin_locs_discardE:
  "\<lbrakk>at proc l s \<longrightarrow> P; AT s' = (AT s)(p := lfn, q := lfn'); at proc l' s'; l \<noteq> l'; proc \<noteq> p; proc \<noteq> q; Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>at proc l s \<longrightarrow> P; AT s' = (AT s)(p := lfn); at proc l' s'; l \<noteq> l'; proc \<noteq> p; Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn, q := lfn'); at proc l' s'; l' \<notin> ls; proc \<noteq> p; proc \<noteq> q; Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn); at proc l' s'; l' \<notin> ls; proc \<noteq> p; Q\<rbrakk> \<Longrightarrow> Q"

  "\<lbrakk>at proc l s \<longrightarrow> P; AT s' = (AT s)(p := lfn, q := lfn'); atS proc ls' s'; l \<notin> ls'; proc \<noteq> p; proc \<noteq> q; Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>at proc l s \<longrightarrow> P; AT s' = (AT s)(p := lfn); atS proc ls' s'; l \<notin> ls'; proc \<noteq> p; Q\<rbrakk> \<Longrightarrow> Q"
(*
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn, q := lfn'); atS proc l s'; l \<notin> ls; proc \<noteq> p; proc \<noteq> q; Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn); atS proc ls' s'; l \<notin> ls; proc \<noteq> p; Q\<rbrakk> \<Longrightarrow> Q"
*)
unfolding atS_def by auto

lemma ni_thin_locs_keep_atE:
  "\<lbrakk>at proc l s \<longrightarrow> P; AT s' = (AT s)(p := lfn, q := lfn'); at proc l s'; proc \<noteq> p; proc \<noteq> q; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>at proc l s \<longrightarrow> P; AT s' = (AT s)(p := lfn); at proc l s'; proc \<noteq> p; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (auto simp: fun_upd_apply)

lemma ni_thin_locs_keep_atSE:
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn, q := lfn'); at proc l' s'; l' \<in> ls; proc \<noteq> p; proc \<noteq> q; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn); at proc l' s'; l' \<in> ls; proc \<noteq> p; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn, q := lfn'); atS proc ls' s'; ls' \<subseteq> ls; proc \<noteq> p; proc \<noteq> q; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk>atS proc ls s \<longrightarrow> P; AT s' = (AT s)(p := lfn); atS proc ls' s'; ls' \<subseteq> ls; proc \<noteq> p; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding atS_def by (auto simp: fun_upd_apply)

lemma loc_mem_tac_intros:
  "\<lbrakk>c \<notin> A; c \<notin> B\<rbrakk> \<Longrightarrow> c \<notin> A \<union> B"
  "c \<noteq> d \<Longrightarrow> c \<notin> {d}"
  "c \<notin> A \<Longrightarrow> c \<in> - A"
  "c \<in> A \<Longrightarrow> c \<notin> - A"
  "A \<subseteq> A"
by blast+

(* FIXME these rules are dangerous if any other sets are lying around. Specialise the types? *)
lemmas loc_mem_tac_elims =
  singletonE
  UnE

lemmas loc_mem_tac_simps =
  append.simps list.simps rev.simps \<comment> \<open>evaluate string equality\<close>
  char.inject cong_exp_iff_simps \<comment> \<open>evaluate character equality\<close>
  prefix_code suffix_to_prefix
  simp_thms
  Eq_FalseI
  not_Cons_self

lemmas vcg_fragments'_simps =
  valid_proc_def gc_coms.simps vcg_fragments'.simps atC.simps
  ball_Un bool_simps if_False if_True

lemmas vcg_sem_simps =
  lconst.simps
  simp_thms
  True_implies_equals
  prod.simps fst_conv snd_conv
  gc_phase.simps process_name.simps hs_type.simps hs_phase.simps
  mem_store_action.simps mem_load_action.simps request_op.simps response.simps

lemmas vcg_inv_simps =
  simp_thms

ML \<open>

signature GC_VCG =
sig
  (* Internals *)
  val nuke_schematic_prems : Proof.context -> int -> tactic
  val loc_mem_tac : Proof.context -> int -> tactic
  val vcg_fragments_tac : Proof.context -> int -> tactic
  val vcg_sem_tac : Proof.context -> int -> tactic
  val thin_pre_inv_tac : Proof.context -> int -> tactic
  val thin_post_inv_tac : bool -> Proof.context -> int -> tactic
  val vcg_inv_tac : bool -> bool -> Proof.context -> int -> tactic
  (* End-user tactics *)
  val vcg_jackhammer_tac : bool -> bool -> Proof.context -> int -> tactic
  val vcg_chainsaw_tac : bool -> thm list -> Proof.context -> int -> tactic
  val vcg_name_cases_tac : term list -> thm list -> context_tactic
end

structure GC_VCG : GC_VCG =
struct

(* Identify and remove schematic premises. FIXME reverses the prems *)
fun nuke_schematic_prems ctxt =
  let
    fun is_schematic_prem t =
      case t of
        Const ("HOL.Trueprop", _) $ t => is_schematic_prem t
      | t $ _ => is_schematic_prem t
      | Var _ => true
      | _ => false
  in
    DETERM o filter_prems_tac ctxt (not o is_schematic_prem)
  end;

(* FIXME Want to unify only with a non-schematic prem. might get there with first order matching or some existing variant of assume. *)
fun assume_non_schematic_prem_tac ctxt =
  (TRY o nuke_schematic_prems ctxt) THEN' assume_tac ctxt

fun vcg_fragments_tac ctxt =
  SELECT_GOAL (HEADGOAL (safe_simp_tac (ss_only (@{thms vcg_fragments'_simps} @ @{thms all_com_interned_defs}) ctxt)
                  THEN' SELECT_GOAL (safe_tac ctxt))); (* FIXME split the goal, simplify the sets away. FIXME try to nuke safe_tac *)

fun vcg_sem_tac ctxt =
  SELECT_GOAL (HEADGOAL (match_tac ctxt @{thms CIMP_vcg.vcg.intros}
                  THEN' (TRY o (ematch_tac ctxt @{thms system_responds_action_specE} THEN' assume_tac ctxt))
                  THEN' Rule_Insts.thin_tac ctxt "HST s = h" [(@{binding s}, NONE, NoSyn), (@{binding h}, NONE, NoSyn)] (* discard history: we don't use it here *)
                  THEN' clarsimp_tac (ss_only @{thms vcg_sem_simps} ctxt)
           THEN_ALL_NEW asm_simp_tac ctxt)); (* remove unused meta-bound vars FIXME subgoaler in HOL's usual simplifier setup, somehow lost by ss_only *)

(* FIXME gingerly settle location set membership and (dis-)equalities *)
fun loc_mem_tac ctxt =
  let
    val loc_defs = Proof_Context.get_fact ctxt (Facts.named "loc_defs")
  in
    SELECT_GOAL (HEADGOAL ( (TRY o REPEAT_ALL_NEW (ematch_tac ctxt @{thms loc_mem_tac_elims}))
               THEN_ALL_NEW (TRY o hyp_subst_tac ctxt)
               THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (match_tac ctxt @{thms loc_mem_tac_intros}))
               THEN_ALL_NEW ( SOLVED' (match_tac ctxt (Named_Theorems.get ctxt \<^named_theorems>\<open>locset_cache\<close>)
                               ORELSE' safe_simp_tac (HOL_ss_only (@{thms loc_mem_tac_simps} @ loc_defs) ctxt) ) )))
  end;

fun thin_pre_inv_tac ctxt =
    SELECT_GOAL (HEADGOAL ( (* FIXME trying to scope the REPEAT_DETERM ala [1] *)
            (REPEAT_DETERM o ematch_tac ctxt @{thms conjE})
      THEN' (REPEAT_DETERM o ( (ematch_tac ctxt @{thms thin_locs_pre_discardE}  THEN' assume_tac ctxt THEN' loc_mem_tac ctxt)
                       ORELSE' (ematch_tac ctxt @{thms thin_locs_pre_keep_atE}  THEN' assume_tac ctxt)
                       ORELSE' (ematch_tac ctxt @{thms thin_locs_pre_keep_atSE} THEN' assume_tac ctxt THEN' loc_mem_tac ctxt) ))));

(* FIXME redo keep_postE: if at loc is provable, discard the at antecedent, otherwise keep it *)
(* if the post inv is an LSTP then the present fix is to say (no_thin_post_inv) -- would be good to automate that *)
fun thin_post_inv_tac keep_locs ctxt =
  let
    val keep_postE_thms = if keep_locs then @{thms thin_locs_post_keep_locsE} else @{thms thin_locs_post_keepE}
    fun nail_discard_prems_tac ctxt = assume_non_schematic_prem_tac ctxt THEN' loc_mem_tac ctxt THEN' (TRY o match_tac ctxt @{thms process_name.simps})
  in
    SELECT_GOAL (HEADGOAL ( (* FIXME trying to scope the REPEAT_DETERM ala [1] *)
            resolve_tac ctxt @{thms schematic_prem}
      THEN' REPEAT_DETERM o CHANGED o (* FIXME CHANGED? also check what happens for non-invL post invs -- aim to fail the ^^^ resolve_tac too *)
              ( (                                      match_tac ctxt @{thms thin_locs_post_discard_conjE} THEN' nail_discard_prems_tac ctxt)
        ORELSE' (eresolve_tac ctxt @{thms TrueE} THEN' match_tac ctxt @{thms thin_locs_post_discardE}      THEN' nail_discard_prems_tac ctxt)
        ORELSE' eresolve_tac ctxt keep_postE_thms )
  ))
  end;

fun vcg_inv_tac keep_locs no_thin_post_inv ctxt =
  let
    val invs = Named_Theorems.get ctxt \<^named_theorems>\<open>inv\<close>
  in
          SELECT_GOAL (Local_Defs.unfold_tac ctxt invs) (* FIXME trying to say unfold in [1] only *)
    THEN' thin_pre_inv_tac ctxt
    THEN' ( if no_thin_post_inv
            then SELECT_GOAL all_tac (* full_simp_tac (ss_only @{thms vcg_inv_simps} ctxt) (* FIXME maybe not? *) *)
            else full_simp_tac (Splitter.add_split @{thm lcond_split_asm} (ss_only @{thms vcg_inv_simps} ctxt))
    THEN_ALL_NEW thin_post_inv_tac keep_locs ctxt )
  end;

(* For showing local invariants. FIXME tack on (no_thin_post_inv) for universal/LSTP ones *)
fun vcg_jackhammer_tac keep_locs no_thin_post_inv ctxt =
    SELECT_GOAL (HEADGOAL (vcg_fragments_tac ctxt)
    THEN PARALLEL_ALLGOALS (
                   vcg_sem_tac ctxt
      THEN_ALL_NEW vcg_inv_tac keep_locs no_thin_post_inv ctxt
      THEN_ALL_NEW (if keep_locs then SELECT_GOAL all_tac else Rule_Insts.thin_tac ctxt "AT _ = _" [])
      THEN_ALL_NEW TRY o clarsimp_tac ctxt (* limply try to solve the remaining goals *)
    ));

(* For showing noninterference *)
fun vcg_chainsaw_tac no_thin unfold_foreign_inv_thms ctxt =
  let
    fun specialize_foreign_invs_tac ctxt =
                   (* FIXME split goal: makes sense because local procs control locs have changed? *)
                       REPEAT_ALL_NEW (match_tac ctxt @{thms conjI})
          THEN_ALL_NEW TRY o ( match_tac ctxt @{thms impI} (* FIXME could tweak rules vvvv *)
                          (* thin out the invariant we're showing non-interference for *)
(* FIXME look for reasons to retain the invariant, then do a big thin_tac at the end.
Intuitively we don't have enough info to settle atS v atS questions and it's too hard/not informative enough to try.
Let the user do it.
Maybe add an info thing that tells what was thinned.

FIXME location-sensitive predicates are not amenable to
simplification: this is the cost of using projections on
pred_state. Instead use elimination rules \<open>nie\<close>.

 *)
                         THEN' ( REPEAT_DETERM o ( ( ematch_tac ctxt @{thms ni_thin_locs_discardE}  THEN' assume_tac ctxt THEN' assume_tac ctxt THEN' loc_mem_tac ctxt THEN' match_tac ctxt @{thms process_name.simps} THEN' TRY o match_tac ctxt @{thms process_name.simps} )
                                           ORELSE' ( ematch_tac ctxt @{thms ni_thin_locs_keep_atE}  THEN' assume_tac ctxt THEN' assume_tac ctxt THEN' match_tac ctxt @{thms process_name.simps} THEN' TRY o match_tac ctxt @{thms process_name.simps} )
                                           ORELSE' ( ematch_tac ctxt @{thms ni_thin_locs_keep_atSE} THEN' assume_tac ctxt THEN' assume_tac ctxt THEN' loc_mem_tac ctxt THEN' match_tac ctxt @{thms process_name.simps} THEN' TRY o match_tac ctxt @{thms process_name.simps} ) ) ) )
  in
    SELECT_GOAL (HEADGOAL (vcg_fragments_tac ctxt)
    THEN PARALLEL_ALLGOALS (
                   vcg_sem_tac ctxt
                   (* nail cheaply with an nie fact + ambient clarsimp *)
      THEN_ALL_NEW ( SOLVED' (ematch_tac ctxt (Named_Theorems.get ctxt @{named_theorems nie}) THEN_ALL_NEW clarsimp_tac ctxt)
             ORELSE' ( (* do it the hard way: specialise any process-specific invariants. Similar to vcg_jackhammer but not the same *)
                       vcg_inv_tac false true ctxt
                       (* unfold the foreign inv *)
                 THEN' SELECT_GOAL (Local_Defs.unfold_tac ctxt unfold_foreign_inv_thms) (* FIXME trying to say [1] *)
                 THEN' (REPEAT_DETERM o ematch_tac ctxt @{thms conjE})
                 THEN' specialize_foreign_invs_tac ctxt
                       (* limply try to solve the remaining goals; FIXME turn s' into s as much as easily possible *)
          THEN_ALL_NEW (TRY o clarsimp_tac ctxt)
                       (* FIXME discard loc info. It is useful, this is a stopgap *)
          THEN_ALL_NEW (if no_thin then SELECT_GOAL all_tac
                        else (Rule_Insts.thin_tac ctxt "AT _ = _" []
                THEN_ALL_NEW (REPEAT_DETERM o Rule_Insts.thin_tac ctxt "at _ _ _ \<longrightarrow> _" [])
                THEN_ALL_NEW (REPEAT_DETERM o Rule_Insts.thin_tac ctxt "atS _ _ _ \<longrightarrow> _" []) ))
    ))))
  end;

(*

Scrutinise the goal state for an `AT` fact that tells us which label the process is at.

It seems this is not kosher:
 - for reasons unknown (Eisbach?) this tactic gets called with a bogus "TERM _" and then the real goal state.
 - this tactic (sometimes) does not work if used with THEN_ALL_NEW ';' --
   chk_label does not manage to uniquify labels -- so be sure to
   combine with ','.
 - if two goals have the same `at` location then we disambiguate, but
   perhaps not stably. Could imagine creating subcases, but
   `Method.goal_cases_tac` is not yet capable of that.
 - at communication steps we could get unlucky and choose the label from the other process.

The user can supply a list of process names to somewhat address these issues.

See Pure/Tools/rule_insts.ML for structurally similar tactics ("dynamic instantiation").

Limitations:
 - only works with `Const` labels
 - brittle: assumes things are very well-formed

*)
fun vcg_name_cases_tac (proc_names: term list) _(*facts*) (ctxt, st) =
  if Thm.nprems_of st = 0
  then Seq.empty (* no_tac *)
  else
    let
      fun fst_ord ord ((x, _), (x', _)) = ord (x, x')
      fun snd_ord ord ((_, y), (_, y')) = ord (y, y')

      (* FIXME this search is drecky *)
      fun find_AT (t: term) : (term * string) option =
            ( (* tracing ("scruting: " ^ Syntax.string_of_term ctxt t) ; *)
              case t of Const ("HOL.Trueprop", _) $ (Const (@{const_name "Set.member"}, _) $ Const (l, _) $ (Const (@{const_name "CIMP_lang.AT"},  _) $ _ $ p)) => ((* tracing "HIT"; *) SOME (p, Long_Name.base_name l))
                      | Const ("HOL.Trueprop", _) $ (Const (@{const_name "CIMP_lang.atS"}, _) $ p $ Const (ls, _) $ _) => ((* tracing "HIT"; *) SOME (p, Long_Name.base_name ls))
                      | _ => NONE )

      (* FIXME Isabelle makes it awkward to use polymorphic process names; paper over that crack here *)
      val rec terms_eq_ignoring_types =
          fn (Const (c0, _), Const (c1, _)) => fast_string_ord (c0, c1) = EQUAL
           | (Free (f0, _),  Free (f1, _))  => fast_string_ord (f0, f1) = EQUAL
           | (Var (v0, _) , Var (v1, _)) => prod_ord fast_string_ord int_ord (v0, v1) = EQUAL
           | (Bound i0, Bound i1) => i0 = i1
           | (Abs (b0, _, t0), Abs (b1, _, t1)) => fast_string_ord (b0, b1) = EQUAL andalso terms_eq_ignoring_types (t0, t1)
           | (t0 $ u0, t1 $ u1) => terms_eq_ignoring_types (t0, t1) andalso terms_eq_ignoring_types (u0, u1)
           | _ => false

      fun mk_label (default: string) (ats : (term * string) list) : string =
            case (ats, proc_names) of
              ((_, l)::_, []) => ((* tracing ("No proc_names, Using label: " ^ l); *) l)
            | _ =>
              let
                val ls = List.mapPartial (fn p => List.find (fn (p', _) => terms_eq_ignoring_types (p, p')) ats) proc_names
              in
                case ls of
                  [] => (warning ("vcg_name_cases: using the default name: " ^ default); default)
                | _  => ls |> List.map snd |> String.concatWith "_"
              end

      fun labels_for_cases (i: int) (acc: (int * string) list) : (int * string) list =
            case i of
              0 => acc
            | i => Thm.cprem_of st i |> Thm.term_of |> Logic.strip_assums_hyp
                   |> List.mapPartial find_AT |> mk_label (Int.toString i)
                   |> (fn l => labels_for_cases (i - 1) ((i, l) :: acc))

        (* Make the labels unique if need be *)
      fun uniquify (i: int) (ls: (int * string) list) : (int * string) list =
        case ls of
          [] => []
        | [l] => [l]
        | l :: l' :: ls => (case fast_string_ord (snd l, snd l') of
                             EQUAL => (fst l, snd l ^ Int.toString i) :: uniquify (i + 1) (l' :: ls)
                           | _     => l :: uniquify 0 (l' :: ls))
      val labels = labels_for_cases (Thm.nprems_of st) []
      val labels = labels
                |> sort (snd_ord fast_string_ord) |> uniquify 0 |> sort (fst_ord int_ord)
                |> List.map (fn (_, l) => ((* tracing ("label: " ^ l); *) l))
    in
      Method.goal_cases_tac labels (ctxt, st)
    end;

end

val _ =
  Theory.setup (Method.setup @{binding loc_mem}
    (Scan.succeed (SIMPLE_METHOD' o GC_VCG.loc_mem_tac))
    "solve location membership goals")

val _ =
  Theory.setup (Method.setup @{binding vcg_fragments}
    (Scan.succeed (SIMPLE_METHOD' o GC_VCG.vcg_fragments_tac))
    "unfold com defs, execute vcg_fragments' and split goals")

val _ =
  Theory.setup (Method.setup @{binding vcg_sem}
    (Scan.succeed (SIMPLE_METHOD' o GC_VCG.vcg_sem_tac))
    "reduce VCG goal to semantics and clarsimp")

val _ =
  Theory.setup (Method.setup @{binding vcg_inv}
    (Scan.lift (Args.mode "keep_locs" -- Args.mode "no_thin_post_inv") >> (fn (keep_locs, no_thin_post_inv) => SIMPLE_METHOD' o GC_VCG.vcg_inv_tac keep_locs no_thin_post_inv))
    "specialise the invariants to the goal. (keep_locs) retains locs in post conds")

val _ =
  Theory.setup (Method.setup @{binding vcg_jackhammer}
    (Scan.lift (Args.mode "keep_locs" -- Args.mode "no_thin_post_inv") >> (fn (keep_locs, no_thin_post_inv) => SIMPLE_METHOD' o GC_VCG.vcg_jackhammer_tac keep_locs no_thin_post_inv))
    "VCG tactic. (keep_locs) retains locs in post conds. (no_thin_post_inv) does not attempt to specalise the post condition.")

val _ =
  Theory.setup (Method.setup @{binding vcg_chainsaw}
    (Scan.lift (Args.mode "no_thin") -- Attrib.thms >> (fn (no_thin, thms) => SIMPLE_METHOD' o GC_VCG.vcg_chainsaw_tac no_thin thms))
    "VCG non-interference tactic. Tell it how to unfold the foreign local invs.")

val _ =
  Theory.setup (Method.setup @{binding vcg_name_cases}
    (Scan.repeat Args.term >> (fn proc_names => fn _ => CONTEXT_METHOD (GC_VCG.vcg_name_cases_tac proc_names)))
    "divine canonical case names for outstanding VCG goals")

\<close>
(*<*)

end
(*>*)
