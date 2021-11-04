section \<open>Soundness theorem for the STRIPS semantics\<close>
text \<open>We prove the soundness theorem according to ~\cite{lifschitz1987semantics}.\<close>

theory Lifschitz_Consistency
imports PDDL_STRIPS_Semantics
begin


text \<open>States are modeled as valuations of our underlying predicate logic.\<close>
type_synonym state = "(predicate\<times>object list) valuation"

context ast_domain begin
  text \<open>An action is a partial function from states to states. \<close>
  type_synonym action = "state \<rightharpoonup> state"

  text \<open>The Isabelle/HOL formula @{prop \<open>f s = Some s'\<close>} means
    that \<open>f\<close> is applicable in state \<open>s\<close>, and the result is \<open>s'\<close>. \<close>

  text \<open>Definition B (i)--(iv) in Lifschitz's paper~\cite{lifschitz1987semantics}\<close>

  fun is_NegPredAtom where
    "is_NegPredAtom (Not x) = is_predAtom x" | "is_NegPredAtom _ = False"

  definition "close_eq s = (\<lambda>predAtm p xs \<Rightarrow> s (p,xs) | Eq a b \<Rightarrow> a=b)"

  lemma close_eq_predAtm[simp]: "close_eq s (predAtm p xs) \<longleftrightarrow> s (p,xs)"
    by (auto simp: close_eq_def)                    

  lemma close_eq_Eq[simp]: "close_eq s (Eq a b) \<longleftrightarrow> a=b"
    by (auto simp: close_eq_def)


  abbreviation entail_eq :: "state \<Rightarrow> object atom formula \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>=" 55)
    where "entail_eq s f \<equiv> close_eq s \<Turnstile> f"


  fun sound_opr :: "ground_action \<Rightarrow> action \<Rightarrow> bool" where
    "sound_opr (Ground_Action pre (Effect add del)) f \<longleftrightarrow>
      (\<forall>s. s \<Turnstile>\<^sub>= pre \<longrightarrow>
        (\<exists>s'. f s = Some s' \<and> (\<forall>atm. is_predAtom atm \<and> atm \<notin> set del \<and> s \<Turnstile>\<^sub>= atm \<longrightarrow> s' \<Turnstile>\<^sub>= atm)
              \<and>  (\<forall>atm. is_predAtom atm \<and> atm \<notin> set add \<and> s \<Turnstile>\<^sub>= Not atm \<longrightarrow> s' \<Turnstile>\<^sub>= Not atm)
              \<and> (\<forall>fmla. fmla \<in> set add \<longrightarrow> s' \<Turnstile>\<^sub>= fmla)
              \<and> (\<forall>fmla. fmla \<in> set del \<and> fmla \<notin> set add \<longrightarrow> s' \<Turnstile>\<^sub>= (Not fmla))
              ))
        \<and> (\<forall>fmla\<in>set add. is_predAtom fmla)"

  lemma sound_opr_alt:
    "sound_opr opr f =
      ((\<forall>s. s \<Turnstile>\<^sub>= (precondition opr) \<longrightarrow>
          (\<exists>s'. f s = (Some s')
                \<and> (\<forall>atm. is_predAtom atm \<and> atm \<notin> set(dels (effect opr)) \<and> s \<Turnstile>\<^sub>= atm \<longrightarrow> s' \<Turnstile>\<^sub>= atm)
                \<and> (\<forall>atm. is_predAtom atm \<and> atm \<notin> set (adds (effect opr)) \<and> s \<Turnstile>\<^sub>= Not atm \<longrightarrow> s' \<Turnstile>\<^sub>= Not atm)
                \<and> (\<forall>atm. atm \<in> set(adds (effect opr)) \<longrightarrow> s' \<Turnstile>\<^sub>= atm)
                \<and> (\<forall>fmla. fmla \<in> set (dels (effect opr)) \<and> fmla \<notin> set(adds (effect opr)) \<longrightarrow> s' \<Turnstile>\<^sub>= (Not fmla))
                \<and> (\<forall>a b. s \<Turnstile>\<^sub>= Atom (Eq a b) \<longrightarrow> s' \<Turnstile>\<^sub>= Atom (Eq a b))
                \<and> (\<forall>a b. s \<Turnstile>\<^sub>= Not (Atom (Eq a b)) \<longrightarrow> s' \<Turnstile>\<^sub>= Not (Atom (Eq a b)))
                ))
        \<and> (\<forall>fmla\<in>set(adds (effect opr)). is_predAtom fmla))"
    by (cases "(opr,f)" rule: sound_opr.cases) auto

  text \<open>Definition B (v)--(vii) in  Lifschitz's paper~\cite{lifschitz1987semantics}\<close>
definition sound_system
    :: "ground_action set
      \<Rightarrow> world_model
      \<Rightarrow> state
      \<Rightarrow> (ground_action \<Rightarrow> action)
      \<Rightarrow> bool"
    where
    "sound_system \<Sigma> M\<^sub>0 s\<^sub>0 f \<longleftrightarrow>
      ((\<forall>fmla\<in>close_world M\<^sub>0. s\<^sub>0  \<Turnstile>\<^sub>= fmla)
      \<and> wm_basic M\<^sub>0
      \<and> (\<forall>\<alpha>\<in>\<Sigma>. sound_opr \<alpha> (f \<alpha>)))"

  text \<open>Composing two actions\<close>
  definition compose_action :: "action \<Rightarrow> action \<Rightarrow> action" where
    "compose_action f1 f2 x = (case f2 x of Some y \<Rightarrow> f1 y | None \<Rightarrow> None)"

  text \<open>Composing a list of actions\<close>
  definition compose_actions :: "action list \<Rightarrow> action" where
    "compose_actions fs \<equiv> fold compose_action fs Some"

  text \<open>Composing a list of actions satisfies some natural lemmas: \<close>
  lemma compose_actions_Nil[simp]:
    "compose_actions [] = Some" unfolding compose_actions_def by auto

  lemma compose_actions_Cons[simp]:
    "f s = Some s' \<Longrightarrow> compose_actions (f#fs) s = compose_actions fs s'"
  proof -
    interpret monoid_add compose_action Some
      apply unfold_locales
      unfolding compose_action_def
      by (auto split: option.split)
    assume "f s = Some s'"
    then show ?thesis
      unfolding compose_actions_def
      by (simp add: compose_action_def fold_plus_sum_list_rev)
  qed

  text \<open>Soundness Theorem in Lifschitz's paper~\cite{lifschitz1987semantics}.\<close>
theorem STRIPS_sema_sound:
  assumes "sound_system \<Sigma> M\<^sub>0 s\<^sub>0 f"
    \<comment> \<open>For a sound system \<open>\<Sigma>\<close>\<close>
  assumes "set \<alpha>s \<subseteq> \<Sigma>"
    \<comment> \<open>And a plan \<open>\<alpha>s\<close>\<close>
  assumes "ground_action_path M\<^sub>0 \<alpha>s M'"
    \<comment> \<open>Which is accepted by the system, yielding result \<open>M'\<close>
          (called \<open>R(\<alpha>s)\<close> in Lifschitz's paper~\cite{lifschitz1987semantics}.)\<close>
  obtains s'
    \<comment> \<open>We have that \<open>f(\<alpha>s)\<close> is applicable
          in initial state, yielding state \<open>s'\<close> (called \<open>f\<^sub>\<alpha>\<^sub>s(s\<^sub>0)\<close> in Lifschitz's paper~\cite{lifschitz1987semantics}.)\<close>
  where "compose_actions (map f \<alpha>s) s\<^sub>0 = Some s'"
    \<comment> \<open>The result world model \<open>M'\<close> is satisfied in state \<open>s'\<close>\<close>
    and "\<forall>fmla\<in>close_world M'. s' \<Turnstile>\<^sub>= fmla"
proof -
  have "(valuation M' \<Turnstile> fmla)" if "wm_basic M'" "fmla\<in>M'" for fmla
    using that apply (induction fmla)
    by (auto simp: valuation_def wm_basic_def split: atom.split)
  have "\<exists>s'. compose_actions (map f \<alpha>s) s\<^sub>0 = Some s' \<and> (\<forall>fmla\<in>close_world M'. s' \<Turnstile>\<^sub>= fmla)"
    using assms
  proof(induction \<alpha>s arbitrary: s\<^sub>0 M\<^sub>0 )
    case Nil
    then show ?case by (auto simp add: close_world_def compose_action_def sound_system_def)
  next
    case ass: (Cons \<alpha> \<alpha>s)
    then obtain pre add del where a: "\<alpha> = Ground_Action pre (Effect add del)"
      using ground_action.exhaust ast_effect.exhaust by metis
    let ?M\<^sub>1 = "execute_ground_action \<alpha> M\<^sub>0"
    have "close_world M\<^sub>0 \<TTurnstile> precondition \<alpha>"
      using ass(4)
      by auto
    moreover have s0_ent_cwM0: "\<forall>fmla\<in>(close_world M\<^sub>0). close_eq s\<^sub>0 \<Turnstile> fmla"
      using ass(2)
      unfolding sound_system_def
      by auto
    ultimately have s0_ent_alpha_precond: "close_eq s\<^sub>0 \<Turnstile> precondition \<alpha>"
      unfolding entailment_def
      by auto
    then obtain s\<^sub>1 where s1: "(f \<alpha>) s\<^sub>0 = Some s\<^sub>1"
      "(\<forall>atm. is_predAtom atm \<longrightarrow> atm \<notin> set(dels (effect \<alpha>))
                                            \<longrightarrow> close_eq s\<^sub>0 \<Turnstile> atm
                                            \<longrightarrow> close_eq s\<^sub>1 \<Turnstile> atm)"
      "(\<forall>fmla. fmla \<in> set(adds (effect \<alpha>))
                                            \<longrightarrow> close_eq s\<^sub>1 \<Turnstile> fmla)"
      "(\<forall>atm. is_predAtom atm \<and> atm \<notin> set (adds (effect \<alpha>)) \<and> close_eq s\<^sub>0 \<Turnstile> Not atm \<longrightarrow> close_eq s\<^sub>1 \<Turnstile> Not atm)"
      "(\<forall>fmla. fmla \<in> set (dels (effect \<alpha>)) \<and> fmla \<notin> set(adds (effect \<alpha>)) \<longrightarrow> close_eq s\<^sub>1 \<Turnstile> (Not fmla))"
      "(\<forall>a b. close_eq s\<^sub>0 \<Turnstile> Atom (Eq a b) \<longrightarrow> close_eq s\<^sub>1 \<Turnstile> Atom (Eq a b))"
      "(\<forall>a b. close_eq s\<^sub>0 \<Turnstile> Not (Atom (Eq a b)) \<longrightarrow> close_eq s\<^sub>1 \<Turnstile> Not (Atom (Eq a b)))"
      using ass(2-4)
      unfolding sound_system_def sound_opr_alt by force
    have "close_eq s\<^sub>1 \<Turnstile> fmla" if "fmla\<in>close_world ?M\<^sub>1" for fmla
      using ass(2)
      using that s1 s0_ent_cwM0
      unfolding sound_system_def execute_ground_action_def wm_basic_def
      apply (auto simp: in_close_world_conv)
      subgoal
        by (metis (no_types, lifting) DiffE UnE a apply_effect.simps ground_action.sel(2) ast_effect.sel(1) ast_effect.sel(2) close_world_extensive subsetCE)
      subgoal
        by (metis Diff_iff Un_iff a ground_action.sel(2) ast_domain.apply_effect.simps ast_domain.close_eq_predAtm ast_effect.sel(1) ast_effect.sel(2) formula_semantics.simps(1) formula_semantics.simps(3) in_close_world_conv is_predAtom.simps(1))
      done
    moreover have "(\<forall>atm. fmla \<noteq> formula.Atom atm) \<longrightarrow> s \<Turnstile> fmla" if "fmla\<in>?M\<^sub>1" for fmla s
    proof-
      have alpha: "(\<forall>s.\<forall>fmla\<in>set(adds (effect \<alpha>)). \<not> is_predAtom fmla \<longrightarrow> s \<Turnstile> fmla)"
        using ass(2,3)
        unfolding sound_system_def ast_domain.sound_opr_alt
        by auto
      then show ?thesis
        using that
        unfolding a execute_ground_action_def
        using ass.prems(1)[unfolded sound_system_def]
        by(cases fmla; fastforce simp: wm_basic_def)

    qed
    moreover have "(\<forall>opr\<in>\<Sigma>. sound_opr opr (f opr))"
      using ass(2) unfolding sound_system_def
      by (auto simp add:)
    moreover have "wm_basic ?M\<^sub>1"
      using ass(2,3)
      unfolding sound_system_def execute_ground_action_def
      thm sound_opr.cases
      apply (cases "(\<alpha>,f \<alpha>)" rule: sound_opr.cases)
      apply (auto simp: wm_basic_def)
      done
    ultimately have "sound_system \<Sigma> ?M\<^sub>1 s\<^sub>1 f"
      unfolding sound_system_def
      by (auto simp: wm_basic_def)
    from ass.IH[OF this] ass.prems obtain s' where
      "compose_actions (map f \<alpha>s) s\<^sub>1 = Some s' \<and> (\<forall>a\<in>close_world M'. s' \<Turnstile>\<^sub>= a)"
      by auto
    thus ?case by (auto simp: s1(1))
  qed
  with that show ?thesis by blast
qed

  text \<open>More compact notation of the soundness theorem.\<close>
  theorem STRIPS_sema_sound_compact_version:
    "sound_system \<Sigma> M\<^sub>0 s\<^sub>0 f \<Longrightarrow> set \<alpha>s \<subseteq> \<Sigma>
    \<Longrightarrow> ground_action_path M\<^sub>0 \<alpha>s M'
    \<Longrightarrow> \<exists>s'. compose_actions (map f \<alpha>s) s\<^sub>0 = Some s'
          \<and> (\<forall>fmla\<in>close_world M'. s' \<Turnstile>\<^sub>= fmla)"
    using STRIPS_sema_sound by metis

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsection \<open>Soundness Theorem for PDDL\<close>

context wf_ast_problem begin

  text \<open>Mapping world models to states\<close>
  definition state_to_wm :: "state \<Rightarrow> world_model"
    where "state_to_wm s = ({formula.Atom (predAtm p xs) | p xs. s (p,xs)})"
  definition wm_to_state :: "world_model \<Rightarrow> state"
    where "wm_to_state M = (\<lambda>(p,xs). (formula.Atom (predAtm p xs)) \<in> M)"


  lemma wm_to_state_eq[simp]: "wm_to_state M (p, as) \<longleftrightarrow> Atom (predAtm p as) \<in> M"
    by (auto simp: wm_to_state_def)




  lemma wm_to_state_inv[simp]: "wm_to_state (state_to_wm s) = s"
    by (auto simp: wm_to_state_def
      state_to_wm_def image_def)

  text \<open>Mapping AST action instances to actions\<close>
  definition "pddl_opr_to_act g_opr s = (
    let M = state_to_wm s in
    if (wm_to_state (close_world M)) \<Turnstile>\<^sub>= (precondition g_opr) then
      Some (wm_to_state (apply_effect (effect g_opr) M))
    else
      None)"

definition "close_eq_M M = (M \<inter> {Atom (predAtm p xs) | p xs. True }) \<union> {Atom (Eq a a) | a. True} \<union> {\<^bold>\<not>(Atom (Eq a b)) | a b. a\<noteq>b}"

  lemma atom_in_wm_eq:
    "s \<Turnstile>\<^sub>= (formula.Atom atm)
      \<longleftrightarrow> ((formula.Atom atm) \<in> close_eq_M (state_to_wm s))"
    by (auto simp: wm_to_state_def
      state_to_wm_def image_def close_eq_M_def close_eq_def split: atom.splits)

lemma atom_in_wm_2_eq:
    "close_eq (wm_to_state M) \<Turnstile> (formula.Atom atm)
      \<longleftrightarrow> ((formula.Atom atm) \<in> close_eq_M M)"
    by (auto simp: wm_to_state_def
      state_to_wm_def image_def close_eq_def close_eq_M_def split:atom.splits)

  lemma not_dels_preserved:
    assumes "f \<notin> (set d)" " f \<in> M"
    shows "f \<in> apply_effect (Effect a d) M"
    using assms
    by auto

  lemma adds_satisfied:
    assumes "f \<in> (set a)"
    shows "f \<in> apply_effect (Effect a d) M"
    using assms
    by auto

  lemma dels_unsatisfied:
    assumes "f \<in> (set d)" "f \<notin> set a"
    shows "f \<notin> apply_effect (Effect a d) M"
    using assms
    by auto

  lemma dels_unsatisfied_2:
    assumes "f \<in> set (dels eff)" "f \<notin> set (adds eff)"
    shows "f \<notin> apply_effect eff M"
    using assms
    by (cases eff; auto)

  lemma wf_fmla_atm_is_atom: "wf_fmla_atom objT f \<Longrightarrow> is_predAtom f"
    by (cases f rule: wf_fmla_atom.cases) auto

  lemma wf_act_adds_are_atoms:
    assumes "wf_effect_inst effs" "ae \<in> set (adds effs)"
    shows "is_predAtom ae"
    using assms
    by (cases effs) (auto simp: wf_fmla_atom_alt)

  lemma wf_act_adds_dels_atoms:
    assumes "wf_effect_inst effs" "ae \<in> set (dels effs)"
    shows "is_predAtom ae"
    using assms
    by (cases effs) (auto simp: wf_fmla_atom_alt)

  lemma to_state_close_from_state_eq[simp]: "wm_to_state (close_world (state_to_wm s)) = s"
    by (auto simp: wm_to_state_def close_world_def
      state_to_wm_def image_def)



lemma wf_eff_pddl_ground_act_is_sound_opr:
  assumes "wf_effect_inst (effect g_opr)"
  shows "sound_opr g_opr ((pddl_opr_to_act g_opr))"
  unfolding sound_opr_alt
  apply(cases g_opr; safe)
  subgoal for pre eff s
    apply (rule exI[where x="wm_to_state(apply_effect eff (state_to_wm s))"])
    apply (auto simp: pddl_opr_to_act_def Let_def split:if_splits)
    subgoal for atm
      by (cases eff; cases atm; auto simp: close_eq_def wm_to_state_def state_to_wm_def split: atom.splits)
    subgoal for atm
      by (cases eff; cases atm; auto simp: close_eq_def wm_to_state_def state_to_wm_def split: atom.splits)
    subgoal for atm
      using assms
      by (cases eff; cases atm; force simp: close_eq_def wm_to_state_def state_to_wm_def split: atom.splits)
    subgoal for fmla
      using assms
      by (cases eff; cases fmla rule: wf_fmla_atom.cases; force simp: close_eq_def wm_to_state_def state_to_wm_def split: atom.splits)
    done
  subgoal for pre eff fmla
    using assms
    by (cases eff; cases fmla rule: wf_fmla_atom.cases; force)
  done



  lemma wf_eff_impt_wf_eff_inst: "wf_effect objT eff \<Longrightarrow> wf_effect_inst eff"
    by (cases eff; auto simp add: wf_fmla_atom_alt)

  lemma wf_pddl_ground_act_is_sound_opr:
    assumes "wf_ground_action g_opr"
    shows "sound_opr g_opr (pddl_opr_to_act g_opr)"
    using wf_eff_impt_wf_eff_inst wf_eff_pddl_ground_act_is_sound_opr assms
    by (cases g_opr; auto)

  lemma wf_action_schema_sound_inst:
    assumes "action_params_match act args" "wf_action_schema act"
    shows "sound_opr
      (instantiate_action_schema act args)
      ((pddl_opr_to_act (instantiate_action_schema act args)))"
    using
      wf_pddl_ground_act_is_sound_opr[
        OF wf_instantiate_action_schema[OF assms]]
      by blast

  lemma wf_plan_act_is_sound:
    assumes "wf_plan_action (PAction n args)"
    shows "sound_opr
      (instantiate_action_schema (the (resolve_action_schema n)) args)
      ((pddl_opr_to_act
        (instantiate_action_schema (the (resolve_action_schema n)) args)))"
    using assms
    using wf_action_schema_sound_inst wf_eff_pddl_ground_act_is_sound_opr
    by (auto split: option.splits)

  lemma wf_plan_act_is_sound':
    assumes "wf_plan_action \<pi>"
    shows "sound_opr
      (resolve_instantiate \<pi>)
      ((pddl_opr_to_act (resolve_instantiate \<pi>)))"
    using assms wf_plan_act_is_sound
    by (cases \<pi>; auto )

  lemma wf_world_model_has_atoms: "f\<in>M \<Longrightarrow> wf_world_model M \<Longrightarrow> is_predAtom f"
    using wf_fmla_atm_is_atom
    unfolding wf_world_model_def
    by auto

  lemma wm_to_state_works_for_wf_wm_closed:
    "wf_world_model M \<Longrightarrow> fmla\<in>close_world M \<Longrightarrow> close_eq (wm_to_state M) \<Turnstile> fmla"
    apply (cases fmla rule: wf_fmla_atom.cases)
    by (auto simp: wf_world_model_def close_eq_def wm_to_state_def close_world_def)

  lemma wm_to_state_works_for_wf_wm: "wf_world_model M \<Longrightarrow> fmla\<in>M \<Longrightarrow> close_eq (wm_to_state M) \<Turnstile> fmla"
    apply (cases fmla rule: wf_fmla_atom.cases)
    by (auto simp: wf_world_model_def close_eq_def wm_to_state_def)



  lemma wm_to_state_works_for_I_closed:
    assumes "x \<in> close_world I"
    shows "close_eq (wm_to_state I) \<Turnstile> x"
    apply (rule wm_to_state_works_for_wf_wm_closed)
    using assms wf_I by auto


  lemma wf_wm_imp_basic: "wf_world_model M \<Longrightarrow> wm_basic M"
    by (auto simp: wf_world_model_def wm_basic_def wf_fmla_atm_is_atom)

theorem wf_plan_sound_system:
  assumes "\<forall>\<pi>\<in> set \<pi>s. wf_plan_action \<pi>"
  shows "sound_system
      (set (map resolve_instantiate \<pi>s))
      I
      (wm_to_state I)
      ((\<lambda>\<alpha>. pddl_opr_to_act \<alpha>))"
  unfolding sound_system_def
proof(intro conjI ballI)
  show "close_eq(wm_to_state I) \<Turnstile> x" if "x \<in> close_world I" for x
    using that[unfolded in_close_world_conv]
      wm_to_state_works_for_I_closed wm_to_state_works_for_wf_wm
    by (auto simp: wf_I)

  show "wm_basic I" using wf_wm_imp_basic[OF wf_I] .

  show "sound_opr \<alpha> (pddl_opr_to_act \<alpha>)" if "\<alpha> \<in> set (map resolve_instantiate \<pi>s)" for \<alpha>
    using that
    using wf_plan_act_is_sound' assms
    by auto
qed

theorem wf_plan_soundness_theorem:
    assumes "plan_action_path I \<pi>s M"
    defines "\<alpha>s \<equiv> map (pddl_opr_to_act \<circ> resolve_instantiate) \<pi>s"
    defines "s\<^sub>0 \<equiv> wm_to_state I"
    shows "\<exists>s'. compose_actions \<alpha>s s\<^sub>0 = Some s' \<and> (\<forall>\<phi>\<in>close_world M. s' \<Turnstile>\<^sub>= \<phi>)"
    apply (rule STRIPS_sema_sound)
    apply (rule wf_plan_sound_system)
    using assms
    unfolding plan_action_path_def
    by (auto simp add: image_def)

end \<comment> \<open>Context of \<open>wf_ast_problem\<close>\<close>

end
