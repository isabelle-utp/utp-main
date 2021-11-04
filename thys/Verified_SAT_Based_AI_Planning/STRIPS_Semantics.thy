(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory STRIPS_Semantics
  imports "STRIPS_Representation"
    "List_Supplement"
    "Map_Supplement"
begin
section "STRIPS Semantics"
text \<open> Having provided a concrete implementation of STRIPS and a corresponding locale \<open>strips\<close>, we
can now continue to define the semantics of serial and parallel STRIPS plan execution (see
\autoref{sub:serial-sas-plus-and-parallel-strips} and
\autoref{sub:parallel-sas-plus-and-parallel-strips}). \<close>
subsection "Serial Plan Execution Semantics"

text \<open> Serial plan execution is defined by primitive recursion on the plan.
Definition \autoref{isadef:execute_serial_plan} returns the given state if the state argument does
note satisfy the precondition of the next operator in the plan.
Otherwise it executes the rest of the plan on the successor state \<^term>\<open>execute_operator s op\<close> of
the given state and operator. \<close>

primrec  execute_serial_plan
  where "execute_serial_plan s [] = s"
  | "execute_serial_plan s (op # ops)
    = (if is_operator_applicable_in s op
      then execute_serial_plan (execute_operator s op) ops
      else s
  )"

text \<open> Analogously, a STRIPS trace either returns the singleton list containing only the given
state in case the precondition of the next operator in the plan is not satisfied. Otherwise, the
given state is prepended to trace of the rest of the plan for the successor state of executing the
next operator on the given state. \<close>

fun  trace_serial_plan_strips
  :: "'variable strips_state \<Rightarrow> 'variable strips_plan \<Rightarrow> 'variable strips_state list"
  where "trace_serial_plan_strips s [] = [s]"
  | "trace_serial_plan_strips s (op # ops)
      = s # (if is_operator_applicable_in s op
        then trace_serial_plan_strips (execute_operator s op) ops
        else [])"

text \<open> Finally, a serial solution is a plan which transforms a given problems initial state into
its goal state and for which all operators are elements of the problem's operator list. \<close>

definition  is_serial_solution_for_problem
  where "is_serial_solution_for_problem \<Pi> \<pi>
    \<equiv> (goal_of \<Pi>) \<subseteq>\<^sub>m execute_serial_plan (initial_of \<Pi>) \<pi>
      \<and> list_all (\<lambda>op. ListMem op (operators_of \<Pi>)) \<pi>"

lemma is_valid_problem_strips_initial_of_dom:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
  shows "dom ((\<Pi>)\<^sub>I) = set ((\<Pi>)\<^sub>\<V>)"
  proof -
    {
      let ?I = "strips_problem.initial_of \<Pi>"
      let ?vs = "strips_problem.variables_of \<Pi>"
      fix v
      have "?I v \<noteq> None \<longleftrightarrow> ListMem v ?vs"
        using assms(1)
        unfolding is_valid_problem_strips_def
        by meson
      hence "v \<in> dom ?I \<longleftrightarrow> v \<in> set ?vs"
        using ListMem_iff
        by fast
    }
    thus ?thesis
      by auto
  qed

lemma is_valid_problem_dom_of_goal_state_is:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
  shows "dom ((\<Pi>)\<^sub>G) \<subseteq> set ((\<Pi>)\<^sub>\<V>)"
  proof -
    let ?vs = "strips_problem.variables_of \<Pi>"
    let ?G = "strips_problem.goal_of \<Pi>"
    have nb: "\<forall>v. ?G v \<noteq> None \<longrightarrow> ListMem v ?vs"
      using assms(1)
      unfolding is_valid_problem_strips_def
      by meson
    {
      fix v
      assume "v \<in> dom ?G"
      then have "?G v \<noteq> None"
        by blast
      hence "v \<in> set ?vs"
        using nb
        unfolding ListMem_iff
        by blast
    }
    thus ?thesis
      by auto
  qed

lemma is_valid_problem_strips_operator_variable_sets:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "op \<in> set ((\<Pi>)\<^sub>\<O>)"
  shows "set (precondition_of op) \<subseteq> set ((\<Pi>)\<^sub>\<V>)"
    and "set (add_effects_of op) \<subseteq> set ((\<Pi>)\<^sub>\<V>)"
    and "set (delete_effects_of op) \<subseteq> set ((\<Pi>)\<^sub>\<V>)"
    and "disjnt (set (add_effects_of op)) (set (delete_effects_of op))"
  proof -
    let ?ops = "strips_problem.operators_of \<Pi>"
      and ?vs = "strips_problem.variables_of \<Pi>"
    have "list_all (is_valid_operator_strips \<Pi>) ?ops"
      using assms(1)
      unfolding is_valid_problem_strips_def
      by meson
    moreover have "\<forall>v \<in> set (precondition_of op). v \<in> set ((\<Pi>)\<^sub>\<V>)"
      and "\<forall>v \<in> set (add_effects_of op). v \<in> set ((\<Pi>)\<^sub>\<V>)"
      and "\<forall>v \<in> set (delete_effects_of op). v \<in> set ((\<Pi>)\<^sub>\<V>)"
      and "\<forall>v \<in> set (add_effects_of op). v \<notin> set (delete_effects_of op)"
      and "\<forall>v \<in> set (delete_effects_of op). v \<notin> set (add_effects_of op)"
      using assms(2) calculation
      unfolding is_valid_operator_strips_def list_all_iff Let_def ListMem_iff
      using variables_of_def
      by auto+
    ultimately show "set (precondition_of op) \<subseteq> set ((\<Pi>)\<^sub>\<V>)"
      and "set (add_effects_of op) \<subseteq> set ((\<Pi>)\<^sub>\<V>)"
      and "set (delete_effects_of op) \<subseteq> set ((\<Pi>)\<^sub>\<V>)"
      and "disjnt (set (add_effects_of op)) (set (delete_effects_of op))"
      unfolding disjnt_def
      by fast+
  qed

lemma effect_to_assignments_i:
  assumes "as = effect_to_assignments op"
  shows "as =  (map (\<lambda>v. (v, True)) (add_effects_of op)
      @ map (\<lambda>v. (v, False)) (delete_effects_of op))"
  using assms
  unfolding effect_to_assignments_def effect__strips_def
  by auto

lemma effect_to_assignments_ii:
  \<comment> \<open> NOTE \<open>effect_to_assignments\<close> can be simplified drastically given that only atomic effects
  and the add-effects as well as delete-effects lists only consist of variables.\<close>
  assumes "as = effect_to_assignments op"
  obtains as\<^sub>1 as\<^sub>2
  where "as = as\<^sub>1 @ as\<^sub>2"
    and "as\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
    and "as\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
  by (simp add: assms effect__strips_def effect_to_assignments_def)

\<comment> \<open> NOTE Show that for every variable \<open>v\<close> in either the add effect list or the delete effect
list, there exists an assignment in  \isaname{effect_to_assignments op} representing setting \<open>v\<close> to
true respectively setting \<open>v\<close> to false. Note that the first assumption amounts to saying that
the add effect list is not empty. This also requires us to split lemma
\isaname{effect_to_assignments_iii} into two separate lemmas since add and delete effect lists are
not required to both contain at least one variable simultaneously. \<close>
lemma effect_to_assignments_iii_a:
  fixes v
  assumes "v \<in> set (add_effects_of op)"
    and "as = effect_to_assignments op"
  obtains a where "a \<in> set as" "a = (v, True)"
  proof -
    let ?add_assignments = "(\<lambda>v. (v, True)) ` set (add_effects_of op)"
    let ?delete_assignments = "(\<lambda>v. (v, False)) ` set (delete_effects_of op)"
    obtain as\<^sub>1 as\<^sub>2
      where a1: "as = as\<^sub>1 @ as\<^sub>2"
        and a2: "as\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
        and a3: "as\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
      using assms(2) effect_to_assignments_ii
      by blast
    then have b: "set as
      = ?add_assignments \<union> ?delete_assignments"
      by auto
    \<comment> \<open> NOTE The existence of an assignment as proposed can be shown by the following sequence of
      set inclusions. \<close>
    {
      from b have "?add_assignments \<subseteq> set as"
        by blast
      moreover have "{(v, True)} \<subseteq> ?add_assignments"
        using assms(1) a2
        by blast
      ultimately have "\<exists>a. a \<in> set as \<and> a = (v, True)"
        by blast
    }
    then show ?thesis
      using that
      by blast
  qed

lemma effect_to_assignments_iii_b:
  \<comment> \<open> NOTE This proof is symmetrical to the one above. \<close>
  fixes v
  assumes "v \<in> set (delete_effects_of op)"
    and "as = effect_to_assignments op"
  obtains a where "a \<in> set as" "a = (v, False)"
  proof -
    let ?add_assignments = "(\<lambda>v. (v, True)) ` set (add_effects_of op)"
    let ?delete_assignments = "(\<lambda>v. (v, False)) ` set (delete_effects_of op)"
    obtain as\<^sub>1 as\<^sub>2
      where a1: "as = as\<^sub>1 @ as\<^sub>2"
        and a2: "as\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
        and a3: "as\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
      using assms(2) effect_to_assignments_ii
      by blast
    then have b: "set as
      = ?add_assignments \<union> ?delete_assignments"
      by auto
    \<comment> \<open> NOTE The existence of an assignment as proposed can be shown by the following sequence of
      set inclusions. \<close>
    {
      from b have "?delete_assignments \<subseteq> set as"
        by blast
      moreover have "{(v, False)} \<subseteq> ?delete_assignments"
        using assms(1) a2
        by blast
      ultimately have "\<exists>a. a \<in> set as \<and> a = (v, False)"
        by blast
    }
    then show ?thesis
      using that
      by blast
  qed

lemma effect__strips_i:
  fixes op
  assumes "e = effect__strips op"
  obtains es\<^sub>1 es\<^sub>2
    where "e = (es\<^sub>1 @ es\<^sub>2)"
      and "es\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
      and "es\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
  proof -
    obtain es\<^sub>1 es\<^sub>2 where a: "e = (es\<^sub>1 @ es\<^sub>2)"
      and b: "es\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
      and c: "es\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
      using assms(1)
      unfolding effect__strips_def
      by blast
    then show ?thesis
      using that
      by force
  qed

lemma effect__strips_ii:
  fixes op
  assumes "e = ConjunctiveEffect (es\<^sub>1 @ es\<^sub>2)"
    and "es\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
    and "es\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
  shows "\<forall>v \<in> set (add_effects_of op). (\<exists>e' \<in> set es\<^sub>1. e' = (v, True))"
    and "\<forall>v \<in> set (delete_effects_of op). (\<exists>e' \<in> set es\<^sub>2. e' = (v, False))"
  proof
  \<comment> \<open> NOTE Show that for each variable \<open>v\<close> in the add effect list, we can obtain an atomic effect
  with true value. \<close>
    fix v
    {
      assume a: "v \<in> set (add_effects_of op)"
      have "set es\<^sub>1 = (\<lambda>v. (v, True)) ` set (add_effects_of op)"
        using assms(2) List.set_map
        by auto
      then obtain e'
        where "e' \<in> set es\<^sub>1"
        and "e' =  (\<lambda>v. (v, True)) v"
        using a
        by blast
      then have "\<exists>e' \<in> set es\<^sub>1. e' = (v, True)"
        by blast
    }
    thus "v \<in> set (add_effects_of op) \<Longrightarrow> \<exists>e' \<in> set es\<^sub>1. e' = (v, True)"
      by fast
  \<comment> \<open> NOTE the proof is symmetrical to the one above: for each variable v in the delete effect list,
  we can obtain an atomic effect with v being false. \<close>
  next
    {
      fix v
      assume a: "v \<in> set (delete_effects_of op)"
      have "set es\<^sub>2 = (\<lambda>v. (v, False)) ` set (delete_effects_of op)"
        using assms(3) List.set_map
        by force
      then obtain e''
        where "e'' \<in> set es\<^sub>2"
        and "e'' =  (\<lambda>v. (v, False)) v"
        using a
        by blast
      then have "\<exists>e'' \<in> set es\<^sub>2. e'' = (v, False)"
        by blast
    }
    thus "\<forall>v\<in>set (delete_effects_of op). \<exists>e'\<in>set es\<^sub>2. e' = (v, False)"
      by fast
  qed

(* TODO refactor theory Appendix AND make visible? *)
lemma map_of_constant_assignments_dom:
  \<comment> \<open> NOTE ancillary lemma used in the proof below. \<close>
  assumes "m = map_of (map (\<lambda>v. (v, d)) vs)"
  shows "dom m = set vs"
  proof -
    let ?vs' = "map (\<lambda>v. (v, d)) vs"
    have "dom m = fst ` set ?vs'"
      using assms(1) dom_map_of_conv_image_fst
      by metis
    moreover have "fst ` set ?vs' = set vs"
      by force
    ultimately show ?thesis
      by argo
  qed

lemma effect__strips_iii_a:
  assumes "s' = (s \<then> op)"
  shows "\<And>v. v \<in> set (add_effects_of op) \<Longrightarrow> s' v = Some True"
  proof -
    fix v
    assume a: "v \<in> set (add_effects_of op)"
    let ?as = "effect_to_assignments op"
    obtain as\<^sub>1 as\<^sub>2 where b: "?as = as\<^sub>1 @ as\<^sub>2"
      and c: "as\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
      and "as\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
      using effect_to_assignments_ii
      by blast
    have d: "map_of ?as = map_of as\<^sub>2 ++ map_of as\<^sub>1"
      using b Map.map_of_append
      by auto
    {
      \<comment> \<open> TODO refactor? \<close>
      let ?vs = "add_effects_of op"
      have "?vs \<noteq> []"
        using a
        by force
      then have "dom (map_of as\<^sub>1) = set (add_effects_of op)"
        using c map_of_constant_assignments_dom
        by metis
      then have "v \<in> dom (map_of as\<^sub>1)"
        using a
        by blast
      then have "map_of ?as v = map_of as\<^sub>1 v"
        using d
        by force
    } moreover {
      let ?f = "\<lambda>_. True"
      from c have "map_of as\<^sub>1 = (Some \<circ> ?f) |` (set (add_effects_of op))"
        using map_of_map_restrict
        by fast
      then have "map_of as\<^sub>1 v = Some True"
        using a
        by auto
    }
    moreover have "s' = s ++ map_of as\<^sub>2 ++ map_of as\<^sub>1"
      using assms(1)
      unfolding execute_operator_def
      using b
      by simp
    ultimately show "s' v = Some True"
      by simp
  qed

(* TODO In contrast to the proof above we need proof preparation with auto. Why? *)
lemma effect__strips_iii_b:
  assumes "s' = (s \<then> op)"
  shows "\<And>v. v \<in> set (delete_effects_of op) \<and> v \<notin> set (add_effects_of op) \<Longrightarrow> s' v = Some False"
  proof (auto)
    fix v
    assume a1: "v \<notin> set (add_effects_of op)" and a2: "v \<in> set (delete_effects_of op)"
    let ?as = "effect_to_assignments op"
    obtain as\<^sub>1 as\<^sub>2 where b: "?as = as\<^sub>1 @ as\<^sub>2"
      and c: "as\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
      and d: "as\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
      using effect_to_assignments_ii
      by blast
    have e: "map_of ?as = map_of as\<^sub>2 ++ map_of as\<^sub>1"
      using b Map.map_of_append
      by auto
    {
      have "dom (map_of as\<^sub>1) = set (add_effects_of op)"
        using c map_of_constant_assignments_dom
        by metis
      then have "v \<notin> dom (map_of as\<^sub>1)"
        using a1
        by blast
    } note f = this
    {
      let ?vs = "delete_effects_of op"
      have "?vs \<noteq> []"
        using a2
        by force
      then have "dom (map_of as\<^sub>2) = set ?vs"
        using d  map_of_constant_assignments_dom
        by metis
    } note g = this
    {
      have "s' = s ++ map_of as\<^sub>2 ++ map_of as\<^sub>1"
        using assms(1)
        unfolding execute_operator_def
        using b
        by simp
      thm  f map_add_dom_app_simps(3)[OF f, of "s ++ map_of as\<^sub>2"]
      moreover have "s' v = (s ++ map_of as\<^sub>2) v"
        using calculation  map_add_dom_app_simps(3)[OF f, of "s ++ map_of as\<^sub>2"]
        by blast
      moreover have "v \<in> dom (map_of as\<^sub>2)"
        using a2 g
        by argo
      ultimately have "s' v = map_of as\<^sub>2 v"
        by fastforce
    }
    moreover
    {
      let ?f = "\<lambda>_. False"
      from d have "map_of as\<^sub>2 = (Some \<circ> ?f) |` (set (delete_effects_of op))"
        using map_of_map_restrict
        by fast
      then have "map_of as\<^sub>2 v = Some False"
        using a2
        by force
    }
    ultimately show  " s' v = Some False"
      by argo
  qed

(* TODO We need proof preparation with auto. Why? *)
lemma effect__strips_iii_c:
  assumes "s' = (s \<then> op)"
  shows "\<And>v. v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op) \<Longrightarrow> s' v = s v"
  proof (auto)
    fix v
    assume a1: "v \<notin> set (add_effects_of op)" and a2: "v \<notin> set (delete_effects_of op)"
    let ?as = "effect_to_assignments op"
    obtain as\<^sub>1 as\<^sub>2 where b: "?as = as\<^sub>1 @ as\<^sub>2"
      and c: "as\<^sub>1 = map (\<lambda>v. (v, True)) (add_effects_of op)"
      and d: "as\<^sub>2 = map (\<lambda>v. (v, False)) (delete_effects_of op)"
      using effect_to_assignments_ii
      by blast
    have e: "map_of ?as = map_of as\<^sub>2 ++ map_of as\<^sub>1"
      using b Map.map_of_append
      by auto
    {
      have "dom (map_of as\<^sub>1) = set (add_effects_of op)"
        using c map_of_constant_assignments_dom
        by metis
      then have "v \<notin> dom (map_of as\<^sub>1)"
        using a1
        by blast
    } moreover  {
      have "dom (map_of as\<^sub>2) = set (delete_effects_of op)"
        using d map_of_constant_assignments_dom
        by metis
      then have "v \<notin> dom (map_of as\<^sub>2)"
        using a2
        by blast
    }
    ultimately show "s' v = s v"
      using assms(1)
      unfolding execute_operator_def
      by (simp add: b map_add_dom_app_simps(3))
  qed

text \<open>The following theorem combines three preceding sublemmas which show
that the following properties hold for the successor state \<open>s' \<equiv> execute_operator op s\<close>
obtained by executing an operator \<open>op\<close> in a state \<open>s\<close>:
\footnote{Lemmas \path{effect__strips_iii_a}, \path{effect__strips_iii_b}, and
\path{effect__strips_iii_c} (not shown).}

\begin{itemize}
  \item every add effect is satisfied in \<open>s'\<close> (sublemma  \isaname{effect__strips_iii_a}); and,
  \item every delete effect that is not also an add effect is not satisfied in \<open>s'\<close> (sublemma
\isaname{effect__strips_iii_b}); and finally
  \item the state remains unchanged---i.e. \<open>s' v = s v\<close>---for all variables which are neither an
add effect nor a delete effect.
\end{itemize} \<close>

(* TODO? Rewrite theorem \<open>operator_effect__strips\<close> to match \<open>s ++ map_of (
effect_to_assignments op)\<close> rather than \<open>execute_operator \<Pi> op s\<close> since we need this
form later on for the parallel execution theorem? *)
theorem  operator_effect__strips:
  assumes "s' = (s \<then> op)"
  shows
    "\<And>v.
      v \<in> set (add_effects_of op)
      \<Longrightarrow> s' v = Some True"
    and "\<And>v.
      v \<notin> set (add_effects_of op) \<and> v \<in> set (delete_effects_of op)
      \<Longrightarrow> s' v = Some False"
    and "\<And>v.
      v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op)
      \<Longrightarrow> s' v = s v"
proof (auto)
  show "\<And>v.
    v \<in> set (add_effects_of op)
    \<Longrightarrow> s' v = Some True"
    using assms effect__strips_iii_a
    by fast
next
  show "\<And>v.
    v \<notin> set (add_effects_of op)
    \<Longrightarrow> v \<in> set (delete_effects_of op)
    \<Longrightarrow>  s' v = Some False"
    using assms effect__strips_iii_b
    by fast
next
  show "\<And>v.
    v \<notin> set (add_effects_of op)
    \<Longrightarrow> v \<notin> set (delete_effects_of op)
    \<Longrightarrow> s' v = s v"
    using assms effect__strips_iii_c
    by metis
qed

subsection "Parallel Plan Semantics"

definition "are_all_operators_applicable s ops
  \<equiv> list_all (\<lambda>op. is_operator_applicable_in s op) ops"

definition "are_operator_effects_consistent op\<^sub>1 op\<^sub>2 \<equiv> let
    add\<^sub>1 = add_effects_of op\<^sub>1
    ; add\<^sub>2 = add_effects_of op\<^sub>2
    ; del\<^sub>1 = delete_effects_of op\<^sub>1
    ; del\<^sub>2 = delete_effects_of op\<^sub>2
  in \<not>list_ex (\<lambda>v. list_ex ((=) v) del\<^sub>2) add\<^sub>1 \<and> \<not>list_ex (\<lambda>v. list_ex ((=) v) add\<^sub>2) del\<^sub>1"

definition "are_all_operator_effects_consistent ops \<equiv>
  list_all (\<lambda>op. list_all (are_operator_effects_consistent op) ops) ops"

definition execute_parallel_operator
  :: "'variable strips_state
    \<Rightarrow> 'variable strips_operator list
    \<Rightarrow> 'variable strips_state"
  where "execute_parallel_operator s ops
    \<equiv> foldl (++) s (map (map_of \<circ> effect_to_assignments) ops)"
text \<open> The parallel STRIPS execution semantics is defined in similar way as the serial STRIPS
execution semantics. However, the applicability test is lifted to parallel operators and we
additionally test for operator consistency (which was unecessary in the serial case). \<close>

fun  execute_parallel_plan
  :: "'variable strips_state
    \<Rightarrow> 'variable strips_parallel_plan
    \<Rightarrow> 'variable strips_state"
  where "execute_parallel_plan s [] = s"
  | "execute_parallel_plan s (ops # opss) = (if
      are_all_operators_applicable s ops
      \<and> are_all_operator_effects_consistent ops
    then execute_parallel_plan (execute_parallel_operator s ops) opss
    else s)"

definition "are_operators_interfering op\<^sub>1 op\<^sub>2
  \<equiv> list_ex (\<lambda>v. list_ex ((=) v) (delete_effects_of op\<^sub>1)) (precondition_of op\<^sub>2)
    \<or>  list_ex (\<lambda>v. list_ex ((=) v) (precondition_of op\<^sub>1)) (delete_effects_of op\<^sub>2)"

(* TODO rewrite as inductive predicate *)
primrec are_all_operators_non_interfering
  :: "'variable strips_operator list \<Rightarrow> bool"
  where "are_all_operators_non_interfering [] = True"
  | "are_all_operators_non_interfering (op # ops)
    = (list_all (\<lambda>op'. \<not>are_operators_interfering op op') ops
      \<and> are_all_operators_non_interfering ops)"

text \<open> Since traces mirror the execution semantics, the same is true for the definition of
parallel STRIPS plan traces. \<close>

fun  trace_parallel_plan_strips
  :: "'variable strips_state \<Rightarrow> 'variable strips_parallel_plan \<Rightarrow> 'variable strips_state list"
  where "trace_parallel_plan_strips s [] = [s]"
  | "trace_parallel_plan_strips s (ops # opss) = s # (if
      are_all_operators_applicable s ops
      \<and> are_all_operator_effects_consistent ops
    then trace_parallel_plan_strips (execute_parallel_operator s ops) opss
    else [])"

text \<open> Similarly, the definition of parallel solutions requires that the parallel execution
semantics transforms the initial problem into the goal state of the problem and that every
operator of every parallel operator in the parallel plan is an operator that is defined in the
problem description. \<close>

definition  is_parallel_solution_for_problem
  where "is_parallel_solution_for_problem \<Pi> \<pi>
    \<equiv> (strips_problem.goal_of \<Pi>) \<subseteq>\<^sub>m execute_parallel_plan
        (strips_problem.initial_of \<Pi>) \<pi>
      \<and> list_all (\<lambda>ops. list_all (\<lambda>op.
        ListMem op (strips_problem.operators_of \<Pi>)) ops) \<pi>"


(* TODO rename are_all_operators_applicable_in_set *)
lemma are_all_operators_applicable_set:
  "are_all_operators_applicable s ops
    \<longleftrightarrow> (\<forall>op \<in> set ops. \<forall>v \<in> set (precondition_of op). s v = Some True)"
  unfolding are_all_operators_applicable_def
    STRIPS_Representation.is_operator_applicable_in_def list_all_iff
  by presburger

(* TODO rename are_all_operators_applicable_in_cons *)
lemma are_all_operators_applicable_cons:
  assumes "are_all_operators_applicable s (op # ops)"
  shows "is_operator_applicable_in s op"
    and "are_all_operators_applicable s ops"
  proof -
    from assms have a: "list_all (\<lambda>op. is_operator_applicable_in s op) (op # ops)"
      unfolding are_all_operators_applicable_def is_operator_applicable_in_def
        STRIPS_Representation.is_operator_applicable_in_def
      by blast
    then have "is_operator_applicable_in s op"
      by fastforce
    moreover {
      from a have "list_all (\<lambda>op. is_operator_applicable_in s op) ops"
        by simp
      then have "are_all_operators_applicable s ops"
      using are_all_operators_applicable_def is_operator_applicable_in_def
        STRIPS_Representation.is_operator_applicable_in_def
        by blast
      }
    ultimately show "is_operator_applicable_in s op"
      and "are_all_operators_applicable s ops"
       by fast+
  qed

lemma are_operator_effects_consistent_set:
  assumes "op\<^sub>1 \<in> set ops"
    and "op\<^sub>2 \<in> set ops"
  shows "are_operator_effects_consistent op\<^sub>1 op\<^sub>2
     = (set (add_effects_of op\<^sub>1) \<inter> set (delete_effects_of op\<^sub>2) = {}
      \<and> set (delete_effects_of op\<^sub>1) \<inter> set (add_effects_of op\<^sub>2) = {})"
  proof -
    have "(\<not>list_ex (\<lambda>v. list_ex ((=) v) (delete_effects_of op\<^sub>2)) (add_effects_of op\<^sub>1))
      = (set (add_effects_of op\<^sub>1) \<inter> set (delete_effects_of op\<^sub>2) = {})"
      using list_ex_intersection[of "delete_effects_of op\<^sub>2" "add_effects_of op\<^sub>1"]
      by meson
    moreover have "(\<not>list_ex (\<lambda>v. list_ex ((=) v) (add_effects_of op\<^sub>2)) (delete_effects_of op\<^sub>1))
      = (set (delete_effects_of op\<^sub>1) \<inter> set (add_effects_of op\<^sub>2) = {})"
      using list_ex_intersection[of "add_effects_of op\<^sub>2"  "delete_effects_of op\<^sub>1"]
      by meson
    ultimately show "are_operator_effects_consistent op\<^sub>1 op\<^sub>2
       = (set (add_effects_of op\<^sub>1) \<inter> set (delete_effects_of op\<^sub>2) = {}
        \<and> set (delete_effects_of op\<^sub>1) \<inter> set (add_effects_of op\<^sub>2) = {})"
      unfolding are_operator_effects_consistent_def
      by presburger
  qed

lemma are_all_operator_effects_consistent_set:
  "are_all_operator_effects_consistent ops
    \<longleftrightarrow> (\<forall>op\<^sub>1 \<in> set ops. \<forall>op\<^sub>2 \<in> set ops.
      (set (add_effects_of op\<^sub>1) \<inter> set (delete_effects_of op\<^sub>2) = {})
        \<and> (set (delete_effects_of op\<^sub>1) \<inter> set (add_effects_of op\<^sub>2) = {}))"
  proof -
    {
      fix op\<^sub>1 op\<^sub>2
      assume "op\<^sub>1 \<in> set ops" and "op\<^sub>2 \<in> set ops"
      hence "are_operator_effects_consistent op\<^sub>1 op\<^sub>2
        = (set (add_effects_of op\<^sub>1) \<inter> set (delete_effects_of op\<^sub>2) = {}
          \<and> set (delete_effects_of op\<^sub>1) \<inter> set (add_effects_of op\<^sub>2) = {})"
        using are_operator_effects_consistent_set[of op\<^sub>1 ops op\<^sub>2]
        by fast
    }
    thus ?thesis
      unfolding are_all_operator_effects_consistent_def list_all_iff
      by force
  qed

lemma are_all_effects_consistent_tail:
  assumes "are_all_operator_effects_consistent (op # ops)"
  shows "are_all_operator_effects_consistent ops"
  proof -
    from assms
    have a: "list_all (\<lambda>op'. list_all (are_operator_effects_consistent op')
      (Cons op ops)) (Cons op ops)"
      unfolding are_all_operator_effects_consistent_def
      by blast
    then have b_1: "list_all (are_operator_effects_consistent op) (op # ops)"
      and b_2: "list_all (\<lambda>op'. list_all (are_operator_effects_consistent op') (op # ops)) ops"
      by force+
    then have "list_all (are_operator_effects_consistent op) ops"
      by simp
    moreover
    {
      {
        fix z
        assume "z \<in> set (Cons op ops)"
         and "list_all (are_operator_effects_consistent z) (op # ops)"
        then have "list_all (are_operator_effects_consistent z) ops"
          by auto
      }
      then have "list_all (\<lambda>op'. list_all (are_operator_effects_consistent op') ops) ops"
        using list.pred_mono_strong[of
            "(\<lambda>op'. list_all (are_operator_effects_consistent op') (op # ops))"
            "Cons op ops" "(\<lambda>op'. list_all (are_operator_effects_consistent op')  ops)"
          ] a
        by fastforce
    }
    ultimately have "list_all (are_operator_effects_consistent op) ops
      \<and> list_all (\<lambda>op'. list_all (are_operator_effects_consistent op') ops) ops"
      by blast
    then show ?thesis
      using are_all_operator_effects_consistent_def
      by fast
  qed

lemma are_all_operators_non_interfering_tail:
  assumes "are_all_operators_non_interfering (op # ops)"
  shows "are_all_operators_non_interfering ops"
  using assms
  unfolding are_all_operators_non_interfering_def
  by simp

lemma are_operators_interfering_symmetric:
  assumes "are_operators_interfering op\<^sub>1 op\<^sub>2"
  shows "are_operators_interfering op\<^sub>2 op\<^sub>1"
  using assms
  unfolding are_operators_interfering_def list_ex_iff
  by fast

\<comment> \<open> A small technical characterizing operator lists with property
\isaname{are_all_operators_non_interfering ops}. We show that pairs of distinct operators which interfere
with one another cannot both be contained in the corresponding operator set. \<close>
lemma are_all_operators_non_interfering_set_contains_no_distinct_interfering_operator_pairs:
  assumes "are_all_operators_non_interfering ops"
    and "are_operators_interfering op\<^sub>1 op\<^sub>2"
    and "op\<^sub>1 \<noteq> op\<^sub>2"
  shows "op\<^sub>1 \<notin> set ops \<or> op\<^sub>2 \<notin> set ops"
  using assms
  proof (induction ops)
    case (Cons op ops)
    thm Cons.IH[OF _ Cons.prems(2, 3)]
    have nb\<^sub>1: "\<forall>op' \<in> set ops. \<not>are_operators_interfering op op'"
      and nb\<^sub>2: "are_all_operators_non_interfering ops"
      using Cons.prems(1)
      unfolding are_all_operators_non_interfering.simps(2) list_all_iff
      by blast+
    then consider (A) "op = op\<^sub>1"
      | (B) "op = op\<^sub>2"
      | (C) "op \<noteq> op\<^sub>1 \<and> op \<noteq> op\<^sub>2"
      by blast
    thus ?case
      proof (cases)
        case A
        {
          assume "op\<^sub>2 \<in> set (op # ops)"
          then have "op\<^sub>2 \<in> set ops"
            using Cons.prems(3) A
            by force
          then have "\<not>are_operators_interfering op\<^sub>1 op\<^sub>2"
            using nb\<^sub>1 A
            by fastforce
          hence False
            using Cons.prems(2)..
        }
        thus ?thesis
          by blast
      next
        case B
        {
          assume "op\<^sub>1 \<in> set (op # ops)"
          then have "op\<^sub>1 \<in> set ops"
            using Cons.prems(3) B
            by force
          then have "\<not>are_operators_interfering op\<^sub>1 op\<^sub>2"
            using nb\<^sub>1 B are_operators_interfering_symmetric
            by blast
          hence False
            using Cons.prems(2)..
        }
        thus ?thesis
          by blast
      next
        case C
        thus ?thesis
          using Cons.IH[OF nb\<^sub>2 Cons.prems(2, 3)]
          by force
      qed
  qed simp

(* TODO The recurring \<open>list_all \<leadsto> \<forall>\<close> transformations could be refactored into a general
lemma.
   TODO refactor (also used in lemma \<open>execute_serial_plan_split_i\<close>). *)
lemma execute_parallel_plan_precondition_cons_i:
  fixes s :: "('variable, bool) state"
  assumes "\<not>are_operators_interfering op op'"
    and "is_operator_applicable_in s op"
    and "is_operator_applicable_in s op'"
  shows "is_operator_applicable_in (s ++ map_of (effect_to_assignments op)) op'"
  proof -
    let ?s' = "s ++ map_of (effect_to_assignments op)"
    \<comment> \<open> TODO slightly hackish to exploit the definition of \<open>execute_operator\<close>, but we
  otherwise have to rewrite theorem \<open>operator_effect__strips\<close> (which is a todo as of now). \<close>
    {
      have a: "?s' = s \<then> op"
        by (simp add: execute_operator_def)
      then have "\<And>v. v \<in> set (add_effects_of op) \<Longrightarrow> ?s' v = Some True"
        and "\<And>v. v \<notin> set (add_effects_of op) \<and> v \<in> set (delete_effects_of op) \<Longrightarrow> ?s' v = Some False"
        and "\<And>v. v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op) \<Longrightarrow> ?s' v = s v"
        using operator_effect__strips
        by metis+
    }
    note a = this
    \<comment> \<open> TODO refactor lemma \<open>not_have_interference_set\<close>. \<close>
    {
      fix v
      assume \<alpha>: "v \<in> set (precondition_of op')"
      {
        fix v
        have "\<not>list_ex ((=) v) (delete_effects_of op)
          = list_all (\<lambda>v'. \<not>v = v') (delete_effects_of op)"
          using not_list_ex_equals_list_all_not[
              where P="(=) v" and xs="delete_effects_of op"]
          by blast
      } moreover {
        from assms(1)
        have "\<not>list_ex (\<lambda>v. list_ex ((=) v) (delete_effects_of op)) (precondition_of op')"
          unfolding are_operators_interfering_def
          by blast
        then have "list_all (\<lambda>v. \<not>list_ex ((=) v) (delete_effects_of op)) (precondition_of op')"
          using not_list_ex_equals_list_all_not[
              where P="\<lambda>v. list_ex ((=) v) (delete_effects_of op)" and xs="precondition_of op'"]
          by blast
      }
      ultimately have \<beta>:
        "list_all (\<lambda>v. list_all (\<lambda>v'. \<not>v = v') (delete_effects_of op)) (precondition_of op')"
        by presburger
      moreover {
        fix v
        have "list_all (\<lambda>v'. \<not>v = v') (delete_effects_of op)
          = (\<forall>v' \<in> set (delete_effects_of op). \<not>v = v')"
          using list_all_iff [where P="\<lambda>v'. \<not>v = v'" and x="delete_effects_of op"]
          .
      }
      ultimately have "\<forall>v \<in> set (precondition_of op'). \<forall>v' \<in> set (delete_effects_of op). \<not>v = v'"
        using \<beta> list_all_iff[
          where P="\<lambda>v. list_all (\<lambda>v'. \<not>v = v') (delete_effects_of op)"
            and x="precondition_of op'"]
        by presburger
      then have "v \<notin> set (delete_effects_of op)"
        using \<alpha>
        by fast
    }
    note b = this
    {
      fix v
      assume a: "v \<in> set (precondition_of op')"
      have "list_all (\<lambda>v. s v = Some True) (precondition_of op')"
        using assms(3)
        unfolding is_operator_applicable_in_def
          STRIPS_Representation.is_operator_applicable_in_def
        by presburger
      then have "\<forall>v \<in> set (precondition_of op'). s v = Some True"
        using list_all_iff[where P="\<lambda>v. s v = Some True" and x="precondition_of op'"]
        by blast
      then have "s v = Some True"
        using a
        by blast
    }
    note c = this
    {
      fix v
      assume d: "v \<in> set (precondition_of op')"
      then have "?s' v = Some True"
      proof (cases "v \<in> set (add_effects_of op)")
        case True
        then show ?thesis
          using a
          by blast
      next
        case e: False
        then show ?thesis
        proof (cases "v \<in> set (delete_effects_of op)")
          case True
          then show ?thesis
            using assms(1) b d
              by fast
          next
            case False
            then have "?s' v = s v"
              using a e
              by blast
            then show ?thesis
              using c d
              by presburger
          qed
      qed
    }
    then have "list_all (\<lambda>v. ?s' v = Some True) (precondition_of op')"
      using list_all_iff[where P="\<lambda>v. ?s' v = Some True" and x="precondition_of op'"]
      by blast
    then show ?thesis
      unfolding is_operator_applicable_in_def
        STRIPS_Representation.is_operator_applicable_in_def
      by auto
  qed

\<comment> \<open> The third assumption \<open>are_all_operators_non_interfering (a # ops)\<close>" is not part of the
precondition of \isaname{execute_parallel_operator} but is required for the proof of the
subgoal hat applicable is maintained. \<close>
lemma execute_parallel_plan_precondition_cons:
  fixes a :: "'variable strips_operator"
  assumes "are_all_operators_applicable s (a # ops)"
    and "are_all_operator_effects_consistent (a # ops)"
    and "are_all_operators_non_interfering (a # ops)"
  shows "are_all_operators_applicable (s ++ map_of (effect_to_assignments a)) ops"
    and "are_all_operator_effects_consistent ops"
    and "are_all_operators_non_interfering ops"
  using are_all_effects_consistent_tail[OF assms(2)]
    are_all_operators_non_interfering_tail[OF assms(3)]
  proof -
    let ?s' = "s ++ map_of (effect_to_assignments a)"
    have nb\<^sub>1: "\<forall>op \<in> set (a # ops). is_operator_applicable_in s op"
      using assms(1) are_all_operators_applicable_set
      unfolding are_all_operators_applicable_def is_operator_applicable_in_def
        STRIPS_Representation.is_operator_applicable_in_def list_all_iff
      by blast
    have nb\<^sub>2: "\<forall>op \<in> set ops. \<not>are_operators_interfering a op"
      using assms(3)
      unfolding are_all_operators_non_interfering_def list_all_iff
      by simp
    have nb\<^sub>3: "is_operator_applicable_in s a"
      using assms(1) are_all_operators_applicable_set
      unfolding are_all_operators_applicable_def is_operator_applicable_in_def
        STRIPS_Representation.is_operator_applicable_in_def list_all_iff
      by force
    {
      fix op
      assume op_in_ops: "op \<in> set ops"
      hence "is_operator_applicable_in ?s' op"
        using execute_parallel_plan_precondition_cons_i[of a op] nb\<^sub>1 nb\<^sub>2 nb\<^sub>3
        by force
    }
    then show "are_all_operators_applicable ?s' ops"
      unfolding are_all_operators_applicable_def list_all_iff
        is_operator_applicable_in_def
      by blast
  qed

lemma execute_parallel_operator_cons[simp]:
  "execute_parallel_operator s (op # ops)
    = execute_parallel_operator (s ++ map_of (effect_to_assignments op)) ops"
  unfolding execute_parallel_operator_def
  by simp

lemma execute_parallel_operator_cons_equals:
  assumes "are_all_operators_applicable s (a # ops)"
    and "are_all_operator_effects_consistent (a # ops)"
    and "are_all_operators_non_interfering (a # ops)"
  shows "execute_parallel_operator s (a # ops)
    = execute_parallel_operator (s ++ map_of (effect_to_assignments a)) ops"
  proof -
    let ?s' = "s ++ map_of (effect_to_assignments a)"
    {
      from assms(1, 2)
      have "execute_parallel_operator s (Cons a ops)
        = foldl (++) s (map (map_of \<circ> effect_to_assignments) (Cons a ops))"
         unfolding execute_parallel_operator_def
         by presburger
       also have "\<dots> = foldl (++) (?s')
         (map (map_of \<circ> effect_to_assignments) ops)"
         by auto
       finally have "execute_parallel_operator s (Cons a ops)
         = foldl (++) (?s')
          (map (map_of \<circ> effect_to_assignments) ops)"
         using execute_parallel_operator_def
         by blast
     }
    \<comment> \<open> NOTE the precondition of \isaname{execute_parallel} for \<open>a # ops\<close> is also true for the tail
    list and \<open>state ?s'\<close> as shown in lemma
    \isaname{execute_parallel_operator_precondition_cons}. Hence the precondition for the r.h.s.
    of the goal also holds. \<close>
     moreover have "execute_parallel_operator ?s' ops
        = foldl (++) (s ++ (map_of \<circ> effect_to_assignments) a)
          (map (map_of \<circ> effect_to_assignments) ops)"
         by (simp add: execute_parallel_operator_def)
    ultimately show ?thesis
      by force
  qed

\<comment> \<open> We show here that following the lemma above, executing one operator of a parallel
operator can be replaced by a (single) STRIPS operator execution. \<close>
corollary execute_parallel_operator_cons_equals_corollary:
  assumes "are_all_operators_applicable s (a # ops)"
  shows "execute_parallel_operator s (a # ops)
    = execute_parallel_operator (s \<then> a) ops"
  proof -
    let ?s' = "s ++ map_of (effect_to_assignments a)"
    from assms
    have "execute_parallel_operator s (a # ops)
      = execute_parallel_operator (s ++ map_of (effect_to_assignments a)) ops"
      using execute_parallel_operator_cons_equals
      by simp
    moreover have "?s' = s \<then> a"
      unfolding execute_operator_def
      by simp
    ultimately show ?thesis
      by argo
  qed

(* TODO duplicate? *)
lemma effect_to_assignments_simp[simp]: "effect_to_assignments op
  = map (\<lambda>v. (v, True)) (add_effects_of op) @ map (\<lambda>v. (v, False)) (delete_effects_of op)"
  by (simp add: effect_to_assignments_i)

lemma effect_to_assignments_set_is[simp]:
  "set (effect_to_assignments op) = { ((v, a), True) | v a. (v, a) \<in> set (add_effects_of op) }
    \<union> { ((v, a), False) | v a. (v, a) \<in> set (delete_effects_of op) }"
proof -
    obtain as where "effect__strips op = as"
      and "as = map (\<lambda>v. (v, True)) (add_effects_of op)
        @ map (\<lambda>v. (v, False)) (delete_effects_of op)"
      unfolding effect__strips_def
      by blast
    moreover have "as
      = map (\<lambda>v. (v, True)) (add_effects_of op) @ map (\<lambda>v. (v, False)) (delete_effects_of op)"
      using calculation(2)
      unfolding map_append map_map comp_apply
      by auto
    moreover have "effect_to_assignments op = as"
      unfolding effect_to_assignments_def calculation(1, 2)
      by auto
    ultimately show ?thesis
      unfolding set_map
      by auto
  qed

corollary effect_to_assignments_construction_from_function_graph:
  assumes "set (add_effects_of op) \<inter> set (delete_effects_of op) = {}"
  shows "effect_to_assignments op = map
    (\<lambda>v. (v, if ListMem v (add_effects_of op) then True else False))
    (add_effects_of op @ delete_effects_of op)"
    and "effect_to_assignments op = map
    (\<lambda>v. (v, if ListMem v (delete_effects_of op) then False else True))
    (add_effects_of op @ delete_effects_of op)"
  proof -
    let ?f = "\<lambda>v. (v, if ListMem v (add_effects_of op) then True else False)"
      and ?g = "\<lambda>v. (v, if ListMem v (delete_effects_of op) then False else True)"
    {
      have "map ?f (add_effects_of op @ delete_effects_of op)
        = map ?f (add_effects_of op) @ map ?f (delete_effects_of op)"
        using map_append
        by fast
      \<comment> \<open> TODO slow. \<close>
      hence "effect_to_assignments op = map ?f (add_effects_of op @ delete_effects_of op)"
        using ListMem_iff assms
        by fastforce
    } moreover {
      have "map ?g (add_effects_of op @ delete_effects_of op)
        = map ?g (add_effects_of op) @ map ?g (delete_effects_of op)"
        using map_append
        by fast
      \<comment> \<open> TODO slow. \<close>
      hence "effect_to_assignments op = map ?g (add_effects_of op @ delete_effects_of op)"
        using ListMem_iff assms
        by fastforce
    }
    ultimately show "effect_to_assignments op = map
      (\<lambda>v. (v, if ListMem v (add_effects_of op) then True else False))
      (add_effects_of op @ delete_effects_of op)"
      and "effect_to_assignments op = map
      (\<lambda>v. (v, if ListMem v (delete_effects_of op) then False else True))
      (add_effects_of op @ delete_effects_of op)"
      by blast+
  qed

corollary map_of_effect_to_assignments_is_none_if:
  assumes "\<not>v \<in> set (add_effects_of op)"
    and "\<not>v \<in> set (delete_effects_of op)"
  shows "map_of (effect_to_assignments op) v = None"
  proof -
    let ?l = "effect_to_assignments op"
    {
      have "set ?l = { (v, True) | v. v \<in> set (add_effects_of op) }
        \<union> { (v, False) | v. v \<in> set (delete_effects_of op)}"
        by auto
      then have "fst ` set ?l
        = (fst ` {(v, True) | v. v \<in> set (add_effects_of op)})
          \<union> (fst ` {(v, False) | v. v \<in> set (delete_effects_of op)})"
        using image_Un[of fst "{(v, True) | v. v \<in> set (add_effects_of op)}"
           "{(v, False) | v. v \<in> set (delete_effects_of op)}"]
        by presburger
      \<comment> \<open> TODO slow.\<close>
      also have "\<dots> = (fst ` (\<lambda>v. (v, True)) ` set (add_effects_of op))
        \<union> (fst ` (\<lambda>v. (v, False)) ` set (delete_effects_of op))"
        using setcompr_eq_image[of "\<lambda>v. (v, True)" "\<lambda>v. v \<in> set (add_effects_of op)"]
          setcompr_eq_image[of "\<lambda>v. (v, False)" "\<lambda>v. v \<in> set (delete_effects_of op)"]
        by simp
      \<comment> \<open> TODO slow.\<close>
      also have "\<dots> = id ` set (add_effects_of op) \<union> id ` set (delete_effects_of op)"
        by force
      \<comment> \<open> TODO slow.\<close>
      finally have "fst ` set ?l = set (add_effects_of op) \<union> set (delete_effects_of op)"
        by auto
      hence "v \<notin> fst ` set ?l"
        using assms(1, 2)
        by blast
    }
    thus ?thesis
      using map_of_eq_None_iff[of ?l v]
      by blast
  qed

lemma execute_parallel_operator_positive_effect_if_i:
  assumes "are_all_operators_applicable s ops"
    and "are_all_operator_effects_consistent ops"
    and "op \<in> set ops"
    and "v \<in> set (add_effects_of op)"
  shows "map_of (effect_to_assignments op) v = Some True"
  proof -
    let ?f = "\<lambda>x. if ListMem x (add_effects_of op) then True else False"
      and ?l'= " map (\<lambda>v. (v, if ListMem v (add_effects_of op) then True else False))
        (add_effects_of op @ delete_effects_of op)"
    have "set (add_effects_of op) \<noteq> {}"
      using assms(4)
      by fastforce
    moreover {
      have "set (add_effects_of op) \<inter> set (delete_effects_of op) = {}"
        using are_all_operator_effects_consistent_set assms(2, 3)
        by fast
      moreover have "effect_to_assignments op = ?l'"
        using effect_to_assignments_construction_from_function_graph(1) calculation
        by fast
      ultimately have "map_of (effect_to_assignments op) = map_of ?l'"
        by argo
    }
    ultimately have "map_of (effect_to_assignments op) v = Some (?f v)"
      using Map_Supplement.map_of_from_function_graph_is_some_if[
          of _ _ "?f", OF _ assms(4)]
      by simp
    thus ?thesis
      using ListMem_iff assms(4)
      by metis
  qed

lemma execute_parallel_operator_positive_effect_if:
  fixes ops
  assumes "are_all_operators_applicable s ops"
    and "are_all_operator_effects_consistent ops"
    and "op \<in> set ops"
    and "v \<in> set (add_effects_of op)"
  shows "execute_parallel_operator s ops v = Some True"
  proof -
    let ?l = "map (map_of \<circ> effect_to_assignments) ops"
    have set_l_is: "set ?l = (map_of \<circ> effect_to_assignments) ` set ops"
      using set_map
      by fastforce
    {
      let ?m = "(map_of \<circ> effect_to_assignments) op"
      have "?m \<in> set ?l"
        using assms(3) set_l_is
        by blast
      moreover have "?m v = Some True"
        using execute_parallel_operator_positive_effect_if_i[OF assms]
        by fastforce
      ultimately have "\<exists>m \<in> set ?l. m v = Some True"
        by blast
    }
    moreover {
      fix m'
      assume "m' \<in> set ?l"
      then obtain op'
        where op'_in_set_ops: "op' \<in> set ops"
          and m'_is: "m' = (map_of \<circ> effect_to_assignments) op'"
        by auto
      then have "set (add_effects_of op) \<inter> set (delete_effects_of op') = {}"
        using assms(2, 3) are_all_operator_effects_consistent_set[of ops]
        by blast
      then have "v \<notin> set (delete_effects_of op')"
        using assms(4)
        by blast
      then consider (v_in_set_add_effects) "v \<in> set (add_effects_of op')"
        | (otherwise) "\<not>v \<in> set (add_effects_of op') \<and> \<not>v \<in> set (delete_effects_of op')"
        by blast
      hence "m' v = Some True \<or> m' v = None"
        proof (cases)
          case v_in_set_add_effects
          \<comment> \<open> TODO slow. \<close>
          thus ?thesis
            using execute_parallel_operator_positive_effect_if_i[
                OF assms(1, 2) op'_in_set_ops, of v] m'_is
            by simp
        next
          case otherwise
          then have "\<not>v \<in> set (add_effects_of op')"
            and "\<not>v \<in> set (delete_effects_of op')"
            by blast+
          thus ?thesis
            using map_of_effect_to_assignments_is_none_if[of v op'] m'_is
            by fastforce
        qed
    }
    \<comment> \<open> TODO slow. \<close>
    ultimately show ?thesis
      unfolding execute_parallel_operator_def
      using foldl_map_append_is_some_if[of s v True ?l]
      by meson
  qed

lemma execute_parallel_operator_negative_effect_if_i:
  assumes "are_all_operators_applicable s ops"
    and "are_all_operator_effects_consistent ops"
    and "op \<in> set ops"
    and "v \<in> set (delete_effects_of op)"
  shows "map_of (effect_to_assignments op) v = Some False"
  proof -
    let ?f = "\<lambda>x. if ListMem x (delete_effects_of op) then False else True"
      and ?l'= " map (\<lambda>v. (v, if ListMem v (delete_effects_of op) then False else True))
        (add_effects_of op @ delete_effects_of op)"
    have "set (delete_effects_of op @ add_effects_of op) \<noteq> {}"
      using assms(4)
      by fastforce
    moreover have "v \<in> set (delete_effects_of op @ add_effects_of op)"
      using assms(4)
      by simp
    moreover {
      have "set (add_effects_of op) \<inter> set (delete_effects_of op) = {}"
        using are_all_operator_effects_consistent_set assms(2, 3)
        by fast
      moreover have "effect_to_assignments op = ?l'"
        using effect_to_assignments_construction_from_function_graph(2) calculation
        by blast
      ultimately have "map_of (effect_to_assignments op) = map_of ?l'"
        by argo
    }
    ultimately have "map_of (effect_to_assignments op) v = Some (?f v)"
      using Map_Supplement.map_of_from_function_graph_is_some_if[
          of "add_effects_of op @ delete_effects_of op" v "?f"]
      by force
    thus ?thesis
      using assms(4)
      unfolding ListMem_iff
      by presburger
  qed

lemma execute_parallel_operator_negative_effect_if:
  assumes "are_all_operators_applicable s ops"
    and "are_all_operator_effects_consistent ops"
    and "op \<in> set ops"
    and "v \<in> set (delete_effects_of op)"
  shows "execute_parallel_operator s ops v = Some False"
  proof -
    let ?l = "map (map_of \<circ> effect_to_assignments) ops"
    have set_l_is: "set ?l = (map_of \<circ> effect_to_assignments) ` set ops"
      using set_map
      by fastforce
    {
      let ?m = "(map_of \<circ> effect_to_assignments) op"
      have "?m \<in> set ?l"
        using assms(3) set_l_is
        by blast
      moreover have "?m v = Some False"
        using execute_parallel_operator_negative_effect_if_i[OF assms]
        by fastforce
      ultimately have "\<exists>m \<in> set ?l. m v = Some False"
        by blast
    }
    moreover {
      fix m'
      assume "m' \<in> set ?l"
      then obtain op'
        where op'_in_set_ops: "op' \<in> set ops"
          and m'_is: "m' = (map_of \<circ> effect_to_assignments) op'"
        by auto
      then have "set (delete_effects_of op) \<inter> set (add_effects_of op') = {}"
        using assms(2, 3) are_all_operator_effects_consistent_set[of ops]
        by blast
      then have "v \<notin> set (add_effects_of op')"
        using assms(4)
        by blast
      then consider (v_in_set_delete_effects) "v \<in> set (delete_effects_of op')"
        | (otherwise) "\<not>v \<in> set (add_effects_of op') \<and> \<not>v \<in> set (delete_effects_of op')"
        by blast
      hence "m' v = Some False \<or> m' v = None"
        proof (cases)
          case v_in_set_delete_effects
          \<comment> \<open> TODO slow. \<close>
          thus ?thesis
            using execute_parallel_operator_negative_effect_if_i[
                OF assms(1, 2) op'_in_set_ops, of v] m'_is
            by simp
        next
          case otherwise
          then have "\<not>v \<in> set (add_effects_of op')"
            and "\<not>v \<in> set (delete_effects_of op')"
            by blast+
          thus ?thesis
            using map_of_effect_to_assignments_is_none_if[of v op'] m'_is
            by fastforce
        qed
    }
    \<comment> \<open> TODO slow. \<close>
    ultimately show ?thesis
      unfolding execute_parallel_operator_def
      using foldl_map_append_is_some_if[of s v False ?l]
      by meson
  qed

lemma execute_parallel_operator_no_effect_if:
  assumes "\<forall>op \<in> set ops. \<not>v \<in> set (add_effects_of op) \<and> \<not>v \<in> set (delete_effects_of op)"
  shows "execute_parallel_operator s ops v = s v"
  using assms
  unfolding execute_parallel_operator_def
  proof (induction ops arbitrary: s)
    case (Cons a ops)
    let ?f = "map_of \<circ> effect_to_assignments"
    {
      have "v \<notin> set (add_effects_of a) \<and> v \<notin> set (delete_effects_of a)"
        using Cons.prems(1)
        by force
      then have "?f a v = None"
        using map_of_effect_to_assignments_is_none_if[of v a]
        by fastforce
      then have "v \<notin> dom (?f a)"
        by blast
      hence "(s ++ ?f a) v = s v"
        using map_add_dom_app_simps(3)[of v "?f a" s]
        by blast
    }
    moreover {
      have "\<forall>op\<in>set ops. v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op)"
        using Cons.prems(1)
        by simp
      hence "foldl (++) (s ++ ?f a) (map ?f ops) v = (s ++ ?f a) v"
        using Cons.IH[of "s ++ ?f a"]
        by blast
    }
    moreover {
      have "map ?f (a # ops) = ?f a # map ?f ops"
        by force
      then have "foldl (++) s (map ?f (a # ops))
        = foldl (++) (s ++ ?f a) (map ?f ops)"
        using foldl_Cons
        by force
    }
    ultimately show ?case
      by argo
  qed fastforce

corollary execute_parallel_operators_strips_none_if:
  assumes "\<forall>op \<in> set ops. \<not>v \<in> set (add_effects_of op) \<and> \<not>v \<in> set (delete_effects_of op)"
    and "s v = None"
  shows "execute_parallel_operator s ops v = None"
  using execute_parallel_operator_no_effect_if[OF assms(1)] assms(2)
  by simp

corollary execute_parallel_operators_strips_none_if_contraposition:
  assumes "\<not>execute_parallel_operator s ops v = None"
  shows "(\<exists>op \<in> set ops. v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op))
    \<or> s v \<noteq> None"
  proof -
    let ?P = "(\<forall>op \<in> set ops. \<not>v \<in> set (add_effects_of op) \<and> \<not>v \<in> set (delete_effects_of op))
      \<and> s v = None"
      and ?Q = "execute_parallel_operator s ops v = None"
    have "?P \<Longrightarrow> ?Q"
      using execute_parallel_operators_strips_none_if[of ops v s]
      by blast
    then have "\<not>?P"
      using contrapos_nn[of ?Q ?P]
      using assms
      by argo
    thus ?thesis
      by meson
  qed

text \<open> We will now move on to showing the equivalent to theorem \isaname{operator_effect__strips}
in \isaname{execute_parallel_operator_effect}.
Under the condition that for a list of operators \<^term>\<open>ops\<close> all
operators in the corresponding set are applicable in a given state \<^term>\<open>s\<close> and all operator effects
are consistent, if an operator \<^term>\<open>op\<close> exists with \<^term>\<open>op \<in> set ops\<close> and with \<^term>\<open>v\<close> being
an add effect of \<^term>\<open>op\<close>, then the successor state

  @{text[display, indent=4] "s' \<equiv> execute_parallel_operator s ops"}

will evaluate \<^term>\<open>v\<close> to true, that is

  @{text[display, indent=4] "execute_parallel_operator s ops v = Some True"}

Symmetrically, if \<^term>\<open>v\<close> is a delete effect, we have

  @{text[display, indent=4] "execute_parallel_operator s ops v = Some False"}

under the same condition as for the positive effect.
Lastly, if \<^term>\<open>v\<close> is neither an add effect nor a delete effect for any operator in the
operator set corresponding to $ops$, then the state after parallel operator execution remains
unchanged, i.e.

  @{text[display, indent=4] "execute_parallel_operator s ops v = s v"}
\<close>

theorem  execute_parallel_operator_effect:
  assumes "are_all_operators_applicable s ops"
  and "are_all_operator_effects_consistent ops"
shows "op \<in> set ops \<and> v \<in> set (add_effects_of op)
  \<longrightarrow> execute_parallel_operator s ops v = Some True"
  and "op \<in> set ops \<and> v \<in> set (delete_effects_of op)
    \<longrightarrow> execute_parallel_operator s ops v = Some False"
  and "(\<forall>op \<in> set ops.
    v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op))
    \<longrightarrow> execute_parallel_operator s ops v = s v"
  using execute_parallel_operator_positive_effect_if[OF assms]
    execute_parallel_operator_negative_effect_if[OF assms]
    execute_parallel_operator_no_effect_if[of ops v s]
  by blast+


lemma is_parallel_solution_for_problem_operator_set:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "ops \<in> set \<pi>"
    and "op \<in> set ops"
  shows "op \<in> set ((\<Pi>)\<^sub>\<O>)"
  proof -
    have "\<forall>ops \<in> set \<pi>. \<forall>op \<in> set ops. op \<in> set (strips_problem.operators_of \<Pi>)"
      using assms(1)
      unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff..
    thus ?thesis
      using assms(2, 3)
      by fastforce
  qed

lemma trace_parallel_plan_strips_not_nil: "trace_parallel_plan_strips I \<pi> \<noteq> []"
  proof (cases \<pi>)
    case (Cons a list)
    then show ?thesis
      by (cases "are_all_operators_applicable I (hd \<pi>) \<and> are_all_operator_effects_consistent (hd \<pi>)"
        , simp+)
  qed simp

corollary length_trace_parallel_plan_gt_0[simp]: "0 < length (trace_parallel_plan_strips I \<pi>)"
  using trace_parallel_plan_strips_not_nil..

corollary length_trace_minus_one_lt_length_trace[simp]:
  "length (trace_parallel_plan_strips I \<pi>) - 1 < length (trace_parallel_plan_strips I \<pi>)"
  using diff_less[OF _ length_trace_parallel_plan_gt_0]
  by auto

lemma trace_parallel_plan_strips_head_is_initial_state:
  "trace_parallel_plan_strips I \<pi> ! 0 = I"
  proof  (cases \<pi>)
    case (Cons a list)
    then show ?thesis
      by (cases "are_all_operators_applicable I a \<and> are_all_operator_effects_consistent a", simp+)
  qed simp

lemma trace_parallel_plan_strips_length_gt_one_if:
  assumes "k < length (trace_parallel_plan_strips I \<pi>) - 1"
  shows "1 < length (trace_parallel_plan_strips I \<pi>)"
  using assms
  by linarith

\<comment> \<open> This lemma simply shows that the last element of a \<open>trace_parallel_plan_strips execution\<close>
\<open>step s # trace_parallel_plan_strips s' \<pi>\<close> always is the last element of
\<open>trace_parallel_plan_strips s' \<pi>\<close> since \<open>trace_parallel_plan_strips\<close> always returns at least a
singleton list (even if \<open>\<pi> = []\<close>). \<close>
lemma trace_parallel_plan_strips_last_cons_then:
  "last (s # trace_parallel_plan_strips s' \<pi>) = last (trace_parallel_plan_strips s' \<pi>)"
  by (cases \<pi>, simp, force)

text \<open> Parallel plan traces have some important properties that we want to confirm before
proceeding. Let \<^term>\<open>\<tau> \<equiv> trace_parallel_plan_strips I \<pi>\<close> be a trace for a parallel plan \<^term>\<open>\<pi>\<close>
with initial state \<^term>\<open>I\<close>.

First, all parallel operators \<^term>\<open>ops = \<pi> ! k\<close> for any index \<^term>\<open>k\<close> with \<^term>\<open>k < length \<tau> - 1\<close>
(meaning that \<^term>\<open>k\<close> is not the index of the last element).
must be applicable and their effects must be consistent. Otherwise, the trace would have terminated
and \<^term>\<open>ops\<close> would have been the last element. This would violate the assumption that \<^term>\<open>k < length \<tau> - 1\<close>
is not the last index since the index of the last element is \<^term>\<open>length \<tau> - 1\<close>.
\footnote{More precisely, the index of the last element is \<^term>\<open>length \<tau> - 1\<close> if \<^term>\<open>\<tau>\<close> is not
empty which is however always true since the trace contains at least the initial state.} \<close>

(* TODO? hide? *)
lemma  trace_parallel_plan_strips_operator_preconditions:
  assumes "k < length (trace_parallel_plan_strips I \<pi>) - 1"
  shows "are_all_operators_applicable (trace_parallel_plan_strips I \<pi> ! k) (\<pi> ! k)
      \<and> are_all_operator_effects_consistent (\<pi> ! k)"
  using assms
  proof  (induction "\<pi>" arbitrary: I k)
    \<comment> \<open> NOTE Base case yields contradiction with assumption and can be left to automation. \<close>
    case (Cons a \<pi>)
    then show ?case
      proof (cases "are_all_operators_applicable I a \<and> are_all_operator_effects_consistent a")
        case True
        have trace_parallel_plan_strips_cons: "trace_parallel_plan_strips I (a # \<pi>)
          = I # trace_parallel_plan_strips (execute_parallel_operator I a) \<pi>"
          using True
          by simp
        then show ?thesis
        proof (cases "k")
          case 0
          have "trace_parallel_plan_strips I (a # \<pi>) ! 0 = I"
            using trace_parallel_plan_strips_cons
            by simp
          moreover have "(a # \<pi>) ! 0 = a"
            by simp
          ultimately show ?thesis
            using True 0
            by presburger
        next
          case (Suc k')
          let ?I' = "execute_parallel_operator I a"
          have "trace_parallel_plan_strips I (a # \<pi>) ! Suc k' = trace_parallel_plan_strips ?I' \<pi> ! k'"
            using trace_parallel_plan_strips_cons
            by simp
          moreover have "(a # \<pi>) ! Suc k' = \<pi> ! k'"
            by simp
          moreover {
            have "length (trace_parallel_plan_strips I (a # \<pi>))
              = 1 + length (trace_parallel_plan_strips ?I' \<pi>)"
              unfolding trace_parallel_plan_strips_cons
              by simp
            then have "k' < length (trace_parallel_plan_strips ?I' \<pi>) - 1"
              using Suc Cons.prems
              by fastforce
            hence "are_all_operators_applicable (trace_parallel_plan_strips ?I' \<pi> ! k') (\<pi> ! k')
            \<and> are_all_operator_effects_consistent (\<pi> ! k')"
              using Cons.IH[of k']
              by blast
          }
          ultimately show ?thesis
            using Suc
            by argo
        qed
      next
        case False
        then have "trace_parallel_plan_strips I (a # \<pi>) = [I]"
          by force
        then have "length (trace_parallel_plan_strips I (a # \<pi>)) - 1 = 0"
          by simp
        \<comment> \<open> NOTE Thesis follows from contradiction with assumption. \<close>
        then show ?thesis
          using Cons.prems
          by force
      qed
  qed auto

text \<open> Another interesting property that we verify below is that elements of the trace
store the result of plan prefix execution. This means that for an index \<^term>\<open>k\<close> with\newline
\<^term>\<open>k < length (trace_parallel_plan_strips I \<pi>)\<close>, the \<^term>\<open>k\<close>-th element of the trace is state
reached by executing the plan prefix \<^term>\<open>take k \<pi>\<close> consisting of the first \<^term>\<open>k\<close> parallel
operators of \<^term>\<open>\<pi>\<close>. \<close>

lemma  trace_parallel_plan_plan_prefix:
  assumes "k < length (trace_parallel_plan_strips I \<pi>)"
  shows "trace_parallel_plan_strips I \<pi> ! k = execute_parallel_plan I (take k \<pi>)"
  using assms
  proof  (induction \<pi> arbitrary: I k)
    case (Cons a \<pi>)
    then show ?case
      proof (cases "are_all_operators_applicable I a \<and> are_all_operator_effects_consistent a")
        case True
        let ?\<sigma> = "trace_parallel_plan_strips I (a # \<pi>)"
          and ?I' = "execute_parallel_operator I a"
        have \<sigma>_equals: "?\<sigma> = I # trace_parallel_plan_strips ?I' \<pi>"
          using True
          by auto
        then show ?thesis
          proof (cases "k = 0")
            case False
            obtain k' where k_is_suc_of_k': "k = Suc k'"
              using not0_implies_Suc[OF False]
              by blast
            then have "execute_parallel_plan I (take k (a # \<pi>))
              = execute_parallel_plan ?I' (take k' \<pi>)"
              using True
              by simp
            moreover have "trace_parallel_plan_strips I (a # \<pi>) ! k
              = trace_parallel_plan_strips ?I' \<pi> ! k'"
              using \<sigma>_equals k_is_suc_of_k'
              by simp
            moreover {
              have "k' < length (trace_parallel_plan_strips (execute_parallel_operator I a) \<pi>)"
                using Cons.prems \<sigma>_equals k_is_suc_of_k'
                by force
              hence "trace_parallel_plan_strips ?I' \<pi> ! k'
                = execute_parallel_plan ?I' (take k' \<pi>)"
                using Cons.IH[of k' ?I']
                by blast
            }
            ultimately show ?thesis
              by presburger
          qed simp
      next
        case operator_precondition_violated: False
        then show ?thesis
        proof (cases "k = 0")
          case False
          then have "trace_parallel_plan_strips I (a # \<pi>) = [I]"
            using operator_precondition_violated
            by force
          moreover have "execute_parallel_plan I (take k (a # \<pi>)) = I"
            using Cons.prems operator_precondition_violated
            by force
          ultimately show ?thesis
            using Cons.prems nth_Cons_0
            by auto
        qed simp
      qed
  qed simp


lemma length_trace_parallel_plan_strips_lte_length_plan_plus_one:
  shows "length (trace_parallel_plan_strips I \<pi>) \<le> length \<pi> + 1"
  proof (induction \<pi> arbitrary: I)
    case (Cons a \<pi>)
    then show ?case
      proof (cases "are_all_operators_applicable I a \<and> are_all_operator_effects_consistent a")
        case True
        let ?I' = "execute_parallel_operator I a"
        {
          have "trace_parallel_plan_strips I (a # \<pi>) = I # trace_parallel_plan_strips ?I' \<pi>"
            using True
            by auto
          then have "length (trace_parallel_plan_strips I (a # \<pi>))
            = length (trace_parallel_plan_strips ?I' \<pi>) + 1"
            by simp
          moreover have "length (trace_parallel_plan_strips ?I' \<pi>) \<le> length \<pi> + 1"
            using Cons.IH[of ?I']
            by blast
          ultimately have "length (trace_parallel_plan_strips I (a # \<pi>)) \<le> length (a # \<pi>) + 1"
            by simp
        }
        thus ?thesis
          by blast
      qed auto
  qed simp

\<comment> \<open> Show that \<open>\<pi>\<close> is at least a singleton list. \<close>
lemma plan_is_at_least_singleton_plan_if_trace_has_at_least_two_elements:
  assumes "k < length (trace_parallel_plan_strips I \<pi>) - 1"
  obtains ops \<pi>' where "\<pi> = ops # \<pi>'"
  proof -
    let ?\<tau> = "trace_parallel_plan_strips I \<pi>"
    have "length ?\<tau> \<le> length \<pi> + 1"
      using length_trace_parallel_plan_strips_lte_length_plan_plus_one
      by fast
    then have "0 < length \<pi>"
      using trace_parallel_plan_strips_length_gt_one_if assms
      by force
    then obtain k' where "length \<pi> = Suc k'"
      using gr0_implies_Suc
      by meson
    thus ?thesis using that
      using length_Suc_conv[of \<pi> k']
      by blast
  qed

\<comment> \<open> Show that if a parallel plan trace does not have maximum length, in the last state
reached through operator execution the parallel operator execution condition was violated. \<close>
corollary length_trace_parallel_plan_strips_lt_length_plan_plus_one_then:
  assumes "length (trace_parallel_plan_strips I \<pi>) < length \<pi> + 1"
  shows "\<not>are_all_operators_applicable
      (execute_parallel_plan I (take (length (trace_parallel_plan_strips I \<pi>) - 1) \<pi>))
      (\<pi> ! (length (trace_parallel_plan_strips I \<pi>) - 1))
    \<or> \<not>are_all_operator_effects_consistent (\<pi> ! (length (trace_parallel_plan_strips I \<pi>) - 1))"
  using assms
  proof (induction \<pi> arbitrary: I)
    case (Cons ops \<pi>)
    let ?\<tau> = "trace_parallel_plan_strips I (ops # \<pi>)"
      and ?I' = "execute_parallel_operator I ops"
    show ?case
      proof (cases "are_all_operators_applicable I ops \<and> are_all_operator_effects_consistent ops")
        case True
        then have \<tau>_is: "?\<tau> = I # trace_parallel_plan_strips ?I' \<pi>"
          by fastforce
        show ?thesis
          proof (cases "length (trace_parallel_plan_strips ?I' \<pi>) < length \<pi> + 1")
            case True
            then have "\<not> are_all_operators_applicable
              (execute_parallel_plan ?I'
                (take (length (trace_parallel_plan_strips ?I' \<pi>) - 1) \<pi>))
              (\<pi> ! (length (trace_parallel_plan_strips ?I' \<pi>) - 1))
            \<or> \<not> are_all_operator_effects_consistent
              (\<pi> ! (length (trace_parallel_plan_strips ?I' \<pi>) - 1))"
              using Cons.IH[of ?I']
              by blast
            moreover have "trace_parallel_plan_strips ?I' \<pi> \<noteq> []"
              using trace_parallel_plan_strips_not_nil
              by blast
            ultimately show ?thesis
              unfolding take_Cons'
              by simp
          next
            case False
            then have "length (trace_parallel_plan_strips ?I' \<pi>) \<ge> length \<pi> + 1"
              by fastforce
            thm Cons.prems
            moreover have "length (trace_parallel_plan_strips I (ops # \<pi>))
              = 1 + length (trace_parallel_plan_strips ?I' \<pi>)"
              using True
              by force
            moreover have "length (trace_parallel_plan_strips ?I' \<pi>)
              < length (ops # \<pi>)"
              using Cons.prems calculation(2)
              by force
            ultimately have False
              by fastforce
            thus ?thesis..
          qed
      next
        case False
        then have \<tau>_is_singleton: "?\<tau> = [I]"
          using False
          by auto
        then have "ops = (ops # \<pi>) ! (length ?\<tau> - 1)"
          by fastforce
        moreover have "execute_parallel_plan I (take (length ?\<tau> - 1) \<pi>) = I"
          using \<tau>_is_singleton
          by auto
        \<comment> \<open> TODO slow. \<close>
        ultimately show ?thesis
          using False
          by auto
      qed
  qed simp

lemma trace_parallel_plan_step_effect_is:
  assumes "k < length (trace_parallel_plan_strips I \<pi>) - 1"
  shows "trace_parallel_plan_strips I \<pi> ! Suc k
    = execute_parallel_operator (trace_parallel_plan_strips I \<pi> ! k) (\<pi> ! k)"
  proof -
    \<comment> \<open> NOTE Rewrite the proposition using lemma \<open>trace_parallel_plan_strips_subplan\<close>. \<close>
    {
      let ?\<tau> = "trace_parallel_plan_strips I \<pi>"
      have "Suc k < length ?\<tau>"
        using assms
        by linarith
      hence "trace_parallel_plan_strips I \<pi> ! Suc k
        = execute_parallel_plan I (take (Suc k) \<pi>)"
        using trace_parallel_plan_plan_prefix[of "Suc k" I \<pi>]
        by blast
    }
    moreover have "execute_parallel_plan I (take (Suc k) \<pi>)
      = execute_parallel_operator (trace_parallel_plan_strips I \<pi> ! k) (\<pi> ! k)"
      using assms
      proof (induction k arbitrary: I \<pi>)
        case 0
        then have "execute_parallel_operator (trace_parallel_plan_strips I \<pi> ! 0) (\<pi> ! 0)
            = execute_parallel_operator I (\<pi> ! 0)"
          using trace_parallel_plan_strips_head_is_initial_state[of I \<pi>]
          by argo
        moreover {
          obtain ops \<pi>' where "\<pi> = ops # \<pi>'"
            using plan_is_at_least_singleton_plan_if_trace_has_at_least_two_elements[OF "0.prems"]
            by blast
          then have "take (Suc 0) \<pi> = [\<pi> ! 0]"
            by simp
          hence "execute_parallel_plan I (take (Suc 0) \<pi>)
            = execute_parallel_plan I [\<pi> ! 0]"
            by argo
        }
        moreover {
          have "0 < length (trace_parallel_plan_strips I \<pi>) - 1"
            using trace_parallel_plan_strips_length_gt_one_if "0.prems"
            by fastforce
          hence "are_all_operators_applicable I (\<pi> ! 0)
            \<and> are_all_operator_effects_consistent (\<pi> ! 0)"
            using trace_parallel_plan_strips_operator_preconditions[of 0 I \<pi>]
              trace_parallel_plan_strips_head_is_initial_state[of I \<pi>]
            by argo
        }
        ultimately show ?case
          by auto
      next
        case (Suc k)
        obtain ops \<pi>' where \<pi>_split: "\<pi> = ops # \<pi>'"
          using plan_is_at_least_singleton_plan_if_trace_has_at_least_two_elements[OF Suc.prems]
          by blast
        let ?I' = "execute_parallel_operator I ops"
        {
          have "length (trace_parallel_plan_strips I \<pi>) =
            1 + length (trace_parallel_plan_strips ?I' \<pi>')"
            using Suc.prems \<pi>_split
            by fastforce
          then have "k < length (trace_parallel_plan_strips ?I' \<pi>')"
            using Suc.prems
            by fastforce
          moreover have "trace_parallel_plan_strips I \<pi> ! Suc k
            = trace_parallel_plan_strips ?I' \<pi>' ! k"
            using Suc.prems \<pi>_split
            by force
          ultimately have "trace_parallel_plan_strips I \<pi> ! Suc k
            = execute_parallel_plan ?I' (take k \<pi>')"
            using trace_parallel_plan_plan_prefix[of k ?I' \<pi>']
            by argo
        }
        moreover have "execute_parallel_plan I (take (Suc (Suc k)) \<pi>)
          = execute_parallel_plan ?I' (take (Suc k) \<pi>')"
          using Suc.prems \<pi>_split
          by fastforce
        moreover {
          have "0 < length (trace_parallel_plan_strips I \<pi>) - 1"
            using Suc.prems
            by linarith
          hence "are_all_operators_applicable I (\<pi> ! 0)
            \<and> are_all_operator_effects_consistent (\<pi> ! 0)"
            using trace_parallel_plan_strips_operator_preconditions[of 0 I \<pi>]
              trace_parallel_plan_strips_head_is_initial_state[of I \<pi>]
            by argo
        }
        ultimately show ?case
          using Suc.IH Suc.prems \<pi>_split
          by auto
      qed
    ultimately show ?thesis
      using assms
      by argo
  qed

\<comment> \<open> Show that every state in a plan execution trace of a valid problem description is defined
for all problem variables. This is true because the initial state is defined for all problem
variables—by definition of @{text "is_valid_problem_strips \<Pi>"}—and no operator can remove a
previously defined variable (only positive and negative effects are possible). \<close>
(* TODO refactor \<open>STRIPS_Semantics\<close> + abstract/concretize first two assumptions (e.g. second one
only needs all operators are problem operators)? *)
lemma trace_parallel_plan_strips_none_if:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)"
  shows "(trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = None \<longleftrightarrow> v \<notin> set ((\<Pi>)\<^sub>\<V>)"
  proof -
    let ?vs = "strips_problem.variables_of \<Pi>"
      and ?ops = "strips_problem.operators_of \<Pi>"
      and ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
      and ?I = "strips_problem.initial_of \<Pi>"
    show ?thesis
      using assms
      proof (induction k)
        case 0
        have "?\<tau> ! 0 = ?I"
          using trace_parallel_plan_strips_head_is_initial_state
          by auto
        then show ?case
          using is_valid_problem_strips_initial_of_dom[OF assms(1)]
          by auto
      next
        case (Suc k)
        have k_lt_length_\<tau>_minus_one: "k < length ?\<tau> - 1"
          using Suc.prems(3)
          by linarith
        then have IH: "(trace_parallel_plan_strips ?I \<pi> ! k) v = None \<longleftrightarrow> v \<notin>set ((\<Pi>)\<^sub>\<V>)"
          using Suc.IH[OF Suc.prems(1, 2)]
          by force
        have \<tau>_Suc_k_is: "(?\<tau> ! Suc k) = execute_parallel_operator (?\<tau> ! k) (\<pi> ! k)"
          using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one].
        have all_operators_applicable: "are_all_operators_applicable (?\<tau> ! k) (\<pi> ! k)"
          and all_effects_consistent: "are_all_operator_effects_consistent (\<pi> ! k)"
          using trace_parallel_plan_strips_operator_preconditions[OF k_lt_length_\<tau>_minus_one]
          by simp+
        show ?case
          proof (rule iffI)
            assume \<tau>_Suc_k_of_v_is_None: "(?\<tau> ! Suc k) v = None"
            show "v \<notin> set ((\<Pi>)\<^sub>\<V>)"
              proof (rule ccontr)
                assume "\<not>v \<notin> set ((\<Pi>)\<^sub>\<V>)"
                then have v_in_set_vs: "v \<in> set((\<Pi>)\<^sub>\<V>)"
                  by blast
                show False
                  proof (cases "\<exists>op \<in> set (\<pi> ! k).
                    v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op)")
                    case True
                    then obtain op
                      where op_in_\<pi>\<^sub>k: "op \<in> set (\<pi> ! k)"
                        and "v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op)"..
                    then consider (A) "v \<in> set (add_effects_of op)"
                      | (B) "v \<in> set (delete_effects_of op)"
                      by blast
                    thus False
                      using execute_parallel_operator_positive_effect_if[OF
                              all_operators_applicable all_effects_consistent op_in_\<pi>\<^sub>k]
                            execute_parallel_operator_negative_effect_if[OF
                              all_operators_applicable all_effects_consistent op_in_\<pi>\<^sub>k]
                            \<tau>_Suc_k_of_v_is_None \<tau>_Suc_k_is
                      by (cases, fastforce+)
                  next
                    case False
                    then have "\<forall>op \<in> set (\<pi> ! k).
                      v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op)"
                      by blast
                    then have "(?\<tau> ! Suc k) v = (?\<tau> ! k) v"
                      using execute_parallel_operator_no_effect_if \<tau>_Suc_k_is
                      by fastforce
                    then have "v \<notin> set ((\<Pi>)\<^sub>\<V>)"
                      using IH  \<tau>_Suc_k_of_v_is_None
                      by simp
                    thus False
                      using v_in_set_vs
                      by blast
                  qed
              qed
          next
            assume v_notin_vs: "v \<notin> set ((\<Pi>)\<^sub>\<V>)"
            {
              fix op
              assume op_in_\<pi>\<^sub>k: "op \<in> set (\<pi> ! k)"
              {
                have "1 < length ?\<tau>"
                  using trace_parallel_plan_strips_length_gt_one_if[OF k_lt_length_\<tau>_minus_one].
                then have "0 < length ?\<tau> - 1"
                  using k_lt_length_\<tau>_minus_one
                  by linarith
                moreover have "length ?\<tau> - 1 \<le> length \<pi>"
                  using length_trace_parallel_plan_strips_lte_length_plan_plus_one le_diff_conv
                  by blast
                then have "k < length \<pi>"
                  using k_lt_length_\<tau>_minus_one
                  by force
                hence "\<pi> ! k \<in> set \<pi>"
                  by simp
              }
              then have op_in_ops: "op \<in> set ?ops"
                using is_parallel_solution_for_problem_operator_set[OF assms(2) _ op_in_\<pi>\<^sub>k]
                by force
              hence "v \<notin> set (add_effects_of op)" and "v \<notin> set (delete_effects_of op)"
                subgoal
                  using is_valid_problem_strips_operator_variable_sets(2) assms(1) op_in_ops
                    v_notin_vs
                  by auto
                subgoal
                  using is_valid_problem_strips_operator_variable_sets(3) assms(1) op_in_ops
                    v_notin_vs
                  by auto
                done
            }
            then have "(?\<tau> ! Suc k) v = (?\<tau> ! k) v"
              using execute_parallel_operator_no_effect_if \<tau>_Suc_k_is
              by metis
            thus "(?\<tau> ! Suc k) v = None"
              using IH v_notin_vs
              by fastforce
          qed
      qed
  qed

text \<open> Finally, given initial and goal states \<^term>\<open>I\<close> and \<^term>\<open>G\<close>, we can show that it's
equivalent to say that \<^term>\<open>\<pi>\<close> is a solution for \<^term>\<open>I\<close> and \<^term>\<open>G\<close>---i.e.
\<^term>\<open>G \<subseteq>\<^sub>m execute_parallel_plan I \<pi>\<close>---and
that the goal state is subsumed by the last element of the trace of \<^term>\<open>\<pi>\<close> with initial state
\<^term>\<open>I\<close>. \<close>

lemma  execute_parallel_plan_reaches_goal_iff_goal_is_last_element_of_trace:
  "G \<subseteq>\<^sub>m execute_parallel_plan I \<pi>
    \<longleftrightarrow> G \<subseteq>\<^sub>m last (trace_parallel_plan_strips I \<pi>)"
  proof  -
    let ?LHS = "G \<subseteq>\<^sub>m execute_parallel_plan I \<pi>"
      and ?RHS = "G \<subseteq>\<^sub>m last (trace_parallel_plan_strips I \<pi>)"
    show ?thesis
      proof (rule iffI)
        assume ?LHS
        thus ?RHS
          proof (induction \<pi> arbitrary: I)
            \<comment> \<open> NOTE Nil case follows from simplification. \<close>
            case (Cons a \<pi>)
            thus ?case
              using Cons.prems
              proof (cases "are_all_operators_applicable I a \<and> are_all_operator_effects_consistent a")
                case True
                let ?I' = "execute_parallel_operator I a"
                {
                  have "execute_parallel_plan I (a # \<pi>) = execute_parallel_plan ?I' \<pi>"
                    using True
                    by auto
                  then have "G \<subseteq>\<^sub>m execute_parallel_plan ?I' \<pi>"
                    using Cons.prems
                    by presburger
                  hence "G \<subseteq>\<^sub>m last (trace_parallel_plan_strips ?I' \<pi>)"
                    using Cons.IH[of ?I']
                    by blast
                }
                moreover {
                  have "trace_parallel_plan_strips I (a # \<pi>)
                    = I # trace_parallel_plan_strips ?I' \<pi>"
                    using True
                    by simp
                  then have "last (trace_parallel_plan_strips I (a # \<pi>))
                    = last (I # trace_parallel_plan_strips ?I' \<pi>)"
                    by argo
                  hence "last (trace_parallel_plan_strips I (a # \<pi>))
                    = last (trace_parallel_plan_strips ?I' \<pi>)"
                    using trace_parallel_plan_strips_last_cons_then[of I ?I' \<pi>]
                    by argo
                }
                ultimately show ?thesis
                  by argo
              qed force
            qed simp
      next
        assume ?RHS
        thus ?LHS
          proof (induction \<pi> arbitrary: I)
            \<comment> \<open> NOTE Nil case follows from simplification. \<close>
            case (Cons a \<pi>)
            thus ?case
              proof (cases "are_all_operators_applicable I a \<and> are_all_operator_effects_consistent a")
                case True
                let ?I' = "execute_parallel_operator I a"
                {
                  have "trace_parallel_plan_strips I (a # \<pi>) = I # (trace_parallel_plan_strips ?I' \<pi>)"
                    using True
                    by simp
                  then have "last (trace_parallel_plan_strips I (a # \<pi>))
                    = last (trace_parallel_plan_strips ?I' \<pi>)"
                    using trace_parallel_plan_strips_last_cons_then[of I ?I' \<pi>]
                    by argo
                  hence "G \<subseteq>\<^sub>m last (trace_parallel_plan_strips ?I' \<pi>)"
                    using Cons.prems
                    by argo
                }
                thus ?thesis
                  using True Cons
                  by simp
              next
                case False
                then have "last (trace_parallel_plan_strips I (a # \<pi>)) = I"
                  and "execute_parallel_plan I (a # \<pi>) = I"
                  by (fastforce, force)
                thus ?thesis
                  using Cons.prems
                  by argo
              qed
          qed fastforce
      qed
  qed

subsection "Serializable Parallel Plans"

text \<open> With the groundwork on parallel and serial execution of STRIPS in place we can now address
the question under which conditions a parallel solution to a problem corresponds to a serial
solution and vice versa.
As we will see (in theorem \ref{isathm:embedding-serial-strips-plan}), while a serial plan can
be trivially rewritten as a parallel plan consisting of singleton operator list for each operator
in the plan, the condition for parallel plan solutions also involves non interference. \<close>


\<comment> \<open> Given that non interference implies that operator execution order can be switched
arbitrarily, it stands to reason that parallel operator execution can be serialized if non
interference is mandated in addition to the regular parallel execution condition (applicability and
effect consistency). This is in fact true as we show in the lemma below
\footnote{In the source literatur it is required that $\mathrm{app}_S(s)$ is defined which requires that
$\mathrm{app}_o(s)$ is defined for every $o \in S$. This again means that the preconditions
hold in $s$ and the set of effects is consistent which translates to the execution condition
in \<open>execute_parallel_operator\<close>.
\cite[Lemma 2.11., p.1037]{DBLP:journals/ai/RintanenHN06}

Also, the proposition \cite[Lemma 2.11., p.1037]{DBLP:journals/ai/RintanenHN06} is in fact
proposed to be true for any total ordering of the operator set but we only proof it for the
implicit total ordering induced by the specific order in the operator list of the problem
statement.} \<close>
(* TODO rename execute_parallel_operator_equals_execute_serial_if *)
lemma execute_parallel_operator_equals_execute_sequential_strips_if:
  fixes s :: "('variable, bool) state"
  assumes "are_all_operators_applicable s ops"
    and "are_all_operator_effects_consistent ops"
    and "are_all_operators_non_interfering ops"
  shows "execute_parallel_operator s ops = execute_serial_plan s ops"
  using assms
  proof (induction ops arbitrary: s)
    case Nil
    have "execute_parallel_operator s Nil
      = foldl (++) s (map (map_of \<circ> effect_to_assignments) Nil)"
      using Nil.prems(1,2)
      unfolding execute_parallel_operator_def
      by presburger
    also have "\<dots> = s"
      by simp
    finally have "execute_parallel_operator s Nil = s"
      by blast
    moreover have "execute_serial_plan s Nil = s"
      by auto
    ultimately show ?case
      by simp
  next
    case (Cons a ops)
    \<comment> \<open> NOTE Use the preceding lemmas to show that the premises hold for the sublist and use the IH
  to obtain the theorem for the sublist ops. \<close>
    have a: "is_operator_applicable_in s a"
      using are_all_operators_applicable_cons Cons.prems(1)
      by blast+
    let ?s' = "s ++ map_of (effect_to_assignments a)"
    {
      from Cons.prems
      have "are_all_operators_applicable ?s' ops"
        and "are_all_operator_effects_consistent ops"
        and "are_all_operators_non_interfering ops"
        using execute_parallel_plan_precondition_cons
        by blast+
      then have "execute_serial_plan ?s' ops
        = execute_parallel_operator ?s' ops"
        using Cons.IH
        by presburger
    }
    moreover from Cons.prems
    have "execute_parallel_operator s (Cons a ops)
      = execute_parallel_operator ?s' ops"
      using execute_parallel_operator_cons_equals_corollary
      unfolding execute_operator_def
      by simp
    moreover
    from a have "execute_serial_plan s (Cons a ops)
      = execute_serial_plan ?s' ops"
      unfolding execute_serial_plan_def execute_operator_def
        is_operator_applicable_in_def
      by fastforce
    ultimately show ?case
      by argo
  qed

lemma execute_serial_plan_split_i:
  assumes "are_all_operators_applicable s (op # \<pi>)"
    and "are_all_operators_non_interfering (op # \<pi>)"
  shows "are_all_operators_applicable (s \<then> op) \<pi>"
  using assms
  proof (induction \<pi> arbitrary: s)
    case Nil
    then show ?case
      unfolding are_all_operators_applicable_def
      by simp
  next
    case (Cons op' \<pi>)
    let ?t = "s \<then> op"
    {
      fix x
      assume "x \<in> set (op' # \<pi>)"
      moreover have "op \<in> set (op # op' # \<pi>)"
        by simp
      moreover have "\<not>are_operators_interfering op x"
        using Cons.prems(2) calculation(1)
        unfolding are_all_operators_non_interfering_def list_all_iff
        by fastforce
      moreover have "is_operator_applicable_in s op"
        using Cons.prems(1)
        unfolding are_all_operators_applicable_def list_all_iff
          is_operator_applicable_in_def
        by force
      moreover have "is_operator_applicable_in s x"
        using are_all_operators_applicable_cons(2)[OF Cons.prems(1)] calculation(1)
        unfolding are_all_operators_applicable_def list_all_iff
          is_operator_applicable_in_def
        by fast
      ultimately have "is_operator_applicable_in ?t x"
        using execute_parallel_plan_precondition_cons_i[of op x s]
        by (auto simp: execute_operator_def)
    }
    thus ?case
      using are_all_operators_applicable_cons(2)
      unfolding is_operator_applicable_in_def
        STRIPS_Representation.is_operator_applicable_in_def
        are_all_operators_applicable_def list_all_iff
      by simp
  qed

\<comment> \<open> Show that plans $\pi$ can be split into separate executions of partial plans $\pi_1$ and
$\pi_2$ with $\pi = \pi_1 @ \pi_2$, if all operators in $\pi_1$ are applicable in the given state
$s$ and there is no interference between subsequent operators in $\pi_1$. This is the case because
non interference ensures that no precondition for any operator in $\pi_1$ is negated by the
execution of a preceding operator. Note that the non interference constraint excludes partial
plans where a precondition is first violated during execution but later restored which would also
allow splitting but does not meet the non interference constraint (which must hold for all
possible executing orders). \<close>
lemma execute_serial_plan_split:
  fixes s :: "('variable, bool) state"
  assumes "are_all_operators_applicable s \<pi>\<^sub>1"
    and "are_all_operators_non_interfering \<pi>\<^sub>1"
  shows "execute_serial_plan s (\<pi>\<^sub>1 @ \<pi>\<^sub>2)
    = execute_serial_plan (execute_serial_plan s \<pi>\<^sub>1) \<pi>\<^sub>2"
  using assms
  proof (induction \<pi>\<^sub>1 arbitrary: s)
    case (Cons op \<pi>\<^sub>1)
    let ?t = "s \<then> op"
    {
      have "are_all_operators_applicable (s \<then> op) \<pi>\<^sub>1"
        using execute_serial_plan_split_i[OF Cons.prems(1, 2)].
      moreover have "are_all_operators_non_interfering \<pi>\<^sub>1"
        using are_all_operators_non_interfering_tail[OF Cons.prems(2)].
      ultimately have "execute_serial_plan ?t (\<pi>\<^sub>1 @ \<pi>\<^sub>2) =
        execute_serial_plan (execute_serial_plan ?t \<pi>\<^sub>1) \<pi>\<^sub>2"
        using Cons.IH[of ?t]
        by blast
    }
    moreover have "STRIPS_Representation.is_operator_applicable_in s op"
      using Cons.prems(1)
      unfolding are_all_operators_applicable_def list_all_iff
      by fastforce
    ultimately show ?case
      unfolding execute_serial_plan_def
      by simp
  qed simp

(* TODO refactor *)
lemma embedding_lemma_i:
  fixes I :: "('variable, bool) state"
  assumes "is_operator_applicable_in I op"
    and "are_operator_effects_consistent op op"
  shows "I \<then> op = execute_parallel_operator I [op]"
  proof -
    have "are_all_operators_applicable I [op]"
      using assms(1)
      unfolding are_all_operators_applicable_def list_all_iff is_operator_applicable_in_def
      by fastforce
    moreover have "are_all_operator_effects_consistent [op]"
      unfolding are_all_operator_effects_consistent_def list_all_iff
      using assms(2)
      by fastforce
    moreover have "are_all_operators_non_interfering [op]"
      by simp
    moreover have "I \<then> op = execute_serial_plan I [op]"
      using assms(1)
      unfolding  is_operator_applicable_in_def
      by (simp add: assms(1) execute_operator_def)
    ultimately show ?thesis
      using execute_parallel_operator_equals_execute_sequential_strips_if
      by force
  qed

lemma execute_serial_plan_is_execute_parallel_plan_ii:
  fixes I :: "'variable strips_state"
  assumes "\<forall>op \<in> set \<pi>. are_operator_effects_consistent op op"
    and "G \<subseteq>\<^sub>m execute_serial_plan I \<pi>"
  shows "G \<subseteq>\<^sub>m execute_parallel_plan I (embed \<pi>)"
  proof -
    show ?thesis
      using assms
      proof (induction \<pi> arbitrary: I)
        case (Cons op \<pi>)
        then show ?case
          proof (cases "is_operator_applicable_in I op")
            case True
            let ?J = "I \<then> op"
              and ?J' = "execute_parallel_operator I [op]"
            {
              have "G \<subseteq>\<^sub>m execute_serial_plan ?J \<pi>"
                using Cons.prems(2) True
                unfolding is_operator_applicable_in_def
                by (simp add: True)
              hence "G \<subseteq>\<^sub>m execute_parallel_plan ?J (embed \<pi>)"
                using Cons.IH[of ?J] Cons.prems(1)
                by fastforce
            }
            moreover {
              have "are_all_operators_applicable I [op]"
                using True
                unfolding are_all_operators_applicable_def list_all_iff
                  is_operator_applicable_in_def
                by fastforce
              moreover have "are_all_operator_effects_consistent [op]"
                unfolding are_all_operator_effects_consistent_def list_all_iff
                using Cons.prems(1)
                by fastforce
              moreover have "?J = ?J'"
                using execute_parallel_operator_equals_execute_sequential_strips_if[OF
                    calculation(1, 2)] Cons.prems(1) True
                unfolding  is_operator_applicable_in_def
                by (simp add: True)
              ultimately have "execute_parallel_plan I (embed (op # \<pi>))
                = execute_parallel_plan ?J (embed \<pi>)"
                by fastforce
            }
            ultimately show ?thesis
              by presburger
          next
            case False
            then have "G \<subseteq>\<^sub>m I"
              using Cons.prems is_operator_applicable_in_def
              by simp
            moreover {
              have "\<not>are_all_operators_applicable I [op]"
                using False
                unfolding are_all_operators_applicable_def list_all_iff
                  is_operator_applicable_in_def
                by force
              hence "execute_parallel_plan I (embed (op # \<pi>)) = I"
                by simp
            }
            ultimately show ?thesis
              by presburger
          qed
      qed simp
  qed

lemma embedding_lemma_iii:
  fixes \<Pi>:: "'a strips_problem"
  assumes "\<forall>op \<in> set \<pi>. op \<in> set ((\<Pi>)\<^sub>\<O>)"
  shows "\<forall>ops \<in> set (embed \<pi>). \<forall>op \<in> set ops. op \<in> set ((\<Pi>)\<^sub>\<O>)"
  proof -
    (* TODO refactor *)
    have nb: "set (embed \<pi>) = { [op] | op. op \<in> set \<pi> }"
      by (induction \<pi>; force)
    {
      fix ops
      assume "ops \<in> set (embed \<pi>)"
      moreover obtain op where "op \<in> set \<pi>" and "ops = [op]"
        using nb calculation
        by blast
      ultimately have "\<forall>op \<in> set ops. op \<in> set ((\<Pi>)\<^sub>\<O>)"
        using assms(1)
        by simp
    }
    thus ?thesis..
  qed

text \<open> We show in the following theorem that---as mentioned---a serial solution \<^term>\<open>\<pi>\<close> to a
STRIPS problem \<^term>\<open>\<Pi>\<close> corresponds directly to a parallel solution obtained by embedding each operator
in \<^term>\<open>\<pi>\<close> in a list (by use of function \<^term>\<open>embed\<close>). The proof shows this by first
confirming that

    @{text[display, indent=4] "G \<subseteq>\<^sub>m execute_serial_plan ((\<Pi>)\<^sub>I) \<pi>
    \<Longrightarrow> G \<subseteq>\<^sub>m execute_serial_plan ((\<Pi>)\<^sub>I) (embed \<pi>)"}

using lemma \isaname{execute_serial_plan_is_execute_parallel_plan_strip_ii}; and
moreover by showing that

    @{text[display, indent=4] "\<forall>ops \<in> set (embed \<pi>). \<forall>op \<in> set ops. op \<in> (\<Pi>)\<^sub>\<O>"}

meaning that under the given assumptions, all parallel operators of the embedded serial plan are
again operators in the operator set of the problem. \<close>
theorem  embedding_lemma:
  assumes "is_valid_problem_strips \<Pi>"
    and "is_serial_solution_for_problem \<Pi> \<pi>"
  shows "is_parallel_solution_for_problem \<Pi> (embed \<pi>)"
  proof  -
    (* TODO refactor \<open>STRIPS_Representation\<close> (characterization of valid operator).
  *)have nb\<^sub>1: "\<forall>op \<in> set \<pi>. op \<in> set ((\<Pi>)\<^sub>\<O>)"
      using assms(2)
      unfolding is_serial_solution_for_problem_def list_all_iff ListMem_iff operators_of_def
      by blast
    (* TODO refactor lemma is_valid_operator_strips_then
  *)      {
      fix op
      assume "op \<in> set \<pi>"
      moreover have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
        using nb\<^sub>1 calculation
        by fast
      moreover have "is_valid_operator_strips \<Pi> op"
        using assms(1) calculation(2)
        unfolding is_valid_problem_strips_def is_valid_problem_strips_def list_all_iff operators_of_def
        by meson
      moreover have "list_all (\<lambda>v. \<not>ListMem v (delete_effects_of op)) (add_effects_of op)"
        and "list_all (\<lambda>v. \<not>ListMem v (add_effects_of op)) (delete_effects_of op)"
        using calculation(3)
        unfolding is_valid_operator_strips_def
        by meson+
      moreover have "\<not>list_ex (\<lambda>v. ListMem v (delete_effects_of op)) (add_effects_of op)"
        and "\<not>list_ex (\<lambda>v. ListMem v (add_effects_of op)) (delete_effects_of op)"
        using calculation(4, 5) not_list_ex_equals_list_all_not
        by blast+
      moreover have "\<not>list_ex (\<lambda>v. list_ex ((=) v) (delete_effects_of op)) (add_effects_of op)"
        and "\<not>list_ex (\<lambda>v. list_ex ((=) v) (add_effects_of op)) (delete_effects_of op)"
        using calculation(6, 7)
        unfolding list_ex_iff ListMem_iff
        by blast+
      ultimately have "are_operator_effects_consistent op op"
        unfolding are_operator_effects_consistent_def Let_def
        by blast
    } note nb\<^sub>2 = this
    moreover {
      have "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_serial_plan ((\<Pi>)\<^sub>I) \<pi>"
        using assms(2)
        unfolding is_serial_solution_for_problem_def
        by simp
      hence "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) (embed \<pi>)"
        using execute_serial_plan_is_execute_parallel_plan_ii nb\<^sub>2
        by blast
    }
    moreover have "\<forall>ops \<in> set (embed \<pi>). \<forall>op \<in> set ops. op \<in> set ((\<Pi>)\<^sub>\<O>)"
      using embedding_lemma_iii[OF nb\<^sub>1].
    ultimately show ?thesis
      unfolding is_parallel_solution_for_problem_def goal_of_def
        initial_of_def operators_of_def list_all_iff ListMem_iff
      by blast
  qed

lemma flattening_lemma_i:
  fixes \<Pi>:: "'a strips_problem"
  assumes "\<forall>ops \<in> set \<pi>. \<forall>op \<in> set ops. op \<in> set ((\<Pi>)\<^sub>\<O>)"
  shows "\<forall>op \<in> set (concat \<pi>). op \<in> set ((\<Pi>)\<^sub>\<O>)"
  proof -
    {
      fix op
      assume "op \<in> set (concat \<pi>)"
      moreover have "op \<in> (\<Union>ops \<in> set \<pi>. set ops)"
        using calculation
        unfolding set_concat.
      then obtain ops where "ops \<in> set \<pi>" and "op \<in> set ops"
        using UN_iff
        by blast
      ultimately have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
        using assms
        by blast
    }
    thus ?thesis..
  qed

lemma flattening_lemma_ii:
  fixes I :: "'variable strips_state"
  assumes "\<forall>ops \<in> set \<pi>. \<exists>op. ops = [op] \<and> is_valid_operator_strips \<Pi> op "
    and "G \<subseteq>\<^sub>m execute_parallel_plan I \<pi>"
  shows "G \<subseteq>\<^sub>m execute_serial_plan I (concat \<pi>)"
  proof -
    let ?\<pi>' = "concat \<pi>"
    (* TODO refactor lemma is_valid_operator_strips_then *)
    {
      fix op
      assume "is_valid_operator_strips \<Pi> op"
      moreover have "list_all (\<lambda>v. \<not>ListMem v (delete_effects_of op)) (add_effects_of op)"
        and "list_all (\<lambda>v. \<not>ListMem v (add_effects_of op)) (delete_effects_of op)"
        using calculation(1)
        unfolding is_valid_operator_strips_def
        by meson+
      moreover have "\<not>list_ex (\<lambda>v. ListMem v (delete_effects_of op)) (add_effects_of op)"
        and "\<not>list_ex (\<lambda>v. ListMem v (add_effects_of op)) (delete_effects_of op)"
        using calculation(2, 3) not_list_ex_equals_list_all_not
        by blast+
      moreover have "\<not>list_ex (\<lambda>v. list_ex ((=) v) (delete_effects_of op)) (add_effects_of op)"
        and "\<not>list_ex (\<lambda>v. list_ex ((=) v) (add_effects_of op)) (delete_effects_of op)"
        using calculation(4, 5)
        unfolding list_ex_iff ListMem_iff
        by blast+
      ultimately have "are_operator_effects_consistent op op"
        unfolding are_operator_effects_consistent_def Let_def
        by blast
    } note nb\<^sub>1 = this
    show ?thesis
      using assms
      proof (induction \<pi> arbitrary: I)
        case (Cons ops \<pi>)
        obtain op where ops_is: "ops = [op]" and is_valid_op: "is_valid_operator_strips \<Pi> op"
          using Cons.prems(1)
          by fastforce
        show ?case
          proof (cases "are_all_operators_applicable I ops")
            case True
            let ?J = "execute_parallel_operator I [op]"
              and ?J' = "I \<then> op"
            have nb\<^sub>2: "is_operator_applicable_in I op"
              using True ops_is
              unfolding are_all_operators_applicable_def list_all_iff
                is_operator_applicable_in_def
              by simp
            have nb\<^sub>3: "are_operator_effects_consistent op op"
              using nb\<^sub>1[OF is_valid_op].
            {
              then have "are_all_operator_effects_consistent ops"
                unfolding are_all_operator_effects_consistent_def list_all_iff
                using ops_is
                by fastforce
              hence "G \<subseteq>\<^sub>m execute_parallel_plan ?J \<pi>"
                using Cons.prems(2) ops_is True
                by fastforce
            }
            moreover have "execute_serial_plan I (concat (ops # \<pi>))
              = execute_serial_plan ?J' (concat \<pi>)"
              using ops_is nb\<^sub>2
              unfolding is_operator_applicable_in_def
              by (simp add: execute_operator_def nb\<^sub>2)
            moreover have "?J = ?J'"
              unfolding execute_parallel_operator_def execute_operator_def comp_apply
              by fastforce
            ultimately show ?thesis
              using Cons.IH Cons.prems
              by force
          next
            case False
            moreover have "G \<subseteq>\<^sub>m I"
              using Cons.prems(2) calculation
              by force
            moreover {
              have "\<not>is_operator_applicable_in I op"
                using ops_is False
                unfolding are_all_operators_applicable_def list_all_iff
                  is_operator_applicable_in_def
                by fastforce
              hence "execute_serial_plan I (concat (ops # \<pi>)) = I"
                using ops_is is_operator_applicable_in_def
                by simp
            }
            ultimately show ?thesis
              by argo
          qed
      qed force
  qed

text \<open> The opposite direction is also easy to show if we can normalize the parallel plan to the
form of an embedded serial plan as shown below. \<close>

lemma flattening_lemma:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<forall>ops \<in> set \<pi>. \<exists>op. ops = [op]"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
  shows "is_serial_solution_for_problem \<Pi> (concat \<pi>)"
  proof  -
    let ?\<pi>' = "concat \<pi>"
    {
      have "\<forall>ops \<in> set \<pi>. \<forall>op \<in> set ops. op \<in> set ((\<Pi>)\<^sub>\<O>)"
        using assms(3)
        unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff
        by force
      hence "\<forall>op \<in> set ?\<pi>'. op \<in> set ((\<Pi>)\<^sub>\<O>)"
        using flattening_lemma_i
        by blast
    }
    moreover {
      {
        fix ops
        assume "ops \<in> set \<pi>"
        moreover obtain op where "ops = [op]"
          using assms(2) calculation
          by blast
        moreover have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
          using assms(3) calculation
          unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff
          by force
        moreover have "is_valid_operator_strips \<Pi> op"
          using assms(1) calculation(3)
          unfolding is_valid_problem_strips_def Let_def list_all_iff ListMem_iff
          by simp
        ultimately have "\<exists>op. ops = [op] \<and> is_valid_operator_strips \<Pi> op"
          by blast
      }
      moreover have "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) \<pi>"
        using assms(3)
        unfolding is_parallel_solution_for_problem_def
        by simp
      ultimately have "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_serial_plan ((\<Pi>)\<^sub>I) ?\<pi>'"
        using flattening_lemma_ii
        by blast
    }
    ultimately show "is_serial_solution_for_problem \<Pi> ?\<pi>'"
      unfolding is_serial_solution_for_problem_def list_all_iff ListMem_iff
      by simp
  qed


text \<open> Finally, we can obtain the important result that a parallel plan with a trace that
reaches the goal state of a given problem \<^term>\<open>\<Pi>\<close>, and for which both the parallel operator execution
condition as well as non interference is assured at every point \<^term>\<open>k < length \<pi>\<close>, the flattening of
the parallel plan \<^term>\<open>concat \<pi>\<close> is a serial solution for the initial and goal state of the problem.
To wit, by lemma \ref{isathm:parallel-solution-trace-strips} we have

    @{text[display, indent=4] "(G \<subseteq>\<^sub>m execute_parallel_plan I \<pi>)
      = (G \<subseteq>\<^sub>m last (trace_parallel_plan_strips I \<pi>))"}

so the second assumption entails that \<^term>\<open>\<pi>\<close> is a solution for the initial state and the goal state
of the problem. (which implicitely means that  \<^term>\<open>\<pi>\<close> is a solution
for the inital state and goal state of the problem). The trace formulation is used in this case
because it allows us to write the---state dependent---applicability condition more succinctly. The
proof (shown below) is by structural induction on \<^term>\<open>\<pi>\<close> with arbitrary initial state.\<close>

(* TODO Demote to lemma; add theorem about problem solutions. Move text to theorem. *)
theorem  execute_parallel_plan_is_execute_sequential_plan_if:
  fixes I :: "('variable, bool) state"
  assumes "is_valid_problem \<Pi>"
    and "G \<subseteq>\<^sub>m last (trace_parallel_plan_strips I \<pi>)"
    and "\<forall>k < length \<pi>.
      are_all_operators_applicable (trace_parallel_plan_strips I \<pi> ! k) (\<pi> ! k)
      \<and> are_all_operator_effects_consistent (\<pi> ! k)
      \<and> are_all_operators_non_interfering (\<pi> ! k)"
  shows "G \<subseteq>\<^sub>m execute_serial_plan I (concat \<pi>)"
  using assms
  proof (induction \<pi> arbitrary: I)
    case (Cons ops \<pi>)
    let ?ops' = "take (length ops) (concat (ops # \<pi>))"
    let ?J = "execute_parallel_operator I ops"
      and ?J' = "execute_serial_plan I ?ops'"
    {
      have "trace_parallel_plan_strips I \<pi> ! 0 = I" and "(ops # \<pi>) ! 0 = ops"
        unfolding trace_parallel_plan_strips_head_is_initial_state
        by simp+
      then have "are_all_operators_applicable I ops"
        and "are_all_operator_effects_consistent ops"
        and "are_all_operators_non_interfering ops"
        using Cons.prems(3)
        by auto+
      then have "trace_parallel_plan_strips I (ops # \<pi>)
        = I # trace_parallel_plan_strips ?J \<pi>"
        by fastforce
    } note nb = this
    {
      have "last (trace_parallel_plan_strips I (ops # \<pi>))
        = last (trace_parallel_plan_strips ?J \<pi>)"
        using trace_parallel_plan_strips_last_cons_then nb
        by metis
      hence "G \<subseteq>\<^sub>m last (trace_parallel_plan_strips ?J \<pi>)"
        using Cons.prems(2)
        by force
    }
    moreover {
      fix k
      assume "k < length \<pi>"
      moreover have "k + 1 < length (ops # \<pi>)"
        using calculation
        by force
      moreover have "\<pi> ! k = (ops # \<pi>) ! (k + 1)"
        by simp
      ultimately have "are_all_operators_applicable
        (trace_parallel_plan_strips ?J \<pi> ! k) (\<pi> ! k)"
        and "are_all_operator_effects_consistent (\<pi> ! k)"
        and "are_all_operators_non_interfering (\<pi> ! k)"
        using Cons.prems(3) nb
        by force+
    }
    ultimately have "G \<subseteq>\<^sub>m execute_serial_plan ?J (concat \<pi>)"
      using Cons.IH[OF Cons.prems(1), of ?J]
      by blast
    moreover {
      have "execute_serial_plan I (concat (ops # \<pi>))
        = execute_serial_plan ?J' (concat \<pi>)"
        using execute_serial_plan_split[of I ops] Cons.prems(3)
        by auto
      thm execute_parallel_operator_equals_execute_sequential_strips_if[of I]
      moreover have "?J = ?J'"
        using execute_parallel_operator_equals_execute_sequential_strips_if Cons.prems(3)
        by fastforce
      ultimately have "execute_serial_plan I (concat (ops # \<pi>))
        = execute_serial_plan ?J (concat \<pi>)"
        using execute_serial_plan_split[of I ops] Cons.prems(3)
        by argo
    }
    ultimately show ?case
      by argo
  qed force

subsection "Auxiliary lemmas about STRIPS"

lemma set_to_precondition_of_op_is[simp]: "set (to_precondition op)
  = { (v, True) | v. v \<in> set (precondition_of op) }"
  unfolding to_precondition_def STRIPS_Representation.to_precondition_def set_map
  by blast


end
