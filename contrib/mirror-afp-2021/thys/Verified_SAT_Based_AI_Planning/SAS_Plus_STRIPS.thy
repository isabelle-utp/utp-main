(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory SAS_Plus_STRIPS
  imports "STRIPS_Semantics" "SAS_Plus_Semantics" 
    "Map_Supplement"
begin

section "SAS+/STRIPS Equivalence"

text \<open> The following part is concerned with showing the equivalent expressiveness of SAS+ and
STRIPS as discussed in \autoref{sub:equivalence-sas-plus-strips}. \<close>

subsection "Translation of SAS+ Problems to STRIPS Problems"

definition possible_assignments_for 
  :: "('variable, 'domain) sas_plus_problem \<Rightarrow> 'variable \<Rightarrow> ('variable \<times> 'domain) list" 
  where "possible_assignments_for \<Psi> v \<equiv> [(v, a). a \<leftarrow> the (range_of \<Psi> v)]"

definition all_possible_assignments_for
  :: "('variable, 'domain) sas_plus_problem \<Rightarrow> ('variable \<times> 'domain) list"
  where "all_possible_assignments_for \<Psi> 
    \<equiv> concat [possible_assignments_for \<Psi> v. v \<leftarrow> variables_of \<Psi>]" 

definition state_to_strips_state
  :: "('variable, 'domain) sas_plus_problem 
    \<Rightarrow> ('variable, 'domain) state 
    \<Rightarrow> ('variable, 'domain) assignment strips_state" 
  ("\<phi>\<^sub>S _ _" 99)
  where "state_to_strips_state \<Psi> s 
    \<equiv> let defined = filter (\<lambda>v. s v \<noteq> None) (variables_of \<Psi>) in
      map_of (map (\<lambda>(v, a). ((v, a), the (s v) = a)) 
        (concat [possible_assignments_for \<Psi> v. v \<leftarrow> defined]))"

definition sasp_op_to_strips
  :: "('variable, 'domain) sas_plus_problem
    \<Rightarrow> ('variable, 'domain) sas_plus_operator
    \<Rightarrow> ('variable, 'domain) assignment strips_operator" 
  ("\<phi>\<^sub>O _ _" 99)
  where "sasp_op_to_strips \<Psi> op \<equiv> let
      pre = precondition_of op
      ; add = effect_of op
      ; delete = [(v, a'). (v, a) \<leftarrow> effect_of op, a' \<leftarrow> filter ((\<noteq>) a) (the (range_of \<Psi> v))]
    in STRIPS_Representation.operator_for pre add delete"

definition sas_plus_problem_to_strips_problem
  :: "('variable, 'domain) sas_plus_problem \<Rightarrow> ('variable, 'domain) assignment strips_problem" 
  ("\<phi> _ " 99)
  where "sas_plus_problem_to_strips_problem \<Psi> \<equiv> let 
      vs = [as. v \<leftarrow> variables_of \<Psi>, as \<leftarrow> (possible_assignments_for \<Psi>) v]
      ; ops = map (sasp_op_to_strips \<Psi>) (operators_of \<Psi>)
      ; I = state_to_strips_state \<Psi> (initial_of \<Psi>)
      ; G = state_to_strips_state \<Psi> (goal_of \<Psi>)
    in STRIPS_Representation.problem_for vs ops I G"

definition sas_plus_parallel_plan_to_strips_parallel_plan
  :: "('variable, 'domain) sas_plus_problem
    \<Rightarrow> ('variable, 'domain) sas_plus_parallel_plan
    \<Rightarrow> ('variable \<times> 'domain) strips_parallel_plan" 
  ("\<phi>\<^sub>P _ _" 99)
  where "sas_plus_parallel_plan_to_strips_parallel_plan \<Psi> \<psi>
    \<equiv> [[sasp_op_to_strips \<Psi> op. op \<leftarrow> ops]. ops \<leftarrow> \<psi>]"

(* TODO first argument should be ('variable, 'domain) strips_problem *)
definition strips_state_to_state
  :: "('variable, 'domain) sas_plus_problem
    \<Rightarrow> ('variable, 'domain) assignment strips_state
    \<Rightarrow> ('variable, 'domain) state" 
  ("\<phi>\<^sub>S\<inverse> _ _" 99)
  where "strips_state_to_state \<Psi> s 
    \<equiv> map_of (filter (\<lambda>(v, a). s (v, a) = Some True) (all_possible_assignments_for \<Psi>))"

(* TODO remove problem argument *)
definition strips_op_to_sasp 
  :: "('variable, 'domain) sas_plus_problem 
    \<Rightarrow> ('variable \<times> 'domain) strips_operator
    \<Rightarrow> ('variable, 'domain) sas_plus_operator"
  ("\<phi>\<^sub>O\<inverse> _ _" 99)
  where "strips_op_to_sasp \<Psi> op 
    \<equiv> let 
        precondition = strips_operator.precondition_of op
        ; effect = strips_operator.add_effects_of op 
      in \<lparr> precondition_of = precondition, effect_of = effect \<rparr>" 

(* TODO \<open>strips_parallel_plan_to_sas_plus_parallel_plan \<leadsto> \<phi>_P\<inverse>\<close> and 
\<open>strips_op_to_sasp \<leadsto> \<phi>_O\<inverse>\<close> *)
definition strips_parallel_plan_to_sas_plus_parallel_plan
  :: "('variable, 'domain) sas_plus_problem
    \<Rightarrow> ('variable \<times> 'domain) strips_parallel_plan
    \<Rightarrow> ('variable, 'domain) sas_plus_parallel_plan" 
  ("\<phi>\<^sub>P\<inverse> _ _" 99)
  where "strips_parallel_plan_to_sas_plus_parallel_plan \<Pi> \<pi>
    \<equiv> [[strips_op_to_sasp \<Pi> op. op \<leftarrow> ops]. ops \<leftarrow> \<pi>]"

text \<open> To set up the equivalence proof context, we declare a common locale 
\isaname{sas_plus_strips_equivalence} for both the STRIPS and SAS+ formalisms and make it a 
sublocale of both locale \isaname{strips} as well as \isaname{sas_plus}.
The declaration itself is omitted for brevity since it basically just joins locales 
\isaname{sas_plus} and \isaname{strips} while renaming the locale parameter to avoid name clashes.
The sublocale proofs are shown below.
\footnote{We append a suffix identifying the respective formalism to the the parameter names 
passed to the parameter names in the locale. This is necessary to avoid ambiguous names in the 
sublocale declarations. For example, without addition of suffixes the type for \<open>initial_of\<close> is 
ambiguous and will therefore not be bound to either \<open>strips_problem.initial_of\<close> or 
\<open>sas_plus_problem.initial_of\<close>. 
Isabelle in fact considers it to be a a free variable in this case. We also qualify the parent 
locales in the sublocale declarations by adding \texttt{strips:} and \texttt{sas\_plus:} before 
the respective parent locale identifiers. } \<close>

definition "range_of_strips \<Pi> x \<equiv> { True, False }"

context
begin

\<comment> \<open> Set-up simp rules. \<close>
lemma[simp]: 
  "(\<phi> \<Psi>) = (let 
      vs = [as. v \<leftarrow> variables_of \<Psi>, as \<leftarrow> (possible_assignments_for \<Psi>) v]
      ; ops = map (sasp_op_to_strips \<Psi>) (operators_of \<Psi>)
      ; I = state_to_strips_state \<Psi> (initial_of \<Psi>)
      ; G = state_to_strips_state \<Psi> (goal_of \<Psi>)
    in STRIPS_Representation.problem_for vs ops I G)"
  and "(\<phi>\<^sub>S \<Psi> s)
    = (let defined = filter (\<lambda>v. s v \<noteq> None) (variables_of \<Psi>) in
      map_of (map (\<lambda>(v, a). ((v, a), the (s v) = a)) 
        (concat [possible_assignments_for \<Psi> v. v \<leftarrow> defined])))"
  and "(\<phi>\<^sub>O \<Psi> op)
    = (let
      pre = precondition_of op
      ; add = effect_of op
      ; delete = [(v, a'). (v, a) \<leftarrow> effect_of op, a' \<leftarrow> filter ((\<noteq>) a) (the (range_of \<Psi> v))]
    in STRIPS_Representation.operator_for pre add delete)" 
  and "(\<phi>\<^sub>P \<Psi> \<psi>) = [[\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]. ops \<leftarrow> \<psi>]"
  and "(\<phi>\<^sub>S\<inverse> \<Psi> s')= map_of (filter (\<lambda>(v, a). s' (v, a) = Some True) 
    (all_possible_assignments_for \<Psi>))" 
  and "(\<phi>\<^sub>O\<inverse> \<Psi> op') = (let 
        precondition = strips_operator.precondition_of op'
        ; effect = strips_operator.add_effects_of op' 
      in \<lparr> precondition_of = precondition, effect_of = effect \<rparr>)" 
  and "(\<phi>\<^sub>P\<inverse> \<Psi> \<pi>) = [[\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> ops]. ops \<leftarrow> \<pi>]"
  unfolding
    SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def
    sas_plus_problem_to_strips_problem_def
    SAS_Plus_STRIPS.state_to_strips_state_def
    state_to_strips_state_def
    SAS_Plus_STRIPS.sasp_op_to_strips_def
    sasp_op_to_strips_def
    SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def
    sas_plus_parallel_plan_to_strips_parallel_plan_def
    SAS_Plus_STRIPS.strips_state_to_state_def
    strips_state_to_state_def 
    SAS_Plus_STRIPS.strips_op_to_sasp_def
    strips_op_to_sasp_def 
    SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
    strips_parallel_plan_to_sas_plus_parallel_plan_def 
  by blast+

lemmas [simp] = range_of'_def

lemma is_valid_problem_sas_plus_dom_sas_plus_problem_range_of:
  assumes "is_valid_problem_sas_plus \<Psi>" 
  shows "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). v \<in> dom (sas_plus_problem.range_of \<Psi>)"
  using assms(1) is_valid_problem_sas_plus_then(1)
  unfolding is_valid_problem_sas_plus_def
  by (meson domIff list.pred_set)

lemma possible_assignments_for_set_is:
  assumes "v \<in> dom (sas_plus_problem.range_of \<Psi>)"
  shows "set (possible_assignments_for \<Psi> v) 
    = { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v }" 
proof -
  have "sas_plus_problem.range_of \<Psi> v \<noteq> None"
    using assms(1) 
    by auto
  thus  ?thesis 
    unfolding possible_assignments_for_def
    by fastforce
qed

lemma all_possible_assignments_for_set_is:
  assumes "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). range_of \<Psi> v \<noteq> None" 
  shows "set (all_possible_assignments_for \<Psi>)
    = (\<Union>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })" 
proof -
  let ?vs = "variables_of \<Psi>"
  have "set (all_possible_assignments_for \<Psi>) = 
    (\<Union>(set ` (\<lambda>v. map (\<lambda>(v, a). (v, a)) (possible_assignments_for \<Psi> v)) ` set ?vs))"
    unfolding all_possible_assignments_for_def set_concat
    using set_map 
    by auto
  also have "\<dots> = (\<Union>((\<lambda>v. set (possible_assignments_for \<Psi> v)) ` set ?vs))"
    using image_comp set_map
    by simp
  (* TODO slow *)
  also have "\<dots> = (\<Union>((\<lambda>v. { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v }) ` set ?vs))"
    using possible_assignments_for_set_is assms 
    by fastforce
  finally show ?thesis
    by force
qed

lemma state_to_strips_state_dom_is_i[simp]:
  assumes "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). v \<in> dom (sas_plus_problem.range_of \<Psi>)"
  shows "set (concat 
      [possible_assignments_for \<Psi> v. v \<leftarrow> filter (\<lambda>v. s v \<noteq> None) (variables_of \<Psi>)])
    = (\<Union>v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }. 
      { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })" 
proof -
  let ?vs = "variables_of \<Psi>"
  let ?defined = "filter (\<lambda>v. s v \<noteq> None) ?vs"
  let ?l = "concat [possible_assignments_for \<Psi> v. v \<leftarrow> ?defined]"
  have nb: "set ?defined = { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }" 
    unfolding set_filter
    by force
  have "set ?l = \<Union>(set ` set (map (possible_assignments_for \<Psi>) ?defined ))" 
    unfolding set_concat image_Union
    by blast
  also have "\<dots> = \<Union>(set ` (possible_assignments_for \<Psi>) ` set ?defined)" 
    unfolding set_map
    by blast
  also have "\<dots> = (\<Union>v \<in> set ?defined. set (possible_assignments_for \<Psi> v))"
    by blast
  also have "\<dots> = (\<Union>v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }.
    set (possible_assignments_for \<Psi> v))"
    using nb 
    by argo
  finally show ?thesis
    using possible_assignments_for_set_is 
      is_valid_problem_sas_plus_dom_sas_plus_problem_range_of assms(1)
    by fastforce
qed

lemma state_to_strips_state_dom_is:
  \<comment> \<open> NOTE A transformed state is defined on all possible assignments for all variables defined 
in the original state. \<close>
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "dom (\<phi>\<^sub>S \<Psi> s) 
    = (\<Union>v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }. 
      { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })"
proof -
  let ?vs = "variables_of \<Psi>"
  let ?l = "concat [possible_assignments_for \<Psi> v. v \<leftarrow> filter (\<lambda>v. s v \<noteq> None) ?vs]"
  have nb: "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). v \<in> dom (sas_plus_problem.range_of \<Psi>)"
    using is_valid_problem_sas_plus_dom_sas_plus_problem_range_of assms(1)
    by fastforce
  have "dom (\<phi>\<^sub>S \<Psi> s) = fst ` set (map (\<lambda>(v, a). ((v, a), the (s v) = a)) ?l)" 
    unfolding state_to_strips_state_def 
      SAS_Plus_STRIPS.state_to_strips_state_def 
    using dom_map_of_conv_image_fst[of "map (\<lambda>(v, a). ((v, a), the (s v) = a)) ?l"]
    by presburger
  also have "\<dots> = fst ` (\<lambda>(v, a). ((v, a), the (s v) = a)) ` set ?l" 
    unfolding set_map
    by blast
  also have "\<dots> = (\<lambda>(v, a). fst  ((v, a), the (s v) = a)) ` set ?l"
    unfolding image_comp[of fst "\<lambda>(v, a). ((v, a), the (s v) = a)"] comp_apply[of 
        fst "\<lambda>(v, a). ((v, a), the (s v) = a)"] prod.case_distrib
    by blast
  finally show ?thesis
    unfolding state_to_strips_state_dom_is_i[OF nb]
    by force
qed

corollary state_to_strips_state_dom_element_iff:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> s) \<longleftrightarrow> v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)
    \<and> s v \<noteq> None
    \<and> a \<in> \<R>\<^sub>+ \<Psi> v"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?s' = "\<phi>\<^sub>S \<Psi> s"
  show ?thesis 
    proof (rule iffI)
      assume "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> s)" 
      then have "v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }"
          and "a \<in> \<R>\<^sub>+ \<Psi> v"
        unfolding state_to_strips_state_dom_is[OF assms(1)]
        by force+
      moreover have "v \<in> set ?vs" and "s v \<noteq> None" 
        using calculation(1) 
        by fastforce+
      ultimately show 
        "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None \<and> a \<in> \<R>\<^sub>+ \<Psi> v"
        by force
    next 
      assume "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None \<and> a \<in> \<R>\<^sub>+ \<Psi> v"
      then have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
        and "s v \<noteq> None"
        and a_in_range_of_v: "a \<in> \<R>\<^sub>+ \<Psi> v" 
        by simp+
      then have "v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }"
        by force
      thus "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> s)"
        unfolding state_to_strips_state_dom_is[OF assms(1)]
        using a_in_range_of_v
        by blast
    qed
qed

lemma state_to_strips_state_range_is:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> s)" 
  shows "(\<phi>\<^sub>S \<Psi> s) (v, a) = Some (the (s v) = a)"
proof -
  let ?vs = "variables_of \<Psi>" 
  let ?s' = "\<phi>\<^sub>S \<Psi> s"
    and ?defined = "filter (\<lambda>v. s v \<noteq> None) ?vs"
  let ?l = "concat [possible_assignments_for \<Psi> v. v \<leftarrow> ?defined]"
  have v_in_set_vs: "v \<in> set ?vs" 
    and s_of_v_is_not_None: "s v \<noteq> None" 
    and a_in_range_of_v: "a \<in> \<R>\<^sub>+ \<Psi> v" 
    using assms(2)
    unfolding state_to_strips_state_dom_is[OF assms(1)]
    by fastforce+
  moreover {
    have "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). v \<in> dom (sas_plus_problem.range_of \<Psi>)"
      using assms(1) is_valid_problem_sas_plus_then(1)
      unfolding is_valid_problem_sas_plus_def
      by fastforce
    moreover have "(v, a) \<in> set ?l" 
      unfolding state_to_strips_state_dom_is_i[OF calculation(1)]
      using s_of_v_is_not_None a_in_range_of_v v_in_set_vs
      by fastforce
    moreover have "set ?l \<noteq> {}" 
      using calculation
      by fastforce
    \<comment> \<open> TODO slow. \<close>
    ultimately have "(\<phi>\<^sub>S \<Psi> s) (v, a) = Some (the (s v) = a)"
      using map_of_from_function_graph_is_some_if[of 
          ?l "(v, a)" "\<lambda>(v, a). the (s v) = a"] 
      unfolding SAS_Plus_STRIPS.state_to_strips_state_def
        state_to_strips_state_def Let_def case_prod_beta'
      by fastforce
  }
  thus ?thesis.
qed


\<comment> \<open> Show that a STRIPS state corresponding to a SAS+ state via transformation is consistent
w.r.t. to the variable subset with same left component (i.e. the original SAS+ variable). This is
the consistency notion corresponding to SAS+ consistency: i.e. if no two assignments with different
values for the same variable exist in the SAS+ state, then assigning the corresponding assignment
both to @{text "True"} is impossible. Vice versa, if both are assigned to @{text "True"} then the
assignment variables must be the same SAS+ variable/SAS+ value pair. \<close>
lemma state_to_strips_state_effect_consistent:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> s)"
    and "(v, a') \<in> dom (\<phi>\<^sub>S \<Psi> s)"
    and "(\<phi>\<^sub>S \<Psi> s) (v, a) = Some True"
    and  "(\<phi>\<^sub>S \<Psi> s) (v, a') = Some True"
  shows "(v, a) = (v, a')" 
proof -
  have "the (s v) = a" and "the (s v) = a'"
    using state_to_strips_state_range_is[OF assms(1)] assms(2, 3, 4, 5)
    by fastforce+
  thus ?thesis 
    by argo
qed


lemma sasp_op_to_strips_set_delete_effects_is:
  assumes "is_valid_operator_sas_plus \<Psi> op" 
  shows "set (strips_operator.delete_effects_of (\<phi>\<^sub>O \<Psi> op)) 
    = (\<Union>(v, a) \<in> set (effect_of op). { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })"
proof -
  let ?D = "range_of \<Psi>"
    and ?effect = "effect_of op" 
  let ?delete = "[(v, a'). (v, a) \<leftarrow> ?effect, a' \<leftarrow> filter ((\<noteq>) a) (the (?D v))]"
  {
    fix v a
    assume "(v, a) \<in> set ?effect"
    then have "(\<R>\<^sub>+ \<Psi> v) = set (the (?D v))"
      using assms 
      using is_valid_operator_sas_plus_then_range_of_sas_plus_op_is_set_range_of_op
      by fastforce
    hence "set (filter ((\<noteq>) a) (the (?D v))) = { a' \<in> \<R>\<^sub>+ \<Psi> v. a' \<noteq> a }"
      unfolding set_filter 
      by blast
  } note nb = this
  {
    \<comment> \<open> TODO slow. \<close>
    have "set ?delete = \<Union>(set ` (\<lambda>(v, a). map (Pair v) (filter ((\<noteq>) a) (the (?D v)))) 
      ` (set ?effect))" 
      using set_concat
      by simp
    also have "\<dots> = \<Union>((\<lambda>(v, a). Pair v ` set (filter ((\<noteq>) a) (the (?D v)))) 
      ` (set ?effect))"
      unfolding image_comp[of set] set_map 
      by auto
    \<comment> \<open> TODO slow. \<close>
    also have "\<dots> = (\<Union>(v, a) \<in> set ?effect. Pair v ` { a' \<in> \<R>\<^sub>+ \<Psi> v. a' \<noteq> a })" 
      using nb 
      by fast
    finally have "set ?delete = (\<Union>(v, a) \<in> set ?effect.
      { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })" 
      by blast
  }
  thus ?thesis
    unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
      sasp_op_to_strips_def Let_def
    by force 
qed

lemma sas_plus_problem_to_strips_problem_variable_set_is:
  \<comment> \<open> The variable set of \<open>\<Pi>\<close> is the set of all possible 
assignments that are possible using the variables of \<open>\<V>\<close> and the corresponding domains. \<close>
  assumes "is_valid_problem_sas_plus \<Psi>" 
  shows "set ((\<phi> \<Psi>)\<^sub>\<V>) = (\<Union>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })"
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
    and ?vs = "variables_of \<Psi>"
  {
    have "set (strips_problem.variables_of ?\<Pi>) 
      = set [as. v \<leftarrow> ?vs, as \<leftarrow> possible_assignments_for \<Psi> v]"
      unfolding sas_plus_problem_to_strips_problem_def 
        SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def
      by force
    also have "\<dots> = (\<Union>(set ` (\<lambda>v. possible_assignments_for \<Psi> v) ` set ?vs))" 
      using set_concat
      by auto
    also have "\<dots> = (\<Union>((set \<circ> possible_assignments_for \<Psi>) ` set ?vs))" 
      using image_comp[of set "\<lambda>v. possible_assignments_for \<Psi> v" "set ?vs"]
      by argo
    finally have "set (strips_problem.variables_of ?\<Pi>) 
      = (\<Union>v \<in> set ?vs. set (possible_assignments_for \<Psi> v))"
      unfolding o_apply
      by blast
  }
  moreover have "\<forall>v \<in> set ?vs. v \<in> dom (sas_plus_problem.range_of \<Psi>)"
    using is_valid_problem_sas_plus_dom_sas_plus_problem_range_of assms
    by force
  ultimately show ?thesis
    using possible_assignments_for_set_is
    by force 
qed

corollary sas_plus_problem_to_strips_problem_variable_set_element_iff:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "(v, a) \<in> set ((\<phi> \<Psi>)\<^sub>\<V>)  \<longleftrightarrow> v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> a \<in> \<R>\<^sub>+ \<Psi> v"
  unfolding sas_plus_problem_to_strips_problem_variable_set_is[OF assms]
  by fast

lemma sasp_op_to_strips_effect_consistent:
  assumes "op = \<phi>\<^sub>O \<Psi> op'" 
    and "op' \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
    and "is_valid_operator_sas_plus \<Psi> op'"
  shows "(v, a) \<in> set (add_effects_of op) \<longrightarrow> (v, a) \<notin> set (delete_effects_of op)"
    and "(v, a) \<in> set (delete_effects_of op) \<longrightarrow> (v, a) \<notin> set (add_effects_of op)"
proof -
  have nb: "(\<forall>(v, a) \<in> set (effect_of op'). \<forall>(v', a') \<in> set (effect_of op'). v \<noteq> v' \<or> a = a')" 
    using assms(3)
    unfolding is_valid_operator_sas_plus_def 
      SAS_Plus_Representation.is_valid_operator_sas_plus_def list_all_iff ListMem_iff Let_def
    by argo
  {
    fix v a
    assume v_a_in_add_effects_of_op: "(v, a) \<in> set (add_effects_of op)" 
    have "(v, a) \<notin> set (delete_effects_of op)" 
      proof (rule ccontr)
        assume "\<not>(v, a) \<notin> set (delete_effects_of op)" 
        moreover have "(v, a) \<in> 
          (\<Union>(v, a') \<in> set (effect_of op'). { (v, a'') 
            | a''. a'' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a'' \<noteq> a' })"
          using calculation sasp_op_to_strips_set_delete_effects_is 
            assms 
          by blast
        moreover obtain a' where "(v, a') \<in> set (effect_of op')" and "a \<noteq> a'" 
          using calculation
          by blast
        moreover have "(v, a') \<in> set (add_effects_of op)" 
          using assms(1) calculation(3)
          unfolding sasp_op_to_strips_def
            SAS_Plus_STRIPS.sasp_op_to_strips_def
            Let_def
          by fastforce
        moreover have "(v, a) \<in> set (effect_of op')" and "(v, a') \<in> set (effect_of op')" 
          using assms(1) v_a_in_add_effects_of_op calculation(5)
          unfolding sasp_op_to_strips_def 
            SAS_Plus_STRIPS.sasp_op_to_strips_def
            Let_def 
          by force+
        ultimately show False 
          using nb 
          by fast
      qed
  }
  moreover {
    fix v a
    assume v_a_in_delete_effects_of_op: "(v, a) \<in> set (delete_effects_of op)" 
    have "(v, a) \<notin> set (add_effects_of op)" 
      proof (rule ccontr)
        assume "\<not>(v, a) \<notin> set (add_effects_of op)" 
        moreover have "(v, a) \<in> set (add_effects_of op)" 
          using calculation 
          by blast
        moreover have "(v, a) \<in> 
          (\<Union>(v, a') \<in> set (effect_of op'). { (v, a'') 
            | a''. a'' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a'' \<noteq> a' })"
          using sasp_op_to_strips_set_delete_effects_is  
            nb assms(1, 3) v_a_in_delete_effects_of_op
          by force
        moreover obtain a' where "(v, a') \<in> set (effect_of op')" and "a \<noteq> a'" 
          using calculation
          by blast
        moreover have "(v, a') \<in> set (add_effects_of op)" 
          using assms(1) calculation(4)
          unfolding sasp_op_to_strips_def 
            SAS_Plus_STRIPS.sasp_op_to_strips_def
            Let_def
          by fastforce
        moreover have "(v, a) \<in> set (effect_of op')" and "(v, a') \<in> set (effect_of op')" 
          using assms(1) calculation(2, 6)
          unfolding sasp_op_to_strips_def 
            SAS_Plus_STRIPS.sasp_op_to_strips_def Let_def 
          by force+
        ultimately show False 
          using nb 
          by fast
      qed
    }
    ultimately show "(v, a) \<in> set (add_effects_of op) 
      \<longrightarrow> (v, a) \<notin> set (delete_effects_of op)"
      and "(v, a) \<in> set (delete_effects_of op) 
      \<longrightarrow> (v, a) \<notin> set (add_effects_of op)"
      by blast+
  qed

lemma is_valid_problem_sas_plus_then_strips_transformation_too_iii:
  assumes "is_valid_problem_sas_plus \<Psi>" 
  shows "list_all (is_valid_operator_strips (\<phi> \<Psi>))
    (strips_problem.operators_of (\<phi> \<Psi>))"
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?vs = "strips_problem.variables_of ?\<Pi>"
  {
    fix op
    assume "op \<in> set (strips_problem.operators_of ?\<Pi>)" 
    \<comment> \<open> TODO slow. \<close>
    then obtain op' 
      where op_is: "op = \<phi>\<^sub>O \<Psi> op'" 
        and op'_in_operators: "op' \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
      unfolding SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def
        sas_plus_problem_to_strips_problem_def 
        sasp_op_to_strips_def 
      by auto
    then have is_valid_op': "is_valid_operator_sas_plus \<Psi> op'"
      using sublocale_sas_plus_finite_domain_representation_ii(2)[OF assms]
      by blast
    moreover {
      fix v a
      assume "(v, a) \<in> set (strips_operator.precondition_of op)"
      \<comment> \<open> TODO slow. \<close>
      then have "(v, a) \<in> set (sas_plus_operator.precondition_of op')" 
        using op_is
        unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def 
          sasp_op_to_strips_def
        by force
      moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
        using is_valid_op' calculation
        using is_valid_operator_sas_plus_then(1)
        by fastforce 
      moreover have  "a \<in> \<R>\<^sub>+ \<Psi> v" 
        using is_valid_op' calculation(1)
        using is_valid_operator_sas_plus_then(2) 
        by fast
      ultimately have "(v, a) \<in> set ?vs" 
        using sas_plus_problem_to_strips_problem_variable_set_element_iff[OF assms(1)]
        by force
    }
    moreover {
      fix v a
      assume "(v, a) \<in> set (strips_operator.add_effects_of op)"
      then have "(v, a) \<in> set (effect_of op')" 
        using op_is
        unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
          sasp_op_to_strips_def
        by force
      then have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" and "a \<in> \<R>\<^sub>+ \<Psi> v" 
        using is_valid_operator_sas_plus_then is_valid_op'
        by fastforce+
      hence "(v, a) \<in> set ?vs" 
        using sas_plus_problem_to_strips_problem_variable_set_element_iff[OF assms(1)]
        by force
    }
    moreover {
      fix v a'
      assume v_a'_in_delete_effects: "(v, a') \<in> set (strips_operator.delete_effects_of op)"
      moreover have "set (strips_operator.delete_effects_of op) 
        =  (\<Union>(v, a) \<in> set (effect_of op'). 
          { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })"
        using sasp_op_to_strips_set_delete_effects_is[OF is_valid_op']
          op_is
        by simp
      \<comment> \<open> TODO slow. \<close>
      ultimately obtain a 
        where "(v, a) \<in> set (effect_of op')" 
          and a'_in: "a' \<in> { a' \<in> \<R>\<^sub>+ \<Psi> v. a' \<noteq> a }"
        by blast 
      moreover have "is_valid_operator_sas_plus \<Psi> op'"
        using op'_in_operators assms(1) 
          is_valid_problem_sas_plus_then(2)
        by blast
      moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
        using is_valid_operator_sas_plus_then calculation(1, 3)
        by fast
      moreover have "a' \<in> \<R>\<^sub>+ \<Psi> v"
        using a'_in 
        by blast
      ultimately have "(v, a') \<in> set ?vs" 
        using sas_plus_problem_to_strips_problem_variable_set_element_iff[OF assms(1)]
        by force
    }
    ultimately have "set (strips_operator.precondition_of op) \<subseteq> set ?vs
      \<and> set (strips_operator.add_effects_of op) \<subseteq> set ?vs
      \<and> set (strips_operator.delete_effects_of op) \<subseteq> set ?vs
      \<and> (\<forall>v\<in>set (add_effects_of op). v \<notin> set (delete_effects_of op))
      \<and> (\<forall>v\<in>set (delete_effects_of op). v \<notin> set (add_effects_of op))"
      using sasp_op_to_strips_effect_consistent[OF 
          op_is op'_in_operators is_valid_op']
      by fast+
  }
  thus ?thesis
    unfolding is_valid_operator_strips_def STRIPS_Representation.is_valid_operator_strips_def 
      list_all_iff ListMem_iff Let_def 
    by blast
qed

lemma is_valid_problem_sas_plus_then_strips_transformation_too_iv:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "\<forall>x. ((\<phi> \<Psi>)\<^sub>I) x \<noteq> None
    \<longleftrightarrow> ListMem x (strips_problem.variables_of (\<phi> \<Psi>))"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?I = "initial_of \<Psi>"
    and ?\<Pi> = "\<phi> \<Psi>"
  let ?vs' = "strips_problem.variables_of ?\<Pi>"
    and ?I' = "strips_problem.initial_of ?\<Pi>"
  {
    fix x
    have "?I' x \<noteq> None \<longleftrightarrow> ListMem x ?vs'" 
      proof (rule iffI)
        assume I'_of_x_is_not_None: "?I' x \<noteq> None"
        then have "x \<in> dom ?I'" 
          by blast
        moreover obtain v a where x_is: "x = (v, a)" 
          by fastforce
        ultimately have "(v, a) \<in> dom ?I'" 
          by blast
        then have "v \<in> set ?vs" 
            and "?I v \<noteq> None"
            and "a \<in> \<R>\<^sub>+ \<Psi> v"
          using state_to_strips_state_dom_element_iff[OF assms(1), of v a  ?I] 
          unfolding sas_plus_problem_to_strips_problem_def 
            SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def 
            state_to_strips_state_def
            SAS_Plus_STRIPS.state_to_strips_state_def 
          by simp+
        thus "ListMem x ?vs'"
          unfolding ListMem_iff
          using sas_plus_problem_to_strips_problem_variable_set_element_iff[OF assms(1)] 
            x_is
          by auto
      next 
        assume list_mem_x_vs': "ListMem x ?vs'"
        then obtain v a where x_is: "x = (v, a)" 
          by fastforce
        then have "(v, a) \<in> set ?vs'" 
          using list_mem_x_vs'
          unfolding ListMem_iff
          by blast
        then have "v \<in> set ?vs" and "a \<in> \<R>\<^sub>+ \<Psi> v" 
          using sas_plus_problem_to_strips_problem_variable_set_element_iff[OF assms(1)]
          by force+
        moreover have "?I v \<noteq> None" 
          using is_valid_problem_sas_plus_then(3) assms(1) calculation(1)
          by auto
        ultimately have "(v, a) \<in> dom ?I'" 
          using state_to_strips_state_dom_element_iff[OF assms(1), of v a ?I]
          unfolding SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def 
            sas_plus_problem_to_strips_problem_def
            SAS_Plus_STRIPS.state_to_strips_state_def
            state_to_strips_state_def
          by force 
        thus "?I' x \<noteq> None"
          using x_is 
          by fastforce
      qed
  }
  thus ?thesis
    by simp
qed

private lemma is_valid_problem_sas_plus_then_strips_transformation_too_v:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "\<forall>x. ((\<phi> \<Psi>)\<^sub>G) x \<noteq> None
    \<longrightarrow> ListMem x (strips_problem.variables_of (\<phi> \<Psi>))"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?D = "range_of \<Psi>"
    and ?G = "goal_of \<Psi>"
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?vs' = "strips_problem.variables_of ?\<Pi>"
    and ?G' = "strips_problem.goal_of ?\<Pi>" 
  have nb: "?G' = \<phi>\<^sub>S \<Psi> ?G" 
    by simp
  {
    fix x
    assume "?G' x \<noteq> None" 
    moreover obtain v a where "x = (v, a)" 
      by fastforce
    moreover have "(v, a) \<in> dom ?G'" 
      using domIff calculation(1, 2)
      by blast
    moreover have "v \<in> set ?vs" and "a \<in> \<R>\<^sub>+ \<Psi> v"
      using state_to_strips_state_dom_is[OF assms(1), of ?G] nb calculation(3)
      by auto+
    ultimately have "x \<in> set ?vs'"
      using sas_plus_problem_to_strips_problem_variable_set_element_iff[OF assms(1)]
      by auto
  }
  thus ?thesis 
    unfolding ListMem_iff
    by simp
qed

text \<open> We now show that given \<^term>\<open>\<Psi>\<close> is a valid SASPlus problem, then \<^term>\<open>\<Pi> \<equiv> \<phi> \<Psi>\<close> is a valid
STRIPS problem as well. 
The proof unfolds the definition of \<^term>\<open>is_valid_problem_strips\<close> and then shows each of the conjuncts 
for \<^term>\<open>\<Pi>\<close>. These are:
\begin{itemize}
  \item \<^term>\<open>\<Pi>\<close> has at least one variable;
  \item \<^term>\<open>\<Pi>\<close> has at least one operator;
  \item all operators are valid STRIPS operators;
  \item \<^term>\<open>(\<Pi>::'a strips_problem)\<^sub>I\<close> is defined for all variables in \<^term>\<open>(\<Pi>::'a strips_problem)\<^sub>\<V>\<close>; and finally,
  \item if \<^term>\<open>((\<Pi>::'a strips_problem)\<^sub>G) x\<close> is defined, then \<^term>\<open>x\<close> is in \<^term>\<open>(\<Pi>::'a strips_problem)\<^sub>\<V>\<close>.
\end{itemize} \<close>

theorem
  is_valid_problem_sas_plus_then_strips_transformation_too:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "is_valid_problem_strips (\<phi> \<Psi>)" 
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
  have "list_all (is_valid_operator_strips (\<phi> \<Psi>))
   (strips_problem.operators_of (\<phi> \<Psi>))" 
    using is_valid_problem_sas_plus_then_strips_transformation_too_iii[OF assms].
  moreover have "\<forall>x. (((\<phi> \<Psi>)\<^sub>I) x \<noteq> None) =
    ListMem x (strips_problem.variables_of (\<phi> \<Psi>))" 
    using is_valid_problem_sas_plus_then_strips_transformation_too_iv[OF assms].
  moreover have "\<forall>x. ((\<phi> \<Psi>)\<^sub>G) x \<noteq> None \<longrightarrow>
    ListMem x (strips_problem.variables_of (\<phi> \<Psi>))" 
    using is_valid_problem_sas_plus_then_strips_transformation_too_v[OF assms].
  ultimately show ?thesis 
    using is_valid_problem_strips_def 
    unfolding STRIPS_Representation.is_valid_problem_strips_def
    by fastforce
qed 

lemma set_filter_all_possible_assignments_true_is:
  assumes "is_valid_problem_sas_plus \<Psi>" 
  shows "set (filter (\<lambda>(v, a). s (v, a) = Some True) 
      (all_possible_assignments_for \<Psi>))
    =  (\<Union>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). Pair v ` { a \<in> \<R>\<^sub>+ \<Psi> v. s (v, a) = Some True })"
proof -
  let ?vs = "sas_plus_problem.variables_of \<Psi>"
    and ?P = "(\<lambda>(v, a). s (v, a) = Some True)"
  let ?l = "filter ?P (all_possible_assignments_for \<Psi>)"
  have "set ?l = set (concat (map (filter ?P) (map (possible_assignments_for \<Psi>) ?vs)))" 
    unfolding all_possible_assignments_for_def
      filter_concat[of ?P "map (possible_assignments_for \<Psi>) (sas_plus_problem.variables_of \<Psi>)"]
    by simp
  also have "\<dots> = set (concat (map (\<lambda>v. filter ?P (possible_assignments_for \<Psi> v)) ?vs))" 
    unfolding map_map comp_apply 
    by blast
  also have "\<dots> = set (concat (map (\<lambda>v. map (Pair v) 
    (filter (?P \<circ> Pair v) (the (range_of \<Psi> v)))) ?vs))" 
    unfolding possible_assignments_for_def filter_map
    by blast
  also have "\<dots> = set (concat (map (\<lambda>v. map (Pair v) (filter (\<lambda>a. s (v, a) = Some True) 
    (the (range_of \<Psi> v)))) ?vs))" 
    unfolding comp_apply
    by fast
  also have "\<dots> = \<Union>(set ` ((\<lambda>v. map (Pair v) (filter (\<lambda>a. s (v, a) = Some True) 
    (the (range_of \<Psi> v)))) ` set ?vs))"
    unfolding set_concat set_map..
  also have "\<dots> = (\<Union>v \<in> set ?vs. Pair v ` set (filter (\<lambda>a. s (v, a) = Some True) 
    (the (range_of \<Psi> v))))" 
    unfolding image_comp[of set] comp_apply set_map..
  also have "\<dots> = (\<Union>v \<in> set ?vs. Pair v 
    ` { a \<in> set (the (range_of \<Psi> v)). s (v, a) = Some True })"
    unfolding set_filter..
  finally show ?thesis 
    using set_the_range_of_is_range_of_sas_plus_if[OF assms(1)]
    by auto
qed

lemma strips_state_to_state_dom_is: 
  assumes "is_valid_problem_sas_plus \<Psi>" 
  shows "dom (\<phi>\<^sub>S\<inverse> \<Psi> s) 
    = (\<Union>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). 
      { v | a. a \<in> (\<R>\<^sub>+ \<Psi> v) \<and> s (v, a) = Some True })"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?s' = "\<phi>\<^sub>S\<inverse> \<Psi> s" 
    and ?P = "(\<lambda>(v, a). s (v, a) = Some True)"
  let ?l = "filter ?P (all_possible_assignments_for \<Psi>)"
  { 
    have "fst ` set ?l = fst ` (\<Union>v \<in> set ?vs. Pair v 
      ` { a \<in> \<R>\<^sub>+ \<Psi> v. s (v, a) = Some True })"
      unfolding set_filter_all_possible_assignments_true_is[OF assms]
      by auto
    also have "\<dots> = (\<Union>v \<in> set ?vs. fst ` Pair v 
      ` { a \<in> \<R>\<^sub>+ \<Psi> v. s (v, a) = Some True })" 
      by blast
    also have "\<dots> = (\<Union>v \<in> set ?vs. (\<lambda>a. fst (Pair v a)) ` 
      { a \<in> \<R>\<^sub>+ \<Psi> v. s (v, a) = Some True })" 
      unfolding image_comp[of fst] comp_apply
      by blast
    finally have "fst ` set ?l = (\<Union>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). 
      { v | a. a \<in> (\<R>\<^sub>+ \<Psi> v) \<and> s (v, a) = Some True })" 
      unfolding setcompr_eq_image fst_conv 
      by simp
  }
  thus ?thesis
    unfolding SAS_Plus_STRIPS.strips_state_to_state_def 
      strips_state_to_state_def dom_map_of_conv_image_fst
    by blast
qed

lemma strips_state_to_state_range_is: 
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "a \<in> \<R>\<^sub>+ \<Psi> v" 
    and "(v, a) \<in> dom s'"
    and "\<forall>(v, a) \<in> dom s'. \<forall>(v, a') \<in> dom s'. s' (v, a) = Some True \<and> s' (v, a') = Some True 
      \<longrightarrow> (v, a) = (v, a')" 
  shows "(\<phi>\<^sub>S\<inverse> \<Psi> s') v = Some a \<longleftrightarrow> the (s' (v, a))" 
proof -
  let ?vs = "variables_of \<Psi>"
    and ?D = "range_of \<Psi>"
    and ?s = "\<phi>\<^sub>S\<inverse> \<Psi> s'"
  let ?as = "all_possible_assignments_for \<Psi>"
  let ?l = "filter (\<lambda>(v, a). s' (v, a) = Some True) ?as"
  show ?thesis 
    proof (rule iffI)
      assume s_of_v_is_Some_a: "?s v = Some a" 
      {
        have "(v, a) \<in> set ?l" 
          using s_of_v_is_Some_a 
          unfolding SAS_Plus_STRIPS.strips_state_to_state_def 
            strips_state_to_state_def 
          using map_of_SomeD
          by fast
        hence "s' (v, a) = Some True"
          unfolding all_possible_assignments_for_set_is set_filter
          by blast
      }
      thus "the (s' (v, a))"
        by simp
    next 
      assume the_of_s'_of_v_a_is: "the (s' (v, a))"
      then have s'_of_v_a_is_Some_true: "s' (v, a) = Some True"
        using assms(4) domIff 
        by force
      \<comment> \<open> TODO slow. \<close>
      moreover {
        fix v v' a a'
        assume "(v, a) \<in> set ?l" and "(v', a') \<in> set ?l"
        then have "v \<noteq> v' \<or> a = a'" 
        using assms(5)
        by fastforce
      }
      moreover {
        have "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). sas_plus_problem.range_of \<Psi> v \<noteq> None"  
          using is_valid_problem_sas_plus_then(1) assms(1)
            range_of_not_empty 
          by force
        (* TODO slow. *)
        moreover have "set ?l = Set.filter (\<lambda>(v, a). s' (v, a) = Some True) 
          (\<Union>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). { (v, a) | a.  a \<in> \<R>\<^sub>+ \<Psi> v })"
          using all_possible_assignments_for_set_is calculation
          by force
        ultimately have "(v, a) \<in> set ?l" 
          using assms(2, 3) s'_of_v_a_is_Some_true
          by simp
      }
      ultimately show "?s v = Some a"  
        using map_of_constant_assignments_defined_if[of ?l v a]
        unfolding SAS_Plus_STRIPS.strips_state_to_state_def
          strips_state_to_state_def
        by blast
    qed
qed

\<comment> \<open> NOTE A technical lemma which characterizes the return values for possible assignments 
@{text "(v, a)"} when used as variables on a state @{text "s"} which was transformed from. \<close> 
lemma strips_state_to_state_inverse_is_i:
assumes "is_valid_problem_sas_plus \<Psi>"
  and "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
  and "s v \<noteq> None" 
  and "a \<in> \<R>\<^sub>+ \<Psi> v" 
shows "(\<phi>\<^sub>S \<Psi> s) (v, a) = Some (the (s v) = a)"
proof -
   let ?vs = "sas_plus_problem.variables_of \<Psi>"
  let ?s' = "\<phi>\<^sub>S \<Psi> s"
    and ?f = "\<lambda>(v, a). the (s v) = a"
    and ?l = "concat (map (possible_assignments_for \<Psi>) (filter (\<lambda>v. s v \<noteq> None) ?vs))"
  have "(v, a) \<in> dom ?s'" 
    using state_to_strips_state_dom_element_iff[
        OF assms(1)] assms(2, 3, 4)
    by presburger
  {
    have "v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }"
      using assms(2, 3)
      by blast
    moreover have "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). v \<in> dom (sas_plus_problem.range_of \<Psi>)"
      using is_valid_problem_sas_plus_dom_sas_plus_problem_range_of[OF assms(1)]. 
    moreover have "set ?l = (\<Union>v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }. 
      { (v, a) |a. a \<in> \<R>\<^sub>+ \<Psi> v })"
      unfolding state_to_strips_state_dom_is_i[OF calculation(2)]
      by blast
    ultimately have "(v, a) \<in> set ?l" 
      using assms(4)
      by blast
  }
  moreover have "set ?l \<noteq> {}" 
    using calculation
    by force
  \<comment> \<open> TODO slow.\<close>
  ultimately show ?thesis 
    unfolding SAS_Plus_STRIPS.state_to_strips_state_def
      state_to_strips_state_def 
    using map_of_from_function_graph_is_some_if[of ?l "(v, a)" ?f] 
    unfolding split_def
    by fastforce
qed

\<comment> \<open> NOTE Show that the transformed strips state is consistent for pairs of assignments 
@{text "(v, a)"} and @{text "(v, a')"} in the same variable domain. \<close>
(* TODO make private. *)
corollary strips_state_to_state_inverse_is_ii:
assumes "is_valid_problem_sas_plus \<Psi>"
  and "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
  and "s v = Some a"  
  and "a \<in> \<R>\<^sub>+ \<Psi> v" 
  and "a' \<in> \<R>\<^sub>+ \<Psi> v" 
  and "a' \<noteq> a"
shows "(\<phi>\<^sub>S \<Psi> s) (v, a') = Some False"
proof -
  have "s v \<noteq> None" 
    using assms(3) 
    by simp
  moreover have "the (s v) \<noteq> a'" 
    using assms(3, 6) 
    by simp 
  ultimately show ?thesis 
    using strips_state_to_state_inverse_is_i[OF assms(1, 2) _ assms(5)]
    by force
qed

\<comment> \<open> NOTE Follows from the corollary above by contraposition. \<close>
(* TODO make private. *)
corollary strips_state_to_state_inverse_is_iii:
assumes "is_valid_problem_sas_plus \<Psi>"
  and "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
  and "s v = Some a" 
  and "a \<in> \<R>\<^sub>+ \<Psi> v" 
  and "a' \<in> \<R>\<^sub>+ \<Psi> v" 
  and "(\<phi>\<^sub>S \<Psi> s) (v, a) = Some True"
  and "(\<phi>\<^sub>S \<Psi> s) (v, a') = Some True"
shows "a = a'"
proof -
  have "s v \<noteq> None" 
    using assms(3)
    by blast
  thus ?thesis 
    using strips_state_to_state_inverse_is_i[OF assms(1, 2)] assms(4, 5, 6, 7)
    by auto
qed

(* TODO make private. *)
lemma strips_state_to_state_inverse_is_iv:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "dom s \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    and "s v = Some a" 
    and "a \<in> \<R>\<^sub>+ \<Psi> v" 
  shows "(\<phi>\<^sub>S\<inverse> \<Psi> (\<phi>\<^sub>S \<Psi> s)) v = Some a"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?s' = "\<phi>\<^sub>S \<Psi> s"
  let ?s'' = "\<phi>\<^sub>S\<inverse> \<Psi> ?s'" 
  let ?P = "\<lambda>(v, a). ?s' (v, a) = Some True"
  let ?as = "filter ?P (all_possible_assignments_for \<Psi>)" 
    and ?As = "Set.filter ?P (\<Union>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). 
      { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })"
  {
    have "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). range_of \<Psi> v \<noteq> None"
      using sublocale_sas_plus_finite_domain_representation_ii(1)[OF assms(1)] 
        range_of_not_empty
      by force
    (* TODO slow. *)
    hence "set ?as = ?As"
      unfolding set_filter 
      using all_possible_assignments_for_set_is
      by force
  } note nb = this
  moreover {
    {
      fix v v' a a' 
      assume "(v, a) \<in> set ?as" 
        and "(v', a') \<in> set ?as" 
      then have "(v, a) \<in> ?As" and "(v', a') \<in> ?As" 
        using nb 
        by blast+
      then have v_in_set_vs: "v \<in> set ?vs" and v'_in_set_vs: "v' \<in> set ?vs"
        and a_in_range_of_v: "a \<in> \<R>\<^sub>+ \<Psi> v" 
        and a'_in_range_of_v: "a' \<in> \<R>\<^sub>+ \<Psi> v'" 
        and s'_of_v_a_is: "?s' (v, a) = Some True" and s'_of_v'_a'_is: "?s' (v', a') = Some True" 
        by fastforce+
      then have "(v, a) \<in> dom ?s'"  
        by blast
      then have s_of_v_is_Some_a: "s v = Some a"  
        using state_to_strips_state_dom_element_iff[OF assms(1)]
          state_to_strips_state_range_is[OF assms(1)] s'_of_v_a_is 
           by auto
      have "v \<noteq> v' \<or> a = a'"
        proof (rule ccontr)
          assume "\<not>(v \<noteq> v' \<or> a = a')"
          then have "v = v'" and "a \<noteq> a'" 
            by simp+
          thus False
            using a'_in_range_of_v a_in_range_of_v assms(1) v'_in_set_vs s'_of_v'_a'_is 
              s'_of_v_a_is s_of_v_is_Some_a strips_state_to_state_inverse_is_iii
            by force
        qed
    }
    moreover {
      have "s v \<noteq> None" 
        using assms(4)
        by simp
      then have "?s' (v, a) = Some True" 
        using strips_state_to_state_inverse_is_i[OF assms(1, 3) _ assms(5)] 
          assms(4)
        by simp
      (* TODO slow *)
      hence "(v, a) \<in> set ?as" 
        using all_possible_assignments_for_set_is assms(3, 5) nb
        by simp
    }
    ultimately have "map_of ?as v = Some a" 
      using map_of_constant_assignments_defined_if[of ?as v a] 
      by blast
  }
  \<comment> \<open> TODO slow. \<close>
  thus ?thesis
    unfolding SAS_Plus_STRIPS.strips_state_to_state_def
      strips_state_to_state_def all_possible_assignments_for_def
    by simp
qed

(* TODO the constraints on the state @{text "s"} could be refactored into a definition of valid 
states for a problem description. *)
(* TODO The proof is not very elegant. Should be simplified. *)
\<comment> \<open> Show that that \<open>\<phi>\<^sub>S\<inverse> \<Psi>\<close> is the inverse of \<open>\<phi>\<^sub>S \<Psi>\<close>. The additional constraints 
\<^term>\<open>dom s = set ((\<Psi>)\<^sub>\<V>\<^sub>+)\<close> and \<^term>\<open>\<forall>v \<in> dom s. the (s v) \<in> \<R>\<^sub>+ \<Psi> v\<close> are needed because the 
transformation functions only take into account variables and domains declared in the problem 
description. They also sufficiently characterize a state that was transformed from SAS+ to STRIPS. \<close>
lemma strips_state_to_state_inverse_is:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "dom s \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom s. the (s v) \<in> \<R>\<^sub>+ \<Psi> v" 
  shows "s = (\<phi>\<^sub>S\<inverse> \<Psi> (\<phi>\<^sub>S \<Psi> s))"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?D = "range_of \<Psi>"
  let ?s' = "\<phi>\<^sub>S \<Psi> s" 
  let ?s'' = "\<phi>\<^sub>S\<inverse> \<Psi> ?s'"
  \<comment> \<open> NOTE Show the thesis by proving that @{text "s"} and @{text "?s'"} are mutual submaps. \<close>
  {
    fix v
    assume v_in_dom_s: "v \<in> dom s"
    then have v_in_set_vs: "v \<in> set ?vs" 
      using assms(2) 
      by auto
    then obtain a 
      where the_s_v_is_a: "s v = Some a" 
        and a_in_dom_v: "a \<in> \<R>\<^sub>+ \<Psi> v" 
      using assms(2, 3) v_in_dom_s
      by force
    moreover have "?s'' v = Some a" 
      using strips_state_to_state_inverse_is_iv[OF assms(1, 2)] v_in_set_vs
        the_s_v_is_a a_in_dom_v 
      by force
    ultimately have "s v = ?s'' v"
      by argo
  } note nb = this
  moreover {
    fix v
    assume "v \<in> dom ?s''"
    then obtain a 
      where "a \<in> \<R>\<^sub>+ \<Psi> v" 
        and "?s' (v, a) = Some True" 
      using strips_state_to_state_dom_is[OF assms(1)]
      by blast
    then have "(v, a) \<in> dom ?s'" 
      by blast
    then have "s v \<noteq> None" 
      using state_to_strips_state_dom_is[OF assms(1)]
      by simp
    then obtain a where "s v = Some a" 
      by blast
    hence "?s'' v = s v"
      using nb 
      by fastforce
  }
  \<comment> \<open> TODO slow.\<close>
  ultimately show ?thesis 
    using map_le_antisym[of s ?s''] map_le_def
    unfolding strips_state_to_state_def 
      state_to_strips_state_def
    by blast
qed

\<comment> \<open> An important lemma which shows that the submap relation does not change if we transform the 
states on either side from SAS+ to STRIPS. 
% TODO what is this called generally? Predicate monotony?? \<close>
lemma state_to_strips_state_map_le_iff:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "dom s \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    and "\<forall>v \<in> dom s. the (s v) \<in> \<R>\<^sub>+ \<Psi> v" 
  shows "s \<subseteq>\<^sub>m t \<longleftrightarrow> (\<phi>\<^sub>S \<Psi> s) \<subseteq>\<^sub>m (\<phi>\<^sub>S \<Psi> t)"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?D = "range_of \<Psi>"
    and ?s' = "\<phi>\<^sub>S \<Psi> s" 
    and ?t' = "\<phi>\<^sub>S \<Psi> t" 
  show ?thesis
    proof (rule iffI)
      assume s_map_le_t: "s \<subseteq>\<^sub>m t"
      {
        fix v a
        assume "(v, a) \<in> dom ?s'" 
        moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" and "s v \<noteq> None" and "a \<in> \<R>\<^sub>+ \<Psi> v"
          using state_to_strips_state_dom_is[OF assms(1)] calculation 
          by blast+
        moreover have "?s' (v, a) = Some (the (s v) = a)"
          using state_to_strips_state_range_is[OF assms(1)] calculation(1) 
          by meson
        moreover have "v \<in> dom s" 
          using calculation(3)
          by auto 
        moreover have "s v = t v" 
          using s_map_le_t calculation(6) 
          unfolding map_le_def
          by blast
        moreover have "t v \<noteq> None" 
          using calculation(3, 7)
          by argo
        moreover have "(v, a) \<in> dom ?t'" 
          using state_to_strips_state_dom_is[OF assms(1)] calculation(2, 4, 8) 
          by blast
        moreover have "?t' (v, a) = Some (the (t v) = a)" 
          using state_to_strips_state_range_is[OF assms(1)] calculation(9)
          by simp
        ultimately have "?s' (v, a) = ?t' (v, a)"
          by presburger
      }
      thus "?s' \<subseteq>\<^sub>m ?t'" 
        unfolding map_le_def 
        by fast
    next
      assume s'_map_le_t': "?s' \<subseteq>\<^sub>m ?t'"
      {
        fix v 
        assume v_in_dom_s: "v \<in> dom s" 
        moreover obtain a where the_of_s_of_v_is_a: "the (s v) = a" 
          by blast
        moreover have v_in_vs: "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
          and s_of_v_is_not_None: "s v \<noteq> None" 
          and a_in_range_of_v: "a \<in> \<R>\<^sub>+ \<Psi> v"
          using assms(2, 3) v_in_dom_s calculation
          by blast+
        moreover have "(v, a) \<in> dom ?s'"  
          using state_to_strips_state_dom_is[OF assms(1)] 
            calculation(3, 4, 5)
          by simp
        moreover have "?s' (v, a) = ?t' (v, a)"
          using s'_map_le_t' calculation
          unfolding map_le_def 
          by blast
        moreover have "(v, a) \<in> dom ?t'" 
          using calculation 
          unfolding domIff
          by argo
        moreover have "?s' (v, a) = Some (the (s v) = a)"
          and "?t' (v, a) = Some (the (t v) = a)" 
          using state_to_strips_state_range_is[OF assms(1)] calculation
          by fast+
        moreover have "s v = Some a" 
          using calculation(2, 4) 
          by force
        moreover have "?s' (v, a) = Some True" 
          using calculation(9, 11)
          by fastforce
        moreover have "?t' (v, a) = Some True" 
          using calculation(7, 12)
          by argo
        moreover have "the (t v) = a" 
          using calculation(10, 13) try0
          by force
        moreover {
          have "v \<in> dom t" 
            using state_to_strips_state_dom_element_iff[OF assms(1)] 
              calculation(8) 
            by auto
          hence "t v = Some a"
            using calculation(14)
            by force
        }
        ultimately have "s v = t v"
          by argo
      }
      thus "s \<subseteq>\<^sub>m t"
        unfolding map_le_def
        by simp
    qed
qed

\<comment> \<open> We also show that \<open>\<phi>\<^sub>O\<inverse> \<Pi>\<close> is the inverse of \<open>\<phi>\<^sub>O \<Psi>\<close>. Note that this proof is completely 
mechanical since both the precondition and effect lists are simply being copied when transforming 
from SAS+ to STRIPS and when transforming back from STRIPS to SAS+. \<close>
(* TODO rename \<open>sasp_op_to_strips_inverse_is\<close> *)
(* TODO prune assumptions (not required) *)
lemma sas_plus_operator_inverse_is:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
  shows "(\<phi>\<^sub>O\<inverse> \<Psi> (\<phi>\<^sub>O \<Psi> op)) = op"
proof -
  let ?op = "\<phi>\<^sub>O\<inverse> \<Psi> (\<phi>\<^sub>O \<Psi> op)"
  have "precondition_of ?op = precondition_of op"
    unfolding SAS_Plus_STRIPS.strips_op_to_sasp_def
      strips_op_to_sasp_def
      SAS_Plus_STRIPS.sasp_op_to_strips_def
      sasp_op_to_strips_def
    by fastforce
  moreover have "effect_of ?op = effect_of op" 
    unfolding SAS_Plus_STRIPS.strips_op_to_sasp_def
      strips_op_to_sasp_def
      SAS_Plus_STRIPS.sasp_op_to_strips_def
      sasp_op_to_strips_def
    by force
  ultimately show ?thesis 
    by simp
qed

\<comment> \<open> Note that we have to make the assumption that \<open>op'\<close> is a member of the operator set of the 
induced STRIPS problem \<open>\<phi> \<Psi>\<close>. This implies that \<open>op'\<close> was transformed from an 
\<open>op \<in> operators_of \<Psi>\<close>. If we don't make this assumption, then multiple STRIPS operators of the 
form  \<open>\<lparr> precondition_of = [], add_effects_of = [], delete_effects_of = [(v, a), ...] \<rparr>\<close> correspond 
to one SAS+ operator (since the delete effects are being discarded in the transformation function). 
\<close>
lemma strips_operator_inverse_is:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)" 
  shows "(\<phi>\<^sub>O \<Psi> (\<phi>\<^sub>O\<inverse> \<Psi> op')) = op'" 
  proof -
    let ?\<Pi> = "\<phi> \<Psi>"
    obtain op where "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op" 
      using assms 
      by auto
    moreover have "\<phi>\<^sub>O\<inverse> \<Psi> op' = op" 
      using sas_plus_operator_inverse_is[OF assms(1) calculation(1)] calculation(2)
      by blast
    ultimately show ?thesis
      by argo
  qed

(* 
  \<^item> TODO Simplify | refactor proof. 
  \<^item> TODO make private. *)
lemma sas_plus_equivalent_to_strips_i_a_I:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "set ops' \<subseteq> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "STRIPS_Semantics.are_all_operators_applicable (\<phi>\<^sub>S \<Psi> s) ops'"
    and "op \<in> set [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
  shows "map_of (precondition_of op) \<subseteq>\<^sub>m (\<phi>\<^sub>S\<inverse> \<Psi> (\<phi>\<^sub>S \<Psi> s))" 
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
    and ?s' = "\<phi>\<^sub>S \<Psi> s" 
  let ?s = "\<phi>\<^sub>S\<inverse> \<Psi> ?s'" 
    and ?D = "range_of \<Psi>"
    and ?ops = "[\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
    and ?pre = "precondition_of op" 
  have nb\<^sub>1: "\<forall>(v, a) \<in> dom ?s'. 
    \<forall>(v, a') \<in> dom ?s'. 
      ?s' (v, a) = Some True \<and> ?s' (v, a') = Some True
      \<longrightarrow> (v, a) = (v, a')" 
    using state_to_strips_state_effect_consistent[OF assms(1)] 
    by blast
  {
    fix op'
    assume "op' \<in> set ops'" 
    moreover have "op' \<in> set ((?\<Pi>)\<^sub>\<O>)"
      using assms(2) calculation 
      by blast
    ultimately have "\<exists>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). op' = (\<phi>\<^sub>O \<Psi> op)" 
      by auto
  } note nb\<^sub>2 = this
  {
    fix op
    assume "op \<in> set ?ops" 
    then obtain op' where "op' \<in> set ops'" and "op = \<phi>\<^sub>O\<inverse> \<Psi> op'" 
      using assms(4) 
      by auto
    moreover obtain op'' where "op'' \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op''" 
      using nb\<^sub>2 calculation(1)
      by blast
    moreover have "op = op''"
      using sas_plus_operator_inverse_is[OF assms(1) calculation(3)] calculation(2, 4)  
      by blast
    ultimately have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
      by blast
  } note nb\<^sub>3 = this
  {
    fix op v a
    assume "op \<in> set ?ops" 
      and v_a_in_precondition_of_op': "(v, a) \<in> set (precondition_of op)"
    moreover obtain op' where "op' \<in> set ops'" and "op = \<phi>\<^sub>O\<inverse> \<Psi> op'" 
      using calculation(1) 
      by auto
    moreover have "strips_operator.precondition_of op' = precondition_of op" 
      using calculation(4) 
      unfolding SAS_Plus_STRIPS.strips_op_to_sasp_def
        strips_op_to_sasp_def
      by simp
    ultimately have "\<exists>op' \<in> set ops'. op = (\<phi>\<^sub>O\<inverse> \<Psi> op')
      \<and> (v, a) \<in> set (strips_operator.precondition_of op')" 
      by metis
  } note nb\<^sub>4 = this
  {
    fix op' v a
    assume "op' \<in> set ops'" 
      and v_a_in_precondition_of_op': "(v, a) \<in> set (strips_operator.precondition_of op')"
    moreover have s'_of_v_a_is_Some_True: "?s' (v, a) = Some True" 
      using assms(3) calculation(1, 2) 
      unfolding are_all_operators_applicable_set
      by blast
    moreover {
      obtain op where "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op" 
        using nb\<^sub>2 calculation(1) 
        by blast
      moreover have "strips_operator.precondition_of op' = precondition_of op" 
        using calculation(2) 
        unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
          sasp_op_to_strips_def
        by simp
      moreover have "(v, a) \<in> set (precondition_of op)"
        using v_a_in_precondition_of_op' calculation(3)
        by argo
      moreover have "is_valid_operator_sas_plus \<Psi> op" 
        using is_valid_problem_sas_plus_then(2) assms(1) calculation(1)
        unfolding is_valid_operator_sas_plus_def
        by auto
      moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" and "a \<in> \<R>\<^sub>+ \<Psi> v" 
        using is_valid_operator_sas_plus_then(1,2) calculation(4, 5)
        unfolding is_valid_operator_sas_plus_def
        by fastforce+
      moreover have "v \<in> dom ?s" 
        using strips_state_to_state_dom_is[OF assms(1), of ?s'] 
          s'_of_v_a_is_Some_True calculation(6, 7)
        by blast
      moreover have "(v, a) \<in> dom ?s'" 
        using s'_of_v_a_is_Some_True domIff 
        by blast
      ultimately have "?s v = Some a"
        using strips_state_to_state_range_is[OF assms(1) _ _ _ nb\<^sub>1] 
          s'_of_v_a_is_Some_True 
        by simp
    }
    hence "?s v = Some a".
  } note nb\<^sub>5 = this
  {
    fix v
    assume "v \<in> dom (map_of ?pre)"
    then obtain a where "map_of ?pre v = Some a"
      by fast
    moreover have "(v, a) \<in> set ?pre" 
      using map_of_SomeD calculation
      by fast
    moreover {
      have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
        using assms(4) nb\<^sub>3
        by blast
      then have "is_valid_operator_sas_plus \<Psi> op" 
        using is_valid_problem_sas_plus_then(2) assms(1)
        unfolding is_valid_operator_sas_plus_def
        by auto
      hence "\<forall>(v, a) \<in> set ?pre. \<forall>(v', a') \<in> set ?pre. v \<noteq> v' \<or> a = a'"
        using is_valid_operator_sas_plus_then(5)
        unfolding is_valid_operator_sas_plus_def
        by fast
    }
    moreover have "map_of ?pre v = Some a"
      using map_of_constant_assignments_defined_if[of ?pre] calculation(2, 3)
      by blast
    moreover obtain op' where "op' \<in> set ops'" 
      and "(v, a) \<in> set (strips_operator.precondition_of op')" 
      using nb\<^sub>4[OF assms(4) calculation(2)]
      by blast
    moreover have "?s v = Some a" 
      using nb\<^sub>5 calculation(5, 6) 
      by fast
    ultimately have "map_of ?pre v = ?s v"
      by argo
  }
  thus ?thesis 
    unfolding map_le_def
    by blast
qed

lemma to_sas_plus_list_of_transformed_sas_plus_problem_operators_structure:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "set ops' \<subseteq> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "op \<in> set [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
  shows "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+) \<and> (\<exists>op' \<in> set ops'. op' = \<phi>\<^sub>O \<Psi> op)"
proof - 
  let ?\<Pi> = "\<phi> \<Psi>"
  obtain op' where "op' \<in> set ops'" and "op = \<phi>\<^sub>O\<inverse> \<Psi> op'" 
    using assms(3) 
    by auto
  moreover have "op' \<in> set ((?\<Pi>)\<^sub>\<O>)"
    using assms(2) calculation(1) 
    by blast
  moreover obtain op'' where "op'' \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op''" 
    using calculation(3) 
    by auto
  moreover have "op = op''" 
    using sas_plus_operator_inverse_is[OF assms(1) calculation(4)] calculation(2, 5) 
    by presburger
  ultimately show ?thesis 
    by blast
qed

(* \<^item> TODO Prune premises (2nd premise and \<open>are_all_operators_applicable s' ops'\<close> can be removed?). 
   \<^item> TODO make private. 
   \<^item> TODO adjust nb indexes *)
lemma sas_plus_equivalent_to_strips_i_a_II:
  fixes \<Psi> :: "('variable, 'domain) sas_plus_problem"
  fixes s :: "('variable, 'domain) state" 
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "set ops' \<subseteq> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "STRIPS_Semantics.are_all_operators_applicable (\<phi>\<^sub>s \<Psi> s) ops' 
      \<and> STRIPS_Semantics.are_all_operator_effects_consistent ops'"
  shows "are_all_operator_effects_consistent [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
proof -
  let ?s' = "\<phi>\<^sub>S \<Psi> s"
  let ?s = "\<phi>\<^sub>S\<inverse> \<Psi> ?s'"
    and ?ops = "[\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']"
    and ?\<Pi> = "\<phi> \<Psi>"
  have nb: "\<forall>(v, a) \<in> dom ?s'. 
    \<forall>(v, a') \<in> dom ?s'. 
      ?s' (v, a) = Some True \<and> ?s' (v, a') = Some True
      \<longrightarrow> (v, a) = (v, a')" 
    using state_to_strips_state_effect_consistent[OF assms(1)] 
    by blast
  {
    fix op\<^sub>1' op\<^sub>2'
    assume "op\<^sub>1' \<in> set ops'" and "op\<^sub>2' \<in> set ops'"
    hence "STRIPS_Semantics.are_operator_effects_consistent op\<^sub>1' op\<^sub>2'" 
      using assms(3)
      unfolding STRIPS_Semantics.are_all_operator_effects_consistent_def list_all_iff
      by blast
  } note nb\<^sub>1 = this
  {
    fix op\<^sub>1 op\<^sub>1' op\<^sub>2 op\<^sub>2'
    assume op\<^sub>1_in_ops: "op\<^sub>1 \<in> set ?ops"
      and op\<^sub>1'_in_ops': "op\<^sub>1' \<in> set ops'" 
      and op\<^sub>1'_is: "op\<^sub>1' = \<phi>\<^sub>O \<Psi> op\<^sub>1" 
      and is_valid_op\<^sub>1: "is_valid_operator_sas_plus \<Psi> op\<^sub>1"
      and op\<^sub>2_in_ops: "op\<^sub>2 \<in> set ?ops"
      and op\<^sub>2'_in_ops': "op\<^sub>2' \<in> set ops'" 
      and op\<^sub>2'_is: "op\<^sub>2' = \<phi>\<^sub>O \<Psi> op\<^sub>2"
      and is_valid_op\<^sub>2: "is_valid_operator_sas_plus \<Psi> op\<^sub>2"
    have "\<forall>(v, a) \<in> set (add_effects_of op\<^sub>1'). \<forall>(v', a') \<in> set (add_effects_of op\<^sub>2').
          v \<noteq> v' \<or> a = a'" 
      proof (rule ccontr)
        assume "\<not>(\<forall>(v, a) \<in> set (add_effects_of op\<^sub>1'). \<forall>(v', a') \<in> set (add_effects_of op\<^sub>2'). 
        v \<noteq> v' \<or> a = a')"
        then obtain v v' a a' where "(v, a) \<in> set (add_effects_of op\<^sub>1')" 
          and "(v', a') \<in> set (add_effects_of op\<^sub>2')" 
          and "v = v'" 
          and "a \<noteq> a'" 
          by blast
        \<comment> \<open> TODO slow. \<close>
        moreover have "(v, a) \<in> set (effect_of op\<^sub>1)"  
          using op\<^sub>1'_is op\<^sub>2'_is calculation(1, 2)
          unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
            sasp_op_to_strips_def 
          by force
        moreover {
          have "(v', a') \<in> set (effect_of op\<^sub>2)" 
            using op\<^sub>2'_is calculation(2) 
            unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
              sasp_op_to_strips_def
            by force
          hence "a' \<in> \<R>\<^sub>+ \<Psi> v"
            using is_valid_operator_sas_plus_then is_valid_op\<^sub>2 calculation(3)
            by fastforce
        }
        moreover have "(v, a') \<in> set (delete_effects_of op\<^sub>1')" 
          using sasp_op_to_strips_set_delete_effects_is
            op\<^sub>1'_is is_valid_op\<^sub>1 calculation(3, 4, 5, 6)
          by blast
        moreover have "\<not>STRIPS_Semantics.are_operator_effects_consistent op\<^sub>1' op\<^sub>2'" 
          unfolding STRIPS_Semantics.are_operator_effects_consistent_def list_ex_iff 
          using calculation(2, 3, 7)
          by meson
        ultimately show False 
          using assms(3) op\<^sub>1'_in_ops' op\<^sub>2'_in_ops'
          unfolding STRIPS_Semantics.are_all_operator_effects_consistent_def list_all_iff
          by blast
      qed
  } note nb\<^sub>3 = this
  {
    fix op\<^sub>1 op\<^sub>2
    assume op\<^sub>1_in_ops: "op\<^sub>1 \<in> set ?ops" and op\<^sub>2_in_ops: "op\<^sub>2 \<in> set ?ops" 
    moreover have op\<^sub>1_in_operators_of_\<Psi>: "op\<^sub>1 \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
      and op\<^sub>2_in_operators_of_\<Psi>: "op\<^sub>2 \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
      using to_sas_plus_list_of_transformed_sas_plus_problem_operators_structure[OF 
          assms(1, 2)] calculation
      by blast+
    moreover have is_valid_operator_op\<^sub>1: "is_valid_operator_sas_plus \<Psi> op\<^sub>1" 
      and is_valid_operator_op\<^sub>2: "is_valid_operator_sas_plus \<Psi> op\<^sub>2" 
      using is_valid_problem_sas_plus_then(2) op\<^sub>1_in_operators_of_\<Psi> op\<^sub>2_in_operators_of_\<Psi>
        assms(1)
      unfolding is_valid_operator_sas_plus_def
      by auto+
    moreover obtain op\<^sub>1' op\<^sub>2' 
      where op\<^sub>1_in_ops': "op\<^sub>1' \<in> set ops'" 
        and op\<^sub>1_is: "op\<^sub>1' = \<phi>\<^sub>O \<Psi> op\<^sub>1"
        and op\<^sub>2_in_ops': "op\<^sub>2' \<in> set ops'"
        and op\<^sub>2_is: "op\<^sub>2' = \<phi>\<^sub>O \<Psi> op\<^sub>2"
      using to_sas_plus_list_of_transformed_sas_plus_problem_operators_structure[OF 
          assms(1, 2)] op\<^sub>1_in_ops op\<^sub>2_in_ops
      by blast
    \<comment> \<open> TODO slow.\<close>
    ultimately have "\<forall>(v, a) \<in> set (add_effects_of op\<^sub>1'). \<forall>(v', a') \<in> set (add_effects_of op\<^sub>2').
          v \<noteq> v' \<or> a = a'" 
      using nb\<^sub>3 
      by auto
    hence "are_operator_effects_consistent op\<^sub>1 op\<^sub>2"
      using op\<^sub>1_is op\<^sub>2_is 
      unfolding are_operator_effects_consistent_def
        sasp_op_to_strips_def 
        SAS_Plus_STRIPS.sasp_op_to_strips_def
        list_all_iff Let_def
      by simp
  }
  thus ?thesis 
    unfolding are_all_operator_effects_consistent_def list_all_iff 
    by fast
qed

\<comment> \<open> A technical lemmas used in \<open>sas_plus_equivalent_to_strips_i_a\<close> showing that 
the execution precondition is linear w.r.t. to STRIPS transformation to SAS+. 

The second premise states that the given STRIPS state corresponds to a consistent SAS+ state (i.e.
no two assignments of the same variable to different values exist). \<close>
(* 
  \<^item> TODO make private. 
  \<^item> TODO decrement suffix *)
lemma sas_plus_equivalent_to_strips_i_a_IV: 
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "set ops' \<subseteq> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "STRIPS_Semantics.are_all_operators_applicable (\<phi>\<^sub>S \<Psi> s) ops' 
      \<and> STRIPS_Semantics.are_all_operator_effects_consistent ops'"
  shows "are_all_operators_applicable_in (\<phi>\<^sub>S\<inverse> \<Psi> (\<phi>\<^sub>S \<Psi> s)) [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops'] \<and>
    are_all_operator_effects_consistent [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
    and ?s' = "\<phi>\<^sub>S \<Psi> s"
  let ?vs' = "strips_problem.variables_of ?\<Pi>"
    and ?ops' = "strips_problem.operators_of ?\<Pi>" 
    and ?vs = "variables_of \<Psi>"
    and ?D = "range_of \<Psi>"
    and ?s = "\<phi>\<^sub>S\<inverse> \<Psi> ?s'"
    and ?ops = "[\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']"
  have nb: "\<forall>(v, a) \<in> dom ?s'. 
    \<forall>(v, a') \<in> dom (\<phi>\<^sub>S \<Psi> s). 
      ?s' (v, a) = Some True \<and> ?s' (v, a') = Some True
      \<longrightarrow> (v, a) = (v, a')" 
    using state_to_strips_state_effect_consistent[OF assms(1)] 
    by blast
  {
    have "STRIPS_Semantics.are_all_operators_applicable ?s' ops'" 
      using assms(3)
      by simp
    moreover have "list_all (\<lambda>op. map_of (precondition_of op) \<subseteq>\<^sub>m ?s) ?ops"
      using sas_plus_equivalent_to_strips_i_a_I[OF assms(1) assms(2)] calculation
      unfolding list_all_iff
      by blast
    moreover have "list_all (\<lambda>op. list_all (are_operator_effects_consistent op) ?ops) ?ops" 
      using sas_plus_equivalent_to_strips_i_a_II assms nb
      unfolding are_all_operator_effects_consistent_def is_valid_operator_sas_plus_def list_all_iff 
      by blast
    ultimately have "are_all_operators_applicable_in ?s ?ops" 
      unfolding are_all_operators_applicable_in_def is_operator_applicable_in_def list_all_iff
      by argo
  }
  moreover have "are_all_operator_effects_consistent ?ops" 
    using sas_plus_equivalent_to_strips_i_a_II assms nb
    by simp
  ultimately show ?thesis
    by simp
qed

(* TODO:
  \<^item> prune premises + make private. 
  \<^item> decrement suffixes 
*)
lemma sas_plus_equivalent_to_strips_i_a_VI:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "dom s \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom s. the (s v) \<in> \<R>\<^sub>+ \<Psi> v" 
    and "set ops' \<subseteq> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "are_all_operators_applicable_in s [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops'] \<and>
      are_all_operator_effects_consistent [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']"  
  shows "STRIPS_Semantics.are_all_operators_applicable (\<phi>\<^sub>S \<Psi> s) ops'"
proof -   
  let ?vs = "variables_of \<Psi>" 
    and ?D = "range_of \<Psi>"
    and ?\<Pi> = "\<phi> \<Psi>" 
    and ?ops = "[\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
    and ?s' = "\<phi>\<^sub>S \<Psi> s"
  \<comment> \<open> TODO refactor. \<close>
  {
    fix op' 
    assume "op' \<in> set ops'" 
    moreover obtain op where "op \<in> set ?ops" and "op = \<phi>\<^sub>O\<inverse> \<Psi> op'" 
      using calculation
      by force
    moreover obtain op'' where "op'' \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op''" 
      using assms(4) calculation(1) 
      by auto
    moreover have "is_valid_operator_sas_plus \<Psi> op''" 
      using is_valid_problem_sas_plus_then(2) assms(1) calculation(4)
      unfolding is_valid_operator_sas_plus_def
      by auto
    moreover have "op = op''" 
      using sas_plus_operator_inverse_is[OF assms(1)] calculation(3, 4, 5)
      by blast
    ultimately have "\<exists>op \<in> set ?ops. op \<in> set ?ops \<and> op = (\<phi>\<^sub>O\<inverse> \<Psi> op') 
      \<and> is_valid_operator_sas_plus \<Psi> op"
      by blast
  } note nb\<^sub>1 = this
  have nb\<^sub>2: "\<forall>(v, a) \<in> dom ?s'. 
    \<forall>(v, a') \<in> dom ?s'. 
      ?s' (v, a) = Some True \<and> ?s' (v, a') = Some True
      \<longrightarrow> (v, a) = (v, a')" 
    using state_to_strips_state_effect_consistent[OF assms(1), of _ _ s]
    by blast
  {
    fix op
    assume "op \<in> set ?ops" 
    hence "map_of (precondition_of op) \<subseteq>\<^sub>m s" 
      using assms(5) 
      unfolding are_all_operators_applicable_in_def 
        is_operator_applicable_in_def list_all_iff
      by blast
  } note nb\<^sub>3 = this
  {
    fix op'
    assume "op' \<in> set ops'" 
    then obtain op where op_in_ops: "op \<in> set ?ops" 
      and op_is: "op = (\<phi>\<^sub>O\<inverse> \<Psi> op')" 
      and is_valid_operator_op: "is_valid_operator_sas_plus \<Psi> op" 
      using nb\<^sub>1
      by force
    moreover have preconditions_are_consistent: 
      "\<forall>(v, a) \<in> set (precondition_of op). \<forall>(v', a') \<in> set (precondition_of op). v \<noteq> v' \<or> a = a'" 
      using is_valid_operator_sas_plus_then(5) calculation(3) 
      unfolding is_valid_operator_sas_plus_def
      by fast
    moreover {
      fix v a
      assume "(v, a) \<in> set (strips_operator.precondition_of op')"
      moreover have v_a_in_precondition_of_op: "(v, a) \<in> set (precondition_of op)" 
        using op_is calculation 
        unfolding SAS_Plus_STRIPS.strips_op_to_sasp_def
          strips_op_to_sasp_def
        by auto
      moreover have "map_of (precondition_of op) v = Some a" 
        using map_of_constant_assignments_defined_if[OF 
            preconditions_are_consistent calculation(2)]
        by blast
      moreover have s_of_v_is: "s v = Some a" 
        using nb\<^sub>3[OF op_in_ops] calculation(3) 
        unfolding map_le_def 
        by force
      moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" and "a \<in> \<R>\<^sub>+ \<Psi> v" 
        using is_valid_operator_sas_plus_then(1, 2) is_valid_operator_op
          v_a_in_precondition_of_op 
        unfolding is_valid_operator_sas_plus_def 
          SAS_Plus_Representation.is_valid_operator_sas_plus_def Let_def list_all_iff ListMem_iff
        by auto+
      moreover have "(v, a) \<in> dom ?s'" 
        using state_to_strips_state_dom_is[OF assms(1)] s_of_v_is 
        calculation 
        by simp
      moreover have "(\<phi>\<^sub>S\<inverse> \<Psi> ?s') v = Some a" 
        using strips_state_to_state_inverse_is[OF assms(1, 2, 3)] s_of_v_is
        by argo
      \<comment> \<open> TODO slow. \<close>
      ultimately have "?s' (v, a) = Some True" 
        using strips_state_to_state_range_is[OF assms(1)] nb\<^sub>2 
        by auto
    }
    ultimately have "\<forall>(v, a) \<in> set (strips_operator.precondition_of op'). ?s' (v, a) = Some True" 
      by fast
  }
  thus ?thesis 
    unfolding are_all_operators_applicable_def is_operator_applicable_in_def 
      STRIPS_Representation.is_operator_applicable_in_def list_all_iff
    by simp
qed

(* TODO Prune premises. *)
lemma sas_plus_equivalent_to_strips_i_a_VII:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "dom s \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    and "\<forall>v \<in> dom s. the (s v) \<in> \<R>\<^sub>+ \<Psi> v" 
    and "set ops' \<subseteq> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "are_all_operators_applicable_in s [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops'] \<and>
    are_all_operator_effects_consistent [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']"  
  shows "STRIPS_Semantics.are_all_operator_effects_consistent ops'"
proof - 
  let ?s' = "\<phi>\<^sub>S \<Psi> s" 
    and ?ops = "[\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']"
    and ?D = "range_of \<Psi>"
    and ?\<Pi> = "\<phi> \<Psi>"
  \<comment> \<open> TODO refactor. \<close>
  {
    fix op' 
    assume "op' \<in> set ops'" 
    moreover obtain op where "op \<in> set ?ops" and "op = \<phi>\<^sub>O\<inverse> \<Psi> op'" 
      using calculation
      by force
    moreover obtain op'' where "op'' \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op''" 
      using assms(4) calculation(1) 
      by auto
    moreover have "is_valid_operator_sas_plus \<Psi> op''" 
      using is_valid_problem_sas_plus_then(2) assms(1) calculation(4)
      unfolding is_valid_operator_sas_plus_def
      by auto
    moreover have "op = op''" 
      using sas_plus_operator_inverse_is[OF assms(1)] calculation(3, 4, 5)
      by blast
    ultimately have "\<exists>op \<in> set ?ops. op \<in> set ?ops \<and> op' = (\<phi>\<^sub>O \<Psi> op)
      \<and> is_valid_operator_sas_plus \<Psi> op"
      by blast
  } note nb\<^sub>1 = this  
  {
    fix op\<^sub>1' op\<^sub>2'
    assume "op\<^sub>1' \<in> set ops'" 
      and "op\<^sub>2' \<in> set ops'" 
      and "\<exists>(v, a) \<in> set (add_effects_of op\<^sub>1'). \<exists>(v', a') \<in> set (delete_effects_of op\<^sub>2').
        (v, a) = (v', a')" 
    moreover obtain op\<^sub>1 op\<^sub>2
      where "op\<^sub>1 \<in> set ?ops" 
          and "op\<^sub>1' = \<phi>\<^sub>O \<Psi> op\<^sub>1" 
          and "is_valid_operator_sas_plus \<Psi> op\<^sub>1"
        and "op\<^sub>2 \<in> set ?ops" 
          and "op\<^sub>2' = \<phi>\<^sub>O \<Psi> op\<^sub>2" 
          and is_valid_op\<^sub>2: "is_valid_operator_sas_plus \<Psi> op\<^sub>2"
      using nb\<^sub>1 calculation(1, 2)
      by meson
    moreover obtain v v' a a' 
      where "(v, a) \<in> set (add_effects_of op\<^sub>1')" 
        and "(v', a') \<in> set (delete_effects_of op\<^sub>2')"
        and "(v, a) = (v', a')" 
      using calculation
      by blast
    moreover have "(v, a) \<in> set (effect_of op\<^sub>1)" 
      using calculation(5, 10) 
      unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
        sasp_op_to_strips_def
      by fastforce
    moreover have "v = v'" and "a = a'"
      using calculation(12) 
      by simp+
    \<comment> \<open> The next proof block shows that \<open>(v', a')\<close> is constructed from an effect \<open>(v'', a'')\<close>
      s.t. \<open>a' \<noteq> a''\<close>.  \<close>
    moreover {
      (* TODO slow. *)
      have "(v', a') \<in> (\<Union>(v'', a'') \<in> set (effect_of op\<^sub>2). 
        { (v'', a''') | a'''. a''' \<in> (\<R>\<^sub>+ \<Psi> v'') \<and>  a''' \<noteq> a'' })"
        using sasp_op_to_strips_set_delete_effects_is 
          calculation(8, 11) is_valid_op\<^sub>2 
        by blast
      then obtain v'' a'' where "(v'', a'') \<in> set (effect_of op\<^sub>2)" 
        and "(v', a') \<in> { (v'', a''') | a'''. a''' \<in> (\<R>\<^sub>+ \<Psi> v'') \<and>  a''' \<noteq> a'' }"
        by blast
      moreover have "(v', a'') \<in> set (effect_of op\<^sub>2)" 
        using calculation 
        by blast
      moreover have "a' \<in> \<R>\<^sub>+ \<Psi> v''" and "a' \<noteq> a''"
        using calculation(1, 2) 
        by fast+
      ultimately have "\<exists>a''. (v', a'') \<in> set (effect_of op\<^sub>2) \<and> a' \<in> (\<R>\<^sub>+ \<Psi> v') 
        \<and> a' \<noteq> a''" 
        by blast
    }
    moreover obtain a'' where "(v', a'') \<in> set (effect_of op\<^sub>2)" 
      and "a' \<in> \<R>\<^sub>+ \<Psi> v'"
      and "a' \<noteq> a''"
      using calculation(16) 
      by blast
    moreover have "\<exists>(v, a) \<in> set (effect_of op\<^sub>1). (\<exists>(v', a') \<in> set (effect_of op\<^sub>2). 
      v = v' \<and> a \<noteq> a')"
      using calculation(13, 14, 15, 17, 19)
      by blast
    moreover have "\<not>are_operator_effects_consistent op\<^sub>1 op\<^sub>2"
      unfolding are_operator_effects_consistent_def list_all_iff
      using calculation(20)
      by fastforce
    ultimately have "\<not>are_all_operator_effects_consistent ?ops" 
      unfolding are_all_operator_effects_consistent_def list_all_iff
      by meson
  } note nb\<^sub>2 = this
  {
    fix op\<^sub>1' op\<^sub>2'
    assume op\<^sub>1'_in_ops: "op\<^sub>1' \<in> set ops'" and op\<^sub>2'_in_ops: "op\<^sub>2' \<in> set ops'" 
    have "STRIPS_Semantics.are_operator_effects_consistent op\<^sub>1' op\<^sub>2'"
      proof (rule ccontr)
        assume "\<not>STRIPS_Semantics.are_operator_effects_consistent op\<^sub>1' op\<^sub>2'"
        then consider (A) "\<exists>(v, a) \<in> set (add_effects_of op\<^sub>1'). 
          \<exists>(v', a') \<in> set (delete_effects_of op\<^sub>2'). (v, a) = (v', a')"
          | (B) "\<exists>(v, a) \<in> set (add_effects_of op\<^sub>2'). 
          \<exists>(v', a') \<in> set (delete_effects_of op\<^sub>1'). (v, a) = (v', a')"
          unfolding STRIPS_Semantics.are_operator_effects_consistent_def list_ex_iff
          by fastforce
        thus False 
          using nb\<^sub>2[OF op\<^sub>1'_in_ops op\<^sub>2'_in_ops] nb\<^sub>2[OF op\<^sub>2'_in_ops op\<^sub>1'_in_ops] assms(5)
          by (cases, argo, force)
      qed
  }
  thus ?thesis 
    unfolding STRIPS_Semantics.are_all_operator_effects_consistent_def 
      STRIPS_Semantics.are_operator_effects_consistent_def list_all_iff
    by blast
qed

lemma sas_plus_equivalent_to_strips_i_a_VIII:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "dom s \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    and "\<forall>v \<in> dom s. the (s v) \<in> \<R>\<^sub>+ \<Psi> v" 
    and "set ops' \<subseteq> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "are_all_operators_applicable_in s [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops'] \<and>
    are_all_operator_effects_consistent [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']"  
  shows "STRIPS_Semantics.are_all_operators_applicable (\<phi>\<^sub>S \<Psi> s) ops' 
    \<and> STRIPS_Semantics.are_all_operator_effects_consistent ops'"
  using sas_plus_equivalent_to_strips_i_a_VI sas_plus_equivalent_to_strips_i_a_VII assms
  by fastforce

(* TODO refactor. *)
lemma sas_plus_equivalent_to_strips_i_a_IX:
  assumes "dom s \<subseteq> V"
    and "\<forall>op \<in> set ops. \<forall>(v, a) \<in> set (effect_of op). v \<in> V" 
  shows "dom (execute_parallel_operator_sas_plus s ops) \<subseteq> V"  
proof -
  show ?thesis 
    using assms
    proof (induction ops arbitrary: s)
      case Nil 
      then show ?case
        unfolding execute_parallel_operator_sas_plus_def
        by simp 
    next
      case (Cons op ops)
      let ?s' = "s ++ map_of (effect_of op)" 
      \<comment> \<open> TODO Wrap IH instantiation in block. \<close>
      {
        have "\<forall>(v, a) \<in> set (effect_of op). v \<in> V" 
          using Cons.prems(2)
          by fastforce
        moreover have "fst ` set (effect_of op) \<subseteq> V" 
          using calculation
          by fastforce
        ultimately have "dom ?s' \<subseteq> V" 
          unfolding dom_map_add dom_map_of_conv_image_fst
          using Cons.prems(1)
          by blast
      }
      moreover have "\<forall>op \<in> set ops. \<forall>(v, a) \<in> set (effect_of op). v \<in> V"
        using Cons.prems(2)
        by fastforce
      ultimately have "dom (execute_parallel_operator_sas_plus ?s' ops) \<subseteq> V"
        using Cons.IH[of ?s']
        by fast
      thus ?case 
        unfolding execute_parallel_operator_sas_plus_cons.
    qed
qed

\<comment> \<open> NOTE Show that the domain value constraint on states is monotonous w.r.t. to valid operator 
execution. I.e. if a parallel operator is executed on a state for which the domain value constraint 
holds, the domain value constraint will also hold on the resultant state. \<close>
(* TODO refactor. 
  TODO Rewrite lemma without domain function, i.e. \<open>set (the (D v)) \<leadsto> D\<close> *)
lemma sas_plus_equivalent_to_strips_i_a_X:
  assumes "dom s \<subseteq> V"
    and "V \<subseteq> dom D"
    and "\<forall>v \<in> dom s. the (s v) \<in> set (the (D v))" 
    and "\<forall>op \<in> set ops. \<forall>(v, a) \<in> set (effect_of op). v \<in> V \<and> a \<in> set (the (D v))" 
  shows "\<forall>v \<in> dom (execute_parallel_operator_sas_plus s ops). 
    the (execute_parallel_operator_sas_plus s ops v) \<in> set (the (D v))"  
proof -
  show ?thesis 
    using assms
    proof (induction ops arbitrary: s)
      case Nil 
      then show ?case
        unfolding execute_parallel_operator_sas_plus_def
        by simp 
    next
      case (Cons op ops)
      let ?s' = "s ++ map_of (effect_of op)" 
      {
        {
          have "\<forall>(v, a) \<in> set (effect_of op). v \<in> V" 
            using Cons.prems(4)
            by fastforce
          moreover have "fst ` set (effect_of op) \<subseteq> V" 
            using calculation
            by fastforce
          ultimately have "dom ?s' \<subseteq> V" 
            unfolding dom_map_add dom_map_of_conv_image_fst
            using Cons.prems(1)
            by blast
        }
        moreover {
          fix v
          assume v_in_dom_s': "v \<in> dom ?s'"
          hence "the (?s' v) \<in> set (the (D v))" 
            proof (cases "v \<in> dom (map_of (effect_of op))")
              case True
              moreover have "?s' v = (map_of (effect_of op)) v"
                unfolding map_add_dom_app_simps(1)[OF True]
                by blast
              moreover obtain a where "(map_of (effect_of op)) v = Some a" 
                using calculation(1) 
                by fast
              moreover have "(v, a) \<in> set (effect_of op)" 
                using map_of_SomeD calculation(3)
                by fast
              moreover have "a \<in> set (the (D v))"
                using Cons.prems(4) calculation(4)
                by fastforce
              ultimately show ?thesis
                by force
            next
              case False
              then show ?thesis
                unfolding map_add_dom_app_simps(3)[OF False]
                using Cons.prems(3) v_in_dom_s'
                by fast
            qed
        }
        moreover have "\<forall>op \<in> set ops. \<forall>(v, a) \<in> set (effect_of op). v \<in> V \<and> a \<in> set (the (D v))" 
          using Cons.prems(4)
          by auto
        ultimately have "\<forall>v \<in> dom (execute_parallel_operator_sas_plus ?s' ops).
          the (execute_parallel_operator_sas_plus ?s' ops v) \<in> set (the (D v))" 
          using Cons.IH[of "s ++ map_of (effect_of op)", OF _ Cons.prems(2)]
          by meson
      }
      thus ?case 
        unfolding execute_parallel_operator_sas_plus_cons
        by blast
    qed
qed

lemma transfom_sas_plus_problem_to_strips_problem_operators_valid:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
  obtains op 
  where "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
    and "op' = (\<phi>\<^sub>O \<Psi> op)" "is_valid_operator_sas_plus \<Psi> op" 
proof -
  {
    obtain op where "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op" 
      using assms 
      by auto
    moreover have "is_valid_operator_sas_plus \<Psi> op" 
      using is_valid_problem_sas_plus_then(2) assms(1) calculation(1)
      by auto
    ultimately have "\<exists>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). op' = (\<phi>\<^sub>O \<Psi> op)
      \<and> is_valid_operator_sas_plus \<Psi> op"
      by blast
  } 
  thus ?thesis 
    using that
    by blast
qed

lemma sas_plus_equivalent_to_strips_i_a_XI:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)" 
  shows "(\<phi>\<^sub>S \<Psi> s) ++ map_of (effect_to_assignments op') 
    = \<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op')))"
proof -
  let ?\<Pi> = "\<phi> \<Psi>" 
  let ?vs = "variables_of \<Psi>"
    and?ops = "operators_of \<Psi>" 
    and ?ops' = "strips_problem.operators_of ?\<Pi>"
  let ?s' = "\<phi>\<^sub>S \<Psi> s"                 
  let ?t = "?s' ++ map_of (effect_to_assignments op')"
    and ?t' = "\<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op')))"
  obtain op where op'_is: "op' = (\<phi>\<^sub>O \<Psi> op)" 
    and op_in_ops: "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
    and is_valid_operator_op: "is_valid_operator_sas_plus \<Psi> op"
    using transfom_sas_plus_problem_to_strips_problem_operators_valid[OF assms]
    by auto
  have nb\<^sub>1: "(\<phi>\<^sub>O\<inverse> \<Psi> op') = op" 
    using sas_plus_operator_inverse_is[OF assms(1)] op'_is op_in_ops 
    by blast
  \<comment> \<open> TODO refactor. \<close>
  {

    (*have "fst ` set (effect_to_assignments op') \<equiv>
fst ` ((\<lambda>v. (v, True)) ` set (add_effects_of op') \<union> (\<lambda>v. (v, False)) ` set (delete_effects_of op'))"
      
      by auto
    then*) have "dom (map_of (effect_to_assignments op')) 
      = set (strips_operator.add_effects_of op') \<union> set (strips_operator.delete_effects_of op')"
      unfolding dom_map_of_conv_image_fst
      by force
    \<comment> \<open> TODO slow.\<close>
    also have "\<dots> = set (effect_of op) \<union> set (strips_operator.delete_effects_of op')" 
      using op'_is 
      unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
        sasp_op_to_strips_def 
      by auto
    \<comment> \<open> TODO slow.\<close>
    finally have "dom (map_of (effect_to_assignments op')) = set (effect_of op)
      \<union> (\<Union>(v, a) \<in> set (effect_of op). { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })" 
      using sasp_op_to_strips_set_delete_effects_is[OF 
          is_valid_operator_op] op'_is
      by argo
  } note nb\<^sub>2 = this
  have nb\<^sub>3: "dom ?t = dom ?s' \<union> set (effect_of op)
    \<union> (\<Union>(v, a) \<in> set (effect_of op). { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })" 
    unfolding nb\<^sub>2 dom_map_add
    by blast
  \<comment> \<open> TODO refactor. \<close>
  have nb\<^sub>4: "dom (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) 
    = dom s \<union> fst ` set (effect_of op)"
    unfolding dom_map_add dom_map_of_conv_image_fst nb\<^sub>1
    by fast
  {
    let ?u = "s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))"
    have "dom ?t' = (\<Union>v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> ?u v \<noteq> None }. 
      { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })" 
      using state_to_strips_state_dom_is[OF assms(1)]
      by presburger
  } note nb\<^sub>5 = this
  \<comment> \<open> TODO refactor. \<close>
  have nb\<^sub>6: "set (add_effects_of op') = set (effect_of op)"
    using op'_is 
    unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
      sasp_op_to_strips_def
    by auto
  \<comment> \<open> TODO refactor. \<close>
  have nb\<^sub>7: "set (delete_effects_of op') = (\<Union>(v, a) \<in> set (effect_of op). 
      { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })" 
    using sasp_op_to_strips_set_delete_effects_is[OF 
        is_valid_operator_op] op'_is
    by argo
  \<comment> \<open> TODO refactor. \<close>
  {
    let ?Add = "set (effect_of op)" 
    let ?Delete = "(\<Union>(v, a) \<in> set (effect_of op). 
      { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })" 
    have dom_add: "dom (map_of (map (\<lambda>v. (v, True)) (add_effects_of op'))) = ?Add" 
      unfolding dom_map_of_conv_image_fst set_map image_comp comp_apply 
      using nb\<^sub>6
      by simp
    have dom_delete: "dom (map_of (map (\<lambda>v. (v, False)) (delete_effects_of op'))) = ?Delete"
      unfolding dom_map_of_conv_image_fst set_map image_comp comp_apply 
      using nb\<^sub>7
      by auto
    {
      {
        fix v a 
        assume v_a_in_dom_add: "(v, a) \<in> dom (map_of (map (\<lambda>v. (v, True)) (add_effects_of op')))"
        have "(v, a) \<notin> dom (map_of (map (\<lambda>v. (v, False)) (delete_effects_of op')))" 
          proof (rule ccontr) 
            assume "\<not>((v, a) \<notin> dom (map_of (map (\<lambda>v. (v, False)) (delete_effects_of op'))))"
            then have "(v, a) \<in> ?Delete" and "(v, a) \<in> ?Add"
              using dom_add dom_delete v_a_in_dom_add
              by argo+   
            moreover have "\<forall>(v', a') \<in> ?Add. v \<noteq> v' \<or> a = a'"
              using is_valid_operator_sas_plus_then(6) is_valid_operator_op
                calculation(2)
              unfolding is_valid_operator_sas_plus_def
              by fast
            ultimately show False
              by fast
          qed
      }
      hence "disjnt (dom (map_of (map (\<lambda>v. (v, True)) (add_effects_of op')))) 
        (dom (map_of (map (\<lambda>v. (v, False)) (delete_effects_of op'))))"
        unfolding disjnt_def Int_def
        using nb\<^sub>7
        by simp
    }
    hence "dom (map_of (map (\<lambda>v. (v, True)) (add_effects_of op'))) = ?Add"
      and "dom (map_of (map (\<lambda>v. (v, False)) (delete_effects_of op'))) = ?Delete"
      and "disjnt (dom (map_of (map (\<lambda>v. (v, True)) (add_effects_of op')))) 
        (dom (map_of (map (\<lambda>v. (v, False)) (delete_effects_of op'))))" 
      using dom_add dom_delete
      by blast+
  } note nb\<^sub>8 = this
  \<comment> \<open> TODO refactor. \<close>
  {
    let ?Add = "set (effect_of op)" 
    let ?Delete = "(\<Union>(v, a) \<in> set (effect_of op). 
      { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })" 
    \<comment> \<open> TODO slow.\<close>
    have "\<forall>(v, a) \<in> ?Add. map_of (effect_to_assignments op') (v, a) = Some True" 
      and "\<forall>(v, a) \<in> ?Delete. map_of (effect_to_assignments op') (v, a) = Some False"
      proof -
        {
          fix v a
          assume "(v, a) \<in> ?Add" 
          hence "map_of (effect_to_assignments op') (v, a) = Some True"
            unfolding effect_to_assignments_simp
            using  nb\<^sub>6 map_of_defined_if_constructed_from_list_of_constant_assignments[of 
                "map (\<lambda>v. (v, True)) (add_effects_of op')" True "add_effects_of op'"]
            by force
        }
        moreover {
          fix v a
          assume "(v, a) \<in> ?Delete"
          moreover have "(v, a) \<in> dom (map_of (map (\<lambda>v. (v, False)) (delete_effects_of op')))"
            using nb\<^sub>8(2) calculation(1)
            by argo
          moreover have "(v, a) \<notin> dom (map_of (map (\<lambda>v. (v, True)) (add_effects_of op')))" 
            using nb\<^sub>8
            unfolding disjnt_def 
            using calculation(1)
            by blast
          moreover have "map_of (effect_to_assignments op') (v, a) 
            = map_of (map (\<lambda>v. (v, False)) (delete_effects_of op')) (v, a)"
            unfolding effect_to_assignments_simp map_of_append 
            using map_add_dom_app_simps(3)[OF calculation(3)]
            by presburger 
          \<comment> \<open> TODO slow. \<close>
          ultimately have "map_of (effect_to_assignments op') (v, a) = Some False"
            using map_of_defined_if_constructed_from_list_of_constant_assignments[
                of "map (\<lambda>v. (v, False)) (delete_effects_of op')" False "delete_effects_of op'"]
               nb\<^sub>7
            by auto
        }
        ultimately show "\<forall>(v, a) \<in> ?Add. map_of (effect_to_assignments op') (v, a) = Some True" 
          and "\<forall>(v, a) \<in> ?Delete. map_of (effect_to_assignments op') (v, a) = Some False" 
          by blast+
      qed
  } note nb\<^sub>9 = this
  {
    fix v a
    assume "(v, a) \<in> set (effect_of op)"
    moreover have "\<forall>(v, a) \<in> set (effect_of op). \<forall>(v', a') \<in> set (effect_of op). v \<noteq> v' \<or> a = a'"
      using is_valid_operator_sas_plus_then is_valid_operator_op
      unfolding is_valid_operator_sas_plus_def
      by fast
    ultimately have "map_of (effect_of op) v = Some a" 
      using map_of_constant_assignments_defined_if[of "effect_of op"]
      by presburger
  } note nb\<^sub>1\<^sub>0 = this
  {
    fix v a
    assume v_a_in_effect_of_op: "(v, a) \<in> set (effect_of op)"
      and "(s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) v \<noteq> None"
    moreover have "v \<in> set ?vs"
        using is_valid_operator_op is_valid_operator_sas_plus_then(3) calculation(1)
        by fastforce 
    moreover {
      have "is_valid_problem_strips ?\<Pi>"
        using is_valid_problem_sas_plus_then_strips_transformation_too 
          assms(1) 
        by blast
      thm calculation(1) nb\<^sub>6 assms(2)
      moreover have "set (add_effects_of op') \<subseteq> set ((?\<Pi>)\<^sub>\<V>)" 
        using assms(2) is_valid_problem_strips_operator_variable_sets(2)
          calculation 
        by blast
      moreover have "(v, a) \<in> set ((?\<Pi>)\<^sub>\<V>)"
        using v_a_in_effect_of_op nb\<^sub>6 calculation(2) 
        by blast
      ultimately have "a \<in> \<R>\<^sub>+ \<Psi> v"
        using sas_plus_problem_to_strips_problem_variable_set_element_iff[OF 
            assms(1)]
        by fast
    }
    \<comment> \<open> TODO slow. \<close>
    ultimately have "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))))"  
      using state_to_strips_state_dom_is[OF assms(1), of 
          "s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))"]
      by simp
  } note nb\<^sub>1\<^sub>1 = this
  {
    fix v a
    assume "(v, a) \<in> set (effect_of op)"
    moreover have "v \<in> dom (map_of (effect_of op))" 
      unfolding dom_map_of_conv_image_fst 
      using calculation
      by force 
    moreover have "(s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) v = Some a" 
      unfolding map_add_dom_app_simps(1)[OF calculation(2)] nb\<^sub>1
      using nb\<^sub>1\<^sub>0 calculation(1)
      by blast
    moreover have "(s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) v \<noteq> None" 
      using calculation(3)
      by auto
    moreover have "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))))"
      using nb\<^sub>1\<^sub>1 calculation(1, 4)
      by presburger
    ultimately have "(\<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op')))) (v, a) = Some True" 
      using state_to_strips_state_range_is[OF assms(1)]
      by simp
  } note nb\<^sub>1\<^sub>2 = this
  {
    fix v a'
    assume "(v, a') \<in> dom (map_of (effect_to_assignments op'))"   
      and "(v, a') \<in>  (\<Union>(v, a) \<in> set (effect_of op).
        { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })"
    moreover have "v \<in> dom (map_of (effect_of op))" 
      unfolding dom_map_of_conv_image_fst 
      using calculation(2)
      by force
    moreover have "v \<in> set ?vs"
      using calculation(3) is_valid_operator_sas_plus_then(3) is_valid_operator_op
      unfolding dom_map_of_conv_image_fst is_valid_operator_sas_plus_def
      by fastforce
    moreover obtain a where "(v, a) \<in> set (effect_of op)" 
      and "a' \<in> \<R>\<^sub>+ \<Psi> v" 
      and "a' \<noteq> a" 
      using calculation(2)
      by blast
    moreover have "(s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) v = Some a" 
      unfolding map_add_dom_app_simps(1)[OF calculation(3)] nb\<^sub>1
      using nb\<^sub>1\<^sub>0 calculation(5)
      by blast
    moreover have "(s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) v \<noteq> None" 
      using calculation(8) 
      by auto
    \<comment> \<open> TODO slow. \<close>
    moreover have "(v, a') \<in> dom (\<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))))"
      using state_to_strips_state_dom_is[OF assms(1), of 
        "s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))"] calculation(4, 6, 9)
      by simp
    \<comment> \<open> TODO slow. \<close>
    ultimately have "(\<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op')))) (v, a') = Some False" 
      using state_to_strips_state_range_is[OF assms(1), 
          of v a' "s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))"]
      by simp
  } note nb\<^sub>1\<^sub>3 = this
  {
    fix v a
    assume "(v, a) \<in> dom ?t" 
      and "(v, a) \<notin> dom (map_of (effect_to_assignments op'))"
    moreover have "(v, a) \<in> dom ?s'" 
      using calculation(1, 2)
      unfolding dom_map_add
      by blast
    moreover have "?t (v, a) = ?s' (v, a)" 
      unfolding map_add_dom_app_simps(3)[OF calculation(2)]..
    ultimately have "?t (v, a) = Some (the (s v) = a)"
      using state_to_strips_state_range_is[OF assms(1)] 
      by presburger
  } note nb\<^sub>1\<^sub>4 = this
  {
    fix v a
    assume "(v, a) \<in> dom ?t" 
      and v_a_not_in: "(v, a) \<notin> dom (map_of (effect_to_assignments op'))"
    moreover have "(v, a) \<in> dom ?s'" 
      using calculation(1, 2)
      unfolding dom_map_add
      by blast
    moreover have "(v, a) \<in> (\<Union> v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }.
      { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })"
      using state_to_strips_state_dom_is[OF assms(1)] calculation(3)
      by presburger
    moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" and "s v \<noteq> None" and "a \<in> \<R>\<^sub>+ \<Psi> v" 
      using calculation(4)
      by blast+
    \<comment> \<open> NOTE Hasn't this been proved before? \<close>
    moreover {
      have "dom (map_of (effect_to_assignments op')) = (\<Union>(v, a) \<in> set (effect_of op). { (v, a) }) 
        \<union> (\<Union>(v, a) \<in> set (effect_of op). 
          { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })"
        unfolding nb\<^sub>2
        by blast
      also have "\<dots> = (\<Union>(v, a) \<in> set (effect_of op). { (v, a) } 
          \<union> { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })" 
        by blast
      finally have "dom (map_of (effect_to_assignments op')) 
        = (\<Union>(v, a) \<in> set (effect_of op). { (v, a) } 
          \<union> { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })"
        by auto
      then have "(v, a) \<notin> (\<Union>(v, a) \<in> set (effect_of op). 
        { (v, a) | a. a \<in> \<R>\<^sub>+ \<Psi> v })" 
        using v_a_not_in
        by blast
    }
    \<comment> \<open> TODO slow. \<close>
    moreover have "v \<notin> dom (map_of (effect_of op))" 
      using dom_map_of_conv_image_fst calculation 
      by fastforce
    moreover have "(s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) v = s v" 
      unfolding nb\<^sub>1 map_add_dom_app_simps(3)[OF calculation(9)]
      by simp
    \<comment> \<open> TODO slow. \<close>
    moreover have "(v, a) \<in> dom ?t'" 
      using state_to_strips_state_dom_is[OF assms(1), of 
        "s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))"] calculation(5, 6, 7, 8, 10)
      by simp
    ultimately have "?t' (v, a) = Some (the (s v) = a)" 
      using state_to_strips_state_range_is[OF assms(1)]
      by presburger
  } note nb\<^sub>1\<^sub>5 = this
  \<comment> \<open> TODO refactor. \<close>
  have nb\<^sub>1\<^sub>6: "dom ?t = (\<Union> v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None }. 
      { (v, a) | a. a \<in> (\<R>\<^sub>+ \<Psi> v) }) 
    \<union> set (effect_of op) 
    \<union> (\<Union>(v, a)\<in>set (effect_of op).
      {(v, a') |a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a})"
    unfolding dom_map_add nb\<^sub>2
    using state_to_strips_state_dom_is[OF assms(1), of s]
    by auto
  {
    {
      fix v a
      assume "(v, a) \<in> dom ?t"
      then consider (A) "(v, a) \<in> dom (\<phi>\<^sub>S \<Psi> s)" 
        | (B) "(v, a) \<in> dom (map_of (effect_to_assignments op'))" 
        by fast
      hence "(v, a) \<in> dom ?t'" 
        proof (cases)
          case A
          then have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" and "s v \<noteq> None" and "a \<in> \<R>\<^sub>+ \<Psi> v"
            unfolding state_to_strips_state_dom_element_iff[OF assms(1)]
            by blast+
          thm map_add_None state_to_strips_state_dom_element_iff[OF assms(1)]
          moreover have "(s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))) v \<noteq> None" 
            using calculation(2)
            by simp
          ultimately show ?thesis 
            unfolding state_to_strips_state_dom_element_iff[OF assms(1)]
            by blast
        next
          case B
          then have "(v, a) \<in> 
              set (effect_of op) 
              \<union> (\<Union>(v, a)\<in>set (effect_of op). { (v, a') | a'. a' \<in> \<R>\<^sub>+ \<Psi> v \<and> a' \<noteq> a })" 
            unfolding nb\<^sub>2
            by blast
          then consider (B\<^sub>1) "(v, a) \<in> set (effect_of op)" 
            | (B\<^sub>2) "(v, a) \<in> (\<Union>(v, a)\<in>set (effect_of op). 
            { (v, a') | a'. a' \<in> \<R>\<^sub>+ \<Psi> v \<and> a' \<noteq> a })"
            by blast
          thm nb\<^sub>1\<^sub>2 nb\<^sub>1\<^sub>3 nb\<^sub>2
          thus ?thesis
            proof (cases)
              case B\<^sub>1
              then show ?thesis
                using nb\<^sub>1\<^sub>2
                by fast
            next
              case B\<^sub>2
              then show ?thesis
                using nb\<^sub>1\<^sub>3 B
                by blast
            qed 
        qed 
    } 
    moreover {
      let ?u = "s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))"
      fix v a
      assume v_a_in_dom_t': "(v, a) \<in> dom ?t'"
      thm nb\<^sub>5
      then have v_in_vs: "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
        and u_of_v_is_not_None: "?u v \<noteq> None" 
        and a_in_range_of_v: "a \<in> \<R>\<^sub>+ \<Psi> v" 
        using state_to_strips_state_dom_element_iff[OF assms(1)]
          v_a_in_dom_t'
        by meson+
      {
        assume "(v, a) \<notin> dom ?t" 
        then have contradiction: "(v, a) \<notin> 
          (\<Union>v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None}. { (v, a) |a. a \<in> \<R>\<^sub>+ \<Psi> v }) 
          \<union> set (effect_of op) 
          \<union> (\<Union>(v, a)\<in>set (effect_of op). {(v, a') |a'. a' \<in> \<R>\<^sub>+ \<Psi> v \<and> a' \<noteq> a})" 
          unfolding nb\<^sub>1\<^sub>6
          by fast
        hence False 
          proof (cases "map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op')) v = None")
            case True
            then have "s v \<noteq> None" 
              using u_of_v_is_not_None
              by simp
            then have "(v, a) \<in> (\<Union>v \<in> { v | v. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> s v \<noteq> None}. 
              { (v, a) |a. a \<in> \<R>\<^sub>+ \<Psi> v })" 
              using v_in_vs a_in_range_of_v 
              by blast
            thus ?thesis 
              using contradiction
              by blast
          next
            case False
            then have "v \<in> dom (map_of (effect_of op))" 
              using u_of_v_is_not_None nb\<^sub>1 
              by blast
            then obtain a' where map_of_effect_of_op_v_is: "map_of (effect_of op) v = Some a'" 
              by blast
            then have v_a'_in: "(v, a') \<in> set (effect_of op)" 
              using map_of_SomeD 
              by fast
            then show ?thesis
              proof (cases "a = a'")
                case True
                then have "(v, a) \<in> set (effect_of op)" 
                  using v_a'_in
                  by blast
                then show ?thesis 
                  using contradiction
                  by blast
              next
                case False
                then have "(v, a) \<in> (\<Union>(v, a)\<in>set (effect_of op). 
                  {(v, a') |a'. a' \<in> \<R>\<^sub>+ \<Psi> v \<and> a' \<noteq> a})" 
                  using v_a'_in calculation a_in_range_of_v
                  by blast
                thus ?thesis
                  using contradiction
                  by fast
              qed
          qed
      }
      hence "(v, a) \<in> dom ?t"
        by argo
    }
    moreover have "dom ?t \<subseteq> dom ?t'" and "dom ?t' \<subseteq> dom ?t" 
      subgoal 
        using calculation(1) subrelI[of "dom ?t" "dom ?t'"]
        by fast
      subgoal
        using calculation(2) subrelI[of "dom ?t'" "dom ?t"]
        by argo
      done
    ultimately have "dom ?t = dom ?t'"
      by force
  } note nb\<^sub>1\<^sub>7 = this
  {
    fix v a
    assume v_a_in_dom_t: "(v, a) \<in> dom ?t" 
    hence "?t (v, a) = ?t' (v, a)"
      proof (cases "(v, a) \<in> dom (map_of (effect_to_assignments op'))")
        case True
        \<comment> \<open> TODO slow. \<close>
        \<comment> \<open> NOTE Split on the (disjunct) domain variable sets of 
          @{text "map_of (effect_to_assignments op')"}. \<close> 
        then consider (A1) "(v, a) \<in> set (effect_of op)" 
          | (A2) "(v, a) \<in> (\<Union>(v, a) \<in> set (effect_of op).
            { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and> a' \<noteq> a })"
          using nb\<^sub>2
          by fastforce
        then show ?thesis 
          proof (cases)
            case A1
            then have "?t (v, a) = Some True" 
              unfolding map_add_dom_app_simps(1)[OF True]
              using nb\<^sub>9(1)
              by fast
            moreover have "?t' (v, a) = Some True"
              using nb\<^sub>1\<^sub>2[OF A1].
            ultimately show ?thesis..
          next
            case A2
            then have "?t (v, a) = Some False" 
              unfolding map_add_dom_app_simps(1)[OF True]
              using nb\<^sub>9(2)
              by blast
            moreover have "?t' (v, a) = Some False"
              using nb\<^sub>1\<^sub>3[OF True A2].
            ultimately show ?thesis..
          qed
      next
        case False
        moreover have "?t (v, a) = Some (the (s v) = a)" 
          using nb\<^sub>1\<^sub>4[OF v_a_in_dom_t False].
        moreover have "?t' (v, a) = Some (the (s v) = a)" 
          using nb\<^sub>1\<^sub>5[OF v_a_in_dom_t False].
        ultimately show ?thesis 
          by argo
      qed
  } note nb\<^sub>1\<^sub>8 = this
  moreover {
    fix v a
    assume "(v, a) \<in> dom ?t'" 
    hence "?t (v, a) = ?t' (v, a)" 
      using nb\<^sub>1\<^sub>7 nb\<^sub>1\<^sub>8
      by presburger
  }
  \<comment> \<open> TODO slow.\<close>
  ultimately have "?t \<subseteq>\<^sub>m ?t'" and "?t' \<subseteq>\<^sub>m ?t" 
    unfolding map_le_def 
    by fastforce+
  thus ?thesis
    using map_le_antisym[of ?t ?t'] 
    by fast
qed

\<comment> \<open> NOTE This is the essential step in the SAS+/STRIPS equivalence theorem. We show that executing
a given parallel STRIPS operator @{text "ops'"} on the corresponding STRIPS state 
@{text "s' = \<phi>\<^sub>S \<Psi> s"} yields the same state as executing the transformed SAS+ parallel operator
@{text "ops = [\<phi>\<^sub>O\<inverse> (\<phi> \<Psi>) op'. op' \<leftarrow> ops']"} on the original SAS+ state @{text "s"} and the 
transforming the resultant SAS+ state to its corresponding STRIPS state. \<close>
(* TODO refactor. *)
lemma sas_plus_equivalent_to_strips_i_a_XII:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "\<forall>op' \<in> set ops'. op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)" 
  shows "execute_parallel_operator (\<phi>\<^sub>S \<Psi> s) ops' 
    = \<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus s [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops'])" 
using assms
proof (induction ops' arbitrary: s)
  case Nil
  then show ?case 
    unfolding execute_parallel_operator_def execute_parallel_operator_sas_plus_def 
    by simp
next
  case (Cons op' ops')
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?t' = "(\<phi>\<^sub>S \<Psi> s) ++ map_of (effect_to_assignments op')"
    and ?t = "s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> op'))"
  have nb\<^sub>1: "?t' = \<phi>\<^sub>S \<Psi> ?t" 
    using sas_plus_equivalent_to_strips_i_a_XI[OF assms(1)] Cons.prems(2)
    by force
  {
    have "\<forall>op' \<in> set ops'. op' \<in> set (strips_problem.operators_of ?\<Pi>)" 
      using Cons.prems(2) 
      by simp
    then have "execute_parallel_operator (\<phi>\<^sub>S \<Psi> ?t) ops' 
      = \<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus ?t [\<phi>\<^sub>O\<inverse> \<Psi> x. x \<leftarrow> ops'])"
      using Cons.IH[OF Cons.prems(1), of ?t]
      by fastforce
    hence "execute_parallel_operator ?t' ops'
      = \<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus ?t [\<phi>\<^sub>O\<inverse> \<Psi> x. x \<leftarrow> ops'])" 
      using nb\<^sub>1
      by argo
  }
  thus ?case 
    by simp
qed

lemma sas_plus_equivalent_to_strips_i_a_XIII: 
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "\<forall>op' \<in> set ops'. op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "(\<phi>\<^sub>S \<Psi> G) \<subseteq>\<^sub>m execute_parallel_plan 
      (execute_parallel_operator (\<phi>\<^sub>S \<Psi> I) ops') \<pi>"
  shows "(\<phi>\<^sub>S \<Psi> G) \<subseteq>\<^sub>m execute_parallel_plan 
    (\<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus I [\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops'])) \<pi>"
proof -
  let ?I' = "(\<phi>\<^sub>S \<Psi> I)"
    and ?G' = "\<phi>\<^sub>S \<Psi> G" 
    and ?ops = "[\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
    and ?\<Pi> = "\<phi> \<Psi>"
  let ?J = "execute_parallel_operator_sas_plus I ?ops"
  {
    fix v a
    assume "(v, a) \<in> dom ?G'"
    then have "?G' (v, a) = execute_parallel_plan 
      (execute_parallel_operator ?I' ops') \<pi> (v, a)"
      using assms(3) 
      unfolding map_le_def
      by auto
    hence "?G' (v, a) = execute_parallel_plan (\<phi>\<^sub>S \<Psi> ?J) \<pi> (v, a)" 
      using sas_plus_equivalent_to_strips_i_a_XII[OF assms(1, 2)]
      by simp
  }
  thus ?thesis 
    unfolding map_le_def
    by fast
qed

\<comment> \<open> NOTE This is a more abstract formulation of the proposition in 
\<open>sas_plus_equivalent_to_strips_i\<close> which is better suited for induction proofs. We essentially claim 
that given a plan the execution in STRIPS semantics of which solves the problem of reaching a 
transformed goal state \<open>\<phi>\<^sub>S \<Psi> G\<close> from a transformed initial state \<open>\<phi>\<^sub>S \<Psi> I\<close>—such as 
the goal and initial state of an induced STRIPS problem for a SAS+ problem—is equivalent to an
execution in SAS+ semantics of the transformed plan \<open>\<phi>\<^sub>P\<inverse> (\<phi> \<Psi>) \<pi>\<close> w.r.t to the original 
initial state \<open>I\<close> and original goal state \<open>G\<close>. \<close> 
lemma sas_plus_equivalent_to_strips_i_a:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "dom I \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom I. the (I v) \<in> \<R>\<^sub>+ \<Psi> v" 
    and "dom G \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    and "\<forall>v \<in> dom G. the (G v) \<in> \<R>\<^sub>+ \<Psi> v" 
    and "\<forall>ops' \<in> set \<pi>. \<forall>op' \<in> set ops'. op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "(\<phi>\<^sub>S \<Psi> G) \<subseteq>\<^sub>m execute_parallel_plan (\<phi>\<^sub>S \<Psi> I) \<pi>"
  shows "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>)"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?\<psi> = "\<phi>\<^sub>P\<inverse> \<Psi> \<pi>"
  show ?thesis 
    using assms
    proof (induction \<pi> arbitrary: I)
      case Nil
      then have "(\<phi>\<^sub>S \<Psi> G) \<subseteq>\<^sub>m (\<phi>\<^sub>S \<Psi> I)" 
        by fastforce
      then have "G \<subseteq>\<^sub>m I" 
        using state_to_strips_state_map_le_iff[OF assms(1, 4, 5)]
        by blast
      thus ?case 
        unfolding SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
          strips_parallel_plan_to_sas_plus_parallel_plan_def 
        by fastforce
    next
      case (Cons ops' \<pi>)
      let ?D = "range_of \<Psi>"
        and ?\<Pi> = "\<phi> \<Psi>" 
        and ?I' = "\<phi>\<^sub>S \<Psi> I"
        and ?G' = "\<phi>\<^sub>S \<Psi> G"
      let ?ops = "[\<phi>\<^sub>O\<inverse> \<Psi> op'. op' \<leftarrow> ops']" 
      let ?J = "execute_parallel_operator_sas_plus I ?ops"
        and ?J' = "execute_parallel_operator ?I' ops'" 
      have nb\<^sub>1: "set ops' \<subseteq> set ((?\<Pi>)\<^sub>\<O>)" 
        using Cons.prems(6)
        unfolding STRIPS_Semantics.is_parallel_solution_for_problem_def list_all_iff ListMem_iff
        by fastforce
      {
        fix op 
        assume "op \<in> set ?ops" 
        moreover obtain op' where "op' \<in> set ops'" and "op = \<phi>\<^sub>O\<inverse> \<Psi> op'" 
          using calculation 
          by auto
        moreover have "op' \<in> set ((?\<Pi>)\<^sub>\<O>)"
          using nb\<^sub>1 calculation(2)
          by blast
        moreover obtain op'' where "op'' \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = \<phi>\<^sub>O \<Psi> op''" 
          using calculation(4) 
          by auto
        moreover have "op = op''" 
          using sas_plus_operator_inverse_is[OF assms(1) calculation(5)] calculation(3, 6) 
          by presburger
        ultimately have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+) \<and> (\<exists>op' \<in> set ops'. op' = \<phi>\<^sub>O \<Psi> op)" 
          by blast
      } note nb\<^sub>2 = this
      {
        fix op v a
        assume "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "(v, a) \<in> set (effect_of op)" 
        moreover have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
          using nb\<^sub>2 calculation(1)
          by blast
        moreover have "is_valid_operator_sas_plus \<Psi> op"
          using is_valid_problem_sas_plus_then(2) Cons.prems(1) calculation(3) 
          by blast
        ultimately have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
          using is_valid_operator_sas_plus_then(3) 
          by fastforce
      } note nb\<^sub>3 = this
      {
        fix op
        assume "op \<in> set ?ops" 
        then have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
          using nb\<^sub>2 
          by blast
        then have "is_valid_operator_sas_plus \<Psi> op"
          using is_valid_problem_sas_plus_then(2) Cons.prems(1)
          by blast
        hence "\<forall>(v, a) \<in> set (effect_of op). v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) 
          \<and> a \<in> \<R>\<^sub>+ \<Psi> v"
          using is_valid_operator_sas_plus_then(3,4) 
          by fast
      } note nb\<^sub>4 = this
      show ?case 
        proof (cases "STRIPS_Semantics.are_all_operators_applicable ?I' ops' 
          \<and> STRIPS_Semantics.are_all_operator_effects_consistent ops'")
          case True
          {
            {
              have "dom I \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
                using Cons.prems(2)
                by blast
              hence "(\<phi>\<^sub>S\<inverse> \<Psi> ?I') = I"
                using strips_state_to_state_inverse_is[OF 
                    Cons.prems(1) _ Cons.prems(3)]
                by argo
            }
            then have "are_all_operators_applicable_in I ?ops
              \<and> are_all_operator_effects_consistent ?ops" 
              using sas_plus_equivalent_to_strips_i_a_IV[OF assms(1) nb\<^sub>1, of I] True
              by simp
            moreover have "(\<phi>\<^sub>P\<inverse> \<Psi> (ops' # \<pi>)) = ?ops # (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>)" 
              unfolding SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
                strips_parallel_plan_to_sas_plus_parallel_plan_def
                SAS_Plus_STRIPS.strips_op_to_sasp_def
                  strips_op_to_sasp_def  
              by simp
            ultimately have "execute_parallel_plan_sas_plus I (\<phi>\<^sub>P\<inverse> \<Psi> (ops' # \<pi>)) 
              = execute_parallel_plan_sas_plus ?J (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>)" 
              by force
          } note nb\<^sub>5 = this
          \<comment> \<open> Show the goal using the IH. \<close>
          {
            have dom_J_subset_eq_vs: "dom ?J \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
              using sas_plus_equivalent_to_strips_i_a_IX[OF Cons.prems(2)] nb\<^sub>2 nb\<^sub>4
              by blast
            moreover {
              have "set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<subseteq> dom (range_of \<Psi>)"
                using is_valid_problem_sas_plus_then(1)[OF assms(1)]
                by fastforce
              moreover have "\<forall>v \<in> dom I. the (I v) \<in> set (the (range_of \<Psi> v))"
                using Cons.prems(2, 3) assms(1) set_the_range_of_is_range_of_sas_plus_if 
                by force
              moreover have "\<forall>op \<in> set ?ops. \<forall>(v, a) \<in> set (effect_of op).
                v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+) \<and> a \<in> set (the (?D v))" 
                using set_the_range_of_is_range_of_sas_plus_if assms(1) nb\<^sub>4 
                by fastforce
              moreover have v_in_dom_J_range: "\<forall>v \<in> dom ?J. the (?J v) \<in> set (the (?D v))" 
                using sas_plus_equivalent_to_strips_i_a_X[of 
                    I "set ((\<Psi>)\<^sub>\<V>\<^sub>+)" ?D ?ops, OF Cons.prems(2)] calculation(1, 2, 3)
                by fastforce
              {
                fix v 
                assume "v \<in> dom ?J"
                moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
                  using nb\<^sub>2 calculation dom_J_subset_eq_vs 
                  by blast
                moreover have "set (the (range_of \<Psi> v)) = \<R>\<^sub>+ \<Psi> v" 
                  using set_the_range_of_is_range_of_sas_plus_if[OF assms(1)] 
                    calculation(2)
                  by presburger
                ultimately have "the (?J v) \<in> \<R>\<^sub>+ \<Psi> v" 
                  using nb\<^sub>3 v_in_dom_J_range
                  by blast
              }
              ultimately have "\<forall>v \<in> dom ?J. the (?J v) \<in> \<R>\<^sub>+ \<Psi> v"
                by fast
            }
            moreover have "\<forall>ops' \<in> set \<pi>. \<forall>op'\<in>set ops'. op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
              using Cons.prems(6)
              by simp
            moreover {
              have "?G' \<subseteq>\<^sub>m execute_parallel_plan ?J' \<pi>" 
                using Cons.prems(7) True
                by auto
              hence "(\<phi>\<^sub>S \<Psi> G) \<subseteq>\<^sub>m execute_parallel_plan (\<phi>\<^sub>S \<Psi> ?J) \<pi>"
                using sas_plus_equivalent_to_strips_i_a_XIII[OF Cons.prems(1)] nb\<^sub>1
                by blast
            }
            ultimately have "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I (\<phi>\<^sub>P\<inverse> \<Psi> (ops' # \<pi>))"
              using Cons.IH[of ?J, OF Cons.prems(1) _ _ Cons.prems(4, 5)] Cons.prems(6) nb\<^sub>5 
              by presburger
          }
          thus ?thesis.
        next
          case False
          then have "?G' \<subseteq>\<^sub>m ?I'" 
            using Cons.prems(7)
            by force
          moreover {
            have "dom I \<subseteq> set ?vs" 
              using Cons.prems(2)
              by simp
            hence "\<not>(are_all_operators_applicable_in I ?ops
              \<and> are_all_operator_effects_consistent ?ops)" 
              using sas_plus_equivalent_to_strips_i_a_VIII[OF Cons.prems(1) _ Cons.prems(3) nb\<^sub>1] 
                False
              by force
          }
          moreover {
            have "(\<phi>\<^sub>P\<inverse> \<Psi> (ops' # \<pi>)) = ?ops # (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>)" 
              unfolding SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
                strips_parallel_plan_to_sas_plus_parallel_plan_def
                SAS_Plus_STRIPS.strips_op_to_sasp_def
                strips_op_to_sasp_def
              by simp
            hence "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I (?ops # (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>))
              \<longleftrightarrow> G \<subseteq>\<^sub>m I" 
              using calculation(2)
              by force
          }
          ultimately show ?thesis 
            using state_to_strips_state_map_le_iff[OF Cons.prems(1, 4, 5)] 
            unfolding SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
              strips_parallel_plan_to_sas_plus_parallel_plan_def
              SAS_Plus_STRIPS.strips_op_to_sasp_def
              strips_op_to_sasp_def
            by force
        qed
    qed
qed

\<comment> \<open> NOTE Show that a solution for the induced STRIPS problem for the given valid SAS+ problem, 
  corresponds to a solution for the given SAS+ problem.

Note that in the context of the SAS+ problem solving pipeline, we
\begin{enumerate}
  \item convert the given valid SAS+ @{text "\<Psi>"} problem to the corresponding STRIPS problem 
@{text "\<Pi>"} (this is implicitely also valid by lemma 
@{text "is_valid_problem_sas_plus_then_strips_transformation_too"}); then,
  \item get a solution @{text "\<pi>"}—if it exists—for the induced STRIPS problem by executing 
SATPlan; and finally,
  \item convert @{text "\<pi>"} back to a solution @{text "\<psi>"} for the SAS+ problem.
\end{enumerate} \<close>
lemma sas_plus_equivalent_to_strips_i:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "STRIPS_Semantics.is_parallel_solution_for_problem 
    (\<phi> \<Psi>) \<pi>"
  shows "goal_of \<Psi> \<subseteq>\<^sub>m execute_parallel_plan_sas_plus 
    (sas_plus_problem.initial_of \<Psi>) (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>)"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?I = "initial_of \<Psi>" 
    and ?G = "goal_of \<Psi>"
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?G' = "strips_problem.goal_of ?\<Pi>"
    and ?I' = "strips_problem.initial_of ?\<Pi>"
  let ?\<psi> = "\<phi>\<^sub>P\<inverse> \<Psi> \<pi>"
  have "dom ?I \<subseteq> set ?vs" 
    using is_valid_problem_sas_plus_then(3) assms(1)
    by auto
  moreover have "\<forall>v \<in> dom ?I. the (?I v) \<in> \<R>\<^sub>+ \<Psi> v" 
    using is_valid_problem_sas_plus_then(4) assms(1) calculation
    by auto
  moreover have "dom ?G \<subseteq> set ?vs"  and "\<forall>v \<in> dom ?G. the (?G v) \<in> \<R>\<^sub>+ \<Psi> v" 
    using is_valid_problem_sas_plus_then(5, 6) assms(1)
    by blast+
  moreover have "\<forall>ops'\<in>set \<pi>. \<forall>op'\<in>set ops'. op' \<in> set ((?\<Pi>)\<^sub>\<O>)"
    using is_parallel_solution_for_problem_operator_set[OF assms(2)]
    by simp
  moreover {
    have "?G' \<subseteq>\<^sub>m execute_parallel_plan ?I' \<pi>"
      using assms(2) 
      unfolding STRIPS_Semantics.is_parallel_solution_for_problem_def..
    moreover have "?G' = \<phi>\<^sub>S \<Psi> ?G" and "?I' = \<phi>\<^sub>S \<Psi> ?I" 
      by simp+
    ultimately have "(\<phi>\<^sub>S \<Psi> ?G) \<subseteq>\<^sub>m execute_parallel_plan (\<phi>\<^sub>S \<Psi> ?I) \<pi>"
      by simp
  }
  ultimately show ?thesis 
    using sas_plus_equivalent_to_strips_i_a[OF assms(1)]
    by simp
qed

\<comment> \<open> NOTE Show that the operators for a given solution @{text "\<pi>"} to the induced STRIPS problem 
for a given SAS+ problem correspond to operators of the SAS+ problem. \<close>
lemma sas_plus_equivalent_to_strips_ii:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "STRIPS_Semantics.is_parallel_solution_for_problem (\<phi> \<Psi>) \<pi>"
  shows "list_all (list_all (\<lambda>op. ListMem op (operators_of \<Psi>))) (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>)" 
proof -
  let ?\<Pi> = "\<phi> \<Psi>" 
  let ?ops = "operators_of \<Psi>" 
    and ?\<psi> = "\<phi>\<^sub>P\<inverse> \<Psi> \<pi>"
  have "is_valid_problem_strips ?\<Pi>" 
    using is_valid_problem_sas_plus_then_strips_transformation_too[OF assms(1)]
    by simp 
  have nb\<^sub>1: "\<forall>op' \<in> set ((?\<Pi>)\<^sub>\<O>). (\<exists>op \<in> set ?ops. op' = (\<phi>\<^sub>O \<Psi> op))"  
    by auto
  {
    fix ops' op' op
    assume "ops' \<in> set \<pi>" and "op' \<in> set ops'" 
    then have "op' \<in> set (strips_problem.operators_of ?\<Pi>)"
      using is_parallel_solution_for_problem_operator_set[OF assms(2)]
      by simp
    then obtain op where "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" and "op' = (\<phi>\<^sub>O \<Psi> op)" 
      by auto
    then have "(\<phi>\<^sub>O\<inverse> \<Psi> op') \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
      using sas_plus_operator_inverse_is[OF assms(1)]
      by presburger
  }
  thus ?thesis 
    unfolding list_all_iff ListMem_iff 
      strips_parallel_plan_to_sas_plus_parallel_plan_def
      SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
      SAS_Plus_STRIPS.strips_op_to_sasp_def
      strips_op_to_sasp_def
    by auto
qed

text \<open> We now show that for a parallel solution \<^term>\<open>\<pi>\<close> of \<^term>\<open>\<Pi>\<close> the SAS+ plan 
\<^term>\<open>\<psi> \<equiv> \<phi>\<^sub>P\<inverse> \<Psi> \<pi>\<close> yielded by the STRIPS to SAS+ plan transformation is a solution for 
\<^term>\<open>\<Psi>\<close>. The proof uses the definition of parallel STRIPS solutions and shows that the 
execution of \<^term>\<open>\<psi>\<close> on the initial state of the SAS+ problem yields a state satisfying the 
problem's goal state, i.e.
  @{text[display, indent=4]"G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I \<psi>"}
and by showing that all operators in all parallel operators of \<^term>\<open>\<psi>\<close> are operators of the 
problem. \<close>

theorem
  sas_plus_equivalent_to_strips:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "STRIPS_Semantics.is_parallel_solution_for_problem (\<phi> \<Psi>) \<pi>" 
  shows "is_parallel_solution_for_problem \<Psi> (\<phi>\<^sub>P\<inverse> \<Psi> \<pi>)"
proof -
  let ?I = "initial_of \<Psi>"
    and ?G = "goal_of \<Psi>" 
    and ?ops = "operators_of \<Psi>"
    and ?\<psi> = "\<phi>\<^sub>P\<inverse> \<Psi> \<pi>"
  show ?thesis
    unfolding is_parallel_solution_for_problem_def Let_def
    proof (rule conjI)
      show "?G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ?I ?\<psi>"
        using sas_plus_equivalent_to_strips_i[OF assms].
    next 
      show "list_all (list_all (\<lambda>op. ListMem op ?ops)) ?\<psi>" 
        using sas_plus_equivalent_to_strips_ii[OF assms].
    qed
qed

private lemma strips_equivalent_to_sas_plus_i_a_I:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "\<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
    and "op' \<in> set [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]"
  obtains op where "op \<in> set ops" 
    and "op' = \<phi>\<^sub>O \<Psi> op"
proof -
  let ?\<Pi> = "\<phi> \<Psi>" 
  let ?ops = "operators_of \<Psi>"
  obtain op where "op \<in> set ops" and "op' = \<phi>\<^sub>O \<Psi> op" 
    using assms(3) 
    by auto
  thus ?thesis 
    using that
    by blast
qed

private corollary strips_equivalent_to_sas_plus_i_a_II:
  assumes"is_valid_problem_sas_plus \<Psi>"
    and "\<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
    and "op' \<in> set [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]"
  shows "op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "is_valid_operator_strips (\<phi> \<Psi>) op'"
proof -
  let ?\<Pi> = "\<phi> \<Psi>" 
  let ?ops = "operators_of \<Psi>"
    and ?ops' = "strips_problem.operators_of ?\<Pi>"
  obtain op where op_in: "op \<in> set ops" and op'_is: "op' = \<phi>\<^sub>O \<Psi> op" 
    using strips_equivalent_to_sas_plus_i_a_I[OF assms].
  then have nb: "op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    using assms(2) op_in op'_is 
    by fastforce
  thus "op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
    and "is_valid_operator_strips ?\<Pi> op'" 
    proof -
      have "\<forall>op' \<in> set ?ops'. is_valid_operator_strips ?\<Pi> op'"
        using is_valid_problem_sas_plus_then_strips_transformation_too_iii[OF assms(1)]
        unfolding list_all_iff. 
      thus "is_valid_operator_strips ?\<Pi> op'" 
        using nb
        by fastforce
    qed fastforce
qed

(* TODO make private *)
lemma strips_equivalent_to_sas_plus_i_a_III:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "\<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
  shows "execute_parallel_operator (\<phi>\<^sub>S \<Psi> s) [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]
    = (\<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus s ops))"
proof -
  {
    fix op s
    assume "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
    moreover have "(\<phi>\<^sub>O \<Psi> op) \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
      using calculation 
      by simp
    moreover have "(\<phi>\<^sub>S \<Psi> s) ++ map_of (effect_to_assignments (\<phi>\<^sub>O \<Psi> op))
      = (\<phi>\<^sub>S \<Psi> (s ++ map_of (effect_of (\<phi>\<^sub>O\<inverse> \<Psi> (\<phi>\<^sub>O \<Psi> op)))))"
      using sas_plus_equivalent_to_strips_i_a_XI[OF assms(1) calculation(2)]
      by blast
    moreover have "(\<phi>\<^sub>O\<inverse> \<Psi> (\<phi>\<^sub>O \<Psi> op)) = op"
      using sas_plus_operator_inverse_is[OF assms(1) calculation(1)].
    ultimately have "(\<phi>\<^sub>S \<Psi> s) \<then> (\<phi>\<^sub>O \<Psi> op)
      = (\<phi>\<^sub>S \<Psi> (s \<then>\<^sub>+ op))" 
      unfolding execute_operator_def execute_operator_sas_plus_def 
      by simp
  } note nb\<^sub>1 = this
  show ?thesis 
    using assms
    proof (induction ops arbitrary: s)
      case Nil
      then show ?case 
        unfolding execute_parallel_operator_def execute_parallel_operator_sas_plus_def 
        by simp
    next
      case (Cons op ops)
      let ?t = "s \<then>\<^sub>+ op"
      let ?s' = "\<phi>\<^sub>S \<Psi> s" 
        and ?ops' = "[\<phi>\<^sub>O \<Psi> op. op \<leftarrow> op # ops]"
      let ?t' = "?s' \<then> (\<phi>\<^sub>O \<Psi> op)"
      have "execute_parallel_operator ?s' ?ops' 
        = execute_parallel_operator ?t' [\<phi>\<^sub>O \<Psi> x. x \<leftarrow> ops]"
        unfolding execute_operator_def
        by simp
      moreover have "(\<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus s (op # ops)))
        = (\<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus ?t ops))" 
        unfolding execute_operator_sas_plus_def
        by simp
      moreover {
        have "?t' = (\<phi>\<^sub>S \<Psi> ?t)"
          using nb\<^sub>1 Cons.prems(2)
          by simp
        hence "execute_parallel_operator ?t'[\<phi>\<^sub>O \<Psi> x. x \<leftarrow> ops] 
          = (\<phi>\<^sub>S \<Psi> (execute_parallel_operator_sas_plus ?t ops))" 
          using Cons.IH[of ?t] Cons.prems
          by simp
      }
      ultimately show ?case 
        by argo
    qed
qed

private lemma strips_equivalent_to_sas_plus_i_a_IV:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "\<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
    and "are_all_operators_applicable_in I ops 
    \<and> are_all_operator_effects_consistent ops"
  shows "STRIPS_Semantics.are_all_operators_applicable (\<phi>\<^sub>S \<Psi> I) [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]
    \<and> STRIPS_Semantics.are_all_operator_effects_consistent [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]"
proof -
  let ?vs = "variables_of \<Psi>" 
    and ?ops = "operators_of \<Psi>" 
  let ?I' = "\<phi>\<^sub>S \<Psi> I" 
    and ?ops' = "[\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]"
  have nb\<^sub>1: "\<forall>op \<in> set ops. is_operator_applicable_in I op"
    using assms(3) 
    unfolding are_all_operators_applicable_in_def list_all_iff
    by blast
  have nb\<^sub>2: "\<forall>op \<in> set ops. is_valid_operator_sas_plus \<Psi> op"
    using is_valid_problem_sas_plus_then(2) assms(1, 2)
    unfolding is_valid_operator_sas_plus_def
    by auto
  have nb\<^sub>3: "\<forall>op \<in> set ops. map_of (precondition_of op) \<subseteq>\<^sub>m I" 
    using nb\<^sub>1 
    unfolding is_operator_applicable_in_def list_all_iff 
    by blast
  {
    fix op\<^sub>1 op\<^sub>2
    assume "op\<^sub>1 \<in> set ops" and "op\<^sub>2 \<in> set ops" 
    hence "are_operator_effects_consistent op\<^sub>1 op\<^sub>2" 
      using assms(3)
      unfolding are_all_operator_effects_consistent_def list_all_iff 
      by blast
  } note nb\<^sub>4 = this
  {
    fix op\<^sub>1 op\<^sub>2
    assume "op\<^sub>1 \<in> set ops" and "op\<^sub>2 \<in> set ops"
    hence "\<forall>(v, a) \<in> set (effect_of op\<^sub>1). \<forall>(v', a') \<in> set (effect_of op\<^sub>2).
      v \<noteq> v' \<or> a = a'"
      using nb\<^sub>4
      unfolding are_operator_effects_consistent_def Let_def list_all_iff
      by presburger
  } note nb\<^sub>5 = this
  {
    fix op\<^sub>1' op\<^sub>2' I
    assume "op\<^sub>1' \<in> set ?ops'" 
      and "op\<^sub>2' \<in> set ?ops'" 
      and "\<exists>(v, a) \<in> set (add_effects_of op\<^sub>1'). \<exists>(v', a') \<in> set (delete_effects_of op\<^sub>2').
        (v, a) = (v', a')" 
    moreover obtain op\<^sub>1 op\<^sub>2
      where "op\<^sub>1 \<in> set ops" 
          and "op\<^sub>1' = \<phi>\<^sub>O \<Psi> op\<^sub>1" 
        and "op\<^sub>2 \<in> set ops" 
          and "op\<^sub>2' = \<phi>\<^sub>O \<Psi> op\<^sub>2" 
      using strips_equivalent_to_sas_plus_i_a_I[OF assms(1, 2)] calculation(1, 2) 
      by auto
    moreover have "is_valid_operator_sas_plus \<Psi> op\<^sub>1"
       and is_valid_operator_op\<^sub>2: "is_valid_operator_sas_plus \<Psi> op\<^sub>2"
      using calculation(4, 6) nb\<^sub>2 
       by blast+
    moreover obtain v v' a a' 
      where "(v, a) \<in> set (add_effects_of op\<^sub>1')" 
        and "(v', a') \<in> set (delete_effects_of op\<^sub>2')"
        and "(v, a) = (v', a')" 
      using calculation
      by blast
    moreover have "(v, a) \<in> set (effect_of op\<^sub>1)" 
      using calculation(5, 10) 
      unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
        sasp_op_to_strips_def Let_def
      by fastforce
    moreover have "v = v'" and "a = a'"
      using calculation(12) 
      by simp+
    moreover {
      have "(v', a') \<in> (\<Union>(v, a) \<in> set (effect_of op\<^sub>2). 
        { (v, a') | a'. a' \<in> (\<R>\<^sub>+ \<Psi> v) \<and>  a' \<noteq> a })"
        using sasp_op_to_strips_set_delete_effects_is 
          calculation(7, 9, 11)
        by blast
      then obtain v'' a'' where "(v'', a'') \<in> set (effect_of op\<^sub>2)" 
        and "(v', a') \<in> { (v'', a''') | a'''. a''' \<in> (\<R>\<^sub>+ \<Psi> v'') \<and>  a''' \<noteq> a'' }"
        by blast
      moreover have "(v', a'') \<in> set (effect_of op\<^sub>2)" 
        using calculation 
        by blast
      moreover have "a' \<in> \<R>\<^sub>+ \<Psi> v''" and "a' \<noteq> a''"
        using calculation(1, 2) 
        by fast+
      ultimately have "\<exists>a''. (v', a'') \<in> set (effect_of op\<^sub>2) \<and> a' \<in> (\<R>\<^sub>+ \<Psi> v') 
        \<and> a' \<noteq> a''" 
        by blast
    }
    moreover obtain a'' where "a' \<in> \<R>\<^sub>+ \<Psi> v'" 
      and "(v', a'') \<in> set (effect_of op\<^sub>2)" 
      and "a' \<noteq> a''"
      using calculation(16)
      by blast
    moreover have "\<exists>(v, a) \<in> set (effect_of op\<^sub>1). (\<exists>(v', a') \<in> set (effect_of op\<^sub>2). 
      v = v' \<and> a \<noteq> a')"
      using calculation(13, 14, 15, 17, 18, 19)
      by blast
    \<comment> \<open> TODO slow. \<close>
    ultimately have "\<exists>op\<^sub>1 \<in> set ops. \<exists>op\<^sub>2 \<in> set ops. \<not>are_operator_effects_consistent op\<^sub>1 op\<^sub>2"
      unfolding are_operator_effects_consistent_def list_all_iff
      by fastforce
  } note nb\<^sub>6 = this
  show ?thesis
    proof (rule conjI)
      {
        fix op' 
        assume "op' \<in> set ?ops'" 
        moreover obtain op where op_in: "op \<in> set ops" 
          and op'_is: "op' = \<phi>\<^sub>O \<Psi> op"
          and op'_in: "op' \<in> set ((\<phi> \<Psi>)\<^sub>\<O>)"
          and is_valid_op': "is_valid_operator_strips (\<phi> \<Psi>) op'"
          using strips_equivalent_to_sas_plus_i_a_I[OF assms(1, 2)]
            strips_equivalent_to_sas_plus_i_a_II[OF assms(1, 2)] calculation 
          by metis
        moreover have is_valid_op: "is_valid_operator_sas_plus \<Psi> op"
          using nb\<^sub>2 calculation(2)..
        {
          fix v a
          assume v_a_in_preconditions': "(v, a) \<in> set (strips_operator.precondition_of op')"
          have v_a_in_preconditions: "(v, a) \<in> set (precondition_of op)" 
            using op'_is
            unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
              sasp_op_to_strips_def Let_def
            using v_a_in_preconditions' 
            by force
          moreover have "v \<in> set ?vs" and "a \<in> \<R>\<^sub>+ \<Psi> v"
            using is_valid_operator_sas_plus_then(1,2) is_valid_op calculation(1)
            by fastforce+
          moreover {
            have "\<forall>(v, a) \<in> set (precondition_of op). \<forall>(v', a') \<in> set (precondition_of op).
              v \<noteq> v' \<or> a = a'" 
              using is_valid_operator_sas_plus_then(5) is_valid_op
              by fast
            hence "map_of (precondition_of op) v = Some a" 
              using map_of_constant_assignments_defined_if[OF _ v_a_in_preconditions]
              by blast
          }
          moreover have "v \<in> dom (map_of (precondition_of op))" 
            using calculation(4)
            by blast
          moreover have "I v = Some a" 
            using nb\<^sub>3 
            unfolding map_le_def 
            using op_in calculation(4, 5)
            by metis
          moreover have "(v, a) \<in> dom ?I'" 
            using state_to_strips_state_dom_element_iff[OF assms(1)] 
              calculation(2, 3, 6)
            by simp
          ultimately have "?I' (v, a) = Some True" 
            using state_to_strips_state_range_is[OF assms(1)]
            by simp
        }
        hence "STRIPS_Representation.is_operator_applicable_in ?I' op'" 
          unfolding 
            STRIPS_Representation.is_operator_applicable_in_def 
            Let_def list_all_iff 
          by fast
      }
      thus "are_all_operators_applicable ?I' ?ops'"
        unfolding are_all_operators_applicable_def list_all_iff
        by blast
    next 
      {
        fix op\<^sub>1' op\<^sub>2'
        assume op\<^sub>1'_in_ops': "op\<^sub>1' \<in> set ?ops'" and op\<^sub>2'_in_ops': "op\<^sub>2' \<in> set ?ops'" 
        have "STRIPS_Semantics.are_operator_effects_consistent op\<^sub>1' op\<^sub>2'" 
          unfolding STRIPS_Semantics.are_operator_effects_consistent_def Let_def
          \<comment> \<open> TODO proof is symmetrical... refactor into nb. \<close>
          proof (rule conjI)          
            show "\<not>list_ex (\<lambda>x. list_ex ((=) x) (delete_effects_of op\<^sub>2')) 
              (add_effects_of op\<^sub>1')"
              proof (rule ccontr)
                assume "\<not>\<not>list_ex (\<lambda>v. list_ex ((=) v) (delete_effects_of op\<^sub>2')) 
                  (add_effects_of op\<^sub>1')" 
                then have "\<exists>(v, a) \<in> set (delete_effects_of op\<^sub>2'). 
                  \<exists>(v', a') \<in> set (add_effects_of op\<^sub>1'). (v, a) = (v', a')" 
                  unfolding list_ex_iff 
                  by fastforce
                then obtain op\<^sub>1 op\<^sub>2 where "op\<^sub>1 \<in> set ops"
                  and "op\<^sub>2 \<in> set ops" 
                  and "\<not>are_operator_effects_consistent op\<^sub>1 op\<^sub>2" 
                  using nb\<^sub>6[OF op\<^sub>1'_in_ops' op\<^sub>2'_in_ops']
                  by blast
                thus False 
                  using nb\<^sub>4
                  by blast              
              qed
          next
            show "\<not>list_ex (\<lambda>v. list_ex ((=) v) (add_effects_of op\<^sub>2')) (delete_effects_of op\<^sub>1')" 
              proof (rule ccontr)
                assume "\<not>\<not>list_ex (\<lambda>v. list_ex ((=) v) (add_effects_of op\<^sub>2')) 
                  (delete_effects_of op\<^sub>1')" 
                then have "\<exists>(v, a) \<in> set (delete_effects_of op\<^sub>1'). 
                  \<exists>(v', a') \<in> set (add_effects_of op\<^sub>2'). (v, a) = (v', a')" 
                  unfolding list_ex_iff
                  by fastforce
                then obtain op\<^sub>1 op\<^sub>2 where "op\<^sub>1 \<in> set ops"
                  and "op\<^sub>2 \<in> set ops" 
                  and "\<not>are_operator_effects_consistent op\<^sub>1 op\<^sub>2" 
                  using nb\<^sub>6[OF op\<^sub>2'_in_ops' op\<^sub>1'_in_ops']
                  by blast
                thus False 
                  using nb\<^sub>4
                  by blast
              qed
          qed
      }
      thus "STRIPS_Semantics.are_all_operator_effects_consistent ?ops'" 
        unfolding STRIPS_Semantics.are_all_operator_effects_consistent_def list_all_iff
        by blast
    qed
qed

private lemma strips_equivalent_to_sas_plus_i_a_V:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "\<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
    and "\<not>(are_all_operators_applicable_in s ops 
    \<and> are_all_operator_effects_consistent ops)"
  shows "\<not>(STRIPS_Semantics.are_all_operators_applicable (\<phi>\<^sub>S \<Psi> s) [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]
    \<and> STRIPS_Semantics.are_all_operator_effects_consistent [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops])"
proof -
  let ?vs = "variables_of \<Psi>"
    and ?ops = "operators_of \<Psi>" 
  let ?s' = "\<phi>\<^sub>S \<Psi> s"
    and ?ops' = "[\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]"
  {
    fix op
    assume "op \<in> set ops" 
    hence "\<exists>op' \<in> set ?ops'. op' = \<phi>\<^sub>O \<Psi> op" 
      by simp
  } note nb\<^sub>1 = this
  {
    fix op
    assume "op \<in> set ops" 
    then have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
      using assms(2) 
      by blast
    then have "is_valid_operator_sas_plus \<Psi> op"
      using is_valid_problem_sas_plus_then(2) assms(1)
      unfolding is_valid_operator_sas_plus_def
      by auto
    hence "\<forall>(v, a) \<in> set (precondition_of op). \<forall>(v', a') \<in> set (precondition_of op).
      v \<noteq> v' \<or> a = a'" 
      using is_valid_operator_sas_plus_then(5)
      unfolding is_valid_operator_sas_plus_def
      by fast
  } note nb\<^sub>2 = this
  {
    consider (A) "\<not>are_all_operators_applicable_in s ops" 
      | (B) "\<not>are_all_operator_effects_consistent ops" 
      using assms(3)
      by blast
    hence "\<not>STRIPS_Semantics.are_all_operators_applicable ?s' ?ops' 
      \<or> \<not>STRIPS_Semantics.are_all_operator_effects_consistent ?ops'"
      proof (cases)
        case A
        then obtain op where op_in: "op \<in> set ops" 
          and not_precondition_map_le_s: "\<not>(map_of (precondition_of op) \<subseteq>\<^sub>m s)"
          using A
          unfolding are_all_operators_applicable_in_def list_all_iff 
            is_operator_applicable_in_def
          by blast
        then obtain op' where op'_in: "op' \<in> set ?ops'" and op'_is: "op' = \<phi>\<^sub>O \<Psi> op" 
          using nb\<^sub>1
          by blast
        have "\<not>are_all_operators_applicable ?s' ?ops'" 
          proof (rule ccontr)
            assume "\<not>\<not>are_all_operators_applicable ?s' ?ops'"
            then have all_operators_applicable: "are_all_operators_applicable ?s' ?ops'"
              by simp
            moreover {
              fix v 
              assume "v \<in> dom (map_of (precondition_of op))" 
              moreover obtain a where "map_of (precondition_of op) v = Some a" 
                using calculation
                by blast
              moreover have "(v, a) \<in> set (precondition_of op)"
                using map_of_SomeD[OF calculation(2)].
              moreover have "(v, a) \<in> set (strips_operator.precondition_of op')"
                using op'_is 
                unfolding sasp_op_to_strips_def
                  SAS_Plus_STRIPS.sasp_op_to_strips_def
                using calculation(3) 
                by auto 
              moreover have "?s' (v, a) = Some True"
                using all_operators_applicable calculation 
                unfolding are_all_operators_applicable_def 
                    STRIPS_Representation.is_operator_applicable_in_def 
                    is_operator_applicable_in_def Let_def list_all_iff 
                using op'_in
                by fast
              moreover have "(v, a) \<in> dom ?s'" 
                using calculation(5)
                by blast
              moreover have "(v, a) \<in> set (precondition_of op)" 
                using op'_is calculation(3)
                unfolding sasp_op_to_strips_def Let_def
                by fastforce
              moreover have "v \<in> set ?vs" 
                and "a \<in> \<R>\<^sub>+ \<Psi> v" 
                and "s v \<noteq> None" 
                using state_to_strips_state_dom_element_iff[OF assms(1)]
                  calculation(6)
                by simp+
              moreover have "?s' (v, a) = Some (the (s v) = a)" 
                using state_to_strips_state_range_is[OF 
                    assms(1) calculation(6)].
              moreover have "the (s v) = a" 
                using calculation(5, 11)
                by fastforce
              moreover have "s v = Some a" 
                using calculation(12) option.collapse[OF calculation(10)]
                by argo
              moreover have "map_of (precondition_of op) v = Some a"
                using map_of_constant_assignments_defined_if[OF nb\<^sub>2[OF op_in] calculation(7)].
              ultimately have "map_of (precondition_of op) v = s v"
                by argo
            }
            then have "map_of (precondition_of op) \<subseteq>\<^sub>m s" 
              unfolding map_le_def
              by blast
            thus False 
              using not_precondition_map_le_s
              by simp
          qed
        thus ?thesis 
          by simp
      next
        case B
        {
          obtain op\<^sub>1 op\<^sub>2 v v' a a' 
            where "op\<^sub>1 \<in> set ops"
              and op\<^sub>2_in: "op\<^sub>2 \<in> set ops"
              and v_a_in: "(v, a) \<in> set (effect_of op\<^sub>1)"
              and v'_a'_in: "(v', a') \<in> set (effect_of op\<^sub>2)" 
              and v_is: "v = v'" and a_is: "a \<noteq> a'"  
            using B 
            unfolding are_all_operator_effects_consistent_def 
              are_operator_effects_consistent_def list_all_iff Let_def
            by blast
          moreover obtain op\<^sub>1' op\<^sub>2' where "op\<^sub>1' \<in> set ?ops'" and "op\<^sub>1' = \<phi>\<^sub>O \<Psi> op\<^sub>1"
            and "op\<^sub>1' \<in> set ?ops'" and op\<^sub>2'_is: "op\<^sub>2' = \<phi>\<^sub>O \<Psi> op\<^sub>2"
            using nb\<^sub>1[OF calculation(1)] nb\<^sub>1[OF calculation(2)]
            by blast
          moreover have "(v, a) \<in> set (add_effects_of op\<^sub>1')"
            using calculation(3, 8)
            unfolding SAS_Plus_STRIPS.sasp_op_to_strips_def
              sasp_op_to_strips_def Let_def
            by force
          moreover {
            have "is_valid_operator_sas_plus \<Psi> op\<^sub>1" 
              using assms(2) calculation(1) is_valid_problem_sas_plus_then(2) assms(1)
              unfolding is_valid_operator_sas_plus_def 
              by auto
            moreover have "is_valid_operator_sas_plus \<Psi> op\<^sub>2"
              using sublocale_sas_plus_finite_domain_representation_ii(2)[
                  OF assms(1)] assms(2) op\<^sub>2_in 
              by blast 
            moreover have "a \<in> \<R>\<^sub>+ \<Psi> v" 
              using is_valid_operator_sas_plus_then(4) calculation v_a_in
              unfolding is_valid_operator_sas_plus_def
              by fastforce
            ultimately have "(v, a) \<in> set (delete_effects_of op\<^sub>2')" 
              using sasp_op_to_strips_set_delete_effects_is[of \<Psi> op\<^sub>2]
                v'_a'_in v_is a_is 
              using op\<^sub>2'_is 
              by blast
          }
          \<comment> \<open> TODO slow. \<close>
          ultimately have "\<exists>op\<^sub>1' \<in> set ?ops'. \<exists>op\<^sub>2' \<in> set ?ops'. 
            \<exists>(v, a) \<in> set (delete_effects_of op\<^sub>2'). \<exists>(v', a') \<in> set (add_effects_of op\<^sub>1').
            (v, a) = (v', a')"
            by fastforce
        }
        then have "\<not>STRIPS_Semantics.are_all_operator_effects_consistent ?ops'" 
          unfolding STRIPS_Semantics.are_all_operator_effects_consistent_def 
            STRIPS_Semantics.are_operator_effects_consistent_def list_all_iff list_ex_iff Let_def 
          by blast
        thus ?thesis 
          by simp 
      qed
  }
  thus ?thesis 
    by blast
qed

(* TODO make private *)
lemma strips_equivalent_to_sas_plus_i_a:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "dom I \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom I. the (I v) \<in> \<R>\<^sub>+ \<Psi> v" 
    and "dom G \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    and "\<forall>v \<in> dom G. the (G v) \<in> \<R>\<^sub>+ \<Psi> v" 
    and "\<forall>ops \<in> set \<psi>. \<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
    and "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I \<psi>" 
  shows "(\<phi>\<^sub>S \<Psi> G) \<subseteq>\<^sub>m execute_parallel_plan (\<phi>\<^sub>S \<Psi> I) (\<phi>\<^sub>P \<Psi> \<psi>)" 
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
    and ?G' = "\<phi>\<^sub>S \<Psi> G"
  show ?thesis 
    using assms
    proof (induction \<psi> arbitrary: I)
      case Nil
      let ?I' = "\<phi>\<^sub>S \<Psi> I"
      have "G \<subseteq>\<^sub>m I" 
        using Nil
        by simp
      moreover have "?G' \<subseteq>\<^sub>m ?I'"
        using state_to_strips_state_map_le_iff[OF Nil.prems(1, 4, 5)] 
          calculation..
      ultimately show ?case 
        unfolding SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def
          sas_plus_parallel_plan_to_strips_parallel_plan_def
        by simp
    next
      case (Cons ops \<psi>)
      let ?vs = "variables_of \<Psi>"
        and ?ops = "operators_of \<Psi>"
        and ?J = "execute_parallel_operator_sas_plus I ops" 
        and ?\<pi> = "\<phi>\<^sub>P \<Psi> (ops # \<psi>)"
      let ?I' = "\<phi>\<^sub>S \<Psi> I"
        and ?J' = "\<phi>\<^sub>S \<Psi> ?J"
        and ?ops' = "[\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]"
      {
        fix op v a
        assume "op \<in> set ops" and "(v, a) \<in> set (effect_of op)" 
        moreover have "op \<in> set ?ops"
          using Cons.prems(6) calculation(1)
          by simp
        moreover have "is_valid_operator_sas_plus \<Psi> op" 
          using is_valid_problem_sas_plus_then(2) Cons.prems(1) calculation(3)
          unfolding is_valid_operator_sas_plus_def
          by auto
        ultimately have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
          and "a \<in> \<R>\<^sub>+ \<Psi> v"
          using is_valid_operator_sas_plus_then(3,4)
          by fastforce+
      } note nb\<^sub>1 = this
      show ?case
      proof (cases "are_all_operators_applicable_in I ops 
        \<and> are_all_operator_effects_consistent ops")
        case True
        {
          have "(\<phi>\<^sub>P \<Psi> (ops # \<psi>)) = ?ops' # (\<phi>\<^sub>P \<Psi> \<psi>)"
            unfolding sas_plus_parallel_plan_to_strips_parallel_plan_def
              SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def 
              sasp_op_to_strips_def
              SAS_Plus_STRIPS.sasp_op_to_strips_def
            by simp
          moreover have "\<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
            using Cons.prems(6)
            by simp
          moreover have "STRIPS_Semantics.are_all_operators_applicable ?I' ?ops'" 
            and "STRIPS_Semantics.are_all_operator_effects_consistent ?ops'" 
            using strips_equivalent_to_sas_plus_i_a_IV[OF Cons.prems(1) _ True] calculation
            by blast+
          ultimately have "execute_parallel_plan ?I' ?\<pi> 
            = execute_parallel_plan (execute_parallel_operator ?I' ?ops') (\<phi>\<^sub>P \<Psi> \<psi>)"
            by fastforce
        }
        \<comment> \<open> NOTE Instantiate the IH on the next state of the SAS+ execution 
          \<open>execute_parallel_operator_sas_plus I ops\<close>. \<close>
        moreover
        {
          {
            have "dom I \<subseteq> set (sas_plus_problem.variables_of \<Psi>)"
              using Cons.prems(2)
              by blast
            moreover have "\<forall>op \<in> set ops. \<forall>(v, a) \<in> set (effect_of op). 
              v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
              using nb\<^sub>1(1) 
              by blast
            ultimately have "dom ?J \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
              using sas_plus_equivalent_to_strips_i_a_IX[of I "set ?vs"]
              by simp
          } note nb\<^sub>2 = this
          moreover {
            have "dom I \<subseteq> set (sas_plus_problem.variables_of \<Psi>)"
              using Cons.prems(2)
              by blast
            moreover have "set (sas_plus_problem.variables_of \<Psi>)
              \<subseteq> dom (range_of \<Psi>)"
              using is_valid_problem_sas_plus_dom_sas_plus_problem_range_of assms(1)
              by auto
           moreover {
              fix v 
              assume "v \<in> dom I"  
              moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
                using Cons.prems(2) calculation
                by blast
              ultimately have "the (I v) \<in> set (the (range_of \<Psi> v))" 
                using Cons.prems(3)
                using set_the_range_of_is_range_of_sas_plus_if[OF assms(1)]
                by blast
            }
            moreover have "\<forall>op\<in>set ops. \<forall>(v, a)\<in>set (effect_of op).
              v \<in> set (sas_plus_problem.variables_of \<Psi>) \<and> a \<in> set (the (range_of \<Psi> v))"
              using set_the_range_of_is_range_of_sas_plus_if[OF assms(1)] nb\<^sub>1(1) nb\<^sub>1(2)
              by force
            moreover have nb\<^sub>3: "\<forall>v \<in> dom ?J. the (?J v) \<in> set (the (range_of \<Psi> v))" 
              using sas_plus_equivalent_to_strips_i_a_X[of I "set ?vs" "range_of \<Psi>" ops] 
                calculation
              by fast
            moreover {
              fix v
              assume "v \<in> dom ?J"
              moreover have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
                using nb\<^sub>2 calculation
                by blast
              moreover have "set (the (range_of \<Psi> v)) = \<R>\<^sub>+ \<Psi> v" 
                using set_the_range_of_is_range_of_sas_plus_if[OF assms(1)] 
                  calculation(2)
                by presburger
              ultimately have "the (?J v) \<in> \<R>\<^sub>+ \<Psi> v" 
                using nb\<^sub>3
                by blast
            }
            ultimately have "\<forall>v \<in> dom ?J. the (?J v) \<in> \<R>\<^sub>+ \<Psi> v"
              by fast
          }
          moreover have "\<forall>ops\<in>set \<psi>. \<forall>op\<in>set ops. op \<in> set ?ops" 
            using Cons.prems(6)
            by auto
          moreover have "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ?J \<psi>" 
            using Cons.prems(7) True
            by simp
          ultimately have "(\<phi>\<^sub>S \<Psi> G) \<subseteq>\<^sub>m execute_parallel_plan ?J' (\<phi>\<^sub>P \<Psi> \<psi>)"
            using Cons.IH[of ?J, OF Cons.prems(1) _ _ Cons.prems(4, 5)]
            by fastforce
        }
        moreover have "execute_parallel_operator ?I' ?ops' = ?J'" 
          using assms(1) strips_equivalent_to_sas_plus_i_a_III[OF assms(1)] Cons.prems(6)
          by auto
        ultimately show ?thesis
          by argo
      next
        case False
        then have nb: "G \<subseteq>\<^sub>m I" 
          using Cons.prems(7)
          by force
        moreover {
          have "?\<pi> = ?ops' # (\<phi>\<^sub>P \<Psi> \<psi>)"
            unfolding sas_plus_parallel_plan_to_strips_parallel_plan_def
              SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def 
              sasp_op_to_strips_def
              SAS_Plus_STRIPS.sasp_op_to_strips_def Let_def
            by auto
          moreover have "set ?ops' \<subseteq> set (strips_problem.operators_of ?\<Pi>)"
            using strips_equivalent_to_sas_plus_i_a_II(1)[OF assms(1)] Cons.prems(6)
            by auto
          moreover have "\<not>(STRIPS_Semantics.are_all_operators_applicable ?I' ?ops' 
            \<and> STRIPS_Semantics.are_all_operator_effects_consistent ?ops')"
            using strips_equivalent_to_sas_plus_i_a_V[OF assms(1) _ False] Cons.prems(6)
            by force 
          ultimately have "execute_parallel_plan ?I' ?\<pi> = ?I'"
            by auto
        }
        moreover have "?G' \<subseteq>\<^sub>m ?I'" 
          using state_to_strips_state_map_le_iff[OF Cons.prems(1, 4, 5)] nb
          by blast
        ultimately show ?thesis 
          by presburger
        qed 
    qed
qed

(* TODO make private *)
lemma strips_equivalent_to_sas_plus_i:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "is_parallel_solution_for_problem \<Psi> \<psi>"
  shows "(strips_problem.goal_of (\<phi> \<Psi>)) \<subseteq>\<^sub>m execute_parallel_plan 
    (strips_problem.initial_of (\<phi> \<Psi>)) (\<phi>\<^sub>P \<Psi> \<psi>)" 
proof -
  let ?vs = "variables_of \<Psi>"
    and ?ops = "operators_of \<Psi>"
    and ?I = "initial_of \<Psi>"
    and ?G = "goal_of \<Psi>"
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?I' = "strips_problem.initial_of ?\<Pi>"
    and ?G' = "strips_problem.goal_of ?\<Pi>"
  have "dom ?I \<subseteq> set ?vs"
    using is_valid_problem_sas_plus_then(3) assms(1)
    by auto
  moreover have "\<forall>v\<in>dom ?I. the (?I v) \<in> \<R>\<^sub>+ \<Psi> v" 
    using is_valid_problem_sas_plus_then(4) assms(1) calculation
    by auto
  moreover have "dom ?G \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    using is_valid_problem_sas_plus_then(5) assms(1)
    by auto
  moreover have "\<forall>v \<in> dom ?G. the (?G v) \<in> \<R>\<^sub>+ \<Psi> v"
    using is_valid_problem_sas_plus_then(6) assms(1)
    by auto
  moreover have "\<forall>ops \<in> set \<psi>. \<forall>op \<in> set ops. op \<in> set ?ops"
    using is_parallel_solution_for_problem_plan_operator_set[OF assms(2)]
    by fastforce
  moreover have "?G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ?I \<psi>" 
    using assms(2) 
    unfolding is_parallel_solution_for_problem_def
    by simp
  (* TODO slow *)
  ultimately show ?thesis
    using strips_equivalent_to_sas_plus_i_a[OF assms(1), of ?I ?G \<psi>]
    unfolding sas_plus_problem_to_strips_problem_def
      SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def 
      state_to_strips_state_def
      SAS_Plus_STRIPS.state_to_strips_state_def
    by force
qed

(* TODO make private *)
lemma strips_equivalent_to_sas_plus_ii:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "is_parallel_solution_for_problem \<Psi> \<psi>"
  shows "list_all (list_all (\<lambda>op. ListMem op (strips_problem.operators_of (\<phi> \<Psi>)))) (\<phi>\<^sub>P \<Psi> \<psi>)" 
proof -
  let ?ops = "operators_of \<Psi>"
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?ops' = "strips_problem.operators_of ?\<Pi>"
    and ?\<pi> = "\<phi>\<^sub>P \<Psi> \<psi>"
  have "is_valid_problem_strips ?\<Pi>" 
    using is_valid_problem_sas_plus_then_strips_transformation_too[OF assms(1)]
    by simp 
  have nb\<^sub>1: "\<forall>op \<in> set ?ops. (\<exists>op' \<in> set ?ops'. op' = (\<phi>\<^sub>O \<Psi> op))" 
    unfolding sas_plus_problem_to_strips_problem_def
      SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def Let_def 
      sasp_op_to_strips_def
    by force
  {
    fix ops op op'
    assume "ops \<in> set \<psi>" and "op \<in> set ops" 
    moreover have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
      using is_parallel_solution_for_problem_plan_operator_set[OF assms(2)] 
        calculation
      by blast
    moreover obtain op' where "op' \<in> set ?ops'" and "op' = (\<phi>\<^sub>O \<Psi> op)" 
      using nb\<^sub>1 calculation(3)
      by auto
    ultimately have "(\<phi>\<^sub>O \<Psi> op) \<in> set ?ops'"
      by blast
  }
  thus ?thesis 
    unfolding list_all_iff ListMem_iff Let_def  
      sas_plus_problem_to_strips_problem_def
      SAS_Plus_STRIPS.sas_plus_problem_to_strips_problem_def
      sas_plus_parallel_plan_to_strips_parallel_plan_def
      SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def 
      sasp_op_to_strips_def
      SAS_Plus_STRIPS.sasp_op_to_strips_def 
      Let_def 
    by auto
qed

text \<open> The following lemma proves the complementary proposition to theorem 
\ref{isathm:equivalence-parallel-strips-parallel-sas-plus}. Namely, given a parallel solution
\<^term>\<open>\<psi>\<close> for a SAS+ problem, the transformation to a STRIPS plan \<^term>\<open>\<phi>\<^sub>P \<Psi> \<psi>\<close> also is a solution 
to the corresponding STRIPS problem \<^term>\<open>\<Pi> \<equiv> (\<phi> \<Psi>)\<close>. In this direction, we have to show that the 
execution of the transformed plan reaches the goal state \<^term>\<open>G' \<equiv> strips_problem.goal_of \<Pi>\<close> 
of the corresponding STRIPS problem, i.e.
  @{text[display, indent=4] "G' \<subseteq>\<^sub>m execute_parallel_plan I' \<pi>"} 
and that all operators in the transformed plan \<^term>\<open>\<pi>\<close> are operators of \<^term>\<open>\<Pi>\<close>. \<close>

theorem
  strips_equivalent_to_sas_plus:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "is_parallel_solution_for_problem \<Psi> \<psi>"
  shows "STRIPS_Semantics.is_parallel_solution_for_problem (\<phi> \<Psi>) (\<phi>\<^sub>P \<Psi> \<psi>)"
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?I' = "strips_problem.initial_of ?\<Pi>"
    and ?G' = "strips_problem.goal_of ?\<Pi>"
    and ?ops' = "strips_problem.operators_of ?\<Pi>"
    and ?\<pi> = "\<phi>\<^sub>P \<Psi> \<psi>"
  show ?thesis
    unfolding STRIPS_Semantics.is_parallel_solution_for_problem_def 
    proof (rule conjI)
      show "?G' \<subseteq>\<^sub>m execute_parallel_plan ?I' ?\<pi>"
        using strips_equivalent_to_sas_plus_i[OF assms]
        by simp
    next 
      show "list_all (list_all (\<lambda>op. ListMem op ?ops')) ?\<pi>" 
        using strips_equivalent_to_sas_plus_ii[OF assms].
    qed
qed

lemma embedded_serial_sas_plus_plan_operator_structure:
  assumes "ops \<in> set (embed \<psi>)"
  obtains op 
  where "op \<in> set \<psi>" 
    and "[\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops] = [\<phi>\<^sub>O \<Psi> op]"
proof -
  let ?\<psi>' = "embed \<psi>"
  {
    have "?\<psi>' = [[op]. op \<leftarrow> \<psi>]"
      by (induction \<psi>; force)
    moreover obtain op where "ops = [op]" and "op \<in> set \<psi>" 
      using assms calculation 
      by fastforce
    ultimately have "\<exists>op \<in> set \<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops] = [\<phi>\<^sub>O \<Psi> op]"
      by auto
  }
  thus ?thesis 
    using that
    by meson
qed

private lemma serial_sas_plus_equivalent_to_serial_strips_i: 
  assumes "ops \<in> set (\<phi>\<^sub>P \<Psi> (embed \<psi>))"
  obtains op where "op \<in> set \<psi>" and "ops = [\<phi>\<^sub>O \<Psi> op]"  
proof -
  let ?\<psi>' = "embed \<psi>" 
  {
    have "set (\<phi>\<^sub>P \<Psi> (embed \<psi>)) = { [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]  | ops. ops \<in> set ?\<psi>' }"
      
      unfolding sas_plus_parallel_plan_to_strips_parallel_plan_def  
        SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def
        sasp_op_to_strips_def set_map
      using setcompr_eq_image  
      by blast
    moreover obtain ops' where "ops' \<in> set ?\<psi>'" and "ops = [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops']" 
      using assms(1) calculation
      by blast
    moreover obtain op where "op \<in> set \<psi>" and "ops = [\<phi>\<^sub>O \<Psi> op]" 
      using embedded_serial_sas_plus_plan_operator_structure calculation(2, 3)
      by blast
    ultimately have "\<exists>op \<in> set \<psi>. ops = [\<phi>\<^sub>O \<Psi> op]"
      by meson
  }
  thus ?thesis 
    using that..
qed

private lemma serial_sas_plus_equivalent_to_serial_strips_ii[simp]:
  "concat (\<phi>\<^sub>P \<Psi> (embed \<psi>)) = [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]" 
proof -
  let ?\<psi>' = "List_Supplement.embed \<psi>"
  have "concat (\<phi>\<^sub>P \<Psi> ?\<psi>') = map (\<lambda>op. \<phi>\<^sub>O \<Psi> op) (concat ?\<psi>')" 
    unfolding sas_plus_parallel_plan_to_strips_parallel_plan_def
      SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def
      sasp_op_to_strips_def
      SAS_Plus_STRIPS.sasp_op_to_strips_def Let_def
      map_concat
    by blast
  also have "\<dots> = map (\<lambda>op. \<phi>\<^sub>O \<Psi> op) \<psi>" 
    unfolding concat_is_inverse_of_embed[of \<psi>]..
  finally show "concat (\<phi>\<^sub>P \<Psi> (embed \<psi>)) = [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]".
qed

text \<open> Having established the equivalence of parallel STRIPS and SAS+, we can now show the 
equivalence in the serial case. The proof combines the 
embedding theorem for serial SAS+ solutions (\ref{isathm:serial-sas-plus-embedding}), the parallel 
plan equivalence theorem \ref{isathm:equivalence-parallel-sas-plus-parallel-strips}, and the 
flattening theorem for parallel STRIPS plans (\ref{isathm:embedded-serial-plan-flattening-strips}).
More precisely, given a serial SAS+ solution \<^term>\<open>\<psi>\<close> for a SAS+ problem \<^term>\<open>\<Psi>\<close>, the embedding 
theorem confirms that the embedded plan \<^term>\<open>embed \<psi>\<close> is an equivalent parallel solution to
\<^term>\<open>\<Psi>\<close>. By parallel plan equivalence, \<^term>\<open>\<pi> \<equiv> \<phi>\<^sub>P \<Psi> (embed \<psi>)\<close> is a parallel solution for the 
corresponding STRIPS problem \<^term>\<open>\<phi> \<Psi>\<close>. Moreover, since \<^term>\<open>embed \<psi>\<close> is a plan consisting of 
singleton parallel operators, the same is true for \<^term>\<open>\<pi>\<close>. Hence, the flattening lemma applies 
and \<^term>\<open>concat \<pi>\<close> is a serial solution for \<^term>\<open>\<phi> \<Psi>\<close>. Since \<^term>\<open>concat\<close> moreover can be shown 
to be the inverse of \<^term>\<open>embed\<close>, the term 
  @{text[display, indent=4] "concat \<pi> = concat (\<phi>\<^sub>P \<Psi> (embed \<psi>))"}
can be reduced to the intuitive form 
  @{text[display, indent=4] "\<pi> = [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]"}
which concludes the proof. \<close>

theorem 
  serial_sas_plus_equivalent_to_serial_strips:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> \<psi>"
  shows "STRIPS_Semantics.is_serial_solution_for_problem (\<phi> \<Psi>) [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]" 
proof -
  let ?\<psi>' = "embed \<psi>"
    and ?\<Pi> = "\<phi> \<Psi>"
  let ?\<pi>' = "\<phi>\<^sub>P \<Psi> ?\<psi>'"
  let ?\<pi> = "concat ?\<pi>'"
  {
    have "SAS_Plus_Semantics.is_parallel_solution_for_problem \<Psi> ?\<psi>'"
      using execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus[OF assms]
      by simp
    hence "STRIPS_Semantics.is_parallel_solution_for_problem ?\<Pi> ?\<pi>'"
      using strips_equivalent_to_sas_plus[OF assms(1)]
      by simp
  }
  moreover have "?\<pi> = [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]"
    by simp
  moreover have "is_valid_problem_strips ?\<Pi>"
      using is_valid_problem_sas_plus_then_strips_transformation_too[OF assms(1)].
  moreover have "\<forall>ops \<in> set ?\<pi>'. \<exists>op \<in> set \<psi>. ops = [\<phi>\<^sub>O \<Psi> op]" 
    using serial_sas_plus_equivalent_to_serial_strips_i[of _ \<Psi> \<psi>]
    by metis
  ultimately show ?thesis
    using STRIPS_Semantics.flattening_lemma[of ?\<Pi>]
    by metis
qed


lemma embedded_serial_strips_plan_operator_structure:
  assumes "ops' \<in> set (embed \<pi>)"
  obtains op 
    where "op \<in> set \<pi>" and "[\<phi>\<^sub>O\<inverse> \<Pi> op. op \<leftarrow> ops'] = [\<phi>\<^sub>O\<inverse> \<Pi> op]"
proof -
  let ?\<pi>' = "embed \<pi>" 
  {
    have "?\<pi>' = [[op]. op \<leftarrow> \<pi>]"
      by (induction \<pi>; force)
    moreover obtain op where "ops' = [op]" and "op \<in> set \<pi>" 
      using calculation assms 
      by fastforce
    ultimately have "\<exists>op \<in> set \<pi>. [\<phi>\<^sub>O\<inverse> \<Pi> op. op \<leftarrow> ops'] = [\<phi>\<^sub>O\<inverse> \<Pi> op]"
      by auto
  }
  thus ?thesis 
    using that
    by meson
qed

private lemma serial_strips_equivalent_to_serial_sas_plus_i: 
  assumes "ops \<in> set (\<phi>\<^sub>P\<inverse> \<Pi> (embed \<pi>))"
  obtains op where "op \<in> set \<pi>" and "ops = [\<phi>\<^sub>O\<inverse> \<Pi> op]"  
proof -
  let ?\<pi>' = "embed \<pi>" 
  {
    have "set (\<phi>\<^sub>P\<inverse> \<Pi> (embed \<pi>)) = { [\<phi>\<^sub>O\<inverse> \<Pi> op. op \<leftarrow> ops]  | ops. ops \<in> set ?\<pi>' }"
      unfolding strips_parallel_plan_to_sas_plus_parallel_plan_def
        SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
        strips_op_to_sasp_def set_map
      using setcompr_eq_image 
      by blast
    moreover obtain ops' where "ops' \<in> set ?\<pi>'" and "ops = [\<phi>\<^sub>O\<inverse> \<Pi> op. op \<leftarrow> ops']" 
      using assms(1) calculation
      by blast
    moreover obtain op where "op \<in> set \<pi>" and "ops = [\<phi>\<^sub>O\<inverse> \<Pi> op]" 
      using embedded_serial_strips_plan_operator_structure calculation(2, 3)
      by blast
    ultimately have "\<exists>op \<in> set \<pi>. ops = [\<phi>\<^sub>O\<inverse> \<Pi> op]" 
      by meson
  }
  thus ?thesis 
    using that..
qed

private lemma serial_strips_equivalent_to_serial_sas_plus_ii[simp]:
  "concat (\<phi>\<^sub>P\<inverse> \<Pi> (embed \<pi>)) = [\<phi>\<^sub>O\<inverse> \<Pi> op. op \<leftarrow> \<pi>]" 
proof -
  let ?\<pi>' = "List_Supplement.embed \<pi>"
  have "concat (\<phi>\<^sub>P\<inverse> \<Pi> ?\<pi>') = map (\<lambda>op. \<phi>\<^sub>O\<inverse> \<Pi> op) (concat ?\<pi>')" 
    unfolding strips_parallel_plan_to_sas_plus_parallel_plan_def
      SAS_Plus_STRIPS.strips_parallel_plan_to_sas_plus_parallel_plan_def
      strips_op_to_sasp_def
      SAS_Plus_STRIPS.strips_op_to_sasp_def Let_def
      map_concat 
    by simp
  also have "\<dots> = map (\<lambda>op. \<phi>\<^sub>O\<inverse> \<Pi> op) \<pi>" 
    unfolding concat_is_inverse_of_embed[of \<pi>]..
  finally show "concat (\<phi>\<^sub>P\<inverse> \<Pi> (embed \<pi>)) = [\<phi>\<^sub>O\<inverse> \<Pi> op. op \<leftarrow> \<pi>]".
qed

text \<open> Using the analogous lemmas for the opposite direction, we can show the counterpart to 
theorem \ref{isathm:equivalence-serial-sas-plus-serial-strips} which shows that serial solutions 
to STRIPS solutions can be transformed to serial SAS+ solutions via composition of embedding, 
transformation and flattening. \<close>

theorem 
  serial_strips_equivalent_to_serial_sas_plus:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "STRIPS_Semantics.is_serial_solution_for_problem (\<phi> \<Psi>) \<pi>"
  shows "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>]" 
proof -
  let ?\<pi>' = "embed \<pi>"
    and ?\<Pi> = "\<phi> \<Psi>"
  let ?\<psi>' = "\<phi>\<^sub>P\<inverse> \<Psi> ?\<pi>'"
  let ?\<psi> = "concat ?\<psi>'"
  {
    have "STRIPS_Semantics.is_parallel_solution_for_problem ?\<Pi> ?\<pi>'"
      using embedding_lemma[OF 
          is_valid_problem_sas_plus_then_strips_transformation_too[OF assms(1)] assms(2)].
    hence "SAS_Plus_Semantics.is_parallel_solution_for_problem \<Psi> ?\<psi>'"
      using sas_plus_equivalent_to_strips[OF assms(1)]
      by simp
  }
  moreover have "?\<psi> = [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>]"
    by simp
  moreover have "is_valid_problem_strips ?\<Pi>"
      using is_valid_problem_sas_plus_then_strips_transformation_too[OF assms(1)].
  moreover have "\<forall>ops \<in> set ?\<psi>'. \<exists>op \<in> set \<pi>. ops = [\<phi>\<^sub>O\<inverse> \<Psi> op]" 
    using serial_strips_equivalent_to_serial_sas_plus_i
    by metis
  ultimately show ?thesis
    using flattening_lemma[OF assms(1)]
    by metis
qed

subsection "Equivalence of SAS+ and STRIPS" 

\<comment> \<open> Define the sets of plans with upper length bound as well as the sets of solutions with 
upper length bound for  SAS problems and induced STRIPS problems.

 We keep this polymorphic by not specifying concrete types so it applies to both STRIPS and 
SAS+ plans. \<close>
abbreviation bounded_plan_set 
  where "bounded_plan_set ops k \<equiv> { \<pi>. set \<pi> \<subseteq> set ops \<and> length \<pi> = k }"

definition bounded_solution_set_sas_plus' 
  :: "('variable, 'domain) sas_plus_problem 
    \<Rightarrow> nat
    \<Rightarrow> ('variable, 'domain) sas_plus_plan set" 
  where "bounded_solution_set_sas_plus' \<Psi> k 
    \<equiv> { \<psi>. is_serial_solution_for_problem \<Psi> \<psi> \<and> length \<psi> = k}"

abbreviation bounded_solution_set_sas_plus
  :: "('variable, 'domain) sas_plus_problem 
    \<Rightarrow> nat
    \<Rightarrow> ('variable, 'domain) sas_plus_plan set" 
  where "bounded_solution_set_sas_plus \<Psi> N 
    \<equiv> (\<Union>k \<in> {0..N}. bounded_solution_set_sas_plus' \<Psi> k)"

definition bounded_solution_set_strips'
  :: "('variable \<times> 'domain) strips_problem 
    \<Rightarrow> nat
    \<Rightarrow> ('variable \<times> 'domain) strips_plan set" 
  where "bounded_solution_set_strips' \<Pi> k
    \<equiv> { \<pi>. STRIPS_Semantics.is_serial_solution_for_problem \<Pi> \<pi> \<and> length \<pi> = k }"

abbreviation bounded_solution_set_strips
  :: "('variable \<times> 'domain) strips_problem 
    \<Rightarrow> nat 
    \<Rightarrow> ('variable \<times> 'domain) strips_plan set" 
  where "bounded_solution_set_strips \<Pi> N \<equiv> (\<Union>k \<in> {0..N}. bounded_solution_set_strips' \<Pi> k)"

\<comment> \<open> Show that plan transformation for all SAS Plus solutions yields a STRIPS solution for the
induced STRIPS problem with same length. 

We first show injectiveness of plan transformation \<open>\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]\<close> on the set of plans 
\<open>P\<^sub>k \<equiv> bounded_plan_set (operators_of \<Psi>) k\<close> with length bound \<open>k\<close>. The injectiveness of 
\<open>Sol\<^sub>k \<equiv> bounded_solution_set_sas_plus \<Psi> k\<close>---the set of solutions with length bound \<open>k\<close>--then 
follows from the subset relation \<open>Sol\<^sub>k \<subseteq> P\<^sub>k\<close>. \<close>
lemma sasp_op_to_strips_injective:
  assumes "(\<phi>\<^sub>O \<Psi> op\<^sub>1) = (\<phi>\<^sub>O \<Psi> op\<^sub>2)"
  shows "op\<^sub>1 = op\<^sub>2" 
  proof  -
    let ?op\<^sub>1' = "\<phi>\<^sub>O \<Psi> op\<^sub>1" 
      and ?op\<^sub>2' = "\<phi>\<^sub>O \<Psi> op\<^sub>2" 
    {
      have "strips_operator.precondition_of ?op\<^sub>1' = strips_operator.precondition_of ?op\<^sub>2'"
        using assms 
        by argo
      hence "sas_plus_operator.precondition_of op\<^sub>1 = sas_plus_operator.precondition_of op\<^sub>2"
        unfolding sasp_op_to_strips_def
          SAS_Plus_STRIPS.sasp_op_to_strips_def
          Let_def 
        by simp
    }
    moreover {
      have "strips_operator.add_effects_of ?op\<^sub>1' = strips_operator.add_effects_of ?op\<^sub>2'"
        using assms 
        unfolding sasp_op_to_strips_def Let_def 
        by argo
      hence "sas_plus_operator.effect_of op\<^sub>1 = sas_plus_operator.effect_of op\<^sub>2"
        unfolding sasp_op_to_strips_def Let_def
          SAS_Plus_STRIPS.sasp_op_to_strips_def
        by simp
    }
    ultimately show ?thesis 
      by simp
  qed

lemma sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_a:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "inj_on (\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]) (bounded_plan_set (sas_plus_problem.operators_of \<Psi>) k)" 
  proof -
    let ?ops = "sas_plus_problem.operators_of \<Psi>"
      (* TODO refactor transformation definitions *)
      and ?\<phi>\<^sub>P = "\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]"
    let ?P = "bounded_plan_set ?ops"
    {
      fix \<psi>\<^sub>1 \<psi>\<^sub>2
      assume \<psi>\<^sub>1_in: "\<psi>\<^sub>1 \<in> ?P k" 
        and \<psi>\<^sub>2_in: "\<psi>\<^sub>2 \<in> ?P k" 
        and \<phi>\<^sub>P_of_\<psi>\<^sub>1_is_\<phi>\<^sub>P_of_\<psi>\<^sub>2: "(?\<phi>\<^sub>P \<psi>\<^sub>1) = (?\<phi>\<^sub>P \<psi>\<^sub>2)"
      hence "\<psi>\<^sub>1 = \<psi>\<^sub>2"
        proof (induction k arbitrary: \<psi>\<^sub>1 \<psi>\<^sub>2)
          case 0
          then have "length \<psi>\<^sub>1 = 0" 
            and "length \<psi>\<^sub>2 = 0" 
            using \<psi>\<^sub>1_in \<psi>\<^sub>2_in
            unfolding bounded_solution_set_sas_plus'_def 
            by blast+
          then show ?case 
            by blast
        next
          case (Suc k)
          moreover have "length \<psi>\<^sub>1 = Suc k" and "length \<psi>\<^sub>2 = Suc k"
            using length_Suc_conv Suc(2, 3) 
            unfolding bounded_solution_set_sas_plus'_def
            by blast+
          moreover obtain op\<^sub>1 \<psi>\<^sub>1' where "\<psi>\<^sub>1 = op\<^sub>1 # \<psi>\<^sub>1'" 
            and "set (op\<^sub>1 # \<psi>\<^sub>1') \<subseteq> set ?ops"
            and "length \<psi>\<^sub>1' = k" 
            using calculation(5) Suc(2)
            unfolding length_Suc_conv
            by blast
          moreover obtain op\<^sub>2 \<psi>\<^sub>2' where "\<psi>\<^sub>2 = op\<^sub>2 # \<psi>\<^sub>2'" 
            and "set (op\<^sub>2 # \<psi>\<^sub>2') \<subseteq> set ?ops" 
            and "length \<psi>\<^sub>2' = k"
            using calculation(6) Suc(3)
            unfolding length_Suc_conv
            by blast
          moreover have "set \<psi>\<^sub>1' \<subseteq> set ?ops" and "set \<psi>\<^sub>2' \<subseteq> set ?ops" 
            using calculation(8, 11) 
            by auto+
          moreover have "\<psi>\<^sub>1' \<in> ?P k" and "\<psi>\<^sub>2' \<in> ?P k"
            using calculation(9, 12, 13, 14)
            by fast+
          moreover have "?\<phi>\<^sub>P \<psi>\<^sub>1' = ?\<phi>\<^sub>P \<psi>\<^sub>2'" 
            using Suc.prems(3) calculation(7, 10) 
            by fastforce
          moreover have "\<psi>\<^sub>1' = \<psi>\<^sub>2'" 
            using Suc.IH[of \<psi>\<^sub>1' \<psi>\<^sub>2', OF calculation(15, 16, 17)]
            by simp
          moreover have "?\<phi>\<^sub>P \<psi>\<^sub>1 = (\<phi>\<^sub>O \<Psi> op\<^sub>1) # ?\<phi>\<^sub>P \<psi>\<^sub>1'" 
            and "?\<phi>\<^sub>P \<psi>\<^sub>2 = (\<phi>\<^sub>O \<Psi> op\<^sub>2) # ?\<phi>\<^sub>P \<psi>\<^sub>2'"
            using Suc.prems(3) calculation(7, 10) 
            by fastforce+
          moreover have "(\<phi>\<^sub>O \<Psi> op\<^sub>1) = (\<phi>\<^sub>O \<Psi> op\<^sub>2)" 
            using Suc.prems(3) calculation(17, 19, 20)
            by simp
          moreover have "op\<^sub>1 = op\<^sub>2" 
            using sasp_op_to_strips_injective[OF calculation(21)].
          ultimately show ?case 
            by argo
        qed
    }
    thus ?thesis 
      unfolding inj_on_def 
      by blast
  qed

private corollary sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_b:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "inj_on (\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]) (bounded_solution_set_sas_plus' \<Psi> k)"
  proof -
    let ?ops = "sas_plus_problem.operators_of \<Psi>"
      and ?\<phi>\<^sub>P = "\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]"
    {
      fix \<psi>
      assume "\<psi> \<in> bounded_solution_set_sas_plus' \<Psi> k" 
      then have "set \<psi> \<subseteq> set ?ops" 
        and "length \<psi> = k" 
        unfolding bounded_solution_set_sas_plus'_def is_serial_solution_for_problem_def Let_def 
          list_all_iff ListMem_iff 
        by fast+
      hence "\<psi> \<in> bounded_plan_set ?ops k" 
         by blast
    }
    hence "bounded_solution_set_sas_plus' \<Psi> k \<subseteq> bounded_plan_set ?ops k" 
      by blast
    moreover have "inj_on ?\<phi>\<^sub>P (bounded_plan_set ?ops k)" 
      using sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_a[OF assms(1)].
    ultimately show ?thesis
      using inj_on_subset[of ?\<phi>\<^sub>P "bounded_plan_set ?ops k" "bounded_solution_set_sas_plus' \<Psi> k"]
      by fast
  qed

(*
lemma "card ((\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]) ` (bounded_solution_set_sas_plus' \<Psi> k)) 
  = card (bounded_solution_set_strips' (\<phi> \<Psi>) k)"  sorry
*)

\<comment> \<open> Show that mapping plan transformation \<open>\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]\<close> over the solution set for a 
given SAS+ problem yields the solution set for the induced STRIPS problem. \<close>
private lemma sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_c:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "(\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]) ` (bounded_solution_set_sas_plus' \<Psi> k) 
    = bounded_solution_set_strips' (\<phi> \<Psi>) k" 
 proof -
   let ?\<Pi> = "\<phi> \<Psi>"
     and ?\<phi>\<^sub>P = "\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]"
   let ?Sol\<^sub>k = "bounded_solution_set_sas_plus' \<Psi> k"
    and ?Sol\<^sub>k' = "bounded_solution_set_strips' ?\<Pi> k"
   {
     assume "?\<phi>\<^sub>P ` ?Sol\<^sub>k \<noteq> ?Sol\<^sub>k'" 
     then consider (A) "\<exists>\<pi> \<in> ?\<phi>\<^sub>P ` ?Sol\<^sub>k. \<pi> \<notin> ?Sol\<^sub>k'"
       | (B) "\<exists>\<pi> \<in> ?Sol\<^sub>k'. \<pi> \<notin>  ?\<phi>\<^sub>P ` ?Sol\<^sub>k"
       by blast
     hence False 
       proof (cases)
         case A
         moreover obtain \<pi> where "\<pi> \<in> ?\<phi>\<^sub>P ` ?Sol\<^sub>k" and "\<pi> \<notin> ?Sol\<^sub>k'"
           using calculation
           by blast
         moreover obtain \<psi> where "length \<psi> = k" 
           and "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> \<psi>" 
           and "\<pi> = ?\<phi>\<^sub>P \<psi>" 
           using calculation(2)
           unfolding bounded_solution_set_sas_plus'_def 
           by blast
         moreover have "length \<pi> = k" and "STRIPS_Semantics.is_serial_solution_for_problem ?\<Pi> \<pi>"
           subgoal 
             using calculation(4, 6) by auto
           subgoal
             using serial_sas_plus_equivalent_to_serial_strips
               assms(1) calculation(5) calculation(6) 
             by blast
           done
         moreover have "\<pi> \<in> ?Sol\<^sub>k'" 
           unfolding bounded_solution_set_strips'_def 
           using calculation(7, 8) 
           by simp
         ultimately show ?thesis
           by fast
       next
         case B
         moreover obtain \<pi> where "\<pi> \<in> ?Sol\<^sub>k'" and "\<pi> \<notin> ?\<phi>\<^sub>P ` ?Sol\<^sub>k"
           using calculation
           by blast
         moreover have "STRIPS_Semantics.is_serial_solution_for_problem ?\<Pi> \<pi>"
           and "length \<pi> = k"
           using calculation(2)
           unfolding bounded_solution_set_strips'_def 
           by simp+
         \<comment> \<open> Construct the counter example \<open>\<psi> \<equiv> [\<phi>\<^sub>O\<inverse> ?\<Pi> op. op \<leftarrow> \<pi>]\<close> and show that \<open>\<psi> \<in> ?Sol\<^sub>k\<close>
            as well as \<open>?\<phi>\<^sub>P \<psi> = \<pi>\<close> hence \<open>\<pi> \<in> ?\<phi>\<^sub>P ` ?Sol\<^sub>k\<close>. \<close>
         moreover have "length [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>] = k"
           and "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>]" 
           subgoal 
             using calculation(5) 
             by simp
           subgoal 
             using serial_strips_equivalent_to_serial_sas_plus[OF assms(1)] 
               calculation(4)
             by simp
           done
         moreover have "[\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>] \<in> ?Sol\<^sub>k" 
           unfolding bounded_solution_set_sas_plus'_def 
           using calculation(6, 7) 
           by blast
         (* TODO refactor transformation lemmas *)
         moreover {
           have "\<forall>op \<in> set \<pi>. op \<in> set ((?\<Pi>)\<^sub>\<O>)"
             using calculation(4)
             unfolding STRIPS_Semantics.is_serial_solution_for_problem_def list_all_iff ListMem_iff
             by simp
           hence "?\<phi>\<^sub>P [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>] = \<pi>" 
             proof (induction \<pi>)
               case (Cons op \<pi>)
               moreover have "?\<phi>\<^sub>P [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> op # \<pi>] 
                = (\<phi>\<^sub>O \<Psi> (\<phi>\<^sub>O\<inverse> \<Psi> op)) # ?\<phi>\<^sub>P [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>]"
                 by simp
               moreover have "op \<in>  set ((?\<Pi>)\<^sub>\<O>)" 
                 using Cons.prems
                 by simp
               moreover have "(\<phi>\<^sub>O \<Psi> (\<phi>\<^sub>O\<inverse> \<Psi> op)) = op"
                 using strips_operator_inverse_is[OF assms(1) calculation(4)].
               moreover have "?\<phi>\<^sub>P [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> \<pi>] = \<pi>" 
                 using Cons.IH Cons.prems 
                 by auto
               ultimately show ?case 
                 by argo
             qed simp
         }
         moreover have "\<pi> \<in> ?\<phi>\<^sub>P ` ?Sol\<^sub>k" 
           using calculation(8, 9) 
           by force
         ultimately show ?thesis
           by blast
      qed
   }
   thus ?thesis 
     by blast
  qed

private lemma sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_d:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "card (bounded_solution_set_sas_plus' \<Psi> k) \<le> card (bounded_solution_set_strips' (\<phi> \<Psi>) k)"
  proof -
    let ?\<Pi> = "\<phi> \<Psi>"
      and ?\<phi>\<^sub>P = "\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]"
    let ?Sol\<^sub>k = "bounded_solution_set_sas_plus' \<Psi> k"
      and ?Sol\<^sub>k' = "bounded_solution_set_strips' ?\<Pi> k"
    have "card (?\<phi>\<^sub>P ` ?Sol\<^sub>k) = card (?Sol\<^sub>k)"
     using sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_b[OF assms(1)] 
       card_image 
     by blast
    moreover have "?\<phi>\<^sub>P ` ?Sol\<^sub>k = ?Sol\<^sub>k'"
     using sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_c[OF assms(1)].
    ultimately show ?thesis 
     by simp
  qed

\<comment> \<open> The set of fixed length plans with operators in a given operator set is finite. \<close>
lemma bounded_plan_set_finite:
  shows "finite { \<pi>. set \<pi> \<subseteq> set ops \<and> length \<pi> = k }"
  proof (induction k)
    case (Suc k)
    let ?P = "{ \<pi>. set \<pi> \<subseteq> set ops \<and> length \<pi> = k }"
      and ?P' = "{ \<pi>. set \<pi> \<subseteq> set ops \<and> length \<pi> = Suc k }"  
    let ?P'' = "(\<Union>op \<in> set ops. (\<Union>\<pi> \<in> ?P. { op # \<pi> }))" 
    {
      have "\<forall>op \<pi>. finite { op # \<pi> }"
        by simp
      then have "\<forall>op. finite (\<Union>\<pi> \<in> ?P. { op # \<pi> })" 
        using finite_UN[of ?P] Suc 
        by blast
      hence "finite ?P''" 
        using finite_UN[of "set ops"]
        by blast
    }
    moreover {
      {
        fix \<pi>
        assume "\<pi> \<in> ?P'"
        moreover have "set \<pi> \<subseteq> set ops" 
          and "length \<pi> = Suc k" 
          using calculation 
          by simp+
        moreover obtain op \<pi>' where "\<pi> = op # \<pi>'" 
          using calculation (3)
          unfolding length_Suc_conv 
          by fast
        moreover have "set \<pi>' \<subseteq> set ops" and "op \<in> set ops"
          using calculation(2, 4) 
          by simp+
        moreover have "length \<pi>' = k"
          using calculation(3, 4) 
          by auto
        moreover have "\<pi>' \<in> ?P" 
          using calculation(5, 7)
          by blast
        ultimately have "\<pi> \<in> ?P''"
          by blast
      }
      hence "?P' \<subseteq> ?P''"
        by blast
    }
    ultimately show ?case 
      using rev_finite_subset[of ?P'' ?P']
      by blast
  qed force

\<comment> \<open> The set of fixed length SAS+ solutions are subsets of the set of plans with fixed length and 
therefore also finite. \<close>
private lemma sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_ii_a:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "finite (bounded_solution_set_sas_plus' \<Psi> k)"
proof -
  let ?Ops = "set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
  let ?Sol\<^sub>k = "bounded_solution_set_sas_plus' \<Psi> k"
    and ?P\<^sub>k = "{ \<pi>. set \<pi> \<subseteq> ?Ops \<and> length \<pi> = k }"
  {
    fix \<psi>
    assume "\<psi> \<in> ?Sol\<^sub>k"
    then have "length \<psi> = k" and "set \<psi> \<subseteq> ?Ops"
      unfolding bounded_solution_set_sas_plus'_def 
        SAS_Plus_Semantics.is_serial_solution_for_problem_def Let_def list_all_iff ListMem_iff
      by fastforce+
    hence "\<psi> \<in> ?P\<^sub>k" 
      by blast
  }
  then have "?Sol\<^sub>k \<subseteq> ?P\<^sub>k" 
    by force
  thus ?thesis
    using bounded_plan_set_finite rev_finite_subset[of ?P\<^sub>k ?Sol\<^sub>k]
    by auto
qed

\<comment> \<open> The set of fixed length STRIPS solutions are subsets of the set of plans with fixed length and 
therefore also finite. \<close>
private lemma sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_ii_b:
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "finite (bounded_solution_set_strips' (\<phi> \<Psi>) k)"
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
  let ?Ops = "set ((?\<Pi>)\<^sub>\<O>)"
  let ?Sol\<^sub>k = "bounded_solution_set_strips' ?\<Pi> k"
    and ?P\<^sub>k = "{ \<pi>. set \<pi> \<subseteq> ?Ops \<and> length \<pi> = k }"
  {
    fix \<pi>
    assume "\<pi> \<in> ?Sol\<^sub>k"
    then have "length \<pi> = k" and "set \<pi> \<subseteq> ?Ops"
      unfolding bounded_solution_set_strips'_def 
        STRIPS_Semantics.is_serial_solution_for_problem_def Let_def list_all_iff ListMem_iff
      by fastforce+
    hence "\<pi> \<in> ?P\<^sub>k" 
      by blast
  }
  then have "?Sol\<^sub>k \<subseteq> ?P\<^sub>k" 
    by force
  thus ?thesis
    using bounded_plan_set_finite rev_finite_subset[of ?P\<^sub>k ?Sol\<^sub>k] 
    unfolding state_to_strips_state_def
      SAS_Plus_STRIPS.state_to_strips_state_def operators_of_def
    by blast
qed

text \<open> With the results on the equivalence of SAS+ and STRIPS solutions, we can now show that given 
problems in both formalisms, the solution sets have the same size.
This is the property required by the definition of planning formalism equivalence presented earlier 
in theorem \ref{thm:solution-sets-sas-plus-strips-f} (\autoref{sub:equivalence-sas-plus-strips}) and 
thus end up with the desired equivalence result.

The proof uses the finiteness and disjunctiveness of the solution sets for either problem to be 
able to equivalently transform the set cardinality over the union of sets of solutions with bounded 
lengths into a sum over the cardinality of the sets of solutions with bounded length. Moreover, 
since we know that for each SAS+ solution with a given length an equivalent STRIPS solution exists 
in the solution set of the transformed problem with the same length, both sets must have the same 
cardinality. 

Hence the cardinality of the  SAS+ solution set over all lengths up to a given upper bound \<^term>\<open>N\<close> 
has the same size as the solution set of the corresponding STRIPS problem over all length up to a 
given upper bound \<^term>\<open>N\<close>. \<close>

theorem
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "card (bounded_solution_set_sas_plus \<Psi> N) 
    = card (bounded_solution_set_strips (\<phi> \<Psi>) N)" 
  proof -
    let ?\<Pi> = "\<phi> \<Psi>"
      and ?R = "{0..N}" 
    \<comment> \<open> Due to the disjoint nature of the bounded solution sets for fixed plan length for different 
    lengths, we can sum the individual set cardinality to obtain the cardinality of the overall SAS+ 
    resp. STRIPS solution sets. \<close>
    have finite_R: "finite ?R" 
      by simp
    moreover {
      have "\<forall>k \<in> ?R. finite (bounded_solution_set_sas_plus' \<Psi> k)" 
        using sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_ii_a[OF 
            assms(1)]..
      moreover have "\<forall>j \<in> ?R. \<forall>k \<in> ?R. j \<noteq> k 
        \<longrightarrow> bounded_solution_set_sas_plus' \<Psi> j 
          \<inter> bounded_solution_set_sas_plus' \<Psi> k = {}"
        unfolding bounded_solution_set_sas_plus'_def 
        by blast
      (* TODO slow. *)
      ultimately have "card (bounded_solution_set_sas_plus \<Psi> N)
        = (\<Sum>k \<in> ?R. card (bounded_solution_set_sas_plus' \<Psi> k))"
        using card_UN_disjoint 
        by blast
    }
    moreover {
      have "\<forall>k \<in> ?R. finite (bounded_solution_set_strips' ?\<Pi> k)" 
        using sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_ii_b[OF 
            assms(1)]..
      moreover have "\<forall>j \<in> ?R. \<forall>k \<in> ?R. j \<noteq> k 
        \<longrightarrow> bounded_solution_set_strips' ?\<Pi> j 
          \<inter> bounded_solution_set_strips' ?\<Pi> k = {}"
        unfolding bounded_solution_set_strips'_def
        by blast
      (* TODO slow. *)
      ultimately have "card (bounded_solution_set_strips ?\<Pi> N)
        = (\<Sum>k \<in> ?R. card (bounded_solution_set_strips' ?\<Pi> k))"
        using card_UN_disjoint
        by blast
    }
    moreover {
      fix k
      have "card (bounded_solution_set_sas_plus' \<Psi> k)
        = card ((\<lambda>\<psi>. [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> \<psi>]) 
          ` bounded_solution_set_sas_plus' \<Psi> k)"
        using sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_b[OF assms]
          card_image[symmetric] 
        by blast
      hence "card (bounded_solution_set_sas_plus' \<Psi> k)
        = card (bounded_solution_set_strips' ?\<Pi> k)" 
        using sas_plus_formalism_and_induced_strips_formalism_are_equally_expressive_i_c[OF assms]
        by presburger
    } 
    ultimately show ?thesis
      by presburger
  qed


end

end