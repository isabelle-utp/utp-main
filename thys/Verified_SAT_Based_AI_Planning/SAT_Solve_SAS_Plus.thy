(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory SAT_Solve_SAS_Plus
  imports "SAS_Plus_STRIPS" 
    "SAT_Plan_Extensions"
begin
section "SAT-Solving of SAS+ Problems"


lemma sas_plus_problem_has_serial_solution_iff_i:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> \<Psi>) t"
  shows "is_serial_solution_for_problem \<Psi> [\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> concat (\<Phi>\<inverse> (\<phi> \<Psi>) \<A> t)]"
proof -
  let ?\<Pi> = "\<phi> \<Psi>"
    and ?\<pi>' = "concat (\<Phi>\<inverse> (\<phi> \<Psi>) \<A> t)"
  let ?\<psi> = "[\<phi>\<^sub>O\<inverse> \<Psi> op. op \<leftarrow> ?\<pi>']"
  {
    have "is_valid_problem_strips ?\<Pi>" 
      using is_valid_problem_sas_plus_then_strips_transformation_too[OF assms(1)]. 
    moreover have "STRIPS_Semantics.is_serial_solution_for_problem ?\<Pi> ?\<pi>'"
      using calculation serializable_encoding_decoded_plan_is_serializable[OF 
          _ assms(2)] 
      unfolding decode_plan_def 
      by simp
    ultimately have "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> ?\<psi>" 
      using assms(1) serial_strips_equivalent_to_serial_sas_plus 
      by blast
  }
  thus ?thesis
    using serial_strips_equivalent_to_serial_sas_plus[OF assms(1)]
    by blast
qed

lemma sas_plus_problem_has_serial_solution_iff_ii:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "is_serial_solution_for_problem \<Psi> \<psi>"
    and "h = length \<psi>"
  shows "\<exists>\<A>. (\<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> \<Psi>) h)" 
proof -
  let ?\<Pi> = "\<phi> \<Psi>" 
    and ?\<pi> = "\<phi>\<^sub>P \<Psi> (embed \<psi>)"
  let ?\<A> = "valuation_for_plan ?\<Pi> ?\<pi>" 
  let ?t = "length \<psi>" 
  (* TODO refactor *)
  have nb: "length \<psi> = length ?\<pi>"
    unfolding SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def 
      sasp_op_to_strips_def 
      sas_plus_parallel_plan_to_strips_parallel_plan_def
    by (induction \<psi>; auto)
  have "is_valid_problem_strips ?\<Pi>" 
    using assms(1) is_valid_problem_sas_plus_then_strips_transformation_too 
    by blast 
  moreover have "STRIPS_Semantics.is_parallel_solution_for_problem ?\<Pi> ?\<pi>" 
    using execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus[OF assms(1,2)] 
      strips_equivalent_to_sas_plus[OF assms(1)] 
    by blast
  moreover {
    fix k
    assume "k < length ?\<pi>" 
    moreover obtain ops' where "ops' = ?\<pi> ! k" 
      by simp
    moreover have "ops' \<in> set ?\<pi>" 
      using calculation nth_mem 
      by blast 
    moreover have "?\<pi> = [[\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]. ops \<leftarrow> embed \<psi>]" 
      unfolding SAS_Plus_STRIPS.sas_plus_parallel_plan_to_strips_parallel_plan_def 
        sasp_op_to_strips_def 
        sas_plus_parallel_plan_to_strips_parallel_plan_def
      ..
    moreover obtain ops 
      where "ops' = [\<phi>\<^sub>O \<Psi> op. op \<leftarrow> ops]"
        and "ops \<in> set (embed \<psi>)" 
      using calculation(3, 4) 
      by auto
    moreover have "ops \<in> { [op] | op. op \<in> set \<psi> }" 
      using calculation(6) set_of_embed_is
      by blast 
    moreover obtain op 
      where "ops = [op]" and "op \<in> set \<psi>" 
      using calculation(7)
      by blast
    ultimately have "are_all_operators_non_interfering (?\<pi> ! k)" 
      by fastforce
  }
  ultimately show ?thesis 
    using encode_problem_serializable_complete nb
    by (auto simp: assms(3))
qed

text \<open> To wrap-up our documentation of the Isabelle formalization, we take a look at the central 
theorem which combines all the previous theorem to show that SAS+ problems \<^term>\<open>\<Psi>\<close> can be solved 
using the planning as satisfiability framework.

A solution \<^term>\<open>\<psi>\<close> for the SAS+ problem \<^term>\<open>\<Psi>\<close> exists if and only if a model \<^term>\<open>\<A>\<close> and a 
hypothesized plan length \<^term>\<open>t\<close> exist s.t. 
@{text[display,indent=4] "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> \<Psi>) t"} 
for the serializable SATPlan encoding of the corresponding STRIPS problem \<^term>\<open>\<Phi>\<^sub>\<forall> (\<phi> \<Psi>) t\<close> exist. \<close>
theorem  sas_plus_problem_has_serial_solution_iff:
  assumes "is_valid_problem_sas_plus \<Psi>" 
  shows "(\<exists>\<psi>. is_serial_solution_for_problem \<Psi> \<psi>) \<longleftrightarrow> (\<exists>\<A> t. \<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> \<Psi>) t)" 
  using sas_plus_problem_has_serial_solution_iff_i[OF assms]
    sas_plus_problem_has_serial_solution_iff_ii[OF assms] 
  by blast


section \<open>Adding Noop actions to the SAS+ problem\<close>

text \<open>Here we add noop actions to the SAS+ problem to enable the SAT formula to be satisfiable if
      there are plans that are shorter than the given horizons.\<close>

definition "empty_sasp_action \<equiv> \<lparr>SAS_Plus_Representation.sas_plus_operator.precondition_of = [],
                                SAS_Plus_Representation.sas_plus_operator.effect_of = []\<rparr>"

lemma sasp_exec_noops: "execute_serial_plan_sas_plus s (replicate n empty_sasp_action) = s"
  by (induction n arbitrary: )
     (auto simp: empty_sasp_action_def STRIPS_Representation.is_operator_applicable_in_def
                 execute_operator_def)

definition
  "prob_with_noop \<Pi> \<equiv>
     \<lparr>SAS_Plus_Representation.sas_plus_problem.variables_of = SAS_Plus_Representation.sas_plus_problem.variables_of \<Pi>,
      SAS_Plus_Representation.sas_plus_problem.operators_of = empty_sasp_action # SAS_Plus_Representation.sas_plus_problem.operators_of \<Pi>, 
      SAS_Plus_Representation.sas_plus_problem.initial_of = SAS_Plus_Representation.sas_plus_problem.initial_of \<Pi>,
      SAS_Plus_Representation.sas_plus_problem.goal_of = SAS_Plus_Representation.sas_plus_problem.goal_of \<Pi>,
      SAS_Plus_Representation.sas_plus_problem.range_of = SAS_Plus_Representation.sas_plus_problem.range_of \<Pi>\<rparr>"

lemma sasp_noops_in_noop_problem: "set (replicate n empty_sasp_action) \<subseteq> set (SAS_Plus_Representation.sas_plus_problem.operators_of (prob_with_noop \<Pi>))"
  by (induction n) (auto simp: prob_with_noop_def)

lemma noops_complete:
  "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> \<pi> \<Longrightarrow>
     SAS_Plus_Semantics.is_serial_solution_for_problem (prob_with_noop \<Psi>) ((replicate n empty_sasp_action) @ \<pi>)"
  by(induction n)
    (auto simp: SAS_Plus_Semantics.is_serial_solution_for_problem_def insert list.pred_set
                    sasp_exec_noops prob_with_noop_def Let_def empty_sasp_action_def elem)

definition "rem_noops \<equiv> filter (\<lambda>op. op \<noteq> empty_sasp_action)"

lemma sasp_filter_empty_action:
  "execute_serial_plan_sas_plus s (rem_noops \<pi>s) = execute_serial_plan_sas_plus s \<pi>s"
  by (induction \<pi>s arbitrary: s)
     (auto simp: empty_sasp_action_def rem_noops_def)

lemma noops_sound:
  "SAS_Plus_Semantics.is_serial_solution_for_problem (prob_with_noop \<Psi>) \<pi>s \<Longrightarrow>
     SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> (rem_noops \<pi>s)"
  by(induction \<pi>s)
    (fastforce simp: SAS_Plus_Semantics.is_serial_solution_for_problem_def insert list.pred_set
                     prob_with_noop_def ListMem_iff rem_noops_def
                     sasp_filter_empty_action[unfolded empty_sasp_action_def rem_noops_def]
                     empty_sasp_action_def)+

lemma noops_valid: "is_valid_problem_sas_plus \<Psi> \<Longrightarrow> is_valid_problem_sas_plus (prob_with_noop \<Psi>)"
  by (auto simp: is_valid_problem_sas_plus_def prob_with_noop_def Let_def
                 empty_sasp_action_def is_valid_operator_sas_plus_def list.pred_set)

lemma sas_plus_problem_has_serial_solution_iff_i':
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop \<Psi>)) t"
  shows "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> 
           (rem_noops
                   (map (\<lambda>op. \<phi>\<^sub>O\<inverse> (prob_with_noop \<Psi>) op)
                        (concat (\<Phi>\<inverse> (\<phi> (prob_with_noop \<Psi>)) \<A> t))))"
  using assms noops_valid 
  by(force intro!: noops_sound sas_plus_problem_has_serial_solution_iff_i)

lemma sas_plus_problem_has_serial_solution_iff_ii':
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "SAS_Plus_Semantics.is_serial_solution_for_problem \<Psi> \<psi>"
    and "length \<psi> \<le> h"
  shows "\<exists>\<A>. (\<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop \<Psi>)) h)" 
  using assms
  by(fastforce 
       intro!: assms noops_valid noops_complete
               sas_plus_problem_has_serial_solution_iff_ii
                 [where \<psi> = "(replicate (h - length \<psi>) empty_sasp_action) @ \<psi>"] )
end


