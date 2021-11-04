(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory SAS_Plus_Semantics  
  imports "SAS_Plus_Representation" "List_Supplement"
    "Map_Supplement"
begin
section "SAS+ Semantics"


subsection "Serial Execution Semantics"

text \<open> Serial plan execution is implemented recursively just like in the STRIPS case. By and large, 
compared to definition \ref{isadef:plan-execution-strips}, we only substitute the operator 
applicability function with its SAS+ counterpart. \<close>

primrec execute_serial_plan_sas_plus
  where "execute_serial_plan_sas_plus s [] = s"
  | "execute_serial_plan_sas_plus s (op # ops) 
    = (if is_operator_applicable_in s op 
    then execute_serial_plan_sas_plus (execute_operator_sas_plus s op) ops
    else s)" 

text \<open> Similarly, serial SAS+ solutions are defined just like in STRIPS but based on the 
corresponding SAS+ definitions. \<close>

definition is_serial_solution_for_problem
  :: "('variable, 'domain) sas_plus_problem \<Rightarrow> ('variable, 'domain) sas_plus_plan \<Rightarrow> bool" 
  where "is_serial_solution_for_problem \<Psi> \<psi>
    \<equiv> let 
        I = sas_plus_problem.initial_of \<Psi>
        ; G = sas_plus_problem.goal_of \<Psi>
        ; ops = sas_plus_problem.operators_of \<Psi>
      in G \<subseteq>\<^sub>m execute_serial_plan_sas_plus I \<psi>
        \<and> list_all (\<lambda>op. ListMem op ops) \<psi>" 


context
begin

private lemma execute_operator_sas_plus_effect_i:
  assumes "is_operator_applicable_in s op"
    and "\<forall>(v, a) \<in> set (effect_of op). \<forall>(v', a') \<in> set (effect_of op).
      v \<noteq> v' \<or> a = a'"
    and"(v, a) \<in> set (effect_of op)"
  shows "(s \<then>\<^sub>+ op) v = Some a"
proof -
  let ?effect = "effect_of op"
  have "map_of ?effect v = Some a" 
    using map_of_constant_assignments_defined_if[OF assms(2, 3)] try0
    by blast
  thus ?thesis 
    unfolding execute_operator_sas_plus_def map_add_def
    by fastforce
qed
    
private lemma  execute_operator_sas_plus_effect_ii:
  assumes "is_operator_applicable_in s op"
    and "\<forall>(v', a') \<in> set (effect_of op). v' \<noteq> v"
  shows "(s \<then>\<^sub>+ op) v = s v"
proof -
  let ?effect = "effect_of op" 
  {
    have "v \<notin> fst ` set ?effect" 
      using assms(2)
      by fastforce
    then have "v \<notin> dom (map_of ?effect)"
      using dom_map_of_conv_image_fst[of ?effect]
      by argo
    hence "(s ++ map_of ?effect) v = s v" 
      using map_add_dom_app_simps(3)[of v "map_of ?effect" s]
      by blast
  }
  thus ?thesis 
    by fastforce
qed

text \<open> Given an operator \<^term>\<open>op\<close> that is applicable in a state \<^term>\<open>s\<close> and has a consistent set 
of effects (second assumption) we can now show that the successor state \<^term>\<open>s' \<equiv> s \<then>\<^sub>+ op\<close> 
has the following properties:
\begin{itemize}
  \item \<^term>\<open>s' v = Some a\<close> if \<^term>\<open>(v, a)\<close> exist in \<^term>\<open>set (effect_of op)\<close>; and,
  \item \<^term>\<open>s' v = s v\<close> if no \<^term>\<open>(v, a')\<close> exist in \<^term>\<open>set (effect_of op)\<close>.
\end{itemize} 
The second property is the case if the operator doesn't have an effect for a variable \<^term>\<open>v\<close>. \<close>

theorem execute_operator_sas_plus_effect:
  assumes "is_operator_applicable_in s op"
    and "\<forall>(v, a) \<in> set (effect_of op). 
      \<forall>(v', a') \<in> set (effect_of op). v \<noteq> v' \<or> a = a'"
  shows "(v, a) \<in> set (effect_of op) 
      \<longrightarrow> (s \<then>\<^sub>+ op) v = Some a"
    and "(\<forall>a. (v, a) \<notin> set (effect_of op)) 
      \<longrightarrow> (s \<then>\<^sub>+ op) v = s v"
proof -
  show "(v, a) \<in> set (effect_of op) 
    \<longrightarrow> (s \<then>\<^sub>+ op) v = Some a" 
    using execute_operator_sas_plus_effect_i[OF assms(1, 2)]
    by blast
next 
  show "(\<forall>a. (v, a) \<notin> set (effect_of op)) 
    \<longrightarrow> (s \<then>\<^sub>+ op) v = s v" 
    using execute_operator_sas_plus_effect_ii[OF assms(1)]
    by blast
qed

end


subsection "Parallel Execution Semantics"

\<comment> \<open> Define a type synonym for \emph{SAS+ parallel plans} and add a definition lifting SAS+
operator applicability to parallel plans. \<close>

type_synonym ('variable, 'domain) sas_plus_parallel_plan 
  = "('variable, 'domain) sas_plus_operator list list" 
    
definition are_all_operators_applicable_in
  :: "('variable, 'domain) state 
    \<Rightarrow> ('variable, 'domain) sas_plus_operator list
    \<Rightarrow> bool"
  where "are_all_operators_applicable_in s ops 
    \<equiv> list_all (is_operator_applicable_in s) ops"

definition are_operator_effects_consistent
  :: "('variable, 'domain) sas_plus_operator
    \<Rightarrow> ('variable, 'domain) sas_plus_operator
    \<Rightarrow> bool"
  where "are_operator_effects_consistent op op' 
    \<equiv> let 
        effect = effect_of op
        ; effect' = effect_of op'
      in list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') effect') effect"

definition are_all_operator_effects_consistent
  :: "('variable, 'domain) sas_plus_operator list
    \<Rightarrow> bool"
  where "are_all_operator_effects_consistent ops 
    \<equiv> list_all (\<lambda>op. list_all (are_operator_effects_consistent op) ops) ops"   

definition execute_parallel_operator_sas_plus
  :: "('variable, 'domain) state 
    \<Rightarrow> ('variable, 'domain) sas_plus_operator list 
    \<Rightarrow> ('variable, 'domain) state"
  where "execute_parallel_operator_sas_plus s ops 
    \<equiv> foldl (++) s (map (map_of \<circ> effect_of) ops)" 

text \<open> We now define parallel execution and parallel traces for SAS+ by lifting the tests for 
applicability and effect consistency to parallel SAS+ operators. The definitions are again very
similar to their STRIPS analogs (definitions \ref{isadef:parallel-plan-execution-strips} and 
\ref{isadef:parallel-plan-trace-strips}). \<close>

fun execute_parallel_plan_sas_plus
  :: "('variable, 'domain) state 
    \<Rightarrow> ('variable, 'domain) sas_plus_parallel_plan
    \<Rightarrow> ('variable, 'domain) state" 
  where "execute_parallel_plan_sas_plus s [] = s"
  | "execute_parallel_plan_sas_plus s (ops # opss) = (if 
      are_all_operators_applicable_in s ops 
      \<and> are_all_operator_effects_consistent ops
    then execute_parallel_plan_sas_plus 
      (execute_parallel_operator_sas_plus s ops) opss
    else s)"

fun trace_parallel_plan_sas_plus
  :: "('variable, 'domain) state  
    \<Rightarrow> ('variable, 'domain) sas_plus_parallel_plan 
    \<Rightarrow> ('variable, 'domain) state list"
  where "trace_parallel_plan_sas_plus s [] = [s]"
  | "trace_parallel_plan_sas_plus s (ops # opss) = s # (if 
      are_all_operators_applicable_in s ops 
      \<and> are_all_operator_effects_consistent ops
    then trace_parallel_plan_sas_plus 
      (execute_parallel_operator_sas_plus s ops) opss
    else [])"

text \<open> A plan \<^term>\<open>\<psi>\<close> is a solution for a SAS+ problem \<^term>\<open>\<Psi>\<close> if 
\begin{enumerate}
  \item starting from the initial state \<^term>\<open>\<Psi>\<close>, SAS+ parallel plan execution 
    reaches a state which satisfies the described goal state \<^term>\<open>sas_plus_problem.goal_of \<Psi>\<close>; and,
  \item all parallel operators \<^term>\<open>ops\<close> in the plan \<^term>\<open>\<psi>\<close> only consist of operators that
    are specified in the problem description.
\end{enumerate} \<close>
definition is_parallel_solution_for_problem 
  :: "('variable, 'domain) sas_plus_problem 
    \<Rightarrow> ('variable, 'domain) sas_plus_parallel_plan 
    \<Rightarrow> bool"
  where "is_parallel_solution_for_problem \<Psi> \<psi> 
    \<equiv> let 
        G = sas_plus_problem.goal_of \<Psi>
        ; I = sas_plus_problem.initial_of \<Psi>
        ; Ops = sas_plus_problem.operators_of \<Psi>
      in G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I \<psi>
      \<and> list_all (\<lambda>ops. list_all (\<lambda>op. ListMem op Ops) ops) \<psi>" 

context 
begin

lemma execute_parallel_operator_sas_plus_cons[simp]:
  "execute_parallel_operator_sas_plus s (op # ops)
    = execute_parallel_operator_sas_plus (s ++  map_of (effect_of op)) ops" 
  unfolding execute_parallel_operator_sas_plus_def
  by simp

text \<open>The following lemmas show the properties of SAS+ parallel plan execution traces. 
The results are analogous to those for STRIPS. So, let \<^term>\<open>\<tau> \<equiv> trace_parallel_plan_sas_plus I \<psi>\<close> 
be a trace of a parallel SAS+ plan \<^term>\<open>\<psi>\<close> with initial state \<^term>\<open>I\<close>, then
\begin{itemize}
  \item the head of the trace \<^term>\<open>\<tau> ! 0\<close> is the initial state of the 
problem (lemma \ref{isathm:head-parallel-plan-trace-sas-plus}); moreover,
  \item for all but the last element of the trace---i.e. elements with index 
\<^term>\<open>k < length \<tau> - 1\<close>---the parallel operator \<^term>\<open>\<pi> ! k\<close> is executable (lemma 
\ref{isathm:parallel-plan-trace-operator-execution-conditions-sas-plus}); and 
finally, 
  \item for all \<^term>\<open>k < length \<tau>\<close>, the parallel execution of the plan prefix \<^term>\<open>take k \<psi>\<close> with 
initial state \<^term>\<open>I\<close> equals the \<^term>\<open>k\<close>-th element of the trace \<^term>\<open>\<tau> ! k\<close> (lemma 
\ref{isathm:parallel-trace-plan-prefixes-sas-plus}).
\end{itemize} \<close>

(* TODO? Make invisible? *)
lemma trace_parallel_plan_sas_plus_head_is_initial_state: 
  "trace_parallel_plan_sas_plus I \<psi> ! 0 = I"
proof (cases \<psi>)
  case (Cons a list)
  then show ?thesis 
    by (cases "are_all_operators_applicable_in I a \<and> are_all_operator_effects_consistent a"; 
        simp+)
qed simp

lemma trace_parallel_plan_sas_plus_length_gt_one_if:
  assumes "k < length (trace_parallel_plan_sas_plus I \<psi>) - 1"  
  shows "1 < length (trace_parallel_plan_sas_plus I \<psi>)" 
  using assms
  by linarith
    
lemma length_trace_parallel_plan_sas_plus_lte_length_plan_plus_one:
  shows "length (trace_parallel_plan_sas_plus I \<psi>) \<le> length \<psi> + 1" 
proof (induction \<psi> arbitrary: I)
  case (Cons a \<psi>)
  then show ?case 
    proof (cases "are_all_operators_applicable_in I a \<and> are_all_operator_effects_consistent a")
      case True
      let ?I' = "execute_parallel_operator_sas_plus I a" 
      {
        have "trace_parallel_plan_sas_plus I (a # \<psi>) = I # trace_parallel_plan_sas_plus ?I' \<psi>" 
          using True
          by auto
        then have "length (trace_parallel_plan_sas_plus I (a # \<psi>)) 
          = length (trace_parallel_plan_sas_plus ?I' \<psi>) + 1"
          by simp
        moreover have "length (trace_parallel_plan_sas_plus ?I' \<psi>) \<le> length \<psi> + 1"
          using Cons.IH[of ?I']
          by blast
        ultimately have "length (trace_parallel_plan_sas_plus I (a # \<psi>)) \<le> length (a # \<psi>) + 1"
          by simp
      }
      thus ?thesis
        by blast
    qed auto
qed simp
    
lemma plan_is_at_least_singleton_plan_if_trace_has_at_least_two_elements:
  assumes "k < length (trace_parallel_plan_sas_plus I \<psi>) - 1" 
  obtains ops \<psi>' where "\<psi> = ops # \<psi>'" 
proof -
  let ?\<tau> = "trace_parallel_plan_sas_plus I \<psi>"
  have "length ?\<tau> \<le> length \<psi> + 1" 
    using length_trace_parallel_plan_sas_plus_lte_length_plan_plus_one
    by fast
  then have "0 < length \<psi>"
    using trace_parallel_plan_sas_plus_length_gt_one_if[OF assms]
    by fastforce
  then obtain k' where "length \<psi> = Suc k'"
    using gr0_implies_Suc
    by meson
  thus ?thesis using that  
    using length_Suc_conv[of \<psi> k']
    by blast
qed

lemma trace_parallel_plan_sas_plus_step_implies_operator_execution_condition_holds:
  assumes "k < length (trace_parallel_plan_sas_plus I \<pi>) - 1"
  shows "are_all_operators_applicable_in (trace_parallel_plan_sas_plus I \<pi> ! k) (\<pi> ! k)
      \<and> are_all_operator_effects_consistent (\<pi> ! k)"
using assms 
proof  (induction "\<pi>" arbitrary: I k)
  \<comment> \<open> NOTE Base case yields contradiction with assumption and can be left to automation. \<close>
  case (Cons a \<pi>)
  then show ?case 
    proof (cases "are_all_operators_applicable_in I a \<and> are_all_operator_effects_consistent a")
      case True
      have trace_parallel_plan_sas_plus_cons: "trace_parallel_plan_sas_plus I (a # \<pi>) 
        = I # trace_parallel_plan_sas_plus (execute_parallel_operator_sas_plus I a) \<pi>"
        using True
        by simp  
      then show ?thesis 
      proof (cases "k")
        case 0
        have "trace_parallel_plan_sas_plus I (a # \<pi>) ! 0 = I" 
          using trace_parallel_plan_sas_plus_cons
          by simp
        moreover have "(a # \<pi>) ! 0 = a"
          by simp
        ultimately show ?thesis 
          using True 0
          by presburger
      next
        case (Suc k')
        have "trace_parallel_plan_sas_plus I (a # \<pi>) ! Suc k' 
          = trace_parallel_plan_sas_plus (execute_parallel_operator_sas_plus I a) \<pi> ! k'" 
          using trace_parallel_plan_sas_plus_cons
          by simp
        moreover have "(a # \<pi>) ! Suc k' = \<pi> ! k'"
          by simp
        moreover {
          let ?I' = "execute_parallel_operator_sas_plus I a"
          have "length (trace_parallel_plan_sas_plus I (a # \<pi>)) 
            = 1 + length (trace_parallel_plan_sas_plus ?I' \<pi>)" 
            using trace_parallel_plan_sas_plus_cons 
            by auto
          then have "k' < length (trace_parallel_plan_sas_plus ?I' \<pi>) - 1" 
            using Cons.prems Suc
            unfolding Suc_eq_plus1
            by fastforce
          hence "are_all_operators_applicable_in
            (trace_parallel_plan_sas_plus (execute_parallel_operator_sas_plus I a) \<pi> ! k')
            (\<pi> ! k') 
          \<and> are_all_operator_effects_consistent (\<pi> ! k')"
            using Cons.IH[of k' "execute_parallel_operator_sas_plus I a"] Cons.prems Suc trace_parallel_plan_sas_plus_cons
            by simp
        }
        ultimately show ?thesis 
          using Suc
          by argo
      qed 
    next
      case False
      then have "trace_parallel_plan_sas_plus I (a # \<pi>) = [I]"
        by force
      then have "length (trace_parallel_plan_sas_plus I (a # \<pi>)) - 1 = 0" 
        by simp
      \<comment> \<open> NOTE Thesis follows from contradiction with assumption. \<close>
      then show ?thesis 
        using Cons.prems
        by force 
    qed
qed auto

lemma trace_parallel_plan_sas_plus_prefix:
  assumes "k < length (trace_parallel_plan_sas_plus I \<psi>)"
  shows "trace_parallel_plan_sas_plus I \<psi> ! k = execute_parallel_plan_sas_plus I (take k \<psi>)" 
  using assms
proof  (induction \<psi> arbitrary: I k)
  case (Cons a \<psi>)
  then show ?case 
    proof (cases "are_all_operators_applicable_in I a \<and> are_all_operator_effects_consistent a")
      case True
      let ?\<sigma> = "trace_parallel_plan_sas_plus I (a # \<psi>)"
        and ?I' = "execute_parallel_operator_sas_plus I a" 
      have \<sigma>_equals: "?\<sigma> = I # trace_parallel_plan_sas_plus ?I' \<psi>" 
        using True
        by auto
      then show ?thesis 
        proof (cases "k = 0")
          case False
          obtain k' where k_is_suc_of_k': "k = Suc k'" 
            using not0_implies_Suc[OF False]
            by blast
          then have "execute_parallel_plan_sas_plus I (take k (a # \<psi>))
            = execute_parallel_plan_sas_plus ?I' (take k' \<psi>)" 
            using True
            by simp
          moreover have "trace_parallel_plan_sas_plus I (a # \<psi>) ! k 
            = trace_parallel_plan_sas_plus ?I' \<psi> ! k'" 
            using \<sigma>_equals k_is_suc_of_k'
            by simp
          moreover {
            have "k' < length (trace_parallel_plan_sas_plus ?I' \<psi>)"
              using Cons.prems \<sigma>_equals k_is_suc_of_k'
              by force
            hence "trace_parallel_plan_sas_plus ?I' \<psi> ! k' 
              = execute_parallel_plan_sas_plus ?I' (take k' \<psi>)" 
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
        then have "trace_parallel_plan_sas_plus I (a # \<psi>) = [I]"
          using operator_precondition_violated
          by force
        moreover have "execute_parallel_plan_sas_plus I (take k (a # \<psi>)) = I" 
          using Cons.prems operator_precondition_violated 
          by force
        ultimately show ?thesis 
          using Cons.prems nth_Cons_0
          by auto
      qed simp
    qed
qed simp

lemma trace_parallel_plan_sas_plus_step_effect_is:
  assumes "k < length (trace_parallel_plan_sas_plus I \<psi>) - 1"
  shows "trace_parallel_plan_sas_plus I \<psi> ! Suc k 
    = execute_parallel_operator_sas_plus (trace_parallel_plan_sas_plus I \<psi> ! k) (\<psi> ! k)" 
proof -
  let ?\<tau> = "trace_parallel_plan_sas_plus I \<psi>"
  let ?\<tau>\<^sub>k = "?\<tau> ! k"
    and ?\<tau>\<^sub>k' = "?\<tau> ! Suc k"
  \<comment> \<open> NOTE rewrite the goal using the subplan formulation to be able. This allows us to make the 
    initial state arbitrary. \<close>
  {
    have suc_k_lt_length_\<tau>: "Suc k < length ?\<tau>" 
      using assms 
      by linarith
    hence "?\<tau>\<^sub>k' = execute_parallel_plan_sas_plus I (take (Suc k) \<psi>)"
      using trace_parallel_plan_sas_plus_prefix[of "Suc k"]
      by blast
  } note rewrite_goal = this
  have "execute_parallel_plan_sas_plus I (take (Suc k) \<psi>) 
    = execute_parallel_operator_sas_plus (trace_parallel_plan_sas_plus I \<psi> ! k) (\<psi> ! k)" 
    using assms
    proof (induction k arbitrary: I \<psi>)
      case 0
      obtain ops \<psi>' where \<psi>_is: "\<psi> = ops # \<psi>'" 
        using plan_is_at_least_singleton_plan_if_trace_has_at_least_two_elements[OF "0.prems"] 
        by force
      {
        have "take (Suc 0) \<psi>  = [\<psi> ! 0]" 
          using \<psi>_is
          by simp
        hence "execute_parallel_plan_sas_plus I (take (Suc 0) \<psi>) 
          = execute_parallel_plan_sas_plus I [\<psi> ! 0]"
          by argo
      }
      moreover {
        have "trace_parallel_plan_sas_plus I \<psi> ! 0 = I" 
          using trace_parallel_plan_sas_plus_head_is_initial_state.
        moreover {
          have "are_all_operators_applicable_in I (\<psi> ! 0)" 
            and "are_all_operator_effects_consistent (\<psi> ! 0)" 
            using trace_parallel_plan_sas_plus_step_implies_operator_execution_condition_holds[OF
                "0.prems"] calculation 
            by argo+
          then have "execute_parallel_plan_sas_plus I [\<psi> ! 0] 
            = execute_parallel_operator_sas_plus I (\<psi> ! 0)"
            by simp
        }
        ultimately have "execute_parallel_operator_sas_plus (trace_parallel_plan_sas_plus I \<psi> ! 0) 
            (\<psi> ! 0)
          = execute_parallel_plan_sas_plus I [\<psi> ! 0]"
          by argo
      }
      ultimately show ?case 
        by argo
    next
      case (Suc k)
      obtain ops \<psi>' where \<psi>_is: "\<psi> = ops # \<psi>'" 
        using plan_is_at_least_singleton_plan_if_trace_has_at_least_two_elements[OF Suc.prems]
        by blast
      let ?I' = "execute_parallel_operator_sas_plus I ops"
      have "execute_parallel_plan_sas_plus I (take (Suc (Suc k)) \<psi>)
        = execute_parallel_plan_sas_plus ?I' (take (Suc k) \<psi>')" 
        using Suc.prems \<psi>_is
        by fastforce
      moreover {
        thm Suc.IH[of ]
        have "length (trace_parallel_plan_sas_plus I \<psi>)
          = 1 + length (trace_parallel_plan_sas_plus ?I' \<psi>')" 
          using \<psi>_is Suc.prems
          by fastforce
        moreover have "k < length (trace_parallel_plan_sas_plus ?I' \<psi>') - 1"
          using Suc.prems calculation
          by fastforce
        ultimately have "execute_parallel_plan_sas_plus ?I' (take (Suc k) \<psi>') =
          execute_parallel_operator_sas_plus (trace_parallel_plan_sas_plus ?I' \<psi>' ! k) 
          (\<psi>' ! k)"
          using Suc.IH[of ?I' \<psi>']
          by blast          
      }
      moreover have "execute_parallel_operator_sas_plus (trace_parallel_plan_sas_plus ?I' \<psi>' ! k) 
          (\<psi>' ! k)
        = execute_parallel_operator_sas_plus (trace_parallel_plan_sas_plus I \<psi> ! Suc k)
          (\<psi> ! Suc k)" 
        using Suc.prems \<psi>_is
        by auto
      ultimately show ?case
        by argo 
    qed 
  thus ?thesis 
    using rewrite_goal
    by argo
qed

text \<open> Finally, we obtain the result corresponding to lemma 
\ref{isathm:parallel-solution-trace-strips} in the SAS+ case: it is equivalent to say that parallel 
SAS+ execution reaches the problem's goal state and that the last element of the corresponding 
trace satisfies the goal state. \<close>
lemma  execute_parallel_plan_sas_plus_reaches_goal_iff_goal_is_last_element_of_trace:
  "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I \<psi> 
    \<longleftrightarrow> G \<subseteq>\<^sub>m last (trace_parallel_plan_sas_plus I \<psi>)" 
proof   -
  let ?\<tau> = "trace_parallel_plan_sas_plus I \<psi>" 
  show ?thesis 
  proof (rule iffI)
    assume "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I \<psi>"
    thus "G \<subseteq>\<^sub>m last ?\<tau>" 
      proof (induction \<psi> arbitrary: I)
        \<comment> \<open> NOTE Base case follows from simplification. \<close>
        case (Cons ops \<psi>)
        show ?case
          proof (cases "are_all_operators_applicable_in I ops 
            \<and> are_all_operator_effects_consistent ops")
            case True
            let ?s = "execute_parallel_operator_sas_plus I ops"
            {
              have "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ?s \<psi>"
                using True Cons.prems
                by simp
              hence "G \<subseteq>\<^sub>m last (trace_parallel_plan_sas_plus ?s \<psi>)" 
                using Cons.IH
                by auto
            }
            moreover {
              have "trace_parallel_plan_sas_plus I (ops # \<psi>) 
                = I # trace_parallel_plan_sas_plus ?s \<psi>" 
                using True 
                by simp
              moreover have "trace_parallel_plan_sas_plus ?s \<psi> \<noteq> []" 
                using trace_parallel_plan_sas_plus.elims
                by blast 
              ultimately have "last (trace_parallel_plan_sas_plus I (ops # \<psi>)) 
                = last (trace_parallel_plan_sas_plus ?s \<psi>)" 
                using last_ConsR
                  by simp
            }
            ultimately show ?thesis 
              by argo
          next
            case False
            then have "G \<subseteq>\<^sub>m I"
              using Cons.prems 
              by force
            thus ?thesis
              using False
              by force
          qed
      qed force
  next 
    assume "G \<subseteq>\<^sub>m last ?\<tau>"
    thus "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I \<psi>" 
      proof (induction \<psi> arbitrary: I)
        case (Cons ops \<psi>)
        thus ?case
          proof (cases "are_all_operators_applicable_in I ops
            \<and> are_all_operator_effects_consistent ops")
            case True
            let ?s = "execute_parallel_operator_sas_plus I ops"
            {
              have "trace_parallel_plan_sas_plus I (ops # \<psi>) 
                = I # trace_parallel_plan_sas_plus ?s \<psi>" 
                using True 
                by simp
              moreover have "trace_parallel_plan_sas_plus ?s \<psi> \<noteq> []" 
                using trace_parallel_plan_sas_plus.elims
                by blast 
              ultimately have "last (trace_parallel_plan_sas_plus I (ops # \<psi>)) 
                = last (trace_parallel_plan_sas_plus ?s \<psi>)" 
                using last_ConsR
                by simp
              hence "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ?s \<psi>"
                using Cons.IH[of ?s] Cons.prems 
                by argo
            }
            moreover have "execute_parallel_plan_sas_plus I (ops # \<psi>) 
                = execute_parallel_plan_sas_plus ?s \<psi>" 
              using True
              by force
            ultimately show ?thesis 
              by argo
          next
            case False
            have "G \<subseteq>\<^sub>m I"
              using Cons.prems False 
              by simp
            thus ?thesis
              using False
              by force
          qed
      qed simp
  qed
qed

lemma is_parallel_solution_for_problem_plan_operator_set:
  (* TODO refactor move + make visible? *)
  fixes \<Psi> :: "('v, 'd) sas_plus_problem"
  assumes "is_parallel_solution_for_problem \<Psi> \<psi>" 
  shows "\<forall>ops \<in> set \<psi>. \<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
  using assms
  unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff operators_of_def 
  by presburger

end


subsection "Serializable Parallel Plans"

text \<open> Again we want to establish conditions for the serializability of plans. Let
\<^term>\<open>\<Psi>\<close> be a SAS+ problem instance and let \<^term>\<open>\<psi>\<close> be a serial solution. We obtain the following 
two important results, namely that
\begin{enumerate}
  \item the embedding \<^term>\<open>embed \<psi>\<close> of \<^term>\<open>\<psi>\<close> is a parallel solution for \<^term>\<open>\<Psi>\<close> 
(lemma \ref{isathm:serial-sas-plus-embedding}); and conversely that,
  \item a parallel solution to \<^term>\<open>\<Psi>\<close> that has the form of an embedded serial plan can be 
concatenated to obtain a serial solution (lemma 
\ref{isathm:embedded-serial-solution-flattening-sas-plus}).
\end{enumerate} \<close>


context
begin

(* TODO refactor *)
lemma execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_i:
  assumes "is_operator_applicable_in s op"
    "are_operator_effects_consistent op op" 
  shows "s \<then>\<^sub>+ op = execute_parallel_operator_sas_plus s [op]"
proof -
  have "are_all_operators_applicable_in s [op]"
    unfolding are_all_operators_applicable_in_def 
       SAS_Plus_Representation.execute_operator_sas_plus_def
      is_operator_applicable_in_def SAS_Plus_Representation.is_operator_applicable_in_def
      list_all_iff  
    using assms(1) 
    by fastforce
  moreover have "are_all_operator_effects_consistent [op]"
    unfolding are_all_operator_effects_consistent_def list_all_iff
    using assms(2)
    by fastforce
  ultimately show ?thesis
    unfolding execute_parallel_operator_sas_plus_def execute_operator_sas_plus_def
    by simp
qed

lemma execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_ii:
  fixes I :: "('variable, 'domain) state"
  assumes "\<forall>op \<in> set \<psi>. are_operator_effects_consistent op op"
    and "G \<subseteq>\<^sub>m execute_serial_plan_sas_plus I \<psi>" 
  shows "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I (embed \<psi>)" 
  using assms
proof (induction \<psi> arbitrary: I)
  case (Cons op \<psi>)
  show ?case 
    proof (cases "are_all_operators_applicable_in I [op]")
      case True
      let ?J = "execute_operator_sas_plus I op" 
        let ?J' = "execute_parallel_operator_sas_plus I [op]" 
      have "SAS_Plus_Representation.is_operator_applicable_in I op"
        using True 
        unfolding are_all_operators_applicable_in_def list_all_iff
        by force
      moreover have "G \<subseteq>\<^sub>m execute_serial_plan_sas_plus ?J \<psi>" 
        using Cons.prems(2) calculation(1) 
        by simp
      moreover have "are_all_operator_effects_consistent [op]" 
        unfolding are_all_operator_effects_consistent_def list_all_iff Let_def
        using Cons.prems(1)
        by simp
      moreover have "execute_parallel_plan_sas_plus I ([op] # embed \<psi>) 
        = execute_parallel_plan_sas_plus ?J' (embed \<psi>)"
        using True calculation(3) 
        by simp
      moreover {
        have "is_operator_applicable_in I op" 
          "are_operator_effects_consistent op op" 
          using True Cons.prems(1)
          unfolding are_all_operators_applicable_in_def 
            SAS_Plus_Representation.is_operator_applicable_in_def list_all_iff 
          by fastforce+
        hence "?J = ?J'" 
          using execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_i
            calculation(1) 
          by blast
      }
      ultimately show ?thesis 
        using Cons.IH[of ?J] Cons.prems(1)
        by simp
    next
      case False
      moreover have "\<not>is_operator_applicable_in I op" 
        using calculation 
        unfolding are_all_operators_applicable_in_def 
          SAS_Plus_Representation.is_operator_applicable_in_def list_all_iff 
        by fastforce
      moreover have "G \<subseteq>\<^sub>m I" 
        using Cons.prems(2) calculation(2)
        unfolding is_operator_applicable_in_def
        by simp
      moreover have "execute_parallel_plan_sas_plus I ([op] # embed \<psi>) = I" 
        using calculation(1)
        by fastforce
      ultimately show ?thesis
        by force
    qed
  qed simp

lemma execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_iii:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "is_serial_solution_for_problem \<Psi> \<psi>"
    and "op \<in> set \<psi>"
  shows "are_operator_effects_consistent op op"
proof -
  have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
    using assms(2) assms(3)
    unfolding is_serial_solution_for_problem_def Let_def list_all_iff ListMem_iff 
    by fastforce
  then have "is_valid_operator_sas_plus \<Psi> op" 
    using is_valid_problem_sas_plus_then(2) assms(1, 3) 
    by auto
  thus ?thesis
    unfolding are_operator_effects_consistent_def Let_def list_all_iff ListMem_iff
    using is_valid_operator_sas_plus_then(6)
    by fast
qed

lemma execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_iv:
  fixes \<Psi> :: "('v, 'd) sas_plus_problem"
  assumes "\<forall>op \<in> set \<psi>. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
  shows "\<forall>ops \<in> set (embed \<psi>). \<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
proof -
  let ?\<psi>' = "embed \<psi>"
  have nb: "set ?\<psi>' = { [op] | op. op \<in> set \<psi> }" 
    by (induction \<psi>; force)
  {
    fix ops
    assume "ops \<in> set ?\<psi>'"
    moreover obtain op where "ops = [op]" and "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
      using assms(1) nb calculation 
      by blast
    ultimately have "\<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
      by fastforce
  }
  thus ?thesis..
qed

theorem execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus:
  assumes "is_valid_problem_sas_plus \<Psi>" 
    and "is_serial_solution_for_problem \<Psi> \<psi>" 
  shows "is_parallel_solution_for_problem \<Psi> (embed \<psi>)" 
proof  -
  let ?ops = "sas_plus_problem.operators_of \<Psi>" 
    and ?\<psi>' = "embed \<psi>" 
  {
    thm execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_ii[OF]
    have "(\<Psi>)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_serial_plan_sas_plus ((\<Psi>)\<^sub>I\<^sub>+) \<psi>"
      using assms(2) 
      unfolding is_serial_solution_for_problem_def Let_def
      by simp
    moreover have "\<forall>op \<in> set \<psi>. are_operator_effects_consistent op op" 
      using execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_iii[OF assms]..
    ultimately have "(\<Psi>)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ((\<Psi>)\<^sub>I\<^sub>+) ?\<psi>'" 
      using execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_ii
      by blast
  }
  moreover {
    have "\<forall>op \<in> set \<psi>. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
      using assms(2) 
      unfolding is_serial_solution_for_problem_def Let_def list_all_iff ListMem_iff
      by fastforce
    hence "\<forall>ops \<in> set ?\<psi>'. \<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
      using execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_iv
      by blast
  }
  ultimately show ?thesis
    unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff Let_def goal_of_def 
      initial_of_def
    by fastforce
qed

lemma flattening_lemma_i:
  fixes \<Psi> :: "('v, 'd) sas_plus_problem"
  assumes "\<forall>ops \<in> set \<pi>. \<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
  shows "\<forall>op \<in> set (concat \<pi>). op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
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
    ultimately have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
      using assms
      by blast
  }
  thus ?thesis..
qed

lemma flattening_lemma_ii:
  fixes I :: "('variable, 'domain) state"
  assumes "\<forall>ops \<in> set \<psi>. \<exists>op. ops = [op] \<and> is_valid_operator_sas_plus \<Psi> op " 
    and "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus I \<psi>" 
  shows "G \<subseteq>\<^sub>m execute_serial_plan_sas_plus I (concat \<psi>)"
proof -
  show ?thesis 
    using assms
    proof (induction \<psi> arbitrary: I)
      case (Cons ops \<psi>)
      obtain op where ops_is: "ops = [op]" and is_valid_op: "is_valid_operator_sas_plus \<Psi> op" 
        using Cons.prems(1)
        by auto
      then show ?case 
        proof (cases "are_all_operators_applicable_in I ops")
          case True
          let ?J = "execute_parallel_operator_sas_plus I [op]" 
            and ?J' = "execute_operator_sas_plus I op" 
          have nb\<^sub>1: "is_operator_applicable_in I op" 
            using True ops_is
            unfolding are_all_operators_applicable_in_def is_operator_applicable_in_def 
              list_all_iff 
            by force
          have nb\<^sub>2: "are_operator_effects_consistent op op" 
            unfolding are_operator_effects_consistent_def list_all_iff Let_def 
            using is_valid_operator_sas_plus_then(6)[OF is_valid_op]
            by blast
          have "are_all_operator_effects_consistent ops" 
            using ops_is 
            unfolding are_all_operator_effects_consistent_def list_all_iff
            using nb\<^sub>2
            by force
          moreover have "G \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ?J \<psi>"
            using Cons.prems(2) True calculation ops_is
            by fastforce
          moreover have "execute_serial_plan_sas_plus I (concat (ops # \<psi>)) 
              = execute_serial_plan_sas_plus ?J' (concat \<psi>)"
              using ops_is nb\<^sub>1 is_operator_applicable_in_def
              by simp
          moreover have "?J = ?J'" 
            using execute_serial_plan_sas_plus_is_execute_parallel_plan_sas_plus_i[OF nb\<^sub>1 nb\<^sub>2]
            by simp
          ultimately show ?thesis
            using Cons.IH[of ?J] Cons.prems(1)
            by force
        next
          case False
          moreover have "G \<subseteq>\<^sub>m I" 
            using Cons.prems(2) calculation
            by fastforce
          moreover {
            have "\<not>is_operator_applicable_in I op" 
              using False ops_is
              unfolding are_all_operators_applicable_in_def 
                is_operator_applicable_in_def list_all_iff
              by force
            moreover have "execute_serial_plan_sas_plus I (concat (ops # \<psi>)) 
              = execute_serial_plan_sas_plus I (op # concat \<psi>)" 
              using ops_is 
              by force
            ultimately have "execute_serial_plan_sas_plus I (concat (ops # \<psi>)) = I"
              using False 
              unfolding is_operator_applicable_in_def
              by fastforce
          }
          ultimately show ?thesis
            by argo
        qed  
    qed force
qed

lemma flattening_lemma:
  assumes "is_valid_problem_sas_plus \<Psi>"
    and "\<forall>ops \<in> set \<psi>. \<exists>op. ops = [op]" 
    and "is_parallel_solution_for_problem \<Psi> \<psi>"
  shows "is_serial_solution_for_problem \<Psi> (concat \<psi>)"
proof  -
  let ?\<psi>' = "concat \<psi>" 
  {
    have "\<forall>ops \<in> set \<psi>. \<forall>op \<in> set ops. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
      using assms(3)
      unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff
      by force
    hence "\<forall>op \<in> set ?\<psi>'. op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)"
      using flattening_lemma_i
      by blast
  }
  moreover {
    {
      fix ops
      assume "ops \<in> set \<psi>" 
      moreover obtain op where "ops = [op]" 
        using assms(2) calculation
        by blast
      moreover have "op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+)" 
        using assms(3) calculation
        unfolding is_parallel_solution_for_problem_def list_all_iff ListMem_iff 
        by force
      moreover have "is_valid_operator_sas_plus \<Psi> op" 
        using assms(1) calculation(3)
        unfolding is_valid_problem_sas_plus_def Let_def list_all_iff 
          ListMem_iff
        by simp
      ultimately have "\<exists>op. ops = [op] \<and> is_valid_operator_sas_plus \<Psi> op"
        by blast
    }
    moreover have "(\<Psi>)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_parallel_plan_sas_plus ((\<Psi>)\<^sub>I\<^sub>+) \<psi>" 
      using assms(3) 
      unfolding is_parallel_solution_for_problem_def
      by fastforce
    ultimately have "(\<Psi>)\<^sub>G\<^sub>+ \<subseteq>\<^sub>m execute_serial_plan_sas_plus ((\<Psi>)\<^sub>I\<^sub>+) ?\<psi>'" 
      using flattening_lemma_ii
      by blast
  }
  ultimately show "is_serial_solution_for_problem \<Psi> ?\<psi>'" 
    unfolding is_serial_solution_for_problem_def list_all_iff ListMem_iff
    by fastforce
qed
end

subsection "Auxiliary lemmata on SAS+"


context
begin

\<comment> \<open> Relate the locale definition \<open>range_of\<close> with its corresponding implementation for valid 
operators and given an effect \<open>(v, a)\<close>. \<close>
lemma is_valid_operator_sas_plus_then_range_of_sas_plus_op_is_set_range_of_op:
  assumes "is_valid_operator_sas_plus \<Psi> op"
    and "(v, a) \<in> set (precondition_of op) \<or> (v, a) \<in> set (effect_of op)"
  shows "(\<R>\<^sub>+ \<Psi> v) = set (the (sas_plus_problem.range_of \<Psi> v))" 
proof -
  consider (A) "(v, a) \<in> set (precondition_of op)"
    | (B)  "(v, a) \<in> set (effect_of op)"
    using assms(2)..
  thus ?thesis 
    proof (cases)
      case A
      then have "(\<R>\<^sub>+ \<Psi> v) \<noteq> {}" and "a \<in> \<R>\<^sub>+ \<Psi> v" 
        using assms 
        unfolding range_of_def
        using is_valid_operator_sas_plus_then(2)
        by fast+
      thus ?thesis
        unfolding range_of'_def option.case_eq_if
        by auto
    next
      case B
      then have "(\<R>\<^sub>+ \<Psi> v) \<noteq> {}" and "a \<in> \<R>\<^sub>+ \<Psi> v" 
        using assms 
        unfolding range_of_def
        using is_valid_operator_sas_plus_then(4)
        by fast+
      thus ?thesis
        unfolding range_of'_def option.case_eq_if
        by auto
    qed  
qed 

lemma set_the_range_of_is_range_of_sas_plus_if:
  fixes \<Psi> :: "('v, 'd) sas_plus_problem"
  assumes "is_valid_problem_sas_plus \<Psi>"
    "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
  shows "set (the (sas_plus_problem.range_of \<Psi> v)) = \<R>\<^sub>+ \<Psi> v"
proof-
  have "v \<in> set((\<Psi>)\<^sub>\<V>\<^sub>+)" 
    using assms(2)
    unfolding variables_of_def.
  moreover have "(\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    using assms(1) calculation is_valid_problem_sas_plus_then(1)
    by blast
  moreover have "sas_plus_problem.range_of \<Psi> v \<noteq> None" 
    and "sas_plus_problem.range_of \<Psi> v \<noteq> Some []"
    using calculation(2) range_of_not_empty
    unfolding range_of_def 
    by fast+
  ultimately show ?thesis
    unfolding option.case_eq_if range_of'_def
    by force
qed

lemma sublocale_sas_plus_finite_domain_representation_ii:
  fixes \<Psi>::"('v,'d) sas_plus_problem"
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    and "\<forall>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and "dom ((\<Psi>)\<^sub>I\<^sub>+) = set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+). the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    and "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+). the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
  using is_valid_problem_sas_plus_then[OF assms]
  by auto

end

end