(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory SAS_Plus_Representation
imports State_Variable_Representation
begin

section "SAS+ Representation"

text \<open> We now continue by defining a concrete implementation of SAS+.\<close>

text \<open> SAS+ operators and SAS+ problems again use records. In contrast to STRIPS, the operator 
effect is contracted into a single list however since we now potentially deal with more than two 
possible values for each problem variable. \<close>

record  ('variable, 'domain) sas_plus_operator = 
  precondition_of :: "('variable, 'domain) assignment list" 
  effect_of :: "('variable, 'domain) assignment list" 

record  ('variable, 'domain) sas_plus_problem =
  variables_of :: "'variable list" ("(_\<^sub>\<V>\<^sub>+)" [1000] 999)
  operators_of :: "('variable, 'domain) sas_plus_operator list" ("(_\<^sub>\<O>\<^sub>+)" [1000] 999)
  initial_of :: "('variable, 'domain) state" ("(_\<^sub>I\<^sub>+)" [1000] 999)
  goal_of :: "('variable, 'domain) state" ("(_\<^sub>G\<^sub>+)" [1000] 999)
  range_of :: "'variable \<rightharpoonup> 'domain list"

definition range_of':: "('variable, 'domain) sas_plus_problem \<Rightarrow> 'variable \<Rightarrow> 'domain set"  ("\<R>\<^sub>+ _ _" 52)
  where
  "range_of' \<Psi> v \<equiv>
     (case sas_plus_problem.range_of \<Psi> v of None \<Rightarrow> {} 
           | Some as \<Rightarrow> set as)"

definition to_precondition 
  :: "('variable, 'domain) sas_plus_operator \<Rightarrow> ('variable, 'domain) assignment list" 
  where "to_precondition \<equiv> precondition_of"

definition to_effect 
  :: "('variable, 'domain) sas_plus_operator \<Rightarrow> ('variable, 'domain) Effect" 
  where "to_effect op \<equiv> [(v, a) . (v, a) \<leftarrow> effect_of op]"

type_synonym  ('variable, 'domain) sas_plus_plan 
  = "('variable, 'domain) sas_plus_operator list"

type_synonym  ('variable, 'domain) sas_plus_parallel_plan 
  = "('variable, 'domain) sas_plus_operator list list"

abbreviation  empty_operator 
  :: "('variable, 'domain) sas_plus_operator" ("\<rho>")
  where "empty_operator \<equiv> \<lparr> precondition_of = [], effect_of = [] \<rparr>" 

definition is_valid_operator_sas_plus
  :: "('variable, 'domain) sas_plus_problem  \<Rightarrow> ('variable, 'domain) sas_plus_operator \<Rightarrow> bool" 
  where "is_valid_operator_sas_plus \<Psi> op \<equiv> let 
      pre = precondition_of op
      ; eff = effect_of op
      ; vs = variables_of \<Psi>
      ; D = range_of \<Psi>
    in list_all (\<lambda>(v, a). ListMem v vs) pre
      \<and> list_all (\<lambda>(v, a). (D v \<noteq> None) \<and> ListMem a (the (D v))) pre 
      \<and> list_all (\<lambda>(v, a). ListMem v vs) eff
      \<and> list_all (\<lambda>(v, a). (D v \<noteq> None) \<and> ListMem a (the (D v))) eff
      \<and> list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') pre) pre
      \<and> list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') eff) eff"

definition "is_valid_problem_sas_plus \<Psi> 
  \<equiv> let ops = operators_of \<Psi>
      ; vs = variables_of \<Psi>
      ; I = initial_of \<Psi>
      ; G = goal_of \<Psi>
      ; D = range_of \<Psi>
    in list_all (\<lambda>v. D v \<noteq> None) vs
    \<and> list_all (is_valid_operator_sas_plus \<Psi>) ops 
    \<and> (\<forall>v. I v \<noteq> None \<longleftrightarrow> ListMem v vs) 
    \<and> (\<forall>v. I v \<noteq> None \<longrightarrow> ListMem (the (I v)) (the (D v)))
    \<and> (\<forall>v. G v \<noteq> None \<longrightarrow> ListMem v (variables_of \<Psi>))
    \<and> (\<forall>v. G v \<noteq> None \<longrightarrow> ListMem (the (G v)) (the (D v)))" 

definition is_operator_applicable_in
  :: "('variable, 'domain) state 
    \<Rightarrow> ('variable, 'domain) sas_plus_operator 
    \<Rightarrow> bool"
  where "is_operator_applicable_in s op 
    \<equiv> map_of (precondition_of op) \<subseteq>\<^sub>m s" 

(* TODO rename execute_operator_in *)
definition execute_operator_sas_plus
  :: "('variable, 'domain) state 
    \<Rightarrow> ('variable, 'domain) sas_plus_operator
    \<Rightarrow> ('variable, 'domain) state" (infixl "\<then>\<^sub>+" 52)
  where "execute_operator_sas_plus s op \<equiv> s ++ map_of (effect_of op)"

\<comment> \<open> Set up simp rules to keep use of local parameters transparent within proofs (i.e. 
automatically substitute definitions). \<close>
lemma[simp]: 
  "is_operator_applicable_in s op = (map_of (precondition_of op) \<subseteq>\<^sub>m s)" 
  "s \<then>\<^sub>+ op = s ++ map_of (effect_of op)"
  unfolding initial_of_def goal_of_def variables_of_def range_of_def operators_of_def      
    SAS_Plus_Representation.is_operator_applicable_in_def
    SAS_Plus_Representation.execute_operator_sas_plus_def
  by simp+

lemma range_of_not_empty:
  "(sas_plus_problem.range_of \<Psi> v \<noteq> None \<and> sas_plus_problem.range_of \<Psi> v \<noteq> Some [])
    \<longleftrightarrow> (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
  apply (cases "sas_plus_problem.range_of \<Psi> v")
  by (auto simp add: SAS_Plus_Representation.range_of'_def)

lemma is_valid_operator_sas_plus_then:
  fixes \<Psi>::"('v,'d) sas_plus_problem"
  assumes "is_valid_operator_sas_plus \<Psi> op"
  shows "\<forall>(v, a) \<in> set (precondition_of op). v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>(v, a) \<in> set (precondition_of op). (\<R>\<^sub>+ \<Psi> v) \<noteq> {} \<and> a \<in> \<R>\<^sub>+ \<Psi> v" 
    and "\<forall>(v, a) \<in> set (effect_of op). v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>(v, a) \<in> set (effect_of op). (\<R>\<^sub>+ \<Psi> v) \<noteq> {} \<and> a \<in> \<R>\<^sub>+ \<Psi> v" 
    and "\<forall>(v, a) \<in> set (precondition_of op). \<forall>(v', a') \<in> set (precondition_of op). v \<noteq> v' \<or> a = a'"
    and "\<forall>(v, a) \<in> set (effect_of op). 
      \<forall>(v', a') \<in> set (effect_of op). v \<noteq> v' \<or> a = a'"
proof -
  let ?vs = "sas_plus_problem.variables_of \<Psi>" 
    and ?pre = "precondition_of op"
    and ?eff = "effect_of op"
    and ?D = "sas_plus_problem.range_of \<Psi>"
  have "\<forall>(v, a)\<in>set ?pre. v \<in> set ?vs"
    and "\<forall>(v, a)\<in>set ?pre.
          (?D v \<noteq> None) \<and>
          a \<in> set (the (?D v))"
    and "\<forall>(v, a)\<in>set ?eff. v \<in> set ?vs"
    and "\<forall>(v, a)\<in>set ?eff.
          (?D v \<noteq> None) \<and>
          a \<in> set (the (?D v))"
    and "\<forall>(v, a)\<in>set ?pre.
          \<forall>(v', a')\<in>set ?pre. v \<noteq> v' \<or> a = a'"
    and "\<forall>(v, a)\<in>set ?eff. 
      \<forall>(v', a')\<in>set ?eff. v \<noteq> v' \<or> a = a'"
    using assms
    unfolding is_valid_operator_sas_plus_def Let_def list_all_iff ListMem_iff 
    by meson+
  moreover have "\<forall>(v, a) \<in> set ?pre. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>(v, a) \<in> set ?eff. v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>(v, a) \<in> set ?pre. \<forall>(v', a') \<in> set ?pre. v \<noteq> v' \<or> a = a'"
    and "\<forall>(v, a) \<in> set ?eff. \<forall>(v', a') \<in> set ?eff. v \<noteq> v' \<or> a = a'" 
    using calculation 
    unfolding variables_of_def
    by blast+
  moreover {
    have "\<forall>(v, a) \<in> set ?pre. (?D v \<noteq> None) \<and> a \<in> set (the (?D v))"
      using assms 
      unfolding is_valid_operator_sas_plus_def Let_def list_all_iff ListMem_iff
      by argo
    hence "\<forall>(v, a) \<in> set ?pre. ((\<R>\<^sub>+ \<Psi> v) \<noteq> {}) \<and> a \<in> \<R>\<^sub>+ \<Psi> v" 
      using range_of'_def 
      by fastforce
  }
  moreover {
    have "\<forall>(v, a) \<in> set ?eff. (?D v \<noteq> None) \<and> a \<in> set (the (?D v))"
      using assms 
      unfolding is_valid_operator_sas_plus_def Let_def list_all_iff ListMem_iff
      by argo
    hence "\<forall>(v, a) \<in> set ?eff. ((\<R>\<^sub>+ \<Psi> v) \<noteq> {}) \<and> a \<in> \<R>\<^sub>+ \<Psi> v" 
      using range_of'_def
      by fastforce
  }
  ultimately show "\<forall>(v, a) \<in> set (precondition_of op). v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>(v, a) \<in> set (precondition_of op). (\<R>\<^sub>+ \<Psi> v) \<noteq> {} \<and> a \<in> \<R>\<^sub>+ \<Psi> v" 
    and "\<forall>(v, a) \<in> set (effect_of op). v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>(v, a) \<in> set (effect_of op). (\<R>\<^sub>+ \<Psi> v) \<noteq> {} \<and> a \<in> \<R>\<^sub>+ \<Psi> v" 
    and "\<forall>(v, a) \<in> set (precondition_of op). \<forall>(v', a') \<in> set (precondition_of op). v \<noteq> v' \<or> a = a'"
    and "\<forall>(v, a) \<in> set (effect_of op). 
      \<forall>(v', a') \<in> set (effect_of op). v \<noteq> v' \<or> a = a'" 
    by blast+
qed

(* TODO can be replaced by proof for sublocale? *)
lemma is_valid_problem_sas_plus_then:
  fixes \<Psi>::"('v,'d) sas_plus_problem"
  assumes "is_valid_problem_sas_plus \<Psi>"
  shows "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    and "\<forall>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and "dom ((\<Psi>)\<^sub>I\<^sub>+) = set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+). the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    and "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+). the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v" 
proof -
  let ?vs = "sas_plus_problem.variables_of \<Psi>"
    and ?ops = "sas_plus_problem.operators_of \<Psi>"
    and ?I = "sas_plus_problem.initial_of \<Psi>"
    and ?G = "sas_plus_problem.goal_of \<Psi>"
    and ?D = "sas_plus_problem.range_of \<Psi>"
  {
    fix v 
    have "(?D v \<noteq> None \<and> ?D v \<noteq> Some []) \<longleftrightarrow> ((\<R>\<^sub>+ \<Psi> v) \<noteq> {})"
      by (cases "?D v"; (auto simp: range_of'_def))
  } note nb = this
  have nb\<^sub>1: "\<forall>v \<in> set ?vs. ?D v \<noteq> None"
    and "\<forall>op \<in> set ?ops. is_valid_operator_sas_plus \<Psi> op"
    and "\<forall>v. (?I v \<noteq> None) = (v \<in> set ?vs)"
    and nb\<^sub>2: "\<forall>v. ?I v \<noteq> None \<longrightarrow> the (?I v) \<in> set (the (?D v))"
    and "\<forall>v. ?G v \<noteq> None \<longrightarrow> v \<in> set ?vs"
    and nb\<^sub>3: "\<forall>v. ?G v \<noteq> None \<longrightarrow> the (?G v) \<in> set (the (?D v))"
    using assms 
    unfolding SAS_Plus_Representation.is_valid_problem_sas_plus_def Let_def 
      list_all_iff ListMem_iff 
    by argo+
  then have G3: "\<forall>op \<in> set ((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and G4: "dom ((\<Psi>)\<^sub>I\<^sub>+) = set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and G5: "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    unfolding variables_of_def operators_of_def
    by auto+
  moreover {
    fix v
    assume "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    then have "?D v \<noteq> None"
      using nb\<^sub>1 
      by force+
  } note G6 = this
  moreover {
    fix v
    assume "v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+)"
    moreover have "((\<Psi>)\<^sub>I\<^sub>+) v \<noteq> None"
      using calculation
      by blast+
    moreover {
      have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
        using G4 calculation(1)
        by argo
      then have "sas_plus_problem.range_of \<Psi> v \<noteq> None" 
        using range_of_not_empty
        unfolding range_of'_def
        using G6 
        by fast+
      hence "set (the (?D v)) = \<R>\<^sub>+ \<Psi> v" 
        by (simp add: \<open>sas_plus_problem.range_of \<Psi> v \<noteq> None\<close> option.case_eq_if range_of'_def)
    }
    ultimately have "the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
      using nb\<^sub>2
      by force
  }
  moreover {
    fix v
    assume "v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+)"
    then have "((\<Psi>)\<^sub>G\<^sub>+) v \<noteq> None"
      by blast
    moreover {
      have "v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
        using G5 calculation(1)
        by fast
      then have "sas_plus_problem.range_of \<Psi> v \<noteq> None" 
        using range_of_not_empty
        using G6
        by fast+
      hence "set (the (?D v)) = \<R>\<^sub>+ \<Psi> v" 
        by (simp add: \<open>sas_plus_problem.range_of \<Psi> v \<noteq> None\<close> option.case_eq_if range_of'_def)
    }
    ultimately have "the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
      using nb\<^sub>3
      by auto
  }
  ultimately show "\<forall>v \<in> set ((\<Psi>)\<^sub>\<V>\<^sub>+). (\<R>\<^sub>+ \<Psi> v) \<noteq> {}"
    and "\<forall>op \<in> set((\<Psi>)\<^sub>\<O>\<^sub>+). is_valid_operator_sas_plus \<Psi> op"
    and "dom ((\<Psi>)\<^sub>I\<^sub>+) = set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>I\<^sub>+). the (((\<Psi>)\<^sub>I\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    and "dom ((\<Psi>)\<^sub>G\<^sub>+) \<subseteq> set ((\<Psi>)\<^sub>\<V>\<^sub>+)"
    and "\<forall>v \<in> dom ((\<Psi>)\<^sub>G\<^sub>+). the (((\<Psi>)\<^sub>G\<^sub>+) v) \<in> \<R>\<^sub>+ \<Psi> v"
    by blast+
qed

end