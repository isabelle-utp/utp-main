(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory SAT_Plan_Extensions
  imports SAT_Plan_Base
begin
section "Serializable SATPlan Encodings"

text \<open> A SATPlan encoding with exclusion of operator interference (see definition
\ref{def:sat-plan-encoding-with-interference-exclusion}) can be defined by extending the basic
SATPlan encoding with clauses

  @{text[display, indent=4] "
    \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>1))
    \<^bold>\<or> \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>2))"}

for all pairs of distinct interfering operators \<^term>\<open>op\<^sub>1\<close>, \<^term>\<open>op\<^sub>2\<close> for all time points
\<^term>\<open>k < t\<close> for a given estimated plan length \<^term>\<open>t\<close>. Definitions
\ref{isadef:interfering-operator-pair-exclusion-encoding} and
\ref{isadef:interfering-operator-exclusion-encoding} implement the encoding for operator pairs
resp. for all interfering operator pairs and all time points. \<close>

definition encode_interfering_operator_pair_exclusion
  :: "'variable strips_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> sat_plan_variable formula"
  where "encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2
    \<equiv> let ops = operators_of \<Pi> in
      \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>1)))
      \<^bold>\<or> \<^bold>\<not>(Atom (Operator k (index ops op\<^sub>2)))"

definition encode_interfering_operator_exclusion
  :: "'variable strips_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_interfering_operator_exclusion \<Pi> t \<equiv> let
      ops = operators_of \<Pi>
      ; interfering = filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ops op\<^sub>1 \<noteq> index ops op\<^sub>2
        \<and> are_operators_interfering op\<^sub>1 op\<^sub>2) (List.product ops ops)
    in foldr (\<^bold>\<and>) [encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2.
      (op\<^sub>1, op\<^sub>2) \<leftarrow> interfering, k \<leftarrow> [0..<t]] (\<^bold>\<not>\<bottom>)"

text \<open> A SATPlan encoding with interfering operator pair exclusion can now be defined by
simplying adding the conjunct \<^term>\<open>encode_interfering_operator_exclusion \<Pi> t\<close> to the basic
SATPlan encoding. \<close>

\<comment> \<open> NOTE This is the quadratic size encoding for the $\forall$-step semantics as defined in @{cite
\<open>3.2.1, p.1045\<close> "DBLP:journals/ai/RintanenHN06"}. This encoding ensures that decoded plans are
sequentializable by simply excluding the simultaneous execution of operators with potential
interference at any timepoint. Note that this yields a $\forall$-step plan for which parallel
operator execution at any time step may be sequentialised in any order (due to non-interference). \<close>

definition encode_problem_with_operator_interference_exclusion
  :: "'variable strips_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  ("\<Phi>\<^sub>\<forall> _ _" 52)
  where "encode_problem_with_operator_interference_exclusion \<Pi> t
    \<equiv> encode_initial_state \<Pi>
      \<^bold>\<and> (encode_operators \<Pi> t
      \<^bold>\<and> (encode_all_frame_axioms \<Pi> t
      \<^bold>\<and> (encode_interfering_operator_exclusion \<Pi> t
      \<^bold>\<and> (encode_goal_state \<Pi> t))))"


\<comment> \<open> Immediately proof the sublocale proposition for strips in order to gain access to definitions
and lemmas. \<close>


lemma cnf_of_encode_interfering_operator_pair_exclusion_is_i[simp]:
  "cnf (encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) = {{
    (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>1))\<inverse>
      , (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>2))\<inverse> }}"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  have "cnf (encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2)
    = cnf (\<^bold>\<not>(Atom (Operator k (index ?ops op\<^sub>1))) \<^bold>\<or> \<^bold>\<not>(Atom (Operator k (index ?ops op\<^sub>2))))"
    unfolding encode_interfering_operator_pair_exclusion_def
    by metis
  also have "\<dots> = { C \<union> D | C D.
    C \<in> cnf (\<^bold>\<not>(Atom (Operator k (index ?ops op\<^sub>1))))
    \<and> D \<in> cnf (\<^bold>\<not>(Atom (Operator k (index ?ops op\<^sub>2)))) }"
    by simp
  finally show ?thesis
    by auto
qed

lemma cnf_of_encode_interfering_operator_exclusion_is_ii[simp]:
  "set [encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2.
      (op\<^sub>1, op\<^sub>2) \<leftarrow> filter (\<lambda>(op\<^sub>1, op\<^sub>2).
          index (strips_problem.operators_of \<Pi>) op\<^sub>1 \<noteq> index (strips_problem.operators_of \<Pi>) op\<^sub>2
          \<and> are_operators_interfering op\<^sub>1 op\<^sub>2)
        (List.product (strips_problem.operators_of \<Pi>) (strips_problem.operators_of \<Pi>))
        , k \<leftarrow> [0..<t]]
    = (\<Union>(op\<^sub>1, op\<^sub>2)
        \<in> { (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>).
          index (strips_problem.operators_of \<Pi>) op\<^sub>1 \<noteq> index (strips_problem.operators_of \<Pi>) op\<^sub>2
          \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }.
      (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) ` {0..<t})"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  let ?interfering = "filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
    \<and> are_operators_interfering op\<^sub>1 op\<^sub>2) (List.product ?ops ?ops)"
  let ?fs = "[encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2.
    (op\<^sub>1, op\<^sub>2) \<leftarrow> ?interfering, k \<leftarrow> [0..<t]]"
  have "set ?fs = \<Union>(set
    ` (\<lambda>(op\<^sub>1, op\<^sub>2). map (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) [0..<t])
    ` (set (filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2 \<and> are_operators_interfering op\<^sub>1 op\<^sub>2)
      (List.product ?ops ?ops))))"
    unfolding set_concat set_map
    by blast
  \<comment> \<open> TODO slow. \<close>
  also have "\<dots> = \<Union>((\<lambda>(op\<^sub>1, op\<^sub>2).
      set (map (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) [0..<t]))
    ` (set (filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2 \<and> are_operators_interfering op\<^sub>1 op\<^sub>2)
      (List.product ?ops ?ops))))"
    unfolding image_comp[of
        set "\<lambda>(op\<^sub>1, op\<^sub>2). map (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) [0..<t]"]
      comp_apply
    by fast
  also have "\<dots> = \<Union>((\<lambda>(op\<^sub>1, op\<^sub>2).
      (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) ` {0..<t})
    ` (set (filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2 \<and> are_operators_interfering op\<^sub>1 op\<^sub>2)
      (List.product ?ops ?ops))))"
    unfolding set_map[of _ "[0..<t]"] atLeastLessThan_upt[of 0 t]
    by blast
  also have "\<dots> = \<Union>((\<lambda>(op\<^sub>1, op\<^sub>2).
      (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) ` {0..<t})
    ` (Set.filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2 \<and> are_operators_interfering op\<^sub>1 op\<^sub>2)
      (set (List.product ?ops ?ops))))"
    unfolding set_filter[of "\<lambda>(op\<^sub>1, op\<^sub>2). are_operators_interfering op\<^sub>1 op\<^sub>2" "List.product ?ops ?ops"]
    by force
  \<comment> \<open> TODO slow.\<close>
  finally show ?thesis
    unfolding operators_of_def set_product[of ?ops ?ops]
    by fastforce
qed

(* TODO refactor using above lemma *)
lemma cnf_of_encode_interfering_operator_exclusion_is_iii[simp]:
  (* TODO why is this necessary? *)
  fixes \<Pi> :: "'variable strips_problem"
  shows "cnf ` set [encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2.
      (op\<^sub>1, op\<^sub>2) \<leftarrow> filter (\<lambda>(op\<^sub>1, op\<^sub>2).
          index (strips_problem.operators_of \<Pi>) op\<^sub>1 \<noteq> index (strips_problem.operators_of \<Pi>) op\<^sub>2
          \<and> are_operators_interfering op\<^sub>1 op\<^sub>2)
        (List.product (strips_problem.operators_of \<Pi>) (strips_problem.operators_of \<Pi>))
      , k \<leftarrow> [0..<t]]
    = (\<Union>(op\<^sub>1, op\<^sub>2)
        \<in> { (op\<^sub>1, op\<^sub>2) \<in> set (strips_problem.operators_of \<Pi>) \<times> set (strips_problem.operators_of \<Pi>).
          index (strips_problem.operators_of \<Pi>) op\<^sub>1 \<noteq> index (strips_problem.operators_of \<Pi>) op\<^sub>2
          \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }.
      {{{ (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>1))\<inverse>
        , (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>2))\<inverse> }} | k. k \<in> {0..<t}})"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  let ?interfering = "filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
    \<and> are_operators_interfering op\<^sub>1 op\<^sub>2) (List.product ?ops ?ops)"
  let ?fs = "[encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2.
    (op\<^sub>1, op\<^sub>2) \<leftarrow> ?interfering, k \<leftarrow> [0..<t]]"
  have "cnf ` set ?fs = cnf ` (\<Union>(op\<^sub>1, op\<^sub>2) \<in> { (op\<^sub>1, op\<^sub>2).
    (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>) \<and> index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
      \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }.
    (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) ` {0..<t})"
    unfolding cnf_of_encode_interfering_operator_exclusion_is_ii
    by blast
  also have "\<dots> = (\<Union>(op\<^sub>1, op\<^sub>2) \<in> { (op\<^sub>1, op\<^sub>2).
    (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>) \<and> index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
      \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }.
    (\<lambda>k. cnf (encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2)) ` {0..<t})"
    unfolding image_Un image_comp comp_apply
    by blast
  also have "\<dots> = (\<Union>(op\<^sub>1, op\<^sub>2) \<in> { (op\<^sub>1, op\<^sub>2).
    (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>) \<and> index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
      \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }.
    (\<lambda>k. {{ (Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse> }}) ` {0..<t})"
    by simp
  also have "\<dots> = (\<Union>(op\<^sub>1, op\<^sub>2) \<in> { (op\<^sub>1, op\<^sub>2).
    (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>) \<and> index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
        \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }.
      (\<lambda>k. {{ (Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse> }})
        ` { k | k. k \<in> {0..<t}})"
    by blast
  \<comment> \<open> TODO slow.\<close>
  finally show ?thesis
    unfolding operators_of_def setcompr_eq_image[of _ "\<lambda>k. k \<in> {0..<t}"]
    by force
qed

lemma cnf_of_encode_interfering_operator_exclusion_is:
  "cnf (encode_interfering_operator_exclusion \<Pi> t) = \<Union>(\<Union>(op\<^sub>1, op\<^sub>2)
      \<in> { (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>).
        index (strips_problem.operators_of \<Pi>) op\<^sub>1 \<noteq> index (strips_problem.operators_of \<Pi>) op\<^sub>2
          \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }.
    {{{ (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>1))\<inverse>
      , (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>2))\<inverse> }} | k. k \<in> {0..<t}})"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  let ?interfering = "filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
    \<and> are_operators_interfering op\<^sub>1 op\<^sub>2) (List.product ?ops ?ops)"
  let ?fs = "[encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2.
    (op\<^sub>1, op\<^sub>2) \<leftarrow> ?interfering, k \<leftarrow> [0..<t]]"
  have "cnf (encode_interfering_operator_exclusion \<Pi> t) = cnf (foldr (\<^bold>\<and>) ?fs (\<^bold>\<not>\<bottom>))"
    unfolding encode_interfering_operator_exclusion_def
    by metis
  also have "\<dots> = \<Union>(cnf ` set ?fs)"
    unfolding cnf_foldr_and[of ?fs]..
  finally show ?thesis
    unfolding cnf_of_encode_interfering_operator_exclusion_is_iii[of \<Pi> t]
    by blast
qed

lemma cnf_of_encode_interfering_operator_exclusion_contains_clause_if:
  (* TODO why do we need to fix the problem type? *)
  fixes \<Pi> :: "'variable strips_problem"
  assumes "k < t"
    and "op\<^sub>1 \<in> set (strips_problem.operators_of \<Pi>)" and "op\<^sub>2 \<in> set (strips_problem.operators_of \<Pi>)"
    and "index (strips_problem.operators_of \<Pi>) op\<^sub>1 \<noteq> index (strips_problem.operators_of \<Pi>) op\<^sub>2"
    and "are_operators_interfering op\<^sub>1 op\<^sub>2"
  shows "{ (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>1))\<inverse>
      , (Operator k (index (strips_problem.operators_of \<Pi>) op\<^sub>2))\<inverse>}
    \<in> cnf (encode_interfering_operator_exclusion \<Pi> t)"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<Phi>\<^sub>X = "encode_interfering_operator_exclusion \<Pi> t"
  let ?Ops = "{ (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>).
        index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2 \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }"
    and ?f = "\<lambda>(op\<^sub>1, op\<^sub>2). {{{ (Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse> }}
      | k. k \<in> {0..<t}}"
  let ?A = "(\<Union>(op\<^sub>1, op\<^sub>2) \<in> ?Ops. ?f (op\<^sub>1, op\<^sub>2))"
  let ?B = "\<Union>?A"
    and ?C = "{ (Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse> }"
  {
    have "(op\<^sub>1, op\<^sub>2) \<in> ?Ops"
      using assms(2, 3, 4, 5)
      unfolding operators_of_def
      by force
    moreover have "{ ?C } \<in> ?f (op\<^sub>1, op\<^sub>2)"
      using assms(1)
      by auto
    moreover have "{ ?C } \<in> ?A"
      using UN_iff[of ?C _ ?Ops] calculation(1, 2)
      by blast
    (* TODO slow *)
    ultimately have "\<exists>X \<in> ?A. ?C \<in> X"
      by auto
  }
  (* TODO slow *)
  thus ?thesis
    unfolding cnf_of_encode_interfering_operator_exclusion_is
    using Union_iff[of ?C ?A]
    by auto
qed

lemma is_cnf_encode_interfering_operator_exclusion:
  (* TODO why is this necessary? *)
  fixes \<Pi> :: "'variable strips_problem"
  shows "is_cnf (encode_interfering_operator_exclusion \<Pi> t)"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  let ?interfering = "filter (\<lambda>(op\<^sub>1, op\<^sub>2). index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
    \<and> are_operators_interfering op\<^sub>1 op\<^sub>2) (List.product ?ops ?ops)"
  let ?fs = "[encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2.
    (op\<^sub>1, op\<^sub>2) \<leftarrow> ?interfering, k \<leftarrow> [0..<t]]"
  let ?Fs = "(\<Union>(op\<^sub>1, op\<^sub>2)
        \<in> { (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>). are_operators_interfering op\<^sub>1 op\<^sub>2 }.
      (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) ` {0..<t})"
  {
    fix f
    assume "f \<in> set ?fs"
    then have "f \<in> ?Fs"
      unfolding cnf_of_encode_interfering_operator_exclusion_is_ii
      by blast
    then obtain op\<^sub>1 op\<^sub>2
      where "(op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>)"
      and "are_operators_interfering op\<^sub>1 op\<^sub>2"
      and "f \<in> (\<lambda>k. encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2) ` {0..<t}"
      by fast
    then obtain k where "f = encode_interfering_operator_pair_exclusion \<Pi> k op\<^sub>1 op\<^sub>2"
      by blast
    then have "f = \<^bold>\<not>(Atom (Operator k (index ?ops op\<^sub>1))) \<^bold>\<or> \<^bold>\<not>(Atom (Operator k (index ?ops op\<^sub>2)))"
      unfolding encode_interfering_operator_pair_exclusion_def
      by metis
    hence "is_cnf f"
      by force
  }
  thus ?thesis
    unfolding encode_interfering_operator_exclusion_def
    using is_cnf_foldr_and_if[of ?fs]
    by meson
qed

lemma is_cnf_encode_problem_with_operator_interference_exclusion:
  assumes "is_valid_problem_strips \<Pi>"
  shows "is_cnf (\<Phi>\<^sub>\<forall> \<Pi> t)"
  using is_cnf_encode_problem is_cnf_encode_interfering_operator_exclusion assms
  unfolding encode_problem_with_operator_interference_exclusion_def SAT_Plan_Base.encode_problem_def
    is_cnf.simps(1)
  by blast

lemma cnf_of_encode_problem_with_operator_interference_exclusion_structure:
  shows "cnf (\<Phi>\<^sub>I \<Pi>) \<subseteq> cnf (\<Phi>\<^sub>\<forall> \<Pi> t)"
    and "cnf ((\<Phi>\<^sub>G \<Pi>) t) \<subseteq> cnf (\<Phi>\<^sub>\<forall> \<Pi> t)"
    and "cnf (encode_operators \<Pi> t) \<subseteq> cnf (\<Phi>\<^sub>\<forall> \<Pi> t)"
    and "cnf (encode_all_frame_axioms \<Pi> t) \<subseteq> cnf (\<Phi>\<^sub>\<forall> \<Pi> t)"
    and "cnf (encode_interfering_operator_exclusion \<Pi> t) \<subseteq> cnf (\<Phi>\<^sub>\<forall> \<Pi> t)"
  unfolding encode_problem_with_operator_interference_exclusion_def encode_problem_def SAT_Plan_Base.encode_problem_def
    encode_initial_state_def
    encode_goal_state_def
  by auto+

(* TODO remove (unused)? *)
lemma encode_problem_with_operator_interference_exclusion_has_model_then_also_partial_encodings:
  assumes "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> \<Pi> t"
  shows "\<A> \<Turnstile> SAT_Plan_Base.encode_initial_state \<Pi>"
    and "\<A> \<Turnstile> SAT_Plan_Base.encode_operators \<Pi> t"
    and "\<A> \<Turnstile> SAT_Plan_Base.encode_all_frame_axioms \<Pi> t"
    and "\<A> \<Turnstile> encode_interfering_operator_exclusion \<Pi> t"
    and "\<A> \<Turnstile> SAT_Plan_Base.encode_goal_state \<Pi> t"
  using assms
  unfolding encode_problem_with_operator_interference_exclusion_def encode_problem_def SAT_Plan_Base.encode_problem_def
  by simp+



text \<open> Just as for the basic SATPlan encoding we defined local context for the SATPlan encoding
with interfering operator exclusion. We omit this here since it is basically identical to the one
shown in the basic SATPlan theory replacing only the definitions of \isaname{encode_transitions}
and \isaname{encode_problem}. The sublocale proof is shown below. It confirms that the new
encoding again a CNF as required by locale \isaname{sat_encode_strips}. \<close>

subsection "Soundness"


text \<open> The Proof of soundness for the SATPlan encoding with interfering operator exclusion follows
directly from the proof of soundness of the basic SATPlan encoding. By looking at the structure of
the new encoding which simply extends the basic SATPlan encoding with a conjunct, any model for
encoding with exclusion of operator interference also models the basic SATPlan encoding and the
soundness of the new encoding therefore follows from theorem
\ref{isathm:soundness-satplan-encoding}.

Moreover, since we additionally added interfering operator exclusion clauses at every timestep, the
decoded parallel plan cannot contain any interfering operators in any parallel operator (making it
serializable). \<close>

\<comment> \<open> NOTE We use the \<open>subseq\<close> formulation in the fourth assumption to be able to instantiate the
induction hypothesis on the subseq \<open>ops\<close> given the induction premise
\<open>op # ops \<in> set (subseqs (\<Phi>\<inverse> \<Pi> \<A> t ! k))\<close>. We do not use subsets in the
assumption since we would otherwise lose the distinctness property which can be infered from
\<open>ops \<in> set (subseqs (\<Phi>\<inverse> \<Pi> \<A> t ! k))\<close> using lemma \<open>subseqs_distinctD\<close>. \<close>
lemma encode_problem_serializable_sound_i:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> \<Pi> t"
    and "k < t"
    and "ops \<in> set (subseqs ((\<Phi>\<inverse> \<Pi> \<A> t) ! k))"
  shows "are_all_operators_non_interfering ops"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
    and ?\<Phi>\<^sub>X = "encode_interfering_operator_exclusion \<Pi> t"
  let ?\<pi>\<^sub>k = "(\<Phi>\<inverse> \<Pi> \<A> t) ! k"
  (* TODO refactor *)
  {
    fix C
    assume C_in: "C \<in> cnf ?\<Phi>\<^sub>X"
    have "cnf_semantics \<A> (cnf ?\<Phi>\<^sub>X)"
      using cnf_semantics_monotonous_in_cnf_subsets_if[OF assms(2)
        is_cnf_encode_problem_with_operator_interference_exclusion[OF assms(1)]
        cnf_of_encode_problem_with_operator_interference_exclusion_structure(5)].
    hence "clause_semantics \<A> C"
      unfolding cnf_semantics_def
      using C_in
      by fast
  } note nb\<^sub>1 = this
  {
    fix op\<^sub>1 op\<^sub>2
    assume "op\<^sub>1 \<in> set ?\<pi>\<^sub>k" and "op\<^sub>2 \<in> set ?\<pi>\<^sub>k"
      and index_op\<^sub>1_is_not_index_op\<^sub>2: "index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2"
    moreover have op\<^sub>1_in: "op\<^sub>1 \<in> set ?ops" and \<A>_models_op\<^sub>1:"\<A> (Operator k (index ?ops op\<^sub>1))"
      and op\<^sub>2_in: "op\<^sub>2 \<in> set ?ops" and \<A>_models_op\<^sub>2: "\<A> (Operator k (index ?ops op\<^sub>2))"
      using decode_plan_step_element_then[OF assms(3)] calculation
      unfolding decode_plan_def
      by blast+
    moreover {
      let ?C = "{ (Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse> }"
      assume "are_operators_interfering op\<^sub>1 op\<^sub>2"
      moreover have "?C \<in> cnf ?\<Phi>\<^sub>X"
        using cnf_of_encode_interfering_operator_exclusion_contains_clause_if[OF
            assms(3) op\<^sub>1_in op\<^sub>2_in index_op\<^sub>1_is_not_index_op\<^sub>2] calculation
        by blast
      moreover have "\<not>clause_semantics \<A> ?C"
        using \<A>_models_op\<^sub>1 \<A>_models_op\<^sub>2
        unfolding clause_semantics_def
        by auto
      ultimately have False
        using nb\<^sub>1
        by blast
    }
    ultimately have "\<not>are_operators_interfering op\<^sub>1 op\<^sub>2"
      by blast
  } note nb\<^sub>3 = this
  show ?thesis
    using assms
    proof (induction ops)
      case (Cons op\<^sub>1 ops)
      have "are_all_operators_non_interfering ops"
        using Cons.IH[OF Cons.prems(1, 2, 3) Cons_in_subseqsD[OF Cons.prems(4)]]
        by blast
      moreover {
        fix op\<^sub>2
        assume op\<^sub>2_in_ops: "op\<^sub>2 \<in> set ops"
        moreover have op\<^sub>1_in_\<pi>\<^sub>k: "op\<^sub>1 \<in> set ?\<pi>\<^sub>k" and op\<^sub>2_in_\<pi>\<^sub>k: "op\<^sub>2 \<in> set ?\<pi>\<^sub>k"
          using element_of_subseqs_then_subset[OF Cons.prems(4)] calculation(1)
          by auto+
        moreover
        {
          have "distinct (op\<^sub>1 # ops)"
            using subseqs_distinctD[OF Cons.prems(4)]
              decode_plan_step_distinct[OF Cons.prems(3)]
            unfolding decode_plan_def
            by blast
          moreover have "op\<^sub>1 \<in> set ?ops" and "op\<^sub>2 \<in> set ?ops"
            using decode_plan_step_element_then(1)[OF Cons.prems(3)] op\<^sub>1_in_\<pi>\<^sub>k op\<^sub>2_in_\<pi>\<^sub>k
            unfolding decode_plan_def
            by force+
          moreover have "op\<^sub>1 \<noteq> op\<^sub>2"
            using op\<^sub>2_in_ops calculation(1)
            by fastforce
          ultimately have "index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2"
            using index_eq_index_conv
            by auto
        }
        ultimately have "\<not>are_operators_interfering op\<^sub>1 op\<^sub>2"
          using nb\<^sub>3
          by blast
      }
      ultimately show ?case
        using list_all_iff
        by auto
    qed simp
qed

theorem encode_problem_serializable_sound:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> \<Pi> t"
  shows "is_parallel_solution_for_problem \<Pi> (\<Phi>\<inverse> \<Pi> \<A> t)"
    and "\<forall>k < length (\<Phi>\<inverse> \<Pi> \<A> t). are_all_operators_non_interfering ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
proof -
  {
    have "\<A> \<Turnstile> SAT_Plan_Base.encode_initial_state \<Pi>"
      and "\<A> \<Turnstile> SAT_Plan_Base.encode_operators \<Pi> t"
      and "\<A> \<Turnstile> SAT_Plan_Base.encode_all_frame_axioms \<Pi> t"
      and "\<A> \<Turnstile> SAT_Plan_Base.encode_goal_state \<Pi> t"
      using assms(2)
      unfolding encode_problem_with_operator_interference_exclusion_def
      by simp+
    then have "\<A> \<Turnstile> SAT_Plan_Base.encode_problem \<Pi> t"
      unfolding SAT_Plan_Base.encode_problem_def
      by simp
  }
  thus "is_parallel_solution_for_problem \<Pi> (\<Phi>\<inverse> \<Pi> \<A> t)"
    using encode_problem_parallel_sound assms(1, 2)
    unfolding decode_plan_def
    by blast
next
  let ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
  {
    fix k
    assume "k < t"
    moreover have "?\<pi> ! k \<in> set (subseqs (?\<pi> ! k))"
      using subseqs_refl
      by blast
    ultimately have "are_all_operators_non_interfering (?\<pi> ! k)"
      using encode_problem_serializable_sound_i[OF assms]
      unfolding SAT_Plan_Base.decode_plan_def decode_plan_def
      by blast
  }
  moreover have "length ?\<pi> = t"
    unfolding SAT_Plan_Base.decode_plan_def decode_plan_def
    by simp
  ultimately show "\<forall>k < length ?\<pi>. are_all_operators_non_interfering (?\<pi> ! k)"
    by simp
qed


subsection "Completeness"


lemma encode_problem_with_operator_interference_exclusion_complete_i:
  assumes "is_valid_problem_strips \<Pi>"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "\<forall>k < length \<pi>. are_all_operators_non_interfering (\<pi> ! k)"
  shows "valuation_for_plan \<Pi> \<pi> \<Turnstile> encode_interfering_operator_exclusion \<Pi> (length \<pi>)"
proof -
  let ?\<A> = "valuation_for_plan \<Pi> \<pi>"
    and ?\<Phi>\<^sub>X = "encode_interfering_operator_exclusion \<Pi> (length \<pi>)"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?t = "length \<pi>"
  let ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?Ops = "{ (op\<^sub>1, op\<^sub>2). (op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>)
    \<and> index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2
    \<and> are_operators_interfering op\<^sub>1 op\<^sub>2 }"
    and ?f = "\<lambda>(op\<^sub>1, op\<^sub>2). {{{ (Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse> }}
      | k. k \<in> {0..<length \<pi>} }"
  let ?A = "\<Union>(?f ` ?Ops)"
  let ?B = "\<Union>?A"
  have nb\<^sub>1: "\<forall>ops \<in> set \<pi>. \<forall>op \<in> set ops. op \<in> set (operators_of \<Pi>)"
    using is_parallel_solution_for_problem_operator_set[OF assms(2)]
    unfolding operators_of_def
    by blast
  (* TODO refactor (characterization of \<A>) *)
  {
    fix k op
    assume "k < length \<pi>" and "op \<in> set (\<pi> ! k)"
    hence "lit_semantics ?\<A> ((Operator k (index ?ops op))\<^sup>+) = (k < length ?\<tau> - 1)"
      using encode_problem_parallel_complete_vi_a[OF assms(2)]
        encode_problem_parallel_complete_vi_b[OF assms(2)] initial_of_def
      by(cases "k < length ?\<tau> - 1"; simp)
  } note nb\<^sub>2 = this
  {
    fix k op\<^sub>1 op\<^sub>2
    assume "k < length \<pi>"
      and "op\<^sub>1 \<in> set (\<pi> ! k)"
      and "index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2"
      and "are_operators_interfering op\<^sub>1 op\<^sub>2"
    moreover have "are_all_operators_non_interfering (\<pi> ! k)"
      using assms(3) calculation(1)
      by blast
    moreover have "op\<^sub>1 \<noteq> op\<^sub>2"
      using calculation(3)
      by blast
    ultimately have "op\<^sub>2 \<notin> set (\<pi> ! k)"
      using are_all_operators_non_interfering_set_contains_no_distinct_interfering_operator_pairs
        assms(3)
      by blast
  } note nb\<^sub>3 = this
  {
    fix C
    assume "C \<in> cnf ?\<Phi>\<^sub>X"
    then have "C \<in> ?B"
      using cnf_of_encode_interfering_operator_exclusion_is[of \<Pi> "length \<pi>"]
      by argo
    then obtain C' where "C' \<in> ?A" and C_in: "C \<in> C'"
      using Union_iff[of C ?A]
      by meson
    then obtain op\<^sub>1 op\<^sub>2 where "(op\<^sub>1, op\<^sub>2) \<in> set (operators_of \<Pi>) \<times> set (operators_of \<Pi>)"
      and index_op\<^sub>1_is_not_index_op\<^sub>2: "index ?ops op\<^sub>1 \<noteq> index ?ops op\<^sub>2"
      and are_operators_interfering_op\<^sub>1_op\<^sub>2: "are_operators_interfering op\<^sub>1 op\<^sub>2"
      and C'_in: "C' \<in> {{{(Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse>}}
        | k. k \<in> {0..<length \<pi>}}"
      using UN_iff[of C' ?f ?Ops]
      by blast
    then obtain k where "k \<in> {0..<length \<pi>}"
      and C_is: "C = { (Operator k (index ?ops op\<^sub>1))\<inverse>, (Operator k (index ?ops op\<^sub>2))\<inverse> }"
      using C_in C'_in
      by blast
    then have k_lt_length_\<pi>: "k < length \<pi>"
      by simp
    consider (A) "op\<^sub>1 \<in> set (\<pi> ! k)"
     | (B) "op\<^sub>2 \<in> set (\<pi> ! k)"
     | (C) "\<not>op\<^sub>1 \<in> set (\<pi> ! k) \<or> \<not>op\<^sub>2 \<in> set (\<pi> ! k)"
      by linarith
    hence "clause_semantics ?\<A> C"
      proof (cases)
        case A
        moreover have "op\<^sub>2 \<notin> set (\<pi> ! k)"
          using nb\<^sub>3 k_lt_length_\<pi> calculation index_op\<^sub>1_is_not_index_op\<^sub>2 are_operators_interfering_op\<^sub>1_op\<^sub>2
          by blast
        moreover have "\<not>?\<A> (Operator k (index ?ops op\<^sub>2))"
          using encode_problem_parallel_complete_vi_d[OF assms(2) k_lt_length_\<pi>]
            calculation(2)
          by blast
        ultimately show ?thesis
          using C_is
          unfolding clause_semantics_def
          by force
      next
        case B
        moreover have "op\<^sub>1 \<notin> set (\<pi> ! k)"
          using nb\<^sub>3 k_lt_length_\<pi> calculation index_op\<^sub>1_is_not_index_op\<^sub>2 are_operators_interfering_op\<^sub>1_op\<^sub>2
          by blast
        moreover have "\<not>?\<A> (Operator k (index ?ops op\<^sub>1))"
          using encode_problem_parallel_complete_vi_d[OF assms(2) k_lt_length_\<pi>]
            calculation(2)
          by blast
        ultimately show ?thesis
          using C_is
          unfolding clause_semantics_def
          by force
      next
        case C
        then show ?thesis
          proof (rule disjE)
            assume "op\<^sub>1 \<notin> set (\<pi> ! k)"
            then have "\<not>?\<A> (Operator k (index ?ops op\<^sub>1))"
              using encode_problem_parallel_complete_vi_d[OF assms(2) k_lt_length_\<pi>]
              by blast
            thus "clause_semantics (valuation_for_plan \<Pi> \<pi>) C"
              using C_is
              unfolding clause_semantics_def
              by force
          next
            assume "op\<^sub>2 \<notin> set (\<pi> ! k)"
            then have "\<not>?\<A> (Operator k (index ?ops op\<^sub>2))"
              using encode_problem_parallel_complete_vi_d[OF assms(2) k_lt_length_\<pi>]
              by blast
            thus "clause_semantics (valuation_for_plan \<Pi> \<pi>) C"
              using C_is
              unfolding clause_semantics_def
              by force
          qed
      qed
  }
  then have "cnf_semantics ?\<A> (cnf ?\<Phi>\<^sub>X)"
    unfolding cnf_semantics_def..
  thus ?thesis
    using cnf_semantics[OF is_nnf_cnf[OF is_cnf_encode_interfering_operator_exclusion]]
    by fast
qed

text \<open> Similar to the soundness proof, we may reuse the previously established
facts about the valuation for the completeness proof of the basic SATPlan encoding
(\ref{isathm:completeness-satplan-encoding}).
To make it clearer why this is true we have a look at the form of the clauses for interfering operator
pairs \<^term>\<open>op\<^sub>1\<close> and \<^term>\<open>op\<^sub>2\<close> at the same time index \<^term>\<open>k\<close> which have the form shown below:
  @{text[display, indent=4] "{ (Operator k (index ops op\<^sub>1))\<inverse>, (Operator k (index ops op\<^sub>2))\<inverse> }"}
where \<^term>\<open>ops \<equiv> strips_problem.operators_of \<Pi>\<close>.
Now, consider an operator \<^term>\<open>op\<^sub>1\<close> that is contained in the \<^term>\<open>k\<close>-th plan step \<^term>\<open>\<pi> ! k\<close>
(symmetrically for \<^term>\<open>op\<^sub>2\<close>). Since \<^term>\<open>\<pi>\<close> is a serializable solution, there can be no
interference between \<^term>\<open>op\<^sub>1\<close> and \<^term>\<open>op\<^sub>2\<close> at time \<^term>\<open>k\<close>. Hence \<^term>\<open>op\<^sub>2\<close> cannot be in \<^term>\<open>\<pi> ! k\<close>
This entails that for \<^term>\<open>\<A> \<equiv> valuation_for_plan \<Pi> \<pi>\<close> it holds that
  @{text[display, indent=4] "\<A> \<Turnstile> \<^bold>\<not> Atom (Operator k (index ops op\<^sub>2))"}
and \<^term>\<open>\<A>\<close> therefore models the clause.

Furthermore, if neither is present, than \<^term>\<open>\<A>\<close> will evaluate both atoms to false and the clause
therefore evaluates to true as well.

It follows from this that each clause in the extension of the SATPlan encoding evaluates to true
for \<^term>\<open>\<A>\<close>. The other parts of the encoding evaluate to true as per the completeness of the
basic SATPlan encoding (theorem \ref{isathm:completeness-satplan-encoding}).\<close>

theorem encode_problem_serializable_complete:
  assumes "is_valid_problem_strips \<Pi>"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "\<forall>k < length \<pi>. are_all_operators_non_interfering (\<pi> ! k)"
  shows "valuation_for_plan \<Pi> \<pi> \<Turnstile> \<Phi>\<^sub>\<forall> \<Pi> (length \<pi>)"
proof -
  let ?\<A> = "valuation_for_plan \<Pi> \<pi>"
    and ?\<Phi>\<^sub>X = "encode_interfering_operator_exclusion \<Pi> (length \<pi>)"
  have "?\<A> \<Turnstile> SAT_Plan_Base.encode_problem \<Pi> (length \<pi>)"
    using assms(1, 2) encode_problem_parallel_complete
    by auto
  moreover have "?\<A> \<Turnstile> ?\<Phi>\<^sub>X"
    using encode_problem_with_operator_interference_exclusion_complete_i[OF assms].
  ultimately show ?thesis
    unfolding encode_problem_with_operator_interference_exclusion_def encode_problem_def
      SAT_Plan_Base.encode_problem_def
    by force
qed

value  "stop" (* Tell document preparation to stop collecting for the last tag *)

(* TODO rename encode_problem_with_operator_interference_exclusion_decoded_plan_is_serializable_i *)
lemma encode_problem_forall_step_decoded_plan_is_serializable_i:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> \<Pi> t"
  shows "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_serial_plan ((\<Pi>)\<^sub>I) (concat (\<Phi>\<inverse> \<Pi> \<A> t))"
proof -
  let ?G = "(\<Pi>)\<^sub>G"
    and ?I = "(\<Pi>)\<^sub>I"
    and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
  let ?\<pi>' = "concat (\<Phi>\<inverse> \<Pi> \<A> t)"
    and ?\<tau> = "trace_parallel_plan_strips ?I ?\<pi>"
    and ?\<sigma> = "map (decode_state_at \<Pi> \<A>) [0..<Suc (length ?\<pi>)]"
  {
    fix k
    assume k_lt_length_\<pi>: "k < length ?\<pi>"
    moreover have "\<A> \<Turnstile> SAT_Plan_Base.encode_problem \<Pi> t"
      using assms(2)
      unfolding encode_problem_with_operator_interference_exclusion_def
        encode_problem_def SAT_Plan_Base.encode_problem_def
      by simp
    moreover have "length ?\<sigma> = length ?\<tau>"
      using encode_problem_parallel_correct_vii assms(1) calculation
      unfolding decode_state_at_def decode_plan_def initial_of_def
      by fast
    ultimately have "k < length ?\<tau> - 1" and "k < t"
      unfolding decode_plan_def SAT_Plan_Base.decode_plan_def
      by force+
  } note nb = this
  {
    have "?G \<subseteq>\<^sub>m execute_parallel_plan ?I ?\<pi>"
      using encode_problem_serializable_sound assms
      unfolding is_parallel_solution_for_problem_def decode_plan_def
        goal_of_def initial_of_def
      by blast
    hence "?G \<subseteq>\<^sub>m last (trace_parallel_plan_strips ?I ?\<pi>)"
      using execute_parallel_plan_reaches_goal_iff_goal_is_last_element_of_trace
      by fast
  }
  moreover {
    fix k
    assume k_lt_length_\<pi>: "k < length ?\<pi>"
    moreover have "k < length ?\<tau> - 1" and "k < t"
      using nb calculation
      by blast+
    moreover have "are_all_operators_applicable (?\<tau> ! k) (?\<pi> ! k)"
      and "are_all_operator_effects_consistent (?\<pi> ! k)"
      using trace_parallel_plan_strips_operator_preconditions calculation(2)
      by blast+
    moreover have "are_all_operators_non_interfering (?\<pi> ! k)"
      using encode_problem_serializable_sound(2)[OF assms(1, 2)] k_lt_length_\<pi>
      by blast
    ultimately have "are_all_operators_applicable (?\<tau> ! k) (?\<pi> ! k)"
      and "are_all_operator_effects_consistent (?\<pi> ! k)"
      and "are_all_operators_non_interfering (?\<pi> ! k)"
      by blast+
  }
  ultimately show ?thesis
    using execute_parallel_plan_is_execute_sequential_plan_if assms(1)
    by metis
qed

(* TODO rename encode_problem_with_operator_interference_exclusion_decoded_plan_is_serializable_ii *)
lemma encode_problem_forall_step_decoded_plan_is_serializable_ii:
  (* TODO why is the fixed type necessary? *)
  fixes \<Pi> :: "'variable strips_problem"
  shows "list_all (\<lambda>op. ListMem op (strips_problem.operators_of \<Pi>))
    (concat (\<Phi>\<inverse> \<Pi> \<A> t))"
proof -
  let ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
  let ?\<pi>' = "concat ?\<pi>"
  (* TODO refactor *)
  {
    have "set ?\<pi>' = \<Union>(set `  (\<Union>k < t. { decode_plan' \<Pi> \<A> k }))"
      unfolding decode_plan_def decode_plan_set_is set_concat
      by auto
    also have "\<dots> = \<Union>(\<Union>k < t. { set (decode_plan' \<Pi> \<A> k) })"
      by blast
    finally have "set ?\<pi>' = (\<Union>k < t. set (decode_plan' \<Pi> \<A> k))"
      by blast
  } note nb = this
  {
    fix op
    assume "op \<in> set ?\<pi>'"
    then obtain k where "k < t" and "op \<in> set (decode_plan' \<Pi> \<A> k)"
      using nb
      by blast
    moreover have "op \<in> set (decode_plan \<Pi> \<A> t ! k)"
      using calculation
      unfolding decode_plan_def SAT_Plan_Base.decode_plan_def
      by simp
    ultimately have "op \<in> set (operators_of \<Pi>)"
      using decode_plan_step_element_then(1)
      unfolding operators_of_def decode_plan_def
      by blast
  }
  thus ?thesis
    unfolding list_all_iff ListMem_iff operators_of_def
    by blast
qed

text \<open> Given the soundness and completeness of the SATPlan encoding with interfering operator
exclusion \<^term>\<open>\<Phi>\<^sub>\<forall> \<Pi> t\<close>, we can
now conclude this part with showing that for a parallel plan \<^term>\<open>\<pi> \<equiv> \<Phi>\<inverse> \<Pi> \<A> t\<close>
that was decoded from a model \<^term>\<open>\<A>\<close> of \<^term>\<open>\<Phi>\<^sub>\<forall> \<Pi> t\<close> the serialized plan
\<^term>\<open>\<pi>' \<equiv> concat \<pi>\<close> is a serial solution for \<^term>\<open>\<Pi>\<close>. To this end, we have to show that
\begin{itemize}
  \item the state reached by serial execution of \<^term>\<open>\<pi>'\<close> subsumes \<^term>\<open>G\<close>, and
  \item all operators in \<^term>\<open>\<pi>'\<close> are operators contained in \<^term>\<open>\<O>\<close>.
\end{itemize}
While the proof of the latter step is rather straight forward, the proof for the
former requires a bit more work. We use the previously established theorem on serial and parallel
STRIPS equivalence (theorem \ref{isathm:equivalence-parallel-serial-strips-plans}) to show the
serializability of \<^term>\<open>\<pi>\<close> and therefore have to show that \<^term>\<open>G\<close> is subsumed by the last state
of the trace of \<^term>\<open>\<pi>'\<close>
  @{text[display, indent=4] "G \<subseteq>\<^sub>m last (trace_sequential_plan_strips I \<pi>')"}
and moreover that at every step of the parallel plan execution, the parallel operator execution
condition as well as non interference are met
  @{text[display, indent=4] "\<forall>k < length \<pi>. are_all_operators_non_interfering (\<pi> ! k)"}.
\footnote{These propositions are shown in lemmas \texttt{encode\_problem\_forall\_step\_decoded\_plan\_is\_serializable\_ii} and
\texttt{encode\_problem\_forall\_step\_decoded\_plan\_is\_serializable\_i} which have been omitted for
brevity.}
Note that the parallel operator execution condition is implicit in the existence of the parallel
trace for \<^term>\<open>\<pi>\<close> with
  @{text[display, indent=4] "G \<subseteq>\<^sub>m last (trace_parallel_plan_strips I \<pi>)"}
warranted by the soundness of \<^term>\<open>\<Phi>\<^sub>\<forall> \<Pi> t\<close>. \<close>

(* TODO rename encode_problem_with_operator_interference_exclusion_decoded_plan_is_serializable *)
theorem serializable_encoding_decoded_plan_is_serializable:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> \<Pi> t"
  shows "is_serial_solution_for_problem \<Pi> (concat (\<Phi>\<inverse> \<Pi> \<A> t))"
  using encode_problem_forall_step_decoded_plan_is_serializable_i[OF assms]
    encode_problem_forall_step_decoded_plan_is_serializable_ii
  unfolding is_serial_solution_for_problem_def goal_of_def
    initial_of_def decode_plan_def
  by blast

end
