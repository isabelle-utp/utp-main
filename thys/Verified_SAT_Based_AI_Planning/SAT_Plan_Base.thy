(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory SAT_Plan_Base
  imports  "List-Index.List_Index"
    "Propositional_Proof_Systems.Formulas"
    "STRIPS_Semantics"
    "Map_Supplement" "List_Supplement"
    "CNF_Semantics_Supplement" "CNF_Supplement"
begin

\<comment> \<open> Hide constant and notation for \isaname{Orderings.bot_class.bot} (\<open>\<bottom>\<close>) to prevent warnings. \<close>
hide_const (open) Orderings.bot_class.bot
no_notation Orderings.bot_class.bot ("\<bottom>")

\<comment> \<open> Hide constant and notation for \isaname{Transitive_Closure.trancl} (\<open>(_\<^sup>+)\<close>) to prevent
warnings. \<close>
hide_const (open) Transitive_Closure.trancl
no_notation Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999)

\<comment> \<open> Hide constant and notation for \isaname{Relation.converse} (\<open>(_\<^sup>+)\<close>) to prevent
warnings. \<close>
hide_const (open) Relation.converse
no_notation Relation.converse  ("(_\<inverse>)" [1000] 999)

section "The Basic SATPlan Encoding"
text \<open> We now move on to the formalization of the basic SATPlan encoding (see
\autoref{def:basic-sat-plan-encoding-strips-problem}).

The two major results that we will obtain here are the soundness and completeness result outlined
in \autoref{thm:soundness-and-completeness-satplan-base} in
\autoref{sub:soundness-completeness-satplan}.

Let in the following \<open>\<Phi> \<equiv> encode_to_sat \<Pi> t\<close> denote the SATPlan encoding for a STRIPS problem \<open>\<Pi>\<close>
and makespan \<open>t\<close>. Let \<^term>\<open>k < t\<close> and \<open>I \<equiv> (\<Pi>)\<^sub>I\<close> be the initial state of \<open>\<Pi>\<close>, \<open>G \<equiv> (\<Pi>)\<^sub>G\<close> be
its goal state, \<open>\<V> \<equiv> (\<Pi>)\<^sub>\<V>\<close> its variable set, and \<open>\<O> \<equiv> (\<Pi>)\<^sub>\<O>\<close> its operator set. \<close>
subsection "Encoding Function Definitions"
text \<open> Since the SATPlan encoding uses propositional variables for both operators and state
variables of the problem as well as time points, we define a datatype using separate constructors
---\<^term>\<open>State k n\<close> for state variables resp. \<^term>\<open>Operator k n\<close> for operator activation---to
facilitate case distinction.
The natural number values store the time index resp. the indexes of the variable or operator
within their lists in the problem representation.
% TODO Note on why formulas are used instead of CNF (simple representation and good basis; e.g.
% export to cnf lists using CNF_Formulas.cnf_lists) \<close>

datatype  sat_plan_variable =
  State nat nat
  | Operator nat nat

text \<open> A SATPlan formula is a regular propositional formula over SATPlan variables. We add a type
synonym to improve readability. \<close>

type_synonym  sat_plan_formula = "sat_plan_variable formula"

text \<open> We now continue with the concrete definitions used in the implementation of the SATPlan
encoding.  State variables are encoded as literals over SATPlan variables using the \<open>State\<close>
constructor of \isaname{sat_plan_variable}. \<close>

definition  encode_state_variable
  :: "nat \<Rightarrow> nat \<Rightarrow> bool option \<Rightarrow> sat_plan_variable formula"
  where "encode_state_variable t k v \<equiv> case v of
    Some True \<Rightarrow> Atom (State t k)
    | Some False \<Rightarrow> \<^bold>\<not> (Atom (State t k))"

text \<open> The initial state encoding (definition \ref{isadef:initial-state-encoding}) is a conjunction
of state variable encodings \<^term>\<open>A \<equiv> encode_state_variable 0 n b\<close> with \<open>n \<equiv> index vs v\<close> and
\<^term>\<open>b \<equiv> I v = Some True\<close> for all \<^term>\<open>v \<in> \<V>\<close>. As we can see below, the same function but
substituting the initial state with the goal state and zero with the makespan \<^term>\<open>t\<close> produces the
goal state encoding (\ref{isadef:goal-state-encoding}).
Note that both functions construct a conjunction of clauses \<open>A \<^bold>\<or> \<bottom>\<close> for which it
is easy to show that we can normalize to conjunctive normal form (CNF). \<close>

definition  encode_initial_state
  :: "'variable strips_problem \<Rightarrow> sat_plan_variable formula" ("\<Phi>\<^sub>I _" 99)
  where "encode_initial_state \<Pi>
    \<equiv> let I = initial_of \<Pi>
        ; vs = variables_of \<Pi>
      in \<^bold>\<And>(map (\<lambda>v. encode_state_variable 0 (index vs v) (I v) \<^bold>\<or> \<bottom>)
    (filter (\<lambda>v. I v \<noteq> None) vs))"

definition  encode_goal_state
  :: "'variable strips_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula" ("\<Phi>\<^sub>G _" 99)
  where "encode_goal_state \<Pi> t
    \<equiv> let
      vs = variables_of \<Pi>
      ; G = goal_of \<Pi>
    in \<^bold>\<And>(map (\<lambda>v. encode_state_variable t (index vs v) (G v) \<^bold>\<or> \<bottom>)
      (filter (\<lambda>v. G v \<noteq> None) vs))"

text \<open> Operator preconditions are encoded using activation-implies-precondition formulation as
mentioned in \autoref{subsub:basic-sat-plan-encoding}: i.e. for each
operator \<^term>\<open>op \<in> \<O>\<close> and \<^term>\<open>p \<in> set (precondition_of op)\<close> we have to encode
  @{text[display, indent=4] "Atom (Operator k (index ops op)) \<^bold>\<rightarrow> Atom (State k (index vs v))"}
We use the equivalent disjunction in the formalization to simplify conversion to CNF.

\<close>

definition encode_operator_precondition
  :: "'variable strips_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> sat_plan_variable formula"
  where "encode_operator_precondition \<Pi> t op \<equiv> let
      vs = variables_of \<Pi>
      ; ops = operators_of \<Pi>
    in \<^bold>\<And>(map (\<lambda>v.
        \<^bold>\<not> (Atom (Operator t (index ops op))) \<^bold>\<or> Atom (State t (index vs v)))
      (precondition_of op))"

definition  encode_all_operator_preconditions
  :: "'variable strips_problem
    \<Rightarrow> 'variable strips_operator list
    \<Rightarrow> nat
    \<Rightarrow> sat_plan_variable formula"
  where "encode_all_operator_preconditions \<Pi> ops t \<equiv> let
      l = List.product [0..<t] ops
    in foldr (\<^bold>\<and>) (map (\<lambda>(t, op). encode_operator_precondition \<Pi> t op) l) (\<^bold>\<not>\<bottom>)"

text \<open> Analogously to the operator precondition, add and delete effects of operators have to be
implied by operator activation. That being said, we have to encode both positive and negative
effects and the effect must be active at the following time point: i.e.
  @{text[display, indent=4] "Atom (Operator k m) \<^bold>\<rightarrow> Atom (State (Suc k) n)"}
for add effects respectively
  @{text[display, indent=4] "Atom (Operator k m) \<^bold>\<rightarrow> \<^bold>\<not>Atom (State (Suc k) n)"}
for delete effects. We again encode the implications as their equivalent disjunctions in
definition \ref{isadef:operator-effect-encoding}. \<close>

definition  encode_operator_effect
  :: "'variable strips_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator
    \<Rightarrow> sat_plan_variable formula"
  where "encode_operator_effect \<Pi> t op
    \<equiv> let
        vs = variables_of \<Pi>
        ; ops = operators_of \<Pi>
      in \<^bold>\<And>(map (\<lambda>v.
              \<^bold>\<not>(Atom (Operator t (index ops op)))
              \<^bold>\<or> Atom (State (Suc t) (index vs v)))
            (add_effects_of op)
          @ map (\<lambda>v.
              \<^bold>\<not>(Atom (Operator t (index ops op)))
               \<^bold>\<or> \<^bold>\<not> (Atom (State (Suc t) (index vs v))))
            (delete_effects_of op))"

definition encode_all_operator_effects
  :: "'variable strips_problem
    \<Rightarrow> 'variable strips_operator list
    \<Rightarrow> nat
    \<Rightarrow> sat_plan_variable formula"
  where "encode_all_operator_effects \<Pi> ops t
    \<equiv> let l = List.product [0..<t] ops
      in foldr (\<^bold>\<and>) (map (\<lambda>(t, op). encode_operator_effect \<Pi> t op) l) (\<^bold>\<not>\<bottom>)"

definition encode_operators
  :: "'variable strips_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_operators \<Pi> t
    \<equiv> let ops = operators_of \<Pi>
      in encode_all_operator_preconditions \<Pi> ops t \<^bold>\<and> encode_all_operator_effects \<Pi> ops t"

text \<open>

Definitions \ref{isadef:negative-transition-frame-axiom-encoding} and
\ref{isadef:positive-transition-frame-axiom-encoding} similarly encode the negative resp. positive
transition frame axioms as disjunctions.  \<close>

definition  encode_negative_transition_frame_axiom
  :: "'variable strips_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable
    \<Rightarrow> sat_plan_variable formula"
  where "encode_negative_transition_frame_axiom \<Pi> t v
    \<equiv> let vs = variables_of \<Pi>
        ; ops = operators_of \<Pi>
        ; deleting_operators = filter (\<lambda>op. ListMem v (delete_effects_of op)) ops
      in \<^bold>\<not>(Atom (State t (index vs v)))
          \<^bold>\<or> (Atom (State (Suc t) (index vs v))
          \<^bold>\<or> \<^bold>\<Or> (map (\<lambda>op. Atom (Operator t (index ops op))) deleting_operators))"

definition  encode_positive_transition_frame_axiom
  :: "'variable strips_problem
    \<Rightarrow> nat
    \<Rightarrow> 'variable
    \<Rightarrow> sat_plan_variable formula"
  where "encode_positive_transition_frame_axiom \<Pi> t v
    \<equiv> let vs = variables_of \<Pi>
        ; ops = operators_of \<Pi>
        ; adding_operators = filter (\<lambda>op. ListMem v (add_effects_of op)) ops
      in (Atom (State t (index vs v))
          \<^bold>\<or> (\<^bold>\<not>(Atom (State (Suc t) (index vs v)))
          \<^bold>\<or> \<^bold>\<Or>(map (\<lambda>op. Atom (Operator t (index ops op))) adding_operators)))"

definition encode_all_frame_axioms
  :: "'variable strips_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula"
  where "encode_all_frame_axioms \<Pi> t
    \<equiv> let l = List.product [0..<t] (variables_of \<Pi>)
      in \<^bold>\<And>(map (\<lambda>(k, v). encode_negative_transition_frame_axiom \<Pi> k v) l
            @ map (\<lambda>(k, v). encode_positive_transition_frame_axiom \<Pi> k v) l)"

text \<open> Finally, the basic SATPlan encoding is the
conjunction of the initial state, goal state, operator and frame axiom encoding for all time steps.
The functions \isaname{encode_operators} and \isaname{encode_all_frame_axioms}\footnote{Not shown.}
take care of mapping the operator precondition, effect and frame axiom encoding over all possible
combinations of time point and operators resp. time points, variables, and operators. \<close>

definition  encode_problem ("\<Phi> _ _" 99)
  where "encode_problem \<Pi> t
    \<equiv> encode_initial_state \<Pi>
      \<^bold>\<and> (encode_operators \<Pi> t
      \<^bold>\<and> (encode_all_frame_axioms \<Pi> t
      \<^bold>\<and> (encode_goal_state \<Pi> t)))"

subsection "Decoding Function Definitions"
text \<open> Decoding plans from a valuation \<^term>\<open>\<A>\<close> of a
SATPlan encoding entails extracting all activated operators for all
time points except the last one. We implement this by mapping over all \<^term>\<open>k < t\<close>
 and extracting activated operators---i.e. operators for which the model valuates the respective
operator encoding at time \<^term>\<open>k\<close> to true---into a parallel operator (see definition
\ref{isadef:satplan-plan-decoding}).
\footnote{This is handled by function \texttt{decode\_plan'} (not shown).} \<close>

\<comment> \<open> Note that due to the implementation based on lists, we have to address the problem of duplicate
operator declarations in the operator list of the problem. Since \<^term>\<open>index op = index op'\<close> for equal
operators, the parallel operator obtained from \isaname{decode_plan'} will contain
duplicates in case the problem's operator list does. We therefore remove duplicates first using
\<^term>\<open>remdups ops\<close> and then filter out activated operators. \<close>
definition decode_plan'
  :: "'variable strips_problem
    \<Rightarrow> sat_plan_variable valuation
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_operator list"
  where "decode_plan' \<Pi> \<A> i
    \<equiv> let ops = operators_of \<Pi>
        ; vs = map (\<lambda>op. Operator i (index ops op)) (remdups ops)
      in map (\<lambda>v. case v of Operator _ k \<Rightarrow> ops ! k) (filter \<A> vs)"


\<comment> \<open> We decode maps over range \<open>0, \<dots>, t - 1\<close> because the last operator takes effect in \<^term>\<open>t\<close> and
must therefore have been applied in step \<^term>\<open>t - 1\<close>. \<close>

definition  decode_plan
  :: "'variable strips_problem
    \<Rightarrow> sat_plan_variable valuation
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_parallel_plan" ("\<Phi>\<inverse> _ _ _" 99)
  where "decode_plan \<Pi> \<A> t \<equiv> map (decode_plan' \<Pi> \<A>) [0..<t]"

text \<open> Similarly to the operator decoding, we can decode a state at time \<^term>\<open>k\<close> from a valuation
of of the SATPlan encoding \<^term>\<open>\<A>\<close> by constructing a map from list of assignments
\<^term>\<open>(v, \<A> (State k (index vs v)))\<close> for all \<^term>\<open>v \<in> \<V>\<close>. \<close>

definition  decode_state_at
  :: "'variable strips_problem
    \<Rightarrow> sat_plan_variable valuation
    \<Rightarrow> nat
    \<Rightarrow> 'variable strips_state" ("\<Phi>\<^sub>S\<inverse> _ _ _" 99)
  where "decode_state_at \<Pi> \<A> k
    \<equiv> let
      vs = variables_of \<Pi>
      ; state_encoding_to_assignment = \<lambda>v. (v, \<A> (State k (index vs v)))
    in map_of (map state_encoding_to_assignment vs)"

text \<open> We continue by setting up the \isaname{sat_plan} context for the proofs of soundness and
completeness. \<close>

definition encode_transitions ::"'variable strips_problem \<Rightarrow> nat \<Rightarrow> sat_plan_variable formula" ("\<Phi>\<^sub>T _ _" 99) where
  "encode_transitions \<Pi> t
      \<equiv> SAT_Plan_Base.encode_operators \<Pi> t \<^bold>\<and>
        SAT_Plan_Base.encode_all_frame_axioms \<Pi> t"

\<comment> \<open> Immediately proof the sublocale proposition for strips in order to gain access to definitions
and lemmas. \<close>

\<comment> \<open> Setup simp rules. \<close>
lemma   [simp]:
  "encode_transitions \<Pi> t
    = SAT_Plan_Base.encode_operators \<Pi> t \<^bold>\<and>
      SAT_Plan_Base.encode_all_frame_axioms \<Pi> t"
  unfolding encode_problem_def encode_initial_state_def encode_transitions_def
    encode_goal_state_def decode_plan_def decode_state_at_def
  by simp+

context
begin

lemma encode_state_variable_is_lit_plus_if:
  assumes "is_valid_problem_strips \<Pi>"
    and "v \<in> dom s"
  shows "is_lit_plus (encode_state_variable k (index (strips_problem.variables_of \<Pi>) v) (s v))"
proof -
  have "s v \<noteq> None"
    using is_valid_problem_strips_initial_of_dom assms(2)
    by blast
  then consider (s_of_v_is_some_true) "s v = Some True"
    | (s_of_v_is_some_false) "s v = Some False"
    by fastforce
  thus ?thesis
    unfolding encode_state_variable_def
    by (cases, simp+)
qed

lemma is_cnf_encode_initial_state:
  assumes "is_valid_problem_strips \<Pi>"
  shows "is_cnf (\<Phi>\<^sub>I \<Pi>)"
proof -
  let ?I = "(\<Pi>)\<^sub>I"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?l = "map (\<lambda>v. encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>)
    (filter (\<lambda>v. ?I v \<noteq> None) ?vs)"
  {
    fix C
    assume c_in_set_l:"C \<in> set ?l"
    have "set ?l = (\<lambda>v. encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>) `
      set (filter (\<lambda>v. ?I v \<noteq> None) ?vs)"
      using set_map[of "\<lambda>v. encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>"
          "filter (\<lambda>v. ?I v \<noteq> None) ?vs"]
      by blast
    then have "set ?l = (\<lambda>v. encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>) `
      {v \<in> set ?vs. ?I v \<noteq> None}"
      using set_filter[of "\<lambda>v. ?I v \<noteq> None" ?vs]
      by argo
    then obtain v
      where c_is: "C = encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>"
      and v_in_set_vs: "v \<in> set ?vs"
      and I_of_v_is_not_None: "?I v \<noteq> None"
      using c_in_set_l
      by auto
    (* TODO refactor. *)
    {
      have "v \<in> dom ?I"
        using I_of_v_is_not_None
        by blast
      moreover have "is_lit_plus (encode_state_variable 0 (index ?vs v) (?I v))"
        using encode_state_variable_is_lit_plus_if[OF _ calculation] assms(1)
        by blast
      moreover have "is_lit_plus \<bottom>"
        by simp
      ultimately have "is_disj C"
        using c_is
        by force
    }
    hence "is_cnf C"
      unfolding encode_state_variable_def
      using c_is
      by fastforce
  }
  thus ?thesis
    unfolding encode_initial_state_def SAT_Plan_Base.encode_initial_state_def Let_def initial_of_def
    using is_cnf_BigAnd[of ?l]
      by (smt is_cnf_BigAnd)
qed

lemma encode_goal_state_is_cnf:
  assumes "is_valid_problem_strips \<Pi>"
  shows "is_cnf (encode_goal_state \<Pi> t)"
proof -
  let ?I = "(\<Pi>)\<^sub>I"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?l = "map (\<lambda>v. encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>)
      (filter (\<lambda>v. ?G v \<noteq> None) ?vs)"
  {
    fix C
    assume "C \<in> set ?l"
    (* TODO refactor (lemma \<open>encode_goal_state_is_cnf_i\<close>) *)
    moreover {
      have "set ?l = (\<lambda>v. encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>)
        ` set (filter (\<lambda>v. ?G v \<noteq> None) ?vs)"
        unfolding set_map
        by blast
      then have "set ?l = { encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>
        | v. v \<in> set ?vs \<and> ?G v \<noteq> None }"
        by auto
    }
    moreover obtain v where C_is: "C = encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom> "
      and "v \<in> set ?vs"
      and G_of_v_is_not_None: "?G v \<noteq> None"
      using calculation(1)
      by auto
    (* TODO refactor. *)
    moreover {
      have "v \<in> dom ?G"
        using G_of_v_is_not_None
        by blast
      moreover have "is_lit_plus (encode_state_variable t (index ?vs v) (?G v))"
        using assms(1) calculation
        by (simp add: encode_state_variable_is_lit_plus_if)
      moreover have "is_lit_plus \<bottom>"
        by simp
      ultimately have "is_disj C"
        unfolding C_is
        by force
    }
    ultimately have "is_cnf C"
      by simp
  }
  thus ?thesis
    unfolding encode_goal_state_def SAT_Plan_Base.encode_goal_state_def Let_def
    using is_cnf_BigAnd[of ?l]
    by simp
qed

private lemma encode_operator_precondition_is_cnf:
  "is_cnf (encode_operator_precondition \<Pi> k op)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?l = "map (\<lambda>v. \<^bold>\<not> (Atom (Operator k (index ?ops op))) \<^bold>\<or> Atom (State k (index ?vs v)))
    (precondition_of op)"
  {
    have "set ?l = (\<lambda>v. \<^bold>\<not>(Atom (Operator k (index ?ops op))) \<^bold>\<or> Atom (State k (index ?vs v)))
      ` set (precondition_of op)"
      using set_map
      by force
    then have "set ?l = { \<^bold>\<not>(Atom (Operator k (index ?ops op))) \<^bold>\<or> Atom (State k (index ?vs v))
      | v. v \<in> set (precondition_of op) }"
      using setcompr_eq_image[of
        "\<lambda>v. \<^bold>\<not>(Atom (Operator k (index ?ops op))) \<^bold>\<or> Atom (State k (index ?vs v))"
        "\<lambda>v. v \<in> set (precondition_of op)"]
      by simp
  } note set_l_is = this
  {
    fix C
    assume "C \<in> set ?l"
    then obtain v
      where "v \<in> set (precondition_of op)"
      and "C = \<^bold>\<not>(Atom (Operator k (index ?ops op))) \<^bold>\<or> Atom (State k (index ?vs v))"
      using set_l_is
      by blast
    hence "is_cnf C"
      by simp
  }
  thus ?thesis
    unfolding encode_operator_precondition_def
    using is_cnf_BigAnd[of ?l]
    by meson
qed

private lemma set_map_operator_precondition[simp]:
  "set (map (\<lambda>(k, op). encode_operator_precondition \<Pi> k op) (List.product [0..<t] ops))
    = { encode_operator_precondition \<Pi> k op | k op. (k, op) \<in> ({0..<t} \<times> set ops) }"
proof -
  let ?l' = "List.product [0..<t] ops"
  let ?fs = "map (\<lambda>(k, op). encode_operator_precondition \<Pi> k op) ?l'"
  have set_l'_is: "set ?l' = {0..<t} \<times> set ops"
    by simp
  moreover {
    have "set ?fs = (\<lambda>(k, op). encode_operator_precondition \<Pi> k op)
      ` ({0..<t} \<times> set ops)"
      using set_map set_l'_is
      by simp
    also have "\<dots> = { encode_operator_precondition \<Pi> k op | k op. (k, op) \<in> {0..<t} \<times> set ops}"
      using setcompr_eq_image
      by fast
    finally have "set ?fs  = { encode_operator_precondition \<Pi> k op
      | k op. (k, op) \<in> ({0..<t} \<times> set ops) }"
      by blast
  }
  thus ?thesis
    by blast
qed

private lemma is_cnf_encode_all_operator_preconditions:
  "is_cnf (encode_all_operator_preconditions \<Pi> (strips_problem.operators_of \<Pi>) t)"
proof -
  let ?l' = "List.product [0..<t] (strips_problem.operators_of \<Pi>)"
  let ?fs = "map (\<lambda>(k, op). encode_operator_precondition \<Pi> k op) ?l'"
  have "\<forall>f \<in> set ?fs. is_cnf f"
    using encode_operator_precondition_is_cnf
    by fastforce
  thus ?thesis
    unfolding encode_all_operator_preconditions_def
    using is_cnf_foldr_and_if[of ?fs]
    by presburger
qed

(* TODO refactor Appendix *)
private lemma set_map_or[simp]:
  "set (map (\<lambda>v. A v \<^bold>\<or> B v) vs) = { A v \<^bold>\<or> B v | v. v \<in> set vs }"
proof -
  let ?l = "map (\<lambda>v. A v \<^bold>\<or> B v) vs"
  have "set ?l = (\<lambda>v. A v \<^bold>\<or> B v) ` set vs"
    using set_map
    by force
  thus ?thesis
    using setcompr_eq_image
    by auto
qed

private lemma encode_operator_effects_is_cnf_i:
  "is_cnf (\<^bold>\<And>(map (\<lambda>v. (\<^bold>\<not> (Atom (Operator t (index (strips_problem.operators_of \<Pi>) op))))
    \<^bold>\<or> Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))) (add_effects_of op)))"
proof -
  let ?fs = "map (\<lambda>v. \<^bold>\<not> (Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
    \<^bold>\<or> Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))) (add_effects_of op)"
  {
    fix C
    assume "C \<in> set ?fs"
    then obtain v
      where "v \<in> set (add_effects_of op)"
        and "C = \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
          \<^bold>\<or> Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))"
      by auto
    hence "is_cnf C"
      by fastforce
  }
  thus ?thesis
    using is_cnf_BigAnd
    by blast
qed

private lemma encode_operator_effects_is_cnf_ii:
  "is_cnf (\<^bold>\<And>(map (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
    \<^bold>\<or> \<^bold>\<not>(Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v)))) (delete_effects_of op)))"
proof -
  let ?fs = "map (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
    \<^bold>\<or> \<^bold>\<not>(Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v)))) (delete_effects_of op)"
  {
    fix C
    assume "C \<in> set ?fs"
    then obtain v
      where "v \<in> set (delete_effects_of op)"
        and "C = \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
          \<^bold>\<or> \<^bold>\<not>(Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v)))"
      by auto
    hence "is_cnf C"
      by fastforce
  }
  thus ?thesis
    using is_cnf_BigAnd
    by blast
qed

private lemma encode_operator_effect_is_cnf:
  shows "is_cnf (encode_operator_effect \<Pi> t op)"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?fs = "map (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index ?ops op)))
      \<^bold>\<or> Atom (State (Suc t) (index ?vs v)))
    (add_effects_of op)"
    and ?fs' = "map (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index ?ops op)))
        \<^bold>\<or> \<^bold>\<not>(Atom (State (Suc t) (index ?vs v))))
      (delete_effects_of op)"
  have "encode_operator_effect \<Pi> t op = \<^bold>\<And>(?fs @ ?fs')"
    unfolding encode_operator_effect_def[of \<Pi> t op]
    by metis
  moreover {
    have "\<forall>f \<in> set ?fs. is_cnf f" "\<forall>f \<in> set ?fs'. is_cnf f"
      using encode_operator_effects_is_cnf_i[of t \<Pi> op]
        encode_operator_effects_is_cnf_ii[of t \<Pi> op]
      by (simp+)
    (* TODO slow. *)
    hence "\<forall>f \<in> set (?fs @ ?fs'). is_cnf f"
      by auto
  }
  ultimately show ?thesis
    using is_cnf_BigAnd[of "?fs @ ?fs'"]
    by presburger
qed

private lemma set_map_encode_operator_effect[simp]:
  "set (map (\<lambda>(t, op). encode_operator_effect \<Pi> t op) (List.product [0..<t]
      (strips_problem.operators_of \<Pi>)))
    = { encode_operator_effect \<Pi> k op
      | k op. (k, op) \<in> ({0..<t} \<times> set (strips_problem.operators_of \<Pi>)) }"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?fs = "map (\<lambda>(t, op). encode_operator_effect \<Pi> t op) (List.product [0..<t] ?ops)"
  have "set ?fs = (\<lambda>(t, op). encode_operator_effect \<Pi> t op) ` ({0..<t} \<times> set ?ops)"
    unfolding encode_operator_effect_def[of \<Pi> t]
    by force
  thus ?thesis
    using setcompr_eq_image[of "\<lambda>(t, op). encode_operator_effect \<Pi> t op"
        "\<lambda>(k, op). (k, op) \<in> {0..<t} \<times> set ?ops"]
    by force
qed

private lemma encode_all_operator_effects_is_cnf:
  assumes "is_valid_problem_strips \<Pi>"
  shows "is_cnf (encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t)"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  let ?l = "List.product [0..<t] ?ops"
  let ?fs = "map (\<lambda>(t, op). encode_operator_effect \<Pi> t op) ?l"
  have "\<forall>f \<in> set ?fs. is_cnf f"
    using encode_operator_effect_is_cnf
    by force
  thus ?thesis
    unfolding encode_all_operator_effects_def
    using is_cnf_foldr_and_if[of ?fs]
    by presburger
qed

lemma encode_operators_is_cnf:
  assumes "is_valid_problem_strips \<Pi>"
  shows "is_cnf (encode_operators \<Pi> t)"
  unfolding encode_operators_def
  using is_cnf_encode_all_operator_preconditions[of \<Pi> t]
    encode_all_operator_effects_is_cnf[OF assms, of t]
    is_cnf.simps(1)[of "encode_all_operator_preconditions \<Pi> (strips_problem.operators_of \<Pi>) t"
      "encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t"]
  by meson

\<comment> \<open> Simp flag alone did not do it, so we have to assign a name to this lemma as well. \<close>
private lemma set_map_to_operator_atom[simp]:
  "set (map (\<lambda>op. Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
      (filter (\<lambda>op. ListMem v vs) (strips_problem.operators_of \<Pi>)))
    = { Atom (Operator t (index (strips_problem.operators_of \<Pi>) op))
      | op. op \<in> set (strips_problem.operators_of \<Pi>) \<and> v \<in> set vs }"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  {
    have "set (filter (\<lambda>op. ListMem v vs) ?ops)
      = { op \<in> set ?ops. ListMem v vs }"
      using set_filter
      by force
    then have "set (filter (\<lambda>op. ListMem v vs) ?ops)
      = { op. op \<in> set ?ops \<and> v \<in> set vs }"
      using ListMem_iff[of v]
      by blast
  }
  then have "set (map (\<lambda>op. Atom (Operator t (index ?ops op)))
      (filter (\<lambda>op. ListMem v vs) ?ops))
    = (\<lambda>op. Atom (Operator t (index ?ops op))) ` { op \<in> set ?ops. v \<in> set vs }"
    using set_map[of "\<lambda>op. Atom (Operator t (index ?ops op))"]
    by presburger
  thus ?thesis
    by blast
qed

(* TODO refactor \<open>Formula_Supplement\<close> *)
lemma is_disj_big_or_if:
  assumes "\<forall>f \<in> set fs. is_lit_plus f"
  shows "is_disj \<^bold>\<Or>fs"
  using assms
proof (induction fs)
  case (Cons f fs)
  have "is_lit_plus f"
    using Cons.prems
    by simp
  moreover have "is_disj \<^bold>\<Or>fs"
    using Cons
    by fastforce
  ultimately show ?case
    by simp
qed simp

lemma is_cnf_encode_negative_transition_frame_axiom:
  shows "is_cnf (encode_negative_transition_frame_axiom \<Pi> t v)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?deleting = "filter (\<lambda>op. ListMem v (delete_effects_of op)) ?ops"
  let ?fs = "map (\<lambda>op. Atom (Operator t (index ?ops op))) ?deleting"
    and ?A = "(\<^bold>\<not>(Atom (State t (index ?vs v))))"
    and ?B = "Atom (State (Suc t) (index ?vs v))"
  {
    fix f
    assume "f \<in> set ?fs"
    (* TODO slow. *)
    then obtain op
      where "op \<in> set ?ops"
        and "v \<in> set (delete_effects_of op)"
        and "f = Atom (Operator t (index ?ops op))"
      using set_map_to_operator_atom[of t \<Pi> v]
      by fastforce
    hence "is_lit_plus f"
      by simp
  } note nb = this
  {
    have "is_disj \<^bold>\<Or>?fs"
      using is_disj_big_or_if nb
      by blast
    then have "is_disj (?B \<^bold>\<or> \<^bold>\<Or>?fs)"
      by force
    then have "is_disj (?A \<^bold>\<or> (?B \<^bold>\<or> \<^bold>\<Or>?fs))"
      by fastforce
    hence "is_cnf (?A \<^bold>\<or> (?B \<^bold>\<or> \<^bold>\<Or>?fs))"
      by fastforce
  }
  thus ?thesis
    unfolding encode_negative_transition_frame_axiom_def
    by meson
qed

lemma is_cnf_encode_positive_transition_frame_axiom:
  shows "is_cnf (encode_positive_transition_frame_axiom \<Pi> t v)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?adding = "filter (\<lambda>op. ListMem v (add_effects_of op)) ?ops"
  let ?fs = "map (\<lambda>op. Atom (Operator t (index ?ops op))) ?adding"
    and ?A = "Atom (State t (index ?vs v))"
    and ?B = "\<^bold>\<not>(Atom (State (Suc t) (index ?vs v)))"
  {
    fix f
    assume "f \<in> set ?fs"
    (* TODO slow. *)
    then obtain op
      where "op \<in> set ?ops"
        and "v \<in> set (add_effects_of op)"
        and "f = Atom (Operator t (index ?ops op))"
      using set_map_to_operator_atom[of t \<Pi> v]
      by fastforce
    hence "is_lit_plus f"
      by simp
  } note nb = this
  {
    have "is_disj \<^bold>\<Or>?fs"
      using is_disj_big_or_if nb
      by blast
    then have "is_disj (?B \<^bold>\<or> \<^bold>\<Or>?fs)"
      by force
    then have "is_disj (?A \<^bold>\<or> (?B \<^bold>\<or> \<^bold>\<Or>?fs))"
      by fastforce
    hence "is_cnf (?A \<^bold>\<or> (?B \<^bold>\<or> \<^bold>\<Or>?fs))"
      by fastforce
  }
  thus ?thesis
    unfolding encode_positive_transition_frame_axiom_def
    by meson
qed

private lemma encode_all_frame_axioms_set[simp]:
  "set (map (\<lambda>(k, v). encode_negative_transition_frame_axiom \<Pi> k v)
        (List.product [0..<t] (strips_problem.variables_of \<Pi>))
      @ (map (\<lambda>(k, v). encode_positive_transition_frame_axiom \<Pi> k v)
        (List.product [0..<t] (strips_problem.variables_of \<Pi>))))
    = { encode_negative_transition_frame_axiom \<Pi> k v
        | k v. (k, v) \<in> ({0..<t} \<times> set (strips_problem.variables_of \<Pi>)) }
      \<union> { encode_positive_transition_frame_axiom \<Pi> k v
        | k v. (k, v) \<in> ({0..<t} \<times> set (strips_problem.variables_of \<Pi>)) }"
proof -
  let ?l = "List.product [0..<t] (strips_problem.variables_of \<Pi>)"
  let ?A = "(\<lambda>(k, v). encode_negative_transition_frame_axiom \<Pi> k v) ` set ?l"
    and ?B = "(\<lambda>(k, v). encode_positive_transition_frame_axiom \<Pi> k v) ` set ?l"
    and ?fs = "map (\<lambda>(k, v). encode_negative_transition_frame_axiom \<Pi> k v) ?l
      @ (map (\<lambda>(k, v). encode_positive_transition_frame_axiom \<Pi> k v) ?l)"
    and ?vs = "strips_problem.variables_of \<Pi>"
  have set_l_is: "set ?l = {0..<t} \<times> set ?vs"
    by simp
  have "set ?fs = ?A \<union> ?B"
    using set_append
    by force
  moreover have "?A = { encode_negative_transition_frame_axiom \<Pi> k v
    | k v. (k, v) \<in> ({0..<t} \<times> set ?vs) }"
    using set_l_is setcompr_eq_image[of "\<lambda>(k, v). encode_negative_transition_frame_axiom \<Pi> k v"
        "\<lambda>(k, v). (k, v) \<in> ({0..<t} \<times> set ?vs)"]
    by fast
  moreover have "?B = { encode_positive_transition_frame_axiom \<Pi> k v
    | k v. (k, v) \<in> ({0..<t} \<times> set ?vs) }"
    using set_l_is setcompr_eq_image[of "\<lambda>(k, v). encode_positive_transition_frame_axiom \<Pi> k v"
        "\<lambda>(k, v). (k, v) \<in> ({0..<t} \<times> set ?vs)"]
    by fast
  ultimately show ?thesis
    by argo
qed

(* rename \<open>is_cnf_encode_all_frame_axioms\<close>. *)
lemma encode_frame_axioms_is_cnf:
  shows "is_cnf (encode_all_frame_axioms \<Pi> t)"
proof -
  let ?l = "List.product [0..<t] (strips_problem.variables_of \<Pi>)"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?A = "{ encode_negative_transition_frame_axiom \<Pi> k v
    | k v. (k, v) \<in> ({0..<t} \<times> set ?vs) }"
    and ?B = "{ encode_positive_transition_frame_axiom \<Pi> k v
    | k v. (k, v) \<in> ({0..<t} \<times> set ?vs) }"
    and ?fs = "map (\<lambda>(k, v). encode_negative_transition_frame_axiom \<Pi> k v) ?l
      @ (map (\<lambda>(k, v). encode_positive_transition_frame_axiom \<Pi> k v) ?l)"
  {
    fix f
    assume "f \<in> set ?fs"
    (* TODO slow. *)
    then consider (f_encodes_negative_frame_axiom) "f \<in> ?A"
      | (f_encodes_positive_frame_axiom) "f \<in> ?B"
      by fastforce
    hence "is_cnf f"
      using is_cnf_encode_negative_transition_frame_axiom
        is_cnf_encode_positive_transition_frame_axiom
      by (smt mem_Collect_eq)
  }
  thus ?thesis
    unfolding encode_all_frame_axioms_def
    using is_cnf_BigAnd[of ?fs]
    by meson
qed

lemma is_cnf_encode_problem:
  assumes "is_valid_problem_strips \<Pi>"
  shows "is_cnf (\<Phi> \<Pi> t)"
proof -
  have "is_cnf (\<Phi>\<^sub>I \<Pi>)"
    using is_cnf_encode_initial_state assms
    by auto
  moreover have "is_cnf (encode_goal_state \<Pi> t)"
    using encode_goal_state_is_cnf[OF assms]
    by simp
  moreover have "is_cnf (encode_operators \<Pi> t \<^bold>\<and> encode_all_frame_axioms \<Pi> t)"
    using encode_operators_is_cnf[OF assms] encode_frame_axioms_is_cnf
    unfolding encode_transitions_def
    by simp
  ultimately show ?thesis
    unfolding encode_problem_def SAT_Plan_Base.encode_problem_def
      encode_transitions_def encode_initial_state_def[symmetric] encode_goal_state_def[symmetric]
    by simp
qed

lemma encode_problem_has_model_then_also_partial_encodings:
  assumes "\<A> \<Turnstile> SAT_Plan_Base.encode_problem \<Pi> t"
  shows "\<A> \<Turnstile> SAT_Plan_Base.encode_initial_state \<Pi>"
    and "\<A> \<Turnstile> SAT_Plan_Base.encode_goal_state \<Pi> t"
    and "\<A> \<Turnstile> SAT_Plan_Base.encode_operators \<Pi> t"
    and "\<A> \<Turnstile> SAT_Plan_Base.encode_all_frame_axioms \<Pi> t"
  using assms
  unfolding SAT_Plan_Base.encode_problem_def
  by simp+

lemma cnf_of_encode_problem_structure:
  shows "cnf (SAT_Plan_Base.encode_initial_state \<Pi>)
    \<subseteq> cnf (SAT_Plan_Base.encode_problem \<Pi> t)"
    and "cnf (SAT_Plan_Base.encode_goal_state \<Pi> t)
      \<subseteq> cnf (SAT_Plan_Base.encode_problem \<Pi> t)"
    and "cnf (SAT_Plan_Base.encode_operators \<Pi> t)
      \<subseteq> cnf (SAT_Plan_Base.encode_problem \<Pi> t)"
    and "cnf (SAT_Plan_Base.encode_all_frame_axioms \<Pi> t)
      \<subseteq> cnf (SAT_Plan_Base.encode_problem \<Pi> t)"
  unfolding SAT_Plan_Base.encode_problem_def
    SAT_Plan_Base.encode_problem_def[of \<Pi> t] SAT_Plan_Base.encode_initial_state_def[of \<Pi>]
    SAT_Plan_Base.encode_goal_state_def[of \<Pi> t] SAT_Plan_Base.encode_operators_def
    SAT_Plan_Base.encode_all_frame_axioms_def[of \<Pi> t]
  subgoal by auto
  subgoal by force
  subgoal by auto
  subgoal by force
  done

\<comment> \<open> A technical lemma which shows a simpler form of the CNF of the initial state encoding. \<close>
(* TODO generalize for more encodings? *)
private lemma cnf_of_encode_initial_state_set_i:
  shows "cnf (\<Phi>\<^sub>I \<Pi>) = \<Union> { cnf (encode_state_variable 0
    (index (strips_problem.variables_of \<Pi>) v) (((\<Pi>)\<^sub>I) v))
      | v. v \<in> set (strips_problem.variables_of \<Pi>) \<and> ((\<Pi>)\<^sub>I) v \<noteq> None }"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?I = "strips_problem.initial_of \<Pi>"
  let ?ls = "map (\<lambda>v. encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>)
    (filter (\<lambda>v. ?I v \<noteq> None) ?vs)"
  {
    have "cnf ` set ?ls = cnf ` (\<lambda>v. encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>)
      ` set (filter (\<lambda>v. ?I v \<noteq> None) ?vs)"
      using set_map[of "\<lambda>v. encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>"]
      by presburger
    also have "\<dots> = (\<lambda>v. cnf (encode_state_variable 0 (index ?vs v) (?I v) \<^bold>\<or> \<bottom>))
      ` set (filter (\<lambda>v. ?I v \<noteq> None) ?vs)"
      using image_comp
      by blast
    also have "\<dots> = (\<lambda>v. cnf (encode_state_variable 0 (index ?vs v) (?I v)))
      ` { v \<in> set ?vs. ?I v \<noteq> None }"
      using set_filter[of "\<lambda>v. ?I v \<noteq> None" ?vs]
      by auto
    finally have "cnf ` set ?ls = { cnf (encode_state_variable 0 (index ?vs v) (?I v))
      | v. v \<in> set ?vs \<and> ?I v \<noteq> None }"
      using setcompr_eq_image[of "\<lambda>v. cnf (encode_state_variable 0 (index ?vs v) (?I v))"]
      by presburger
  }
  moreover have "cnf (\<Phi>\<^sub>I \<Pi>) = \<Union> (cnf ` set ?ls)"
    unfolding encode_initial_state_def SAT_Plan_Base.encode_initial_state_def
    using cnf_BigAnd[of ?ls]
    by meson
  ultimately show ?thesis
    by auto
qed

\<comment> \<open> A simplification lemma for the above one. \<close>
(* TODO Replace above lemma with this?. *)
corollary cnf_of_encode_initial_state_set_ii:
  assumes "is_valid_problem_strips \<Pi>"
  shows "cnf (\<Phi>\<^sub>I \<Pi>) = (\<Union>v \<in> set (strips_problem.variables_of \<Pi>). {{
    literal_formula_to_literal (encode_state_variable 0 (index (strips_problem.variables_of \<Pi>) v)
      (strips_problem.initial_of \<Pi> v)) }})"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?I = "strips_problem.initial_of \<Pi>"
  have nb\<^sub>1: "{ v. v \<in> set ?vs \<and> ?I v \<noteq> None } = set ?vs"
    using is_valid_problem_strips_initial_of_dom assms(1)
    by auto
  (* TODO generalize and refactor. *)
  {
    fix v
    assume "v \<in> set ?vs"
    then have "?I v \<noteq> None"
      using is_valid_problem_strips_initial_of_dom assms(1)
      by auto
    then consider (I_v_is_Some_True) "?I v = Some True"
      | (I_v_is_Some_False) "?I v = Some False"
      by fastforce
    hence "cnf (encode_state_variable 0 (index ?vs v) (?I v))
      = {{ literal_formula_to_literal (encode_state_variable 0 (index ?vs v) (?I v)) }}"
      unfolding encode_state_variable_def
      by (cases, simp+)
  } note nb\<^sub>2 = this
  {
    have "{ cnf (encode_state_variable 0 (index ?vs v) (?I v)) | v. v \<in> set ?vs \<and> ?I v \<noteq> None }
       = (\<lambda>v. cnf (encode_state_variable 0 (index ?vs v) (?I v))) ` set ?vs"
    using setcompr_eq_image[of "\<lambda>v. cnf (encode_state_variable 0 (index ?vs v) (?I v))"
        "\<lambda>v. v \<in> set ?vs \<and> ?I v \<noteq> None"] using nb\<^sub>1
    by presburger
    hence "{ cnf (encode_state_variable 0 (index ?vs v) (?I v)) | v. v \<in> set ?vs \<and> ?I v \<noteq> None }
      = (\<lambda>v. {{ literal_formula_to_literal (encode_state_variable 0 (index ?vs v) (?I v)) }})
        ` set ?vs"
      using nb\<^sub>2
      by force
  }
  thus ?thesis
    using cnf_of_encode_initial_state_set_i
    by (smt Collect_cong)
qed

(* TODO \<open>\<exists>!\<close> is superfluous now? rm? + Above lemma basically covers this one. *)
lemma  cnf_of_encode_initial_state_set:
  assumes "is_valid_problem_strips \<Pi>"
    and "v \<in> dom (strips_problem.initial_of \<Pi>)"
  shows "strips_problem.initial_of \<Pi> v = Some True \<longrightarrow> (\<exists>!C. C \<in> cnf (\<Phi>\<^sub>I \<Pi>)
      \<and> C = { (State 0 (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ })"
    and "strips_problem.initial_of \<Pi> v = Some False \<longrightarrow> (\<exists>!C. C \<in> cnf (\<Phi>\<^sub>I \<Pi>)
      \<and> C = { (State 0 (index (strips_problem.variables_of \<Pi>) v))\<inverse> })"
proof -
  let ?I = "(\<Pi>)\<^sub>I"
  let ?vs = "strips_problem.variables_of \<Pi>"
  let ?\<Phi>\<^sub>I = "\<Phi>\<^sub>I \<Pi>"
  have nb\<^sub>1: "cnf (\<Phi>\<^sub>I \<Pi>) = \<Union> { cnf (encode_state_variable 0 (index ?vs v)
      (strips_problem.initial_of \<Pi> v)) | v. v \<in> set ?vs \<and> ?I v \<noteq> None }"
    using cnf_of_encode_initial_state_set_i
    by blast
  {
    have "v \<in> set ?vs"
      using is_valid_problem_strips_initial_of_dom assms(1, 2)
      by blast
    hence "v \<in> { v. v \<in> set ?vs \<and> ?I v \<noteq> None }"
      using assms(2)
      by auto
  } note nb\<^sub>2 = this
  show "strips_problem.initial_of \<Pi> v = Some True \<longrightarrow> (\<exists>!C. C \<in> cnf (\<Phi>\<^sub>I \<Pi>)
      \<and> C = { (State 0 (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ })"
    and "strips_problem.initial_of \<Pi> v = Some False \<longrightarrow> (\<exists>!C. C \<in> cnf (\<Phi>\<^sub>I \<Pi>)
      \<and> C = { (State 0 (index (strips_problem.variables_of \<Pi>) v))\<inverse> })"
    proof (auto)
      assume i_v_is_some_true: "strips_problem.initial_of \<Pi> v = Some True"
      then have "{ (State 0 (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }
        \<in> cnf (encode_state_variable 0 (index (strips_problem.variables_of \<Pi>) v) (?I v))"
        unfolding encode_state_variable_def
        using i_v_is_some_true
        by auto
      thus "{ (State 0 (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }
        \<in> cnf (\<Phi>\<^sub>I \<Pi>)"
        using nb\<^sub>1 nb\<^sub>2
        by auto
    next
      assume i_v_is_some_false: "strips_problem.initial_of \<Pi> v = Some False"
      then have "{ (State 0 (index (strips_problem.variables_of \<Pi>) v))\<inverse> }
        \<in> cnf (encode_state_variable 0 (index (strips_problem.variables_of \<Pi>) v) (?I v))"
        unfolding encode_state_variable_def
        using i_v_is_some_false
        by auto
      thus "{ (State 0 (index (strips_problem.variables_of \<Pi>) v))\<inverse> }
        \<in> cnf (\<Phi>\<^sub>I \<Pi>)"
        using nb\<^sub>1 nb\<^sub>2
        by auto
    qed
qed

lemma cnf_of_operator_encoding_structure:
  "cnf (encode_operators \<Pi> t) = cnf (encode_all_operator_preconditions \<Pi>
      (strips_problem.operators_of \<Pi>) t)
    \<union> cnf (encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t)"
  unfolding encode_operators_def
  using cnf.simps(5)
  by metis

corollary cnf_of_operator_precondition_encoding_subset_encoding:
  "cnf (encode_all_operator_preconditions \<Pi> (strips_problem.operators_of \<Pi>) t)
    \<subseteq> cnf (\<Phi> \<Pi> t)"
  using cnf_of_operator_encoding_structure cnf_of_encode_problem_structure subset_trans
  unfolding encode_problem_def
  by blast

(* TODO refactor \<open>CNF_Supplement\<close> *)
lemma  cnf_foldr_and[simp]:
  "cnf (foldr (\<^bold>\<and>) fs (\<^bold>\<not>\<bottom>)) = (\<Union>f \<in> set fs. cnf f)"
proof (induction fs)
  case (Cons f fs)
  have ih: "cnf (foldr (\<^bold>\<and>) fs (\<^bold>\<not>\<bottom>)) = (\<Union>f \<in> set fs. cnf f)"
    using Cons.IH
    by blast
  {
    have "cnf (foldr (\<^bold>\<and>) (f # fs) (\<^bold>\<not>\<bottom>)) = cnf (f \<^bold>\<and> foldr (\<^bold>\<and>) fs (\<^bold>\<not>\<bottom>))"
      by simp
    also have "\<dots> = cnf f \<union> cnf (foldr (\<^bold>\<and>) fs (\<^bold>\<not>\<bottom>))"
      by force
    finally have "cnf (foldr (\<^bold>\<and>) (f # fs) (\<^bold>\<not>\<bottom>)) = cnf f \<union> (\<Union>f \<in> set fs. cnf f)"
      using ih
      by argo
  }
  thus ?case
    by auto
qed simp

(* TODO rm (unused)? *)
private lemma cnf_of_encode_operator_precondition[simp]:
  "cnf (encode_operator_precondition \<Pi> t op) = (\<Union>v \<in> set (precondition_of op).
    {{(Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
      , (State t (index (strips_problem.variables_of \<Pi>) v))\<^sup>+}})"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<Phi>\<^sub>P = "encode_operator_precondition \<Pi> t op"
  let ?fs = "map (\<lambda>v. \<^bold>\<not> (Atom (Operator t (index ?ops op))) \<^bold>\<or> Atom (State t (index ?vs v)))
    (precondition_of op)"
    and ?A = "(\<lambda>v. \<^bold>\<not> (Atom (Operator t (index ?ops op))) \<^bold>\<or> Atom (State t (index ?vs v)))
      ` set (precondition_of op)"
  have "cnf (encode_operator_precondition \<Pi> t op) = cnf (\<^bold>\<And>?fs)"
    unfolding encode_operator_precondition_def
    by presburger
  also have "\<dots> = \<Union> (cnf ` set ?fs)"
    using cnf_BigAnd
    by blast
  also have "\<dots> = \<Union>(cnf ` ?A)"
    using set_map[of "\<lambda>v. \<^bold>\<not> (Atom (Operator t (index ?ops op))) \<^bold>\<or> Atom (State t (index ?vs v))"
        "precondition_of op"]
    by argo
  also have "\<dots> = (\<Union>v \<in> set (precondition_of op).
    cnf (\<^bold>\<not>(Atom (Operator t (index ?ops op))) \<^bold>\<or> Atom (State t (index ?vs v))))"
    by blast
  (* TODO slow. *)
  finally show ?thesis
    by auto
qed

(* TODO Shorten proof. *)
lemma cnf_of_encode_all_operator_preconditions_structure[simp]:
  "cnf (encode_all_operator_preconditions \<Pi> (strips_problem.operators_of \<Pi>) t)
    = (\<Union>(t, op) \<in> ({..<t} \<times> set (operators_of \<Pi>)).
      (\<Union>v \<in> set (precondition_of op).
        {{(Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
          , (State t (index (strips_problem.variables_of \<Pi>) v))\<^sup>+}}))"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?l = "List.product [0..<t] ?ops"
    and ?\<Phi>\<^sub>P = "encode_all_operator_preconditions \<Pi> (strips_problem.operators_of \<Pi>) t"
  let ?A = "set (map (\<lambda>(t, op). encode_operator_precondition \<Pi> t op) ?l)"
  {
    have "set ?l = {0..<t} \<times> set ((\<Pi>)\<^sub>\<O>)"
      by auto
    then have "?A = (\<lambda>(t, op). encode_operator_precondition \<Pi> t op) ` ({0..<t} \<times> set ((\<Pi>)\<^sub>\<O>))"
      using set_map
      by force
  } note nb = this
  have "cnf ?\<Phi>\<^sub>P = cnf (foldr (\<^bold>\<and>) (map (\<lambda>(t, op). encode_operator_precondition \<Pi> t op) ?l) (\<^bold>\<not>\<bottom>))"
    unfolding encode_all_operator_preconditions_def
    by presburger
  also have "\<dots> = (\<Union>f \<in> ?A. cnf f)"
    by simp
  (* TODO slow. *)
  also have "\<dots> = (\<Union>(k, op) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<O>)).
    cnf (encode_operator_precondition \<Pi> k op))"
    using nb
    by fastforce
  (* TODO very slow. *)
  finally show ?thesis
     by fastforce
 qed

corollary cnf_of_encode_all_operator_preconditions_contains_clause_if:
  fixes \<Pi>::"'variable STRIPS_Representation.strips_problem"
  assumes "is_valid_problem_strips (\<Pi>::'variable STRIPS_Representation.strips_problem)"
    and "k < t"
    and "op \<in> set ((\<Pi>)\<^sub>\<O>)"
    and "v \<in> set (precondition_of op)"
  shows "{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
    , (State k (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }
  \<in> cnf (encode_all_operator_preconditions \<Pi> (strips_problem.operators_of \<Pi>) t)"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?\<Phi>\<^sub>P = "encode_all_operator_preconditions \<Pi> ?ops t"
    and ?C = "{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
      , (State k (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }"
  {
    have nb: "(k, op) \<in> {..<t} \<times> set ((\<Pi>)\<^sub>\<O>)"
      using assms(2, 3)
      by blast
    moreover {
      have "?C \<in> (\<Union>v\<in>set (precondition_of op).
        {{(Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>,
          (State k (index (strips_problem.variables_of \<Pi>) v))\<^sup>+}})"
        using UN_iff[where A="set (precondition_of op)"
          and B="\<lambda>v. {{(Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>,
          (State t (index (strips_problem.variables_of \<Pi>) v))\<^sup>+}}"] assms(4)
        by blast
      hence "\<exists>x\<in>{..<t} \<times> set ((\<Pi>)\<^sub>\<O>).
        ?C \<in> (case x of (k, op) \<Rightarrow> \<Union>v\<in>set (precondition_of op).
        {{(Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>,
          (State k (index (strips_problem.variables_of \<Pi>) v))\<^sup>+}})"
        using nb
        by blast
    }
    ultimately have "?C \<in> (\<Union>(t, op) \<in> ({..<t} \<times> set ((\<Pi>)\<^sub>\<O>)).
      (\<Union>v \<in> set (precondition_of op).
        {{ (Operator t (index ?ops op))\<inverse>, (State t (index ?vs v))\<^sup>+ }}))"
      by blast
  }
  thus ?thesis
    using cnf_of_encode_all_operator_preconditions_structure[of \<Pi> t]
    by argo
qed

corollary cnf_of_encode_all_operator_effects_subset_cnf_of_encode_problem:
  "cnf (encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t)
    \<subseteq> cnf (\<Phi> \<Pi> t)"
  using cnf_of_encode_problem_structure(3) cnf_of_operator_encoding_structure
  unfolding encode_problem_def
  by blast

private lemma cnf_of_encode_operator_effect_structure[simp]:
  "cnf (encode_operator_effect \<Pi> t op)
    = (\<Union>v \<in> set (add_effects_of op). {{ (Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
        , (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }})
      \<union> (\<Union>v \<in> set (delete_effects_of op).
        {{ (Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
          , (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }})"
proof -
  let ?fs\<^sub>1 = "map (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
    \<^bold>\<or> Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v)))
    (add_effects_of op)"
    and ?fs\<^sub>2 = "map (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
      \<^bold>\<or> \<^bold>\<not> (Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))))
      (delete_effects_of op)"
  {
    have "cnf ` set ?fs\<^sub>1 = cnf
        ` (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
      \<^bold>\<or> Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))) ` set (add_effects_of op)"
      using set_map
      by force
    also have "\<dots> = (\<lambda>v. cnf (\<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
      \<^bold>\<or> Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))))
        ` set (add_effects_of op)"
      using image_comp
      by blast
    (* TODO slow. *)
    finally have "cnf ` set ?fs\<^sub>1 = (\<lambda>v. {{ (Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
      , (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }}) ` set (add_effects_of op)"
      by auto
  } note nb\<^sub>1 = this
  {
    have "cnf ` set ?fs\<^sub>2 = cnf ` (\<lambda>v. \<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
      \<^bold>\<or> \<^bold>\<not>(Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))))
        ` set (delete_effects_of op)"
      using set_map
      by force
    also have "\<dots> = (\<lambda>v. cnf (\<^bold>\<not>(Atom (Operator t (index (strips_problem.operators_of \<Pi>) op)))
      \<^bold>\<or> \<^bold>\<not> (Atom (State (Suc t) (index (strips_problem.variables_of \<Pi>) v)))))
        ` set (delete_effects_of op)"
      using image_comp
      by blast
    (* TODO slow. *)
    finally have "cnf ` set ?fs\<^sub>2 = (\<lambda>v. {{ (Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
      , (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }})
        ` set (delete_effects_of op)"
      by auto
  } note nb\<^sub>2 = this
  {
    have "cnf (encode_operator_effect \<Pi> t op) = \<Union>(cnf ` set (?fs\<^sub>1 @ ?fs\<^sub>2))"
      unfolding encode_operator_effect_def
      using cnf_BigAnd[of "?fs\<^sub>1 @ ?fs\<^sub>2"]
      by meson
    also have "\<dots> = \<Union>(cnf ` set ?fs\<^sub>1 \<union> cnf ` set ?fs\<^sub>2)"
      using set_append[of "?fs\<^sub>1" "?fs\<^sub>2"] image_Un[of cnf "set ?fs\<^sub>1" "set ?fs\<^sub>2"]
      by argo
    also have "\<dots> = \<Union>(cnf ` set ?fs\<^sub>1) \<union> \<Union>(cnf ` set ?fs\<^sub>2)"
      using Union_Un_distrib[of "cnf ` set ?fs\<^sub>1" "cnf ` set ?fs\<^sub>2"]
      by argo
    (* TODO slow. *)
    finally have "cnf (encode_operator_effect \<Pi> t op)
        = (\<Union>v \<in> set (add_effects_of op).
          {{ (Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
            , (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }})
        \<union> (\<Union>v \<in> set (delete_effects_of op).
          {{ (Operator t (index (strips_problem.operators_of \<Pi>) op))\<inverse>
            , (State (Suc t) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }})"
      using nb\<^sub>1 nb\<^sub>2
      by argo
  }
  thus ?thesis
    by blast
qed

lemma cnf_of_encode_all_operator_effects_structure:
  "cnf (encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t)
    = (\<Union>(k, op) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<O>)).
        (\<Union>v \<in> set (add_effects_of op).
          {{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
            , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }}))
      \<union> (\<Union>(k, op) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<O>)).
        (\<Union>v \<in> set (delete_effects_of op).
          {{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
            , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }}))"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?\<Phi>\<^sub>E = "encode_all_operator_effects \<Pi> ?ops t"
    and ?l = "List.product [0..<t] ?ops"
  let ?fs = "map (\<lambda>(t, op). encode_operator_effect \<Pi> t op) ?l"
  have nb: "set (List.product [0..<t] ?ops) = {0..<t} \<times> set ?ops"
    by simp
  {
    have "cnf ` set ?fs = cnf ` (\<lambda>(k, op). encode_operator_effect \<Pi> k op) ` ({0..<t} \<times> set ?ops)"
      by force
    also have "\<dots> = (\<lambda>(k, op). cnf (encode_operator_effect \<Pi> k op)) ` ({0..<t} \<times> set ?ops)"
      using image_comp
      by fast
    (* TODO slow. *)
    finally have "cnf ` set ?fs = (\<lambda>(k, op).
          (\<Union>v \<in> set (add_effects_of op).
            {{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
              , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }})
        \<union> (\<Union>v \<in> set (delete_effects_of op).
            {{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
              , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }}))
      ` ({0..<t} \<times> set ?ops)"
      using cnf_of_encode_operator_effect_structure
      by auto
  }
  (* TODO slow. *)
  thus ?thesis
    unfolding encode_all_operator_effects_def
    using cnf_BigAnd[of ?fs]
    by auto
qed

corollary cnf_of_operator_effect_encoding_contains_add_effect_clause_if:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "k < t"
    and "op \<in> set ((\<Pi>)\<^sub>\<O>)"
    and "v \<in> set (add_effects_of op)"
  shows "{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
      , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }
    \<in> cnf (encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t)"
proof -
  let ?\<Phi>\<^sub>E = "encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?Add = "\<Union>(k, op)\<in>{0..<t} \<times> set ((\<Pi>)\<^sub>\<O>).
    \<Union>v\<in>set (add_effects_of op). {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}}"
  let ?C = "{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }"
  have "?Add \<subseteq> cnf ?\<Phi>\<^sub>E"
    using cnf_of_encode_all_operator_effects_structure[of \<Pi> t] Un_upper1[of "?Add"]
    by presburger
  moreover {
    have "?C  \<in> {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }}"
        using assms(4)
        by blast
      then have "?C \<in> (\<Union>v\<in>set (add_effects_of op).
        {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}})"
        using Complete_Lattices.UN_iff[of "?C" "\<lambda>v. {{ (Operator k (index ?ops op))\<inverse>
          , (State (Suc k) (index ?vs v))\<^sup>+}}" "set (add_effects_of op)"]
      using assms(4)
      by blast
    moreover have "(k, op) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<O>))"
      using assms(2, 3)
      by fastforce
    (* TODO slow step. *)
    ultimately have "?C \<in> ?Add"
      by blast
  }
  ultimately show ?thesis
    using subset_eq[of "?Add" "cnf ?\<Phi>\<^sub>E"]
    by meson
qed

corollary cnf_of_operator_effect_encoding_contains_delete_effect_clause_if:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "k < t"
    and "op \<in> set ((\<Pi>)\<^sub>\<O>)"
    and "v \<in> set (delete_effects_of op)"
  shows "{ (Operator k (index (strips_problem.operators_of \<Pi>) op))\<inverse>
      , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }
    \<in> cnf (encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t)"
proof -
  let ?\<Phi>\<^sub>E = "encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) t"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?Delete = "(\<Union>(k, op)\<in>{0..<t} \<times> set ((\<Pi>)\<^sub>\<O>).
    \<Union>v\<in>set (delete_effects_of op).
      {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse> }})"
  let ?C = "{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse> }"
  have "?Delete \<subseteq> cnf ?\<Phi>\<^sub>E"
    using cnf_of_encode_all_operator_effects_structure[of \<Pi> t] Un_upper2[of "?Delete"]
    by presburger
  moreover {
    have "?C \<in> (\<Union>v \<in> set (delete_effects_of op).
      {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse> }})"
      using assms(4)
      by blast
    moreover have "(k, op) \<in> {0..<t} \<times> set ?ops"
    using assms(2, 3)
    by force
    (* TODO slow step. *)
    ultimately have "?C \<in> ?Delete"
      by fastforce
  }
  (* TODO slow step. *)
  ultimately show ?thesis
    using subset_eq[of "?Delete" "cnf ?\<Phi>\<^sub>E"]
    by meson
qed

(* TODO refactor \<open>CNF_Supplement\<close>. *)
private lemma cnf_of_big_or_of_literal_formulas_is[simp]:
  assumes "\<forall>f \<in> set fs. is_literal_formula f"
  shows "cnf (\<^bold>\<Or>fs) = {{ literal_formula_to_literal f | f. f \<in> set fs }}"
  using assms
proof (induction fs)
  case (Cons f fs)
  {
    have is_literal_formula_f: "is_literal_formula f"
      using Cons.prems(1)
      by simp
    then have "cnf f = {{ literal_formula_to_literal f }}"
      using cnf_of_literal_formula
      by blast
  } note nb\<^sub>1 = this
  {
    have "\<forall>f' \<in> set fs. is_literal_formula f'"
      using Cons.prems
      by fastforce
    hence "cnf (\<^bold>\<Or>fs) = {{ literal_formula_to_literal f | f. f \<in> set fs }}"
      using Cons.IH
      by argo
  } note nb\<^sub>2 = this
  {
    have "cnf (\<^bold>\<Or>(f # fs)) = (\<lambda>(g, h). g \<union> h)
      ` ({{ literal_formula_to_literal f}}
        \<times> {{ literal_formula_to_literal f' | f'. f' \<in> set fs }})"
      using nb\<^sub>1 nb\<^sub>2
      by simp
    also have "\<dots> = {{ literal_formula_to_literal f}
      \<union> { literal_formula_to_literal f' | f'. f' \<in> set fs }}"
      by fast
    finally have "cnf (\<^bold>\<Or>(f # fs)) = {{ literal_formula_to_literal f' | f'. f' \<in> set (f # fs) }}"
      by fastforce
  }
  thus ?case .
qed simp

private lemma set_filter_op_list_mem_vs[simp]:
  "set (filter (\<lambda>op. ListMem v vs) ops) = { op. op \<in> set ops \<and> v \<in> set vs }"
  using set_filter[of "\<lambda>op. ListMem v vs" ops] ListMem_iff
  by force

private lemma  cnf_of_positive_transition_frame_axiom:
  "cnf (encode_positive_transition_frame_axiom \<Pi> k v)
    = {{ (State k (index (strips_problem.variables_of \<Pi>) v))\<^sup>+
        , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }
      \<union> { (Operator k (index (strips_problem.operators_of \<Pi>) op))\<^sup>+
        | op. op \<in> set (strips_problem.operators_of \<Pi>) \<and> v \<in> set (add_effects_of op) }}"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?adding_operators = "filter (\<lambda>op. ListMem v (add_effects_of op)) ?ops"
  let ?fs = "map (\<lambda>op. Atom (Operator k (index ?ops op))) ?adding_operators"
  {
    have "set ?fs = (\<lambda>op. Atom (Operator k (index ?ops op))) ` set ?adding_operators"
      using set_map[of "\<lambda>op. Atom (Operator k (index ?ops op))" "?adding_operators"]
      by blast
    (* TODO slow. *)
    then have "literal_formula_to_literal ` set ?fs
      = (\<lambda>op. (Operator k (index ?ops op))\<^sup>+) ` set ?adding_operators"
      using image_comp[of literal_formula_to_literal "\<lambda>op. Atom (Operator k (index ?ops op))"
          "set ?adding_operators"]
      by simp
    also have "\<dots> = (\<lambda>op. (Operator k (index ?ops op))\<^sup>+)
        ` { op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
      using set_filter_op_list_mem_vs[of v _  ?ops]
      by auto
    (* TODO slow. *)
    finally have "literal_formula_to_literal ` set ?fs
      = { (Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
      using setcompr_eq_image[of "\<lambda>op. (Operator k (index ?ops op))\<^sup>+"
          "\<lambda>op. op \<in>set ?adding_operators"]
      by blast
    (* TODO slow. *)
    hence "cnf (\<^bold>\<Or>?fs) = {{ (Operator k (index ?ops op))\<^sup>+
      | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }}"
      using cnf_of_big_or_of_literal_formulas_is[of ?fs]
        setcompr_eq_image[of literal_formula_to_literal "\<lambda>f. f \<in> set ?fs"]
      by force
  }
  (* TODO slow. *)
  then have "cnf (\<^bold>\<not>(Atom (State (Suc k) (index ?vs v))) \<^bold>\<or> \<^bold>\<Or>?fs)
  = {{ (State (Suc k) (index ?vs v))\<inverse>  } \<union> { (Operator k (index ?ops op))\<^sup>+
    | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }}"
    by force
  (* TODO slow. *)
  then have "cnf ((Atom (State k (index ?vs v)) \<^bold>\<or> (\<^bold>\<not>(Atom (State (Suc k) (index ?vs v))) \<^bold>\<or> \<^bold>\<Or>?fs)))
    = {{ (State k (index ?vs v))\<^sup>+ }
      \<union> { (State (Suc k) (index ?vs v))\<inverse> }
      \<union> { (Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }}"
    by simp
  (* TODO No idea why this is necessary (apparently only metis unfolds the definition properly). *)
  moreover have "cnf (encode_positive_transition_frame_axiom \<Pi> k v)
    = cnf ((Atom (State k (index ?vs v)) \<^bold>\<or> (\<^bold>\<not>(Atom (State (Suc k) (index ?vs v))) \<^bold>\<or> \<^bold>\<Or>?fs)))"
    unfolding encode_positive_transition_frame_axiom_def
    by metis
  (* TODO slow. *)
  ultimately show ?thesis
    by blast
qed

private lemma cnf_of_negative_transition_frame_axiom:
  "cnf (encode_negative_transition_frame_axiom \<Pi> k v)
    = {{ (State k (index (strips_problem.variables_of \<Pi>) v))\<inverse>
        , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+  }
      \<union> { (Operator k (index (strips_problem.operators_of \<Pi>) op))\<^sup>+
        | op. op \<in> set (strips_problem.operators_of \<Pi>) \<and> v \<in> set (delete_effects_of op) }}"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?deleting_operators = "filter (\<lambda>op. ListMem v (delete_effects_of op)) ?ops"
  let ?fs = "map (\<lambda>op. Atom (Operator k (index ?ops op))) ?deleting_operators"
  {
    have "set ?fs = (\<lambda>op. Atom (Operator k (index ?ops op))) ` set ?deleting_operators"
      using set_map[of "\<lambda>op. Atom (Operator k (index ?ops op))" "?deleting_operators"]
      by blast
    (* TODO slow. *)
    then have "literal_formula_to_literal ` set ?fs
      = (\<lambda>op. (Operator k (index ?ops op))\<^sup>+) ` set ?deleting_operators"
      using image_comp[of literal_formula_to_literal "\<lambda>op. Atom (Operator k (index ?ops op))"
          "set ?deleting_operators"]
      by simp
    also have "\<dots> = (\<lambda>op. (Operator k (index ?ops op))\<^sup>+)
        ` { op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }"
      using set_filter_op_list_mem_vs[of v _  ?ops]
      by auto
    (* TODO slow. *)
    finally have "literal_formula_to_literal ` set ?fs
      = { (Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }"
      using setcompr_eq_image[of "\<lambda>op. (Operator k (index ?ops op))\<^sup>+"
          "\<lambda>op. op \<in>set ?deleting_operators"]
      by blast
    (* TODO slow. *)
    hence "cnf (\<^bold>\<Or>?fs) = {{ (Operator k (index ?ops op))\<^sup>+
      | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }}"
      using cnf_of_big_or_of_literal_formulas_is[of ?fs]
        setcompr_eq_image[of literal_formula_to_literal "\<lambda>f. f \<in> set ?fs"]
      by force
  }
  (* TODO slow. *)
  then have "cnf (Atom (State (Suc k) (index ?vs v)) \<^bold>\<or> \<^bold>\<Or>?fs)
  = {{ (State (Suc k) (index ?vs v))\<^sup>+  } \<union> { (Operator k (index ?ops op))\<^sup>+
    | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }}"
    by force
  (* TODO slow. *)
  then have "cnf ((\<^bold>\<not>(Atom (State k (index ?vs v))) \<^bold>\<or> (Atom (State (Suc k) (index ?vs v)) \<^bold>\<or> \<^bold>\<Or>?fs)))
    = {{ (State k (index ?vs v))\<inverse> }
      \<union> { (State (Suc k) (index ?vs v))\<^sup>+ }
      \<union> { (Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }}"
    by simp
  (* TODO unfold Let_def + remove metis. *)
  moreover have "cnf (encode_negative_transition_frame_axiom \<Pi> k v)
    = cnf ((\<^bold>\<not>(Atom (State k (index ?vs v))) \<^bold>\<or> (Atom (State (Suc k) (index ?vs v)) \<^bold>\<or> \<^bold>\<Or>?fs)))"
    unfolding encode_negative_transition_frame_axiom_def
    by metis
  (* TODO slow. *)
  ultimately show ?thesis
    by blast
qed

lemma cnf_of_encode_all_frame_axioms_structure:
  "cnf (encode_all_frame_axioms \<Pi> t)
    = \<Union>(\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index (strips_problem.variables_of  \<Pi>) v))\<^sup>+
            , (State (Suc k) (index (strips_problem.variables_of  \<Pi>) v))\<inverse>  }
          \<union> {(Operator k (index (strips_problem.operators_of  \<Pi>) op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (add_effects_of op) }}})
      \<union> \<Union>(\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index (strips_problem.variables_of \<Pi>) v))\<inverse>
            , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }
          \<union> { (Operator k (index (strips_problem.operators_of \<Pi>) op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op) }}})"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<Phi>\<^sub>F = "encode_all_frame_axioms \<Pi> t"
  let ?l = "List.product [0..<t] ?vs"
  let ?fs = "map (\<lambda>(k, v). encode_negative_transition_frame_axiom \<Pi> k v) ?l
    @ map (\<lambda>(k, v). encode_positive_transition_frame_axiom \<Pi> k v) ?l"
  {
    let ?A = "{ encode_negative_transition_frame_axiom \<Pi> k v
        | k v. (k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)) }"
      and ?B = "{ encode_positive_transition_frame_axiom \<Pi> k v
        | k v. (k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)) }"
    have set_l: "set ?l = {..<t} \<times> set ((\<Pi>)\<^sub>\<V>)"
      using set_product
      by force
    (* TODO slow *)
    have "set ?fs = ?A \<union> ?B"
      unfolding set_append set_map
      using encode_all_frame_axioms_set
      by force
    then have "cnf ` set ?fs = cnf ` ?A \<union> cnf ` ?B"
      using image_Un[of cnf "?A" "?B"]
      by argo
    moreover {
      have "?A = (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        { encode_negative_transition_frame_axiom \<Pi> k v })"
        by blast
      then have  "cnf ` ?A  = (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        { cnf (encode_negative_transition_frame_axiom \<Pi> k v) })"
        by blast
      hence "cnf ` ?A = (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<inverse>
            , (State (Suc k) (index ?vs v))\<^sup>+ }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op)}}})"
        using cnf_of_negative_transition_frame_axiom[of \<Pi>]
        by presburger
    }
    moreover {
      have "?B = (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        { encode_positive_transition_frame_axiom \<Pi> k v})"
        by blast
      then have  "cnf ` ?B = (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        { cnf (encode_positive_transition_frame_axiom \<Pi> k v)  })"
        by blast
      hence "cnf ` ?B = (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<^sup>+
            , (State (Suc k) (index ?vs v))\<inverse> }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }}})"
        using cnf_of_positive_transition_frame_axiom[of \<Pi>]
        by presburger
    }
    (* TODO slow *)
    ultimately have "cnf ` set ?fs
      = (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<^sup>+
            , (State (Suc k) (index ?vs v))\<inverse> }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (add_effects_of op) }}})
      \<union> (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<inverse>
            , (State (Suc k) (index ?vs v))\<^sup>+ }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op)}}})"
      unfolding set_append set_map
      by force
  }
  then have "cnf (encode_all_frame_axioms \<Pi> t)
    = \<Union>((\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<^sup>+
            , (State (Suc k) (index ?vs v))\<inverse> }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (add_effects_of op) }}})
      \<union> (\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<inverse>
            , (State (Suc k) (index ?vs v))\<^sup>+ }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op)}}}))"
    unfolding encode_all_frame_axioms_def Let_def
    using cnf_BigAnd[of ?fs]
    by argo
  thus ?thesis
    using Union_Un_distrib[of
        "(\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<^sup>+
            ,  (State (Suc k) (index ?vs v))\<inverse> }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (add_effects_of op) }}})"
        "(\<Union>(k, v) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<V>)).
        {{{ (State k (index ?vs v))\<inverse>
            , (State (Suc k) (index ?vs v))\<^sup>+ }
          \<union> {(Operator k (index ?ops op))\<^sup>+
            | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op)}}})"]
    by argo
qed

\<comment> \<open> A technical lemma used in \isaname{cnf_of_encode_goal_state_set}. \<close>
private lemma cnf_of_encode_goal_state_set_i:
    "cnf ((\<Phi>\<^sub>G \<Pi>) t ) = \<Union>({ cnf (encode_state_variable t
      (index (strips_problem.variables_of \<Pi>) v) (((\<Pi>)\<^sub>G) v))
    | v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ((\<Pi>)\<^sub>G) v \<noteq> None })"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?\<Phi>\<^sub>G = "(\<Phi>\<^sub>G \<Pi>) t"
  let ?fs = "map (\<lambda>v. encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>)
      (filter (\<lambda>v. ?G v \<noteq> None) ?vs)"
  {
    have "cnf ` set ?fs  = cnf ` (\<lambda>v. encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>)
      ` { v | v. v \<in> set ?vs \<and> ?G v \<noteq> None }"
      unfolding set_map
      by force
    also have "\<dots> = (\<lambda>v. cnf (encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>))
      ` { v | v. v \<in> set ?vs \<and> ?G v \<noteq> None }"
      using image_comp[of cnf "(\<lambda>v. encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>)"
          "{ v | v. v \<in> set ?vs \<and> ?G v \<noteq> None }"]
      by fast
    finally have "cnf ` set ?fs = { cnf (encode_state_variable t (index ?vs v) (?G v))
        | v. v \<in> set ?vs \<and> ?G v \<noteq> None }"
      unfolding setcompr_eq_image[of "\<lambda>v. cnf (encode_state_variable t (index ?vs v) (?G v) \<^bold>\<or> \<bottom>)"]
      by auto
  }
  moreover have "cnf ((\<Phi>\<^sub>G \<Pi>) t) = \<Union> (cnf ` set ?fs)"
    unfolding encode_goal_state_def SAT_Plan_Base.encode_goal_state_def Let_def
    using cnf_BigAnd[of ?fs]
    by force
  ultimately show ?thesis
    by simp
qed

\<comment> \<open> A simplification lemma for the above one. \<close>
(* TODO Replace above lemma with this?. *)
corollary cnf_of_encode_goal_state_set_ii:
  assumes "is_valid_problem_strips \<Pi>"
  shows "cnf ((\<Phi>\<^sub>G \<Pi>) t) = \<Union>({{{ literal_formula_to_literal
      (encode_state_variable t (index (strips_problem.variables_of \<Pi>) v) (((\<Pi>)\<^sub>G) v)) }}
    | v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ((\<Pi>)\<^sub>G) v \<noteq> None })"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?\<Phi>\<^sub>G = "(\<Phi>\<^sub>G \<Pi>) t"
  {
    fix v
    assume "v \<in> { v | v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ?G v \<noteq> None }"
    then have "v \<in> set ((\<Pi>)\<^sub>\<V>)" and G_of_v_is_not_None: "?G v \<noteq> None"
      by fast+
    then consider (A) "?G v = Some True"
      | (B) "?G v = Some False"
      by fastforce
    hence "cnf (encode_state_variable t (index ?vs v) (?G v))
      = {{ literal_formula_to_literal (encode_state_variable t (index ?vs v) (?G v))  }}"
      unfolding encode_state_variable_def
      by (cases, force+)
  } note nb = this
  have  "cnf ?\<Phi>\<^sub>G = \<Union>({ cnf (encode_state_variable t (index ?vs v) (?G v))
    | v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ?G v \<noteq> None })"
    unfolding cnf_of_encode_goal_state_set_i
    by blast
  also have "\<dots> = \<Union>((\<lambda>v. cnf (encode_state_variable t (index ?vs v) (((\<Pi>)\<^sub>G) v)))
    ` { v | v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ((\<Pi>)\<^sub>G) v \<noteq> None })"
    using setcompr_eq_image[of
        "\<lambda>v. cnf (encode_state_variable t (index ?vs v) (((\<Pi>)\<^sub>G) v))"
        "\<lambda>v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ((\<Pi>)\<^sub>G) v \<noteq> None"]
    by presburger
  also have "\<dots> = \<Union>((\<lambda>v. {{ literal_formula_to_literal
      (encode_state_variable t (index ?vs v) (?G v)) }})
    `  { v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ((\<Pi>)\<^sub>G) v \<noteq> None })"
    using nb
    by simp
  finally show ?thesis
    unfolding nb
    by auto
qed

\<comment> \<open> This lemma essentially states that the cnf for the cnf formula for the encoding has a
clause for each variable whose state is defined in the goal state with the corresponding literal. \<close>
(* TODO is \<open>\<exists>!\<close> still needed? *)
lemma cnf_of_encode_goal_state_set:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "v \<in> dom ((\<Pi>)\<^sub>G)"
  shows "((\<Pi>)\<^sub>G) v = Some True \<longrightarrow> (\<exists>!C. C \<in> cnf ((\<Phi>\<^sub>G \<Pi>) t)
      \<and> C = { (State t (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ })"
    and "((\<Pi>)\<^sub>G) v = Some False \<longrightarrow> (\<exists>!C. C \<in> cnf ((\<Phi>\<^sub>G \<Pi>) t)
      \<and> C = { (State t (index (strips_problem.variables_of \<Pi>) v))\<inverse> })"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?\<Phi>\<^sub>G = "(\<Phi>\<^sub>G \<Pi>) t"
  have nb\<^sub>1: "cnf ?\<Phi>\<^sub>G  = \<Union> { cnf (encode_state_variable t (index ?vs v)
      (?G v)) | v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ?G v \<noteq> None }"
    unfolding cnf_of_encode_goal_state_set_i
    by auto
  have nb\<^sub>2: "v \<in> { v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ?G v \<noteq> None }"
    using is_valid_problem_dom_of_goal_state_is assms(1, 2)
    by auto
  have nb\<^sub>3: "cnf (encode_state_variable t (index (strips_problem.variables_of \<Pi>) v) (((\<Pi>)\<^sub>G) v))
    \<subseteq> (\<Union>{ cnf (encode_state_variable t (index ?vs v)
      (?G v)) | v. v \<in> set ((\<Pi>)\<^sub>\<V>) \<and> ?G v \<noteq> None })"
    using UN_upper[OF nb\<^sub>2, of "\<lambda>v. cnf (encode_state_variable t (index ?vs v) (?G v))"] nb\<^sub>2
    by blast
  show "((\<Pi>)\<^sub>G) v = Some True \<longrightarrow> (\<exists>!C. C \<in> cnf ((\<Phi>\<^sub>G \<Pi>) t)
      \<and> C = { (State t (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ })"
    and "((\<Pi>)\<^sub>G) v = Some False \<longrightarrow> (\<exists>!C. C \<in> cnf ((\<Phi>\<^sub>G \<Pi>) t)
      \<and> C = { (State t (index (strips_problem.variables_of \<Pi>) v))\<inverse> })"
    using nb\<^sub>3
    unfolding nb\<^sub>1 encode_state_variable_def
    by auto+
qed

end


text \<open> We omit the proofs that the partial encoding functions produce formulas in CNF form due to
their more technical nature.
The following sublocale proof confirms that definition \ref{isadef:encode-problem-sat-plan-base}
encodes a valid problem \<^term>\<open>\<Pi>\<close> into a formula that can be transformed to CNF
(\<^term>\<open>is_cnf (\<Phi> \<Pi> t)\<close>) and that its CNF has the required form. \<close>


subsection "Soundness of the Basic SATPlan Algorithm"


lemma valuation_models_encoding_cnf_formula_equals:
  assumes "is_valid_problem_strips \<Pi>"
  shows "\<A> \<Turnstile> \<Phi> \<Pi> t = cnf_semantics \<A> (cnf (\<Phi> \<Pi> t))"
proof -
  let ?\<Phi> = "\<Phi> \<Pi> t"
  {
    have "is_cnf ?\<Phi>"
      using is_cnf_encode_problem[OF assms].
    hence "is_nnf ?\<Phi>"
      using is_nnf_cnf
      by blast
  }
  thus ?thesis
    using cnf_semantics[of ?\<Phi> \<A>]
    by blast
qed

(* TODO refactor *)
corollary valuation_models_encoding_cnf_formula_equals_corollary:
  assumes "is_valid_problem_strips \<Pi>"
  shows "\<A> \<Turnstile> (\<Phi> \<Pi> t)
    = (\<forall>C \<in> cnf (\<Phi> \<Pi> t). \<exists>L \<in> C. lit_semantics \<A> L)"
  using valuation_models_encoding_cnf_formula_equals[OF assms]
  unfolding cnf_semantics_def clause_semantics_def encode_problem_def
  by presburger

\<comment> \<open> A couple of technical lemmas about \<open>decode_plan\<close>. \<close>
lemma decode_plan_length:
  assumes "\<pi> = \<Phi>\<inverse> \<Pi> \<nu> t"
  shows "length \<pi> = t"
  using assms
  unfolding decode_plan_def SAT_Plan_Base.decode_plan_def
  by simp

lemma decode_plan'_set_is[simp]:
  "set (decode_plan' \<Pi> \<A> k)
    = { (strips_problem.operators_of \<Pi>) ! (index (strips_problem.operators_of \<Pi>) op)
      | op. op \<in> set (strips_problem.operators_of \<Pi>)
        \<and> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) }"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  let ?f = "\<lambda>op. Operator k (index ?ops op)"
  let ?vs = "map ?f ?ops"
  {
    have "set (filter \<A> ?vs) = set (map ?f (filter (\<A> \<circ> ?f) ?ops))"
      unfolding filter_map[of \<A> "\<lambda>op. Operator k (index ?ops op)" ?ops]..
    hence "set (filter \<A> ?vs) = (\<lambda>op. Operator k (index ?ops op)) `
      { op \<in> set ?ops. \<A> (Operator k (index ?ops op)) }"
      unfolding set_map set_filter
      by simp
  }
  have "set (decode_plan' \<Pi> \<A> k) = (\<lambda>v. case v of Operator k i \<Rightarrow> ?ops ! i)
    ` (\<lambda>op. Operator k (index ?ops op)) ` { op \<in> set ?ops. \<A> (Operator k (index ?ops op)) }"
    unfolding decode_plan'_def set_map Let_def
    by auto
  also have "\<dots> = (\<lambda>op. case Operator k (index ?ops op) of Operator k i \<Rightarrow> ?ops ! i)
    ` { op \<in> set ?ops. \<A> (Operator k (index ?ops op)) }"
    unfolding image_comp comp_apply
    by argo
  also have "\<dots> = (\<lambda>op. ?ops ! (index ?ops op))
    ` { op \<in> set ?ops. \<A> (Operator k (index ?ops op)) }"
    by force
  finally show ?thesis
    by blast
qed

lemma decode_plan_set_is[simp]:
  "set (\<Phi>\<inverse> \<Pi> \<A> t) = (\<Union>k \<in> {..<t}. { decode_plan' \<Pi> \<A> k })"
  unfolding decode_plan_def SAT_Plan_Base.decode_plan_def set_map
  using atLeast_upt
  by blast

lemma decode_plan_step_element_then_i:
  assumes "k < t"
  shows "set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)
    = { (strips_problem.operators_of \<Pi>) ! (index (strips_problem.operators_of \<Pi>) op)
      | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) }"
proof -
  have "(\<Phi>\<inverse> \<Pi> \<A> t) ! k = decode_plan' \<Pi> \<A> k"
    unfolding decode_plan_def SAT_Plan_Base.decode_plan_def
    using assms
    by simp
  thus ?thesis
    by force
qed

\<comment> \<open> Show that each operator $op$ in the $k$-th parallel operator in a decoded parallel plan is
contained within the problem's operator set and the valuation is true for the corresponding SATPlan
variable. \<close>
lemma decode_plan_step_element_then:
  fixes \<Pi>::"'a strips_problem"
  assumes "k < t"
    and "op \<in> set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
  shows "op \<in> set ((\<Pi>)\<^sub>\<O>)"
    and "\<A> (Operator k (index (strips_problem.operators_of \<Pi>) op))"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
  let ?Ops = "{ ?ops ! (index ?ops op)
    | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> \<A> (Operator k (index ?ops op)) }"
  have "op \<in> ?Ops"
    using assms(2)
    unfolding decode_plan_step_element_then_i[OF assms(1)] assms
    by blast
  moreover have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
    and "\<A> (Operator k (index ?ops op))"
    using calculation
    by fastforce+
  ultimately show "op \<in> set ((\<Pi>)\<^sub>\<O>)"
    and "\<A> (Operator k (index ?ops op))"
    by blast+
qed

\<comment> \<open> Show that the \<open>k\<close>-th parallel operators of the decoded plan are distinct lists (i.e. do not
contain duplicates). \<close>
lemma decode_plan_step_distinct:
  assumes "k < t"
  shows "distinct ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<pi>\<^sub>k = "(\<Phi>\<inverse> \<Pi> \<A> t) ! k"
  let ?f = "\<lambda>op. Operator k (index ?ops op)"
    and ?g = "\<lambda>v. case v of Operator _ k \<Rightarrow> ?ops ! k"
  let ?vs = "map ?f (remdups ?ops)"
  have nb\<^sub>1: "?\<pi>\<^sub>k = decode_plan' \<Pi> \<A> k"
    unfolding decode_plan_def SAT_Plan_Base.decode_plan_def
    using assms
    by fastforce
  {
    have "distinct (remdups ?ops)"
      by blast
    moreover have "inj_on ?f (set (remdups ?ops))"
      unfolding inj_on_def
      by fastforce
    ultimately have "distinct ?vs"
      using distinct_map
      by blast
  } note nb\<^sub>2 = this
  {
    have "inj_on ?g (set ?vs)"
      unfolding inj_on_def
      by fastforce
    hence "distinct (map ?g ?vs)"
      using distinct_map nb\<^sub>2
      by blast
  }
  thus ?thesis
    using distinct_map_filter[of ?g ?vs \<A>]
    unfolding nb\<^sub>1 decode_plan'_def Let_def
    by argo
qed

lemma decode_state_at_valid_variable:
  fixes \<Pi> :: "'a strips_problem"
  assumes "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) v \<noteq> None"
  shows "v \<in> set ((\<Pi>)\<^sub>\<V>)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
  let ?f = "\<lambda>v. (v,\<A> (State k (index ?vs v)))"
  {
    have "fst ` set (map ?f ?vs) = fst ` (\<lambda>v. (v,\<A> (State k (index ?vs v)))) ` set ?vs"
      by force
    also have "\<dots> = (\<lambda>v. fst (v,\<A> (State k (index ?vs v)))) ` set ?vs"
      by blast
    finally have "fst ` set (map ?f ?vs) = set ?vs"
      by auto
  }
  moreover have "\<not>v \<notin> fst ` set (map ?f ?vs)"
    using map_of_eq_None_iff[of "map ?f ?vs" v] assms
    unfolding decode_state_at_def SAT_Plan_Base.decode_state_at_def
    by meson
  ultimately show ?thesis
    by fastforce
qed

\<comment> \<open> Show that there exists an equivalence between a model \<open>\<A>\<close> of the (CNF of the) encoded
problem and the state at step \<open>k\<close> decoded from the encoded problem. \<close>
lemma decode_state_at_encoding_variables_equals_some_of_valuation_if:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
    and "k \<le> t"
    and "v \<in> set ((\<Pi>)\<^sub>\<V>)"
  shows "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) v
    = Some (\<A> (State k (index (strips_problem.variables_of \<Pi>) v)))"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
  let ?l = "map (\<lambda>x. (x,\<A> (State k (index ?vs x)))) ?vs"
  have "set ?vs \<noteq> {}"
    using assms(4)
    by fastforce
  then have "map_of ?l v = Some (\<A> (State k (index ?vs v)))"
    using map_of_from_function_graph_is_some_if[of ?vs v
        "\<lambda>v. \<A> (State k (index ?vs v))"] assms(4)
    by fastforce
  thus ?thesis
    unfolding decode_state_at_def SAT_Plan_Base.decode_state_at_def
    by meson
qed

lemma decode_state_at_dom:
  assumes "is_valid_problem_strips \<Pi>"
  shows "dom (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) = set ((\<Pi>)\<^sub>\<V>)"
proof-
  let ?s = "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k"
    and ?vs = "strips_problem.variables_of \<Pi>"
  have "dom ?s = fst ` set (map (\<lambda>v. (v, \<A> (State k (index ?vs v)))) ?vs)"
    unfolding decode_state_at_def SAT_Plan_Base.decode_state_at_def
    using dom_map_of_conv_image_fst[of "(map (\<lambda>v. (v, \<A> (State k (index ?vs v)))) ?vs)"]
    by meson
  also have "\<dots> = fst ` (\<lambda>v. (v, \<A> (State k (index ?vs v)))) ` set ((\<Pi>)\<^sub>\<V>)"
    using set_map[of "(\<lambda>v. (v, \<A> (State k (index ?vs v))))" ?vs]
    by simp
  also have "\<dots> = (fst \<circ> (\<lambda>v. (v, \<A> (State k (index ?vs v))))) ` set ((\<Pi>)\<^sub>\<V>)"
    using image_comp[of fst "(\<lambda>v. (v, \<A> (State k (index ?vs v))))"]
    by presburger
  finally show ?thesis
    by force
qed

(* TODO shorten the proof (there are a lot of duplicate parts still!). *)
lemma decode_state_at_initial_state:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
  shows "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> 0) = (\<Pi>)\<^sub>I"
proof -
  let ?I = "(\<Pi>)\<^sub>I"
  let ?s = "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> 0"
  let ?vs = "strips_problem.variables_of \<Pi>"
  let ?\<Phi> = "\<Phi> \<Pi> t"
  let ?\<Phi>\<^sub>I = "\<Phi>\<^sub>I \<Pi>"
  {
    have "is_cnf ?\<Phi>\<^sub>I" and "cnf ?\<Phi>\<^sub>I \<subseteq> cnf ?\<Phi>"
      subgoal
        using is_cnf_encode_initial_state[OF assms(1)]
        by simp
      subgoal
        using cnf_of_encode_problem_structure(1)
        unfolding encode_initial_state_def encode_problem_def
        by blast
      done
    then have "cnf_semantics \<A> (cnf ?\<Phi>\<^sub>I)"
      using cnf_semantics_monotonous_in_cnf_subsets_if is_cnf_encode_problem[OF assms(1)]
        assms(2)
      by blast
    hence "\<forall>C \<in> cnf ?\<Phi>\<^sub>I. clause_semantics \<A> C"
      unfolding cnf_semantics_def encode_initial_state_def
      by blast
  } note nb\<^sub>1 = this
  {
    (* TODO refactor. *)
    {
      fix v
      assume v_in_dom_i: "v \<in> dom ?I"
      moreover  {
        have v_in_variable_set: "v \<in> set ((\<Pi>)\<^sub>\<V>)"
          using is_valid_problem_strips_initial_of_dom assms(1) v_in_dom_i
          by auto
        hence "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> 0) v = Some (\<A> (State 0 (index ?vs v)))"
          using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
              assms(1, 2) _ v_in_variable_set]
          by fast
      } note nb\<^sub>2 = this
      consider (v_initially_true) "?I v = Some True"
        | (v_initially_false) "?I v = Some False"
        using v_in_dom_i
        by fastforce
      hence "?I v = ?s v"
        proof (cases)
          case v_initially_true
          then obtain C
            where "C \<in> cnf ?\<Phi>\<^sub>I"
              and c_is: "C = { (State 0 (index ?vs v))\<^sup>+ }"
            using cnf_of_encode_initial_state_set v_in_dom_i assms(1)
            by fastforce
          hence "\<A> (State 0 (index ?vs v)) = True"
            using nb\<^sub>1
            unfolding clause_semantics_def
            by fastforce
          thus ?thesis
            using nb\<^sub>2 v_initially_true
            by presburger
        next
          case v_initially_false
          (* TODO slow *)
          then obtain C
            where "C \<in> cnf ?\<Phi>\<^sub>I"
              and c_is: "C = { (State 0 (index ?vs v))\<inverse> }"
            using cnf_of_encode_initial_state_set assms(1) v_in_dom_i
            by fastforce
          hence "\<A> (State 0 (index ?vs v)) = False"
            using nb\<^sub>1
            unfolding clause_semantics_def
            by fastforce
          thus ?thesis
            using nb\<^sub>2 v_initially_false
            by presburger
        qed
    }
    hence "?I \<subseteq>\<^sub>m ?s"
      using map_le_def
      by blast
  } moreover {
    {
      fix v
      assume v_in_dom_s: "v \<in> dom ?s"
      then have v_in_set_vs: "v \<in> set ?vs"
        using decode_state_at_dom[OF assms(1)]
        by simp
      have v_in_dom_I: "v \<in> dom ?I"
        using is_valid_problem_strips_initial_of_dom assms(1) v_in_set_vs
        by auto
      have s_v_is: "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> 0) v = Some (\<A> (State 0 (index ?vs v)))"
        using decode_state_at_encoding_variables_equals_some_of_valuation_if assms(1, 2)
          v_in_set_vs
        by (metis le0)
      consider (s_v_is_some_true) "?s v = Some True"
        | (s_v_is_some_false) "?s v = Some False"
        using v_in_dom_s
        by fastforce
      hence "?s v = ?I v"
        proof (cases)
          case s_v_is_some_true
          then have \<A>_of_s_v: "lit_semantics \<A> ((State 0 (index ?vs v))\<^sup>+)"
            using s_v_is
            by fastforce
          consider (I_v_is_some_true) "?I v = Some True"
            | (I_v_is_some_false) "?I v = Some False"
            using v_in_dom_I
            by fastforce
          thus ?thesis
            proof (cases)
              case I_v_is_some_true
              then show ?thesis
                using s_v_is_some_true
                by argo
            next
              case I_v_is_some_false
              (* TODO slow *)
              then obtain C
                where C_in_encode_initial_state: "C \<in> cnf ?\<Phi>\<^sub>I"
                  and C_is: "C = { (State 0 (index ?vs v))\<inverse>  }"
                using cnf_of_encode_initial_state_set assms(1) v_in_dom_I
                by fastforce
              hence "lit_semantics \<A> ((State 0 (index ?vs v))\<inverse>)"
                using nb\<^sub>1
                unfolding clause_semantics_def
                by fast
              thus ?thesis
                using \<A>_of_s_v
                by fastforce
            qed
        next
          case s_v_is_some_false
          then have \<A>_of_s_v: "lit_semantics \<A> ((State 0 (index ?vs v))\<inverse>)"
            using s_v_is
            by fastforce
          consider (I_v_is_some_true) "?I v = Some True"
            | (I_v_is_some_false) "?I v = Some False"
            using v_in_dom_I
            by fastforce
          thus ?thesis
            proof (cases)
              case I_v_is_some_true
              then obtain C
                where C_in_encode_initial_state: "C \<in> cnf ?\<Phi>\<^sub>I"
                  and C_is: "C = { (State 0 (index ?vs v))\<^sup>+  }"
                using cnf_of_encode_initial_state_set assms(1) v_in_dom_I
                by fastforce
              hence "lit_semantics \<A> ((State 0 (index ?vs v))\<^sup>+)"
                using nb\<^sub>1
                unfolding clause_semantics_def
                by fast
              thus ?thesis
                using \<A>_of_s_v
                by fastforce
            next
              case I_v_is_some_false
              thus ?thesis
                using s_v_is_some_false
                by presburger
            qed
        qed
    }
    hence "?s \<subseteq>\<^sub>m ?I"
      using map_le_def
      by blast
  } ultimately show ?thesis
    using map_le_antisym
    by blast
qed

lemma decode_state_at_goal_state:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
  shows "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m \<Phi>\<^sub>S\<inverse> \<Pi> \<A> t"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?G' = "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> t"
    and ?\<Phi> = "\<Phi> \<Pi> t"
    and ?\<Phi>\<^sub>G = "(\<Phi>\<^sub>G \<Pi>) t"
  {
    have "is_cnf ?\<Phi>\<^sub>G" and "cnf ?\<Phi>\<^sub>G \<subseteq> cnf ?\<Phi>"
      subgoal
        using encode_goal_state_is_cnf[OF assms(1)]
        by simp
      subgoal
        using cnf_of_encode_problem_structure(2)
        unfolding encode_goal_state_def encode_problem_def
        by blast
      done
    then have "cnf_semantics \<A> (cnf ?\<Phi>\<^sub>G)"
      using cnf_semantics_monotonous_in_cnf_subsets_if is_cnf_encode_problem[OF assms(1)]
        assms(2)
      by blast
    hence "\<forall>C \<in> cnf ?\<Phi>\<^sub>G. clause_semantics \<A> C"
      unfolding cnf_semantics_def encode_initial_state_def
      by blast
  } note nb\<^sub>1 = this
  (* TODO refactor. *)
  {
    fix v
    assume "v \<in> set ((\<Pi>)\<^sub>\<V>)"
    moreover have "set ?vs \<noteq> {}"
      using calculation(1)
      by fastforce
    moreover have "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> t)
      = map_of (map (\<lambda>v. (v, \<A> (State t (index ?vs v)))) ?vs)"
      unfolding decode_state_at_def SAT_Plan_Base.decode_state_at_def
      by metis
    (* TODO slow. *)
    ultimately have "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> t) v = Some (\<A> (State t (index ?vs v)))"
      using map_of_from_function_graph_is_some_if
      by fastforce
  } note nb\<^sub>2 = this
  {
    fix v
    assume v_in_dom_G: "v \<in> dom ?G"
    then have v_in_vs: "v \<in> set ?vs"
      using is_valid_problem_dom_of_goal_state_is assms(1)
      by auto
    then have decode_state_at_is: "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> t) v = Some (\<A> (State t (index ?vs v)))"
      using nb\<^sub>2
      by fastforce
    consider (A) "?G v = Some True"
      | (B) "?G v = Some False"
      using v_in_dom_G
      by fastforce
    hence "?G v = ?G' v"
      proof (cases)
        case A
        {
          obtain C where "C \<subseteq> cnf ?\<Phi>\<^sub>G" and "C = {{ (State t (index ?vs v))\<^sup>+ }}"
            using cnf_of_encode_goal_state_set(1)[OF assms(1) v_in_dom_G] A
            by auto
          then have "{ (State t (index ?vs v))\<^sup>+ } \<in> cnf ?\<Phi>\<^sub>G"
            by blast
          then have "clause_semantics \<A> { (State t (index ?vs v))\<^sup>+ }"
            using nb\<^sub>1
            by blast
          then have "lit_semantics \<A> ((State t (index ?vs v))\<^sup>+)"
            unfolding clause_semantics_def
            by blast
          hence "\<A> (State t (index ?vs v)) = True"
            by force
        }
        thus ?thesis
          using decode_state_at_is A
          by presburger
      next
        case B
        {
          obtain C where "C \<subseteq> cnf ?\<Phi>\<^sub>G" and "C = {{ (State t (index ?vs v))\<inverse> }}"
            using cnf_of_encode_goal_state_set(2)[OF assms(1) v_in_dom_G] B
            by auto
          then have "{ (State t (index ?vs v))\<inverse> } \<in> cnf ?\<Phi>\<^sub>G"
            by blast
          then have "clause_semantics \<A> { (State t (index ?vs v))\<inverse> }"
            using nb\<^sub>1
            by blast
          then have "lit_semantics \<A> ((State t (index ?vs v))\<inverse>)"
            unfolding clause_semantics_def
            by blast
          hence "\<A> (State t (index ?vs v)) = False"
            by simp
        }
        thus ?thesis
          using decode_state_at_is B
          by presburger
    qed
  }
  thus ?thesis
    using map_le_def
    by blast
qed

\<comment> \<open> Show that the operator activation implies precondition constraints hold at every time step
of the decoded plan. \<close>
lemma decode_state_at_preconditions:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
    and "k < t"
    and "op \<in> set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
    and "v \<in> set (precondition_of op)"
  shows "\<A> (State k (index (strips_problem.variables_of \<Pi>) v))"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?\<Phi> = "\<Phi> \<Pi> t"
    and ?\<Phi>\<^sub>O = "encode_operators \<Pi> t"
    and ?\<Phi>\<^sub>P = "encode_all_operator_preconditions \<Pi> ?ops t"
  {
    have "\<A> (Operator k (index ?ops op))"
      and "op \<in> set ((\<Pi>)\<^sub>\<O>)"
      using decode_plan_step_element_then[OF assms(3, 4)]
      by blast+
    moreover obtain C
      where clause_is_in_operator_encoding: "C \<in> cnf ?\<Phi>\<^sub>P"
        and "C = { (Operator k (index ?ops op))\<inverse>,
        (State k (index ?vs v))\<^sup>+ }"
      using cnf_of_encode_all_operator_preconditions_contains_clause_if[OF assms(1, 3)
          calculation(2) assms(5)]
      by blast
    moreover have clause_semantics_\<A>_\<Phi>\<^sub>P: "\<forall>C \<in> cnf ?\<Phi>\<^sub>P. clause_semantics \<A> C"
      using cnf_semantics_monotonous_in_cnf_subsets_if[OF assms(2)
          is_cnf_encode_problem[OF assms(1)]
        cnf_of_operator_precondition_encoding_subset_encoding]
      unfolding cnf_semantics_def
      by blast
    (* TODO slow step *)
    ultimately have "lit_semantics \<A> (Pos (State k (index ?vs v)))"
      unfolding clause_semantics_def
      by fastforce
  }
  thus ?thesis
    unfolding lit_semantics_def
    by fastforce
qed

\<comment> \<open> This lemma shows that for a problem encoding with makespan zero for which a model exists,
the goal state encoding must be subset of the initial state encoding. In this case, the state
variable encodings for the goal state are included in the initial state encoding. \<close>
(* TODO simplify/refactor proof. *)
lemma encode_problem_parallel_correct_i:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> 0"
  shows "cnf ((\<Phi>\<^sub>G \<Pi>) 0) \<subseteq> cnf (\<Phi>\<^sub>I \<Pi>)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?I = "(\<Pi>)\<^sub>I"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?\<Phi>\<^sub>I = "\<Phi>\<^sub>I \<Pi>"
    and ?\<Phi>\<^sub>G = "(\<Phi>\<^sub>G \<Pi>) 0"
    and ?\<Phi> = "\<Phi> \<Pi> 0"
  (* TODO refactor and generalize for all partial encodings? *)
  \<comment> \<open> Show that the model of the encoding is also a model of the partial encodings. \<close>
  have \<A>_models_\<Phi>\<^sub>I: "\<A> \<Turnstile> ?\<Phi>\<^sub>I" and \<A>_models_\<Phi>\<^sub>G: "\<A> \<Turnstile> ?\<Phi>\<^sub>G"
    using assms(2) encode_problem_has_model_then_also_partial_encodings(1, 2)
    unfolding encode_problem_def encode_initial_state_def encode_goal_state_def
    by blast+
  \<comment> \<open> Show that every clause in the CNF of the goal state encoding @{text "\<Phi>\<^sub>G"} is also in
  the CNF of the initial state encoding @{text "\<Phi>\<^sub>I"} thus making it a subset. We can conclude this
  from the fact that both @{text "\<Phi>\<^sub>I"} and @{text "\<Phi>\<^sub>G"} contain singleton clauses—which must all
  be evaluated to true by the given model \<open>\<A>\<close>—and the similar structure of the clauses in both
  partial encodings.

  By extension, if we decode the goal state @{text "G"} and the initial state @{text "I"} from a
  model of the encoding,  @{text "G v = I v"} must hold for variable @{text "v"} in the domain of
  the goal state. \<close>
  {
    fix C'
    assume C'_in_cnf_\<Phi>\<^sub>G: "C' \<in> cnf ?\<Phi>\<^sub>G"
    then obtain v
      where v_in_vs: "v \<in> set ?vs"
        and G_of_v_is_not_None: "?G v \<noteq> None"
        and C'_is: "C' = { literal_formula_to_literal (encode_state_variable 0 (index ?vs v)
          (?G v)) }"
      using cnf_of_encode_goal_state_set_ii[OF assms(1)]
      by auto
    obtain C
      where C_in_cnf_\<Phi>\<^sub>I: "C \<in> cnf ?\<Phi>\<^sub>I"
        and C_is: "C = { literal_formula_to_literal (encode_state_variable 0 (index ?vs v)
          (?I v)) }"
      using cnf_of_encode_initial_state_set_ii[OF assms(1)] v_in_vs
      by auto
    {
      let ?L = "literal_formula_to_literal (encode_state_variable 0 (index ?vs v) (?I v))"
      have "{ ?L } \<in> cnf ?\<Phi>\<^sub>I"
        using C_in_cnf_\<Phi>\<^sub>I C_is
        by blast
      hence "lit_semantics \<A> ?L"
        using model_then_all_singleton_clauses_modelled[OF
            is_cnf_encode_initial_state[OF assms(1)]_ \<A>_models_\<Phi>\<^sub>I]
        by blast
    } note lit_semantics_\<A>_L = this
    {
      let ?L' = "literal_formula_to_literal (encode_state_variable 0 (index ?vs v) (?G v))"
      have "{ ?L' } \<in> cnf ?\<Phi>\<^sub>G"
        using C'_in_cnf_\<Phi>\<^sub>G C'_is
        by blast
      hence "lit_semantics \<A> ?L'"
        using model_then_all_singleton_clauses_modelled[OF
            encode_goal_state_is_cnf[OF assms(1)]_ \<A>_models_\<Phi>\<^sub>G]
        by blast
    } note lit_semantics_\<A>_L' = this
    {
      have "?I v = ?G v"
        proof (rule ccontr)
          assume contradiction: "?I v \<noteq> ?G v"
          moreover have "?I v \<noteq> None"
            using v_in_vs is_valid_problem_strips_initial_of_dom assms(1)
            by auto
          ultimately consider (A) "?I v = Some True \<and> ?G v = Some False"
            | (B) "?I v = Some False \<and> ?G v = Some True"
            using G_of_v_is_not_None
            by force
          thus False
            using lit_semantics_\<A>_L lit_semantics_\<A>_L'
            unfolding encode_state_variable_def
            by (cases, fastforce+)
        qed
    }
    hence "C' \<in> cnf ?\<Phi>\<^sub>I"
      using C_is C_in_cnf_\<Phi>\<^sub>I C'_is C'_in_cnf_\<Phi>\<^sub>G
      by argo
  }
  thus ?thesis
    by blast
qed

\<comment> \<open> Show that the encoding secures that for every parallel operator \<open>ops\<close>
decoded from the plan at every time step \<open>t < length pi\<close> the following hold:
\begin{enumerate}
\item  \<open>ops\<close> is applicable, and
\item the effects of \<open>ops\<close> are consistent.
\end{enumerate}\<close>
lemma encode_problem_parallel_correct_ii:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
    and "k < length (\<Phi>\<inverse> \<Pi> \<A> t)"
  shows "are_all_operators_applicable (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k)
    ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
    and "are_all_operator_effects_consistent ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
    and ?s = "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k"
  let ?\<Phi> = "\<Phi> \<Pi> t"
    and ?\<Phi>\<^sub>E = "encode_all_operator_effects \<Pi> ?ops t"
  have k_lt_t: "k < t"
    using decode_plan_length assms(3)
    by metis
  {
    {
      fix op v
      assume op_in_kth_of_decoded_plan_set: "op \<in> set (?\<pi> ! k)"
        and v_in_precondition_set: "v \<in> set (precondition_of op)"
      {
        have "\<A> (Operator k (index ?ops op))"
          using decode_plan_step_element_then[OF k_lt_t op_in_kth_of_decoded_plan_set]
          by blast
        hence "\<A> (State k (index ?vs v))"
          using decode_state_at_preconditions[
              OF assms(1, 2) _ op_in_kth_of_decoded_plan_set v_in_precondition_set] k_lt_t
          by blast
      }
      moreover have "k \<le> t"
        using k_lt_t
        by auto
      moreover {
        have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
          using decode_plan_step_element_then[OF k_lt_t op_in_kth_of_decoded_plan_set]
          by simp
        then have  "v \<in> set ((\<Pi>)\<^sub>\<V>)"
          using is_valid_problem_strips_operator_variable_sets(1) assms(1)
            v_in_precondition_set
          by auto
      }
      ultimately have "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) v = Some True"
        using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF assms(1, 2)]
        by presburger
    }
    hence "are_all_operators_applicable ?s (?\<pi> ! k)"
      using are_all_operators_applicable_set[of ?s "?\<pi> ! k"]
      by blast
  } moreover {
    {
      fix op\<^sub>1 op\<^sub>2
      assume op\<^sub>1_in_k_th_of_decoded_plan: "op\<^sub>1 \<in> set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
        and op\<^sub>2_in_k_th_of_decoded_plan: "op\<^sub>2 \<in> set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
      have op\<^sub>1_in_set_ops: "op\<^sub>1 \<in> set ((\<Pi>)\<^sub>\<O>)"
        and op\<^sub>2_in_set_ops: "op\<^sub>2 \<in> set ((\<Pi>)\<^sub>\<O>)"
        and op\<^sub>1_active_at_k: "\<not>lit_semantics \<A> ((Operator k (index ?ops op\<^sub>1))\<inverse>)"
        and op\<^sub>2_active_at_k: "\<not>lit_semantics \<A> ((Operator k (index ?ops op\<^sub>2))\<inverse>)"
        subgoal
          using decode_plan_step_element_then[OF k_lt_t op\<^sub>1_in_k_th_of_decoded_plan]
          by simp
        subgoal
          using decode_plan_step_element_then[OF k_lt_t op\<^sub>2_in_k_th_of_decoded_plan]
          by force
        subgoal
          using decode_plan_step_element_then[OF k_lt_t op\<^sub>1_in_k_th_of_decoded_plan]
          by simp
        subgoal
          using decode_plan_step_element_then[OF k_lt_t op\<^sub>2_in_k_th_of_decoded_plan]
          by simp
        done
      (* TODO the following two blocks could be contracted and refactored into a single lemma. *)
      {
        fix v
        assume v_in_add_effects_set_of_op\<^sub>1: "v \<in> set (add_effects_of op\<^sub>1)"
          and  v_in_delete_effects_set_of_op\<^sub>2: "v \<in> set (delete_effects_of op\<^sub>2)"
        let ?C\<^sub>1 = "{(Operator k (index ?ops op\<^sub>1))\<inverse>,
          (State (Suc k) (index ?vs v))\<^sup>+}"
          and ?C\<^sub>2 = "{(Operator k (index ?ops op\<^sub>2))\<inverse>,
          (State (Suc k) (index ?vs v))\<inverse>}"
        have "?C\<^sub>1 \<in> cnf ?\<Phi>\<^sub>E" and "?C\<^sub>2 \<in> cnf ?\<Phi>\<^sub>E"
          subgoal
            using cnf_of_operator_effect_encoding_contains_add_effect_clause_if[OF
                assms(1) k_lt_t op\<^sub>1_in_set_ops v_in_add_effects_set_of_op\<^sub>1]
            by blast
          subgoal
            using cnf_of_operator_effect_encoding_contains_delete_effect_clause_if[OF
                assms(1) k_lt_t op\<^sub>2_in_set_ops v_in_delete_effects_set_of_op\<^sub>2]
            by blast
          done
        then have "?C\<^sub>1 \<in> cnf ?\<Phi>" and "?C\<^sub>2 \<in> cnf ?\<Phi>"
          using cnf_of_encode_all_operator_effects_subset_cnf_of_encode_problem
          by blast+
        then have C\<^sub>1_true: "clause_semantics \<A> ?C\<^sub>1" and C\<^sub>2_true: "clause_semantics \<A> ?C\<^sub>2"
          using valuation_models_encoding_cnf_formula_equals[OF assms(1)] assms(2)
          unfolding cnf_semantics_def
          by blast+
        have "lit_semantics \<A> ((State (Suc k) (index ?vs v))\<^sup>+)"
          and "lit_semantics \<A> ((State (k + 1) (index ?vs v))\<inverse>)"
          subgoal
            using op\<^sub>1_active_at_k C\<^sub>1_true
            unfolding clause_semantics_def
            by blast
          subgoal
            using op\<^sub>2_active_at_k C\<^sub>2_true
            unfolding clause_semantics_def
            by fastforce
          done
        hence False
          by auto
      } moreover {
        fix v
        assume v_in_delete_effects_set_of_op\<^sub>1: "v \<in> set (delete_effects_of op\<^sub>1)"
          and  v_in_add_effects_set_of_op\<^sub>2: "v \<in> set (add_effects_of op\<^sub>2)"
        let ?C\<^sub>1 = "{(Operator k (index ?ops op\<^sub>1))\<inverse>, (State (Suc k) (index ?vs v))\<inverse>}"
          and ?C\<^sub>2 = "{(Operator k (index ?ops op\<^sub>2))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}"
        have "?C\<^sub>1 \<in> cnf ?\<Phi>\<^sub>E" and "?C\<^sub>2 \<in> cnf ?\<Phi>\<^sub>E"
          subgoal
            using cnf_of_operator_effect_encoding_contains_delete_effect_clause_if[OF
                assms(1) k_lt_t op\<^sub>1_in_set_ops v_in_delete_effects_set_of_op\<^sub>1]
            by fastforce
          subgoal
            using cnf_of_operator_effect_encoding_contains_add_effect_clause_if[OF
                assms(1) k_lt_t op\<^sub>2_in_set_ops v_in_add_effects_set_of_op\<^sub>2]
            by simp
          done
        then have "?C\<^sub>1 \<in> cnf ?\<Phi>" and "?C\<^sub>2 \<in> cnf ?\<Phi>"
          using cnf_of_encode_all_operator_effects_subset_cnf_of_encode_problem
          by blast+
        then have C\<^sub>1_true: "clause_semantics \<A> ?C\<^sub>1" and C\<^sub>2_true: "clause_semantics \<A> ?C\<^sub>2"
          using valuation_models_encoding_cnf_formula_equals[OF assms(1)] assms(2)
          unfolding cnf_semantics_def
          by blast+
        have "lit_semantics \<A> ((State (Suc k) (index ?vs v))\<inverse>)"
          and "lit_semantics \<A> ((State (k + 1) (index ?vs v))\<^sup>+)"
          subgoal
            using op\<^sub>1_active_at_k C\<^sub>1_true
            unfolding clause_semantics_def
            by blast
          subgoal
            using op\<^sub>2_active_at_k  C\<^sub>2_true
            unfolding clause_semantics_def
            by fastforce
          done
        hence False
          by simp
      }
      ultimately have "set (add_effects_of op\<^sub>1) \<inter> set (delete_effects_of op\<^sub>2) = {}"
        and "set (delete_effects_of op\<^sub>1) \<inter> set (add_effects_of op\<^sub>2) = {}"
        by blast+
    }
    hence "are_all_operator_effects_consistent (?\<pi> ! k)"
      using are_all_operator_effects_consistent_set[of "?\<pi> ! k"]
      by blast
  }
  ultimately show "are_all_operators_applicable ?s (?\<pi> ! k)"
    and "are_all_operator_effects_consistent (?\<pi> ! k)"
    by blast+
qed

\<comment> \<open> Show that for all operators \<open>op\<close> at timestep \<open>k\<close> of the plan
\<open>\<Phi>\<inverse> \<Pi> \<A> t\<close> decoded from the model \<open>\<A>\<close>, both add effects as
well as delete effects will hold in the next timestep \<open>Suc k\<close>. \<close>
lemma encode_problem_parallel_correct_iii:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
    and "k < length (\<Phi>\<inverse> \<Pi> \<A> t)"
    and "op \<in> set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
  shows "v \<in> set (add_effects_of op)
    \<longrightarrow> (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)) v = Some True"
  and "v \<in> set (delete_effects_of op)
    \<longrightarrow> (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)) v = Some False"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?\<Phi>\<^sub>F = "encode_all_operator_effects \<Pi> ?ops t"
    and ?A = "(\<Union>(t, op)\<in>{0..<t} \<times> set ((\<Pi>)\<^sub>\<O>).
      {{{ (Operator t (index ?ops op))\<inverse>, (State (Suc t) (index ?vs v))\<^sup>+ }}
        | v. v \<in> set (add_effects_of op)})"
    and ?B = "(\<Union>(t, op)\<in>{0..<t} \<times> set ((\<Pi>)\<^sub>\<O>).
       {{{ (Operator t (index ?ops op))\<inverse>,
          (State (Suc t) (index ?vs v))\<inverse> }}
        | v. v \<in> set (delete_effects_of op)})"
  have k_lt_t: "k < t"
    using decode_plan_length assms(3)
    by metis
  have op_is_valid: "op \<in> set ((\<Pi>)\<^sub>\<O>)"
    using decode_plan_step_element_then[OF k_lt_t assms(4)]
    by blast
  have k_op_included: "(k, op) \<in> ({0..<t} \<times> set ((\<Pi>)\<^sub>\<O>))"
    using k_lt_t op_is_valid
    by fastforce
  thus  "v \<in> set (add_effects_of op)
    \<longrightarrow> (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)) v = Some True"
    and "v \<in> set (delete_effects_of op)
      \<longrightarrow> (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)) v = Some False"
    proof (auto)
      assume v_is_add_effect: "v \<in> set (add_effects_of op)"
      have "\<A> (Operator k (index ?ops op))"
        using decode_plan_step_element_then[OF k_lt_t assms(4)]
        by blast
      moreover {
        have "{{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}}
          \<in> {{{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}}
            | v. v \<in> set (add_effects_of op)}"
          using v_is_add_effect
          by blast
        (* TODO slow. *)
        then have "{{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}} \<in> ?A"
          using k_op_included cnf_of_operator_encoding_structure
            UN_iff[of "{{(Operator t (index ?ops op))\<inverse>, (State (Suc t) (index ?vs v))\<^sup>+}}"
              _ "{0..<t} \<times> set ((\<Pi>)\<^sub>\<O>)"]
          by blast
        (* TODO slow. *)
        then have "{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+} \<in> \<Union> ?A"
          using Union_iff[of "{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}"]
          by blast
        (* TODO slow. *)
        moreover have "\<Union>?A \<subseteq> cnf ?\<Phi>\<^sub>F"
          using cnf_of_encode_all_operator_effects_structure
          by blast
        ultimately have "{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+} \<in> cnf ?\<Phi>\<^sub>F"
          using in_mono[of "\<Union>?A" "cnf ?\<Phi>\<^sub>F"]
          by presburger
      }
      (* TODO slow. *)
      ultimately have "\<A> (State (Suc k) (index ?vs v))"
        using cnf_of_encode_all_operator_effects_subset_cnf_of_encode_problem
              assms(2)[unfolded valuation_models_encoding_cnf_formula_equals_corollary[OF assms(1)]]
        unfolding Bex_def
        by fastforce
      thus "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)) v = Some True"
        using assms(1) assms(2)
          decode_state_at_encoding_variables_equals_some_of_valuation_if
          is_valid_problem_strips_operator_variable_sets(2) k_lt_t op_is_valid subsetD
          v_is_add_effect
        by fastforce
    next
      assume v_is_delete_effect: "v \<in> set (delete_effects_of op)"
      have "\<A> (Operator k (index ?ops op))"
        using decode_plan_step_element_then[OF k_lt_t assms(4)]
        by blast
      moreover {
        have "{{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse>}}
          \<in> {{{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse>}}
            | v. v \<in> set (delete_effects_of op)}"
          using v_is_delete_effect
          by blast
        (* TODO slow. *)
        then have "{{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse>}} \<in> ?B"
          using k_op_included cnf_of_encode_all_operator_effects_structure
            UN_iff[of "{{(Operator t (index ?ops op))\<inverse>, (State (Suc t) (index ?vs v))\<^sup>+}}"
              _ "{0..<t} \<times> set ((\<Pi>)\<^sub>\<O>)"]
          by blast
        (* TODO slow. *)
        then have "{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse>} \<in> \<Union> ?B"
          using Union_iff[of "{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse>}"]
          by blast
        (* TODO slow. *)
        moreover have "\<Union>?B \<subseteq> cnf ?\<Phi>\<^sub>F"
          using cnf_of_encode_all_operator_effects_structure Un_upper2[of "\<Union>?B" "\<Union>?A"]
          by fast
        ultimately have "{(Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse>} \<in> cnf ?\<Phi>\<^sub>F"
          using in_mono[of "\<Union>?B" "cnf ?\<Phi>\<^sub>F"]
          by presburger
      }
      (* TODO slow. *)
      ultimately have "\<not>\<A> (State (Suc k) (index ?vs v))"
        using cnf_of_encode_all_operator_effects_subset_cnf_of_encode_problem
          valuation_models_encoding_cnf_formula_equals_corollary[OF assms(1)] assms(2)
        by fastforce
      moreover have "Suc k \<le> t"
        using k_lt_t
        by fastforce
      moreover have "v \<in> set((\<Pi>)\<^sub>\<V>)"
        using v_is_delete_effect is_valid_problem_strips_operator_variable_sets(3) assms(1)
            op_is_valid
        by auto
      ultimately show "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)) v = Some False"
        using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF assms(1, 2)]
        by auto
    qed
qed

\<comment> \<open> In broad strokes, this lemma shows that the operator frame axioms ensure that state is
propagated—i.e. the valuation of a variable does not change inbetween time steps—, if there is
no operator active which has an effect on a given variable a: i.e.

  \begin{align*}
    \mathcal A &\vDash (\lnot a_i \land a_{i+1})
      \longrightarrow \bigvee\{op_i, k: op_i \text{ has add effect } a\}\\
    \mathcal A &\vDash (a_i \land \lnot a_{i+1})
      \longrightarrow \bigvee\{op_i, k: op_i \text{ has delete effect } a\}
  \end{align*}

Now, if the disjunctions are empty—i.e. if no operator which is activated at time step $k$ has
either a positive or negative effect—, we have by simplification

  \begin{align*}
    \mathcal A \vDash \lnot(\lnot a_i \land a_{i+1})
      &\equiv \mathcal A \vDash a_i \lor \lnot a_{i+1}\\
    \mathcal A \vDash \lnot(a_i \land \lnot a_{i+1})
      &\equiv \mathcal A \vDash \lnot a_i \lor a_{i+1}
  \end{align*}

hence

   \begin{align*}
      \mathcal A &\vDash (\lnot a_i \lor a_{i+1}) \land (a_i \lor \lnot a_{i+1})\\
      \leadsto \mathcal A &\vDash \{\{\lnot a_i, a_{i+1}\}, \{a_i, \lnot a_{i+1}\}\}
    \end{align*}

The lemma characterizes this simplification.
\footnote{This part of the soundness proof is only treated very briefly in
\cite[theorem 3.1, p.1044]{DBLP:journals/ai/RintanenHN06}} \<close>
lemma encode_problem_parallel_correct_iv:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
    and "k < t"
    and "v \<in> set ((\<Pi>)\<^sub>\<V>)"
    and "\<not>(\<exists>op \<in> set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k).
      v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op))"
  shows "cnf_semantics \<A> {{ (State k (index (strips_problem.variables_of \<Pi>) v))\<inverse>
    , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }}"
    and "cnf_semantics \<A> {{ (State k (index (strips_problem.variables_of \<Pi>) v))\<^sup>+
      , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }}"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?\<Phi> = "\<Phi> \<Pi> t"
    and ?\<Phi>\<^sub>F = "encode_all_frame_axioms \<Pi> t"
    and ?\<pi>\<^sub>k = "(\<Phi>\<inverse> \<Pi> \<A> t) ! k"
    and ?A = "\<Union>(k, v) \<in> ({0..<t} \<times> set ?vs).
      {{{ (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse>  }
        \<union> {(Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }}}"
    and ?B = "\<Union>(k, v) \<in> ({0..<t} \<times> set ?vs).
      {{{ (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }
        \<union> { (Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }}}"
    and ?C = "{ (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse>  }
        \<union> {(Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
    and ?C' = "{ (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }
        \<union> { (Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }"
    (* TODO refactor (next two blocks)? *)
  have k_v_included: "(k, v) \<in> ({..<t} \<times> set ((\<Pi>)\<^sub>\<V>))"
    using assms(3, 4)
    by blast
  have operator_encoding_subset_encoding: "cnf ?\<Phi>\<^sub>F \<subseteq> cnf ?\<Phi>"
    using cnf_of_encode_problem_structure(4)
    unfolding encode_problem_def
    by fast
  \<comment> \<open> Given the premise that no operator in \<open>\<pi>\<^sub>k\<close> exists with add-effect respectively delete
effect \<open>v\<close>, we have the following situation for the EPC (effect precondition) sets:
  \begin{itemize}
    \item assuming \<open>op\<close> is in \<open>set ?ops\<close>, either \<open>op\<close> is in \<open>\<pi>\<^sub>k\<close> (then it doesn't have effect on \<open>v\<close>
      and therefore is not in either of the sets), or if is not, then
      \<open>\<A> (Operator k (index ?ops op) = \<bottom>\<close> by definition of \<open>decode_plan\<close>; moreover,
    \item assuming \<open>op\<close> is not in \<open>set ?ops\<close>—this is implicitely encoded as \<open>Operator k
      (length ?ops)\<close> and \<open>\<A> (Operator k (length ?ops))\<close> may or may not be true—, then it's not
      in either of the sets.
  \end{itemize}.
Altogether, we have the situation that the sets only have members \<open>Operator k (index ?ops op)\<close>
with \<open>\<A> (Operator k (index ?ops op)) = \<bottom>\<close>, hence the clause can be reduced to the state
variable literals.

More concretely, the following proof block shows that the following two conditions hold for the
operators:

  @{text[display, indent=4] "\<forall>op. op \<in> { ((Operator k (index ?ops op))\<^sup>+)
      | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op)}
    \<longrightarrow> \<not>lit_semantics \<A> op" }

and

  @{text[display, indent=4] "\<forall>op. op \<in> { ((Operator k (index ?ops op))\<^sup>+)
      | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op)}
    \<longrightarrow> \<not>lit_semantics \<A> op" }

Hence, the operators are irrelevant for \<open>cnf_semantics \<A> { C }\<close> where \<open>C\<close> is
a clause encoding a positive or negative transition frame axiom for a given variable \<open>v\<close> of the
problem. \<close>
  (* TODO refactor. *)
  {
    let ?add = "{ ((Operator k (index ?ops op))\<^sup>+)
        | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
      and ?delete = "{ ((Operator k (index ?ops op))\<^sup>+)
        | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }"
    {
      fix op
      assume operator_encoding_in_add: "(Operator k (index ?ops op))\<^sup>+ \<in> ?add"
      hence "\<not>lit_semantics \<A> ((Operator k (index ?ops op))\<^sup>+)"
        proof (cases "op \<in> set ?\<pi>\<^sub>k")
          case True
          then have "v \<notin> set (add_effects_of op)"
            using assms(5)
            by simp
          then have "(Operator k (index ?ops op))\<^sup>+ \<notin> ?add"
            by fastforce
          thus ?thesis
            using operator_encoding_in_add
            by blast
        next
          case False
          then show ?thesis
            proof (cases "op \<in> set ?ops")
              case True
              {
                let ?A = "{ ?ops ! index ?ops op |op.
                   op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> \<A> (Operator k (index ?ops op))}"
                assume "lit_semantics \<A> ((Operator k (index ?ops op))\<^sup>+)"
                moreover have operator_active_at_k: "\<A> (Operator k (index ?ops op))"
                  using calculation
                  by auto
                moreover have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
                  using True
                  by force
                moreover have "(?ops ! index ?ops op) \<in> ?A"
                  using calculation(2, 3)
                  by blast
                ultimately have "op \<in> set ?\<pi>\<^sub>k"
                  using decode_plan_step_element_then_i[OF assms(3)]
                  by auto
                hence False
                  using False
                  by blast
              }
              thus ?thesis
                by blast
            next
              case False
              then have "op \<notin> {op \<in> set ?ops. v \<in> set (add_effects_of op)}"
                by blast
              moreover have "?add =
                (\<lambda>op. (Operator k (index ?ops op))\<^sup>+)
                  ` { op \<in> set ?ops. v \<in> set (add_effects_of op) }"
                using setcompr_eq_image[of "\<lambda>op. (Operator k (index ?ops op))\<^sup>+"
                    "\<lambda>op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op)"]
                by blast
              (* TODO slow. *)
              ultimately have "(Operator k (index ?ops op))\<^sup>+ \<notin> ?add"
                by force
              thus ?thesis using operator_encoding_in_add
                by blast
            qed
        qed
    } moreover {
      fix op
      assume operator_encoding_in_delete: "((Operator k (index ?ops op))\<^sup>+) \<in> ?delete"
      hence "\<not>lit_semantics \<A> ((Operator k (index ?ops op))\<^sup>+)"
        proof (cases "op \<in> set ?\<pi>\<^sub>k")
          case True
          then have "v \<notin> set (delete_effects_of op)"
            using assms(5)
            by simp
          then have "(Operator k (index ?ops op))\<^sup>+ \<notin> ?delete"
            by fastforce
          thus ?thesis
            using operator_encoding_in_delete
            by blast
        next
          case False
          then show ?thesis
            proof (cases "op \<in> set ?ops")
              case True
              {
                let ?A = "{ ?ops ! index ?ops op |op.
                   op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> \<A> (Operator k (index ?ops op))}"
                assume "lit_semantics \<A> ((Operator k (index ?ops op))\<^sup>+)"
                moreover have operator_active_at_k: "\<A> (Operator k (index ?ops op))"
                  using calculation
                  by auto
                moreover have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
                  using True
                  by force
                moreover have "(?ops ! index ?ops op) \<in> ?A"
                  using calculation(2, 3)
                  by blast
                ultimately have "op \<in> set ?\<pi>\<^sub>k"
                  using decode_plan_step_element_then_i[OF assms(3)]
                  by auto
                hence False
                  using False
                  by blast
              }
              thus ?thesis
                by blast
            next
              case False
              then have "op \<notin> { op \<in> set ?ops. v \<in> set (delete_effects_of op) }"
                by blast
              moreover have "?delete =
                (\<lambda>op. (Operator k (index ?ops op))\<^sup>+)
                  ` { op \<in> set ?ops. v \<in> set (delete_effects_of op) }"
                using setcompr_eq_image[of "\<lambda>op. (Operator k (index ?ops op))\<^sup>+"
                    "\<lambda>op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op)"]
                by blast
              (* TODO slow. *)
              ultimately have "(Operator k (index ?ops op))\<^sup>+ \<notin> ?delete"
                by force
              thus ?thesis using operator_encoding_in_delete
                by blast
            qed
        qed
    }
    ultimately have "\<forall>op. op \<in> ?add \<longrightarrow> \<not>lit_semantics \<A> op"
    and "\<forall>op. op \<in> ?delete \<longrightarrow> \<not>lit_semantics \<A> op"
      by blast+
  } note nb = this
  {
    let ?Ops = "{ (Operator k (index ?ops op))\<^sup>+
      | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
    have "?Ops \<subseteq> ?C"
      by blast
    moreover have "?C - ?Ops = { (State k (index ?vs v))\<^sup>+ , (State (Suc k) (index ?vs v))\<inverse>  }"
      by fast
    moreover have "\<forall>L \<in> ?Ops. \<not> lit_semantics \<A> L"
      using nb(1)
      by blast
    (* TODO slow. *)
    ultimately have "clause_semantics \<A> ?C
      = clause_semantics \<A> { (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse> }"
      using lit_semantics_reducible_to_subset_if[of ?Ops ?C]
      by presburger
  }  moreover {
    let ?Ops' = "{ (Operator k (index ?ops op))\<^sup>+
      | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }"
    have "?Ops' \<subseteq> ?C'"
      by blast
    moreover have "?C' - ?Ops' = { (State k (index ?vs v))\<inverse> , (State (Suc k) (index ?vs v))\<^sup>+ }"
      by fast
    moreover have "\<forall>L \<in> ?Ops'. \<not> lit_semantics \<A> L"
      using nb(2)
      by blast
    (* TODO slow. *)
    ultimately have "clause_semantics \<A> ?C'
      = clause_semantics \<A> { (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }"
      using lit_semantics_reducible_to_subset_if[of ?Ops' ?C']
      by presburger
  }  moreover {
    have cnf_semantics_\<A>_\<Phi>:"cnf_semantics \<A> (cnf ?\<Phi>)"
      using valuation_models_encoding_cnf_formula_equals[OF assms(1)] assms(2)
      by blast
    have k_v_included: "(k, v) \<in> ({..<t} \<times> set ((\<Pi>)\<^sub>\<V>))"
      using assms(3, 4)
      by blast
    (* TODO slow. *)
    have c_in_un_a: "?C \<in> \<Union>?A" and c'_in_un_b: "?C' \<in> \<Union>?B"
      using k_v_included
      by force+
    (* TODO slow. *)
    then have "?C \<in> cnf ?\<Phi>\<^sub>F" and "?C' \<in> cnf ?\<Phi>\<^sub>F"
      subgoal
        using cnf_of_encode_all_frame_axioms_structure UnI1[of "?C" "\<Union>?A" "\<Union>?B"] c_in_un_a
        by metis
      subgoal
        using cnf_of_encode_all_frame_axioms_structure UnI2[of "?C'" "\<Union>?B" "\<Union>?A"] c'_in_un_b
        by metis
      done
    then have "{ ?C } \<subseteq> cnf ?\<Phi>\<^sub>F" and c'_subset_frame_axiom_encoding: "{ ?C' } \<subseteq> cnf ?\<Phi>\<^sub>F"
      by blast+
    then have "{ ?C } \<subseteq> cnf ?\<Phi>" and "{ ?C' } \<subseteq> cnf ?\<Phi>"
      subgoal
        using operator_encoding_subset_encoding
        by fast
      subgoal
        using c'_subset_frame_axiom_encoding operator_encoding_subset_encoding
        by fast
      done
    (* TODO slow. *)
    hence "cnf_semantics \<A> { ?C }" and "cnf_semantics \<A> { ?C' }"
      using cnf_semantics_\<A>_\<Phi> model_for_cnf_is_model_of_all_subsets
      by fastforce+
  }
  ultimately show "cnf_semantics \<A> {{ (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }}"
    and "cnf_semantics \<A> {{ (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse> }}"
    unfolding cnf_semantics_def
    by blast+
qed

lemma encode_problem_parallel_correct_v:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
    and "k < length (\<Phi>\<inverse> \<Pi> \<A> t)"
  shows "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)) = execute_parallel_operator (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
    and ?s\<^sub>k = "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k"
    and ?s\<^sub>k' = "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)"
  let ?t\<^sub>k' = "execute_parallel_operator ?s\<^sub>k (?\<pi> ! k)"
    and ?\<pi>\<^sub>k = "?\<pi> ! k"
  have k_lt_t: "k < t" and k_lte_t: "k \<le> t" and suc_k_lte_t: "Suc k \<le> t"
    using decode_plan_length[of ?\<pi> \<Pi> \<A> t] assms(3)
    by (argo, fastforce+)
  then have operator_preconditions_hold:
    "are_all_operators_applicable ?s\<^sub>k ?\<pi>\<^sub>k \<and> are_all_operator_effects_consistent ?\<pi>\<^sub>k"
    using encode_problem_parallel_correct_ii[OF assms(1, 2, 3)]
    by blast
  \<comment> \<open> We show the goal in classical fashion by proving that
      @{text[display, indent=4] "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k) v
        = execute_parallel_operator (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k)
          ((\<Phi>\<inverse> \<Pi> \<A> t) ! k) v"}
    ---i.e. the state decoded at time \<open>k + 1\<close> is equivalent to the state obtained by executing the
    parallel operator \<open>(\<Phi>\<inverse> \<Pi> \<A> t) ! k\<close> on the previous state
    \<open>\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k\<close>—for all variables \<open>v\<close> given \<open>k < t\<close>, a model \<open>\<A>\<close>,
    and makespan \<open>t\<close>. \<close>
  moreover {
    {
      fix v
      assume v_in_dom_s\<^sub>k':"v \<in> dom ?s\<^sub>k'"
      then have s\<^sub>k'_not_none: "?s\<^sub>k' v \<noteq> None"
        by blast
      hence "?s\<^sub>k' v = ?t\<^sub>k' v"
        proof (cases "\<exists>op \<in> set ?\<pi>\<^sub>k. v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op)")
          case True
          then obtain op
            where op_in_\<pi>\<^sub>k: "op \<in> set ?\<pi>\<^sub>k"
            and "v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op)"
            by blast
          then consider (v_is_add_effect) "v \<in> set (add_effects_of op)"
            | (v_is_delete_effect) "v \<in> set (delete_effects_of op)"
            by blast
          then show ?thesis
            proof (cases)
              case v_is_add_effect
              then have "?s\<^sub>k' v = Some True"
                using encode_problem_parallel_correct_iii(1)[OF assms(1, 2, 3) op_in_\<pi>\<^sub>k]
                  v_is_add_effect
                by blast
              moreover have "are_all_operators_applicable (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
                and "are_all_operator_effects_consistent ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
                using operator_preconditions_hold v_is_add_effect
                by blast+
              moreover have "?t\<^sub>k' v = Some True"
                using execute_parallel_operator_positive_effect_if[of
                    "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k" "(\<Phi>\<inverse> \<Pi> \<A> t) ! k"] op_in_\<pi>\<^sub>k
                  v_is_add_effect calculation(2, 3)
                by blast
              ultimately show ?thesis
                by argo
            next
              case v_is_delete_effect
              then have "?s\<^sub>k' v = Some False"
                using encode_problem_parallel_correct_iii(2)[OF assms(1, 2, 3) op_in_\<pi>\<^sub>k]
                  v_is_delete_effect
                by blast
              moreover have "are_all_operators_applicable (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
                and "are_all_operator_effects_consistent ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
                using operator_preconditions_hold
                by blast+
              moreover have "?t\<^sub>k' v = Some False"
                using execute_parallel_operator_effect(2) op_in_\<pi>\<^sub>k
                  v_is_delete_effect calculation(2, 3)
                by fast
              moreover have "?t\<^sub>k' v = Some False"
                by (meson execute_parallel_operator_negative_effect_if op_in_\<pi>\<^sub>k operator_preconditions_hold v_is_delete_effect)
              ultimately show ?thesis
                by argo
            qed
        next
          case False
          (* TODO slow. *)
          then have "?t\<^sub>k' v = ?s\<^sub>k v"
            using execute_parallel_operator_no_effect_if
            by fastforce
          moreover {
            have v_in_set_vs: "v \<in> set ((\<Pi>)\<^sub>\<V>)"
              using decode_state_at_valid_variable[OF s\<^sub>k'_not_none].
            then have state_propagation_positive:
              "cnf_semantics \<A> {{(State k (index ?vs v))\<inverse>
                , (State (Suc k) (index ?vs v))\<^sup>+}}"
            and state_propagation_negative:
              "cnf_semantics \<A> {{(State k (index ?vs v))\<^sup>+
                , (State (Suc k) (index ?vs v))\<inverse>}}"
              using encode_problem_parallel_correct_iv[OF assms(1, 2) k_lt_t _ False]
              by fastforce+
            consider (s\<^sub>k'_v_positive) "?s\<^sub>k' v = Some True"
              | (s\<^sub>k'_v_negative) "?s\<^sub>k' v = Some False"
              using s\<^sub>k'_not_none
              by fastforce
            hence "?s\<^sub>k' v = ?s\<^sub>k v"
              proof (cases)
                case s\<^sub>k'_v_positive
                then have "lit_semantics \<A> ((State (Suc k) (index ?vs v))\<^sup>+)"
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
                      assms(1, 2) suc_k_lte_t v_in_set_vs]
                  by fastforce
                (* TODO slow. *)
                then have "lit_semantics \<A> ((State k (index ?vs v))\<^sup>+)"
                  using state_propagation_negative
                  unfolding cnf_semantics_def clause_semantics_def
                  by fastforce
                then show ?thesis
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
                      assms(1, 2) k_lte_t v_in_set_vs] s\<^sub>k'_v_positive
                  by fastforce
              next
                case s\<^sub>k'_v_negative
                then have "\<not>lit_semantics \<A> ((State (Suc k) (index ?vs v))\<^sup>+)"
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[
                      OF assms(1, 2) suc_k_lte_t v_in_set_vs]
                  by fastforce
                (* TODO slow. *)
                then have "\<not>lit_semantics \<A> ((State k (index ?vs v))\<^sup>+)"
                  using state_propagation_positive
                  unfolding cnf_semantics_def clause_semantics_def
                  by fastforce
                then show ?thesis
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
                      assms(1, 2) k_lte_t v_in_set_vs] s\<^sub>k'_v_negative
                  by fastforce
              qed
          }
          ultimately show ?thesis
            by argo
        qed
      }
    hence "?s\<^sub>k' \<subseteq>\<^sub>m ?t\<^sub>k'"
      using map_le_def
      by blast
  }
  moreover {
    {
      fix v
      assume "v \<in> dom ?t\<^sub>k'"
      then have t\<^sub>k'_not_none: "?t\<^sub>k' v \<noteq> None"
        by blast
      {
        {
          assume contradiction: "v \<notin> set ((\<Pi>)\<^sub>\<V>)"
          then have "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) v = None"
            using decode_state_at_valid_variable
            by fastforce
          then obtain op
            where op_in: "op \<in> set ((\<Phi>\<inverse> \<Pi> \<A> t) ! k)"
              and v_is_or: "v \<in> set (add_effects_of op)
                \<or> v \<in> set (delete_effects_of op)"
            using execute_parallel_operators_strips_none_if_contraposition[OF
                t\<^sub>k'_not_none]
            by blast
          have op_in: "op \<in> set ((\<Pi>)\<^sub>\<O>)"
              using op_in decode_plan_step_element_then(1) k_lt_t
              by blast
          consider (A) "v \<in> set (add_effects_of op)"
            | (B) "v \<in> set (delete_effects_of op)"
            using v_is_or
            by blast
          hence False
            proof (cases)
              case A
              then have "v \<in> set ((\<Pi>)\<^sub>\<V>)"
                using is_valid_problem_strips_operator_variable_sets(2)[OF
                    assms(1)] op_in A
                by blast
              thus False
                using contradiction
                by blast
            next
              case B
              then have "v \<in> set ((\<Pi>)\<^sub>\<V>)"
                using is_valid_problem_strips_operator_variable_sets(3)[OF
                    assms(1)] op_in B
                by blast
              thus False
                using contradiction
                by blast
            qed
          }
      }
      hence v_in_set_vs: "v \<in> set ((\<Pi>)\<^sub>\<V>)"
        by blast
      hence "?t\<^sub>k' v = ?s\<^sub>k' v"
        proof (cases "(\<exists>op\<in>set ?\<pi>\<^sub>k. v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op))")
          case True
          then obtain op
            where op_in_set_\<pi>\<^sub>k: "op \<in> set ?\<pi>\<^sub>k"
            and v_options: "v \<in> set (add_effects_of op) \<or> v \<in> set (delete_effects_of op)"
            by blast
          then have "op \<in> set ((\<Pi>)\<^sub>\<O>)"
            using decode_plan_step_element_then[OF k_lt_t]
            by blast
          then consider (v_is_add_effect) "v \<in> set (add_effects_of op)"
            | (v_is_delete_effect) "v \<in> set (delete_effects_of op)"
            using v_options
            by blast
          thus ?thesis
            proof (cases)
              case v_is_add_effect
              then have "?t\<^sub>k' v = Some True"
                using execute_parallel_operator_positive_effect_if[OF _ _ op_in_set_\<pi>\<^sub>k]
                  operator_preconditions_hold
                by blast
              moreover have "?s\<^sub>k' v = Some True"
                using encode_problem_parallel_correct_iii(1)[OF assms(1, 2, 3) op_in_set_\<pi>\<^sub>k]
                  v_is_add_effect
                by blast
              ultimately show ?thesis
                by argo
            next
              case v_is_delete_effect
              then have "?t\<^sub>k' v = Some False"
                using execute_parallel_operator_negative_effect_if[OF _ _ op_in_set_\<pi>\<^sub>k]
                  operator_preconditions_hold
                by blast
              moreover have "?s\<^sub>k' v = Some False"
                using encode_problem_parallel_correct_iii(2)[OF assms(1, 2, 3) op_in_set_\<pi>\<^sub>k]
                  v_is_delete_effect
                by blast
              ultimately show ?thesis
                by argo
            qed
        next
          case False
          have state_propagation_positive:
            "cnf_semantics \<A> {{(State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+}}"
          and state_propagation_negative:
            "cnf_semantics \<A> {{(State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse>}}"
            using encode_problem_parallel_correct_iv[OF assms(1, 2) k_lt_t v_in_set_vs
                False]
            by blast+
          {
            have all_op_in_set_\<pi>\<^sub>k_have_no_effect:
              "\<forall>op \<in> set ?\<pi>\<^sub>k. v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op)"
              using False
              by blast
            then have "?t\<^sub>k' v = ?s\<^sub>k v"
              using execute_parallel_operator_no_effect_if[OF all_op_in_set_\<pi>\<^sub>k_have_no_effect]
              by blast
          } note t\<^sub>k'_equals_s\<^sub>k = this
          {
            have "?s\<^sub>k v \<noteq> None"
              using t\<^sub>k'_not_none t\<^sub>k'_equals_s\<^sub>k
              by argo
            then consider (s\<^sub>k_v_is_some_true) "?s\<^sub>k v = Some True"
              | (s\<^sub>k_v_is_some_false) "?s\<^sub>k v = Some False"
              by fastforce
          }
          then show ?thesis
            proof (cases)
              case s\<^sub>k_v_is_some_true
              moreover {
                have "lit_semantics \<A> ((State k (index ?vs v))\<^sup>+)"
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
                      assms(1, 2) k_lte_t v_in_set_vs] s\<^sub>k_v_is_some_true
                  by simp
                then have "lit_semantics \<A> ((State (Suc k) (index ?vs v))\<^sup>+)"
                  using state_propagation_positive
                  unfolding cnf_semantics_def clause_semantics_def
                  by fastforce
                then have "?s\<^sub>k' v = Some True"
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
                      assms(1, 2) suc_k_lte_t v_in_set_vs]
                  by fastforce
              }
              ultimately show ?thesis
                using t\<^sub>k'_equals_s\<^sub>k
                by simp
            next
              case s\<^sub>k_v_is_some_false
              moreover {
                have "lit_semantics \<A> ((State k (index ?vs v))\<inverse>)"
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
                      assms(1, 2) k_lte_t v_in_set_vs] s\<^sub>k_v_is_some_false
                  by simp
                then have "lit_semantics \<A> ((State (Suc k) (index ?vs v))\<inverse>)"
                  using state_propagation_negative
                  unfolding cnf_semantics_def clause_semantics_def
                  by fastforce
                then have "?s\<^sub>k' v = Some False"
                  using decode_state_at_encoding_variables_equals_some_of_valuation_if[OF
                      assms(1, 2) suc_k_lte_t v_in_set_vs]
                  by fastforce
              }
              ultimately show ?thesis
                using t\<^sub>k'_equals_s\<^sub>k
                by simp
            qed
        qed
    }
    hence "?t\<^sub>k' \<subseteq>\<^sub>m ?s\<^sub>k'"
    using map_le_def
    by blast
  }
  ultimately show ?thesis
    using map_le_antisym
    by blast
qed

lemma encode_problem_parallel_correct_vi:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
    and "k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) (\<Phi>\<inverse> \<Pi> \<A> t))"
  shows "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) (\<Phi>\<inverse> \<Pi> \<A> t) ! k
    = \<Phi>\<^sub>S\<inverse> \<Pi> \<A> k"
  using assms
proof -
  let ?I = "(\<Pi>)\<^sub>I"
    and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
  let ?\<tau> = "trace_parallel_plan_strips ?I ?\<pi>"
  show ?thesis
    using assms
    proof (induction k)
      case 0
      hence "?\<tau> ! 0 = ?I"
        using trace_parallel_plan_strips_head_is_initial_state
        by blast
      moreover have "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> 0 = ?I"
        using decode_state_at_initial_state[OF assms(1, 2)]
        by simp
      ultimately show ?case
        by simp
    next
      case (Suc k)
      let ?\<tau>\<^sub>k = "trace_parallel_plan_strips ?I ?\<pi> ! k"
        and ?s\<^sub>k = "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> k"
      have k_lt_length_\<tau>_minus_one: "k < length ?\<tau> - 1" and k_lt_length_\<tau>: "k < length ?\<tau>"
        using Suc.prems(3)
        by linarith+
      \<comment> \<open> Use the induction hypothesis to obtain the proposition for the previous step $k$.
        Then, show that applying the $k$-th parallel operator in the plan $\pi$ on either the state
        obtained from the trace or decoded from the model yields the same successor state. \<close>
      {
        have "?\<tau> ! k = execute_parallel_plan ?I (take k ?\<pi>)"
          using trace_parallel_plan_plan_prefix k_lt_length_\<tau>
          by blast
        hence "?\<tau>\<^sub>k = ?s\<^sub>k"
          using Suc.IH[OF assms(1, 2) k_lt_length_\<tau>]
          by blast
      }
      moreover have "trace_parallel_plan_strips ?I ?\<pi> ! Suc k
        = execute_parallel_operator ?\<tau>\<^sub>k (?\<pi> ! k)"
        using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one]
        by blast
      moreover {
        thm Suc.prems(3)
        have "length (trace_parallel_plan_strips ?I ?\<pi>) \<le> length ?\<pi> + 1"
          using length_trace_parallel_plan_strips_lte_length_plan_plus_one
          by blast
        then have "k < length ?\<pi>"
          using Suc.prems(3)
          unfolding Suc_eq_plus1
          by linarith
        hence "\<Phi>\<^sub>S\<inverse> \<Pi> \<A> (Suc k)
          = execute_parallel_operator ?s\<^sub>k (?\<pi> ! k)"
          using encode_problem_parallel_correct_v[OF assms(1, 2)]
          by simp
      }
      ultimately show ?case
        by argo
    qed
qed

lemma encode_problem_parallel_correct_vii:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
  shows "length (map (decode_state_at \<Pi> \<A>)
      [0..<Suc (length (\<Phi>\<inverse> \<Pi> \<A> t))])
    = length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) (\<Phi>\<inverse> \<Pi> \<A> t))"
proof -
  let ?I = "(\<Pi>)\<^sub>I"
    and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
  let ?\<sigma> = "map (decode_state_at \<Pi> \<A>) [0..<Suc (length ?\<pi>)]"
    and ?\<tau> = "trace_parallel_plan_strips ?I ?\<pi>"
  let ?l = "length ?\<tau> "
  let ?k = "?l - 1"
  show ?thesis
    proof (rule ccontr)
      assume length_\<sigma>_neq_length_\<tau>: "length ?\<sigma> \<noteq> length ?\<tau>"
      {
        have "length ?\<sigma> = length ?\<pi> + 1"
          by fastforce
        moreover have "length ?\<tau> \<le> length ?\<pi> + 1"
          using length_trace_parallel_plan_strips_lte_length_plan_plus_one
          by blast
        moreover have "length ?\<tau> < length ?\<pi> + 1"
          using length_\<sigma>_neq_length_\<tau> calculation
          by linarith
      } note nb\<^sub>1 = this
      {
        have "0 < length ?\<tau>"
          using trace_parallel_plan_strips_not_nil..
        then have "length ?\<tau> - 1 < length ?\<pi>"
          using nb\<^sub>1
          by linarith
      } note nb\<^sub>2 = this
      {
        obtain k' where "length ?\<tau> = Suc k'"
          using less_imp_Suc_add[OF length_trace_parallel_plan_gt_0]
          by blast
        hence "?k < length ?\<pi>"
          using nb\<^sub>2
          by blast
      } note nb\<^sub>3 = this
      {
        have "?\<tau> ! ?k = execute_parallel_plan ?I (take ?k ?\<pi>)"
          using trace_parallel_plan_plan_prefix[of ?k]
            length_trace_minus_one_lt_length_trace
          by blast
        thm encode_problem_parallel_correct_vi[OF assms(1, 2)] nb\<^sub>3
        moreover have "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> ?k) = ?\<tau> ! ?k"
          using encode_problem_parallel_correct_vi[OF assms(1, 2)
              length_trace_minus_one_lt_length_trace]..
        ultimately have "(\<Phi>\<^sub>S\<inverse> \<Pi> \<A> ?k)  = execute_parallel_plan ?I (take ?k ?\<pi>)"
          by argo
      } note nb\<^sub>4 = this
      {
        have "are_all_operators_applicable (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> ?k) (?\<pi> ! ?k)"
          and "are_all_operator_effects_consistent (?\<pi> ! ?k)"
          using encode_problem_parallel_correct_ii(1, 2)[OF assms(1, 2)] nb\<^sub>3
          by blast+
        \<comment> \<open> Unsure why \<open>calculation(1, 2)\<close> is needed for this proof step. Should just require the
          default proof. \<close>
        moreover have "\<not>are_all_operators_applicable (\<Phi>\<^sub>S\<inverse> \<Pi> \<A> ?k) (?\<pi> ! ?k)"
          and "\<not>are_all_operator_effects_consistent (?\<pi> ! ?k)"
          using length_trace_parallel_plan_strips_lt_length_plan_plus_one_then[OF nb\<^sub>1]
            calculation(1, 2)
          unfolding nb\<^sub>3 nb\<^sub>4
          by blast+
        ultimately have False
          by blast
      }
      thus False.
    qed
qed

lemma encode_problem_parallel_correct_x:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
  shows "map (decode_state_at \<Pi> \<A>)
      [0..<Suc (length (\<Phi>\<inverse> \<Pi> \<A> t))]
    = trace_parallel_plan_strips ((\<Pi>)\<^sub>I) (\<Phi>\<inverse> \<Pi> \<A> t)"
proof -
  let ?I = "(\<Pi>)\<^sub>I"
    and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
  let ?\<sigma> = "map (decode_state_at \<Pi> \<A>) [0..<Suc (length ?\<pi>)]"
    and ?\<tau> = "trace_parallel_plan_strips ?I ?\<pi>"
  {
    have "length ?\<tau> = length ?\<sigma>"
      using encode_problem_parallel_correct_vii[OF assms]..
    moreover {
      fix k
      assume k_lt_length_\<tau>: "k < length ?\<tau>"
      then have "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) (\<Phi>\<inverse> \<Pi> \<A> t) ! k
        = \<Phi>\<^sub>S\<inverse> \<Pi> \<A> k"
        using encode_problem_parallel_correct_vi[OF assms]
        by blast
      moreover {
        have "length ?\<tau> \<le> length ?\<pi> + 1"
          using length_trace_parallel_plan_strips_lte_length_plan_plus_one
          by blast
        then have "k < length ?\<pi> + 1"
          using k_lt_length_\<tau>
          by linarith
        then have "k < Suc (length ?\<pi>) - 0"
          by simp
        hence "?\<sigma> ! k = \<Phi>\<^sub>S\<inverse> \<Pi> \<A> k"
          using nth_map_upt[of k "Suc (length ?\<pi>)" 0]
          by auto
      }
      ultimately have "?\<tau> ! k = ?\<sigma> ! k"
        by argo
    }
    ultimately have "?\<tau> = ?\<sigma>"
      using list_eq_iff_nth_eq[of ?\<tau> ?\<sigma>]
      by blast
  }
  thus ?thesis
    by argo
qed

lemma encode_problem_parallel_correct_xi:
  fixes \<Pi>:: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
   and "\<A> \<Turnstile> \<Phi> \<Pi> t"
   and "ops \<in> set (\<Phi>\<inverse> \<Pi> \<A> t)"
   and "op \<in> set ops"
 shows "op \<in> set ((\<Pi>)\<^sub>\<O>)"
proof -
  let ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
  have "length ?\<pi> = t"
    using decode_plan_length
    by force
  moreover obtain k where "k < length ?\<pi>" and "ops = ?\<pi> ! k"
    using in_set_conv_nth[of ops ?\<pi>] assms(3)
    unfolding calculation
    by blast
  ultimately show ?thesis
    using assms(4) decode_plan_step_element_then(1)
    by force
qed


text \<open> To show soundness, we have to prove the following: given the existence of a model
\<^term>\<open>\<A>\<close> of the basic SATPlan encoding \<^term>\<open>encode_problem \<Pi> t\<close> for a given valid problem \<^term>\<open>\<Pi>\<close>
and hypothesized plan length \<^term>\<open>t\<close>, the decoded plan \<^term>\<open>\<pi> \<equiv> \<Phi>\<inverse> \<Pi> \<A> t\<close> is a parallel solution
for \<^term>\<open>\<Pi>\<close>.

We show this theorem by showing equivalence between the execution trace of the decoded plan and the
sequence of states

  @{text[display, indent=4] "\<sigma> = map (\<lambda> k. \<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) [0..<Suc (length ?\<pi>)]" }

decoded from the model \<^term>\<open>\<A>\<close>. Let

  @{text[display, indent=4] "\<tau> \<equiv> trace_parallel_plan_strips I \<pi>"}

be the trace of \<^term>\<open>\<pi>\<close>. Theorem \ref{isathm:soundness-satplan-encoding} first establishes the
equality \<^term>\<open>\<sigma> = \<tau>\<close> of the decoded state sequence and the trace of \<^term>\<open>\<pi>\<close>.
We can then derive that \<^term>\<open>G \<subseteq>\<^sub>m last \<sigma>\<close> by lemma \ref{isathm:parallel-solution-trace-strips}, i.e. the last
state reached by plan execution (and moreover the last state decoded from the model), satisfies the
goal state \<^term>\<open>G\<close> defined by the problem. By lemma \ref{isathm:parallel-solution-trace-strips}, we
can conclude that \<^term>\<open>\<pi>\<close> is a solution for \<^term>\<open>I\<close> and \<^term>\<open>G\<close>.

Moreover, we show that all operators \<^term>\<open>op\<close> in all parallel operators \<^term>\<open>ops \<in> set \<pi>\<close>
are also contained in \<^term>\<open>\<O>\<close>. This is the case because the plan decoding function reverses the
encoding function (which only encodes operators in \<^term>\<open>\<O>\<close>).

By definition \ref{isadef:parallel-solution-strips} this means that \<^term>\<open>\<pi>\<close> is a parallel solution
for \<^term>\<open>\<Pi>\<close>. Moreover \<^term>\<open>\<pi>\<close> has length \<^term>\<open>t\<close> as confirmed by lemma
\isaname{decode_plan_length}.
\footnote{This lemma is used in the proof but not shown.} \<close>

theorem  encode_problem_parallel_sound:
  assumes "is_valid_problem_strips \<Pi>"
    and "\<A> \<Turnstile> \<Phi> \<Pi> t"
  shows "is_parallel_solution_for_problem \<Pi> (\<Phi>\<inverse> \<Pi> \<A> t)"
  proof -
    let ?ops = "strips_problem.operators_of \<Pi>"
      and ?I = "(\<Pi>)\<^sub>I"
      and ?G = "(\<Pi>)\<^sub>G"
      and ?\<pi> = "\<Phi>\<inverse> \<Pi> \<A> t"
    let ?\<sigma> = "map (\<lambda> k. \<Phi>\<^sub>S\<inverse> \<Pi> \<A> k) [0..<Suc (length ?\<pi>)]"
      and ?\<tau> = "trace_parallel_plan_strips ?I ?\<pi>"
    {
      have "?\<sigma> = ?\<tau>"
        using encode_problem_parallel_correct_x[OF assms].
      moreover {
        have "length ?\<pi> = t"
          using decode_plan_length
          by auto
        then have "?G \<subseteq>\<^sub>m last ?\<sigma>"
          using decode_state_at_goal_state[OF assms]
          by simp
      }
      ultimately have "((\<Pi>)\<^sub>G) \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) (\<Phi>\<inverse> \<Pi> \<A> t)"
        using execute_parallel_plan_reaches_goal_iff_goal_is_last_element_of_trace
        by auto
    }
    moreover have "\<forall>ops \<in> set ?\<pi>. \<forall>op \<in> set ops. op \<in> set ((\<Pi>)\<^sub>\<O>)"
      using encode_problem_parallel_correct_xi[OF assms(1, 2)]
      by auto
    ultimately show ?thesis
      unfolding is_parallel_solution_for_problem_def
      unfolding list_all_iff ListMem_iff operators_of_def STRIPS_Representation.operators_of_def
      by fastforce
  qed

value  "stop" (* Tell document preparation to stop collecting for the last tag *)



subsection "Completeness"

(* TODO make abbreviation *)
definition empty_valuation :: "sat_plan_variable valuation" ("\<A>\<^sub>0")
  where "empty_valuation \<equiv>  (\<lambda>_. False)"

abbreviation valuation_for_state
  :: "'variable list
    \<Rightarrow>'variable strips_state
    \<Rightarrow> nat
    \<Rightarrow> 'variable
    \<Rightarrow> sat_plan_variable valuation
    \<Rightarrow> sat_plan_variable valuation"
  where "valuation_for_state vs s k v \<A>
    \<equiv> \<A>(State k (index vs v) := (s v = Some True))"

\<comment> \<open> Since the trace may be shorter than the plan length even though the last trace element
subsumes the goal state---namely in case plan execution is impossible due to violation of the
execution condition but the reached state serendipitously subsumes the goal state---, we also have
to repeat the valuation for all time steps \<^term>\<open>k' \<in> {length \<tau>..(length \<pi> + 1)}\<close> for all \
\<^term>\<open>v \<in> \<V>\<close> (see \<^term>\<open>\<A>\<^sub>2\<close>). \<close>
definition valuation_for_state_variables
  :: "'variable strips_problem
    \<Rightarrow> 'variable strips_operator list list
    \<Rightarrow> 'variable strips_state list
    \<Rightarrow> sat_plan_variable valuation"
  where "valuation_for_state_variables \<Pi> \<pi> \<tau> \<equiv> let
      t' = length \<tau>
      ; \<tau>\<^sub>\<Omega> = \<tau> ! (t' - 1)
      ; vs = variables_of \<Pi>
      ; V\<^sub>1 = { State k (index vs v) | k v. k \<in> {0..<t'} \<and> v \<in> set vs }
      ; V\<^sub>2 = { State k (index vs v) | k v. k \<in> {t'..(length \<pi> + 1)} \<and> v \<in> set vs }
      ; \<A>\<^sub>1 = foldr
        (\<lambda>(k, v) \<A>. valuation_for_state (variables_of \<Pi>) (\<tau> ! k) k v \<A>)
        (List.product [0..<t'] vs)
        \<A>\<^sub>0
      ; \<A>\<^sub>2 = foldr
        (\<lambda>(k, v) \<A>. valuation_for_state (variables_of \<Pi>) \<tau>\<^sub>\<Omega> k v \<A>)
        (List.product [t'..<length \<pi> + 2] vs)
        \<A>\<^sub>0
    in override_on (override_on \<A>\<^sub>0 \<A>\<^sub>1 V\<^sub>1) \<A>\<^sub>2 V\<^sub>2"

\<comment> \<open> The valuation is left to yield false for the potentially remaining
\<^term>\<open>k' \<in> {length \<tau>..(length \<pi> + 1)}\<close> since no more operators are executed after the trace ends
anyway. The definition of \<^term>\<open>\<A>\<^sub>0\<close> as the valuation that is false for every argument ensures
this implicitely. \<close>
definition valuation_for_operator_variables
  :: "'variable strips_problem
    \<Rightarrow> 'variable strips_operator list list
    \<Rightarrow> 'variable strips_state list
    \<Rightarrow> sat_plan_variable valuation"
  where "valuation_for_operator_variables \<Pi> \<pi> \<tau> \<equiv> let
      ops = operators_of \<Pi>
      ; Op = { Operator k (index ops op) | k op. k \<in> {0..<length \<tau> - 1} \<and> op \<in> set ops }
    in override_on
      \<A>\<^sub>0
      (foldr
        (\<lambda>(k, op) \<A>. \<A>(Operator k (index ops op) := True))
        (concat (map (\<lambda>k. map (Pair k) (\<pi> ! k)) [0..<length \<tau> - 1]))
        \<A>\<^sub>0)
      Op"


text \<open> The completeness proof requires that we show that the SATPlan encoding \<^term>\<open>\<Phi> \<Pi> t\<close> of a
problem \<^term>\<open>\<Pi>\<close> has a model \<^term>\<open>\<A>\<close> in case a solution \<^term>\<open>\<pi>\<close> with length \<^term>\<open>t\<close> exists.
Since a plan corresponds to a state trace \<^term>\<open>\<tau> \<equiv> trace_parallel_plan_strips I \<pi>\<close> with
  @{text[display, indent=4] "\<tau> ! k = execute_parallel_plan I (take k \<pi>)"}
for all \<^term>\<open>k < length \<tau>\<close> we can construct a valuation \<^term>\<open>\<A>\<^sub>V\<close> modeling the state sequence in
\<^term>\<open>\<tau>\<close> by letting
  @{text[display, indent=4] "\<A>(State k (index vs v) := (s v = Some True))"}
or all \<^term>\<open>v \<in> \<V>\<close> where \<^term>\<open>s \<equiv> \<tau> ! k\<close> .
\footnote{It is helpful to remember at this point, that the trace elements of a solution contain
the states reached by plan prefix execution (lemma \ref{isathm:trace-elements-and-plan-prefixes}).}

Similarly to \<^term>\<open>\<A>\<^sub>V\<close>, we obtain an operator valuation \<^term>\<open>\<A>\<^sub>O\<close> by defining
  @{text[display, indent=4] "\<A>(Operator k (index ops op) := True)"}
for all operators \<^term>\<open>op \<in> \<O>\<close> s.t. \<^term>\<open>op \<in> set (\<pi> ! k)\<close> for all \<^term>\<open>k < length \<tau> - 1\<close>.

The overall valuation for the plan execution \<^term>\<open>\<A>\<close> can now be constructed by combining the
state variable valuation \<^term>\<open>\<A>\<^sub>V\<close> and operator valuation \<^term>\<open>\<A>\<^sub>O\<close>. \<close>

definition  valuation_for_plan
  :: "'variable strips_problem
    \<Rightarrow> 'variable strips_operator list list
    \<Rightarrow> sat_plan_variable valuation"
  where "valuation_for_plan \<Pi> \<pi> \<equiv> let
      vs = variables_of \<Pi>
      ; ops = operators_of \<Pi>
      ; \<tau> = trace_parallel_plan_strips (initial_of \<Pi>) \<pi>
      ; t = length \<pi>
      ; t' = length \<tau>
      ; \<A>\<^sub>V = valuation_for_state_variables \<Pi> \<pi> \<tau>
      ; \<A>\<^sub>O = valuation_for_operator_variables \<Pi> \<pi> \<tau>
      ; V = { State k (index vs v)
        | k v. k \<in> {0..<t + 1} \<and> v \<in> set vs }
      ; Op = { Operator k (index ops op)
        | k op. k \<in> {0..<t} \<and> op \<in> set ops }
    in override_on (override_on \<A>\<^sub>0 \<A>\<^sub>V V) \<A>\<^sub>O Op"


\<comment> \<open> Show that in case of an encoding with makespan zero, it suffices to show that a given
model satisfies the initial state and goal state encodings. \<close>
(* TODO refactor. *)
lemma model_of_encode_problem_makespan_zero_iff:
  "\<A> \<Turnstile> \<Phi> \<Pi> 0 \<longleftrightarrow> \<A> \<Turnstile> \<Phi>\<^sub>I \<Pi> \<^bold>\<and> (\<Phi>\<^sub>G \<Pi>) 0"
proof -
  have "encode_operators \<Pi> 0 = \<^bold>\<not>\<bottom> \<^bold>\<and> \<^bold>\<not>\<bottom>"
    unfolding encode_operators_def encode_all_operator_effects_def
      encode_all_operator_preconditions_def
    by simp
  moreover have "encode_all_frame_axioms \<Pi> 0 = \<^bold>\<not>\<bottom>"
    unfolding encode_all_frame_axioms_def
    by simp
  ultimately show ?thesis
    unfolding encode_problem_def SAT_Plan_Base.encode_problem_def encode_initial_state_def
      encode_goal_state_def
    by simp
qed

(* TODO refactor. *)
lemma empty_valution_is_False[simp]: "\<A>\<^sub>0 v = False"
  unfolding empty_valuation_def..

lemma  model_initial_state_set_valuations:
  assumes "is_valid_problem_strips \<Pi>"
  shows "set (map (\<lambda>v. case ((\<Pi>)\<^sub>I) v of Some b
          \<Rightarrow> \<A>\<^sub>0(State 0 (index (strips_problem.variables_of \<Pi>) v) := b)
        | _ \<Rightarrow> \<A>\<^sub>0)
      (strips_problem.variables_of \<Pi>))
    = { \<A>\<^sub>0(State 0 (index (strips_problem.variables_of \<Pi>) v) := the (((\<Pi>)\<^sub>I) v))
      | v. v \<in> set ((\<Pi>)\<^sub>\<V>) }"
proof -
  let ?I = "(\<Pi>)\<^sub>I"
    and ?vs = "strips_problem.variables_of \<Pi>"
  let ?f = "\<lambda>v. case ((\<Pi>)\<^sub>I) v of Some b
    \<Rightarrow> \<A>\<^sub>0(State 0 (index ?vs v) := b) | _ \<Rightarrow> \<A>\<^sub>0"
    and ?g = "\<lambda>v. \<A>\<^sub>0(State 0 (index ?vs v) := the (?I v))"
  let ?\<A>s = "map ?f ?vs"
  have nb\<^sub>1: "dom ?I = set ((\<Pi>)\<^sub>\<V>)"
    using is_valid_problem_strips_initial_of_dom assms
    by fastforce
  {
    {
      fix v
      assume "v \<in> dom ?I"
      hence "?f v = ?g v"
        using nb\<^sub>1
        by fastforce
    }
    hence "?f ` set ((\<Pi>)\<^sub>\<V>) = ?g ` set ((\<Pi>)\<^sub>\<V>)"
      using nb\<^sub>1
      by force
  }
  then have "set ?\<A>s = ?g ` set ((\<Pi>)\<^sub>\<V>)"
    unfolding set_map
    by simp
  thus ?thesis
    by blast
qed

(* TODO refactor *)
lemma valuation_of_state_variable_implies_lit_semantics_if:
  assumes "v \<in> dom S"
    and "\<A> (State k (index vs v)) = the (S v)"
  shows "lit_semantics \<A> (literal_formula_to_literal (encode_state_variable k (index vs v) (S v)))"
proof -
  let ?L = "literal_formula_to_literal (encode_state_variable k (index vs v) (S v))"
  consider (True) "S v = Some True"
    | (False) "S v = Some False"
    using assms(1)
    by fastforce
  thus ?thesis
    unfolding encode_state_variable_def
    using assms(2)
    by (cases, force+)
qed

(* TODO refactor \<open>Fun_Supplement\<close>? *)
lemma foldr_fun_upd:
  assumes "inj_on f (set xs)"
    and "x \<in> set xs"
  shows "foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A> (f x) = g x"
  using assms
proof (induction xs)
  case (Cons a xs)
  then show ?case
    proof (cases "xs = []")
      case True
      then have "x = a"
        using Cons.prems(2)
        by simp
      thus ?thesis
        by simp
    next
      case False
      thus ?thesis
        proof (cases "a = x")
        next
          case False
          {
            from False
            have "x \<in> set xs"
              using Cons.prems(2)
              by simp
            moreover have "inj_on f (set xs)"
              using Cons.prems(1)
              by fastforce
            ultimately have "(foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A>) (f x) = g x"
              using Cons.IH
              by blast
          } moreover {
            \<comment> \<open> Follows from modus tollens on the definition of @{text "inj_on"}. \<close>
            have "f a \<noteq> f x"
              using Cons.prems False
              by force
            moreover have "foldr (\<lambda>x \<A>. \<A>(f x := g x)) (a # xs) \<A>
              = (foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A>)(f a := g a)"
              by simp
            ultimately have "foldr (\<lambda>x \<A>. \<A>(f x := g x)) (a # xs) \<A> (f x)
              = (foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A>) (f x)"
              unfolding fun_upd_def
              by presburger
          } ultimately show ?thesis
            by argo
       qed simp
   qed
qed fastforce

lemma foldr_fun_no_upd:
  assumes "inj_on f (set xs)"
    and "y \<notin> f ` set xs"
  shows "foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A> y = \<A> y"
  using assms
proof (induction xs)
  case (Cons a xs)
  {
    have "inj_on f (set xs)" and "y \<notin> f ` set xs"
      using Cons.prems
      by (fastforce, simp)
    hence "foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A> y = \<A> y"
      using Cons.IH
      by blast
  }
  moreover {
    have "f a \<noteq> y"
      using Cons.prems(2)
      by auto
    moreover have "foldr (\<lambda>x \<A>. \<A>(f x := g x)) (a # xs) \<A>
      = (foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A>)(f a := g a)"
      by simp
    ultimately have "foldr (\<lambda>x \<A>. \<A>(f x := g x)) (a # xs) \<A> y
      = (foldr (\<lambda>x \<A>. \<A>(f x := g x)) xs \<A>) y"
      unfolding fun_upd_def
      by presburger
  }
  ultimately show ?case
    by argo
qed simp

\<comment> \<open> We only use the part of the characterization of \<open>\<A>\<close> which pertains to the state
variables here. \<close>
lemma encode_problem_parallel_complete_i:
  fixes \<Pi>::"'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) \<pi>"
     "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow>  (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)
        \<and> (\<not>\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> ((trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v \<noteq> Some True))"
  shows "\<A> \<Turnstile> \<Phi>\<^sub>I \<Pi>"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?I = "(\<Pi>)\<^sub>I"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?\<Phi>\<^sub>I = "\<Phi>\<^sub>I \<Pi>"
  let ?\<tau> = "trace_parallel_plan_strips ?I \<pi>"
  {
    fix C
    assume "C \<in> cnf ?\<Phi>\<^sub>I"
    then obtain v
      where v_in_set_vs: "v \<in> set ?vs"
      and C_is: "C = { literal_formula_to_literal (encode_state_variable 0 (index ?vs v) (?I v)) }"
      using cnf_of_encode_initial_state_set_ii[OF assms(1)]
      by auto
    {
      have "0 < length ?\<tau>"
        using trace_parallel_plan_strips_not_nil
        by blast
      then have "\<A> (State 0 (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! 0) v = Some True"
        and "\<not>\<A> (State 0 (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> ((trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! 0) v \<noteq> Some True)"
        using assms(3)
        by (presburger+)
    } note nb = this
    {
      let ?L = "literal_formula_to_literal (encode_state_variable 0 (index ?vs v) (?I v))"
      have \<tau>_0_is: "?\<tau> ! 0 = ?I"
        using trace_parallel_plan_strips_head_is_initial_state
        by blast
      have v_in_dom_I: "v \<in> dom ?I"
        using is_valid_problem_strips_initial_of_dom assms(1) v_in_set_vs
        by fastforce
      then consider (I_v_is_Some_True) "?I v = Some True"
        | (I_v_is_Some_False) "?I v = Some False"
        by fastforce
      hence "lit_semantics \<A> ?L"
          unfolding encode_state_variable_def
          using assms(3) \<tau>_0_is nb
          by (cases, force+)
    }
    hence "clause_semantics \<A> C"
      unfolding clause_semantics_def C_is
      by blast
  }
  thus ?thesis
    using is_cnf_encode_initial_state[OF assms(1)] is_nnf_cnf cnf_semantics
    unfolding cnf_semantics_def
    by blast
qed

\<comment> \<open> Plans may terminate early (i.e. by reaching a state satisfying the goal state before
reaching the time point corresponding to the plan length). We therefore have to show the goal by
splitting cases on whether the plan successfully terminated early.
If not, we can just derive the goal from the assumptions pertaining to \<open>\<A>\<close> Otherwise, we
have to first show that the goal was reached (albeit early) and that our valuation \<open>\<A>\<close>
reflects the termination of plan execution after the time point at which the goal was reached. \<close>
lemma encode_problem_parallel_complete_ii:
  fixes \<Pi>::"'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) \<pi>"
    and "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow> (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)"
    and "\<forall>v l. l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) \<and> l < length \<pi> + 1
      \<longrightarrow> \<A> (State l (index (strips_problem.variables_of \<Pi>) v))
        = \<A> (State (length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1)
          (index (strips_problem.variables_of \<Pi>) v))"
  shows "\<A> \<Turnstile> (\<Phi>\<^sub>G \<Pi>)(length \<pi>)"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?I = "(\<Pi>)\<^sub>I"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?\<Phi>\<^sub>I = "\<Phi>\<^sub>I \<Pi>"
    and ?t = "length \<pi>"
    and ?\<Phi>\<^sub>G = "(\<Phi>\<^sub>G \<Pi>) (length \<pi>)"
  let ?\<tau> = "trace_parallel_plan_strips ?I \<pi>"
  let ?t' = "length ?\<tau>"
  {
    fix v
    assume G_of_v_is_not_None: "?G v \<noteq> None"
    have "?G \<subseteq>\<^sub>m last ?\<tau>"
      using execute_parallel_plan_reaches_goal_iff_goal_is_last_element_of_trace assms(2)
      by blast
    also have "\<dots> = ?\<tau> ! (?t' - 1)"
      using last_conv_nth[OF trace_parallel_plan_strips_not_nil].
    finally have "?G \<subseteq>\<^sub>m ?\<tau> ! (?t' - 1)"
      by argo
    hence "(?\<tau> ! (?t' - 1)) v = ?G v"
      using G_of_v_is_not_None
      unfolding map_le_def
      by force
  } note nb\<^sub>1 = this
  (* TODO refactor. *)
  \<comment> \<open> Discriminate on whether the trace has full length or not and show that the model
  valuation of the state variables always correspond to the (defined) goal state values. \<close>
  {
    fix v
    assume G_of_v_is_not_None: "?G v \<noteq> None"
    hence "\<A> (State ?t (index ?vs v)) \<longleftrightarrow> ?G v = Some True"
      proof (cases "?t' = ?t + 1")
        case True
        moreover have "?t < ?t'"
          using calculation
          by fastforce
        moreover have "\<A> (State ?t (index ?vs v)) \<longleftrightarrow> (?\<tau> ! ?t) v = Some True"
          using assms(3) calculation(2)
          by blast
        ultimately show ?thesis
          using nb\<^sub>1[OF G_of_v_is_not_None]
          by force
      next
        case False
        {
          have "?t' < ?t + 1"
            using length_trace_parallel_plan_strips_lte_length_plan_plus_one False
              le_neq_implies_less
            by blast
          moreover have "\<A> (State ?t (index ?vs v)) = \<A> (State (?t' - 1) (index ?vs v))"
            using assms(4) calculation
            by simp
          moreover have "?t' - 1 < ?t'"
            using trace_parallel_plan_strips_not_nil length_greater_0_conv[of ?\<tau>]
              less_diff_conv2[of 1 ?t' ?t']
            by force
          moreover have "\<A> (State (?t' - 1) (index ?vs v)) \<longleftrightarrow> (?\<tau> ! (?t' - 1)) v = Some True"
            using assms(3) calculation(3)
            by blast
          ultimately have "\<A> (State ?t (index ?vs v)) \<longleftrightarrow> (?\<tau> ! (?t' - 1)) v = Some True"
            by blast
        }
        thus ?thesis
          using nb\<^sub>1[OF G_of_v_is_not_None]
          by presburger
      qed
  } note nb\<^sub>2 = this
  {
    fix C
    assume C_in_cnf_of_\<Phi>\<^sub>G: "C \<in> cnf ?\<Phi>\<^sub>G"

    moreover obtain v
      where "v \<in> set ?vs"
        and G_of_v_is_not_None: "?G v \<noteq> None"
      and C_is: "C = { literal_formula_to_literal (encode_state_variable ?t (index ?vs v)
        (?G v)) }"
      using cnf_of_encode_goal_state_set_ii[OF assms(1)] calculation
      by auto
    consider (G_of_v_is_Some_True) "?G v = Some True"
      | (G_of_v_is_Some_False) "?G v = Some False"
      using G_of_v_is_not_None
      by fastforce
    then have "clause_semantics \<A> C"
      using nb\<^sub>2 C_is
      unfolding clause_semantics_def encode_state_variable_def
      by (cases, force+)
  }
  thus ?thesis
    using cnf_semantics[OF is_nnf_cnf[OF encode_goal_state_is_cnf[OF assms(1)]]]
    unfolding cnf_semantics_def
    by blast
qed

\<comment> \<open> We are not using the full characterization of \<open>\<A>\<close> here since it's not needed. \<close>
(* TODO make private *)
lemma encode_problem_parallel_complete_iii_a:
  fixes \<Pi>::"'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) \<pi>"
    and "C \<in> cnf (encode_all_operator_preconditions \<Pi> (strips_problem.operators_of \<Pi>) (length \<pi>))"
    and "\<forall>k op. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1
      \<longrightarrow> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) = (op \<in> set (\<pi> ! k))"
    and "\<forall>l op. l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1 \<and> l < length \<pi>
      \<longrightarrow> \<not>\<A> (Operator l (index (strips_problem.operators_of \<Pi>) op))"
    and "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow>  (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)"
  shows "clause_semantics \<A> C"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
    and ?t = "length \<pi>"
  let ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  (* TODO slow. *)
  obtain k op
    where k_and_op_are: "(k, op) \<in> ({0..<?t} \<times> set ((\<Pi>)\<^sub>\<O>))"
      and "C \<in> (\<Union>v \<in> set (precondition_of op). {{ (Operator k (index ?ops op))\<inverse>
        , (State k (index ?vs v))\<^sup>+ }})"
    using cnf_of_encode_all_operator_preconditions_structure assms(3)
      UN_E[of C ]
    by auto
  then obtain v
    where v_in_preconditions_of_op: "v \<in> set (precondition_of op)"
      and C_is: "C = { (Operator k (index ?ops op))\<inverse>, (State k (index ?vs v))\<^sup>+ }"
    by blast
  thus ?thesis
    proof (cases "k < length ?\<tau> - 1")
      case k_lt_length_\<tau>_minus_one: True
      thus ?thesis
        proof (cases "op \<in> set (\<pi> ! k)")
          case True
          {
            have "are_all_operators_applicable (?\<tau> ! k) (\<pi> ! k)"
              using trace_parallel_plan_strips_operator_preconditions k_lt_length_\<tau>_minus_one
              by blast
            then have "(?\<tau> ! k) v = Some True"
              using are_all_operators_applicable_set v_in_preconditions_of_op True
              by fast
            hence "\<A> (State k (index ?vs v))"
              using assms(6) k_lt_length_\<tau>_minus_one
              by force
          }
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by fastforce
        next
          case False
          then have "\<not>\<A> (Operator k (index ?ops op))"
            using assms(4) k_lt_length_\<tau>_minus_one
            by blast
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by fastforce
        qed
    next
      case False
      then have "k \<ge> length ?\<tau> - 1" "k < ?t"
        using k_and_op_are
        by(force, simp)
      then have "\<not>\<A> (Operator k (index ?ops op))"
        using assms(5)
        by blast
      thus ?thesis
        unfolding clause_semantics_def
        using C_is
        by fastforce
    qed
qed

\<comment> \<open> We are not using the full characterization of \<open>\<A>\<close> here since it's not needed. \<close>
(* TODO make private *)
lemma encode_problem_parallel_complete_iii_b:
  fixes \<Pi>::"'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) \<pi>"
    and "C \<in> cnf (encode_all_operator_effects \<Pi> (strips_problem.operators_of \<Pi>) (length \<pi>))"
    and "\<forall>k op. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1
      \<longrightarrow> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) = (op \<in> set (\<pi> ! k))"
    and "\<forall>l op. l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1 \<and> l < length \<pi>
      \<longrightarrow> \<not>\<A> (Operator l (index (strips_problem.operators_of \<Pi>) op))"
    and "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow>  (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)"
  shows "clause_semantics \<A> C"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?vs = "strips_problem.variables_of \<Pi>"
    and ?t = "length \<pi>"
  let ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?A = "(\<Union>(k, op) \<in> {0..<?t} \<times> set ((\<Pi>)\<^sub>\<O>).
    \<Union>v \<in> set (add_effects_of op).
      {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }})"
    and ?B = "(\<Union>(k, op) \<in> {0..<?t} \<times> set ((\<Pi>)\<^sub>\<O>).
      \<Union>v \<in> set (delete_effects_of op).
         {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse> }})"
  consider (C_in_A) "C \<in> ?A"
    | (C_in_B) "C \<in> ?B"
    using Un_iff[of C ?A ?B] cnf_of_encode_all_operator_effects_structure assms(3)
     by (metis C_in_A C_in_B)
  thus ?thesis
    proof (cases)
      case C_in_A
      then obtain k op
        where k_and_op_are: "(k, op) \<in> {0..<?t} \<times> set((\<Pi>)\<^sub>\<O>)"
          and "C \<in> (\<Union>v \<in> set (add_effects_of op).
            {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }})"
        by blast
      then obtain v where v_in_add_effects_of_op: "v \<in> set (add_effects_of op)"
        and C_is: "C = { (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }"
        by blast
      thus ?thesis
        proof (cases "k < length ?\<tau> - 1")
          case k_lt_length_\<tau>_minus_one: True
          thus ?thesis
            proof (cases "op \<in> set (\<pi> ! k)")
              case True
              {
                then have "are_all_operators_applicable (?\<tau> ! k) (\<pi> ! k)"
                  and "are_all_operator_effects_consistent (\<pi> ! k)"
                  using trace_parallel_plan_strips_operator_preconditions k_lt_length_\<tau>_minus_one
                  by blast+
                hence "execute_parallel_operator (?\<tau> ! k) (\<pi> ! k) v = Some True"
                  using execute_parallel_operator_positive_effect_if[
                    OF _ _ True v_in_add_effects_of_op, of "?\<tau> ! k"]
                  by blast
              }
              then have \<tau>_Suc_k_is_Some_True: "(?\<tau> ! Suc k) v = Some True"
                using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one]
                by argo
              have "\<A> (State (Suc k) (index ?vs v))"
                using assms(6) k_lt_length_\<tau>_minus_one \<tau>_Suc_k_is_Some_True
                by fastforce
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by fastforce
            next
              case False
              then have "\<not>\<A> (Operator k (index ?ops op))"
                using assms(4) k_lt_length_\<tau>_minus_one
                by blast
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by force
            qed
        next
          case False
          then have "k \<ge> length ?\<tau> - 1" and "k < ?t"
            using k_and_op_are
            by auto
          then have "\<not>\<A> (Operator k (index ?ops op))"
            using assms(5)
            by blast
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by fastforce
        qed
    next
      \<comment> \<open> This case is completely symmetrical to the one above. \<close>
      case C_in_B
      then obtain k op
        where k_and_op_are: "(k, op) \<in> {0..<?t} \<times> set ((\<Pi>)\<^sub>\<O>)"
          and "C \<in> (\<Union>v \<in> set (delete_effects_of op).
            {{ (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse> }})"
        by blast
      then obtain v where v_in_delete_effects_of_op: "v \<in> set (delete_effects_of op)"
        and C_is: "C = { (Operator k (index ?ops op))\<inverse>, (State (Suc k) (index ?vs v))\<inverse> }"
        by blast
      thus ?thesis
        proof (cases "k < length ?\<tau> - 1")
          case k_lt_length_\<tau>_minus_one: True
          thus ?thesis
            proof (cases "op \<in> set (\<pi> ! k)")
              case True
              {
                then have "are_all_operators_applicable (?\<tau> ! k) (\<pi> ! k)"
                  and "are_all_operator_effects_consistent (\<pi> ! k)"
                  using trace_parallel_plan_strips_operator_preconditions k_lt_length_\<tau>_minus_one
                  by blast+
                hence "execute_parallel_operator (?\<tau> ! k) (\<pi> ! k) v = Some False"
                  using execute_parallel_operator_negative_effect_if[
                    OF _ _ True v_in_delete_effects_of_op, of "?\<tau> ! k"]
                  by blast
              }
              then have \<tau>_Suc_k_is_Some_True: "(?\<tau> ! Suc k) v = Some False"
                using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one]
                by argo
              have "\<not>\<A> (State (Suc k) (index ?vs v))"
                using assms(6) k_lt_length_\<tau>_minus_one \<tau>_Suc_k_is_Some_True
                by fastforce
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by fastforce
            next
              case False
              then have "\<not>\<A> (Operator k (index ?ops op))"
                using assms(4) k_lt_length_\<tau>_minus_one
                by blast
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by force
            qed
        next
          case False
          then have "k \<ge> length ?\<tau> - 1" and "k < ?t"
            using k_and_op_are
            by auto
          then have "\<not>\<A> (Operator k (index ?ops op))"
            using assms(5)
            by blast
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by fastforce
        qed
    qed
qed

(* TODO make private *)
lemma encode_problem_parallel_complete_iii:
  fixes \<Pi>::"'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "(\<Pi>)\<^sub>G \<subseteq>\<^sub>m execute_parallel_plan ((\<Pi>)\<^sub>I) \<pi>"
    and "\<forall>k op. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1
      \<longrightarrow> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) = (op \<in> set (\<pi> ! k))"
    and "\<forall>l op. l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1 \<and> l < length \<pi>
      \<longrightarrow> \<not>\<A> (Operator l (index (strips_problem.operators_of \<Pi>) op))"
    and "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow>  (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)"
  shows "\<A> \<Turnstile> encode_operators \<Pi> (length \<pi>)"
proof -
  let ?t = "length \<pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
  let ?\<Phi>\<^sub>O = "encode_operators \<Pi> ?t"
    and ?\<Phi>\<^sub>P = "encode_all_operator_preconditions \<Pi> ?ops?t"
    and ?\<Phi>\<^sub>E = "encode_all_operator_effects \<Pi> ?ops ?t"
  {
    fix C
    assume "C \<in> cnf ?\<Phi>\<^sub>O"
    then consider (C_in_precondition_encoding) "C \<in> cnf ?\<Phi>\<^sub>P"
      | (C_in_effect_encoding) "C \<in> cnf ?\<Phi>\<^sub>E"
      using cnf_of_operator_encoding_structure
      by blast
    hence "clause_semantics \<A> C"
      proof (cases)
        case C_in_precondition_encoding
        thus ?thesis
          using encode_problem_parallel_complete_iii_a[OF assms(1, 2) _ assms(3, 4, 5)]
          by blast
      next
        case C_in_effect_encoding
        thus ?thesis
          using encode_problem_parallel_complete_iii_b[OF assms(1, 2) _ assms(3, 4, 5)]
          by blast
      qed
  }
  thus ?thesis
    using encode_operators_is_cnf[OF assms(1)] is_nnf_cnf cnf_semantics
    unfolding cnf_semantics_def
    by blast
qed

(* TODO make private *)
lemma encode_problem_parallel_complete_iv_a:
  fixes \<Pi> :: "'a strips_problem"
  assumes "STRIPS_Semantics.is_parallel_solution_for_problem \<Pi> \<pi>"
    and "\<forall>k op. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1
      \<longrightarrow> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) = (op \<in> set (\<pi> ! k))"
    and "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow>  (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)"
    and "\<forall>v l. l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) \<and> l < length \<pi> + 1
      \<longrightarrow> \<A> (State l (index (strips_problem.variables_of \<Pi>) v))
        = \<A> (State
          (length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1)
          (index (strips_problem.variables_of \<Pi>) v))"
    and "C \<in> \<Union> (\<Union>(k, v) \<in> {0..<length \<pi>} \<times> set ((\<Pi>)\<^sub>\<V>).
      {{{ (State k (index (strips_problem.variables_of \<Pi>) v))\<^sup>+
          , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<inverse> }
        \<union> { (Operator k (index (strips_problem.operators_of \<Pi>) op))\<^sup>+
          |op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (add_effects_of op) }}})"
  shows "clause_semantics \<A> C"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?t = "length \<pi>"
  let ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?A = "(\<Union>(k, v) \<in> {0..<?t} \<times> set ?vs.
    {{{ (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse> }
      \<union> { (Operator k (index ?ops op))\<^sup>+ |op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }}})"
  (* TODO refactor *)
  {
    (* TODO slow *)
    obtain C' where "C' \<in> ?A" and C_in_C': "C \<in> C'"
      using Union_iff assms(5)
      by auto
    then obtain k v
      where "(k, v) \<in> {0..<?t} \<times> set ?vs"
      and "C' \<in> {{{ (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse> }
        \<union> { (Operator k (index ?ops op))\<^sup>+ |op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }}}"
      using UN_E
      by blast
    hence "\<exists>k v.
      k \<in> {0..<?t}
      \<and> v \<in> set ?vs
      \<and> C = { (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse> }
        \<union> { (Operator k (index ?ops op))\<^sup>+ |op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
      using C_in_C'
      by blast
  }
  then obtain k v
    where k_in: "k \<in> {0..<?t}"
      and v_in_vs: "v \<in> set ?vs"
      and C_is: "C = { (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse> }
        \<union> { (Operator k (index ?ops op))\<^sup>+ |op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
    by blast
  show ?thesis
    proof (cases "k < length ?\<tau> - 1")
      case k_lt_length_\<tau>_minus_one: True
      then have k_lt_t: "k < ?t"
        using k_in
        by force
      have all_operators_applicable: "are_all_operators_applicable (?\<tau> ! k) (\<pi> ! k)"
        and all_operator_effects_consistent: "are_all_operator_effects_consistent (\<pi> ! k)"
        using trace_parallel_plan_strips_operator_preconditions[OF k_lt_length_\<tau>_minus_one]
        by simp+
      then consider (A) "\<exists>op \<in> set (\<pi> ! k). v \<in> set (add_effects_of op)"
        | (B) "\<exists>op \<in> set (\<pi> ! k). v \<in> set (delete_effects_of op)"
        | (C) "\<forall>op \<in> set (\<pi> ! k). v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op)"
        by blast
      thus ?thesis
        proof (cases)
          case A
          moreover obtain op
            where op_in_\<pi>\<^sub>k: "op \<in> set (\<pi> ! k)"
              and v_is_add_effect: "v \<in> set (add_effects_of op)"
            using A
            by blast
          moreover {
            have "(\<pi> ! k) \<in> set \<pi>"
              using k_lt_t
              by simp
            hence "op \<in> set ?ops"
              using is_parallel_solution_for_problem_operator_set[OF assms(1) _ op_in_\<pi>\<^sub>k]
              by blast
          }
          ultimately have "(Operator k (index ?ops op))\<^sup>+
            \<in> { (Operator k (index ?ops op))\<^sup>+ | op. op \<in> set ?ops \<and> v \<in> set (add_effects_of op) }"
            using v_is_add_effect
            by blast
          then have "(Operator k (index ?ops op))\<^sup>+ \<in> C"
            using C_is
            by auto
          moreover have "\<A> (Operator k (index ?ops op))"
            using assms(2) k_lt_length_\<tau>_minus_one op_in_\<pi>\<^sub>k
            by blast
          ultimately show ?thesis
            unfolding clause_semantics_def
            by force
        next
          case B
          then obtain op
            where op_in_\<pi>\<^sub>k: "op \<in> set (\<pi> ! k)"
              and v_is_delete_effect: "v \<in> set (delete_effects_of op)"..
          then have "\<not>(\<exists>op \<in> set (\<pi> ! k). v \<in> set (add_effects_of op))"
            using all_operator_effects_consistent are_all_operator_effects_consistent_set
            by fast
          then have "execute_parallel_operator (?\<tau> ! k) (\<pi> ! k) v
             = Some False"
            using execute_parallel_operator_negative_effect_if[OF all_operators_applicable
                all_operator_effects_consistent op_in_\<pi>\<^sub>k v_is_delete_effect]
            by blast
          moreover have "(?\<tau> ! Suc k) v = execute_parallel_operator (?\<tau> ! k) (\<pi> ! k) v"
            using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one]
            by simp
          ultimately have "\<not>\<A> (State (Suc k) (index ?vs v))"
            using assms(3) k_lt_length_\<tau>_minus_one
            by simp
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by simp
        next
          case C
          show ?thesis
            proof (cases "(?\<tau> ! k) v = Some True")
              case True
              then have "\<A> (State k (index ?vs v))"
                using assms(3) k_lt_length_\<tau>_minus_one
                by force
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by fastforce
            next
              case False
              {
                have "(?\<tau> ! Suc k) = execute_parallel_operator (?\<tau> ! k) (\<pi> ! k)"
                  using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one].
                then have "(?\<tau> ! Suc k) v = (?\<tau> ! k) v"
                  using execute_parallel_operator_no_effect_if C
                  by fastforce
                hence "(?\<tau> ! Suc k) v \<noteq> Some True"
                  using False
                  by argo
              }
              then have "\<not>\<A> (State (Suc k) (index ?vs v))"
                using assms(3) k_lt_length_\<tau>_minus_one
                by auto
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by fastforce
            qed
        qed
    next
      case k_gte_length_\<tau>_minus_one: False
      show ?thesis
        proof (cases "\<A> (State (length ?\<tau> - 1) (index ?vs v))")
          case True
          {
            have "\<A> (State k (index ?vs v)) = \<A> (State (length ?\<tau> - 1) (index ?vs v))"
              proof (cases "k = length ?\<tau> - 1")
                case False
                then have "length ?\<tau> \<le> k" and "k < ?t + 1"
                  using k_gte_length_\<tau>_minus_one k_in
                  by fastforce+
                thus ?thesis
                  using assms(4)
                  by blast
              qed blast
            hence "\<A> (State k (index ?vs v))"
              using True
              by blast
          }
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by simp
        next
          case False
          {
            have "length ?\<tau> \<le> Suc k" and "Suc k < ?t + 1"
              using k_gte_length_\<tau>_minus_one k_in
              by fastforce+
            then have "\<A> (State (Suc k) (index ?vs v)) = \<A> (State (length ?\<tau> - 1) (index ?vs v))"
              using assms(4)
              by blast
            hence "\<not>\<A> (State (Suc k) (index ?vs v))"
              using False
              by blast
          }
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by fastforce
        qed
    qed
qed

(* TODO make private *)
lemma encode_problem_parallel_complete_iv_b:
  fixes \<Pi> :: "'a strips_problem"
  assumes "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "\<forall>k op. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1
      \<longrightarrow> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) = (op \<in> set (\<pi> ! k))"
    and "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow>  (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)"
    and "\<forall>v l. l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) \<and> l < length \<pi> + 1
      \<longrightarrow> \<A> (State l (index (strips_problem.variables_of \<Pi>) v))
        = \<A> (State
          (length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1)
          (index (strips_problem.variables_of \<Pi>) v))"
    and "C \<in> \<Union> (\<Union>(k, v) \<in> {0..<length \<pi>} \<times> set ((\<Pi>)\<^sub>\<V>).
      {{{ (State k (index (strips_problem.variables_of \<Pi>) v))\<inverse>
          , (State (Suc k) (index (strips_problem.variables_of \<Pi>) v))\<^sup>+ }
        \<union> { (Operator k (index (strips_problem.operators_of \<Pi>) op))\<^sup>+
          |op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op) }}})"
  shows "clause_semantics \<A> C"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?t = "length \<pi>"
  let ?\<tau> = "trace_parallel_plan_strips (initial_of \<Pi>) \<pi>"
  let ?A = "(\<Union>(k, v) \<in> {0..<?t} \<times> set ?vs.
    {{{ (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }
      \<union> { (Operator k (index ?ops op))\<^sup>+
        | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op) }}})"
  (* TODO refactor *)
  {
    (* TODO slow *)
    obtain C' where "C' \<in> ?A" and C_in_C': "C \<in> C'"
      using Union_iff assms(5)
      by auto
    (* TODO slow *)
    then obtain k v
      where "(k, v) \<in> {0..<?t} \<times> set ?vs"
      and "C' \<in> {{{ (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }
        \<union> { (Operator k (index ?ops op))\<^sup>+ |op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }}}"
      using UN_E
      by fastforce
    hence "\<exists>k v.
      k \<in> {0..<?t}
      \<and> v \<in> set ?vs
      \<and> C = { (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }
        \<union> { (Operator k (index ?ops op))\<^sup>+
          | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op) }"
      using C_in_C'
      by auto
  }
  then obtain k v
    where k_in: "k \<in> {0..<?t}"
      and v_in_vs: "v \<in> set ((\<Pi>)\<^sub>\<V>)"
      and C_is: "C = { (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }
        \<union> { (Operator k (index ?ops op))\<^sup>+
          | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op) }"
    by auto
  show ?thesis
    proof (cases "k < length ?\<tau> - 1")
      case k_lt_length_\<tau>_minus_one: True
      then have k_lt_t: "k < ?t"
        using k_in
        by force
      have all_operators_applicable: "are_all_operators_applicable (?\<tau> ! k) (\<pi> ! k)"
        and all_operator_effects_consistent: "are_all_operator_effects_consistent (\<pi> ! k)"
        using trace_parallel_plan_strips_operator_preconditions[OF k_lt_length_\<tau>_minus_one]
        by simp+
      then consider (A) "\<exists>op \<in> set (\<pi> ! k). v \<in> set (delete_effects_of op)"
        | (B) "\<exists>op \<in> set (\<pi> ! k). v \<in> set (add_effects_of op)"
        | (C) "\<forall>op \<in> set (\<pi> ! k). v \<notin> set (add_effects_of op) \<and> v \<notin> set (delete_effects_of op)"
        by blast
      thus ?thesis
        proof (cases)
          case A
          moreover obtain op
            where op_in_\<pi>\<^sub>k: "op \<in> set (\<pi> ! k)"
              and v_is_delete_effect: "v \<in> set (delete_effects_of op)"
            using A
            by blast
          moreover {
            have "(\<pi> ! k) \<in> set \<pi>"
              using k_lt_t
              by simp
            hence "op \<in> set ?ops"
              using is_parallel_solution_for_problem_operator_set[OF assms(1) _ op_in_\<pi>\<^sub>k]
              by auto
          }
          ultimately have "(Operator k (index ?ops op))\<^sup>+
            \<in> { (Operator k (index ?ops op))\<^sup>+
              | op. op \<in> set ?ops \<and> v \<in> set (delete_effects_of op) }"
            using v_is_delete_effect
            by blast
          then have "(Operator k (index ?ops op))\<^sup>+ \<in> C"
            using C_is
            by auto
          moreover have "\<A> (Operator k (index ?ops op))"
            using assms(2) k_lt_length_\<tau>_minus_one op_in_\<pi>\<^sub>k
            by blast
          ultimately show ?thesis
            unfolding clause_semantics_def
            by force
        next
          case B
          then obtain op
            where op_in_\<pi>\<^sub>k: "op \<in> set (\<pi> ! k)"
              and v_is_add_effect: "v \<in> set (add_effects_of op)"..
          then have "\<not>(\<exists>op \<in> set (\<pi> ! k). v \<in> set (delete_effects_of op))"
            using all_operator_effects_consistent are_all_operator_effects_consistent_set
            by fast
          then have "execute_parallel_operator (?\<tau> ! k) (\<pi> ! k) v = Some True"
            using execute_parallel_operator_positive_effect_if[OF all_operators_applicable
                all_operator_effects_consistent op_in_\<pi>\<^sub>k v_is_add_effect]
            by blast
          moreover have "(?\<tau> ! Suc k) v = execute_parallel_operator (?\<tau> ! k) (\<pi> ! k) v"
            using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one]
            by simp
          ultimately have "\<A> (State (Suc k) (index ?vs v))"
            using assms(3) k_lt_length_\<tau>_minus_one
            by simp
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by simp
        next
          case C
          show ?thesis
            \<comment> \<open> We split on cases for @{text "(?\<tau> ! k) v = Some True"} here to avoid having to
              proof @{text "(?\<tau> ! k) v \<noteq> None"}. \<close>
            proof (cases "(?\<tau> ! k) v = Some True")
              case True
              {
                have "(?\<tau> ! Suc k) = execute_parallel_operator (?\<tau> ! k) (\<pi> ! k)"
                  using trace_parallel_plan_step_effect_is[OF k_lt_length_\<tau>_minus_one].
                then have "(?\<tau> ! Suc k) v = (?\<tau> ! k) v"
                  using execute_parallel_operator_no_effect_if C
                  by fastforce
                then have "(?\<tau> ! Suc k) v = Some True"
                  using True
                  by argo
                hence "\<A> (State (Suc k) (index ?vs v))"
                  using assms(3) k_lt_length_\<tau>_minus_one
                  by fastforce
              }
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by fastforce
            next
              case False
              then have "\<not>\<A> (State k (index ?vs v))"
                using assms(3) k_lt_length_\<tau>_minus_one
                by simp
              thus ?thesis
                using C_is
                unfolding clause_semantics_def
                by fastforce
            qed
        qed
    next
      case k_gte_length_\<tau>_minus_one: False
      show ?thesis
        proof (cases "\<A> (State (length ?\<tau> - 1) (index ?vs v))")
          case True
          {
            have "length ?\<tau> \<le> Suc k" and "Suc k < ?t + 1"
              using k_gte_length_\<tau>_minus_one k_in
              by fastforce+
            then have "\<A> (State (Suc k) (index ?vs v)) = \<A> (State (length ?\<tau> - 1) (index ?vs v))"
              using assms(4)
              by blast
            hence "\<A> (State (Suc k) (index ?vs v))"
              using True
              by blast
          }
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by fastforce
        next
          case False
          {
            have "\<A> (State k (index ?vs v)) = \<A> (State (length ?\<tau> - 1) (index ?vs v))"
              proof (cases "k = length ?\<tau> - 1")
                case False
                then have "length ?\<tau> \<le> k" and "k < ?t + 1"
                  using k_gte_length_\<tau>_minus_one k_in
                  by fastforce+
                thus ?thesis
                  using assms(4)
                  by blast
              qed blast
            hence "\<not>\<A> (State k (index ?vs v))"
              using False
              by blast
          }
          thus ?thesis
            using C_is
            unfolding clause_semantics_def
            by simp
        qed
    qed
qed

(* TODO make private *)
lemma encode_problem_parallel_complete_iv:
  fixes \<Pi>::"'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "\<forall>k op. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1
      \<longrightarrow> \<A> (Operator k (index (strips_problem.operators_of \<Pi>) op)) = (op \<in> set (\<pi> ! k))"
    and "\<forall>v k. k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      \<longrightarrow>  (\<A> (State k (index (strips_problem.variables_of \<Pi>) v))
          \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True)"
    and "\<forall>v l. l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) \<and> l < length \<pi> + 1
      \<longrightarrow> \<A> (State l (index (strips_problem.variables_of \<Pi>) v))
        = \<A> (State
          (length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1)
          (index (strips_problem.variables_of \<Pi>) v))"
  shows "\<A> \<Turnstile> encode_all_frame_axioms \<Pi> (length \<pi>)"
proof -
  let ?\<Phi>\<^sub>F = "encode_all_frame_axioms \<Pi> (length \<pi>)"
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?t = "length \<pi>"
  let ?A = "\<Union> (\<Union>(k, v) \<in> {0..<?t} \<times> set ((\<Pi>)\<^sub>\<V>).
    {{{ (State k (index ?vs v))\<^sup>+, (State (Suc k) (index ?vs v))\<inverse> }
      \<union> { (Operator k (index ?ops op))\<^sup>+
        | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (add_effects_of op) }}})"
    and ?B = "\<Union> (\<Union>(k, v) \<in> {0..<?t} \<times> set ((\<Pi>)\<^sub>\<V>).
      {{{ (State k (index ?vs v))\<inverse>, (State (Suc k) (index ?vs v))\<^sup>+ }
        \<union> { (Operator k (index ?ops op))\<^sup>+
          | op. op \<in> set ((\<Pi>)\<^sub>\<O>) \<and> v \<in> set (delete_effects_of op) }}})"
  (* TODO slow (and why can only metis do this?). *)
  have cnf_\<Phi>\<^sub>F_is_A_union_B: "cnf ?\<Phi>\<^sub>F = ?A \<union> ?B"
    using cnf_of_encode_all_frame_axioms_structure
    by (simp add: cnf_of_encode_all_frame_axioms_structure)
  {
    fix C
    assume "C \<in> cnf ?\<Phi>\<^sub>F"
    then consider (C_in_A) "C \<in> ?A"
      | (C_in_B) "C \<in> ?B"
      using Un_iff[of C ?A ?B] cnf_\<Phi>\<^sub>F_is_A_union_B
      by argo
    hence "clause_semantics \<A> C"
      proof (cases)
        case C_in_A
        then show ?thesis
          using encode_problem_parallel_complete_iv_a[OF assms(2, 3, 4, 5) C_in_A]
          by blast
      next
        case C_in_B
        then show ?thesis
          using encode_problem_parallel_complete_iv_b[OF assms(2, 3, 4, 5) C_in_B]
          by blast
      qed
  }
  thus ?thesis
    using encode_frame_axioms_is_cnf is_nnf_cnf cnf_semantics
    unfolding cnf_semantics_def
    by blast
qed

(* TODO refactor. *)
lemma valuation_for_operator_variables_is:
  fixes \<Pi> :: "'a strips_problem"
  assumes "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1"
    and "op \<in> set ((\<Pi>)\<^sub>\<O>)"
  shows "valuation_for_operator_variables \<Pi> \<pi> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)
      (Operator k (index (strips_problem.operators_of \<Pi>) op))
    = (op \<in> set (\<pi> ! k))"
proof -
  let ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?v = "Operator k (index ?ops op)"
    and ?Op = "{ Operator k (index ?ops op)
      | k op. k \<in> {0..<length ?\<tau> - 1} \<and> op \<in> set ((\<Pi>)\<^sub>\<O>) }"
  let ?l = "concat (map (\<lambda>k. map (Pair k) (\<pi> ! k)) [0..<length ?\<tau> - 1])"
    and ?f = "\<lambda>x. Operator (fst x) (index ?ops (snd x))"
  \<comment> \<open> show that our operator construction function is injective on
    @{text "set (concat (map (\<lambda>k. map (Pair k) (\<pi> ! k)) [0..<length ?\<tau> - 1]))"}. \<close>
  have k_in: "k \<in> {0..<length ?\<tau> - 1}"
    using assms(2)
    by fastforce
  {
    (* TODO refactor. *)
    {
      fix k k' op op'
      assume k_op_in: "(k, op) \<in> set ?l" and k'_op'_in: "(k', op') \<in> set ?l"
      have "Operator k (index ?ops op) = Operator k' (index ?ops op') \<longleftrightarrow> (k, op) = (k', op')"
        proof (rule iffI)
          assume index_op_is_index_op': "Operator k (index ?ops op) = Operator k' (index ?ops op')"
          then have k_is_k': "k = k'"
            by fast
          moreover {
            have k'_lt: "k' < length ?\<tau> - 1"
              using k'_op'_in
              by fastforce
            (* TODO slow *)
            have op_in: "op \<in> set (\<pi> ! k)"
              using k_op_in
              by force
            (* TODO slow *)
            then have op'_in: "op' \<in> set (\<pi> ! k)"
              using k'_op'_in k_is_k'
              by auto
            {
              have length_\<tau>_gt_1: "length ?\<tau> > 1"
                using assms(2)
                by linarith
              have "length ?\<tau> - Suc 0 \<le> length \<pi> + 1 - Suc 0"
                using length_trace_parallel_plan_strips_lte_length_plan_plus_one
                using diff_le_mono
                by blast
              then have "length ?\<tau> - 1 \<le> length \<pi>"
                by fastforce
              then have "k' < length \<pi>"
                using length_\<tau>_gt_1 k'_lt
                by linarith
              hence "\<pi> ! k' \<in> set \<pi>"
                by simp
            }
            moreover have "op \<in> set ?ops" and "op' \<in> set ?ops"
              using is_parallel_solution_for_problem_operator_set[OF assms(1)] op_in op'_in k_is_k'
                calculation
              by auto
            ultimately have "op = op'"
              using index_op_is_index_op'
              by force
          }
          ultimately show "(k, op) = (k', op')"
            by blast
        qed fast
    }
    (* TODO slow *)
    hence "inj_on ?f (set ?l)"
      unfolding inj_on_def fst_def snd_def
      by fast
  } note inj_on_f_set_l = this
  (* TODO refactor. *)
  {
    have "set ?l = \<Union> (set ` set (map (\<lambda>k. map (Pair k) (\<pi> ! k)) [0..<length ?\<tau> - 1]))"
      using set_concat
      by metis
    also have "\<dots> = \<Union> (set ` (\<lambda>k. map (Pair k) (\<pi> ! k)) ` {0..<length ?\<tau> - 1})"
      by force
    also have "\<dots> = \<Union> ((\<lambda>k. (Pair k) ` set (\<pi> ! k)) ` {0..<length ?\<tau> - 1})"
      by force
    also have "\<dots> = \<Union>((\<lambda>k. { (k, op) | op. op \<in> set (\<pi> ! k) }) ` {0..<length ?\<tau> - 1})"
      by blast
    also have "\<dots> = \<Union>({{ (k, op) } | k op. k \<in> {0..<length ?\<tau> - 1} \<and> op \<in> set (\<pi> ! k) })"
      by blast
    (* TODO slow. *)
    finally have "set ?l = \<Union>((\<lambda>(k, op). { (k, op) })
      ` { (k, op). k \<in> {0..<length ?\<tau> - 1} \<and> op \<in> set (\<pi> ! k) })"
      using setcompr_eq_image[of "\<lambda>(k, op). { (k, op) }" _]
      by auto
  } note set_l_is = this
  {
    have "Operator k (index ?ops op) \<in> ?Op"
      using assms(3) k_in
      by blast
    (* TODO slow *)
    hence "valuation_for_operator_variables \<Pi> \<pi> ?\<tau> ?v
      = foldr (\<lambda>(k, op) \<A>. \<A>(Operator k (index ?ops op) := True)) ?l \<A>\<^sub>0 ?v"
      unfolding valuation_for_operator_variables_def override_on_def Let_def
      by auto
  } note nb = this
  show ?thesis
    proof (cases "op \<in> set (\<pi> ! k)")
      case True
      moreover have k_op_in: "(k, op) \<in> set ?l"
        using set_l_is k_in calculation
        by blast
      \<comment> \<open> There is some problem with the pattern match in the lambda in fact \isaname{nb}, sow
        we have to do some extra work to convince Isabelle of the truth of the statement. \<close>
      moreover {
        let ?g = "\<lambda>_. True"
        thm foldr_fun_upd[OF inj_on_f_set_l k_op_in]
        have "?v = Operator (fst (k, op)) (index ?ops (snd (k, op)))"
          by simp
        moreover have "(\<lambda>(k, op) \<A>. \<A>(Operator k (index ?ops op) := True))
          = (\<lambda>x \<A>. \<A>(Operator (fst x) (index ?ops  (snd x)) := True))"
          by fastforce
        moreover have "foldr (\<lambda>x \<A>. \<A>(Operator (fst x) (index ?ops  (snd x)) := ?g x))
          ?l \<A>\<^sub>0 (Operator (fst (k, op)) (index ?ops (snd (k, op)))) = True"
          unfolding foldr_fun_upd[OF inj_on_f_set_l k_op_in]..
        ultimately have "valuation_for_operator_variables \<Pi> \<pi> ?\<tau> ?v = True"
          using nb
          by argo
      }
      thus ?thesis
        using True
        by blast
    next
      case False
      {
        have "(k, op) \<notin> set ?l"
          using False set_l_is
          by fast
        moreover {
          fix k' op'
          assume "(k', op') \<in> set ?l"
            and "?f (k', op') = ?f (k, op)"
          (* TODO slow. *)
          hence "(k', op') = (k, op)"
            using inj_on_f_set_l assms(3)
            by simp
        }
        (* TODO slow. *)
        ultimately have "Operator k (index ?ops op) \<notin> ?f ` set ?l"
          using image_iff
          by force
      } note operator_not_in_f_image_set_l = this
      {
        have "\<A>\<^sub>0 (Operator k (index ?ops op)) = False"
          by simp
        moreover have "(\<lambda>(k, op) \<A>. \<A>(Operator k (index ?ops op) := True))
          = (\<lambda>x \<A>. \<A>(Operator (fst x) (index ?ops (snd x)) := True))"
          by fastforce
        ultimately have "foldr (\<lambda>(k, op) \<A>. \<A>(Operator k (index ?ops op) := True)) ?l \<A>\<^sub>0 ?v = False"
          using foldr_fun_no_upd[OF inj_on_f_set_l operator_not_in_f_image_set_l, of "\<lambda>_. True" \<A>\<^sub>0]
          by presburger
      }
      thus ?thesis
      using nb False
      by blast
    qed
qed

(* TODO refactor (also used in proof of completeness for \<forall>-step 1 encoding)
  TODO make private *)
lemma encode_problem_parallel_complete_vi_a:
  fixes \<Pi> :: "'a strips_problem"
  assumes "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1"
  shows "valuation_for_plan \<Pi> \<pi> (Operator k (index (strips_problem.operators_of \<Pi>) op))
    = (op \<in> set (\<pi> ! k))"
proof -
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?t = "length \<pi>"
    and ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?\<A>\<^sub>\<pi> = "valuation_for_plan \<Pi> \<pi>"
    and ?\<A>\<^sub>O = "valuation_for_operator_variables \<Pi> \<pi> ?\<tau>"
    and ?Op = "{ Operator k (index ?ops op) | k op. k \<in> {0..<?t} \<and> op \<in> set ?ops }"
    and ?V = "{ State k (index ?vs v) | k v. k \<in> {0..<?t + 1} \<and> v \<in> set ?vs }"
    and ?v = "Operator k (index ?ops op)"
  {
    have "length ?\<tau> \<le> length \<pi> + 1"
      using length_trace_parallel_plan_strips_lte_length_plan_plus_one.
    then have "length ?\<tau> - 1 \<le> length \<pi>"
      by simp
    then have "k < ?t"
      using assms
      by fastforce
  } note k_lt_length_\<pi> = this
  show ?thesis
    proof (cases "op \<in> set ((\<Pi>)\<^sub>\<O>)")
      case True
      {
        have "?v \<in> ?Op"
          using k_lt_length_\<pi> True
          by auto
        (* TODO slow. *)
        hence "?\<A>\<^sub>\<pi> ?v = ?\<A>\<^sub>O ?v"
          unfolding valuation_for_plan_def override_on_def Let_def
          by force
      }
      then show ?thesis
        using valuation_for_operator_variables_is[OF assms(1, 2) True]
        by blast
    next
      (* TODO refactor (used in the lemma below as well). *)
      case False
      {
        {
          \<comment> \<open> We have @{text "\<not>index ?ops op < length ?ops"} due to the assumption that
            @{text "\<not>op \<in> set ?ops"}. Hence @{text "\<not>k \<in> {0..<?t"} and therefore
            @{text "?v \<notin> ?Op"}. \<close>
          have "?Op = (\<lambda>(k, op). Operator k (index ?ops op)) ` ({0..<?t} \<times> set ?ops)"
            by fast
          moreover have "\<not>index ?ops op < length ?ops"
            using False
            by simp
          ultimately have "?v \<notin> ?Op"
            by fastforce
        }
        moreover have "?v \<notin> ?V"
          by force
        (* TODO slow. *)
        ultimately have "?\<A>\<^sub>\<pi> ?v = \<A>\<^sub>0 ?v"
          unfolding valuation_for_plan_def override_on_def
          by metis
        hence "\<not>?\<A>\<^sub>\<pi> ?v"
          unfolding empty_valuation_def
          by blast
      }
      moreover have "(\<pi> ! k) \<in> set \<pi>"
        using k_lt_length_\<pi>
        by simp
      moreover have "op \<notin> set (\<pi> ! k)"
        using is_parallel_solution_for_problem_operator_set[OF assms(1) calculation(2)] False
        by blast
      ultimately show ?thesis
        by blast
    qed
qed

(* TODO make private *)
lemma encode_problem_parallel_complete_vi_b:
  fixes \<Pi> :: "'a strips_problem"
  assumes "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1"
    and "l < length \<pi>"
  shows "\<not>valuation_for_plan \<Pi> \<pi> (Operator l (index (strips_problem.operators_of \<Pi>) op))"
proof -
  (* TODO prune variables *)
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?t = "length \<pi>"
    and ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?\<A>\<^sub>\<pi> = "valuation_for_plan \<Pi> \<pi>"
    and ?\<A>\<^sub>O = "valuation_for_operator_variables \<Pi> \<pi> ?\<tau>"
    and ?Op = "{ Operator k (index ?ops op) | k op. k \<in> {0..<?t} \<and> op \<in> set ?ops }"
    and ?Op' = "{ Operator k (index ?ops op) | k op. k \<in> {0..<length ?\<tau> - 1} \<and> op \<in> set ?ops }"
    and ?V = "{ State k (index ?vs v) | k v. k \<in> {0..<?t + 1} \<and> v \<in> set ?vs }"
    and ?v = "Operator l (index ?ops op)"
  show ?thesis
    proof (cases "op \<in> set ((\<Pi>)\<^sub>\<O>)")
      case True
      {
        {
          have "?v \<in> ?Op"
            using assms(3) True
            by auto
          (* TODO slow. *)
          hence "?\<A>\<^sub>\<pi> ?v = ?\<A>\<^sub>O ?v"
            unfolding valuation_for_plan_def override_on_def Let_def
            by simp
        }
        moreover {
          have "l \<notin> {0..<length ?\<tau> - 1}"
            using assms(2)
            by simp
          then have "?v \<notin> ?Op'"
            by blast
          hence "?\<A>\<^sub>O ?v = \<A>\<^sub>0 ?v"
            unfolding valuation_for_operator_variables_def override_on_def
            by meson
        }
        ultimately have "\<not>?\<A>\<^sub>\<pi> ?v"
          unfolding empty_valuation_def
          by blast
      }
      then show ?thesis
        by blast
    next
      (* TODO refactor (used in the lemma above as well). *)
      case False
      {
        {
          \<comment> \<open> We have @{text "\<not>index ?ops op < length ?ops"} due to the assumption that
            @{text "\<not>op \<in> set ?ops"}. Hence @{text "\<not>k \<in> {0..<?t"} and therefore
            @{text "?v \<notin> ?Op"}. \<close>
          have "?Op = (\<lambda>(k, op). Operator k (index ?ops op)) ` ({0..<?t} \<times> set ?ops)"
            by fast
          moreover have "\<not>index ?ops op < length ?ops"
            using False
            by simp
          ultimately have "?v \<notin> ?Op"
            by fastforce
        }
        moreover have "?v \<notin> ?V"
          by force
        (* TODO slow. *)
        ultimately have "?\<A>\<^sub>\<pi> ?v = \<A>\<^sub>0 ?v"
          unfolding valuation_for_plan_def override_on_def
          by metis
        hence "\<not>?\<A>\<^sub>\<pi> ?v"
          unfolding empty_valuation_def
          by blast
      }
      thus ?thesis
        by blast
    qed
qed

\<comment> \<open> As a corollary from lemmas \isaname{encode_problem_parallel_complete_vi_a} and
\isaname{encode_problem_parallel_complete_vi_b} we obtain the result that the constructed
valuation \<^term>\<open>\<A> \<equiv> valuation_for_plan \<Pi> \<pi>\<close> valuates SATPlan operator variables as false if
they are not contained in any operator set \<^term>\<open>\<pi> ! k\<close> for any time point \<^term>\<open>k < length \<pi>\<close>. \<close>
corollary encode_problem_parallel_complete_vi_d:
  (* TODO why is this necessary? *)
  fixes \<Pi> :: "'variable strips_problem"
  assumes "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "k < length \<pi>"
    and "op \<notin> set (\<pi> ! k)"
  shows "\<not>valuation_for_plan \<Pi> \<pi> (Operator k (index (strips_problem.operators_of \<Pi>) op))"
  using encode_problem_parallel_complete_vi_a[OF assms(1)] assms(3)
    encode_problem_parallel_complete_vi_b[OF assms(1) _ assms(2)] assms(3)
  by (cases "k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1"; fastforce)

(* TODO refactor List_Supplement OR rm (unused) *)
lemma list_product_is_nil_iff: "List.product xs ys = [] \<longleftrightarrow> xs = [] \<or> ys = []"
proof (rule iffI)
  assume product_xs_ys_is_Nil: "List.product xs ys = []"
  show "xs = [] \<or> ys = []"
    proof (rule ccontr)
      assume "\<not>(xs = [] \<or> ys = [])"
      then have "xs \<noteq> []" and "ys \<noteq> []"
        by simp+
      then obtain x xs' y ys' where "xs = x # xs'" and "ys = y # ys'"
        using list.exhaust
        by metis
      then have "List.product xs ys = (x, y) # map (Pair x) ys' @ List.product xs' (y # ys')"
        by simp
      thus False
        using product_xs_ys_is_Nil
        by simp
    qed
next
  assume "xs = [] \<or> ys = []"
  thus "List.product xs ys = []"
  \<comment> \<open> First cases in the next two proof blocks follow from definition of List.product. \<close>
  proof (rule disjE)
    assume ys_is_Nil: "ys = []"
    show "List.product xs ys = []"
      proof (induction xs)
        case (Cons x xs)
        have "List.product (x # xs) ys = map (Pair x) ys @ List.product xs ys"
          by simp
        also have "\<dots> = [] @ List.product xs ys"
          using Nil_is_map_conv ys_is_Nil
          by blast
        finally show ?case
          using Cons.IH
          by force
      qed auto
  qed simp
qed

\<comment> \<open> We keep the state abstract by requiring a function \<open>s\<close> which takes the index
\<open>k\<close> and returns state. This makes the lemma cover both cases, i.e. dynamic (e.g. the \<open>k\<close>-th
trace state) as well as static state (e.g. final trace state). \<close>
lemma valuation_for_state_variables_is:
  assumes "k \<in> set ks"
    and "v \<in> set vs"
  shows "foldr (\<lambda>(k, v) \<A>. valuation_for_state vs (s k) k v \<A>) (List.product ks vs) \<A>\<^sub>0
      (State k (index vs v))
    \<longleftrightarrow> (s k) v = Some True"
proof -
  let ?v = "State k (index vs v)"
    and ?ps = "List.product ks vs"
  let ?\<A> = "foldr (\<lambda>(k, v) \<A>. valuation_for_state vs (s k) k v \<A>) ?ps \<A>\<^sub>0"
    and ?f = "\<lambda>x. State (fst x) (index vs (snd x))"
    and ?g = "\<lambda>x. (s (fst x)) (snd x) = Some True"
  have nb\<^sub>1: "(k, v) \<in> set ?ps"
    using assms(1, 2) set_product
    by simp
  (* TODO refactor (State construction is injective on List.product ks vs). *)
  moreover {
    {
      fix x y
      assume x_in_ps: "x \<in> set ?ps" and y_in_ps: "y \<in> set ?ps"
        and "\<not>(?f x = ?f y \<longrightarrow> x = y)"
      then have f_x_is_f_y: "?f x = ?f y" and x_is_not_y: "x \<noteq> y"
        by blast+
      then obtain k' k'' v' v''
        where x_is: "x = (k', v')"
          and y_is: "y = (k'', v'')"
        by fastforce
      then consider (A) "k' \<noteq> k''"
        | (B) "v' \<noteq> v''"
        using x_is_not_y
        by blast
      hence False
        proof (cases)
          case A
          then have "?f x \<noteq> ?f y"
            using x_is y_is
            by simp
          thus ?thesis
            using f_x_is_f_y
            by argo
        next
          case B
          have "v' \<in> set vs" and "v'' \<in> set vs"
            using x_in_ps x_is y_in_ps y_is set_product
            by blast+
          then have "index vs v' \<noteq> index vs v''"
            using B
            by force
          then have "?f x \<noteq> ?f y"
            using x_is y_is
            by simp
          thus False
            using f_x_is_f_y
            by blast
        qed
    }
    hence "inj_on ?f (set ?ps)"
      using inj_on_def
      by blast
  } note nb\<^sub>2 = this
  {
    have "foldr (\<lambda>x. valuation_for_state vs (s (fst x)) (fst x) (snd x))
     (List.product ks vs) \<A>\<^sub>0 (State (fst (k, v)) (index vs (snd (k, v)))) =
    (s (fst (k, v)) (snd (k, v)) = Some True)"
      using foldr_fun_upd[OF nb\<^sub>2 nb\<^sub>1, of ?g \<A>\<^sub>0]
      by blast
    moreover have "(\<lambda>x. valuation_for_state vs (s (fst x)) (fst x) (snd x))
      = (\<lambda>(k, v). valuation_for_state vs (s k) k v)"
      by fastforce
    ultimately have "?\<A> (?f (k, v)) = ?g (k, v)"
      by simp
  }
  thus ?thesis
    by simp
qed

(* TODO make private *)
lemma encode_problem_parallel_complete_vi_c:
  fixes \<Pi> :: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "k < length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)"
  shows "valuation_for_plan \<Pi> \<pi> (State k (index (strips_problem.variables_of \<Pi>) v))
    \<longleftrightarrow> (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi> ! k) v = Some True"
proof -
  (* TODO prune variables *)
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?t = "length \<pi>"
    and ?t' = "length ?\<tau>"
  let ?\<A>\<^sub>\<pi> = "valuation_for_plan \<Pi> \<pi>"
    and ?\<A>\<^sub>V = "valuation_for_state_variables \<Pi> \<pi> ?\<tau>"
    and ?\<A>\<^sub>O = "valuation_for_state_variables \<Pi> \<pi> ?\<tau>"
    and ?\<A>\<^sub>1 = "foldr
      (\<lambda>(k, v) \<A>. valuation_for_state ?vs (?\<tau> ! k) k v \<A>)
      (List.product [0..<?t'] ?vs) \<A>\<^sub>0"
    and ?Op = "{ Operator k (index ?ops op) | k op. k \<in> {0..<?t} \<and> op \<in> set ((\<Pi>)\<^sub>\<O>) }"
    and ?Op' = "{ Operator k (index ?ops op) | k op. k \<in> {0..<?t' - 1} \<and> op \<in> set ((\<Pi>)\<^sub>\<O>) }"
    and ?V = "{ State k (index ?vs v) | k v. k \<in> {0..<?t + 1} \<and> v \<in> set ((\<Pi>)\<^sub>\<V>) }"
    and ?V\<^sub>1 = "{ State k (index ?vs v) | k v. k \<in> {0..<?t'} \<and> v \<in> set ((\<Pi>)\<^sub>\<V>) }"
    and ?V\<^sub>2 = "{ State k (index ?vs v) | k v. k \<in> {?t'..(?t + 1)} \<and> v \<in> set ((\<Pi>)\<^sub>\<V>) }"
    and ?v = "State k (index ?vs v)"
  have v_notin_Op: "?v \<notin> ?Op"
    by blast
  have k_lte_length_\<pi>_plus_one: "k < length \<pi> + 1"
    using less_le_trans length_trace_parallel_plan_strips_lte_length_plan_plus_one assms(3)
    by blast
  show ?thesis
    proof (cases "v \<in> set ((\<Pi>)\<^sub>\<V>)")
      case True
      {
        (* TODO refactor. *)
        {
          have "?v \<in> ?V" "?v \<notin> ?Op"
            using k_lte_length_\<pi>_plus_one True
            by force+
          hence "?\<A>\<^sub>\<pi> ?v = ?\<A>\<^sub>V ?v"
            unfolding valuation_for_plan_def override_on_def Let_def
            by simp
        }
        moreover {
          have "?v \<in> ?V\<^sub>1" "?v \<notin> ?V\<^sub>2"
            using assms(3) True
            by fastforce+
          hence "?\<A>\<^sub>V ?v = ?\<A>\<^sub>1 ?v"
            unfolding valuation_for_state_variables_def override_on_def Let_def
            by force
        }
        ultimately have "?\<A>\<^sub>\<pi> ?v = ?\<A>\<^sub>1 ?v"
          by blast
      }
      moreover have "k \<in> set [0..<?t']"
        using assms(3)
        by simp
      moreover have "v \<in> set (strips_problem.variables_of \<Pi>)"
        using True
        by simp
      (* TODO slow *)
      ultimately show ?thesis
        using valuation_for_state_variables_is[of k "[0..<?t']"]
        by fastforce
    next
      case False
      {
        {
          have "\<not> index ?vs v < length ?vs"
            using False index_less_size_conv
            by simp
          hence "?v \<notin> ?V"
            by fastforce
        }
        then have "\<not>?\<A>\<^sub>\<pi> ?v"
          using v_notin_Op
          unfolding valuation_for_plan_def override_on_def empty_valuation_def Let_def
             variables_of_def operators_of_def
          by presburger
      }
      moreover have "\<not>(?\<tau> ! k) v = Some True"
        using trace_parallel_plan_strips_none_if[of \<Pi> \<pi> k v] assms(1, 2, 3) False
        unfolding initial_of_def
        by force
      ultimately show ?thesis
        by blast
    qed
qed

(* TODO make private *)
lemma encode_problem_parallel_complete_vi_f:
  fixes \<Pi> :: "'a strips_problem"
  assumes "is_valid_problem_strips \<Pi>"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
    and "l \<ge> length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>)"
    and "l < length \<pi> + 1"
  shows "valuation_for_plan \<Pi> \<pi> (State l (index (strips_problem.variables_of \<Pi>) v))
    = valuation_for_plan \<Pi> \<pi>
      (State (length (trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>) - 1)
      (index (strips_problem.variables_of \<Pi>) v))"
proof -
  (* TODO prune variables *)
  let ?vs = "strips_problem.variables_of \<Pi>"
    and ?ops = "strips_problem.operators_of \<Pi>"
    and ?\<tau> = "trace_parallel_plan_strips ((\<Pi>)\<^sub>I) \<pi>"
  let ?t = "length \<pi>"
    and ?t' = "length ?\<tau>"
  let ?\<tau>\<^sub>\<Omega> = "?\<tau> ! (?t' - 1)"
    and ?\<A>\<^sub>\<pi> = "valuation_for_plan \<Pi> \<pi>"
    and ?\<A>\<^sub>V = "valuation_for_state_variables \<Pi> \<pi> ?\<tau>"
    and ?\<A>\<^sub>O = "valuation_for_state_variables \<Pi> \<pi> ?\<tau>"
  let ?\<A>\<^sub>2 = "foldr
    (\<lambda>(k, v) \<A>. valuation_for_state (strips_problem.variables_of \<Pi>) ?\<tau>\<^sub>\<Omega> k v \<A>)
    (List.product [?t'..<length \<pi> + 2] ?vs)
    \<A>\<^sub>0"
    and ?Op = "{ Operator k (index ?ops op) | k op. k \<in> {0..<?t} \<and> op \<in> set ((\<Pi>)\<^sub>\<O>) }"
    and ?Op' = "{ Operator k (index ?ops op) | k op. k \<in> {0..<?t' - 1} \<and> op \<in> set ((\<Pi>)\<^sub>\<O>) }"
    and ?V = "{ State k (index ?vs v) | k v. k \<in> {0..<?t + 1} \<and> v \<in> set ((\<Pi>)\<^sub>\<V>) }"
    and ?V\<^sub>1 = "{ State k (index ?vs v) | k v. k \<in> {0..<?t'} \<and> v \<in> set ((\<Pi>)\<^sub>\<V>) }"
    and ?V\<^sub>2 = "{ State k (index ?vs v) | k v. k \<in> {?t'..(?t + 1)} \<and> v \<in> set ((\<Pi>)\<^sub>\<V>) }"
    and ?v = "State l (index ?vs v)"
  have v_notin_Op: "?v \<notin> ?Op"
    by blast
  show ?thesis
    proof (cases "v \<in> set ((\<Pi>)\<^sub>\<V>)")
      case True
      {
        (* TODO refactor. *)
        {
          have "?v \<in> ?V" "?v \<notin> ?Op"
            using assms(4) True
            by force+
          (* TODO slow. *)
          hence "?\<A>\<^sub>\<pi> ?v = ?\<A>\<^sub>V ?v"
            unfolding valuation_for_plan_def override_on_def Let_def
            by simp
        }
        moreover {
          have "?v \<notin> ?V\<^sub>1" "?v \<in> ?V\<^sub>2"
            using assms(3, 4) True
            by force+
          (* TODO slow. *)
          hence "?\<A>\<^sub>V ?v = ?\<A>\<^sub>2 ?v"
            unfolding valuation_for_state_variables_def override_on_def Let_def
            by auto
        }
        ultimately have "?\<A>\<^sub>\<pi> ?v = ?\<A>\<^sub>2 ?v"
          by blast
      } note nb = this
      moreover
      {
        have "l \<in> set [?t'..<?t + 2]"
          using assms(3, 4)
          by auto
        (* TODO slow *)
        hence "?\<A>\<^sub>2 ?v \<longleftrightarrow> ?\<tau>\<^sub>\<Omega> v = Some True"
          using valuation_for_state_variables_is[of l "[?t'..<?t + 2]"] True nb
          by fastforce
      }
      ultimately have "?\<A>\<^sub>\<pi> ?v \<longleftrightarrow> ?\<tau>\<^sub>\<Omega> v = Some True"
        by fast
      moreover {
        have "0 < ?t'"
          using trace_parallel_plan_strips_not_nil
          by blast
        then have "?t' - 1 < ?t'"
          using diff_less
          by presburger
      }
      ultimately show ?thesis
        using encode_problem_parallel_complete_vi_c[of _ _ "?t' - 1", OF assms(1, 2)]
        by blast
    next
      case False
      {
        {
          have "\<not> index ?vs v < length ?vs"
            using False index_less_size_conv
            by auto
          hence "?v \<notin> ?V"
            by fastforce
        }
        then have "\<not>?\<A>\<^sub>\<pi> ?v"
          using v_notin_Op
          unfolding valuation_for_plan_def override_on_def empty_valuation_def Let_def
            variables_of_def operators_of_def
          by presburger
      }
      moreover {
        have "0 < ?t'"
          using trace_parallel_plan_strips_not_nil
          by blast
        then have "?t' - 1 < ?t'"
          by simp
      }
      moreover have  "\<not>((?\<tau> ! (?t' - 1)) v = Some True)"
        using trace_parallel_plan_strips_none_if[of _ _ "?t' - 1" v, OF _ assms(2) calculation(2)]
          assms(1) False
        by simp
      ultimately show ?thesis
        using encode_problem_parallel_complete_vi_c[of _ _ "?t' - 1", OF assms(1, 2)]
        by blast
    qed
qed


text \<open> Let now \<^term>\<open>\<tau> \<equiv> trace_parallel_plan_strips I \<pi>\<close> be the trace of the plan \<^term>\<open>\<pi>\<close>, \<^term>\<open>t \<equiv> length \<pi>\<close>, and
\<^term>\<open>t' \<equiv> length \<tau>\<close>.

Any model of the SATPlan encoding \<^term>\<open>\<A>\<close> must satisfy the following properties:
\footnote{Cf. \cite[Theorem 3.1, p. 1044]{DBLP:journals/ai/RintanenHN06} for the construction
of \<^term>\<open>\<A>\<close>.}

  \begin{enumerate}
    \item for all \<^term>\<open>k\<close> and for all \<^term>\<open>op\<close> with \<^term>\<open>k < t' - 1\<close>

      @{text[display, indent=4] "\<A> (Operator k (index (operators_of \<Pi>) op)) = op \<in> set (\<pi> ! k)"}
    \item for all \<^term>\<open>l\<close> and for all \<^term>\<open>op\<close> with \<^term>\<open>l \<ge> t' - 1\<close> and
      \<^term>\<open>l < length \<pi>\<close> we require

      @{text[display, indent=4] "\<A> (Operator l (index (operators_of \<Pi>) op))"}
    \item for all \<^term>\<open>v\<close> and for all \<^term>\<open>k\<close> with \<^term>\<open>k < t'\<close> we require

      @{text[display, indent=4] "\<A> (State k (index (variables_of \<Pi>) v)) \<longrightarrow> ((\<tau> ! k) v = Some True)"}
    \item and finally for all \<^term>\<open>v\<close> and for all \<^term>\<open>l\<close> with \<^term>\<open>l \<ge> t'\<close> and \<^term>\<open>l < t + 1\<close> we require

      @{text[display, indent=4] "\<A> (State l (index (variables_of \<Pi>) v))
        = \<A> (State (t' - 1) (index (variables_of \<Pi>) v))"}
  \end{enumerate}

Condition ``1.'' states that the model must reflect operator activation for all operators in the
parallel operator lists \<^term>\<open>\<pi> ! k\<close> of the plan \<^term>\<open>\<pi>\<close> for each time step \<^term>\<open>k < t' - 1\<close> s.t. there is a
successor state in the trace. Moreover ``3.''
requires that the model is consistent with the states reached during plan execution (i.e. the
elements \<^term>\<open>\<tau> ! k\<close> for \<^term>\<open>k < t'\<close> of the trace \<^term>\<open>\<tau>\<close>). Meaning that
\<^term>\<open>\<A> (State k (index (strips_problem.variables_of \<Pi>) v))\<close> for the SAT plan variable of
every state variable \<^term>\<open>v\<close> at time point \<^term>\<open>k\<close> if and only if \<^term>\<open>(\<tau> ! k) v = Some True\<close>
for the corresponding state \<^term>\<open>\<tau> ! k\<close> at time \<^term>\<open>k\<close> (and
\<^term>\<open>\<not>\<A> (State k (index (strips_problem.variables_of \<Pi>) v))\<close> otherwise).

The second respectively fourth condition cover early plan termination by negating operator
activation and propagating the last reached state. Note that in the state propagation constraint,
the index is incremented by one compared to the similar constraint for operators, since operator
activations are always followed by at least one successor state.
Hence the last state in the trace has index
\<^term>\<open>length (trace_parallel_plan_strips ((\<Pi>::'variable strips_problem)\<^sub>I) \<pi>) - 1\<close> and the remaining states
take up the indexes to \<^term>\<open>length \<pi> + 1\<close>.

% TODO Comments on how the partial encoding modeling follows from the construction (lemmas ...). \<close>

value  "stop" (* Tell document preparation to stop collecting for the last tag *)

\<comment> \<open> To show completeness—i.e. every valid parallel plan \<open>\<pi>\<close> corresponds to a model
for the SATPlan encoding \<open>\<Phi> \<Pi> (length \<pi>)\<close>—, we simply split the
conjunction defined by the encoding into partial encodings and show that the model satisfies each
of them. \<close>
theorem
  encode_problem_parallel_complete:
  assumes "is_valid_problem_strips \<Pi>"
    and "is_parallel_solution_for_problem \<Pi> \<pi>"
  shows "valuation_for_plan \<Pi> \<pi> \<Turnstile> \<Phi> \<Pi> (length \<pi>)"
proof -
  let ?t = "length \<pi>"
    and ?I = "(\<Pi>)\<^sub>I"
    and ?G = "(\<Pi>)\<^sub>G"
    and ?\<A> = "valuation_for_plan \<Pi> \<pi>"
  have nb: "?G \<subseteq>\<^sub>m execute_parallel_plan ?I \<pi>"
    using assms(2)
    unfolding is_parallel_solution_for_problem_def
    by force
  have "?\<A> \<Turnstile> \<Phi>\<^sub>I \<Pi>"
    using encode_problem_parallel_complete_i[OF assms(1) nb]
      encode_problem_parallel_complete_vi_c[OF assms(1, 2)]
    by presburger
  moreover have "?\<A> \<Turnstile> (\<Phi>\<^sub>G \<Pi>) ?t"
    using encode_problem_parallel_complete_ii[OF assms(1) nb]
      encode_problem_parallel_complete_vi_c[OF assms(1, 2)]
      encode_problem_parallel_complete_vi_f[OF assms(1, 2)]
    by presburger
  moreover have "?\<A> \<Turnstile> encode_operators \<Pi> ?t"
    using encode_problem_parallel_complete_iii[OF assms(1) nb]
      encode_problem_parallel_complete_vi_a[OF assms(2)]
      encode_problem_parallel_complete_vi_b[OF assms(2)]
      encode_problem_parallel_complete_vi_c[OF assms(1, 2)]
    by presburger
  moreover have "?\<A> \<Turnstile> encode_all_frame_axioms \<Pi> ?t"
    using encode_problem_parallel_complete_iv[OF assms(1, 2)]
      encode_problem_parallel_complete_vi_a[OF assms(2)]
      encode_problem_parallel_complete_vi_c[OF assms(1, 2)]
      encode_problem_parallel_complete_vi_f[OF assms(1, 2)]
    by presburger
  ultimately show ?thesis
    unfolding encode_problem_def SAT_Plan_Base.encode_problem_def
      encode_initial_state_def encode_goal_state_def
    by auto
qed

end

