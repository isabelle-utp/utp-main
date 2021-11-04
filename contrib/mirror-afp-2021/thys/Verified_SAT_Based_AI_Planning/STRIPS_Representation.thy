(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory STRIPS_Representation
  imports State_Variable_Representation
begin

section "STRIPS Representation"

(*<*)
type_synonym  ('variable) strips_state = "('variable, bool) state"
(*>*)
text \<open> We start by declaring a \isakeyword{record} for STRIPS operators.
This which allows us to define a data type and automatically generated selector operations. 
\footnote{For the full reference on records see \cite[11.6, pp.260-265]{wenzel--2018}} 

The record specification given below closely resembles the canonical representation of
STRIPS operators with fields corresponding to precondition, add effects as well as delete effects.\<close>

record  ('variable) strips_operator = 
  precondition_of :: "'variable list" 
  add_effects_of :: "'variable list" 
  delete_effects_of :: "'variable list" 

\<comment> \<open> This constructor function is sometimes a more descriptive and replacement for the record 
syntax and can moreover be helpful if the record syntax leads to type ambiguity.\<close>
abbreviation  operator_for
  :: "'variable list \<Rightarrow> 'variable list \<Rightarrow> 'variable list \<Rightarrow> 'variable strips_operator"
  where "operator_for pre add delete \<equiv> \<lparr> 
    precondition_of = pre
    , add_effects_of = add
    , delete_effects_of = delete \<rparr>" 

definition  to_precondition
  :: "'variable strips_operator \<Rightarrow> ('variable, bool) assignment list"
  where "to_precondition op \<equiv> map (\<lambda>v. (v, True)) (precondition_of op)" 

definition  to_effect
  :: "'variable strips_operator \<Rightarrow> ('variable, bool) Effect" 
  where "to_effect op =  [(v\<^sub>a, True). v\<^sub>a \<leftarrow> add_effects_of op] @ [(v\<^sub>d, False). v\<^sub>d \<leftarrow> delete_effects_of op]"

text \<open> Similar to the operator definition, we use a record to represent STRIPS problems and specify
fields for the variables, operators, as well as the initial and goal state. \<close>

record  ('variable) strips_problem =
  variables_of :: "'variable list" ("(_\<^sub>\<V>)" [1000] 999)
  operators_of :: "'variable strips_operator list" ("(_\<^sub>\<O>)" [1000] 999)
  initial_of :: "'variable strips_state" ("(_\<^sub>I)" [1000] 999)
  goal_of :: "'variable strips_state" ("(_\<^sub>G)" [1000] 999)

value  "stop" (* Tell document preparation to stop collecting for the last tag *)
(*<*)
\<comment> \<open> This constructor function is sometimes a more descriptive and replacement for the record 
syntax and can moreover be helpful if the record syntax leads to type ambiguity.\<close>
(* TODO change identifier gs ~> G *)
abbreviation problem_for 
  :: "'variable list 
  \<Rightarrow> 'variable strips_operator list 
  \<Rightarrow> 'variable strips_state 
  \<Rightarrow> 'variable strips_state
  \<Rightarrow> ('variable) strips_problem"
  where "problem_for vs ops I gs \<equiv> \<lparr> 
    variables_of = vs
    , operators_of = ops
    , initial_of = I
    , goal_of = gs \<rparr>" 

type_synonym ('variable) strips_plan = "'variable strips_operator list"

type_synonym ('variable) strips_parallel_plan = "'variable strips_operator list list"

definition is_valid_operator_strips
  :: "'variable strips_problem \<Rightarrow> 'variable strips_operator \<Rightarrow> bool"
  where "is_valid_operator_strips \<Pi> op \<equiv> let 
      vs = variables_of \<Pi> 
      ; pre = precondition_of op
      ; add = add_effects_of op
      ; del = delete_effects_of op
    in list_all (\<lambda>v. ListMem v vs) pre 
    \<and> list_all (\<lambda>v. ListMem v vs) add
    \<and> list_all (\<lambda>v. ListMem v vs) del
    \<and> list_all (\<lambda>v. \<not>ListMem v del) add
    \<and> list_all (\<lambda>v. \<not>ListMem v add) del"

definition "is_valid_problem_strips \<Pi>
  \<equiv> let ops = operators_of \<Pi>
      ; vs = variables_of \<Pi>
      ; I = initial_of \<Pi>
      ; G = goal_of \<Pi>
    in  list_all (is_valid_operator_strips \<Pi>) ops 
    \<and> (\<forall>v. I v \<noteq> None \<longleftrightarrow> ListMem v vs) 
    \<and> (\<forall>v. G v \<noteq> None \<longrightarrow> ListMem v vs)"

definition is_operator_applicable_in
  :: "'variable strips_state \<Rightarrow> 'variable strips_operator \<Rightarrow> bool"
  where "is_operator_applicable_in s op \<equiv> let p = precondition_of op in
    list_all (\<lambda>v. s v = Some True) p"

(* TODO effect_to_strips and effect_to_assignments could just be removed if we prove a lemma 
  showing the equivalence to effcond semantics.*)
definition effect__strips 
  :: "'variable strips_operator \<Rightarrow> ('variable, bool) Effect"
  where "effect__strips op 
    = 
      map (\<lambda>v. (v, True)) (add_effects_of op)
      @ map (\<lambda>v. (v, False)) (delete_effects_of op)"

definition effect_to_assignments 
  where "effect_to_assignments op \<equiv> effect__strips op"
(*>*)

text \<open> As discussed in \autoref{sub:serial-sas-plus-and-parallel-strips}, the effect of
a STRIPS operator can be normalized to a conjunction of atomic effects. We can therefore construct 
the successor state by simply converting the list of add effects to assignments to \<^term>\<open>True\<close> resp. 
converting the list of delete effect to a list of assignments to \<^term>\<open>False\<close> and then adding the 
map corresponding to the assignments to the given state \<^term>\<open>s\<close> as shown below in definition 
\ref{isadef:operator-execution-strips}. 
\footnote{Function \path{effect_to_assignments} converts the operator effect to a list of 
assignments. }\<close>

definition  execute_operator
  :: "'variable strips_state 
    \<Rightarrow> 'variable strips_operator 
    \<Rightarrow> 'variable strips_state" (infixl "\<then>" 52)
  where "execute_operator s op
    \<equiv> s ++ map_of (effect_to_assignments op)"

end