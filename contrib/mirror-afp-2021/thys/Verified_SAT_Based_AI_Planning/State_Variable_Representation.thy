(*
  Author: Mohammad Abdulaziz, Fred Kurz
*)
theory State_Variable_Representation
  imports Main "Propositional_Proof_Systems.Formulas" "Propositional_Proof_Systems.Sema" 
    "Propositional_Proof_Systems.CNF"
begin
section "State-Variable Representation"

text \<open> Moving on to the Isabelle implementation of state-variable representation, we
first add a more concrete representation of states using Isabelle maps. To this end, we add a 
type synonym \isaname{state} for maps of variables to values. 
Since maps can be conveniently constructed from lists of 
assignments---i.e. pairs \<open>(v, a) :: 'variable \<times> 'domain\<close>---we also add a corresponding type 
synonym \isaname{assignment}. \<close>

type_synonym ('variable, 'domain) state = "'variable \<rightharpoonup> 'domain"

type_synonym ('variable, 'domain) assignment = "'variable \<times> 'domain"

text \<open> Effects and effect condition (see \autoref{sub:state-variable-representation}) are 
implemented in a straight forward manner using a datatype with constructors for each effect type.\<close>

type_synonym ('variable, 'domain) Effect = "('variable \<times> 'domain) list"

end