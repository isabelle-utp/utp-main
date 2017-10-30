section {* Modelica.Math *}

theory Modelica_Math
imports Modelica_Core
begin

text {* We need some additional functions, such as summation, on finite Cartesian products that
  we here define. *}
  
setup_lifting type_definition_vec
  
lift_definition vec_sum :: "'a::comm_monoid_add ^ 'i::finite \<Rightarrow> 'a" is
"\<lambda> f. \<Sum> (range f)" .
  
adhoc_overloading
  usums vec_sum

text {* We define Modelica.Math functions that are not part of Isabelle/HOL *}
  
definition sign\<^sub>m :: "real \<Rightarrow> real" where
[upred_defs]: "sign\<^sub>m(u) = (if (u > 0) then 1 else if (u = 0) then 0 else -1)"

definition atan2\<^sub>m :: "real \<Rightarrow> real \<Rightarrow> real" where
[upred_defs]: "atan2\<^sub>m(u) = undefined"
  
end