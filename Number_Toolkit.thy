section \<open> Number Toolkit \<close>

theory Number_Toolkit
  imports Function_Toolkit
begin

text \<open> The numeric operators are all implemented in HOL (@{const "plus"}, @{const "minus"}, 
  @{const times}, etc.), and there seems little to be gained by repackaging them. However,
  we do make some syntactic additions. \<close>

subsection \<open> Successor \<close>

abbreviation (input) "succ n \<equiv> n + 1"

subsection \<open> Integers \<close>

type_notation int ("\<int>")

subsection \<open> Natural numbers \<close>

type_notation nat ("\<nat>")

subsection \<open> Rational numbers \<close>

type_notation rat ("\<rat>")

subsection \<open> Real numbers \<close>

type_notation real ("\<real>")

subsection \<open> Strictly positive natural numbers \<close>

definition Nats1 ("\<nat>\<^sub>1") where "\<nat>\<^sub>1 = {x \<in> \<nat>. \<not> x = 0}"

subsection \<open> Non-zero integers \<close>

definition Ints1 ("\<int>\<^sub>1") where "\<int>\<^sub>1 = {x \<in> \<int>. \<not> x = 0}"

end