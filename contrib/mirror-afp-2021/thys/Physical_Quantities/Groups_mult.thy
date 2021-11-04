section \<open> Multiplication Groups \<close>

theory Groups_mult
  imports Main
begin

text \<open> The HOL standard library only has groups based on addition. Here, we build one based on
  multiplication. \<close>

notation times (infixl "\<cdot>" 70)

class group_mult = inverse + monoid_mult +
  assumes left_inverse: "inverse a \<cdot> a = 1"
  assumes multi_inverse_conv_div [simp]: "a \<cdot> (inverse b) = a / b"
begin

lemma div_conv_mult_inverse: "a / b = a \<cdot> (inverse b)"
  by simp

sublocale mult: group times 1 inverse
  by standard (simp_all add: left_inverse)

lemma diff_self [simp]: "a / a = 1"
  using mult.right_inverse by auto

lemma mult_distrib_inverse [simp]: "(a * b) / b = a"
  by (metis local.mult_1_right local.multi_inverse_conv_div mult.right_inverse mult_assoc)

end

class ab_group_mult = comm_monoid_mult + group_mult
begin

lemma mult_distrib_inverse' [simp]: "(a * b) / a = b"
  using local.mult_distrib_inverse mult_commute by fastforce

lemma inverse_distrib: "inverse (a * b)  =  (inverse a) * (inverse b)"
  by (simp add: local.mult.inverse_distrib_swap mult_commute)

lemma inverse_divide [simp]: "inverse (a / b) = b / a"
  by (metis div_conv_mult_inverse inverse_distrib mult.commute mult.inverse_inverse)

end

abbreviation (input) npower :: "'a::{power,inverse} \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<^sup>-\<^sup>_)" [1000,999] 999) 
  where "npower x n \<equiv> inverse (x ^ n)"

end