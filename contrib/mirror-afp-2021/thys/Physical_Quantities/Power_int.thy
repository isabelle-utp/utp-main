section \<open> Integer Powers \<close>

theory Power_int
  imports "HOL.Real"
begin

text \<open> The standard HOL power operator is only for natural powers. This operator allows integers. \<close>

definition intpow :: "'a::{linordered_field} \<Rightarrow> int \<Rightarrow> 'a" (infixr "^\<^sub>Z" 80) where
"intpow x n = (if (n < 0) then inverse (x ^ nat (-n)) else (x ^ nat n))"

lemma intpow_zero [simp]: "x ^\<^sub>Z 0 = 1"
  by (simp add: intpow_def)

lemma intpow_spos [simp]: "x > 0 \<Longrightarrow> x ^\<^sub>Z n > 0"
  by (simp add: intpow_def)

lemma intpow_one [simp]: "x ^\<^sub>Z 1 = x"
  by (simp add: intpow_def)

lemma one_intpow [simp]: "1 ^\<^sub>Z n = 1"
  by (simp add: intpow_def)

lemma intpow_plus: "x > 0 \<Longrightarrow> x ^\<^sub>Z (m + n) = x ^\<^sub>Z m * x ^\<^sub>Z n"
  apply (simp add: intpow_def field_simps power_add)
  apply (metis (no_types, hide_lams) abs_ge_zero add.commute add_diff_cancel_right' nat_add_distrib power_add uminus_add_conv_diff zabs_def)
  done

lemma intpow_mult_combine: "x > 0 \<Longrightarrow> x ^\<^sub>Z m * (x ^\<^sub>Z n * y) = x ^\<^sub>Z (m + n) * y"
  by (simp add: intpow_plus)

lemma intpow_pos [simp]: "n \<ge> 0 \<Longrightarrow> x ^\<^sub>Z n = x ^ nat n"
  by (simp add: intpow_def)

lemma intpow_uminus: "x ^\<^sub>Z -n = inverse (x ^\<^sub>Z n)"
  by (simp add: intpow_def)

lemma intpow_uminus_nat: "n \<ge> 0 \<Longrightarrow> x ^\<^sub>Z -n = inverse (x ^ nat n)"
  by (simp add: intpow_def)

lemma intpow_inverse: "inverse a ^\<^sub>Z n = inverse (a ^\<^sub>Z n)"
  by (simp add: intpow_def power_inverse)

lemma intpow_mult_distrib: "(x * y) ^\<^sub>Z m = x ^\<^sub>Z m * y ^\<^sub>Z m"
  by (simp add: intpow_def power_mult_distrib)

end