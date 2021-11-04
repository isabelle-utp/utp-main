section \<open>Signed Modulo Operation\<close>

theory Signed_Modulo
  imports 
    Berlekamp_Zassenhaus.Poly_Mod
    Sqrt_Babylonian.Sqrt_Babylonian_Auxiliary
begin

text \<open>The upcoming definition of symmetric modulo 
  is different to the HOL-Library-Signed\_Division.smod, since
  here the modulus will be in range $\{-m/2,...,m/2\}$, 
  whereas there -1 symmod m = m - 1.

  The advantage of have range $\{-m/2,...,m/2\}$ is that small negative
  numbers are represented by small numbers.

  One limitation is that the symmetric modulo is only working properly,
  if the modulus is a positive number.\<close>

definition sym_mod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "symmod" 70) where
  "sym_mod x y = poly_mod.inv_M y (x mod y)"

lemma sym_mod_code[code]: "sym_mod x y = (let m = x mod y
   in if m + m \<le> y then m else m - y)" 
  unfolding sym_mod_def poly_mod.inv_M_def Let_def ..

lemma sym_mod_zero[simp]: "n symmod 0 = n" "n > 0 \<Longrightarrow> 0 symmod n = 0"
  unfolding sym_mod_def poly_mod.inv_M_def by auto

lemma sym_mod_range: "y > 0 \<Longrightarrow> x symmod y \<in> {- ((y - 1) div 2) .. y div 2}"
  unfolding sym_mod_def poly_mod.inv_M_def using pos_mod_bound[of y x]
  by (cases "x mod y \<ge> y", auto) 
    (smt (verit) Euclidean_Division.pos_mod_bound Euclidean_Division.pos_mod_sign half_nonnegative_int_iff)+

text \<open>The range is optimal in the sense that exactly y elements can be represented.\<close>
lemma card_sym_mod_range: "y > 0 \<Longrightarrow> card {- ((y - 1) div 2) .. y div 2} = y" 
  by simp

lemma sym_mod_abs: "y > 0 \<Longrightarrow> \<bar>x symmod y\<bar> < y"
  "y \<ge> 1 \<Longrightarrow> \<bar>x symmod y\<bar> \<le> y div 2"
  using sym_mod_range[of y x] by auto


lemma sym_mod_sym_mod[simp]: "x symmod y symmod y = x symmod (y :: int)" 
  unfolding sym_mod_def using poly_mod.M_def poly_mod.M_inv_M_id by auto

lemma sym_mod_diff_eq: "(a symmod c - b symmod c) symmod c = (a - b) symmod c" 
  unfolding sym_mod_def
  by (metis mod_diff_cong mod_mod_trivial poly_mod.M_def poly_mod.M_inv_M_id)

lemma sym_mod_sym_mod_cancel: "c dvd b \<Longrightarrow> a symmod b symmod c = a symmod c" 
  using mod_mod_cancel[of c b] unfolding sym_mod_def
  by (metis poly_mod.M_def poly_mod.M_inv_M_id)

lemma sym_mod_diff_right_eq: "(a - b symmod c) symmod c = (a - b) symmod c" 
  using sym_mod_diff_eq by (metis sym_mod_sym_mod)

lemma sym_mod_mult_right_eq: "a * (b symmod c) symmod c = a * b symmod c" 
  unfolding sym_mod_def by (metis poly_mod.M_def poly_mod.M_inv_M_id mod_mult_right_eq)

lemma dvd_imp_sym_mod_0 [simp]:
  "b symmod a = 0" if "a > 0" "a dvd b"
  unfolding sym_mod_def poly_mod.inv_M_def using that by simp

lemma sym_mod_0_imp_dvd [dest!]:
  "b dvd a" if "a symmod b = 0"
  using that unfolding sym_mod_def poly_mod.inv_M_def
  by (smt (verit) Euclidean_Division.pos_mod_bound dvd_eq_mod_eq_0)

definition sym_div :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "symdiv" 70) where
  "sym_div x y = (let d = x div y; m = x mod y in 
       if m + m \<le> y then d else d + 1)"

lemma of_int_mod_integer: "(of_int (x mod y) :: integer) = (of_int x :: integer) mod (of_int y)" 
  using integer_of_int_eq_of_int modulo_integer.abs_eq by presburger

lemma sym_div_code[code]: 
  "sym_div x y = (let yy = integer_of_int y in 
     (case divmod_integer (integer_of_int x) yy
     of (d, m) \<Rightarrow> if m + m \<le> yy then int_of_integer d else (int_of_integer (d + 1))))"
  unfolding sym_div_def Let_def divmod_integer_def split
  apply (rule if_cong, subst of_int_le_iff[symmetric], unfold of_int_add)
  by (subst (1 2) of_int_mod_integer, auto)

lemma sym_mod_sym_div: assumes y: "y > 0" shows "x symmod y = x - sym_div x y * y"
proof -
  let ?z = "x - y * (x div y)" 
  let ?u = "y * (x div y)" 
  have "x = y * (x div y) + x mod y" using y by simp
  hence id: "x mod y = ?z" by linarith
  have "x symmod y = poly_mod.inv_M y ?z" unfolding sym_mod_def id by auto
  also have "\<dots> = (if ?z + ?z \<le> y then ?z else ?z - y)" unfolding poly_mod.inv_M_def ..
  also have "\<dots> = x - (if (x mod y) + (x mod y) \<le> y then x div y else x div y + 1) * y" 
    by (simp add: algebra_simps id)
  also have "(if (x mod y) + (x mod y) \<le> y then x div y else x div y + 1) = sym_div x y" 
    unfolding sym_div_def Let_def ..
  finally show ?thesis .
qed
  
lemma dvd_sym_div_mult_right [simp]:
  "(a symdiv b) * b = a" if "b > 0" "b dvd a"
  using sym_mod_sym_div[of b a] that by simp

lemma dvd_sym_div_mult_left [simp]:
  "b * (a symdiv b) = a" if "b > 0" "b dvd a"
  using dvd_sym_div_mult_right[OF that] by (simp add: ac_simps)


end