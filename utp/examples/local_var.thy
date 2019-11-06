subsection \<open> Local Variables \<close>

theory local_var
  imports "UTP.utp"
begin

utp_lit_vars

text \<open> State space of global variables. \<close>

alphabet global = x :: int  y :: int

abbreviation swap :: "global hrel" where
"swap \<equiv> var z :: int in all\<^sub>L \<bullet> z := x ;; x := y ;; y := &z"

lemma swap_wp: "swap wp (x = Y \<and> y = X) = \<^U>(y = Y \<and> x = X)"
  by (simp add: vblock_def wp usubst unrest)

lemma swap_hoare: "\<lbrace>x = X \<and> y = Y\<rbrace> swap \<lbrace>x = Y \<and> y = X\<rbrace>\<^sub>u" 
  by (rel_auto)

lemma swap_alt_def: "swap = (x, y) := (y, x)" by (rel_auto)

end