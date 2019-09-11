subsection \<open> Local Variables \<close>

theory local_var
  imports "UTP.utp"
begin

text \<open> State space of global variables. \<close>

alphabet global =
  x :: int
  y :: int

text \<open> State space of local variables, extending @{typ global} with an additional variable. \<close>

alphabet local = global +
  temp :: int

text \<open> Construct a symmetric lens that partitions the state space into globals and locals, using
  the lenses @{term global.base\<^sub>L} and @{term global.more\<^sub>L}. \<close>

abbreviation lv :: "<global, \<lparr>temp\<^sub>v :: int\<rparr>> \<Longleftrightarrow> local" where
"lv \<equiv> \<lparr> view = (global.base\<^sub>L :: (global \<Longrightarrow> local)), coview = global.more\<^sub>L \<rparr>"

lemma sym_lens_lv [simp]: "sym_lens lv"
  by (rule sym_lens.intro, simp_all)

text \<open> Define a program that uses the symmetric lens for modelling the variable scope \<close>

abbreviation swap :: "global hrel" where
"swap \<equiv> open\<^bsub>lv\<^esub> ;; \<comment> \<open> Open the local scope \<close>
         temp := &x ;; \<comment> \<open> @{term x} is a global variable; @{term temp} is a local variable\<close> 
         x := &y ;; 
         y := &temp ;; 
         close\<^bsub>lv\<^esub>" \<comment> \<open> Close the local scope\<close>

lemma swap_wp: "swap wp U(&x = \<guillemotleft>Y\<guillemotright> \<and> &y = \<guillemotleft>X\<guillemotright>) = U(&y = \<guillemotleft>Y\<guillemotright> \<and> &x = \<guillemotleft>X\<guillemotright>)"
  by (simp add: wp usubst unrest)

lemma swap_hoare: "\<lbrace>&x = \<guillemotleft>X\<guillemotright> \<and> &y = \<guillemotleft>Y\<guillemotright>\<rbrace> swap \<lbrace>&x = \<guillemotleft>Y\<guillemotright> \<and> &y = \<guillemotleft>X\<guillemotright>\<rbrace>\<^sub>u"
  unfolding block_open_def block_close_def
  by (rel_auto)

lemma swap_alt_def: "swap = (x, y) := (y, x)"
  by (rel_auto)

end