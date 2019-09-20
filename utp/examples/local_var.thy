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

(* FIXME: Why does this fail?
term "swap wp U(&x = \<guillemotleft>Y\<guillemotright> \<and> &y = \<guillemotleft>X\<guillemotright>)"
*)

alphabet local2 = global +
  pivot :: int
  i :: nat
  j :: nat

abbreviation lv2 :: "<global, _> \<Longleftrightarrow> local2" where
"lv2 \<equiv> \<lparr> view = (global.base\<^sub>L :: (global \<Longrightarrow> local2)), coview = global.more\<^sub>L \<rparr>"

lemma sym_lens_lv2 [simp]: "sym_lens lv2"
  by (rule sym_lens.intro, simp_all)

abbreviation partititn :: "(int list \<Longrightarrow> local2) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> global hrel" where
"partititn A lo hi \<equiv>
   open\<^bsub>lv2\<^esub> ;;
   pivot := &A ! \<guillemotleft>hi\<guillemotright> ;;
   i := \<guillemotleft>lo\<guillemotright> ;;
   j := \<guillemotleft>lo\<guillemotright> ;;
   while j \<le> \<guillemotleft>hi\<guillemotright>
   do
     if (&A ! j) < pivot then
       (A[j], A[i]) := (&A ! i, &A ! j) ;;
       i := i + 1
     else II fi ;;
     j := j + 1
   od ;;
   (A[i], A[\<guillemotleft>hi\<guillemotright>]) := (&A ! \<guillemotleft>hi\<guillemotright>, &A ! i) ;;
   close\<^bsub>lv2\<^esub> "

lemma swap_wp: "swap wp (&x = \<guillemotleft>Y\<guillemotright> \<and> &y = \<guillemotleft>X\<guillemotright>) = U(&y = \<guillemotleft>Y\<guillemotright> \<and> &x = \<guillemotleft>X\<guillemotright>)"
  by (simp add: wp usubst unrest)

lemma swap_hoare: "\<lbrace>&x = \<guillemotleft>X\<guillemotright> \<and> &y = \<guillemotleft>Y\<guillemotright>\<rbrace> swap \<lbrace>&x = \<guillemotleft>Y\<guillemotright> \<and> &y = \<guillemotleft>X\<guillemotright>\<rbrace>\<^sub>u"
  unfolding block_open_def block_close_def
  by (rel_auto)

lemma swap_alt_def: "swap = (x, y) := (y, x)"
  by (rel_auto)

end