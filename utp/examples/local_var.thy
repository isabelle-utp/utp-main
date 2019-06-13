subsection \<open> Local Variables \<close>

theory local_var
  imports "UTP.utp"
begin

alphabet global =
  x :: int
  y :: int

alphabet local = global +
  temp :: int

abbreviation swap :: "global hrel" where
"swap \<equiv> open\<^bsub>global.base\<^sub>L :: global \<Longrightarrow> local\<^esub> ;; \<comment> \<open> Open the local scope \<close>
         temp := &x ;; \<comment> \<open> @{term x} is a global variable; @{term temp} is a local variable\<close> 
         x := &y ;; 
         y := &temp ;; 
         close\<^bsub>global.base\<^sub>L\<^esub>" \<comment> \<open> Close the local scope\<close>

lemma "\<lbrace>&x =\<^sub>u \<guillemotleft>X\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>Y\<guillemotright>\<rbrace>
        open\<^bsub>global.base\<^sub>L\<^esub> ;; temp := &x ;; x := &y ;; y := &temp ;; close\<^bsub>global.base\<^sub>L\<^esub>
       \<lbrace>&x =\<^sub>u \<guillemotleft>Y\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>X\<guillemotright>\<rbrace>\<^sub>u"
  unfolding block_open_def block_close_def
  by (rel_auto)

end