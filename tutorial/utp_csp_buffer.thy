theory utp_csp_buffer
  imports "../theories/utp_csp"
begin

alphabet st_buffer =
  buff :: "nat list"

datatype ch_buffer =
  inp nat | outp nat
  
type_synonym act_buffer = "(st_buffer, ch_buffer) action"
  
definition Buffer :: act_buffer where
"Buffer = buff :=\<^sub>C \<langle>\<rangle> ;; (\<mu> X \<bullet> (inp\<^bold>?v \<^bold>\<rightarrow> buff :=\<^sub>C (&buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>)
                             \<box> (#\<^sub>u(&buff) >\<^sub>u 0) &\<^sub>u outp\<^bold>!last\<^sub>u(&buff) \<^bold>\<rightarrow> buff :=\<^sub>C tail\<^sub>u(&buff)) ;; X)"

end