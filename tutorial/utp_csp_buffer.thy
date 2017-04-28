theory utp_csp_buffer
  imports "../theories/utp_csp"
begin

alphabet st_buffer =
  buff :: "nat list"

datatype ch_buffer =
  Input nat | Output nat
  
type_synonym act_buffer = "(st_buffer, ch_buffer) action"
  
definition Buffer :: act_buffer where
"Buffer = \<langle>[buff \<mapsto>\<^sub>s \<guillemotleft>[]\<guillemotright>]\<rangle>\<^sub>R ;; (\<mu> X \<bullet> X)"
  
  
end