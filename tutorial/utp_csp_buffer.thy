theory utp_csp_buffer
  imports "../theories/utp_csp"
begin

alphabet st_buffer =
  buff :: "nat list"

datatype ch_buffer =
  inp nat | outp nat
  
type_synonym act_buffer = "(st_buffer, ch_buffer) action"
  
abbreviation DoBuff :: act_buffer where
"DoBuff \<equiv> (inp\<^bold>?v \<^bold>\<rightarrow> buff :=\<^sub>C (&buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>)
           \<box> (#\<^sub>u(&buff) >\<^sub>u 0) &\<^sub>u outp\<^bold>!last\<^sub>u(&buff) \<^bold>\<rightarrow> buff :=\<^sub>C tail\<^sub>u(&buff))"
  
definition Buffer :: act_buffer where
"Buffer = buff :=\<^sub>C \<langle>\<rangle> ;; (\<mu> X \<bullet> (inp\<^bold>?v \<^bold>\<rightarrow> buff :=\<^sub>C (&buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>)
                             \<box> (#\<^sub>u(&buff) >\<^sub>u 0) &\<^sub>u outp\<^bold>!last\<^sub>u(&buff) \<^bold>\<rightarrow> buff :=\<^sub>C tail\<^sub>u(&buff)) ;; CSP(X))"
  
declare image_eqI [closure del]
declare Healthy_set_image_member [closure del]
declare image_subsetI [closure del]  
declare NCSP_Healthy_subset_member [closure del]
  
lemma preR_Buffer: "pre\<^sub>R(Buffer) = true"
  by (simp add: Buffer_def rdes closure wp Continuous_Monotonic unrest usubst alpha)
   
lemma postR_Buffer: "post\<^sub>R(Buffer) = false"
  by (simp add: Buffer_def rdes closure wp Continuous_Monotonic unrest usubst alpha)

lemma periR_Buffer: "peri\<^sub>R(Buffer) = undefined"
    apply (simp add: Buffer_def rdes closure wp Continuous_Monotonic unrest usubst alpha)
oops
    
    
end