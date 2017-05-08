theory utp_csp_buffer
  imports "../theories/utp_csp"
begin

alphabet st_buffer =
  buff :: "nat list"

datatype ch_buffer =
  inp nat | outp nat
  
type_synonym act_buffer = "(st_buffer, ch_buffer) action"
  
abbreviation DoBuff :: act_buffer where
"DoBuff \<equiv> (inp?(v) \<^bold>\<rightarrow> buff :=\<^sub>C (&buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>)
           \<box> (#\<^sub>u(&buff) >\<^sub>u 0) &\<^sub>u outp!(head\<^sub>u(&buff)) \<^bold>\<rightarrow> buff :=\<^sub>C tail\<^sub>u(&buff))"

definition Buffer :: act_buffer where
"Buffer = buff :=\<^sub>C \<langle>\<rangle> ;; (\<mu> X \<bullet> DoBuff ;; CSP(X))"
  
declare image_eqI [closure del]
declare Healthy_set_image_member [closure del]
declare image_subsetI [closure del]  
declare NCSP_Healthy_subset_member [closure del]

lemma preR_DoBuff: "pre\<^sub>R(DoBuff) = true"
  by (simp add: rdes closure wp unrest usubst alpha)
    
lemma periR_DoBuff: 
  "peri\<^sub>R(DoBuff) = 
     ((\<Squnion> v \<bullet> (inp\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute>) \<and> $tr\<acute> =\<^sub>u $tr \<and>
      (\<lceil>(outp\<cdot>head\<^sub>u(&buff))\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> #\<^sub>u($st:buff) >\<^sub>u 0 \<triangleright> true)"
  by (simp add: rdes closure wp unrest usubst alpha, rel_auto)
  
lemma postR_DoBuff: 
  "post\<^sub>R(DoBuff) = ((\<Sqinter> v \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(inp\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle> \<and> \<lceil>buff := &buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>\<rceil>\<^sub>S) \<or>
                    #\<^sub>u($st:buff) >\<^sub>u 0 \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>(outp\<cdot>head\<^sub>u(&buff))\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>buff := tail\<^sub>u(&buff)\<rceil>\<^sub>S)"
  by (simp add: rdes closure wp unrest usubst alpha)
  
lemma preR_Buffer: "pre\<^sub>R(Buffer) = true"
  by (simp add: Buffer_def rdes closure wp unrest usubst alpha)
   
lemma postR_Buffer: "post\<^sub>R(Buffer) = false"
  by (simp add: Buffer_def rdes closure wp unrest usubst alpha)
    
lemma periR_Buffer: "peri\<^sub>R(Buffer) = undefined"
    apply (simp add: Buffer_def rdes closure wp unrest usubst alpha seq_UINF_distr)
oops
    
    
end