section {* CSP process examples *}

theory utp_csp_ex
  imports "../theories/utp_csp"
begin

lemma csp_ex_1:
  "(a \<^bold>\<rightarrow> Stop \<box> b \<^bold>\<rightarrow> Skip) = 
       \<^bold>R\<^sub>s(true \<turnstile> ((\<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<and> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>))
               \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>b\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri Stop_is_CSP CSP3_Stop Skip_is_CSP CSP3_Skip
                pre_Stop peri_Stop post_Stop pre_Skip peri_Skip post_Skip extChoice_tri_rdes 
                usubst unrest, rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)

end