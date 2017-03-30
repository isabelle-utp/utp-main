section {* CSP process examples *}

theory utp_csp_ex
  imports "../theories/utp_csp"
begin

lemma csp_ex_1:
  "(a \<^bold>\<rightarrow> Stop \<box> b \<^bold>\<rightarrow> Skip) = 
       \<^bold>R\<^sub>s(true \<turnstile> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<and> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<or> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>))
               \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>b\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri Stop_is_CSP CSP3_Stop Skip_is_CSP CSP3_Skip rdes extChoice_tri_rdes 
                usubst unrest, rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
              
lemma csp_ex_2:
  "(a \<^bold>\<rightarrow> Chaos \<box> b \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s ((\<not> $tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>) \<turnstile>
                                   ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<and> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)
                                 \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>b\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri closure rdes extChoice_tri_rdes 
                usubst unrest, rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)

lemma csp_ex_3:
  "\<lbrakk> P is NCSP ; Q is NCSP \<rbrakk> \<Longrightarrow> (a \<^bold>\<rightarrow> P \<box> a \<^bold>\<rightarrow> Q) = a \<^bold>\<rightarrow> (P \<sqinter> Q)"
  apply (rule antisym)
  apply rdes_refine
  apply (rule_tac SRD_refine_intro)
  apply (simp_all add: closure rdes unrest usubst)
oops
    
end