section {* CSP process examples *}

theory utp_csp_ex
  imports "../theories/utp_csp"
begin

declare zero_list_def [simp]
  
text {* In this theory we calculate reactive designs for a number of simple CSP processes. *}
  
lemma csp_ex_1:
  "(a \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s(true \<turnstile> (tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<diamondop> (tt =\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"  
  by (simp add: PrefixCSP_RHS_tri closure rdes usubst, rel_auto)

lemma csp_ex_2:
  "(a \<^bold>\<rightarrow> Chaos) = \<^bold>R\<^sub>s((\<not> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<le>\<^sub>u tt) \<turnstile> (tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<diamondop> false)"  
  by (simp add: PrefixCSP_RHS_tri closure rdes usubst, rel_auto)
    
lemma csp_ex_3:
  "(a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip) 
   = \<^bold>R\<^sub>s(true \<turnstile> (tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute> \<or> tt =\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> \<guillemotleft>b\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<diamondop> (tt =\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>,\<guillemotleft>b\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (subst PrefixCSP_RHS_tri, simp_all add: closure rdes usubst unrest, rel_auto)     
  
lemma csp_ex_4:
  "(a \<^bold>\<rightarrow> Stop \<box> b \<^bold>\<rightarrow> Skip) = 
       \<^bold>R\<^sub>s(true \<turnstile> (($tr\<acute> =\<^sub>u $tr \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute> \<and> \<guillemotleft>b\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<or> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle>))
               \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>b\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri Stop_is_CSP CSP3_Stop Skip_is_CSP CSP3_Skip rdes extChoice_tri_rdes 
                usubst unrest, rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)

              
lemma prefix_concat_dest [simp]: "x @ y \<le> z \<Longrightarrow> y \<le> z - x"
  by (metis Prefix_Order.same_prefix_prefix diff_add_cancel_left' list_append_prefixD plus_list_def)
  
lemma prefix_concat_minus_iff [simp]: "length y > 0 \<Longrightarrow> x @ y \<le> z \<longleftrightarrow> y \<le> z - x"
  by (metis Prefix_Order.prefix_length_le Prefix_Order.same_prefix_prefix diff_add_cancel_left' leD list.size(3) minus_cancel not_le_minus ordered_cancel_monoid_diff_class.diff_cancel plus_list_def prefix_concat_dest)
            
lemma csp_ex_5:
  "(a \<^bold>\<rightarrow> Chaos \<box> b \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s ((\<not> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<le>\<^sub>u tt) \<turnstile>
                                   (tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute> \<and> \<guillemotleft>b\<guillemotright> \<notin>\<^sub>u $ref\<acute>)
                                 \<diamondop> (tt =\<^sub>u \<langle>\<guillemotleft>b\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri closure rdes extChoice_tri_rdes usubst unrest, rel_auto)

lemma csp_ex_6:
  "\<lbrakk> P is NCSP ; Q is NCSP \<rbrakk> \<Longrightarrow> (a \<^bold>\<rightarrow> P \<box> a \<^bold>\<rightarrow> Q) = a \<^bold>\<rightarrow> (P \<sqinter> Q)"
  apply (rule antisym)
  apply rdes_refine
  apply (rule_tac SRD_refine_intro)
  apply (simp_all add: closure rdes unrest usubst)
  oops
    
lemma csp_ex_7: "a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> Miracle \<sqsubseteq> a \<^bold>\<rightarrow> Miracle"
  by (rdes_refine)    
  
end