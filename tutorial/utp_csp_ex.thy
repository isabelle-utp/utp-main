section {* CSP process examples *}

theory utp_csp_ex
  imports "../theories/utp_csp"
begin

subsection {* Sequential Examples *}
  
text {* In this theory we calculate reactive designs for a number of simple CSP processes. *}

lemma csp_ex_1:
  "(a \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s(true \<turnstile> (&tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<diamondop> (&tt =\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri closure rdes usubst, rel_auto)

lemma csp_ex_2:
  "(a \<^bold>\<rightarrow> Chaos) = \<^bold>R\<^sub>s((\<not> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<le>\<^sub>u &tt) \<turnstile> (&tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<diamondop> false)"
  by (simp add: PrefixCSP_RHS_tri closure rdes usubst, rel_auto)

lemma csp_ex_3:
  "(a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip)
   = \<^bold>R\<^sub>s(true \<turnstile> (&tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute> \<or> &tt =\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> \<guillemotleft>b\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<diamondop> (&tt =\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>,\<guillemotleft>b\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (subst PrefixCSP_RHS_tri, simp_all add: closure rdes usubst unrest, rel_auto)

lemma csp_ex_4:
  "(a \<^bold>\<rightarrow> Stop \<box> b \<^bold>\<rightarrow> Skip) =
       \<^bold>R\<^sub>s(true \<turnstile> (($tr\<acute> =\<^sub>u $tr \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute> \<and> \<guillemotleft>b\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<or> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle>))
               \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>b\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri extChoice_tri_rdes rdes closure usubst unrest rpred, rel_auto)

lemma csp_ex_5:
  "(a \<^bold>\<rightarrow> Chaos \<box> b \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s ((\<not> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<le>\<^sub>u &tt) \<turnstile>
                                   (&tt =\<^sub>u \<langle>\<rangle> \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute> \<and> \<guillemotleft>b\<guillemotright> \<notin>\<^sub>u $ref\<acute>)
                                 \<diamondop> (&tt =\<^sub>u \<langle>\<guillemotleft>b\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: PrefixCSP_RHS_tri closure rdes extChoice_tri_rdes usubst unrest, rel_auto)

lemma csp_ex_6:
  assumes "P is NCSP" "Q is NCSP"
  shows "(a \<^bold>\<rightarrow> P \<box> a \<^bold>\<rightarrow> Q) = a \<^bold>\<rightarrow> (P \<sqinter> Q)"
  by (rdes_eq cls: assms)  

lemma csp_ex_7: "a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> Miracle \<sqsubseteq> a \<^bold>\<rightarrow> Miracle"
  by (rdes_refine)

subsection {* Parallel Examples *}
  
lemma csp_parallel_ex1:
  assumes "a \<in> cs" "P is NCSP" "Q is NCSP" "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "(a \<^bold>\<rightarrow> Skip \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> a \<^bold>\<rightarrow> Skip) = a \<^bold>\<rightarrow> Skip" (is "?lhs = ?rhs")
  using assms(1) by (rdes_eq cls: assms)

lemma csp_parallel_ex2:
  assumes "a \<in> cs" "b \<in> cs" "a \<noteq> b" "P is NCSP" "Q is NCSP" "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "(a \<^bold>\<rightarrow> Skip \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> b \<^bold>\<rightarrow> Skip) = Stop" (is "?lhs = ?rhs")
  using assms(1-3) by (rdes_eq cls: assms)
    
end