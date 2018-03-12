section {* CSP and Circus process examples *}

theory utp_csp_ex
  imports "../theories/circus/utp_circus"
begin

subsection {* Sequential Examples *}
  
text {* In this theory we calculate reactive designs for a number of simple CSP/Circus processes. *}

lemma csp_ex_1:
  "(a \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) \<diamondop> \<Phi>(true,id,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_2:
  "(a \<^bold>\<rightarrow> Chaos) = \<^bold>R\<^sub>s ((\<not>\<^sub>r \<I>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>)) \<turnstile> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) \<diamondop> false)"
  by (rdes_simp)

lemma csp_ex_3:
  "(a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip)
   =  \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) \<or> \<E>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>, {\<guillemotleft>b\<guillemotright>}\<^sub>u)) \<diamondop> \<Phi>(true,id,\<langle>\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_4:
  "(a \<^bold>\<rightarrow> Stop \<box> b \<^bold>\<rightarrow> Skip) =
   \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>}\<^sub>u) \<or> \<E>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>, {}\<^sub>u)) \<diamondop> \<Phi>(true,id,\<langle>\<guillemotleft>b\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_5:
  "(a \<^bold>\<rightarrow> Chaos \<box> b \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s ((\<not>\<^sub>r \<I>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>)) \<turnstile> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>}\<^sub>u) \<diamondop> \<Phi>(true,id,\<langle>\<guillemotleft>b\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_6:
  assumes "P is NCSP" "Q is NCSP"
  shows "(a \<^bold>\<rightarrow> P \<box> a \<^bold>\<rightarrow> Q) = a \<^bold>\<rightarrow> (P \<sqinter> Q)"
  by (rdes_simp cls: assms)  

lemma csp_ex_7: "a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> Miracle \<sqsubseteq> a \<^bold>\<rightarrow> Miracle"
  by (rdes_refine)

lemma csp_ex_8: 
  "a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip \<box> c \<^bold>\<rightarrow> Skip = 
   \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>, \<guillemotleft>c\<guillemotright>}\<^sub>u) \<or> \<E>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>, {\<guillemotleft>b\<guillemotright>}\<^sub>u)) \<diamondop> (\<Phi>(true,id,\<langle>\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>\<rangle>) \<or> \<Phi>(true,id,\<langle>\<guillemotleft>c\<guillemotright>\<rangle>)))"
  by (rdes_simp)

subsection {* State Examples *}

lemma assign_prefix_ex:
  assumes "vwb_lens x"
  shows "x :=\<^sub>C 1 ;; a \<^bold>\<rightarrow> x :=\<^sub>C (&x + 2) = a \<^bold>\<rightarrow> x :=\<^sub>C 3"
  (is "?lhs = ?rhs")
proof -
  from assms have "?lhs = \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) \<diamondop> \<Phi>(true,[&x \<mapsto>\<^sub>s 3],\<langle>\<guillemotleft>a\<guillemotright>\<rangle>))"
    by (rdes_simp)
  also have "... = ?rhs"
    by (rdes_simp)
  finally show ?thesis .
qed

subsection {* Parallel Examples *}
  
lemma csp_parallel_ex1:
  assumes "a \<in> cs" "P is NCSP" "Q is NCSP" "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "(a \<^bold>\<rightarrow> Skip \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> a \<^bold>\<rightarrow> Skip) = a \<^bold>\<rightarrow> Skip" (is "?lhs = ?rhs")
  using assms(1) by (rdes_eq cls: assms)

lemma csp_parallel_ex2:
  assumes "a \<in> cs" "b \<in> cs" "a \<noteq> b" "P is NCSP" "Q is NCSP" "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "(a \<^bold>\<rightarrow> Skip \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> b \<^bold>\<rightarrow> Skip) = Stop" (is "?lhs = ?rhs")
  using assms(1-3) by (rdes_eq cls: assms)

lemma csp_interleave_ex1: "a \<^bold>\<rightarrow> Skip ||| b \<^bold>\<rightarrow> Skip = (a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip \<box> b \<^bold>\<rightarrow> a \<^bold>\<rightarrow> Skip)"
  by (rdes_eq)
  
end