section \<open> CSP and Circus process examples \<close>

theory utp_csp_ex
  imports "../theories/circus/utp_circus"
begin

subsection \<open> Sequential Examples \<close>
  
text \<open> In this theory we calculate reactive designs for a number of simple CSP/Circus processes. \<close>

datatype ev = a | b | c

lemma csp_ex_1:
  "(a \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) \<diamondop> \<Phi>(true,id\<^sub>s,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_2:
  "(a \<^bold>\<rightarrow> Chaos) = \<^bold>R\<^sub>s ((\<I>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>)) \<turnstile> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) \<diamondop> false)"
  by (rdes_simp)

lemma csp_ex_3:
  "(a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip)
   =  \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) \<or> \<E>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>, {\<guillemotleft>b\<guillemotright>}\<^sub>u)) \<diamondop> \<Phi>(true,id\<^sub>s,\<langle>\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_4:
  "(a \<^bold>\<rightarrow> Stop \<box> b \<^bold>\<rightarrow> Skip) =
   \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>}\<^sub>u) \<or> \<E>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>, {}\<^sub>u)) \<diamondop> \<Phi>(true,id\<^sub>s,\<langle>\<guillemotleft>b\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_5:
  "(a \<^bold>\<rightarrow> Chaos \<box> b \<^bold>\<rightarrow> Skip) = \<^bold>R\<^sub>s (\<I>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>) \<turnstile> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>}\<^sub>u) \<diamondop> \<Phi>(true,id\<^sub>s,\<langle>\<guillemotleft>b\<guillemotright>\<rangle>))"
  by (rdes_simp)

lemma csp_ex_6:
  assumes "P is NCSP" "Q is NCSP"
  shows "(a \<^bold>\<rightarrow> P \<box> a \<^bold>\<rightarrow> Q) = a \<^bold>\<rightarrow> (P \<sqinter> Q)"
  by (rdes_simp cls: assms)  

lemma csp_ex_7: "a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> a \<^bold>\<rightarrow> Miracle \<sqsubseteq> a \<^bold>\<rightarrow> Miracle"
  by (rdes_refine)

lemma csp_ex_8: 
  "a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip \<box> c \<^bold>\<rightarrow> Skip = 
   \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>, \<guillemotleft>c\<guillemotright>}\<^sub>u) \<or> \<E>(true,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>, {\<guillemotleft>b\<guillemotright>}\<^sub>u)) \<diamondop> (\<Phi>(true,id\<^sub>s,\<langle>\<guillemotleft>a\<guillemotright>, \<guillemotleft>b\<guillemotright>\<rangle>) \<or> \<Phi>(true,id\<^sub>s,\<langle>\<guillemotleft>c\<guillemotright>\<rangle>)))"
  by (rdes_simp)

subsection \<open> State Examples \<close>

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

subsection \<open> Parallel Examples \<close>
  
lemma csp_parallel_ex1:
  "(a \<^bold>\<rightarrow> Skip) \<lbrakk>{a}\<rbrakk>\<^sub>C (a \<^bold>\<rightarrow> Skip) = a \<^bold>\<rightarrow> Skip" (is "?lhs = ?rhs")
  by (rdes_eq)

lemma csp_parallel_ex2:
  "(a \<^bold>\<rightarrow> Skip) \<lbrakk>{a,b}\<rbrakk>\<^sub>C (b \<^bold>\<rightarrow> Skip) = Stop" (is "?lhs = ?rhs")
  by (rdes_eq)

lemma csp_parallel_ex3:
  "(a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip) \<lbrakk>{b}\<rbrakk>\<^sub>C (b \<^bold>\<rightarrow> c \<^bold>\<rightarrow> Skip) = a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> c \<^bold>\<rightarrow> Skip" (is "?lhs = ?rhs") 
  by (rdes_eq)

lemma csp_parallel_ex4:
  "(a \<^bold>\<rightarrow> Skip \<box> b \<^bold>\<rightarrow> Skip) \<lbrakk>{b}\<rbrakk>\<^sub>C (b \<^bold>\<rightarrow> Skip) = a \<^bold>\<rightarrow> Stop \<box> b \<^bold>\<rightarrow> Skip" (is "?lhs = ?rhs") 
  by (rdes_eq)

lemma csp_parallel_ex5:
  "(a \<^bold>\<rightarrow> Chaos \<box> b \<^bold>\<rightarrow> Skip) \<lbrakk>{a, b}\<rbrakk>\<^sub>C (b \<^bold>\<rightarrow> Skip) = b \<^bold>\<rightarrow> Skip" (is "?lhs = ?rhs") 
  by (rdes_eq) 

lemma csp_parallel_ex6:
  assumes "vwb_lens ns\<^sub>1" "vwb_lens ns\<^sub>2" "x \<subseteq>\<^sub>L ns\<^sub>1" "y \<subseteq>\<^sub>L ns\<^sub>2" "ns\<^sub>1 \<bowtie> ns\<^sub>2"
  shows "(x :=\<^sub>C u) \<lbrakk>ns\<^sub>1\<parallel>{b}\<parallel>ns\<^sub>2\<rbrakk> (y :=\<^sub>C v) = \<langle>[x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]\<rangle>\<^sub>C"
  using assms by (rdes_eq)

lemma csp_interleave_ex1: "(a \<^bold>\<rightarrow> Skip) ||| (b \<^bold>\<rightarrow> Skip) = (a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip \<box> b \<^bold>\<rightarrow> a \<^bold>\<rightarrow> Skip)"
  by (rdes_eq)

lemma csp_hiding_ex1: "(a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip) \\\<^sub>C {b} = a \<^bold>\<rightarrow> Skip"
  by (rdes_eq)

lemma "(while\<^sub>C true do a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip od) \<lbrakk>{b}\<rbrakk>\<^sub>C (while\<^sub>C true do b \<^bold>\<rightarrow> c \<^bold>\<rightarrow> Skip od) = 
       while\<^sub>C true do a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> c \<^bold>\<rightarrow> Skip od"
  apply (rdes_eq_split)
  oops

(*
lemma
  assumes "P is NCSP" "Q is NCSP" "pre\<^sub>R P = true" "pre\<^sub>R Q = true" "B\<^sub>1 \<noteq> {}" "A\<^sub>1 \<noteq> {}"
    "peri\<^sub>R(P) = (\<Sqinter> i\<in>A\<^sub>1\<bullet> \<E>(s\<^sub>P\<^sub>1(i),t\<^sub>P\<^sub>1(i),E\<^sub>P(i)))"
    "post\<^sub>R(P) = (\<Sqinter> i\<in>A\<^sub>2\<bullet> \<Phi>(s\<^sub>P\<^sub>2(i),\<sigma>\<^sub>P(i),t\<^sub>P\<^sub>2(i)))"
    "peri\<^sub>R(Q) = (\<Sqinter> i\<in>B\<^sub>1\<bullet> \<E>(s\<^sub>Q\<^sub>1(i),t\<^sub>Q\<^sub>1(i),E\<^sub>Q(i)))"
    "post\<^sub>R(Q) = (\<Sqinter> i\<in>B\<^sub>2\<bullet> \<Phi>(s\<^sub>Q\<^sub>2(i),\<sigma>\<^sub>Q(i),t\<^sub>Q\<^sub>2(i)))"
  shows "(a \<^bold>\<rightarrow> P) ||| (b \<^bold>\<rightarrow> Q) = (a \<^bold>\<rightarrow> (P ||| (b \<^bold>\<rightarrow> Q)) \<box> b \<^bold>\<rightarrow> ((a \<^bold>\<rightarrow> P) ||| Q))"
  apply (rdes_eq_split cls: assms(1-2))
    apply (simp_all add: assms wp rpred closure usubst unrest rdes_rel_norms)
*) 

end