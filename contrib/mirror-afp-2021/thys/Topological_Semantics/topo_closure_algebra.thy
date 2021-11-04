theory topo_closure_algebra
  imports topo_operators_basic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Closure algebra\<close>
text\<open>\noindent{We define a topological Boolean algebra with a primitive closure operator and verify a few properties.}\<close>

text\<open>\noindent{Declares a primitive (unconstrained) closure operation and defines others from it.}\<close>
consts \<C>::"\<sigma>\<Rightarrow>\<sigma>"
abbreviation "\<I> \<equiv> \<C>\<^sup>d" \<comment>\<open> interior \<close>
abbreviation "\<B> \<equiv> \<B>\<^sub>C \<C>" \<comment>\<open> border \<close>
abbreviation "\<F> \<equiv> \<F>\<^sub>C \<C>" \<comment>\<open> frontier \<close>


subsection \<open>Basic properties\<close>

text\<open>\noindent{Verifies minimal conditions under which operators resulting from conversion functions coincide.}\<close>
lemma ICdual': "\<C> \<^bold>\<equiv> \<I>\<^sup>d" using dual_symm equal_op_def by auto
lemma IB_rel: "Cl_2 \<C> \<Longrightarrow> \<I> \<^bold>\<equiv> \<I>\<^sub>B \<B>" using Br_cl_def EXP_dual1 Int_br_def compl_def dEXP_def diff_def dual_def equal_op_def meet_def by fastforce
lemma IF_rel: "Cl_2 \<C> \<Longrightarrow> \<I> \<^bold>\<equiv> \<I>\<^sub>F \<F>" by (smt EXP_def Fr_cl_def Int_fr_def compl_def diff_def dual_def equal_op_def meet_def) 
lemma CB_rel: "Cl_2 \<C> \<Longrightarrow> \<C> \<^bold>\<equiv> \<C>\<^sub>B \<B>" by (smt Cl_br_def EXP_def IB_rel Int_br_def compl_def diff_def dual_def dual_symm eq_ext' equal_op_def join_def)
lemma CF_rel: "Cl_2 \<C> \<Longrightarrow> \<C> \<^bold>\<equiv> \<C>\<^sub>F \<F>" by (smt Br_cl_def CB_rel Cl_br_def Cl_fr_def Fr_cl_def equal_op_def join_def meet_def)
lemma BI_rel: "\<B> \<^bold>\<equiv> \<B>\<^sub>I \<I>" using BI_BC_rel dual_symm equal_op_def by metis
lemma BF_rel: "Cl_2 \<C> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>F \<F>" by (smt Br_cl_def Br_fr_def EXP_def Fr_cl_def equal_op_def meet_def)
lemma FI_rel: "\<F> \<^bold>\<equiv> \<F>\<^sub>I \<I>" by (metis FI2 Fr_2_def Fr_cl_def Fr_int_def ICdual' dual_def eq_ext' equal_op_def)
lemma FB_rel: "Cl_2 \<C> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>B \<B>" by (smt BF_rel Br_fr_def CB_rel Cl_br_def Fr_br_def Fr_cl_def equal_op_def join_def meet_def)

text\<open>\noindent{Fixed-point and other operators are interestingly related.}\<close>
lemma fp1: "Cl_2 \<C> \<Longrightarrow> \<I>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>c" by (smt BI_rel Br_int_def IB_rel Int_br_def compl_def diff_def dimp_def equal_op_def)
lemma fp2: "Cl_2 \<C> \<Longrightarrow> \<B>\<^sup>f\<^sup>p \<^bold>\<equiv> \<I>\<^sup>c" using fp1 by (smt compl_def dimp_def equal_op_def)
lemma fp3: "Cl_2 \<C> \<Longrightarrow> \<C>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>d" by (smt BI_rel Br_int_def CB_rel Cl_br_def compl_def diff_def dimp_def dual_def equal_op_def join_def)
lemma fp4: "Cl_2 \<C> \<Longrightarrow> (\<B>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> \<C>" by (smt dimp_def equal_op_def fp3)
lemma fp5: "Cl_2 \<C> \<Longrightarrow> \<F>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B> \<^bold>\<squnion> (\<C>\<^sup>c)" by (smt Br_cl_def CF_rel Cl_fr_def FC2 Fr_2_def compl_def dimp_def eq_ext' equal_op_def join_def meet_def)

text\<open>\noindent{Define some fixed-point predicates and prove some properties.}\<close>
abbreviation openset ("Op") where "Op A \<equiv> fp \<I> A"
abbreviation closedset ("Cl") where "Cl A \<equiv> fp \<C> A"
abbreviation borderset ("Br") where "Br A \<equiv> fp \<B> A"
abbreviation frontierset ("Fr") where "Fr A \<equiv> fp \<F> A"

lemma Int_Open: "Cl_4 \<C> \<Longrightarrow> \<forall>A. Op(\<I> A)" using IC4 IDEM_def by blast
lemma Cl_Closed: "Cl_4 \<C> \<Longrightarrow> \<forall>A. Cl(\<C> A)" by (simp add: IDEM_def)
lemma Br_Border: "Cl_1b \<C> \<Longrightarrow> \<forall>A. Br(\<B> A)" by (metis BI_rel Br_cl_def Br_int_def CI1b MULT_a_def diff_def eq_ext' meet_def) 
text\<open>\noindent{In contrast, there is no analogous fixed-point result for frontier:}\<close>
lemma "\<CC> \<C> \<Longrightarrow> \<forall>A. Fr(\<F> A)" nitpick oops (*counterexample even if assuming all closure conditions*)

lemma OpCldual: "\<forall>A. Cl A \<longleftrightarrow> Op(\<^bold>\<midarrow>A)" by (simp add: compl_def dual_def)
lemma ClOpdual: "\<forall>A. Op A \<longleftrightarrow> Cl(\<^bold>\<midarrow>A)" by (simp add: fp_d)
lemma Fr_ClBr: "Cl_2 \<C> \<Longrightarrow> \<forall>A. Fr(A) = (Cl(A) \<and> Br(A))" using BF_rel by (metis Br_fr_def CF_rel Cl_fr_def eq_ext' join_def meet_def)
lemma Cl_F: "Cl_1b \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4 \<C> \<Longrightarrow> \<forall>A. Cl(\<F> A)" using Cl_8_def Fr_cl_def PC8 by auto

end
