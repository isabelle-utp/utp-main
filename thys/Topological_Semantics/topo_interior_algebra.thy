theory topo_interior_algebra
  imports topo_operators_basic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Interior algebra\<close>
text\<open>\noindent{We define a topological Boolean algebra taking the interior operator as primitive and verify some properties.}\<close>

text\<open>\noindent{Declares a primitive (unconstrained) interior operation and defines others from it.}\<close>
consts \<I>::"\<sigma>\<Rightarrow>\<sigma>"
abbreviation "\<C> \<equiv> \<I>\<^sup>d" \<comment>\<open> closure \<close>
abbreviation "\<B> \<equiv> \<B>\<^sub>I \<I>" \<comment>\<open> border \<close>
abbreviation "\<F> \<equiv> \<F>\<^sub>I \<I>" \<comment>\<open> frontier \<close>


subsection \<open>Basic properties\<close>

text\<open>\noindent{Verifies minimal conditions under which operators resulting from conversion functions coincide.}\<close>
lemma ICdual:  "\<I> \<^bold>\<equiv> \<C>\<^sup>d" using dual_symm equal_op_def by auto
lemma IB_rel: "Int_2 \<I> \<Longrightarrow> \<I> \<^bold>\<equiv> \<I>\<^sub>B \<B>" by (smt Br_int_def Int_br_def dEXP_def diff_def equal_op_def)
lemma IF_rel: "Int_2 \<I> \<Longrightarrow> \<I> \<^bold>\<equiv> \<I>\<^sub>F \<F>" using EXP_def EXP_dual2 Fr_int_def IB_rel Int_br_def Int_fr_def compl_def diff_def equal_op_def meet_def by fastforce  
lemma CB_rel: "Int_2 \<I> \<Longrightarrow> \<C> \<^bold>\<equiv> \<C>\<^sub>B \<B>" using Br_int_def Cl_br_def EXP_def EXP_dual2 compl_def diff_def dual_def equal_op_def join_def by fastforce
lemma CF_rel: "Int_2 \<I> \<Longrightarrow> \<C> \<^bold>\<equiv> \<C>\<^sub>F \<F>" by (smt Cl_fr_def EXP_def EXP_dual2 Fr_int_def compl_def dEXP_def equal_op_def join_def meet_def)
lemma BC_rel: "\<B> \<^bold>\<equiv> \<B>\<^sub>C \<C>" by (simp add: BI_BC_rel equal_op_def)
lemma BF_rel: "Int_2 \<I> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>F \<F>" by (smt Br_fr_def Br_int_def IF_rel Int_fr_def diff_def equal_op_def meet_def)
lemma FC_rel: "\<F> \<^bold>\<equiv> \<F>\<^sub>C \<C>" using Fr_cl_def Fr_int_def compl_def dual_def equal_op_def meet_def by fastforce
lemma FB_rel: "Int_2 \<I> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>B \<B>" unfolding Fr_br_def by (smt BC_rel Br_cl_def CB_rel Cl_br_def FC_rel Fr_cl_def equal_op_def join_def meet_def)

text\<open>\noindent{Fixed-point and other operators are interestingly related.}\<close>
lemma fp1: "Int_2 \<I> \<Longrightarrow> \<I>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>c" by (smt Br_int_def IB_rel Int_br_def compl_def diff_def dimp_def equal_op_def)
lemma fp2: "Int_2 \<I> \<Longrightarrow> \<B>\<^sup>f\<^sup>p \<^bold>\<equiv> \<I>\<^sup>c" using fp1 unfolding compl_def dimp_def equal_op_def by smt
lemma fp3: "Int_2 \<I> \<Longrightarrow> \<C>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>d" by (metis (no_types) dual_comp eq_ext' fp2 ofp_c ofp_d ofp_invol)
lemma fp4: "Int_2 \<I> \<Longrightarrow> (\<B>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> \<C>" by (smt dimp_def equal_op_def fp3)
lemma fp5: "Int_2 \<I> \<Longrightarrow> \<F>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B> \<^bold>\<squnion> (\<C>\<^sup>c)" by (smt BC_rel Br_cl_def CF_rel Cl_fr_def FI2 Fr_2_def compl_def dimp_def eq_ext' equal_op_def join_def meet_def)

text\<open>\noindent{Define some fixed-point predicates and prove some properties.}\<close>
abbreviation openset ("Op") where "Op A \<equiv> fp \<I> A"
abbreviation closedset ("Cl") where "Cl A \<equiv> fp \<C> A"
abbreviation borderset ("Br") where "Br A \<equiv> fp \<B> A"
abbreviation frontierset ("Fr") where "Fr A \<equiv> fp \<F> A"

lemma Int_Open: "Int_4 \<I> \<Longrightarrow> \<forall>A. Op(\<I> A)" by (simp add: IDEM_def)
lemma Cl_Closed: "Int_4 \<I> \<Longrightarrow> \<forall>A. Cl(\<C> A)" using IC4 IDEM_def by blast
lemma Br_Border: "Int_1a \<I> \<Longrightarrow> \<forall>A. Br(\<B> A)" by (metis Br_int_def MONO_MULTa MONO_def diff_def)
text\<open>\noindent{In contrast, there is no analogous fixed-point result for frontier:}\<close>
lemma "\<II> \<I> \<Longrightarrow> \<forall>A. Fr(\<F> A)" nitpick oops (*counterexample even if assuming all interior conditions*)

lemma OpCldual: "\<forall>A. Cl A \<longleftrightarrow> Op(\<^bold>\<midarrow>A)" by (simp add: fp_d)
lemma ClOpdual: "\<forall>A. Op A \<longleftrightarrow> Cl(\<^bold>\<midarrow>A)" by (simp add: compl_def dual_def)
lemma Fr_ClBr: "Int_2 \<I> \<Longrightarrow> \<forall>A. Fr(A) = (Cl(A) \<and> Br(A))" using BF_rel Br_fr_def CF_rel Cl_fr_def eq_ext' join_def meet_def by fastforce
lemma Cl_F: "Int_1a \<I> \<Longrightarrow> Int_2 \<I> \<Longrightarrow> Int_4 \<I> \<Longrightarrow> \<forall>A. Cl(\<F> A)" by (metis CF_rel Cl_fr_def FI4 Fr_4_def eq_ext' join_def)
 
end
