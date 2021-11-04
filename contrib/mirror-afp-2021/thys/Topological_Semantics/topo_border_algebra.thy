theory topo_border_algebra
  imports topo_operators_basic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Border algebra\<close>
text\<open>\noindent{We define a border algebra in an analogous fashion to the well-known closure/interior algebras.
We also verify a few interesting properties.}\<close>

text\<open>\noindent{Declares a primitive (unconstrained) border operation and defines others from it.}\<close>
consts \<B>::"\<sigma>\<Rightarrow>\<sigma>"
abbreviation "\<I> \<equiv> \<I>\<^sub>B \<B>" \<comment>\<open> interior \<close>
abbreviation "\<C> \<equiv> \<C>\<^sub>B \<B>" \<comment>\<open> closure \<close>
abbreviation "\<F> \<equiv> \<F>\<^sub>B \<B>" \<comment>\<open> frontier \<close>


subsection \<open>Basic properties\<close>

text\<open>\noindent{Verifies minimal conditions under which operators resulting from conversion functions coincide.}\<close>
lemma ICdual:  "\<I> \<^bold>\<equiv> \<C>\<^sup>d" by (simp add: Cl_br_def Int_br_def dual_def equal_op_def conn)
lemma ICdual': "\<C> \<^bold>\<equiv> \<I>\<^sup>d"  by (simp add: Cl_br_def Int_br_def dual_def equal_op_def conn)
lemma FI_rel: "Br_1 \<B> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>I \<I>" using Fr_br_def Fr_int_def Int_br_def equal_op_def by (smt Br_5b_def PB5b dual_def conn)
lemma IF_rel: "Br_1 \<B> \<Longrightarrow> \<I> \<^bold>\<equiv> \<I>\<^sub>F \<F>" using Br_5b_def Fr_br_def Int_br_def Int_fr_def PB5b unfolding equal_op_def conn by fastforce
lemma FC_rel: "Br_1 \<B> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>C \<C>" using Br_5b_def Cl_br_def Fr_br_def Fr_cl_def PB5b unfolding equal_op_def conn by fastforce
lemma CF_rel: "Br_1 \<B> \<Longrightarrow> \<C> \<^bold>\<equiv> \<C>\<^sub>F \<F>" using Br_5b_def Cl_br_def Cl_fr_def Fr_br_def PB5b unfolding equal_op_def conn by fastforce
lemma BI_rel: "Br_1 \<B> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>I \<I>" using Br_5b_def Br_int_def Int_br_def PB5b diff_def equal_op_def by fastforce
lemma BC_rel: "Br_1 \<B> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>C \<C>" using BI_BC_rel BI_rel ICdual' eq_ext' by fastforce
lemma BF_rel: "Br_1 \<B> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>F \<F>" by (smt BI_rel Br_fr_def Br_int_def IF_rel Int_fr_def diff_def equal_op_def meet_def) 

text\<open>\noindent{Fixed-point and other operators are interestingly related.}\<close>
lemma fp1: "Br_1 \<B> \<Longrightarrow> \<I>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>c" using Br_5b_def Int_br_def PB5b unfolding equal_op_def conn by fastforce
lemma fp2: "Br_1 \<B> \<Longrightarrow> \<B>\<^sup>f\<^sup>p \<^bold>\<equiv> \<I>\<^sup>c" using Br_5b_def Int_br_def PB5b conn equal_op_def by fastforce 
lemma fp3: "Br_1 \<B> \<Longrightarrow> \<C>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>d" using Br_5c_def Cl_br_def PB5c dual_def unfolding equal_op_def conn by fastforce
lemma fp4: "Br_1 \<B> \<Longrightarrow> (\<B>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> \<C>" by (smt dimp_def equal_op_def fp3)
lemma fp5: "Br_1 \<B> \<Longrightarrow> \<F>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B> \<^bold>\<squnion> (\<C>\<^sup>c)" by (smt Br_5b_def Cl_br_def Fr_br_def PB5b equal_op_def conn)

text\<open>\noindent{Define some fixed-point predicates and prove some properties.}\<close>
abbreviation openset ("Op") where "Op A \<equiv> fp \<I> A"
abbreviation closedset ("Cl") where "Cl A \<equiv> fp \<C> A"
abbreviation borderset ("Br") where "Br A \<equiv> fp \<B> A"
abbreviation frontierset ("Fr") where "Fr A \<equiv> fp \<F> A"

lemma Int_Open: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. Op(\<I> A)" using IB4 IDEM_def by blast
lemma Cl_Closed: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. Cl(\<C> A)" using CB4 IDEM_def by blast
lemma Br_Border: "Br_1 \<B> \<Longrightarrow> \<forall>A. Br(\<B> A)" using IDEM_def PB6 by blast
text\<open>\noindent{In contrast, there is no analogous fixed-point result for frontier:}\<close>
lemma "\<BB> \<B> \<Longrightarrow> \<forall>A. Fr(\<F> A)" nitpick oops (*counterexample even if assuming all border conditions*)

lemma OpCldual: "\<forall>A. Cl A \<longleftrightarrow> Op(\<^bold>\<midarrow>A)" using Cl_br_def Int_br_def conn by auto 
lemma ClOpdual: "\<forall>A. Op A \<longleftrightarrow> Cl(\<^bold>\<midarrow>A)" using Cl_br_def Int_br_def conn by auto
lemma Fr_ClBr: "Br_1 \<B> \<Longrightarrow> \<forall>A. Fr(A) = (Cl(A) \<and> Br(A))" by (metis BF_rel Br_fr_def CF_rel Cl_fr_def eq_ext' join_def meet_def)
lemma Cl_F: "Br_1 \<B> \<Longrightarrow> Br_3 \<B> \<Longrightarrow> \<forall>A. Cl(\<F> A)" by (metis CF_rel Cl_fr_def FB4 Fr_4_def eq_ext' join_def)

end
