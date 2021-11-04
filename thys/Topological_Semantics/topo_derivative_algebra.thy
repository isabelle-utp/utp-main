theory topo_derivative_algebra
  imports topo_operators_derivative
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Derivative algebra\<close>
text\<open>\noindent{The closure of a set A (@{text "\<C>(A)"}) can be seen as the set A augmented by (i) its boundary points, or
(ii) its accumulation/limit points. We explore the second variant by drawing on the notion of derivative algebra.}\<close>

text\<open>\noindent{Declares a primitive (unconstrained) derivative (aka. derived-set) operation and defines others from it.}\<close>
consts \<D>::"\<sigma>\<Rightarrow>\<sigma>"
abbreviation "\<I> \<equiv> \<I>\<^sub>D \<D>" \<comment>\<open> interior \<close>
abbreviation "\<C> \<equiv> \<C>\<^sub>D \<D>" \<comment>\<open> closure \<close>
abbreviation "\<B> \<equiv> \<B>\<^sub>D \<D>" \<comment>\<open> border \<close>
abbreviation "\<F> \<equiv> \<F>\<^sub>D \<D>" \<comment>\<open> frontier \<close>
abbreviation "\<K> \<equiv> \<K>\<^sub>D \<D>" \<comment>\<open> coherence \<close>


subsection \<open>Basic properties\<close>

text\<open>\noindent{Verifies minimal conditions under which operators resulting from conversion functions coincide.}\<close>
lemma ICdual: "\<I> \<^bold>\<equiv> \<C>\<^sup>d" by (simp add: dual_der2 equal_op_def)
lemma ICdual': "\<C> \<^bold>\<equiv> \<I>\<^sup>d" by (simp add: dual_der1 equal_op_def)
lemma BI_rel: "\<B> \<^bold>\<equiv> \<B>\<^sub>I \<I>" using Br_der_def Br_int_def Int_der_def unfolding equal_op_def conn by auto
lemma IB_rel: "\<I> \<^bold>\<equiv> \<I>\<^sub>B \<B>" using Br_der_def Int_br_def Int_der_def unfolding equal_op_def conn by auto
lemma BC_rel: "\<B> \<^bold>\<equiv> \<B>\<^sub>C \<C>" using BI_BC_rel BI_rel dual_der1 by auto
lemma CB_rel: "\<C> \<^bold>\<equiv> \<C>\<^sub>B \<B>" using Br_der_def2 Cl_br_def Int_der_def2 dual_def dual_der1 unfolding equal_op_def conn by auto
lemma FI_rel: "\<F> \<^bold>\<equiv> \<F>\<^sub>I \<I>" by (metis Cl_der_def FI2 Fr_2_def Fr_der_def2 Fr_int_def ICdual' dual_def eq_ext' equal_op_def)
lemma FC_rel: "\<F> \<^bold>\<equiv> \<F>\<^sub>C \<C>" by (simp add: Cl_der_def Fr_cl_def Fr_der_def2 equal_op_def)
lemma FB_rel: "\<F> \<^bold>\<equiv> \<F>\<^sub>B \<B>" by (smt Br_der_def CB_rel Cl_br_def Cl_der_def Fr_br_def Fr_der_def Fr_der_def2 equal_op_def conn)

text\<open>\noindent{Recall that derivative and coherence operations cannot be obtained from either interior, closure, border
nor frontier. The derivative operation can indeed be seen as being more fundamental than the other ones.}\<close>

text\<open>\noindent{Fixed-point and other operators are interestingly related.}\<close>
lemma fp1: "\<I>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>c" by (smt BI_rel Br_int_def IB_rel Int_br_def equal_op_def conn)
lemma fp2: "\<B>\<^sup>f\<^sup>p \<^bold>\<equiv> \<I>\<^sup>c" using Br_der_def Int_der_def unfolding equal_op_def conn by auto 
lemma fp3: "\<C>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>d" by (smt BI_rel Br_int_def CB_rel Cl_br_def dual_def equal_op_def conn)
lemma fp4: "(\<B>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> \<C>" by (smt dimp_def equal_op_def fp3)
lemma fp5: "\<F>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B> \<^bold>\<squnion> (\<C>\<^sup>c)" using Br_der_def Cl_der_def Fr_der_def unfolding equal_op_def conn by auto
lemma fp6: "\<D>\<^sup>f\<^sup>p \<^bold>\<equiv> \<K> \<^bold>\<squnion> (\<C>\<^sup>c)" using Cl_der_def Kh_der_def equal_op_def conn by fastforce

text\<open>\noindent{Different inter-relations (some redundant ones are kept to help the provers).}\<close>
lemma monI: "Der_1b \<D> \<Longrightarrow> MONO \<I>" by (simp add: ID1b MONO_MULTa)
lemma monC: "Der_1b \<D> \<Longrightarrow> MONO \<C>" by (simp add: CD1b MONO_ADDIb)
lemma pB1: "\<forall>A. \<B> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<I> A" using BI_rel Br_int_def eq_ext' by fastforce
lemma pB2: "\<forall>A. \<B> A \<^bold>\<approx> A \<^bold>\<and> \<F> A" using Br_der_def Fr_der_def conn by auto
lemma pB3: "\<forall>A. \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<and> \<F> A" using FD2 Fr_2_def meet_def pB2 by auto
lemma pB4: "\<forall>A. \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<and> \<C> A" by (simp add: dual_def dual_der1 pB1 conn)
lemma pB5: "Der_1b \<D> \<Longrightarrow> \<forall>A. \<B>(\<C> A) \<^bold>\<preceq> (\<B> A) \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" using ADDI_b_def Cl_der_def MONO_ADDIb monI pB1 pB4 unfolding conn by auto
lemma pF1: "\<forall>A. \<F> A \<^bold>\<approx> \<C> A \<^bold>\<leftharpoonup> \<I> A"  using Cl_der_def Fr_der_def Int_der_def conn by auto
lemma pF2: "\<forall>A. \<F> A \<^bold>\<approx> \<C> A \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)" by (simp add: Cl_der_def Fr_der_def2)
lemma pF3: "\<forall>A. \<F> A \<^bold>\<approx> \<B> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" by (smt Br_der_def Cl_der_def dual_def dual_der1 dual_der2 pF2 conn)
lemma pF4: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A. \<F>(\<I> A) \<^bold>\<preceq> \<F> A" by (metis CD1 CD2 CD4a ICdual ID4 IDEM_def PC1 PC4 PC5 PD8 diff_def eq_ext' pF1)
lemma pF5: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A. \<F>(\<C> A) \<^bold>\<preceq> \<F> A" by (metis FD2 Fr_2_def ICdual' dual_def eq_ext' pF4)
lemma pA1: "\<forall>A. A \<^bold>\<approx> \<I> A \<^bold>\<or> \<B> A" using Br_der_def2 Int_der_def2 conn by auto
lemma pA2: "\<forall>A. A \<^bold>\<approx> \<C> A \<^bold>\<leftharpoonup> \<B>(\<^bold>\<midarrow>A)" using Cl_der_def pB4 conn by auto
lemma pC1: "\<forall>A. \<C> A \<^bold>\<approx> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" using CB_rel Cl_br_def eq_ext' by fastforce
lemma pC2: "\<forall>A. \<C> A \<^bold>\<approx> A \<^bold>\<or> \<F> A" using Cl_der_def Fr_der_def2 conn by auto
lemma pI1: "\<forall>A. \<I> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<B> A" using pA1 pB1 conn by auto
lemma pI2: "\<forall>A. \<I> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<F> A" using Br_der_def Fr_der_def pI1 conn by auto

lemma IC_imp: "Der_1 \<D> \<Longrightarrow> Der_3 \<D> \<Longrightarrow> \<forall>A B. \<I>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<C> A \<^bold>\<rightarrow> \<C> B" proof -
  assume der1: "Der_1 \<D>" and der3: "Der_3 \<D>"
  { fix a b
    have "(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a = \<^bold>\<top>" unfolding conn by auto
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a) \<^bold>\<approx> \<I>(\<^bold>\<top>)" by simp
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" using der3 dNOR_def using ID3 by auto 
    moreover have "let A=(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b; B=\<^bold>\<midarrow>a in \<I>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<I>(A) \<^bold>\<rightarrow> \<I>(B)" using ID1 Int_7_def PI7 der1 by auto
    ultimately have "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b) \<^bold>\<rightarrow> \<I>(\<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    moreover have "let A=a \<^bold>\<rightarrow> b; B=\<^bold>\<midarrow>b in \<I>(A \<^bold>\<and> B) \<^bold>\<approx> \<I>(A) \<^bold>\<and> \<I>(B)" using ID1 MULT_def der1 by auto
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<I>(\<^bold>\<midarrow>b) \<^bold>\<rightarrow> \<I>(\<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    moreover have "\<forall>A. \<I>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>\<C>(A)" by (simp add: dual_def dual_der1 conn)
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>\<C>(b) \<^bold>\<rightarrow> \<^bold>\<midarrow>\<C>(a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    hence "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>\<C>(b) \<^bold>\<preceq> \<^bold>\<midarrow>\<C>(a)" unfolding conn by simp
    hence "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<C> a \<^bold>\<preceq> \<C> b" unfolding conn by metis
  } thus ?thesis unfolding conn by simp
qed

text\<open>\noindent{Define some fixed-point predicates and prove some properties.}\<close>
abbreviation openset ("Op") where "Op A \<equiv> fp \<I> A"
abbreviation closedset ("Cl") where "Cl A \<equiv> fp \<C> A"
abbreviation borderset ("Br") where "Br A \<equiv> fp \<B> A"
abbreviation frontierset ("Fr") where "Fr A \<equiv> fp \<F> A"

lemma Int_Open: "Der_1a \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A. Op(\<I> A)" using ID4a IDEM_def by blast
lemma Cl_Closed: "Der_1a \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A. Cl(\<C> A)" using CD4a IDEM_def by blast
lemma Br_Border: "Der_1b \<D> \<Longrightarrow> \<forall>A. Br(\<B> A)" by (smt Br_der_def CI1b IC1_dual PD1 conn)
text\<open>\noindent{In contrast, there is no analogous fixed-point result for frontier:}\<close>
lemma "\<DD> \<D> \<Longrightarrow> \<forall>A. Fr(\<F> A)" nitpick oops (*counterexample even if assuming all derivative conditions*)
  
lemma OpCldual: "\<forall>A. Cl A \<longleftrightarrow> Op(\<^bold>\<midarrow>A)" using dual_def dual_der1 conn by auto
lemma ClOpdual: "\<forall>A. Op A \<longleftrightarrow> Cl(\<^bold>\<midarrow>A)" by (simp add: dual_def dual_der1 conn)
lemma Fr_ClBr: "\<forall>A. Fr(A) = (Cl(A) \<and> Br(A))" using join_def meet_def pB2 pC2 by auto
lemma Cl_F: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A. Cl(\<F> A)" using FD4 Fr_4_def join_def pC2 by auto


subsection \<open>Further properties\<close>

text\<open>\noindent{The definitions and theorems below are well known in the literature (e.g. @{cite Kuratowski2}).
Here we uncover the minimal conditions under which they hold (taking derivative operation as primitive).}\<close>
lemma Cl_Bzero: "\<forall>A. Cl A \<longleftrightarrow> \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<bottom>" using pA2 pC1 unfolding conn by metis
lemma Op_Bzero: "\<forall>A. Op A \<longleftrightarrow>  \<B> A \<^bold>\<approx> \<^bold>\<bottom>" using pB1 pI1 unfolding conn by metis
lemma Br_boundary: "\<forall>A. Br(A) \<longleftrightarrow> \<I> A \<^bold>\<approx> \<^bold>\<bottom>" using Br_der_def2 Int_der_def2 unfolding conn by metis
lemma Fr_nowhereDense: "\<forall>A. Fr(A) \<longrightarrow> \<I>(\<C> A) \<^bold>\<approx> \<^bold>\<bottom>" using Fr_ClBr Br_boundary eq_ext by metis
lemma Cl_FB: "\<forall>A. Cl A \<longleftrightarrow> \<F> A \<^bold>\<approx> \<B> A" using Br_der_def2 pA2 pF1 pF3 unfolding conn by metis
lemma Op_FB: "\<forall>A. Op A \<longleftrightarrow> \<F> A \<^bold>\<approx> \<B>(\<^bold>\<midarrow>A)" using pA1 pA2 pF3 pI2 unfolding conn by metis
lemma Clopen_Fzero: "\<forall>A. Cl A \<and> Op A \<longleftrightarrow> \<F> A \<^bold>\<approx> \<^bold>\<bottom>" using Cl_der_def Int_der_def Fr_der_def unfolding conn by smt

lemma Int_sup_closed: "Der_1b \<D> \<Longrightarrow> supremum_closed (\<lambda>A. Op A)" by (smt IC1_dual ID1b Int_der_def2 PD1 sup_char diff_def)
lemma Int_meet_closed: "Der_1a \<D> \<Longrightarrow> meet_closed (\<lambda>A. Op A)" by (metis ID1a Int_der_def MULT_b_def meet_def)
lemma Int_inf_closed: "Der_inf \<D> \<Longrightarrow> infimum_closed (\<lambda>A. Op A)" by (simp add: fp_ID_inf_closed)
lemma Cl_inf_closed: "Der_1b \<D> \<Longrightarrow> infimum_closed (\<lambda>A. Cl A)" by (smt Cl_der_def IC1_dual ID1b PD2 dual_der1 inf_char join_def)
lemma Cl_join_closed: "Der_1a \<D> \<Longrightarrow> join_closed (\<lambda>A. Cl A)" using ADDI_a_def Cl_der_def join_def by fastforce
lemma Cl_sup_closed: "Der_inf \<D> \<Longrightarrow> supremum_closed (\<lambda>A. Cl A)" by (simp add: fp_CD_sup_closed)
lemma Br_inf_closed: "Der_1b \<D> \<Longrightarrow> infimum_closed (\<lambda>A. Br A)" by (smt Br_der_def CI1b IC1_dual PD1 inf_char diff_def)
lemma Fr_inf_closed: "Der_1b \<D> \<Longrightarrow> infimum_closed (\<lambda>A. Fr A)" by (metis (full_types) Br_der_def Br_inf_closed Cl_der_def Cl_inf_closed Fr_der_def join_def diff_def)
lemma Br_Fr_join: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A B. Br A \<and> Fr B \<longrightarrow> Br(A \<^bold>\<or> B)" proof -
  assume der1: "Der_1 \<D>" and der4: "Der_4e \<D>"
  { fix A B
    { assume bra: "Br A" and frb: "Fr B"
      from bra have "\<I> A \<^bold>\<approx> \<^bold>\<bottom>" using Br_boundary by auto
      hence 1: "\<C>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<top>" by (metis ICdual bottom_def compl_def dual_def eq_ext' top_def)
      from frb have "\<I>(\<C> B) \<^bold>\<approx> \<^bold>\<bottom>" by (simp add: Fr_nowhereDense)
      hence 2: "\<C>(\<^bold>\<midarrow>(\<C> B)) \<^bold>\<approx> \<^bold>\<top>" by (metis ICdual bottom_def compl_def dual_def eq_ext' top_def)
      from der1 have "\<C>(\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>((\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> B)" by (simp add: CD1 PD4)
      hence "\<C>(\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" unfolding conn by simp
      hence "\<^bold>\<top> \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" using 1 unfolding conn by simp
      hence 3: "\<^bold>\<midarrow>(\<C> B) \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" unfolding conn by simp
      from der1 der4 have 4: "let M=\<^bold>\<midarrow>(\<C> B); N=\<^bold>\<midarrow>(A \<^bold>\<or> B) in  M \<^bold>\<preceq> \<C> N \<longrightarrow> \<C> M \<^bold>\<preceq> \<C> N" by (smt CD1b Cl_Closed PC1 PD1)
      from 3 4 have "\<C>(\<^bold>\<midarrow>(\<C> B)) \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" by simp 
      hence "\<^bold>\<top> \<^bold>\<approx> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" using 2 unfolding top_def by simp
      hence "\<^bold>\<bottom> \<^bold>\<approx> \<I>(A \<^bold>\<or> B)" using ICdual dual_def eq_ext' conn by metis
      hence "Br (A \<^bold>\<or> B)" using Br_boundary by simp
    } hence "Br A \<and> Fr B \<longrightarrow> Br (A \<^bold>\<or> B)" by simp
  } hence "\<forall>A B. Br A \<and> Fr B \<longrightarrow> Br (A \<^bold>\<or> B)" by simp
  thus ?thesis by simp
qed
lemma Fr_join_closed: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> join_closed (\<lambda>A. Fr A)" by (simp add: Br_Fr_join Cl_join_closed Fr_ClBr PC1)


text\<open>\noindent{Introduces a predicate for indicating that two sets are disjoint and proves some properties.}\<close>
abbreviation "Disj A B \<equiv> A \<^bold>\<and> B \<^bold>\<approx> \<^bold>\<bottom>" 

lemma Disj_comm: "\<forall>A B. Disj A B \<longrightarrow> Disj B A" unfolding conn by fastforce
lemma Disj_IF: "\<forall>A. Disj (\<I> A) (\<F> A)" by (simp add: Cl_der_def Fr_der_def2 dual_def dual_der2 conn)
lemma Disj_B: "\<forall>A. Disj (\<B> A) (\<B>(\<^bold>\<midarrow>A))" by (simp add: Br_der_def2 conn)
lemma Disj_I: "\<forall>A. Disj (\<I> A) (\<^bold>\<midarrow>A)" by (simp add: Int_der_def conn)
lemma Disj_BCI: "\<forall>A. Disj (\<B>(\<C> A)) (\<I>(\<^bold>\<midarrow>A))" by (simp add: Br_der_def2 dual_def dual_der1 conn)
lemma Disj_CBI: "Der_1b \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A. Disj (\<C>(\<B>(\<^bold>\<midarrow>A))) (\<I>(\<^bold>\<midarrow>A))" by (smt Br_der_def2 Der_4e_def Cl_der_def Int_der_def2 PD3 conn)

text\<open>\noindent{Introduce a predicate for indicating that two sets are separated and proves some properties.}\<close>
definition "Sep A B \<equiv> Disj (\<C> A) B \<and> Disj (\<C> B) A"

lemma Sep_comm: "\<forall>A B. Sep A B \<longrightarrow> Sep B A" by (simp add: Sep_def)
lemma Sep_disj: "\<forall>A B. Sep A B \<longrightarrow> Disj A B" using CD2 EXP_def Sep_def conn by auto
lemma Sep_I: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A. Sep (\<I> A) (\<I> (\<^bold>\<midarrow>A))" unfolding Sep_def by (smt CD2 CD4 IC1 ID1 PC4 PC5 PD8 dual_def dual_der1 dual_der2 conn)

lemma Sep_sub: "Der_1b \<D> \<Longrightarrow> \<forall>A B C D. Sep A B \<and> C \<^bold>\<preceq> A \<and> D \<^bold>\<preceq> B \<longrightarrow> Sep C D" using MONO_ADDIb PD2 dual_der1 monI unfolding Sep_def conn by metis
lemma Sep_Cl_diff: "Der_1b \<D> \<Longrightarrow> \<forall>A B. Cl(A) \<and> Cl(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" unfolding Sep_def using CD1b PD1 bottom_def diff_def meet_def by smt
lemma Sep_Op_diff: "Der_1b \<D> \<Longrightarrow> \<forall>A B. Op(A) \<and> Op(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" proof - 
  assume der1b:"Der_1b \<D>"
  { fix A B 
    from der1b have aux: "let M=\<^bold>\<midarrow>A ; N=\<^bold>\<midarrow>B in (Cl(M) \<and> Cl(N) \<longrightarrow> Sep (M \<^bold>\<leftharpoonup> N) (N \<^bold>\<leftharpoonup> M))" using Sep_Cl_diff by simp
    { assume "Op(A) \<and> Op(B)"
      hence "Cl(\<^bold>\<midarrow>A) \<and> Cl(\<^bold>\<midarrow>B)" using der1b ClOpdual by simp
      hence "Sep (\<^bold>\<midarrow>A \<^bold>\<leftharpoonup> \<^bold>\<midarrow>B) (\<^bold>\<midarrow>B \<^bold>\<leftharpoonup> \<^bold>\<midarrow>A)" using der1b aux unfolding conn by simp
      moreover have "(\<^bold>\<midarrow>A \<^bold>\<leftharpoonup> \<^bold>\<midarrow>B) \<^bold>\<approx> (B \<^bold>\<leftharpoonup> A)" unfolding conn by auto
      moreover have "(\<^bold>\<midarrow>B \<^bold>\<leftharpoonup> \<^bold>\<midarrow>A) \<^bold>\<approx> (A \<^bold>\<leftharpoonup> B)" unfolding conn by auto
      ultimately have "Sep (B \<^bold>\<leftharpoonup> A) (A \<^bold>\<leftharpoonup> B)" unfolding conn by simp
      hence "Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" using Sep_comm by simp
    } hence "Op(A) \<and> Op(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" by (rule impI)
  } thus ?thesis by simp
qed
lemma Sep_Cl: "\<forall>A B. Cl(A) \<and> Cl(B) \<and> Disj A B \<longrightarrow> Sep A B" unfolding Sep_def conn by blast
lemma Sep_Op: "Der_1b \<D>  \<Longrightarrow> \<forall>A B. Op(A) \<and> Op(B) \<and> Disj A B \<longrightarrow> Sep A B" proof -
  assume der1b:"Der_1b \<D>"
  { fix A B 
    from der1b have aux: "Op(A) \<and> Op(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" using Sep_Op_diff by simp
    { assume op: "Op(A) \<and> Op(B)" and disj: "Disj A B"
      hence "(A \<^bold>\<leftharpoonup> B) \<^bold>\<approx> A \<and> (B \<^bold>\<leftharpoonup> A) \<^bold>\<approx> B" unfolding conn by blast
      hence "Sep A B" using op aux unfolding conn by simp
    } hence "Op(A) \<and> Op(B) \<and> Disj A B \<longrightarrow> Sep A B" by simp
  } thus ?thesis by simp
qed
lemma "Der_1a \<D> \<Longrightarrow> \<forall>A B C. Sep A B \<and> Sep A C \<longrightarrow> Sep A (B \<^bold>\<or> C)" using ADDI_a_def CD1a unfolding Sep_def conn by metis


text\<open>\noindent{Verifies a neighborhood-based definition of interior.}\<close>
definition "nbhd A p \<equiv> \<exists>E. E \<^bold>\<preceq> A \<and> Op(E) \<and> (E p)"
lemma nbhd_def2: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> \<forall>A p. (nbhd A p) = (\<I> A p)" unfolding nbhd_def by (smt Int_Open MONO_def PC1 monI pI2 conn)

lemma I_def'_lr': "\<forall>A p. (\<I> A p) \<longrightarrow> (\<exists>E. (\<I> E p) \<and> E \<^bold>\<preceq> A)" by blast
lemma I_def'_rl': "Der_1b \<D> \<Longrightarrow> \<forall>A p. (\<I> A p) \<longleftarrow> (\<exists>E. (\<I> E p) \<and> E \<^bold>\<preceq> A)" using MONO_def monI by metis
lemma I_def': "Der_1b \<D> \<Longrightarrow>  \<forall>A p. (\<I> A p) \<longleftrightarrow> (\<exists>E. (\<I> E p) \<and> E \<^bold>\<preceq> A)" using MONO_def monI by metis


text\<open>\noindent{Explore the Barcan and converse Barcan formulas.}\<close>
lemma Barcan_I: "Der_inf \<D> \<Longrightarrow> \<forall>P. (\<^bold>\<forall>x. \<I>(P x)) \<^bold>\<preceq> \<I>(\<^bold>\<forall>x. P x)" using ID_inf Barcan1 by auto
lemma Barcan_C: "Der_inf \<D> \<Longrightarrow> \<forall>P. \<C>(\<^bold>\<exists>x. P x) \<^bold>\<preceq> (\<^bold>\<exists>x. \<C>(P x))" using CD_inf Barcan2 by metis
lemma CBarcan_I: "Der_1b \<D> \<Longrightarrow> \<forall>P. \<I>(\<^bold>\<forall>x. P x)  \<^bold>\<preceq> (\<^bold>\<forall>x. \<I>(P x))" by (metis (mono_tags, lifting) MONO_def monI)
lemma CBarcan_C: "Der_1b \<D> \<Longrightarrow> \<forall>P. (\<^bold>\<exists>x. \<C>(P x)) \<^bold>\<preceq> \<C>(\<^bold>\<exists>x. P x)"  by (metis (mono_tags, lifting) MONO_def monC)

end
