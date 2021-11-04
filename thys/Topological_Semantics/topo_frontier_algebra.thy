theory topo_frontier_algebra
  imports topo_operators_basic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Frontier Algebra\<close>

text\<open>\noindent{The closure of a set A (@{text "\<C>(A)"}) can be seen as the set A augmented by (i) its boundary points,
or (ii) its accumulation/limit points. In this section we explore the first variant by drawing on the notion
of a frontier algebra, defined in an analogous fashion as the well-known closure and interior algebras.}\<close>

text\<open>\noindent{Declares a primitive (unconstrained) frontier (aka. boundary) operation and defines others from it.}\<close>
consts \<F>::"\<sigma>\<Rightarrow>\<sigma>"
abbreviation "\<I> \<equiv> \<I>\<^sub>F \<F>" \<comment>\<open> interior \<close>
abbreviation "\<C> \<equiv> \<C>\<^sub>F \<F>" \<comment>\<open> closure \<close>
abbreviation "\<B> \<equiv> \<B>\<^sub>F \<F>" \<comment>\<open> border \<close>


subsection \<open>Basic properties\<close>

text\<open>\noindent{Verifies minimal conditions under which operators resulting from conversion functions coincide.}\<close>
lemma ICdual: "Fr_2 \<F> \<Longrightarrow> \<I> \<^bold>\<equiv> \<C>\<^sup>d" by (simp add: Cl_fr_def Fr_2_def Int_fr_def dual_def equal_op_def conn)
lemma ICdual': "Fr_2 \<F> \<Longrightarrow> \<C> \<^bold>\<equiv> \<I>\<^sup>d" by (simp add: Cl_fr_def Fr_2_def Int_fr_def dual_def equal_op_def conn)
lemma BI_rel: "\<B> \<^bold>\<equiv> \<B>\<^sub>I \<I>" using Br_fr_def Br_int_def Int_fr_def unfolding equal_op_def conn by auto
lemma IB_rel: "\<I> \<^bold>\<equiv> \<I>\<^sub>B \<B>" using Br_fr_def Int_br_def Int_fr_def unfolding equal_op_def conn by auto
lemma BC_rel: "Fr_2 \<F> \<Longrightarrow> \<B> \<^bold>\<equiv> \<B>\<^sub>C \<C>"  using BI_BC_rel BI_rel ICdual' eq_ext' by fastforce
lemma CB_rel: "Fr_2 \<F> \<Longrightarrow> \<C> \<^bold>\<equiv> \<C>\<^sub>B \<B>" using Br_fr_def Cl_br_def Cl_fr_def Fr_2_def unfolding equal_op_def conn by auto
lemma FI_rel: "Fr_2 \<F> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>I \<I>" by (smt Cl_fr_def Fr_int_def ICdual' Int_fr_def compl_def diff_def equal_op_def join_def meet_def)
lemma FC_rel: "Fr_2 \<F> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>C \<C>" by (metis (mono_tags, lifting) FI_rel Fr_2_def Fr_cl_def Fr_int_def ICdual' dual_def eq_ext' equal_op_def)
lemma FB_rel: "Fr_2 \<F> \<Longrightarrow> \<F> \<^bold>\<equiv> \<F>\<^sub>B \<B>" by (smt Br_fr_def CB_rel Cl_br_def FC_rel Fr_br_def Fr_cl_def equal_op_def join_def meet_def)

text\<open>\noindent{Fixed-point and other operators are interestingly related.}\<close>
lemma fp1: "\<I>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>c" using Br_fr_def Int_fr_def unfolding equal_op_def conn by auto
lemma fp2: "\<B>\<^sup>f\<^sup>p \<^bold>\<equiv> \<I>\<^sup>c" using Br_fr_def Int_fr_def unfolding equal_op_def conn by auto 
lemma fp3: "Fr_2 \<F> \<Longrightarrow> \<C>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B>\<^sup>d" using Br_fr_def Cl_fr_def Fr_2_def dual_def equal_op_def conn by fastforce
lemma fp4: "Fr_2 \<F> \<Longrightarrow> (\<B>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> \<C>" by (smt dimp_def equal_op_def fp3)
lemma fp5: "\<F>\<^sup>f\<^sup>p \<^bold>\<equiv> \<B> \<^bold>\<squnion> (\<C>\<^sup>c)" using Br_fr_def Cl_fr_def unfolding equal_op_def conn by auto

text\<open>\noindent{Different inter-relations (some redundant ones are kept to help the provers).}\<close>
lemma monI: "Fr_1b \<F> \<Longrightarrow> MONO(\<I>)" by (simp add: IF1a MONO_MULTa)
lemma monC: "Fr_6 \<F> \<Longrightarrow> MONO(\<C>)" by (simp add: Cl_fr_def Fr_6_def MONO_def conn)
lemma pB1: "\<forall>A. \<B> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<I> A" using Br_fr_def fp1 unfolding conn equal_op_def by metis
lemma pB2: "\<forall>A. \<B> A \<^bold>\<approx> A \<^bold>\<and> \<F> A" by (simp add: Br_fr_def)
lemma pB3: "Fr_2 \<F> \<Longrightarrow> \<forall>A. \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<and> \<F> A" by (simp add: Fr_2_def pB2 conn)
lemma pB4: "Fr_2 \<F> \<Longrightarrow> \<forall>A. \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<and> \<C> A" using CB_rel Cl_br_def pB3 unfolding conn equal_op_def by metis
lemma pB5: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> \<forall>A. \<B>(\<C> A) \<^bold>\<preceq> (\<B> A) \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)"  by (smt BC_rel Br_cl_def Cl_fr_def Fr_6_def PF6 equal_op_def conn)
lemma pF1: "\<forall>A. \<F> A \<^bold>\<approx> \<C> A \<^bold>\<leftharpoonup> \<I> A"  using Cl_fr_def Int_fr_def conn by auto
lemma pF2: "Fr_2 \<F> \<Longrightarrow> \<forall>A. \<F> A \<^bold>\<approx> \<C> A \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)" using Cl_fr_def Fr_2_def conn by auto
lemma pF3: "Fr_2 \<F> \<Longrightarrow> \<forall>A. \<F> A \<^bold>\<approx> \<B> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" using Br_fr_def Fr_2_def conn by auto
lemma pF4: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4(\<F>) \<Longrightarrow> \<forall>A. \<F>(\<I> A) \<^bold>\<preceq> \<F> A" by (smt IDEMa_def IF2 IF4 Int_fr_def MONO_def PF1 PF6 PI4 diff_def monC pF1)
lemma pF5: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A. \<F>(\<C> A) \<^bold>\<preceq> \<F> A" by (metis Br_fr_def CF4 Cl_fr_def IDEM_def PF1 join_def meet_def pB5 pF3)
lemma pA1: "\<forall>A. A \<^bold>\<approx> \<I> A \<^bold>\<or> \<B> A" using Br_fr_def Int_fr_def unfolding conn by auto
lemma pA2: "Fr_2 \<F> \<Longrightarrow> \<forall>A. A \<^bold>\<approx> \<C> A \<^bold>\<leftharpoonup> \<B>(\<^bold>\<midarrow>A)" using pB1 dual_def fp3 unfolding equal_op_def conn by smt 
lemma pC1: "Fr_2 \<F> \<Longrightarrow> \<forall>A. \<C> A \<^bold>\<approx> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)" using Cl_fr_def pB4 conn by auto
lemma pC2: "\<forall>A. \<C> A \<^bold>\<approx> A \<^bold>\<or> \<F> A" using Cl_fr_def by auto
lemma pI1: "\<forall>A. \<I> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<B> A" using pA1 pB1 conn by auto
lemma pI2: "\<forall>A. \<I> A \<^bold>\<approx> A \<^bold>\<leftharpoonup> \<F> A" by (simp add: Int_fr_def)

lemma IC_imp: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>A B. \<I>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<C> A \<^bold>\<rightarrow> \<C> B" proof -
  assume fr1: "Fr_1 \<F>" and fr2: "Fr_2 \<F>" and fr3: "Fr_3 \<F>"
  { fix a b
    have "(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a = \<^bold>\<top>" unfolding conn by auto
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a) \<^bold>\<approx> \<I>(\<^bold>\<top>)" by simp
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<rightarrow> \<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" using fr3 IF3 dNOR_def fr2 by auto
    moreover have "let A=(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b; B=\<^bold>\<midarrow>a in \<I>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<I>(A) \<^bold>\<rightarrow> \<I>(B)" using fr1 IF1 PI7 Int_7_def by metis
    ultimately have "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b) \<^bold>\<rightarrow> \<I>(\<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    moreover have "let A=a \<^bold>\<rightarrow> b; B=\<^bold>\<midarrow>b in \<I>(A \<^bold>\<and> B) \<^bold>\<approx> \<I>(A) \<^bold>\<and> \<I>(B)" using fr1 IF1 MULT_def by simp
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<I>(\<^bold>\<midarrow>b) \<^bold>\<rightarrow> \<I>(\<^bold>\<midarrow>a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    moreover have "\<forall>A. \<I>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<midarrow>\<C>(A)" using Cl_fr_def Fr_2_def Int_fr_def fr2  unfolding conn by auto
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>\<C>(b) \<^bold>\<rightarrow> \<^bold>\<midarrow>\<C>(a) \<^bold>\<approx> \<^bold>\<top>" unfolding conn by simp
    hence "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>\<C>(b) \<^bold>\<preceq> \<^bold>\<midarrow>\<C>(a)" unfolding conn by simp
    hence "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<C> a \<^bold>\<preceq> \<C> b" unfolding conn by metis
  } thus ?thesis unfolding conn by simp
qed

text\<open>\noindent{Defines some fixed-point predicates and prove some properties.}\<close>
abbreviation openset ("Op") where "Op A \<equiv> fp \<I> A"
abbreviation closedset ("Cl") where "Cl A \<equiv> fp \<C> A"
abbreviation borderset ("Br") where "Br A \<equiv> fp \<B> A"
abbreviation frontierset ("Fr") where "Fr A \<equiv> fp \<F> A"

lemma Int_Open: "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A. Op(\<I> A)" using IF4 IDEM_def by blast
lemma Cl_Closed: "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A. Cl(\<C> A)" using CF4 IDEM_def by blast
lemma Br_Border: "Fr_1b \<F> \<Longrightarrow> \<forall>A. Br(\<B> A)" using Br_fr_def Fr_1b_def conn by auto
text\<open>\noindent{In contrast, there is no analogous fixed-point result for frontier:}\<close>
lemma "\<FF> \<F> \<Longrightarrow> \<forall>A. Fr(\<F> A)" nitpick oops (*counterexample even if assuming all frontier conditions*)

lemma OpCldual: "Fr_2 \<F> \<Longrightarrow> \<forall>A. Cl A \<longleftrightarrow> Op(\<^bold>\<midarrow>A)" using Cl_fr_def Fr_2_def Int_fr_def conn by auto
lemma ClOpdual: "Fr_2 \<F> \<Longrightarrow> \<forall>A. Op A \<longleftrightarrow> Cl(\<^bold>\<midarrow>A)" using ICdual dual_def unfolding equal_op_def conn by auto
lemma Fr_ClBr: "\<forall>A. Fr(A) = (Cl(A) \<and> Br(A))" using Br_fr_def Cl_fr_def join_def meet_def by auto
lemma Cl_F: "Fr_4 \<F> \<Longrightarrow> \<forall>A. Cl(\<F> A)" using Cl_fr_def Fr_4_def conn by auto


subsection \<open>Further properties\<close>

text\<open>\noindent{The definitions and theorems below are well known in the literature (e.g. @{cite Kuratowski2}).
Here we uncover the minimal conditions under which they hold (taking frontier operation as primitive).}\<close>
lemma Cl_Bzero: "Fr_2 \<F> \<Longrightarrow> \<forall>A. Cl A \<longleftrightarrow> \<B>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<bottom>" using pA2 pC1 unfolding conn by metis
lemma Op_Bzero: "\<forall>A. Op A \<longleftrightarrow> (\<B> A) \<^bold>\<approx> \<^bold>\<bottom>" using pB1 pI1 unfolding conn by metis
lemma Br_boundary: "Fr_2 \<F> \<Longrightarrow> \<forall>A. Br(A) \<longleftrightarrow> \<I> A \<^bold>\<approx> \<^bold>\<bottom>" by (metis Br_fr_def Int_fr_def bottom_def diff_def meet_def)
lemma Fr_nowhereDense: "Fr_2 \<F> \<Longrightarrow> \<forall>A. Fr(A) \<longrightarrow> \<I>(\<C> A) \<^bold>\<approx> \<^bold>\<bottom>" using Fr_ClBr Br_boundary eq_ext by metis
lemma Cl_FB: "\<forall>A. Cl A \<longleftrightarrow> \<F> A \<^bold>\<approx> \<B> A" using Br_fr_def Cl_fr_def unfolding conn by auto
lemma Op_FB: "Fr_2 \<F> \<Longrightarrow> \<forall>A. Op A \<longleftrightarrow> \<F> A \<^bold>\<approx> \<B>(\<^bold>\<midarrow>A)" using Br_fr_def Fr_2_def Int_fr_def unfolding conn by auto
lemma Clopen_Fzero: "\<forall>A. Cl A \<and> Op A \<longleftrightarrow> \<F> A \<^bold>\<approx> \<^bold>\<bottom>" using Cl_fr_def Int_fr_def unfolding conn by auto

lemma Int_sup_closed: "Fr_1b \<F> \<Longrightarrow> supremum_closed (\<lambda>A. Op A)" by (smt IF1a Int_fr_def MONO_def MONO_MULTa sup_char conn)
lemma Int_meet_closed: "Fr_1a \<F> \<Longrightarrow> meet_closed (\<lambda>A. Op A)" using Fr_1a_def Int_fr_def unfolding conn by metis
lemma Int_inf_closed: "Fr_inf \<F> \<Longrightarrow> infimum_closed (\<lambda>A. Op A)" by (simp add: fp_IF_inf_closed)
lemma Cl_inf_closed: "Fr_6 \<F> \<Longrightarrow> infimum_closed (\<lambda>A. Cl A)" by (smt Cl_fr_def Fr_6_def infimum_def join_def)
lemma Cl_join_closed: "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> join_closed (\<lambda>A. Cl A)" using ADDI_a_def CF1a CF2 EXP_def unfolding conn by metis
lemma Cl_sup_closed: "Fr_2 \<F> \<Longrightarrow> Fr_inf \<F> \<Longrightarrow> supremum_closed (\<lambda>A. Cl A)" by (simp add: fp_CF_sup_closed)
lemma Br_inf_closed: "Fr_1b \<F> \<Longrightarrow> infimum_closed (\<lambda>A. Br A)" by (smt BI_rel Br_int_def IF1a MONO_iMULTa MONO_MULTa Ra_restr_all eq_ext' iMULT_a_def inf_char diff_def)
lemma Fr_inf_closed: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> infimum_closed (\<lambda>A. Fr A)" by (metis (full_types) Br_fr_def Br_inf_closed PF6 Cl_fr_def Cl_inf_closed meet_def join_def)
lemma Br_Fr_join: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A B. Br A \<and> Fr B \<longrightarrow> Br(A \<^bold>\<or> B)" proof -
  assume fr1: "Fr_1 \<F>" and fr2: "Fr_2 \<F>" and fr4: "Fr_4 \<F>"
  { fix A B
    { assume bra: "Br A" and frb: "Fr B"
      from bra have "\<I> A \<^bold>\<approx> \<^bold>\<bottom>" using Br_boundary fr2 by auto
      hence 1: "\<C>(\<^bold>\<midarrow>A) \<^bold>\<approx> \<^bold>\<top>" by (metis ICdual bottom_def compl_def dual_def eq_ext' fr2 top_def)
      from frb have "\<I>(\<C> B) \<^bold>\<approx> \<^bold>\<bottom>" by (simp add: Fr_nowhereDense fr2)
      hence 2: "\<C>(\<^bold>\<midarrow>(\<C> B)) \<^bold>\<approx> \<^bold>\<top>" by (metis ICdual bottom_def compl_def dual_def eq_ext' fr2 top_def)
      from fr1 fr2 have "\<C>(\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>((\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> B)" using CF1 Cl_6_def PC6 by metis
      hence "\<C>(\<^bold>\<midarrow>A) \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" unfolding conn by simp
      hence "\<^bold>\<top> \<^bold>\<leftharpoonup> \<C> B \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" using 1 unfolding conn by simp
      hence 3: "\<^bold>\<midarrow>(\<C> B) \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" unfolding conn by simp
      from fr1 fr2 fr4 have 4: "let M=\<^bold>\<midarrow>(\<C> B); N=\<^bold>\<midarrow>(A \<^bold>\<or> B) in  M \<^bold>\<preceq> \<C> N \<longrightarrow> \<C> M \<^bold>\<preceq> \<C> N" using PC9 CF4 Cl_9_def PF1 CF1b by fastforce
      from 3 4 have "\<C>(\<^bold>\<midarrow>(\<C> B)) \<^bold>\<preceq> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" by simp 
      hence "\<^bold>\<top> \<^bold>\<approx> \<C>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" using 2 unfolding top_def by simp
      hence "\<^bold>\<bottom> \<^bold>\<approx> \<I>(A \<^bold>\<or> B)" using fr2 ICdual dual_def eq_ext' conn by metis
      hence "Br (A \<^bold>\<or> B)" using fr2 Br_boundary by simp
    } hence "Br A \<and> Fr B \<longrightarrow> Br (A \<^bold>\<or> B)" by simp
  } hence "\<forall>A B. Br A \<and> Fr B \<longrightarrow> Br (A \<^bold>\<or> B)" by simp
  thus ?thesis by simp
qed
lemma Fr_join_closed: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> join_closed (\<lambda>A. Fr A)" by (smt Br_Fr_join ADDI_a_def CF1a Cl_fr_def PF1 diff_def join_def meet_def pB2 pF1)


text\<open>\noindent{Introduces a predicate for indicating that two sets are disjoint and proves some properties.}\<close>
abbreviation "Disj A B \<equiv> A \<^bold>\<and> B \<^bold>\<approx> \<^bold>\<bottom>" 

lemma Disj_comm: "\<forall>A B. Disj A B \<longrightarrow> Disj B A" unfolding conn by fastforce
lemma Disj_IF: "\<forall>A. Disj (\<I> A) (\<F> A)" by (simp add: Int_fr_def conn)
lemma Disj_B: "\<forall>A. Disj (\<B> A) (\<B>(\<^bold>\<midarrow>A))" using Br_fr_def unfolding conn by auto
lemma Disj_I: "\<forall>A. Disj (\<I> A) (\<^bold>\<midarrow>A)" by (simp add: Int_fr_def conn)
lemma Disj_BCI: "Fr_2 \<F> \<Longrightarrow> \<forall>A. Disj (\<B>(\<C> A)) (\<I>(\<^bold>\<midarrow>A))" using Br_fr_def Cl_fr_def Fr_2_def Int_fr_def conn by metis
lemma Disj_CBI: "Fr_6 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A. Disj (\<C>(\<B>(\<^bold>\<midarrow>A))) (\<I>(\<^bold>\<midarrow>A))" by (metis Br_fr_def Cl_F IB_rel Int_br_def MONO_MULTa MULT_a_def eq_ext' monC conn)

text\<open>\noindent{Introduces a predicate for indicating that two sets are separated and proves some properties.}\<close>
definition "Sep A B \<equiv> Disj (\<C> A) B \<and> Disj (\<C> B) A"

lemma Sep_comm: "\<forall>A B. Sep A B \<longrightarrow> Sep B A" by (simp add: Sep_def)
lemma Sep_disj: "\<forall>A B. Sep A B \<longrightarrow> Disj A B" using Cl_fr_def Sep_def conn by fastforce
lemma Sep_I: "Fr_1(\<F>) \<Longrightarrow> Fr_2(\<F>) \<Longrightarrow> Fr_4(\<F>) \<Longrightarrow> \<forall>A. Sep (\<I> A) (\<I> (\<^bold>\<midarrow>A))" using Cl_fr_def pF4 Fr_2_def Int_fr_def unfolding Sep_def conn by metis
lemma Sep_sub: "Fr_6 \<F>  \<Longrightarrow> \<forall>A B C D. Sep A B \<and> C \<^bold>\<preceq> A \<and> D \<^bold>\<preceq> B \<longrightarrow> Sep C D" using MONO_def monC unfolding Sep_def conn by smt
lemma Sep_Cl_diff: "Fr_6 \<F> \<Longrightarrow> \<forall>A B. Cl(A) \<and> Cl(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" using Fr_6_def pC2 unfolding Sep_def conn by smt
lemma Sep_Op_diff: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> \<forall>A B. Op(A) \<and> Op(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" proof - 
  assume fr1b:"Fr_1b \<F>" and fr2:"Fr_2 \<F>"
  { fix A B 
    from fr1b fr2 have aux: "let M=\<^bold>\<midarrow>A ; N=\<^bold>\<midarrow>B in (Cl(M) \<and> Cl(N) \<longrightarrow> Sep (M \<^bold>\<leftharpoonup> N) (N \<^bold>\<leftharpoonup> M))" using PF6 Sep_Cl_diff by simp
    { assume "Op(A) \<and> Op(B)"
      hence "Cl(\<^bold>\<midarrow>A) \<and> Cl(\<^bold>\<midarrow>B)" using fr2 ClOpdual by simp
      hence "Sep (\<^bold>\<midarrow>A \<^bold>\<leftharpoonup> \<^bold>\<midarrow>B) (\<^bold>\<midarrow>B \<^bold>\<leftharpoonup> \<^bold>\<midarrow>A)" using fr1b fr2 aux unfolding conn by simp
      moreover have "(\<^bold>\<midarrow>A \<^bold>\<leftharpoonup> \<^bold>\<midarrow>B) \<^bold>\<approx> (B \<^bold>\<leftharpoonup> A)" unfolding conn by auto
      moreover have "(\<^bold>\<midarrow>B \<^bold>\<leftharpoonup> \<^bold>\<midarrow>A) \<^bold>\<approx> (A \<^bold>\<leftharpoonup> B)" unfolding conn by auto
      ultimately have "Sep (B \<^bold>\<leftharpoonup> A) (A \<^bold>\<leftharpoonup> B)" unfolding conn by simp
      hence "Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" using Sep_comm by simp
    } hence "Op(A) \<and> Op(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" by (rule impI)
  } thus ?thesis by simp
qed
lemma Sep_Cl: "\<forall>A B. Cl(A) \<and> Cl(B) \<and> Disj A B \<longrightarrow> Sep A B" unfolding Sep_def conn by blast
lemma Sep_Op: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F>  \<Longrightarrow> \<forall>A B. Op(A) \<and> Op(B) \<and> Disj A B \<longrightarrow> Sep A B" proof -
  assume fr1b:"Fr_1b \<F>" and fr2:"Fr_2 \<F>"
  { fix A B 
    from fr1b fr2 have aux: "Op(A) \<and> Op(B) \<longrightarrow> Sep (A \<^bold>\<leftharpoonup> B) (B \<^bold>\<leftharpoonup> A)" using Sep_Op_diff by simp
    { assume op: "Op(A) \<and> Op(B)" and disj: "Disj A B"
      hence "(A \<^bold>\<leftharpoonup> B) \<^bold>\<approx> A \<and> (B \<^bold>\<leftharpoonup> A) \<^bold>\<approx> B" unfolding conn by blast
      hence "Sep A B" using op aux unfolding conn by simp
    } hence "Op(A) \<and> Op(B) \<and> Disj A B \<longrightarrow> Sep A B" by simp
  } thus ?thesis by simp
qed
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> \<forall>A B C. Sep A B \<and> Sep A C \<longrightarrow> Sep A (B \<^bold>\<or> C)" using CF1a ADDI_a_def unfolding Sep_def conn by metis


text\<open>\noindent{Verifies a neighborhood-based definition of closure.}\<close>
definition "nbhd A p \<equiv> \<exists>E. E \<^bold>\<preceq> A \<and> Op(E) \<and> (E p)"
lemma nbhd_def2: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A p. (nbhd A p) = (\<I> A p)" using pF4 MONO_def PF1 monI pI2 unfolding nbhd_def conn by smt

lemma C_def_lr: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A p. (\<C> A p) \<longrightarrow> (\<forall>E. (nbhd E p) \<longrightarrow> \<not>(Disj E A))" using Cl_fr_def Fr_2_def Fr_6_def PF6 pF1 unfolding nbhd_def conn by smt
lemma C_def_rl: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A p. (\<C> A p) \<longleftarrow> (\<forall>E. (nbhd E p) \<longrightarrow> \<not>(Disj E A))" using Cl_fr_def pF5 pA1 pB4 unfolding nbhd_def conn by smt
lemma C_def: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>A p. (\<C> A p) \<longleftrightarrow> (\<forall>E. (nbhd E p) \<longrightarrow> \<not>(Disj E A))" using C_def_lr C_def_rl PF1 by blast


text\<open>\noindent{Explore the Barcan and converse Barcan formulas.}\<close>
lemma Barcan_I: "Fr_inf \<F> \<Longrightarrow> \<forall>P. (\<^bold>\<forall>x. \<I>(P x)) \<^bold>\<preceq> \<I>(\<^bold>\<forall>x. P x)" using IF_inf Barcan1 by auto
lemma Barcan_C: "Fr_2 \<F> \<Longrightarrow> Fr_inf \<F> \<Longrightarrow> \<forall>P. \<C>(\<^bold>\<exists>x. P x) \<^bold>\<preceq> (\<^bold>\<exists>x. \<C>(P x))" using Fr_2_def CF_inf Barcan2 by metis
lemma CBarcan_I: "Fr_1b \<F> \<Longrightarrow> \<forall>P. \<I>(\<^bold>\<forall>x. P x)  \<^bold>\<preceq> (\<^bold>\<forall>x. \<I>(P x))" by (metis (mono_tags, lifting) MONO_def monI)
lemma CBarcan_C: "Fr_6 \<F> \<Longrightarrow> \<forall>P. (\<^bold>\<exists>x. \<C>(P x)) \<^bold>\<preceq> \<C>(\<^bold>\<exists>x. P x)"  by (metis (mono_tags, lifting) MONO_def monC)

end
