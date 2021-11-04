theory topo_operators_derivative
  imports topo_operators_basic
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)


subsection \<open>Derivative and coherence\<close>

text\<open>\noindent{In this section we investigate two related operators, namely the `derivative' (or `derived set')
and the (Cantorian) `coherence' of a set. The derivative of a set is the set of its accumulation (aka. limit)
points. The coherence of a set A is the set formed by those limit points of A belonging to A.
For the derivative operator we draw upon the works by Kuratowski @{cite Kuratowski1} and
(in more detail) by Zarycki @{cite Zarycki3}; cf.~also McKinsey \& Tarski @{cite AOT}.
For the (Cantorian) coherence operator we follow the treatment given by Zarycki in @{cite Zarycki2}.}\<close>

subsubsection \<open>Derivative conditions\<close>

text\<open>\noindent{The derivative conditions overlap partly with Kuratowski closure conditions @{cite Kuratowski1}.
We try to make both notations coincide when possible.}\<close>

abbreviation "Der_1 \<phi>  \<equiv> Cl_1 \<phi>"
abbreviation "Der_1a \<phi> \<equiv> Cl_1a \<phi>"
abbreviation "Der_1b \<phi> \<equiv> Cl_1b \<phi>"
abbreviation "Der_2 \<phi>  \<equiv> Cl_5 \<phi>" \<comment>\<open> follows from Cl-2 \<close>
abbreviation "Der_3 \<phi>  \<equiv> Cl_3 \<phi>"
abbreviation "Der_4 \<phi>  \<equiv> Cl_4' \<phi>"
definition   "Der_4e \<phi> \<equiv> \<forall>A. \<phi>(\<phi> A) \<^bold>\<preceq> (\<phi> A \<^bold>\<or> A)"
definition   "Der_5 \<phi> \<equiv> \<forall>A. (\<phi> A \<^bold>\<preceq> A) \<and> (A \<^bold>\<preceq> \<phi>\<^sup>d A) \<longrightarrow> (A \<^bold>\<approx> \<^bold>\<bottom> \<or> A \<^bold>\<approx> \<^bold>\<top>)"

text\<open>\noindent{Some remarks:
Condition Der-2 basically says (when assuming other derivative axioms) that the space is dense-in-itself,
i.e. that all points are accumulation points (no point is isolated) w.r.t the whole space.
Der-4 is a weakened (left-to-right) variant of Cl-4.
Condition Der-4e corresponds to a (weaker) condition than Der-4 and is used in more recent literature
(in particular in the works of Leo Esakia @{cite Esakia}).
When other derivative axioms are assumed, Der-5 above as used by Zarycki @{cite Zarycki3} says that
the only clopen sets in the space are the top and bottom elements (empty set and universe, resp.).
We verify some properties:}\<close>

lemma Der4e_rel: "Der_4 \<phi> \<Longrightarrow> Der_4e \<phi>" by (simp add: IDEMb_def Der_4e_def conn)
lemma PD1: "Der_1b \<phi> \<Longrightarrow> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> \<phi> A \<^bold>\<preceq> \<phi> B" using MONO_def MONO_ADDIb by auto
lemma PD2: "Der_1b \<phi> \<Longrightarrow> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> \<phi>\<^sup>d A \<^bold>\<preceq> \<phi>\<^sup>d B" using CI1b MONO_def MONO_MULTa dual_def by fastforce
lemma PD3: "Der_1b \<phi> \<Longrightarrow> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> \<phi> A \<^bold>\<and> \<phi> B" unfolding conn by (metis (no_types, lifting) PD1)
lemma PD4: "Der_1 \<phi> \<Longrightarrow> \<forall>A B. (\<phi> A \<^bold>\<leftharpoonup> \<phi> B) \<^bold>\<preceq> \<phi>(A \<^bold>\<leftharpoonup> B)" using Cl_6_def PC6 by metis
lemma PD5: "Der_4 \<phi> \<Longrightarrow> \<forall>A. \<phi>(\<phi>(\<^bold>\<midarrow>(\<phi> A))) \<^bold>\<preceq> \<phi>(\<^bold>\<midarrow>(\<phi> A))" unfolding IDEMb_def by blast
text\<open>\noindent{Observe that the lemmas below require Der-2 as premise:}\<close>
lemma PD6: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> \<forall>A. \<phi>\<^sup>d A \<^bold>\<preceq> \<phi> A" unfolding ADDI_def dNOR_def dual_def conn by fastforce
lemma PD7: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> \<forall>A. \<phi>(\<phi>\<^sup>d A) \<^bold>\<preceq> \<phi>(\<phi> A)" by (metis (mono_tags, lifting) PC1 PD1 PD6)
lemma PD8: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> Der_4 \<phi> \<Longrightarrow> \<forall>A. \<phi>(\<phi>\<^sup>d A) \<^bold>\<preceq> \<phi> A" by (meson IDEMb_def PD7)
lemma PD9: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> Der_4 \<phi> \<Longrightarrow> \<forall>A. \<phi>\<^sup>d A \<^bold>\<preceq> \<phi>\<^sup>d(\<phi> A)" by (metis CI4' IDEMa_def PC1 PD2 PD6)
lemma PD10: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> Der_4 \<phi> \<Longrightarrow> \<forall>A. \<phi>\<^sup>d A \<^bold>\<preceq> \<phi>(\<phi>\<^sup>d A)" using CI4' IDEMa_def PD6 by metis
lemma PD11: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> Der_4 \<phi> \<Longrightarrow> \<forall>A. \<^bold>\<midarrow>(\<phi> A) \<^bold>\<preceq> \<phi>(\<^bold>\<midarrow>(\<phi> A))" using IDEMb_def PD6 dual_def unfolding conn by metis
lemma PD12: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> Der_4 \<phi> \<Longrightarrow> \<forall>A. (\<phi>\<^sup>d A) \<^bold>\<and> (\<phi> A) \<^bold>\<approx> \<phi>\<^sup>d(A \<^bold>\<and> (\<phi> A))" proof -
 assume der1: "Der_1 \<phi>" and der2: "Der_2 \<phi>" and der4: "Der_4 \<phi>"
  { fix A 
    from der1 have "let M=\<^bold>\<midarrow>A ; N=\<^bold>\<midarrow>(\<phi> A) in \<phi>(M \<^bold>\<or> N) \<^bold>\<approx> (\<phi> M) \<^bold>\<or> (\<phi> N)" unfolding ADDI_def by simp
    hence aux: "\<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>(\<phi> A))) \<^bold>\<approx> \<^bold>\<midarrow>(\<phi> (\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>(\<phi> A)))" unfolding dual_def conn by simp
    have "(\<phi>\<^sup>d A \<^bold>\<and> \<phi> A) = (\<phi>\<^sup>d A \<^bold>\<and> \<phi>\<^sup>d(\<phi> A))" using PD6 PD9 der1 der2 der4 unfolding conn by metis
    also have "... = \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>(\<phi> A)))" unfolding dual_def conn by simp
    also from aux have "... = \<^bold>\<midarrow>(\<phi> (\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>(\<phi> A)))" unfolding dual_def by blast
    also have "... = \<phi>\<^sup>d(A \<^bold>\<and> (\<phi> A))" unfolding dual_def conn by simp
    finally have "(\<phi>\<^sup>d A) \<^bold>\<and> (\<phi> A) \<^bold>\<approx> \<phi>\<^sup>d(A \<^bold>\<and> (\<phi> A))" by simp
 } thus ?thesis by simp
qed

text\<open>\noindent{The conditions below can serve to axiomatize a derivative operator. Different authors consider different
sets of conditions. We define below some corresponding to Zarycki @{cite Zarycki3}, Kuratowski @{cite Kuratowski1}
@{cite Zarycki2}, McKinsey \& Tarski @{cite AOT}, and Esakia @{cite Esakia}, respectively.}\<close>
abbreviation "\<DD>z \<phi>  \<equiv> Der_1 \<phi> \<and> Der_2 \<phi> \<and> Der_3 \<phi> \<and> Der_4 \<phi> \<and> Der_5 \<phi>"
abbreviation "\<DD>k \<phi>  \<equiv> Der_1 \<phi> \<and> Der_2 \<phi> \<and> Der_3 \<phi> \<and> Der_4 \<phi>"
abbreviation "\<DD>mt \<phi> \<equiv> Der_1 \<phi>           \<and> Der_3 \<phi> \<and> Der_4 \<phi>"
abbreviation "\<DD>e \<phi>  \<equiv> Der_1 \<phi>           \<and> Der_3 \<phi> \<and> Der_4e \<phi>"

text\<open>\noindent{Our `default' derivative operator will coincide with @{text "\<DD>k"} from Kuratowski (also Zarycki).
However, for proving theorems we will employ the weaker variant Der-4e instead of Der-4 whenever possible.
We start by defining a dual operator and verifying some dualities; we then define conversion operators.
Observe that conditions Der-2 and  Der-5 are not used in the rest of this subsection.
Der-2 will be required later when working with the coherence operator.}\<close>
abbreviation "\<DD> \<phi> \<equiv> \<DD>k \<phi>"
abbreviation "\<Sigma> \<phi> \<equiv> Int_1 \<phi> \<and> Int_3 \<phi> \<and> Int_4' \<phi> \<and> Int_5 \<phi>" \<comment>\<open> 'dual-derivative' operator \<close>

lemma SD_dual1: "\<Sigma>(\<phi>) \<Longrightarrow> \<DD>(\<phi>\<^sup>d)" using IC1 IC4' IC3 IC5 by simp
lemma SD_dual2: "\<Sigma>(\<phi>\<^sup>d) \<Longrightarrow> \<DD>(\<phi>)" using IC1 IC4' IC3 IC5 dual_symm by metis
lemma DS_dual1: "\<DD>(\<phi>) \<Longrightarrow> \<Sigma>(\<phi>\<^sup>d)" using CI1 CI4' CI3 CI5 by simp
lemma DS_dual2: "\<DD>(\<phi>\<^sup>d) \<Longrightarrow> \<Sigma>(\<phi>)" using CI1 CI4' CI3 CI5 dual_symm by metis
lemma DS_dual: "\<DD>(\<phi>) = \<Sigma>(\<phi>\<^sup>d)"  using SD_dual2 DS_dual1 by smt

text\<open>\noindent{Closure operator as derived from derivative.}\<close>
definition Cl_der::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<C>\<^sub>D") where  "\<C>\<^sub>D \<D> \<equiv> \<lambda>A. A \<^bold>\<or> \<D>(A)"
text\<open>\noindent{Verify properties:}\<close>
lemma CD1a: "Der_1a \<D> \<Longrightarrow> Cl_1a (\<C>\<^sub>D \<D>)" unfolding Cl_der_def ADDI_a_def conn by auto
lemma CD1b: "Der_1b \<D> \<Longrightarrow> Cl_1b (\<C>\<^sub>D \<D>)" unfolding Cl_der_def ADDI_b_def conn by auto
lemma CD1 : "Der_1 \<D> \<Longrightarrow> Cl_1 (\<C>\<^sub>D \<D>)" unfolding Cl_der_def ADDI_def conn by blast
lemma CD2: "Cl_2 (\<C>\<^sub>D \<D>)" unfolding Cl_der_def EXP_def conn by simp
lemma CD3: "Der_3 \<D> \<Longrightarrow> Der_3 (\<C>\<^sub>D \<D>)" unfolding Cl_der_def NOR_def conn by simp
lemma CD4a: "Der_1a \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> Cl_4 (\<C>\<^sub>D \<D>)" unfolding Cl_der_def by (smt ADDI_a_def Der_4e_def IDEM_def join_def)
lemma "Der_1b \<D> \<Longrightarrow> Der_4 \<D> \<Longrightarrow> Cl_4 (\<C>\<^sub>D \<D>)" nitpick oops (*countermodel*)
lemma CD4: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> Cl_4 (\<C>\<^sub>D \<D>)" unfolding Cl_der_def by (metis (no_types, lifting) CD4a Cl_der_def IDEM_def PC1)

text\<open>\noindent{Interior operator as derived from (dual) derivative.}\<close>
definition Int_der::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<I>\<^sub>D") where "\<I>\<^sub>D \<D> \<equiv> \<lambda>A. A \<^bold>\<and> \<D>\<^sup>d(A)" 
text\<open>\noindent{Verify definition:}\<close>
lemma Int_der_def2: "\<I>\<^sub>D \<D> = (\<lambda>\<phi>. \<phi> \<^bold>\<leftharpoonup> \<D>(\<^bold>\<midarrow>\<phi>))" unfolding Int_der_def dual_def conn by simp 
lemma dual_der1: "\<C>\<^sub>D \<D> \<equiv> (\<I>\<^sub>D \<D>)\<^sup>d" unfolding Cl_der_def Int_der_def dual_def conn by simp
lemma dual_der2: "\<I>\<^sub>D \<D> \<equiv> (\<C>\<^sub>D \<D>)\<^sup>d" unfolding Cl_der_def Int_der_def dual_def conn by simp
text\<open>\noindent{Verify properties:}\<close>
lemma ID1: "Der_1 \<D> \<Longrightarrow> Int_1 (\<I>\<^sub>D \<D>)" using Int_der_def MULT_def ADDI_def CI1 unfolding conn by auto
lemma ID1a: "Der_1a \<D> \<Longrightarrow> Int_1b (\<I>\<^sub>D \<D>)" by (simp add: CI1a dual_der2 CD1a)
lemma ID1b: "Der_1b \<D> \<Longrightarrow> Int_1a (\<I>\<^sub>D \<D>)" by (simp add: CI1b dual_der2 CD1b)
lemma ID2: "Int_2 (\<I>\<^sub>D \<D>)" unfolding Int_der_def dEXP_def conn by simp
lemma ID3: "Der_3 \<D> \<Longrightarrow> Int_3 (\<I>\<^sub>D \<D>)" by (simp add: CI3 CD3 dual_der2)
lemma ID4: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> Int_4 (\<I>\<^sub>D \<D>)" using CI4 CD4 dual_der2 by simp
lemma ID4a: "Der_1a \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> Int_4 (\<I>\<^sub>D \<D>)" by (simp add: CI4 dual_der2 CD4a)
lemma "Der_1b \<D> \<Longrightarrow> Der_4 \<D> \<Longrightarrow> Int_4 (\<I>\<^sub>D \<D>)" nitpick oops (*countermodel*)

text\<open>\noindent{Border operator as derived from (dual) derivative.}\<close>
definition Br_der::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<B>\<^sub>D") where "\<B>\<^sub>D \<D> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> \<D>\<^sup>d(A)"
text\<open>\noindent{Verify definition:}\<close>
lemma Br_der_def2: "\<B>\<^sub>D \<D> = (\<lambda>A. A \<^bold>\<and> \<D>(\<^bold>\<midarrow>A))" unfolding Br_der_def dual_def conn by simp 
text\<open>\noindent{Verify properties:}\<close>
lemma BD1: "Der_1 \<D> \<Longrightarrow> Br_1 (\<B>\<^sub>D \<D>)" using Br_der_def Br_1_def CI1 MULT_def conn by auto 
lemma BD2: "Der_3 \<D> \<Longrightarrow> Br_2 (\<B>\<^sub>D \<D>)" using Br_der_def Br_2_def CI3 dNOR_def unfolding conn by auto
lemma BD3: "Der_1b \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> Br_3 (\<B>\<^sub>D \<D>)" using dual_def Der_4e_def MONO_ADDIb MONO_def  unfolding Br_der_def Br_3_def conn by smt

text\<open>\noindent{Frontier operator as derived from derivative.}\<close>
definition Fr_der::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<F>\<^sub>D") where "\<F>\<^sub>D \<D> \<equiv> \<lambda>A. (A \<^bold>\<leftharpoonup> \<D>\<^sup>d(A)) \<^bold>\<or> (\<D>(A) \<^bold>\<leftharpoonup> A)"
text\<open>\noindent{Verify definition:}\<close>
lemma Fr_der_def2: "\<F>\<^sub>D \<D> = (\<lambda>A. (A \<^bold>\<or> \<D>(A)) \<^bold>\<and> (\<^bold>\<midarrow>A \<^bold>\<or> \<D>(\<^bold>\<midarrow>A)))" unfolding Fr_der_def dual_def conn by auto  
text\<open>\noindent{Verify properties:}\<close>
lemma FD1a: "Der_1a \<D> \<Longrightarrow> Fr_1a(\<F>\<^sub>D \<D>)" unfolding Fr_1a_def Fr_der_def using CI1a MULT_b_def conn by auto
lemma FD1b: "Der_1b \<D> \<Longrightarrow> Fr_1b(\<F>\<^sub>D \<D>)" unfolding Fr_1b_def Fr_der_def using CI1b MULT_a_def conn by smt
lemma FD1: "Der_1 \<D> \<Longrightarrow> Fr_1(\<F>\<^sub>D \<D>)" unfolding Fr_1_def Fr_der_def using CI1 MULT_def conn by auto
lemma FD2: "Fr_2(\<F>\<^sub>D \<D>)" using dual_def dual_symm unfolding Fr_2_def Fr_der_def conn by metis
lemma FD3: "Der_3 \<D> \<Longrightarrow> Fr_3(\<F>\<^sub>D \<D>)" by (simp add: NOR_def Fr_der_def conn)
lemma FD4: "Der_1 \<D> \<Longrightarrow> Der_4e \<D> \<Longrightarrow> Fr_4(\<F>\<^sub>D \<D>)" by (metis CD1b CD2 CD4 Cl_8_def Cl_der_def Fr_4_def Fr_der_def2 PC1 PC8 meet_def)

text\<open>\noindent{Note that the derivative operation cannot be obtained from interior, closure, border, nor frontier.
In this respect the derivative is a fundamental operation.}\<close>

subsubsection \<open>Infinitary conditions\<close>

text\<open>\noindent{The corresponding infinitary condition on derivative operators is inherited from the one for closure.}\<close>
abbreviation "Der_inf \<phi> \<equiv> Cl_inf(\<phi>)"

lemma CD_inf: "Der_inf \<phi> \<Longrightarrow> Cl_inf(\<C>\<^sub>D \<phi>)" unfolding iADDI_a_def by (smt Cl_der_def Fr_2_def Ra_restr_ex compl_def dom_compl_def2 iDM_b join_def meet_def supremum_def)
lemma ID_inf: "Der_inf \<phi> \<Longrightarrow> Int_inf(\<I>\<^sub>D \<phi>)" by (simp add: CD_inf dual_der2 iADDI_MULT_dual1)

text\<open>\noindent{This condition is indeed strong enough as to entail closure of some fixed-point predicates under infimum/supremum.}\<close>
lemma fp_ID_inf_closed: "Der_inf \<phi> \<Longrightarrow> infimum_closed (fp (\<I>\<^sub>D \<phi>))" by (metis (full_types) ID2 ID_inf Ra_restr_all dEXP_def iMULT_b_def inf_char)
lemma fp_CD_sup_closed: "Der_inf \<phi> \<Longrightarrow> supremum_closed (fp (\<C>\<^sub>D \<phi>))" by (metis (full_types) CD_inf Cl_der_def Ra_restr_ex iADDI_a_def join_def supremum_def)


subsubsection \<open>Coherence conditions\<close>
text\<open>\noindent{We finish this section by introducing the `coherence' operator (Cantor's `Koherenz') as discussed
by Zarycki in @{cite Zarycki2}. As happens with the derivative operator, the coherence operator cannot
be derived from interior, closure, border, nor frontier.}\<close>

definition "Kh_1 \<phi> \<equiv> ADDI_b \<phi>"
definition "Kh_2 \<phi> \<equiv> dEXP \<phi>"
definition "Kh_3 \<phi> \<equiv> \<forall>A. \<phi>(\<phi>\<^sup>d A) \<^bold>\<approx> \<phi>\<^sup>d(\<phi> A)"

lemma PK1: "Kh_1 \<phi> \<equiv> MONO \<phi>" using ADDI_b_def Kh_1_def MONO_ADDIb by auto
lemma PK2: "Kh_1 \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" using MULT_a_def MONO_MULTa PK1 by auto
lemma PK3: "Kh_2 \<phi> \<Longrightarrow> \<phi> \<^bold>\<bottom> \<^bold>\<approx> \<^bold>\<bottom>" using Kh_2_def dEXP_def unfolding conn by auto
lemma PK4: "Kh_1 \<phi> \<Longrightarrow>  Kh_3 \<phi> \<Longrightarrow> \<phi> \<^bold>\<top> \<^bold>\<approx> \<^bold>\<top>" using MONO_def PK1 dual_def unfolding Kh_3_def conn by metis
lemma PK5: "Kh_2 \<phi> \<Longrightarrow>  \<forall>A. \<phi>(\<^bold>\<midarrow>A) \<^bold>\<preceq> \<^bold>\<midarrow>(\<phi> A)" unfolding Kh_2_def dEXP_def conn by metis
lemma PK6: "Kh_1 \<phi> \<Longrightarrow> Kh_2 \<phi> \<Longrightarrow>  \<forall>A B. \<phi>(A \<^bold>\<leftharpoonup> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<leftharpoonup> (\<phi> B)" unfolding conn by (metis (no_types, lifting) Kh_2_def dEXP_def MONO_def PK1)
lemma PK7: "Kh_3 \<phi> \<Longrightarrow>  \<forall>A. \<phi>(\<phi>(\<^bold>\<midarrow>(\<phi> A))) \<^bold>\<approx> \<phi>(\<^bold>\<midarrow>(\<phi>(\<phi>\<^sup>d A)))" proof -
 assume kh3: "Kh_3 \<phi>"
  { fix A
    from kh3 have "\<phi>(\<phi>\<^sup>d A) = \<phi>\<^sup>d(\<phi> A)" using Kh_3_def by auto
    hence "\<phi>(\<^bold>\<midarrow>(\<phi>(\<phi>\<^sup>d A))) \<^bold>\<approx> \<phi>(\<phi>(\<^bold>\<midarrow>(\<phi> A)))" unfolding dual_def conn by simp   
  } thus ?thesis by simp
qed
lemma PK8: "Kh_3 \<phi> \<Longrightarrow>  \<forall>A. \<phi>(\<^bold>\<midarrow>(\<phi>(\<phi> A))) \<^bold>\<approx> \<phi>\<^sup>d(\<phi>(\<^bold>\<midarrow>(\<phi> A)))" proof -
 assume kh3: "Kh_3 \<phi>"
  { fix A
    from kh3 have aux: "\<phi>\<^sup>d(\<phi> A) \<^bold>\<approx> \<phi>(\<phi>\<^sup>d A)" using Kh_3_def by simp
    have "let A=\<^bold>\<midarrow>(\<phi> A) in (\<phi>\<^sup>d(\<phi> A) \<^bold>\<approx> \<phi>(\<phi>\<^sup>d A))" using Kh_3_def kh3 by auto
    hence "\<phi>(\<^bold>\<midarrow>(\<phi>(\<phi> A))) \<^bold>\<approx> \<phi>\<^sup>d(\<phi>(\<^bold>\<midarrow>(\<phi> A)))" unfolding dual_def conn by simp
  } thus ?thesis  by simp
qed

text\<open>\noindent{Coherence operator as derived from derivative (requires conditions Der-2 and Der-4).}\<close>
definition Kh_der::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<K>\<^sub>D") where "\<K>\<^sub>D \<D> \<equiv> \<lambda>A. A \<^bold>\<and> (\<D> A)"
text\<open>\noindent{Verify properties:}\<close>
lemma KD1: "Der_1 \<phi> \<Longrightarrow> Kh_1 (\<K>\<^sub>D \<phi>)" using PC1 PD3 PK2 ADDI_def Kh_der_def unfolding conn by (metis (full_types))  
lemma KD2: "Kh_2 (\<K>\<^sub>D \<phi>)" by (simp add: Kh_2_def dEXP_def Kh_der_def conn) 
lemma KD3: "Der_1 \<phi> \<Longrightarrow> Der_2 \<phi> \<Longrightarrow> Der_4 \<phi>  \<Longrightarrow> Kh_3 (\<K>\<^sub>D \<phi>)" proof -
 assume der1: "Der_1 \<phi>" and der2: "Der_2 \<phi>" and der4: "Der_4 \<phi>"
  { fix A 
    from der1 have aux1: "let M=A ; N=(\<phi>\<^sup>d A) in \<phi>(M \<^bold>\<or> N) \<^bold>\<approx> (\<phi> M \<^bold>\<or> \<phi> N)" unfolding ADDI_def by simp
    from der1 der2 der4 have aux2: "(\<phi>\<^sup>d A) \<^bold>\<and> (\<phi> A) \<^bold>\<approx> \<phi>\<^sup>d(A \<^bold>\<and> \<phi> A)" using PD12 by simp
    have "(\<K>\<^sub>D \<phi>)((\<K>\<^sub>D \<phi>)\<^sup>d A) = (\<^bold>\<midarrow>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> (\<^bold>\<midarrow>A)) \<^bold>\<and> \<phi> (\<^bold>\<midarrow>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> (\<^bold>\<midarrow>A))))" unfolding Kh_der_def dual_def by simp
    also have "... = (A \<^bold>\<or> \<phi>\<^sup>d A) \<^bold>\<and> \<phi>(A \<^bold>\<or> \<phi>\<^sup>d A)" unfolding dual_def conn by simp
    also from aux1 have "... = (A \<^bold>\<or> \<phi>\<^sup>d A) \<^bold>\<and> (\<phi> A \<^bold>\<or> \<phi>(\<phi>\<^sup>d A))" unfolding conn by meson
    also have "... = (A \<^bold>\<and> \<phi> A) \<^bold>\<or> \<phi>\<^sup>d A" using PD6 PD8 der1 der2 der4 unfolding conn by blast
    also have "... = (A \<^bold>\<and> \<phi> A) \<^bold>\<or> (\<phi>\<^sup>d A \<^bold>\<and> \<phi> A)" using PD6 der1 der2 unfolding conn by blast
    also have "... = (A \<^bold>\<or> \<phi>\<^sup>d A) \<^bold>\<and> (\<phi> A)" unfolding conn by auto
    also from aux2 have "... = (A \<^bold>\<and> \<phi> A) \<^bold>\<or> \<phi>\<^sup>d(A \<^bold>\<and> \<phi> A)" unfolding dual_def conn by meson
    also have "... = \<^bold>\<midarrow>(\<^bold>\<midarrow>(A \<^bold>\<and> \<phi> A) \<^bold>\<and> \<phi> (\<^bold>\<midarrow>(A \<^bold>\<and> \<phi> A)))" unfolding dual_def conn by simp
    also have "... = (\<K>\<^sub>D \<phi>)\<^sup>d((\<K>\<^sub>D \<phi>) A)" unfolding Kh_der_def dual_def by simp
    finally have "(\<K>\<^sub>D \<phi>)((\<K>\<^sub>D \<phi>)\<^sup>d A) \<^bold>\<approx> (\<K>\<^sub>D \<phi>)\<^sup>d((\<K>\<^sub>D \<phi>) A)" by simp
 } thus ?thesis unfolding Kh_3_def by simp
qed

end
