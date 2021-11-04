theory ex_subminimal_logics
  imports topo_negation_conditions topo_strict_implication
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Example application: Subintuitionistic and subminimal logics\<close>

text\<open>\noindent{In this section we examine some special paracomplete logics. The idea is to illustrate an approach by
means of which we can obtain logics which are boldly paracomplete and (non-boldly) paraconsistent at the
same time, Johansson's 'minimal logic' @{cite JML} being the paradigmatic case we aim at modelling.}\<close>

text\<open>\noindent{Drawing upon the literature on Johanson's minimal logic, we introduce an unconstrained propositional
constant Q, which we then employ to define a 'rigid' frontier operation @{text "\<F>'"}.}\<close>
consts Q::"\<sigma>"
abbreviation "\<F>' \<equiv> \<lambda>X. Q" 
abbreviation "\<I>' \<equiv> \<I>\<^sub>F \<F>'"
abbreviation "\<C>' \<equiv> \<C>\<^sub>F \<F>'"
abbreviation "\<B>' \<equiv> \<B>\<^sub>F \<F>'"

text\<open>\noindent{As defined, @{text "\<F>'"} (and its corresponding closure operation) satisfies several semantic conditions.}\<close>
lemma "Fr_1 \<F>' \<and> Fr_2 \<F>' \<and> Fr_4 \<F>'" by (simp add: Fr_1_def Fr_2_def Fr_4_def conn)
lemma "Cl_1 \<C>' \<and> Cl_2 \<C>' \<and> Cl_4 \<C>'" using ADDI_def CF2 IDEMb_def Cl_fr_def PC4 unfolding conn by auto
text\<open>\noindent{However Fr-3 is not valid. In fact, adding it by hand would collapse into classical logic (making all sets clopen).}\<close>
lemma "Fr_3 \<F>'" nitpick oops (*counterexample found*)
lemma "Cl_3 \<C>'" nitpick oops (*counterexample found*)
lemma "Fr_3 \<F>' \<Longrightarrow> \<forall>A. \<F>'(A) \<^bold>\<approx> \<^bold>\<bottom>"  by (simp add: NOR_def) 

text\<open>\noindent{In order to obtain a paracomplete logic not validating ECQ, we define negation as follows,}\<close>
abbreviation neg_IC::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>")  where  "\<^bold>\<not>A \<equiv> \<C>'(\<I>(\<^bold>\<midarrow>A))"

text\<open>\noindent{and observe that some plausible semantic properties obtain:}\<close>
lemma Q_def1: "\<forall>A. Q \<^bold>\<approx> \<^bold>\<not>A \<^bold>\<and> \<^bold>\<not>(\<^bold>\<not>A)" using Cl_fr_def IF2 dEXP_def conn by auto
lemma Q_def2: "Fr_1b \<F> \<Longrightarrow> \<forall>A. Q \<^bold>\<approx> \<^bold>\<not>(A \<^bold>\<or> \<^bold>\<not>A)" by (smt Cl_fr_def IF2 dEXP_def MONO_def monI conn)
lemma neg_Idef: "\<forall>A. \<^bold>\<not>A \<^bold>\<approx> \<I>(\<^bold>\<midarrow>A) \<^bold>\<or> Q" by (simp add: Cl_fr_def)
lemma neg_Cdef: "Fr_2 \<F> \<Longrightarrow> \<forall>A. \<^bold>\<not>A \<^bold>\<approx> \<C>(A) \<^bold>\<rightarrow> Q" using Cl_fr_def Fr_2_def Int_fr_def conn by auto

text\<open>\noindent{The negation so defined validates some properties corresponding to a (rather weak) paracomplete logic:}\<close>
lemma "\<FF> \<F> \<Longrightarrow> TND \<^bold>\<not>" nitpick oops (*counterexample found: negation is paracomplete*)
lemma "\<FF> \<F> \<Longrightarrow> TNDw \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> TNDm \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> ECQ \<^bold>\<not>" nitpick oops (*counterexample found: negation is paraconsistent...*)
lemma ECQw: "ECQw \<^bold>\<not>" using Cl_fr_def Disj_I ECQw_def unfolding conn by auto (*...but not 'boldly' paraconsistent*) 
lemma ECQm: "ECQm \<^bold>\<not>" using Cl_fr_def Disj_I ECQm_def unfolding conn by auto 
lemma "\<FF> \<F> \<Longrightarrow> LNC \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DNI \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DNE \<^bold>\<not>"  nitpick oops
lemma CoPw: "Fr_1b \<F> \<Longrightarrow> CoPw \<^bold>\<not>" using Cl_fr_def MONO_def monI unfolding Defs conn by smt
lemma "\<FF> \<F> \<Longrightarrow> CoP1 \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> CoP2 \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> CoP3 \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> XCoP \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DM3 \<^bold>\<not>" nitpick oops
lemma DM4: "Fr_1a \<F> \<Longrightarrow> DM4 \<^bold>\<not>" using ADDI_a_def Cl_fr_def DM4_def IC1b IF1b dual_def unfolding conn by smt
lemma Nor: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> nNor \<^bold>\<not>" using Cl_fr_def nNor_I nNor_def unfolding conn by auto
lemma "\<FF> \<F> \<Longrightarrow> nDNor \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops

text\<open>\noindent{Moreover, we cannot have both DNI and DNE without validating ECQ (thus losing paraconsistency).}\<close>
lemma "DNI \<^bold>\<not> \<and> DNE \<^bold>\<not> \<longrightarrow> ECQ \<^bold>\<not>" using DNE_def ECQ_def Int_fr_def neg_Idef unfolding conn by (metis (no_types, lifting))
text\<open>\noindent{However, we can have all of De Morgan laws while keeping (non-bold) paraconsistency.}\<close>
lemma "\<sim>ECQ \<^bold>\<not> \<and> DM1 \<^bold>\<not> \<and> DM2 \<^bold>\<not> \<and> DM3 \<^bold>\<not> \<and> DM4 \<^bold>\<not> \<and> \<FF> \<F>" nitpick[satisfy,card w=3] oops (*(weakly paraconsistent) model found*)

text\<open>\noindent{Below we combine negation with strict implication and verify some interesting properties.
For instance, the following are not valid (and cannot become valid by adding semantic restrictions). }\<close>
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (\<^bold>\<not>a \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> b)) \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*counterexample found*)
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (\<^bold>\<not>a \<^bold>\<rightarrow> (a \<^bold>\<rightarrow> b)) \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<and> \<^bold>\<not>a \<^bold>\<Rightarrow> b) \<^bold>\<approx> \<^bold>\<top>"  nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<and> \<^bold>\<not>a \<^bold>\<rightarrow> b) \<^bold>\<approx> \<^bold>\<top>"  nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> (b \<^bold>\<or> \<^bold>\<not>b)) \<^bold>\<approx> \<^bold>\<top>"  nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<rightarrow> (b \<^bold>\<or> \<^bold>\<not>b)) \<^bold>\<approx> \<^bold>\<top>"  nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. (a \<^bold>\<Rightarrow> \<^bold>\<not>a) \<^bold>\<Rightarrow> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. (a \<^bold>\<rightarrow> \<^bold>\<not>a) \<^bold>\<rightarrow> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<and> \<^bold>\<not>a) \<^bold>\<Rightarrow> b \<^bold>\<approx> \<^bold>\<top>" nitpick oops 
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<and> \<^bold>\<not>a) \<^bold>\<rightarrow> b \<^bold>\<approx> \<^bold>\<top>" nitpick oops 
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. a \<^bold>\<Rightarrow> (b \<^bold>\<or> \<^bold>\<not>b) \<^bold>\<approx> \<^bold>\<top>" nitpick oops 
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. a \<^bold>\<rightarrow> (b \<^bold>\<or> \<^bold>\<not>b) \<^bold>\<approx> \<^bold>\<top>" nitpick oops 
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<leftrightarrow> b) \<^bold>\<Rightarrow> (\<^bold>\<not>a \<^bold>\<leftrightarrow> \<^bold>\<not>b) \<^bold>\<approx> \<^bold>\<top>" nitpick oops 
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<leftrightarrow> b) \<^bold>\<rightarrow> (\<^bold>\<not>a \<^bold>\<leftrightarrow> \<^bold>\<not>b) \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> b) \<^bold>\<and> (a \<^bold>\<Rightarrow> \<^bold>\<not>b) \<^bold>\<Rightarrow> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<rightarrow> b) \<^bold>\<and> (a \<^bold>\<rightarrow> \<^bold>\<not>b) \<^bold>\<Rightarrow> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. (\<^bold>\<not>a  \<^bold>\<Rightarrow>  \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<top>" nitpick oops 
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. (\<^bold>\<not>a  \<^bold>\<rightarrow>  \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<top>" nitpick oops 
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. (\<^bold>\<not>a \<^bold>\<Rightarrow> \<^bold>\<not>(\<^bold>\<not>\<^bold>\<top>)) \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. (\<^bold>\<not>a \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<not>\<^bold>\<top>)) \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. \<^bold>\<not>(\<^bold>\<not>(\<^bold>\<not>a)) \<^bold>\<Rightarrow> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a. \<^bold>\<not>(\<^bold>\<not>(\<^bold>\<not>a)) \<^bold>\<rightarrow> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" nitpick oops

text\<open>\noindent{The (weak) local contraposition axiom is indeed valid under appropriate conditions.}\<close>
lemma lCoPw: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> lCoPw(\<^bold>\<Rightarrow>) \<^bold>\<not>" proof -
  assume fr1: "Fr_1 \<F>" and fr2: "Fr_2 \<F>" and fr3: "Fr_3 \<F>" and fr4: "Fr_4 \<F>"
  { fix a b
    from fr2 have "\<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a \<^bold>\<approx> (\<C> a \<^bold>\<rightarrow> \<C> b) \<^bold>\<or> Q" using Cl_fr_def Fr_2_def Int_fr_def conn by auto
    moreover from fr1 fr2 fr3 have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<preceq> \<C> a \<^bold>\<rightarrow> \<C> b" using IC_imp by simp
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<preceq> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a" unfolding conn by simp   
    moreover from fr1 fr2 fr4 have "let A=(a \<^bold>\<rightarrow> b); B=(\<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a) in \<I> A \<^bold>\<preceq> B \<longrightarrow> \<I> A \<^bold>\<preceq> \<I> B"
      using PF1 MONO_MULTa IF1a IF4 PI9 Int_9_def by smt
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<preceq> \<I>(\<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a)" by simp
  } hence "lCoPw(\<^bold>\<Rightarrow>) \<^bold>\<not>" unfolding Defs conn by blast
  thus ?thesis by simp
qed
lemma lCoPw_strict: "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> (\<^bold>\<not>b \<^bold>\<Rightarrow> \<^bold>\<not>a) \<^bold>\<approx> \<^bold>\<top>" by (metis (no_types, lifting) DTw2 lCoPw lCoPw_def)

text\<open>\noindent{However, other (local) contraposition axioms are not valid.}\<close>
lemma "\<FF> \<F> \<Longrightarrow> lCoP1(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops (*counterexample found*)
lemma "\<FF> \<F> \<Longrightarrow> lCoP2(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> lCoP3(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
text\<open>\noindent{And this time no variant of disjunctive syllogism is valid.}\<close>
lemma "\<FF> \<F> \<Longrightarrow> DS1(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DS2(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DS2(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "\<FF> \<F> \<Longrightarrow> DS4(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops

text\<open>\noindent{Interestingly, one of the local contraposition axioms (lCoP1) follows from DNI.}\<close>
lemma DNI_lCoP1: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> DNI \<^bold>\<not> \<longrightarrow> lCoP1(\<^bold>\<Rightarrow>) \<^bold>\<not>" proof -
  assume fr1: "Fr_1 \<F>" and fr2: "Fr_2 \<F>" and fr3: "Fr_3 \<F>" and fr4: "Fr_4 \<F>"
  { assume dni: "DNI \<^bold>\<not>"
    { fix a b
      from fr1 fr2 fr3 fr4 have "lCoPw(\<^bold>\<Rightarrow>) \<^bold>\<not>"  using lCoPw by simp
      hence 1: "a \<^bold>\<Rightarrow> \<^bold>\<not>b \<^bold>\<preceq> \<^bold>\<not>(\<^bold>\<not>b) \<^bold>\<Rightarrow> \<^bold>\<not>a" unfolding lCoPw_def by simp
      from fr1 have 2: "let A=b; B=\<^bold>\<not>(\<^bold>\<not>b); C=\<^bold>\<not>a in A \<^bold>\<preceq> B \<longrightarrow>  \<I>(B \<^bold>\<rightarrow> C) \<^bold>\<preceq> \<I>(A \<^bold>\<rightarrow> C)" by (simp add: MONO_ant PF1 monI)
      from dni have dnib: "b \<^bold>\<preceq> \<^bold>\<not>(\<^bold>\<not>b)" unfolding DNI_def by simp
      from 1 2 dnib have "a \<^bold>\<Rightarrow> \<^bold>\<not>b \<^bold>\<preceq> b \<^bold>\<Rightarrow> \<^bold>\<not>a" unfolding conn by meson
    } hence "lCoP1(\<^bold>\<Rightarrow>) \<^bold>\<not>" unfolding Defs by blast
  } thus ?thesis by simp
qed
text\<open>\noindent{This entails some other interesting results.}\<close>
lemma DNI_CoP1: "Fr_1b \<F> \<Longrightarrow> DNI \<^bold>\<not> \<Longrightarrow> CoP1 \<^bold>\<not>" using CoP1_def2 CoPw by blast
lemma CoP1_LNC: "CoP1 \<^bold>\<not> \<Longrightarrow> LNC \<^bold>\<not>" using CoP1_def ECQm_def LNC_def  Cl_fr_def Disj_I ECQm_def unfolding conn by smt
lemma DNI_LNC: "Fr_1b \<F> \<Longrightarrow> DNI \<^bold>\<not> \<Longrightarrow> LNC \<^bold>\<not>" by (simp add: CoP1_LNC DNI_CoP1)

text\<open>\noindent{The following variants of modus tollens also obtain.}\<close>
lemma MT: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> b) \<^bold>\<and> \<^bold>\<not>b \<^bold>\<preceq> \<^bold>\<not>a" using Cl_fr_def Fr_2_def IC_imp Int_fr_def unfolding conn by metis
lemma MT': "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> \<^bold>\<not>b) \<^bold>\<Rightarrow> \<^bold>\<not>a \<^bold>\<approx> \<^bold>\<top>" by (simp add: DTw2 MT)

text\<open>\noindent{We now semantically characterize (an approximation of) Johansson's Minimal Logic along with some 
exemplary 'subminimal' logics (observing that many more are possible). We check some relevant properties.}\<close>
abbreviation "JML \<equiv> \<FF> \<F> \<and> DNI \<^bold>\<not>"
abbreviation "SML1 \<equiv> \<FF> \<F>" (*Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F>*)
abbreviation "SML2 \<equiv> Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F>"
abbreviation "SML3 \<equiv> Fr_1 \<F>"
abbreviation "SML4 \<equiv> Fr_1b \<F>"

text\<open>\noindent{TND:}\<close>
lemma "JML \<Longrightarrow> TND \<^bold>\<not>" nitpick oops (*counterexample found*)
lemma "JML \<Longrightarrow> TNDw \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> TNDm \<^bold>\<not>" nitpick oops

text\<open>\noindent{ECQ:}\<close>
lemma "JML \<Longrightarrow> ECQ \<^bold>\<not>" nitpick oops
lemma "ECQw \<^bold>\<not>" using Cl_fr_def Disj_I ECQw_def unfolding conn by auto  
lemma "ECQm \<^bold>\<not>" using Cl_fr_def Disj_I ECQm_def unfolding conn by auto

text\<open>\noindent{LNC:}\<close>
lemma "JML \<Longrightarrow> LNC \<^bold>\<not>" using DNI_LNC PF1 by blast
lemma "SML1 \<Longrightarrow> LNC \<^bold>\<not>" nitpick oops

text\<open>\noindent{(r)DNI/DNE:}\<close>
lemma "JML \<Longrightarrow> DNI \<^bold>\<not>" using CoP1_def2 by blast
lemma "SML1 \<Longrightarrow> rDNI \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> rDNE \<^bold>\<not>"  nitpick oops

text\<open>\noindent{CoP/MT:}\<close>
lemma "SML4 \<Longrightarrow> CoPw \<^bold>\<not>" unfolding Defs by (smt Cl_fr_def MONO_def monI conn)
lemma "JML \<Longrightarrow> CoP1 \<^bold>\<not>" using DNI_CoP1 PF1 by blast
lemma "SML1 \<Longrightarrow> MT1 \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> MT2 \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> MT3 \<^bold>\<not>" nitpick oops

text\<open>\noindent{XCoP:}\<close>
lemma "JML \<Longrightarrow> XCoP \<^bold>\<not>" nitpick oops

text\<open>\noindent{DM3/4:}\<close>
lemma "JML \<Longrightarrow> DM3 \<^bold>\<not>" nitpick oops
lemma "SML3 \<Longrightarrow> DM4 \<^bold>\<not>" by (simp add: DM4 PF1)
lemma "SML4 \<Longrightarrow> DM4 \<^bold>\<not>" nitpick oops

text\<open>\noindent{nNor/nDNor:}\<close>
lemma "SML2 \<Longrightarrow> nNor \<^bold>\<not>" using Cl_fr_def nNor_I nNor_def unfolding conn by auto
lemma "SML3 \<Longrightarrow> nNor \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> nDNor \<^bold>\<not>" nitpick oops

text\<open>\noindent{lCoP classical:}\<close>
lemma "JML \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops

text\<open>\noindent{DS classical:}\<close>
lemma "JML \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<^bold>\<not>" nitpick oops

text\<open>\noindent{lCoP strict:}\<close>
lemma "SML1 \<Longrightarrow> lCoPw(\<^bold>\<Rightarrow>) \<^bold>\<not>" using lCoPw by blast
lemma "SML2 \<Longrightarrow> lCoPw(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lCoP1(\<^bold>\<Rightarrow>) \<^bold>\<not>" using CoP1_def2 DNI_lCoP1 by blast
lemma "SML1 \<Longrightarrow> lCoP1(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lCoP2(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lCoP3(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops

text\<open>\noindent{lMT strict:}\<close>
lemma "SML2 \<Longrightarrow> lMT0(\<^bold>\<Rightarrow>) \<^bold>\<not>" unfolding Defs using MT by auto
lemma "SML3 \<Longrightarrow> lMT0(\<^bold>\<Rightarrow>) \<^bold>\<not>"  (*nitpick*) oops (*no countermodel found*)
lemma "SML4 \<Longrightarrow> lMT0(\<^bold>\<Rightarrow>) \<^bold>\<not>"  nitpick oops
lemma "JML \<Longrightarrow> lMT1(\<^bold>\<Rightarrow>) \<^bold>\<not>"  by (smt DNI_lCoP1 DT1 lCoP1_def lMT1_def)
lemma "SML1 \<Longrightarrow> lMT1(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lMT2(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> lMT3(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops

text\<open>\noindent{DS strict:}\<close>
lemma "JML \<Longrightarrow> DS1(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> DS2(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> DS3(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops
lemma "JML \<Longrightarrow> DS4(\<^bold>\<Rightarrow>) \<^bold>\<not>" nitpick oops

end
