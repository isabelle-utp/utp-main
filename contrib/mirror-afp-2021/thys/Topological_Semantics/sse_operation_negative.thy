theory sse_operation_negative
  imports sse_boolean_algebra
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Negative semantic conditions for operations\<close>

text\<open>\noindent{We define and interrelate some conditions on operations (i.e. propositional functions of type
@{text "\<sigma>\<Rightarrow>\<sigma>"}), this time involving negative-like properties.}\<close>

named_theorems Defs

subsection \<open>Definitions and interrelations (finitary case)\<close>

subsubsection \<open>Principles of excluded middle, contradiction and explosion\<close>

text\<open>\noindent{TND: tertium non datur, aka. law of excluded middle (resp. strong, weak, minimal).}\<close>
abbreviation pTND  ("TND\<^sup>_  _") where "TND\<^sup>a  \<eta> \<equiv>       \<^bold>\<top>  \<^bold>\<approx> a \<^bold>\<or> (\<eta> a)"
abbreviation pTNDw ("TNDw\<^sup>_ _") where "TNDw\<^sup>a \<eta> \<equiv> \<forall>b. (\<eta> b) \<^bold>\<preceq> a \<^bold>\<or> (\<eta> a)"
abbreviation pTNDm ("TNDm\<^sup>_ _") where "TNDm\<^sup>a \<eta> \<equiv>     (\<eta> \<^bold>\<bottom>) \<^bold>\<preceq> a \<^bold>\<or> (\<eta> a)"
definition "TND  \<eta> \<equiv> \<forall>\<phi>. TND\<^sup>\<phi>  \<eta>"
definition "TNDw \<eta> \<equiv> \<forall>\<phi>. TNDw\<^sup>\<phi> \<eta>"
definition "TNDm \<eta> \<equiv> \<forall>\<phi>. TNDm\<^sup>\<phi> \<eta>"
declare TND_def[Defs] TNDw_def[Defs] TNDm_def[Defs]

text\<open>\noindent{Explore some (non)entailment relations:}\<close>
lemma "TND  \<eta> \<Longrightarrow> TNDw \<eta>" unfolding Defs conn by simp
lemma "TNDw \<eta> \<Longrightarrow> TND  \<eta>" nitpick oops
lemma "TNDw \<eta> \<Longrightarrow> TNDm \<eta>" unfolding Defs by simp
lemma "TNDm \<eta> \<Longrightarrow> TNDw \<eta>" nitpick oops

text\<open>\noindent{ECQ: ex contradictione (sequitur) quodlibet (resp: strong, weak, minimal).}\<close>
abbreviation pECQ  ("ECQ\<^sup>_ _")  where "ECQ\<^sup>a  \<eta> \<equiv>     a \<^bold>\<and> (\<eta> a) \<^bold>\<approx> \<^bold>\<bottom>"
abbreviation pECQw ("ECQw\<^sup>_ _") where "ECQw\<^sup>a \<eta> \<equiv> \<forall>b. a \<^bold>\<and> (\<eta> a) \<^bold>\<preceq> (\<eta> b)"
abbreviation pECQm ("ECQm\<^sup>_ _") where "ECQm\<^sup>a \<eta> \<equiv>     a \<^bold>\<and> (\<eta> a) \<^bold>\<preceq> (\<eta> \<^bold>\<top>)"
definition "ECQ  \<eta> \<equiv> \<forall>a. ECQ\<^sup>a  \<eta>"
definition "ECQw \<eta> \<equiv> \<forall>a. ECQw\<^sup>a \<eta>"
definition "ECQm \<eta> \<equiv> \<forall>a. ECQm\<^sup>a \<eta>"
declare ECQ_def[Defs] ECQw_def[Defs] ECQm_def[Defs]

text\<open>\noindent{Explore some (non)entailment relations:}\<close>
lemma "ECQ  \<eta> \<Longrightarrow> ECQw \<eta>" unfolding Defs conn by blast
lemma "ECQw \<eta> \<Longrightarrow> ECQ  \<eta>" nitpick oops
lemma "ECQw \<eta> \<Longrightarrow> ECQm \<eta>" unfolding Defs conn by simp
lemma "ECQm \<eta> \<Longrightarrow> ECQw \<eta>" nitpick oops

text\<open>\noindent{LNC: law of non-contradiction.}\<close>
abbreviation pLNC  ("LNC\<^sup>_ _")  where "LNC\<^sup>a \<eta> \<equiv> \<eta>(a \<^bold>\<and> \<eta> a) \<^bold>\<approx> \<^bold>\<top>"
definition "LNC \<eta> \<equiv> \<forall>a. LNC\<^sup>a \<eta>"
declare LNC_def[Defs]

text\<open>\noindent{ECQ and LNC are in general independent.}\<close>
lemma "ECQ \<eta> \<Longrightarrow> LNC \<eta>" nitpick oops
lemma "LNC \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops


subsubsection \<open>Contraposition rules\<close>

text\<open>\noindent{CoP: contraposition (global/rule variants, resp. weak, strong var. 1, strong var. 2, strong var. 3).}\<close>
abbreviation pCoPw ("CoPw\<^sup>_\<^sup>_ _") where "CoPw\<^sup>a\<^sup>b \<eta> \<equiv> a \<^bold>\<preceq> b \<longrightarrow> (\<eta> b) \<^bold>\<preceq> (\<eta> a)"
abbreviation pCoP1 ("CoP1\<^sup>_\<^sup>_ _") where "CoP1\<^sup>a\<^sup>b \<eta> \<equiv> a \<^bold>\<preceq> (\<eta> b) \<longrightarrow> b \<^bold>\<preceq> (\<eta> a)"
abbreviation pCoP2 ("CoP2\<^sup>_\<^sup>_ _") where "CoP2\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<preceq> b \<longrightarrow> (\<eta> b) \<^bold>\<preceq> a"
abbreviation pCoP3 ("CoP3\<^sup>_\<^sup>_ _") where "CoP3\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<preceq> (\<eta> b) \<longrightarrow> b \<^bold>\<preceq> a"
definition "CoPw  \<eta> \<equiv> \<forall>a b. CoPw\<^sup>a\<^sup>b \<eta>"
definition "CoP1  \<eta> \<equiv> \<forall>a b. CoP1\<^sup>a\<^sup>b \<eta>"
definition "CoP1' \<eta> \<equiv> \<forall>a b. a \<^bold>\<preceq> (\<eta> b) \<longleftrightarrow> b \<^bold>\<preceq> (\<eta> a)"
definition "CoP2  \<eta> \<equiv> \<forall>a b. CoP2\<^sup>a\<^sup>b \<eta>"
definition "CoP2' \<eta> \<equiv> \<forall>a b. (\<eta> a) \<^bold>\<preceq> b \<longleftrightarrow> (\<eta> b) \<^bold>\<preceq> a"
definition "CoP3  \<eta> \<equiv> \<forall>a b. CoP3\<^sup>a\<^sup>b \<eta>"
declare CoPw_def[Defs] CoP1_def[Defs] CoP1'_def[Defs]
        CoP2_def[Defs] CoP2'_def[Defs] CoP3_def[Defs]

lemma CoP1_defs_rel: "CoP1 \<eta> = CoP1' \<eta>" unfolding Defs by metis
lemma CoP2_defs_rel: "CoP2 \<eta> = CoP2' \<eta>" unfolding Defs by metis

text\<open>\noindent{Explore some (non)entailment relations:}\<close>
lemma "CoP1 \<eta> \<Longrightarrow> CoPw \<eta>" unfolding Defs by metis
lemma "CoPw \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops
lemma "CoP2 \<eta> \<Longrightarrow> CoPw \<eta>" unfolding Defs by metis
lemma "CoPw \<eta> \<Longrightarrow> CoP2 \<eta>" nitpick oops
lemma "CoP3 \<eta> \<Longrightarrow> CoPw \<eta>" (*nitpick*) oops \<comment>\<open> no countermodel found so far \<close>
lemma "CoPw \<eta> \<Longrightarrow> CoP3 \<eta>" nitpick oops

text\<open>\noindent{All three strong variants are pairwise independent. However, CoP3 follows from CoP1 plus CoP2.}\<close>
lemma CoP123: "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> CoP3 \<eta>" unfolding Defs by smt
text\<open>\noindent{Taking all CoP together still leaves room for a boldly paraconsistent resp. paracomplete logic.}\<close>
lemma "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops 
lemma "CoP1 \<eta> \<Longrightarrow> CoP2 \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops 


subsubsection \<open>Modus tollens rules\<close>

text\<open>\noindent{MT: modus (tollendo) tollens (global/rule variants).}\<close>
abbreviation pMT0 ("MT0\<^sup>_\<^sup>_ _") where "MT0\<^sup>a\<^sup>b \<eta> \<equiv> a \<^bold>\<preceq> b \<and> (\<eta> b) \<^bold>\<approx> \<^bold>\<top> \<longrightarrow> (\<eta> a) \<^bold>\<approx> \<^bold>\<top>"
abbreviation pMT1 ("MT1\<^sup>_\<^sup>_ _") where "MT1\<^sup>a\<^sup>b \<eta> \<equiv> a \<^bold>\<preceq> (\<eta> b) \<and> b \<^bold>\<approx> \<^bold>\<top> \<longrightarrow> (\<eta> a) \<^bold>\<approx> \<^bold>\<top>"
abbreviation pMT2 ("MT2\<^sup>_\<^sup>_ _") where "MT2\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<preceq> b \<and> (\<eta> b) \<^bold>\<approx> \<^bold>\<top> \<longrightarrow> a \<^bold>\<approx> \<^bold>\<top>"
abbreviation pMT3 ("MT3\<^sup>_\<^sup>_ _") where "MT3\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<preceq> (\<eta> b) \<and> b \<^bold>\<approx> \<^bold>\<top> \<longrightarrow> a \<^bold>\<approx> \<^bold>\<top>"
definition "MT0 \<eta> \<equiv> \<forall>a b. MT0\<^sup>a\<^sup>b \<eta>"
definition "MT1 \<eta> \<equiv> \<forall>a b. MT1\<^sup>a\<^sup>b \<eta>"
definition "MT2 \<eta> \<equiv> \<forall>a b. MT2\<^sup>a\<^sup>b \<eta>"
definition "MT3 \<eta> \<equiv> \<forall>a b. MT3\<^sup>a\<^sup>b \<eta>"
declare MT0_def[Defs] MT1_def[Defs] MT2_def[Defs] MT3_def[Defs]

text\<open>\noindent{Again, all MT variants are pairwise independent. We explore some (non)entailment relations:}\<close>
lemma "CoPw \<eta> \<Longrightarrow> MT0 \<eta>" unfolding Defs by (metis top_def)
lemma "CoP1 \<eta> \<Longrightarrow> MT1 \<eta>" unfolding Defs by (metis top_def)
lemma "CoP2 \<eta> \<Longrightarrow> MT2 \<eta>" unfolding Defs by (metis top_def)
lemma "CoP3 \<eta> \<Longrightarrow> MT3 \<eta>" unfolding Defs by (metis top_def)
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> CoPw \<eta>" nitpick oops
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops
lemma "MT0 \<eta> \<Longrightarrow> MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops
lemma MT123: "MT1 \<eta> \<Longrightarrow> MT2 \<eta> \<Longrightarrow> MT3 \<eta>"  unfolding Defs by smt


subsubsection \<open>Double negation introduction and elimination\<close>

text\<open>\noindent{DNI/DNE: double negation introduction/elimination (as axioms).}\<close>
abbreviation pDNI ("DNI\<^sup>_ _") where "DNI\<^sup>a \<eta> \<equiv> a \<^bold>\<preceq> \<eta> (\<eta> a)"
abbreviation pDNE ("DNE\<^sup>_ _") where "DNE\<^sup>a \<eta> \<equiv> \<eta> (\<eta> a) \<^bold>\<preceq> a"
definition "DNI \<eta> \<equiv> \<forall>a. DNI\<^sup>a \<eta>"
definition "DNE \<eta> \<equiv> \<forall>a. DNE\<^sup>a \<eta>"
declare DNI_def[Defs] DNE_def[Defs]

text\<open>\noindent{CoP1 (resp. CoP2) can alternatively be defined as CoPw plus DNI (resp. DNE).}\<close>
lemma "DNI \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops
lemma CoP1_def2: "CoP1 \<eta> = (CoPw \<eta> \<and> DNI \<eta>)" unfolding Defs by smt
lemma "DNE \<eta> \<Longrightarrow>  CoP2 \<eta>" nitpick oops
lemma CoP2_def2: "CoP2 \<eta> = (CoPw \<eta> \<and> DNE \<eta>)" unfolding Defs by smt

text\<open>\noindent{Explore some non-entailment relations:}\<close>
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> CoPw \<eta>" nitpick oops 
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops 
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops 
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT0 \<eta>" nitpick oops
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT1 \<eta>" nitpick oops
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT2 \<eta>" nitpick oops
lemma "DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> MT3 \<eta>" nitpick oops

text\<open>\noindent{DNI/DNE: double negation introduction/elimination (as rules).}\<close>
abbreviation prDNI ("rDNI\<^sup>_ _") where "rDNI\<^sup>a \<eta> \<equiv> a \<^bold>\<approx> \<^bold>\<top> \<longrightarrow> \<eta> (\<eta> a) \<^bold>\<approx> \<^bold>\<top>"
abbreviation prDNE ("rDNE\<^sup>_ _") where "rDNE\<^sup>a \<eta> \<equiv> \<eta> (\<eta> a) \<^bold>\<approx> \<^bold>\<top> \<longrightarrow> a \<^bold>\<approx> \<^bold>\<top>"
definition "rDNI \<eta> \<equiv> \<forall>a. rDNI\<^sup>a \<eta>"
definition "rDNE \<eta> \<equiv> \<forall>a. rDNE\<^sup>a \<eta>"
declare rDNI_def[Defs] rDNE_def[Defs]

text\<open>\noindent{The rule variants are strictly weaker than the axiom variants,}\<close>
lemma "DNI \<eta> \<Longrightarrow> rDNI \<eta>" by (simp add: DNI_def rDNI_def top_def) 
lemma "rDNI \<eta> \<Longrightarrow> DNI \<eta>" nitpick oops
lemma "DNE \<eta> \<Longrightarrow> rDNE \<eta>" by (metis DNE_def rDNE_def top_def) 
lemma "rDNE \<eta> \<Longrightarrow> DNE \<eta>" nitpick oops
text\<open>\noindent{and follow already from modus tollens.}\<close>
lemma MT1_rDNI: "MT1 \<eta> \<Longrightarrow> rDNI \<eta>" unfolding Defs by blast
lemma MT2_rDNE: "MT2 \<eta> \<Longrightarrow> rDNE \<eta>" unfolding Defs by blast


subsubsection \<open>Normality and its dual\<close>

text\<open>\noindent{n(D)Nor: negative (dual) 'normality'.}\<close>
definition "nNor \<eta> \<equiv> (\<eta> \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<top>"
definition "nDNor \<eta> \<equiv> (\<eta> \<^bold>\<top>) \<^bold>\<approx> \<^bold>\<bottom>"
declare nNor_def[Defs] nDNor_def[Defs]

text\<open>\noindent{nNor (resp. nDNor) is entailed by CoP1 (resp. CoP2). }\<close>
lemma CoP1_Nor: "CoP1 \<eta> \<Longrightarrow> nNor \<eta>" unfolding Defs conn by simp
lemma CoP2_DNor: "CoP2 \<eta> \<Longrightarrow> nDNor \<eta>" unfolding Defs conn by fastforce
lemma "DNI \<eta> \<Longrightarrow> nNor \<eta>" nitpick oops 
lemma "DNE \<eta> \<Longrightarrow> nDNor \<eta>" nitpick oops 
text\<open>\noindent{nNor and nDNor together entail the rule variant of DNI (rDNI).}\<close>
lemma nDNor_rDNI: "nNor \<eta> \<Longrightarrow> nDNor \<eta> \<Longrightarrow> rDNI \<eta>" unfolding Defs using nDNor_def nNor_def eq_ext by metis
lemma "nNor \<eta> \<Longrightarrow> nDNor \<eta> \<Longrightarrow> rDNE \<eta>" nitpick oops


subsubsection \<open>De Morgan laws\<close>

text\<open>\noindent{DM: De Morgan laws.}\<close>
abbreviation pDM1 ("DM1\<^sup>_\<^sup>_ _") where "DM1\<^sup>a\<^sup>b \<eta> \<equiv> \<eta>(a \<^bold>\<or> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<and> (\<eta> b)"
abbreviation pDM2 ("DM2\<^sup>_\<^sup>_ _") where "DM2\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<or> (\<eta> b) \<^bold>\<preceq> \<eta>(a \<^bold>\<and> b)"
abbreviation pDM3 ("DM3\<^sup>_\<^sup>_ _") where "DM3\<^sup>a\<^sup>b \<eta> \<equiv> \<eta>(a \<^bold>\<and> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<or> (\<eta> b)"
abbreviation pDM4 ("DM4\<^sup>_\<^sup>_ _") where "DM4\<^sup>a\<^sup>b \<eta> \<equiv> (\<eta> a) \<^bold>\<and> (\<eta> b) \<^bold>\<preceq>  \<eta>(a \<^bold>\<or> b)"
definition "DM1 \<eta> \<equiv> \<forall>a b. DM1\<^sup>a\<^sup>b \<eta>"
definition "DM2 \<eta> \<equiv> \<forall>a b. DM2\<^sup>a\<^sup>b \<eta>"
definition "DM3 \<eta> \<equiv> \<forall>a b. DM3\<^sup>a\<^sup>b \<eta>"
definition "DM4 \<eta> \<equiv> \<forall>a b. DM4\<^sup>a\<^sup>b \<eta>"
declare DM1_def[Defs] DM2_def[Defs] DM3_def[Defs] DM4_def[Defs]

text\<open>\noindent{CoPw, DM1 and DM2 are indeed equivalent.}\<close>
lemma DM1_CoPw: "DM1 \<eta> = CoPw \<eta>" proof -
  have LtoR: "DM1 \<eta> \<Longrightarrow> CoPw \<eta>" proof -
  assume dm1: "DM1 \<eta>"
  { fix a b
    { assume "a \<^bold>\<preceq> b"
      hence 1: "a \<^bold>\<or> b \<^bold>\<preceq> b" unfolding conn by simp
      have 2: "b \<^bold>\<preceq> a \<^bold>\<or> b" unfolding conn by simp
      from 1 2 have "b = a \<^bold>\<or> b" using eq_ext by blast
      hence 3: "\<eta> b \<^bold>\<approx> \<eta> (a \<^bold>\<or> b)" by auto
      from dm1 have "\<eta>(a \<^bold>\<or> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<and> (\<eta> b)" unfolding Defs by blast
      hence 4: "(\<eta> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<and> (\<eta> b)" using 3 by simp
      have 5: "(\<eta> a) \<^bold>\<and> (\<eta> b) \<^bold>\<preceq> (\<eta> a)" unfolding conn by simp
      from 4 5 have "(\<eta> b) \<^bold>\<preceq> (\<eta> a)" by simp
    } hence "a \<^bold>\<preceq> b \<longrightarrow> (\<eta> b) \<^bold>\<preceq> (\<eta> a)" by (rule impI)
  } thus ?thesis unfolding Defs by simp
  qed
  have RtoL: "CoPw \<eta> \<Longrightarrow> DM1 \<eta>" unfolding Defs conn by (metis (no_types, lifting))
  thus ?thesis using LtoR RtoL by blast  
qed
lemma DM2_CoPw: "DM2 \<eta> = CoPw \<eta>" proof -
 have LtoR: "DM2 \<eta> \<Longrightarrow> CoPw \<eta>" proof -
   assume dm2: "DM2 \<eta>"
    { fix a b
      { assume "a \<^bold>\<preceq> b"
        hence 1: "a \<^bold>\<preceq> a \<^bold>\<and> b" unfolding conn by simp
        have 2: "a \<^bold>\<and> b \<^bold>\<preceq> a" unfolding conn by simp
        from 1 2 have "a = a \<^bold>\<and> b" using eq_ext by blast
        hence 3: "\<eta> a \<^bold>\<approx> \<eta> (a \<^bold>\<and> b)" by auto
        from dm2 have "(\<eta> a) \<^bold>\<or> (\<eta> b) \<^bold>\<preceq> \<eta>(a \<^bold>\<and> b)" unfolding Defs by blast
        hence 4: "(\<eta> a) \<^bold>\<or> (\<eta> b) \<^bold>\<preceq> (\<eta> a) " using 3 by simp
        have 5: "(\<eta> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<or> (\<eta> b)" unfolding conn by simp
        from 4 5 have "(\<eta> b) \<^bold>\<preceq> (\<eta> a)" by simp
      } hence "a \<^bold>\<preceq> b \<longrightarrow> (\<eta> b) \<^bold>\<preceq> (\<eta> a)" by (rule impI)
    } thus ?thesis unfolding Defs by simp
  qed
  have RtoL: "CoPw \<eta> \<Longrightarrow> DM2 \<eta>" unfolding Defs conn by (metis (no_types, lifting))
  thus ?thesis using LtoR RtoL by blast
qed
lemma DM12: "DM1 \<eta> = DM2 \<eta>" by (simp add: DM1_CoPw DM2_CoPw)

text\<open>\noindent{DM3 (resp. DM4) are entailed by CoPw together with DNE (resp. DNI).}\<close>
lemma CoPw_DNE_DM3: "CoPw \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> DM3 \<eta>" proof -
  assume copw: "CoPw \<eta>" and dne: "DNE \<eta>"
  { fix a b
    have "\<eta>(a) \<^bold>\<preceq> (\<eta> a) \<^bold>\<or> (\<eta> b)" unfolding conn by simp
    hence "\<eta>(\<eta>(a) \<^bold>\<or> \<eta>(b)) \<^bold>\<preceq> \<eta>((\<eta> a))" using CoPw_def copw by (metis (no_types, lifting))
    hence 1: "\<eta>(\<eta>(a) \<^bold>\<or> \<eta>(b)) \<^bold>\<preceq> a" using DNE_def dne by metis
    have "\<eta>(b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<or> (\<eta> b)" unfolding conn by simp
    hence "\<eta>(\<eta>(a) \<^bold>\<or> \<eta>(b)) \<^bold>\<preceq> \<eta>((\<eta> b))" using CoPw_def copw by (metis (no_types, lifting))
    hence 2: "\<eta>(\<eta>(a) \<^bold>\<or> \<eta>(b)) \<^bold>\<preceq> b" using DNE_def dne by metis
    from 1 2 have "\<eta>(\<eta>(a) \<^bold>\<or> \<eta>(b)) \<^bold>\<preceq> a \<^bold>\<and> b" unfolding conn by simp
    hence "\<eta>(a \<^bold>\<and> b) \<^bold>\<preceq> \<eta>(\<eta>(\<eta>(a) \<^bold>\<or> \<eta>(b)))" using CoPw_def copw by smt
    hence "\<eta>(a \<^bold>\<and> b) \<^bold>\<preceq> (\<eta> a) \<^bold>\<or> (\<eta> b)" using DNE_def dne by metis
  } thus ?thesis by (simp add: DM3_def)
qed
lemma CoPw_DNI_DM4: "CoPw \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> DM4 \<eta>" proof -
  assume copw: "CoPw \<eta>" and dni: "DNI \<eta>"
  { fix a b
    have "(\<eta> a) \<^bold>\<and> (\<eta> b) \<^bold>\<preceq> \<eta>(a)" unfolding conn by simp
    hence "\<eta>((\<eta> a)) \<^bold>\<preceq> \<eta>(\<eta>(a) \<^bold>\<and> \<eta>(b))" using CoPw_def copw by (metis (no_types, lifting))
    hence 1: "a \<^bold>\<preceq> \<eta>(\<eta>(a) \<^bold>\<and> \<eta>(b))" using DNI_def dni by metis
    have "(\<eta> a) \<^bold>\<and> (\<eta> b) \<^bold>\<preceq> \<eta>(b)" unfolding conn by simp
    hence "\<eta>((\<eta> b)) \<^bold>\<preceq> \<eta>(\<eta>(a) \<^bold>\<and> \<eta>(b))" using CoPw_def copw by (metis (no_types, lifting))
    hence 2: "b \<^bold>\<preceq> \<eta>(\<eta>(a) \<^bold>\<and> \<eta>(b))" using DNI_def dni by metis
    from 1 2 have "a \<^bold>\<or> b \<^bold>\<preceq> \<eta>(\<eta>(a) \<^bold>\<and> \<eta>(b))" unfolding conn by simp
    hence "\<eta>(\<eta>(\<eta>(a) \<^bold>\<and> \<eta>(b))) \<^bold>\<preceq> \<eta>(a \<^bold>\<or> b)" using CoPw_def copw by auto
    hence "\<eta>(a) \<^bold>\<and> \<eta>(b) \<^bold>\<preceq> \<eta>(a \<^bold>\<or> b)" using DNI_def dni by simp
  } thus ?thesis by (simp add: DM4_def)
qed
text\<open>\noindent{From this follows that DM3 (resp. DM4) is entailed by CoP2 (resp. CoP1).}\<close>
lemma CoP2_DM3: "CoP2 \<eta> \<Longrightarrow> DM3 \<eta>" by (simp add: CoP2_def2 CoPw_DNE_DM3)
lemma CoP1_DM4: "CoP1 \<eta> \<Longrightarrow> DM4 \<eta>" by (simp add: CoP1_def2 CoPw_DNI_DM4)
text\<open>\noindent{Explore some non-entailment relations:}\<close>
lemma "CoPw \<eta> \<Longrightarrow> DM3 \<eta> \<Longrightarrow> DM4 \<eta> \<Longrightarrow> nNor \<eta> \<Longrightarrow> nDNor \<eta> \<Longrightarrow> DNI \<eta>" nitpick oops 
lemma "CoPw \<eta> \<Longrightarrow> DM3 \<eta> \<Longrightarrow> DM4 \<eta> \<Longrightarrow> nNor \<eta> \<Longrightarrow> nDNor \<eta> \<Longrightarrow> DNE \<eta>" nitpick oops 
lemma "CoPw \<eta> \<Longrightarrow> DM3 \<eta> \<Longrightarrow> DM4 \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> ECQm \<eta>" nitpick oops 
lemma "CoPw \<eta> \<Longrightarrow> DM3 \<eta> \<Longrightarrow> DM4 \<eta> \<Longrightarrow> DNI \<eta> \<Longrightarrow> DNE \<eta> \<Longrightarrow> TNDm \<eta>" nitpick oops 


subsubsection \<open>Contextual (strong) contraposition rule\<close>

text\<open>\noindent{XCoP: contextual contraposition (global/rule variant).}\<close>
abbreviation pXCoP ("XCoP\<^sup>_\<^sup>_ _") where "XCoP\<^sup>a\<^sup>b \<eta> \<equiv> \<forall>c. c \<^bold>\<and> a \<^bold>\<preceq> b \<longrightarrow> c \<^bold>\<and> (\<eta> b) \<^bold>\<preceq> (\<eta> a)"
definition "XCoP \<eta> \<equiv> \<forall>a b. XCoP\<^sup>a\<^sup>b \<eta>"
declare XCoP_def[Defs]

text\<open>\noindent{XCoP can alternatively be defined as ECQw plus TNDw.}\<close>
lemma XCoP_def2: "XCoP \<eta> = (ECQw \<eta> \<and> TNDw \<eta>)" proof -
  have LtoR1: "XCoP \<eta> \<Longrightarrow> ECQw \<eta>" unfolding XCoP_def ECQw_def conn by auto
  have LtoR2: "XCoP \<eta> \<Longrightarrow> TNDw \<eta>" unfolding XCoP_def TNDw_def conn by (smt atom_def atomic2 conn)
  have RtoL: "ECQw \<eta> \<and> TNDw \<eta> \<Longrightarrow> XCoP \<eta>" using XCoP_def ECQw_def TNDw_def unfolding conn by metis
  from LtoR1 LtoR2 RtoL show ?thesis by blast
qed
text\<open>\noindent{Explore some (non)entailment relations:}\<close>
lemma "XCoP \<eta> \<Longrightarrow> ECQ \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> TND \<eta>" nitpick oops 
lemma XCoP_CoPw: "XCoP \<eta> \<Longrightarrow> CoPw \<eta>" unfolding Defs conn by metis
lemma "XCoP \<eta> \<Longrightarrow> CoP1 \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> CoP2 \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> CoP3 \<eta>" nitpick oops 
lemma "CoP1 \<eta> \<and> CoP2 \<eta> \<Longrightarrow> XCoP \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> nNor \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> nDNor \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> rDNI \<eta>" nitpick oops 
lemma "XCoP \<eta> \<Longrightarrow> rDNE \<eta>" nitpick oops 
lemma XCoP_DM3: "XCoP \<eta> \<Longrightarrow> DM3 \<eta>" unfolding DM3_def XCoP_def conn using ECQw_def TNDw_def atom_def atomic2 conn by smt
lemma XCoP_DM4: "XCoP \<eta> \<Longrightarrow> DM4 \<eta>" unfolding DM4_def XCoP_def conn using ECQw_def TNDw_def atom_def atomic2 conn by smt


subsubsection \<open>Local contraposition axioms\<close>
text\<open>\noindent{Observe that the definitions below take implication as an additional parameter: @{text "\<iota>"}.}\<close>

text\<open>\noindent{lCoP: contraposition (local/axiom variants).}\<close>
abbreviation plCoPw ("lCoPw\<^sup>_\<^sup>_ _ _") where "lCoPw\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a b::\<sigma>) \<^bold>\<preceq> (\<iota> (\<eta> b) (\<eta> a))"
abbreviation plCoP1 ("lCoP1\<^sup>_\<^sup>_ _ _") where "lCoP1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a (\<eta> b::\<sigma>)) \<^bold>\<preceq> (\<iota> b (\<eta> a))"
abbreviation plCoP2 ("lCoP2\<^sup>_\<^sup>_ _ _") where "lCoP2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) b::\<sigma>) \<^bold>\<preceq> (\<iota> (\<eta> b) a)"
abbreviation plCoP3 ("lCoP3\<^sup>_\<^sup>_ _ _") where "lCoP3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) (\<eta> b::\<sigma>)) \<^bold>\<preceq> (\<iota> b a)"
definition "lCoPw  \<iota> \<eta> \<equiv> \<forall>a b. lCoPw\<^sup>a\<^sup>b \<iota> \<eta>"
definition "lCoP1  \<iota> \<eta> \<equiv> \<forall>a b. lCoP1\<^sup>a\<^sup>b \<iota> \<eta>"
definition "lCoP1' \<iota> \<eta> \<equiv> \<forall>a b. (\<iota> a (\<eta> b)) \<^bold>\<approx> (\<iota> b (\<eta> a))"
definition "lCoP2  \<iota> \<eta> \<equiv> \<forall>a b. lCoP2\<^sup>a\<^sup>b \<iota> \<eta>"
definition "lCoP2' \<iota> \<eta> \<equiv> \<forall>a b. (\<iota> (\<eta> a) b) \<^bold>\<approx> (\<iota> (\<eta> b) a)"
definition "lCoP3  \<iota> \<eta> \<equiv> \<forall>a b. lCoP3\<^sup>a\<^sup>b \<iota> \<eta>"
declare lCoPw_def[Defs] lCoP1_def[Defs] lCoP1'_def[Defs]
        lCoP2_def[Defs] lCoP2'_def[Defs] lCoP3_def[Defs]

lemma lCoP1_defs_rel: "lCoP1 \<iota> \<eta> = lCoP1' \<iota> \<eta>" by (metis (full_types) lCoP1'_def lCoP1_def)
lemma lCoP2_defs_rel: "lCoP2 \<iota> \<eta> = lCoP2' \<iota> \<eta>" by (metis (full_types) lCoP2'_def lCoP2_def)

text\<open>\noindent{All local contraposition variants are in general independent from each other. However if we take
classical implication we can verify some relationships.}\<close>

lemma lCoP1_def2: "lCoP1(\<^bold>\<rightarrow>) \<eta> = (lCoPw(\<^bold>\<rightarrow>) \<eta> \<and> DNI \<eta>)" unfolding Defs conn by smt
lemma lCoP2_def2: "lCoP2(\<^bold>\<rightarrow>) \<eta> = (lCoPw(\<^bold>\<rightarrow>) \<eta> \<and> DNE \<eta>)" unfolding Defs conn by smt

lemma "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis
lemma "lCoPw(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis
lemma "lCoPw(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma "lCoP3(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by blast
lemma "lCoPw(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma lCoP123: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<and> lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis

text\<open>\noindent{Local variants imply global ones as expected.}\<close>
lemma "lCoPw(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoPw \<eta>" unfolding Defs conn by metis
lemma "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP1 \<eta>" unfolding Defs conn by metis
lemma "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP2 \<eta>" unfolding Defs conn by metis
lemma "lCoP3(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> CoP3 \<eta>" unfolding Defs conn by metis

text\<open>\noindent{Explore some (non)entailment relations.}\<close>
lemma lCoPw_XCoP: "lCoPw(\<^bold>\<rightarrow>) \<eta> = XCoP \<eta>" unfolding Defs conn by (smt XCoP_def XCoP_def2 TNDw_def conn)
lemma lCoP1_TND: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> TND \<eta>" by (smt XCoP_CoPw XCoP_def2 CoP1_Nor CoP1_def2 nNor_def TND_def TNDw_def lCoP1_def2 lCoPw_XCoP conn)
lemma "TND \<eta> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma lCoP2_ECQ: "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> ECQ \<eta>" by (smt XCoP_CoPw XCoP_def2 CoP2_DNor CoP2_def2 nDNor_def ECQ_def ECQw_def lCoP2_def2 lCoPw_XCoP conn)
lemma "ECQ \<eta> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>) \<eta>" nitpick oops


subsubsection \<open>Local modus tollens axioms\<close>

text\<open>\noindent{lMT: Modus tollens (local/axiom variants).}\<close>
abbreviation plMT0 ("lMT0\<^sup>_\<^sup>_ _ _") where "lMT0\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a b::\<sigma>) \<^bold>\<and> (\<eta> b) \<^bold>\<preceq> (\<eta> a)"
abbreviation plMT1 ("lMT1\<^sup>_\<^sup>_ _ _") where "lMT1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a (\<eta> b::\<sigma>)) \<^bold>\<and> b \<^bold>\<preceq> (\<eta> a)"
abbreviation plMT2 ("lMT2\<^sup>_\<^sup>_ _ _") where "lMT2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) b::\<sigma>) \<^bold>\<and> (\<eta> b) \<^bold>\<preceq> a"
abbreviation plMT3 ("lMT3\<^sup>_\<^sup>_ _ _") where "lMT3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) (\<eta> b::\<sigma>)) \<^bold>\<and> b \<^bold>\<preceq> a"
definition "lMT0 \<iota> \<eta> \<equiv> \<forall>a b. lMT0\<^sup>a\<^sup>b \<iota> \<eta>"
definition "lMT1 \<iota> \<eta> \<equiv> \<forall>a b. lMT1\<^sup>a\<^sup>b \<iota> \<eta>"
definition "lMT2 \<iota> \<eta> \<equiv> \<forall>a b. lMT2\<^sup>a\<^sup>b \<iota> \<eta>"
definition "lMT3 \<iota> \<eta> \<equiv> \<forall>a b. lMT3\<^sup>a\<^sup>b \<iota> \<eta>"
declare lMT0_def[Defs] lMT1_def[Defs] lMT2_def[Defs] lMT3_def[Defs]

text\<open>\noindent{All local MT variants are in general independent from each other and also from local CoP instances.
However if we take classical implication we can verify that local MT and CoP are indeed equivalent.}\<close>
lemma "lMT0(\<^bold>\<rightarrow>) \<eta> = lCoPw(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis
lemma "lMT1(\<^bold>\<rightarrow>) \<eta> = lCoP1(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis
lemma "lMT2(\<^bold>\<rightarrow>) \<eta> = lCoP2(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis
lemma "lMT3(\<^bold>\<rightarrow>) \<eta> = lCoP3(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis


subsubsection \<open>Disjunctive syllogism\<close>

text\<open>\noindent{DS: disjunctive syllogism.}\<close>
abbreviation pDS1 ("DS1\<^sup>_\<^sup>_ _ _") where "DS1\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (a \<^bold>\<or> b::\<sigma>) \<^bold>\<preceq> (\<iota> (\<eta> a) b)"
abbreviation pDS2 ("DS2\<^sup>_\<^sup>_ _ _") where "DS2\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> (\<eta> a) b::\<sigma>) \<^bold>\<preceq> (a \<^bold>\<or> b)"
abbreviation pDS3 ("DS3\<^sup>_\<^sup>_ _ _") where "DS3\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> ((\<eta> a) \<^bold>\<or> b::\<sigma>) \<^bold>\<preceq> (\<iota> a b)"
abbreviation pDS4 ("DS4\<^sup>_\<^sup>_ _ _") where "DS4\<^sup>a\<^sup>b \<iota> \<eta> \<equiv> (\<iota> a b::\<sigma>) \<^bold>\<preceq> ((\<eta> a) \<^bold>\<or> b)"
definition "DS1 \<iota> \<eta> \<equiv> \<forall>a b. DS1\<^sup>a\<^sup>b \<iota> \<eta>"
definition "DS2 \<iota> \<eta> \<equiv> \<forall>a b. DS2\<^sup>a\<^sup>b \<iota> \<eta>"
definition "DS3 \<iota> \<eta> \<equiv> \<forall>a b. DS3\<^sup>a\<^sup>b \<iota> \<eta>"
definition "DS4 \<iota> \<eta> \<equiv> \<forall>a b. DS4\<^sup>a\<^sup>b \<iota> \<eta>"
declare DS1_def[Defs] DS2_def[Defs] DS3_def[Defs] DS4_def[Defs]

text\<open>\noindent{All DS variants are in general independent from each other. However if we take classical implication
we can verify that the pairs DS1-DS3 and DS2-DS4 are indeed equivalent. }\<close>
lemma "DS1(\<^bold>\<rightarrow>) \<eta> = DS3(\<^bold>\<rightarrow>) \<eta>" unfolding Defs by (metis impl_def join_def)
lemma "DS2(\<^bold>\<rightarrow>) \<eta> = DS4(\<^bold>\<rightarrow>) \<eta>" unfolding Defs by (metis impl_def join_def)

text\<open>\noindent{Explore some (non)entailment relations.}\<close>
lemma DS1_nDNor: "DS1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> nDNor \<eta>" unfolding Defs by (metis bottom_def impl_def join_def top_def)
lemma DS2_nNor:  "DS2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> nNor \<eta>" unfolding Defs by (metis bottom_def impl_def join_def top_def)
lemma lCoP2_DS1: "lCoP2(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<eta>" unfolding Defs conn by metis
lemma lCoP1_DS2: "lCoP1(\<^bold>\<rightarrow>) \<eta> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<eta>" unfolding Defs by (metis (no_types, lifting) conn)
lemma "CoP2 \<eta> \<Longrightarrow> DS1(\<^bold>\<rightarrow>) \<eta>" nitpick oops
lemma "CoP1 \<eta> \<Longrightarrow> DS2(\<^bold>\<rightarrow>) \<eta>" nitpick oops

end
