theory sse_operation_positive_quantification
  imports sse_operation_positive sse_boolean_algebra_quantification
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)


subsection \<open>Definitions (infinitary case)\<close>

text\<open>\noindent{We define and interrelate infinitary variants for some previously introduced ('positive') conditions 
on operations and show how they relate to quantifiers as previously defined.}\<close>

text\<open>\noindent{Distribution over infinite meets (infima) or infinite multiplicativity (iMULT).}\<close>
definition "iMULT \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>\<approx> \<^bold>\<And>Ra[\<phi>|S]" 
definition "iMULT_a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>\<preceq> \<^bold>\<And>Ra[\<phi>|S]"
definition "iMULT_b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<And>S) \<^bold>\<succeq> \<^bold>\<And>Ra[\<phi>|S]"

text\<open>\noindent{Distribution over infinite joins (suprema) or infinite additivity (iADDI).}\<close>
definition "iADDI \<phi>   \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<approx> \<^bold>\<Or>Ra[\<phi>|S]" 
definition "iADDI_a \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<preceq> \<^bold>\<Or>Ra[\<phi>|S]" 
definition "iADDI_b \<phi> \<equiv> \<forall>S. \<phi>(\<^bold>\<Or>S) \<^bold>\<succeq> \<^bold>\<Or>Ra[\<phi>|S]"


subsection \<open>Relations among conditions (infinitary case)\<close>

text\<open>\noindent{We start by noting that there is a duality between iADDI-a and iMULT-b.}\<close>
lemma iADDI_MULT_dual1: "iADDI_a \<phi> \<Longrightarrow> iMULT_b \<phi>\<^sup>d" unfolding iADDI_a_def iMULT_b_def by (metis compl_def dual_def iDM_a iDM_b Ra_dual1)
lemma iADDI_MULT_dual2: "iMULT_b \<phi> \<Longrightarrow> iADDI_a \<phi>\<^sup>d" unfolding iADDI_a_def iMULT_b_def by (metis compl_def dual_def iDM_b Ra_dual3)

text\<open>\noindent{MULT-a and iMULT-a are equivalent.}\<close>
lemma iMULTa_rel: "iMULT_a \<phi> = MULT_a \<phi>" proof -
  have lr: "iMULT_a \<phi> \<Longrightarrow> MULT_a \<phi>" proof -
  assume imulta: "iMULT_a \<phi>"
  { fix A::"\<sigma>" and B::"\<sigma>"
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    from imulta have "\<phi>(\<^bold>\<And>?S) \<^bold>\<preceq> \<^bold>\<forall>\<^sup>R\<lparr>?S\<rparr> \<phi>" by (simp add: iMULT_a_def Ra_restr_all)
    moreover have "\<^bold>\<And>?S = A \<^bold>\<and> B" using infimum_def meet_def by auto
    moreover have "\<^bold>\<forall>\<^sup>R\<lparr>?S\<rparr> \<phi> = (\<phi> A) \<^bold>\<and> (\<phi> B)" using meet_def by auto
    ultimately have "\<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" by smt
  } thus ?thesis by (simp add: MULT_a_def) qed
  have rl: "MULT_a \<phi> \<Longrightarrow> iMULT_a \<phi>" by (smt MONO_def MONO_MULTa Ra_restr_all iMULT_a_def inf_char)
  from lr rl show ?thesis by auto
qed
text\<open>\noindent{ADDI-b and iADDI-b are equivalent.}\<close>
lemma iADDIb_rel: "iADDI_b \<phi> = ADDI_b \<phi>" proof -
  have lr: "iADDI_b \<phi> \<Longrightarrow> ADDI_b \<phi>" proof -
  assume iaddib: "iADDI_b \<phi>"
  { fix A::"\<sigma>" and B::"\<sigma>"
    let ?S="\<lambda>Z. Z=A \<or> Z=B"
    from iaddib have "\<phi>(\<^bold>\<Or>?S) \<^bold>\<succeq> \<^bold>\<exists>\<^sup>R\<lparr>?S\<rparr>(\<phi>)" by (simp add: iADDI_b_def Ra_restr_ex)
    moreover have "\<^bold>\<Or>?S = A \<^bold>\<or> B" using supremum_def join_def by auto
    moreover have "\<^bold>\<exists>\<^sup>R\<lparr>?S\<rparr>(\<phi>) = (\<phi> A) \<^bold>\<or> (\<phi> B)" using join_def by auto
    ultimately have "\<phi>(A \<^bold>\<or> B) \<^bold>\<succeq> (\<phi> A) \<^bold>\<or> (\<phi> B)" by smt
  } thus ?thesis by (simp add: ADDI_b_def) qed
  have rl: "ADDI_b \<phi> \<Longrightarrow> iADDI_b \<phi>" by (smt MONO_def MONO_ADDIb Ra_restr_ex iADDI_b_def sup_char)
  from lr rl show ?thesis by auto
qed

text\<open>\noindent{Thus we have that MONO, MULT-a/iMULT-a and ADDI-b/iADDI-b are all equivalent.}\<close>
lemma MONO_iADDIb: "MONO \<phi> = iADDI_b \<phi>" using MONO_ADDIb iADDIb_rel by simp
lemma MONO_iMULTa: "MONO \<phi> = iMULT_a \<phi>" using MONO_MULTa iMULTa_rel by simp
lemma iADDI_b_iMULTa: "iADDI_b \<phi> = iMULT_a \<phi>" using MONO_iADDIb MONO_iMULTa by auto

lemma PI_imult: "MONO \<phi> \<Longrightarrow> iMULT_b \<phi> \<Longrightarrow> iMULT \<phi>" using MONO_MULTa iMULT_a_def iMULT_b_def iMULT_def iMULTa_rel by auto
lemma PC_iaddi: "MONO \<phi> \<Longrightarrow> iADDI_a \<phi> \<Longrightarrow> iADDI \<phi>"  using MONO_ADDIb iADDI_a_def iADDI_b_def iADDI_def iADDIb_rel by auto

text\<open>\noindent{Interestingly, we can show that suitable (infinitary) conditions on an operation can make the set
of its fixed points closed under infinite meets/joins.}\<close>
lemma fp_inf_closed: "MONO \<phi> \<Longrightarrow> iMULT_b \<phi> \<Longrightarrow> infimum_closed (fp \<phi>)" by (metis (full_types) PI_imult Ra_restr_all iMULT_def infimum_def)
lemma fp_sup_closed: "MONO \<phi> \<Longrightarrow> iADDI_a \<phi> \<Longrightarrow> supremum_closed (fp \<phi>)" by (metis (full_types) PC_iaddi Ra_restr_ex iADDI_def supremum_def) 


subsection \<open>Exploring the Barcan formula and its converse\<close>

text\<open>\noindent{The converse Barcan formula follows readily from monotonicity.}\<close>
lemma CBarcan1: "MONO \<phi> \<Longrightarrow> \<forall>\<pi>.  \<phi>(\<^bold>\<forall>x. \<pi> x)  \<^bold>\<preceq> (\<^bold>\<forall>x. \<phi>(\<pi> x))" by (metis (mono_tags, lifting) MONO_def)
lemma CBarcan2: "MONO \<phi> \<Longrightarrow> \<forall>\<pi>. (\<^bold>\<exists>x. \<phi>(\<pi> x)) \<^bold>\<preceq> \<phi>(\<^bold>\<exists>x. \<pi> x)" by (metis (mono_tags, lifting) MONO_def)

text\<open>\noindent{However, the Barcan formula requires a stronger assumption (of an infinitary character).}\<close>
lemma Barcan1: "iMULT_b \<phi> \<Longrightarrow> \<forall>\<pi>. (\<^bold>\<forall>x. \<phi>(\<pi> x)) \<^bold>\<preceq> \<phi>(\<^bold>\<forall>x. \<pi> x)" proof -
  assume imultb: "iMULT_b \<phi>"
  { fix \<pi>::"'a\<Rightarrow>\<sigma>"
    from imultb have "(\<^bold>\<And>Ra(\<phi>\<circ>\<pi>)) \<^bold>\<preceq> \<phi>(\<^bold>\<And>Ra(\<pi>))" unfolding iMULT_b_def by (smt comp_apply infimum_def pfunRange_def pfunRange_restr_def)
    moreover have "\<^bold>\<And>Ra(\<pi>) = (\<^bold>\<forall>x. \<pi> x)" unfolding Ra_all by simp
    moreover have "\<^bold>\<And>Ra(\<phi>\<circ>\<pi>) = (\<^bold>\<forall>x. \<phi>(\<pi> x))" unfolding Ra_all by simp
    ultimately have "(\<^bold>\<forall>x. \<phi>(\<pi> x)) \<^bold>\<preceq> \<phi>(\<^bold>\<forall>x. \<pi> x)" by simp
  } thus ?thesis by simp
qed
lemma Barcan2: "iADDI_a \<phi> \<Longrightarrow> \<forall>\<pi>. \<phi>(\<^bold>\<exists>x. \<pi> x) \<^bold>\<preceq> (\<^bold>\<exists>x. \<phi>(\<pi> x))" proof -
  assume iaddia: "iADDI_a \<phi>"
  { fix \<pi>::"'a\<Rightarrow>\<sigma>"
    from iaddia have "\<phi>(\<^bold>\<Or>Ra(\<pi>)) \<^bold>\<preceq> (\<^bold>\<Or>Ra(\<phi>\<circ>\<pi>))" unfolding iADDI_a_def Ra_restr_ex by (smt fcomp_comp fcomp_def pfunRange_def sup_char)
    moreover have "\<^bold>\<Or>Ra(\<pi>) = (\<^bold>\<exists>x. \<pi> x)" unfolding Ra_ex by simp
    moreover have "\<^bold>\<Or>Ra(\<phi>\<circ>\<pi>) = (\<^bold>\<exists>x. \<phi>(\<pi> x))" unfolding Ra_ex by simp
    ultimately have "\<phi>(\<^bold>\<exists>x. \<pi> x) \<^bold>\<preceq> (\<^bold>\<exists>x. \<phi>(\<pi> x))" by simp
  } thus ?thesis by simp
qed

end
