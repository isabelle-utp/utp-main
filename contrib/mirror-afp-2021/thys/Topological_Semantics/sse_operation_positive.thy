theory sse_operation_positive
  imports sse_boolean_algebra
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Positive semantic conditions for operations\<close>

text\<open>\noindent{We define and interrelate some useful conditions on propositional functions which do not involve
negative-like properties (hence 'positive'). We focus on propositional functions which correspond to unary
connectives of the algebra (with type @{text "\<sigma>\<Rightarrow>\<sigma>"}). We call such propositional functions 'operations'.}\<close>

subsection \<open>Definitions (finitary case)\<close>

text\<open>\noindent{Monotonicity (MONO).}\<close>
definition "MONO \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> \<phi> A \<^bold>\<preceq> \<phi> B" 
lemma MONO_ant: "MONO \<phi> \<Longrightarrow> \<forall>A B C. A \<^bold>\<preceq> B \<longrightarrow> \<phi>(B \<^bold>\<rightarrow> C) \<^bold>\<preceq> \<phi>(A \<^bold>\<rightarrow> C)" by (smt MONO_def conn)
lemma MONO_cons: "MONO \<phi> \<Longrightarrow> \<forall>A B C. A \<^bold>\<preceq> B \<longrightarrow> \<phi>(C \<^bold>\<rightarrow> A) \<^bold>\<preceq> \<phi>(C \<^bold>\<rightarrow> B)" by (smt MONO_def conn)
lemma MONO_dual: "MONO \<phi> \<Longrightarrow> MONO \<phi>\<^sup>d" by (smt MONO_def dual_def compl_def)

text\<open>\noindent{Extensive/expansive (EXP) and its dual (dEXP), aka. 'contractive'.}\<close>
definition "EXP \<phi>  \<equiv> \<forall>A. A \<^bold>\<preceq> \<phi> A" 
definition "dEXP \<phi> \<equiv> \<forall>A. \<phi> A \<^bold>\<preceq> A"
lemma EXP_dual1: "EXP \<phi> \<Longrightarrow> dEXP \<phi>\<^sup>d" by (metis EXP_def dEXP_def dual_def compl_def)
lemma EXP_dual2: "dEXP \<phi> \<Longrightarrow> EXP \<phi>\<^sup>d" by (metis EXP_def dEXP_def dual_def compl_def)

text\<open>\noindent{Idempotence (IDEM).}\<close>
definition "IDEM \<phi>  \<equiv> \<forall>A. (\<phi> A) \<^bold>\<approx> \<phi>(\<phi> A)"
definition "IDEMa \<phi> \<equiv> \<forall>A. (\<phi> A) \<^bold>\<preceq> \<phi>(\<phi> A)"
definition "IDEMb \<phi> \<equiv> \<forall>A. (\<phi> A) \<^bold>\<succeq> \<phi>(\<phi> A)"
lemma IDEM_dual1: "IDEMa \<phi> \<Longrightarrow> IDEMb \<phi>\<^sup>d" unfolding dual_def IDEMa_def IDEMb_def compl_def by auto
lemma IDEM_dual2: "IDEMb \<phi> \<Longrightarrow> IDEMa \<phi>\<^sup>d" unfolding dual_def IDEMa_def IDEMb_def compl_def by auto
lemma IDEM_dual: "IDEM \<phi> = IDEM \<phi>\<^sup>d" by (metis IDEM_def IDEM_dual1 IDEM_dual2 IDEMa_def IDEMb_def dual_symm)

text\<open>\noindent{Normality (NOR) and its dual (dNOR).}\<close>
definition "NOR \<phi>  \<equiv> (\<phi> \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<bottom>"
definition "dNOR \<phi> \<equiv> (\<phi> \<^bold>\<top>) \<^bold>\<approx> \<^bold>\<top>" 
lemma NOR_dual1: "NOR \<phi> = dNOR \<phi>\<^sup>d" unfolding dual_def NOR_def dNOR_def top_def bottom_def compl_def by simp
lemma NOR_dual2: "dNOR \<phi> = NOR \<phi>\<^sup>d" unfolding dual_def NOR_def dNOR_def top_def bottom_def compl_def by simp

text\<open>\noindent{Distribution over meets or multiplicativity (MULT).}\<close>
definition "MULT \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<approx> (\<phi> A) \<^bold>\<and> (\<phi> B)" 
definition "MULT_a \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" 
definition "MULT_b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<succeq> (\<phi> A) \<^bold>\<and> (\<phi> B)" 

text\<open>\noindent{Distribution over joins or additivity (ADDI).}\<close>
definition "ADDI \<phi>   \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<^bold>\<approx> (\<phi> A) \<^bold>\<or> (\<phi> B)" 
definition "ADDI_a \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<or> (\<phi> B)"
definition "ADDI_b \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<or> B) \<^bold>\<succeq> (\<phi> A) \<^bold>\<or> (\<phi> B)" 


subsection \<open>Relations among conditions (finitary case)\<close>

text\<open>\noindent{dEXP and dNOR entail NOR.}\<close>
lemma "dEXP \<phi> \<Longrightarrow> dNOR \<phi> \<Longrightarrow> NOR \<phi>" by (meson bottom_def dEXP_def NOR_def)

text\<open>\noindent{EXP and NOR entail dNOR.}\<close>
lemma "EXP \<phi> \<Longrightarrow> NOR \<phi> \<Longrightarrow> dNOR \<phi>" by (simp add: EXP_def dNOR_def top_def)

text\<open>\noindent{Interestingly, EXP and its dual allow for an alternative characterization of fixed-point operators.}\<close>
lemma EXP_fp:  "EXP  \<phi> \<Longrightarrow> \<phi>\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>c \<^bold>\<squnion> id)" by (smt id_def EXP_def dual_def dual_symm equal_op_def conn)
lemma dEXP_fp: "dEXP \<phi> \<Longrightarrow> \<phi>\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi> \<^bold>\<squnion> compl)" by (smt dEXP_def equal_op_def conn)

text\<open>\noindent{MONO, MULT-a and ADDI-b are equivalent.}\<close>
lemma MONO_MULTa: "MONO \<phi> = MULT_a \<phi>" proof -
  have lr: "MONO \<phi> \<Longrightarrow> MULT_a \<phi>" by (smt MONO_def MULT_a_def meet_def)
  have rl: "MULT_a \<phi> \<Longrightarrow> MONO \<phi>" proof-
    assume multa: "MULT_a \<phi>"
    { fix A B
      { assume "A \<^bold>\<preceq> B"
        hence "A \<^bold>\<approx> A \<^bold>\<and> B" unfolding conn by blast
        hence "\<phi> A \<^bold>\<approx> \<phi>(A \<^bold>\<and> B)" unfolding conn by simp
        moreover from multa have "\<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" using MULT_a_def by metis
        ultimately have "\<phi> A \<^bold>\<preceq> (\<phi> A) \<^bold>\<and> (\<phi> B)" by blast
        hence "\<phi> A \<^bold>\<preceq> (\<phi> B)" unfolding conn by blast
      } hence "A \<^bold>\<preceq> B \<longrightarrow> \<phi> A \<^bold>\<preceq> \<phi> B" by (rule impI)
    } thus ?thesis by (simp add: MONO_def) qed
  from lr rl show ?thesis by auto
qed
lemma MONO_ADDIb: "MONO \<phi> = ADDI_b \<phi>" proof -
  have lr: "MONO \<phi> \<Longrightarrow> ADDI_b \<phi>" by (smt ADDI_b_def MONO_def join_def)
  have rl: "ADDI_b \<phi> \<Longrightarrow> MONO \<phi>" proof -
  assume addib: "ADDI_b \<phi>"
  { fix A B
    { assume "A \<^bold>\<preceq> B"
      hence "B \<^bold>\<approx> A \<^bold>\<or> B" unfolding conn by blast
      hence "\<phi> B \<^bold>\<approx> \<phi>(A \<^bold>\<or> B)" unfolding conn by simp
      moreover from addib have "(\<phi> A) \<^bold>\<or> (\<phi> B) \<^bold>\<preceq> \<phi>(A \<^bold>\<or> B)" using ADDI_b_def by metis
      ultimately have "(\<phi> A) \<^bold>\<or> (\<phi> B) \<^bold>\<preceq> \<phi> B" by blast
      hence "\<phi> A \<^bold>\<preceq> (\<phi> B)" unfolding conn by blast
    } hence "A \<^bold>\<preceq> B \<longrightarrow> \<phi> A \<^bold>\<preceq> \<phi> B" by (rule impI)
  } thus ?thesis by (simp add: MONO_def) qed
  from lr rl show ?thesis by auto
qed
lemma ADDIb_MULTa: "ADDI_b \<phi> = MULT_a \<phi>" using MONO_ADDIb MONO_MULTa by auto

end
