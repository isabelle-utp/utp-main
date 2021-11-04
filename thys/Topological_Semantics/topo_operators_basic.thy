theory topo_operators_basic
  imports sse_operation_positive_quantification
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

abbreviation implies_rl::"bool\<Rightarrow>bool\<Rightarrow>bool" (infixl "\<longleftarrow>" 25) where "\<phi> \<longleftarrow> \<psi> \<equiv> \<psi> \<longrightarrow> \<phi>" (*for readability*)

section \<open>Topological operators\<close>

text\<open>\noindent{Below we define some conditions on algebraic operations (aka. operators) with type @{text "\<sigma>\<Rightarrow>\<sigma>"}.
Those operations are aimed at extending a Boolean 'algebra of propositions' towards different
generalizations of topological algebras.
We divide this section into two parts. In the first we define and interrelate the topological operators of 
interior, closure, border and frontier. In the second we introduce the (more fundamental) notion of
derivative (aka. derived set) and its related notion of (Cantorian) coherence, defining both as operators.
We follow the naming conventions introduced originally by Kuratowski @{cite Kuratowski1}
(cf. also @{cite Kuratowski2}) and Zarycki @{cite Zarycki1}.}\<close>

subsection \<open>Interior and closure\<close>
text\<open>\noindent{In this section we examine the traditional notion of topological (closure, resp. interior) algebras
in the spirit of McKinsey \& Tarski @{cite AOT}, but drawing primarily from the works of Zarycki
@{cite Zarycki1} and Kuratowski @{cite Kuratowski1}.
We also explore the less-known notions of border (cf. 'Rand' @{cite Hausdorff}, 'bord' @{cite Zarycki1}) and
frontier (aka. 'boundary'; cf. 'Grenze' @{cite Hausdorff}, 'fronti\`ere' @{cite Zarycki1} @{cite Kuratowski2})
as studied by Zarycki @{cite Zarycki1} and define corresponding operations for them.}\<close>

subsubsection \<open>Interior conditions\<close>

abbreviation "Int_1 \<phi>  \<equiv> MULT \<phi>" 
abbreviation "Int_1a \<phi> \<equiv> MULT_a \<phi>"
abbreviation "Int_1b \<phi> \<equiv> MULT_b \<phi>" 
abbreviation "Int_2 \<phi>  \<equiv> dEXP \<phi>"
abbreviation "Int_3 \<phi>  \<equiv> dNOR \<phi>"
abbreviation "Int_4 \<phi>  \<equiv> IDEM \<phi>"
abbreviation "Int_4' \<phi> \<equiv> IDEMa \<phi>"

abbreviation "Int_5 \<phi>  \<equiv> NOR \<phi>"
definition "Int_6 \<phi>  \<equiv> \<forall>A B. \<phi>(A \<^bold>\<leftharpoonup> B) \<^bold>\<preceq> \<phi>(A) \<^bold>\<leftharpoonup> \<phi>(B)"
definition "Int_7 \<phi>  \<equiv> \<forall>A B. \<phi>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<phi>(A) \<^bold>\<rightarrow> \<phi>(B)"
definition "Int_8 \<phi>  \<equiv> \<forall>A B. \<phi>(\<phi> A \<^bold>\<or> \<phi> B) \<^bold>\<approx> (\<phi> A) \<^bold>\<or> (\<phi> B)"
definition "Int_9 \<phi>  \<equiv> \<forall>A B. \<phi> A \<^bold>\<preceq> B \<longrightarrow> \<phi> A \<^bold>\<preceq> \<phi> B"

text\<open>\noindent{@{text "\<phi>"} is an interior operator (@{text "\<II>(\<phi>)"}) iff it satisfies conditions 1-4 (cf. @{cite Zarycki1}
and also @{cite Kuratowski2}). This characterization is shown consistent by generating a non-trivial model.}\<close>
abbreviation "\<II> \<phi> \<equiv> Int_1 \<phi> \<and> Int_2 \<phi> \<and> Int_3 \<phi> \<and> Int_4 \<phi>"
lemma "\<II> \<phi>" nitpick[satisfy, card w=3] oops (*model found: characterization is consistent*)

text\<open>\noindent{We verify some properties which will become useful later (also to improve provers' performance).}\<close>
lemma PI1: "Int_1 \<phi> = (Int_1a \<phi> \<and> Int_1b \<phi>)" by (metis MULT_def MULT_a_def MULT_b_def)
lemma PI4: "Int_2 \<phi> \<Longrightarrow> (Int_4 \<phi> = Int_4' \<phi>)" unfolding dEXP_def IDEM_def IDEMa_def by blast
lemma PI5: "Int_2 \<phi> \<Longrightarrow> Int_5 \<phi>" unfolding dEXP_def NOR_def conn by blast
lemma PI6: "Int_1a \<phi> \<Longrightarrow> Int_2 \<phi> \<Longrightarrow> Int_6 \<phi>" by (smt dEXP_def Int_6_def MONO_MULTa MONO_def conn)
lemma PI7: "Int_1 \<phi> \<Longrightarrow> Int_7 \<phi>" proof -
  assume int1: "Int_1 \<phi>"
  { fix a b
    have "a \<^bold>\<and> b = a \<^bold>\<and> (a \<^bold>\<rightarrow> b)" unfolding conn by blast
    hence "\<phi>(a \<^bold>\<and> b) = \<phi>(a \<^bold>\<and> (a \<^bold>\<rightarrow> b))" by simp
    moreover from int1 have "\<phi>(a \<^bold>\<and> b) \<^bold>\<approx> \<phi> a \<^bold>\<and> \<phi> b" by (simp add: MULT_def)
    moreover from int1 have "\<phi>(a \<^bold>\<and> (a \<^bold>\<rightarrow> b)) \<^bold>\<approx> \<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b)" by (simp add: MULT_def)
    ultimately have "\<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b) \<^bold>\<approx> \<phi> a \<^bold>\<and> \<phi> b" by simp
    hence "\<phi> a \<^bold>\<and> \<phi> (a \<^bold>\<rightarrow> b) \<^bold>\<approx> \<phi> a \<^bold>\<and> (\<phi> a \<^bold>\<rightarrow> \<phi> b)" unfolding conn by blast
    hence "\<phi>(a \<^bold>\<rightarrow> b) \<^bold>\<preceq> \<phi> a \<^bold>\<rightarrow> \<phi> b" unfolding conn by blast
  } thus ?thesis by (simp add: Int_7_def)
qed
lemma PI8: "Int_1a \<phi> \<Longrightarrow> Int_2 \<phi> \<Longrightarrow> Int_4 \<phi> \<Longrightarrow> Int_8 \<phi>" using ADDI_b_def IDEM_def Int_8_def MONO_ADDIb MONO_MULTa dEXP_def join_def by auto
lemma PI9: "Int_1a \<phi> \<Longrightarrow> Int_4 \<phi> \<Longrightarrow> Int_9 \<phi>" using IDEM_def Int_9_def MONO_def MONO_MULTa by simp


subsubsection \<open>Closure conditions\<close>

abbreviation "Cl_1 \<phi> \<equiv> ADDI \<phi>"
abbreviation "Cl_1a \<phi> \<equiv> ADDI_a \<phi>"
abbreviation "Cl_1b \<phi> \<equiv> ADDI_b \<phi>"
abbreviation "Cl_2 \<phi> \<equiv> EXP \<phi>"
abbreviation "Cl_3 \<phi>  \<equiv> NOR \<phi>"
abbreviation "Cl_4 \<phi> \<equiv> IDEM \<phi>"
abbreviation "Cl_4' \<phi> \<equiv> IDEMb \<phi>"

abbreviation "Cl_5 \<phi>  \<equiv> dNOR \<phi>"
definition "Cl_6 \<phi>  \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<leftharpoonup> (\<phi> B) \<^bold>\<preceq> \<phi> (A \<^bold>\<leftharpoonup> B)"
definition "Cl_7 \<phi> \<equiv> \<forall>A B. (\<phi> A) \<^bold>\<rightarrow> (\<phi> B) \<^bold>\<preceq> \<phi> (A \<^bold>\<rightarrow> B)"
definition "Cl_8 \<phi>  \<equiv> \<forall>A B. \<phi>(\<phi> A \<^bold>\<and> \<phi> B) \<^bold>\<approx> (\<phi> A) \<^bold>\<and> (\<phi> B)"
definition "Cl_9 \<phi>  \<equiv> \<forall>A B.  A \<^bold>\<preceq> \<phi> B \<longrightarrow> \<phi> A \<^bold>\<preceq> \<phi> B"

text\<open>\noindent{@{text "\<phi>"} is a closure operator (@{text "\<CC>(\<phi>)"}) iff it satisfies conditions 1-4 (cf. @{cite Kuratowski1}
@{cite Kuratowski2}). This characterization is shown consistent by generating a non-trivial model.}\<close>
abbreviation "\<CC> \<phi>  \<equiv> Cl_1 \<phi> \<and> Cl_2 \<phi> \<and> Cl_3  \<phi> \<and> Cl_4 \<phi>"
lemma "\<CC> \<phi>" nitpick[satisfy, card w=3] oops (*model found: characterization is consistent*)

text\<open>\noindent{We verify some properties that will become useful later.}\<close>
lemma PC1: "Cl_1 \<phi> = (Cl_1a \<phi> \<and> Cl_1b \<phi>)" unfolding ADDI_def ADDI_a_def ADDI_b_def by blast
lemma PC4: "Cl_2 \<phi> \<Longrightarrow> (Cl_4 \<phi> = Cl_4' \<phi>)" unfolding EXP_def IDEM_def IDEMb_def by smt
lemma PC5: "Cl_2 \<phi> \<Longrightarrow> Cl_5 \<phi>" unfolding EXP_def dNOR_def conn by simp
lemma PC6: "Cl_1 \<phi> \<Longrightarrow> Cl_6 \<phi>" proof -
  assume cl1: "Cl_1 \<phi>"
  { fix a b
    have "a \<^bold>\<or> b = (a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b" unfolding conn by blast
    hence "\<phi>(a \<^bold>\<or> b) = \<phi>((a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b)" by simp
    moreover from cl1 have "\<phi>(a \<^bold>\<or> b) \<^bold>\<approx> \<phi> a \<^bold>\<or> \<phi> b" by (simp add: ADDI_def)
    moreover from cl1 have "\<phi>((a \<^bold>\<leftharpoonup> b) \<^bold>\<or> b) \<^bold>\<approx> \<phi> (a \<^bold>\<leftharpoonup> b) \<^bold>\<or> (\<phi> b)" by (simp add: ADDI_def)
    ultimately have "\<phi> a \<^bold>\<or> \<phi> b \<^bold>\<approx> \<phi>(a \<^bold>\<leftharpoonup> b) \<^bold>\<or> \<phi> b" by simp
    hence "(\<phi> a \<^bold>\<leftharpoonup> \<phi> b) \<^bold>\<or> \<phi> b \<^bold>\<approx> \<phi>(a \<^bold>\<leftharpoonup> b) \<^bold>\<or> \<phi> b" unfolding conn by blast
    hence "\<phi> a \<^bold>\<leftharpoonup> \<phi> b \<^bold>\<preceq> \<phi> (a \<^bold>\<leftharpoonup> b)" unfolding conn by blast
  } thus ?thesis by (simp add: Cl_6_def)
qed
lemma PC7: "Cl_1b \<phi> \<Longrightarrow> Cl_2 \<phi> \<Longrightarrow> Cl_7 \<phi>" by (smt EXP_def Cl_7_def MONO_def PC1 MONO_ADDIb conn)
lemma PC8: "Cl_1b \<phi> \<Longrightarrow> Cl_2 \<phi> \<Longrightarrow> Cl_4 \<phi> \<Longrightarrow> Cl_8 \<phi>" by (smt Cl_8_def EXP_def IDEM_def MONO_ADDIb MONO_MULTa MULT_a_def meet_def)
lemma PC9: "Cl_1b \<phi> \<Longrightarrow> Cl_4 \<phi> \<Longrightarrow> Cl_9 \<phi>" by (smt IDEM_def Cl_9_def MONO_def MONO_ADDIb)


subsubsection \<open>Exploring dualities\<close>

lemma IC1_dual: "Int_1a \<phi> = Cl_1b \<phi>" using MONO_ADDIb MONO_MULTa by auto
lemma "Int_1b \<phi> = Cl_1a \<phi>" nitpick oops

lemma IC1a: "Int_1a \<phi> \<Longrightarrow> Cl_1b \<phi>\<^sup>d" by (smt MULT_a_def ADDI_b_def MONO_def MONO_MULTa dual_def conn)
lemma IC1b: "Int_1b \<phi> \<Longrightarrow> Cl_1a \<phi>\<^sup>d" unfolding MULT_b_def ADDI_a_def dual_def conn by auto
lemma IC1:  "Int_1 \<phi>  \<Longrightarrow> Cl_1 \<phi>\<^sup>d" unfolding MULT_def ADDI_def dual_def conn by simp
lemma IC2:  "Int_2 \<phi>  \<Longrightarrow> Cl_2 \<phi>\<^sup>d" unfolding dEXP_def EXP_def dual_def conn by blast
lemma IC3:  "Int_3 \<phi>  \<Longrightarrow> Cl_3 \<phi>\<^sup>d" unfolding dNOR_def NOR_def dual_def conn by simp
lemma IC4:  "Int_4 \<phi>  \<Longrightarrow> Cl_4 \<phi>\<^sup>d" unfolding IDEM_def IDEM_def dual_def conn by simp
lemma IC4': "Int_4' \<phi> \<Longrightarrow> Cl_4' \<phi>\<^sup>d" unfolding IDEMa_def IDEMb_def dual_def conn by metis
lemma IC5:  "Int_5 \<phi>  \<Longrightarrow> Cl_5 \<phi>\<^sup>d" unfolding NOR_def dNOR_def dual_def conn by simp

lemma CI1a: "Cl_1a \<phi>  \<Longrightarrow> Int_1b \<phi>\<^sup>d" proof -
  assume cl1a: "Cl_1a \<phi>" 
  { fix A B
    have "\<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>(A \<^bold>\<and> B)) \<^bold>\<approx> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>B)" unfolding conn by simp
    moreover from cl1a have "\<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>B)) \<^bold>\<preceq> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A \<^bold>\<or> \<^bold>\<midarrow>B)" using ADDI_a_def conn by metis
    ultimately have "\<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>A)) \<^bold>\<and> \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>B)) \<^bold>\<preceq> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>(A \<^bold>\<and> B))" unfolding conn by simp
    hence "(\<phi>\<^sup>d A) \<^bold>\<and> (\<phi>\<^sup>d B) \<^bold>\<preceq> (\<phi>\<^sup>d (A \<^bold>\<and> B))" unfolding dual_def by simp
  } thus "Int_1b \<phi>\<^sup>d" using MULT_b_def by blast
qed
lemma CI1b: "Cl_1b \<phi> \<Longrightarrow> Int_1a \<phi>\<^sup>d" by (metis IC1a MONO_ADDIb MONO_MULTa)
lemma CI1:  "Cl_1 \<phi>  \<Longrightarrow> Int_1 \<phi>\<^sup>d" by (simp add: CI1a CI1b PC1 PI1)
lemma CI2:  "Cl_2 \<phi>  \<Longrightarrow> Int_2 \<phi>\<^sup>d" unfolding EXP_def dEXP_def dual_def conn by metis
lemma CI3:  "Cl_3 \<phi>  \<Longrightarrow> Int_3 \<phi>\<^sup>d" unfolding NOR_def dNOR_def dual_def conn by simp
lemma CI4:  "Cl_4 \<phi>  \<Longrightarrow> Int_4 \<phi>\<^sup>d" unfolding IDEM_def IDEM_def dual_def conn by simp
lemma CI4': "Cl_4' \<phi> \<Longrightarrow> Int_4' \<phi>\<^sup>d" unfolding IDEMa_def IDEMb_def dual_def conn by metis
lemma CI5:  "Cl_5 \<phi>  \<Longrightarrow> Int_5 \<phi>\<^sup>d" unfolding dNOR_def NOR_def dual_def conn by simp


subsection \<open>Frontier and border\<close>

subsubsection \<open>Frontier conditions\<close>

definition "Fr_1a \<phi> \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> (A \<^bold>\<and> B) \<^bold>\<and> (\<phi> A \<^bold>\<or> \<phi> B)"
definition "Fr_1b \<phi> \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<and> B) \<^bold>\<succeq> (A \<^bold>\<and> B) \<^bold>\<and> (\<phi> A \<^bold>\<or> \<phi> B)"
definition "Fr_1 \<phi>  \<equiv> \<forall>A B. (A \<^bold>\<and> B) \<^bold>\<and> \<phi>(A \<^bold>\<and> B) \<^bold>\<approx> (A \<^bold>\<and> B) \<^bold>\<and> (\<phi> A \<^bold>\<or> \<phi> B)"
definition "Fr_2 \<phi> \<equiv> \<forall>A. \<phi> A \<^bold>\<approx> \<phi>(\<^bold>\<midarrow>A)"
abbreviation "Fr_3 \<phi> \<equiv> NOR \<phi>"
definition "Fr_4 \<phi> \<equiv> \<forall>A. \<phi>(\<phi> A) \<^bold>\<preceq> (\<phi> A)"

definition "Fr_5 \<phi> \<equiv> \<forall>A. \<phi>(\<phi>(\<phi> A)) \<^bold>\<approx> \<phi>(\<phi> A)"
definition "Fr_6 \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> (\<phi> A \<^bold>\<preceq> B \<^bold>\<or> \<phi> B)"

text\<open>\noindent{@{text "\<phi>"} is a topological frontier operator (@{text "\<FF>(\<phi>)"}) iff it satisfies conditions 1-4
(cf. @{cite Zarycki1}). This is also shown consistent by generating a non-trivial model.}\<close>
abbreviation "\<FF> \<phi>  \<equiv> Fr_1 \<phi> \<and> Fr_2 \<phi> \<and> Fr_3 \<phi> \<and> Fr_4 \<phi>"
lemma "\<FF> \<phi>" nitpick[satisfy, card w=3] oops (*model found: characterization is consistent*)

text\<open>\noindent{We now verify some useful properties of the frontier operator.}\<close>
lemma PF1: "Fr_1 \<phi> = (Fr_1a \<phi> \<and> Fr_1b \<phi>)" unfolding Fr_1_def Fr_1a_def Fr_1b_def by meson
lemma PF5: "Fr_1 \<phi> \<Longrightarrow> Fr_4 \<phi> \<Longrightarrow> Fr_5 \<phi>" proof -
  assume fr1: "Fr_1 \<phi>" and fr4: "Fr_4 \<phi>"
  { fix A
    from fr1 have "(\<phi>(\<phi> A) \<^bold>\<and> (\<phi> A)) \<^bold>\<and> \<phi>(\<phi>(\<phi> A) \<^bold>\<and> (\<phi> A)) \<^bold>\<approx> (\<phi>(\<phi> A) \<^bold>\<and> (\<phi> A)) \<^bold>\<and> (\<phi>(\<phi>(\<phi> A)) \<^bold>\<or> \<phi>(\<phi> A))" by (simp add: Fr_1_def)
    moreover have r1: "\<phi>(\<phi> A) \<^bold>\<and> (\<phi> A) \<^bold>\<approx> \<phi>(\<phi> A)" using meet_char Fr_4_def fr4 by simp
    moreover have r2: "\<phi>(\<phi>(\<phi> A)) \<^bold>\<or> \<phi>(\<phi> A) \<^bold>\<approx> \<phi>(\<phi> A)" using join_char Fr_4_def fr4 by simp
    ultimately have "(\<phi>(\<phi> A) \<^bold>\<and> (\<phi> A)) \<^bold>\<and> \<phi>(\<phi>(\<phi> A)) \<^bold>\<approx> (\<phi>(\<phi> A) \<^bold>\<and> (\<phi> A)) \<^bold>\<and> \<phi>(\<phi> A)" unfolding conn by auto
    hence "\<phi>(\<phi>(\<phi> A)) \<^bold>\<approx> \<phi>(\<phi> A)" using r1 r2 conn by auto
  } thus ?thesis by (simp add: Fr_5_def)
qed
lemma PF6: "Fr_1b \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Fr_6 \<phi>" proof -
  assume fr1b: "Fr_1b \<phi>" and fr2: "Fr_2 \<phi>"
  { fix A B
    have "\<phi>(\<^bold>\<midarrow>(A \<^bold>\<or> B)) \<^bold>\<approx> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B)" unfolding conn by simp
    hence aux: "\<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B) \<^bold>\<approx> \<phi>(A \<^bold>\<or> B)" by (metis (mono_tags) Fr_2_def fr2)
    from fr1b have "(\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B) \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B) \<^bold>\<succeq> (\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B) \<^bold>\<and> (\<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>B))" using Fr_1b_def by metis
    hence "A \<^bold>\<or> B \<^bold>\<or> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B) \<^bold>\<preceq> A \<^bold>\<or> B \<^bold>\<or> (\<^bold>\<midarrow>(\<phi> A) \<^bold>\<and> \<^bold>\<midarrow>(\<phi> B))" using Fr_2_def fr2 conn by auto
    hence "\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B \<^bold>\<and> \<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B) \<^bold>\<preceq> \<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B \<^bold>\<and> \<^bold>\<midarrow>(\<phi> A) \<^bold>\<and> \<^bold>\<midarrow>(\<phi> B)" unfolding conn by blast
    hence "A \<^bold>\<or> B \<^bold>\<or> \<phi>(A \<^bold>\<or> B) \<^bold>\<succeq> A \<^bold>\<or> B \<^bold>\<or> (\<phi> A) \<^bold>\<or> (\<phi> B)" using aux unfolding conn by blast
    hence "A \<^bold>\<preceq> B \<longrightarrow> B \<^bold>\<or> \<phi>(A \<^bold>\<or> B) \<^bold>\<succeq> B \<^bold>\<or> (\<phi> A) \<^bold>\<or> (\<phi> B)" unfolding conn by auto
    hence "A \<^bold>\<preceq> B \<longrightarrow> B \<^bold>\<or> (\<phi> B) \<^bold>\<succeq> B \<^bold>\<or> (\<phi> A) \<^bold>\<or> (\<phi> B)" using join_char unfolding conn by simp
    hence "A \<^bold>\<preceq> B \<longrightarrow> (\<phi> A) \<^bold>\<preceq> B \<^bold>\<or> (\<phi> B)" unfolding conn by simp
  } thus "Fr_6 \<phi>" by (simp add: Fr_6_def)
qed


subsubsection \<open>Border conditions\<close>

definition "Br_1 \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<approx> (A \<^bold>\<and> \<phi> B) \<^bold>\<or> (B \<^bold>\<and> \<phi> A)"
definition "Br_2 \<phi> \<equiv> (\<phi> \<^bold>\<top>) \<^bold>\<approx> \<^bold>\<bottom>"
definition "Br_3 \<phi> \<equiv> \<forall>A. \<phi>(\<phi>\<^sup>d A) \<^bold>\<preceq> A"

definition "Br_4 \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> A \<^bold>\<and> (\<phi> B) \<^bold>\<preceq> \<phi> A"
definition "Br_5a \<phi> \<equiv> \<forall>A. \<phi>(\<phi>\<^sup>d A) \<^bold>\<preceq> \<phi> A"
definition "Br_5b \<phi> \<equiv> \<forall>A. \<phi> A \<^bold>\<preceq> A"
definition "Br_5c \<phi> \<equiv> \<forall>A. A \<^bold>\<preceq> \<phi>\<^sup>d A"
definition "Br_5d \<phi> \<equiv> \<forall>A. \<phi>\<^sup>d A \<^bold>\<preceq> \<phi>\<^sup>d(\<phi> A)"
abbreviation "Br_6 \<phi> \<equiv> IDEM \<phi>"
abbreviation "Br_7 \<phi> \<equiv> ADDI_a \<phi>"
abbreviation "Br_8 \<phi> \<equiv> MULT_b \<phi>"
definition "Br_9 \<phi> \<equiv> \<forall>A B. \<phi>(A \<^bold>\<and> B) \<^bold>\<preceq> (\<phi> A) \<^bold>\<or> (\<phi> B)"
definition "Br_10 \<phi> \<equiv> \<forall>A. \<phi>(\<^bold>\<midarrow>(\<phi> A) \<^bold>\<and> \<phi>\<^sup>d A) \<^bold>\<approx> \<^bold>\<bottom>"

text\<open>\noindent{@{text "\<phi>"} is a topological border operator (@{text "\<BB>(\<phi>)"}) iff it satisfies conditions 1-3
(cf. @{cite Zarycki1}). This is also shown consistent.}\<close>
abbreviation "\<BB> \<phi>  \<equiv> Br_1 \<phi> \<and> Br_2 \<phi> \<and> Br_3 \<phi>"
lemma "\<BB> \<phi>" nitpick[satisfy, card w=3] oops (*model found: characterization is consistent*)

text\<open>\noindent{We now verify some useful properties of the border operator.}\<close>
lemma PB4: "Br_1 \<phi> \<Longrightarrow> Br_4 \<phi>" proof -
  assume br1: "Br_1 \<phi>"
  { fix A B
    have aux: "\<phi>(A \<^bold>\<and> B) \<^bold>\<approx> (A \<^bold>\<and> \<phi> B) \<^bold>\<or> (B \<^bold>\<and> \<phi> A)" using br1 Br_1_def by simp
    { assume "A \<^bold>\<preceq> B"
      hence "\<phi>(A \<^bold>\<and> B) \<^bold>\<approx> \<phi> A" using meet_char unfolding conn by simp
      hence "\<phi> A \<^bold>\<approx> (A \<^bold>\<and> \<phi> B) \<^bold>\<or> (B \<^bold>\<and> \<phi> A)" using aux by auto
      hence "A \<^bold>\<and> \<phi> B \<^bold>\<preceq> \<phi> A" unfolding conn by auto
    } hence "A \<^bold>\<preceq> B \<longrightarrow> A \<^bold>\<and> \<phi> B \<^bold>\<preceq> \<phi> A" by (rule impI)
  } thus "Br_4 \<phi>"  by (simp add: Br_4_def)
qed
lemma PB5b: "Br_1 \<phi> \<Longrightarrow> Br_5b \<phi>" proof -
  assume br1: "Br_1 \<phi>"
  { fix A
    from br1 have aux: "\<phi>(A \<^bold>\<and> A) \<^bold>\<approx> (A \<^bold>\<and> \<phi> A) \<^bold>\<or> (A \<^bold>\<and> \<phi> A)" unfolding Br_1_def by blast
    hence "\<phi> A \<^bold>\<approx> (A \<^bold>\<and> \<phi> A)" unfolding conn by metis
    hence "\<phi> A \<^bold>\<preceq> A" unfolding conn by blast
  } thus "Br_5b \<phi>" using Br_5b_def by blast 
qed
lemma PB5c: "Br_1 \<phi> \<Longrightarrow> Br_5c \<phi>" using Br_5b_def Br_5c_def PB5b dual_def unfolding conn by force 
lemma PB5a: "Br_1 \<phi> \<Longrightarrow> Br_3 \<phi> \<Longrightarrow> Br_5a \<phi>" proof -
  assume br1: "Br_1 \<phi>" and br3: "Br_3 \<phi>"
  hence br5c: "Br_5c \<phi>" using PB5c by simp
  { fix A
    have "A \<^bold>\<and> \<phi>(\<phi>\<^sup>d A) \<^bold>\<preceq> \<phi> A" by (metis br5c Br_4_def Br_5c_def PB4 br1)
    hence "\<phi>(\<phi>\<^sup>d A) \<^bold>\<preceq> \<phi> A" using Br_3_def br3 unfolding conn by metis
  } thus "Br_5a \<phi>" using Br_5a_def by simp 
qed
lemma PB5d: "Br_1 \<phi> \<Longrightarrow> Br_3 \<phi> \<Longrightarrow> Br_5d \<phi>" proof -
  assume br1: "Br_1 \<phi>" and br3: "Br_3 \<phi>"
  hence br5a: "Br_5a \<phi>" using PB5a by simp
  { fix A
    from br5a have "\<phi>(\<phi>\<^sup>d(\<^bold>\<midarrow>A)) \<^bold>\<preceq> \<phi>(\<^bold>\<midarrow>A)" unfolding Br_5a_def by simp
    hence "\<^bold>\<midarrow>\<phi>(\<^bold>\<midarrow>A) \<^bold>\<preceq> \<^bold>\<midarrow>\<phi>(\<phi>\<^sup>d(\<^bold>\<midarrow>A))" unfolding conn by blast
    hence "\<phi>\<^sup>d A \<^bold>\<preceq> \<phi>\<^sup>d(\<phi> A)" unfolding dual_def conn by simp
  } thus "Br_5d \<phi>" using Br_5d_def by simp 
qed
lemma PB6: "Br_1 \<phi> \<Longrightarrow> Br_6 \<phi>" by (smt Br_4_def Br_5b_def IDEM_def PB4 PB5b conn)
lemma PB7: "Br_1 \<phi> \<Longrightarrow> Br_7 \<phi>" using Br_4_def Br_5b_def ADDI_a_def PB4 PB5b unfolding conn by smt
lemma PB8: "Br_1 \<phi> \<Longrightarrow> Br_8 \<phi>" using Br_1_def Br_5b_def MULT_b_def PB5b unfolding conn by metis
lemma PB9: "Br_1 \<phi> \<Longrightarrow> Br_9 \<phi>" unfolding Br_1_def Br_9_def conn by simp
lemma PB10: "Br_1 \<phi> \<Longrightarrow> Br_3 \<phi> \<Longrightarrow> Br_10 \<phi>" proof - \<comment>\<open> proof automagically generated \<close>
  assume a1: "Br_3 \<phi>"
  assume a2: "Br_1 \<phi>"
  { fix bb :: "w \<Rightarrow> bool" and ww :: w
    have "\<forall>p pa w pb. ((pb p w \<or> pb pa w) \<or> \<not>pb (pa \<^bold>\<and> p) w) \<or> \<not>Br_9 pb"
      by (metis Br_9_def join_def) (* 20 ms *)
    then have "(\<phi> (((\<phi>\<^sup>c) \<^bold>\<sqinter> (\<phi>\<^sup>d)) bb) ww) \<and> (\<^bold>\<bottom> ww) \<or> \<not>(\<phi> (((\<phi>\<^sup>c) \<^bold>\<sqinter> (\<phi>\<^sup>d)) bb) ww) \<and> \<not>(\<^bold>\<bottom> ww)"
      using a2 a1 by (metis (no_types) Br_5a_def Br_5b_def Br_5d_def PB5a PB5b PB5d PB9 bottom_def compl_def dual_def meet_def) (* 86 ms *)
  } then show ?thesis unfolding Br_10_def by blast (* 1 ms *)
qed


subsubsection \<open>Relation with closure and interior\<close>

text\<open>\noindent{We define and verify some conversion operators useful to derive border and frontier operators from
closure/interior operators and also between each other.}\<close>

text\<open>\noindent{Frontier operator as derived from interior.}\<close>
definition Fr_int::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<F>\<^sub>I") where "\<F>\<^sub>I \<I> \<equiv> \<lambda>A. \<^bold>\<midarrow>(\<I> A) \<^bold>\<and> \<I>\<^sup>d A" 
lemma FI1: "Int_1 \<phi> \<Longrightarrow> Int_2 \<phi> \<Longrightarrow>  Fr_1(\<F>\<^sub>I \<phi>)" using EXP_def Fr_1_def Fr_int_def IC2 MULT_def conn by auto
lemma FI2: "Fr_2(\<F>\<^sub>I \<phi>)" using Fr_2_def Fr_int_def dual_def dual_symm unfolding conn by smt 
lemma FI3: "Int_3 \<phi> \<Longrightarrow> Fr_3(\<F>\<^sub>I \<phi>)" using NOR_def Fr_int_def IC3 unfolding conn by auto  
lemma FI4: "Int_1a \<phi> \<Longrightarrow> Int_2 \<phi>  \<Longrightarrow> Int_4 \<phi> \<Longrightarrow> Fr_4(\<F>\<^sub>I \<phi>)" unfolding Fr_int_def Fr_4_def dual_def conn by (smt Int_9_def MONO_MULTa PI9)

text\<open>\noindent{Frontier operator as derived from closure.}\<close>
definition Fr_cl::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<F>\<^sub>C") where "\<F>\<^sub>C \<C> \<equiv> \<lambda>A. (\<C> A) \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)" 
lemma FC1: "Cl_1 \<phi> \<Longrightarrow> Cl_2 \<phi> \<Longrightarrow>  Fr_1(\<F>\<^sub>C \<phi>)" using CI1 EXP_def Fr_1_def Fr_cl_def MULT_def dual_def unfolding conn by smt
lemma FC2: "Fr_2(\<F>\<^sub>C \<phi>)" using Fr_2_def Fr_cl_def dual_def dual_symm unfolding conn by smt
lemma FC3: "Cl_3 \<phi> \<Longrightarrow> Fr_3(\<F>\<^sub>C \<phi>)" unfolding NOR_def Fr_cl_def conn by simp 
lemma FC4: "Cl_1b \<phi> \<Longrightarrow> Cl_2 \<phi> \<Longrightarrow> Cl_4 \<phi> \<Longrightarrow> Fr_4(\<F>\<^sub>C \<phi>)" using Cl_8_def MONO_ADDIb PC8 unfolding Fr_cl_def Fr_4_def conn by blast
  
text\<open>\noindent{Frontier operator as derived from border.}\<close>
definition Fr_br::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<F>\<^sub>B") where "\<F>\<^sub>B \<B> \<equiv> \<lambda>A. \<B> A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)"
lemma FB1: "Br_1 \<phi> \<Longrightarrow>  Fr_1(\<F>\<^sub>B \<phi>)" unfolding Fr_br_def Fr_1_def using Br_1_def Br_5b_def PB5b conn by smt
lemma FB2: "Fr_2(\<F>\<^sub>B \<phi>)" unfolding Fr_br_def Fr_2_def conn by auto
lemma FB3: "Br_1 \<phi> \<Longrightarrow> Br_2 \<phi> \<Longrightarrow>  Fr_3(\<F>\<^sub>B \<phi>)" using Br_2_def Br_5b_def PB5b unfolding Fr_br_def NOR_def conn by force
lemma FB4: "Br_1 \<phi> \<Longrightarrow> Br_3 \<phi> \<Longrightarrow>  Fr_4(\<F>\<^sub>B \<phi>)" proof -
  assume br1: "Br_1 \<phi>" and br3: "Br_3 \<phi>"
  { fix A 
   have "(\<F>\<^sub>B \<phi>) ((\<F>\<^sub>B \<phi>) A) = \<phi>(\<phi> A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A)) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>(\<phi> A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A)))" by (simp add: Fr_br_def conn)
   also have "... = \<phi>(\<phi> A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A)) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>(\<phi> A) \<^bold>\<and> \<phi>\<^sup>d A)" by (simp add: dual_def conn)
   also from br1 br3 have "... = \<phi>(\<phi> A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A)) \<^bold>\<or> \<^bold>\<bottom>" using Br_10_def PB10 by metis
   finally have "(\<F>\<^sub>B \<phi>) ((\<F>\<^sub>B \<phi>) A) \<^bold>\<approx> \<phi>(\<phi> A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A))" unfolding conn by simp
   hence "(\<F>\<^sub>B \<phi>) ((\<F>\<^sub>B \<phi>) A) \<^bold>\<preceq> (\<F>\<^sub>B \<phi>) A" using Br_5b_def Fr_br_def PB5b br1 by fastforce
  } thus "Fr_4(\<F>\<^sub>B \<phi>)" using Fr_4_def by blast
qed

text\<open>\noindent{Border operator as derived from interior.}\<close>
definition Br_int::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<B>\<^sub>I") where "\<B>\<^sub>I \<I> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<I> A)"
lemma BI1: "Int_1 \<phi> \<Longrightarrow>  Br_1 (\<B>\<^sub>I \<phi>)" using Br_1_def Br_int_def MULT_def conn by auto
lemma BI2: "Int_3 \<phi> \<Longrightarrow>  Br_2 (\<B>\<^sub>I \<phi>)" by (simp add: Br_2_def Br_int_def dNOR_def conn)
lemma BI3: "Int_1a \<phi> \<Longrightarrow> Int_4 \<phi> \<Longrightarrow> Br_3 (\<B>\<^sub>I \<phi>)" unfolding Br_int_def Br_3_def dual_def by (smt Int_9_def MONO_MULTa PI9 conn)

text\<open>\noindent{Border operator as derived from closure.}\<close>
definition Br_cl::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<B>\<^sub>C")  where "\<B>\<^sub>C \<C> \<equiv> \<lambda>A. A \<^bold>\<and> \<C>(\<^bold>\<midarrow>A)"
lemma BC1: "Cl_1 \<phi> \<Longrightarrow>  Br_1(\<B>\<^sub>C \<phi>)" using Br_1_def Br_cl_def CI1 MULT_def dual_def unfolding conn by smt
lemma BC2: "Cl_3 \<phi> \<Longrightarrow>  Br_2(\<B>\<^sub>C \<phi>)" using Br_2_def Br_cl_def CI3 dNOR_def dual_def unfolding conn by auto
lemma BC3: "Cl_1b \<phi> \<Longrightarrow> Cl_4 \<phi> \<Longrightarrow> Br_3 (\<B>\<^sub>C \<phi>)" unfolding Br_cl_def Br_3_def dual_def conn by (metis (mono_tags, lifting) Cl_9_def PC9)

text\<open>\noindent{Note that the previous two conversion functions are related:}\<close>
lemma BI_BC_rel: "(\<B>\<^sub>I \<phi>) = \<B>\<^sub>C(\<phi>\<^sup>d)" by (simp add: Br_cl_def Br_int_def dual_def conn)

text\<open>\noindent{Border operator as derived from frontier.}\<close>
definition Br_fr::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<B>\<^sub>F") where "\<B>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<and> (\<F> A)"
lemma BF1: "Fr_1 \<phi> \<Longrightarrow> Br_1(\<B>\<^sub>F \<phi>)" using Br_1_def Br_fr_def Fr_1_def conn by auto 
lemma BF2: "Fr_2 \<phi> \<Longrightarrow> Fr_3 \<phi> \<Longrightarrow> Br_2(\<B>\<^sub>F \<phi>)" using Br_2_def Br_fr_def Fr_2_def NOR_def unfolding conn by fastforce
lemma BF3: "Fr_1b \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Fr_4 \<phi> \<Longrightarrow> Br_3(\<B>\<^sub>F \<phi>)" proof - 
  assume fr1b: "Fr_1b \<phi>" and fr2: "Fr_2 \<phi>" and fr4: "Fr_4 \<phi>"
  { fix A
    from fr1b fr2 have "let M= \<^bold>\<midarrow>A \<^bold>\<and> \<phi> A ; N= \<phi> A in M \<^bold>\<preceq> N \<longrightarrow> (\<phi> M \<^bold>\<preceq> N \<^bold>\<or> \<phi> N)" using PF1 PF6 by (simp add: Fr_6_def)
    hence "\<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A) \<^bold>\<preceq> \<phi> A \<^bold>\<or> \<phi>(\<phi> A)" unfolding conn by meson
    hence "\<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A) \<^bold>\<preceq> \<phi> A" using Fr_4_def fr4 unfolding conn by metis
    hence aux: "\<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A) \<^bold>\<and> \<^bold>\<midarrow>(\<phi> A) \<^bold>\<approx> \<^bold>\<bottom>" unfolding conn by blast
    have "(\<B>\<^sub>F \<phi>)((\<B>\<^sub>F \<phi>)\<^sup>d A) = \<^bold>\<midarrow>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A)) \<^bold>\<and> \<phi>(\<^bold>\<midarrow>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A)))" unfolding Br_fr_def dual_def by simp 
    also have "... = (A \<^bold>\<or> \<^bold>\<midarrow>\<phi> A) \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A)" using Fr_2_def fr2 unfolding conn by force
    also have "... = (A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A)) \<^bold>\<or> (\<^bold>\<midarrow>\<phi> A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A))" unfolding conn by auto
    also have "... = (A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A))" using aux unfolding conn by blast
    finally have "(\<B>\<^sub>F \<phi>)((\<B>\<^sub>F \<phi>)\<^sup>d A) = A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi> A)" unfolding Br_fr_def dual_def conn by simp
  } thus "Br_3(\<B>\<^sub>F \<phi>)" unfolding Br_3_def Br_fr_def conn by meson
qed

text\<open>\noindent{Interior operator as derived from border.}\<close>
definition Int_br::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<I>\<^sub>B") where "\<I>\<^sub>B \<B> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<B> A)"
lemma IB1: "Br_1 \<phi> \<Longrightarrow> Int_1(\<I>\<^sub>B \<phi>)" using Br_1_def MULT_def Int_br_def conn by auto 
lemma IB2: "Int_2(\<I>\<^sub>B \<phi>)" by (simp add: dEXP_def Int_br_def conn)
lemma IB3: "Br_2 \<phi> \<Longrightarrow> Int_3(\<I>\<^sub>B \<phi>)" by (simp add: Br_2_def dNOR_def Int_br_def conn)
lemma IB4: "Br_1 \<phi> \<Longrightarrow> Br_3 \<phi> \<Longrightarrow> Int_4(\<I>\<^sub>B \<phi>)" unfolding Int_br_def IDEM_def conn
  using Br_1_def Br_5c_def Br_5d_def PB5c PB5d dual_def unfolding conn by (metis (full_types))

text\<open>\noindent{Interior operator as derived from frontier.}\<close>
definition Int_fr::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<I>\<^sub>F") where "\<I>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<leftharpoonup> (\<F> A)"
lemma IF1a: "Fr_1b \<phi> \<Longrightarrow> Int_1a(\<I>\<^sub>F \<phi>)" using Fr_1b_def MULT_a_def Int_fr_def conn by auto
lemma IF1b: "Fr_1a \<phi> \<Longrightarrow> Int_1b(\<I>\<^sub>F \<phi>)" using Fr_1a_def MULT_b_def Int_fr_def conn by auto
lemma IF1: "Fr_1 \<phi> \<Longrightarrow> Int_1(\<I>\<^sub>F \<phi>)" by (simp add: IF1a IF1b PF1 PI1)
lemma IF2: "Int_2(\<I>\<^sub>F \<phi>)" by (simp add: dEXP_def Int_fr_def conn)
lemma IF3: "Fr_2 \<phi> \<Longrightarrow> Fr_3 \<phi> \<Longrightarrow> Int_3(\<I>\<^sub>F \<phi>)" using BF2 Br_2_def Br_fr_def dNOR_def Int_fr_def unfolding conn by auto
lemma IF4: "Fr_1a \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Fr_4 \<phi> \<Longrightarrow> Int_4(\<I>\<^sub>F \<phi>)"
  using Fr_1a_def Fr_2_def Fr_4_def unfolding Int_fr_def IDEM_def conn by metis  

text\<open>\noindent{Closure operator as derived from border.}\<close>
definition Cl_br::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<C>\<^sub>B") where "\<C>\<^sub>B \<B> \<equiv> \<lambda>A. A \<^bold>\<or> \<B>(\<^bold>\<midarrow>A)"
lemma CB1: "Br_1 \<phi> \<Longrightarrow> Cl_1(\<C>\<^sub>B \<phi>)" proof -
 assume br1: "Br_1 \<phi>"
  { fix A B
    have "(\<C>\<^sub>B \<phi>) (A \<^bold>\<or> B) = A \<^bold>\<or> B \<^bold>\<or> \<phi>(\<^bold>\<midarrow>(A \<^bold>\<or> B))" by (simp add: Cl_br_def conn)
    also have "... = A \<^bold>\<or> B \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<^bold>\<midarrow>B)" unfolding conn by simp
    also have "... = A \<^bold>\<or> B \<^bold>\<or> (\<^bold>\<midarrow>A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>B)) \<^bold>\<or> (\<^bold>\<midarrow>B \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A))" using Br_1_def br1 unfolding conn by auto
    also have "... = A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> B \<^bold>\<or> \<phi>(\<^bold>\<midarrow>B)" unfolding conn by auto
    also have "... = (\<C>\<^sub>B \<phi>) A \<^bold>\<or> (\<C>\<^sub>B \<phi>) B" by (simp add: Cl_br_def conn)
    finally have "(\<C>\<^sub>B \<phi>)(A \<^bold>\<or> B) = (\<C>\<^sub>B \<phi>) A \<^bold>\<or> (\<C>\<^sub>B \<phi>) B" unfolding Cl_br_def by blast
  } thus "Cl_1(\<C>\<^sub>B \<phi>)" unfolding ADDI_def Cl_br_def by simp
qed
lemma CB2: "Cl_2(\<C>\<^sub>B \<phi>)" by (simp add: EXP_def Cl_br_def conn) 
lemma CB3: "Br_2 \<phi> \<Longrightarrow> Cl_3(\<C>\<^sub>B \<phi>)" using Br_2_def Cl_br_def IC3 dNOR_def dual_def dual_symm unfolding conn by smt
lemma CB4: "Br_1 \<phi> \<Longrightarrow> Br_3 \<phi> \<Longrightarrow> Cl_4(\<C>\<^sub>B \<phi>)" proof -
 assume br1: "Br_1 \<phi>" and br3: "Br_3 \<phi>"
  { fix A 
   have "(\<C>\<^sub>B \<phi>) ((\<C>\<^sub>B \<phi>) A) = A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>(A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A)))" by (simp add: Cl_br_def conn)
   also have "... = A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A \<^bold>\<and> \<phi>\<^sup>d A)" unfolding dual_def conn by simp
   also have "... = A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A) \<^bold>\<or> (\<^bold>\<midarrow>A \<^bold>\<and> \<phi>(\<phi>\<^sup>d A)) \<^bold>\<or> (\<^bold>\<midarrow>A \<^bold>\<and> \<phi>(\<^bold>\<midarrow>A))" unfolding dual_def using Br_1_def br1 conn by auto
   also have "... = A \<^bold>\<or> \<phi>(\<^bold>\<midarrow>A)" using Br_3_def br3 unfolding conn by metis
   finally have "(\<C>\<^sub>B \<phi>) ((\<C>\<^sub>B \<phi>) A) = (\<C>\<^sub>B \<phi>) A" unfolding Cl_br_def by blast
  } thus "Cl_4(\<C>\<^sub>B \<phi>)" unfolding IDEM_def Cl_br_def by simp
qed

text\<open>\noindent{Closure operator as derived from frontier.}\<close>
definition Cl_fr::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<C>\<^sub>F") where "\<C>\<^sub>F \<F> \<equiv> \<lambda>A. A \<^bold>\<or> (\<F> A)"
lemma CF1b: "Fr_1b \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Cl_1b(\<C>\<^sub>F \<phi>)" using Cl_fr_def Fr_6_def MONO_def MONO_ADDIb PF6 unfolding conn by auto
lemma CF1a: "Fr_1a \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Cl_1a(\<C>\<^sub>F \<phi>)" proof -
  have aux: "Fr_2 \<phi> \<Longrightarrow> (\<I>\<^sub>F \<phi>)\<^sup>d = (\<C>\<^sub>F \<phi>)" by (simp add: Cl_fr_def Fr_2_def Int_fr_def dual_def conn)
  hence "Fr_1a \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Cl_1a(\<I>\<^sub>F \<phi>)\<^sup>d" using IC1b IF1b by blast
  thus "Fr_1a \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Cl_1a(\<C>\<^sub>F \<phi>)" using ADDI_a_def aux unfolding conn by simp
qed
lemma CF1: "Fr_1 \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Cl_1(\<C>\<^sub>F \<phi>)" by (simp add: CF1a CF1b PC1 PF1)
lemma CF2: "Cl_2(\<C>\<^sub>F \<phi>)" by (simp add: EXP_def Cl_fr_def conn)
lemma CF3: "Fr_3 \<phi> \<Longrightarrow> Cl_3(\<C>\<^sub>F \<phi>)" by (simp add: Cl_fr_def NOR_def conn)
lemma CF4: "Fr_1a \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Fr_4 \<phi> \<Longrightarrow> Cl_4(\<C>\<^sub>F \<phi>)" proof -
  have aux: "Fr_2 \<phi> \<Longrightarrow> (\<I>\<^sub>F \<phi>)\<^sup>d = (\<C>\<^sub>F \<phi>)"  by (simp add: Cl_fr_def Fr_2_def Int_fr_def dual_def conn)
  hence "Fr_1a \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Fr_4 \<phi> \<Longrightarrow> Cl_4(\<I>\<^sub>F \<phi>)\<^sup>d" using IC4 IF4 by blast
  thus "Fr_1a \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> Fr_4 \<phi> \<Longrightarrow> Cl_4(\<C>\<^sub>F \<phi>)" by (simp add: aux)
qed


subsubsection \<open>Infinitary conditions\<close>

text\<open>\noindent{We define the essential infinitary conditions for the closure and interior operators (entailing infinite
additivity and multiplicativity resp.). Observe that the other direction is implied by monotonicity (MONO).}\<close>
abbreviation "Cl_inf \<phi> \<equiv> iADDI_a(\<phi>)"
abbreviation "Int_inf \<phi> \<equiv> iMULT_b(\<phi>)"

text\<open>\noindent{There exists indeed a condition on frontier operators responsible for the infinitary conditions above:}\<close>
definition "Fr_inf \<phi> \<equiv> \<forall>S. \<^bold>\<And>S \<^bold>\<and> \<phi>(\<^bold>\<And>S) \<^bold>\<preceq> \<^bold>\<And>S \<^bold>\<and> \<^bold>\<Or>Ra[\<phi>|S]"

lemma CF_inf: "Fr_2 \<phi> \<Longrightarrow> Fr_inf \<phi> \<Longrightarrow> Cl_inf(\<C>\<^sub>F \<phi>)" unfolding iADDI_a_def  Fr_inf_def 
  by (smt Cl_fr_def Fr_2_def Ra_restr_ex compl_def dom_compl_def2 iDM_b join_def meet_def supremum_def)
lemma IF_inf: "Fr_inf \<phi> \<Longrightarrow> Int_inf(\<I>\<^sub>F \<phi>)" unfolding Fr_inf_def iMULT_b_def Int_fr_def Ra_restr_all
  by (metis (mono_tags, hide_lams) diff_def infimum_def meet_def pfunRange_restr_def supremum_def)

text\<open>\noindent{This condition is indeed strong enough to entail closure of the fixed-point predicates under infimum/supremum.}\<close>
lemma fp_IF_inf_closed: "Fr_inf \<phi> \<Longrightarrow> infimum_closed (fp (\<I>\<^sub>F \<phi>))" by (metis (full_types) IF2 IF_inf Ra_restr_all dEXP_def iMULT_b_def infimum_def)
lemma fp_CF_sup_closed: "Fr_inf \<phi> \<Longrightarrow> Fr_2 \<phi> \<Longrightarrow> supremum_closed (fp (\<C>\<^sub>F \<phi>))" by (metis (full_types) CF2 CF_inf EXP_def Ra_restr_ex iADDI_a_def supremum_def)

end
