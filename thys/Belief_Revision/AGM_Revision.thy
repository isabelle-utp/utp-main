(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : AGM Theory
 * Version         : 1.0
 *
 * Authors         : Valentin Fouillard, Safouan Taha, Frederic Boulanger
                     and Nicolas Sabouret
 *
 * This file       : AGM revision
 *
 * Copyright (c) 2021 Université Paris Saclay, France
 *
 ******************************************************************************\<close>

theory AGM_Revision

imports AGM_Contraction

begin
(*>*)

section \<open>Revisions\<close>
text \<open>The third operator of belief change introduce by the AGM framework is the revision. In revision a sentence 
@{term \<open>\<phi>\<close>} is added to the belief set  @{term \<open>K\<close>} in such a way that other sentences 
of @{term \<open>K\<close>} are removed if needed so that @{term \<open>K\<close>} is consistent\<close>

subsection \<open>AGM revision postulates\<close>

text \<open>The revision operator is denoted by the symbol @{text \<open>\<^bold>*\<close>} and respect the following conditions :
\<^item> @{text \<open>revis_closure\<close>} : a belief set @{term \<open>K\<close>} revised by @{term \<open>\<phi>\<close>} should be logically closed
\<^item> @{text \<open>revis_inclusion\<close>} : a belief set @{term \<open>K\<close>} revised by @{term \<open>\<phi>\<close>} should be a subset of @{term \<open>K\<close>} expanded by @{term \<open>\<phi>\<close>}
\<^item> @{text \<open>revis_vacuity\<close>} : if @{text \<open>\<not>\<phi>\<close>} is not in @{term \<open>K\<close>} then the revision of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} is equivalent of the expansion of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>}
\<^item> @{text \<open>revis_success\<close>} : a belief set @{term \<open>K\<close>} revised by @{term \<open>\<phi>\<close>} should contain @{term \<open>\<phi>\<close>}
\<^item> @{text \<open>revis_extensionality\<close>} :  Extensionality guarantees that the logic of contraction is extensional in the sense of allowing logically equivalent sentences to be freely substituted for each other
\<^item> @{text \<open>revis_consistency\<close>} : a belief set @{term \<open>K\<close>} revised by @{term \<open>\<phi>\<close>} is consistent if @{term \<open>\<phi>\<close>} is consistent\<close>
locale AGM_Revision = Supraclassical_logic +

fixes revision:: \<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set\<close> (infix \<open>\<^bold>*\<close> 55)

assumes revis_closure:        \<open>K = Cn(A) \<Longrightarrow> K \<^bold>* \<phi> = Cn(K \<^bold>* \<phi>)\<close>
    and revis_inclusion:      \<open>K = Cn(A) \<Longrightarrow> K \<^bold>* \<phi> \<subseteq> K \<oplus> \<phi>\<close>
    and revis_vacuity:        \<open>K = Cn(A) \<Longrightarrow> .\<not> \<phi> \<notin> K \<Longrightarrow> K \<oplus> \<phi> \<subseteq> K \<^bold>* \<phi>\<close>
    and revis_success:        \<open>K = Cn(A) \<Longrightarrow> \<phi> \<in> K \<^bold>* \<phi>\<close>
    and revis_extensionality: \<open>K = Cn(A) \<Longrightarrow> Cn({\<phi>}) = Cn({\<psi>}) \<Longrightarrow> K \<^bold>* \<phi> = K \<^bold>* \<psi>\<close>
    and revis_consistency:    \<open>K = Cn(A) \<Longrightarrow> .\<not> \<phi> \<notin> Cn({})  \<Longrightarrow> \<bottom> \<notin> K \<^bold>* \<phi>\<close>

text\<open>A full revision is defined by two more postulates :
\<^item> @{text \<open>revis_superexpansion\<close>} : An element of @{text \<open> K \<^bold>* (\<phi> .\<and>. \<psi>)\<close>} is also an element of @{term \<open>K\<close>} revised by @{term \<open>\<phi>\<close>} and expanded by @{term \<open>\<psi>\<close>}
\<^item> @{text \<open>revis_subexpansion\<close>} : An element of @{text \<open>(K \<^bold>* \<phi>) \<oplus> \<psi>\<close>} is also an element of @{term \<open>K\<close>} revised by @{text \<open>\<phi> .\<and>. \<psi>\<close>} if @{text \<open>(K \<^bold>* \<phi>)\<close>} do not imply @{text \<open>\<not> \<psi>\<close>}
\<close>
locale AGM_FullRevision = AGM_Revision + 
  assumes revis_superexpansion: \<open>K = Cn(A) \<Longrightarrow> K \<^bold>* (\<phi> .\<and>. \<psi>) \<subseteq> (K \<^bold>* \<phi>) \<oplus> \<psi>\<close>
      and revis_subexpansion:   \<open>K = Cn(A) \<Longrightarrow> .\<not> \<psi> \<notin> (K \<^bold>* \<phi>) \<Longrightarrow> (K \<^bold>* \<phi>) \<oplus> \<psi> \<subseteq> K \<^bold>* (\<phi> .\<and>. \<psi>)\<close>

begin

\<comment> \<open>important lemmas/corollaries that can replace the previous assumptions\<close>
corollary revis_superexpansion_ext : \<open>K = Cn(A) \<Longrightarrow> (K \<^bold>* \<phi>) \<inter> (K \<^bold>* \<psi>) \<subseteq> (K \<^bold>* (\<phi> .\<or>. \<psi>))\<close>
proof(intro subsetI, elim IntE)
  fix \<chi>
  assume a:\<open>K = Cn(A)\<close> and b:\<open>\<chi> \<in> (K \<^bold>* \<phi>)\<close> and c:\<open>\<chi> \<in> (K \<^bold>* \<psi>)\<close>
  have \<open> Cn({(\<phi>' .\<or>. \<psi>') .\<and>. \<phi>'}) = Cn({\<phi>'})\<close> for \<phi>' \<psi>' 
    using conj_superexpansion2 by (simp add: Cn_same)
  hence d:\<open>K \<^bold>* \<phi>' \<subseteq> (K \<^bold>* (\<phi>' .\<or>. \<psi>')) \<oplus> \<phi>'\<close> for \<phi>' \<psi>'
    using revis_superexpansion[OF a, of \<open>\<phi>' .\<or>. \<psi>'\<close> \<phi>'] revis_extensionality a by metis
  hence \<open>\<phi> .\<longrightarrow>. \<chi> \<in> (K \<^bold>* (\<phi> .\<or>. \<psi>))\<close> and \<open>\<psi> .\<longrightarrow>. \<chi> \<in> (K \<^bold>* (\<phi> .\<or>. \<psi>))\<close> 
    using d[of \<phi> \<psi>] d[of \<psi> \<phi>] revis_extensionality[OF a disj_com_Cn, of \<psi> \<phi>]  
    using imp_PL a b c expansion_def revis_closure by fastforce+
  then show  c:\<open>\<chi> \<in> (K \<^bold>* (\<phi> .\<or>. \<psi>))\<close>
    using disjE_PL a revis_closure revis_success by fastforce
qed

end

subsection \<open>Relation of AGM revision and AGM contraction \<close>

text\<open>The AGM contraction of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} can be defined as the AGM revision of @{term \<open>K\<close>} by @{text \<open>\<not>\<phi>\<close>}
intersect with @{term \<open>K\<close>} (to remove @{text \<open>\<not>\<phi>\<close>} from K revised). This definition is known as Harper identity @{cite "Harper1976"}\<close>
sublocale AGM_Revision \<subseteq> AGM_Contraction where contraction = \<open>\<lambda>K \<phi>. K \<inter> (K \<^bold>* .\<not> \<phi>)\<close> 
proof(unfold_locales, goal_cases)
  case closure:(1 K A \<phi>)
  then show ?case
    by (metis Cn_inter revis_closure)
next
  case inclusion:(2 K A \<phi>)
  then show ?case by blast
next
  case vacuity:(3 K A \<phi>)
  hence \<open>.\<not> (.\<not> \<phi>) \<notin> K\<close>
    using absurd_PL infer_def by blast
  hence \<open>K \<subseteq> (K \<^bold>* .\<not> \<phi>)\<close> 
    using revis_vacuity[where \<phi>=\<open>.\<not> \<phi>\<close>] expansion_def inclusion_L vacuity(1) by fastforce 
  then show ?case 
    by fast
next
  case success:(4 K A \<phi>)
  hence \<open>.\<not> (.\<not> \<phi>) \<notin> Cn({})\<close>
    using infer_def notnot_PL by blast
  hence a:\<open>\<bottom> \<notin> K \<^bold>* (.\<not> \<phi>)\<close>
    by (simp add: revis_consistency success(1))
  have \<open>.\<not> \<phi> \<in>  K \<^bold>* (.\<not> \<phi>)\<close>      
    by (simp add: revis_success success(1))
  with a have \<open>\<phi> \<notin>  K \<^bold>* (.\<not> \<phi>)\<close>
    using infer_def non_consistency revis_closure success(1) by blast
  then show ?case
    by simp
next
  case recovery:(5 K A \<phi>)
  show ?case 
  proof
    fix \<psi>
    assume a:\<open>\<psi> \<in> K\<close>
    hence b:\<open>\<phi> .\<longrightarrow>. \<psi> \<in> K\<close> using impI2 recovery by auto 
    have \<open>.\<not> \<psi> .\<longrightarrow>. .\<not> \<phi> \<in> K \<^bold>* .\<not> \<phi>\<close>
      using impI2 recovery revis_closure revis_success by fastforce
    hence \<open>\<phi> .\<longrightarrow>. \<psi> \<in> K \<^bold>* .\<not> \<phi>\<close>
      using imp_contrapos recovery revis_closure by fastforce
    with b show \<open>\<psi> \<in> Cn (K \<inter> (K \<^bold>* .\<not> \<phi>) \<union> {\<phi>})\<close>
      by (meson Int_iff Supraclassical_logic.imp_PL Supraclassical_logic_axioms inclusion_L subsetD)
  qed
next
  case extensionality:(6 K A \<phi> \<psi>)
  hence \<open>Cn({.\<not> \<phi>}) = Cn({.\<not> \<psi>})\<close> 
    using  equiv_negation[of \<open>{}\<close> \<phi> \<psi>] valid_Cn_equiv valid_def by auto
  hence \<open>(K \<^bold>* .\<not> \<phi>) = (K \<^bold>* .\<not> \<psi>)\<close>
    using extensionality(1) revis_extensionality by blast
  then show ?case by simp
qed


locale AGMC_S = AGM_Contraction + Supraclassical_logic

text\<open>The AGM revision of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} can be defined as the AGM contraction of @{term \<open>K\<close>} by @{text \<open>\<not>\<phi>\<close>}
followed by an expansion by @{term \<open>\<phi>\<close>}. This definition is known as Levi identity @{cite "Levi1977SubjunctivesDA"}.\<close>
sublocale AGMC_S \<subseteq> AGM_Revision where revision = \<open>\<lambda>K \<phi>. (K \<div> .\<not> \<phi>) \<oplus> \<phi>\<close>
proof(unfold_locales, goal_cases)
  case closure:(1 K A \<phi>)
  then show ?case
    by (simp add: expansion_def idempotency_L)
next
  case inclusion:(2 K A \<phi>)
  have "K \<div> .\<not> \<phi> \<subseteq> K \<union> {\<phi>}"
    using contract_inclusion inclusion by auto
  then show ?case
      by (simp add: expansion_def monotonicity_L)
next
  case vacuity:(3 K A \<phi>)
  then show ?case
    by (simp add: contract_vacuity expansion_def)
next
  case success:(4 K A \<phi>)
  then show ?case
    using assumption_L expansion_def by auto
next
  case extensionality:(5 K A \<phi> \<psi>)
  hence \<open>Cn({.\<not> \<phi>}) = Cn({.\<not> \<psi>})\<close> 
    using  equiv_negation[of \<open>{}\<close> \<phi> \<psi>] valid_Cn_equiv valid_def by auto
  hence \<open>(K \<div> .\<not> \<phi>) = (K \<div> .\<not> \<psi>)\<close>
    using contract_extensionality extensionality(1) by blast
  then show ?case
    by (metis Cn_union expansion_def extensionality(2))
next
  case consistency:(6 K A \<phi>)
  then show ?case
    by (metis contract_closure contract_success expansion_def infer_def not_PL)
qed

text\<open>The relationship between AGM full revision and  AGM full contraction is the same as the relation between AGM revison and AGM contraction\<close>
sublocale AGM_FullRevision \<subseteq> AGM_FullContraction where contraction = \<open>\<lambda>K \<phi>. K \<inter> (K \<^bold>* .\<not> \<phi>)\<close> 
proof(unfold_locales, goal_cases)
  case conj_overlap:(1 K A \<phi> \<psi>)
  have a:\<open>Cn({.\<not> (\<phi> .\<and>. \<psi>)}) = Cn({(.\<not> \<phi>) .\<or>. (.\<not> \<psi>)})\<close>
    using Cn_same morgan by simp
  show ?case (is ?A) 
    using revis_superexpansion_ext[OF conj_overlap(1), of \<open>.\<not> \<phi>\<close> \<open>.\<not> \<psi>\<close>] 
          revis_extensionality[OF conj_overlap(1) a] by auto
next
  case conj_inclusion:(2 K A \<phi> \<psi>)
  have a:\<open>Cn({.\<not> (\<phi> .\<and>. \<psi>) .\<and>. .\<not> \<phi>}) = Cn({.\<not> \<phi>})\<close>
    using conj_superexpansion1 by (simp add: Cn_same)
  from conj_inclusion show ?case
  proof(cases \<open>\<phi> \<in> K\<close>)
    case True
    hence b:\<open>.\<not> (.\<not> \<phi>) \<notin> K \<^bold>* .\<not> (\<phi> .\<and>. \<psi>)\<close>
      using absurd_PL  conj_inclusion revis_closure by fastforce
    show ?thesis
      using revis_subexpansion[OF conj_inclusion(1) b] revis_extensionality[OF conj_inclusion(1) a] 
             expansion_def inclusion_L by fastforce
  next
    case False
    then show ?thesis
      by (simp add: conj_inclusion(1) contract_vacuity)
  qed
qed


locale AGMFC_S = AGM_FullContraction + AGMC_S

sublocale AGMFC_S \<subseteq> AGM_FullRevision where revision = \<open>\<lambda>K \<phi>. (K \<div> .\<not> \<phi>) \<oplus> \<phi>\<close>
proof(unfold_locales, safe, goal_cases)
  case super:(1 K A \<phi> \<psi> \<chi>)
  hence a:\<open>(\<phi> .\<and>. \<psi>) .\<longrightarrow>. \<chi> \<in> Cn(Cn(A) \<div> .\<not> (\<phi> .\<and>. \<psi>))\<close> 
    using Supraclassical_logic.imp_PL Supraclassical_logic_axioms expansion_def by fastforce
  have b:\<open>(\<phi> .\<and>. \<psi>) .\<longrightarrow>. \<chi> \<in> Cn({.\<not> (\<phi> .\<and>. \<psi>)})\<close>
    by (meson Supraclassical_logic.imp_recovery0 Supraclassical_logic.valid_disj_PL Supraclassical_logic_axioms)
  have c:\<open>(\<phi> .\<and>. \<psi>) .\<longrightarrow>. \<chi> \<in> Cn(A) \<div> (.\<not> (\<phi> .\<and>. \<psi>) .\<and>. .\<not> \<phi>)\<close> 
    using contract_conj_overlap_variant[of \<open>Cn(A)\<close> A \<open>.\<not> (\<phi> .\<and>. \<psi>)\<close> \<open>.\<not> \<phi>\<close>] a b
    using AGM_Contraction.contract_closure AGM_FullContraction_axioms AGM_FullContraction_def by fastforce
  have d:\<open>Cn({.\<not> (\<phi> .\<and>. \<psi>) .\<and>. .\<not> \<phi>}) = Cn({.\<not> \<phi>})\<close>
    using conj_superexpansion1 by (simp add: Cn_same)
  hence e:\<open>(\<phi> .\<and>. \<psi>) .\<longrightarrow>. \<chi> \<in> Cn(A) \<div> .\<not> \<phi>\<close> 
    using AGM_Contraction.contract_extensionality[OF _ _ d] c
          AGM_FullContraction_axioms AGM_FullContraction_def by fastforce
  hence f:\<open>\<phi> .\<longrightarrow>. (\<psi> .\<longrightarrow>. \<chi>) \<in> Cn(A) \<div> .\<not> \<phi>\<close> 
    using conj_imp AGM_Contraction.contract_closure AGM_FullContraction_axioms AGM_FullContraction_def conj_imp by fastforce
  then show ?case
    by (metis assumption_L expansion_def imp_PL infer_def)
next
  case sub:(2 K A \<psi> \<phi> \<chi>)
  hence a:\<open>\<phi> .\<longrightarrow>. (\<psi> .\<longrightarrow>. \<chi>) \<in> Cn(A) \<div> .\<not> \<phi>\<close>
    by (metis AGMC_S.axioms(1) AGMC_S_axioms AGM_Contraction.contract_closure expansion_def impI_PL infer_def revis_closure)
  have b:\<open>Cn({.\<not> (\<phi> .\<and>. \<psi>) .\<and>. .\<not> \<phi>}) = Cn({.\<not> \<phi>})\<close>
    using conj_superexpansion1 by (simp add: Cn_same)
  have c:\<open>.\<not> (\<phi> .\<and>. \<psi>) \<notin> Cn A \<div> (.\<not> \<phi>)\<close>
    using sub(1) by (metis assumption_L conj_imp expansion_def imp_PL infer_def not_PL)
  have c:\<open>Cn(A) \<div> .\<not> \<phi> \<subseteq> Cn(A) \<div> (.\<not> (\<phi> .\<and>. \<psi>))\<close>
    using contract_conj_inclusion[of \<open>Cn(A)\<close> A \<open>.\<not> (\<phi> .\<and>. \<psi>)\<close> \<open>.\<not> \<phi>\<close>] 
    by (metis AGM_Contraction.contract_extensionality AGM_FullContraction.axioms(1) AGM_FullContraction_axioms b c)
  then show ?case 
    by (metis a assumption_L conj_imp expansion_def imp_PL in_mono infer_def) 
qed


end


