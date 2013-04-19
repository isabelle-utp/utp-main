(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_recursion.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Predicate Lattice *}

theory utp_recursion
imports 
  utp_lattice
begin

subsection {* Fixed Points *}

abbreviation WFP ::
  "'VALUE WF_FUNCTION \<Rightarrow>
   'VALUE WF_PREDICATE" ("\<mu>") where
"WFP \<equiv> lfp"

syntax
  "_WFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3MU _./ _)" [0, 10] 10)

syntax (xsymbols)
  "_WFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3\<mu>_\<bullet>/ _)" [0, 10] 10)

translations
  "MU x. P" == "CONST WFP (%x. P)"

abbreviation SFP ::
  "'VALUE WF_FUNCTION \<Rightarrow>
   'VALUE WF_PREDICATE" ("\<nu>") where
"SFP \<equiv> gfp"

syntax
  "_SFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3NU _./ _)" [0, 10] 10)

syntax (xsymbols)
  "_SFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3\<nu>_\<bullet>/ _)" [0, 10] 10)

translations
  "NU x. P" == "CONST SFP (%x. P)"

lemma WFP: "F(Y) \<sqsubseteq> Y \<Longrightarrow> \<mu> F \<sqsubseteq> Y"
  by (metis lfp_lowerbound)

lemma WFP_unfold: "mono F \<Longrightarrow> \<mu> F = F(\<mu> F)"
  by (metis lfp_unfold)

lemma WFP_id: "(\<mu> X \<bullet> X) = true"
  by (metis bot_WF_PREDICATE_def bot_unique WFP)

lemma SFP: "S \<sqsubseteq> F(S) \<Longrightarrow> S \<sqsubseteq> \<nu> F"
  by (metis gfp_upperbound)

lemma SFP_unfold: "mono F \<Longrightarrow> F (\<nu> F) = \<nu> F"
  by (metis gfp_unfold)

lemma SFP_id: "(\<nu> X \<bullet> X) = false"
  by (metis SFP top_WF_PREDICATE_def top_unique)

type_synonym 'a WF_PRED_CHAIN = "nat \<Rightarrow> 'a WF_PREDICATE"

definition chain :: "'a WF_PRED_CHAIN \<Rightarrow> bool" where
  "chain Y = ((Y 0 = false) \<and> (\<forall>i. Y (Suc i) \<sqsubseteq> Y i))"

lemma chain0 [simp]: "chain Y \<Longrightarrow> Y 0 = false"
  by (simp add:chain_def)

lemma chainI: "\<lbrakk> Y 0 = false; \<And>i. Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> chain Y"
  unfolding chain_def by fast

lemma chainE: "\<lbrakk> chain Y; \<And> i. \<lbrakk> Y 0 = false; Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding chain_def by fast

lemma L274: "\<forall> n. (E n \<and>p X = E n \<and>p Y) \<Longrightarrow> \<Sqinter> (range E) \<and>p X = \<Sqinter> (range E) \<and>p Y"
  by (utp_pred_auto_tac)

definition constr :: 
  " ('a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE) 
  \<Rightarrow> 'a WF_PRED_CHAIN \<Rightarrow> bool" where
"constr F E \<longleftrightarrow> (\<forall> X n. (F(X) \<and>p E (n + 1) = F(X \<and>p E n) \<and>p E (n + 1)))"

text {* This lemma gives a way of showing that there is a unique fixed-point when
        the predicate function can be built using a constructive function F
        over an approximation chain E *}
lemma chain_pred_terminates: 
  assumes "constr F E" "chain E" "mono F"
  shows "\<Sqinter> (range E) \<and>p \<mu> F  = \<Sqinter> (range E) \<and>p \<nu> F"
proof -
  from assms have "\<forall> n. E n \<and>p \<mu> F = E n \<and>p \<nu> F"
  proof (rule_tac allI)
    fix n
    from assms show "E n \<and>p \<mu> F = E n \<and>p \<nu> F"
    proof (induct n)
      case 0 thus ?case by (simp add:eval)
    next
      case (Suc n) 
      note hyp = this
      thus ?case
      proof -
        thm hyp
        have "E (n + 1) \<and>p \<mu> F = E (n + 1) \<and>p F (\<mu> F)"
          by (metis WFP_unfold assms(3))
        
        also from hyp have "... = E (n + 1) \<and>p F (E n \<and>p \<mu> F)"
          by (metis (no_types) AndP_comm constr_def)
        
        also from hyp have "... = E (n + 1) \<and>p F (E n \<and>p \<nu> F)"
          by simp
        
        also from hyp have "... = E (n + 1) \<and>p \<nu> F"
          by (smt AndP_comm SFP_unfold constr_def)
        
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
    
  thus ?thesis
    apply (rule_tac L274)
    apply (simp)
  done
qed

lemma WFP_rec: 
  assumes "(C \<Rightarrow>p S) \<sqsubseteq> F (C \<Rightarrow>p S)" "taut ([C \<Rightarrow>p (\<mu> F \<Leftrightarrow>p \<nu> F)]p)" 
  shows "(C \<Rightarrow>p S) \<sqsubseteq> \<mu> F"
proof -

  from assms have "(C \<Rightarrow>p S) \<sqsubseteq> \<nu> F"
    by (auto intro:SFP)

  with assms show ?thesis
    by (utp_pred_auto_tac)
qed

text {* Relational Iteration (Kleene Star) *}

instantiation WF_PREDICATE :: (VALUE) star
begin

definition star_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"star_WF_PREDICATE p = \<Sqinter> {p\<^bsup>n\<^esup> | n. n \<in> UNIV}"

instance ..

end

definition IterP :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a  WF_PREDICATE" where
"IterP b P \<equiv> \<mu> X \<bullet> ((P ; X) \<triangleleft> b \<triangleright> II)"

end