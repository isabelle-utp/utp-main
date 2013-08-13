(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_recursion.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Constructs for Recursion *}

theory utp_recursion
imports 
  utp_lattice
  "../laws/utp_rel_laws"
begin

subsection {* Fixed Points *}

abbreviation WFP ::
  "'VALUE WF_FUNCTION \<Rightarrow>
   'VALUE WF_PREDICATE" ("\<mu>") where
"WFP \<equiv> gfp"

syntax
  "_WFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3MU _./ _)" [0, 10] 10)

syntax (xsymbols)
  "_WFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3\<mu>_\<bullet>/ _)" [0, 10] 10)

translations
  "MU x. P" == "CONST WFP (%x. P)"

abbreviation SFP ::
  "'VALUE WF_FUNCTION \<Rightarrow>
   'VALUE WF_PREDICATE" ("\<nu>") where
"SFP \<equiv> lfp"

syntax
  "_SFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3NU _./ _)" [0, 10] 10)

syntax (xsymbols)
  "_SFP" :: "pttrn => 'VALUE WF_PREDICATE => 'VALUE WF_PREDICATE" ("(3\<nu>_\<bullet>/ _)" [0, 10] 10)

translations
  "NU x. P" == "CONST SFP (%x. P)"

syntax
  "_upred_wfp"      :: "pttrn \<Rightarrow> upred \<Rightarrow> upred" ("(3\<mu>_./ _)" [0, 10] 10)
  "_upred_sfp"      :: "pttrn \<Rightarrow> upred \<Rightarrow> upred" ("(3\<nu>_./ _)" [0, 10] 10)

translations
  "_upred_wfp x p"  == "CONST WFP (\<lambda>x. p)"
  "_upred_sfp x p"  == "CONST SFP (\<lambda>x. p)"

lemma WFP: "F(Y) \<sqsubseteq> Y \<Longrightarrow> \<mu> F \<sqsubseteq> Y"
  by (metis gfp_upperbound)

lemma WFP_unfold: "mono F \<Longrightarrow> \<mu> F = F(\<mu> F)"
  by (metis gfp_unfold)

lemma WFP_id: "(\<mu> X \<bullet> X) = true"
  by (metis WFP top_WF_PREDICATE_def top_unique)

lemma SFP: "S \<sqsubseteq> F(S) \<Longrightarrow> S \<sqsubseteq> \<nu> F"
  by (metis lfp_lowerbound)

lemma SFP_unfold: "mono F \<Longrightarrow> F (\<nu> F) = \<nu> F"
  by (metis lfp_unfold)

lemma SFP_id: "(\<nu> X \<bullet> X) = false"
  by (metis SFP bot_WF_PREDICATE_def bot_unique)

type_synonym 'a WF_PRED_CHAIN = "nat \<Rightarrow> 'a WF_PREDICATE"

definition chain :: "'a WF_PRED_CHAIN \<Rightarrow> bool" where
  "chain Y = ((Y 0 = false) \<and> (\<forall>i. Y (Suc i) \<sqsubseteq> Y i))"

lemma chain0 [simp]: "chain Y \<Longrightarrow> Y 0 = false"
  by (simp add:chain_def)

lemma chainI: "\<lbrakk> Y 0 = false; \<And>i. Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> chain Y"
  unfolding chain_def by fast

lemma chainE: "\<lbrakk> chain Y; \<And> i. \<lbrakk> Y 0 = false; Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding chain_def by fast

lemma L274: "\<forall> n. (E n \<and>\<^sub>p X = E n \<and>\<^sub>p Y) \<Longrightarrow> \<Sqinter> (range E) \<and>\<^sub>p X = \<Sqinter> (range E) \<and>\<^sub>p Y"
  by (utp_pred_auto_tac)

definition constr :: 
  " ('a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE) 
  \<Rightarrow> 'a WF_PRED_CHAIN \<Rightarrow> bool" where
"constr F E \<longleftrightarrow> (\<forall> X n. (F(X) \<and>\<^sub>p E (n + 1) = F(X \<and>\<^sub>p E n) \<and>\<^sub>p E (n + 1)))"

text {* This lemma gives a way of showing that there is a unique fixed-point when
        the predicate function can be built using a constructive function F
        over an approximation chain E *}
lemma chain_pred_terminates: 
  assumes "constr F E" "chain E" "mono F"
  shows "\<Sqinter> (range E) \<and>\<^sub>p \<mu> F  = \<Sqinter> (range E) \<and>\<^sub>p \<nu> F"
proof -
  from assms have "\<forall> n. E n \<and>\<^sub>p \<mu> F = E n \<and>\<^sub>p \<nu> F"
  proof (rule_tac allI)
    fix n
    from assms show "E n \<and>\<^sub>p \<mu> F = E n \<and>\<^sub>p \<nu> F"
    proof (induct n)
      case 0 thus ?case by (simp add:eval)
    next
      case (Suc n) 
      note hyp = this
      thus ?case
      proof -
        have "E (n + 1) \<and>\<^sub>p \<mu> F = E (n + 1) \<and>\<^sub>p F (\<mu> F)"
          by (metis WFP_unfold assms(3))
        
        also from hyp have "... = E (n + 1) \<and>\<^sub>p F (E n \<and>\<^sub>p \<mu> F)"
          by (metis (no_types) AndP_comm constr_def)
        
        also from hyp have "... = E (n + 1) \<and>\<^sub>p F (E n \<and>\<^sub>p \<nu> F)"
          by simp
        
        also from hyp have "... = E (n + 1) \<and>\<^sub>p \<nu> F"
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
  assumes "(C \<Rightarrow>\<^sub>p S) \<sqsubseteq> F (C \<Rightarrow>\<^sub>p S)" "[C \<Rightarrow>\<^sub>p (\<mu> F \<Leftrightarrow>\<^sub>p \<nu> F)]\<^sub>p" 
  shows "(C \<Rightarrow>\<^sub>p S) \<sqsubseteq> \<mu> F"
proof -

  from assms have "(C \<Rightarrow>\<^sub>p S) \<sqsubseteq> \<nu> F"
    by (auto intro:SFP)

  with assms show ?thesis
    by (utp_pred_auto_tac)
qed

end