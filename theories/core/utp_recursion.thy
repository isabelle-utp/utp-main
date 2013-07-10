(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_recursion.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Constructs for Recursion and Iteration *}

theory utp_recursion
imports 
  utp_lattice
  "../laws/utp_rel_laws"
(*  "../algebra/Kleene_Algebra/Kleene_Algebras" *)
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

text {* Relational Iteration (Kleene Star) *}

(*
lemma "\<lbrakk>\<mu> F\<rbrakk>R = gfp (\<lambda>x. \<lbrakk>F (IEvalR x)\<rbrakk>R)"
  apply (simp add:gfp_def evalr)
  apply (force)
  apply (rule_tac f="Union" in cong)
  apply (auto)
  apply (metis (lifting) IEvalR_inverse set_rev_mp)
  apply (rule_tac x="IEvalR x" in exI)
  apply (rule)
  apply (auto simp add:EvalR_def)
*)

lemma EvalRR_power [evalrr]:
  "\<lbrakk>P^n\<rbrakk>\<R> = \<lbrakk>P\<rbrakk>\<R> ^^ n"
  apply (induct n)
  apply (simp add:one_WF_PREDICATE_def evalrr)
  apply (simp add:times_WF_PREDICATE_def evalrr relpow_commute)
done

lemma UNREST_PowerP [unrest]: "UNREST NON_REL_VAR p \<Longrightarrow> UNREST NON_REL_VAR (p ^ n)"
  apply (induct n)
  apply (simp add:unrest one_WF_PREDICATE_def)
  apply (simp add:times_WF_PREDICATE_def)
  apply (force intro:unrest)
done

instantiation WF_PREDICATE :: (VALUE) star_op
begin

definition star_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"star_WF_PREDICATE p \<equiv> (\<Sqinter> { p ^ n | n. n \<in> UNIV})"

instance ..

end

lemma EvalRR_StarP: "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<R> = \<lbrakk>P\<rbrakk>\<R>\<^sup>*"
  apply (auto simp add: rtrancl_is_UN_relpow star_WF_PREDICATE_def evalrr)
  apply (metis EvalRR_power)
done
lemma EvalRR_StarP_Union: "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<R> = (\<Union>n. (\<lbrakk>P\<rbrakk>\<R> ^^ n))"
  apply (auto simp add: rtrancl_is_UN_relpow star_WF_PREDICATE_def evalrr)
  apply (metis EvalRR_power)
done

lemma UNREST_StarP [unrest]: "UNREST NON_REL_VAR p \<Longrightarrow> UNREST NON_REL_VAR (p\<^sup>\<star>)"
  by (auto intro:unrest simp add:star_WF_PREDICATE_def)

instantiation WF_PREDICATE :: (VALUE) dioid
begin

instance
  apply (intro_classes)
  apply (simp_all add:plus_WF_PREDICATE_def times_WF_PREDICATE_def 
                      zero_WF_PREDICATE_def one_WF_PREDICATE_def
                      less_WF_PREDICATE_def)
  apply (utp_pred_auto_tac)+
done
end

instantiation WF_PREDICATE :: (VALUE) kleene_algebra
begin

instance proof

  fix x :: "'a WF_PREDICATE"
  show "x\<^sup>\<star> \<sqsubseteq> 1 + x \<cdot> x\<^sup>\<star>"
    by (auto simp add: evalrr EvalRR_StarP)

next

  fix x y z :: "'a WF_PREDICATE"
  show "y \<sqsubseteq> z + x \<cdot> y \<longrightarrow> y \<sqsubseteq> x\<^sup>\<star> \<cdot> z"
    apply (simp add: evalrr EvalRR_StarP)
    apply (metis rel_dioid.add_lub rel_kleene_algebra.star_inductl)
  done

next

  fix x y z :: "'a WF_PREDICATE"
  show "y \<sqsubseteq> z + y \<cdot> x \<longrightarrow> y \<sqsubseteq> z \<cdot> x\<^sup>\<star>"
    apply (simp add: evalrr EvalRR_StarP)
    apply (metis Un_least rel_kleene_algebra.star_inductr)
  done

qed (simp_all add: evalrr)
end

lemma StarP_mono: "mono (\<lambda> x. (II \<or>\<^sub>p (p ; x)))"
  apply (rule)
  apply (utp_rel_auto_tac)
done
lemma StarP_WFP1: "(\<mu> X \<bullet> II \<or>\<^sub>p (P ; X)) \<sqsubseteq> P\<^sup>\<star>"
  apply (auto simp add:evalrr EvalRR_StarP gfp_def)
  apply (metis EvalRR_StarP rel_kleene_algebra.star_unfoldl_eq subset_refl)
done

lemma StarP_WFP2: "P\<^sup>\<star> \<sqsubseteq> (\<mu> X \<bullet> II \<or>\<^sub>p (P ; X))"
  apply (auto simp add:evalrr EvalRR_StarP_Union gfp_def)
oops

definition 
  IterP :: " 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE" ("while _ do _ od") where
"IterP b P \<equiv> (P \<lhd> b \<rhd> II)\<^sup>\<star>"

declare EvalRR_StarP [evalrr]
declare IterP_def [eval, evalr, evalrr]

lemma IterP_false: "while false do P od = II"
  by (simp add:evalrr)
lemma IterP_true: "while true do P od = P\<^sup>\<star>"
  by (simp add:evalrr)

end