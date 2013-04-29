(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_recursion.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Predicate Lattice *}

theory utp_recursion
imports 
  utp_laws
  utp_lattice
  "../algebra/Kleene_Algebra/Kleene_Algebra2"
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
  assumes "(C \<Rightarrow>p S) \<sqsubseteq> F (C \<Rightarrow>p S)" "[C \<Rightarrow>p (\<mu> F \<Leftrightarrow>p \<nu> F)]p" 
  shows "(C \<Rightarrow>p S) \<sqsubseteq> \<mu> F"
proof -

  from assms have "(C \<Rightarrow>p S) \<sqsubseteq> \<nu> F"
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
  apply (simp add:NON_REL_VAR_def)
  apply (force intro:unrest)
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

interpretation rel_dioid: dioid_one_zero "op \<union>" "op O" Id "{}" "op \<subseteq>" "op \<subset>"
  by (unfold_locales, auto)

interpretation rel_monoid: monoid_mult Id "op O" ..

lemma power_is_relpow: "rel_dioid.power X n = X ^^ n"
proof (induct n)
  case 0 show ?case
    by (metis rel_dioid.power_0 relpow.simps(1))
  case Suc thus ?case
    by (metis rel_dioid.power_Suc2 relpow.simps(2))
qed

lemma rel_star_def: "X^* = (\<Union>n. rel_dioid.power X n)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>n. X O rel_dioid.power Y n)"
by (metis rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>n. (rel_dioid.power X n) O Y)"
by (metis rel_star_def relcomp_UNION_distrib2)

context dioid_one_zero
begin

lemma power_inductl: "z + x \<cdot> y \<le> y \<longrightarrow> (x ^ n) \<cdot> z \<le> y"
proof (induct n)
  case 0 show ?case
    by (metis add_lub mult_onel power_0)
  case Suc thus ?case
    by (auto, metis add_lub mult.assoc mult_isol order_trans)
qed

lemma power_inductr: "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> (x ^ n) \<le> y"
proof (induct n)
  case 0 show ?case
    by (metis add_lub mult_oner power_0)
  case Suc
  {
    fix n
    assume "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x ^ n \<le> y"
      and "z + y \<cdot> x \<le> y"
    hence "z \<cdot> x ^ n \<le> y"
      by auto
    also have "z \<cdot> x ^ Suc n = z \<cdot> x \<cdot> x ^ n"
      by (metis mult.assoc power_Suc)
    moreover have "... = (z \<cdot> x ^ n) \<cdot> x"
      by (metis mult.assoc power_commutes)
    moreover have "... \<le> y \<cdot> x"
      by (metis calculation(1) mult_isor)
    moreover have "... \<le> y"
      by (metis `z + y \<cdot> x \<le> y` add_lub)
    ultimately have "z \<cdot> x ^ Suc n \<le> y" by auto
  }
  thus ?case
    by (metis Suc)
qed

end (* dioid_one_zero *)

interpretation rel_kleene_algebra: kleene_algebra "op \<union>" "op O" Id "{}" "op \<subseteq>" "op \<subset>" rtrancl
proof
  fix x y z :: "'a rel"
  show "Id \<union> x O x\<^sup>* \<subseteq> x\<^sup>*"
    by (metis order_refl r_comp_rtrancl_eq rtrancl_unfold)
  show "z \<union> x O y \<subseteq> y \<longrightarrow> x\<^sup>* O z \<subseteq> y"
    by (simp only: rel_star_contr, metis (lifting) SUP_le_iff rel_dioid.power_inductl)
  show "z \<union> y O x \<subseteq> y \<longrightarrow> z O x\<^sup>* \<subseteq> y"
    by (simp only: rel_star_contl, metis (lifting) SUP_le_iff rel_dioid.power_inductr)
qed

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

lemma StarP_mono: "mono (\<lambda> x. (II \<or>p (p ; x)))"
  apply (rule)
  apply (utp_rel_auto_tac)
done
lemma StarP_WFP1: "(\<mu> X \<bullet> II \<or>p (P ; X)) \<sqsubseteq> P\<^sup>\<star>"
  apply (auto simp add:evalrr EvalRR_StarP gfp_def)
  apply (metis EvalRR_StarP rel_kleene_algebra.star_unfoldl_eq subset_refl)
done

lemma StarP_WFP2: "P\<^sup>\<star> \<sqsubseteq> (\<mu> X \<bullet> II \<or>p (P ; X))"
  apply (auto simp add:evalrr EvalRR_StarP_Union gfp_def)
oops

definition 
  IterP :: " 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE" ("while _ do _ od") where
"IterP b P \<equiv> (P \<triangleleft> b \<triangleright> II)\<^sup>\<star>"

declare EvalRR_StarP [evalrr]
declare IterP_def [eval, evalr, evalrr]

lemma IterP_false: "while false do P od = II"
  by (simp add:evalrr)
lemma IterP_true: "while true do P od = P\<^sup>\<star>"
  by (simp add:evalrr)

end