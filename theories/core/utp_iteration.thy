(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_iteration.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Constructs for Iteration *}

theory utp_iteration
imports 
  utp_recursion
  "../laws/utp_refine_laws"
begin

text {* Relational Iteration (Kleene Star) *}

lemma OneP_closure [closure]:
  "1 \<in> WF_RELATION"
  by (simp add:one_WF_PREDICATE_def closure)

lemma TimesP_closure [closure]:
  "\<lbrakk> P \<in> WF_RELATION; Q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> P\<cdot>Q \<in> WF_RELATION"
  by (simp add:times_WF_PREDICATE_def closure)

lemma PowerP_closure [closure]:
  fixes P :: "'a WF_PREDICATE"
  assumes "P \<in> WF_RELATION"
  shows "P^n \<in> WF_RELATION"
  by (induct n, simp_all add:closure assms)
  
lemma EvalRR_power [evalrr]:
  "\<lbrakk>P^n\<rbrakk>\<R> = \<lbrakk>P\<rbrakk>\<R> ^^ n"
  apply (induct n)
  apply (simp add:one_WF_PREDICATE_def evalrr)
  apply (simp add:times_WF_PREDICATE_def evalrr relpow_commute)
done

lemma EvalRX_power [evalrx]:
  "P \<in> WF_RELATION \<Longrightarrow> \<lbrakk>P^n\<rbrakk>RX = \<lbrakk>P\<rbrakk>RX ^^ n"
  apply (induct n)
  apply (simp add:one_WF_PREDICATE_def evalrx)
  apply (simp add:times_WF_PREDICATE_def evalrx closure relpow_commute)
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

context kleene_algebra
begin

definition star1 :: "'a \<Rightarrow> 'a" ("_\<^sup>+" [101] 100) where
"star1 p = p\<cdot>p\<^sup>\<star>"

end


declare star1_def [eval,evalr,evalrr,evalrx]

syntax
  "_upred_star"     :: "upred \<Rightarrow> upred" ("_\<^sup>\<star>" [101] 100)

translations
  "_upred_star p"   == "p\<^sup>\<star>"

lemma StarP_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> P\<^sup>\<star> \<in> WF_RELATION"
  by (auto intro:closure simp add:star_WF_PREDICATE_def)

lemma EvalRR_StarP: "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<R> = \<lbrakk>P\<rbrakk>\<R>\<^sup>*"
  apply (auto simp add: rtrancl_is_UN_relpow star_WF_PREDICATE_def evalrr)
  apply (metis EvalRR_power)
done

lemma EvalRX_StarP [evalrx]: 
  "P \<in> WF_RELATION \<Longrightarrow> \<lbrakk>P\<^sup>\<star>\<rbrakk>RX = \<lbrakk>P\<rbrakk>RX\<^sup>*"
  apply (auto simp add: rtrancl_is_UN_relpow star_WF_PREDICATE_def evalrx closure)
  apply (metis EvalRX_power)
done

lemma EvalRR_StarP_Union: "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<R> = (\<Union>n. (\<lbrakk>P\<rbrakk>\<R> ^^ n))"
  apply (auto simp add: rtrancl_is_UN_relpow star_WF_PREDICATE_def evalrr)
  apply (metis EvalRR_power)
done

lemma EvalRX_StarP_Union: 
  "P \<in> WF_RELATION \<Longrightarrow> \<lbrakk>P\<^sup>\<star>\<rbrakk>RX = (\<Union>n. (\<lbrakk>P\<rbrakk>RX ^^ n))"
  apply (auto simp add: rtrancl_is_UN_relpow star_WF_PREDICATE_def evalrx closure)
  apply (metis EvalRX_power)
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

lemma Star1P_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> P\<^sup>+ \<in> WF_RELATION"
  by (auto intro:closure simp add:star1_def)

lemma StarP_mono: "mono (\<lambda> x. (II \<or>\<^sub>p (p ; x)))"
  apply (rule)
  apply (utp_rel_auto_tac)
done
lemma StarP_WFP: "(\<mu> X \<bullet> II \<or>\<^sub>p (P ; X)) \<sqsubseteq> P\<^sup>\<star>"
  apply (auto simp add:evalrr EvalRR_StarP gfp_def)
  apply (metis EvalRR_StarP rel_kleene_algebra.star_unfoldl_eq subset_refl)
done
lemma StarP_SFP: "P\<^sup>\<star> \<sqsubseteq> (\<nu> X \<bullet> II \<or>\<^sub>p (P ; X))"
  apply (subgoal_tac "{u. Id \<subseteq> \<lbrakk>u\<rbrakk>\<R> \<and> \<lbrakk>P\<rbrakk>\<R> O \<lbrakk>u\<rbrakk>\<R> \<subseteq> \<lbrakk>u\<rbrakk>\<R>} \<noteq> {}")
  apply (auto simp add:evalrr EvalRR_StarP lfp_def)
  apply (metis EvalRR_StarP rel_kleene_algebra.star_1l rel_kleene_algebra.star_ref)
  apply (rule_tac x="true" in exI)
  apply (metis EvalRR_SemiR EvalRR_SkipR EvalRR_refinement RefineP_TrueP_refine)
done

definition 
  IterP :: " 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE" ("while _ do _ od") where
"IterP b P \<equiv> (P \<lhd> b \<rhd> II)\<^sup>\<star>"

syntax
  "_upred_while"    :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("while _ do _ od")

translations
  "_upred_while b p"   == "CONST IterP b p"

declare EvalRR_StarP [evalrr]
declare IterP_def [eval, evalr, evalrr, evalrx]

lemma IterP_closure [closure]:
  "\<lbrakk> b \<in> WF_RELATION; P \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
     while b do P od \<in> WF_RELATION"
  by (simp add:IterP_def closure)

theorem IterP_refine [refine]:
  "while b do P od \<sqsubseteq> (P \<lhd> b \<rhd> II) ; (while b do P od)"
  by (metis IterP_def star_1l times_WF_PREDICATE_def)
  
theorem IterP_false: "while false do P od = II"
  by (simp add:evalrr)
theorem IterP_true: "while true do P od = P\<^sup>\<star>"
  by (simp add:evalrr)

theorem IterP_cond_true_refine [refine]:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION"
  shows "`(while b do P od) \<and> b` \<sqsubseteq> `(P \<and> b) ; while b do P od`"
proof -

  have "`while b do P od \<and> b` \<sqsubseteq> `((P \<lhd> b \<rhd> II) ; (while b do P od)) \<and> b`" (is "?l \<sqsubseteq> ?r")
    by (metis AndP_mono_refine IterP_refine order_refl)

  also have "?r = `b \<and> ((P \<lhd> b \<rhd> II) ; while b do P od)`"
    by (metis AndP_comm)

  also have "... = `((P \<and> b) ; while b do P od)`"
    by (metis AndP_comm CondR_rel_closure CondR_true_cond IterP_closure SemiR_AndP_left_precond SkipR_closure WF_CONDITION_WF_RELATION assms)

  finally show ?thesis ..
qed

theorem IterP_cond_false_refine [refine]:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION"
  shows "`(while b do P od) \<and> \<not>b` \<sqsubseteq> `II \<and> \<not>b`"
  using assms
  apply (simp add:IterP_def)
  apply (frule SemiR_TrueP_precond)
  apply (utp_xrel_auto_tac)
done

end
