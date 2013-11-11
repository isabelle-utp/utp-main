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

definition star1 :: "'a \<Rightarrow> 'a" ("_\<^sup>+" [201] 200) where
"star1 p = p\<cdot>p\<^sup>\<star>"

end


declare star1_def [eval,evalr,evalrr,evalrx]

syntax
  "_upred_star"     :: "upred \<Rightarrow> upred" ("_\<^sup>\<star>" [900] 900)

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

text {* Kleene star talks about finite iteration only, and is therefore a strict subset of
        the set of infinite recursions *}

lemma StarP_refines_WFP: "(\<mu> X \<bullet> II \<or>\<^sub>p (P ; X)) \<sqsubseteq> P\<^sup>\<star>"
  apply (auto simp add:evalrr EvalRR_StarP gfp_def)
  apply (metis EvalRR_StarP rel_kleene_algebra.star_unfoldl_eq subset_refl)
done
lemma SFP_refines_StarP: "P\<^sup>\<star> \<sqsubseteq> (\<nu> X \<bullet> II \<or>\<^sub>p (P ; X))"
  apply (rule lfp_lowerbound)
  apply (metis OrP_refine one_WF_PREDICATE_def star_1l star_ref times_WF_PREDICATE_def)
done

lemma StarP_refines_SFP: "(\<nu> X \<bullet> II \<or>\<^sub>p (P ; X)) \<sqsubseteq> P\<^sup>\<star>"
  apply (rule lfp_greatest)
  apply (metis one_WF_PREDICATE_def plus_WF_PREDICATE_def star_inductl_one times_WF_PREDICATE_def)
done

text {* The star is equivalent to the greatest fixed-point *}
theorem StarP_as_SFP: "P\<^sup>\<star> = (\<nu> X \<bullet> II \<or>\<^sub>p (P ; X))"
  by (metis SFP_refines_StarP StarP_refines_SFP antisym)

definition 
  IterP :: " 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE 
           \<Rightarrow> 'a WF_PREDICATE" ("while _ do _ od") where
"IterP b P \<equiv> ((b \<and>\<^sub>p P)\<^sup>\<star>) \<and>\<^sub>p (\<not>\<^sub>p b\<acute>)"  
  
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

theorem IterP_false: "while false do P od = II"
  by (simp add:evalrr)

theorem IterP_true: "while true do P od = false"
  by (simp add:evalrr)

theorem IterP_cond_true:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION"
  shows "`(while b do P od) \<and> b` = `(P \<and> b) ; while b do P od`"
proof -
  have "`while b do P od \<and> b` = `((b \<and> P)\<^sup>\<star> \<and> \<not>b\<acute>) \<and> b`"
    by (simp add:IterP_def)

  also have "... = `((II \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>)) \<and> \<not>b\<acute>) \<and> b`"
    by (metis star_unfoldl_eq one_WF_PREDICATE_def plus_WF_PREDICATE_def times_WF_PREDICATE_def)

  also have "... = `(b \<and> (II \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>`"
    by (metis AndP_assoc AndP_comm)

  also have "... = `(((b \<and> II) \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>`"
    by (smt AndP_OrP_distl AndP_rel_closure OrP_AndP_distr SemiR_AndP_left_precond StarP_closure WF_CONDITION_WF_RELATION assms utp_pred_simps(7) utp_pred_simps(8))

  also have "... = `(((II \<and> b\<acute>) \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>`"
    by (utp_rel_auto_tac)

  also have "... = `(((II \<and> b\<acute> \<and> \<not>b\<acute>) \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>`"
    by (metis (lifting, no_types) AndP_OrP_distr AndP_assoc AndP_idem)

  also have "... = `((b \<and> P) ; (b \<and> P)\<^sup>\<star>) \<and> \<not>b\<acute>`"
    by (metis AndP_contra utp_pred_simps(10) utp_pred_simps(5))

  also have "... = `(b \<and> P) ; while b do P od`"
    by (metis AndP_rel_closure ConvR_NotP IterP_def NotP_cond_closure PrimeP_WF_CONDITION_WF_POSTCOND SemiR_AndP_right_postcond StarP_closure WF_CONDITION_WF_RELATION assms(1) assms(2))

  finally show ?thesis by (metis AndP_comm)
qed

theorem IterP_cond_false:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION"
  shows "`while b do P od \<and> \<not>b` = `II \<and> \<not>b`"
proof -
  have "`while b do P od \<and> \<not>b` = `((b \<and> P)\<^sup>\<star> \<and> \<not>b\<acute>) \<and> \<not>b`"
    by (simp add:IterP_def)

  also have "... = `((II \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>)) \<and> \<not>b\<acute>) \<and> \<not>b`"
    by (metis star_unfoldl_eq one_WF_PREDICATE_def plus_WF_PREDICATE_def times_WF_PREDICATE_def)

  also have "... = `(\<not>b \<and> (II \<or> ((b \<and> P) ; (b \<and> P)\<^sup>\<star>))) \<and> \<not>b\<acute>`"
    by (metis AndP_assoc AndP_comm)

  also have "... = `((\<not>b \<and> II) \<or> ((\<not>b \<and> (b \<and> P)) ; (b \<and> P)\<^sup>\<star>)) \<and> \<not>b\<acute>`"
    by (metis AndP_OrP_distl AndP_rel_closure NotP_cond_closure SemiR_AndP_left_precond StarP_closure WF_CONDITION_WF_RELATION assms(1) assms(2))

  also have "... = `(\<not>b \<and> II) \<and> \<not>b\<acute>`"
    by (metis (hide_lams, no_types) AndP_assoc AndP_comm AndP_contra OrP_comm SemiR_FalseP_left calculation utp_pred_simps(10) utp_pred_simps(5))

  also have "... = `(\<not>b \<and> II)`"
  using assms by (utp_xrel_auto_tac)

  finally show ?thesis
    by (metis AndP_comm) 
qed
   
theorem IterP_unfold:
  assumes "b \<in> WF_CONDITION" "S \<in> WF_RELATION"
  shows "while b do S od = (S ; while b do S od) \<lhd> b \<rhd> II"
proof -
  have "`while b do S od` = `(while b do S od \<and> b) \<or> (while b do S od \<and> \<not>b)`"
    by (metis AndP_comm WF_PREDICATE_cases)

  also have "... = `((S \<and> b) ; while b do S od) \<or> (II \<and> \<not>b)`"
    by (metis IterP_cond_false IterP_cond_true assms)

  also have "... = (S ; while b do S od) \<lhd> b \<rhd> II"
    by (metis AndP_comm CondR_def IterP_closure SemiR_AndP_left_precond WF_CONDITION_WF_RELATION assms)

  finally show ?thesis .
qed

theorem SemiR_ImpliesP_idem:
  "p \<in> WF_CONDITION \<Longrightarrow> `(p \<Rightarrow> p\<acute>) ; (p \<Rightarrow> p\<acute>)` = `(p \<Rightarrow> p\<acute>)`"
  by (frule SemiR_TrueP_precond, utp_xrel_auto_tac)

lemma SFP_refines_IterP:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION"
  shows "while b do P od \<sqsubseteq> (\<nu> X \<bullet> ((P ; X) \<lhd> b \<rhd> II))"
  by (metis IterP_unfold assms(1) assms(2) lfp_lowerbound order_refl)


(* Can't prove this yet, though I reckon it's true *)
lemma IterP_refines_SFP:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION"
shows "(\<nu> X \<bullet> ((P ; X) \<lhd> b \<rhd> II)) \<sqsubseteq> while b do P od"
  apply (simp add:IterP_def StarP_as_SFP)
oops
 
end
