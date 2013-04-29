(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_lattice.thy                                                *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Lattice *}

theory utp_alpha_lattice
imports 
  "../core/utp_lattice" 
  utp_alpha_laws 
begin

instantiation WF_ALPHA_PREDICATE :: (VALUE) order
begin

instance
  apply (intro_classes)
  apply (utp_alpha_tac, utp_pred_auto_tac)+
done
end

instantiation WF_ALPHA_PREDICATE :: (VALUE) inf
begin

definition inf_WF_ALPHA_PREDICATE :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"inf_WF_ALPHA_PREDICATE = AndA"

instance ..
end

instantiation WF_ALPHA_PREDICATE :: (VALUE) sup
begin

definition sup_WF_ALPHA_PREDICATE :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"sup_WF_ALPHA_PREDICATE = OrA"

instance ..
end

definition BotA :: "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("\<bottom>\<^bsub>_\<^esub>") where
"BotA = TrueA"

theorem BotA_rep_eq:
  "Rep_WF_ALPHA_PREDICATE \<bottom>\<^bsub>a \<^esub>= (a, \<bottom>)"
  by (simp add:BotA_def TrueA_rep_eq top_WF_PREDICATE_def)

definition TopA :: "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("\<top>\<^bsub>_\<^esub>") where
"TopA = FalseA"

theorem TopA_rep_eq:
  "Rep_WF_ALPHA_PREDICATE \<top>\<^bsub>a \<^esub>= (a, \<top>)"
  by (simp add:TopA_def FalseA_rep_eq bot_WF_PREDICATE_def)

declare BotA_def [evala]
declare TopA_def [evala]

lemma RefinementA_intro [intro]: 
  "\<lbrakk> \<alpha> p = \<alpha> q; \<pi> p \<sqsubseteq> \<pi> q \<rbrakk> \<Longrightarrow> p \<sqsubseteq> q"
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp add:EvalA_def)
done

definition SupA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE set \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" ("\<Squnion>\<^bsub>_ \<^esub>_" [900,900] 900) where
"ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow>
 SupA a ps =
 (if ps = {} then \<bottom>\<^bsub>a\<^esub> else
   Abs_WF_ALPHA_PREDICATE (a, \<Squnion> (\<pi> ` ps)))"

theorem SupA_rep_eq:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow>
   Rep_WF_ALPHA_PREDICATE (\<Squnion>\<^bsub>a \<^esub>ps) = (a, \<Squnion> (\<pi> ` ps))"
  apply (subgoal_tac "(a, \<Squnion> (\<pi> ` ps)) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:SupA_def BotA_rep_eq)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule unrest)
  apply (auto simp add:WF_ALPHA_PREDICATE_OVER_def)
done

definition InfA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE set \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" ("\<Sqinter>\<^bsub>_ \<^esub>_" [900,900] 900) where
"ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow>
 InfA a ps =
 (if ps = {} then \<top>\<^bsub>a\<^esub> else
   Abs_WF_ALPHA_PREDICATE (a, \<Sqinter> (\<pi> ` ps)))"

theorem InfA_rep_eq:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow>
   Rep_WF_ALPHA_PREDICATE (\<Sqinter>\<^bsub>a \<^esub>ps) = (a, \<Sqinter> (\<pi> ` ps))"
  apply (subgoal_tac "(a, \<Sqinter> (\<pi> ` ps)) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:InfA_def TopA_rep_eq)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule unrest)
  apply (auto simp add:WF_ALPHA_PREDICATE_OVER_def)
done

subsection {* Alphabet theorems *} 

lemma TopA_alphabet [alphabet]:
  "\<alpha> \<top>\<^bsub>a\<^esub> = a"
  by (simp add:pred_alphabet_def TopA_rep_eq)

lemma BotA_alphabet [alphabet]:
  "\<alpha> \<bottom>\<^bsub>a\<^esub> = a"
  by (simp add:pred_alphabet_def BotA_rep_eq)

lemma sup_alphabet [alphabet]:
  "\<alpha> (p \<squnion> q) = \<alpha> p \<union>\<^sub>f \<alpha> q"
  by (simp add:inf_WF_ALPHA_PREDICATE_def alphabet)

lemma inf_alphabet [alphabet]:
  "\<alpha> (p \<sqinter> q) = \<alpha> p \<union>\<^sub>f \<alpha> q"
  by (simp add:sup_WF_ALPHA_PREDICATE_def alphabet)

lemma SupA_alphabet [alphabet]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<alpha> (\<Squnion>\<^bsub>a \<^esub>ps) = a"
  by (simp add:pred_alphabet_def SupA_rep_eq)

lemma InfA_alphabet [alphabet]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<alpha> (\<Sqinter>\<^bsub>a \<^esub>ps) = a"
  by (simp add:pred_alphabet_def InfA_rep_eq)

lemma MeetA_WF_ALPHA_PREDICATE_OVER [closure]:
  "\<lbrakk> p \<in> WF_ALPHA_PREDICATE_OVER a; q \<in> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow>
  p \<sqinter> q \<in> WF_ALPHA_PREDICATE_OVER a"
  by (auto simp add:alphabet)

lemma SupA_WF_ALPHA_PREDICATE_OVER [closure]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> SupA a ps \<in> WF_ALPHA_PREDICATE_OVER a"
  by (auto simp add: alphabet)

lemma InfaA_WF_ALPHA_PREDICATE_OVER [closure]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> InfA a ps \<in> WF_ALPHA_PREDICATE_OVER a"
  by (auto simp add: alphabet)

subsubsection {* Evaluation laws *}

lemma EvalA_sup [evala]:
  "\<lbrakk>p \<squnion> q\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi> \<squnion> \<lbrakk>q\<rbrakk>\<pi>"
  by (simp add: inf_WF_ALPHA_PREDICATE_def inf_WF_PREDICATE_def evala)

lemma EvalA_inf [evala]:
  "\<lbrakk>p \<sqinter> q\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi> \<sqinter> \<lbrakk>q\<rbrakk>\<pi>"
  by (simp add: sup_WF_ALPHA_PREDICATE_def sup_WF_PREDICATE_def evala)

lemma EvalA_SupA [evala]: 
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<lbrakk>\<Squnion>\<^bsub>a \<^esub>ps\<rbrakk>\<pi> = \<Squnion> {\<lbrakk>p\<rbrakk>\<pi> | p . p \<in> ps}"
  apply (subgoal_tac "EvalA ` ps = {\<lbrakk>p\<rbrakk>\<pi> | p . p \<in> ps}")
  apply (auto simp add:SupA_rep_eq EvalA_def image_def)
done

lemma EvalA_InfA [evala]: 
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<lbrakk>\<Sqinter>\<^bsub>a \<^esub>ps\<rbrakk>\<pi> = \<Sqinter> {\<lbrakk>p\<rbrakk>\<pi> | p . p \<in> ps}"
  apply (subgoal_tac "EvalA ` ps = {\<lbrakk>p\<rbrakk>\<pi> | p . p \<in> ps}")
  apply (auto simp add:InfA_rep_eq EvalA_def image_def)
done
  
lemma LatticeA_L1: 
  "\<lbrakk> \<alpha> P = a; S \<subseteq> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow>
   P \<sqsubseteq> \<Sqinter>\<^bsub>a \<^esub>S \<longleftrightarrow> (\<forall> X\<in>S. P \<sqsubseteq> X)"
  by (auto simp add:EvalA_RefinementA alphabet evala Lattice_L1)

lemma LatticeA_L2:
  "\<lbrakk> \<alpha> Q = a; S \<subseteq> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow>
  (\<Squnion>\<^bsub>a \<^esub>S \<sqinter> Q) = \<Squnion>\<^bsub>a \<^esub>{P \<sqinter> Q | P. P \<in> S}"
  apply (subgoal_tac "{P \<sqinter> Q |P. P \<in> S} \<subseteq> WF_ALPHA_PREDICATE_OVER a")
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (simp add:evala alphabet closure)
  apply (simp add: Lattice_L2)
  apply (rule_tac f="Inf" in cong, simp)
  apply (auto)[1]
  apply (metis EvalA_inf inf_alphabet)
  apply (simp add:WF_ALPHA_PREDICATE_OVER_def)
  apply (force simp add: alphabet)
done

lemma LatticeA_L3:
  "\<lbrakk> \<alpha> Q = a; S \<subseteq> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow>
   (\<Sqinter>\<^bsub>a\<^esub> S) \<squnion> Q = \<Sqinter>\<^bsub>a\<^esub> { P \<squnion> Q | P. P \<in> S}"
  apply (subgoal_tac "{P \<squnion> Q |P. P \<in> S} \<subseteq> WF_ALPHA_PREDICATE_OVER a")
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (simp add:evala alphabet closure)
  apply (simp add: Lattice_L3)
  apply (rule_tac f="Sup" in cong, simp)
  apply (auto)[1]
  apply (metis EvalA_sup sup_alphabet)
  apply (simp add:WF_ALPHA_PREDICATE_OVER_def)
  apply (force simp add: alphabet)
done

subsection {* Fixed Points *}

definition WFP ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHA_FUNCTION \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" where
"f \<in> WF_ALPHA_FUNCTION_BETWEEN a a \<longrightarrow>
 WFP a f = SupA a {x \<in> WF_ALPHA_PREDICATE_OVER a . f x \<le> x}"

definition SFP ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHA_FUNCTION \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" where
"f \<in> WF_ALPHA_FUNCTION_BETWEEN a a \<longrightarrow>
 SFP a f = InfA a {x \<in> WF_ALPHA_PREDICATE_OVER a . x \<le> f x}"

lemma BotA_least: "\<bottom>\<^bsub>\<alpha> p\<^esub> \<sqsubseteq> p"
  by (utp_alpha_tac, utp_pred_tac)

lemma TopA_greatest: "p \<sqsubseteq> \<top>\<^bsub>\<alpha> p\<^esub>"
  by (utp_alpha_tac, utp_pred_tac)

(*
definition 
  WF_ALPHA_PREDICATE_gorder
  :: "'a ALPHABET \<Rightarrow> ('a WF_ALPHA_PREDICATE gorder)" where
  "WF_ALPHA_PREDICATE_gorder a \<equiv> \<lparr> carrier = WF_ALPHA_PREDICATE_OVER a
                                 , eq = op =
                                 , le = op \<le> \<rparr>" 

lemma WF_ALPHA_PREDICATE_partial_order [simp]:
  "partial_order (WF_ALPHA_PREDICATE_gorder a)"
  apply (unfold_locales)
  apply (simp_all add: WF_ALPHA_PREDICATE_gorder_def)
done

lemma WF_ALPHA_PREDICATE_complete_lattice [simp]:
  "complete_lattice (WF_ALPHA_PREDICATE_gorder a)"
  apply (unfold_locales)
  apply (simp_all add: WF_ALPHA_PREDICATE_gorder_def)
  apply (rule_tac x="x \<and>\<alpha> y" in exI)
  apply (simp add:least_def Upper_def alphabet closure)
  apply (safe)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (auto)[1]
  apply (metis WF_ALPHA_PREDICATE_OVER_alphabet)
  apply (metis WF_ALPHA_PREDICATE_OVER_alphabet)
  apply (rule_tac x="x \<or>\<alpha> y" in exI)
  apply (simp add:greatest_def Lower_def alphabet closure)
  apply (safe)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (auto)[1]
  apply (metis WF_ALPHA_PREDICATE_OVER_alphabet)
  apply (metis WF_ALPHA_PREDICATE_OVER_alphabet)
  apply (rule_tac x="SupA a A" in exI)
  apply (simp add:least_def Upper_def alphabet closure)
  apply (safe)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (force)
  apply (rule_tac x="InfA a A" in exI)
  apply (simp add:greatest_def Lower_def alphabet closure)
  apply (safe)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (force)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (force)
done

interpretation WF_ALPHA_PREDICATE_comlat: complete_lattice "WF_ALPHA_PREDICATE_gorder a"
  where "partial_object.carrier (WF_ALPHA_PREDICATE_gorder a) = WF_ALPHA_PREDICATE_OVER a"
    and "\<And> A. \<lbrakk> A \<subseteq> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow> sup (WF_ALPHA_PREDICATE_gorder a) A = SupA a A"
  apply (simp) 
  apply (simp_all add:WF_ALPHA_PREDICATE_gorder_def)
  apply (simp add:Lattice.sup_def)
  apply (rule some_equality)
  apply (simp add:least_def Upper_def alphabet closure)
  apply (safe)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (force)
  apply (simp add:least_def Upper_def alphabet closure)
  apply (auto)
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (simp add:EvalA_SupA eval)
  apply (force)
  apply (utp_alpha_tac2)


thm WF_ALPHA_PREDICATE_comlat.sup_closed





interpretation WF_ALPHA_PREDICATE_po: partial_order "WF_ALPHA_PREDICATE_gorder a"
  apply (unfold_locales)
  apply (simp_all add: WF_ALPHA_PREDICATE_gorder_def)
done

thm WF_ALPHA_PREDICATE_po.le_trans
*)

end
