(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_lattice.thy                                                *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Lattice *}

theory utp_alpha_lattice
imports "../core/utp_lattice" utp_alpha_laws
begin

instantiation WF_ALPHA_PREDICATE :: (VALUE) order
begin

instance
  apply (intro_classes)
  apply (utp_alpha_tac, utp_pred_auto_tac)+
done
end

instantiation WF_ALPHA_PREDICATE :: (VALUE) sup
begin

definition sup_WF_ALPHA_PREDICATE :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"sup_WF_ALPHA_PREDICATE = AndA"

instance ..
end

instantiation WF_ALPHA_PREDICATE :: (VALUE) inf
begin

definition inf_WF_ALPHA_PREDICATE :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"inf_WF_ALPHA_PREDICATE = OrA"

instance ..
end

definition BotA :: "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("\<bottom>\<^bsub>_\<^esub>") where
"BotA = TrueA"

theorem BotA_rep_eq:
  "Rep_WF_ALPHA_PREDICATE \<bottom>\<^bsub>a \<^esub>= (a, bot)"
  by (simp add:BotA_def TrueA_rep_eq bot_WF_PREDICATE_def)

definition TopA :: "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("\<top>\<^bsub>_\<^esub>") where
"TopA = FalseA"

theorem TopA_rep_eq:
  "Rep_WF_ALPHA_PREDICATE \<top>\<^bsub>a \<^esub>= (a, top)"
  by (simp add:TopA_def FalseA_rep_eq top_WF_PREDICATE_def)

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
   'VALUE WF_ALPHA_PREDICATE" where
"\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow>
 SupA a ps =
 (if ps = {} then \<bottom>\<^bsub>a\<^esub> else
   Abs_WF_ALPHA_PREDICATE (a, \<Squnion> (\<pi> ` ps)))"

theorem SupA_rep_eq:
  "\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow>
   Rep_WF_ALPHA_PREDICATE (SupA a ps) = (a, \<Squnion> (\<pi> ` ps))"
  apply (subgoal_tac "(a, \<Squnion> (\<pi> ` ps)) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:SupA_def BotA_rep_eq)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest)
done

definition InfA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE set \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" where
"\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow>
 InfA a ps =
 (if ps = {} then \<top>\<^bsub>a\<^esub> else
   Abs_WF_ALPHA_PREDICATE (a, \<Sqinter> (\<pi> ` ps)))"

theorem InfA_rep_eq:
  "\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow>
   Rep_WF_ALPHA_PREDICATE (InfA a ps) = (a, \<Sqinter> (\<pi> ` ps))"
  apply (subgoal_tac "(a, \<Sqinter> (\<pi> ` ps)) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:InfA_def TopA_rep_eq)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest)
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
  by (simp add:sup_WF_ALPHA_PREDICATE_def alphabet)

lemma inf_alphabet [alphabet]:
  "\<alpha> (p \<sqinter> q) = \<alpha> p \<union>\<^sub>f \<alpha> q"
  by (simp add:inf_WF_ALPHA_PREDICATE_def alphabet)

lemma SupA_alphabet [alphabet]:
  "\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow> \<alpha> (SupA a ps) = a"
  by (simp add:pred_alphabet_def SupA_rep_eq)

lemma InfA_alphabet [alphabet]:
  "\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow> \<alpha> (InfA a ps) = a"
  by (simp add:pred_alphabet_def InfA_rep_eq)

subsubsection {* Evaluation laws *}

lemma EvalA_sup [evala]:
  "\<lbrakk>p \<squnion> q\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi> \<squnion> \<lbrakk>q\<rbrakk>\<pi>"
  by (simp add: sup_WF_ALPHA_PREDICATE_def sup_WF_PREDICATE_def evala)

lemma EvalA_inf [evala]:
  "\<lbrakk>p \<sqinter> q\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi> \<sqinter> \<lbrakk>q\<rbrakk>\<pi>"
  by (simp add: inf_WF_ALPHA_PREDICATE_def inf_WF_PREDICATE_def evala)
  
lemma EvalA_SupA [evala]: 
  "\<lbrakk>\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<rbrakk> \<Longrightarrow> \<lbrakk>SupA a ps\<rbrakk>\<pi> = \<Squnion> (EvalA ` ps)"
  by (simp add:SupA_rep_eq EvalA_def image_def)

lemma EvalA_InfA [evala]: 
  "\<lbrakk>\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<rbrakk> \<Longrightarrow> \<lbrakk>InfA a ps\<rbrakk>\<pi> = \<Sqinter> (EvalA ` ps)"
  by (simp add:InfA_rep_eq EvalA_def image_def)

  
lemma L1: 
  "\<lbrakk> \<alpha> P = a; \<forall> p\<in>S. \<alpha> p = a \<rbrakk> \<Longrightarrow>
   P \<sqsubseteq> InfA a S \<longleftrightarrow> (\<forall> X\<in>S. P \<sqsubseteq> X)"
  by (simp add:EvalA_RefinementA alphabet evala Lattice_L1)

lemma L2:
  "\<lbrakk> \<alpha> Q = a; \<forall> p\<in>S. \<alpha> p = a \<rbrakk> \<Longrightarrow>
  ((SupA a S) \<sqinter> Q) = SupA a {P \<sqinter> Q | P. P \<in> S}"
  apply (subgoal_tac "\<forall> p \<in> {P \<sqinter> Q | P. P \<in> S}. \<alpha> p = a")
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (simp add:EvalA_SupA EvalA_inf Lattice_L2)
  apply (subgoal_tac "{P \<sqinter> \<lbrakk>Q\<rbrakk>\<pi> |P. P \<in> EvalA ` S} = EvalA ` {P \<sqinter> Q |P. P \<in> S}")
  apply (simp)
oops

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

end
