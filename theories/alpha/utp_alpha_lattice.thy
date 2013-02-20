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

definition TopA :: "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("\<top>\<^bsub>_\<^esub>") where
"TopA = FalseA"

declare sup_WF_ALPHA_PREDICATE_def [evala]
declare inf_WF_ALPHA_PREDICATE_def [evala]
declare BotA_def [evala]
declare TopA_def [evala]

lemma RefinementA_intro [intro]: 
  "\<lbrakk> \<alpha> p = \<alpha> q; \<pi> p \<sqsubseteq> \<pi> q \<rbrakk> \<Longrightarrow> p \<sqsubseteq> q"
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp add:EvalA_def)
done

definition SupP ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE set \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" where
"\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow>
 SupP a ps =
 (if ps = {} then \<bottom>\<^bsub>a\<^esub> else
   Abs_WF_ALPHA_PREDICATE (a, \<Squnion> (\<pi> ` ps)))"

definition InfP ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE set \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" where
"\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow>
 InfP a ps =
 (if ps = {} then \<top>\<^bsub>a\<^esub> else
   Abs_WF_ALPHA_PREDICATE (a, \<Sqinter> (\<pi> ` ps)))"

(*
lemma InfP_alphabet:
  "\<forall> p\<in>ps. \<alpha> p \<subseteq>\<^sub>f a \<Longrightarrow> \<alpha> (InfP a ps) = a"
  apply (simp add:InfP_def)
  apply (utp_alpha_tac)

lemma "\<alpha> P = a \<Longrightarrow> P \<sqsubseteq> InfP a S"

subsection {* Fixed Points *}

definition WFP ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHA_FUNCTION \<Rightarrow>
   'VALUE ALPHA_PREDICATE" ("\<mu>") where
"a \<in> WF_ALPHABET \<and>
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a \<longrightarrow>
 WFP a f = \<Squnion> a {x \<in> WF_ALPHA_PREDICATE_OVER a . f x \<sqsubseteq> x}"

definition SFP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<nu>") where
"a \<in> WF_ALPHABET \<and>
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a \<longrightarrow>
 SFP a f = \<Sqinter> a {x \<in> WF_ALPHA_PREDICATE_OVER a . x \<sqsubseteq> f x}"


lemma BotA_least: "\<bottom>\<^bsub>\<alpha> p\<^esub> \<sqsubseteq> p"
  by (utp_alpha_tac, utp_pred_tac)

lemma TopA_greatest: "p \<sqsubseteq> \<top>\<^bsub>\<alpha> p\<^esub>"
  by (utp_alpha_tac, utp_pred_tac)
*)

end
