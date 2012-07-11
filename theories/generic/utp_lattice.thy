(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_lattice.thy                                          *)
(* Authors: Simon Foster and Frank Zeyda, University of York                  *)
(******************************************************************************)

header {* Predicate Lattice *}

theory utp_lattice
imports utp_gen_pred utp_eval_tactic utp_function
begin

text {* This theory provides definitions for predicate lattices. *}

context GEN_PRED
begin

subsection {* Top and Bottom *}

definition BotP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<bottom>p") where
"BotP a = TrueP a"

definition TopP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<top>p") where
"TopP a = FalseP a"

subsection {* Supremum and Infimum *}

definition SupP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE set \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<Squnion>") where
"a \<in> WF_ALPHABET \<and>
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<longrightarrow>
 SupP a ps =
 (if ps = {} then (\<bottom>p a) else
   (\<Union> {\<alpha> p | p . p \<in> ps} , \<Inter> {\<beta> p | p . p \<in> ps}))"

definition InfP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE set \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<Sqinter>") where
"a \<in> WF_ALPHABET \<and>
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<longrightarrow>
 InfP a ps =
 (if ps = {} then (\<top>p a)
   else (\<Union> {\<alpha> p | p . p \<in> ps} , \<Union> {\<beta> p | p . p \<in> ps}))"

subsection {* Fixed Points *}

definition WFP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<mu>") where
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

subsection {* Theorems *}

text {* Making the theorem below a default dest rule incurs problems?! *}

theorem WF_BINDING_SET_Union [intro,binding] :
"ps \<subseteq> WF_BINDING_SET a \<Longrightarrow>
 \<Union> ps \<in> WF_BINDING_SET a"
apply (simp add: Union_eq WF_BINDING_SET_def)
apply (safe)
apply (auto) [1]
apply (rule_tac x = "x" in bexI)
apply (auto)
done

theorem WF_BINDING_SET_Inter [intro,binding] :
"\<lbrakk>ps \<subseteq> WF_BINDING_SET a; ps \<noteq> {}\<rbrakk> \<Longrightarrow>
 \<Inter> ps \<in> WF_BINDING_SET a"
apply (simp add: WF_BINDING_SET_def)
apply (auto)
done

subsubsection {* Closure Theorems *}

theorem BotP_closure [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 (\<bottom>p a) \<in> WF_ALPHA_PREDICATE"
  by (simp add: BotP_def closure)


theorem TopP_closure [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 (\<top>p a) \<in> WF_ALPHA_PREDICATE"
  by (simp add: TopP_def closure)

theorem SupP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<Squnion> a ps \<in> WF_ALPHA_PREDICATE"
apply (case_tac "ps = {}")
apply (simp add: SupP_def alphabet closure)+
apply (subgoal_tac "\<Union> {\<alpha> p | p . p \<in> ps} = a")
apply(auto simp add:WF_ALPHA_PREDICATE_def)[1]
apply(simp add:WF_ALPHA_PREDICATE_OVER_def)
apply(auto simp add:WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def)[1]
apply(subgoal_tac "{\<beta> p |p. p \<in> ps} \<subseteq> WF_BINDING_SET (\<Union>{\<alpha> p |p. p \<in> ps})")
apply(auto simp add:WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def)
done

theorem InfP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<Sqinter> a ps \<in> WF_ALPHA_PREDICATE"
apply (case_tac "ps = {}")
apply (simp add: InfP_def alphabet closure)+
apply (subgoal_tac "\<Union> {\<alpha> p | p . p \<in> ps} = a")
apply (auto simp add: WF_ALPHA_PREDICATE_def)[1]
apply(simp add:WF_ALPHA_PREDICATE_OVER_def)
apply(auto simp add:WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def)[1]
apply(subgoal_tac "{\<beta> p |p. p \<in> ps} \<subseteq> WF_BINDING_SET (\<Union>{\<alpha> p |p. p \<in> ps})")
apply(auto simp add:WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def)
done

theorem WFP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<mu> a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: WFP_def)
apply (rule SupP_closure)
apply (auto)
done

theorem SFP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<nu> a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: SFP_def)
apply (rule InfP_closure)
apply (auto)
done

subsubsection {* Alphabet Theorems *}

theorem BotP_alphabet [alphabet] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 \<alpha> (\<bottom>p a) = a"
apply (simp add: BotP_def closure alphabet)
done

theorem TopP_alphabet [alphabet] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 \<alpha> (\<top>p a) = a"
apply (simp add: TopP_def closure alphabet)
done

theorem SupP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<Squnion> a ps) = a"
apply (simp add: SupP_def WF_ALPHA_PREDICATE_OVER_def)
apply (auto simp add:alphabet)
done

theorem InfP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<Sqinter> a ps) = a"
apply (simp add: InfP_def WF_ALPHA_PREDICATE_OVER_def)
apply (auto simp add:alphabet)
done

theorem WFP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<mu> a f) = a"
apply (simp add: WFP_def)
apply (subst SupP_alphabet)
apply (auto simp add:alphabet)
done

theorem SFP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<nu> a f) = a"
apply (simp add: SFP_def)
apply (subst InfP_alphabet)
apply (auto simp add:alphabet)
done

subsubsection {* Evaluation Theorems *}

declare BotP_def [eval]
declare TopP_def [eval]

theorem EvalP_InfP [eval] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<Sqinter> a ps) b = (\<exists> p \<in> ps . EvalP p b)"
apply (simp add: EvalP_def closure)
apply (simp add: InfP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: TopP_def FalseP_def)
-- {* Subgoal 2 *}
apply (rule_tac x = "p" in bexI)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto dest: WF_ALPHA_PREDICATE_OVER_dest) [1]
apply (assumption)
-- {* Subgoal 3 *}
apply (rule_tac x = "\<beta> p" in exI)
apply (safe)
apply (rule_tac x = "p" in exI)
apply (simp)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto dest: WF_ALPHA_PREDICATE_OVER_dest) [1]
done

theorem EvalP_SupP [eval] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<Squnion> a ps) b = (\<forall> p \<in> ps . EvalP p b)"
apply (simp add: EvalP_def closure)
apply (simp add: SupP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: BotP_def TrueP_def)
-- {* Subgoal 2 *}
apply (drule_tac x = "\<beta> p" in spec)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto) [1]
apply (auto dest: WF_ALPHA_PREDICATE_OVER_dest) [1]
-- {* Subgoal 3 *}
apply (drule_tac x = "p" in bspec)
apply (assumption)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto dest: WF_ALPHA_PREDICATE_OVER_dest) [1]
done

declare WFP_def [eval]
declare SFP_def [eval]

subsubsection {* Lattice Interpretation *}

abbreviation pred_order ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE gorder" where
"pred_order a \<equiv>
 \<lparr> partial_object.carrier = WF_ALPHA_PREDICATE_OVER a,
   eq = (\<lambda> x y . x = y),
   le = (\<lambda> x y . x \<sqsubseteq> y) \<rparr>"

lemma SupP_lub :
  assumes "a \<in> WF_ALPHABET" "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "least (pred_order a) (\<Squnion> a ps) (Upper (pred_order a) ps)"
  apply(insert assms)
  apply(simp add:least_def Upper_def)
  apply(auto intro!:eval_intro dest:WF_ALPHA_PREDICATE_OVER_dest intro:closure alpha_closure simp add:alphabet)
  apply(simp add:eval closure alpha_closure WF_ALPHA_PREDICATE_OVER_def)
  apply(simp add:eval closure alpha_closure WF_ALPHA_PREDICATE_OVER_def taut)
  apply(auto)
  apply(erule_tac x="p" in allE)
  apply(auto)
done

lemma InfP_glb:
  assumes "a \<in> WF_ALPHABET" "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "greatest (pred_order a) (\<Sqinter> a ps) (Lower (pred_order a) ps)"
  apply(insert assms)
  apply(simp add:greatest_def Lower_def)
  apply(auto intro!:eval_intro dest:WF_ALPHA_PREDICATE_OVER_dest intro:closure alpha_closure simp add:alphabet)
  apply(simp add:eval closure alpha_closure WF_ALPHA_PREDICATE_OVER_def)
  apply(force)
  apply(simp add:eval closure alpha_closure WF_ALPHA_PREDICATE_OVER_def taut)
  apply(auto)
  apply(erule_tac x="p" in allE)
  apply(auto)
done

lemma pred_complete_lattice [simp, intro!] :
  "a \<in> WF_ALPHABET \<Longrightarrow> complete_lattice (pred_order a)"
apply (unfold_locales)
apply (simp_all add: WF_ALPHA_PREDICATE_OVER_def)
apply (auto)
apply (simp add:eval taut closure alphabet alpha_closure)
apply (simp add:eval taut closure alphabet alpha_closure)
apply(force)
apply (simp add:eval taut closure alphabet alpha_closure)
apply (simp add:eval taut closure alphabet alpha_closure)
apply (rule_tac x = "x \<and>p y" in exI)
apply (simp add: least_def Upper_def)
apply (safe)
apply (simp add:eval taut closure alphabet alpha_closure)+
apply (rule_tac x = "x \<or>p y" in exI)
apply (simp add: greatest_def Lower_def)
apply (safe)
apply (simp add:eval taut closure alphabet alpha_closure)+
apply (rule_tac x = "\<Squnion> a A" in exI)
apply (insert SupP_lub)
apply (auto simp add: WF_ALPHA_PREDICATE_OVER_def)
apply (rule_tac x = "\<Sqinter> a A" in exI)
apply (insert InfP_glb)
apply (auto simp add: WF_ALPHA_PREDICATE_OVER_def)
done

subsubsection {* Algebraic Properties *}

theorem InfP_Ref :
  assumes
    "a \<in> WF_ALPHABET"
    "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
    "p \<in> ps"
  shows "(\<Sqinter> a ps) \<sqsubseteq> p"
proof -
  from assms have r1: "p \<in> WF_ALPHA_PREDICATE"
    by (auto dest: WF_ALPHA_PREDICATE_OVER_dest)

  from assms have r2: "\<alpha> p = a"
    by (auto simp: WF_ALPHA_PREDICATE_OVER_def)

  with assms r1 r2 show "(\<Sqinter> a ps) \<sqsubseteq> p"
    by (auto simp add:eval taut closure alphabet alpha_closure)
qed

theorem SupP_Ref :
  assumes
    "a \<in> WF_ALPHABET"
    "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
    "p \<in> ps"
  shows "p \<sqsubseteq> (\<Squnion> a ps)"
proof -
  from assms have r1: "p \<in> WF_ALPHA_PREDICATE"
    by (auto dest: WF_ALPHA_PREDICATE_OVER_dest)

  from assms have r2: "\<alpha> p = a"
    by (auto simp: WF_ALPHA_PREDICATE_OVER_def)

  with assms r1 r2 show "p \<sqsubseteq> (\<Squnion> a ps)"
    by (auto simp add:eval taut closure alphabet alpha_closure)
qed
end
end
