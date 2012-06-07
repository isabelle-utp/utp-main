(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_lattice.thy                                          *)
(* Author: Simon Foster and Frank Zeyda, University of York                   *)
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

theorem WF_ALPHA_PREDICATE_OVER_closure :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 p \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_ALPHA_PREDICATE_OVER_def)
done

theorem WF_BINDING_SET_Union [intro] :
"ps \<subseteq> WF_BINDING_SET a \<Longrightarrow>
 \<Union> ps \<in> WF_BINDING_SET a"
apply (simp add: Union_eq WF_BINDING_SET_def)
apply (safe)
apply (auto) [1]
apply (rule_tac x = "x" in bexI)
apply (auto)
done

theorem WF_BINDING_SET_Inter [intro] :
"\<lbrakk>ps \<subseteq> WF_BINDING_SET a; ps \<noteq> {}\<rbrakk> \<Longrightarrow>
 \<Inter> ps \<in> WF_BINDING_SET a"
apply (simp add: WF_BINDING_SET_def)
apply (auto)
done

subsubsection {* Closure Theorems *}

theorem BotP_closure [simp] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 (\<bottom>p a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: BotP_def)
done

theorem TopP_closure [simp] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 (\<top>p a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: TopP_def)
done

theorem SupP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<Squnion> a ps \<in> WF_ALPHA_PREDICATE"
apply (case_tac "ps = {}")
apply (simp add: SupP_def)
apply (simp add: SupP_def)
apply (simp add: WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def)
apply (safe)
apply (auto) [1]
apply (rule WF_BINDING_SET_Inter)
apply (auto)
apply (subgoal_tac "\<Union> {\<alpha> p | p . p \<in> ps} = \<alpha> p")
apply (auto)
done

theorem InfP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<Sqinter> a ps \<in> WF_ALPHA_PREDICATE"
apply (case_tac "ps = {}")
apply (simp add: InfP_def)
apply (simp add: InfP_def)
apply (simp add: WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def)
apply (safe)
apply (auto) [1]
apply (rule WF_BINDING_SET_Union)
apply (auto)
apply (subgoal_tac "\<Union> {\<alpha> p | p . p \<in> ps} = \<alpha> p")
apply (auto)
done

theorem WFP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<mu> a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: WFP_def)
apply (rule SupP_closure)
apply (auto)
done

theorem SFP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<nu> a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: SFP_def)
apply (rule InfP_closure)
apply (auto)
done

subsubsection {* Alphabet Theorems *}

theorem BotP_alphabet [simp] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 \<alpha> (\<bottom>p a) = a"
apply (simp add: BotP_def)
done

theorem TopP_alphabet [simp] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 \<alpha> (\<top>p a) = a"
apply (simp add: TopP_def)
done

theorem SupP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<Squnion> a ps) = a"
apply (simp add: SupP_def WF_ALPHA_PREDICATE_OVER_def)
apply (auto)
done

theorem InfP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<Sqinter> a ps) = a"
apply (simp add: InfP_def WF_ALPHA_PREDICATE_OVER_def)
apply (auto)
done

theorem WFP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<mu> a f) = a"
apply (simp add: WFP_def)
apply (subst SupP_alphabet)
apply (auto)
done

theorem SFP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_ALPHA_FUNCTION_BETWEEN a a\<rbrakk> \<Longrightarrow>
 \<alpha> (\<nu> a f) = a"
apply (simp add: SFP_def)
apply (subst InfP_alphabet)
apply (auto)
done

subsubsection {* Evaluation Theorems *}

declare BotP_def [eval]
declare TopP_def [eval]

theorem EvalP_InfP [eval] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<Sqinter> a ps) b = (\<exists> p \<in> ps . EvalP p b)"
apply (simp add: EvalP_def)
apply (simp add: InfP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: TopP_def FalseP_def)
-- {* Subgoal 2 *}
apply (rule_tac x = "p" in bexI)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto dest: WF_ALPHA_PREDICATE_OVER_closure) [1]
apply (assumption)
-- {* Subgoal 3 *}
apply (rule_tac x = "\<beta> p" in exI)
apply (safe)
apply (rule_tac x = "p" in exI)
apply (simp)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto dest: WF_ALPHA_PREDICATE_OVER_closure) [1]
done

theorem EvalP_SupP [eval] :
"\<lbrakk>a \<in> WF_ALPHABET;
 ps \<subseteq> WF_ALPHA_PREDICATE_OVER a;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<Squnion> a ps) b = (\<forall> p \<in> ps . EvalP p b)"
apply (simp add: EvalP_def)
apply (simp add: SupP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: BotP_def TrueP_def)
-- {* Subgoal 2 *}
apply (drule_tac x = "\<beta> p" in spec)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto) [1]
apply (auto dest: WF_ALPHA_PREDICATE_OVER_closure) [1]
-- {* Subgoal 3 *}
apply (drule_tac x = "p" in bspec)
apply (assumption)
apply (subgoal_tac "p \<in> WF_ALPHA_PREDICATE")
apply (simp add: EvalP_def)
apply (auto dest: WF_ALPHA_PREDICATE_OVER_closure) [1]
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
proof (auto simp add: least_def Upper_def)

  from assms have r1: "ps \<subseteq> WF_ALPHA_PREDICATE"
    by (auto simp add: WF_ALPHA_PREDICATE_OVER_def)

  with assms have r2: "\<forall>x\<in>ps . \<alpha> (\<Squnion> a ps) = \<alpha> x"
    by (auto simp add: SupP_def WF_ALPHA_PREDICATE_OVER_def)

  with assms have r3: "\<forall>x\<in>ps . {\<beta> p | p . p \<in> ps} \<subseteq> WF_BINDING_SET (\<alpha> x)"
    apply (auto simp only: WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def)
    apply (subgoal_tac "\<alpha> x = a")
    apply (subgoal_tac "\<alpha> p = a")
    apply (force)
    apply (force)
    apply (force)
  done

  with assms r1 have r4: "\<Squnion> a ps \<in> WF_ALPHA_PREDICATE"
    by (simp add: SupP_closure)

  fix x
  show "\<lbrakk>x \<in> ps; x \<in> WF_ALPHA_PREDICATE_OVER a\<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Squnion> a ps"
    proof -
      assume assm1: "x \<in> ps" "x \<in> WF_ALPHA_PREDICATE_OVER a"
      from assms assm1 r1 r2 r3 r4 show ?thesis
        apply (simp add: SupP_def WF_ALPHA_PREDICATE_OVER_def)
        apply (rule conjI)
        apply (force)
        apply (rule impI)
        apply (utp_pred_taut_tac)
        apply (auto simp add: EvalP_def)
      done
  qed

  from assms r2 r4 show r6: "\<Squnion> a ps \<in> WF_ALPHA_PREDICATE_OVER a"
    apply (simp add: WF_ALPHA_PREDICATE_OVER_def SupP_def)
    apply (auto)
  done

  from assms r6 show
    "\<lbrakk>x \<in> WF_ALPHA_PREDICATE_OVER a;
     \<forall> y . y \<in> ps \<and> y \<in> WF_ALPHA_PREDICATE_OVER a \<longrightarrow> y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> \<Squnion> a ps \<sqsubseteq> x"
  proof -
    assume assms': "x \<in> WF_ALPHA_PREDICATE_OVER a"
      "\<forall> y . y \<in> ps \<and> y \<in> WF_ALPHA_PREDICATE_OVER a \<longrightarrow> y \<sqsubseteq> x"

    with assms have r7: "\<alpha> (\<Squnion> a ps) = \<alpha> x"
      by (simp add: WF_ALPHA_PREDICATE_OVER_def)

    from assms assms' have r8: "x \<in> WF_ALPHA_PREDICATE"
      by (simp add: WF_ALPHA_PREDICATE_OVER_def)

    from assms assms' r4 r6 r7 r8 r1 show ?thesis
    apply (simp add: WF_ALPHA_PREDICATE_OVER_def)
    apply (auto)
    apply (subgoal_tac "\<Squnion> (\<alpha> x) ps \<in> WF_ALPHA_PREDICATE")
    apply (subgoal_tac "\<alpha> (\<Squnion> (\<alpha> x) ps) = \<alpha> x")
    apply (utp_pred_taut_tac)
    apply (simp add: EvalP_def)
    apply (auto)
    apply (subgoal_tac "\<alpha> x \<in> WF_ALPHABET")
    apply (subgoal_tac "ps \<subseteq> WF_ALPHA_PREDICATE_OVER (\<alpha> x)")
    apply (simp add: SupP_def)
    apply (simp add: BotP_def)
    apply (simp add: TrueP_def)
    apply (force)
    apply (simp add: WF_ALPHA_PREDICATE_OVER_def)
    apply (force)
    apply (metis (no_types) SupP_alphabet assms(1) assms(2) r7)
    apply (metis (no_types) SupP_alphabet assms(1) assms(2) r7)
    apply (metis (no_types) SupP_alphabet SupP_closure assms(1) assms(2) r7)
  done
qed
qed

lemma InfP_glb:
  assumes "a \<in> WF_ALPHABET" "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "greatest (pred_order a) (\<Sqinter> a ps) (Lower (pred_order a) ps)"
proof (auto simp add: greatest_def Lower_def)
  fix x
  assume assm1: "x \<in> ps" "x \<in> WF_ALPHA_PREDICATE_OVER a"
  with assms show "\<Sqinter> a ps \<sqsubseteq> x"
    apply (subgoal_tac "\<alpha> (\<Sqinter> a ps) = a")
    apply (subgoal_tac "\<alpha> (\<Sqinter> a ps) = \<alpha> x")
    apply (subgoal_tac "\<Sqinter> a ps \<in> WF_ALPHA_PREDICATE")
    apply (simp add: InfP_def WF_ALPHA_PREDICATE_OVER_def)
    apply (rule conjI)
    apply (force)
    apply (rule impI)
    apply (utp_pred_taut_tac)
    apply (simp add: EvalP_def)
    apply (fast)
    apply (simp add: InfP_closure)
    apply (simp add: InfP_alphabet WF_ALPHA_PREDICATE_OVER_def)
    apply (simp add: InfP_alphabet)
  done
  next

  from assms show r1: "\<Sqinter> a ps \<in> WF_ALPHA_PREDICATE_OVER a"
    by (simp add: WF_ALPHA_PREDICATE_OVER_def InfP_closure InfP_alphabet)

  fix x
  assume assm1: "x \<in> WF_ALPHA_PREDICATE_OVER a"
    "\<forall> y . y \<in> ps \<and> y \<in> WF_ALPHA_PREDICATE_OVER a \<longrightarrow> x \<sqsubseteq> y"
  with assms r1 show "x \<sqsubseteq> \<Sqinter> a ps"
    apply (simp only: WF_ALPHA_PREDICATE_OVER_def)
    apply (auto)
    apply (utp_pred_taut_tac)
    apply (simp add: EvalP_def)
    apply (auto)
    apply (subgoal_tac "\<alpha> x \<in> WF_ALPHABET")
    apply (subgoal_tac "ps \<subseteq> WF_ALPHA_PREDICATE_OVER (\<alpha> x)")
    apply (simp add: InfP_def)
    apply (simp add: WF_ALPHA_PREDICATE_OVER_def)
    apply (auto)
    apply (case_tac "ps = {}")
    apply (simp only: FalseP_def TopP_def)
    apply (simp)
    apply (simp only: FalseP_def TopP_def)
    apply (simp)
    apply (erule exE)
    apply (erule conjE)
    apply (erule exE)
    apply (erule conjE)
    apply (simp)
    apply (erule_tac x = "p" in allE)
    apply (force)
    apply (simp add: WF_ALPHA_PREDICATE_OVER_def)
    apply (force)
  done
qed

lemma pred_complete_lattice [simp, intro!] :
  "a \<in> WF_ALPHABET \<Longrightarrow> complete_lattice (pred_order a)"
apply (unfold_locales)
apply (simp_all add: WF_ALPHA_PREDICATE_OVER_def)
apply (auto)
apply (utp_pred_taut_tac)
apply (utp_pred_taut_tac)
apply (rule_tac ballI)
apply (erule_tac x = "b" in ballE)+
apply (auto)
apply (utp_pred_taut_tac)
apply (rule_tac x = "x \<and>p y" in exI)
apply (simp add: least_def Upper_def)
apply (safe)
apply (utp_pred_taut_tac)+
apply (rule_tac x = "x \<or>p y" in exI)
apply (simp add: greatest_def Lower_def)
apply (safe)
apply (utp_pred_taut_tac)+
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
    by (auto dest: WF_ALPHA_PREDICATE_OVER_closure)

  from assms have r2: "\<alpha> p = a"
    by (auto simp: WF_ALPHA_PREDICATE_OVER_def)

  with assms r1 r2 show "(\<Sqinter> a ps) \<sqsubseteq> p"
    by (utp_pred_taut_tac, auto)
qed

theorem SupP_Ref :
  assumes
    "a \<in> WF_ALPHABET"
    "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
    "p \<in> ps"
  shows "p \<sqsubseteq> (\<Squnion> a ps)"
proof -
  from assms have r1: "p \<in> WF_ALPHA_PREDICATE"
    by (auto dest: WF_ALPHA_PREDICATE_OVER_closure)

  from assms have r2: "\<alpha> p = a"
    by (auto simp: WF_ALPHA_PREDICATE_OVER_def)

  with assms r1 r2 show "p \<sqsubseteq> (\<Squnion> a ps)"
    by (utp_pred_taut_tac)
qed
end
end
