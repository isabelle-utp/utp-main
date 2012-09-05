(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_pred_tac.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Predicates *}

theory utp_pred_tac
imports "../core/utp_pred"
begin

text {* Theorem Attribute *}

ML {*
  structure eval =
    Named_Thms (val name = @{binding eval} val description = "eval theorems")
*}

setup eval.setup

context PRED
begin

subsection {* Interpretation Function *}

definition EvalP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>_" [0, 1000] 51) where
"EvalP p b = (b \<in> p)"

subsection {* Transfer Theorems *}

theorem EvalP_simp [eval] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 = p2 \<longleftrightarrow> (\<forall> b \<in> WF_BINDING . \<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: EvalP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem EvalP_intro :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 (\<forall> b \<in> WF_BINDING . \<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)\<rbrakk> \<Longrightarrow> p1 = p2"
apply (simp add: EvalP_simp)
done

subsection {* Distribution Theorems *}

theorem EvalP_TrueP [eval] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>true\<rbrakk>b = True"
apply (simp add: EvalP_def)
apply (simp add: TrueP_def)
done

theorem EvalP_FalseP [eval] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>false\<rbrakk>b = False"
apply (simp add: EvalP_def)
apply (simp add: FalseP_def)
done

theorem EvalP_NotP [eval] :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<not>p p\<rbrakk>b = (\<not>\<lbrakk>p\<rbrakk>b)"
apply (simp add: EvalP_def)
apply (simp add: NotP_def)
done

theorem EvalP_AndP [eval] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<and>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<and> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: EvalP_def)
apply (simp add: AndP_def)
done

theorem EvalP_OrP [eval] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<or>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<or> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: EvalP_def)
apply (simp add: OrP_def)
done

theorem EvalP_ImpliesP [eval] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<Rightarrow>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: ImpliesP_def)
apply (simp add: EvalP_OrP EvalP_NotP closure)
done

theorem EvalP_IffP [eval] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<Leftrightarrow>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: IffP_def)
apply (simp add: EvalP_AndP EvalP_ImpliesP closure)
apply (auto)
done

theorem EvalP_ExistsP [eval] :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<exists>p vs . p\<rbrakk>b = (\<exists> b' \<in> WF_BINDING . \<lbrakk>p\<rbrakk>(b \<oplus> b' on vs))"
apply (simp add: ExistsP_def)
apply (simp add: EvalP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (clarsimp)
apply (rule_tac x = "b1" in bexI)
apply (simp)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "b \<oplus> b' on vs" in exI)
apply (rule_tac x = "b" in exI)
apply (simp)
done

theorem EvalP_ForallP [eval] :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<forall>p vs . p\<rbrakk>b = (\<forall> b' \<in> WF_BINDING . \<lbrakk>p\<rbrakk>(b \<oplus> b' on vs))"
apply (simp add: ForallP_def)
apply (simp add: EvalP_NotP EvalP_ExistsP closure)
done

theorems EvalP_QuantP =
  EvalP_ExistsP
  EvalP_ForallP

theorem EvalP_ClosureP [eval] :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>[p]p\<rbrakk>b = (\<forall> b \<in> WF_BINDING . \<lbrakk>p\<rbrakk>b)"
apply (simp add: ClosureP_def)
apply (simp add: EvalP_ForallP)
done

theorem EvalP_RefP [eval] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<sqsubseteq>p p2\<rbrakk>b = (\<forall> b \<in> WF_BINDING . \<lbrakk>p2\<rbrakk>b \<longrightarrow> \<lbrakk>p1\<rbrakk>b)"
apply (simp add: RefP_def)
apply (simp add: EvalP_ClosureP EvalP_ImpliesP closure)
done

declare Tautology_def [eval]
declare Contradiction_def [eval]
declare Refinement_def [eval]

subsection {* Support Theorems *}

theorem EvalP_ExistsP_singleton :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<exists>p {x} . p\<rbrakk>b = (\<exists> v \<in> carrier (type x) . \<lbrakk>p\<rbrakk>(b(x := v)))"
apply (simp add: ExistsP_def)
apply (simp add: EvalP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "b1 x" in bexI)
apply (simp add: override_on_singleton)
apply (simp add: WF_BINDING_app_carrier)
-- {* Subgoal 2 *}
apply (rule_tac x = "b(x := v)" in exI)
apply (rule_tac x = "b" in exI)
apply (simp add: override_on_singleton)
done

theorem EvalP_ForallP_singleton :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<forall>p {x} . p\<rbrakk>b = (\<forall> v \<in> carrier (type x) . \<lbrakk>p\<rbrakk>(b(x := v)))"
apply (simp add: ForallP_def)
apply (simp add: EvalP_NotP EvalP_ExistsP_singleton closure)
done

theorems EvalP_QuantP_singleton =
  EvalP_ExistsP_singleton
  EvalP_ForallP_singleton

subsection {* Normalisation *}

theorem NotP_NotP :
"p \<in> WF_PREDICATE \<Longrightarrow>
 \<not>p \<not>p p = p"
apply (auto simp: NotP_def)
done

theorem ExistsP_empty :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p {} . p) = p"
apply (simp add: ExistsP_def)
apply (auto)
done

theorem ForallP_empty :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p {} . p) = p"
apply (simp add: ForallP_def)
apply (simp add: ExistsP_empty closure)
apply (simp add: NotP_NotP)
done

theorem ExistsP_insert :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p (insert v vs) . p) = (\<exists>p {v} . (\<exists>p vs . p))"
apply (simp add: ExistsP_def [of "(\<exists>p vs . p)"] closure)
apply (simp add: ExistsP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "b1 \<oplus> b2 on vs" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (rule_tac x = "b1" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "b1a" in exI)
apply (rule_tac x = "b2a \<oplus> b2 on {v}" in exI)
apply (simp)
apply (simp add: override_on_assoc closure)
done

theorem ForallP_insert :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p (insert v vs) . p) = (\<forall>p {v} . (\<forall>p vs . p))"
apply (simp add: ForallP_def closure)
apply (simp add: NotP_NotP closure)
apply (subst ExistsP_insert)
apply (simp_all add: closure)
done

theorem ExistsP_atomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p {x} . (\<exists>p (insert y vs) . p)) =
 (\<exists>p (insert x (insert y vs)) . p)"
apply (auto intro!: sym [OF ExistsP_insert])
done

theorem ForallP_atomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p {x} . (\<forall>p (insert y vs) . p)) =
 (\<forall>p (insert x (insert y vs)) . p)"
apply (auto intro!: sym [OF ForallP_insert])
done

theorems QuantP_atomise =
  ExistsP_atomise
  ForallP_atomise

theorem ExistsP_deatomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p (insert x (insert y vs)) . p) =
 (\<exists>p {x} . (\<exists>p (insert y vs) . p))"
apply (auto intro!: ExistsP_insert)
done

theorem ForallP_deatomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p (insert x (insert y vs)) . p) =
 (\<forall>p {x} . (\<forall>p (insert y vs) . p))"
apply (auto intro!: ForallP_insert)
done

theorems QuantP_deatomise =
  ExistsP_deatomise
  ForallP_deatomise

subsection {* Proof Tactics *}

text {*
  We note that the proof method is also generic and does not have to be
  recreated for concrete instantiations of the @{term PRED} locale.
*}

ML {*
  fun utp_pred_simpset ctxt =
    (simpset_of ctxt)
      addsimps (eval.get ctxt)
      addsimps (closure.get ctxt);
*}

ML {*
  fun utp_atomise_simpset ctxt =
    (simpset_of ctxt)
      addsimps @{thms QuantP_atomise}
      addsimps (closure.get ctxt);
*}

ML {*
  fun utp_deatomise_simpset ctxt =
    (simpset_of ctxt)
      addsimps @{thms QuantP_deatomise}
      addsimps (closure.get ctxt);
*}

ML {*
  fun utp_singleton_simpset ctxt =
    (simpset_of ctxt)
      addsimps (eval.get ctxt)
      delsimps @{thms EvalP_QuantP}
      addsimps @{thms EvalP_QuantP_singleton}
      addsimps (closure.get ctxt);
*}

ML {*
  fun utp_auto_simpset ctxt =
    (simpset_of ctxt);
*}

ML {*
  fun utp_pred_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_pred_simpset ctxt) i))
*}

ML {*
  fun utp_pred_atomise_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_atomise_simpset ctxt) i) THEN
      TRY (asm_full_simp_tac (utp_pred_simpset ctxt) i))
*}

ML {*
  fun utp_pred_deatomise_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_deatomise_simpset ctxt) i) THEN
      TRY (asm_full_simp_tac (utp_singleton_simpset ctxt) i))
*}

text {* Should we atomise or deatomise below? *}

ML {*
  fun utp_pred_auto_tac thms ctxt i =
    CHANGED ((
      (asm_full_simp_tac (utp_pred_simpset ctxt)) THEN_ALL_NEW
      (asm_full_simp_tac (utp_auto_simpset ctxt)) THEN_ALL_NEW
      (SELECT_GOAL (auto_tac ctxt))) i)
*}
end

method_setup utp_pred_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_pred_tac thms ctxt))
*} "proof tactic for predicates"

method_setup utp_pred_atomise_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_pred_atomise_tac thms ctxt))
*} "proof tactic for predicates with atomisation"

method_setup utp_pred_deatomise_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_pred_deatomise_tac thms ctxt))
*} "proof tactic for predicates with deatomisation"

method_setup utp_pred_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_pred_auto_tac thms ctxt))
*} "proof tactic for predicates with auto"

subsection {* Proof Experiments *}

context PRED
begin

theorem ExistsP_norm_test :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p {x} . \<exists>p {y} . p) = (\<exists>p {y} . \<exists>p {x} . p)"
apply (utp_pred_atomise_tac)
apply (subgoal_tac "{x, y} = {y, x}")
apply (simp)
apply (auto)
done

theorem AndP_assoc :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p (p2 \<and>p p3) = (p1 \<and>p p2) \<and>p p3"
apply (utp_pred_auto_tac)
done

theorem AndP_OrP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p (p2 \<or>p p3) = (p1 \<and>p p2) \<or>p (p1 \<and>p p3)"
apply (utp_pred_auto_tac)
done

theorem NotP_FalseP :
"true = \<not>p false"
apply (utp_pred_auto_tac)
done

theorem AndP_comm_taut :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 taut (p1 \<and>p p2) \<Leftrightarrow>p (p2 \<and>p p1)"
apply (utp_pred_auto_tac)
done

theorem AndP_equals_FalseP :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p \<and>p \<not>p p = false"
apply (utp_pred_auto_tac)
done

theorem OrP_equals_TrueP :
"\<lbrakk>p \<in> WF_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<or>p \<not>p p = true"
apply (utp_pred_auto_tac)
done

theorem ForallP_NotP_ExistsP_taut :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 taut (\<forall>p vs . \<not>p p) \<Leftrightarrow>p \<not>p (\<exists>p vs . p)"
apply (utp_pred_auto_tac)
done

theorem OrP_RefP_taut :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 taut p1 \<or>p p2 \<sqsubseteq>p p1"
apply (utp_pred_auto_tac)
done

theorem OrP_ref :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 (\<alpha> p1) = (\<alpha> p2)\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<sqsubseteq> p1"
apply (utp_pred_auto_tac)
done

text {* The theorem below would be tedious to prove by mere rewriting. *}

lemma AndP_reorder_test :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE;
 p4 \<in> WF_PREDICATE;
 p5 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p p2 \<and>p p3 \<and>p p4 \<and>p p5 = (p1 \<and>p p5) \<and>p p3 \<and>p (p4 \<and>p p2)"
apply (utp_pred_auto_tac)
done
end
end