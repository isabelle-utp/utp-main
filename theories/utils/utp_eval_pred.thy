(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_eval_pred.thy                                                    *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Predicates *}

theory utp_eval_pred
imports "../generic/utp_pred"
begin

text {* Theorem Attribute *}

ML {*
  structure eval =
    Named_Thms (val name = "eval" val description = "eval theorems")
*}

setup eval.setup

context PRED
begin

subsection {* Interpretation Function *}

definition EvalP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>_" [0, 1000] 51) where
"EvalP p b = (b \<in> p)"

notation EvalP ("\<lbrakk>_\<rbrakk>_" [0, 1000] 51)

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

theorem EvalP_ClosureP [eval] :
"\<lbrakk>p \<in> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>[p]\<rbrakk>b = (\<forall> b \<in> WF_BINDING . \<lbrakk>p\<rbrakk>b)"
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
end

context PRED
begin
theorem WF_BINDING_type [intro] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) : (type v)"
apply (simp add: WF_BINDING_def)
done

theorem WF_BINDING_update [intro] :
"\<lbrakk>b \<in> WF_BINDING; x : (type v)\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: WF_BINDING_def)
done

theorem Exists_WF_BINDING_override_single :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 (\<exists> b' \<in> WF_BINDING . f (b \<oplus> b' on {v})) =
 (\<exists> x \<in> carrier (type v) . f (b(v := x)))"
apply (simp add: override_on_singleton)
apply (safe)
apply (rule_tac x = "b' v" in bexI)
apply (assumption)
apply (unfold carrier_def)
apply (auto) [1]
apply (rule_tac x = "b(v := x)" in bexI)
apply (simp)
apply (auto)
done

theorem Forall_WF_BINDING_override_single :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 (\<forall> b' \<in> WF_BINDING . f (b \<oplus> b' on {v})) =
 (\<forall> x \<in> carrier (type v) . f (b(v := x)))"
apply (simp add: override_on_singleton)
apply (safe)
apply (drule_tac x = "b(v := x)" in bspec)
apply (unfold carrier_def)
apply (auto) [1]
apply (simp)
apply (drule_tac x = "b' v" in bspec)
apply (auto) [1]
apply (assumption)
done
end

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
  fun utp_pred_auto_simpset ctxt =
    (simpset_of ctxt)
*}

ML {*
  fun utp_pred_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_pred_simpset ctxt) i)
*}

ML {*
  fun utp_pred_auto_tac thms ctxt i =
    TRY (asm_full_simp_tac (utp_pred_simpset ctxt) i) THEN
    TRY (asm_full_simp_tac (utp_pred_auto_simpset ctxt) i) THEN
    (auto_tac ctxt)
*}

method_setup utp_pred_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_pred_tac thms ctxt))
*} "proof tactic for predicates"

method_setup utp_pred_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_pred_auto_tac thms ctxt))
*} "proof tactic for predicates with auto"

subsection {* Proof Experiments *}

context PRED
begin

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

theorem AndP_eq_FalseP :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p \<and>p \<not>p p = false"
apply (utp_pred_auto_tac)
done

theorem OrP_eq_TrueP :
"\<lbrakk>p \<in> WF_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<or>p \<not>p p = true"
apply (utp_pred_auto_tac)
done

theorem ForallP_NotP_taut :
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