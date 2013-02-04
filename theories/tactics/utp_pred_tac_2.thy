(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_pred_tac.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Predicates *}

theory utp_pred_tac_2
imports "../core/utp_pred_2"
begin

text {* Theorem Attribute *}

ML {*
  structure eval =
    Named_Thms (val name = @{binding eval} val description = "eval theorems")
*}

setup eval.setup

subsection {* Interpretation Function *}

definition EvalP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_BINDING \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>_" [0, 1000] 51) where
"EvalP p = (\<lambda> b. b \<in> destPRED p)"

subsection {* Transfer Theorems *}

theorem EvalP_simp [eval] :
"p1 = p2 \<longleftrightarrow> (\<forall> b. \<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)"
  by (auto simp add: EvalP_def)

theorem EvalP_intro :
"\<lbrakk> \<And> b. \<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b \<rbrakk> \<Longrightarrow> p1 = p2"
  by (simp add: EvalP_simp)

subsection {* Distribution Theorems *}

theorem EvalP_LiftP [eval] :
"\<lbrakk>LiftP f\<rbrakk>b = f b"
apply (simp add: EvalP_def)
apply (simp add: LiftP_def)
done 

theorem EvalP_EqualsP [eval] :
"\<lbrakk>v =p x\<rbrakk>b = (\<langle>b\<rangle>\<^sub>bv = x)"
apply (simp add: EqualsP_def)
apply (simp add: EvalP_LiftP)
done

theorem EvalP_TrueP [eval] :
"\<lbrakk>true\<rbrakk>b = True"
apply (simp add: EvalP_def)
apply (simp add: TrueP_def)
done

theorem EvalP_FalseP [eval] :
"\<lbrakk>false\<rbrakk>b = False"
apply (simp add: EvalP_def)
apply (simp add: FalseP_def)
done

theorem EvalP_NotP [eval] :
"\<lbrakk>\<not>p p\<rbrakk>b = (\<not>\<lbrakk>p\<rbrakk>b)"
apply (simp add: EvalP_def)
apply (simp add: NotP_def)
done

theorem EvalP_AndP [eval] :
"\<lbrakk>p1 \<and>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<and> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: EvalP_def)
apply (simp add: AndP_def)
done

theorem EvalP_OrP [eval] :
"\<lbrakk>p1 \<or>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<or> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: EvalP_def)
apply (simp add: OrP_def)
done

theorem EvalP_ImpliesP [eval] :
"\<lbrakk>p1 \<Rightarrow>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: ImpliesP_def)
apply (simp add: EvalP_OrP EvalP_NotP closure)
done

theorem EvalP_IffP [eval] :
"\<lbrakk>p1 \<Leftrightarrow>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (simp add: IffP_def)
apply (simp add: EvalP_AndP EvalP_ImpliesP closure)
apply (auto)
done

theorem EvalP_ExistsP [eval] :
"\<lbrakk>\<exists>p vs . p\<rbrakk>b = (\<exists> b'. \<lbrakk>p\<rbrakk>(b \<oplus>\<^sub>b b' on vs))"
apply (simp add: ExistsP_def)
apply (simp add: EvalP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "b1" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "b \<oplus>\<^sub>b b' on vs" in exI)
apply (simp)
apply (rule_tac x = "b" in exI)
apply (simp)
done

theorem EvalP_ForallP [eval] :
"\<lbrakk>\<forall>p vs . p\<rbrakk>b = (\<forall> b'. \<lbrakk>p\<rbrakk>(b \<oplus>\<^sub>b b' on vs))"
apply (simp add: ForallP_def)
apply (simp add: EvalP_NotP EvalP_ExistsP closure)
done

theorems EvalP_QuantP =
  EvalP_ExistsP
  EvalP_ForallP

theorem EvalP_ClosureP [eval] :
"\<lbrakk>[p]p\<rbrakk>b = (\<forall> b. \<lbrakk>p\<rbrakk>b)"
apply (simp add: ClosureP_def)
apply (simp add: EvalP_ForallP)
done

theorem EvalP_RefP [eval] :
"\<lbrakk>p1 \<sqsubseteq>p p2\<rbrakk>b = (\<forall> b. \<lbrakk>p2\<rbrakk>b \<longrightarrow> \<lbrakk>p1\<rbrakk>b)"
apply (simp add: RefP_def)
apply (simp add: EvalP_ClosureP EvalP_ImpliesP closure)
done

declare Tautology_def [eval]
declare Contradiction_def [eval]
(* declare Refinement_def [eval] *)
declare less_eq_WF_PREDICATE_def [eval]

subsection {* Support Theorems *}

theorem EvalP_ExistsP_singleton :
"\<lbrakk>\<exists>p {x} . p\<rbrakk>b = (\<exists> v . v \<rhd> x \<and> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)))"
apply (simp add: ExistsP_def)
apply (simp add: EvalP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "\<langle>b1\<rangle>\<^sub>bx" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "b(x :=\<^sub>b v)" in exI)
apply (auto)
apply (rule_tac x = "b" in exI)
apply (simp add: carrier_def)
done

theorem EvalP_ForallP_singleton :
"\<lbrakk>\<forall>p {x} . p\<rbrakk>b = (\<forall> v. v \<rhd> x \<longrightarrow> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)))"
apply (simp add: ForallP_def)
apply (simp add: EvalP_NotP EvalP_ExistsP_singleton closure)
done

theorems EvalP_QuantP_singleton =
  EvalP_ExistsP_singleton
  EvalP_ForallP_singleton

subsection {* Normalisation *}

theorem NotP_NotP :
"\<not>p \<not>p p = p"
apply (auto simp: NotP_def)
done

theorem ExistsP_empty :
"(\<exists>p {} . p) = p"
  by (simp add: ExistsP_def)

theorem ForallP_empty :
"(\<forall>p {} . p) = p"
apply (simp add: ForallP_def)
apply (simp add: ExistsP_empty closure)
apply (simp add: NotP_NotP)
done

theorem ExistsP_insert :
"(\<exists>p (insert v vs) . p) = (\<exists>p {v} . (\<exists>p vs . p))"
apply (rule destPRED_intro)
apply (simp add: ExistsP.rep_eq)
apply (auto)
-- {* Subgoal 1 *}
apply (rule_tac x = "b1 \<oplus>\<^sub>b b2 on vs" in exI)
apply (force)
-- {* Subgoal 2 *}
apply (rule_tac x = "b1a" in exI)
apply (safe)
apply (rule_tac x = "b2a \<oplus>\<^sub>b b2 on {v}" in exI)
apply (auto simp add: override_on_assoc closure)
apply (metis (no_types) binding_override_simps(3,5) binding_override_singleton)
done

theorem ForallP_insert :
"(\<forall>p (insert v vs) . p) = (\<forall>p {v} . (\<forall>p vs . p))"
apply (simp add: ForallP_def closure)
apply (simp add: NotP_NotP closure)
apply (subst ExistsP_insert)
apply (simp_all add: closure)
done

theorem ExistsP_atomise :
"(\<exists>p {x} . (\<exists>p (insert y vs) . p)) =
 (\<exists>p (insert x (insert y vs)) . p)"
apply (auto intro!: sym [OF ExistsP_insert])
done

theorem ForallP_atomise :
"(\<forall>p {x} . (\<forall>p (insert y vs) . p)) =
 (\<forall>p (insert x (insert y vs)) . p)"
apply (auto intro!: sym [OF ForallP_insert])
done

theorems QuantP_atomise =
  ExistsP_atomise
  ForallP_atomise

theorem ExistsP_deatomise :
"(\<exists>p (insert x (insert y vs)) . p) =
 (\<exists>p {x} . (\<exists>p (insert y vs) . p))"
apply (auto intro!: ExistsP_insert)
done

theorem ForallP_deatomise :
"(\<forall>p (insert x (insert y vs)) . p) =
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


theorem ExistsP_norm_test :
"(\<exists>p {x} . \<exists>p {y} . p) = (\<exists>p {y} . \<exists>p {x} . p)"
apply (simp add:QuantP_atomise)
apply (subgoal_tac "{x, y} = {y, x}")
apply (simp)
apply (blast)
done

theorem AndP_comm :
"p1 \<and>p p2 = p2 \<and>p p1"
  by (utp_pred_auto_tac)

theorem AndP_idem :
"p \<and>p p = p"
  by (utp_pred_auto_tac)

theorem AndP_assoc :
"p1 \<and>p (p2 \<and>p p3) = (p1 \<and>p p2) \<and>p p3"
  by (utp_pred_auto_tac)

theorem AndP_OrP_distl :
"p1 \<and>p (p2 \<or>p p3) = (p1 \<and>p p2) \<or>p (p1 \<and>p p3)"
  by (utp_pred_auto_tac)

theorem AndP_OrP_distr:
"(p1 \<or>p p2) \<and>p p3 = (p1 \<and>p p3) \<or>p (p2 \<and>p p3)"
  by (utp_pred_auto_tac)

theorem OrP_comm :
"p1 \<or>p p2 = p2 \<or>p p1"
  by (utp_pred_auto_tac)

theorem OrP_idem :
"p \<or>p p = p"
  by (utp_pred_auto_tac)

theorem OrP_assoc :
"p1 \<or>p (p2 \<or>p p3) = (p1 \<or>p p2) \<or>p p3"
  by (utp_pred_auto_tac)

theorem OrP_AndP_distl :
"p1 \<or>p (p2 \<and>p p3) = (p1 \<or>p p2) \<and>p (p1 \<or>p p3)"
  by (utp_pred_auto_tac)

theorem OrP_AndP_distr :
  "(p1 \<and>p p2) \<or>p p3 = (p1 \<or>p p3) \<and>p (p2 \<or>p p3)"
  by (utp_pred_auto_tac)

theorem NotP_FalseP :
"true = \<not>p false"
  by (utp_pred_auto_tac)

theorem AndP_comm_taut :
"taut (p1 \<and>p p2) \<Leftrightarrow>p (p2 \<and>p p1)"
  by (utp_pred_auto_tac)

theorem AndP_equals_FalseP :
"p \<and>p \<not>p p = false"
  by (utp_pred_auto_tac)


theorem OrP_equals_TrueP :
"p \<or>p \<not>p p = true"
  by (utp_pred_auto_tac)

theorem ForallP_NotP_ExistsP_taut :
"taut (\<forall>p vs . \<not>p p) \<Leftrightarrow>p \<not>p (\<exists>p vs . p)"
  by (utp_pred_auto_tac)

theorem OrP_RefP_taut :
"taut p1 \<or>p p2 \<sqsubseteq>p p1"
  by (utp_pred_auto_tac)

theorem OrP_ref :
"p1 \<or>p p2 \<sqsubseteq> p1"
  by (utp_pred_auto_tac)

text {* The theorem below would be tedious to prove by mere rewriting. *}

lemma AndP_reorder_test :
"p1 \<and>p p2 \<and>p p3 \<and>p p4 \<and>p p5 = (p1 \<and>p p5) \<and>p p3 \<and>p (p4 \<and>p p2)"
  by (utp_pred_auto_tac)

end
