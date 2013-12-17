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
  by (simp add: EvalP_def LiftP_def)
 
theorem EvalP_EqualsP [eval] :
"\<lbrakk>v =\<^sub>p x\<rbrakk>b = (\<langle>b\<rangle>\<^sub>bv = x)"
  by (simp add: EqualsP_def EvalP_LiftP)

theorem EvalP_TrueP [eval] :
"\<lbrakk>true\<rbrakk>b = True"
  by (simp add: EvalP_def TrueP_def)

theorem EvalP_FalseP [eval] :
"\<lbrakk>false\<rbrakk>b = False"
  by (simp add: EvalP_def FalseP_def)

theorem EvalP_NotP [eval] :
"\<lbrakk>\<not>\<^sub>p p\<rbrakk>b = (\<not>\<lbrakk>p\<rbrakk>b)"
  by (simp add: EvalP_def NotP_def)

theorem EvalP_AndP [eval] :
"\<lbrakk>p1 \<and>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<and> \<lbrakk>p2\<rbrakk>b)"
  by (simp add: EvalP_def AndP_def)

theorem EvalP_OrP [eval] :
"\<lbrakk>p1 \<or>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<or> \<lbrakk>p2\<rbrakk>b)"
  by (simp add: EvalP_def OrP_def)

theorem EvalP_ImpliesP [eval] :
"\<lbrakk>p1 \<Rightarrow>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longrightarrow> \<lbrakk>p2\<rbrakk>b)"
  by (simp add: ImpliesP_def EvalP_OrP EvalP_NotP closure)

theorem EvalP_IffP [eval] :
"\<lbrakk>p1 \<Leftrightarrow>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)"
  by (auto simp add: IffP_def EvalP_AndP EvalP_ImpliesP closure)

theorem EvalP_DistAndP [eval] :
"\<lbrakk>\<And>\<^sub>p ps\<rbrakk>b = \<Squnion> {\<lbrakk>p\<rbrakk>b | p. p \<in> ps}"
  by (auto simp add:EvalP_def AndDistP_rep_eq)

theorem EvalP_DistOrP [eval]:
"\<lbrakk>\<Or>\<^sub>p ps\<rbrakk>b = \<Sqinter> {\<lbrakk>p\<rbrakk>b | p. p \<in> ps}"
  by (auto simp add:EvalP_def OrDistP_rep_eq)

theorem EvalP_ANDI_enum [eval]:
  "\<lbrakk>\<And>\<^sub>pi:A. P i\<rbrakk>b = (INF i:A. \<lbrakk>P i\<rbrakk>b)"
  by (auto simp add:ANDI_def eval)

theorem EvalP_ORDI_enum [eval]:
  "\<lbrakk>\<Or>\<^sub>pi:A. P i\<rbrakk>b = (SUP i:A. \<lbrakk>P i\<rbrakk>b)"
  by (auto simp add:ORDI_def eval)

theorem EvalP_ExistsP [eval] :
"\<lbrakk>\<exists>\<^sub>p vs . p\<rbrakk>b = (\<exists> b'. \<lbrakk>p\<rbrakk>(b \<oplus>\<^sub>b b' on vs))"
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
"\<lbrakk>\<forall>\<^sub>p vs . p\<rbrakk>b = (\<forall> b'. \<lbrakk>p\<rbrakk>(b \<oplus>\<^sub>b b' on vs))"
  by (simp add: ForallP_def EvalP_NotP EvalP_ExistsP closure)

theorem EvalP_ExistsShP [eval] :
"\<lbrakk>ExistsShP P\<rbrakk>b = (\<exists> x. \<lbrakk>P x\<rbrakk>b)"
  by (auto simp add:EvalP_def ExistsShP.rep_eq)

theorem EvalP_ForallShP [eval] :
"\<lbrakk>ForallShP P\<rbrakk>b = (\<forall> x. \<lbrakk>P x\<rbrakk>b)"
  by (auto simp add:EvalP_def ForallShP.rep_eq)

theorems EvalP_QuantP =
  EvalP_ExistsP
  EvalP_ForallP
  EvalP_ExistsShP
  EvalP_ForallShP

theorem EvalP_ClosureP [eval] :
"\<lbrakk>[p]\<^sub>p\<rbrakk>b = (\<forall> b. \<lbrakk>p\<rbrakk>b)"
  by (simp add: ClosureP_def EvalP_ForallP)

theorem EvalP_RefP [eval] :
"\<lbrakk>p1 \<sqsubseteq>\<^sub>p p2\<rbrakk>b = (\<forall> b. \<lbrakk>p2\<rbrakk>b \<longrightarrow> \<lbrakk>p1\<rbrakk>b)"
  by (simp add: RefP_def EvalP_ClosureP EvalP_ImpliesP closure)

theorem EvalP_RenameP [eval] :
"\<lbrakk>ss\<bullet>p\<rbrakk>b = \<lbrakk>p\<rbrakk>((inv\<^sub>s ss)\<bullet>b)"
apply (auto simp add: EvalP_def PermP.rep_eq image_def)
apply (rule_tac x = "RenameB (inv\<^sub>s ss) b" in bexI)
apply (simp)
apply (assumption)
done

declare Tautology_def [eval]
declare Contradiction_def [eval]
(* declare Refinement_def [eval] *)
declare less_eq_WF_PREDICATE_def [eval]
(* declare PrimeP_def [eval] *)

subsection {* Support Theorems *}

theorem EvalP_ExistsP_singleton :
"\<lbrakk>\<exists>\<^sub>p {x} . p\<rbrakk>b = (\<exists> v . v \<rhd> x \<and> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)))"
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
"\<lbrakk>\<forall>\<^sub>p {x} . p\<rbrakk>b = (\<forall> v. v \<rhd> x \<longrightarrow> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)))"
  by (simp add: ForallP_def EvalP_NotP EvalP_ExistsP_singleton closure)

theorems EvalP_QuantP_singleton =
  EvalP_ExistsP_singleton
  EvalP_ForallP_singleton

subsection {* Normalisation *}

theorem NotP_NotP :
"\<not>\<^sub>p \<not>\<^sub>p p = p"
  by (auto simp: NotP_def)

theorem ExistsP_empty :
"(\<exists>\<^sub>p {} . p) = p"
  by (simp add: ExistsP_def)

theorem ForallP_empty :
"(\<forall>\<^sub>p {} . p) = p"
  by (simp add: ForallP_def ExistsP_empty closure NotP_NotP)

theorem ExistsP_insert :
"(\<exists>\<^sub>p (insert v vs) . p) = (\<exists>\<^sub>p {v} . (\<exists>\<^sub>p vs . p))"
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
"(\<forall>\<^sub>p (insert v vs) . p) = (\<forall>\<^sub>p {v} . (\<forall>\<^sub>p vs . p))"
apply (simp add: ForallP_def closure)
apply (simp add: NotP_NotP closure)
apply (subst ExistsP_insert)
apply (simp_all add: closure)
done

theorem ExistsP_atomise :
"(\<exists>\<^sub>p {x} . (\<exists>\<^sub>p (insert y vs) . p)) =
 (\<exists>\<^sub>p (insert x (insert y vs)) . p)"
  by (auto intro!: sym [OF ExistsP_insert])

theorem ForallP_atomise :
"(\<forall>\<^sub>p {x} . (\<forall>\<^sub>p (insert y vs) . p)) =
 (\<forall>\<^sub>p (insert x (insert y vs)) . p)"
  by (auto intro!: sym [OF ForallP_insert])

theorems QuantP_atomise =
  ExistsP_atomise
  ForallP_atomise

theorem ExistsP_deatomise :
"(\<exists>\<^sub>p (insert x (insert y vs)) . p) =
 (\<exists>\<^sub>p {x} . (\<exists>\<^sub>p (insert y vs) . p))"
  by (auto intro!: ExistsP_insert)

theorem ForallP_deatomise :
"(\<forall>\<^sub>p (insert x (insert y vs)) . p) =
 (\<forall>\<^sub>p {x} . (\<forall>\<^sub>p (insert y vs) . p))"
  by (auto intro!: ForallP_insert)

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
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt);
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
"(\<exists>\<^sub>p {x} . \<exists>\<^sub>p {y} . p) = (\<exists>\<^sub>p {y} . \<exists>\<^sub>p {x} . p)"
apply (simp add:QuantP_atomise)
apply (subgoal_tac "{x, y} = {y, x}")
apply (simp)
apply (blast)
done

text {* The theorem below would be tedious to prove by mere rewriting. *}

lemma AndP_reorder_test :
"p1 \<and>\<^sub>p p2 \<and>\<^sub>p p3 \<and>\<^sub>p p4 \<and>\<^sub>p p5 = (p1 \<and>\<^sub>p p5) \<and>\<^sub>p p3 \<and>\<^sub>p (p4 \<and>\<^sub>p p2)"
  by (utp_pred_auto_tac)

end
