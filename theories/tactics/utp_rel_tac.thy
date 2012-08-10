(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_rel_tac.thy                                                      *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Relations *}

theory utp_rel_tac
imports "../generic/utp_pred" "../generic/utp_rel"
begin

text {* Theorem Attribute *}

ML {*
  structure evalr =
    Named_Thms (val name = "evalr" val description = "evalr theorems")
*}

setup evalr.setup

subsection {* Type Synonyms *}

type_synonym ('VALUE, 'TYPE) RELATION =
  "(('VALUE, 'TYPE) BINDING \<times>
    ('VALUE, 'TYPE) BINDING) set"

context PRED
begin

subsection {* Relational Model *}

text {*
  We require an arbitrary but fixed binding in our model of relations in order
  to constrain dashed variables which we do not care about. We note that an
  alternative approach is possible that upward closes the relation with respect
  to the values of these variables. In practice, it turns out that a constant
  valuation yields simpler proofs and there is not loss of generality with it.
*}

definition bc :: "('VALUE, 'TYPE) BINDING" where
"bc = (SOME b . b \<in> WF_BINDING)"

theorem bc_WF_BINDING [closure] :
"bc \<in> WF_BINDING"
apply (simp add: bc_def)
apply (rule_tac P = "\<lambda> b . b \<in> WF_BINDING" in someI_ex)
apply (simp add: WF_BINDING_exists)
done

definition WF_REL_BINDING :: "('VALUE, 'TYPE) BINDING set" where
"WF_REL_BINDING = {b \<oplus> bc on DASHED | b . b \<in> WF_BINDING}"

subsection {* Interpretation Function *}

definition BindR ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<times>
   ('VALUE, 'TYPE) BINDING" where
"BindR b = (b \<oplus> bc on DASHED, (SubstB SS b) \<oplus> bc on DASHED)"

definition BindP ::
  "('VALUE, 'TYPE) BINDING \<times>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING" where
"BindP = (\<lambda> (rb1, rb2) . rb1 \<oplus> (SubstB SS rb2) on DASHED)"

definition EvalR ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) RELATION" ("\<lbrakk>_\<rbrakk>R") where
"EvalR p = BindR ` p"

definition IEvalR ::
  "('VALUE, 'TYPE) RELATION \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"IEvalR r = BindP ` r"

subsection {* Auxilary Theorems *}

theorem EvalR_range :
"p \<in> WF_PREDICATE \<Longrightarrow>
 \<lbrakk>p\<rbrakk>R \<subseteq> WF_REL_BINDING \<times> WF_REL_BINDING"
apply (simp add: EvalR_def)
apply (simp add: image_def)
apply (simp add: BindR_def)
apply (simp add: WF_REL_BINDING_def)
apply (safe)
apply (rule_tac x = "xa" in exI)
apply (simp)
apply (rule_tac x = "SubstB SS xa" in exI)
apply (simp add: closure)
done

theorem WF_REL_BINDING_member1 [simp, intro] :
"\<lbrakk>p \<in> WF_PREDICATE;
 (rb1, rb2) \<in> \<lbrakk>p\<rbrakk>R\<rbrakk> \<Longrightarrow>
 rb1 \<in> WF_REL_BINDING"
apply (auto dest: EvalR_range)
done

theorem WF_REL_BINDING_member2 [simp, intro] :
"\<lbrakk>p \<in> WF_PREDICATE;
 (rb1, rb2) \<in> \<lbrakk>p\<rbrakk>R\<rbrakk> \<Longrightarrow>
 rb2 \<in> WF_REL_BINDING"
apply (auto dest: EvalR_range)
done

theorem BindP_inverse :
"b \<in> WF_BINDING \<Longrightarrow> BindP (BindR b) = b"
apply (simp add: BindR_def BindP_def)
apply (rule ext)
apply (case_tac "x \<in> DASHED")
apply (simp add: SubstB_def SS_DASHED_member closure)
apply (simp)
done

theorem IEvalR_inverse :
"p \<in> WF_PREDICATE \<Longrightarrow> IEvalR (EvalR p) = p"
apply (simp add: IEvalR_def EvalR_def)
apply (simp add: image_image)
apply (simp add: image_def)
apply (simp add: set_eq_iff)
apply (simp add: BindP_inverse)
done

theorem BindR_inject [simp] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 BindR b1 = BindR b2 \<longleftrightarrow> b1 = b2"
apply (simp add: BindR_def)
apply (simp add: override_on_eq)
apply (safe)
apply (rule ext)
apply (case_tac "x \<in> DASHED")
-- {* Subgoal 1 *}
apply (drule_tac x = "undash x" in spec)
back
apply (subgoal_tac "undash x \<notin> DASHED")
apply (simp)
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (simp add: var_defs)
-- {* Subgoal 2 *}
apply (simp)
done

theorem BindR_COMPOSABLE_BINDINGS :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (rb1, rb3) = BindR b1;
 (rb3, rb2) = BindR b2\<rbrakk> \<Longrightarrow>
 (b1, b2) \<in> COMPOSABLE_BINDINGS"
apply (simp add: BindR_def)
apply (simp add: COMPOSABLE_BINDINGS_def)
apply (simp add: override_on_eq)
apply (simp_all add: SubstB_def closure)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: SS_def)
apply (drule_tac x = "v" in spec)
apply (simp)
-- {* Subgoal 2 *}
apply (simp add: binding_equiv_def)
apply (simp add: NON_REL_VAR_def)
apply (rule ballI)
apply (simp add: SS_def)
apply (drule_tac x = "x" in spec)
apply (simp)
done

theorem BindR_override :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (rb1, rb3) = BindR b1;
 (rb3, rb2) = BindR b2\<rbrakk> \<Longrightarrow>
 (rb1, rb2) = BindR (b1 \<oplus> b2 on DASHED)"
apply (simp add: BindR_def)
apply (simp add: override_on_eq)
apply (simp_all add: SubstB_def closure)
apply (clarify)
apply (simp add: SS_def)
apply (safe)
apply (drule_tac x = "x" in spec)
apply (simp)
done

subsection {* Transfer Theorems *}

theorem EvalR_inj_on :
"inj_on EvalR WF_PREDICATE"
apply (insert IEvalR_inverse)
apply (erule inj_on_inverseI)
done

theorem EvalR_simp [evalr] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 = p2 \<longleftrightarrow> \<lbrakk>p1\<rbrakk>R = \<lbrakk>p2\<rbrakk>R"
apply (rule inj_on_eval_simp [of EvalR WF_PREDICATE "p1" "p2"])
apply (simp add: EvalR_inj_on)
apply (assumption)+
done

theorem EvalR_intro :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 \<lbrakk>p1\<rbrakk>R = \<lbrakk>p2\<rbrakk>R\<rbrakk> \<Longrightarrow> p1 = p2"
apply (rule inj_on_eval_intro [of EvalR WF_PREDICATE "p1" "p2"])
apply (simp add: EvalR_inj_on)
apply (assumption)+
done

subsection {* Distribution Theorems *}

theorem EvalR_TrueP_explicit :
"\<lbrakk>true\<rbrakk>R = {(b1, b2) | b1 b2 .
   b1 \<in> WF_REL_BINDING \<and>
   b2 \<in> WF_REL_BINDING \<and>
   b1 \<cong> b2 on DASHED \<and>
   b1 \<cong> b2 on NON_REL_VAR}"
apply (simp add: EvalR_def)
apply (simp add: TrueP_def)
apply (simp add: image_def)
apply (simp add: BindR_def WF_REL_BINDING_def)
apply (simp add: binding_equiv_def)
apply (simp add: set_eq_subset)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "xa" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "SubstB SS xa" in exI)
apply (simp add: closure)
-- {* Subgoal 3 *}
apply (simp)
-- {* Subgoal 4 *}
apply (simp add: NON_REL_VAR_def)
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
-- {* Subgoal 5 *}
apply (rule_tac x = "b \<oplus> (SubstB SS ba) on DASHED" in bexI)
apply (simp)
apply (simp add: override_on_eq)
apply (safe)
apply (simp add: SubstB_def closure)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS_simps)
apply (simp add: SS_simps)
apply (drule_tac x = "x" in bspec)
apply (simp add: NON_REL_VAR_def var_defs)
apply (simp)
apply (simp add: closure)
done

theorem EvalR_TrueP [evalr] :
"\<lbrakk>true\<rbrakk>R = \<lbrakk>WF_BINDING\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: TrueP_def)
done

theorem EvalR_FalseP [evalr] :
"\<lbrakk>false\<rbrakk>R = {}"
apply (simp add: EvalR_def)
apply (simp add: FalseP_def)
done

theorem EvalR_NotP [evalr] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<not>p p\<rbrakk>R = \<lbrakk>true\<rbrakk>R - \<lbrakk>p\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: NotP_def TrueP_def)
apply (auto)
done

theorem EvalR_AndP [evalr] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<and>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<inter> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: AndP_def)
apply (auto)
done

theorem EvalR_OrP [evalr] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<or>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<union> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: OrP_def)
apply (auto)
done

declare ImpliesP_def [evalr]

declare IffP_def [evalr]

theorem EvalR_SkipR [evalr] :
"\<lbrakk>II\<rbrakk>R = Id_on WF_REL_BINDING"
apply (simp add: EvalR_def)
apply (simp add: SkipR_def)
apply (simp add: WF_REL_BINDING_def)
apply (simp add: image_def)
apply (simp add: BindR_def)
apply (simp add: Id_on_def)
apply (simp add: set_eq_iff)
apply (safe)
-- {* Subgoal 1 *}
apply (rename_tac x b)
apply (rule_tac x = "b \<oplus> bc on DASHED" in exI)
apply (simp add: override_on_eq)
apply (rule conjI)
apply (rule_tac x = "b" in exI)
apply (simp)
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
-- {* Subgoal 2 *}
apply (rule_tac x = "b \<oplus> (SubstB SS b) on DASHED" in exI)
apply (simp add: override_on_eq)
apply (simp add: closure)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (clarify)
apply (subgoal_tac "v \<notin> DASHED")
apply (simp)
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (auto) [1]
apply (auto) [1]
-- {* Subgoal 2.2 *}
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (auto) [1]
done

theorem SubstB_SS_COMPOSABLE_BINDINGS_1 :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
 SubstB SS b1 \<oplus> bc on DASHED = b2 \<oplus> bc on DASHED"
apply (simp add: override_on_eq)
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (safe)
apply (simp add: COMPOSABLE_BINDINGS_def)
apply (simp add: COMPOSABLE_BINDINGS_def)
apply (clarify)
apply (simp add: binding_equiv_def)
apply (simp add: NON_REL_VAR_def)
done

theorem SubstB_SS_COMPOSABLE_BINDINGS_2 :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 (b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
 SubstB SS (b1 \<oplus> b2 on DASHED) \<oplus> bc on DASHED = SubstB SS b2 \<oplus> bc on DASHED"
apply (simp add: override_on_eq)
apply (simp add: SubstB_def closure)
apply (simp add: SS_def)
apply (safe)
apply (simp add: COMPOSABLE_BINDINGS_def)
apply (clarify)
apply (simp add: binding_equiv_def)
apply (simp add: NON_REL_VAR_def)
done

theorems SubstB_SS_COMPOSABLE_BINDINGS =
  SubstB_SS_COMPOSABLE_BINDINGS_1
  SubstB_SS_COMPOSABLE_BINDINGS_2

theorem EvalR_SemiR [evalr] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 ; p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R O \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: SemiR_def)
apply (simp add: set_eq_iff)
apply (simp add: rel_comp_def image_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rename_tac x rb1 rb2 xa b1 b2)
apply (rule_tac x = "(SubstB SS b1) \<oplus> bc on DASHED" in exI)
apply (rule conjI)
-- {* Subgoal 1.1 *}
apply (rule_tac x = "b1" in bexI)
apply (simp add: BindR_def)
apply (assumption)
-- {* Subgoal 1.2 *}
apply (rule_tac x = "b2" in bexI)
apply (simp add: BindR_def)
apply (simp add: SubstB_SS_COMPOSABLE_BINDINGS)
apply (assumption)
-- {* Subgoal 2 *}
apply (rename_tac x rb1 rb2 rb3 b1 b2)
apply (rule_tac x = "b1 \<oplus> b2 on DASHED" in exI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (rule_tac x = "b1" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (simp add: BindR_COMPOSABLE_BINDINGS)
-- {* Subgoal 2.1 *}
apply (simp add: BindR_override)
done

declare CondR_def [evalr]

(* The following are useless since quantifications are not supported yet. *)

(*
declare Tautology_def [evalr]
declare Contradiction_def [evalr]
declare Refinement_def [evalr]
*)
end

subsection {* Proof Tactics *}

text {*
  We note that the proof method is also generic and does not have to be
  recreated for concrete instantiations of the @{term PRED} locale.
*}

ML {*
  fun utp_rel_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evalr.get ctxt)
      addsimps (closure.get ctxt);
*}

ML {*
  fun utp_rel_auto_simpset ctxt =
    (simpset_of ctxt)
      addsimps @{thms "rel_comp_def"}
*}

ML {*
  fun utp_rel_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_rel_simpset ctxt) i)
*}

ML {*
  fun utp_rel_auto_tac thms ctxt i =
    TRY (asm_full_simp_tac (utp_rel_simpset ctxt) i) THEN
    TRY (asm_full_simp_tac (utp_rel_auto_simpset ctxt) i) THEN
    (auto_tac ctxt)
*}

method_setup utp_rel_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_rel_tac thms ctxt))
*} "proof tactic for relations"

method_setup utp_rel_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_rel_auto_tac thms ctxt))
*} "proof tactic for relations with auto"

subsection {* Algebraic Laws *}

context PRED
begin

theorem SemiP_FalseP :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p ; false = false"
apply (utp_rel_auto_tac)
done

theorem SemiP_OrP_distr :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 ; (p2 \<or>p p3) = (p1 ; p2) \<or>p (p1 ; p3)"
apply (utp_rel_auto_tac)
done

theorem SemiP_IffP_comm :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>p p2 = p2 \<Leftrightarrow>p p1"
apply (utp_rel_auto_tac)
done

theorem SemiP_SkipR_left :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 II ; p = p"
apply (utp_rel_auto_tac)
done

theorem SemiP_SkipR_right :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p ; II = p"
apply (utp_rel_auto_tac)
done

theorem SemiP_assoc :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 ; (p2 ; p3) = (p1 ; p2) ; p3"
apply (utp_rel_auto_tac)
done

subsection {* Proof Experiments *}

text {* The proof below is still very nasty even with simple predicates. *}

theorem SemiP_assoc :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (p1 ; p2) ; p3 = p1 ; (p2 ; p3)"
apply (subgoal_tac "(p1 ; p2) \<in> WF_PREDICATE")
apply (subgoal_tac "(p2 ; p3) \<in> WF_PREDICATE")
apply (simp add: SemiR_def)
apply (safe)
oops
end
end
