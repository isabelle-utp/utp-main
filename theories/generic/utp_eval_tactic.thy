(******************************************************************************)
(* Title: utp/generic/utp_eval_tactic.thy                                     *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_eval_tactic
imports utp_gen_pred
begin

section {* Proof Tactic for Predicates *}

context GEN_PRED
begin

subsection {* Interpretation Function *}

definition EvalP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow> bool" where
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP p b \<longleftrightarrow> b \<in> \<beta> p"

subsection {* Fundamental Theorem *}

theorem EvalP_intro :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 = p2 \<longleftrightarrow>
 (\<alpha> p1) = (\<alpha> p2) \<and> (\<forall> b \<in> WF_BINDING . (EvalP p1 b) \<longleftrightarrow> (EvalP p2 b))"
apply (safe)
apply (simp add: EvalP_def)
apply (rule prod_eqI)
apply (assumption)
apply (subgoal_tac "\<beta> p1 \<subseteq> WF_BINDING")
apply (subgoal_tac "\<beta> p2 \<subseteq> WF_BINDING")
apply (auto) [1]
apply (simp_all add: WF_BINDING_bindings)
done

theorem EvalP_intro_rule :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 (\<alpha> p1) = (\<alpha> p2);
 (\<forall> b \<in> WF_BINDING . (EvalP p1 b) \<longleftrightarrow> (EvalP p2 b))\<rbrakk> \<Longrightarrow> p1 = p2"
apply (subst EvalP_intro)
apply (simp_all)
done

subsection {* Distribution Theorems *}

theorem EvalP_LiftP :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_FUN a;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (LiftP a f) b = f b"
apply (simp add: EvalP_def)
apply (simp add: LiftP_def)
done

theorem EvalP_TrueP :
"\<lbrakk>a \<in> WF_ALPHABET;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (true a) b = True"
apply (simp add: EvalP_def)
apply (simp add: TrueP_def)
done

theorem EvalP_FalseP :
"\<lbrakk>a \<in> WF_ALPHABET;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (false a) b = False"
apply (simp add: EvalP_def)
apply (simp add: FalseP_def)
done

theorem EvalP_ExtP :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (p \<oplus> a) b = (EvalP p b)"
apply (simp add: EvalP_def)
apply (simp add: ExtP_def)
done

theorem EvalP_ResP :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (p \<ominus> a) b =
   (\<exists> b' \<in> WF_BINDING . b \<cong> b' on (\<alpha> p) - a \<and> EvalP p b')"
apply (simp add: EvalP_def)
apply (simp add: ResP_def)
apply (safe)
apply (rule_tac x = "b1" in bexI)
apply (simp add: binding_equiv_comm)
apply (simp add: WF_BINDING_member2)
apply (rule_tac x = "b'" in bexI)
apply (simp add: binding_equiv_comm)
apply (assumption)
done

(*
  The theorem below is provable if we remove @{text "b \<in> WF_BINDING"} from the
  assumptions in the definition of EvalP. However, it turns out that the law
  is not as useful in practice because we have no general law that establishes
  that the overridden binding is in @{text "WF_BINDING}. There is an open issue
  how we recover the simplicity of the old approach using function override.
*)

(*
theorem EvalP_ResP_override :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (p \<ominus> a) b =
   (\<exists> b' \<in> WF_BINDING . EvalP p (b' \<oplus> b on (\<alpha> p) - a))"
apply (simp add: EvalP_def)
apply (simp add: ResP_def)
apply (safe)
apply (rule_tac x = "b1" in bexI)
apply (simp add: binding_equiv_override)
apply (simp add: WF_BINDING_member2)
apply (rule_tac x = "b' \<oplus> b on \<alpha> p - a" in bexI)
apply (simp add: binding_equiv_def)
apply (assumption)
done
*)

theorem EvalP_NotP :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<not>p p) b = (\<not> (EvalP p b))"
apply (simp add: EvalP_def)
apply (simp add: NotP_def)
done

theorem EvalP_AndP :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (p1 \<and>p p2) b = ((EvalP p1 b) \<and> (EvalP p2 b))"
apply (simp add: EvalP_def)
apply (simp add: AndP_def)
done

theorem EvalP_OrP :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (p1 \<or>p p2) b = ((EvalP p1 b) \<or> (EvalP p2 b))"
apply (simp add: EvalP_def)
apply (simp add: OrP_def)
done

theorem EvalP_ImpliesP :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (p1 \<Rightarrow>p p2) b = ((EvalP p1 b) \<longrightarrow> (EvalP p2 b))"
apply (simp add: ImpliesP_def)
apply (simp add: EvalP_OrP EvalP_NotP)
done

theorem EvalP_IffP :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (p1 \<Leftrightarrow>p p2) b = ((EvalP p1 b) \<longleftrightarrow> (EvalP p2 b))"
apply (simp add: IffP_def)
apply (simp add: EvalP_AndP EvalP_ImpliesP)
apply (auto)
done

theorem EvalP_ExistsResP :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<exists>-p a . p) b =
   (\<exists> b' \<in> WF_BINDING . b \<cong> b' on (\<alpha> p) - a \<and> EvalP p b')"
apply (simp add: ExistsResP_def)
apply (simp add: EvalP_ResP)
done

theorem EvalP_ForallResP :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<forall>-p a . p) b =
   (\<forall> b' \<in> WF_BINDING . b \<cong> b' on (\<alpha> p) - a \<longrightarrow> EvalP p b')"
apply (simp add: ForallResP_def)
apply (simp add: EvalP_NotP EvalP_ExistsResP)
done

theorem EvalP_ExistsP :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<exists>p a . p) b =
   (\<exists> b' \<in> WF_BINDING . b \<cong> b' on (\<alpha> p) - a \<and> EvalP p b')"
apply (simp add: ExistsP_def)
apply (simp add: EvalP_ExtP EvalP_ExistsResP)
done

theorem EvalP_ForallP :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 EvalP (\<forall>p a . p) b =
   (\<forall> b' \<in> WF_BINDING . b \<cong> b' on (\<alpha> p) - a \<longrightarrow> EvalP p b')"
apply (simp add: ForallP_def)
apply (simp add: EvalP_ExtP EvalP_ForallResP)
done
end

subsection {* Automatic Tactics *}

subsubsection {* Theorem Attributes *}

ML {*
  structure eval =
    Named_Thms (val name = "eval" val description = "eval theorems")
*}
setup eval.setup

ML {*
  structure taut =
    Named_Thms (val name = "taut" val description = "taut theorems")
*}
setup taut.setup

context GEN_PRED
begin
declare EvalP_intro [eval]
declare EvalP_LiftP [eval]
declare EvalP_TrueP [eval]
declare EvalP_FalseP [eval]
declare EvalP_ExtP [eval]
declare EvalP_ResP [eval]
declare EvalP_NotP [eval]
declare EvalP_AndP [eval]
declare EvalP_OrP [eval]
declare EvalP_ImpliesP [eval]
declare EvalP_IffP [eval]
declare EvalP_ExistsResP [eval]
declare EvalP_ForallResP [eval]
declare EvalP_ExistsP [eval]
declare EvalP_ForallP [eval]
declare ClosureP_def [eval]
declare RefP_def [eval]
declare WF_ALPHABET_alphabet [eval]
declare Tautology_def [taut]
declare Contradiction_def [taut]
declare Contingency_def [taut]
declare Refinement_def [taut]
end

subsubsection {* Proof Methods *}

text {*
  We note that the proof methods are also generic and do not have to be
  recreated for concrete instantiations of the @{text "GEN_PRED"} locale.
*}

ML{*
  fun utp_pred_eq_simpset ctxt =
    (simpset_of ctxt) addsimps (eval.get ctxt);
*}

ML{*
  fun utp_pred_taut_simpset ctxt =
    (utp_pred_eq_simpset ctxt) addsimps (taut.get ctxt);
*}

method_setup utp_pred_eq_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      CHANGED (asm_full_simp_tac
        (utp_pred_eq_simpset ctxt) i)))
*} "Proof Tactic for Predicate Equalities"

method_setup utp_pred_taut_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      CHANGED (asm_full_simp_tac
        (utp_pred_taut_simpset ctxt) i)))
*} "Proof Tactic for Predicate Tautologies"

text {* TODO: Integrate Holger's code for the simplifier to raise provisos. *}

subsection {* Proof Experiments *}

context GEN_PRED
begin
theorem
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p (p2 \<and>p p3) = (p1 \<and>p p2) \<and>p p3"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p (p2 \<or>p p3) = (p1 \<and>p p2) \<or>p (p1 \<and>p p3)"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE;
 p4 \<in> WF_ALPHA_PREDICATE;
 p5 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p p2 \<and>p p3 \<and>p p4 \<and>p p5 = (p1 \<and>p p5) \<and>p p3 \<and>p (p4 \<and>p p2)"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (true a) = \<not>p (false a)"
apply (utp_pred_eq_tac)
done

theorem
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 taut (p1 \<and>p p2) \<Leftrightarrow>p (p2 \<and>p p1)"
apply (utp_pred_taut_tac)
apply (auto)
done

theorem
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 taut (\<forall>p a . \<not>p p) \<Leftrightarrow>p \<not>p (\<exists>p a . p)"
apply (utp_pred_taut_tac)
done

theorem
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
  p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 taut p1 \<or>p p2 \<sqsubseteq>p p1"
apply (utp_pred_taut_tac)
done

theorem
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
  p2 \<in> WF_ALPHA_PREDICATE;
 (\<alpha> p1) = (\<alpha> p2)\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<sqsubseteq> p1"
apply (utp_pred_taut_tac)
done
end
end
