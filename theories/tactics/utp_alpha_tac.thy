(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_alpha_tac.thy                                                    *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Alphabetised Predicates *}

theory utp_alpha_tac
imports 
  "../alpha/utp_alpha_pred"
begin

text {* Theorem Attribute *}

ML {*
  structure evala =
    Named_Thms (val name = @{binding evala} val description = "evala theorems")
*}

setup evala.setup

subsection {* Interpretation Function *}

definition EvalA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" ("\<lbrakk>_\<rbrakk>\<pi>") where
"EvalA p = \<pi> p"

subsection {* Transfer Theorems *}

theorem EvalA_simp [evala] :
"p1 = p2 \<longleftrightarrow> (\<alpha> p1) = (\<alpha> p2) \<and> \<lbrakk>p1\<rbrakk>\<pi> = \<lbrakk>p2\<rbrakk>\<pi>"
  by (auto simp add: EvalA_def)

theorem EvalA_intro :
"\<lbrakk>(\<alpha> p1) = (\<alpha> p2);
 \<lbrakk>p1\<rbrakk>\<pi> = \<lbrakk>p2\<rbrakk>\<pi>\<rbrakk> \<Longrightarrow> p1 = p2"
  by (auto simp add: EvalA_def)

theorem EvalA_UNREST [unrest] :
"UNREST (VAR - \<langle>\<alpha> p\<rangle>\<^sub>f) \<lbrakk>p\<rbrakk>\<pi>"
  by (simp add: EvalA_def unrest)

subsection {* Distribution Theorems *}

theorem EvalA_LiftA [evala] :
"f \<in> WF_BINDING_PRED \<langle>a\<rangle>\<^sub>f \<Longrightarrow>
 \<lbrakk>LiftA a f\<rbrakk>\<pi> = LiftP f"
  by (simp add: EvalA_def LiftA_rep_eq)

theorem EvalA_EqualsA [evala] :
"\<lbrakk>v =\<^sub>\<alpha> x\<rbrakk>\<pi> = (v =\<^sub>p x)"
  by (simp add: EvalA_def EqualsA.rep_eq)

theorem EvalA_TrueA [evala] :
"\<lbrakk>true\<^bsub>a\<^esub>\<rbrakk>\<pi> = true"
  by (simp add: EvalA_def TrueA_rep_eq)

theorem EvalA_FalseA [evala] :
"\<lbrakk>false\<^bsub>a\<^esub>\<rbrakk>\<pi> = false"
  by (simp add: EvalA_def FalseA_rep_eq)

theorem EvalA_ExtA [evala] :
"\<lbrakk>p \<oplus>\<^sub>\<alpha> a\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi>"
  by (simp add: EvalA_def ExtA.rep_eq)

theorem EvalA_ResA [evala] :
"\<lbrakk>p \<ominus>\<^sub>\<alpha> a\<rbrakk>\<pi> = (\<exists>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add: EvalA_def ResA.rep_eq)

theorem EvalA_NotA [evala] :
"\<lbrakk>\<not>\<^sub>\<alpha> p\<rbrakk>\<pi> = \<not>\<^sub>p \<lbrakk>p\<rbrakk>\<pi>"
  by (simp add: EvalA_def NotA.rep_eq)

theorem EvalA_AndA [evala] :
"\<lbrakk>p1 \<and>\<^sub>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<and>\<^sub>p \<lbrakk>p2\<rbrakk>\<pi>"
  by (simp add: EvalA_def AndA.rep_eq)

theorem EvalA_OrA [evala] :
"\<lbrakk>p1 \<or>\<^sub>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<or>\<^sub>p \<lbrakk>p2\<rbrakk>\<pi>"
  by (simp add: EvalA_def OrA.rep_eq)

theorem EvalA_ImpliesA [evala] :
"\<lbrakk>p1 \<Rightarrow>\<^sub>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<Rightarrow>\<^sub>p \<lbrakk>p2\<rbrakk>\<pi>"
  by (simp add: EvalA_def ImpliesA.rep_eq)

theorem EvalA_IffA [evala] :
"\<lbrakk>p1 \<Leftrightarrow>\<^sub>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<Leftrightarrow>\<^sub>p \<lbrakk>p2\<rbrakk>\<pi>"
  by (simp add: EvalA_def IffA.rep_eq)

theorem EvalA_ExistsA [evala] :
"\<lbrakk>\<exists>\<^sub>\<alpha> a . p\<rbrakk>\<pi> = (\<exists>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add: EvalA_def ExistsA.rep_eq)

theorem EvalA_ForallA [evala] :
"\<lbrakk>\<forall>\<^sub>\<alpha> a . p\<rbrakk>\<pi> = (\<forall>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add: EvalA_def ForallA.rep_eq)

theorem EvalA_ExistsResA [evala] :
"\<lbrakk>\<exists>-\<^sub>\<alpha> a . p\<rbrakk>\<pi> = \<lbrakk>\<exists>\<^sub>\<alpha> a . p\<rbrakk>\<pi>"
  by (simp add: EvalA_def ExistsResA.rep_eq ExistsA.rep_eq)

theorem EvalA_ForallResA [evala] :
"\<lbrakk>\<forall>-\<^sub>\<alpha> a . p\<rbrakk>\<pi> = \<lbrakk>\<forall>\<^sub>\<alpha> a . p\<rbrakk>\<pi>"
  by (simp add: EvalA_def ForallResA.rep_eq ForallA.rep_eq)

theorem EvalA_ClosureA [evala] :
"\<lbrakk>[p]\<^sub>\<alpha>\<rbrakk>\<pi> = [\<lbrakk>p\<rbrakk>\<pi>]\<^sub>p"
  by (simp add: EvalA_def ClosureA.rep_eq)

theorem EvalA_RefA [evala] :
"\<lbrakk>p1 \<sqsubseteq>\<^sub>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<sqsubseteq>\<^sub>p \<lbrakk>p2\<rbrakk>\<pi>"
  by (simp add: EvalA_def RefA.rep_eq)

theorem EvalA_RenameA [evala] :
"\<lbrakk>ss\<bullet>p\<rbrakk>\<pi> = ss\<bullet>\<lbrakk>p\<rbrakk>\<pi>"
  by (simp add:EvalA_def PermA.rep_eq)

declare TautologyA_def [evala]
declare ContradictionA_def [evala]
declare less_eq_WF_ALPHA_PREDICATE_def [evala]
declare less_WF_ALPHA_PREDICATE_def [evala]

lemma EvalA_RefinementA: "p \<sqsubseteq> q \<longleftrightarrow> \<alpha> q \<subseteq>\<^sub>f \<alpha> p \<and> \<lbrakk>p\<rbrakk>\<pi> \<sqsubseteq> \<lbrakk>q\<rbrakk>\<pi>"
  by (simp add:less_eq_WF_ALPHA_PREDICATE_def less_eq_WF_PREDICATE_def evala eval alphabet)

subsection {* Proof Tactics *}

text {*
  We note that the proof methods is also generic and does not have to be
  recreated for concrete instantiations of the @{term ALPHA_PRED} locale.
*}

ML {*
  fun utp_alpha_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evala.get ctxt)
      addsimps (closure.get ctxt)
      (* Closure alone seems not enough e.g. to simplify (p1 \<or>\<alpha> p2) \<sqsubseteq> p2. *)
      addsimps (alphabet.get ctxt)
      addsimps (typing.get ctxt)
      addsimps @{thms var_simps}
      addsimps @{thms var_dist};
*}

ML {*
  fun utp_alphabet_simpset ctxt =
    (simpset_of ctxt)
      addsimps (alphabet.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps @{thms var_simps}
      addsimps @{thms var_dist};
*}

ML {*
  fun utp_alpha_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_alpha_simpset ctxt) i)
*}

ML {*
  fun utp_alpha_tac2 thms ctxt i =
    CHANGED (resolve_tac @{thms EvalA_intro} 1 
      THEN
        asm_full_simp_tac ((simpset_of ctxt) addsimps (evala.get ctxt @ closure.get ctxt @ typing.get ctxt)) 2
      THEN
        asm_full_simp_tac (utp_alphabet_simpset ctxt) 1
      THEN
        TRY (force_tac ctxt 1))
*}

ML {*
  fun utp_alphabet_tac thms ctxt i =
    CHANGED  (
      TRY (asm_full_simp_tac (utp_alphabet_simpset ctxt) i) THEN
      (auto_tac ctxt))
*}

method_setup utp_alpha_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_alpha_tac thms ctxt))
*} "proof tactic for alphabetised predicates"


method_setup utp_alpha_tac2 = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_alpha_tac2 thms ctxt))
*} "proof tactic for alphabetised predicates"

method_setup utp_alphabet_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_alphabet_tac thms ctxt))
*} "proof tactic for alphabets"

ML {* utp_alpha_tac2 *}

subsection {* Proof Experiments *}

theorem EvalA_test :
"\<not>\<^sub>\<alpha> (\<not>\<^sub>\<alpha> p) = p"
  by (utp_alpha_tac)

theorem EvalA_contr:
"p \<Rightarrow>\<^sub>\<alpha> false\<^bsub>\<alpha> p\<^esub> = \<not>\<^sub>\<alpha> p"
  by (utp_alpha_tac)

instance WF_ALPHA_PREDICATE :: (VALUE) order
  apply (intro_classes)
  apply (utp_alpha_tac)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (utp_alpha_tac, utp_pred_auto_tac)
done

instantiation WF_ALPHA_PREDICATE :: (VALUE) lattice
begin

definition "inf_WF_ALPHA_PREDICATE p q = (\<forall>-\<^sub>\<alpha> (\<alpha> p -\<^sub>f \<alpha> q). p) \<and>\<^sub>\<alpha> (\<forall>-\<^sub>\<alpha> (\<alpha> q -\<^sub>f \<alpha> p). q)"
definition "sup_WF_ALPHA_PREDICATE = op \<or>\<^sub>\<alpha>"

instance
  apply (intro_classes)
  apply (simp_all add:inf_WF_ALPHA_PREDICATE_def sup_WF_ALPHA_PREDICATE_def)
  apply (simp add:less_eq_WF_ALPHA_PREDICATE_def)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
  apply (metis binding_override_simps(2))
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
  apply (metis binding_override_simps(2))
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
  apply (subgoal_tac "UNREST (\<langle>\<alpha> y\<rangle>\<^sub>f - \<langle>\<alpha> z\<rangle>\<^sub>f) \<lbrakk>x\<rbrakk>\<pi>")
  apply (metis EvalP_UNREST_override)
  apply (metis Diff_mono EvalA_UNREST UNREST_subset VAR_subset)
  apply (subgoal_tac "UNREST (\<langle>\<alpha> z\<rangle>\<^sub>f - \<langle>\<alpha> y\<rangle>\<^sub>f) \<lbrakk>x\<rbrakk>\<pi>")
  apply (metis EvalP_UNREST_override)
  apply (metis Diff_mono EvalA_UNREST UNREST_subset VAR_subset)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (utp_alpha_tac, utp_pred_auto_tac)
done
end

lemma "\<alpha> p = \<alpha> q \<Longrightarrow> inf p q = p \<and>\<^sub>\<alpha> q"
  by (simp add:inf_WF_ALPHA_PREDICATE_def, utp_alpha_tac, utp_pred_tac)

(*
instantiation WF_ALPHA_PREDICATE :: (VALUE) complete_lattice
begin

definition "Inf_WF_ALPHA_PREDICATE A = {p. 
*)

end
