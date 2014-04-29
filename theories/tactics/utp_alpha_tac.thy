(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_alpha_tac.thy                                                    *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Alphabetised Predicates *}

theory utp_alpha_tac
imports 
  "../alpha/utp_alphabet"
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

theorem UNREST_EvalA [unrest] :
"UNREST (- \<langle>\<alpha> p\<rangle>\<^sub>f) \<lbrakk>p\<rbrakk>\<pi>"
  by (simp add: EvalA_def unrest UNREST_subset)

lemma EvalA_UNREST_alpha [unrest]:
  "x \<notin>\<^sub>f \<alpha> P \<Longrightarrow> {x} \<sharp> \<lbrakk>P\<rbrakk>\<pi>"
  apply (rule UNREST_subset)
  apply (rule UNREST_EvalA)
  apply (auto)
done

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
  by (simp add: EvalA_def TrueA.rep_eq)

theorem EvalA_FalseA [evala] :
"\<lbrakk>false\<^bsub>a\<^esub>\<rbrakk>\<pi> = false"
  by (simp add: EvalA_def FalseA.rep_eq)

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

theorem EvalA_AndDistA [evala] :
"\<lbrakk> \<forall> a \<in> \<alpha>`ps. a \<subseteq>\<^sub>f t \<rbrakk> \<Longrightarrow> \<lbrakk>\<And>\<^bsub>t\<^esub> ps\<rbrakk>\<pi> = \<And>\<^sub>p {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}"
  apply (case_tac "ps = {}")
  apply (simp add:AndDistA_empty evala)
  apply (utp_pred_auto_tac)
  apply (simp add:EvalA_def AndDistA_rep_eq)
  apply (utp_pred_auto_tac)
done

theorem EvalA_OrDistA [evala] :
"\<lbrakk> \<forall> a \<in> \<alpha>`ps. a \<subseteq>\<^sub>f t \<rbrakk> \<Longrightarrow> \<lbrakk>\<Or>\<^bsub>t\<^esub> ps\<rbrakk>\<pi> = \<Or>\<^sub>p {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}"
  apply (case_tac "ps = {}")
  apply (simp add:OrDistA_empty evala)
  apply (utp_pred_auto_tac)
  apply (auto simp add: EvalA_def OrDistA_rep_eq)
  apply (utp_pred_auto_tac)
done

theorem EvalA_AANDI_enum [evala]:
  "\<lbrakk> \<forall> i\<in>A. \<alpha> (P i) \<subseteq>\<^sub>f a \<rbrakk> \<Longrightarrow> \<lbrakk>\<And>\<^bsub>a\<^esub> i:A. P i\<rbrakk>\<pi> = (\<And>\<^sub>p i:A. \<lbrakk>P i\<rbrakk>\<pi>)"
  apply (simp add:AANDI_def)
  apply (subst EvalA_AndDistA)
  apply (simp) 
  apply (utp_pred_auto_tac)
  apply (metis imageI)
done

theorem EvalA_AORDI_enum [evala]:
  "\<lbrakk> \<forall> i\<in>A. \<alpha> (P i) \<subseteq>\<^sub>f a \<rbrakk> \<Longrightarrow> \<lbrakk>\<Or>\<^bsub>a\<^esub> i:A. P i\<rbrakk>\<pi> = (\<Or>\<^sub>p i:A. \<lbrakk>P i\<rbrakk>\<pi>)"
  apply (simp add:AORDI_def)
  apply (subst EvalA_OrDistA)
  apply (simp) 
  apply (utp_pred_auto_tac)
done

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

lemma EvalA_TautologyA [evala]:
  "taut\<^sub>\<alpha>(p) \<longleftrightarrow> taut(\<lbrakk>p\<rbrakk>\<pi>)"
  by (metis EvalA_TrueA EvalA_intro TautologyA_def Tautology_def TrueA_alphabet TrueP_eq_ClosureP utp_pred_simps(21))

(* declare TautologyA_def [evala] *)
declare ContradictionA_def [evala]
declare less_eq_WF_ALPHA_PREDICATE_def [evala]
declare less_WF_ALPHA_PREDICATE_def [evala]

lemma EvalA_RefinementA: "p \<sqsubseteq> q \<longleftrightarrow> \<alpha> p = \<alpha> q \<and> \<lbrakk>p\<rbrakk>\<pi> \<sqsubseteq> \<lbrakk>q\<rbrakk>\<pi>"
  by (simp add:less_eq_WF_ALPHA_PREDICATE_def less_eq_WF_PREDICATE_def evala eval alphabet)

subsection {* Proof Tactics *}

text {*
  We note that the proof methods is also generic and does not have to be
  recreated for concrete instantiations of the @{term ALPHA_PRED} locale.
*}

ML {*
  fun utp_alpha_simpset ctxt =
    ctxt
      addsimps (evala.get ctxt)
      addsimps (closure.get ctxt)
      (* Closure alone seems not enough e.g. to simplify (p1 \<or>\<alpha> p2) \<sqsubseteq> p2. *)
      addsimps (alphabet.get ctxt)
      addsimps (typing.get ctxt)
      addsimps @{thms var_simps}
      addsimps @{thms var_dist}
      addsimps @{thms alphabet_dist};
*}

ML {*
  fun utp_alphabet_simpset ctxt =
    ctxt
      addsimps (alphabet.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps @{thms var_simps}
      addsimps @{thms var_dist}
      addsimps @{thms alphabet_dist};
*}

ML {*
  fun utp_alpha_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_alpha_simpset ctxt) i)
*}

ML {*
  fun utp_alpha_tac2 thms ctxt i =
    CHANGED (resolve_tac @{thms EvalA_intro} 1 
      THEN
        asm_full_simp_tac (ctxt addsimps (evala.get ctxt @ closure.get ctxt @ typing.get ctxt)) 2
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

end
