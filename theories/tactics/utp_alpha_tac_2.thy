(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_alpha_tac.thy                                                    *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Alphabetised Predicates *}

theory utp_alpha_tac_2
imports "../alpha/utp_alpha_pred_2"
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
apply (simp add: EvalA_def)
apply (simp add: LiftA_rep_eq)
done

theorem EvalA_EqualsA [evala] :
"\<lbrakk>v =\<alpha> x\<rbrakk>\<pi> = (v =p x)"
apply (simp add: EvalA_def)
apply (simp add: EqualsA.rep_eq)
done

theorem EvalA_TrueA [evala] :
"\<lbrakk>true a\<rbrakk>\<pi> = true"
apply (simp add: EvalA_def)
apply (simp add: TrueA_rep_eq)
done

theorem EvalA_FalseA [evala] :
"\<lbrakk>false a\<rbrakk>\<pi> = false"
apply (simp add: EvalA_def)
apply (simp add: FalseA_rep_eq)
done

theorem EvalA_ExtA [evala] :
"\<lbrakk>p \<oplus>\<alpha> a\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ExtA.rep_eq)
done

theorem EvalA_ResA [evala] :
"\<lbrakk>p \<ominus>\<alpha> a\<rbrakk>\<pi> = (\<exists>p \<langle>a\<rangle>\<^sub>f . \<lbrakk>p\<rbrakk>\<pi>)"
apply (simp add: EvalA_def)
apply (simp add: ResA.rep_eq)
done

theorem EvalA_NotA [evala] :
"\<lbrakk>\<not>\<alpha> p\<rbrakk>\<pi> = \<not>p \<lbrakk>p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: NotA.rep_eq)
done

theorem EvalA_AndA [evala] :
"\<lbrakk>p1 \<and>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<and>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: AndA.rep_eq)
done

theorem EvalA_OrA [evala] :
"\<lbrakk>p1 \<or>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<or>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: OrA.rep_eq)
done

theorem EvalA_ImpliesA [evala] :
"\<lbrakk>p1 \<Rightarrow>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<Rightarrow>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ImpliesA.rep_eq)
done

theorem EvalA_IffA [evala] :
"\<lbrakk>p1 \<Leftrightarrow>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<Leftrightarrow>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: IffA.rep_eq)
done

theorem EvalA_ExistsA [evala] :
"\<lbrakk>\<exists>\<alpha> a . p\<rbrakk>\<pi> = (\<exists>p \<langle>a\<rangle>\<^sub>f . \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add: EvalA_def ExistsA.rep_eq)

theorem EvalA_ForallA [evala] :
"\<lbrakk>\<forall>\<alpha> a . p\<rbrakk>\<pi> = (\<forall>p \<langle>a\<rangle>\<^sub>f . \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add: EvalA_def ForallA.rep_eq)

theorem EvalA_ExistsResA [evala] :
"\<lbrakk>\<exists>-\<alpha> a . p\<rbrakk>\<pi> = \<lbrakk>\<exists>\<alpha> a . p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ExistsResA.rep_eq)
apply (simp add: ExistsA.rep_eq)
done

theorem EvalA_ForallResA [evala] :
"\<lbrakk>\<forall>-\<alpha> a . p\<rbrakk>\<pi> = \<lbrakk>\<forall>\<alpha> a . p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ForallResA.rep_eq)
apply (simp add: ForallA.rep_eq)
done

theorem EvalA_ClosureA [evala] :
"\<lbrakk>[p]\<alpha>\<rbrakk>\<pi> = [\<lbrakk>p\<rbrakk>\<pi>]p"
apply (simp add: EvalA_def)
apply (simp add: ClosureA.rep_eq)
done

theorem EvalA_RefA [evala] :
"\<lbrakk>p1 \<sqsubseteq>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<sqsubseteq>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: RefA.rep_eq)
done

declare TautologyA_def [evala]
declare ContradictionA_def [evala]
declare less_eq_WF_ALPHA_PREDICATE_def [evala]
declare less_WF_ALPHA_PREDICATE_def [evala]

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
      addsimps (alphabet.get ctxt);
*}

ML {*
  fun utp_alphabet_simpset ctxt =
    (simpset_of ctxt)
      addsimps (alphabet.get ctxt)
      addsimps (closure.get ctxt)
      addsimps @{thms alphabet_simps}
      addsimps @{thms alphabet_dist};
*}

ML {*
  fun utp_alpha_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_alpha_simpset ctxt) i)
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

method_setup utp_alphabet_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_alphabet_tac thms ctxt))
*} "proof tactic for alphabets"

subsection {* Proof Experiments *}

theorem EvalA_test :
"\<not>\<alpha> (\<not>\<alpha> p) = p"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

theorem EvalA_contr:
"p \<Rightarrow>\<alpha> false (\<alpha> p) = \<not>\<alpha> p"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

end
