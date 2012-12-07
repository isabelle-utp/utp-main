(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_alpha_tac.thy                                                    *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Alphabetised Predicates *}

theory utp_alpha_tac
imports "../alpha/utp_alpha_pred"
begin

text {* Theorem Attribute *}

ML {*
  structure evala =
    Named_Thms (val name = @{binding evala} val description = "evala theorems")
*}

setup evala.setup

context ALPHA_PRED
begin

subsection {* Interpretation Function *}

definition EvalA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" ("\<lbrakk>_\<rbrakk>\<pi>") where
"EvalA p = \<pi> p"

subsection {* Transfer Theorems *}

theorem EvalA_simp [evala] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 = p2 \<longleftrightarrow> (\<alpha> p1) = (\<alpha> p2) \<and> \<lbrakk>p1\<rbrakk>\<pi> = \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: prod_eq_iff)
done

theorem EvalA_intro :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 (\<alpha> p1) = (\<alpha> p2);
 \<lbrakk>p1\<rbrakk>\<pi> = \<lbrakk>p2\<rbrakk>\<pi>\<rbrakk> \<Longrightarrow> p1 = p2"
apply (simp add: EvalA_def)
apply (simp add: prod_eq_iff)
done

subsection {* Distribution Theorems *}

theorem EvalA_LiftA [evala] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_PRED a\<rbrakk> \<Longrightarrow>
 \<lbrakk>LiftA a f\<rbrakk>\<pi> = LiftP f"
apply (simp add: EvalA_def)
apply (simp add: LiftA_def)
done

theorem EvalA_EqualsA [evala] :
"\<lbrakk>v =\<alpha> x\<rbrakk>\<pi> = (v =p x)"
apply (simp add: EvalA_def)
apply (simp add: EqualsA_def)
done

theorem EvalA_TrueA [evala] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 \<lbrakk>true a\<rbrakk>\<pi> = true"
apply (simp add: EvalA_def)
apply (simp add: TrueA_def)
done

theorem EvalA_FalseA [evala] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 \<lbrakk>false a\<rbrakk>\<pi> = false"
apply (simp add: EvalA_def)
apply (simp add: FalseA_def)
done

theorem EvalA_ExtA [evala] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<lbrakk>p \<oplus>\<alpha> a\<rbrakk>\<pi> = \<lbrakk>p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ExtA_def)
done

theorem EvalA_ResA [evala] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<lbrakk>p \<ominus>\<alpha> a\<rbrakk>\<pi> = (\<exists>p a . \<lbrakk>p\<rbrakk>\<pi>)"
apply (simp add: EvalA_def)
apply (simp add: ResA_def)
done

theorem EvalA_NotA [evala] :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow>
 \<lbrakk>\<not>\<alpha> p\<rbrakk>\<pi> = \<not>p \<lbrakk>p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: NotA_def)
done

theorem EvalA_AndA [evala] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<and>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<and>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: AndA_def)
done

theorem EvalA_OrA [evala] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<or>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<or>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: OrA_def)
done

theorem EvalA_ImpliesA [evala] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<Rightarrow>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<Rightarrow>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ImpliesA_def)
done

theorem EvalA_IffA [evala] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<Leftrightarrow>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<Leftrightarrow>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: IffA_def)
done

theorem EvalA_ExistsA [evala] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<exists>\<alpha> a . p\<rbrakk>\<pi> = (\<exists>p a . \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add: EvalA_def ExistsA_def)

theorem EvalA_ForallA [evala] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<forall>\<alpha> a . p\<rbrakk>\<pi> = (\<forall>p a . \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add: EvalA_def ForallA_def)

theorem EvalA_ExistsResA [evala] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<exists>-\<alpha> a . p\<rbrakk>\<pi> = \<lbrakk>\<exists>\<alpha> a . p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ExistsResA_def)
apply (simp add: ExistsA_def)
done

theorem EvalA_ForallResA [evala] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<forall>-\<alpha> a . p\<rbrakk>\<pi> = \<lbrakk>\<forall>\<alpha> a . p\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: ForallResA_def)
apply (simp add: ForallA_def)
done

theorem EvalA_ClosureA [evala] :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow>
 \<lbrakk>[p]\<alpha>\<rbrakk>\<pi> = [\<lbrakk>p\<rbrakk>\<pi>]p"
apply (simp add: EvalA_def)
apply (simp add: ClosureA_def)
done

theorem EvalA_RefA [evala] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<lbrakk>p1 \<sqsubseteq>\<alpha> p2\<rbrakk>\<pi> = \<lbrakk>p1\<rbrakk>\<pi> \<sqsubseteq>p \<lbrakk>p2\<rbrakk>\<pi>"
apply (simp add: EvalA_def)
apply (simp add: RefA_def)
done

declare TautologyA_def [evala]
declare ContradictionA_def [evala]
declare RefinementA_def [evala]
end

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
      addsimps @{thms VAR.alphabet_simps}
      addsimps @{thms VAR.alphabet_dist};
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

context ALPHA_PRED
begin

subsection {* Support Theorems *}

theorem alphabet_WF_ALPHABET [closure] :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> \<lbrakk>p\<rbrakk>\<pi> \<in> WF_PREDICATE"
apply (simp add: EvalA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
done

subsection {* Proof Experiments *}

theorem EvalA_test :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow>
 \<not>\<alpha> (\<not>\<alpha> p) = p"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

theorem EvalA_contr:
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> 
p \<Rightarrow>\<alpha> false (\<alpha> p) = \<not>\<alpha> p"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

end
end
