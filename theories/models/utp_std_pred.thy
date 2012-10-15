(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_std_pred.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Standard Predicates *}

theory utp_std_pred
imports
  "../utp_global"
  "../alpha/utp_alpha_pred"
  "../tactics/utp_pred_tac"
  "../tactics/utp_alpha_tac"
  utp_default_value
  utp_complex_value
begin

type_synonym STD_VALUE = "DEFAULT_VALUE COMPLEX_VALUE"
type_synonym STD_TYPE = "DEFAULT_TYPE COMPLEX_TYPE"

subsection {* Locale @{term STD_PRED} *}

locale STD_PRED =
  COMPLEX_VALUE "basic_type_rel" +
  ALPHA_PRED "complex_type_rel ::
    'VALUE COMPLEX_VALUE \<Rightarrow> 'TYPE COMPLEX_TYPE \<Rightarrow> bool"
for basic_type_rel :: "'VALUE :: BASIC_VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool"

subsection {* Locale Interpretation *}

interpretation STD : STD_PRED "default_type_rel"
apply (simp add: STD_PRED_def ALPHA_PRED_def PRED_def)
apply (auto)
done

subsection {* Type Definitions *}

typedef (open) STD_PREDICATE = "STD.WF_ALPHA_PREDICATE"
  morphisms Dest_STD_PREDICATE Mk_STD_PREDICATE
apply (rule_tac x = "STD.FALSE" in exI)
apply (simp add: closure)
done

typedef (open) STD_ALPHABET = "STD.WF_ALPHABET"
  morphisms Dest_STD_ALPHABET Mk_STD_ALPHABET
apply (rule_tac x = "{}" in exI)
apply (simp add: closure)
done

text {* Default Simplifications *}

declare Mk_STD_PREDICATE_inverse [simp]
declare Mk_STD_PREDICATE_inject [simp, intro!]
declare Dest_STD_PREDICATE_inverse [simp]
(* declare Dest_STD_PREDICATE_inject [simp, intro!] *)
declare Dest_STD_PREDICATE [simp]

theorem Dest_STD_PREDICATE_inject_sym [simp, intro!] :
"(p1 = p2) \<longleftrightarrow> (Dest_STD_PREDICATE p1 = Dest_STD_PREDICATE p2)"
apply (simp add: Dest_STD_PREDICATE_inject)
done

declare Mk_STD_ALPHABET_inverse [simp]
declare Mk_STD_ALPHABET_inject [simp, intro!]
declare Dest_STD_ALPHABET_inverse [simp]
(* declare Dest_STD_ALPHABET_inject [simp, intro!] *)
declare Dest_STD_ALPHABET [simp]

theorem Dest_STD_ALPHABET_inject_sym [simp, intro!] :
"(p1 = p2) \<longleftrightarrow> (Dest_STD_PREDICATE p1 = Dest_STD_PREDICATE p2)"
apply (simp add: Dest_STD_ALPHABET_inject)
done

subsection {* Semantic Domains *}

definition STD_ALPHABET [simp] :
"STD_ALPHABET \<equiv> STD.WF_ALPHABET"

definition STD_BINDING [simp] :
"STD_BINDING \<equiv> STD.WF_BINDING"

definition STD_BINDING_PRED [simp] :
"STD_BINDING_PRED \<equiv> STD.WF_BINDING_PRED"

definition STD_PREDICATE [simp] :
"STD_PREDICATE \<equiv> STD.WF_ALPHA_PREDICATE"

definition STD_FUNCTION [simp] :
"STD_FUNCTION \<equiv> STD.WF_FUNCTION"

subsection {* Global Syntax *}

text {* Value Syntax *}

defs STD_set_type_rel [simp] :
"global_set_type_rel \<equiv> STD.set_type_rel"

text {* Predicate Syntax *}

definition STD_alphabet ::
  "STD_PREDICATE \<Rightarrow> STD_TYPE ALPHABET" ("\<alpha>") where
"\<alpha> p = STD.alphabet (Dest_STD_PREDICATE p)"

declare STD_alphabet_def [simp]

definition STD_predicate ::
  "STD_PREDICATE \<Rightarrow>
   (STD_VALUE, STD_TYPE) PREDICATE" ("\<pi>") where
"\<pi> p = STD.predicate (Dest_STD_PREDICATE p)"

declare STD_predicate_def [simp]

defs STD_binding_equiv [simp] :
"global_binding_equiv \<equiv> STD.binding_equiv"

defs STD_LiftG [simp] :
"LiftG a bfun \<equiv>
 Mk_STD_PREDICATE (STD.LiftA a bfun)"

defs STD_TrueG [simp] :
"TrueG a \<equiv>
 Mk_STD_PREDICATE (STD.TrueA a)"

defs STD_FalseG [simp] :
"FalseG a \<equiv>
 Mk_STD_PREDICATE (STD.FalseA a)"

defs STD_TRUE [simp] :
"TRUE \<equiv>
 Mk_STD_PREDICATE STD.TRUE"

defs STD_FALSE [simp] :
"FALSE \<equiv>
 Mk_STD_PREDICATE STD.FALSE"

defs STD_ExtG [simp] :
"ExtG p a \<equiv>
 Mk_STD_PREDICATE
   (STD.ExtA (Dest_STD_PREDICATE p) a)"

defs STD_ResG [simp] :
"ResG p a \<equiv>
 Mk_STD_PREDICATE
   (STD.ResA (Dest_STD_PREDICATE p) a)"

defs STD_NotG [simp] :
"NotG p \<equiv>
 Mk_STD_PREDICATE
   (STD.NotA (Dest_STD_PREDICATE p))"

defs STD_AndG [simp] :
"AndG p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.AndA
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_OrG [simp] :
"OrG p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.OrA
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_ImpliesG [simp] :
"ImpliesG p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.ImpliesA
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_IffG [simp] :
"IffG p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.IffA
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_ExistsG [simp] :
"ExistsG a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ExistsA a (Dest_STD_PREDICATE p))"

defs STD_ForallG [simp] :
"ForallG a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ForallA a (Dest_STD_PREDICATE p))"

defs STD_ExistsResG [simp] :
"ExistsResG a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ExistsResA a (Dest_STD_PREDICATE p))"

defs STD_ForallResG [simp] :
"ForallResG a p \<equiv>
 Mk_STD_PREDICATE
   (STD.ForallResA a (Dest_STD_PREDICATE p))"

defs STD_ClosureG [simp] :
"ClosureG p \<equiv>
 Mk_STD_PREDICATE
   (STD.ClosureA (Dest_STD_PREDICATE p))"

defs STD_RefG [simp] :
"RefG p1 p2 \<equiv>
 Mk_STD_PREDICATE (STD.RefA
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2))"

defs STD_Tautology [simp] :
"Tautology p \<equiv>
 STD.TautologyA (Dest_STD_PREDICATE p)"

defs STD_Contradiction [simp] :
"Contradiction p \<equiv>
 STD.ContradictionA (Dest_STD_PREDICATE p)"

defs STD_Refinement [simp] :
"Refinement p1 p2 \<equiv>
 STD.RefinementA
   (Dest_STD_PREDICATE p1)
   (Dest_STD_PREDICATE p2)"

theorem meta_sym : "(A \<equiv> B) \<Longrightarrow> (B = A)"
apply (auto)
done

subsection {* Proof Support *}

theorems global_syntax_intro_simps =
  sym [OF STD_alphabet_def]
  sym [OF STD_predicate_def]
  meta_sym [OF STD_binding_equiv]
  meta_sym [OF STD_LiftG]
  meta_sym [OF STD_TrueG]
  meta_sym [OF STD_FalseG]
  meta_sym [OF STD_TRUE]
  meta_sym [OF STD_FALSE]
  meta_sym [OF STD_ExtG]
  meta_sym [OF STD_ResG]
  meta_sym [OF STD_NotG]
  meta_sym [OF STD_AndG]
  meta_sym [OF STD_OrG]
  meta_sym [OF STD_ImpliesG]
  meta_sym [OF STD_IffG]
  meta_sym [OF STD_ExistsG]
  meta_sym [OF STD_ForallG]
  meta_sym [OF STD_ExistsResG]
  meta_sym [OF STD_ForallResG]
  meta_sym [OF STD_ClosureG]
  meta_sym [OF STD_RefG]
  meta_sym [OF STD_Tautology]
  meta_sym [OF STD_Contradiction]
  meta_sym [OF STD_Refinement]

ML {*
  fun utp_syntax_intro_simpset ctxt =
    HOL_basic_ss
      addsimps @{thms global_syntax_intro_simps};
*}

ML {*
  fun utp_syntax_intro_tac ctxt i =
    TRY (asm_full_simp_tac (utp_syntax_intro_simpset ctxt) i);
*}

method_setup utp_syntax_intro = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_syntax_intro_tac ctxt))
*} "proof tactic to (re)introduce global syntax"

subsection {* Proof Experiments *}

theorem
"STD.MkInt(1) +v STD.MkInt(2) = STD.MkInt(3)"
apply (simp)
done

theorem
"STD.MkInt(1) \<in>v STD.MkSet({STD.MkInt(1), STD.MkInt(2)})"
apply (simp)
done

theorem
"STD.MkInt(3) \<in>v
 STD.MkSet({STD.MkInt(1)}) \<union>v STD.MkSet({STD.MkInt(1) +v STD.MkInt(2)})"
apply (simp)
done

theorem
"(p1 :: STD_PREDICATE) \<and>u (p2 \<and>u p3) = (p1 \<and>u p2) \<and>u p3"
apply (utp_alpha_tac)
apply (rule conjI)
apply (utp_alphabet_tac) [1]
apply (utp_pred_auto_tac) [1]
done

theorem
"taut (p1 :: STD_PREDICATE) \<and>u p2 \<Rightarrow>u p1"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

theorem
"\<alpha> (p1 :: STD_PREDICATE) = \<alpha> (p2 :: STD_PREDICATE) \<Longrightarrow>
 p1 \<or>u p2 \<sqsubseteq> p1"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

theorem
"\<lbrakk>(\<alpha> (p1 :: STD_PREDICATE)) = (\<alpha> p2);
 taut (p1 \<Rightarrow>u p2)\<rbrakk> \<Longrightarrow>
 p1 = (p1 \<and>u p2)"
apply (simp)
apply (utp_syntax_intro)
apply (utp_alpha_tac)
apply (utp_syntax_intro)
apply (utp_pred_auto_tac)
done
end