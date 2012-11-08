(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_ho_inst.thy                                                      *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* HO Instantiation *}

theory utp_ho_inst
imports "../utp_global"
  "../tactics/utp_pred_tac"
  "../tactics/utp_alpha_tac"
  utp_ho_value
  utp_ho_pred
begin

subsection {* Hiding Definitions *}

hide_const (open) utp_ho_model.HO_ALPHABET
hide_const (open) utp_ho_model.HO_BINDING
hide_const (open) utp_ho_model.HO_UNREST
hide_const (open) utp_ho_model.HO_PREDICATE
hide_const (open) utp_ho_model.HO_PREDICATE_OVER
hide_const (open) utp_ho_model.ho_alphabet
hide_const (open) utp_ho_model.ho_predicate
(* hide_const (open) utp_ho_model.Rank *)
hide_const (open) utp_ho_model.HO_ALPHA_PREDICATE
hide_const (open) utp_ho_model.HO_ALPHA_PREDICATE_OVER
hide_const (open) utp_ho_model.HO_ALPHA_PREDICATE_RANK

subsection {* Locale Interpretation *}

interpretation HO : HO_PRED "ho_type_rel"
apply (auto simp: HO_PRED_def HO_PRED_axioms_def ALPHA_PRED_def PRED_def)
done

subsection {* Type Definitions *}

typedef (open) HO_PREDICATE = "HO.WF_ALPHA_PREDICATE"
  morphisms Dest_HO_PREDICATE Mk_HO_PREDICATE
apply (rule_tac x = "HO.FALSE" in exI)
apply (simp add: closure)
done

typedef (open) HO_ALPHABET = "HO.WF_ALPHABET"
  morphisms Dest_HO_ALPHABET Mk_HO_ALPHABET
apply (rule_tac x = "{}" in exI)
apply (simp add: closure)
done

text {* Default Simplifications *}

declare Mk_HO_PREDICATE_inverse [simp]
declare Mk_HO_PREDICATE_inject [simp, intro!]
declare Dest_HO_PREDICATE_inverse [simp]
(* declare Dest_HO_PREDICATE_inject [simp, intro!] *)
declare Dest_HO_PREDICATE [simp]

theorem Dest_HO_PREDICATE_inject_sym [simp, intro!] :
"(p1 = p2) \<longleftrightarrow> (Dest_HO_PREDICATE p1 = Dest_HO_PREDICATE p2)"
apply (simp add: Dest_HO_PREDICATE_inject)
done

declare Mk_HO_ALPHABET_inverse [simp]
declare Mk_HO_ALPHABET_inject [simp, intro!]
declare Dest_HO_ALPHABET_inverse [simp]
(* declare Dest_HO_ALPHABET_inject [simp, intro!] *)
declare Dest_HO_ALPHABET [simp]

theorem Dest_HO_ALPHABET_inject_sym [simp, intro!] :
"(p1 = p2) \<longleftrightarrow> (Dest_HO_PREDICATE p1 = Dest_HO_PREDICATE p2)"
apply (simp add: Dest_HO_ALPHABET_inject)
done

subsection {* Semantic Domains *}

definition HO_ALPHABET [simp] :
"HO_ALPHABET \<equiv> HO.WF_ALPHABET"

definition HO_BINDING [simp] :
"HO_BINDING \<equiv> HO.WF_BINDING"

definition HO_BINDING_PRED [simp] :
"HO_BINDING_PRED = HO.WF_BINDING_PRED"

definition HO_PREDICATE [simp] :
"HO_PREDICATE = HO.WF_ALPHA_PREDICATE"

definition HO_FUNCTION [simp] :
"HO_FUNCTION = HO.WF_FUNCTION"

subsection {* Global Syntax *}

text {* Value Syntax *}

defs HO_set_type_rel [simp] :
"global_set_type_rel \<equiv> HO.set_type_rel"

text {* Predicate Syntax *}

definition HO_alphabet ::
  "HO_PREDICATE \<Rightarrow> HO_TYPE ALPHABET" ("\<alpha>") where
"\<alpha> p = HO.alphabet (Dest_HO_PREDICATE p)"

declare HO_alphabet_def [simp]

definition HO_predicate ::
  "HO_PREDICATE \<Rightarrow>
   (HO_VALUE, HO_TYPE) PREDICATE" ("\<pi>") where
"\<pi> p = HO.predicate (Dest_HO_PREDICATE p)"

declare HO_predicate_def [simp]

defs HO_binding_equiv [simp] :
"global_binding_equiv \<equiv> HO.binding_equiv"

defs HO_Lift [simp] :
"utp_global.Lift a bfun \<equiv>
 Mk_HO_PREDICATE (HO.LiftA a bfun)"

defs HO_True [simp] :
"utp_global.True a \<equiv>
 Mk_HO_PREDICATE (HO.TrueA a)"

defs HO_False [simp] :
"utp_global.False a \<equiv>
 Mk_HO_PREDICATE (HO.FalseA a)"

defs HO_TRUE [simp] :
"utp_global.TRUE \<equiv>
 Mk_HO_PREDICATE HO.TRUE"

defs HO_FALSE [simp] :
"utp_global.FALSE \<equiv>
 Mk_HO_PREDICATE HO.FALSE"

defs HO_Ext [simp] :
"utp_global.Ext p a \<equiv>
 Mk_HO_PREDICATE
   (HO.ExtA (Dest_HO_PREDICATE p) a)"

defs HO_Res [simp] :
"utp_global.Res p a \<equiv>
 Mk_HO_PREDICATE
   (HO.ResA (Dest_HO_PREDICATE p) a)"

defs HO_Not [simp] :
"utp_global.Not p \<equiv>
 Mk_HO_PREDICATE
   (HO.NotA (Dest_HO_PREDICATE p))"

defs HO_And [simp] :
"utp_global.And p1 p2 \<equiv>
 Mk_HO_PREDICATE (HO.AndA
   (Dest_HO_PREDICATE p1)
   (Dest_HO_PREDICATE p2))"

defs HO_Or [simp] :
"utp_global.Or p1 p2 \<equiv>
 Mk_HO_PREDICATE (HO.OrA
   (Dest_HO_PREDICATE p1)
   (Dest_HO_PREDICATE p2))"

defs HO_Implies [simp] :
"utp_global.Implies p1 p2 \<equiv>
 Mk_HO_PREDICATE (HO.ImpliesA
   (Dest_HO_PREDICATE p1)
   (Dest_HO_PREDICATE p2))"

defs HO_Iff [simp] :
"utp_global.Iff p1 p2 \<equiv>
 Mk_HO_PREDICATE (HO.IffA
   (Dest_HO_PREDICATE p1)
   (Dest_HO_PREDICATE p2))"

defs HO_Exists [simp] :
"utp_global.Exists a p \<equiv>
 Mk_HO_PREDICATE
   (HO.ExistsA a (Dest_HO_PREDICATE p))"

defs HO_Forall [simp] :
"utp_global.Forall a p \<equiv>
 Mk_HO_PREDICATE
   (HO.ForallA a (Dest_HO_PREDICATE p))"

defs HO_ExistsRes [simp] :
"utp_global.ExistsRes a p \<equiv>
 Mk_HO_PREDICATE
   (HO.ExistsResA a (Dest_HO_PREDICATE p))"

defs HO_ForallRes [simp] :
"utp_global.ForallRes a p \<equiv>
 Mk_HO_PREDICATE
   (HO.ForallResA a (Dest_HO_PREDICATE p))"

defs HO_Closure [simp] :
"utp_global.Closure p \<equiv>
 Mk_HO_PREDICATE
   (HO.ClosureA (Dest_HO_PREDICATE p))"

defs HO_Ref [simp] :
"utp_global.Ref p1 p2 \<equiv>
 Mk_HO_PREDICATE (HO.RefA
   (Dest_HO_PREDICATE p1)
   (Dest_HO_PREDICATE p2))"

defs HO_Tautology [simp] :
"utp_global.Tautology p \<equiv>
 HO.TautologyA (Dest_HO_PREDICATE p)"

defs HO_Contradiction [simp] :
"utp_global.Contradiction p \<equiv>
 HO.ContradictionA (Dest_HO_PREDICATE p)"

defs HO_Refinement [simp] :
"utp_global.Refinement p1 p2 \<equiv>
 HO.RefinementA
   (Dest_HO_PREDICATE p1)
   (Dest_HO_PREDICATE p2)"

subsection {* Proof Support *}

theorems global_syntax_intro_simps =
  sym [OF HO_alphabet_def]
  sym [OF HO_predicate_def]
  meta_sym [OF HO_binding_equiv]
  meta_sym [OF HO_Lift]
  meta_sym [OF HO_True]
  meta_sym [OF HO_False]
  meta_sym [OF HO_TRUE]
  meta_sym [OF HO_FALSE]
  meta_sym [OF HO_Ext]
  meta_sym [OF HO_Res]
  meta_sym [OF HO_Not]
  meta_sym [OF HO_And]
  meta_sym [OF HO_Or]
  meta_sym [OF HO_Implies]
  meta_sym [OF HO_Iff]
  meta_sym [OF HO_Exists]
  meta_sym [OF HO_Forall]
  meta_sym [OF HO_ExistsRes]
  meta_sym [OF HO_ForallRes]
  meta_sym [OF HO_Closure]
  meta_sym [OF HO_Ref]
  meta_sym [OF HO_Tautology]
  meta_sym [OF HO_Contradiction]
  meta_sym [OF HO_Refinement]

ML {*
  fun global_syntax_intro_simpset ctxt =
    HOL_basic_ss
      addsimps @{thms global_syntax_intro_simps};
*}

ML {*
  fun global_syntax_intro_tac ctxt i =
    TRY (asm_full_simp_tac (global_syntax_intro_simpset ctxt) i);
*}

method_setup global_syntax_intro = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (global_syntax_intro_tac ctxt))
*} "proof tactic to (re)introduce global syntax"

subsection {* Proof Experiments *}

theorem
"HO.MkInt(1) +v HO.MkInt(2) = HO.MkInt(3)"
apply (simp)
done

theorem
"HO.MkInt(1) \<in>v HO.MkSet({HO.MkInt(1), HO.MkInt(2)})"
apply (simp)
done

theorem
"HO.MkInt(3) \<in>v
 HO.MkSet({HO.MkInt(1)}) \<union>v HO.MkSet({HO.MkInt(1) +v HO.MkInt(2)})"
apply (simp)
done

theorem
"(p1 :: HO_PREDICATE) \<and>u (p2 \<and>u p3) = (p1 \<and>u p2) \<and>u p3"
apply (utp_alpha_tac)
apply (rule conjI)
apply (utp_alphabet_tac) [1]
apply (utp_pred_auto_tac) [1]
done

theorem
"taut (p1 :: HO_PREDICATE) \<and>u p2 \<Rightarrow>u p1"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

theorem
"\<alpha> (p1 :: HO_PREDICATE) = \<alpha> (p2 :: HO_PREDICATE) \<Longrightarrow>
 p1 \<or>u p2 \<sqsubseteq> p1"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

theorem
"\<lbrakk>(\<alpha> (p1 :: HO_PREDICATE)) = (\<alpha> p2);
 taut (p1 \<Rightarrow>u p2)\<rbrakk> \<Longrightarrow>
 p1 = (p1 \<and>u p2)"
apply (simp)
apply (global_syntax_intro)
apply (utp_alpha_tac)
-- {* The following doesn't do much! *}
apply (global_syntax_intro)
apply (utp_pred_auto_tac)
done
end