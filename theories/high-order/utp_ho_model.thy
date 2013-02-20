(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_ho_model.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* HO Model *}

theory utp_ho_model
imports
  "../utp_global"
  "../core/utp_synonyms"
  "../alpha/utp_alphabet"
  utp_ho_value
begin

text {*
  In this theory we provide a basic model for HO predicates. This cannot be
  simply done by interpretation of the @{term ALPHA_PRED} locale as we would
  have to discharge @{term "VALUE ho_type_rel"}. However, @{const ho_type_rel}
  only becomes fully meaningful when the type morphisms for @{type PROG_VALUE}
  are defined. In turn, the morphisms require the higher-order predicate model
  to be in place. To break this circularity, we duplicate the core definitions
  of @{term PRED} and @{term ALPHA_PRED} just so that the morphism can be
  defined. This is slightly cumbersome, but the only alternative solution may
  be to endow predicate locales with weaker assumptions and I am not sure this
  is an elegant and desirable solution either as it create surplus structure.
*}

subsection {* HO Alphabets *}

definition HO_ALPHABET :: "HO_TYPE ALPHABET set" where
"HO_ALPHABET = VAR.WF_ALPHABET"

subsection {* HO Bindings *}

definition HO_BINDING :: "(HO_VALUE, HO_TYPE) BINDING set" where
"HO_BINDING = {b . \<forall> v . (b v) : (type v)}"

definition HO_UNREST ::
  "(HO_TYPE VAR) set \<Rightarrow> (HO_VALUE, HO_TYPE) PREDICATE \<Rightarrow> bool" where
"HO_UNREST vs p \<longleftrightarrow> (\<forall> b1 \<in> p . \<forall> b2 \<in> HO_BINDING . b1 \<oplus> b2 on vs \<in> p)"

subsection {* HO Predicates *}

definition HO_PREDICATE :: "(HO_VALUE, HO_TYPE) PREDICATE set" where
"HO_PREDICATE = {b . b \<subseteq> HO_BINDING}"

definition HO_PREDICATE_OVER ::
  "(HO_TYPE VAR) set \<Rightarrow> (HO_VALUE, HO_TYPE) PREDICATE set" where
"HO_PREDICATE_OVER vs = {p . p \<in> HO_PREDICATE \<and> HO_UNREST (VAR - vs) p}"

subsection {* HO Alphabetised Predicates *}

abbreviation ho_alphabet ::
  "(HO_VALUE, HO_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (HO_TYPE ALPHABET)" where
"ho_alphabet p \<equiv> (fst p)"

notation ho_alphabet ("\<alpha>")

abbreviation ho_predicate ::
  "(HO_VALUE, HO_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (HO_VALUE, HO_TYPE) PREDICATE" where
"ho_predicate p \<equiv> (snd p)"

notation ho_predicate ("\<pi>")

definition HO_ALPHA_PREDICATE ::
  "(HO_VALUE, HO_TYPE) ALPHA_PREDICATE set" where
"HO_ALPHA_PREDICATE =
 {p . (\<alpha> p) \<in> HO_ALPHABET \<and> (\<pi> p) \<in> HO_PREDICATE_OVER (\<alpha> p)}"

theorems ho_model_simps =
  HO_ALPHABET_def
  HO_BINDING_def
  HO_UNREST_def
  HO_PREDICATE_def
  HO_PREDICATE_OVER_def
  HO_ALPHA_PREDICATE_def

subsection {* Theorems *}

text {* TODO: Check where the theorems below are actually needed. *}

subsubsection {* HO Alphabets *}

theorem HO_ALPHABET_empty [simp] :
"{} \<in> HO_ALPHABET"
apply (simp add: HO_ALPHABET_def)
apply (simp add: VAR.WF_ALPHABET_def)
done

theorem HO_ALPHABET_insert [simp] :
"a \<in> HO_ALPHABET \<Longrightarrow>
 (insert x a) \<in> HO_ALPHABET"
apply (simp add: HO_ALPHABET_def)
apply (simp add: VAR.WF_ALPHABET_def)
done

subsubsection {* HO Bindings *}

theorem HO_BINDING_subset [simp] :
"\<lbrakk>b \<in> bs; bs \<subseteq> HO_BINDING\<rbrakk> \<Longrightarrow>
 b \<in> HO_BINDING"
apply (auto)
done

theorem ho_type_rel_binding [simp] :
"\<lbrakk>p \<in> HO_ALPHA_PREDICATE; b \<in> \<pi> p\<rbrakk> \<Longrightarrow>
 (b v) : (type v)"
apply (simp add: HO_ALPHA_PREDICATE_def)
apply (simp add: HO_PREDICATE_OVER_def)
apply (simp add: HO_PREDICATE_def HO_BINDING_def)
apply (auto)
done

theorem HO_ALPHA_PREDICATE_equals :
"\<lbrakk>p1 \<in> HO_ALPHA_PREDICATE;
 p2 \<in> HO_ALPHA_PREDICATE;
 (\<alpha> p1) = (\<alpha> p2);
 (\<pi> p1) = (\<pi> p2)\<rbrakk> \<Longrightarrow> p1 = p2"
apply (simp add: prod_eq_iff)
done
end