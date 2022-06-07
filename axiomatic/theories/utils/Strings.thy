(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Strings.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* String Literals *}

theory Strings
imports "Z_Toolkit.Infinity" Normalise
  "HOL-Library.Countable"
  "HOL-Library.Char_ord"
begin

subsection {* Type Synonyms *}

type_synonym string_t = "String.literal"

translations (type) "string"   \<leftharpoondown> (type) "char list"
translations (type) "string_t" \<leftharpoondown> (type) "String.literal"

subsection {* Instantiations *}

subsubsection {* Countability *}

text {* @{type "String.literal"} already instantiates @{class countable}. *}

subsubsection {* Infinity *}

setup_lifting String.type_definition_literal

lift_definition succ_literal :: "String.literal \<Rightarrow> String.literal"
is "\<lambda>s. String.ascii_of undefined # s" by (auto)

lemma inj_succ_literal :
"inj succ_literal"
apply (rule injI)
apply (transfer)
apply (simp)
done

lemma not_surj_succ_literal :
"\<not> surj succ_literal"
apply (unfold surj_def)
apply (clarsimp)
apply (transfer)
apply (rule_tac x = "[]" in bexI)
apply (auto)
done

theorem infinite_UNIV_String_literal [simp]:
"infinite (UNIV :: String.literal set)"
apply (clarify)
apply (drule_tac f = "succ_literal" in finite_UNIV_inj_surj)
apply (rule inj_succ_literal)
apply (erule contrapos_pp; simp)
apply (rule not_surj_succ_literal)
done

instance String.literal :: infinite
apply (intro_classes)
apply (rule infinite_UNIV_String_literal)
done

hide_const succ_literal

hide_fact inj_succ_literal not_surj_succ_literal

subsubsection {* Linear Order *}

text {* @{type "String.literal"} already instantiates @{class linorder}. *}

subsubsection {* Normalisation *}

instance String.literal :: normalise by (intro_classes)
end