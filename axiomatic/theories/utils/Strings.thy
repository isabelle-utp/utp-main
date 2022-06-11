(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Strings.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>String Literals\<close>

theory Strings
imports Normalise
  "HOL-Library.Countable"
  "HOL-Library.Char_ord"
  "Z_Toolkit.Infinity" 
begin

subsection \<open>Type Synonyms\<close>

type_synonym string_t = "String.literal"

translations (type) "string"   \<leftharpoondown> (type) "char list"
translations (type) "string_t" \<leftharpoondown> (type) "String.literal"

subsection \<open>Instantiations\<close>

subsubsection \<open>Countability\<close>

text \<open>@{type "String.literal"} already instantiates @{class countable}.\<close>

subsubsection \<open>Infinity\<close>

instance String.literal :: infinite
apply (intro_classes)
apply (rule String.infinite_literal)
done

subsubsection \<open>Linear Order\<close>

text \<open>@{type "String.literal"} already instantiates @{class linorder}.\<close>

subsubsection \<open>Normalisation\<close>

instance String.literal :: normalise by (intro_classes)

end