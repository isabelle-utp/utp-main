(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: wf_value.thy                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Sep 2017 *)

section {* Well-formed Values *}

theory wf_value
imports Main
begin

text {*
  We declare a type class here that introduces a notion of well-formedness of
  values of some HOL type @{typ 'a}. With this, we are able to perform generic
  construction of subtypes that include well-formed values only. We may use
  this, for instance, to obtain types for well-formed events.
*}

class wf =
fixes is_wf :: "'a \<Rightarrow> bool"
assumes wf_value_exists: "\<exists>x. is_wf x"
begin
definition WF_UNIV :: "'a itself \<Rightarrow> 'a set" where
"WF_UNIV t = Collect is_wf"
end

text {* Generic construction of a subtype comprising well-defined values only. *}

typedef (overloaded) 'a::wf wf = "WF_UNIV TYPE('a)"
apply (unfold WF_UNIV_def)
apply (clarsimp)
apply (rule wf_value_exists)
done

setup_lifting type_definition_wf
end