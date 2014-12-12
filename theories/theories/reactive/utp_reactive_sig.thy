(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster and Samuel Canham, University of York                *)
(******************************************************************************)

header {* UTP Reactive Signature *}

theory utp_reactive_sig
imports 
  utp_theory
begin

class REACTIVE_SORT = 
  BOOL_SORT + 
  LIST_SORT + 
  FSET_SORT + 
  SET_SORT +
  EVENT_SORT

default_sort REACTIVE_SORT

text {* Reactive Alphabet *}

abbreviation "ref  \<equiv> MkPlainP ''ref'' True TYPE('m event USET) TYPE('m)"
abbreviation "wait \<equiv> MkPlainP ''wait'' True TYPE(bool) TYPE('m)"
abbreviation "tr   \<equiv> MkPlainP ''tr'' True TYPE('m event ULIST) TYPE('m)"

abbreviation "TR \<equiv> {tr\<down>, tr\<down>\<acute>}"
abbreviation "WAIT \<equiv> {wait\<down>, wait\<down>\<acute>}"
abbreviation "REA \<equiv> {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}"
end