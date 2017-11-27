(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp.thy                                                              *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section {* Meta-theory for Library Imports *}

theory utp_imports
  imports
  Deriv
  "~~/src/HOL/Library/Char_ord"  
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/Countable_Set"
  "~~/src/HOL/Library/FSet"
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Countable"
  "~~/src/HOL/Library/Order_Continuity"
  "~~/src/HOL/Library/Prefix_Order"
  "~~/src/HOL/Library/Product_Order"
  "~~/src/HOL/Library/Sublist"
  "../contrib/Algebra/Complete_Lattice"
  "../contrib/Algebra/Galois_Connection"
  "../optics/Lenses"
  "Library_extra/Countable_Set_extra"
  "Library_extra/FSet_extra"
  "Library_extra/List_extra"
  "Library_extra/List_lexord_alt"
  "Library_extra/Terminated_lists" 
  "Library_extra/Monoid_extra"
  "Library_extra/Pfun"
  "Library_extra/Ffun"
  "Library_extra/Set_extra"
  Infinity
  Positive
  Profiling
  TotalRecall
begin end
