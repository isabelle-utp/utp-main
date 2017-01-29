(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uattrib.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* Theorem Attributes *}

theory uattrib
imports Main "../utils/Named_Attrib"
begin

subsection {* Named Theorems *}

(* Commented out partly for compatibility with Isabelle/UTP. *)

named_theorems typing "typing theorems"
named_theorems vars "variable theorems"
named_theorems alphabet "alphabet theorems"
(* named_theorems unrest "unrestriction laws" *)
(* named_theorems closure "closure theorems" *)
named_theorems refine "refinement laws"

subsection {* Attribute Structures *}

ML {*
  structure typing = Named_Attrib(val name = @{named_theorems typing});
  structure vars = Named_Attrib(val name = @{named_theorems vars});
  structure alphabet = Named_Attrib(val name = @{named_theorems alphabet});
  (* structure unrest = Named_Attrib(val name = @{named_theorems unrest}); *)
  (* structure closure = Named_Attrib(val name = @{named_theorems closure}); *)
  structure refine = Named_Attrib(val name = @{named_theorems refine});
*}
end