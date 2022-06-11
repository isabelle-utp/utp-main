(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uattrib.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Theorem Attributes\<close>

theory uattrib
imports "../utils/Named_Attrib"
begin

subsection \<open>Named Theorems\<close>

\<comment> \<open>Commented out partly for compatibility with Isabelle/UTP.\<close>

named_theorems typing "typing theorems"
named_theorems vars "variable theorems"
named_theorems alphas "alphabet theorems"
(* named_theorems unrest "unrestriction laws" *)
(* named_theorems closure "closure theorems" *)
named_theorems refine "refinement laws"

subsection \<open>Attribute Structures\<close>

\<comment> \<open>Commented out partly for compatibility with Isabelle/UTP.\<close>

ML \<open>
  structure typing = Named_Attrib(val name = @{named_theorems typing});
  structure vars = Named_Attrib(val name = @{named_theorems vars});
  structure alphas = Named_Attrib(val name = @{named_theorems alphas});
  (* structure unrest = Named_Attrib(val name = @{named_theorems unrest}); *)
  (* structure closure = Named_Attrib(val name = @{named_theorems closure}); *)
  structure refine = Named_Attrib(val name = @{named_theorems refine});
\<close>

end