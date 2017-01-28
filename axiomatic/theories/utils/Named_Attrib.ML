(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Named_Attrib.ML                                                      *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

(* Attribute Structure *)

signature NAMED_ATTRIB =
sig
  val get : Proof.context -> thm list;
  val add : attribute;
  val del : attribute;
end;

(* Instantiation Functor *)

functor Named_Attrib(val name : string) : NAMED_ATTRIB =
struct
  val get = (fn ctx => Named_Theorems.get ctx name);
  val add = Named_Theorems.add name;
  val del = Named_Theorems.del name;
end;
