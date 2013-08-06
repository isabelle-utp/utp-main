(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_process.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML processes *}

theory utp_cml_process
imports 
  utp_cml_expr
  utp_cml_types
begin

definition ParallelD :: 
  "cmlp \<Rightarrow> cmlv UCHAN set \<Rightarrow> cmlp \<Rightarrow> cmlp" where
"ParallelD p cs q = ParallelCSP p (LitPE (MkEvents cs)) q"

abbreviation MkChanD :: "string \<Rightarrow> 'a set \<Rightarrow> ('a option) CHAN" where
"MkChanD n xs \<equiv> MkCHAN (bName n, TYPE('a option))"

(* FIXME: Execution of CML operations needs to take care of undefinedness *)

lift_definition Exec1D :: 
  "('a option \<Rightarrow> cmlp) \<Rightarrow> 'a cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e. {b :: cmlv WF_BINDING. b \<in> P (e b)}" .

lift_definition Exec2D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> cmlp) \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f. {b :: cmlv WF_BINDING. b \<in> P (e b) (f b)}" .

syntax
  "_upred_parcml"    :: "upred \<Rightarrow> cmlv UCHAN set \<Rightarrow> upred \<Rightarrow> upred" (infixl "[|_|]" 50)
  "_upred_cml_exec1" :: "idt \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_')")
  "_upred_cml_exec2" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_, _')")

translations
  "_upred_parcml p vs q"     == "CONST ParallelD p vs q"
  "_upred_cml_exec1 f s"     == "CONST R (CONST Exec1D f s)"
  "_upred_cml_exec2 v1 v2 s" == "CONST R (CONST Exec2D v1 v2 s)"

term "`P [|{x,y,z}|] Q`"

term "MkChanD"

end