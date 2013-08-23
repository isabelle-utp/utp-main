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

(* FIXME: Surely these can all be unified into a single thing ... *)

lift_definition Exec1D :: 
  "('a option \<Rightarrow> cmlp) \<Rightarrow> 'a cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e. {b :: cmlv WF_BINDING. b \<in> P (e b)}" .

lift_definition Exec2D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> cmlp) \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f. {b :: cmlv WF_BINDING. b \<in> P (e b) (f b)}" .

lift_definition Exec3D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g. {b :: cmlv WF_BINDING. b \<in> P (e b) (f b) (g b)}" .

lift_definition Exec4D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g h. {b :: cmlv WF_BINDING. b \<in> P (e b) (f b) (g b) (h b)}" .

lift_definition Exec5D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option \<Rightarrow> 'e option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle \<Rightarrow> 'e cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g h i. {b :: cmlv WF_BINDING. b \<in> P (e b) (f b) (g b) (h b) (i b)}" .

lift_definition Exec6D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option \<Rightarrow> 'e option \<Rightarrow> 'f option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle \<Rightarrow> 'e cmle \<Rightarrow> 'f cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g h i j. {b :: cmlv WF_BINDING. b \<in> P (e b) (f b) (g b) (h b) (i b) (j b)}" .

syntax
  "_upred_parcml"    :: "upred \<Rightarrow> cmlv UCHAN set \<Rightarrow> upred \<Rightarrow> upred" (infixl "[|_|]" 50)
  "_upred_cml_exec1" :: "idt \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_')")
  "_upred_cml_exec2" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_, _')")
  "_upred_cml_exec3" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_, _, _')")
  "_upred_cml_exec4" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_, _, _, _')")
  "_upred_cml_exec5" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_, _, _, _, _')")
  "_upred_cml_exec6" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_'(_, _, _, _, _, _')")

translations
  "_upred_parcml p vs q"        == "CONST ParallelD p vs q"
  "_upred_cml_exec1 f s"        == "CONST R (CONST Exec1D f s)"
  "_upred_cml_exec2 v1 v2 s"    == "CONST R (CONST Exec2D v1 v2 s)"
  "_upred_cml_exec3 v1 v2 v3 s" == "CONST R (CONST Exec3D v1 v2 v3 s)"
  "_upred_cml_exec3 v1 v2 v3 v4 s" == "CONST R (CONST Exec3D v1 v2 v3 v4 s)"
  "_upred_cml_exec3 v1 v2 v3 v4 v5 s" == "CONST R (CONST Exec3D v1 v2 v3 v4 v5 s)"
  "_upred_cml_exec3 v1 v2 v3 v4 v5 v6 s" == "CONST R (CONST Exec3D v1 v2 v3 v4 v5 v6 s)"

term "`P [|{x,y,z}|] Q`"

term "MkChanD"

end