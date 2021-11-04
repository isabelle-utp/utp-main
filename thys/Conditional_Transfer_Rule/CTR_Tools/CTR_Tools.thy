(* Title: CTR_Tools/CTR_Tools.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A collection of basic Isabelle/ML functions for the CTR.
*)

section\<open>Import\<close>
theory CTR_Tools 
  imports Main
begin



subsection\<open>Standard library extension\<close>

ML_file "More_Library.ML"
ML_file "More_Binding.ML"
ML_file "More_Type.ML"
ML_file "More_Sort.ML"
ML_file "More_Term.ML"
ML_file "More_Variable.ML"
ML_file "More_Logic.ML"
ML_file "More_Thm.ML"
ML_file "More_Simplifier.ML"
ML_file "More_HOLogic.ML"
ML_file "More_Transfer.ML"



subsection\<open>Specialized functionality\<close>

ML_file "CTR_Utilities.ML"

end