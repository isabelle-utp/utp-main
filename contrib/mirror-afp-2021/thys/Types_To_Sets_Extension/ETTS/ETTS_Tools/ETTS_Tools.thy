(* Title: ETTS/ETTS_Tools/ETTS_Tools.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A collection of basic Isabelle/ML functions for the ETTS.
*)

section\<open>Import\<close>
theory ETTS_Tools
  imports "Conditional_Transfer_Rule.CTR_Tools"
begin



subsection\<open>Auxiliary\<close>

lemma tr_to_tr_rel: "A b c \<Longrightarrow> (Transfer.Rel A) b c"
  unfolding Transfer.Rel_def .



subsection\<open>Standard library extension\<close>

ML_file "More_Library.ML"
ML_file "More_Term.ML"
ML_file "More_Logic.ML"
ML_file "More_Tactical.ML"
ML_file "More_Simplifier.ML"
ML_file "More_HOLogic.ML"
ML_file "More_Transfer.ML"



subsection\<open>Specialized functionality\<close>

ML_file "ETTS_Writer.ML"

end