(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Reference prerequisites\<close>
theory Reference_Prerequisites
  imports "HOL-Library.LaTeXsugar" 
begin

ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>


(* Copied from Transfer.thy in the main library. *)
notation rel_fun (infixr "===>" 55)
notation map_fun (infixr "--->" 55)

end