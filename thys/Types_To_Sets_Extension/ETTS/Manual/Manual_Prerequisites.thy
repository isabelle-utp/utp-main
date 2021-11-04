(* Title: ETTS/Manual/Manual_Prerequisites.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

section\<open>Prerequisites\<close>
theory Manual_Prerequisites
  imports 
    "../ETTS"
    "HOL-Library.LaTeXsugar"
begin

ML_file \<open>~~/src/Doc/antiquote_setup.ML\<close>

(* Copied from Transfer.thy in the main library. *)
notation rel_fun (infixr "===>" 55)
notation map_fun (infixr "--->" 55)

type_notation bool (\<open>\<bool>\<close>)

end