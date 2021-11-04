(* Title: Examples/TTS_Foundations/Foundations/FNDS_Auxiliary.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Auxiliary\<close>
theory FNDS_Auxiliary
  imports Types_To_Sets_Extension.ETTS_Auxiliary
begin



subsection\<open>Methods\<close>

method ow_locale_transfer uses locale_defs = 
  (
    unfold locale_defs, 
    (
      (simp only: all_simps(6) all_comm, fold Ball_def) 
      | (fold Ball_def) 
      | tactic\<open>all_tac\<close>
    ),
    transfer_prover_start,
    transfer_step+,
    rule refl
  )

text\<open>\newpage\<close>

end