(* Title: UD/UD.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Infrastructure for unoverloading definitions.
*)

section\<open>UD\<close>
theory UD
  imports "../CTR_Tools/CTR_Tools" Main
  keywords "ud" :: thy_decl
begin



subsection\<open>Import\<close>

ML_file\<open>UD_With.ML\<close>
ML_file\<open>UD_Consts.ML\<close>
ML_file\<open>UD.ML\<close>



subsection\<open>\<open>ud_with\<close>\<close>

setup\<open>UD_With.UDWithData.setup\<close>

end