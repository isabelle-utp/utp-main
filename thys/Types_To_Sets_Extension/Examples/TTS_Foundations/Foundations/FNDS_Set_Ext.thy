(* Title: Examples/TTS_Foundations/Foundations/FNDS_Set_Ext.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Extension of the theory \<^text>\<open>Set\<close>\<close>
theory FNDS_Set_Ext
  imports Main
begin

lemma Ex1_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows "((A ===> (=)) ===> (=)) (\<lambda>P. (\<exists>!x\<in>(Collect (Domainp A)). P x)) Ex1"
  unfolding Ex1_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

text\<open>\newpage\<close>

end