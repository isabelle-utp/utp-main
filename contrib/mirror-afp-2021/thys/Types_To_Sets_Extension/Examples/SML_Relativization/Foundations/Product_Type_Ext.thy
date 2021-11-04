(* Title: Examples/SML_Relativization/Foundations/Product_Type_Ext.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Extension of the theory \<^text>\<open>Product_Type_Ext\<close>\<close>
theory Product_Type_Ext
  imports Main
begin

context
  includes lifting_syntax
begin

lemma Sigma_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A"
  shows 
    "(rel_set A ===> (A ===> rel_set B) ===> rel_set (rel_prod A B))
      Sigma Sigma"
  unfolding Sigma_def by transfer_prover

end

text\<open>\newpage\<close>

end