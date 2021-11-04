(* Title: Examples/SML_Relativization/Foundations/Set_Ext.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Extension of the theory \<^text>\<open>Set\<close>\<close>
theory Set_Ext
  imports Main
begin

lemma set_comp_pair: "{f t r |t r. P t r} = {x. \<exists>t r. P t r \<and> x = (f t r)}"
  by auto

lemma image_iff': "(\<forall>x\<in>A. f x \<in> B) = (f ` A \<subseteq> B)" by auto

text\<open>\newpage\<close>

end