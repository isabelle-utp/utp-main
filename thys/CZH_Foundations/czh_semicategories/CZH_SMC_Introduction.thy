(* Copyright 2021 (C) Mihails Milehins *)

chapter\<open>Semicategories\<close>

section\<open>Introduction\<close>
theory CZH_SMC_Introduction
  imports CZH_DG_Introduction
begin



subsection\<open>Background\<close>


text\<open>
Many concepts that are normally associated with category theory can be 
generalized to semicategories. It is the goal of 
this chapter to expose these generalized concepts and provide the 
relevant foundations for the development of the notion of a category
in the next chapter.
\<close>



subsection\<open>Preliminaries\<close>

named_theorems smc_op_simps
named_theorems smc_op_intros

named_theorems smc_cs_simps
named_theorems smc_cs_intros

named_theorems smc_arrow_cs_intros



subsection\<open>CS setup for foundations\<close>

lemmas (in \<Z>) [smc_cs_intros] = \<Z>_\<beta>

text\<open>\newpage\<close>

end