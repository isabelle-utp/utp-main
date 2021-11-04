(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Introduction\<close>
theory CZH_ECAT_Introduction
  imports CZH_Foundations.CZH_DG_Introduction
begin



subsection\<open>Background\<close>


text\<open>
This article provides a 
formalization of the elementary theory of 1-categories without
an additional structure. For further information see 
chapter Introduction in \cite{milehins_category_2021}.
\<close>



subsection\<open>Preliminaries\<close>

named_theorems cat_op_simps
named_theorems cat_op_intros

named_theorems cat_cs_simps
named_theorems cat_cs_intros

named_theorems cat_arrow_cs_intros



subsection\<open>CS setup for foundations\<close>

lemmas (in \<Z>) [cat_cs_intros] = 
  \<Z>_\<beta>
  
text\<open>\newpage\<close>

end