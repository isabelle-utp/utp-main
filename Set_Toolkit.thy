section \<open> Set Toolkit \<close>

theory Set_Toolkit
  imports "HOL-Library.Adhoc_Overloading" "Relation_Lib"
begin

text \<open> The majority of the Z set toolkit is implemented in the core libraries of HOL. We could
  prove all the axioms of ISO 13568 as theorems, but we omit this for now. The main thing we
  need is to map between finite sets and the normal set type. \<close>

declare [[coercion_enabled]]

unbundle Z_Type_Syntax

end