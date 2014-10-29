(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Unit_ord.thy                                                         *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 3 September 2014 *)

header {* Unit Order *}

theory Unit_ord
imports "../utp_common"
begin

text {*
  Defining a linear order for the @{type unit} type is useful in conjunction
  with defining linear orders on record types, because the type instantiated
  for ``more'' in a closed record is typically @{type unit}.
*}

instantiation unit :: linorder
begin
definition less_eq_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
"less_eq_unit x y \<longleftrightarrow> True"
definition less_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
"less_unit x y \<longleftrightarrow> False"
instance
apply (intro_classes)
apply (unfold less_eq_unit_def less_unit_def)
apply (simp_all)
done
end

paragraph {* Default Simplifications *}

declare less_eq_unit_def [simp]
declare less_unit_def [simp]
end
