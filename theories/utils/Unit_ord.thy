(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Unit_ord.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 23 January 2014 *)

header {* Linear Order for Unit *}

theory Unit_ord
imports Main
begin

text {*
  Defining a linear order on @{type unit} is useful in conjunction with linear
  orders on open record types, because the type instantiated for ``more'' in a
  closed record is typically @{type unit}.
*}

instantiation unit :: linorder
begin
definition less_eq_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
"less_eq_unit x y \<longleftrightarrow> True"
definition less_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
"less_unit x y \<longleftrightarrow> False"
instance
apply (intro_classes)
apply (simp_all add: less_eq_unit_def less_unit_def)
done
end

text {* Default Simplifications *}

declare less_eq_unit_def [simp]
declare less_unit_def [simp]
end
