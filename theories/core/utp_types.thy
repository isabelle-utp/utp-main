(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_types.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Abstract Type Locales *}

theory utp_types
imports utp_value utp_sorts
begin

hide_const (open) Lattice.top
hide_const (open) Lattice.inf
hide_const (open) Lattice.sup

context VALUE
begin

definition mtype_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":!" 50) where
"mtype_rel v t \<equiv> \<forall> t'. v : t' \<longrightarrow> t' = t"

end


locale BOT_VALUE = 
  VALUE where type_rel = type_rel
  for type_rel :: "'VALUE :: BOT_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) +
  assumes bot_type [typing]: "bot : t"

locale BOOL_VALUE = 
  BOT_VALUE where type_rel = type_rel
  for type_rel :: "'VALUE :: {BOOL_SORT,BOT_SORT} \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) +
  fixes BoolType :: 'TYPE
  assumes TypeLink: "\<And> x. \<lbrakk> \<D> x \<rbrakk> \<Longrightarrow> x : BoolType \<longleftrightarrow> x \<in> range MkBool"

begin

lemma MkBool_type [typing]: "MkBool x : BoolType"
  by (simp add:Defined TypeLink)

lemma BoolType_defined: "\<And> x. \<lbrakk> x : BoolType; \<D> x \<rbrakk> \<Longrightarrow> x \<in> range MkBool"
  by (simp add:TypeLink)

lemma MkBool_cases: "\<lbrakk> x : BoolType; \<D> x \<rbrakk> \<Longrightarrow> x = MkBool True \<or> x = MkBool False"
  by (metis (full_types) BoolType_defined DestBool_inv)

lemma DestBool_inv_typed: "\<lbrakk> x : BoolType; \<D> x \<rbrakk> \<Longrightarrow> MkBool (DestBool x) = x"
  by (metis BoolType_defined DestBool_inv)

end

end
