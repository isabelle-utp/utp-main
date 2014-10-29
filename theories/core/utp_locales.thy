(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_locales.thy                                                      *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 4 September 2014 *)

header {* Utility Locales *}

theory utp_locales
imports utp_model
begin

default_sort type

subsubsection {* Locale for Basic Sorts *}

text {* This locale facilitates the definition of basic UTP value sorts. *}

locale BASIC_SORT =
  fixes MkVal :: "'a \<Rightarrow> 'm::TYPED_MODEL uval"
  fixes DestVal :: "'m uval \<Rightarrow> 'a"
  fixes Domain :: "'a set"
  fixes Type :: "'m utype"
  assumes MkVal_defined : "\<D>\<^sub>v (MkVal x) \<longleftrightarrow> (x \<in> Domain)"
  assumes MkVal_typed : "x \<in> Domain \<Longrightarrow> (MkVal x) : Type"
  assumes MkVal_inverse : "x \<in> Domain \<Longrightarrow> DestVal (MkVal x) = x"
  assumes DestVal_inverse : "v :! Type \<Longrightarrow> MkVal (DestVal v) = v"
  assumes Domain_neq_empty : "Domain \<noteq> {}"
begin

subsubsection {* Constants *}

definition VALUE :: "'m uval set" where
"VALUE = dcarrier Type"

subsubsection {* Operators *}

definition IsVal :: "'m uval \<Rightarrow> bool" where
"IsVal v = (v : Type)"

subsubsection {* Theorems *}

theorem dcarrier_Type :
"(dcarrier Type) = MkVal ` Domain"
apply (rule Set.set_eqI)
apply (simp add: image_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (metis DestVal_inverse MkVal_defined strict_type_rel_def)
-- {* Subgoal 2 *}
apply (metis MkVal_typed)
-- {* Subgoal 3 *}
apply (metis MkVal_defined)
done

theorem DestVal_dcarrier :
"DestVal ` (dcarrier Type) = Domain"
apply (simp add: image_def)
apply (simp add: dcarrier_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (metis DestVal_inverse MkVal_defined strict_type_rel_def)
-- {* Subgoal 2 *}
apply (metis MkVal_defined MkVal_inverse MkVal_typed)
done

theorem in_image_MkVal :
"v :! Type \<Longrightarrow> v \<in> (MkVal ` Domain)"
apply (fold dcarrier_Type)
apply (simp add: dcarrier_def)
done

theorem inj_on_MkVal :
"inj_on MkVal Domain"
apply (rule inj_onI)
apply (metis MkVal_inverse)
done

theorem inj_on_DestVal :
"inj_on DestVal (dcarrier Type)"
apply (rule inj_onI)
apply (unfold dcarrier_member)
apply (metis DestVal_inverse)
done
end

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

subsubsection {* Locale for Paramatric Sorts *}

locale PARAM_SORT =
  fixes MkVal :: "'m::TYPED_MODEL utype \<Rightarrow> ('a \<Rightarrow> 'm uval)"
  fixes DestVal :: "'m uval \<Rightarrow> 'a"
  fixes Domain :: "'m utype \<Rightarrow>'a set"
  fixes MkType :: "'m utype \<Rightarrow> 'm utype"
  assumes MkVal_defined : "\<D>\<^sub>v (MkVal t x) \<longleftrightarrow> x \<in> Domain t"
  assumes MkVal_typed : "x \<in> Domain t \<Longrightarrow> (MkVal t x) : (MkType t)"
  assumes MkVal_inverse : "x \<in> Domain t \<Longrightarrow> DestVal (MkVal t x) = x"
  assumes DestVal_inverse : "v :! (MkType t) \<Longrightarrow> MkVal t (DestVal v) = v"
  assumes Domain_non_empty : "Domain t \<noteq> {}"
  assumes MkType_inj : "inj MkType"
begin

subsubsection {* Derived Operators *}

definition IsType :: "'m utype \<Rightarrow> bool" where
"IsType t = (\<exists> t' . t = MkType t')"

definition DestType :: "'m utype \<Rightarrow> 'm utype" where
"DestType t = (THE t' . t = MkType t')"

subsubsection {* Theorems *}

theorem MkVal_definedI :
"x \<in> Domain t \<Longrightarrow> \<D>\<^sub>v (MkVal t x)"
apply (metis MkVal_defined)
done

theorem MkVal_strictly_typed :
"x \<in> Domain t \<Longrightarrow> (MkVal t x) :! (MkType t)"
apply (unfold strict_type_rel_def)
apply (rule conjI)
apply (metis MkVal_typed)
apply (metis MkVal_defined)
done

theorem MkVal_witness :
"x :! MkType t \<Longrightarrow> \<exists> y . y \<in> Domain t \<and> x = MkVal t y"
apply (metis DestVal_inverse MkVal_defined strict_type_rel_def)
done

theorem MkVal_unique_witness :
"x :! MkType t \<Longrightarrow> \<exists>! y . y \<in> Domain t \<and> x = MkVal t y"
apply (safe)
apply (metis MkVal_witness strict_type_rel_def)
apply (rename_tac x y)
apply (metis MkVal_inverse)
done

theorem IsType_MkType :
"IsType (MkType t)"
apply (unfold IsType_def)
apply (auto)
done

theorem IsType_elim :
"IsType t \<Longrightarrow> (\<And> t' . t = MkType t' \<Longrightarrow> P) \<Longrightarrow> P"
apply (unfold IsType_def)
apply (auto)
done

theorem MkType_elim :
"x :! MkType t \<Longrightarrow> (\<And> y . \<lbrakk>x = MkVal t y; y \<in> Domain t\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
apply (metis MkVal_witness)
done

theorem MkType_inverse :
"DestType (MkType t) = t"
apply (unfold DestType_def)
apply (rule the_equality)
apply (clarify)
apply (metis MkType_inj injD)
done

theorem DestType_inverse :
"IsType t \<Longrightarrow> MkType (DestType t) = t"
apply (unfold IsType_def)
apply (metis MkType_inverse)
done
end
end
