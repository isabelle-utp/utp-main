(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_store.thy                                                        *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Typed Stores *}

theory utp_store
imports 
  "../core/utp_value"
  "../core/utp_sorts"
  "../core/utp_var"
  "../poly/utp_poly_var"
begin

default_sort VALUE

typedef 'm STORE = "{f :: ('m VAR, 'm) fmap. \<forall> x \<in>\<^sub>f fdom f. the (\<langle>f\<rangle>\<^sub>m x) : vtype x}"
  by (rule_tac x="fmempty" in exI, simp)

declare Rep_STORE [simp]
declare Rep_STORE_inverse [simp]
declare Abs_STORE_inverse [simp]

lemma Rep_STORE_intro [intro]:
  "Rep_STORE x = Rep_STORE y \<Longrightarrow> x = y"
  by (simp add:Rep_STORE_inject)

lemma Rep_STORE_type:
  "x \<in>\<^sub>f fdom (Rep_STORE s) \<Longrightarrow> the (\<langle>Rep_STORE s\<rangle>\<^sub>m x) : vtype x"
  by (metis (lifting, no_types) Rep_STORE mem_Collect_eq)

setup_lifting type_definition_STORE

term "\<langle>Rep_STORE s\<rangle>\<^sub>m (erase x)"

lift_definition st_empty :: "'m STORE" is fmempty
  by (simp)

definition st_lookup :: "'m STORE \<Rightarrow> ('a::DEFINED, 'm) PVAR \<Rightarrow> 'a option" where
"st_lookup s x = (\<langle>Rep_STORE s\<rangle>\<^sub>m (erase x) \<guillemotright>= Some \<circ> ProjU)"

lift_definition st_upd :: "('a::DEFINED, 'm) PVAR \<Rightarrow> 'a \<Rightarrow> 'm STORE \<Rightarrow> 'm STORE" is
"\<lambda> x v f. (if (TYPEUSOUND('a, 'm)) then fmap_upd f (erase x) (Some (InjU v)) else f)"
  by (case_tac "(TYPEUSOUND('a, 'm))", auto intro:typing)

lemma st_lookup_upd [simp]:
  fixes x :: "('a, 'm) PVAR"
  assumes "TYPEUSOUND('a, 'm)"
  shows "st_lookup (st_upd x v s) x = Some v"
  by (simp add:st_lookup_def st_upd.rep_eq assms)

class STORE_SORT = VALUE +
  fixes MkStore   :: "'a STORE \<Rightarrow> 'a"
  and   DestStore :: "'a \<Rightarrow> 'a STORE"
  and   StoreType :: "'a UTYPE"

  assumes Inverse [simp] : 
    "DestStore (MkStore v) = v"
  and     EventType_dcarrier: 
    "dcarrier StoreType = range MkStore"

instantiation STORE :: (VALUE) DEFINED_NE
begin

definition "Defined_STORE (x::'a STORE) = True"

instance
  by (intro_classes, auto simp add:Defined_STORE_def)
end

lemma Defined_STORE [defined]:
  "\<D> (x :: 'a STORE) = True"
  by (simp add:Defined_STORE_def)

defs (overloaded)
  InjU_store [inju]:  "InjU (x::('m::STORE_SORT) STORE) \<equiv> MkStore x"
  ProjU_store [inju]: "ProjU (x::('m::STORE_SORT)) \<equiv> DestStore x"
  TypeU_store [simp]: "TypeU (x::('m STORE) itself) \<equiv> StoreType"

lemma TypeUSound_store [typing]: "TYPEUSOUND('m STORE, 'm :: STORE_SORT)"
  apply (rule)
  apply (simp_all add:inju)
  apply (metis STORE_SORT_class.EventType_dcarrier dcarrier_type rangeI)
  apply (metis (full_types) STORE_SORT_class.EventType_dcarrier UNIV_I dcarrier_defined image_eqI)
  apply (metis Defined_STORE_def)
  apply (metis STORE_SORT_class.EventType_dcarrier STORE_SORT_class.Inverse dtype_as_dcarrier image_iff)
done

end