(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_var.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Shallowly Embedded Polymorphic Variables *}

theory utp_poly_var
imports 
  "../core/utp_var"
  "../core/utp_rename"
  utp_poly_value
begin

default_sort type

subsection {* Polymorphic type variables *}

text {* A derivative of normal variables @{typ "'m uvar"} which also carry 
        their HOL type. They are not and cannot be a replacement
        because the HOL type-system does not allow sets of heterogeneous
        values, hence alphabets remain sets of deep variables. But whenever
        they can be used the advantage is that the HOL type-system can
        help the proof processes by discharging the type constraints.

        At first glance this type may seem odd as it refers to two
        type variables which are not used internally. This is because
        these are simply there to help the type-system and store no
        additional data. *}

typedef ('a, 'm::PRE_TYPED_MODEL) pvar = "UNIV :: (uname * bool) set"
  by auto

declare Rep_pvar [simp]
declare Rep_pvar_inverse [simp]
declare Abs_pvar_inverse [simp]

definition MkPVAR :: 
  "uname \<Rightarrow> bool \<Rightarrow> 'a itself \<Rightarrow> 'm itself \<Rightarrow> ('a, 'm::PRE_TYPED_MODEL) pvar" where
"MkPVAR n s a t = Abs_pvar (n, s)"

abbreviation MkPlainP ::
  "string \<Rightarrow> bool \<Rightarrow> 'a itself \<Rightarrow> 'm itself \<Rightarrow> ('a, 'm::PRE_TYPED_MODEL) pvar" where
"MkPlainP n s a t \<equiv> MkPVAR (bName n) s a t"

text {* Some default variables constructors *}

abbreviation "MkBoolV n a \<equiv> MkPlainP n a TYPE(bool) TYPE('m :: BOOL_SORT)"

abbreviation "MkIntV n a \<equiv> MkPlainP n a TYPE(int) TYPE('m :: INT_SORT)"

abbreviation "MkRealV n a \<equiv> MkPlainP n a TYPE(real) TYPE('m :: REAL_SORT)"

abbreviation pvname :: "('a, 'm::PRE_TYPED_MODEL) pvar \<Rightarrow> uname" where
"pvname x \<equiv> fst (Rep_pvar x)"

abbreviation pvaux :: "('a, 'm::PRE_TYPED_MODEL) pvar \<Rightarrow> bool" where
"pvaux x \<equiv> snd (Rep_pvar x)"

lemma pvname_MkPVAR [simp]:
  "pvname (MkPVAR n s a m) = n"
  by (simp add:MkPVAR_def)

lemma pvaux_MkPVAR [simp]:
  "pvaux (MkPVAR n s a m) = s"
  by (simp add:MkPVAR_def)

definition pvundash ::
  "('a, 'm::PRE_TYPED_MODEL) pvar \<Rightarrow> ('a, 'm::PRE_TYPED_MODEL) pvar" where
"pvundash v = Abs_pvar (MkName (name_str (pvname v)) (dashes (pvname v) - 1)
  (subscript (pvname v)), pvaux v)"

definition pvdash ::
    "('a, 'm::PRE_TYPED_MODEL) pvar \<Rightarrow> ('a, 'm::PRE_TYPED_MODEL) pvar" where
"pvdash v = Abs_pvar (MkName (name_str (pvname v)) (dashes (pvname v) + 1)
  (subscript (pvname v)), pvaux v)"

definition pvchsub ::
  "('a, 'm::PRE_TYPED_MODEL) pvar \<Rightarrow> string \<Rightarrow> ('a, 'm) pvar" where
"pvchsub v s = Abs_pvar (chsub s (pvname v), pvaux v)"

adhoc_overloading
  prime pvdash

adhoc_overloading
  unprime pvundash

adhoc_overloading
  subscr pvchsub

text {* Set up syntax for operators which perform type erasure *}

consts
  erase :: "'r \<Rightarrow> 'a" ("(_)\<down>" [1000] 1000)

text {* This function performs a type erasure on the variable. *}

definition PVAR_VAR :: "('a, 'm) pvar \<Rightarrow> ('m :: PRE_TYPED_MODEL) uvar" where
"PVAR_VAR v = MkVar (pvname v) (TypeU TYPE('a)) (pvaux v)"

adhoc_overloading
  erase PVAR_VAR

definition VAR_PVAR :: "('m :: PRE_TYPED_MODEL) uvar \<Rightarrow> ('a, 'm) pvar" where
"VAR_PVAR v = Abs_pvar (name v, aux v)"

lemma PVAR_VAR_inv [simp]: 
  "VAR_PVAR v\<down> = v"
  by (simp add:PVAR_VAR_def VAR_PVAR_def)

lemma PVAR_VAR_inj [dest]:
  fixes x y :: "('a :: DEFINED, 'm :: PRE_TYPED_MODEL) pvar"
  assumes "x\<down> = y\<down>"
  shows "x = y"
   by (metis PVAR_VAR_inv assms)

lemma VAR_PVAR_inv [erasure]: 
  "vtype x = TYPEU('a) \<Longrightarrow> (VAR_PVAR x :: ('a, 'm :: PRE_TYPED_MODEL) pvar)\<down> = x"
  apply (case_tac x)
  apply (auto simp add:PVAR_VAR_def VAR_PVAR_def MkVar_def)
done

lemma PVAR_VAR_pvundash [simp]:
  "(pvundash x)\<down> = undash x\<down>"
  by (auto simp add:PVAR_VAR_def undash_def pvundash_def)

lemma PVAR_VAR_pvdash [simp]:
  "(pvdash x)\<down> = dash x\<down>"
  by (auto simp add:PVAR_VAR_def dash_def pvdash_def)

lemma PVAR_VAR_pvchsub [simp]:
  "(pvchsub x n)\<down> = vchsub (x\<down>) n"
  apply (case_tac x, case_tac y, case_tac a)
  apply (simp add: PVAR_VAR_def pvchsub_def MkVar_def vchsub_def)
done

lemma PVAR_VAR_MkPVAR:
  "(MkPVAR n s (a :: 'a itself) (m :: ('m::PRE_TYPED_MODEL) itself))\<down> 
  = MkVar n (TYPEU('a)  :: 'm utype) s"
  by (simp add:MkPVAR_def PVAR_VAR_def)

lemma VAR_PVAR_erase_simps [simp]:
  "VAR_PVAR (x\<down>) = x"
  "VAR_PVAR (x\<down>)\<acute> = x\<acute>"
  "VAR_PVAR (x\<down>)\<acute>\<acute> = x\<acute>\<acute>"
  "VAR_PVAR (x\<down>)\<acute>\<acute>\<acute> = x\<acute>\<acute>\<acute>"
  apply (metis PVAR_VAR_inv)
  apply (metis PVAR_VAR_inv PVAR_VAR_pvdash)
  apply (metis PVAR_VAR_inv PVAR_VAR_pvdash)
  by (metis PVAR_VAR_inv PVAR_VAR_pvdash)

lemma MkPVAR_VAR_name [simp]:
  "name (MkPVAR n s a t)\<down> = n"
  by (simp add:PVAR_VAR_MkPVAR)

lemma MkPVAR_VAR_aux [simp]:
  "aux (MkPVAR n s a t)\<down> = s"
  by (simp add:PVAR_VAR_MkPVAR)

lemma pvaux_aux:
  "pvaux x = aux x\<down>"
  apply (case_tac x)
  apply (simp add:PVAR_VAR_def)
done

lemma pvname_name:
  "pvname x = name x\<down>"
  apply (case_tac x)
  apply (simp add:PVAR_VAR_def)
done

lemma pvaux_pvdash [simp]: 
  "pvaux (x\<acute>) = pvaux x"
  by (simp add:pvdash_def)

lemma pvaux_pvundash [simp]: 
  "pvaux (pvundash x) = pvaux x"
  by (simp add:pvundash_def)

lemma pvaux_sub [simp]:
  "pvaux (x\<^bsub>n\<^esub>) = pvaux x"
  by (simp add:pvchsub_def)

definition "PUNDASHED     \<equiv> {x. PVAR_VAR x \<in> UNDASHED}"
definition "PDASHED       \<equiv> {x. PVAR_VAR x \<in> DASHED}"
definition "PDASHED_TWICE \<equiv> {x. PVAR_VAR x \<in> DASHED_TWICE}"
definition "PNOSUB        = {x. PVAR_VAR x \<in> NOSUB}"
definition "PWITHSUB n    = {x. PVAR_VAR x \<in> WITHSUB n}"

lemma PVAR_VAR_PUNDASHED_UNDASHED [closure]:
  "x \<in> PUNDASHED \<Longrightarrow> x\<down> \<in> UNDASHED"
  by (simp add:PUNDASHED_def)

lemma PVAR_VAR_PDASHED_DASHED [closure]:
  "x \<in> PDASHED \<Longrightarrow> x\<down> \<in> DASHED"
  by (simp add:PDASHED_def)

lemma PVAR_VAR_PDASHED_DASHED_TWICE [closure]:
  "x \<in> PDASHED_TWICE \<Longrightarrow> x\<down> \<in> DASHED_TWICE"
  by (simp add:PDASHED_TWICE_def)

lemma PVAR_VAR_PNOSUB_NOSUB [closure]:
  "x \<in> PNOSUB \<Longrightarrow> x\<down> \<in> NOSUB"
  by (simp add: PNOSUB_def)

lemma PVAR_VAR_PSUB_SUB [closure]:
  "x \<in> PWITHSUB(n) \<Longrightarrow> x\<down> \<in> WITHSUB(n)"
  by (simp add: PWITHSUB_def)

lemma PUNDASHED_dash [closure]:
  "x \<in> PUNDASHED \<Longrightarrow> x\<acute> \<in> PDASHED"
  by (simp add:PDASHED_def PUNDASHED_def)

lemma PDASHED_dash [closure]:
  "x \<in> PDASHED \<Longrightarrow> x\<acute> \<in> PDASHED_TWICE"
  by (simp add:PDASHED_def PDASHED_TWICE_def)

lemma MkPlainP_UNDASHED [closure]:
  "MkPlainP n a t m \<in> PUNDASHED"
  by (simp add: PVAR_VAR_MkPVAR PUNDASHED_def)

lemma MkPlainP_NOSUB [closure]:
  "MkPlainP n a t m \<in> PNOSUB"
  by (simp add: PVAR_VAR_MkPVAR PNOSUB_def)

lemma pvdash_pvundash [simp]:
  "pvundash (pvdash x) = x"
  by (metis PVAR_VAR_inv PVAR_VAR_pvdash PVAR_VAR_pvundash undash_dash)

lemma pvundash_pvdash_PDASHED [simp]:
  "x \<in> PDASHED \<Longrightarrow> pvdash (pvundash x) = x"
  by (metis DASHED_dash_elim PVAR_VAR_PDASHED_DASHED PVAR_VAR_pvundash VAR_PVAR_erase_simps undash_dash)

subsection {* Adapting Permutation *}

definition PermPV :: 
  "'m VAR_RENAME \<Rightarrow> ('a, 'm :: TYPED_MODEL) pvar \<Rightarrow> ('a, 'm) pvar" where
"PermPV ss x \<equiv> VAR_PVAR (\<langle>ss\<rangle>\<^sub>s x\<down>)"

notation PermPV ("\<langle>_\<rangle>\<^sub>s\<^sub>*")

adhoc_overloading
  permute PermPV

lemma PVAR_VAR_vtype [simp]:
  "vtype (x :: ('a, 'm :: PRE_TYPED_MODEL) pvar)\<down> = TYPEU('a)"
  by (metis MkVar_vtype PVAR_VAR_def)

lemma PVAR_VAR_RENAME [simp]: 
  "(ss\<bullet>x)\<down> = ss\<bullet>(x\<down>)"
  by (simp add:PermPV_def erasure)

lemma PermPV_PVAR:
  "ss\<bullet>x = VAR_PVAR (ss\<bullet>(x\<down>))"
  by (metis PermPV_def)

text {* A list produced from a polymorphic auxiliary variable is within the carrier of
        the list elements *}

(* The TYPEUSOUND('a, 'm) assumption seems not necessary below? *)

lemma PVAR_list_aux [typing]:
  fixes x :: "('a::DEFINED ULIST, 'm::LIST_SORT) pvar"
  assumes (* "TYPEUSOUND('a, 'm)" *) "aux (x\<down>)" "t = TYPEU('a)"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b x\<down>)) \<subseteq> dcarrier t"
  by (metis DestList_subset_dcarrier PVAR_VAR_vtype TypeU_ULIST assms binding_stype)

lemma PVAR_dash_list_aux [typing]:
  fixes x :: "('a::DEFINED ULIST, 'm::LIST_SORT) pvar"
  assumes (* "TYPEUSOUND('a, 'm)" *) "aux (x\<down>)" "t = TYPEU('a)"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b (x\<down>\<acute>))) \<subseteq> dcarrier t"
  by (metis PVAR_VAR_pvdash PVAR_list_aux assms(1) assms(2) aux_dash)

lemma PVAR_binding_type [typing] :
  fixes x :: "('a :: DEFINED, 'm :: TYPED_MODEL) pvar"
  assumes "t = TYPEU('a)"
  shows "\<langle>b\<rangle>\<^sub>b x\<down> : t"
  by (simp add: assms typing)

lemma PVAR_binding_defined_aux [defined]:
  fixes x :: "('a :: DEFINED, 'm :: TYPED_MODEL) pvar"
  assumes "pvaux x"
  shows "\<D> (\<langle>b\<rangle>\<^sub>b x\<down>)"
  by (metis (full_types) assms aux_defined defined_uval_def pvaux_aux)

(*
lemma PVAR_binding_aux_stype [typing]:
  fixes x :: "('a::DEFINED, 'm::REACTIVE_SORT) pvar"
  assumes "pvaux x" "t = TYPEU('a)"
  shows "\<langle>b\<rangle>\<^sub>b x\<down> :! t"
    by (metis PVAR_binding_defined_aux PVAR_binding_type assms dtype_rel_def)
*)

(* NOTE (Frank): Looks like we do not need 'm::REACTIVE_SORT. *)

lemma PVAR_binding_aux_stype [typing]:
  fixes x :: "('a::DEFINED, 'm::TYPED_MODEL) pvar"
  assumes "pvaux x" "t = TYPEU('a)"
  shows "\<langle>b\<rangle>\<^sub>b x\<down> :! t"
    by (metis PVAR_VAR_vtype assms(1) assms(2) binding_stype pvaux_aux)

lemma TypeUSound_InjU_var_compat [typing] :
  fixes x :: "('a::DEFINED, 'm::TYPED_MODEL) pvar"
  and   y :: "'a"
  assumes "TYPEUSOUND('a, 'm)" "\<D> y"
  shows "(InjU y :: 'm uval) \<rhd> x\<down>"
apply (simp add: var_compat_def)
apply (metis UTypedef.InjU_defined UTypedef.axm1 assms(1) assms(2))
done

(* Compatibility *)

definition pvar_compat :: 
  "'a \<Rightarrow> ('a :: DEFINED, 'm :: PRE_TYPED_MODEL) pvar \<Rightarrow> bool" (infix "\<rhd>\<^sub>p" 50) where
"pvar_compat v x \<equiv> (if (pvaux x) then \<D> v else True) \<and> TYPEUSOUND('a,'m)"

lemma npvaux_pvar_compat [typing]:
  fixes x :: "('a :: DEFINED, 'm :: PRE_TYPED_MODEL) pvar"
  assumes "TYPEUSOUND('a,'m)" "\<not> pvaux x"
  shows "v \<rhd>\<^sub>p x"
  by (simp add:pvar_compat_def assms)

lemma pvaux_pvar_compat [typing]:
  fixes x :: "('a :: DEFINED, 'm :: PRE_TYPED_MODEL) pvar"
  assumes "TYPEUSOUND('a,'m)" "\<D> v"
  shows "v \<rhd>\<^sub>p x"
  by (simp add:pvar_compat_def assms)

lemma var_compat_pvar [typing]:
  fixes x :: "('a :: DEFINED, 'm :: TYPED_MODEL) pvar"
  and   v :: "'a"
  assumes "v \<rhd>\<^sub>p x"
  shows "InjU v \<rhd> x\<down>"
  using assms
apply (simp add: var_compat_def typing pvar_compat_def UTypedef.InjU_defined pvaux_aux)
apply (metis UTypedef.axm1)
done

lemma RenamePV_aux [simp]:
  "pvaux (ss\<bullet>x) = pvaux x"
  by (metis PVAR_VAR_RENAME Rep_VAR_RENAME_aux pvaux_aux)
end
