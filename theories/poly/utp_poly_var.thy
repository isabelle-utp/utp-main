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

text {* A derivative of normal variables @{typ "'m VAR"} which also carry 
        their HOL type. They are not and cannot be a replacement
        because the HOL type-system does not allow sets of heterogeneous
        values, hence alphabets remain sets of deep variables. But whenever
        they can be used the advantage is that the HOL type-system can
        help the proof processes by discharging the type constraints.

        At first glance this type may seem odd as it refers to two
        type variables which are not used internally. This is because
        these are simply there to help the type-system and store no
        additional data. *}

typedef ('a, 'm :: VALUE) PVAR = "UNIV :: (NAME * bool) set"
  by auto

declare Rep_PVAR [simp]
declare Rep_PVAR_inverse [simp]
declare Abs_PVAR_inverse [simp]

definition MkPVAR :: 
  "NAME \<Rightarrow> bool \<Rightarrow> 'a itself \<Rightarrow> 'm itself \<Rightarrow> ('a, 'm :: VALUE) PVAR" where
"MkPVAR n s a t = Abs_PVAR (n, s)"

abbreviation MkPlainP ::
  "string \<Rightarrow> bool \<Rightarrow> 'a itself \<Rightarrow> 'm itself \<Rightarrow> ('a, 'm :: VALUE) PVAR" where
"MkPlainP n s a t \<equiv> MkPVAR (bName n) s a t"

abbreviation pvname :: "('a, 'm :: VALUE) PVAR \<Rightarrow> NAME" where
"pvname x \<equiv> fst (Rep_PVAR x)"

abbreviation pvaux :: "('a, 'm :: VALUE) PVAR \<Rightarrow> bool" where
"pvaux x \<equiv> snd (Rep_PVAR x)"

lemma pvname_MkPVAR [simp]:
  "pvname (MkPVAR n s a m) = n"
  by (simp add:MkPVAR_def)

lemma pvaux_MkPVAR [simp]:
  "pvaux (MkPVAR n s a m) = s"
  by (simp add:MkPVAR_def)

definition pvundash :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm :: VALUE) PVAR" where
"pvundash v = Abs_PVAR (MkName (name_str (pvname v)) (dashes (pvname v) - 1) (subscript (pvname v)), pvaux v)"

definition pvdash :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm :: VALUE) PVAR" where
"pvdash v = Abs_PVAR (MkName (name_str (pvname v)) (dashes (pvname v) + 1) (subscript (pvname v)), pvaux v)"

setup {*
Adhoc_Overloading.add_variant @{const_name prime} @{const_name pvdash}
*}

text {* Set up syntax for operators which perform type erasure *}

consts
  erase :: "'r \<Rightarrow> 'a" ("(_)\<down>" [1000] 1000)

setup {*
  Adhoc_Overloading.add_overloaded @{const_name erase}
*}

text {* This function performs a type erasure on the variable. *}

definition PVAR_VAR :: "('a, 'm) PVAR \<Rightarrow> ('m :: VALUE) VAR" where
"PVAR_VAR v = MkVar (pvname v) (TypeU TYPE('a)) (pvaux v)"

setup {*
Adhoc_Overloading.add_variant @{const_name erase} @{const_name PVAR_VAR}
*}

definition VAR_PVAR :: "('m :: VALUE) VAR \<Rightarrow> ('a, 'm) PVAR" where
"VAR_PVAR v = Abs_PVAR (name v, aux v)"

lemma PVAR_VAR_inv [simp]: 
  "VAR_PVAR v\<down> = v"
  by (simp add:PVAR_VAR_def VAR_PVAR_def)

lemma VAR_PVAR_inv [simp]: 
  "vtype x = TYPEU('a) \<Longrightarrow> (VAR_PVAR x :: ('a, 'm :: VALUE) PVAR)\<down> = x"
  apply (case_tac x)
  apply (auto simp add:PVAR_VAR_def VAR_PVAR_def MkVar_def)
done

lemma PVAR_VAR_pvundash [simp]:
  "(pvundash x)\<down> = undash x\<down>"
  by (auto simp add:PVAR_VAR_def undash_def pvundash_def)

lemma PVAR_VAR_pvdash [simp]:
  "(pvdash x)\<down> = dash x\<down>"
  by (auto simp add:PVAR_VAR_def dash_def pvdash_def)

lemma PVAR_VAR_MkPVAR:
  "(MkPVAR n s (a :: 'a itself) (m :: ('m::VALUE) itself))\<down> 
  = MkVar n (TYPEU('a)  :: 'm UTYPE) s"
  by (simp add:MkPVAR_def PVAR_VAR_def)

lemma MkPVAR_VAR_name [simp]:
  "name (MkPVAR n s a t)\<down> = n"
  by (simp add:PVAR_VAR_MkPVAR)

lemma MkPVAR_VAR_aux [simp]:
  "aux (MkPVAR n s a t)\<down> = s"
  by (simp add:PVAR_VAR_MkPVAR)

definition "PUNDASHED     \<equiv> {x. PVAR_VAR x \<in> UNDASHED}"
definition "PDASHED       \<equiv> {x. PVAR_VAR x \<in> DASHED}"
definition "PDASHED_TWICE \<equiv> {x. PVAR_VAR x \<in> DASHED_TWICE}"

lemma PVAR_VAR_PUNDASHED_UNDASHED [closure]:
  "x \<in> PUNDASHED \<Longrightarrow> x\<down> \<in> UNDASHED"
  by (simp add:PUNDASHED_def)

lemma PVAR_VAR_PDASHED_DASHED [closure]:
  "x \<in> PDASHED \<Longrightarrow> x\<down> \<in> DASHED"
  by (simp add:PDASHED_def)

lemma PVAR_VAR_PDASHED_DASHED_TWICE [closure]:
  "x \<in> PDASHED_TWICE \<Longrightarrow> x\<down> \<in> DASHED_TWICE"
  by (simp add:PDASHED_TWICE_def)

lemma MkPlainP_UNDASHED [closure]:
  "MkPlainP n a t m \<in> PUNDASHED"
  by (simp add: PVAR_VAR_MkPVAR PUNDASHED_def)

subsection {* Adapting Permutation *}

definition PermPV :: 
  "'m VAR_RENAME \<Rightarrow> ('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) PVAR" where
"PermPV ss x \<equiv> VAR_PVAR (\<langle>ss\<rangle>\<^sub>s x\<down>)"

notation PermPV ("\<langle>_\<rangle>\<^sub>s\<^sub>*")

setup {*
Adhoc_Overloading.add_variant @{const_name permute} @{const_name PermPV}
*}


lemma PVAR_VAR_vtype [simp]:
  "vtype (x :: ('a, 'm :: VALUE) PVAR)\<down> = TYPEU('a)"
  by (simp add:PVAR_VAR_def)

lemma PVAR_VAR_RENAME [simp]: 
  "(ss\<bullet>x)\<down> = ss\<bullet>(x\<down>)"
  by (simp add:PermPV_def)

end

