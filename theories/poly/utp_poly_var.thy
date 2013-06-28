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

text {* This function performs a type erasure on the variable. *}

definition PVAR_VAR :: "('a, 'm) PVAR \<Rightarrow> ('m :: VALUE) VAR" ("[_]\<^sub>*") where
"PVAR_VAR v = MkVar (pvname v) (TypeU TYPE('a)) (pvaux v)"

definition VAR_PVAR :: "('m :: VALUE) VAR \<Rightarrow> ('a, 'm) PVAR" where
"VAR_PVAR v = Abs_PVAR (name v, aux v)"

lemma PVAR_VAR_inv [simp]: 
  "VAR_PVAR [v]\<^sub>* = v"
  by (simp add:PVAR_VAR_def VAR_PVAR_def)

lemma VAR_PVAR_inv [simp]: 
  "vtype x = TYPEU('a) \<Longrightarrow> [VAR_PVAR x :: ('a, 'm :: VALUE) PVAR]\<^sub>* = x"
  apply (case_tac x)
  apply (auto simp add:PVAR_VAR_def VAR_PVAR_def MkVar_def)
done

lemma PVAR_VAR_pvundash [simp]:
  "[pvundash x]\<^sub>* = undash [x]\<^sub>*"
  by (auto simp add:PVAR_VAR_def undash_def pvundash_def)

lemma PVAR_VAR_pvdash [simp]:
  "[pvdash x]\<^sub>* = dash [x]\<^sub>*"
  by (auto simp add:PVAR_VAR_def dash_def pvdash_def)

term "MkVar"

lemma PVAR_VAR_MkPVAR:
  " [MkPVAR n s (a :: 'a itself) (m :: ('m::VALUE) itself)]\<^sub>* 
  = MkVar n (TYPEU('a)  :: 'm UTYPE) s"
  by (simp add:MkPVAR_def PVAR_VAR_def)

abbreviation "PUNDASHED     \<equiv> {x. PVAR_VAR x \<in> UNDASHED}"
abbreviation "PDASHED       \<equiv> {x. PVAR_VAR x \<in> DASHED}"
abbreviation "PDASHED_TWICE \<equiv> {x. PVAR_VAR x \<in> DASHED_TWICE}"

subsection {* Adapting Renaming *}

definition Rep_VAR_RENAME_poly :: 
  "'m VAR_RENAME \<Rightarrow> ('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) PVAR" where
"Rep_VAR_RENAME_poly ss x \<equiv> VAR_PVAR (\<langle>ss\<rangle>\<^sub>s [x]\<^sub>*)"

notation Rep_VAR_RENAME_poly ("\<langle>_\<rangle>\<^sub>s\<^sub>*")

lemma PVAR_VAR_vtype [simp]:
  "vtype [x :: ('a, 'm :: VALUE) PVAR]\<^sub>* = TYPEU('a)"
  by (simp add:PVAR_VAR_def)

lemma PVAR_VAR_RENAME [simp]: 
  "[\<langle>ss\<rangle>\<^sub>s\<^sub>* x]\<^sub>* = \<langle>ss\<rangle>\<^sub>s [x]\<^sub>*"
  by (simp add:Rep_VAR_RENAME_poly_def)

end

