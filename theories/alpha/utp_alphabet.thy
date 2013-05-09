(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alphabet.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Alphabets *}

theory utp_alphabet
imports 
  "../core/utp_var" 
  "../core/utp_synonyms"
begin

subsection {* Operators *}

lift_definition in_alphabet ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHABET" ("in\<^sub>\<alpha>") is "in"
  by (simp add:in_vars_def fsets_def)

declare in_alphabet.rep_eq [simp]

lift_definition out_alphabet ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHABET" ("out\<^sub>\<alpha>") is "out"
  by (simp add:out_vars_def fsets_def)

declare out_alphabet.rep_eq [simp]

definition COMP_ALPHAS :: "'VALUE ALPHABET \<Rightarrow> 'VALUE ALPHABET \<Rightarrow> bool" where
"COMP_ALPHAS a1 a2 = COMPOSABLE \<langle>a1\<rangle>\<^sub>f \<langle>a2\<rangle>\<^sub>f"

definition HOM_ALPHA :: "'VALUE ALPHABET \<Rightarrow> bool" where
"HOM_ALPHA a = COMP_ALPHAS a a"

lemma HOM_ALPHA_HOMOGENEOUS:
  "HOM_ALPHA a \<longleftrightarrow> HOMOGENEOUS \<langle>a\<rangle>\<^sub>f"
  by (simp add:HOM_ALPHA_def HOMOGENEOUS_def COMP_ALPHAS_def COMPOSABLE_def)

lemma HOM_ALPHA_unfold:
  "HOM_ALPHA a \<longleftrightarrow> out\<^sub>\<alpha> a = dash `\<^sub>f in\<^sub>\<alpha> a"
  by (auto simp add:HOM_ALPHA_def COMP_ALPHAS_def COMPOSABLE_def)

subsection {* Restrictions *}

definition PROGRAM_ALPHABET :: "'VALUE ALPHABET set" where
"PROGRAM_ALPHABET \<equiv> {a. \<langle>a\<rangle>\<^sub>f \<subseteq> PROGRAM_VAR}"

subsection {* Proof Support *}

ML {*
  structure alphabet =
    Named_Thms (val name = @{binding alphabet} val description = "alphabet theorems")
*}

setup alphabet.setup

subsection {* Theorems *}

theorems alphabet_defs =
  in_alphabet_def
  out_alphabet_def

subsubsection {* Membership Theorems *}

theorem in_UNDASHED :
"\<langle>in\<^sub>\<alpha> a\<rangle>\<^sub>f \<subseteq> UNDASHED"
  by simp

theorem out_DASHED :
"\<langle>out\<^sub>\<alpha> a\<rangle>\<^sub>f \<subseteq> DASHED"
  by simp

theorem not_dash_member_in :
"\<not> dash x \<in>\<^sub>f in\<^sub>\<alpha> a"
  by (simp add: var_defs)

theorems alphabet_member =
  in_UNDASHED
  out_DASHED

subsubsection {* Simplification Theorems *}

theorem alphabet_simps:
  "\<langle>a\<rangle>\<^sub>f \<subseteq> DASHED \<Longrightarrow> in\<^sub>\<alpha> a = \<lbrace>\<rbrace>"
  "\<langle>a\<rangle>\<^sub>f \<subseteq> DASHED \<Longrightarrow> out\<^sub>\<alpha> a = a"
  "\<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<Longrightarrow> in\<^sub>\<alpha> a = a"
  "\<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<Longrightarrow> out\<^sub>\<alpha> a = \<lbrace>\<rbrace>"
  "in\<^sub>\<alpha> (in\<^sub>\<alpha> a) = in\<^sub>\<alpha> a" "out\<^sub>\<alpha> (out\<^sub>\<alpha> a) = out\<^sub>\<alpha> a"
  "in\<^sub>\<alpha> (out\<^sub>\<alpha> a) = \<lbrace>\<rbrace>" "out\<^sub>\<alpha> (in\<^sub>\<alpha> a) = \<lbrace>\<rbrace>"
  "in\<^sub>\<alpha> (dash `\<^sub>f vs) = \<lbrace>\<rbrace>"
  "in\<^sub>\<alpha> (undash `\<^sub>f out\<^sub>\<alpha> vs) = undash `\<^sub>f (out\<^sub>\<alpha> vs)"
  "out\<^sub>\<alpha> (dash `\<^sub>f vs) = dash `\<^sub>f (in\<^sub>\<alpha> vs)"
  "out\<^sub>\<alpha> (undash `\<^sub>f out\<^sub>\<alpha> a) = \<lbrace>\<rbrace>"
  "(in\<^sub>\<alpha> a1) \<inter>\<^sub>f (out\<^sub>\<alpha> a2) = \<lbrace>\<rbrace>"
  "\<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> (in\<^sub>\<alpha> a) \<union>\<^sub>f (out\<^sub>\<alpha> a) = a"
  "undash `\<^sub>f dash `\<^sub>f a = a"
  "dash `\<^sub>f undash `\<^sub>f out\<^sub>\<alpha> a = out\<^sub>\<alpha> a"
  by (auto, metis (lifting) equals0D in_undash out_in)

declare alphabet_simps [simp]

subsubsection {* Distribution Theorems *}

theorem in_alphabet_empty :
  "in\<^sub>\<alpha> \<lbrace>\<rbrace> = \<lbrace>\<rbrace>"
  by (force simp add:var_defs)

theorem in_alphabet_union :
"in\<^sub>\<alpha> (a1 \<union>\<^sub>f a2) = (in\<^sub>\<alpha> a1) \<union>\<^sub>f (in\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem in_alphabet_inter :
"in\<^sub>\<alpha> (a1 \<inter>\<^sub>f a2) = (in\<^sub>\<alpha> a1) \<inter>\<^sub>f (in\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem in_alphabet_diff :
"in\<^sub>\<alpha>(a1 -\<^sub>f a2) = (in\<^sub>\<alpha>a1) -\<^sub>f (in\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorem in_alphabet_finsert1 :
  "x \<in> UNDASHED \<Longrightarrow> in\<^sub>\<alpha> (finsert x xs) = finsert x (in\<^sub>\<alpha> xs)"
  by (force simp add: var_dist)

theorem in_alphabet_finsert2 :
  "x \<in> DASHED \<Longrightarrow> in\<^sub>\<alpha> (finsert x xs) = (in\<^sub>\<alpha> xs)"
  by (force simp add: var_dist)

theorem out_alphabet_empty :
  "out\<^sub>\<alpha> \<lbrace>\<rbrace> = \<lbrace>\<rbrace>"
  by (force simp add:var_defs)

theorem out_alphabet_union :
"out\<^sub>\<alpha>(a1 \<union>\<^sub>f a2) = (out\<^sub>\<alpha>a1) \<union>\<^sub>f (out\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorem out_alphabet_inter :
"out\<^sub>\<alpha>(a1 \<inter>\<^sub>f a2) = (out\<^sub>\<alpha>a1) \<inter>\<^sub>f (out\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorem out_alphabet_diff :
"out\<^sub>\<alpha>(a1 -\<^sub>f a2) = (out\<^sub>\<alpha>a1) -\<^sub>f (out\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorem out_alphabet_finsert1 :
  "x \<in> DASHED \<Longrightarrow> out\<^sub>\<alpha> (finsert x xs) = finsert x (out\<^sub>\<alpha> xs)"
  by (force simp add: var_dist)

theorem out_alphabet_finsert2 :
  "x \<in> UNDASHED \<Longrightarrow> out\<^sub>\<alpha> (finsert x xs) = out\<^sub>\<alpha> xs"
  by (force simp add: var_dist)

theorems alphabet_dist =
  in_alphabet_empty
  in_alphabet_union
  in_alphabet_inter
  in_alphabet_diff
  in_alphabet_finsert1
  in_alphabet_finsert2
  out_alphabet_empty
  out_alphabet_union
  out_alphabet_inter
  out_alphabet_diff
  out_alphabet_finsert1
  out_alphabet_finsert2

end

