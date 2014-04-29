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

lift_definition nrel_alpha :: 
  "'a ALPHABET \<Rightarrow> 
   'a ALPHABET" ("nrel\<^sub>\<alpha>") is nrel
  by (simp add: fsets_def nrel_vars_def)

declare nrel_alpha.rep_eq [simp]

definition dash_alpha :: "'a ALPHABET \<Rightarrow> 'a ALPHABET" where
"dash_alpha A = dash `\<^sub>f A"

adhoc_overloading
  prime dash_alpha

definition undash_alpha :: "'a ALPHABET \<Rightarrow> 'a ALPHABET" where
"undash_alpha A = dash `\<^sub>f A"

adhoc_overloading
  unprime undash_alpha

definition COMP_ALPHAS :: "'VALUE ALPHABET \<Rightarrow> 'VALUE ALPHABET \<Rightarrow> bool" where
"COMP_ALPHAS a1 a2 = COMPOSABLE \<langle>a1\<rangle>\<^sub>f \<langle>a2\<rangle>\<^sub>f"

definition REL_ALPHA :: "'a ALPHABET \<Rightarrow> bool" where
"REL_ALPHA a = (\<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED)"

definition COND_ALPHA :: "'a ALPHABET \<Rightarrow> bool" where
"COND_ALPHA a = (\<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED)"

definition POST_ALPHA :: "'a ALPHABET \<Rightarrow> bool" where
"POST_ALPHA a = (\<langle>a\<rangle>\<^sub>f \<subseteq> DASHED)"

definition HOM_ALPHA :: "'VALUE ALPHABET \<Rightarrow> bool" where
"HOM_ALPHA a = COMP_ALPHAS a a"

definition REL_ALPHABET :: "'VALUE ALPHABET set" where
"REL_ALPHABET = {a . \<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED}"

definition COND_ALPHABET :: "'VALUE ALPHABET set" where
"COND_ALPHABET = {a . \<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED}"

definition HOM_ALPHABET :: "'VALUE ALPHABET set" where
"HOM_ALPHABET = {a . HOM_ALPHA a}"

lift_definition homl_alpha ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHABET" ("homl\<^sub>\<alpha>") is "homl"
  by (simp add: fsets_def var_defs)

lift_definition homr_alpha ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHABET" ("homr\<^sub>\<alpha>") is "homr"
  by (simp add: fsets_def var_defs)

lemma HOM_ALPHA_HOMOGENEOUS:
  "HOM_ALPHA a \<longleftrightarrow> HOMOGENEOUS \<langle>a\<rangle>\<^sub>f"
  by (simp add:HOM_ALPHA_def HOMOGENEOUS_def COMP_ALPHAS_def COMPOSABLE_def)

lemma HOM_ALPHA_unfold:
  "HOM_ALPHA a \<longleftrightarrow> out\<^sub>\<alpha> a = dash `\<^sub>f in\<^sub>\<alpha> a"
  by (auto simp add:HOM_ALPHA_def COMP_ALPHAS_def COMPOSABLE_def)

lemma REL_ALPHABET_empty [closure]:
  "\<lbrace>\<rbrace> \<in> REL_ALPHABET"
  by (simp add: REL_ALPHABET_def)

lemma REL_ALPHABET_finsert_UNDASHED [closure]:
  "\<lbrakk> a \<in> REL_ALPHABET; x \<in> D\<^sub>0 \<rbrakk> \<Longrightarrow> finsert x a \<in> REL_ALPHABET"
  by (simp add: REL_ALPHABET_def)

lemma REL_ALPHABET_finsert_DASHED [closure]:
  "\<lbrakk> a \<in> REL_ALPHABET; x \<in> D\<^sub>1 \<rbrakk> \<Longrightarrow> finsert x a \<in> REL_ALPHABET"
  by (simp add: REL_ALPHABET_def)

lemma HOM_ALPHABET_empty [closure]:
  "\<lbrace>\<rbrace> \<in> HOM_ALPHABET"
  by (simp add: HOM_ALPHABET_def HOM_ALPHA_def COMP_ALPHAS_def COMPOSABLE_def)

lemma HOM_ALPHABET_insert [closure]:
  "\<lbrakk> a \<in> HOM_ALPHABET; x \<in> D\<^sub>0 \<rbrakk> \<Longrightarrow> (finsert x (finsert x\<acute> a)) \<in> HOM_ALPHABET"
  by (metis HOMOGENEOUS_insert HOM_ALPHABET_def HOM_ALPHA_HOMOGENEOUS finsert.rep_eq mem_Collect_eq)
  
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

lemma REL_ALPHABET_in_alpha [closure]: "in\<^sub>\<alpha>(a) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def var_defs)

lemma REL_ALPHABET_out_alpha [closure]: "out\<^sub>\<alpha>(a) \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def var_defs)

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

lemma NON_REL_VAR_nrel_member [simp]: 
  "x \<in> NON_REL_VAR \<Longrightarrow> x \<in> nrel vs \<longleftrightarrow> x \<in> vs"
  by (auto simp add:var_defs)

declare alphabet_simps [simp]

lemma alpha_dash_empty [simp]: "\<lbrace>\<rbrace>\<acute> = \<lbrace>\<rbrace>"
  by (metis dash_alpha_def fimage_fempty)

lemma alpha_dash_finsert [simp]: "(finsert x A)\<acute> = finsert x\<acute> A\<acute>"
  by (metis dash_alpha_def fimage_finsert)

lemma alpha_dash_union [simp]: "(A \<union>\<^sub>f B)\<acute> = (A\<acute> \<union>\<^sub>f B\<acute>)"
  by (metis dash_alpha_def fimage_funion)

lemma alpha_dash_inter [simp]: "(A \<inter>\<^sub>f B)\<acute> = (A\<acute> \<inter>\<^sub>f B\<acute>)"
  by (auto simp add:dash_alpha_def)

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
"in\<^sub>\<alpha>(a1 -\<^sub>f a2) = (in\<^sub>\<alpha>(a1)) -\<^sub>f (in\<^sub>\<alpha>(a2))"
  by (force simp add: var_dist)

theorem in_alphabet_finsert1 :
  "x \<in> UNDASHED \<Longrightarrow> in\<^sub>\<alpha> (finsert x xs) = finsert x (in\<^sub>\<alpha> xs)"
  by (force simp add: var_dist)

theorem in_alphabet_finsert2 :
  "x \<in> DASHED \<Longrightarrow> in\<^sub>\<alpha> (finsert x xs) = (in\<^sub>\<alpha> xs)"
  by (force simp add: var_dist)

theorem in_alphabet_finsert_NON_REL_VAR :
  "x \<in> NON_REL_VAR \<Longrightarrow> in\<^sub>\<alpha> (finsert x xs) = in\<^sub>\<alpha> xs"
  by (auto simp add: var_defs)

theorem out_alphabet_empty :
  "out\<^sub>\<alpha> \<lbrace>\<rbrace> = \<lbrace>\<rbrace>"
  by (force simp add:var_defs)

theorem out_alphabet_union :
"out\<^sub>\<alpha>(a1 \<union>\<^sub>f a2) = (out\<^sub>\<alpha> a1) \<union>\<^sub>f (out\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem out_alphabet_inter :
"out\<^sub>\<alpha>(a1 \<inter>\<^sub>f a2) = (out\<^sub>\<alpha> a1) \<inter>\<^sub>f (out\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem out_alphabet_diff :
"out\<^sub>\<alpha>(a1 -\<^sub>f a2) = (out\<^sub>\<alpha> a1) -\<^sub>f (out\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem out_alphabet_finsert1 :
  "x \<in> DASHED \<Longrightarrow> out\<^sub>\<alpha> (finsert x xs) = finsert x (out\<^sub>\<alpha> xs)"
  by (force simp add: var_dist)

theorem out_alphabet_finsert2 :
  "x \<in> UNDASHED \<Longrightarrow> out\<^sub>\<alpha> (finsert x xs) = out\<^sub>\<alpha> xs"
  by (force simp add: var_dist)

theorem out_alphabet_finsert_NON_REL_VAR :
  "x \<in> NON_REL_VAR \<Longrightarrow> out\<^sub>\<alpha> (finsert x xs) = out\<^sub>\<alpha> xs"
  by (auto simp add: var_defs)


theorem nrel_alphabet_empty :
  "nrel\<^sub>\<alpha> \<lbrace>\<rbrace> = \<lbrace>\<rbrace>"
  by (force simp add:var_defs)

theorem nrel_alphabet_union :
"nrel\<^sub>\<alpha>(a1 \<union>\<^sub>f a2) = (nrel\<^sub>\<alpha> a1) \<union>\<^sub>f (nrel\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem nrel_alphabet_inter :
"nrel\<^sub>\<alpha>(a1 \<inter>\<^sub>f a2) = (nrel\<^sub>\<alpha> a1) \<inter>\<^sub>f (nrel\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem nrel_alphabet_diff :
"nrel\<^sub>\<alpha>(a1 -\<^sub>f a2) = (nrel\<^sub>\<alpha> a1) -\<^sub>f (nrel\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem nrel_alphabet_finsert_NON_REL_VAR :
  "x \<in> NON_REL_VAR \<Longrightarrow> nrel\<^sub>\<alpha> (finsert x xs) = finsert x (nrel\<^sub>\<alpha> xs)"
  by (auto simp add: var_defs)

theorem nrel_alphabet_finsert_UNDASHED :
  "x \<in> UNDASHED \<Longrightarrow> nrel\<^sub>\<alpha> (finsert x xs) = (nrel\<^sub>\<alpha> xs)"
  by (auto simp add: var_defs)

theorem nrel_alphabet_finsert_DASHED :
  "x \<in> DASHED \<Longrightarrow> nrel\<^sub>\<alpha> (finsert x xs) = (nrel\<^sub>\<alpha> xs)"
  by (auto simp add: var_defs)

theorems alphabet_dist =
  in_alphabet_empty
  in_alphabet_union
  in_alphabet_inter
  in_alphabet_diff
  in_alphabet_finsert1
  in_alphabet_finsert2
  in_alphabet_finsert_NON_REL_VAR
  out_alphabet_empty
  out_alphabet_union
  out_alphabet_inter
  out_alphabet_diff
  out_alphabet_finsert1
  out_alphabet_finsert2
  out_alphabet_finsert_NON_REL_VAR
  nrel_alphabet_empty
  nrel_alphabet_union
  nrel_alphabet_inter
  nrel_alphabet_diff
  nrel_alphabet_finsert_NON_REL_VAR
  nrel_alphabet_finsert_UNDASHED
  nrel_alphabet_finsert_DASHED

lemma alphabet_split:
  "in\<^sub>\<alpha> a \<union>\<^sub>f (out\<^sub>\<alpha> a \<union>\<^sub>f nrel\<^sub>\<alpha> a) = a"
  by (auto simp add:var_defs)

end

