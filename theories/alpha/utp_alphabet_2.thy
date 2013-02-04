(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alphabet.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Alphabets *}

theory utp_alphabet_2
imports "../core/utp_var_2" "../core/utp_synonyms"
begin

(*
text {* Alphabets are finite sets of variables. *}

definition WF_ALPHABET :: "(('VALUE, 'VALUE UTYPE) ALPHABET) set" where
"WF_ALPHABET = {vs . finite vs}"

typedef (open) 'VALUE WF_ALPHABET = "WF_ALPHABET :: ('VALUE ALPHABET) set"
  by (auto simp add:WF_ALPHABET_def)

setup_lifting type_definition_WF_ALPHABET
*)

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

definition hom_alphabet ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE ALPHABET" ("hom") where
"hom a = a \<union>\<^sub>f (dash `\<^sub>f in\<^sub>\<alpha> a) \<union>\<^sub>f (undash `\<^sub>f out\<^sub>\<alpha> a)"

subsection {* Restrictions *}

(*
definition COMPOSABLE ::
  "'VALUE UTYPE ALPHABET \<Rightarrow>
   'VALUE UTYPE ALPHABET \<Rightarrow> bool" where
"COMPOSABLE a1 a2 \<longleftrightarrow> (out\<^sub>\<alpha> a1) = dash `\<^sub>f (in\<^sub>\<alpha> a2)"

definition HOMOGENEOUS :: "'VALUE UTYPE ALPHABET \<Rightarrow> bool" where
"HOMOGENEOUS a \<longleftrightarrow> COMPOSABLE a a"
*)

definition PROGRAM_ALPHABET :: "'VALUE ALPHABET \<Rightarrow> bool" where
"PROGRAM_ALPHABET a \<equiv> \<langle>a\<rangle>\<^sub>f \<subseteq> PROGRAM_VARS"

subsection {* Proof Support *}

ML {*
  structure alphabet =
    Named_Thms (val name = @{binding alphabet} val description = "alphabet theorems")
*}

setup alphabet.setup

subsection {* Theorems *}

theorems alphabet_defs =
(*  COMPOSABLE_def
  HOMOGENEOUS_def *)
  in_alphabet_def
  out_alphabet_def
  hom_alphabet_def

subsubsection {* Closure Theorems *}

(*
theorem WF_ALPHABET_empty [closure] :
"{} \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_insert [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 (insert x a) \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_union [closure] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<union> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_inter [closure] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<inter> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_diff [closure] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 - a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_subset [intro]:
"\<lbrakk>a1 \<in> WF_ALPHABET; a2 \<subseteq> a1\<rbrakk> \<Longrightarrow>
 a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
apply (simp add: finite_subset)
done

theorem WF_ALPHABET_image [closure] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 f ` a \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_in [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 in a \<in> WF_ALPHABET"
apply (simp add: in_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_out [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 out a \<in> WF_ALPHABET"
apply (simp add: out_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_hom [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 hom a \<in> WF_ALPHABET"
apply (simp add: hom_alphabet_def)
apply (simp add: closure)
done
*)

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
  "in\<^sub>\<alpha> (in\<^sub>\<alpha> a) = in\<^sub>\<alpha> a" "out\<^sub>\<alpha> (out\<^sub>\<alpha> a) = out\<^sub>\<alpha> a"
  "in\<^sub>\<alpha> (out\<^sub>\<alpha> a) = {}\<^sub>f" "out\<^sub>\<alpha> (in\<^sub>\<alpha> a) = {}\<^sub>f"
  "in\<^sub>\<alpha> (dash `\<^sub>f vs) = {}\<^sub>f"
  "in\<^sub>\<alpha> (undash `\<^sub>f out\<^sub>\<alpha> vs) = undash `\<^sub>f (out\<^sub>\<alpha> vs)"
  "out\<^sub>\<alpha> (dash `\<^sub>f vs) = dash `\<^sub>f (in\<^sub>\<alpha> vs)"
  "(in\<^sub>\<alpha> a1) \<inter>\<^sub>f (out\<^sub>\<alpha> a2) = {}\<^sub>f"
  "\<langle>a\<rangle>\<^sub>f \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> (in\<^sub>\<alpha> a) \<union>\<^sub>f (out\<^sub>\<alpha> a) = a"
  by (auto)

declare alphabet_simps [simp]

subsubsection {* Distribution Theorems *}

theorem in_alphabet_union :
"in\<^sub>\<alpha> (a1 \<union>\<^sub>f a2) = (in\<^sub>\<alpha> a1) \<union>\<^sub>f (in\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem in_alphabet_inter :
"in\<^sub>\<alpha> (a1 \<inter>\<^sub>f a2) = (in\<^sub>\<alpha> a1) \<inter>\<^sub>f (in\<^sub>\<alpha> a2)"
  by (force simp add: var_dist)

theorem in_alphabet_diff :
"in\<^sub>\<alpha>(a1 -\<^sub>f a2) = (in\<^sub>\<alpha>a1) -\<^sub>f (in\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorem out_alphabet_union :
"out\<^sub>\<alpha>(a1 \<union>\<^sub>f a2) = (out\<^sub>\<alpha>a1) \<union>\<^sub>f (out\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorem out_alphabet_inter :
"out\<^sub>\<alpha>(a1 \<inter>\<^sub>f a2) = (out\<^sub>\<alpha>a1) \<inter>\<^sub>f (out\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorem out_alphabet_diff :
"out\<^sub>\<alpha>(a1 -\<^sub>f a2) = (out\<^sub>\<alpha>a1) -\<^sub>f (out\<^sub>\<alpha>a2)"
  by (force simp add: var_dist)

theorems alphabet_dist =
  in_alphabet_union
  in_alphabet_inter
  in_alphabet_diff
  out_alphabet_union
  out_alphabet_inter
  out_alphabet_diff

end