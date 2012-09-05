(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alphabet.thy                                                     *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Alphabets *}

theory utp_alphabet
imports "../core/utp_var" "../core/utp_rel"
begin

type_synonym 'TYPE ALPHABET = "'TYPE VAR set"

context VAR
begin

text {* Alphabets are finite sets of variables. *}

definition WF_ALPHABET :: "('TYPE ALPHABET) set" where
"WF_ALPHABET = {vs . finite vs}"

subsection {* Operators *}

definition in_alphabet ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" ("in") where
"in a = a \<inter> UNDASHED"

definition out_alphabet ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" ("out") where
"out a = a \<inter> DASHED"

definition hom_alphabet ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" ("hom") where
"hom a = a \<union> (dash ` in a) \<union> (undash ` out a)"

subsection {* Restrictions *}

definition COMPOSABLE ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET \<Rightarrow> bool" where
"COMPOSABLE a1 a2 \<longleftrightarrow> (out a1) = dash ` (in a2)"

definition HOMOGENEOUS :: "'TYPE ALPHABET \<Rightarrow> bool" where
"HOMOGENEOUS a \<longleftrightarrow> COMPOSABLE a a"
end

subsection {* Proof Support *}

ML {*
  structure alphabet =
    Named_Thms (val name = @{binding alphabet} val description = "alphabet theorems")
*}

setup alphabet.setup

subsection {* Theorems *}

context VAR
begin

theorems alphabet_defs =
  COMPOSABLE_def
  HOMOGENEOUS_def
  in_alphabet_def
  out_alphabet_def
  hom_alphabet_def

subsubsection {* Closure Theorems *}

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

subsubsection {* Membership Theorems *}

theorem in_UNDASHED :
"in a \<subseteq> UNDASHED"
apply (simp add: in_alphabet_def)
done

theorem out_DASHED :
"out a \<subseteq> DASHED"
apply (simp add: out_alphabet_def)
done

theorem not_dash_member_in :
"\<not> dash x \<in> in a"
apply (simp add: in_alphabet_def)
apply (simp add: var_defs)
done

theorems alphabet_member =
  in_UNDASHED
  out_DASHED

subsubsection {* Simplification Theorems *}

theorem in_in :
"in (in a) = in a"
apply (simp add: in_alphabet_def)
apply (auto)
done

theorem out_out :
"out (out a) = out a"
apply (simp add: out_alphabet_def)
apply (auto)
done

theorem in_out :
"in (out a) = {}"
apply (simp add: in_alphabet_def out_alphabet_def)
apply (auto)
done

theorem out_in :
"out (in a) = {}"
apply (simp add: in_alphabet_def out_alphabet_def)
apply (auto)
done

lemma in_out_disj :
"(in a1) \<inter> (out a2) = {}"
apply (simp add: in_alphabet_def out_alphabet_def)
apply (auto)
done

theorem in_out_union [intro] :
"a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow>
 (in a) \<union> (out a) = a"
apply (simp add: in_alphabet_def out_alphabet_def)
apply (auto)
done

theorems alphabet_simps =
  in_in
  out_out
  in_out
  out_in
  in_out_disj
  in_out_union

subsubsection {* Distribution Theorems *}

theorem in_alphabet_union :
"in (a1 \<union> a2) = (in a1) \<union> (in a2)"
apply (simp add: in_alphabet_def)
apply (auto)
done

theorem in_alphabet_inter :
"in (a1 \<inter> a2) = (in a1) \<inter> (in a2)"
apply (simp add: in_alphabet_def)
apply (auto)
done

theorem in_alphabet_diff :
"in (a1 - a2) = (in a1) - (in a2)"
apply (simp add: in_alphabet_def)
apply (auto)
done

theorem out_alphabet_union :
"out (a1 \<union> a2) = (out a1) \<union> (out a2)"
apply (simp add: out_alphabet_def)
apply (auto)
done

theorem out_alphabet_inter :
"out (a1 \<inter> a2) = (out a1) \<inter> (out a2)"
apply (simp add: out_alphabet_def)
apply (auto)
done

theorem out_alphabet_diff :
"out (a1 - a2) = (out a1) - (out a2)"
apply (simp add: out_alphabet_def)
apply (auto)
done

theorems alphabet_dist =
  in_alphabet_union
  in_alphabet_inter
  in_alphabet_diff
  out_alphabet_union
  out_alphabet_inter
  out_alphabet_diff
end
end