(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_var.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Variables *}

theory utp_var
imports utp_synonyms utp_names
begin

definition VAR :: "'TYPE VAR set" where
"VAR = UNIV"

abbreviation var_name :: "'TYPE VAR \<Rightarrow> NAME" ("name") where
"var_name \<equiv> fst"

abbreviation var_type :: "'TYPE VAR \<Rightarrow> 'TYPE" ("type") where
"var_type \<equiv> snd"

subsection {* Locale @{term "VAR"} *}

locale VAR =
-- {* The type universe is fixed to determine @{typ "'TYPE"}. *}
  fixes type_univ :: "'TYPE set"
begin

subsection {* Constructors *}

definition MkVar :: "NAME \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE VAR" where
"MkVar n t = (n, t)"

definition MkPlain :: "string \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE VAR" where
"MkPlain s t =
 MkVar \<lparr>name_str = s, dashes = 0, subscript = NoSub\<rparr> t"

subsection {* Operators *}

definition dash :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"dash v =
 (\<lparr>name_str = name_str (name v),
 dashes = dashes (name v) + 1,
 subscript = subscript (name v)\<rparr>, type v)"

definition undash :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"undash v =
 (\<lparr>name_str = name_str (name v),
 dashes = dashes (name v) - 1,
 subscript = subscript (name v)\<rparr>, type v)"

subsection {* Restrictions *}

definition UNDASHED :: "'TYPE VAR set" where
"UNDASHED = {v . dashes (name v) = 0}"

definition DASHED :: "'TYPE VAR set" where
"DASHED = {v . dashes (name v) = 1}"

definition DASHED_TWICE :: "'TYPE VAR set" where
"DASHED_TWICE = {v . dashes (name v) = 2}"

definition PLAIN :: "'TYPE VAR set" where
"PLAIN = {v . v \<in> UNDASHED \<and> subscript (name v) = NoSub}"

subsection {* Theorems *}

theorems var_defs =
  VAR_def
  UNDASHED_def
  DASHED_def
  DASHED_TWICE_def
  PLAIN_def
  undash_def
  dash_def

theorem VAR_member [simp] :
"x \<in> VAR"
apply (simp add: VAR_def)
done

subsubsection {* Names and Types *}

theorem type_dash [simp] :
"type (dash x) = type x"
apply (simp add: var_defs)
done

theorem type_undash [simp] :
"type (undash x) = type x"
apply (simp add: var_defs)
done

subsubsection {* Membership Theorems *}

theorem UNDASHED_not_DASHED :
"x \<in> UNDASHED \<Longrightarrow> \<not> x \<in> DASHED"
apply (simp add: var_defs)
done

theorem UNDASHED_not_DASHED_TWICE :
"x \<in> UNDASHED \<Longrightarrow> \<not> x \<in> DASHED_TWICE"
apply (simp add: var_defs)
done

theorem DASHED_not_DASHED_TWICE :
"x \<in> DASHED \<Longrightarrow> \<not> x \<in> DASHED_TWICE"
apply (simp add: var_defs)
done

theorem UNDASHED_dash_DASHED :
"x \<in> UNDASHED \<Longrightarrow> dash x \<in> DASHED"
apply (simp add: var_defs)
done

theorem DASHED_undash_UNDASHED :
"x \<in> DASHED \<Longrightarrow> undash x \<in> UNDASHED"
apply (simp add: var_defs)
done

theorem DASHED_dash_DASHED_TWICE :
"x \<in> DASHED \<Longrightarrow> dash x \<in> DASHED_TWICE"
apply (simp add: var_defs)
done

theorem DASHED_TWICE_undash_DASHED :
"x \<in> DASHED_TWICE \<Longrightarrow> undash x \<in> DASHED"
apply (simp add: var_defs)
done

theorems var_member =
  UNDASHED_not_DASHED
  UNDASHED_not_DASHED_TWICE
  DASHED_not_DASHED_TWICE
  UNDASHED_dash_DASHED
  DASHED_undash_UNDASHED
  DASHED_dash_DASHED_TWICE
  DASHED_TWICE_undash_DASHED

declare var_member [intro, simp]

subsubsection {* Contradiction Theorems *}

theorem UNDASHED_DASHED_contra :
"\<lbrakk>x \<in> UNDASHED; x \<in> DASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem UNDASHED_DASHED_TWICE_contra :
"\<lbrakk>x \<in> UNDASHED; x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem DASHED_DASHED_TWICE_contra :
"\<lbrakk>x \<in> DASHED; x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem UNDASHED_eq_dash_contra :
"\<lbrakk>x = dash y; x \<in> UNDASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem undash_eq_dash_contra1 :
"\<lbrakk>undash x = dash y; x \<in> DASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem undash_eq_dash_contra2 :
"\<lbrakk>undash x = dash y; x \<in> DASHED_TWICE; y \<in> DASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem dash_eq_undash_contra1 :
"\<lbrakk>dash x = undash y; y \<in> DASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem dash_eq_undash_contra2 :
"\<lbrakk>dash x = undash y; x \<in> DASHED; y \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorems var_contra =
  UNDASHED_DASHED_contra
  UNDASHED_DASHED_TWICE_contra
  DASHED_DASHED_TWICE_contra
  UNDASHED_eq_dash_contra
  undash_eq_dash_contra1
  undash_eq_dash_contra2
  dash_eq_undash_contra1
  dash_eq_undash_contra2

declare var_contra [dest]

subsubsection {* Simplification Theorems *}

theorem dash_undash_DASHED :
"x \<in> DASHED \<Longrightarrow> dash (undash x) = x"
apply (simp add: var_defs)
apply (atomize (full))
apply (induct_tac x)
apply (auto)
done

theorem dash_undash_DASHED_TWICE :
"x \<in> DASHED_TWICE \<Longrightarrow> dash (undash x) = x"
apply (simp add: var_defs)
apply (atomize (full))
apply (induct_tac x)
apply (auto)
done

theorem undash_dash :
"undash (dash x) = x"
apply (simp add: var_defs)
apply (induct_tac x)
apply (simp)
done

lemma dash_UNDASHED_image: 
"dash ` UNDASHED = DASHED"
  by (auto simp add:image_def, metis DASHED_undash_UNDASHED dash_undash_DASHED)

lemma undash_DASHED_image: 
"undash ` DASHED = UNDASHED"
  by (auto simp add:image_def, metis UNDASHED_dash_DASHED undash_dash)

lemma dash_undash_image:
"vs \<subseteq> DASHED \<Longrightarrow> dash ` undash ` vs = vs"
  by (auto simp add:image_def dash_undash_DASHED, metis dash_undash_DASHED set_mp)

lemma undash_dash_image: 
"undash ` dash ` vs = vs"
  by (auto simp add: image_def undash_dash)

theorems var_simps =
  dash_undash_DASHED
  dash_undash_DASHED_TWICE
  undash_dash
  dash_UNDASHED_image
  undash_DASHED_image
  dash_undash_image
  undash_dash_image

declare var_simps [simp]

subsubsection {* Injectivity Theorems *}

theorem dash_inj :
"inj dash"
apply (rule injI)
apply (simp add: dash_def)
apply (auto simp: split_paired_all)
done

theorem undash_inj_on :
"inj_on undash (VAR - UNDASHED)"
apply (rule inj_onI)
apply (simp add: var_defs)
apply (auto simp: split_paired_all)
done

theorem undash_inj_on_DASHED :
"inj_on undash DASHED"
apply (rule inj_onI)
apply (simp add: var_defs)
apply (auto simp: split_paired_all)
done

theorem undash_inj_on_DASHED_TWICE :
"inj_on undash DASHED_TWICE"
apply (rule inj_onI)
apply (simp add: var_defs)
apply (auto simp: split_paired_all)
done

subsubsection {* Distribution Theorems *}

theorem dash_inter_distr :
"dash ` (vs1 \<inter> vs2) = (dash ` vs1) \<inter> (dash ` vs2)"
apply (auto intro!: image_Int dash_inj)
done

theorem dash_unsion_distr :
"dash ` (vs1 \<union> vs2) = (dash ` vs1) \<union> (dash ` vs2)"
apply (auto intro!: image_Un)
done
end
end
