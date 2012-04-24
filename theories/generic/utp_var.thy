(******************************************************************************)
(* Title: utp/generic/utp_var.thy                                             *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_var
imports utp_name
begin

section {* Generic Variables *}

text {* Should we introduce a proper type for variables? *}

types 'TYPE VAR = "NAME \<times> 'TYPE"

subsection {* Locale @{text "VAR"} *}

locale VAR =
-- {* Type Universe -- needed to determine @{text "'TYPE"}. *}
  fixes var_type_univ :: "'TYPE set"
begin

subsection {* Constructors *}

definition MkVar :: "NAME \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE VAR" where
"MkVar n t = (n, t)"

definition MkPlain :: "string \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE VAR" where
"MkPlain s t = MkVar \<lparr>name_str = s, dashes = 0, subscript = NoSub\<rparr> t"

subsection {* Destructors *}

abbreviation var_name :: "'TYPE VAR \<Rightarrow> NAME" ("name") where
"name v \<equiv> (fst v)"

abbreviation var_type :: "'TYPE VAR \<Rightarrow> 'TYPE" ("type") where
"type v \<equiv> (snd v)"

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
"UNDASHED \<equiv> {v . dashes (name v) = 0}"

definition DASHED :: "'TYPE VAR set" where
"DASHED \<equiv> {v . dashes (name v) = 1}"

definition PLAIN :: "'TYPE VAR set" where
"PLAIN \<equiv> {v . v \<in> UNDASHED \<and> subscript (name v) = NoSub}"

subsection {* Substitution *}

definition VAR_SUBST :: "('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST \<equiv> {ss . bij ss \<and> (\<forall> v . type (ss v) = type v)}"
end
end
