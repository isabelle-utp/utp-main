(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_var.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Variables *}

theory utp_var
imports utp_types utp_names
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

theorem type_dash [simp] :
"type (dash v) = type v"
apply (simp add: var_defs)
done

theorem type_undash [simp] :
"type (undash v) = type v"
apply (simp add: var_defs)
done

theorem UNDASHED_dash_DASHED [simp] :
"x \<in> UNDASHED \<Longrightarrow> dash x \<in> DASHED"
apply (simp add: var_defs)
done

theorem DASHED_undash_UNDASHED [simp] :
"x \<in> DASHED \<Longrightarrow> undash x \<in> UNDASHED"
apply (simp add: var_defs)
done

theorem UNDASHED_DASHED_contra [dest] :
"\<lbrakk>x \<in> UNDASHED; x \<in> DASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem UNDASHED_dash_contra [dest] :
"\<lbrakk>x \<in> UNDASHED; x = dash y\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem undash_dash_contra [dest] :
"\<lbrakk>x \<in> DASHED; y \<in> UNDASHED; undash x = dash y\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem undash_dash [simp] :
"undash (dash x) = x"
apply (simp add: var_defs)
apply (induct_tac x)
apply (simp)
done

theorem dash_undash [simp] :
"x \<in> DASHED \<Longrightarrow> dash (undash x) = x"
apply (simp add: var_defs)
apply (atomize (full))
apply (induct_tac x)
apply (auto)
done

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
end
end