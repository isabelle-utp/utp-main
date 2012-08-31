(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_var.thy                                              *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Variables *}

theory utp_var
imports utp_name
begin

type_synonym 'TYPE SIMPLE_VAR = "SIMPLE_NAME \<times> 'TYPE"
type_synonym 'TYPE VAR = "NAME \<times> 'TYPE"

abbreviation var_name :: "'TYPE VAR \<Rightarrow> NAME" ("name") where
"var_name \<equiv> fst"

abbreviation var_type :: "'TYPE VAR \<Rightarrow> 'TYPE" ("type") where
"var_type \<equiv> snd"

definition add_dash :: "nat \<Rightarrow> 'TYPE SIMPLE_VAR \<Rightarrow> 'TYPE VAR" where
"add_dash n v \<equiv> (\<lparr> name_str = name_str (fst v), subscript = subscript (fst v), dashes = n \<rparr>, snd v)"

definition rem_dash :: "'TYPE VAR \<Rightarrow> 'TYPE SIMPLE_VAR" where
"rem_dash v \<equiv> (\<lparr> name_str = name_str (fst v), subscript = subscript (fst v) \<rparr>, snd v)"

ML {*
  structure VarThm =
    Named_Thms (val name = @{binding "var"} val description = "variable laws");
*}

setup {* VarThm.setup *}

subsection {* Locale @{term "VAR"} *}

locale VAR =
-- {* The type universe is fixed to determine @{typ "'TYPE"}. *}
  fixes var_type_univ :: "'TYPE set"
begin

subsection {* Constructors *}

definition MkVar :: "NAME \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE VAR" where
"MkVar n t = (n, t)"

definition MkPlain :: "string \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE VAR" where
"MkPlain s t = MkVar \<lparr>name_str = s, subscript = NoSub, dashes = 0\<rparr> t"

subsection {* Operators *}

definition dash :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"dash v = (
   \<lparr>name_str = name_str (name v),
   subscript = subscript (name v),
   dashes = dashes (name v) + 1\<rparr>, type v)"

definition undash :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"undash v = (
   \<lparr>name_str = name_str (name v),
   subscript = subscript (name v),
   dashes = dashes (name v) - 1\<rparr>, type v)"

subsection {* Restrictions *}

definition UNDASHED :: "'TYPE VAR set" where
"UNDASHED = {v . dashes (name v) = 0}"

definition DASHED :: "'TYPE VAR set" where
"DASHED = {v . dashes (name v) = 1}"

definition DASHED_TWICE :: "'TYPE VAR set" where
"DASHED_TWICE = {v . dashes (name v) = 2}"

definition PLAIN :: "'TYPE VAR set" where
"PLAIN = {v . v \<in> UNDASHED \<and> subscript (name v) = NoSub}"

subsection {* Properties *}

theorem dash_undash[var]: "x \<in> -UNDASHED \<Longrightarrow> dash (undash x) = x"
  apply(auto simp add:dash_def undash_def UNDASHED_def)
  apply(smt NAME.surjective pair_collapse unit.exhaust)
done

theorem undash_dash[var]: "undash (dash x) = x"
  apply(auto simp add:dash_def undash_def)
  apply(smt NAME.surjective pair_collapse unit.exhaust)
done

lemma dash_inj[var]: "inj dash"
  apply(auto simp add:inj_on_def dash_def)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
done

lemma dash_bij[var]: "bij_betw dash UNIV (-UNDASHED)"
  apply(auto simp add:bij_betw_def dash_inj)
  apply(simp add:UNDASHED_def dash_def)
  apply(simp add:image_def)
  apply(rule_tac x="undash x" in exI)
  apply(metis ComplI dash_undash)
done

lemma dashed_undash_inj[var]: "inj_on undash DASHED"
  apply(auto simp add:inj_on_def undash_def DASHED_def)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
done

lemma dashed2_undash_inj[var]: "inj_on undash DASHED_TWICE"  
  apply(auto simp add:inj_on_def undash_def DASHED_TWICE_def)
  apply(case_tac x)
  apply(case_tac y)
  apply(simp)
done

theorem dash_undashed [var]:
"vs \<subseteq> UNDASHED \<Longrightarrow> dash ` vs \<subseteq> DASHED"
  by (auto simp add: DASHED_def UNDASHED_def dash_def)

theorem dash_dashed [var]:
"vs \<subseteq> DASHED \<Longrightarrow> dash ` vs \<subseteq> DASHED_TWICE"
  by (auto simp add: DASHED_def DASHED_TWICE_def dash_def)

theorem undash_dashed [var]:
"vs \<subseteq> DASHED \<Longrightarrow> undash ` vs \<subseteq> UNDASHED"
  by (auto simp add: DASHED_def UNDASHED_def undash_def)

theorem undash_dashed_twice [var]:
"vs \<subseteq> DASHED_TWICE \<Longrightarrow> undash ` vs \<subseteq> DASHED"
  by (auto simp add: DASHED_def DASHED_TWICE_def undash_def)

lemma [var]: "v \<in> UNDASHED \<Longrightarrow> dash v \<in> DASHED"
  by (simp add:UNDASHED_def DASHED_def dash_def)

lemma [var]: "v \<in> DASHED \<Longrightarrow> dash v \<in> DASHED_TWICE"
  by (simp add:DASHED_def DASHED_TWICE_def dash_def)

lemma [var]: "v \<in> DASHED \<Longrightarrow> undash v \<in> UNDASHED"
  by (simp add:DASHED_def UNDASHED_def undash_def)

lemma [var]: "v \<in> DASHED_TWICE \<Longrightarrow> undash v \<in> DASHED"
  by (simp add:DASHED_def DASHED_TWICE_def undash_def)

lemma [var]: "UNDASHED \<subseteq> UNDASHED \<union> DASHED" by auto
lemma [var]: "DASHED \<subseteq> UNDASHED \<union> DASHED" by auto

lemma [var]: "a \<subseteq> UNDASHED \<Longrightarrow> a \<subseteq> UNDASHED \<union> DASHED"
  by auto

lemma [var]: "a \<subseteq> DASHED \<Longrightarrow> a \<subseteq> UNDASHED \<union> DASHED"
  by auto

lemma [var]: "DASHED \<subseteq> -UNDASHED"
  by (auto simp add:DASHED_def UNDASHED_def)

lemma [var]: "DASHED_TWICE \<subseteq> -UNDASHED"
  by (auto simp add:DASHED_TWICE_def UNDASHED_def)

lemma [var]: "x \<in> DASHED \<Longrightarrow> dash (undash x) = x"
  by (insert var, auto)

lemma [var]: "dash ` UNDASHED = DASHED"
  apply(auto simp add: image_def)
  apply(simp add:var dash_def DASHED_def UNDASHED_def)
  apply(rule_tac x="undash x" in bexI)
  apply(auto simp add:var)
done

lemma [var]: "undash ` DASHED = UNDASHED"
  apply(auto simp add: image_def)
  apply(simp add:var undash_def DASHED_def UNDASHED_def)
  apply(rule_tac x="dash x" in bexI)
  apply(auto simp add:var)
done

lemma add_dash_inj[simp,var]: "inj (add_dash n)"
  apply(auto simp add:inj_on_def add_dash_def)
  apply(case_tac x, case_tac y, simp)
done

end
end
