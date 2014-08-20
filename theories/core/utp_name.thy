(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_name.thy                                                         *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 15 July 2014 *)

header {* Variable Names *}

theory utp_name
imports "../utp_common" "../utils/Unit_ord"
begin

default_sort type

subsection {* Type Definition *}

text {*
  Names are encoded by records that consist of a name string, a dash count
  and a subscript. Undashed variables have a dash count of zero, and plain
  variables an empty string as a subscript. Future work may consider the use
  of extendible records to account for extendible custom notions of names.
*}

record name =
  name_str::"string"
  dashes::"nat"
  subscript::"string"

-- {* TODO: Perhaps move the following into @{theory utp_common}. *}

translations (type) "string" \<leftharpoondown> (type) "char list"

subsection {* Constructors *}

abbreviation MkName :: "string \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> name" where
"MkName n d s \<equiv> \<lparr>name_str = n, dashes = d, subscript = s\<rparr>"

text {* TODO: Perhaps rename @{text bName} into @{text MkPlainName}. *}

abbreviation bName :: "string \<Rightarrow> name" where
"bName n \<equiv> MkName n 0 ''''"

subsection {* Countability *}

definition name_to_nat :: "'MORE::countable name_ext \<Rightarrow> nat" where
"name_to_nat n = to_nat (name_str n, dashes n, subscript n, more n)"

instance name_ext :: (countable) countable
apply (intro_classes)
apply (rule_tac x = "name_to_nat" in exI)
apply (rule injI)
apply (unfold name_to_nat_def)
apply (erule asmE)
apply (induct_tac x)
apply (induct_tac y)
apply (simp_all)
done

subsection {* Linear Order *}

instantiation name_ext :: (linorder) linorder
begin
definition less_eq_name_ext :: "'a name_ext \<Rightarrow> 'a name_ext \<Rightarrow> bool" where
"(less_eq_name_ext n1 n2) \<longleftrightarrow>
   (name_str n1, dashes n1, subscript n1, more n1) \<le>
   (name_str n2, dashes n2, subscript n2, more n2)"

definition less_name_ext :: "'a name_ext \<Rightarrow> 'a name_ext \<Rightarrow> bool" where
"(less_name_ext n1 n2) \<longleftrightarrow> (n1 \<le> n2 \<and> \<not> n2 \<le> n1)"
instance
apply (intro_classes)
apply (simp add: less_name_ext_def)
apply (simp add: less_eq_name_ext_def)
apply (simp_all add: less_eq_name_ext_def)
apply (auto)
done
end

text {* The following automatically evaluates order relations on names. *}

declare less_eq_char_def [simp]
declare less_char_def [simp]
declare nat_of_char_def [simp]
declare less_eq_name_ext_def [simp]
declare less_name_ext_def [simp]

subsection {* Subscripts *}

syntax "_NoSub" :: "string" ("NoSub")

translations "NoSub" \<rightharpoonup> "''''"

definition chsub :: "string \<Rightarrow> name \<Rightarrow> name" where
"chsub s' = subscript_update
  (\<lambda> s . if s = NoSub then s' else (if s = s' then NoSub else s))"

paragraph {* Theorems *}

theorem chsub_inv [simp] :
"chsub s (chsub s n) = n"
apply (unfold chsub_def)
apply (simp)
done

theorem chsub_inj :
"inj (chsub s)"
apply (rule injI)
apply (metis chsub_inv)
done

theorem chsub_surj :
"surj (chsub s)"
apply (rule surjI)
apply (rule chsub_inv)
done

theorem chsub_bij [closure] :
"bij (chsub s)"
apply (rule Fun.bijI)
apply (rule chsub_inj)
apply (rule chsub_surj)
done

subsection {* Theorems *}

lemma MkName_name_mono :
"n1 < n2 \<Longrightarrow> MkName n1 d1 s1 < MkName n2 d2 s2"
apply (auto)
done

lemma MkName_dash_mono :
"d1 < d2 \<Longrightarrow> MkName n d1 s1 < MkName n d2 s2"
apply (auto)
done

lemma MkName_subscript_mono :
"s1 < s2 \<Longrightarrow> MkName n d s1 < MkName n d s2"
apply (auto)
done

lemma name_eq_intro [intro] :
"\<lbrakk>name_str (n1 :: name) = name_str (n2 :: name);
 dashes n1 = dashes n2;
 subscript n1 = subscript n2\<rbrakk> \<Longrightarrow> n1 = n2"
apply (rule name.equality)
apply (simp_all)
done

lemma name_elim [elim] :
"\<lbrakk>\<And> n d s . a = MkName n d s \<Longrightarrow> P a\<rbrakk> \<Longrightarrow> P a"
apply (erule name.cases)
done

lemma name_less_iff :
"(n1 :: name) < (n2 :: name) \<longleftrightarrow>
  (name_str n1 < name_str n2) \<or>
  (name_str n1 = name_str n2 \<and> dashes n1 < dashes n2) \<or>
  (name_str n1 = name_str n2 \<and> dashes n1 = dashes n2 \<and>
    subscript n1 < subscript n2)"
apply (case_tac n1)
apply (case_tac n2)
apply (clarsimp)
apply (auto)
done

lemma name_str_mono :
"name_str n1 < name_str n1 \<Longrightarrow> n1 < n2"
apply (auto)
done

lemma dashes_mono :
"\<lbrakk>name_str n1 \<le> name_str n2; dashes n1 < dashes n2\<rbrakk> \<Longrightarrow> n1 < n2"
apply (auto)
done

lemma subscript_mono :
"\<lbrakk>name_str n1 \<le> name_str n2;
 dashes n1 \<le> dashes n2;
 subscript n1 < subscript n2\<rbrakk> \<Longrightarrow> n1 < n2"
apply (auto)
done

lemma name_str_unique [simp] :
"name_str x \<noteq> name_str y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

lemma dashes_unique [simp] :
"dashes x \<noteq> dashes y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

lemma subscript_unique [simp] :
"subscript x \<noteq> subscript y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

text {* There is an infinite supply of names. *}

definition Suc_name :: "name \<Rightarrow> name" where
"Suc_name = dashes_update Suc"

lemma inj_Suc_name :
"inj Suc_name"
apply (rule injI)
apply (unfold Suc_name_def)
apply (case_tac x)
apply (case_tac y)
apply (simp)
done

lemma not_surj_Suc_name :
"\<not> surj Suc_name"
apply (unfold surj_def)
apply (clarsimp)
apply (rule_tac x = "MkName n 0 s" in exI)
apply (unfold Suc_name_def)
apply (simp)
done

lemma infinite_name :
"infinite (UNIV :: name set)"
apply (clarify)
apply (drule finite_UNIV_inj_surj [of "Suc_name"])
apply (rule inj_Suc_name)
apply (metis not_surj_Suc_name)
done

-- {* Hide auxiliary definition and facts for the above proof. *}

hide_fact inj_Suc_name
hide_fact not_surj_Suc_name
hide_const Suc_name
end
