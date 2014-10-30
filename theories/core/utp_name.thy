(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_name.thy                                                         *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 3 September 2014 *)

header {* Variable Names *}

theory utp_name
imports "../utp_common"
begin

default_sort type

subsection {* Type Definition *}

text {*
  Names are encoded by records that consist of a name string, a dash count,
  and a string for a subscript. Undashed variables have a dash count of zero,
  and plain variables an empty string as a subscript. Names are implicitly
  extendible but the mechanisation does not take advantage of this for now.
*}

text {* \todo{Add support for extendible names throughout the mechanisation.} *}

record uname =
  name_str::"string"
  dashes::"nat"
  subscript::"string"

text {* The following is for pretty-printing the string type. *}

translations (type) "string" \<leftharpoondown> (type) "char list"

subsection {* Constructors *}

abbreviation MkName :: "string \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> uname" where
"MkName n d s \<equiv> \<lparr>name_str = n, dashes = d, subscript = s\<rparr>"

text {* \fixme{Perhaps rename @{text bName} into @{text MkPlain}}. *}

abbreviation bName :: "string \<Rightarrow> uname" where
"bName n \<equiv> MkName n 0 ''''"

subsection {* Subscripts *}

paragraph {* Empty Subscript *}

text {* An empty string is used to signify the absence of a subscript. *}

syntax "_NoSub" :: "string" ("NoSub")

translations "NoSub" \<rightharpoonup> "''''"

paragraph {* Change Subscript *}

text {* Our definition ensures that changing subscripts is an involution. *}

text {* \fixme{Does it have to be? Is there benefit in this?} *}

definition chsub :: "string \<Rightarrow> uname \<Rightarrow> uname" where
"chsub s' = subscript_update
  (\<lambda> s . if s = NoSub then s' else if s = s' then NoSub else s)"

theorem chsub_inv [simp] :
"chsub s (chsub s n) = n"
apply (unfold chsub_def)
apply (simp)
done

theorem chsub_comp_id [simp] :
"(chsub s) o (chsub s) = id"
apply (rule ext)
apply (simp)
done

theorem chsub_inj [simp] :
"inj (chsub s)"
apply (rule injI)
apply (metis chsub_inv)
done

theorem chsub_surj [simp] :
"surj (chsub s)"
apply (rule surjI)
apply (rule chsub_inv)
done

theorem chsub_bij [simp] :
"bij (chsub s)"
apply (rule Fun.bijI)
apply (rule chsub_inj)
apply (rule chsub_surj)
done

subsection {* Countability *}

definition uname_to_nat :: "'more::countable uname_ext \<Rightarrow> nat" where
"uname_to_nat n = to_nat (name_str n, dashes n, subscript n, more n)"

instance uname_ext :: (countable) countable
apply (intro_classes)
apply (rule_tac x = "uname_to_nat" in exI)
apply (rule injI)
apply (unfold uname_to_nat_def)
apply (erule asmE)
apply (induct_tac x)
apply (induct_tac y)
apply (clarsimp)
done

subsection {* Infinity of Names *}

text {* We next prove that there is an infinite supply of names. *}

definition Suc_uname :: "'more uname_ext \<Rightarrow> 'more uname_ext" where
"Suc_uname = dashes_update Suc"

lemma inj_Suc_uname :
"inj Suc_uname"
apply (rule injI)
apply (unfold Suc_uname_def)
apply (case_tac x)
apply (case_tac y)
apply (simp)
done

lemma not_surj_Suc_uname :
"\<not> surj Suc_uname"
apply (unfold surj_def)
apply (clarsimp)
apply (rule_tac x =
  "\<lparr>name_str = undefined, dashes = 0, subscript = undefined, \<dots> = undefined\<rparr>"
    in exI)
apply (unfold Suc_uname_def)
apply (rule allI)
apply (induct_tac x)
apply (simp)
done

lemma infinite_uname :
"infinite (UNIV :: 'm uname_ext set)"
apply (clarify)
apply (drule finite_UNIV_inj_surj [of "Suc_uname"])
apply (rule inj_Suc_uname)
apply (erule contrapos_pp)
apply (rule not_surj_Suc_uname)
done

instance uname_ext :: (type) infinite
apply (intro_classes)
apply (rule infinite_uname)
done

text {* Hide auxiliary definition and facts for the above proof. *}

hide_const Suc_uname
hide_fact inj_Suc_uname not_surj_Suc_uname

subsection {* Linear Order *}

text {*
  Names are ordered lexicographically by their name string, dash count,
  subscript, and a possible extension type for ``more''.
*}
  
instantiation uname_ext :: (linorder) linorder
begin
definition less_eq_uname_ext :: "'a uname_ext \<Rightarrow> 'a uname_ext \<Rightarrow> bool" where
"(less_eq_uname_ext n1 n2) \<longleftrightarrow>
   (name_str n1, dashes n1, subscript n1, more n1) \<le>
   (name_str n2, dashes n2, subscript n2, more n2)"

definition less_uname_ext :: "'a uname_ext \<Rightarrow> 'a uname_ext \<Rightarrow> bool" where
"(less_uname_ext n1 n2) \<longleftrightarrow> (n1 \<le> n2 \<and> \<not> n2 \<le> n1)"

instance
apply (intro_classes)
apply (simp add: less_uname_ext_def)
apply (simp add: less_eq_uname_ext_def)
apply (simp_all add: less_eq_uname_ext_def)
apply (auto)
done
end

text {*
  The following simplifications automatically evaluate name inequalities.
*}

declare less_eq_char_def [simp]
declare less_char_def [simp]
declare nat_of_char_def [simp]
declare less_eq_uname_ext_def [simp]
declare less_uname_ext_def [simp]

subsection {* Theorems *}

text {* \fixme{Should the following be a default simplification?} *}

lemma uname_less_iff (* [simp] *) :
"(n1 :: uname) < (n2 :: uname) \<longleftrightarrow>
 (name_str n1 < name_str n2) \<or>
 (name_str n1 = name_str n2 \<and> dashes n1 < dashes n2) \<or>
 (name_str n1 = name_str n2 \<and> dashes n1 = dashes n2 \<and>
  subscript n1 < subscript n2)"
apply (induct_tac n1)
apply (induct_tac n2)
apply (simp)
apply (safe, simp_all)
done

lemma name_str_neq_dest [simp] :
"name_str x \<noteq> name_str y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

lemma dashes_neq_dest [simp] :
"dashes x \<noteq> dashes y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

lemma subscript_neq_dest [simp] :
"subscript x \<noteq> subscript y \<Longrightarrow> x \<noteq> y"
apply (auto)
done
end
