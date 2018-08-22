(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uname.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 27 Jan 2016 *)

section {* Variable Names *}

text {* Note that I decided to remove the feature of multiple dashes. *}

theory uname
imports uconsts "../utils/Strings"
begin

text {* We are going to use the floor brackets for parsing names. *}

no_notation floor ("\<lfloor>_\<rfloor>")

subsection {* Name Type *}

text {*
  Names are encoded by records that consist of a name string, a dashing flag,
  and a string for a subscript. Dashed variables have a @{const True} flag,
  and undecorated variables have an empty string as a subscript. In principle,
  names can made extensible because records are extensible. The framework
  currently does not take advantage of this. We use @{type String.literal}
  rather than @{type string} as this gives us freedom in how we instantiate
  an ordering on strings. (We note that @{type string} is just a synonym for
  type @{typ "char list"} and therefore the ordering on @{type string} is
  already determined by the orderings chosen for lists. This turned out to
  be an issue when integrating the axiomatic value model with Isabelle/UTP.
*}

text {* \todo{Add support for extensible names throughout the framework}. *}

record uname =
  name_str::"string_t"
  dashed::"bool"
  subscript::"string_t"

subsection {* Constructors *}

abbreviation MkName :: "string \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> uname" where
"MkName n d s \<equiv> \<lparr>name_str = String.implode n, dashed = d, subscript = String.implode s\<rparr>"

abbreviation (input) MkPlain :: "string \<Rightarrow> uname" where
"MkPlain n \<equiv> MkName n False ''''"

subsection {* Restrictions *}

definition UNDASHED_uname :: "'more uname_ext set" where
[vars]: "UNDASHED_uname = {n. \<not> dashed n}"

adhoc_overloading UNDASHED UNDASHED_uname

definition DASHED_uname :: "'more uname_ext set" where
[vars]: "DASHED_uname = {n. dashed n}"

adhoc_overloading DASHED DASHED_uname

subsection {* Operators *}

definition dash_uname :: "'more uname_ext \<Rightarrow> 'more uname_ext" where
[vars]: "dash_uname = (dashed_update (\<lambda>_. True))"

adhoc_overloading dash dash_uname

definition undash_uname :: "'more uname_ext \<Rightarrow> 'more uname_ext" where
[vars]: "undash_uname = (dashed_update (\<lambda>_. False))"

adhoc_overloading undash undash_uname

subsection {* Subscripts *}

subsubsection {* No Subscript *}

text {* An empty string indicates the absence of a subscript. *}

syntax "_NoSub" :: "string" ("NoSub")

translations "NoSub" \<rightharpoonup> "(CONST String.implode) []"

subsubsection {* Add Subscript *}

text {* The definition below ensures that subscripting is an involution. *}

definition subscr_change ::
  "string \<Rightarrow> 'more uname_ext \<Rightarrow> 'more uname_ext" where
"subscr_change s' = (subscript_update
  (\<lambda>s. if s = NoSub then String.implode s' else if s = String.implode s' then NoSub else s))"

definition subscr_uname ::
  "'more uname_ext \<Rightarrow> string \<Rightarrow> 'more uname_ext" where
[vars]: "subscr_uname n s = (subscr_change s n)"

adhoc_overloading subscr_uname subscr

paragraph {* Theorems *}

interpretation invol_subscr :
  invol "subscr_change s"
apply (unfold_locales)
apply (unfold subscr_change_def)
apply (rule ext)
apply (clarsimp)
done

subsection {* Parsing and Printing *}

subsubsection {* Name Syntax *}

syntax "_uname" :: "id \<Rightarrow> uname" ("\<lfloor>_\<rfloor>")

subsubsection {* Parser Options *}

text {* Option @{text disable_uname_pp} disables pretty-printing of names. *}

ML {*
  val (disable_uname_pp, disable_uname_pp_setup) =
    Attrib.config_bool @{binding disable_uname_pp} (K false);
*}

setup disable_uname_pp_setup

subsubsection {* Translations *}

ML_file "uname.ML"

parse_translation {* [(@{syntax_const "_uname"}, K Name_Parser.uname_tr)] *}
print_translation {* [(@{const_syntax "MkName"}, Name_Printer.MkName_tr')] *}

subsection {* Instantiations *}

subsubsection {* Countability *}

definition uname_to_nat :: "'more::countable uname_ext \<Rightarrow> nat" where
"uname_to_nat n = to_nat (name_str n, dashed n, subscript n, more n)"

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

subsubsection {* Infinity *}

theorem infinite_uname_ext [simp]:
"infinite (UNIV :: 'a uname_ext set)"
apply (insert infinite_UNIV_String_literal)
apply (erule_tac f = "name_str" in infinite_transfer)
apply (unfold image_def)
apply (clarsimp)
apply (rule_tac x = "name_str_update (\<lambda>_. x) undefined" in exI)
apply (simp)
done

instance uname_ext :: (type) infinite
apply (intro_classes)
apply (rule infinite_uname_ext)
done

subsubsection {* Linear Order *}

text {* Names are ordered lexicographically by their record fields. *}

instantiation uname_ext :: (ord) ord
begin
definition less_eq_uname_ext :: "'a uname_ext \<Rightarrow> 'a uname_ext \<Rightarrow> bool" where
"(less_eq_uname_ext n1 n2) \<longleftrightarrow>
    name_str n1 < name_str n2 \<or>
    name_str n1 \<le> name_str n2 \<and> dashed n1 < dashed n2 \<or>
    name_str n1 \<le> name_str n2 \<and> dashed n1 \<le> dashed n2 \<and> subscript n1 < subscript n2 \<or>
    name_str n1 \<le> name_str n2 \<and> dashed n1 \<le> dashed n2 \<and> subscript n1 \<le> subscript n2 \<and> more n1 \<le> more n2"

definition less_uname_ext :: "'a uname_ext \<Rightarrow> 'a uname_ext \<Rightarrow> bool" where
"(less_uname_ext n1 n2) \<longleftrightarrow> (n1 \<le> n2 \<and> \<not> n2 \<le> n1)"
instance ..
end

instance uname_ext :: (order) order
proof
  show "\<And>x y :: 'a uname_ext. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (unfold less_eq_uname_ext_def less_uname_ext_def, rule refl)
  show "\<And>x :: 'a uname_ext. x \<le> x"
    by (simp add: less_eq_uname_ext_def)
  show "\<And>x y z :: 'a uname_ext. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (unfold less_eq_uname_ext_def)
    fix x :: "'a uname_scheme" and y :: "'a uname_scheme" and z :: "'a uname_scheme"
    assume a1: "name_str x < name_str y \<or> name_str x \<le> name_str y \<and> dashed x < dashed y \<or> name_str x \<le> name_str y \<and> dashed x \<le> dashed y \<and> subscript x < subscript y \<or> name_str x \<le> name_str y \<and> dashed x \<le> dashed y \<and> subscript x \<le> subscript y \<and> uname.more x \<le> uname.more y"
    assume a2: "name_str y < name_str z \<or> name_str y \<le> name_str z \<and> dashed y < dashed z \<or> name_str y \<le> name_str z \<and> dashed y \<le> dashed z \<and> subscript y < subscript z \<or> name_str y \<le> name_str z \<and> dashed y \<le> dashed z \<and> subscript y \<le> subscript z \<and> uname.more y \<le> uname.more z"
    then have f3: "name_str z = name_str y \<or> name_str y < name_str z"
      by fastforce
    then have f4: "name_str z = name_str y \<or> name_str x \<le> name_str z \<or> name_str x = name_str y"
      using a1 by fastforce
    { assume "dashed z \<le> dashed y"
      { assume "\<not> dashed y < dashed z \<and> dashed y \<le> dashed x"
        have "name_str x = name_str y \<and> name_str z = name_str y \<and> name_str y \<le> name_str y \<and> dashed x \<le> dashed z \<and> dashed y \<le> dashed x \<and> dashed z \<le> dashed y \<longrightarrow> (name_str x < name_str z \<or> name_str x \<le> name_str z \<and> dashed x < dashed z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x < subscript z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x \<le> subscript z \<and> uname.more x \<le> uname.more z) \<or> name_str y < name_str z \<or> name_str y < name_str y"
          using a2 a1 by (metis dual_order.trans less_le not_le)
        then have "name_str x = name_str y \<and> name_str z = name_str y \<and> dashed y \<le> dashed z \<and> name_str y \<le> name_str y \<and> dashed x \<le> dashed y \<and> dashed y \<le> dashed x \<and> dashed z \<le> dashed y \<longrightarrow> (name_str x < name_str z \<or> name_str x \<le> name_str z \<and> dashed x < dashed z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x < subscript z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x \<le> subscript z \<and> uname.more x \<le> uname.more z) \<or> name_str y < name_str z \<or> name_str y < name_str y"
          using dual_order.trans by blast }
      then have "name_str x = name_str y \<and> name_str z = name_str y \<and> name_str y \<le> name_str y \<and> dashed z \<le> dashed x \<and> dashed x \<le> dashed y \<and> dashed z \<le> dashed y \<longrightarrow> (name_str x < name_str z \<or> name_str x \<le> name_str z \<and> dashed x < dashed z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x < subscript z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x \<le> subscript z \<and> uname.more x \<le> uname.more z) \<or> name_str y < name_str z \<or> name_str y < name_str y"
        using a2 by (metis less_le not_le) }
    then have "name_str x = name_str y \<longrightarrow> name_str x < name_str z \<or> name_str x \<le> name_str z \<and> dashed x < dashed z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x < subscript z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x \<le> subscript z \<and> uname.more x \<le> uname.more z"
      using a2 a1 by force
    then show "name_str x < name_str z \<or> name_str x \<le> name_str z \<and> dashed x < dashed z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x < subscript z \<or> name_str x \<le> name_str z \<and> dashed x \<le> dashed z \<and> subscript x \<le> subscript z \<and> uname.more x \<le> uname.more z"
      using f4 f3 a1 by (metis (no_types) less_le not_le)
  qed
  show "\<And>x y :: 'a uname_ext. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis dual_order.strict_iff_order less_eq_uname_ext_def less_le_not_le uname.equality)
qed

instance uname_ext :: (linorder) linorder
apply (intro_classes)
apply (unfold less_eq_uname_ext_def less_uname_ext_def)
apply force
done

instance uname_ext :: (linorder) normalise
apply (intro_classes)
done

subsection {* Proof Support *}

text {* The simplifications below evaluate inequalities on names. *}

declare less_eq_char_def [simp]
declare less_char_def [simp]
declare less_eq_literal.rep_eq [simp]
declare less_literal.rep_eq [simp]
declare less_eq_uname_ext_def [simp]
declare less_uname_ext_def [simp]

subsection {* Theorems *}

text {* \fixme{Should the following be a default simplification?} *}

lemma uname_less_iff (*[simp]*):
"(n1 :: uname) < (n2 :: uname) \<longleftrightarrow>
 (name_str n1 < name_str n2) \<or>
 (name_str n1 = name_str n2 \<and> dashed n1 < dashed n2) \<or>
 (name_str n1 = name_str n2 \<and> dashed n1 = dashed n2 \<and>
  subscript n1 < subscript n2)"
apply (induct_tac n1)
apply (induct_tac n2)
apply (clarsimp)
apply (metis less_asym' less_eq_literal.rep_eq less_literal.rep_eq linorder_cases not_less)
done

text {* \fixme{Are the three lemmas below really needed / desirable?} *}

lemma name_str_neq_dest (*[simp]*):
"name_str x \<noteq> name_str y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

lemma dashes_neq_dest (*[simp]*):
"dashes x \<noteq> dashes y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

lemma subscript_neq_dest (*[simp]*):
"subscript x \<noteq> subscript y \<Longrightarrow> x \<noteq> y"
apply (auto)
done

subsection {* Experiments *}

lemma
"f(\<lfloor>c\<rfloor> := (30::nat), \<lfloor>b\<rfloor> := (20::nat), \<lfloor>a\<rfloor> := (10::nat)) =
 f(\<lfloor>b\<rfloor> := (20::nat), \<lfloor>a\<rfloor> := (10::nat), \<lfloor>c\<rfloor> := (30::nat))"
(* This seems to take a little more time... An Isabelle2016-1 issue? *)
apply (fun_upd_normalise_tac)
apply (rule refl)
done
end