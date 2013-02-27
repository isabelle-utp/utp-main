(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_names.thy                                                        *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Variable Names *}

theory utp_names
imports "../utp_common"
begin

subsection {* Subscripts *}

text {* Subscripts are encoded by virtue of a datatype. *}

datatype SUBSCRIPT = Sub "nat" | NoSub

derive countable SUBSCRIPT
derive linorder SUBSCRIPT

subsection {* Names *}

text {* We use a datatype to encode names, which consist of a name string, dash count
and possible subscript. We opt for a datatype rather than a record because it is
then easier to show that @{term "NAME"} is countable. As a result we derive the
usual record theorems manually.
*} 

datatype NAME =
  MkName string nat SUBSCRIPT

derive countable NAME
derive linorder NAME

lemma MkName_name_mono: "n1 < n2 \<Longrightarrow> MkName n1 d1 s1 < MkName n2 d2 s2"
  by (simp add: less_NAME_def)

lemma MkName_dash_mono: "d1 < d2 \<Longrightarrow> MkName n d1 s1 < MkName n d2 s2"
  by (simp add: less_NAME_def)

lemma MkName_subscript_mono: "s1 < s2 \<Longrightarrow> MkName n d s1 < MkName n d s2"
  by (simp add: less_NAME_def)

primrec name_str :: "NAME \<Rightarrow> string" where
"name_str (MkName n d s) = n"

primrec dashes :: "NAME \<Rightarrow> nat" where
"dashes (MkName n d s) = d"

primrec subscript :: "NAME \<Rightarrow> SUBSCRIPT" where
"subscript (MkName n d s) = s"

abbreviation bName :: "string \<Rightarrow> NAME" where
"bName n \<equiv> MkName n 0 NoSub"

lemma MkName_inverse [simp]: 
  "MkName (name_str n) (dashes n) (subscript n) = n"
  by (case_tac n, simp)

lemma NAME_eq_intro [intro]:
  "\<lbrakk> name_str n1 = name_str n2; dashes n1 = dashes n2; subscript n1 = subscript n2 \<rbrakk> 
   \<Longrightarrow> n1 = n2"
  by (case_tac n1, case_tac n2, simp)

lemma NAME_elim [elim]:
  "\<lbrakk> \<And> n d s. a = MkName n d s \<Longrightarrow> P a \<rbrakk> \<Longrightarrow> P a"
  by (case_tac a, simp)

lemma NAME_less_iff: 
  "n1 < n2 \<longleftrightarrow> 
    name_str n1 < name_str n2 \<or> 
    (name_str n1 = name_str n2 \<and> dashes n1 < dashes n2) \<or>
    (name_str n1 = name_str n2 \<and> dashes n1 = dashes n2 \<and> subscript n1 < subscript n2)"
  by (case_tac n1, case_tac n2, auto simp add:less_NAME_def)

lemma name_str_mono: "name_str x < name_str y \<Longrightarrow> x < y"
  by (case_tac x, case_tac y, auto intro: MkName_name_mono)

lemma dashes_mono: "\<lbrakk> name_str x \<le> name_str y; dashes x < dashes y \<rbrakk> \<Longrightarrow> x < y"
  apply (case_tac x, case_tac y, auto)
  apply (metis MkName_dash_mono MkName_name_mono order_less_le)
done

lemma subscript_mono: 
  "\<lbrakk> name_str x \<le> name_str y; dashes x \<le> dashes y; subscript x < subscript y \<rbrakk> \<Longrightarrow> x < y"
  apply (case_tac x, case_tac y, auto)
  apply (metis MkName_dash_mono MkName_name_mono MkName_subscript_mono linorder_not_le order_antisym)
done

subsection {* There are infinite names *}

text {* It is useful to know that given a finite number of names that a fresh name
can be generated. The way we do this by showing the NAME is an infinite sort, or
rather than name is not finite. The proof below demonstrates this by showing that
the successor name injection @{term "Suc_NAME"} cannot be a surjection. *}

definition Suc_NAME :: "NAME \<Rightarrow> NAME" where
"Suc_NAME n = MkName (name_str n @ ''0'') (dashes n) (subscript n)"

lemma inj_Suc_NAME: "inj Suc_NAME"
  by (auto simp add:inj_on_def Suc_NAME_def)

lemma infinite_NAME: "\<not> finite (UNIV :: NAME set)"
proof
  assume "finite (UNIV :: NAME set)"
  with finite_UNIV_inj_surj[of "Suc_NAME"]
  show False
    apply (simp add:inj_Suc_NAME)
    apply (auto simp add:surj_def Suc_NAME_def)
    apply (metis finite_UNIV_inj_surj name_str.simps snoc_eq_iff_butlast)
  done
qed

subsection {* Restrictions *}

text {* We only consider substitutions that are permutations. *}

definition NAME_SUBST :: "(NAME \<Rightarrow> NAME) \<Rightarrow> bool" where
"NAME_SUBST = bij"

end