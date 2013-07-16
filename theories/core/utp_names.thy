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

type_synonym SUBSCRIPT = "nat list"


abbreviation "NoSub \<equiv> [] :: SUBSCRIPT"
abbreviation "Sub n \<equiv> [n] :: SUBSCRIPT"

(*
datatype SUBSCRIPT = Sub "nat" | NoSub

primrec to_nat_SUBSCRIPT :: "SUBSCRIPT \<Rightarrow> nat" where
"to_nat_SUBSCRIPT (Sub n) = Suc n" |
"to_nat_SUBSCRIPT (NoSub) = 0" 

instance SUBSCRIPT :: countable 
  apply (intro_classes)
  apply (rule_tac x="to_nat_SUBSCRIPT" in exI)
  apply (rule injI)
  apply (case_tac x, case_tac[!] y)
  apply (auto)
done

instantiation SUBSCRIPT :: linorder
begin

definition less_eq_SUBSCRIPT :: "SUBSCRIPT \<Rightarrow> SUBSCRIPT \<Rightarrow> bool" where
"less_eq_SUBSCRIPT x y = (to_nat_SUBSCRIPT x \<le> to_nat_SUBSCRIPT y)"

definition less_SUBSCRIPT :: "SUBSCRIPT \<Rightarrow> SUBSCRIPT \<Rightarrow> bool" where
"less_SUBSCRIPT x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
  apply (intro_classes, auto simp add:less_eq_SUBSCRIPT_def less_SUBSCRIPT_def)
  apply (case_tac x, case_tac[!] y)
  apply (auto)
done
end
*)

subsection {* Names *}

text {* We use a datatype to encode names, which consist of a name string, dash count
and possible subscript. We opt for a datatype rather than a record because it is
then easier to show that @{term "NAME"} is countable. As a result we derive the
usual record theorems manually.
*} 

datatype NAME =
  MkName string nat SUBSCRIPT

primrec to_nat_NAME :: "NAME \<Rightarrow> nat" where
"to_nat_NAME (MkName n d s) = to_nat (n, d, s)"

instance NAME :: countable
  apply (intro_classes)
  apply (rule_tac x="to_nat_NAME" in exI)
  apply (rule injI)
  apply (case_tac x, case_tac[!] y)
  apply (auto)
done

instantiation NAME :: linorder
begin

fun less_eq_NAME :: "NAME \<Rightarrow> NAME \<Rightarrow> bool" where
"(MkName n1 d1 s1) \<le> (MkName n2 d2 s2) = ((n1,d1,s1) \<le> (n2,d2,s2))"

fun less_NAME :: "NAME \<Rightarrow> NAME \<Rightarrow> bool" where
"(MkName n1 d1 s1) < (MkName n2 d2 s2) = ((n1,d1,s1) < (n2,d2,s2))"

instance
  apply (intro_classes, auto)
  apply (case_tac x, case_tac y, auto)
  apply (case_tac x, case_tac y, auto)
  apply (case_tac x, case_tac y, simp, metis less_le prod.inject)
  apply (case_tac x, auto)
  apply (case_tac x, case_tac y, case_tac z, auto)
  apply (case_tac x, case_tac y, auto)
  apply (case_tac x, case_tac y, auto)
done
end

lemma MkName_name_mono: "n1 < n2 \<Longrightarrow> MkName n1 d1 s1 < MkName n2 d2 s2"
  by (auto simp add:prod_less_eq)

lemma MkName_dash_mono: "d1 < d2 \<Longrightarrow> MkName n d1 s1 < MkName n d2 s2"
  by (auto simp add:prod_less_eq)


lemma MkName_subscript_mono: "s1 < s2 \<Longrightarrow> MkName n d s1 < MkName n d s2"
  by (auto simp add:prod_less_eq)

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
  by (case_tac n1, case_tac n2, auto simp add:prod_less_eq)

lemma name_str_mono: "name_str x < name_str y \<Longrightarrow> x < y"
  by (case_tac x, case_tac y, auto simp add:prod_less_eq)

lemma dashes_mono: "\<lbrakk> name_str x \<le> name_str y; dashes x < dashes y \<rbrakk> \<Longrightarrow> x < y"
  by (case_tac x, case_tac y, auto simp add:prod_less_eq)

lemma subscript_mono: 
  "\<lbrakk> name_str x \<le> name_str y; dashes x \<le> dashes y; subscript x < subscript y \<rbrakk> \<Longrightarrow> x < y"
  by (case_tac x, case_tac y, auto simp add:prod_less_eq)

lemma name_str_uniq [simp]: 
  "name_str x \<noteq> name_str y \<Longrightarrow> x \<noteq> y"
  by (auto)

lemma dashes_uniq [simp]: 
  "dashes x \<noteq> dashes y \<Longrightarrow> x \<noteq> y"
  by (auto)

lemma subscript_uniq [simp]: 
  "subscript x \<noteq> subscript y \<Longrightarrow> x \<noteq> y"
  by (auto)

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