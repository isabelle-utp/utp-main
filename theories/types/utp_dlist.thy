(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_dlist.thy                                                        *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 30 July 2014 *)

header {* Defined Lists *}

theory utp_dlist
imports "../core/utp_defined"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
begin

default_sort DEFINED

subsection {* Type Definition *}

text {* Rename the following type into @{text "'a dlist"}. *}

typedef 'a ULIST = "{l :: 'a list . \<forall> x \<in> set l . \<D> x}"
apply (rule_tac x = "[]" in exI)
apply (auto)
done

setup_lifting type_definition_ULIST

theorems Rep_ULIST' = Rep_ULIST [simplified]
theorems Abs_ULIST_inverse' = Abs_ULIST_inverse [simplified]
declare Rep_ULIST' [simp]
declare Abs_ULIST_inverse' [simp]
declare Rep_ULIST_inverse [simp]

lemma Rep_ULIST_intro [intro!] :
"Rep_ULIST x = Rep_ULIST y \<Longrightarrow> x = y"
apply (metis Rep_ULIST_inject)
done

lemma Rep_ULIST_elim [elim] :
"x = y \<Longrightarrow> \<lbrakk>Rep_ULIST x = Rep_ULIST y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (auto)
done

subsection {* Constants *}

lift_definition NilUL :: "'a ULIST"
is "[]" by (simp)

subsection {* Operators *}

lift_definition AppendUL ::
  "'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST" (infixr "@\<^sub>u" 65)
is "op @" by (auto)

lift_definition PrefixUL :: "'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> bool"
is "prefix" .

lift_definition PrefixeqUL :: "'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> bool"
is "prefixeq" .

lift_definition MinusUL :: "'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST"
is "\<lambda> xs ys. drop (length ys) xs"
  by (metis in_set_dropD)

definition ConsUL :: "'a \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST" (infixr "#\<^sub>u" 65) where
"ConsUL x xs = Abs_ULIST (x # Rep_ULIST xs)"

lemma ConsUL_rep_eq :
"\<D> x \<Longrightarrow> Rep_ULIST (x #\<^sub>u xs) = x # Rep_ULIST xs"
  by (simp_all add: ConsUL_def)

subsection {* Definedness *}

lemma ULIST_elems_defined [defined] :
"x \<in> set (Rep_ULIST xs) \<Longrightarrow> \<D> x"
apply (insert Rep_ULIST [of xs])
apply (auto)
done

instantiation ULIST :: (DEFINED) DEFINED_NE
begin
definition "defined_ULIST (xs :: 'a ULIST) = True"

lemma defined_ULIST [defined] :
"\<D> (xs :: 'a ULIST)"
  by (simp add: defined_ULIST_def)

instance
  by (intro_classes, auto simp add: defined_ULIST_def)
end

text {* Set up the UTP proof tactics to evaluate defined sets. *}

lemma ULIST_transfer [eval, evale] :
"xs = ys \<longleftrightarrow> Rep_ULIST xs = Rep_ULIST ys"
  by (auto)

declare NilUL.rep_eq [eval, evale]
declare ConsUL_rep_eq [eval, evale]
declare AppendUL.rep_eq [eval, evale]
declare MinusUL.rep_eq [eval, evale]
declare PrefixUL.rep_eq [eval, evale]
declare PrefixeqUL.rep_eq [eval, evale]
end
