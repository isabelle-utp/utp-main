(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_value.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Abstract Values *}

theory utp_value_2
imports "../utp_common"
begin

subsection {* Theorem Attributes *}

ML {*
  structure typing =
    Named_Thms (val name = @{binding typing} val description = "typing theorems")
*}

setup typing.setup

ML {*
  structure defined =
    Named_Thms (val name = @{binding defined} val description = "definedness theorems")
*}

setup defined.setup

class DEFINED =
  fixes Defined   :: "'a \<Rightarrow> bool" ("\<D>")

class VALUE = DEFINED +
  fixes   utype_rel :: "'a \<Rightarrow> udom \<Rightarrow> bool" (infix ":\<^sub>u" 50)
  assumes utype_nonempty: "\<exists> t v. v :\<^sub>u t \<and> \<D> v"

default_sort VALUE

(* A type must contain at least one defined value *) 
definition "UTYPES (x::'a itself) = {t. \<exists> v :: 'a. v :\<^sub>u t \<and> \<D> v}"

typedef (open) 'VALUE UTYPE = "UTYPES TYPE('VALUE)"
  apply (insert utype_nonempty)
  apply (auto simp add:UTYPES_def)
done

lemma Rep_UTYPE_elim [elim]:
  "\<lbrakk> \<And> v\<Colon>'VALUE. \<lbrakk> v :\<^sub>u Rep_UTYPE (t :: 'VALUE UTYPE); \<D> v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (insert Rep_UTYPE[of t])
  apply (auto simp add:UTYPES_def)
done

definition type_rel :: "'VALUE \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool" (infix ":" 50) where
"x : t \<longleftrightarrow> x :\<^sub>u Rep_UTYPE t"

definition default :: "'VALUE UTYPE \<Rightarrow> 'VALUE" where
"default t \<equiv> SOME x. x : t"

definition someType :: "'VALUE UTYPE" where
"someType \<equiv> SOME t. \<exists>x. x : t"

lemma type_non_empty: "\<exists> x. x : t"
  apply (auto simp add:type_rel_def)
  apply (rule_tac Rep_UTYPE_elim)
  apply (auto)
done

lemma type_non_empty_defined: "\<exists> x. x : t \<and> \<D> x"
  apply (auto simp add:type_rel_def)
  apply (rule_tac Rep_UTYPE_elim)
  apply (auto)
done

lemma type_non_empty_elim [elim]:
  "\<lbrakk> \<And> x. \<lbrakk> x : t; \<D> x \<rbrakk> \<Longrightarrow> P t \<rbrakk> \<Longrightarrow> P t"
  apply (insert type_non_empty_defined[of t])
  apply (auto)
done

lemma default_type [typing,intro]: "default t : t"
  apply (simp add:default_def)
  apply (rule type_non_empty_elim)
  apply (force intro:someI)
done

lemma someType_value: "\<exists> v. v : someType"
  apply (simp add:someType_def)
  apply (metis (lifting) Rep_UTYPE_elim type_rel_def)
done

declare Abs_UTYPE_inverse [simp]
declare Rep_UTYPE_inverse [simp]

lemma Abs_UTYPE_type [typing,intro]: "\<lbrakk> x :\<^sub>u t; \<D> x \<rbrakk> \<Longrightarrow> x : Abs_UTYPE t"
  by (metis (lifting) Rep_UTYPE_cases Rep_UTYPE_inverse UTYPES_def mem_Collect_eq type_rel_def)

definition embTYPE :: "'b::countable \<Rightarrow> 'a::VALUE UTYPE" where
"embTYPE t \<equiv> Abs_UTYPE (emb\<cdot>(Def t))"

definition prjTYPE :: "'a::VALUE UTYPE \<Rightarrow> 'b::{countable,cpo}" where
"prjTYPE t \<equiv> Undef (prj\<cdot>(Rep_UTYPE t))"

lemma embTYPE_inv [simp]:
  fixes x :: "'a::{countable,cpo}"
        and v :: "'b"
  assumes "v :\<^sub>u emb\<cdot>(Def x)" "\<D> v"
  shows "prjTYPE (embTYPE x :: 'b UTYPE) = x"
  apply (subgoal_tac "emb\<cdot>(Def x) \<in> UTYPES TYPE('b)")
  apply (simp add:prjTYPE_def embTYPE_def)
  apply (simp add:UTYPES_def)
  apply (rule_tac x="v" in exI)
  apply (simp add:assms)
done

(*
lemma prjTYPE_inv [simp]:
  fixes x :: "'a::{countable,cpo}"
        and v :: "'b"
  assumes "v :\<^sub>u emb\<cdot>(Def x)"
  shows "prjTYPE (embTYPE x :: 'b UTYPE) = x"
*)

subsection {* Syntax *}

abbreviation Tall :: "'a UTYPE \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Tall t P \<equiv> (\<forall>x. x : t \<longrightarrow> P x)"

abbreviation Tex :: "'a UTYPE \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Tex t P \<equiv> (\<exists>x. x : t \<and> P x)"

syntax
  "_Tall" :: "pttrn => 'a UTYPE => bool => bool" ("(3\<forall> _:_./ _)" [0, 0, 10] 10)
  "_Tex"  :: "pttrn => 'a UTYPE => bool => bool" ("(3\<exists> _:_./ _)" [0, 0, 10] 10)
  
translations
  "\<forall> x:A. P" == "CONST Tall A (%x. P)"
  "\<exists> x:A. P" == "CONST Tex A (%x. P)"

instantiation UTYPE :: (VALUE) DEFINED
begin

definition Defined_UTYPE :: "'a UTYPE \<Rightarrow> bool" where
"Defined_UTYPE t = (\<exists> v:t. \<D> v)"

instance ..
end

lemma Defined_UTYPE_elim [elim]:
  "\<lbrakk> \<D> t; \<And> x. \<lbrakk> x : t; \<D> x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:Defined_UTYPE_def)

subsection {* Universe *}

definition VALUE :: "'VALUE set" where
"VALUE = UNIV"

subsection {* Carrier Set *}

definition carrier :: "'VALUE UTYPE \<Rightarrow> 'VALUE set" where
"carrier t = {x . x : t}"

theorem carrier_non_empty :
"\<forall> t . carrier t \<noteq> {}"
apply (simp add: carrier_def type_non_empty)
done

theorem carrier_member :
"x : t \<Longrightarrow> x \<in> carrier t"
apply (simp add: carrier_def)
done

theorem carrier_intro :
"(x : t) = (x \<in> carrier t)"
apply (simp add: carrier_def)
done

theorem carrier_elim :
"(x \<in> carrier t) = (x : t)"
apply (simp add: carrier_def)
done

subsection {* Value Sets *}

definition set_type_rel :: "('VALUE) set \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool" where
"set_type_rel s t = (\<forall> x \<in> s . x : t)"

notation set_type_rel (infix ":\<subseteq>" 50)

theorem set_type_rel_empty [simp] :
"{} :\<subseteq> t"
apply (simp add: set_type_rel_def)
done

theorem set_type_rel_insert [simp] :
"(insert x s) :\<subseteq> t \<longleftrightarrow> (x : t \<and> s :\<subseteq> t)"
apply (simp add: set_type_rel_def)
done

end
