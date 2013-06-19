(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_value.thy                                                        *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Abstract Values *}

theory utp_value
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

subsection {* The @{term "VALUE"} class *}

text {* We fix a notion of definedness from the start. This is because control
variables, such as @{term "ok"}, must always be defined but we can't assume that
all values are. *}

class DEFINED =
  fixes Defined   :: "'a \<Rightarrow> bool" ("\<D>")

text {* The @{term "VALUE"} class introduces the typing relation with an arbitrary
value sort, and the type sort given by @{term "udom"}, the Universal Domain from
HOLCF. Specifically the type sort must be injectable into udom, which has the
cardinality of the continuum and can be populated using the domain package from
HOLCF. We expect that most type sorts will be @{term "countable"}. 

We require that the typing relation have at least one type with at least one defined
value.
 *}

class VALUE = DEFINED +
  fixes   utype_rel :: "'a \<Rightarrow> nat \<Rightarrow> bool" (infix ":\<^sub>u" 50)
  assumes utype_nonempty: "\<exists> t v. v :\<^sub>u t \<and> \<D> v"

default_sort VALUE

subsection {* The @{term "UTYPE"} type *}

text {* The type @{term "UTYPE"} consists of the set of types which, according
to the typing relation, have at least one defined value. This set should be
more-or-less isomorphic to the underlying type sort in the user's value
model. *}

definition "UTYPES (x::'a itself) = {t. \<exists> v :: 'a. v :\<^sub>u t \<and> \<D> v}"

typedef 'VALUE UTYPE = "UTYPES TYPE('VALUE)"
  apply (insert utype_nonempty)
  apply (auto simp add:UTYPES_def)
done

declare Rep_UTYPE [simp]
declare Abs_UTYPE_inverse [simp]
declare Rep_UTYPE_inverse [simp]

lemma Rep_UTYPE_intro [intro!]:
  "Rep_UTYPE x = Rep_UTYPE y \<Longrightarrow> x = y"
  by (simp add:Rep_UTYPE_inject)

lemma Rep_UTYPE_elim [elim]:
  "\<lbrakk> \<And> v\<Colon>'VALUE. \<lbrakk> v :\<^sub>u Rep_UTYPE (t :: 'VALUE UTYPE); \<D> v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (insert Rep_UTYPE[of t])
  apply (auto simp add:UTYPES_def)
done

instantiation UTYPE :: (VALUE) countable
begin
instance
  apply (intro_classes)
  apply (rule_tac x="Rep_UTYPE" in exI)
  apply (metis Rep_UTYPE_inverse injI)
done
end

(*  
class VALUE_SUBTYPES = VALUE +
  fixes   usubtype_lattice :: "'a itself \<Rightarrow> nat lattice" 
  assumes carrier_UTYPES: "carrier (Rep_lattice (usubtype_lattice TYPE('a))) = UTYPES TYPE('a)"

instantiation UTYPE :: (VALUE_SUBTYPES) order
begin

definition less_eq_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" where
"less_eq_UTYPE s t \<longleftrightarrow> le (Rep_lattice (usubtype_lattice TYPE('a))) (Rep_UTYPE s) (Rep_UTYPE t)"

definition less_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" where
"less_UTYPE x y \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)"

instance
  apply (intro_classes)
  apply (simp add:less_UTYPE_def)
  apply (simp_all add: less_eq_UTYPE_def)
  apply (metis Rep_UTYPE carrier_UTYPES ltype.le_refl)
  apply (metis (no_types) Rep_UTYPE carrier_UTYPES ltype.le_trans)
  apply (metis Rep_UTYPE Rep_UTYPE_intro carrier_UTYPES ltype.le_antisym)
done
end

instantiation UTYPE :: (VALUE_SUBTYPES) lattice
begin

definition sup_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> 'a UTYPE" where
"sup_UTYPE s t = Abs_UTYPE (join (Rep_lattice (usubtype_lattice TYPE('a))) (Rep_UTYPE s) (Rep_UTYPE t))"

definition inf_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> 'a UTYPE" where
"inf_UTYPE s t = Abs_UTYPE (meet (Rep_lattice (usubtype_lattice TYPE('a))) (Rep_UTYPE s) (Rep_UTYPE t))"

instance
  apply (intro_classes)
  apply (simp_all add:inf_UTYPE_def less_eq_UTYPE_def)
  apply (smt Abs_UTYPE_inverse Rep_UTYPE carrier_UTYPES ltype.meet_closed ltype.meet_left)
  apply (smt Abs_UTYPE_inverse Rep_UTYPE carrier_UTYPES ltype.meet_closed ltype.meet_right)
  apply (smt Abs_UTYPE_inverse Rep_UTYPE carrier_UTYPES ltype.meet_closed ltype.meet_le)
  apply (smt Abs_UTYPE_inverse Rep_UTYPE carrier_UTYPES ltype.join_closed ltype.join_left utp_value.sup_UTYPE_def)
  apply (metis (no_types) Abs_UTYPE_inverse Rep_UTYPE carrier_UTYPES ltype.join_closed ltype.join_right utp_value.sup_UTYPE_def)
  apply (metis (no_types) Abs_UTYPE_inverse Rep_UTYPE carrier_UTYPES ltype.join_closed ltype.join_le utp_value.sup_UTYPE_def)
done
end
*)

instantiation UTYPE :: (VALUE) linorder 
begin

definition less_eq_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" where
"less_eq_UTYPE x y = (Rep_UTYPE x \<le> Rep_UTYPE y)"

definition less_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" where
"less_UTYPE x y = (Rep_UTYPE x < Rep_UTYPE y)"

instance
  apply (intro_classes)
  apply (auto simp add:less_eq_UTYPE_def less_UTYPE_def)
done
end


text {* We derive a typing relation using @{term "UTYPE"}, which has more 
useful properties than the underlying @{term "utype_rel"}. *}

definition type_rel :: "'VALUE \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool" (infix ":" 50) where
"x : t \<longleftrightarrow> x :\<^sub>u Rep_UTYPE t"

definition dtype_rel :: "'VALUE \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool" (infix ":!" 50) where
"x :! t \<longleftrightarrow> x : t \<and> \<D> x"

definition default :: "'VALUE UTYPE \<Rightarrow> 'VALUE" where
"default t \<equiv> SOME x. x : t \<and> \<D> x"

definition someType :: "'VALUE UTYPE" where
"someType \<equiv> SOME t. \<exists>x. x : t"

definition monotype :: "'VALUE UTYPE \<Rightarrow> bool" where
"monotype t \<longleftrightarrow> (\<forall> x a. x :! t \<and> x :! a \<longrightarrow> a = t)"

definition type_of :: "'VALUE \<Rightarrow> 'VALUE UTYPE" ("\<tau>") where
"type_of x = (THE t. x : t)"

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

lemma dtype_non_empty: "\<exists> x. x :! t"
  apply (auto simp add:dtype_rel_def type_rel_def)
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
  apply (smt tfl_some)
done

lemma default_defined [defined]: "\<D> (default t)"
  apply (simp add:default_def)
  apply (metis (lifting) some_eq_ex type_non_empty_defined)
done

lemma someType_value: "\<exists> v. v : someType"
  apply (simp add:someType_def)
  apply (metis (lifting) Rep_UTYPE_elim type_rel_def)
done

lemma type_of_monotype: "\<lbrakk> x :! t; monotype t \<rbrakk> \<Longrightarrow> \<tau> x = t"
  apply (unfold type_of_def monotype_def)
  apply (rule the_equality)
  apply (auto simp add:dtype_rel_def)
done

lemma Abs_UTYPE_type [typing,intro]: 
  "\<lbrakk> x :\<^sub>u t; \<D> x \<rbrakk> \<Longrightarrow> x : Abs_UTYPE t"
  by (metis (lifting) Rep_UTYPE_cases Rep_UTYPE_inverse UTYPES_def mem_Collect_eq type_rel_def)

lemma dtype_relI [intro]: "\<lbrakk> x : t; \<D> x \<rbrakk> \<Longrightarrow> x :! t"
  by (simp add:dtype_rel_def)

lemma dtype_relE [elim]: "\<lbrakk> x :! t; \<lbrakk> x : t; \<D> x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:dtype_rel_def)

definition embTYPE :: "'b::countable \<Rightarrow> 'a::VALUE UTYPE" where
"embTYPE t \<equiv> Abs_UTYPE (to_nat t)"

definition prjTYPE :: "'a::VALUE UTYPE \<Rightarrow> 'b::{countable}" where
"prjTYPE t \<equiv> from_nat (Rep_UTYPE t)"

lemma embTYPE_inv [simp]:
  fixes t :: "'a::countable"
    and v :: "'b"
  assumes "v :\<^sub>u to_nat t" "\<D> v"
  shows "prjTYPE (embTYPE t :: 'b UTYPE) = t"
  apply (subgoal_tac "to_nat t \<in> UTYPES TYPE('b)")
  apply (simp add:embTYPE_def prjTYPE_def)
  apply (simp add:UTYPES_def)
  apply (rule_tac x="v" in exI)
  apply (simp add:assms)
done

subsection {* Typing operator syntax *}

abbreviation Tall :: "'a UTYPE \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Tall t P \<equiv> (\<forall>x. x : t \<longrightarrow> P x)"

abbreviation Tex :: "'a UTYPE \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Tex t P \<equiv> (\<exists>x. x : t \<and> P x)"

abbreviation DTex :: "'a UTYPE \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "DTex t P \<equiv> (\<exists>x. x :! t \<and> P x)"

abbreviation DTall :: "'a UTYPE \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "DTall t P \<equiv> (\<forall>x. x :! t \<longrightarrow> P x)"

syntax
  "_Tall" :: "pttrn => 'a UTYPE => bool => bool" ("(3\<forall> _:_./ _)" [0, 0, 10] 10)
  "_Tex"  :: "pttrn => 'a UTYPE => bool => bool" ("(3\<exists> _:_./ _)" [0, 0, 10] 10)
  "_DTall" :: "pttrn => 'a UTYPE => bool => bool" ("(3\<forall> _:!_./ _)" [0, 0, 10] 10)
  "_DTex"  :: "pttrn => 'a UTYPE => bool => bool" ("(3\<exists> _:!_./ _)" [0, 0, 10] 10)

  
translations
  "\<forall> x:A. P" == "CONST Tall A (%x. P)"
  "\<exists> x:A. P" == "CONST Tex A (%x. P)"
  "\<forall> x:!A. P" == "CONST DTall A (%x. P)"
  "\<exists> x:!A. P" == "CONST DTex A (%x. P)"


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

definition dcarrier :: "'VALUE UTYPE \<Rightarrow> 'VALUE set" where
"dcarrier t = {x . x : t \<and> \<D> x}"

lemma dcarrierI [intro]: 
  "\<lbrakk> x : a; \<D> x \<rbrakk> \<Longrightarrow> x \<in> dcarrier a"
  by (simp add:dcarrier_def)

lemma dcarrier_carrier:
  "dcarrier a \<subseteq> carrier a"
  by (auto simp add:carrier_def dcarrier_def)

lemma dcarrier_dtype [typing]:
  "x \<in> dcarrier a \<Longrightarrow> x :! a"
  by (auto simp add:dcarrier_def)

lemma dtype_as_dcarrier:
  "x :! a \<longleftrightarrow> x \<in> dcarrier a"
  by (auto simp add:dcarrier_def dtype_rel_def)

lemma dcarrier_type [typing]:
  "x \<in> dcarrier a \<Longrightarrow> x : a"
  by (auto simp add:dcarrier_def)

lemma dcarrier_defined [defined]:
  "x \<in> dcarrier a \<Longrightarrow> \<D> x"
  by (auto simp add:dcarrier_def)

subsection {* Function type sets *}

text {* In several models we don't necessarily want to give a complete account to functions
        so these two sets give an account to unary and binary HOL functions in the UTP *}

definition "FUNC1 a b   = {f. \<forall>x:!a. f x :! b}"

lemma FUNC11I [intro, typing]: 
  "\<lbrakk> \<And> x. x :! a \<Longrightarrow> f x :! b \<rbrakk> \<Longrightarrow> f \<in> FUNC1 a b"
  by (simp add:FUNC1_def)

definition "FUNC2 a b c = {f. \<forall>x:!a. \<forall>y:!b. f x y :! c}"

lemma FUNC2I [intro, typing]: 
  "\<lbrakk> \<And> x y. \<lbrakk> x :! a; y :! b \<rbrakk> \<Longrightarrow> f x y :! c \<rbrakk> \<Longrightarrow> f \<in> FUNC2 a b c"
  by (simp add:FUNC2_def)

end
