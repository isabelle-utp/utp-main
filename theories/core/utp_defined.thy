(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_defined.thy                                                      *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 4 September 2014 *)

header {* Definedness *}

theory utp_defined
imports "../utp_common"
begin

text {* \fixme{Perhaps move this theory into the theory root folder.} *}

default_sort type

text {*
  We introduce a generic notion of definedness in this theory. It does not
  exclusively apply to model values but any kind of mathematical object in
  the mechanisation where definedness is applicable and useful.
*}

subsection {* Type class @{text DEFINED} *}

text {*
  The class @{text DEFINED} introduces a definedness predicates for some HOL
  type. Initially, there are no constraints on that predicate.
*}

class DEFINED =
  fixes defined :: "'a \<Rightarrow> bool" ("\<D>")
begin

subsubsection {* Constants *}

text {* Carrier for defined values. *}

definition DEFINED :: "'a set" where
"DEFINED = {x. \<D> x}"

text {* Carrier for undefined values. *}

definition UNDEFINED :: "'a set" where
"UNDEFINED = {x. \<not> \<D> x}"

subsubsection {* Operators *}

text {* Domain and range of a function according to definedness. *}

definition Dom :: "('a \<Rightarrow> 'b::DEFINED) \<Rightarrow> 'a set" where
"Dom f = {x . \<D> (f x)}"

definition Ran :: "('a \<Rightarrow> 'b::DEFINED) \<Rightarrow> 'b set" where
"Ran f = {f x | x . \<D> (f x)}"

subsubsection {* Theorems *}

theorem DEFINED_member [iff] :
"x \<in> DEFINED \<longleftrightarrow> \<D> x"
apply (unfold DEFINED_def)
apply (simp)
done

theorem UNDEFINED_member [iff] :
"x \<in> UNDEFINED \<longleftrightarrow> \<not> \<D> x"
apply (unfold UNDEFINED_def)
apply (simp)
done

theorem DEFINED_UNDEFINED_UNIV :
"DEFINED \<union> UNDEFINED = UNIV"
apply (rule Set.set_eqI)
apply (simp)
done

theorem app_defined [defined] :
"x \<in> Dom f \<Longrightarrow> \<D> (f x)"
apply (unfold Dom_def)
apply (simp)
done
end

subsection {* Type class @{text DEFINED_NE} *}

text {*
  The class @{text DEFINED_NE} carries the additional assumption that there
  must be at least one defined value.
*}

class DEFINED_NE = DEFINED +
  assumes defined_nonempty : "\<exists> x . \<D> x"

subsection {* Type class @{text DEFINED_TOTAL} *}

text {*
  The class @{text DEFINED_TOTAL} requires \emph{all} values are defined.
*}

class DEFINED_TOTAL = DEFINED +
  assumes defined_total [defined] : "\<D> x"

instance DEFINED_TOTAL \<subseteq> DEFINED_NE
apply (intro_classes)
apply (rule_tac x = "undefined" in exI)
apply (metis defined_total)
done

subsection {* Instantiations *}

text {*
  We instantiate definedness for HOL types that we inject into the UTP model.
*}

text {* \fixme{What about the type @{type fun}? Is it not injected?} *}

paragraph {* Definedness of type @{type unit} *}

instantiation unit :: DEFINED_TOTAL
begin
definition defined_unit :: "unit \<Rightarrow> bool" where
"\<D> (x :: unit) = True"
instance
  by (intro_classes, unfold defined_unit_def, simp)

theorem defined_unit [defined] :
"\<D> (x :: unit)"
apply (simp add: defined_unit_def)
done
end

paragraph {* Definedness of type @{type bool} *}

instantiation bool :: DEFINED_TOTAL
begin
definition defined_bool :: "bool \<Rightarrow> bool" where
"\<D> (x :: bool) = True"
instance
  by (intro_classes, unfold defined_bool_def, simp)

theorem defined_bool [defined] :
"\<D> (x :: bool)"
apply (simp add: defined_bool_def)
done
end

paragraph {* Definedness of type @{type nat} *}

instantiation nat :: DEFINED_TOTAL
begin
definition defined_nat :: "nat \<Rightarrow> bool" where
"\<D> (x :: nat) = True"
instance
  by (intro_classes, unfold defined_nat_def, simp)

theorem defined_nat [defined] :
"\<D> (x :: nat)"
apply (simp add: defined_nat_def)
done
end

paragraph {* Definedness of type @{type int} *}

instantiation int :: DEFINED_TOTAL
begin
definition defined_int :: "int \<Rightarrow> bool" where
"\<D> (x :: int) = True"
instance
  by (intro_classes, unfold defined_int_def, simp)

theorem defined_int [defined] :
"\<D> (x :: int)"
apply (simp add: defined_int_def)
done
end

paragraph {* Definedness of type @{type real} *}

instantiation real :: DEFINED_TOTAL
begin
definition defined_real :: "real \<Rightarrow> bool" where
"\<D> (x :: real) = True"
instance
  by (intro_classes, unfold defined_real_def, simp)

theorem defined_real [defined] :
"\<D> (x :: real)"
apply (simp add: defined_real_def)
done
end

paragraph {* Definedness of type @{type char} *}

instantiation char :: DEFINED_TOTAL
begin
definition defined_char :: "char \<Rightarrow> bool" where
"\<D> (x :: char) = True"
instance
  by (intro_classes, unfold defined_char_def, simp)

theorem defined_char [defined] :
"\<D> (x :: char)"
apply (simp add: defined_char_def)
done
end

paragraph {* Definedness of type @{type prod} *}

instantiation prod :: (DEFINED, DEFINED) DEFINED
begin
definition defined_prod :: "'a \<times> 'b \<Rightarrow> bool" where
"defined_prod = (\<lambda> (x, y) . \<D> x \<and> \<D> y)"
instance by (intro_classes)

theorem defined_prod [defined] :
"\<D> (x, y) \<longleftrightarrow> \<D> x \<and> \<D> y"
apply (simp add: defined_prod_def)
done
end

instance prod :: (DEFINED_NE, DEFINED_NE) DEFINED_NE
apply (intro_classes)
apply (rule_tac x = "(SOME x . \<D> x, SOME y . \<D> y)" in exI)
apply (unfold defined_prod)
apply (metis defined_nonempty someI)
done

instance prod :: (DEFINED_TOTAL, DEFINED_TOTAL) DEFINED_TOTAL
apply (intro_classes)
apply (induct_tac x)
apply (simp add: defined)
done

paragraph {* Definedness of type @{type sum} *}

instantiation sum :: (DEFINED, DEFINED) DEFINED
begin
primrec defined_sum :: "'a + 'b \<Rightarrow> bool" where
"defined_sum (Inl (x :: 'a)) = \<D> x" |
"defined_sum (Inr (y :: 'b)) = \<D> y"
instance by (intro_classes)

declare defined_sum.simps [simp del]
declare defined_sum.simps [defined]
end

instance sum :: (DEFINED_NE, DEFINED_NE) DEFINED_NE
apply (intro_classes)
apply (rule_tac x = "Inl (SOME x . \<D> x)" in exI)
apply (simp add: defined)
apply (metis defined_nonempty someI)
done

instance sum :: (DEFINED_TOTAL, DEFINED_TOTAL) DEFINED_TOTAL
apply (intro_classes)
apply (induct_tac x)
apply (simp_all add: defined)
done

paragraph {* Definedness of type @{type list} *}

instantiation list :: (DEFINED) DEFINED_NE
begin
definition defined_list :: "'a list \<Rightarrow> bool" where
"\<D> (xs :: 'a list) = (\<forall> x \<in> set xs . \<D> x)"
instance
apply (intro_classes)
apply (unfold defined_list_def)
apply (rule_tac x = "[]" in exI)
apply (simp)
done

theorem defined_list [defined] :
"\<D> (xs :: 'a list) \<longleftrightarrow> (\<forall>x \<in> set xs . \<D> x)"
apply (simp add: defined_list_def)
done
end

instance list :: (DEFINED_TOTAL) DEFINED_TOTAL
apply (intro_classes)
apply (simp_all add: defined)
done

paragraph {* Definedness of type @{type set} *}

instantiation set :: (DEFINED) DEFINED_NE
begin
definition defined_set :: "'a set \<Rightarrow> bool" where
"\<D> (xs :: 'a set) = (\<forall> x \<in> xs . \<D> x)"
instance
apply (intro_classes)
apply (unfold defined_set_def)
apply (rule_tac x = "{}" in exI)
apply (simp)
done

theorem defined_set [defined] :
"\<D> (xs :: 'a set) \<longleftrightarrow> (\<forall>x \<in> xs . \<D> x)"
apply (simp add: defined_set_def)
done
end

instance set :: (DEFINED_TOTAL) DEFINED_TOTAL
apply (intro_classes)
apply (simp_all add: defined)
done

paragraph {* Definedness of type @{type fset} *}

instantiation fset :: (DEFINED) DEFINED_NE
begin
definition defined_fset :: "'a fset \<Rightarrow> bool" where
"\<D> (xs :: 'a fset) = (\<forall> x \<in>\<^sub>f xs . \<D> x)"
instance
apply (intro_classes)
apply (unfold defined_fset_def)
apply (rule_tac x = "\<lbrace>\<rbrace>" in exI)
apply (simp)
done

theorem defined_fset [defined] :
"\<D> (xs :: 'a fset) \<longleftrightarrow> (\<forall>x \<in>\<^sub>f xs . \<D> x)"
apply (simp add: defined_fset_def)
done
end

instance fset :: (DEFINED_TOTAL) DEFINED_TOTAL
apply (intro_classes)
apply (simp_all add: defined)
done
end
