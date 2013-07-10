(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_value.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Shallow Polymorphic Values *}

theory utp_poly_value
imports 
  "../core/utp_value"
  "../core/utp_sorts"
  "../core/utp_event"
begin

default_sort type

text {* We first provided definedness instances for injectable types *}

typedef 'a::DEFINED ULIST = "{xs :: 'a list. \<forall>x\<in>set xs. \<D> x}"
  apply (rule_tac x="[]" in exI)
  apply (auto)
done

setup_lifting type_definition_ULIST

typedef 'a::DEFINED UFSET = "{xs :: 'a fset. \<forall>x\<in>\<^sub>fxs. \<D> x}"
  apply (rule_tac x="\<lbrace>\<rbrace>" in exI)
  apply (auto)
done

instantiation bool :: DEFINED
begin
definition "Defined_bool (x::bool) = True"
instance ..
end

lemma Defined_bool [defined]: "\<D> (x :: bool)" by (simp add:Defined_bool_def)

instantiation int :: DEFINED
begin
definition "Defined_int (x::int) = True"
instance ..
end

lemma Defined_int [defined]: "\<D> (x :: int)" by (simp add:Defined_int_def)

instantiation ULIST :: (DEFINED) DEFINED
begin
definition "Defined_ULIST (xs :: 'a ULIST) = True"
instance ..
end

lemma Defined_ULIST [defined]: "\<D> (xs :: ('a::DEFINED) ULIST)"
  by (simp add:Defined_ULIST_def)

instantiation list :: (DEFINED) DEFINED
begin
definition "Defined_list (xs :: 'a list) = (\<forall>x\<in>set xs. \<D> x)"
instance ..
end

lemma Defined_list [defined]: 
  "\<D> (xs :: ('a::DEFINED) list) = (\<forall>x\<in>set xs. \<D> x)"
  by (simp add:Defined_list_def)

instantiation UFSET :: (DEFINED) DEFINED
begin
definition "Defined_UFSET (xs :: 'a UFSET) = True"
instance ..
end

lemma Defined_UFET [defined]: 
  "\<D> (xs :: ('a::DEFINED UFSET))"
  by (simp add:Defined_UFSET_def)

subsection {* Polymorphic constants *}

text {* The following global constants serve to link the (polymorphic)
        HOL types which we would like to use in UTP predicates /
        expressions with the (also polymorphic) model type. Since we
        need range over these two type variables we cannot use a
        type-class, which are limited to one variable for reasons of
        guaranteeing decidability. Isabelle constants provide a way to
        directly create polymorphic functions, but a great deal of
        care is needed in using them. If associated definitions for
        the constants overlap chaos will ensue, as the type-system may
        not be able to disambiguate. FIXME: We need to defined some
        carefully thought rules to define what we can and can't have here. 
*}

consts 
  TypeU :: "'a itself \<Rightarrow> ('m :: VALUE) UTYPE"
  InjU  :: "'a \<Rightarrow> 'm :: VALUE"
  ProjU :: "'m :: VALUE \<Rightarrow> 'a"

text {* @{const TypeU} gives the corresponding UTP model type for a
        given HOL type, effectively performing an erasure. @{const
        InjU} injects a HOL value into a given model, and @{const
        ProjU} is the inverse. *}

text {* At this point we could add axioms about our consts, but since
        these are user checked I consider this too dangerous to the integrity of 
        the Isabelle/UTP model. Instead we create the following definition
        which encodes the required constraints over the constants, and will need
        to be added as assumptions to proofs about definitions which use these 
        constants. Without this we know nothing about the behaviour of constants. *}

definition TypeUSound :: "'a::DEFINED itself \<Rightarrow> 'm::VALUE itself \<Rightarrow> bool" where
"TypeUSound a m \<longleftrightarrow> (\<forall> x::'a. (InjU x :: 'm) :! TypeU a) 
                 \<and> (\<forall> x::'a. \<D> x \<longrightarrow> \<D> (InjU x :: 'm))
                 \<and> (\<forall> x::'a. ProjU (InjU x :: 'm) = x)"

(* Can we deal without: (\<forall> x :! TypeU a. (InjU (ProjU x :: 'a) :: 'm) = x) *)

syntax
  "_TYPEU"      :: "type => logic"  ("(1TYPEU/(1'(_')))")
  "_TYPEUSOUND" :: "type \<Rightarrow> type => logic"  ("(1TYPEUSOUND/(1'(_, _')))")

translations 
  "TYPEUSOUND('a, 'm)" == "CONST TypeUSound TYPE('a) TYPE('m)"
  "TYPEU('a)" == "CONST TypeU TYPE('a)"

text {* @{const TypeUSound} can be thought of as a two-parameter type
        class which stores the properties of the above polymorphic
        constants, namely that the given Isabelle type can be
        constructed under the given sort constraints. For instance we could
        declare @{term "TYPEUSOUND(int, 'm :: INT_SORT)"}. *}

text {* The following defs are carefully crafted, there must no
        overlap or \emph{potential} overlap.  That is to say it must
        not be possible to create a type class or instance which
        renders them undisambiguable.  Basically the LHS (value type)
        of @{const InjU} / @{const TypeU} should define the
        \emph{concrete type} which is to mapped. It can be parametric,
        but I can't conceive of a situation when this would be a class
        constraint -- I believe this would wreck the type system. This
        given, the RHS (model type) can then consist of only sort
        constraints. For instance for @{typ bool} the value type is of
        course @{typ bool} and the model type is @{typ "'m ::
        BOOL_SORT"}, since we need the ability to reconstruct the
        boolean in the model. Nevertheless these definitions
        \emph{are} extensible, but a great deal of care is required! *}

defs (overloaded)
  InjU_bool [simp]:  "InjU (x::bool) \<equiv> MkBool x"
  ProjU_bool [simp]: "ProjU (x::('a::BOOL_SORT)) \<equiv> DestBool x"
  TypeU_bool [simp]: "TypeU (x::bool itself) \<equiv> BoolType"

  InjU_int [simp]:  "InjU (x::int) \<equiv> MkInt x"
  ProjU_int [simp]: "ProjU (x::('a::INT_SORT)) \<equiv> DestInt x"
  TypeU_int [simp]: "TypeU (x::int itself) \<equiv> IntType"

  InjU_event [simp]:  "InjU (x::('m::EVENT_SORT) EVENT) \<equiv> (MkEvent x::'m)"
  ProjU_event [simp]: "ProjU (x::('m::EVENT_SORT)) \<equiv> DestEvent x"
  TypeU_event [simp]: "TypeU (x::('m::EVENT_SORT) EVENT itself) \<equiv> EventType::'m UTYPE"

  InjU_ULIST [simp]: 
    "InjU (xs::'a::DEFINED ULIST) \<equiv> MkList TYPEU('a) (map InjU (Rep_ULIST xs))"
  ProjU_ULIST [simp]:
    "ProjU (xs::('a::LIST_SORT)) \<equiv> Abs_ULIST (map ProjU (DestList xs))"
  TypeU_ULIST [simp]:
    "TypeU (x::('a ULIST) itself) \<equiv> ListType (TypeU TYPE('a))"

  InjU_list [simp]: "InjU (xs::'a list) \<equiv> MkList (TypeU (TYPE('a))) (map InjU xs)"
  ProjU_list [simp]: "ProjU (xs::('a::LIST_SORT)) \<equiv> map ProjU (DestList xs)"
  TypeU_list [simp]: "TypeU (x::('a list) itself) \<equiv> ListType (TypeU TYPE('a))"

  InjU_fset [simp]: "InjU (xs::'a fset) \<equiv> MkFSet (TypeU (TYPE('a))) (InjU `\<^sub>f xs)"
  ProjU_fset [simp]: "ProjU (xs::('a::FSET_SORT)) \<equiv> ProjU `\<^sub>f (DestFSet xs)"
  TypeU_fset [simp]: "TypeU (x::('a fset) itself) \<equiv> FSetType (TypeU TYPE('a))"  

subsection {* @{const TypeUSound} rules *}

lemma TypeUSound_intro [intro]:
  "\<lbrakk> \<And> (x :: 'a :: DEFINED). (InjU x :: 'm) :! TYPEU('a)
   ; \<And> (x :: 'a). (ProjU (InjU x :: 'm) = x) 
   ; \<And> x::'a. \<D> x \<Longrightarrow> \<D> (InjU x :: 'm) \<rbrakk> \<Longrightarrow>
   TYPEUSOUND('a, 'm :: VALUE)"
  by (simp add:TypeUSound_def)

lemma TypeUSound_InjU_type [typing]:
  fixes x :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "(InjU x :: 'm) : TYPEU('a)"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_InjU_defined [defined]:
  fixes x :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)" "\<D> x"
  shows "\<D> (InjU x :: 'm)"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_InjU_inv [simp]:
  fixes x :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "ProjU (InjU x :: 'm) = x"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_InjU_inj [intro]:
  fixes x y :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)" "(InjU x :: 'm) = InjU y"
  shows "x = y"
  using assms
  by (simp add:TypeUSound_def, metis)


(*
lemma TypeUSound_ProjU_inv [simp]:
  fixes x :: "'m :: VALUE"
  assumes "TYPEUSOUND('a :: DEFINED, 'm :: VALUE)" "x :! TYPEU('a)"
  shows "(InjU (ProjU x :: 'a) :: 'm) = x"
  using assms by (auto simp add:TypeUSound_def)
*)

subsection {* Some basic instantiations *}

text {* The following instantiations make use of the sort constraints
        to discharge the requirements of @{const TypeUSound}. *}

lemma TypeUSound_bool [typing]: "TYPEUSOUND(bool, 'm :: BOOL_SORT)"
  by (auto simp add:TypeUSound_def typing defined)

lemma TypeUSound_int [typing]: "TYPEUSOUND(int, 'm :: INT_SORT)"
  by (auto simp add:TypeUSound_def typing defined)

(*
lemma TypeUSound_ULIST [typing]: 
  "\<lbrakk> (TYPEU('a :: DEFINED) :: 'm UTYPE) \<in> ListPerm; TYPEUSOUND('a, 'm) \<rbrakk> 
     \<Longrightarrow> TYPEUSOUND('a ULIST, 'm :: LIST_SORT)"
  apply (rule)
  apply (simp_all)
*)

(*
lemma TypeUSound_list [typing]: 
  "\<lbrakk> (TYPEU('a :: DEFINED) :: 'm UTYPE) \<in> ListPerm; TYPEUSOUND('a, 'm) \<rbrakk> 
     \<Longrightarrow> TYPEUSOUND('a list, 'm :: LIST_SORT)"
  apply (rule)
  apply (simp_all)
  apply (rule MkList_type)
  apply (simp)
  apply (auto simp add:dcarrier_def TypeUSound_def)[1]
  apply (rule typing, auto)
  apply (subgoal_tac "set (map InjU x) \<subseteq> dcarrier (TYPEU('a) :: 'm UTYPE)")
  apply (auto simp add:comp_def)
done

lemma TypeUSound_fset [typing]: 
  "\<lbrakk> (TYPEU('a) :: 'm UTYPE) \<in> FSetPerm; TYPEUSOUND('a, 'm) \<rbrakk> 
     \<Longrightarrow> TYPEUSOUND('a fset, 'm :: FSET_SORT)"
  apply (simp add:dcarrier_def TypeUSound_def)
  apply (rule)
  apply (clarify)
  apply (rule typing)
  apply (force)
  apply (force)
  apply (clarify)
  apply (subgoal_tac "\<langle>InjU `\<^sub>f x\<rangle>\<^sub>f \<subseteq> dcarrier (TYPEU('a) :: 'm UTYPE)")
  apply (auto simp add:image_def)
done

lemma TypeUSound_Event [typing]:
  "TYPEUSOUND('m EVENT, 'm :: EVENT_SORT)"
  by (auto simp add:typing)
*)

end
