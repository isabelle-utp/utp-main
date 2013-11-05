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
  "../types/utp_list"
  "../types/utp_fset"
  "../types/utp_uset"
begin

default_sort type

subsection {* Theorem Attributes *}

ML {*
  structure erasure =
    Named_Thms (val name = @{binding erasure} val description = "erasure theorems")
*}

setup erasure.setup

text {* We first provided definedness instances for injectable types *}

instantiation bool :: DEFINED_NE
begin
definition "Defined_bool (x::bool) = True"
instance 
  by (intro_classes, auto simp add:Defined_bool_def)
end

lemma Defined_bool [defined]: "\<D> (x :: bool)" by (simp add:Defined_bool_def)

instantiation int :: DEFINED_NE
begin
definition "Defined_int (x::int) = True"
instance
  by (intro_classes, auto simp add:Defined_int_def)
end

lemma Defined_int [defined]: "\<D> (x :: int)" by (simp add:Defined_int_def)

instantiation real :: DEFINED_NE
begin
definition "Defined_real (x::real) = True"
instance
  by (intro_classes, auto simp add:Defined_real_def)
end

lemma Defined_real [defined]: "\<D> (x :: real)" by (simp add:Defined_real_def)

instantiation list :: (DEFINED) DEFINED
begin
definition "Defined_list (xs :: 'a list) = (\<forall>x\<in>set xs. \<D> x)"
instance ..
end

lemma Defined_list [defined]: 
  "\<D> (xs :: ('a::DEFINED) list) = (\<forall>x\<in>set xs. \<D> x)"
  by (simp add:Defined_list_def)

instantiation prod :: (DEFINED, DEFINED) DEFINED
begin

definition "Defined_prod = (\<lambda>(x, y). \<D> x \<and> \<D> y)"

instance ..
end

lemma Defined_prod [defined]:
  "\<D> (x, y) \<longleftrightarrow> \<D> x \<and> \<D> y"
  by (auto simp add:Defined_prod_def)

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
"TypeUSound a m \<longleftrightarrow> (\<forall> x::'a. (InjU x :: 'm) : TypeU a) 
                 \<and> (\<forall> x::'a. \<D> x \<longrightarrow> \<D> (InjU x :: 'm))
                 \<and> (\<forall> x::'m. x :! TypeU a \<longrightarrow> \<D> (ProjU x :: 'a))
                 \<and> (\<forall> x::'a. ProjU (InjU x :: 'm) = x)
                 \<and> (\<forall> x :! TypeU a. (InjU (ProjU x :: 'a) :: 'm) = x)"

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

ML {*
  structure inju =
    Named_Thms (val name = @{binding inju} val description = "inju theorems")
*}

setup inju.setup

defs (overloaded)
  InjU_bool [inju]:  "InjU (x::bool) \<equiv> MkBool x"
  ProjU_bool [inju]: "ProjU (x::('a::BOOL_SORT)) \<equiv> DestBool x"
  TypeU_bool [simp]: "TypeU (x::bool itself) \<equiv> BoolType"

  InjU_int [inju]:  "InjU (x::int) \<equiv> MkInt x"
  ProjU_int [inju]: "ProjU (x::('a::INT_SORT)) \<equiv> DestInt x"
  TypeU_int [simp]: "TypeU (x::int itself) \<equiv> IntType"

  InjU_real [inju]:  "InjU (x::real) \<equiv> MkReal x"
  ProjU_real [inju]: "ProjU (x::('a::REAL_SORT)) \<equiv> DestReal x"
  TypeU_real [simp]: "TypeU (x::real itself) \<equiv> RealType"

  InjU_event [inju]:  "InjU (x::('m::EVENT_SORT) EVENT) \<equiv> (MkEvent x::'m)"
  ProjU_event [inju]: "ProjU (x::('m::EVENT_SORT)) \<equiv> DestEvent x"
  TypeU_event [simp]: "TypeU (x::('m::EVENT_SORT) EVENT itself) \<equiv> EventType::'m UTYPE"

  InjU_ULIST [inju]: 
    "InjU (xs::'a::DEFINED ULIST) \<equiv> MkList TYPEU('a) (map InjU (Rep_ULIST xs))"
  ProjU_ULIST [inju]:
    "ProjU (xs::('a::LIST_SORT)) \<equiv> Abs_ULIST (map ProjU (DestList xs))"
  TypeU_ULIST [simp]:
    "TypeU (x::('a ULIST) itself) \<equiv> ListType (TypeU TYPE('a))"

  InjU_UFSET [inju]: 
    "InjU (xs::'a::DEFINED UFSET) \<equiv> MkFSet TYPEU('a) (InjU `\<^sub>f (Rep_UFSET xs))"
  ProjU_UFSET [inju]:
    "ProjU (xs::('a::FSET_SORT)) \<equiv> Abs_UFSET (ProjU `\<^sub>f (DestFSet xs))"
  TypeU_UFSET [simp]:
    "TypeU (x::('a UFSET) itself) \<equiv> FSetType (TypeU TYPE('a))"

  InjU_USET [inju]: 
    "InjU (xs::'a::DEFINED USET) \<equiv> MkSet TYPEU('a) (InjU ` (Rep_USET xs))"
  ProjU_USET [inju]:
    "ProjU (xs::('a::SET_SORT)) \<equiv> Abs_USET (ProjU ` (DestSet xs))"
  TypeU_USET [simp]:
    "TypeU (x::('a USET) itself) \<equiv> SetType (TypeU TYPE('a))"

  InjU_list [inju]: "InjU (xs::'a list) \<equiv> MkList (TypeU (TYPE('a))) (map InjU xs)"
  ProjU_list [inju]: "ProjU (xs::('a::LIST_SORT)) \<equiv> map ProjU (DestList xs)"
  TypeU_list [simp]: "TypeU (x::('a list) itself) \<equiv> ListType (TypeU TYPE('a))"

  InjU_fset [inju]: "InjU (xs::'a fset) \<equiv> MkFSet (TypeU (TYPE('a))) (InjU `\<^sub>f xs)"
  ProjU_fset [inju]: "ProjU (xs::('a::FSET_SORT)) \<equiv> ProjU `\<^sub>f (DestFSet xs)"
  TypeU_fset [simp]: "TypeU (x::('a fset) itself) \<equiv> FSetType (TypeU TYPE('a))"  

subsection {* @{const TypeUSound} rules *}

lemma TypeUSound_intro [intro]:
  "\<lbrakk> \<And> (x :: 'a :: DEFINED). (InjU x :: 'm) : TYPEU('a)
   ; \<And> (x :: 'a). (ProjU (InjU x :: 'm) = x) 
   ; \<And> x::'a. \<D> x \<Longrightarrow> \<D> (InjU x :: 'm)
   ; \<And> x::'m. x :! TYPEU('a) \<Longrightarrow> \<D> (ProjU x :: 'a)
   ; \<And> x. x :! TYPEU('a) \<Longrightarrow> (InjU (ProjU x :: 'a) :: 'm) = x \<rbrakk> \<Longrightarrow>
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

lemma TypeUSound_InjU_dtype [typing]:
  fixes x :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)" "\<D> x"
  shows "(InjU x :: 'm) :! TYPEU('a)"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_ProjU_defined [defined]:
  fixes x :: "'m :: VALUE"
  assumes "TYPEUSOUND('a :: DEFINED, 'm)" "x :! TYPEU('a)"
  shows "\<D> (ProjU x :: 'a)"
  using assms by (simp add:TypeUSound_def)

lemma TypeUSound_InjU_inv [simp]:
  fixes x :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "ProjU (InjU x :: 'm) = x"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_InjU_inv_pf [simp]:
  fixes x :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "(ProjU \<circ> (InjU :: 'a \<Rightarrow> 'm)) = id"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_InjU_inv_fimage [simp]:
  fixes x :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "ProjU `\<^sub>f (InjU :: 'a \<Rightarrow> 'm) `\<^sub>f xs = xs"
  using assms 
  apply (auto)
  apply (metis TypeUSound_InjU_inv image_iff)
done

lemma TypeUSound_InjU_inj [intro]:
  fixes x y :: "'a :: DEFINED"
  assumes "TYPEUSOUND('a, 'm :: VALUE)" "(InjU x :: 'm) = InjU y"
  shows "x = y"
  using assms
  by (simp add:TypeUSound_def, metis)

lemma TypeUSound_ProjU_inv [simp]:
  fixes x :: "'m :: VALUE"
  assumes "TYPEUSOUND('a :: DEFINED, 'm :: VALUE)" "x :! TYPEU('a)"
  shows "(InjU (ProjU x :: 'a) :: 'm) = x"
  using assms by (auto simp add:TypeUSound_def)

subsection {* Some basic instantiations *}

text {* The following instantiations make use of the sort constraints
        to discharge the requirements of @{const TypeUSound}. *}

lemma TypeUSound_bool [typing]: "TYPEUSOUND(bool, 'm :: BOOL_SORT)"
  by (force simp add: typing defined inju)

lemma TypeUSound_int [typing]: "TYPEUSOUND(int, 'm :: INT_SORT)"
  by (force simp add: typing defined inju)

lemma TypeUSound_real [typing]: "TYPEUSOUND(real, 'm :: REAL_SORT)"
  by (force simp add: typing defined inju)

lemma TypeUSound_Event [typing]:
  "TYPEUSOUND('m EVENT, 'm :: EVENT_SORT)"
  by (auto simp add:typing defined inju)

lemma map_InjU_ProjU [simp]:
  assumes "TYPEUSOUND('a :: DEFINED, 'm::VALUE)" "set xs \<subseteq> dcarrier TYPEU('a)"
  shows "map ((InjU :: 'a \<Rightarrow> 'm) \<circ> ProjU) xs = xs"
  apply (simp add:map_eq_conv[where g="id",simplified])
  apply (metis TypeUSound_ProjU_inv assms dtype_as_dcarrier set_mp)
done

lemma InjU_MkEvent [simp]: "InjU = MkEvent"
  by (auto simp add:inju)

lemma ProjU_DestEvent [simp]: "ProjU = DestEvent"
  by (auto simp add:inju)

lemma TypeUSound_ULIST [typing]: 
  assumes 
    "(TYPEU('a :: DEFINED) :: 'm UTYPE) \<in> ListPerm" "TYPEUSOUND('a, 'm)"
  shows "TYPEUSOUND('a ULIST, 'm :: LIST_SORT)"
proof -

  from assms
  have "\<And> x::'a ULIST. MkList TYPEU('a) (map InjU (Rep_ULIST x)) :! (ListType TYPEU('a) :: 'm UTYPE)"
    apply (rule_tac typing)
    apply (simp)
    apply (auto simp add:dcarrier_def intro:typing)
    apply (metis TypeUSound_InjU_defined ULIST_elems_defined)
  done

  with assms show ?thesis
    apply (rule_tac TypeUSound_intro)
    apply (auto simp add:inju)
    apply (subgoal_tac "set (map InjU (Rep_ULIST x)) \<subseteq> (dcarrier TYPEU('a) :: 'm set)")
    apply (simp)
    apply (auto)
    apply (metis TypeUSound_InjU_dtype ULIST_elems_defined dtype_as_dcarrier)
    apply (auto simp add:defined)
    apply (subgoal_tac "\<forall> y::'a \<in> set (map ProjU (DestList x)). \<D> y")
    defer
    apply (auto simp add:defined)[1]
    apply (rule defined)
    apply (simp)
    apply (metis ListType_witness MkList_inv dcarrier_dtype set_mp)
    apply (drule Abs_ULIST_inverse')
    apply (simp)
    apply (subgoal_tac "map ((InjU :: 'a \<Rightarrow> 'm) \<circ> ProjU) (DestList x :: 'm list) = map id (DestList x)")
    apply (simp)
    apply (metis ListType_elim MkList_inv)
    apply (unfold map_eq_conv)
    apply (auto)
    apply (subgoal_tac "xa :! TYPEU('a)")
    apply (metis TypeUSound_ProjU_inv)
    apply (metis ListType_elim MkList_inv dtype_as_dcarrier in_mono)
  done
qed

lemma fimage_InjU_ProjU [simp]:
  assumes "TYPEUSOUND('a :: DEFINED, 'm::VALUE)" "\<langle>xs\<rangle>\<^sub>f \<subseteq> dcarrier TYPEU('a)"
  shows "(InjU :: 'a \<Rightarrow> 'm) `\<^sub>f ProjU `\<^sub>f xs = xs"
  apply (auto)
  apply (metis TypeUSound_ProjU_inv assms(1) assms(2) dtype_as_dcarrier set_mp)
  apply (metis (full_types) TypeUSound_ProjU_inv assms(1) assms(2) dcarrier_dtype imageI in_mono)
done

lemma Abs_UFSET_inverse'': "(\<forall>x \<in> \<langle>xs\<rangle>\<^sub>f. \<D> x) \<Longrightarrow> Rep_UFSET (Abs_UFSET xs) = xs"
  by (metis Abs_UFSET_inverse')

lemma TypeUSound_UFSET [typing]: 
  assumes 
    "(TYPEU('a :: DEFINED) :: 'm UTYPE) \<in> FSetPerm" "TYPEUSOUND('a, 'm)"
  shows "TYPEUSOUND('a UFSET, 'm :: FSET_SORT)"
proof -

  from assms
  have "\<And> x::'a UFSET. MkFSet TYPEU('a) (InjU `\<^sub>f (Rep_UFSET x)) :! (FSetType TYPEU('a) :: 'm UTYPE)"
    apply (rule_tac typing)
    apply (simp add: inju)
    apply (auto simp add:dcarrier_def intro:typing)
    apply (metis Rep_UFSET' TypeUSound_InjU_defined)
  done

  with assms show ?thesis
    apply (rule_tac TypeUSound_intro)
    apply (auto simp add:inju)
    apply (subgoal_tac "\<langle>InjU `\<^sub>f (Rep_UFSET x)\<rangle>\<^sub>f \<subseteq> (dcarrier TYPEU('a) :: 'm set)")
    apply (simp)
    apply (subgoal_tac "\<langle>InjU `\<^sub>f (Rep_UFSET x)\<rangle>\<^sub>f \<subseteq> (dcarrier TYPEU('a) :: 'm set)")
    apply (auto)
    apply (metis Rep_UFSET' TypeUSound_InjU_dtype)
    apply (auto simp add:defined)
    apply (subgoal_tac "\<langle>InjU `\<^sub>f (Rep_UFSET x)\<rangle>\<^sub>f \<subseteq> (dcarrier TYPEU('a) :: 'm set)")
    apply (auto simp add:defined)
    apply (metis Rep_UFSET' TypeUSound_InjU_dtype)

    apply (subgoal_tac "\<forall> y::'a \<in> \<langle>ProjU `\<^sub>f (DestFSet x)\<rangle>\<^sub>f. \<D> y")
    defer
    apply (auto simp add:defined)[1]
    apply (rule defined)
    apply (simp)
    apply (metis FSetType_elim MkFSet_inv dcarrier_defined dcarrier_type dtype_relI in_mono)
    apply (drule Abs_UFSET_inverse'')
    apply (simp)
    apply (subgoal_tac "(InjU :: 'a \<Rightarrow> 'm) `\<^sub>f ProjU `\<^sub>f (DestFSet x :: 'm fset) = (DestFSet x)")
    apply (simp)
    apply (metis FSetType_elim MkFSet_inv)
    apply (auto)
  done
qed

lemma image_InjU_ProjU [simp]:
  assumes "TYPEUSOUND('a :: DEFINED, 'm::VALUE)" "xs \<subseteq> dcarrier TYPEU('a)"
  shows "(InjU :: 'a \<Rightarrow> 'm) ` ProjU ` xs = xs"
  apply (auto)
  apply (metis TypeUSound_ProjU_inv assms(1) assms(2) dtype_as_dcarrier set_mp)
  apply (metis TypeUSound_ProjU_inv assms(1) assms(2) dtype_as_dcarrier image_iff in_mono)
done

lemma TypeUSound_USET [typing]: 
  assumes 
    "(TYPEU('a :: DEFINED) :: 'm UTYPE) \<in> SetPerm" "TYPEUSOUND('a, 'm)"
  shows "TYPEUSOUND('a USET, 'm :: SET_SORT)"
proof -

  from assms
  have "\<And> x::'a USET. MkSet TYPEU('a) (InjU ` (Rep_USET x)) :! (SetType TYPEU('a) :: 'm UTYPE)"
    apply (rule_tac typing)
    apply (simp)
    apply (auto simp add:dcarrier_def intro:typing)
    apply (metis Rep_USET' TypeUSound_InjU_defined)
  done

  with assms show ?thesis
    apply (rule_tac TypeUSound_intro)
    apply (auto simp add:inju)
    apply (subgoal_tac "InjU ` (Rep_USET x) \<subseteq> (dcarrier TYPEU('a) :: 'm set)")
    apply (simp)
    apply (subgoal_tac "InjU ` (Rep_USET x) \<subseteq> (dcarrier TYPEU('a) :: 'm set)")
    apply (auto)
    apply (metis Rep_USET' TypeUSound_InjU_dtype)
    apply (auto simp add:defined)
    apply (subgoal_tac "InjU ` (Rep_USET x) \<subseteq> (dcarrier TYPEU('a) :: 'm set)")
    apply (auto simp add:defined)
    apply (metis (full_types) TypeUSound_InjU_inv imageI)
    apply (metis TypeUSound_InjU_dtype USET_elems_defined)
    apply (subgoal_tac "\<forall>y::'a \<in> (ProjU ` DestSet x). \<D> y")
    apply (auto)
    apply (erule SetType_elim)
    apply (auto)
    apply (metis TypeUSound_ProjU_defined dcarrier_defined dcarrier_type dtype_relI set_mp)
  done
qed

(*
    apply (auto)

    apply (subgoal_tac "\<forall> y::'a \<in> \<langle>ProjU `\<^sub>f (DestFSet x)\<rangle>\<^sub>f. \<D> y")
    defer
    apply (auto simp add:defined)[1]
    apply (rule defined)
    apply (simp)
    apply (metis FSetType_elim MkFSet_inv dcarrier_defined dcarrier_type dtype_relI in_mono)
    apply (drule Abs_UFSET_inverse'')
    apply (simp)
*)

(*
lemma TypeUSound_list [typing]: 
  "\<lbrakk> (TYPEU('a :: DEFINED) :: 'm UTYPE) \<in> ListPerm; TYPEUSOUND('a, 'm) \<rbrakk> 
     \<Longrightarrow> TYPEUSOUND('a list, 'm :: LIST_SORT)"
  apply (rule)
  apply (simp_all)
  apply (rule MkList_type)
  apply (simp)
  apply (auto simp add:dcarrier_def defined intro:typing)
  apply (auto simp add:dcarrier_def TypeUSound_def)[1]
  apply (rule typing, auto)
  apply (subgoal_tac "set (map InjU x) \<subseteq> dcarrier (TYPEU('a) :: 'm UTYPE)")
  apply (auto simp add:comp_def)
done
*)

(*
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
