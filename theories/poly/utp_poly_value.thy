(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_poly_value.thy                                                   *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)

header {* Polymorphic Values *}

theory utp_poly_value
imports
  "../core/utp_model"
  "../core/utp_sorts"
  "../core/utp_event"
  "../types/utp_dlist"
  "../types/utp_dset"
  "../types/utp_dfset"
  "../core/utp_defined"
begin

default_sort type

subsection {* Theorem Attributes *}

ML {*
  structure erasure = Named_Thms
    (val name = @{binding erasure} val description = "erasure theorems")
*}

setup erasure.setup

text {* Perhaps rename @{text "inju"} into something like @{text "poly"}. *}

ML {*
  structure inju = Named_Thms
    (val name = @{binding inju} val description = "inju theorems")
*}

setup inju.setup

subsection {* HOL-to-UTP Injection *}

text {*
  The following locale serves to link HOL types and values to UTP model types
  and values. We cannot use a type class here as the linking functions range
  over two type variables, one for the injected HOL type and another one for
  the UTP model type. Type classes in Isabelle are limited to range over one
  type variable only to guarantee decidability. Polymorphic constants provide
  an easy way to create polymorphic functions, but some care is needed using
  them. If associated definitions for the constants overlap, for instance,
  Isabelle's type system may not be able to disambiguate them upon parsing.
*}

text {*
  FIXME: We need to defined some carefully thought-out rules to define what we
  can and what we cannot have here. (Simon Foster)
*}

consts
-- {* Injects a HOL value into a given UTP model. *}
  InjU  :: "'a::DEFINED \<Rightarrow> 'm::PRE_TYPED_MODEL uval"
-- {* Extracts a HOL value from a given UTP model. *}
  ProjU :: "'m::PRE_TYPED_MODEL uval \<Rightarrow> 'a"
-- {* Yields the UTP model type of a HOL type. *}
  TypeU :: "'a itself \<Rightarrow> 'm::PRE_TYPED_MODEL utype"

syntax
  "_UTYPE" :: "type \<Rightarrow> logic" ("(1UTYPE/(1'(_')))")
  "_TYPEU" :: "type \<Rightarrow> logic" ("(1TYPEU/(1'(_')))")

translations
  "UTYPE('a)" \<rightleftharpoons> "CONST TypeU TYPE('a)"
  "TYPEU('a)" \<rightharpoonup> "UTYPE('a)" -- {* For compatibility. Remove eventually! *}

subsection {* Injection Locale *}

text {*
  We create the following locale to captures the required properties of the
  injection and projection functions. These roughly correspond to the axioms
  of a typedef but are geared towards the UTP model. The locale predicate is
  then proved for various concrete injections of HOL types, and this provides
  the basic reasoning support for polymorphic values, expressions, etc. over
  arbitrary HOL types using a set of permissible HOL type constructors.
*}

(* Simon's original definition is now captured by the locale below. *)

(*
definition TypeUSound ::
  "'a::DEFINED itself \<Rightarrow> 'm::PRE_TYPED_MODEL itself \<Rightarrow> bool" where
"UTypedef t m \<longleftrightarrow>
  (\<forall> x :: 'a . (InjU x :: 'm uval) : TypeU t) \<and>
  (\<forall> x :: 'a . \<D> x \<longrightarrow> \<D>\<^sub>v (InjU x :: 'm uval)) \<and>
  (\<forall> x :: 'm uval . x :! TypeU t \<longrightarrow> \<D> (ProjU x :: 'a)) \<and>
  (\<forall> x :: 'a . ProjU (InjU x :: 'm uval) = x) \<and>
  (\<forall> x :! TypeU t . (InjU (ProjU x::'a)::'m uval) = x)"
*)

(* Can we do without (\<forall> x :! TypeU a . (InjU (ProjU x :: 'a) :: 'm) = x) ? *)

text {* TODO: Perhaps give the axioms below more meaningful names. *}

locale UTypedef =
  fixes hol_type :: "'a::DEFINED itself"
  fixes utp_type :: "'m::PRE_TYPED_MODEL itself" 
  assumes axm1 : "(\<forall> x :: 'a . (InjU x :: 'm uval) : UTYPE('a))"
  assumes axm2 : "(\<forall> x :: 'a . \<D> x \<longrightarrow> \<D>\<^sub>v (InjU x :: 'm uval))"
  assumes axm3 : "(\<forall> x :: 'm uval . x :! UTYPE('a) \<longrightarrow> \<D> (ProjU x :: 'a))"
  assumes axm4 : "(\<forall> x :: 'a . ProjU (InjU x :: 'm uval) = x)"
  assumes axm5 : "(\<forall> (x :: 'm uval) :! UTYPE('a) . (InjU (ProjU x :: 'a)) = x)"

syntax
  "_UTYPEDEF"   :: "type \<Rightarrow> type => logic" ("(1UTYPEDEF/(1'(_, _')))")
  "_TYPEUSOUND" :: "type \<Rightarrow> type => logic" ("(1TYPEUSOUND/(1'(_, _')))")

translations
  "UTYPEDEF('a, 'm)"   \<rightleftharpoons> "CONST UTypedef TYPE('a) TYPE('m)"
  "TYPEUSOUND('a, 'm)" \<rightharpoonup> "CONST UTypedef TYPE('a) TYPE('m)"

context UTypedef
begin

paragraph {* Lemmas derived from the Axioms *}

lemma InjU_typed [typing] :
  shows "(InjU (x :: 'a) :: 'm uval) : UTYPE('a)"
  by (metis axm1)

lemma InjU_defined [defined] :
  assumes "\<D> (x :: 'a)"
  shows "\<D>\<^sub>v (InjU x :: 'm uval)"
  by (metis assms axm2)

lemma InjU_strictly_typed [typing] :
  assumes "\<D> (x :: 'a)"
  shows "(InjU x :: 'm uval) :! UTYPE('a)"
apply (unfold strict_type_rel_def)
apply (metis assms InjU_typed InjU_defined)
done

lemma ProjU_defined [defined] :
  assumes "(x :: 'm uval) :! UTYPE('a)"
  shows "\<D> (ProjU x :: 'a)"
  by (metis assms axm3)

lemma InjU_inverse [simp] :
  shows "ProjU (InjU (x :: 'a) :: 'm uval) = x"
  by (metis axm4)

lemma ProjU_inverse [simp] :
  assumes "(x :: 'm uval)  :! UTYPE('a)"
  shows "(InjU (ProjU x :: 'a) :: 'm uval) = x"
  by (metis (lifting, mono_tags) DTall_def assms axm5)

lemma ProjU_InjU_comp [simp] :
  shows "ProjU \<circ> (InjU :: 'a \<Rightarrow> 'm uval) = id"
apply (rule ext)
apply (unfold comp_def id_def)
apply (rule InjU_inverse)
done

lemma InjU_inject [intro] :
  assumes "(InjU x :: 'm uval) = (InjU y :: 'm uval)"
  shows "(x :: 'a) = (y :: 'a)"
  by (metis InjU_inverse assms)

lemma ProjU_image_InjU [simp] :
  shows "ProjU ` (InjU :: 'a \<Rightarrow> 'm uval) ` xs = xs"
  by (metis ProjU_InjU_comp id_apply image_comp image_id)

lemma InjU_image_ProjU [simp] :
  assumes "xs \<subseteq> dcarrier UTYPE('a)"
  shows "(InjU :: 'a \<Rightarrow> 'm uval) ` ProjU ` xs = xs"
apply (safe)
apply (simp_all)
apply (metis ProjU_inverse assms dcarrier_def in_mono mem_Collect_eq)
apply (unfold image_def)
apply (clarsimp)
apply (metis ProjU_inverse assms dcarrier_def in_mono mem_Collect_eq)
done

lemma ProjU_fimage_InjU [simp] :
  shows "ProjU |`| (InjU :: 'a \<Rightarrow> 'm uval) |`| xs = xs"
  apply (transfer')
  apply (metis ProjU_InjU_comp fset.map_comp fset.map_id)
done

lemma InjU_fimage_ProjU [simp] :
  assumes "\<langle>xs\<rangle>\<^sub>f \<subseteq> dcarrier UTYPE('a)"
  shows "(InjU :: 'a \<Rightarrow> 'm uval) |`| ProjU |`| xs = xs"
  apply (insert assms)
  apply (transfer')
  apply (metis (erased, hide_lams) InjU_image_ProjU fimage.rep_eq fset_inject)
done

lemma map_InjU_ProjU [simp] :
  assumes "set xs \<subseteq> dcarrier UTYPE('a)"
  shows "map ((InjU :: 'a \<Rightarrow> 'm uval) \<circ> ProjU) xs = xs"
apply (simp add: map_eq_conv [where g = "id", simplified])
apply (metis ProjU_inverse assms dcarrier_def in_mono mem_Collect_eq)
done
end

theorem UTypedef_intro [intro] :
"\<lbrakk>\<And> (x :: 'a::DEFINED) . (InjU x :: 'm::PRE_TYPED_MODEL uval) : UTYPE('a);
  \<And> (x :: 'a) . ProjU (InjU x :: 'm uval) = x;
  \<And> x :: 'a . \<D> x \<Longrightarrow> \<D>\<^sub>v (InjU x :: 'm uval);
  \<And> x :: 'm uval. x :! UTYPE('a) \<Longrightarrow> \<D> (ProjU x :: 'a);
  \<And> x . x :! UTYPE('a) \<Longrightarrow> (InjU (ProjU x :: 'a) :: 'm uval) = x\<rbrakk> \<Longrightarrow>
  UTYPEDEF('a::DEFINED, 'm::PRE_TYPED_MODEL)"
  by (simp add: UTypedef_def)

subsection {* Concrete Injections *}

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

(* TODO: Review the following explanation and revise the layout. *)

text {* The following defs are carefully crafted, there must no
        overlap or \emph{potential} overlap. That is to say it must
        not be possible to create a type class or instance which
        renders them undisambiguable. Basically the LHS (value type)
        of @{const InjU} / @{const TypeU} should define the
        \emph{concrete type} which is to mapped. It can be parametric,
        but I can't conceive of a situation when this would be a class
        constraint -- I believe this would wreck the type system. This
        given, the RHS (model type) can then consist of only sort
        constraints. For instance for @{typ bool} the value type is of
        course @{typ bool} and the model type is @{typ "'m ::
        BOOL_SORT"}, since we need the ability to reconstruct the
        boolean in the model. Nevertheless these definitions
        \emph{are} extensible, but a great deal of care is required!
*}

(* TODO: The TypeU definitions should not be in [simp] I think... *)

defs (overloaded)
  InjU_bool [inju] : "InjU (x :: bool) \<equiv> MkBool x"
  ProjU_bool [inju] : "ProjU (x :: 'm::BOOL_SORT uval) \<equiv> DestBool x"
  TypeU_bool [simp] : "TypeU (x :: bool itself) \<equiv> BoolType"

  InjU_int [inju] : "InjU (x :: int) \<equiv> MkInt x"
  ProjU_int [inju] : "ProjU (x :: 'm::INT_SORT uval) \<equiv> DestInt x"
  TypeU_int [simp] : "TypeU (x::int itself) \<equiv> IntType"

  InjU_real [inju] :  "InjU (x :: real) \<equiv> MkReal x"
  ProjU_real [inju] : "ProjU (x :: 'a::REAL_SORT uval) \<equiv> DestReal x"
  TypeU_real [simp] : "TypeU (x :: real itself) \<equiv> RealType"

  InjU_event [inju] :  "InjU (x :: 'm::EVENT_SORT event) \<equiv> MkEvent x"
  ProjU_event [inju] : "ProjU (x :: 'm::EVENT_SORT uval) \<equiv> DestEvent x"
  TypeU_event [simp] : "TypeU (x :: 'm::EVENT_SORT event itself) \<equiv> EventType"

  InjU_ULIST [inju] : "InjU (xs :: 'a::DEFINED ULIST) \<equiv> MkList UTYPE('a) (map InjU (Rep_ULIST xs))"
  ProjU_ULIST [inju] : "ProjU (xs :: 'a::LIST_SORT uval) \<equiv> Abs_ULIST (map ProjU (DestList xs))"
  TypeU_ULIST [simp] : "TypeU (x :: 'a ULIST itself) \<equiv> ListType (TypeU TYPE('a))"

  InjU_USET [inju] : "InjU (xs :: 'a::DEFINED USET) \<equiv> MkSet UTYPE('a) (bset_image InjU (Rep_USET xs))"
  ProjU_USET [inju] : "ProjU (xs :: ('a::SET_SORT uval)) \<equiv> Abs_USET (bset_image ProjU (DestSet xs))"
  TypeU_USET [simp] : "TypeU (x :: ('a USET) itself) \<equiv> SetType (TypeU TYPE('a))"

  InjU_UFSET [inju] : "InjU (xs :: 'a::DEFINED UFSET) \<equiv> MkFSet UTYPE('a) (InjU |`| (Rep_UFSET xs))"
  ProjU_UFSET [inju] : "ProjU (xs :: 'a::FSET_SORT uval) \<equiv> Abs_UFSET (ProjU |`| (DestFSet xs))"
  TypeU_UFSET [simp] : "TypeU (x::('a UFSET) itself) \<equiv> FSetType (TypeU TYPE('a))"

  InjU_list [inju] : "InjU (xs :: 'a::DEFINED list) \<equiv> MkList (TypeU TYPE('a)) (map InjU xs)"
  ProjU_list [inju] : "ProjU (xs :: 'a::LIST_SORT uval) \<equiv> map ProjU (DestList xs)"
  TypeU_list [simp] : "TypeU (x :: 'a list itself) \<equiv> ListType (TypeU TYPE('a))"

  InjU_fset [inju] : "InjU (xs :: 'a::DEFINED fset) \<equiv> MkFSet (TypeU TYPE('a)) (InjU |`| xs)"
  ProjU_fset [inju] : "ProjU (xs :: 'a::FSET_SORT uval) \<equiv> ProjU |`| (DestFSet xs)"
  TypeU_fset [simp] : "TypeU (x :: 'a fset itself) \<equiv> FSetType (TypeU TYPE('a))"

lemma InjU_MkEvent [simp] :
"InjU = MkEvent"
  by (auto simp add: inju)

lemma ProjU_DestEvent [simp] :
"ProjU = DestEvent"
  by (auto simp add: inju)

text {*
  The following instantiations make use of the sort constraints to discharge
  the requirements of @{const UTypedef}.
*}

lemma UTypedef_bool [typing] :
"UTYPEDEF(bool, 'm::BOOL_SORT)"
  by (force simp add: defined typing inju)

lemma UTypedef_int [typing] :
"UTYPEDEF(int, 'm::INT_SORT)"
  by (force simp add: defined typing inju)

(*
lemma UTypedef_char [typing] :
"UTYPEDEF(char, 'm::CHAR_SORT)"
  by (force simp add: defined typing inju)
*)

lemma UTypedef_real [typing] :
"UTYPEDEF(real, 'm::REAL_SORT)"
  by (force simp add: defined typing inju)

lemma UTypedef_Event [typing] :
"UTYPEDEF('m event, 'm::EVENT_SORT)"
  by (auto simp add: typing defined inju)

theorem UTypedef_ULIST [typing] :
"UTYPEDEF('a::DEFINED, 'm::LIST_SORT) \<Longrightarrow>
 UTYPEDEF('a::DEFINED ULIST, 'm::LIST_SORT)"
apply (rule_tac UTypedef_intro)
apply (unfold inju TypeU_ULIST)
-- {* Subgoal 1 *}
apply (rule MkList_typed)
apply (transfer)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2)
-- {* Subgoal 2 *}
apply (subst MkList_inverse)
apply (clarsimp)
apply (metis Rep_ULIST' UTypedef.axm1 UTypedef.axm2)
apply (clarsimp simp: UTypedef.ProjU_InjU_comp)
-- {* Subgoal 3 *}
apply (subst MkList_defined)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2 ULIST_elems_defined)
-- {* Subgoal 4 *}
apply (clarsimp)
apply (metis defined_ULIST)
-- {* Subgoal 5 *}
apply (subst Abs_ULIST_inverse)
apply (clarsimp)
apply (metis UTypedef.axm3 in_DestList_strictly_typed strict_type_rel_def)
apply (clarsimp)
apply (metis DestList_inverse DestList_subset_dcarrier
  UTypedef.map_InjU_ProjU strict_type_rel_def)
done

theorem UTypedef_USET [typing] :
"UTYPEDEF('a::DEFINED, 'm::SET_SORT) \<Longrightarrow>
 UTYPEDEF('a::DEFINED USET, 'm::SET_SORT)"
apply (rule_tac UTypedef_intro)
apply (unfold inju TypeU_USET)
-- {* Subgoal 1 *}
apply (rule MkSet_typed)
apply (transfer)
apply (clarsimp)
apply (auto simp add:bset_image.rep_eq)[1]
apply (metis UTypedef.axm1)
apply (metis UTypedef.InjU_defined)
-- {* Subgoal 2 *}
apply (subst MkSet_inverse)
apply (clarsimp)
apply (transfer, simp add: bBall_def)
apply (transfer)
apply (auto)[1]
apply (metis UTypedef.axm1)
apply (metis UTypedef.InjU_defined)
apply (metis Rep_USET_inverse UTypedef.ProjU_InjU_comp bset.map_comp bset.map_id)
-- {* Subgoal 3 *}
apply (subst MkSet_defined)
apply (clarsimp)
apply (simp add: bBall_def bset_image.rep_eq, (auto)[1])
apply (metis UTypedef.axm1)
apply (metis USET_elems_defined UTypedef.InjU_defined bset_member.rep_eq)
-- {* Subgoal 4 *}
apply (clarsimp)
apply (metis defined_USET)
-- {* Subgoal 5 *}
apply (subst Abs_USET_inverse)
apply (auto simp add: bBall_def bset_image_def)
apply (metis UTypedef.ProjU_defined bset_member.rep_eq in_DestSet_strictly_typed strict_type_rel_def)
apply (metis DestBSet_inverse DestSet_inverse DestSet_subset_dcarrier UTypedef.InjU_image_ProjU strict_type_rel_def)
done

lemma Abs_UFSET_inverse'' :
"\<forall> x \<in> \<langle>xs\<rangle>\<^sub>f . \<D> x \<Longrightarrow> Rep_UFSET (Abs_UFSET xs) = xs"
  by (metis Abs_UFSET_inverse' fBall_intro)

theorem UTypedef_UFSET [typing] :
"UTYPEDEF('a::DEFINED, 'm::FSET_SORT) \<Longrightarrow>
 UTYPEDEF('a::DEFINED UFSET, 'm::FSET_SORT)"
apply (rule_tac UTypedef_intro)
apply (unfold inju TypeU_UFSET)
-- {* Subgoal 1 *}
apply (rule MkFSet_typed)
apply (transfer)
apply (clarsimp)
apply (metis UTypedef.InjU_defined UTypedef.axm1 fBallE)
-- {* Subgoal 2 *}
apply (subst MkFSet_inverse)
apply (clarsimp)
apply (metis UFSET_elems_defined UTypedef.InjU_defined UTypedef.axm1)
apply (clarsimp)
apply (metis Rep_UFSET_inverse UTypedef.ProjU_InjU_comp fset.map_id)
-- {* Subgoal 3 *}
apply (subst MkFSet_defined)
apply (clarsimp)
apply (metis UFSET_elems_defined UTypedef.InjU_defined UTypedef.axm1)
-- {* Subgoal 4 *}
apply (clarsimp)
apply (metis defined_UFSET)
-- {* Subgoal 5 *}
apply (erule FSetType_elim)
apply (clarsimp)
apply (subst Abs_UFSET_inverse'')
-- {* Subgoal 5.1 *}
apply (clarsimp)
apply (metis UTypedef.axm3 fBallE fmember.rep_eq strict_type_rel_def)
-- {* Subgoal 5.2 *}
apply (subst UTypedef.InjU_fimage_ProjU)
apply (simp_all)
apply (metis (mono_tags, lifting) dcarrier_def fBallE fmember.rep_eq mem_Collect_eq strict_type_rel_def subsetI)
done

theorem UTypedef_list [typing] :
"UTYPEDEF('a::DEFINED_TOTAL, 'm::LIST_SORT) \<Longrightarrow>
 UTYPEDEF('a::DEFINED_TOTAL list, 'm::LIST_SORT)"
apply (rule_tac UTypedef_intro)
apply (unfold inju TypeU_list)
-- {* Subgoal 1 *}
apply (rule MkList_typed)
apply (transfer)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2 defined_total)
-- {* Subgoal 2 *}
apply (subst MkList_inverse)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2 defined_total)
apply (simp add: UTypedef.ProjU_InjU_comp)
-- {* Subgoal 3 *}
apply (subst MkList_defined)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2 defined_list_def)
-- {* Subgoal 4 *}
apply (clarsimp)
apply (metis defined_list_def defined_total)
-- {* Subgoal 5 *}
apply (clarsimp)
apply (metis DestList_inverse DestList_subset_dcarrier UTypedef.map_InjU_ProjU
  strict_type_rel_def)
done

theorem UTypedef_fset [typing] :
"UTYPEDEF('a::DEFINED_TOTAL, 'm::FSET_SORT) \<Longrightarrow>
 UTYPEDEF('a::DEFINED_TOTAL fset, 'm::FSET_SORT)"
apply (rule_tac UTypedef_intro)
apply (unfold inju TypeU_fset)
-- {* Subgoal 1 *}
apply (rule MkFSet_typed)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2 defined_total)
-- {* Subgoal 2 *}
apply (subst MkFSet_inverse)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2 defined_total)
apply (clarsimp)
apply (metis UTypedef.ProjU_InjU_comp fset.map_id0 id_apply)
-- {* Subgoal 3 *}
apply (subst MkFSet_defined)
apply (clarsimp)
apply (metis UTypedef.axm1 UTypedef.axm2 defined_total)
-- {* Subgoal 4 *}
apply (clarsimp)
apply (metis defined_fset_def defined_total)
-- {* Subgoal 5 *}
apply (metis Abs_UFSET_inverse'' InjU_UFSET ProjU_UFSET TypeU_UFSET UTypedef.ProjU_inverse UTypedef_UFSET defined_total)
done

definition psigma :: "'a::DEFINED \<Rightarrow> 'm::TYPED_MODEL sigtype" where
"psigma v = (\<Sigma> InjU v : UTYPE('a))"

lemma sigtype_psigma [simp] :
  fixes x :: "'a :: DEFINED"
  assumes "UTYPEDEF('a, 'm :: TYPED_MODEL)"
  shows "sigtype (psigma x :: 'm sigtype) = UTYPE('a)"
  by (metis UTypedef.InjU_typed assms psigma_def sigtype)

lemma sigvalue_psigma [simp] :
  fixes x :: "'a :: DEFINED"
  assumes "UTYPEDEF('a, 'm :: TYPED_MODEL)"
  shows "sigvalue (psigma x :: 'm sigtype) = InjU x"
  apply (simp add: psigma_def)
  apply (subst sigvalue)
  apply (metis UTypedef.axm1 assms)
  apply (simp)
done
end
