(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: generic_model.thy                                                    *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 9 September 2014 *)

header {* UTP Generic Model *}

theory utp_generic_model
imports "../core/utp_model"
begin

text {*
  The generic model facilitates the creation of UTP models from UTP value and
  type encodings as separate HOL types. It avoids duplication of code and also
  simplifies proofs. Note, however, that the type @{text model} should not be
  used directly but wrapped into a HOL typedef instead. This is important for
  reusing the generic model for different instantiations.
*}

default_sort BASE_MODEL

subsection {* Model Datatype *}

datatype ('uval, 'utype) model =
  MdlVal "'uval" |
  MdlTyp "'utype"

subsubsection {* Destructors *}

primrec MdlValOf :: "('VALUE, 'TYPE) model \<Rightarrow> 'VALUE" where
"MdlValOf (MdlVal v) = v" |
"MdlValOf (MdlTyp t) = undefined"

primrec MdlTypOf :: "('VALUE, 'TYPE) model \<Rightarrow> 'TYPE" where
"MdlTypOf (MdlVal v) = undefined" |
"MdlTypOf (MdlTyp t) = t"

subsubsection {* Testing Functions *}

primrec IsMdlVal :: "('VALUE, 'TYPE) model \<Rightarrow> bool" where
"IsMdlVal (MdlVal v) = True" |
"IsMdlVal (MdlTyp t) = False"

primrec IsMdlTyp :: "('VALUE, 'TYPE) model \<Rightarrow> bool" where
"IsMdlTyp (MdlVal v) = False" |
"IsMdlTyp (MdlTyp t) = True"

subsubsection {* Inverse Theorems *}

theorem MdlValOf_inverse [simp] :
"IsMdlVal v \<Longrightarrow> MdlVal (MdlValOf v) = v"
apply (erule asmE)
apply (induct_tac v)
apply (simp_all)
done

theorem MdlTypOf_inverse [simp] :
"IsMdlTyp v \<Longrightarrow> MdlTyp (MdlTypOf v) = v"
apply (erule asmE)
apply (induct_tac v)
apply (simp_all)
done

subsection {* Generic Carriers *}

definition model_uval :: "('VALUE, 'TYPE) model set" where
"model_uval = range MdlVal"

definition model_utype :: "('VALUE, 'TYPE) model set" where
"model_utype = range MdlTyp"

theorem model_uval_exists [intro] :
"\<exists> x . x \<in> model_uval"
apply (unfold model_uval_def)
apply (metis rangeI)
done

theorem model_utype_exists [intro] :
"\<exists> x . x \<in> model_utype"
apply (unfold model_utype_def)
apply (metis rangeI)
done

subsection {* Model Embedding *}

definition EmbVal :: "(('VALUE, 'TYPE) model \<Rightarrow> 'MODEL::BASE_MODEL) \<Rightarrow>
  'VALUE \<Rightarrow> 'MODEL uval" ("EmbVal[_]") where
"EmbVal[Abs] v = Abs_uval (Abs (MdlVal v))"

definition EmbTyp :: "(('VALUE, 'TYPE) model \<Rightarrow> 'MODEL::BASE_MODEL) \<Rightarrow>
  'TYPE \<Rightarrow> 'MODEL utype" ("EmbTyp[_]") where
"EmbTyp[Abs] t = Abs_utype (Abs (MdlTyp t))"

definition PrjVal :: "('MODEL::BASE_MODEL \<Rightarrow> ('VALUE, 'TYPE) model) \<Rightarrow>
  'MODEL uval \<Rightarrow> 'VALUE" ("PrjVal[_]") where
"PrjVal[Rep] v = MdlValOf (Rep (Rep_uval v))"

definition PrjTyp :: "('MODEL::BASE_MODEL \<Rightarrow> ('VALUE, 'TYPE) model) \<Rightarrow>
  'MODEL utype \<Rightarrow> 'TYPE" ("PrjTyp[_]") where
"PrjTyp[Rep] t = MdlTypOf (Rep (Rep_utype t))"

subsection {* Inverse Theorems *}

theorem EmbVal_inverse :
"\<lbrakk>type_definition Rep Abs UNIV; Abs ` model_uval = VALUE\<rbrakk> \<Longrightarrow>
 PrjVal[Rep] (EmbVal[Abs] v) = v"
apply (unfold EmbVal_def PrjVal_def)
apply (subst Abs_uval_inverse)
apply (metis model_uval_def image_eqI rangeI)
apply (simp add: type_definition.Abs_inverse)
done

theorem EmbTyp_inverse :
"\<lbrakk>type_definition Rep Abs UNIV; Abs ` model_utype = UTYPE\<rbrakk> \<Longrightarrow>
 PrjTyp[Rep] (EmbTyp[Abs] t) = t"
apply (unfold EmbTyp_def PrjTyp_def)
apply (subst Abs_utype_inverse)
apply (metis model_utype_def image_eqI rangeI)
apply (simp add: type_definition.Abs_inverse)
done

theorem PrjVal_inverse :
"\<lbrakk>type_definition Rep Abs UNIV; Abs ` model_uval = VALUE\<rbrakk> \<Longrightarrow>
 EmbVal[Abs] (PrjVal[Rep] v) = v"
apply (unfold EmbVal_def PrjVal_def)
apply (subst MdlValOf_inverse)
apply (drule type_definition.Abs_imageD)
apply (assumption)
apply (simp)
apply (unfold model_uval_def) [1]
apply (metis IsMdlVal.simps(1) Rep_uval image_iff)
apply (simp add: type_definition.Rep_inverse)
done

theorem PrjTyp_inverse :
"\<lbrakk>type_definition Rep Abs UNIV; Abs ` model_utype = UTYPE\<rbrakk> \<Longrightarrow>
 EmbTyp[Abs] (PrjTyp[Rep] t) = t"
apply (unfold EmbTyp_def PrjTyp_def)
apply (subst MdlTypOf_inverse)
apply (drule type_definition.Abs_imageD)
apply (assumption)
apply (simp)
apply (unfold model_utype_def) [1]
apply (metis IsMdlTyp.simps(2) Rep_utype image_iff)
apply (simp add: type_definition.Rep_inverse)
done

theorems Emb_Prj_simps =
  EmbVal_inverse
  EmbTyp_inverse
  PrjVal_inverse
  PrjTyp_inverse

subsection {* Transfer Support *}

theorem type_definition_VALUE_model :
fixes Abs :: "('VALUE, 'TYPE) model \<Rightarrow> 'MODEL::BASE_MODEL"
fixes Rep :: "'MODEL::BASE_MODEL \<Rightarrow> ('VALUE, 'TYPE) model"
assumes "type_definition Rep Abs UNIV"
assumes "Abs ` model_uval = VALUE"
shows "type_definition EmbVal[Abs] PrjVal[Rep] UNIV"
apply (subst type_definition_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp)
-- {* Subgoal 2 *}
apply (simp add: EmbVal_inverse assms)
-- {* Subgoal 3 *}
apply (simp add: PrjVal_inverse assms)
done

theorem type_definition_UTYPE_model :
fixes Abs :: "('VALUE, 'TYPE) model \<Rightarrow> 'MODEL::BASE_MODEL"
fixes Rep :: "'MODEL::BASE_MODEL \<Rightarrow> ('VALUE, 'TYPE) model"
assumes "type_definition Rep Abs UNIV"
assumes "Abs ` model_utype = UTYPE"
shows "type_definition EmbTyp[Abs] PrjTyp[Rep] UNIV"
apply (subst type_definition_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp)
-- {* Subgoal 2 *}
apply (simp add: EmbTyp_inverse assms)
-- {* Subgoal 3 *}
apply (simp add: PrjTyp_inverse assms)
done
end
