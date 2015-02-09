(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_sorts.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

theory utp_cml_sorts
imports 
  "../../core/utp_sorts"
  utp_cml_inject
begin

section {* Instantiation of various UTP sorts *}

datatype cmlm = MkCmlv cmlv | MkCmlt cmlt 

primrec DestCmlv :: "cmlm \<Rightarrow> cmlv" where
"DestCmlv(MkCmlv x) = x"

primrec DestCmlt :: "cmlm \<Rightarrow> cmlt" where
"DestCmlt(MkCmlt x) = x"

setup_lifting type_definition_utype
setup_lifting type_definition_uval

instantiation cmlm :: BASE_MODEL
begin

definition VALUE_cmlm :: "cmlm set" where
"VALUE_cmlm = range MkCmlv" 

definition UTYPE_cmlm :: "cmlm set" where
"UTYPE_cmlm = range MkCmlt" 

instance by (intro_classes, auto simp add:VALUE_cmlm_def UTYPE_cmlm_def)

end

instantiation cmlm :: DEFINED_MODEL
begin

lift_definition value_defined_cmlm :: "cmlm uval \<Rightarrow> bool" is
"\<lambda> v. \<D> (DestCmlv v) \<and> (\<exists>t. DestCmlv v :\<^sub>v t)" .

instance
  by (intro_classes, transfer, auto simp add:VALUE_cmlm_def, metis cmlt_total)

end

instantiation cmlm :: TYPED_MODEL
begin

lift_definition type_rel_cmlm :: "cmlm uval \<Rightarrow> cmlm utype \<Rightarrow> bool"
is "\<lambda> x t. DestCmlv x :\<^sub>v DestCmlt t" .

instance
  apply (intro_classes)
  apply (transfer)
  apply (auto simp add:UTYPE_cmlm_def VALUE_cmlm_def)
  apply (metis cmlt_total)
  apply (transfer, auto simp add:VALUE_cmlm_def UTYPE_cmlm_def)
done
end

instantiation cmlm :: BOT_SORT
begin

term "BotD \<circ> DestCmlt"

lift_definition ubot_cmlm :: "cmlm utype \<Rightarrow> cmlm uval" is
"MkCmlv \<circ> BotD \<circ> DestCmlt" by (simp add:VALUE_cmlm_def)

instance
  by (intro_classes, (transfer, auto)+)

end

subsection {* Bool sort instantiation *}

instantiation cmlm :: BOOL_SORT
begin

lift_definition MkBool_cmlm :: "bool \<Rightarrow> cmlm uval" 
is "\<lambda> x. MkCmlv (BoolD x)" by (simp add:VALUE_cmlm_def)

lift_definition DestBool_cmlm :: "cmlm uval \<Rightarrow> bool" is
"\<lambda> x. the (ProjBoolD (DestCmlv x))" .

lift_definition BoolType_cmlm :: "cmlm utype" 
is "MkCmlt BoolT" by (simp add:UTYPE_cmlm_def) 

instance 
  apply (intro_classes, unfold_locales)
  apply (transfer, auto elim!:BoolD_type_cases simp add:VALUE_cmlm_def)+
done

end

instantiation cmlm :: STR_SORT
begin

lift_definition MkStr_cmlm :: "string \<Rightarrow> cmlm uval" 
is "MkCmlv \<circ> StringD" by (simp add:VALUE_cmlm_def)

lift_definition DestStr_cmlm :: "cmlm uval \<Rightarrow> string" is 
"ProjStringD \<circ> DestCmlv" .

lift_definition StrType_cmlm :: "cmlm utype" 
is "MkCmlt StringT" by (simp add:UTYPE_cmlm_def) 

instance
  apply (intro_classes, unfold_locales)
  apply (transfer,auto)
  apply (metis (full_types) CharD_type ListD_type ex_map_conv)
  apply (transfer,auto)
  apply (transfer,auto,subst map_idI, simp)
  apply (auto)
  apply (transfer, simp add:VALUE_cmlm_def, clarify, simp)
  apply (erule ListT_type_cases, auto, subst map_idI)
  apply (auto)
done
end

subsection {* List sort instantiation *}

instantiation cmlm :: LIST_SORT
begin

lift_definition MkList_cmlm :: "cmlm utype \<Rightarrow> cmlm uval list \<Rightarrow> cmlm uval" is
"\<lambda> a xs. MkCmlv (ListD (DestCmlt a) (map DestCmlv xs))" by (simp add:UTYPE_cmlm_def VALUE_cmlm_def)

lift_definition DestList_cmlm :: "cmlm uval \<Rightarrow> cmlm uval list" is
"\<lambda> x. map MkCmlv (the (ProjListD (DestCmlv x)))" by (auto simp add:VALUE_cmlm_def pred_list_def)

lift_definition ListType_cmlm :: "cmlm utype \<Rightarrow> cmlm utype" is
"\<lambda> a. MkCmlt (ListT (DestCmlt a))" by (simp add:UTYPE_cmlm_def)

instance
  apply (intro_classes, unfold_locales)
  apply (auto simp add:WT_LIST_def)[1]
  apply (transfer, (auto simp add:UTYPE_cmlm_def)[1])
  apply (transfer, auto elim!:ListD_type_cases simp add:UTYPE_cmlm_def VALUE_cmlm_def)
  apply (metis (full_types) DestCmlv.simps)
  apply (transfer, (auto simp add:UTYPE_cmlm_def VALUE_cmlm_def)[1])
  apply (rule_tac x="ListT xa" in exI, auto)
  apply (transfer, auto)
  apply (transfer, auto simp add:UTYPE_cmlm_def VALUE_cmlm_def)
  apply (subst map_idI, auto, metis DestCmlv.simps list_all_iff rangeE)
  apply (transfer, auto simp add: VALUE_cmlm_def UTYPE_cmlm_def)
  apply (subst map_idI, auto)
  apply (simp add: WT_LIST_def, transfer, auto simp add:UTYPE_cmlm_def)
  apply (metis empty_iff list.set(1) list_all_iff)
  apply (rule injI, transfer, auto simp add:UTYPE_cmlm_def)
done
end

subsection {* Set Sort instantiation *}

instantiation cmlm :: SET_SORT
begin

lift_definition MkSet_cmlm :: "cmlm utype \<Rightarrow> cmlm uval bset \<Rightarrow> cmlm uval" is
"\<lambda> a xs. MkCmlv (SetD (DestCmlt a) (bset_image DestCmlv xs))" by (simp add:UTYPE_cmlm_def VALUE_cmlm_def)

lift_definition DestSet_cmlm :: "cmlm uval \<Rightarrow> cmlm uval bset" is
"\<lambda> x. bset_image MkCmlv (ProjSetD (DestCmlv x))" 
  by (auto simp add:VALUE_cmlm_def pred_bset_def bset_image.rep_eq)

lift_definition SetType_cmlm :: "cmlm utype \<Rightarrow> cmlm utype" is
"\<lambda> a. MkCmlt (SetT (DestCmlt a))" by (simp add:UTYPE_cmlm_def)

instance
  sorry

end

end
