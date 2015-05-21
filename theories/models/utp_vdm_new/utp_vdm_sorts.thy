(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_sorts.thy                                                    *)
(* Authors: Original CML model by Simon Foster, University of York (UK)       *)
(*          Adapted to VDM by Luis Diogo Couto, Aarhus University (DK)        *)
(******************************************************************************)

theory utp_vdm_sorts
imports 
  "../../core/utp_sorts"
  utp_vdm_inject
begin

section {* Instantiation of various UTP sorts *}

datatype vdmm = MkVdmv vdmv | MkVdmt vdmt 

primrec DestVdmv :: "vdmm \<Rightarrow> vdmv" where
"DestVdmv(MkVdmv x) = x"

primrec DestVdmt :: "vdmm \<Rightarrow> vdmt" where
"DestVdmt(MkVdmt x) = x"

setup_lifting type_definition_utype
setup_lifting type_definition_uval

instantiation vdmm :: BASE_MODEL
begin

definition VALUE_vdmm :: "vdmm set" where
"VALUE_vdmm = range MkVdmv" 

definition UTYPE_vdmm :: "vdmm set" where
"UTYPE_vdmm = range MkVdmt" 

instance by (intro_classes, auto simp add:VALUE_vdmm_def UTYPE_vdmm_def)

end

lift_definition MkVdmVal :: "vdmv \<Rightarrow> vdmm uval" is MkVdmv
  by (metis VALUE_vdmm_def rangeI)

lift_definition DestVdmVal :: "vdmm uval \<Rightarrow> vdmv" is DestVdmv .

lemma MkVdmVal_inv [simp]: "DestVdmVal (MkVdmVal x) = x"
  by (transfer, simp)

lemma MkVdmVal_bset_inv [simp]: "DestVdmVal `\<^sub>b MkVdmVal `\<^sub>b A = A"
  by (metis (no_types, hide_lams) MkVdmVal_inv bset.map_comp bset.map_cong0 bset.map_id0 comp_def id_apply)

lemma DestVdmVal_inject: "DestVdmVal A = DestVdmVal B \<Longrightarrow> A = B"
  by (transfer, auto simp add:VALUE_vdmm_def)
  
lift_definition MkVdmTyp :: "vdmt \<Rightarrow> vdmm utype" is MkVdmt
  by (metis UTYPE_vdmm_def rangeI)

lift_definition DestVdmTyp :: "vdmm utype \<Rightarrow> vdmt" is DestVdmt .

lemma DestVdmType_dest [dest!]: 
  "DestVdmTyp t = a \<Longrightarrow> t = MkVdmTyp a"
  by (transfer, auto simp add:UTYPE_vdmm_def)

lemma MkVdmTyp_inv [simp]: "DestVdmTyp (MkVdmTyp x) = x"
  by (transfer, simp)

instantiation vdmm :: DEFINED_MODEL
begin

definition value_defined_vdmm :: "vdmm uval \<Rightarrow> bool" where
"\<D>\<^sub>v(v) \<longleftrightarrow> \<D> (DestVdmVal v) \<and> (\<exists>t. DestVdmVal v :\<^sub>v DestVdmTyp t)"

instance
  apply (intro_classes, simp add: value_defined_vdmm_def)
  apply (transfer, auto simp add:VALUE_vdmm_def, metis vdmt_total)
done
end

instantiation vdmm :: TYPED_MODEL
begin

definition type_rel_vdmm :: "vdmm uval \<Rightarrow> vdmm utype \<Rightarrow> bool" where
"x : t \<longleftrightarrow> DestVdmVal x :\<^sub>v DestVdmTyp t"

instance
  apply (intro_classes, simp add: type_rel_vdmm_def)
  apply (metis DestVdmVal.rep_eq DestVdmv.simps Rep_uval_cases VALUE_vdmm_def vdmt_total rangeI value_defined_vdmm_def)
  apply (simp add: type_rel_vdmm_def value_defined_vdmm_def)
done
end

lemma value_defined_vdmm_alt_def:
  "\<D>\<^sub>v v  \<longleftrightarrow> \<D> (DestVdmVal v) \<and> (\<exists>t. v : t)"
  by (simp add: value_defined_vdmm_def type_rel_vdmm_def)

lemma value_defined_vdmm_dest:
  "\<D>\<^sub>v v \<Longrightarrow> \<D> (DestVdmVal v)"
  by (simp add:value_defined_vdmm_alt_def)
  
instantiation vdmm :: BOT_SORT
begin

term "BotD \<circ> DestVdmt"

definition ubot_vdmm :: "vdmm utype \<Rightarrow> vdmm uval" where
"ubot_vdmm = MkVdmVal \<circ> BotD \<circ> DestVdmTyp"

instance
  apply (intro_classes)
  apply (auto simp add: ubot_vdmm_def value_defined_vdmm_def type_rel_vdmm_def)
done

end

subsection {* Bool sort instantiation *}

instantiation vdmm :: BOOL_SORT
begin

definition MkBool_vdmm :: "bool \<Rightarrow> vdmm uval" where 
"MkBool x = MkVdmVal (BoolD x)"

definition DestBool_vdmm :: "vdmm uval \<Rightarrow> bool" where
"DestBool x = the (ProjBoolD (DestVdmVal x))"

definition BoolType_vdmm :: "vdmm utype" where 
"BoolType = MkVdmTyp BoolT" 

instance 
  apply (intro_classes, unfold_locales)
  apply (auto elim!:BoolD_type_cases simp add: MkBool_vdmm_def DestBool_vdmm_def 
                    value_defined_vdmm_def type_rel_vdmm_def BoolType_vdmm_def)
  apply (metis BoolD_type MkVdmTyp_inv)
  apply (transfer)
  apply (auto elim!:BoolD_type_cases simp add:VALUE_vdmm_def)+
done

end

instantiation vdmm :: STR_SORT
begin

definition MkStr_vdmm :: "string \<Rightarrow> vdmm uval" where
"MkStr = MkVdmVal \<circ> StringD"

definition DestStr_vdmm :: "vdmm uval \<Rightarrow> string" where 
"DestStr = ProjStringD \<circ> DestVdmVal"

definition StrType_vdmm :: "vdmm utype" where 
"StrType = MkVdmTyp StringT" 

instance
  apply (intro_classes, unfold_locales)
  apply (transfer, auto)
  apply (auto simp add: value_defined_vdmm_def MkStr_vdmm_def StrType_vdmm_def DestStr_vdmm_def type_rel_vdmm_def)
  apply (metis (erased, lifting) CharD_type ListD_type MkVdmTyp_inv ex_map_conv)
  apply (subst map_idI, simp_all)
  apply (subst map_idI)
  apply (auto)
  apply (transfer, simp add:VALUE_vdmm_def, clarify, auto)
done
end

subsection {* List sort instantiation *}

instantiation vdmm :: LIST_SORT
begin

definition MkList_vdmm :: "vdmm utype \<Rightarrow> vdmm uval list \<Rightarrow> vdmm uval" where
"MkList a xs = MkVdmVal (ListD (DestVdmTyp a) (map DestVdmVal xs))"

definition DestList_vdmm :: "vdmm uval \<Rightarrow> vdmm uval list" where
"DestList x = map MkVdmVal (the (ProjListD (DestVdmVal x)))"

definition ListType_vdmm :: "vdmm utype \<Rightarrow> vdmm utype" where
"ListType a = MkVdmTyp (ListT (DestVdmTyp a))"

instance
  apply (intro_classes, unfold_locales)
  apply (simp_all add:value_defined_vdmm_def MkList_vdmm_def DestList_vdmm_def ListType_vdmm_def type_rel_vdmm_def WT_LIST_def)
  apply (auto simp add:WT_LIST_def)[1]
  apply (transfer, (auto simp add:UTYPE_vdmm_def)[1])
  apply (transfer, auto elim!:ListD_type_cases simp add:UTYPE_vdmm_def VALUE_vdmm_def)
  apply (metis (full_types) DestVdmv.simps)
  apply (transfer, (auto simp add:UTYPE_vdmm_def VALUE_vdmm_def)[1])
  apply (rule_tac x="ListT xa" in exI, auto)
  apply (transfer, auto)
  apply (transfer, auto simp add:UTYPE_vdmm_def VALUE_vdmm_def)
  apply (subst map_idI, auto, metis DestVdmv.simps list_all_iff rangeE)
  apply (transfer, auto simp add: VALUE_vdmm_def UTYPE_vdmm_def)
  apply (subst map_idI, auto)
  apply (metis empty_iff list.set(1))
  apply (rule injI, simp add:ListType_vdmm_def, transfer, auto simp add:UTYPE_vdmm_def)
done
end

lemma MkVdmVal_defined_elim [elim!]: 
  "\<lbrakk> \<D>\<^sub>v (MkVdmVal x); \<And> t. \<lbrakk> \<D> x; x :\<^sub>v t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (simp add: value_defined_vdmm_def type_rel_vdmm_def)
  apply (transfer)
  apply (auto simp add:UTYPE_vdmm_def)
done

lemma MkVdmVal_type_rel_transfer [simp]: "MkVdmVal x : MkVdmTyp t \<longleftrightarrow> x :\<^sub>v t"
  by (simp add: type_rel_vdmm_def)

lemma MkVdmTyp_type_rel_elim [elim!]: 
  "\<lbrakk> x : MkVdmTyp t; \<And> v. \<lbrakk> x = MkVdmVal v; v :\<^sub>v t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (simp add: type_rel_vdmm_def)
  apply (transfer)
  apply (auto simp add: VALUE_vdmm_def)
done

subsection {* Set Sort instantiation *}

instantiation vdmm :: SET_SORT
begin

definition MkSet_vdmm :: "vdmm utype \<Rightarrow> vdmm uval bset \<Rightarrow> vdmm uval" where
"MkSet a xs = MkVdmVal (SetD (DestVdmTyp a) (bset_image DestVdmVal xs))"

definition DestSet_vdmm :: "vdmm uval \<Rightarrow> vdmm uval bset" where
"DestSet x = bset_image MkVdmVal (ProjSetD (DestVdmVal x))" 

definition SetType_vdmm :: "vdmm utype \<Rightarrow> vdmm utype" where
"SetType a = MkVdmTyp (SetT (DestVdmTyp a))"

lemma WT_SET_alt_def: 
  "WT_SET a = {A. \<forall> x\<in>\<^sub>bA. x : a \<and> \<D> (DestVdmVal x)}"
  by (auto simp add: WT_SET_def value_defined_vdmm_alt_def)
  
instance proof (intro_classes, unfold_locales)
  fix A :: "vdmm uval bset" and t :: "vdmm utype"
  show "\<D>\<^sub>v (MkSet t A) \<longleftrightarrow> (A \<in> WT_SET t)"
  proof -
    have 1:"\<D>\<^sub>v (MkSet t A) \<Longrightarrow> (A \<in> WT_SET t)"
      apply (clarsimp simp add: WT_SET_alt_def)
      apply (simp add: value_defined_vdmm_alt_def)
      apply (auto elim!: SetD_type_cases simp add: value_defined_vdmm_alt_def MkSet_vdmm_def type_rel_vdmm_def)
      apply (drule sym)
      apply (simp only: DestBSet_inject)
      apply (drule_tac x="DestVdmVal x" in spec)
      apply (simp add:bset_image.rep_eq)
      apply (metis bset.set_map imageI)
    done
    have  2:"(A \<in> WT_SET t) \<Longrightarrow> \<D>\<^sub>v (MkSet t A)"
      apply (auto simp add: WT_SET_def value_defined_vdmm_alt_def MkSet_vdmm_def bset_image.rep_eq)
      apply (rule_tac x="MkVdmTyp (SetT (DestVdmTyp t))" in exI)
      apply (auto simp add:bset_image.rep_eq type_rel_vdmm_def)
    done
    from 1 2 show ?thesis ..
  qed
next
  fix A :: "vdmm uval bset" and t :: "vdmm utype"
  show "A \<in> WT_SET t \<Longrightarrow> MkSet t A : SetType t"
    apply (auto simp add: WT_SET_alt_def MkSet_vdmm_def SetType_vdmm_def bset_image.rep_eq)
    apply (simp add:type_rel_vdmm_def)
  done
next
  fix A :: "vdmm uval bset" and t :: "vdmm utype"
  show "A \<in> WT_SET t \<Longrightarrow> DestSet (MkSet t A) = A"
    apply (auto simp add: WT_SET_alt_def MkSet_vdmm_def DestSet_vdmm_def SetType_vdmm_def bset_image.rep_eq)
    apply (rename_tac y)
    apply (drule_tac x="y" in spec, auto)
    apply (metis MkVdmTyp_inv MkVdmTyp_type_rel_elim MkVdmVal_inv type_rel_vdmm_def)
    apply (rename_tac y)
    apply (drule_tac x="y" in spec, auto)
    apply (metis DestVdmType_dest MkVdmTyp_type_rel_elim MkVdmVal_inv imageI)
  done
next
  fix A :: "vdmm uval" and t :: "vdmm utype"
  show "A :! SetType t \<Longrightarrow> MkSet t (DestSet A) = A"
    by (auto elim!:SetT_type_cases dest!:value_defined_vdmm_dest intro:DestVdmVal_inject 
             simp add: type_rel_vdmm_def MkSet_vdmm_def DestSet_vdmm_def SetType_vdmm_def)
next
  fix t :: "vdmm utype"
  show "WT_SET t \<noteq> {}"
    apply (auto simp add: WT_SET_alt_def)
    apply (rule_tac x="{}\<^sub>b" in exI)
    apply (simp)
  done
next
  show "inj (SetType :: vdmm utype \<Rightarrow> vdmm utype)"
    apply (rule injI)
    apply (simp add:SetType_vdmm_def)
    apply (metis DestVdmType_dest DestVdmt.simps MkVdmTyp.rep_eq vdmt.inject(1))
  done
qed

end



end
