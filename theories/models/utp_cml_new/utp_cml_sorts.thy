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

lift_definition MkCmlVal :: "cmlv \<Rightarrow> cmlm uval" is MkCmlv
  by (metis VALUE_cmlm_def rangeI)

lift_definition DestCmlVal :: "cmlm uval \<Rightarrow> cmlv" is DestCmlv .

lemma MkCmlVal_inv [simp]: "DestCmlVal (MkCmlVal x) = x"
  by (transfer, simp)

lemma MkCmlVal_bset_inv [simp]: "DestCmlVal `\<^sub>b MkCmlVal `\<^sub>b A = A"
  by (metis (no_types, hide_lams) MkCmlVal_inv bset.map_comp bset.map_cong0 bset.map_id0 comp_def id_apply)

lemma DestCmlVal_inject: "DestCmlVal A = DestCmlVal B \<Longrightarrow> A = B"
  by (transfer, auto simp add:VALUE_cmlm_def)
  
lift_definition MkCmlTyp :: "cmlt \<Rightarrow> cmlm utype" is MkCmlt
  by (metis UTYPE_cmlm_def rangeI)

lift_definition DestCmlTyp :: "cmlm utype \<Rightarrow> cmlt" is DestCmlt .

lemma DestCmlType_dest [dest!]: 
  "DestCmlTyp t = a \<Longrightarrow> t = MkCmlTyp a"
  by (transfer, auto simp add:UTYPE_cmlm_def)

lemma MkCmlTyp_inv [simp]: "DestCmlTyp (MkCmlTyp x) = x"
  by (transfer, simp)

instantiation cmlm :: DEFINED_MODEL
begin

definition value_defined_cmlm :: "cmlm uval \<Rightarrow> bool" where
"\<D>\<^sub>v(v) \<longleftrightarrow> \<D> (DestCmlVal v) \<and> (\<exists>t. DestCmlVal v :\<^sub>v DestCmlTyp t)"

instance
  apply (intro_classes, simp add: value_defined_cmlm_def)
  apply (transfer, auto simp add:VALUE_cmlm_def, metis cmlt_total)
done
end

instantiation cmlm :: TYPED_MODEL
begin

definition type_rel_cmlm :: "cmlm uval \<Rightarrow> cmlm utype \<Rightarrow> bool" where
"x : t \<longleftrightarrow> DestCmlVal x :\<^sub>v DestCmlTyp t"

instance
  apply (intro_classes, simp add: type_rel_cmlm_def)
  apply (metis DestCmlVal.rep_eq DestCmlv.simps Rep_uval_cases VALUE_cmlm_def cmlt_total rangeI value_defined_cmlm_def)
  apply (simp add: type_rel_cmlm_def value_defined_cmlm_def)
done
end

lemma value_defined_cmlm_alt_def:
  "\<D>\<^sub>v v  \<longleftrightarrow> \<D> (DestCmlVal v) \<and> (\<exists>t. v : t)"
  by (simp add: value_defined_cmlm_def type_rel_cmlm_def)

lemma value_defined_cmlm_dest:
  "\<D>\<^sub>v v \<Longrightarrow> \<D> (DestCmlVal v)"
  by (simp add:value_defined_cmlm_alt_def)
  
instantiation cmlm :: BOT_SORT
begin

term "BotD \<circ> DestCmlt"

definition ubot_cmlm :: "cmlm utype \<Rightarrow> cmlm uval" where
"ubot_cmlm = MkCmlVal \<circ> BotD \<circ> DestCmlTyp"

instance
  apply (intro_classes)
  apply (auto simp add: ubot_cmlm_def value_defined_cmlm_def type_rel_cmlm_def)
done

end

subsection {* Bool sort instantiation *}

instantiation cmlm :: BOOL_SORT
begin

definition MkBool_cmlm :: "bool \<Rightarrow> cmlm uval" where 
"MkBool x = MkCmlVal (BoolD x)"

definition DestBool_cmlm :: "cmlm uval \<Rightarrow> bool" where
"DestBool x = the (ProjBoolD (DestCmlVal x))"

definition BoolType_cmlm :: "cmlm utype" where 
"BoolType = MkCmlTyp BoolT" 

instance 
  apply (intro_classes, unfold_locales)
  apply (auto elim!:BoolD_type_cases simp add: MkBool_cmlm_def DestBool_cmlm_def 
                    value_defined_cmlm_def type_rel_cmlm_def BoolType_cmlm_def)
  apply (metis BoolD_type MkCmlTyp_inv)
  apply (transfer)
  apply (auto elim!:BoolD_type_cases simp add:VALUE_cmlm_def)+
done

end

instantiation cmlm :: STR_SORT
begin

definition MkStr_cmlm :: "string \<Rightarrow> cmlm uval" where
"MkStr = MkCmlVal \<circ> StringD"

definition DestStr_cmlm :: "cmlm uval \<Rightarrow> string" where 
"DestStr = ProjStringD \<circ> DestCmlVal"

definition StrType_cmlm :: "cmlm utype" where 
"StrType = MkCmlTyp StringT" 

instance
  apply (intro_classes, unfold_locales)
  apply (transfer, auto)
  apply (auto simp add: value_defined_cmlm_def MkStr_cmlm_def StrType_cmlm_def DestStr_cmlm_def type_rel_cmlm_def)
  apply (metis (erased, lifting) CharD_type ListD_type MkCmlTyp_inv ex_map_conv)
  apply (subst map_idI, simp_all)
  apply (subst map_idI)
  apply (auto)
  apply (transfer, simp add:VALUE_cmlm_def, clarify, auto)
done
end

subsection {* List sort instantiation *}

instantiation cmlm :: LIST_SORT
begin

definition MkList_cmlm :: "cmlm utype \<Rightarrow> cmlm uval list \<Rightarrow> cmlm uval" where
"MkList a xs = MkCmlVal (ListD (DestCmlTyp a) (map DestCmlVal xs))"

definition DestList_cmlm :: "cmlm uval \<Rightarrow> cmlm uval list" where
"DestList x = map MkCmlVal (the (ProjListD (DestCmlVal x)))"

definition ListType_cmlm :: "cmlm utype \<Rightarrow> cmlm utype" where
"ListType a = MkCmlTyp (ListT (DestCmlTyp a))"

instance
  apply (intro_classes, unfold_locales)
  apply (simp_all add:value_defined_cmlm_def MkList_cmlm_def DestList_cmlm_def ListType_cmlm_def type_rel_cmlm_def WT_LIST_def)
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
  apply (metis empty_iff list.set(1))
  apply (rule injI, simp add:ListType_cmlm_def, transfer, auto simp add:UTYPE_cmlm_def)
done
end

lemma MkCmlVal_defined_elim [elim!]: 
  "\<lbrakk> \<D>\<^sub>v (MkCmlVal x); \<And> t. \<lbrakk> \<D> x; x :\<^sub>v t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (simp add: value_defined_cmlm_def type_rel_cmlm_def)
  apply (transfer)
  apply (auto simp add:UTYPE_cmlm_def)
done

lemma MkCmlVal_type_rel_transfer [simp]: "MkCmlVal x : MkCmlTyp t \<longleftrightarrow> x :\<^sub>v t"
  by (simp add: type_rel_cmlm_def)

lemma MkCmlTyp_type_rel_elim [elim!]: 
  "\<lbrakk> x : MkCmlTyp t; \<And> v. \<lbrakk> x = MkCmlVal v; v :\<^sub>v t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (simp add: type_rel_cmlm_def)
  apply (transfer)
  apply (auto simp add: VALUE_cmlm_def)
done

subsection {* Set Sort instantiation *}

instantiation cmlm :: SET_SORT
begin

definition MkSet_cmlm :: "cmlm utype \<Rightarrow> cmlm uval bset \<Rightarrow> cmlm uval" where
"MkSet a xs = MkCmlVal (SetD (DestCmlTyp a) (bset_image DestCmlVal xs))"

definition DestSet_cmlm :: "cmlm uval \<Rightarrow> cmlm uval bset" where
"DestSet x = bset_image MkCmlVal (ProjSetD (DestCmlVal x))" 

definition SetType_cmlm :: "cmlm utype \<Rightarrow> cmlm utype" where
"SetType a = MkCmlTyp (SetT (DestCmlTyp a))"

lemma WT_SET_alt_def: 
  "WT_SET a = {A. \<forall> x\<in>\<^sub>bA. x : a \<and> \<D> (DestCmlVal x)}"
  by (auto simp add: WT_SET_def value_defined_cmlm_alt_def)
  
instance proof (intro_classes, unfold_locales)
  fix A :: "cmlm uval bset" and t :: "cmlm utype"
  show "\<D>\<^sub>v (MkSet t A) \<longleftrightarrow> (A \<in> WT_SET t)"
  proof -
    have 1:"\<D>\<^sub>v (MkSet t A) \<Longrightarrow> (A \<in> WT_SET t)"
      apply (clarsimp simp add: WT_SET_alt_def)
      apply (simp add: value_defined_cmlm_alt_def)
      apply (auto elim!: SetD_type_cases simp add: value_defined_cmlm_alt_def MkSet_cmlm_def type_rel_cmlm_def)
      apply (drule sym)
      apply (simp only: DestBSet_inject)
      apply (drule_tac x="DestCmlVal x" in spec)
      apply (simp add:bset_image.rep_eq)
      apply (metis bset.set_map imageI)
    done
    have  2:"(A \<in> WT_SET t) \<Longrightarrow> \<D>\<^sub>v (MkSet t A)"
      apply (auto simp add: WT_SET_def value_defined_cmlm_alt_def MkSet_cmlm_def bset_image.rep_eq)
      apply (rule_tac x="MkCmlTyp (SetT (DestCmlTyp t))" in exI)
      apply (auto simp add:bset_image.rep_eq type_rel_cmlm_def)
    done
    from 1 2 show ?thesis ..
  qed
next
  fix A :: "cmlm uval bset" and t :: "cmlm utype"
  show "A \<in> WT_SET t \<Longrightarrow> MkSet t A : SetType t"
    apply (auto simp add: WT_SET_alt_def MkSet_cmlm_def SetType_cmlm_def bset_image.rep_eq)
    apply (simp add:type_rel_cmlm_def)
  done
next
  fix A :: "cmlm uval bset" and t :: "cmlm utype"
  show "A \<in> WT_SET t \<Longrightarrow> DestSet (MkSet t A) = A"
    apply (auto simp add: WT_SET_alt_def MkSet_cmlm_def DestSet_cmlm_def SetType_cmlm_def bset_image.rep_eq)
    apply (rename_tac y)
    apply (drule_tac x="y" in spec, auto)
    apply (metis MkCmlTyp_inv MkCmlTyp_type_rel_elim MkCmlVal_inv type_rel_cmlm_def)
    apply (rename_tac y)
    apply (drule_tac x="y" in spec, auto)
    apply (metis DestCmlType_dest MkCmlTyp_type_rel_elim MkCmlVal_inv imageI)
  done
next
  fix A :: "cmlm uval" and t :: "cmlm utype"
  show "A :! SetType t \<Longrightarrow> MkSet t (DestSet A) = A"
    by (auto elim!:SetT_type_cases dest!:value_defined_cmlm_dest intro:DestCmlVal_inject 
             simp add: type_rel_cmlm_def MkSet_cmlm_def DestSet_cmlm_def SetType_cmlm_def)
next
  fix t :: "cmlm utype"
  show "WT_SET t \<noteq> {}"
    apply (auto simp add: WT_SET_alt_def)
    apply (rule_tac x="{}\<^sub>b" in exI)
    apply (simp)
  done
next
  show "inj (SetType :: cmlm utype \<Rightarrow> cmlm utype)"
    apply (rule injI)
    apply (simp add:SetType_cmlm_def)
    apply (metis DestCmlType_dest DestCmlt.simps MkCmlTyp.rep_eq cmlt.inject(1))
  done
qed

end

definition EventD :: "cmlm event \<Rightarrow> cmlv" where
"EventD e = EvD (uchan_name (EventChan e)) 
                (DestCmlTyp (uchan_type (EventChan e)))
                (DestCmlVal (EventValue e))"

primrec ProjEventD :: "cmlv \<Rightarrow> cmlm event" where
"ProjEventD (EvD n t v) = Event n (MkCmlTyp t) (MkCmlVal v)"

lemma EventD_type [typing,intro]:
  "EventD e :\<^sub>v EventT"
  apply (case_tac e)
  apply (auto simp add:EventD_def type_rel_cmlm_def)
done

lemma EventD_defined [simp]:
  "\<D> (EventD e)"
  by (simp add:EventD_def)

lemma EventI_inv [simp]:
  "ProjEventD (EventD e) = e"
  apply (simp add:EventD_def)
  apply (metis DestCmlType_dest DestCmlVal_inject EventChan.rep_eq EventValue.rep_eq MkCmlVal_inv RepEvent_inverse RepUChan_inverse prod.swap_def surj_pair swap_simp)
done


instantiation cmlm :: EVENT_SORT
begin

definition MkEvent_cmlm :: "cmlm event \<Rightarrow> cmlm uval" where
"MkEvent e = MkCmlVal (EventD e)"

definition DestEvent_cmlm :: "cmlm uval \<Rightarrow> cmlm event" where
"DestEvent_cmlm e = ProjEventD (DestCmlVal e)"

definition EventType_cmlm :: "cmlm utype" where
"EventType_cmlm = MkCmlTyp EventT"

instance
  apply (intro_classes, unfold_locales, auto simp add:MkEvent_cmlm_def 
                        EventType_cmlm_def DestEvent_cmlm_def value_defined_cmlm_def)
  apply (rule_tac x="MkCmlTyp EventT" in exI, force)
  apply (simp add:EventD_def)
  apply (metis DestCmlType_dest monotype_def type_rel_cmlm_def vbasic_type_rel_uniq)
done

end

instance cmlm :: REACTIVE_SORT ..

end
