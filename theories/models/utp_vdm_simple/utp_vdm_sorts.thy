(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_sorts.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

theory utp_vdm_sorts
imports 
  "../../core/utp_sorts"
  utp_vdm_inject
begin

section {* Instantiation of various UTP sorts *}

instantiation vdmv :: VALUE
begin

definition utype_rel_vdmv :: "vdmv \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vdmv x u = (\<exists> t :: vdmt. u = to_nat t \<and> x :\<^sub>v t)"

definition Defined_vdmv :: "vdmv \<Rightarrow> bool" where
"Defined_vdmv \<equiv> \<D>\<^sub>v"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_vdmv_def Defined_vdmv_def)
  apply (rule_tac x="to_nat BoolT" in exI)
  apply (force)
done
end

lemma vdmt_UTYPE [simp]: "\<lbrakk> v :\<^sub>v t; \<D> v \<rbrakk> \<Longrightarrow> to_nat t \<in> UTYPES (TYPE(vdmv))"
  by (auto simp add:UTYPES_def utype_rel_vdmv_def)

lemma prjTYPE_inv_vdm [simp]
  : "embTYPE ((prjTYPE t) :: vdmt) = (t :: vdmv UTYPE)"
  apply (simp add:prjTYPE_def embTYPE_def)
  apply (case_tac t)
  apply (auto simp add: utype_rel_vdmv_def UTYPES_def)
done

lemma embTYPE_inv_vdm [simp]: 
  "prjTYPE (embTYPE VTYPE('a::vbasic) :: vdmv UTYPE) = VTYPE('a)"
  apply (rule_tac embTYPE_inv[of "BasicD (Inject undefined)"])
  apply (auto simp add:utype_rel_vdmv_def Defined_vdmv_def)
  apply (rule)
  apply (rule Inject_type)
done

lemma embTYPE_inv_vbtypes [simp]:
  "t \<in> vbtypes \<Longrightarrow> prjTYPE (embTYPE t :: vdmv UTYPE) = t"
  apply (auto simp add:vbtypes_def)
  apply (rule_tac v="BasicD x" in embTYPE_inv)
  apply (auto simp add: utype_rel_vdmv_def Defined_vdmv_def)
done

lemma type_rel_vdmt_exists: 
  "(x::vdmv) : a \<Longrightarrow> \<exists> t. a = embTYPE t \<and> x :\<^sub>v t" 
  apply (simp add:type_rel_def)
  apply (simp add:utype_rel_vdmv_def)
  apply (case_tac a)
  apply (auto simp add:UTYPES_def)
  apply (rule_tac x="t" in exI)
  apply (simp add:embTYPE_def)
done

lemma type_rel_vdmt_elim [elim]:
  "\<lbrakk>(x::vdmv) : a; \<And> t. \<lbrakk> a = embTYPE t; x :\<^sub>v t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis type_rel_vdmt_exists)

lemma BotD_type: "BotD a :\<^sub>v a"
  by (auto)

lemma type_rel_vdmt: 
  "x : t \<longleftrightarrow> x :\<^sub>v prjTYPE t"
  apply (auto simp add: type_rel_def utype_rel_vdmv_def prjTYPE_def)
  apply (metis Rep_UTYPE_elim from_nat_to_nat utype_rel_vdmv_def)
done

(*
instantiation vdmv :: BOT_SORT
begin

definition ubot_vdmv :: "vdmv" where
"ubot_vdmv = BotD"

instance
  apply (intro_classes)
  apply (simp add:ubot_vdmv_def Defined_vdmv_def)
done
end

lemma Defined_bot [simp]: "\<D> (BotD :: vdmv) \<longleftrightarrow> False"
  by (simp add:Defined_vdmv_def)

lemma Defined_ubot [simp]: "\<D> \<bottom>v \<longleftrightarrow> False"
  by (simp add:Defined_vdmv_def)
*)

(*
lemma vdmv_UTYPE_nbot [simp]: 
  "(from_nat (Rep_UTYPE (t :: vdmv UTYPE)) :: vdmt lift) \<noteq> \<bottom>"
  apply (case_tac t)
  apply (auto simp add: UTYPES_def utype_rel_vdmv_def)
  apply (auto)
done

lemma vdmv_UTYPE_Def [simp]: 
  "\<exists> x. (prj\<cdot>(Rep_UTYPE (a :: vdmv UTYPE)) :: vdmt lift) = Def x"
  apply (case_tac a)
  apply (simp add: UTYPES_def)
  apply (simp add: utype_rel_vdmv_def)
  apply (auto)
done

lemma vdmv_UTYPE_elim [elim]:
  assumes "\<And> x. (prj\<cdot>(Rep_UTYPE (a :: vdmv UTYPE)) :: vdmt lift) = Def x \<Longrightarrow> P" 
  shows "P"
  by (metis assms vdmv_UTYPE_Def)
*)
subsection {* Int sort instantiation *}

instantiation vdmv :: INT_SORT
begin

definition MkInt_vdmv where "MkInt_vdmv (x::int) = BasicD (IntI x)"
definition DestInt_vdmv where "DestInt_vdmv x = the (ProjIntI (ProjBasicD x))"
definition IntType_vdmv :: "vdmv UTYPE" where 
"IntType_vdmv = embTYPE IntT"

instance 
  apply (intro_classes, simp_all add:MkInt_vdmv_def DestInt_vdmv_def IntType_vdmv_def type_rel_def utype_rel_vdmv_def)
  apply (auto simp add:dcarrier_def type_rel_vdmt image_def MkInt_vdmv_def Defined_vdmv_def)
done
end

subsection {* Bool sort instantiation *}

instantiation vdmv :: BOOL_SORT
begin

definition MkBool_vdmv where "MkBool_vdmv (x::bool) = BasicD (BoolI x)"
definition DestBool_vdmv where "DestBool_vdmv x = the (ProjBoolI (ProjBasicD x))"
definition BoolType_vdmv :: "vdmv UTYPE" where 
"BoolType_vdmv = embTYPE BoolT"

instance 
  apply (intro_classes, simp_all add:MkBool_vdmv_def DestBool_vdmv_def BoolType_vdmv_def type_rel_def utype_rel_vdmv_def)
  apply (auto simp add:dcarrier_def type_rel_vdmt image_def MkBool_vdmv_def Defined_vdmv_def monotype_def)
  apply (erule vbtypes_type_cases)
  apply (auto)
  apply (metis BasicD_type_cases BoolI_type_cases prjTYPE_inv_vdm)
done
end

lemma MkBool_vdmv [simp]: 
  "MkBool x = BasicD (Inject x)"
  by (simp add:MkBool_vdmv_def Inject_bool_def)

subsection {* List sort instantiation *}

lemma ProjBasicD_o_BasicD [simp]: 
  "ProjBasicD \<circ> BasicD = id"
  by (auto)

instantiation vdmv :: LIST_SORT
begin

definition MkList_vdmv :: "vdmv UTYPE \<Rightarrow> vdmv list \<Rightarrow> vdmv" where
"MkList_vdmv a xs = BasicD (ListI (prjTYPE a) (map ProjBasicD xs))"

definition DestList_vdmv :: "vdmv \<Rightarrow> vdmv list" where
"DestList_vdmv x = map BasicD (the (ProjListI (ProjBasicD x)))"

definition ListType_vdmv :: "vdmv UTYPE \<Rightarrow> vdmv UTYPE" where
"ListType_vdmv a = embTYPE (ListT (prjTYPE a))"

definition ListPerm_vdmv :: "vdmv UTYPE set" where
"ListPerm_vdmv = embTYPE ` vbtypes"

lemma foldr_over_prop:
  "foldr (op \<and> \<circ> P) xs True = (\<forall> x \<in> set xs. P x)"
  by (induct xs, auto)

instance
  apply (intro_classes)
  apply (unfold_locales)
  apply (auto simp add:MkList_vdmv_def DestList_vdmv_def ListType_vdmv_def ListPerm_vdmv_def dcarrier_def type_rel_vdmt image_def Defined_vdmv_def)
  apply (subgoal_tac "map (BasicD \<circ> ProjBasicD) x = map id x")
  apply (simp)
  apply (unfold map_eq_conv)
  apply (force)
  apply (erule vbtypes_type_cases)
  apply (simp)
  apply (auto)
  apply (rule_tac x="map BasicD xs" in exI)
  apply (force simp add:foldr_over_prop)
  apply (force)
  apply (force simp add:foldr_over_prop)
  apply (rule injI)
  apply (simp add:ListType_vdmv_def)
  apply (metis embTYPE_inv_vbtypes prjTYPE_inv_vdm vbtypes_simps(8) vdmt.inject(3))
  apply (rule_tac x="embTYPE NatT" in exI)
  apply (force)
done
end

subsection {* Events and Event Sort Instantiation *}

instantiation vdmv :: EVENT_PERM
begin

definition EventPerm_vdmv :: "vdmv UTYPE set" where
"EventPerm_vdmv = embTYPE ` vbtypes"

instance
  apply (intro_classes)
  apply (auto simp add:EventPerm_vdmv_def)
  apply (rule_tac x="embTYPE IntT" in exI)
  apply (auto)
done

end

definition EventI :: "vdmv EVENT \<Rightarrow> vbasic" where
"EventI e = EvI (chan_name (EVENT_channel e)) 
                (prjTYPE (chan_type (EVENT_channel e))) 
                (ProjBasicD (EVENT_value e))"

primrec ProjEventI :: "vbasic \<Rightarrow> vdmv EVENT" where
"ProjEventI (EvI n t v) = EV n (embTYPE t) (BasicD v)"

lemma EVENT_type_vbtypes:
  fixes e :: "vdmv EVENT"
  shows "prjTYPE (chan_type (EVENT_channel e)) \<in> vbtypes"
  by (case_tac e, auto simp add:EventPerm_vdmv_def)

lemma EventI_type [typing,intro]:
  "EventI e :\<^sub>b EventT"
  apply (case_tac e)
  apply (auto simp add:EventI_def dtype_rel_def type_rel_vdmt EventPerm_vdmv_def)
  apply (metis ProjBasicD.simps(1) vbtypes_type_cases)
done

lemma EventI_defined [simp]:
  "\<D>\<^sub>b (EventI e) = True"
  by (simp add:EventI_def)

lemma EventI_inv [simp]:
  "ProjEventI (EventI e) = e"
  apply (case_tac e)
  apply (auto simp add:EventI_def ProjEventI_def EventPerm_vdmv_def dtype_rel_def type_rel_vdmt)
  apply (metis ProjBasicD.simps(1) vbtypes_type_cases)
done

instantiation vdmv :: EVENT_SORT
begin

definition MkEvent_vdmv :: "vdmv EVENT \<Rightarrow> vdmv" where
"MkEvent_vdmv e = BasicD (EventI e)"

definition DestEvent_vdmv :: "vdmv \<Rightarrow> vdmv EVENT" where
"DestEvent_vdmv e = ProjEventI (ProjBasicD e)"

definition EventType_vdmv :: "vdmv UTYPE" where
"EventType_vdmv = embTYPE EventT"

instance
  apply (intro_classes)
  apply (auto simp add:DestEvent_vdmv_def MkEvent_vdmv_def EventType_vdmv_def dcarrier_def type_rel_vdmt image_def)


subsection {* Set sort instantiation *}

instantiation vdmv :: SET_SORT_PRE
begin

  definition MkSet_vdmv :: "vdmv set \<Rightarrow> vdmv" where
  "MkSet_vdmv xs = SetD (ProjBasicD ` xs)"
  
  definition DestSet_vdmv :: "vdmv \<Rightarrow> vdmv set" where
  "DestSet_vdmv v = BasicD ` ProjSetD v"

  definition IsSetElemType_vdmv :: "vdmv UTYPE \<Rightarrow> bool" where
  "IsSetElemType_vdmv t = (prjTYPE t \<in> vbtypes)"

  definition SetType_vdmv :: "vdmv UTYPE \<Rightarrow> vdmv UTYPE" where
  "SetType_vdmv t = embTYPE (SetT (prjTYPE t))"

instance ..

end

lemma embTYPE_inv_SetT:
  "prjTYPE (embTYPE (SetT t) :: vdmv UTYPE) = SetT t"
  apply (rule_tac embTYPE_inv[of "SetD {}"])
  apply (auto simp add: utype_rel_vdmv_def Defined_vdmv_def)
done

instantiation vdmv :: SET_SORT
begin

instance
  apply (intro_classes)
  apply (auto simp add:DestSet_vdmv_def MkSet_vdmv_def SetType_vdmv_def IsSetElemType_vdmv_def type_rel_vdmt)
  apply (drule_tac x="xb" in bspec)
  apply (simp)
  apply (force)
  apply (force)
  apply (simp_all add:dcarrier_def type_rel_vdmt)
  apply (auto)
  apply (subgoal_tac "\<exists> v::vdmv. v :\<^sub>u to_nat (SetT (prjTYPE t)) \<and> \<D> v")
  apply (force)
  apply (rule_tac x="SetD {}" in exI)
  apply (auto simp add:utype_rel_vdmv_def Defined_vdmv_def embTYPE_inv_SetT)
  apply (metis (lifting) CollectD IsBasicD.simps(1) ProjBasicD_inv set_mp vbtypes_type_cases vdefined.simps(1))
  apply (simp add:image_def MkSet_vdmv_def)
  apply (erule SetT_type_cases)
  apply (auto)
  apply (rule_tac x="BasicD ` xs" in bexI)
  apply (auto)
done

end

lemma ProjBasicD_inv [simp]: 
  "x \<in> vbvalues \<Longrightarrow> BasicD (ProjBasicD x) = x"
  by (auto simp add:vbvalues_def)

(*
lemma ProjBasicD_not_basic [simp]: "\<lbrakk> x :\<^sub>v a;  \<not> IsBasicD x \<rbrakk> \<Longrightarrow> ProjBasicD x = BotI a"
  apply (case_tac x, auto)
*)

lemma embTYPE_inv_FuncT:
  "prjTYPE (embTYPE (a \<rightarrow> b) :: vdmv UTYPE) = (a \<rightarrow> b)"
  apply (rule_tac embTYPE_inv[of "FuncD (\<lambda> x. BotD b)"])
  apply (auto simp add: utype_rel_vdmv_def Defined_vdmv_def)
done

(*
instantiation vdmv :: FUNCTION_SORT
begin

definition "MkFunc_vdmv f = FuncD (f \<circ> BasicD)"
definition "DestFunc_vdmv f = (\<lambda> x. (ProjFuncD f) (ProjBasicD x))"
definition "IsFunc_vdmv f = ({x. f x \<noteq> BotD} \<subseteq> range BasicD \<and> f BotD = BotD)"
definition FuncType_vdmv :: "vdmv UTYPE \<Rightarrow> vdmv UTYPE \<Rightarrow> vdmv UTYPE" where
"FuncType_vdmv a b = embTYPE (FuncT (prjTYPE a) (prjTYPE b))"

instance 
  apply (intro_classes)
  apply (rule ext)
  apply (simp add:DestFunc_vdmv_def MkFunc_vdmv_def IsFunc_vdmv_def FuncType_vdmv_def type_rel_vdmt)
  apply (clarify)
  apply (case_tac "IsBasicD x")
  apply (simp)
  apply (simp add: subset_iff)
  apply (metis IsBasicD.simps(1) image_iff)
  apply (metis Defined_vdmv_def MkFunc_vdmv_def vdefined.simps(3))
  apply (simp add:MkFunc_vdmv_def IsFunc_vdmv_def dcarrier_def FuncType_vdmv_def embTYPE_inv_FuncT Defined_vdmv_def type_rel_vdmt)
  apply (auto)
  apply (rule)
  apply (force)
  apply (force)
  apply (erule FuncT_type_cases)
  apply (rule_tac x="f \<circ> ProjBasicD" in exI)
  apply (clarify)
  apply (rule)
  apply (force)
  apply (rule)
  apply (rule)
  apply (rule)
  apply (auto)[1]
  apply (metis (lifting) BasicD_type_cases BotI_type ProjBasicD_not_basic utp_vdm_values.ProjBasicD_inv)
  apply (simp)
  apply (smt ProjBasicD_not_basic UNIV_I image_iff mem_Collect_eq subsetI utp_vdm_values.ProjBasicD_inv)
  apply (force)
  apply (simp_all add:FuncType_vdmv_def)
  apply (metis embTYPE_inv_FuncT prjTYPE_inv_vdm vdmt.simps(8))+
done

end
*)


(*
instantiation vdmv :: LIST_SORT
begin

definition MkList_vdmv :: "vdmv list \<Rightarrow> vdmv" where
"MkList_vdmv xs = BasicV (ListI (map ProjBasicV xs))"
*)


end