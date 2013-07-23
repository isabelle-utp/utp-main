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

instance
  apply (intro_classes)
  apply (simp add:utype_rel_vdmv_def)
  apply (rule_tac x="to_nat BoolT" in exI)
  apply (force)
done
end

lemma vdmt_UTYPE [simp]: "\<lbrakk> v :\<^sub>v t; \<D> v \<rbrakk> \<Longrightarrow> to_nat t \<in> UTYPES (TYPE(vdmv))"
  by (auto simp add:UTYPES_def utype_rel_vdmv_def)

lemma prjTYPE_inv_vdmt [simp]
  : "embTYPE ((prjTYPE t) :: vdmt) = (t :: vdmv UTYPE)"
  apply (simp add:prjTYPE_def embTYPE_def)
  apply (case_tac t)
  apply (auto simp add: utype_rel_vdmv_def UTYPES_def)
done

lemma prjTYPE_vdmt_inj:
  "(prjTYPE (x :: vdmv UTYPE) :: vdmt) = prjTYPE y \<Longrightarrow> x = y"
  by (metis prjTYPE_inv_vdmt)

lemma embTYPE_inv_vdmt [simp]:
  "prjTYPE (embTYPE (t :: vdmt) :: vdmv UTYPE) = t"
  apply (rule embTYPE_inv[of "default_vdmt t"])
  apply (simp_all add:utype_rel_vdmv_def typing defined embTYPE_inv)
done

lemma embTYPE_vdmt_inj:
  "(embTYPE (x :: vdmt) :: vdmv UTYPE) = embTYPE y \<Longrightarrow> x = y"
  by (metis embTYPE_inv_vdmt)

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

lemma type_rel_vdmt: 
  "x : t \<longleftrightarrow> x :\<^sub>v prjTYPE t"
  apply (auto simp add: type_rel_def utype_rel_vdmv_def prjTYPE_def)
  apply (metis Rep_UTYPE_elim from_nat_to_nat utype_rel_vdmv_def)
done

instantiation vdmv :: BOT_SORT
begin

definition ubot_vdmv :: "vdmv UTYPE \<Rightarrow> vdmv" where
"ubot_vdmv = BotD \<circ> prjTYPE"

instance
  apply (intro_classes)
  apply (auto simp add:ubot_vdmv_def type_rel_vdmt)
done
end

subsection {* Int sort instantiation *}

instantiation vdmv :: INT_SORT
begin

definition MkInt_vdmv where "MkInt_vdmv (x::int) = BasicD (IntI x)"
definition DestInt_vdmv where "DestInt_vdmv x = the (ProjIntI (ProjBasicD x))"
definition IntType_vdmv :: "vdmv UTYPE" where 
"IntType_vdmv = embTYPE IntT"

instance 
  apply (intro_classes, simp_all add:MkInt_vdmv_def DestInt_vdmv_def IntType_vdmv_def type_rel_def utype_rel_vdmv_def)
  apply (auto simp add:dcarrier_def type_rel_vdmt image_def MkInt_vdmv_def)
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
  apply (auto simp add:dcarrier_def type_rel_vdmt image_def MkBool_vdmv_def monotype_def)
  apply (metis BasicD_type_cases BoolI_type_cases prjTYPE_inv_vdmt)
done
end

lemma MkBool_vdmv [simp]: 
  "MkBool x = BasicD (Inject x)"
  by (simp add:MkBool_vdmv_def Inject_bool_def)

subsection {* List sort instantiation *}

instantiation vdmv :: LIST_SORT
begin

definition MkList_vdmv :: "vdmv UTYPE \<Rightarrow> vdmv list \<Rightarrow> vdmv" where
"MkList_vdmv a xs = BasicD (ListI (ProjBasicT (prjTYPE a)) (map ProjBasicD xs))"

definition DestList_vdmv :: "vdmv \<Rightarrow> vdmv list" where
"DestList_vdmv x = map BasicD (the (ProjListI (ProjBasicD x)))"

definition ListType_vdmv :: "vdmv UTYPE \<Rightarrow> vdmv UTYPE" where
"ListType_vdmv a = (if (prjTYPE a \<in> vbtypes) then embTYPE (ListT (prjTYPE a)) else a)"

definition ListPerm_vdmv :: "vdmv UTYPE set" where
"ListPerm_vdmv = embTYPE ` vbtypes"

lemma foldr_over_prop:
  "foldr (op \<and> \<circ> P) xs True = (\<forall> x \<in> set xs. P x)"
  by (induct xs, auto)

instance
  apply (intro_classes)
  apply (unfold_locales)
  apply (auto simp add:MkList_vdmv_def DestList_vdmv_def ListType_vdmv_def ListPerm_vdmv_def dcarrier_def type_rel_vdmt image_def vbtypes_def)
  apply (subgoal_tac "map (BasicD \<circ> ProjBasicD) x = map id x")
  apply (force)
  apply (unfold map_eq_conv)
  apply (force)
  apply (rule_tac x="map BasicD xs" in exI)
  apply (auto)
  apply (force)
  apply (rule inj_onI)
  apply (simp add:ListType_vdmv_def)
  apply (case_tac "prjTYPE x \<in> vbtypes")
  apply (case_tac[!] "prjTYPE y \<in> vbtypes")
  apply (auto simp add:vbtypes_def)
  apply (metis ProjBasicT.simps embTYPE_inv_vdmt prjTYPE_inv_vdmt vbasict.inject(3))
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
  apply (auto simp add:vbtypes_def)
done

end

definition EventI :: "vdmv EVENT \<Rightarrow> vbasic" where
"EventI e = EvI (chan_name (EVENT_channel e)) 
                (ProjBasicT (prjTYPE (chan_type (EVENT_channel e))))
                (ProjBasicD (EVENT_value e))"

primrec ProjEventI :: "vbasic \<Rightarrow> vdmv EVENT" where
"ProjEventI (EvI n t v) = EV n (embTYPE (BasicT t)) (BasicD v)"

lemma EVENT_type_vbtypes:
  fixes e :: "vdmv EVENT"
  shows "prjTYPE (chan_type (EVENT_channel e)) \<in> vbtypes"
  by (case_tac e, auto simp add:EventPerm_vdmv_def)

lemma EventI_type [typing,intro]:
  "EventI e :\<^sub>b EventBT"
  apply (case_tac e)
  apply (auto simp add:EventI_def dtype_rel_def type_rel_vdmt EventPerm_vdmv_def vbtypes_def)
done

lemma EventI_defined [simp]:
  "\<D> (EventI e)"
  by (simp add:EventI_def)

lemma EventI_inv [simp]:
  "ProjEventI (EventI e) = e"
  apply (case_tac e)
  apply (auto simp add:EventI_def ProjEventI_def EventPerm_vdmv_def dtype_rel_def type_rel_vdmt vbtypes_def)
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
  apply (rule_tac x="EV n (embTYPE (BasicT  t)) (BasicD v)" in exI)
  apply (subgoal_tac "BasicD v : embTYPE (BasicT t)")
  apply (subgoal_tac "(embTYPE (BasicT t) :: vdmv UTYPE) \<in> EventPerm")
  apply (simp add:EventI_def)
  apply (simp add:EventPerm_vdmv_def vbtypes_def)
  apply (force simp add:type_rel_vdmt)
  apply (simp add:monotype_def type_rel_vdmt)
  apply (auto)
  apply (metis BasicD_type_cases EvI_type_cases prjTYPE_inv_vdmt)
done
end

subsection {* Set sort instantiation *}

(*
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
*)

instantiation option :: (type) DEFINED
begin

primrec Defined_option :: "'a option \<Rightarrow> bool" where
"Defined_option None = False" |
"Defined_option (Some x) = True"

instance ..

end

lemma InjVB_defined [defined]:
  "\<D> x \<Longrightarrow> \<D> (InjVB x)"
   by (case_tac x, auto)

lemma InjVB_type [typing]:
  "InjVB (x :: ('a::vbasic option)) :\<^sub>v VTYPE('a)"
  by (case_tac x, auto)

lemma ProjVB_defined [defined]: 
  "\<lbrakk> \<D> x; x :\<^sub>v VTYPE('a::vbasic) \<rbrakk> \<Longrightarrow> \<D> (ProjVB x :: 'a option)"
  by (auto simp add:ProjVB_def)

lemma ProjVB_inv [simp]: 
  "\<lbrakk> \<D> x; x :\<^sub>v VTYPE('a::vbasic) \<rbrakk> \<Longrightarrow> InjVB (ProjVB x :: 'a option) = x"
  apply (auto simp add:ProjVB_def)
  apply (metis InjVB.simps(2) Inject_Project Project_Inject)
done

end