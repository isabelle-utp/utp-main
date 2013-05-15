theory utp_vdm_sorts
imports 
  "../../core/utp_sorts"
  utp_vdm_inject 
begin

instantiation vdmv :: VALUE
begin

(*
definition utype_rel_vval :: "vval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vval x u = \<exists> t :: vdmt. u = emb\<cdot>(Def t) \<and> x :\<^sub>v t)"
*)

lemma Defined_nbot [simp]: "\<D>\<^sub>v x \<Longrightarrow> x \<noteq> BotD"
  by (auto)

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

lemma BotD_type: "BotD :\<^sub>v a"
  by (auto)

lemma type_rel_vdmt: 
  "x : t \<longleftrightarrow> x :\<^sub>v prjTYPE t"
  apply (auto simp add: type_rel_def utype_rel_vdmv_def prjTYPE_def)
  apply (metis Rep_UTYPE_elim from_nat_to_nat utype_rel_vdmv_def)
done

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

definition MkInt_vdmv where "MkInt_vdmv (x::int) = InjVB x"
definition DestInt_vdmv where "DestInt_vdmv x = (ProjVB x :: int)"
definition IntUType_vdmv :: "vdmv itself \<Rightarrow> nat" where 
"IntUType_vdmv = (\<lambda> x. to_nat IntT)"

instance 
  apply (intro_classes, simp_all add:MkInt_vdmv_def DestInt_vdmv_def IntUType_vdmv_def type_rel_def utype_rel_vdmv_def embTYPE_def)
  apply (auto)
  apply (simp_all add: Inject_int_def InjVB_def Defined_vdmv_def MkInt_vdmv_def image_def)
  apply (force)+
done
end

subsection {* Bool sort instantiation *}

instantiation vdmv :: BOOL_SORT
begin

definition MkBool_vdmv where "MkBool_vdmv (x::bool) = InjVB x"
definition DestBool_vdmv where "DestBool_vdmv x = (ProjVB x :: bool)"
definition BoolUType_vdmv :: "vdmv itself \<Rightarrow> nat" where 
"BoolUType_vdmv = (\<lambda>x. to_nat BoolT)"

instance 
  apply (intro_classes, simp_all add:MkBool_vdmv_def DestBool_vdmv_def BoolUType_vdmv_def type_rel_def utype_rel_vdmv_def embTYPE_def)
  apply (auto)
  apply (simp_all add:InjVB_def Inject_bool_def Defined_vdmv_def MkBool_vdmv_def image_def)
  apply (force)
  apply (erule vbtypes_type_cases)
  apply (auto)
done
end

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

lemma ProjBasicD_not_basic [simp]: "\<not> IsBasicD x \<Longrightarrow> ProjBasicD x = BotI"
  by (case_tac x, auto)

lemma embTYPE_inv_FuncT:
  "prjTYPE (embTYPE (a \<rightarrow> b) :: vdmv UTYPE) = (a \<rightarrow> b)"
  apply (rule_tac embTYPE_inv[of "FuncD (\<lambda> x. BotD)"])
  apply (auto simp add: utype_rel_vdmv_def Defined_vdmv_def)
done

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

end