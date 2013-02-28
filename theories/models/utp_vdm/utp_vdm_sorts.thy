theory utp_vdm_sorts
imports 
  "../../core/utp_sorts" 
  utp_vdm_inject 
begin

instantiation vval :: VALUE
begin

(*
definition utype_rel_vval :: "vval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vval x u = \<exists> t :: vtype. u = emb\<cdot>(Def t) \<and> x :\<^sub>v t)"
*)

definition utype_rel_vval :: "vval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vval x u = (\<exists> t :: vtype. u = to_nat t \<and> x :\<^sub>v t)"

definition Defined_vval :: "vval \<Rightarrow> bool" where
"Defined_vval x \<equiv> x \<noteq> \<bottom>"

definition arb_vtype :: "vtype \<Rightarrow> udom" where
"arb_vtype t = \<bottom>"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_vval_def Defined_vval_def)
  apply (rule_tac x="to_nat BoolT" in exI)
  apply (force)
done
end

lemma Defined_BasicV [simp]: "\<D> (BasicV\<cdot>(Def x))"
  by (simp add:Defined_vval_def)

lemma vtype_UTYPE [simp]: "\<lbrakk> v :\<^sub>v t; \<D> v \<rbrakk> \<Longrightarrow> to_nat t \<in> UTYPES (TYPE(vval))"
  by (auto simp add:UTYPES_def utype_rel_vval_def)

lemma prjTYPE_inv_vdm [simp]
  : "embTYPE ((prjTYPE t) :: vtype) = (t :: vval UTYPE)"
  apply (simp add:prjTYPE_def embTYPE_def)
  apply (case_tac t)
  apply (auto simp add: utype_rel_vval_def UTYPES_def)
done

lemma type_rel_vtype_exists: 
  "(x::vval) : a \<Longrightarrow> \<exists> t. a = embTYPE t \<and> x :\<^sub>v t" 
  apply (simp add:type_rel_def)
  apply (simp add:utype_rel_vval_def)
  apply (case_tac a)
  apply (auto simp add:UTYPES_def)
  apply (rule_tac x="t" in exI)
  apply (simp add:embTYPE_def)
done

lemma type_rel_vtype_elim [elim]:
  "\<lbrakk>(x::vval) : a; \<And> t. a = embTYPE t \<and> x :\<^sub>v t \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis type_rel_vtype_exists)

lemma type_rel_vtype [simp]: "x : t \<longleftrightarrow> x :\<^sub>v prjTYPE t"
  apply (auto)
  apply (erule type_rel_vtype_elim)
  apply (auto)
  apply (metis BotV_type Defined_vval_def embTYPE_inv utype_rel_vval_def)
  apply (simp add:type_rel_def utype_rel_vval_def)
  apply (rule_tac x="prjTYPE t" in exI)
  apply (simp add:prjTYPE_def)
  apply (case_tac t)
  apply (auto simp add:UTYPES_def utype_rel_vval_def)
done

instantiation vval :: BOT_SORT
begin

definition ubot_vval :: "vval" where
"ubot_vval = \<bottom>"

instance
  apply (intro_classes)
  apply (simp add:ubot_vval_def Defined_vval_def)
done
end

lemma Defined_bval [simp]: "\<D> (InjVB x)"
  by (simp add:Defined_vval_def InjVB_def InjB_def)

lemma Defined_bot [simp]: "\<D> (\<bottom> :: vval) \<longleftrightarrow> False"
  by (simp add:Defined_vval_def)

lemma Defined_ubot [simp]: "\<D> \<bottom>v \<longleftrightarrow> False"
  by (simp add:Defined_vval_def)

(*
lemma vval_UTYPE_nbot [simp]: 
  "(from_nat (Rep_UTYPE (t :: vval UTYPE)) :: vtype lift) \<noteq> \<bottom>"
  apply (case_tac t)
  apply (auto simp add: UTYPES_def utype_rel_vval_def)
  apply (auto)
done

lemma vval_UTYPE_Def [simp]: 
  "\<exists> x. (prj\<cdot>(Rep_UTYPE (a :: vval UTYPE)) :: vtype lift) = Def x"
  apply (case_tac a)
  apply (simp add: UTYPES_def)
  apply (simp add: utype_rel_vval_def)
  apply (auto)
done

lemma vval_UTYPE_elim [elim]:
  assumes "\<And> x. (prj\<cdot>(Rep_UTYPE (a :: vval UTYPE)) :: vtype lift) = Def x \<Longrightarrow> P" 
  shows "P"
  by (metis assms vval_UTYPE_Def)
*)
subsection {* Int sort instantiation *}

instantiation vval :: INT_SORT
begin

definition MkInt_vval where "MkInt_vval (x::int) = InjVB x"
definition DestInt_vval where "DestInt_vval x = (ProjVB x :: int)"
definition IntUType_vval :: "vval itself \<Rightarrow> nat" where 
"IntUType_vval = (\<lambda> x. to_nat IntT)"

instance 
  apply (intro_classes, simp_all add:MkInt_vval_def DestInt_vval_def IntUType_vval_def type_rel_def utype_rel_vval_def embTYPE_def)
  apply (auto)
  apply (simp_all add:InjVB_def InjB_def Inject_int_def Defined_vval_def MkInt_vval_def image_def)
  apply (force)+
done
end

subsection {* Bool sort instantiation *}

instantiation vval :: BOOL_SORT
begin

definition MkBool_vval where "MkBool_vval (x::bool) = InjVB x"
definition DestBool_vval where "DestBool_vval x = (ProjVB x :: bool)"
definition BoolUType_vval :: "vval itself \<Rightarrow> nat" where 
"BoolUType_vval = (\<lambda>x. to_nat BoolT)"

instance 
  apply (intro_classes, simp_all add:MkBool_vval_def DestBool_vval_def BoolUType_vval_def type_rel_def utype_rel_vval_def embTYPE_def)
  apply (auto)
  apply (simp_all add:InjVB_def InjB_def Inject_bool_def Defined_vval_def MkBool_vval_def image_def)
  apply (force)
  apply (erule vbtypes_type_cases)
  apply (auto)
done
end

subsection {* Set sort instantiation *}

instantiation vval :: SET_SORT_PRE
begin

  definition MkSet_vval :: "vval set \<Rightarrow> vval" where
  "MkSet_vval xs = SetV\<cdot>(set2cset (Rep_cfun ProjBasicV ` xs))"
  
  definition DestSet_vval :: "vval \<Rightarrow> vval set" where
  "DestSet_vval v = Rep_cfun BasicV ` cset2set (ProjSetV\<cdot>v)"

  definition IsSetElemType_vval :: "vval UTYPE \<Rightarrow> bool" where
  "IsSetElemType_vval t = (prjTYPE t \<in> vbtypes)"

  definition SetType_vval :: "vval UTYPE \<Rightarrow> vval UTYPE" where
  "SetType_vval t = embTYPE (SetT (prjTYPE t))"

instance ..

end

instantiation vval :: SET_SORT
begin

instance
  apply (intro_classes)
  apply (simp add:DestSet_vval_def MkSet_vval_def IsSetElemType_vval_def)
  apply (clarify)
  apply (subgoal_tac "(Rep_cfun ProjBasicV ` vs) \<subseteq> flat")
  apply (force)
  apply (simp add:flat_def)
  apply (auto)[1]
  apply (drule_tac x="xa" in bspec)
  apply (simp)
  apply (clarify)
  apply (erule vbtypes_type_cases)
  apply (simp_all)
  apply (simp add:dcarrier_def)
  apply (simp add:SetType_vval_def MkSet_vval_def IsSetElemType_vval_def)
  apply (subgoal_tac "\<exists> v::vval. v :\<^sub>u to_nat (SetT (prjTYPE t)) \<and> \<D> v")
  apply (clarify)
  apply (auto)
  apply (simp add:MkSet_vval_def)
  apply (rule SetV_type)
  apply (auto)
  apply (subgoal_tac "(Rep_cfun ProjBasicV ` xa) \<subseteq> flat")
  apply (force)
  apply (auto)[1]
  apply (simp add:flat_def carrier_def)
  apply (drule_tac c="xc" in rev_subsetD)
  apply (auto)
  apply (simp add:MkSet_vval_def Defined_vval_def)
  apply (subgoal_tac "Rep_cfun ProjBasicV ` xa \<subseteq> flat")
  apply (subgoal_tac "\<exists> (x::vbasic lift). x \<in> flat")
  apply (simp)
  apply (metis Cfun_Partial.flat_def CollectI flat_value_Def)
  apply (force simp add:flat_def)
  apply (erule SetT_type_cases)
  apply (auto)
  apply (simp add:image_def MkSet_vval_def)
  apply (rule_tac x="Rep_cfun BasicV ` (cset2set xs)" in bexI)
  apply (auto)

  apply (rule_tac cset2set_inv[THEN sym])
  apply (auto)
  thm set2cset_nbot
  apply (drule set2cset_nbot)
  apply (simp)
  apply (erule vbtypes_type_cases)
  apply (force)
  apply (simp)
  apply (simp)

  apply (simp add: SET_SORT_PRE.IsSet_def)


end

(*
instantiation vval :: FUNCTION_SORT
begin

definition MkFunc_vval where "MkFunc_vval f = FuncV\<cdot>(\<Lambda>! x. f x)"
definition DestFunc_vval where "DestFunc_vval f \<equiv> \<lambda> x. (sfun_rep\<cdot>(ProjFuncV\<cdot>f))\<cdot>x"
definition IsFunc_vval :: "(vval \<Rightarrow> vval) \<Rightarrow> bool" where
"IsFunc_vval f \<equiv> cont f \<and> f \<bottom> = \<bottom> \<and> (\<exists>x. x \<noteq> \<bottom> \<and> f x \<noteq> \<bottom>)"
definition FuncType_vval :: "vval UTYPE \<Rightarrow> vval UTYPE \<Rightarrow> vval UTYPE" where
"FuncType_vval a b \<equiv>
  case (prj\<cdot>(Rep_UTYPE a), prj\<cdot>(Rep_UTYPE b)) of
    (Def a', Def b') \<Rightarrow> embTYPE (FuncT a' b') |
    _ \<Rightarrow> Abs_UTYPE (emb\<cdot>(\<bottom> :: vtype lift))"

instance proof
  fix f :: "vval \<Rightarrow> vval"

  assume isFunc: "IsFunc f"
  from isFunc show "DestFunc (MkFunc f) = f"
    by (simp add:MkFunc_vval_def DestFunc_vval_def IsFunc_vval_def)

  from isFunc show "\<D> (MkFunc f)"
    apply (auto simp add:Defined_vval_def IsFunc_vval_def MkFunc_vval_def FuncType_vval_def sfun_eq_iff)
    apply (metis Abs_cfun_inverse2 Rep_cfun_strict1)
  done

  fix a b :: "vval UTYPE"
  assume funcRange: "\<forall>x. x : a \<longrightarrow> f x : b"
  from isFunc funcRange show "MkFunc f : FuncType a b"
    apply (auto simp add: MkFunc_vval_def type_rel_def utype_rel_vval_def IsFunc_vval_def)
    apply (simp add:FuncType_vval_def)
    apply (insert vval_UTYPE_Def[of "a"])
    apply (erule exE)
    apply (simp)
    apply (insert vval_UTYPE_Def[of "b"])
    apply (erule exE)
    apply (simp add:embTYPE_def)

    apply (rule FuncV_type)
    apply (auto)
    apply (metis (lifting) BasicV_type Rep_UTYPE_elim emb_inverse lift.inject utype_rel_vval_def)
  done
qed
end



lemma carrier_vcarrier [simp]: "carrier t = vcarrier (prjTYPE t)"
  by (simp add:carrier_def vcarrier_def)

lemma prjTYPE_vval_IntT [simp]: 
  "prjTYPE (IntType :: vval UTYPE) = IntT"
  by (auto intro!: embTYPE_inv simp add:utype_rel_vval_def IntType_vval_def)

lemma prjTYPE_vval_BoolT [simp]: 
  "prjTYPE (BoolType :: vval UTYPE) = BoolT"
  by (auto intro!: embTYPE_inv simp add:utype_rel_vval_def BoolType_vval_def)

lemma prjTYPE_vval_FuncT [simp]:
  "prjTYPE (FuncType a b :: vval UTYPE) = prjTYPE a → prjTYPE b"
  apply (case_tac a)
  apply (simp)
  apply (simp add:FuncType_vval_def)
  apply (insert vval_UTYPE_Def[of a])
  apply (insert vval_UTYPE_Def[of b])
  apply (erule exE)
  apply (erule exE)
  apply (simp)
  apply (auto)
  apply (metis Abs_UTYPE_inverse Undef.simps embTYPE_def emb_inverse prjTYPE_def vtype_UTYPE)
done
*)

end