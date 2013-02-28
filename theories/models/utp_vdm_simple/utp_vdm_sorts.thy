theory utp_vdm_sorts
imports 
  "../../core/utp_sorts"
  "../../alpha/utp_alpha_pred" 
  utp_vdm_inject 
begin

instantiation vdmval :: VALUE
begin

(*
definition utype_rel_vval :: "vval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vval x u = \<exists> t :: vdmtype. u = emb\<cdot>(Def t) \<and> x :\<^sub>v t)"
*)

definition utype_rel_vdmval :: "vdmval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vdmval x u = (\<exists> t :: vdmtype. u = to_nat t \<and> x :\<^sub>v t)"

definition Defined_vdmval :: "vdmval \<Rightarrow> bool" where
"Defined_vdmval x \<equiv> x \<noteq> BotV"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_vdmval_def Defined_vdmval_def)
  apply (rule_tac x="to_nat BoolT" in exI)
  apply (force)
done
end

lemma Defined_BasicV [simp]: "\<D> (BasicV x)"
  by (simp add:Defined_vdmval_def)

lemma vdmtype_UTYPE [simp]: "\<lbrakk> v :\<^sub>v t; \<D> v \<rbrakk> \<Longrightarrow> to_nat t \<in> UTYPES (TYPE(vdmval))"
  by (auto simp add:UTYPES_def utype_rel_vdmval_def)

lemma prjTYPE_inv_vdm [simp]
  : "embTYPE ((prjTYPE t) :: vdmtype) = (t :: vdmval UTYPE)"
  apply (simp add:prjTYPE_def embTYPE_def)
  apply (case_tac t)
  apply (auto simp add: utype_rel_vdmval_def UTYPES_def)
done

lemma type_rel_vdmtype_exists: 
  "(x::vdmval) : a \<Longrightarrow> \<exists> t. a = embTYPE t \<and> x :\<^sub>v t" 
  apply (simp add:type_rel_def)
  apply (simp add:utype_rel_vdmval_def)
  apply (case_tac a)
  apply (auto simp add:UTYPES_def)
  apply (rule_tac x="t" in exI)
  apply (simp add:embTYPE_def)
done

lemma type_rel_vdmtype_elim [elim]:
  "\<lbrakk>(x::vdmval) : a; \<And> t. a = embTYPE t \<and> x :\<^sub>v t \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis type_rel_vdmtype_exists)

lemma type_rel_vdmtype [simp]: "x : t \<longleftrightarrow> x :\<^sub>v prjTYPE t"
  apply (auto)
  apply (erule type_rel_vdmtype_elim)
  apply (auto)
  apply (metis BotV_type Defined_vdmval_def embTYPE_inv utype_rel_vdmval_def)
  apply (simp add:type_rel_def utype_rel_vdmval_def)
  apply (rule_tac x="prjTYPE t" in exI)
  apply (simp add:prjTYPE_def)
  apply (case_tac t)
  apply (auto simp add:UTYPES_def utype_rel_vdmval_def)
done

instantiation vdmval :: BOT_SORT
begin

definition ubot_vdmval :: "vdmval" where
"ubot_vdmval = BotV"

instance
  apply (intro_classes)
  apply (simp add:ubot_vdmval_def Defined_vdmval_def)
done
end

lemma Defined_bot [simp]: "\<D> (BotV :: vdmval) \<longleftrightarrow> False"
  by (simp add:Defined_vdmval_def)

lemma Defined_ubot [simp]: "\<D> \<bottom>v \<longleftrightarrow> False"
  by (simp add:Defined_vdmval_def)

(*
lemma vdmval_UTYPE_nbot [simp]: 
  "(from_nat (Rep_UTYPE (t :: vdmval UTYPE)) :: vdmtype lift) \<noteq> \<bottom>"
  apply (case_tac t)
  apply (auto simp add: UTYPES_def utype_rel_vdmval_def)
  apply (auto)
done

lemma vdmval_UTYPE_Def [simp]: 
  "\<exists> x. (prj\<cdot>(Rep_UTYPE (a :: vdmval UTYPE)) :: vdmtype lift) = Def x"
  apply (case_tac a)
  apply (simp add: UTYPES_def)
  apply (simp add: utype_rel_vdmval_def)
  apply (auto)
done

lemma vdmval_UTYPE_elim [elim]:
  assumes "\<And> x. (prj\<cdot>(Rep_UTYPE (a :: vdmval UTYPE)) :: vdmtype lift) = Def x \<Longrightarrow> P" 
  shows "P"
  by (metis assms vdmval_UTYPE_Def)
*)
subsection {* Int sort instantiation *}

instantiation vdmval :: INT_SORT
begin

definition MkInt_vdmval where "MkInt_vdmval (x::int) = InjVB x"
definition DestInt_vdmval where "DestInt_vdmval x = (ProjVB x :: int)"
definition IntUType_vdmval :: "vdmval itself \<Rightarrow> nat" where 
"IntUType_vdmval = (\<lambda> x. to_nat IntT)"

instance 
  apply (intro_classes, simp_all add:MkInt_vdmval_def DestInt_vdmval_def IntUType_vdmval_def type_rel_def utype_rel_vdmval_def embTYPE_def)
  apply (auto)
  apply (simp_all add: Inject_int_def InjVB_def Defined_vdmval_def MkInt_vdmval_def image_def)
  apply (force)+
done
end

subsection {* Bool sort instantiation *}

instantiation vdmval :: BOOL_SORT
begin

definition MkBool_vdmval where "MkBool_vdmval (x::bool) = InjVB x"
definition DestBool_vdmval where "DestBool_vdmval x = (ProjVB x :: bool)"
definition BoolUType_vdmval :: "vdmval itself \<Rightarrow> nat" where 
"BoolUType_vdmval = (\<lambda>x. to_nat BoolT)"

instance 
  apply (intro_classes, simp_all add:MkBool_vdmval_def DestBool_vdmval_def BoolUType_vdmval_def type_rel_def utype_rel_vdmval_def embTYPE_def)
  apply (auto)
  apply (simp_all add:InjVB_def Inject_bool_def Defined_vdmval_def MkBool_vdmval_def image_def)
  apply (force)
  apply (erule vbtypes_type_cases)
  apply (auto)
done
end

subsection {* Set sort instantiation *}

instantiation vdmval :: SET_SORT_PRE
begin

  definition MkSet_vdmval :: "vdmval set \<Rightarrow> vdmval" where
  "MkSet_vdmval xs = SetV (ProjBasicV ` xs)"
  
  definition DestSet_vdmval :: "vdmval \<Rightarrow> vdmval set" where
  "DestSet_vdmval v = BasicV ` ProjSetV v"

  definition IsSetElemType_vdmval :: "vdmval UTYPE \<Rightarrow> bool" where
  "IsSetElemType_vdmval t = (prjTYPE t \<in> vbtypes)"

  definition SetType_vdmval :: "vdmval UTYPE \<Rightarrow> vdmval UTYPE" where
  "SetType_vdmval t = embTYPE (SetT (prjTYPE t))"

instance ..

end

instantiation vdmval :: SET_SORT
begin

instance
  apply (intro_classes)
  apply (auto simp add:DestSet_vdmval_def MkSet_vdmval_def SetType_vdmval_def IsSetElemType_vdmval_def)
  apply (drule_tac x="xb" in bspec)
  apply (simp)
  apply (force)
  apply (force)
  apply (simp_all add:dcarrier_def)
  apply (auto)
  apply (subgoal_tac "\<exists> v::vdmval. v :\<^sub>u to_nat (SetT (prjTYPE t)) \<and> \<D> v")
  apply (force)
  apply (rule_tac x="SetV {}" in exI)
  apply (auto simp add:utype_rel_vdmval_def Defined_vdmval_def)
  apply (subgoal_tac "\<exists> v::vdmval. v :\<^sub>u to_nat (SetT (prjTYPE t)) \<and> \<D> v")
  apply (auto simp add:image_def MkSet_vdmval_def utype_rel_vdmval_def Defined_vdmval_def)
  apply (erule SetT_type_cases)
  apply (simp)
  apply (auto)
  apply (rule_tac x="BasicV ` xs" in bexI)
  apply (auto)
done

end

(*
instantiation vdmval :: FUNCTION_SORT
begin

definition MkFunc_vdmval where "MkFunc_vdmval f = FuncV\<cdot>(\<Lambda>! x. f x)"
definition DestFunc_vdmval where "DestFunc_vdmval f \<equiv> \<lambda> x. (sfun_rep\<cdot>(ProjFuncV\<cdot>f))\<cdot>x"
definition IsFunc_vdmval :: "(vdmval \<Rightarrow> vdmval) \<Rightarrow> bool" where
"IsFunc_vdmval f \<equiv> cont f \<and> f \<bottom> = \<bottom> \<and> (\<exists>x. x \<noteq> \<bottom> \<and> f x \<noteq> \<bottom>)"
definition FuncType_vdmval :: "vdmval UTYPE \<Rightarrow> vdmval UTYPE \<Rightarrow> vdmval UTYPE" where
"FuncType_vdmval a b \<equiv>
  case (prj\<cdot>(Rep_UTYPE a), prj\<cdot>(Rep_UTYPE b)) of
    (Def a', Def b') \<Rightarrow> embTYPE (FuncT a' b') |
    _ \<Rightarrow> Abs_UTYPE (emb\<cdot>(\<bottom> :: vdmtype lift))"

instance proof
  fix f :: "vdmval \<Rightarrow> vdmval"

  assume isFunc: "IsFunc f"
  from isFunc show "DestFunc (MkFunc f) = f"
    by (simp add:MkFunc_vdmval_def DestFunc_vdmval_def IsFunc_vdmval_def)

  from isFunc show "\<D> (MkFunc f)"
    apply (auto simp add:Defined_vdmval_def IsFunc_vdmval_def MkFunc_vdmval_def FuncType_vdmval_def sfun_eq_iff)
    apply (metis Abs_cfun_inverse2 Rep_cfun_strict1)
  done

  fix a b :: "vdmval UTYPE"
  assume funcRange: "\<forall>x. x : a \<longrightarrow> f x : b"
  from isFunc funcRange show "MkFunc f : FuncType a b"
    apply (auto simp add: MkFunc_vdmval_def type_rel_def utype_rel_vdmval_def IsFunc_vdmval_def)
    apply (simp add:FuncType_vdmval_def)
    apply (insert vdmval_UTYPE_Def[of "a"])
    apply (erule exE)
    apply (simp)
    apply (insert vdmval_UTYPE_Def[of "b"])
    apply (erule exE)
    apply (simp add:embTYPE_def)

    apply (rule FuncV_type)
    apply (auto)
    apply (metis (lifting) BasicV_type Rep_UTYPE_elim emb_inverse lift.inject utype_rel_vdmval_def)
  done
qed
end



lemma carrier_vcarrier [simp]: "carrier t = vcarrier (prjTYPE t)"
  by (simp add:carrier_def vcarrier_def)

lemma prjTYPE_vdmval_IntT [simp]: 
  "prjTYPE (IntType :: vdmval UTYPE) = IntT"
  by (auto intro!: embTYPE_inv simp add:utype_rel_vdmval_def IntType_vdmval_def)

lemma prjTYPE_vdmval_BoolT [simp]: 
  "prjTYPE (BoolType :: vdmval UTYPE) = BoolT"
  by (auto intro!: embTYPE_inv simp add:utype_rel_vdmval_def BoolType_vdmval_def)

lemma prjTYPE_vdmval_FuncT [simp]:
  "prjTYPE (FuncType a b :: vdmval UTYPE) = prjTYPE a → prjTYPE b"
  apply (case_tac a)
  apply (simp)
  apply (simp add:FuncType_vdmval_def)
  apply (insert vdmval_UTYPE_Def[of a])
  apply (insert vdmval_UTYPE_Def[of b])
  apply (erule exE)
  apply (erule exE)
  apply (simp)
  apply (auto)
  apply (metis Abs_UTYPE_inverse Undef.simps embTYPE_def emb_inverse prjTYPE_def vdmtype_UTYPE)
done
*)

definition WF_BINDING_MAP :: "('VALUE VAR, 'VALUE) fmap set" where
"WF_BINDING_MAP = {f. \<forall>x. x \<in>\<^sub>f fdom f \<longrightarrow> the (\<langle>f\<rangle>\<^sub>m x) \<rhd> x}"

definition binding_fmap ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_BINDING \<Rightarrow> ('VALUE VAR, 'VALUE) fmap" where
"binding_fmap a b = list_fmap (map (\<lambda> x. (x, \<langle>b\<rangle>\<^sub>b x)) (flist a))"

lemma binding_fmap_rep_eq: 
  assumes "x \<in>\<^sub>f a"
  shows "\<langle>binding_fmap a b\<rangle>\<^sub>m x = Some (\<langle>b\<rangle>\<^sub>b x)"
proof -
  obtain xs where fset: "a = fset xs" and lprops: "sorted xs" "distinct xs"
    by (metis flist_inv flist_props)

  with assms have "x \<in>\<^sub>f fset xs"
    by simp

  with lprops have "\<langle>binding_fmap (fset xs) b\<rangle>\<^sub>m x = Some (\<langle>b\<rangle>\<^sub>b x)"
    apply (induct xs)
    apply (simp add: binding_fmap_def list_fmap.rep_eq)+
    apply (subgoal_tac "flist (finsert xa (fset xs)) = (xa # flist (fset xs))")
    apply (simp add: sorted_Cons)
    apply (metis)
    apply (metis (lifting) distinct.simps(2) fset_cons fset_inv sorted_Cons)
  done

  with fset show ?thesis
    by (simp)
qed

lemma fdom_binding_map [simp]:
  "fdom (binding_fmap a b) = a"
  by (auto simp add:binding_fmap_def)

lemma binding_fmap [closure]:
  "binding_fmap a b \<in> WF_BINDING_MAP"
  apply (unfold WF_BINDING_MAP_def)
  apply (rule CollectI)
  apply (rule allI)
  apply (simp add:binding_fmap_rep_eq)
done

definition fmap_binding ::
  "('VALUE VAR, 'VALUE) fmap \<Rightarrow> 'VALUE WF_BINDING" where
"fmap_binding f = Abs_WF_BINDING (\<lambda> x. if (x \<in>\<^sub>f Fmap.fdom f) then the (\<langle>f\<rangle>\<^sub>m x) else default (vtype x))"

lemma fmap_binding_rep_eq:
  "f \<in> WF_BINDING_MAP \<Longrightarrow> 
   \<langle>fmap_binding f\<rangle>\<^sub>b = (\<lambda> x. if (x \<in>\<^sub>f Fmap.fdom f) then the (\<langle>f\<rangle>\<^sub>m x) else default (vtype x))"
  apply (subgoal_tac "(\<lambda> x. if (x \<in>\<^sub>f Fmap.fdom f) then the (\<langle>f\<rangle>\<^sub>m x) else default (vtype x)) \<in> WF_BINDING")
  apply (simp add:fmap_binding_def)
  apply (unfold WF_BINDING_def)
  apply (unfold WF_BINDING_MAP_def)
  apply (rule CollectI)
  apply (rule allI)
  apply (case_tac "v \<in>\<^sub>f fdom f")
  apply (auto intro:typing defined)
done

lemma binding_fmap_inv:
  "fmap_binding (binding_fmap a b) \<cong> b on \<langle>a\<rangle>\<^sub>f"
  by (simp add:binding_equiv_def closure fmap_binding_rep_eq binding_fmap_rep_eq)

definition predicate_maps :: 
  "'VALUE ALPHABET \<Rightarrow>    'VALUE WF_PREDICATE \<Rightarrow> ('VALUE VAR, 'VALUE) fmap set" where
"predicate_maps a p = binding_fmap a ` destPRED p"

definition maps_predicate :: 
  "('VALUE VAR, 'VALUE) fmap set \<Rightarrow> 'VALUE WF_PREDICATE" where
"maps_predicate fs = mkPRED {b. \<exists>f\<in>fs. fmap_binding f \<cong> b on \<langle>fdom f\<rangle>\<^sub>f}"

lemma predicate_maps_inv[simp]:
  "maps_predicate (predicate_maps (\<alpha> p) (\<pi> p)) = \<pi> p"
  apply (simp add:maps_predicate_def predicate_maps_def)
  apply (subgoal_tac "\<And> b f. (fmap_binding (binding_fmap (\<alpha> p) f) \<cong> b on \<langle>\<alpha> p\<rangle>\<^sub>f) = f \<cong> b on \<langle>\<alpha> p\<rangle>\<^sub>f")
  apply (safe)
  apply (smt UNIV_I WF_ALPHA_PREDICATE_binding_equiv mem_Collect_eq mkPRED_inverse)
  apply (simp)
  apply (rule_tac x="x" in bexI)
  apply (metis binding_fmap_inv)
  apply (simp)
  apply (metis (lifting) binding_equiv_comm binding_equiv_trans binding_fmap_inv)
  apply (metis (lifting) binding_equiv_trans binding_fmap_inv)
done

end