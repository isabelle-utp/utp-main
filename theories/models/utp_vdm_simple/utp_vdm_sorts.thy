theory utp_vdm_sorts
imports 
  "../../core/utp_sorts"
  "../../alpha/utp_alpha_pred" 
  "../../alpha/utp_alpha_map" 
  utp_vdm_inject 
begin

instantiation vdmval :: VALUE
begin

(*
definition utype_rel_vval :: "vval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vval x u = \<exists> t :: vdmtype. u = emb\<cdot>(Def t) \<and> x :\<^sub>v t)"
*)

lemma Defined_nbot [simp]: "\<D>\<^sub>v x \<Longrightarrow> x \<noteq> BotV"
  by (auto)

definition utype_rel_vdmval :: "vdmval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_vdmval x u = (\<exists> t :: vdmtype. u = to_nat t \<and> x :\<^sub>v t)"

definition Defined_vdmval :: "vdmval \<Rightarrow> bool" where
"Defined_vdmval \<equiv> \<D>\<^sub>v"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_vdmval_def Defined_vdmval_def)
  apply (rule_tac x="to_nat BoolT" in exI)
  apply (force)
done
end

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
  "\<lbrakk>(x::vdmval) : a; \<And> t. \<lbrakk> a = embTYPE t; x :\<^sub>v t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis type_rel_vdmtype_exists)

lemma BotV_type: "BotV :\<^sub>v a"
  by (auto)

lemma type_rel_vdmtype [simp]: "x : t \<longleftrightarrow> x :\<^sub>v prjTYPE t"
  apply (auto simp add: type_rel_def utype_rel_vdmval_def prjTYPE_def)
  apply (metis Rep_UTYPE_elim from_nat_to_nat utype_rel_vdmval_def)
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

lemma embTYPE_inv_SetT:
  "prjTYPE (embTYPE (SetT t) :: vdmval UTYPE) = SetT t"
  apply (rule_tac embTYPE_inv[of "SetV {}"])
  apply (auto simp add: utype_rel_vdmval_def Defined_vdmval_def)
done

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
  apply (auto simp add:utype_rel_vdmval_def Defined_vdmval_def embTYPE_inv_SetT)
  apply (metis (lifting) CollectD IsBasicV.simps(1) ProjBasicV_inv set_mp vbtypes_type_cases vdefined.simps(1))
  apply (simp add:image_def MkSet_vdmval_def)
  apply (erule SetT_type_cases)
  apply (auto)
  apply (rule_tac x="BasicV ` xs" in bexI)
  apply (auto)
done

end

lemma ProjBasicV_inv [simp]: 
  "x \<in> vbvalues \<Longrightarrow> BasicV (ProjBasicV x) = x"
  by (auto simp add:vbvalues_def)

lemma ProjBasicV_not_basic [simp]: "\<not> IsBasicV x \<Longrightarrow> ProjBasicV x = BotI"
  by (case_tac x, auto)

lemma embTYPE_inv_FuncT:
  "prjTYPE (embTYPE (a → b) :: vdmval UTYPE) = (a → b)"
  apply (rule_tac embTYPE_inv[of "FuncV (\<lambda> x. BotV)"])
  apply (auto simp add: utype_rel_vdmval_def Defined_vdmval_def)
done

instantiation vdmval :: FUNCTION_SORT
begin

definition "MkFunc_vdmval f = FuncV (f \<circ> BasicV)"
definition "DestFunc_vdmval f = (\<lambda> x. (ProjFuncV f) (ProjBasicV x))"
definition "IsFunc_vdmval f = ({x. f x \<noteq> BotV} \<subseteq> range BasicV \<and> f BotV = BotV)"
definition FuncType_vdmval :: "vdmval UTYPE \<Rightarrow> vdmval UTYPE \<Rightarrow> vdmval UTYPE" where
"FuncType_vdmval a b = embTYPE (FuncT (prjTYPE a) (prjTYPE b))"

instance 
  apply (intro_classes)
  apply (rule ext)
  apply (simp add:DestFunc_vdmval_def MkFunc_vdmval_def IsFunc_vdmval_def FuncType_vdmval_def)
  apply (clarify)
  apply (case_tac "IsBasicV x")
  apply (simp)
  apply (simp add: subset_iff)
  apply (metis IsBasicV.simps(1) image_iff)
  apply (metis Defined_vdmval_def MkFunc_vdmval_def vdefined.simps(3))
  apply (simp add:MkFunc_vdmval_def IsFunc_vdmval_def dcarrier_def FuncType_vdmval_def embTYPE_inv_FuncT Defined_vdmval_def)
  apply (auto)
  apply (rule)
  apply (force)
  apply (force)
  apply (erule FuncT_type_cases)
  apply (rule_tac x="f \<circ> ProjBasicV" in exI)
  apply (clarify)
  apply (rule)
  apply (force)
  apply (rule)
  apply (rule)
  apply (rule)
  apply (auto)[1]
  apply (metis (lifting) BasicV_type_cases BotI_type ProjBasicV_not_basic utp_vdm_values.ProjBasicV_inv)
  apply (simp)
  apply (smt ProjBasicV_not_basic UNIV_I image_iff mem_Collect_eq subsetI utp_vdm_values.ProjBasicV_inv)
  apply (force)
  apply (simp_all add:FuncType_vdmval_def)
  apply (metis (lifting) embTYPE_inv_FuncT prjTYPE_inv_vdm vdmtype.simps(9))+
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

definition vdm_enc_var ::
  "vdmval VAR \<Rightarrow> vbasic" where
"vdm_enc_var v = RecI [NameI (name v), TypeI (prjTYPE (vtype v)), BoolI (aux v)]"

definition vdm_dec_var ::
  "vbasic \<Rightarrow> vdmval VAR" where
"vdm_dec_var v = 
  (let r = the (ProjRecI v) 
    in MkVar (the (ProjNameI (r!0))) (embTYPE (the (ProjTypeI (r!1)))) (the (ProjBoolI (r!2))))"

lemma vdm_enc_var_inv [simp]:
  "vdm_dec_var (vdm_enc_var v) = v"
  by (simp add:vdm_enc_var_def vdm_dec_var_def MkVar_def)

abbreviation "VarT \<equiv> RecordT [NameT, TypeT, BoolT]"

lemma vdm_enc_var_type [typing]:
  "vdm_enc_var v :\<^sub>b VarT"
  by (force simp add:vdm_enc_var_def)

(*
lemma "xs < ys \<Longrightarrow> RecI xs < RecI ys"
*)

lemma vdm_enc_var_strict_mono [simp]:
  "strict_mono vdm_enc_var"
  apply (simp add:strict_mono_def vdm_enc_var_def)
  sorry

definition vdm_enc_value :: "vdmval \<Rightarrow> vbasic" where
"vdm_enc_value v = ProjBasicV v"

fun vdm_dec_value :: "vbasic \<Rightarrow> vdmval" where
"vdm_dec_value (OptionI (Some v)) = BasicV v" |
"vdm_dec_value (OptionI None) = BotV" |
"vdm_dec_value _ = BotV"

lemma vdm_enc_value_inv [simp]:
  "v \<in> vbvalues \<Longrightarrow> vdm_dec_value (vdm_enc_value v) = v"
  apply (simp add:vdm_enc_value_def)
  apply (case_tac v)
  apply (simp_all add:vbvalues_def)
done

definition vdm_enc_binding :: 
  "vdmval ALPHABET \<Rightarrow> vdmval WF_BINDING \<Rightarrow> vbasic" where
"vdm_enc_binding a b =
  (let bf = fmap_list (binding_fmap a b)
    in PairI (FinI (map (vdm_enc_var \<circ> fst) bf)) (RecI (map (vdm_enc_value \<circ> snd) bf)))"

fun vdm_dec_binding ::
  "vbasic \<Rightarrow> vdmval WF_BINDING" where
"vdm_dec_binding (PairI (FinI vs) (RecI bs)) 
  = fmap_binding 
      (list_fmap 
         (zip (map vdm_dec_var vs) (map vdm_dec_value bs)))"

lemma vdm_enc_binding_inv [simp]:
  assumes "\<forall>v\<in>\<^sub>fa. prjTYPE (vtype v) \<in> vbtypes" 
  shows "vdm_dec_binding (vdm_enc_binding a b) \<cong> b on \<langle>a\<rangle>\<^sub>f"
proof -

  have map_simp:
        "map (vdm_dec_value \<circ> (vdm_enc_value \<circ> snd)) (fmap_list (binding_fmap a b)) =
        map snd (fmap_list (binding_fmap a b))" (is "?A = ?B")
  proof -
    have "?A = map (vdm_dec_value \<circ> vdm_enc_value) (map snd (fmap_list (binding_fmap a b)))"
      by (metis map_map)

    also have "... = map snd (fmap_list (binding_fmap a b))"
    proof -
      from assms have "\<forall> x \<in> set (map snd (fmap_list (binding_fmap a b))). x \<in> vbvalues"
        apply (simp add: fmap_list_binding_fmap)
        apply (rule ballI)
        apply (drule_tac x="x" in spec)
        apply (simp)
        apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b x : vtype x")
        apply (simp)
        apply (erule vbtypes_type_cases)
        apply (simp add:vbvalues_def)
        apply (simp add:vbvalues_def)
        apply (simp_all add:vbvalues_def vbtypes_def)
        apply (force)
        apply (metis binding_type type_rel_vdmtype)
      done

      with assms show ?thesis
        by (metis (no_types) map_idI o_def vdm_enc_value_inv)
    qed
    
    ultimately show ?thesis by simp

  qed
  
  show ?thesis
    apply (simp add:vdm_enc_binding_def)
    apply (simp add:Let_def)
    apply (simp add:map_simp)
    apply (unfold comp_def)
    apply (simp only: vdm_enc_var_inv zip_map_fst_snd)
    apply (simp)
    apply (subgoal_tac "vdm_dec_var \<circ> (vdm_enc_var \<circ> fst) = fst")
    apply (metis binding_fmap_inv)
    apply (simp add:comp_def)
  done
qed

lemma vdm_enc_binding_type [typing]:
  assumes "\<forall>v\<in>\<^sub>fa. prjTYPE (vtype v) \<in> vbtypes" 
  shows "vdm_enc_binding a b :\<^sub>b  
         PairT (FSetT VarT) (RecordT (map (OptionT \<circ> prjTYPE \<circ> vtype) (flist a)))"
  proof -

    obtain xs where xs_def: "a = fset xs" and xs_props: "distinct xs" "sorted xs"
      by (metis flist_inv flist_props(1) flist_props(2))
      
    with assms have "\<forall>v\<in>\<^sub>ffset xs. prjTYPE (vtype v) \<in> vbtypes" 
      by simp

    with xs_props
    have "map (\<lambda>x. vdm_enc_value (\<langle>b\<rangle>\<^sub>b x)) xs :\<^sub>r map (\<lambda>x. OptionT (prjTYPE (vtype x))) xs"
    proof (induct xs)
      case Nil thus ?case by (force)

    next

      case (Cons y ys)
      thus ?case
        apply (simp add:vdm_enc_value_def)
        apply (rule)
        apply (case_tac "\<langle>b\<rangle>\<^sub>b y = BotV")
        apply (simp)
        apply (force)

        sorry
    qed

    with xs_props show ?thesis
      apply (simp add:vdm_enc_binding_def Let_def)
      apply (rule)
      apply (rule)
      apply (simp add: fmap_list_binding_fmap typing)
      apply (simp add: map_map[THEN sym])
      apply (metis flist_fimage flist_props(1) vdm_enc_var_strict_mono)
      apply (simp add: map_map[THEN sym])
      apply (metis flist_fimage flist_props(2) vdm_enc_var_strict_mono)
      apply (rule)
      apply (simp add: fmap_list_binding_fmap typing comp_def xs_def)
    done
qed

end