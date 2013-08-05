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

instantiation cmlv :: VALUE
begin

definition utype_rel_cmlv :: "cmlv \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_cmlv x u = (\<exists> t :: cmlt. u = to_nat t \<and> x :\<^sub>v t)"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_cmlv_def)
  apply (rule_tac x="to_nat BoolT" in exI)
  apply (force)
done
end

lemma cmlt_UTYPE [simp]: "\<lbrakk> v :\<^sub>v t; \<D> v \<rbrakk> \<Longrightarrow> to_nat t \<in> UTYPES (TYPE(cmlv))"
  by (auto simp add:UTYPES_def utype_rel_cmlv_def)

lemma prjTYPE_inv_cmlt [simp]
  : "embTYPE ((prjTYPE t) :: cmlt) = (t :: cmlv UTYPE)"
  apply (simp add:prjTYPE_def embTYPE_def)
  apply (case_tac t)
  apply (auto simp add: utype_rel_cmlv_def UTYPES_def)
done

lemma prjTYPE_cmlt_inj:
  "(prjTYPE (x :: cmlv UTYPE) :: cmlt) = prjTYPE y \<Longrightarrow> x = y"
  by (metis prjTYPE_inv_cmlt)

lemma embTYPE_inv_cmlt [simp]:
  "prjTYPE (embTYPE (t :: cmlt) :: cmlv UTYPE) = t"
  apply (rule embTYPE_inv[of "default_cmlt t"])
  apply (simp_all add:utype_rel_cmlv_def typing defined embTYPE_inv)
done

lemma embTYPE_cmlt_inj:
  "(embTYPE (x :: cmlt) :: cmlv UTYPE) = embTYPE y \<Longrightarrow> x = y"
  by (metis embTYPE_inv_cmlt)

lemma embTYPE_cmlt_inj' [simp]:
  "inj (embTYPE :: cmlt \<Rightarrow> cmlv UTYPE)"
  by (metis embTYPE_inv_cmlt injI)

lemma type_rel_cmlt_exists: 
  "(x::cmlv) : a \<Longrightarrow> \<exists> t. a = embTYPE t \<and> x :\<^sub>v t" 
  apply (simp add:type_rel_def)
  apply (simp add:utype_rel_cmlv_def)
  apply (case_tac a)
  apply (auto simp add:UTYPES_def)
  apply (rule_tac x="t" in exI)
  apply (simp add:embTYPE_def)
done

lemma type_rel_cmlt_elim [elim]:
  "\<lbrakk>(x::cmlv) : a; \<And> t. \<lbrakk> a = embTYPE t; x :\<^sub>v t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis type_rel_cmlt_exists)

lemma type_rel_cmlt: 
  "x : t \<longleftrightarrow> x :\<^sub>v prjTYPE t"
  apply (auto simp add: type_rel_def utype_rel_cmlv_def prjTYPE_def)
  apply (metis Rep_UTYPE_elim from_nat_to_nat utype_rel_cmlv_def)
done

lemma carrier_embTYPE:
  "carrier (embTYPE t) = vcarrier t"
  by (simp add:carrier_def type_rel_cmlt vcarrier_def)

lemma dcarrier_embTYPE:
  "dcarrier (embTYPE t) = {x. x :\<^sub>v t \<and> \<D> x}"
  by (simp add:dcarrier_def type_rel_cmlt vcarrier_def)

instantiation cmlv :: BOT_SORT
begin

definition ubot_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv" where
"ubot_cmlv = BotD \<circ> prjTYPE"

instance
  apply (intro_classes)
  apply (auto simp add:ubot_cmlv_def type_rel_cmlt)
done
end

subsection {* Int sort instantiation *}

(*
instantiation cmlv :: INT_SORT
begin

definition MkInt_cmlv where "MkInt_cmlv (x::int) = BasicD (IntI x)"
definition DestInt_cmlv where "DestInt_cmlv x = the (ProjIntI (ProjBasicD x))"
definition IntType_cmlv :: "cmlv UTYPE" where 
"IntType_cmlv = embTYPE IntT"

instance 
  apply (intro_classes, simp_all add:MkInt_cmlv_def DestInt_cmlv_def IntType_cmlv_def type_rel_def utype_rel_cmlv_def)
  apply (auto simp add:dcarrier_def type_rel_cmlt image_def MkInt_cmlv_def)
done
end
*)

subsection {* Bool sort instantiation *}

instantiation cmlv :: BOOL_SORT
begin

definition MkBool_cmlv where "MkBool_cmlv (x::bool) = BasicD (BoolI x)"
definition DestBool_cmlv where "DestBool_cmlv x = the (ProjBoolI (ProjBasicD x))"
definition BoolType_cmlv :: "cmlv UTYPE" where 
"BoolType_cmlv = embTYPE BoolT"

instance 
  apply (intro_classes, simp_all add:MkBool_cmlv_def DestBool_cmlv_def BoolType_cmlv_def type_rel_def utype_rel_cmlv_def)
  apply (auto simp add:dcarrier_def type_rel_cmlt image_def MkBool_cmlv_def monotype_def)
  apply (metis BasicD_type_cases BoolI_type_cases prjTYPE_inv_cmlt)
done
end

lemma MkBool_cmlv [simp]: 
  "MkBool x = BasicD (Inject x)"
  by (simp add:MkBool_cmlv_def Inject_bool_def)

abbreviation "StringBT \<equiv> ListBT CharBT"
abbreviation "StringI xs \<equiv> ListI CharBT (map CharI xs)"
abbreviation "ProjStringI xs \<equiv> map (the \<circ> ProjCharI) (the (ProjListI xs))"

lemma StringI_type [typing]:
  "StringI xs :\<^sub>b StringBT"
  by (auto)

lemma ProjCharI_comp_CharI [simp]:
  "ProjCharI \<circ> CharI = Some"
  by (auto)

instantiation cmlv :: STRING_SORT
begin

definition MkStr_cmlv where "MkStr_cmlv (x::string) = BasicD (StringI x)"
definition DestStr_cmlv where "DestStr_cmlv x = ProjStringI (ProjBasicD x)"
definition StringType_cmlv :: "cmlv UTYPE" where 
"StringType_cmlv = embTYPE StringT"

instance
  apply (intro_classes)
  apply (auto simp add:MkStr_cmlv_def DestStr_cmlv_def StringType_cmlv_def 
                       type_rel_cmlt image_def)
  apply (metis ProjCharI_comp_CharI comp_apply map_idI map_map the.simps the_Some)
  apply (metis CharT_type_cases Defined_vbasic.simps(1) ex_map_conv)
done
end

subsection {* List sort instantiation *}

instantiation cmlv :: LIST_SORT
begin

definition MkList_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv list \<Rightarrow> cmlv" where
"MkList_cmlv a xs = BasicD (ListI (ProjBasicT (prjTYPE a)) (map ProjBasicD xs))"

definition DestList_cmlv :: "cmlv \<Rightarrow> cmlv list" where
"DestList_cmlv x = map BasicD (the (ProjListI (ProjBasicD x)))"

definition ListType_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv UTYPE" where
"ListType_cmlv a = (if (prjTYPE a \<in> vbtypes) then embTYPE (ListT (prjTYPE a)) else a)"

definition ListPerm_cmlv :: "cmlv UTYPE set" where
"ListPerm_cmlv = embTYPE ` vbtypes"

lemma foldr_over_prop:
  "foldr (op \<and> \<circ> P) xs True = (\<forall> x \<in> set xs. P x)"
  by (induct xs, auto)

instance
  apply (intro_classes)
  apply (unfold_locales)
  apply (auto simp add:MkList_cmlv_def DestList_cmlv_def ListType_cmlv_def ListPerm_cmlv_def dcarrier_def type_rel_cmlt image_def vbtypes_def)
  apply (subgoal_tac "map (BasicD \<circ> ProjBasicD) x = map id x")
  apply (force)
  apply (unfold map_eq_conv)
  apply (force)
  apply (rule_tac x="map BasicD xs" in exI)
  apply (auto)
  apply (force)
  apply (rule inj_onI)
  apply (simp add:ListType_cmlv_def)
  apply (case_tac "prjTYPE x \<in> vbtypes")
  apply (case_tac[!] "prjTYPE y \<in> vbtypes")
  apply (auto simp add:vbtypes_def)
  apply (metis ProjBasicT.simps embTYPE_inv_cmlt prjTYPE_inv_cmlt vbasict.inject(3))
done
end

subsection {* Finite set instantiation *}

instantiation cmlv :: FSET_SORT
begin

definition MkFSet_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv fset \<Rightarrow> cmlv" where
"MkFSet_cmlv a xs = BasicD (FSetI (ProjBasicT (prjTYPE a)) (ProjBasicD `\<^sub>f xs))"

definition DestFSet_cmlv :: "cmlv \<Rightarrow> cmlv fset" where
"DestFSet_cmlv x = BasicD `\<^sub>f (the (ProjFSetI (ProjBasicD x)))"

definition FSetType_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv UTYPE" where
"FSetType_cmlv a = (if (prjTYPE a \<in> vbtypes) then embTYPE (FSetT (prjTYPE a)) else a)"

definition FSetPerm_cmlv :: "cmlv UTYPE set" where
"FSetPerm_cmlv = embTYPE ` vbtypes"

(*
lemma Rep_fset_eq: 
  "xs = ys \<longleftrightarrow> \<langle>xs\<rangle>\<^sub>f = \<langle>ys\<rangle>\<^sub>f"
  by (auto)

lemma fimage_eq_conv: 
  "inj_on f \<langle>xs\<rangle>\<^sub>f \<Longrightarrow> f `\<^sub>f xs = g `\<^sub>f xs \<longleftrightarrow> (\<forall>x\<in>\<langle>xs\<rangle>\<^sub>f. f x = g x)"
  apply (auto simp add:Rep_fset_eq)
  thm inj_on_Un_image_eq_iff
  
  apply (auto simp add:fimage_def)
*)

instance
  apply (intro_classes)
  apply (unfold_locales)
  apply (auto simp add:MkFSet_cmlv_def DestFSet_cmlv_def FSetType_cmlv_def FSetPerm_cmlv_def type_rel_cmlt dcarrier_embTYPE)
  apply (force simp add:vbtypes_def)
  apply (auto simp add:vbtypes_def)
  apply (frule subsetD, simp)
  apply (auto)
  apply (metis ProjBasicD.simps(1) imageI)
  apply (simp add:image_def MkFSet_cmlv_def)
  apply (rule_tac x="BasicD `\<^sub>f xs" in exI)
  apply (auto)
  apply (rule_tac f="FSetI xa" and g="FSetI xa" in cong, simp)
  apply (auto)
  apply (metis ProjBasicD.simps(1) image_eqI)
  apply (rule, rule, force)
  apply (auto simp add:inj_on_def)
  apply (metis (mono_tags) FSetType_cmlv_def ProjBasicT.simps embTYPE_inv_cmlt rangeI vbasict.inject(1) vbtypes_def)
done
end

subsection {* Set instantiation *}

instantiation cmlv :: SET_SORT
begin

definition MkSet_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv set \<Rightarrow> cmlv" where
"MkSet_cmlv a xs = SetD (ProjBasicT (prjTYPE a)) (ProjBasicD ` xs)"

definition DestSet_cmlv :: "cmlv \<Rightarrow> cmlv set" where
"DestSet_cmlv x = BasicD ` ProjSetD x"

definition SetType_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv UTYPE" where
"SetType_cmlv a = (if (prjTYPE a \<in> vbtypes) then embTYPE (SetT (ProjBasicT (prjTYPE a))) else a)"

definition SetPerm_cmlv :: "cmlv UTYPE set" where
"SetPerm_cmlv = ((embTYPE :: cmlt \<Rightarrow> cmlv UTYPE) ` vbtypes)"

(*
lemma Rep_fset_eq: 
  "xs = ys \<longleftrightarrow> \<langle>xs\<rangle>\<^sub>f = \<langle>ys\<rangle>\<^sub>f"
  by (auto)

lemma fimage_eq_conv: 
  "inj_on f \<langle>xs\<rangle>\<^sub>f \<Longrightarrow> f `\<^sub>f xs = g `\<^sub>f xs \<longleftrightarrow> (\<forall>x\<in>\<langle>xs\<rangle>\<^sub>f. f x = g x)"
  apply (auto simp add:Rep_fset_eq)
  thm inj_on_Un_image_eq_iff
  
  apply (auto simp add:fimage_def)
*)


(*

proof (intro_classes, unfold_locales)
  fix a::"cmlv UTYPE"
  assume "a \<in> SetPerm"
  show "dcarrier (SetType a) = MkSet a ` {xs. id xs \<subseteq> dcarrier a}"
    apply (auto simp add:MkSet_cmlv_def DestSet_cmlv_def SetType_cmlv_def SetPerm_cmlv_def type_rel_cmlt dcarrier_embTYPE)
    apply (simp add:image_def MkSet_cmlv_def)
    apply (rule_tac x="BasicD ` xs" in exI)
    apply (auto)


    apply (auto)

*)
instance 
  apply (intro_classes)
  apply (unfold_locales)
  apply (auto simp add:MkSet_cmlv_def DestSet_cmlv_def SetType_cmlv_def SetPerm_cmlv_def type_rel_cmlt dcarrier_embTYPE)
  apply (force simp add:vbtypes_def)
  apply (auto simp add:vbtypes_def)
  apply (frule subsetD, simp)
  apply (auto)
  apply (metis ProjBasicD.simps(1) imageI)
  apply (simp add:image_def MkSet_cmlv_def)
  apply (rule_tac x="BasicD ` xs" in exI)
  apply (auto intro!:SetD_type)
  apply (auto simp add:inj_on_def)
  apply (metis (mono_tags) ProjBasicT.simps SetType_cmlv_def embTYPE_inv_cmlt rangeI vbtypes_def cmlt.inject(2))
done
end

subsection {* Events and Event Sort Instantiation *}

instantiation cmlv :: EVENT_PERM
begin

definition EventPerm_cmlv :: "cmlv UTYPE set" where
"EventPerm_cmlv = embTYPE ` vbtypes"

instance
  apply (intro_classes)
  apply (auto simp add:EventPerm_cmlv_def)
  apply (rule_tac x="embTYPE NumberT" in exI)
  apply (auto simp add:vbtypes_def)
done

end

lemma EVENT_value_IsBasicD: 
  "IsBasicD (EVENT_value x)"
  by (case_tac x, auto simp add:EventPerm_cmlv_def type_rel_cmlt vbtypes_def)

lemma EVENT_type_vbtypes:
  fixes e :: "cmlv EVENT"
  shows "prjTYPE (uchan_type (EVENT_chan e)) \<in> vbtypes"
  by (case_tac e, auto simp add:EventPerm_cmlv_def)

definition EventI :: "cmlv EVENT \<Rightarrow> vbasic" where
"EventI e = EvI (uchan_name (EVENT_chan e)) 
                (ProjBasicT (prjTYPE (uchan_type (EVENT_chan e))))
                (ProjBasicD (EVENT_value e))"

primrec ProjEventI :: "vbasic \<Rightarrow> cmlv EVENT" where
"ProjEventI (EvI n t v) = EV n (embTYPE (BasicT t)) (BasicD v)"

lemma EventI_type [typing,intro]:
  "EventI e :\<^sub>b EventBT"
  apply (case_tac e)
  apply (auto simp add:EventI_def dtype_rel_def type_rel_cmlt EventPerm_cmlv_def vbtypes_def)
done

lemma EventI_defined [simp]:
  "\<D> (EventI e)"
  by (simp add:EventI_def)

lemma EventI_inv [simp]:
  "ProjEventI (EventI e) = e"
  by (simp add:EventI_def EVENT_value_IsBasicD EVENT_type_vbtypes)

instantiation cmlv :: EVENT_SORT
begin

definition MkEvent_cmlv :: "cmlv EVENT \<Rightarrow> cmlv" where
"MkEvent_cmlv e = BasicD (EventI e)"

definition DestEvent_cmlv :: "cmlv \<Rightarrow> cmlv EVENT" where
"DestEvent_cmlv e = ProjEventI (ProjBasicD e)"

definition EventType_cmlv :: "cmlv UTYPE" where
"EventType_cmlv = embTYPE EventT"

instance
  apply (intro_classes)
  apply (auto simp add:DestEvent_cmlv_def MkEvent_cmlv_def EventType_cmlv_def dcarrier_def type_rel_cmlt image_def)
  apply (rule_tac x="EV n (embTYPE (BasicT  t)) (BasicD v)" in exI)
  apply (subgoal_tac "BasicD v : embTYPE (BasicT t)")
  apply (subgoal_tac "(embTYPE (BasicT t) :: cmlv UTYPE) \<in> EventPerm")
  apply (simp add:EventI_def)
  apply (simp add:EventPerm_cmlv_def vbtypes_def)
  apply (force simp add:type_rel_cmlt)
  apply (simp add:monotype_def type_rel_cmlt)
  apply (auto)
  apply (metis BasicD_type_cases EvI_type_cases prjTYPE_inv_cmlt)
done
end

subsection {* Set sort instantiation *}

(*
instantiation cmlv :: SET_SORT_PRE
begin

  definition MkSet_cmlv :: "cmlv set \<Rightarrow> cmlv" where
  "MkSet_cmlv xs = SetD (ProjBasicD ` xs)"
  
  definition DestSet_cmlv :: "cmlv \<Rightarrow> cmlv set" where
  "DestSet_cmlv v = BasicD ` ProjSetD v"

  definition IsSetElemType_cmlv :: "cmlv UTYPE \<Rightarrow> bool" where
  "IsSetElemType_cmlv t = (prjTYPE t \<in> vbtypes)"

  definition SetType_cmlv :: "cmlv UTYPE \<Rightarrow> cmlv UTYPE" where
  "SetType_cmlv t = embTYPE (SetT (prjTYPE t))"

instance ..

end

lemma embTYPE_inv_SetT:
  "prjTYPE (embTYPE (SetT t) :: cmlv UTYPE) = SetT t"
  apply (rule_tac embTYPE_inv[of "SetD {}"])
  apply (auto simp add: utype_rel_cmlv_def Defined_cmlv_def)
done

instantiation cmlv :: SET_SORT
begin

instance
  apply (intro_classes)
  apply (auto simp add:DestSet_cmlv_def MkSet_cmlv_def SetType_cmlv_def IsSetElemType_cmlv_def type_rel_cmlt)
  apply (drule_tac x="xb" in bspec)
  apply (simp)
  apply (force)
  apply (force)
  apply (simp_all add:dcarrier_def type_rel_cmlt)
  apply (auto)
  apply (subgoal_tac "\<exists> v::cmlv. v :\<^sub>u to_nat (SetT (prjTYPE t)) \<and> \<D> v")
  apply (force)
  apply (rule_tac x="SetD {}" in exI)
  apply (auto simp add:utype_rel_cmlv_def Defined_cmlv_def embTYPE_inv_SetT)
  apply (metis (lifting) CollectD IsBasicD.simps(1) ProjBasicD_inv set_mp vbtypes_type_cases vdefined.simps(1))
  apply (simp add:image_def MkSet_cmlv_def)
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
  "prjTYPE (embTYPE (a \<rightarrow> b) :: cmlv UTYPE) = (a \<rightarrow> b)"
  apply (rule_tac embTYPE_inv[of "FuncD (\<lambda> x. BotD b)"])
  apply (auto simp add: utype_rel_cmlv_def Defined_cmlv_def)
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

instantiation cmlv :: REACTIVE_SORT
begin

instance
  apply (intro_classes)
  apply (auto simp add:EventType_cmlv_def FSetPerm_cmlv_def ListPerm_cmlv_def  
                       SetPerm_cmlv_def ListType_cmlv_def inj_image_mem_iff vbtypes_def)
done

end

end