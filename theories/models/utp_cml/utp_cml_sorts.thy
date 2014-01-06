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

lemma cmlt_UTYPE [simp]: 
  "\<lbrakk> v :\<^sub>v t; \<D> v \<rbrakk> \<Longrightarrow> to_nat t \<in> UTYPES (TYPE(cmlv))"
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

lemma DestBool_TrueD [simp]: 
  "DestBool TrueD = True"
  by (metis BOOL_SORT_class.Inverse MkBool_cmlv_def)

lemma DestBool_FalseD [simp]: 
  "DestBool FalseD = False"
  by (metis BOOL_SORT_class.Inverse MkBool_cmlv_def)

lemma TrueD_compat [typing]:
  "vtype x = BoolType \<Longrightarrow> TrueD \<rhd> x"
  by (metis MkBool_True_compat MkBool_cmlv_def)

lemma FalseD_compat [typing]:
  "vtype x = BoolType \<Longrightarrow> FalseD \<rhd> x"
  by (metis MkBool_False_compat MkBool_cmlv_def)

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
  apply (metis CharT_type_cases Defined_vbasic.simps(2) ex_map_conv)
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
  apply (metis ProjBasicT.simps embTYPE_inv_cmlt prjTYPE_inv_cmlt vbasict.inject(2))
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

subsection {* Set Sort instantiation *}

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

subsection {* Reactive Sort instantiation *}

instantiation cmlv :: REACTIVE_SORT
begin

instance
  apply (intro_classes)
  apply (auto simp add:EventType_cmlv_def FSetPerm_cmlv_def ListPerm_cmlv_def  
                       SetPerm_cmlv_def ListType_cmlv_def inj_image_mem_iff vbtypes_def)
done

end

(*
instantiation cmlv :: VALUE_RANK
begin

fun rank_cmlv :: "cmlv \<Rightarrow> nat" where
"rank_cmlv (SetD a xs) = 1" |
"rank_cmlv (FuncD a b f) = 1" |
"rank_cmlv (BasicD x) = 0" |
"rank_cmlv (BotD' (BasicT a)) = 0" |
"rank_cmlv (BotD' a) = 1"

definition max_rank_cmlv :: "cmlv itself \<Rightarrow> nat" where
"max_rank_cmlv a = 1"

instance 
  apply (intro_classes)
  sorry
end
*)

lift_definition fmap_map_value :: "('a \<Rightarrow> 'b) \<Rightarrow> ('k, 'a) fmap \<Rightarrow> ('k, 'b) fmap"
is "\<lambda> (f :: 'a \<Rightarrow> 'b) (m :: 'k \<rightharpoonup> 'a) (x :: 'k). Option.map f (m x)"
  by (auto simp add:fmaps_def dom_def)

definition var_to_vbasic :: "cmlv VAR \<Rightarrow> vbasic" where
"var_to_vbasic = (\<lambda> (n,t,a). PairI (NameI n) (PairI (TypeI (prjTYPE t)) (BoolI a)))"

definition alpha_to_vbasic :: "cmlv ALPHABET \<Rightarrow> vbasic" where
"alpha_to_vbasic a = FSetI (PairBT NameBT (PairBT TypeBT BoolBT)) (var_to_vbasic `\<^sub>f a)"

text {* Giving an injection from WF_BINDING into cmlv either requires
that we formalise some sort of dependent map type, or that we rather
use products to represent bindings which is probably easier. But if we
use products this requires that bindings be injectable into lists
which only works if variables have a linear order on them. *}

end