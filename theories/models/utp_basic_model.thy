theory utp_basic_model
imports 
  "../core/utp_value"
  "../core/utp_sorts"
begin

datatype BV = IntV int | BoolV bool

instantiation BV :: VALUE
begin

fun utype_rel_BV :: "BV \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_BV (IntV n) 0 = True" |
"utype_rel_BV (BoolV x) (Suc 0) = True" |
"utype_rel_BV _ _ = False"

definition Defined_BV :: "BV \<Rightarrow> bool" where
"Defined_BV x = True"

instance
  apply (intro_classes)
  apply (rule_tac x="0" in exI, rule_tac x = "IntV 1" in exI)
  apply (simp add:Defined_BV_def)
done
end

definition "IntT = Abs_UTYPE 0"
definition "BoolT = Abs_UTYPE 1"

lemma IntV_utype [typing]:
  "IntV n :\<^sub>u 0"
  by (simp)

lemma IntV_defined [defined]:
  "\<D> (IntV n)"
  by (simp add:Defined_BV_def)

lemma IntV_type [typing]:
  "IntV n : IntT"
  by (simp add: IntT_def type_rel_def Abs_UTYPE_inv[OF IntV_utype IntV_defined])

lemma BoolV_utype [typing]:
  "BoolV n :\<^sub>u (Suc 0)"
  by (simp)

lemma BoolV_defined [defined]:
  "\<D> (BoolV n)"
  by (simp add:Defined_BV_def)

lemma BoolV_type [typing]:
  "BoolV n : BoolT"
  by (simp add: BoolT_def type_rel_def Abs_UTYPE_inv[OF BoolV_utype BoolV_defined])

instantiation BV :: BOOL_SORT
begin

definition MkBool_BV :: "bool \<Rightarrow> BV" where
"MkBool_BV x = BoolV x"

primrec DestBool_BV :: "BV \<Rightarrow> bool" where
"DestBool_BV (BoolV x) = x" 

definition BoolType_BV :: "BV UTYPE" where
"BoolType_BV = Abs_UTYPE 1"

instance
  apply (intro_classes)
  apply (simp add:MkBool_BV_def DestBool_BV_def BoolType_BV_def dcarrier_def monotype_def Defined_BV_def type_rel_def)
  apply (simp add:MkBool_BV_def DestBool_BV_def BoolType_BV_def dcarrier_def monotype_def Defined_BV_def type_rel_def)
  apply (simp add: Abs_UTYPE_inv[OF BoolV_utype BoolV_defined])
  apply (auto simp add:MkBool_BV_def)
  apply (case_tac x)
  apply (simp)
  apply (simp add:image_def MkBool_BV_def)
  apply (auto simp add:monotype_def BoolType_BV_def Abs_UTYPE_inv[OF BoolV_utype BoolV_defined] type_rel_def)
  apply (case_tac x)
  apply (auto)
  apply (metis (full_types) list_decode.cases utype_rel_BV.simps(3) utype_rel_BV.simps(6))
done
end
