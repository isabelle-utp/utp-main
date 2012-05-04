(******************************************************************************)
(* Title: utp/models/utp_ho2_utils.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho2_utils
imports
  "../models/utp_ho1_value"
  "../models/utp_ho2_value"
begin

section {* Utilities for the HO Models *}

subsection {* HO Variable Types *}

definition IsStdVar1 :: "HO1_TYPE VAR \<Rightarrow> bool" ("IsStdVar") where
"IsStdVar1 x = utp_ho1_value.IsBaseType (type x)"

definition IsStdVar2 :: "HO2_TYPE VAR \<Rightarrow> bool" ("IsStdVar") where
"IsStdVar2 x = utp_ho2_value.IsBaseType (type x)"

definition IsProgVar :: "HO1_TYPE VAR \<Rightarrow> bool" where
"IsProgVar x = IsProgType (type x)"

definition IsProg1Var :: "HO2_TYPE VAR \<Rightarrow> bool" where
"IsProg1Var x = IsProg1Type (type x)"

definition IsProg2Var :: "HO2_TYPE VAR \<Rightarrow> bool" where
"IsProg2Var x = IsProg2Type (type x)"

theorems IsVar_simps =
  IsStdVar1_def
  IsStdVar2_def
  IsProgVar_def
  IsProg1Var_def
  IsProg2Var_def

subsection {* Lifting and Coercion *}

text {*
  There is quite a bit of overloading of notation going on here which may
  potentially slow down parsing. Using generic constants on the other hand
  speeds up parsing but might not identify potential ambiguities. For example,
  it turned out that @{text "(STD.MkInt 1) \<up>VAL \<down>VAL"} cannot fully infer the
  type of the lifting and coercion functions. Not identifying ambiguities is
  I believe the greater evil, hence I did not opt for the consts solution.
*}

subsubsection {* Value Lifting *}

definition Lift_STD_VALUE_HO1 :: "STD_VALUE \<Rightarrow> HO1_VALUE" ("_ \<up>VAL") where
"Lift_STD_VALUE_HO1 v = utp_ho1_value.BaseVal v"

definition Lift_STD_VALUE_HO2 :: "STD_VALUE \<Rightarrow> HO2_VALUE" ("_ \<up>VAL") where
"Lift_STD_VALUE_HO2 v = utp_ho2_value.BaseVal v"

definition Lift_HO1_VALUE_HO2 :: "HO1_VALUE \<Rightarrow> HO2_VALUE" ("_ \<up>VAL") where
"Lift_HO1_VALUE_HO2 v = utp_ho2_value.Prog1Val (utp_ho1_value.ProgOf v)"

definition Coerce_HO1_VALUE_STD :: "HO1_VALUE \<Rightarrow> STD_VALUE" ("_ \<down>VAL") where
"Coerce_HO1_VALUE_STD v = utp_ho1_value.BaseOf v"

definition Coerce_HO2_VALUE_STD :: "HO2_VALUE \<Rightarrow> STD_VALUE" ("_ \<down>VAL") where
"Coerce_HO2_VALUE_STD v = utp_ho2_value.BaseOf v"

definition Coerce_HO2_VALUE_HO1 :: "HO2_VALUE \<Rightarrow> HO1_VALUE" ("_ \<down>VAL") where
"Coerce_HO2_VALUE_HO1 v = utp_ho1_value.ProgVal (utp_ho2_value.Prog1Of v)"

subsubsection {* Type Lifting *}

definition Lift_STD_TYPE_HO1 :: "STD_TYPE \<Rightarrow> HO1_TYPE" ("_ \<up>TYPE") where
"Lift_STD_TYPE_HO1 t = utp_ho1_value.BaseType t"

definition Lift_STD_TYPE_HO2 :: "STD_TYPE \<Rightarrow> HO2_TYPE" ("_ \<up>TYPE") where
"Lift_STD_TYPE_HO2 t = utp_ho2_value.BaseType t"

definition Lift_HO1_TYPE_HO2 :: "HO1_TYPE \<Rightarrow> HO2_TYPE" ("_ \<up>TYPE") where
"Lift_HO1_TYPE_HO2 t = utp_ho2_value.Prog1Type (utp_ho1_value.ProgTypeOf t)"

definition Coerce_HO1_TYPE_STD :: "HO1_TYPE \<Rightarrow> STD_TYPE" ("_ \<down>TYPE") where
"Coerce_HO1_TYPE_STD t = utp_ho1_value.BaseTypeOf t"

definition Coerce_HO2_TYPE_STD :: "HO2_TYPE \<Rightarrow> STD_TYPE" ("_ \<down>TYPE") where
"Coerce_HO2_TYPE_STD t = utp_ho2_value.BaseTypeOf t"

definition Coerce_HO2_TYPE_HO1 :: "HO2_TYPE \<Rightarrow> HO1_TYPE" ("_ \<down>TYPE") where
"Coerce_HO2_TYPE_HO1 t = utp_ho1_value.ProgType (utp_ho2_value.Prog1TypeOf t)"

subsubsection {* Variable Lifting *}

definition Lift_STD_VAR_HO1 :: "STD_TYPE VAR \<Rightarrow> HO1_TYPE VAR" ("_ \<up>VAR") where
"Lift_STD_VAR_HO1 v = VAR.MkVar (name v) (type v) \<up>TYPE"

definition Lift_STD_VAR_HO2 :: "STD_TYPE VAR \<Rightarrow> HO2_TYPE VAR" ("_ \<up>VAR") where
"Lift_STD_VAR_HO2 v = VAR.MkVar (name v) (type v) \<up>TYPE"

definition Lift_HO1_VAR_HO2 :: "HO1_TYPE VAR \<Rightarrow> HO2_TYPE VAR" ("_ \<up>VAR") where
"Lift_HO1_VAR_HO2 v = VAR.MkVar (name v) (type v) \<up>TYPE"

definition Coerce_HO1_VAR_STD :: "HO1_TYPE VAR \<Rightarrow> STD_TYPE VAR" ("_ \<down>VAR") where
"Coerce_HO1_VAR_STD v = VAR.MkVar (name v) (type v) \<down>TYPE"

definition Coerce_HO2_VAR_STD :: "HO2_TYPE VAR \<Rightarrow> STD_TYPE VAR" ("_ \<down>VAR") where
"Coerce_HO2_VAR_STD v = VAR.MkVar (name v) (type v) \<down>TYPE"

definition Coerce_HO2_VAR_HO1 :: "HO2_TYPE VAR \<Rightarrow> HO1_TYPE VAR" ("_ \<down>VAR") where
"Coerce_HO2_VAR_HO1 v = VAR.MkVar (name v) (type v) \<down>TYPE"

subsubsection {* Binding Lifting *}

definition Lift_STD_BINDING_HO1 ::
  "(STD_VALUE, STD_TYPE) BINDING \<Rightarrow>
   (HO1_VALUE, HO1_TYPE) BINDING" ("_ \<up>BIND") where
"Lift_STD_BINDING_HO1 b = (\<lambda> x . b (x \<down>VAR) \<up>VAL)"

definition Lift_STD_BINDING_HO2 ::
  "(STD_VALUE, STD_TYPE) BINDING \<Rightarrow>
   (HO2_VALUE, HO2_TYPE) BINDING" ("_ \<up>BIND") where
"Lift_STD_BINDING_HO2 b = (\<lambda> x . b (x \<down>VAR) \<up>VAL)"

definition Lift_HO1_BINDING_HO2 ::
  "(HO1_VALUE, HO1_TYPE) BINDING \<Rightarrow>
   (HO2_VALUE, HO2_TYPE) BINDING" ("_ \<up>BIND") where
"Lift_HO1_BINDING_HO2 b = (\<lambda> x . b (x \<down>VAR) \<up>VAL)"

definition Coerce_HO1_BINDING_STD ::
  "(HO1_VALUE, HO1_TYPE) BINDING \<Rightarrow>
   (STD_VALUE, STD_TYPE) BINDING" ("_ \<down>BIND") where
"Coerce_HO1_BINDING_STD b = (\<lambda> x . b (x \<up>VAR) \<down>VAL)"

definition Coerce_HO2_BINDING_STD ::
  "(HO2_VALUE, HO2_TYPE) BINDING \<Rightarrow>
   (STD_VALUE, STD_TYPE) BINDING" ("_ \<down>BIND") where
"Coerce_HO2_BINDING_STD b = (\<lambda> x . b (x \<up>VAR) \<down>VAL)"

definition Coerce_HO2_BINDING_HO1 ::
  "(HO2_VALUE, HO2_TYPE) BINDING \<Rightarrow>
   (HO1_VALUE, HO1_TYPE) BINDING" ("_ \<down>BIND") where
"Coerce_HO2_BINDING_HO1 b = (\<lambda> x . b (x \<up>VAR) \<down>VAL)"

subsubsection {* Predicate Lifting *}

definition Lift_STD_PREDICATE_HO1 ::
  "(STD_VALUE, STD_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (HO1_VALUE, HO1_TYPE) ALPHA_PREDICATE" ("_ \<up>PRED") where
"Lift_STD_PREDICATE_HO1 p =
   (Lift_STD_VAR_HO1 ` (\<alpha> p), Lift_STD_BINDING_HO1 ` (\<beta> p))"

definition Lift_STD_PREDICATE_HO2 ::
  "(STD_VALUE, STD_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (HO2_VALUE, HO2_TYPE) ALPHA_PREDICATE" ("_ \<up>PRED") where
"Lift_STD_PREDICATE_HO2 p =
   (Lift_STD_VAR_HO2 ` (\<alpha> p), Lift_STD_BINDING_HO2 ` (\<beta> p))"

definition Lift_HO1_PREDICATE_HO2 ::
  "(HO1_VALUE, HO1_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (HO2_VALUE, HO2_TYPE) ALPHA_PREDICATE" ("_ \<up>PRED") where
"Lift_HO1_PREDICATE_HO2 p =
   (Lift_HO1_VAR_HO2 ` (\<alpha> p), Lift_HO1_BINDING_HO2 ` (\<beta> p))"

definition Coerce_HO1_PREDICATE_STD ::
  "(HO1_VALUE, HO1_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (STD_VALUE, STD_TYPE) ALPHA_PREDICATE" ("_ \<down>PRED") where
"Coerce_HO1_PREDICATE_STD p =
   (Coerce_HO1_VAR_STD ` (\<alpha> p), Coerce_HO1_BINDING_STD ` (\<beta> p))"

definition Coerce_HO2_PREDICATE_STD ::
  "(HO2_VALUE, HO2_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (STD_VALUE, STD_TYPE) ALPHA_PREDICATE" ("_ \<down>PRED") where
"Coerce_HO2_PREDICATE_STD p =
   (Coerce_HO2_VAR_STD ` (\<alpha> p), Coerce_HO2_BINDING_STD ` (\<beta> p))"

definition Coerce_HO2_PREDICATE_HO1 ::
  "(HO2_VALUE, HO2_TYPE) ALPHA_PREDICATE \<Rightarrow>
   (HO1_VALUE, HO1_TYPE) ALPHA_PREDICATE" ("_ \<down>PRED") where
"Coerce_HO2_PREDICATE_HO1 p =
   (Coerce_HO2_VAR_HO1 ` (\<alpha> p), Coerce_HO2_BINDING_HO1 ` (\<beta> p))"

subsubsection {* Simplification List *}

theorems Lift_VALUE_simps =
  Lift_STD_VALUE_HO1_def
  Lift_STD_VALUE_HO2_def
  Lift_HO1_VALUE_HO2_def
  Coerce_HO1_VALUE_STD_def
  Coerce_HO2_VALUE_STD_def
  Coerce_HO2_VALUE_HO1_def

theorems  Lift_TYPE_simps =
  Lift_STD_TYPE_HO1_def
  Lift_STD_TYPE_HO2_def
  Lift_HO1_TYPE_HO2_def
  Coerce_HO1_TYPE_STD_def
  Coerce_HO2_TYPE_STD_def
  Coerce_HO2_TYPE_HO1_def

theorems  Lift_VAR_simps =
  Lift_STD_VAR_HO1_def
  Lift_STD_VAR_HO2_def
  Lift_HO1_VAR_HO2_def
  Coerce_HO1_VAR_STD_def
  Coerce_HO2_VAR_STD_def
  Coerce_HO2_VAR_HO1_def

theorems Lift_BINDING_simps =
  Lift_STD_BINDING_HO1_def
  Lift_STD_BINDING_HO2_def
  Lift_HO1_BINDING_HO2_def
  Coerce_HO1_BINDING_STD_def
  Coerce_HO2_BINDING_STD_def
  Coerce_HO2_BINDING_HO1_def

theorems Lift_PREDICATE_simps =
  Lift_STD_PREDICATE_HO1_def
  Lift_STD_PREDICATE_HO2_def
  Lift_HO1_PREDICATE_HO2_def
  Coerce_HO1_PREDICATE_STD_def
  Coerce_HO2_PREDICATE_STD_def
  Coerce_HO2_PREDICATE_HO1_def

theorems Lift_simps =
  Lift_VALUE_simps
  Lift_TYPE_simps
  Lift_VAR_simps
  Lift_BINDING_simps
  Lift_PREDICATE_simps

subsection {* Program Calls *}

definition HO1_Call ::
  "HO1_VALUE \<Rightarrow> (STD_VALUE, STD_TYPE) ALPHA_PREDICATE" ("call") where
"HO1_Call v = Dest_STD_PREDICATE (ProgOf v)"

definition HO2_Call1 ::
  "HO2_VALUE \<Rightarrow> (STD_VALUE, STD_TYPE) ALPHA_PREDICATE" ("call") where
"HO2_Call1 v = Dest_STD_PREDICATE (Prog1Of v)"

definition HO2_Call2 ::
  "HO2_VALUE \<Rightarrow> (HO1_VALUE, HO1_TYPE) ALPHA_PREDICATE" ("call") where
"HO2_Call2 v = Dest_HO1_PREDICATE (Prog2Of v)"

subsubsection {* Simplification List *}

theorems Call_simps =
  HO1_Call_def
  HO2_Call1_def
  HO2_Call2_def

subsection {* Theorems *}

lemma IsStdVar_deduct :
"\<lbrakk>\<not> IsProg1Var v; \<not> IsProg2Var v\<rbrakk> \<Longrightarrow> IsStdVar v"
apply (cases v)
apply (clarify)
apply (simp add: IsVar_simps)
apply (rule_tac P = "\<not> IsProg1Type b" in mp)
apply (rule_tac P = "\<not> IsProg2Type b" in mp)
apply (induct_tac b)
apply (simp_all)
done

lemma IsProg1Var_deduct :
"\<lbrakk>\<not> IsStdVar v; \<not> IsProg2Var v\<rbrakk> \<Longrightarrow> IsProg1Var v"
apply (cases v)
apply (clarify)
apply (simp add: IsVar_simps)
apply (rule_tac P = "\<not> IsBaseType b" in mp)
apply (rule_tac P = "\<not> IsProg2Type b" in mp)
apply (induct_tac b)
apply (simp_all)
done

lemma IsProg2Var_deduct :
"\<lbrakk>\<not> IsStdVar v; \<not> IsProg1Var v\<rbrakk> \<Longrightarrow> IsProg2Var v"
apply (cases v)
apply (clarify)
apply (simp add: IsVar_simps)
apply (rule_tac P = "\<not> IsBaseType b" in mp)
apply (rule_tac P = "\<not> IsProg1Type b" in mp)
apply (induct_tac b)
apply (simp_all)
done

lemma IsStdVar_IsProg1Var_contra :
"\<lbrakk>IsStdVar v; IsProg1Var v\<rbrakk> \<Longrightarrow> False"
apply (cases v)
apply (clarify)
apply (simp add: IsVar_simps)
apply (rule_tac P = "IsBaseType b" in mp)
apply (rule_tac P = "IsProg1Type b" in mp)
apply (induct_tac b)
apply (simp_all)
done

lemma IsStdVar_IsProg2Var_contra :
"\<lbrakk>IsStdVar v; IsProg2Var v\<rbrakk> \<Longrightarrow> False"
apply (cases v)
apply (clarify)
apply (simp add: IsVar_simps)
apply (rule_tac P = "IsBaseType b" in mp)
apply (rule_tac P = "IsProg2Type b" in mp)
apply (induct_tac b)
apply (simp_all)
done

lemma IsProg1Var_IsProg2Var_contra :
"\<lbrakk>IsProg1Var v; IsProg2Var v\<rbrakk> \<Longrightarrow> False"
apply (cases v)
apply (clarify)
apply (simp add: IsVar_simps)
apply (rule_tac P = "IsProg1Type b" in mp)
apply (rule_tac P = "IsProg2Type b" in mp)
apply (induct_tac b)
apply (simp_all)
done

theorems IsVar_dest =
  IsStdVar_deduct
  IsProg1Var_deduct
  IsProg2Var_deduct
  IsStdVar_IsProg1Var_contra
  IsStdVar_IsProg2Var_contra
  IsProg1Var_IsProg2Var_contra

theorem IsStdVar_exists_type :
"(IsStdVar (v :: HO2_TYPE VAR)) \<Longrightarrow> (\<exists> t . type v = BaseType t)"
apply (cases v)
apply (simp add: IsVar_simps)
apply (clarify)
apply (rule_tac P = "IsBaseType b" in mp)
apply (induct_tac b)
apply (auto)
done

theorem IsProg1Var_exists_type :
"(IsProg1Var (v :: HO2_TYPE VAR)) \<Longrightarrow> (\<exists> t . type v = Prog1Type t)"
apply (cases v)
apply (simp add: IsVar_simps)
apply (clarify)
apply (rule_tac P = "IsProg1Type b" in mp)
apply (induct_tac b)
apply (auto)
done

theorem IsProg2Var_exists_type :
"(IsProg2Var (v :: HO2_TYPE VAR)) \<Longrightarrow> (\<exists> t . type v = Prog2Type t)"
apply (cases v)
apply (simp add: IsVar_simps)
apply (clarify)
apply (rule_tac P = "IsProg2Type b" in mp)
apply (induct_tac b)
apply (auto)
done

theorems IsVar_exists_type =
  IsStdVar_exists_type
  IsProg1Var_exists_type
  IsProg2Var_exists_type

subsection {* Proof Experiments *}

theorem
"(((STD.MkInt 1) \<up>VAL) :: HO1_VALUE) \<down>VAL = (STD.MkInt 1)"
apply (simp add: Lift_simps)
done

theorem
"p \<in> STD_PREDICATE \<longrightarrow>
 ((p \<up>PRED) :: (HO1_VALUE, HO1_TYPE) ALPHA_PREDICATE) \<down>PRED = p"
apply (induct_tac p)
apply (auto simp: Lift_simps VAR.MkVar_def)
apply (simp add: image_chain_elim)
apply (rule_tac x = "x" in exI)
apply (simp add: Lift_simps VAR.MkVar_def)
apply (simp add: image_chain_elim)
apply (rule_tac x = "x" in exI)
apply (simp add: Lift_simps VAR.MkVar_def)
done
end
