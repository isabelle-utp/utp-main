(******************************************************************************)
(* Project: Isabelle-UTP: Unifying Theories of Programming in HOL             *)
(* File: utp_default_value.thy                                                *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 22 November 2013. *)

header {* Default Values *}

theory utp_default_value
imports Derive
  "../utp_common"
(* "../utp_global" *)
  "../core/utp_value"
  "../core/utp_sorts"
begin

text {* We are going to use the colon for type membership in our model. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

subsection {* Auxiliary Theorems *}

text {* Move these theoresm to utp_common.thy.*}

theorem inj_f_inv_f :
"\<lbrakk>x \<in> range f; inj f\<rbrakk> \<Longrightarrow> f ((inv f) x) = x"
apply (erule rangeE)
apply (clarsimp)
done

theorem to_nat_from_nat :
"x \<in> range (to_nat::('a\<Colon>countable) \<Rightarrow> nat) \<Longrightarrow>
   (to_nat::('a\<Colon>countable) \<Rightarrow> nat) (from_nat x) = x"
apply (unfold from_nat_def)
apply (erule inj_f_inv_f)
apply (rule inj_to_nat)
done

subsection {* Default Value Model *}

datatype DEFAULT_VALUE =
  IntVal "int" |
  BoolVal "bool" |
  StrVal "string" |
  RealVal "real"

derive linorder DEFAULT_VALUE

subsection {* Default Type Model *}

datatype DEFAULT_TYPE =
  IntType |
  BoolType |
  StrType |
  RealType

derive countable DEFAULT_TYPE

subsection {* Testing Functions *}

primrec IsIntVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsIntVal (IntVal _) = True" |
"IsIntVal (BoolVal _) = False" |
"IsIntVal (StrVal _) = False" |
"IsIntVal (RealVal _) = False"

primrec IsBoolVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsBoolVal (IntVal _) = False" |
"IsBoolVal (BoolVal _) = True" |
"IsBoolVal (StrVal _) = False" |
"IsBoolVal (RealVal _) = False"

primrec IsStrVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsStrVal (IntVal _) = False" |
"IsStrVal (BoolVal _) = False" |
"IsStrVal (StrVal _) = True" |
"IsStrVal (RealVal _) = False"

primrec IsRealVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsRealVal (IntVal _) = False" |
"IsRealVal (BoolVal _) = False" |
"IsRealVal (StrVal _) = False" |
"IsRealVal (RealVal _) = True"

subsection {* Typing Relation *}

fun default_type_rel ::
  "DEFAULT_VALUE \<Rightarrow> DEFAULT_TYPE \<Rightarrow> bool" (infix ":\<^sub>d\<^sub>e\<^sub>f\<^sub>a\<^sub>u\<^sub>l\<^sub>t" 50) where
"default_type_rel (IntVal _) IntType = True" |
"default_type_rel (IntVal _) BoolType = False" |
"default_type_rel (IntVal _) StrType = False" |
"default_type_rel (IntVal _) RealType = False" |
"default_type_rel (BoolVal _) IntType = False" |
"default_type_rel (BoolVal _) BoolType = True" |
"default_type_rel (BoolVal _) StrType = False" |
"default_type_rel (BoolVal _) RealType = False" |
"default_type_rel (StrVal _) IntType = False" |
"default_type_rel (StrVal _) BoolType = False" |
"default_type_rel (StrVal _) StrType = True" |
"default_type_rel (StrVal _) RealType = False" |
"default_type_rel (RealVal _) IntType = False" |
"default_type_rel (RealVal _) BoolType = False" |
"default_type_rel (RealVal _) StrType = False" |
"default_type_rel (RealVal _) RealType = True"

subsection {* Value Model Instantiation *}

instantiation DEFAULT_VALUE :: DEFINED
begin
definition "Defined_DEFAULT_VALUE (v :: DEFAULT_VALUE) = True"
instance ..
end

text {* Default Simplification *}

declare Defined_DEFAULT_VALUE_def [simp]

instantiation DEFAULT_VALUE :: VALUE
begin
definition utype_rel_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_DEFAULT_VALUE v tenc \<longleftrightarrow> (\<exists> t . tenc = to_nat t \<and> v :\<^sub>d\<^sub>e\<^sub>f\<^sub>a\<^sub>u\<^sub>l\<^sub>t t)"
instance
  apply (intro_classes)
  apply (rule_tac x = "to_nat IntType" in exI)
  apply (rule_tac x = "IntVal 0" in exI)
  apply (simp add: utype_rel_DEFAULT_VALUE_def)
  apply (simp add: Defined_DEFAULT_VALUE_def)
done
end

subsection {* Type Embedding Theorems *}

theorem embTYPE_DEFAULT_TYPE_inv [simp] :
"prjTYPE (embTYPE (t :: DEFAULT_TYPE) :: DEFAULT_VALUE UTYPE) = t"
apply (induct t)
-- {* Subgoal 1 *}
apply (rule embTYPE_inv [of "IntVal 0"])
apply (simp_all add: utype_rel_DEFAULT_VALUE_def) [2]
-- {* Subgoal 2 *}
apply (rule embTYPE_inv [of "BoolVal false"])
apply (simp_all add: utype_rel_DEFAULT_VALUE_def) [2]
-- {* Subgoal 3 *}
apply (rule embTYPE_inv [of "StrVal ''''"])
apply (simp_all add: utype_rel_DEFAULT_VALUE_def) [2]
-- {* Subgoal 4 *}
apply (rule embTYPE_inv [of "RealVal 0"])
apply (simp_all add: utype_rel_DEFAULT_VALUE_def) [2]
done

theorem prjTYPE_DEFAULT_TYPE_inv [simp] :
"embTYPE ((prjTYPE tenc) :: DEFAULT_TYPE) = (tenc :: DEFAULT_VALUE UTYPE)"
apply (unfold embTYPE_def prjTYPE_def)
apply (subst to_nat_from_nat)
-- {* Subgoal 1 *}
apply (rule Rep_UTYPE_elim [where t = "tenc"])
apply (simp add: utype_rel_DEFAULT_VALUE_def)
apply (clarsimp)
-- {* Subgoal 2 *}
apply (simp)
done

theorem type_rel_DEFAULT_TYPE [simp] :
"x : tenc \<longleftrightarrow> x :\<^sub>d\<^sub>e\<^sub>f\<^sub>a\<^sub>u\<^sub>l\<^sub>t (prjTYPE tenc)"
apply (simp add: type_rel_def)
apply (simp add: utype_rel_DEFAULT_VALUE_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: prjTYPE_def)
-- {* Subgoal 2 *}
apply (rule_tac x = "prjTYPE tenc" in exI)
apply (simp add: prjTYPE_def)
apply (rule Rep_UTYPE_elim [where t = "tenc"])
apply (simp add: utype_rel_DEFAULT_VALUE_def)
apply (clarsimp)
done

subsection {* Sort Memberships *}

subsubsection {* Integer Sort *}

instantiation DEFAULT_VALUE :: INT_SORT
begin
definition MkInt_DEFAULT_VALUE :: "int \<Rightarrow> DEFAULT_VALUE" where
"MkInt_DEFAULT_VALUE i = IntVal i"

primrec DestInt_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> int" where
"DestInt_DEFAULT_VALUE (IntVal i) = i"

definition IntType_DEFAULT_VALUE :: "DEFAULT_VALUE UTYPE" where
"IntType_DEFAULT_VALUE = embTYPE IntType"

instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (simp add: MkInt_DEFAULT_VALUE_def)
-- {* Subgoal 2 *}
apply (simp add: IntType_DEFAULT_VALUE_def)
apply (simp add: dcarrier_def)
apply (safe)
-- {* Subgoal 2.1 *}
apply (atomize (full))
apply (rule allI)
apply (induct_tac x)
apply (simp_all) [4]
apply (fold MkInt_DEFAULT_VALUE_def)
apply (simp)
-- {* Subgoal 2.1 *}
apply (simp add: MkInt_DEFAULT_VALUE_def)
done
end

subsubsection {* Boolean Sort *}

instantiation DEFAULT_VALUE :: BOOL_SORT
begin
definition MkBool_DEFAULT_VALUE :: "bool \<Rightarrow> DEFAULT_VALUE" where
"MkBool_DEFAULT_VALUE b = BoolVal b"

primrec DestBool_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"DestBool_DEFAULT_VALUE (BoolVal b) = b"

definition BoolType_DEFAULT_VALUE :: "DEFAULT_VALUE UTYPE" where
"BoolType_DEFAULT_VALUE = embTYPE BoolType"

instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (simp add: MkBool_DEFAULT_VALUE_def)
-- {* Subgoal 2 *}
apply (simp add: BoolType_DEFAULT_VALUE_def)
apply (simp add: dcarrier_def)
apply (safe)
-- {* Subgoal 2.1 *}
apply (atomize (full))
apply (rule allI)
apply (induct_tac x)
apply (simp_all) [4]
apply (fold MkBool_DEFAULT_VALUE_def)
apply (simp)
-- {* Subgoal 2.1 *}
apply (simp add: MkBool_DEFAULT_VALUE_def)
-- {* Subgoal 3 *}
apply (simp add: BoolType_DEFAULT_VALUE_def)
apply (simp add: monotype_def)
apply (clarify del: Rep_UTYPE_intro)
apply (subgoal_tac "prjTYPE a = BoolType")
-- {* Subgoal 3.1 *}
apply (erule subst)
apply (simp)
-- {* Subgoal 3.2 *}
apply (case_tac x)
apply (simp_all)
apply (case_tac "(prjTYPE a) :: DEFAULT_TYPE")
apply (simp_all)
done
end

subsubsection {* String Sort *}

instantiation DEFAULT_VALUE :: STRING_SORT
begin
definition MkStr_DEFAULT_VALUE :: "string \<Rightarrow> DEFAULT_VALUE" where
"MkStr_DEFAULT_VALUE s = StrVal s"

primrec DestStr_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> string" where
"DestStr_DEFAULT_VALUE (StrVal s) = s"

definition StringType_DEFAULT_VALUE :: "DEFAULT_VALUE UTYPE" where
"StringType_DEFAULT_VALUE = embTYPE StrType"

instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (simp add: MkStr_DEFAULT_VALUE_def)
-- {* Subgoal 2 *}
apply (simp add: StrType_DEFAULT_VALUE_def)
apply (safe)
-- {* Subgoal 2.1 *}
apply (simp add: MkStr_DEFAULT_VALUE_def StringType_DEFAULT_VALUE_def)
apply (simp)
-- {* Subgoal 2.2 *}
apply (simp add: type_rel_def)
apply (simp add: StringType_DEFAULT_VALUE_def)
apply (atomize (full))
apply (rule allI)
apply (induct_tac x)
apply (simp_all) [4]
apply (simp add: MkStr_DEFAULT_VALUE_def)
done
end

subsection {* Proof Experiments *}

theorem "(IntVal 1) :\<^sub>d\<^sub>e\<^sub>f\<^sub>a\<^sub>u\<^sub>l\<^sub>t IntType"
apply (auto)
done

theorem "((MkInt 1) :: DEFAULT_VALUE) : INT_SORT_class.IntType"
apply (simp add: MkInt_DEFAULT_VALUE_def IntType_DEFAULT_VALUE_def)
done
end