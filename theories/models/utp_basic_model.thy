theory utp_basic_model
imports 
  Derive
  "../utp_base"
begin

default_sort type

datatype bval = IntV int | BoolV bool | ListV "bval list"

derive linorder bval

datatype btyp = BoolT | IntT | ListT btyp

derive countable btyp

type_synonym 'a bexp   = "('a, bval) WF_PEXPRESSION"
type_synonym bpred     = "bval WF_PREDICATE" 
type_synonym 'a bvar   = "('a, bval) PVAR"

translations
  (type) "'a bexp" <= (type) "('a, bval) WF_PEXPRESSION"
  (type) "bpred" <= (type) "bval WF_PREDICATE"
  (type) "'a bvar" <= (type) "('a, bval) PVAR"

inductive bval_type_rel :: "bval \<Rightarrow> btyp \<Rightarrow> bool" (infix ":\<^sub>b" 50) where
BoolV_type [intro]: "BoolV x :\<^sub>b BoolT" |
IntV_type  [intro]: "IntV x :\<^sub>b IntT" |
ListV_type [intro]: "\<forall> x\<in>set xs. x :\<^sub>b t \<Longrightarrow> ListV xs :\<^sub>b ListT t"

inductive_cases
  BoolV_cases [elim]: "BoolV x :\<^sub>b t" and
  BoolT_cases [elim!]: "x :\<^sub>b BootT" and
  IntV_cases [elim]: "IntV x :\<^sub>b t" and
  IntT_cases [elim!]: "x :\<^sub>b IntT" and
  ListV_cases [elim]: "ListV xs :\<^sub>b t" and
  ListT_cases [elim!]: "x :\<^sub>b ListT a"

instantiation bval :: DEFINED
begin

definition "Defined_bval (x::bval) = True"

instance ..
end

declare Defined_bval_def [simp]

instantiation bval :: VALUE
begin

definition utype_rel_bval :: "bval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_bval x t \<longleftrightarrow> (\<exists> a. t = to_nat a \<and> x :\<^sub>b a)"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_bval_def)
  apply (rule_tac x="IntV 0" in exI)
  apply (auto)
done
end

lemma prjTYPE_inv_bty [simp]
  : "embTYPE ((prjTYPE t) :: btyp) = (t :: bval UTYPE)"
  by (metis Rep_UTYPE_elim Rep_UTYPE_inverse embTYPE_def from_nat_to_nat prjTYPE_def utype_rel_bval_def)

lemma embTYPE_inv_bty [simp]:
  "prjTYPE (embTYPE (t :: btyp) :: bval UTYPE) = t"
  apply (induct t)
  apply (rule embTYPE_inv[of "BoolV False"])
  apply (auto simp add: utype_rel_bval_def)
  apply (rule embTYPE_inv[of "IntV 0"])
  apply (auto simp add: utype_rel_bval_def)
  apply (rule embTYPE_inv[of "ListV []"])
  apply (auto simp add: utype_rel_bval_def)
done

lemma type_rel_btyp [simp]: 
  "x : t \<longleftrightarrow> x :\<^sub>b prjTYPE t"
  by (metis (full_types) Rep_UTYPE_elim empty_Collect_eq from_nat_to_nat prjTYPE_def type_rel_def utype_rel_bval_def)

instantiation bval :: BOOL_SORT
begin

definition MkBool_bval :: "bool \<Rightarrow> bval" where
"MkBool_bval x = BoolV x"

primrec DestBool_bval :: "bval \<Rightarrow> bool" where
"DestBool_bval (BoolV x) = x" 

definition BoolType_bval :: "bval UTYPE" where
"BoolType_bval = embTYPE BoolT"

instance
  apply (intro_classes)
  apply (simp add:MkBool_bval_def DestBool_bval_def BoolType_bval_def dcarrier_def monotype_def Defined_bval_def type_rel_def)
  apply (auto simp add:MkBool_bval_def DestBool_bval_def BoolType_bval_def Defined_bval_def dcarrier_def monotype_def)
  apply (metis prjTYPE_inv_bty)
done
end

instantiation bval :: INT_SORT
begin

definition MkInt_bval :: "int \<Rightarrow> bval" where
"MkInt_bval x = IntV x"

primrec DestInt_bval :: "bval \<Rightarrow> int" where
"DestInt_bval (IntV x) = x" 

definition IntType_bval :: "bval UTYPE" where
"IntType_bval = embTYPE IntT"

instance
  apply (intro_classes)
  apply (simp add:MkInt_bval_def DestInt_bval_def IntType_bval_def dcarrier_def monotype_def Defined_bval_def type_rel_def)
  apply (auto simp add:MkInt_bval_def DestInt_bval_def IntType_bval_def Defined_bval_def dcarrier_def monotype_def)
done
end

syntax
  "_pexpr_op1" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_'(_')")
  "_pexpr_op2" :: "idt \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_'(_,_')")

translations
  "_pexpr_op1 f x"   == "CONST Op1PE f x"
  "_pexpr_op2 f x y" == "CONST Op2PE f x y"

term "|x > y|"

term "`X := $X - $Y \<lhd> ($X > $Y) \<rhd> Y := $Y - $X`"

term "MkPlainP n True t TYPE(bval)"

abbreviation MkV :: "string \<Rightarrow> 'a itself \<Rightarrow> 'a bvar" where
"MkV n t \<equiv> MkPlainP n True t TYPE(bval)"

abbreviation "X \<equiv> MkV ''X'' TYPE(int)"
abbreviation "Y \<equiv> MkV ''Y'' TYPE(int)"

abbreviation "GCD_BODY \<equiv> `X := $X - $Y \<lhd> $X > $Y \<rhd> Y := $Y - $X`"

abbreviation 
"GCD \<equiv> `while \<not>($X = $Y) do GCD_BODY od`"

abbreviation
  "GCD_INV x y \<equiv> `($X > \<guillemotleft>0\<guillemotright>) \<and> ($Y > \<guillemotleft>0\<guillemotright>) \<and> (gcd($X,$Y) = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>))`"

lemma GCD_pre_sat_GCD_INV:
  "\<lbrakk> x > 0; y > 0 \<rbrakk> \<Longrightarrow> `($X > \<guillemotleft>0\<guillemotright>) \<and> ($Y > \<guillemotleft>0\<guillemotright>) \<and> (gcd($X,$Y) = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>))` \<sqsubseteq> `($X = \<guillemotleft>x\<guillemotright> \<and> $Y = \<guillemotleft>y\<guillemotright>)`"
  by (utp_pred_auto_tac)

lemma GCD_post_sat_GCD_INV:
  "\<lbrakk> x > 0; y > 0 \<rbrakk> \<Longrightarrow> `($X > \<guillemotleft>0\<guillemotright>) \<and> ($Y > \<guillemotleft>0\<guillemotright>) \<and> (gcd($X,$Y) = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>))` \<sqsubseteq> `$X = $Y \<and> $X = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>)`"
  apply (utp_pred_auto_tac)
  apply (metis gcd_pos_int less_int_code(1))
  apply (metis abs_gcd_int)
done

theorem GCD_partial_correct:
  assumes "x > 0" "y > 0"
  shows "`($X = \<guillemotleft>x\<guillemotright> \<and> $Y = \<guillemotleft>y\<guillemotright>){GCD}($X = $Y \<and> $X = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>))`"
proof -
  let ?I = "GCD_INV x y" and ?S = "`\<not> ($X = $Y)`"

  have "?I {while ?S do GCD_BODY od}\<^sub>p (\<not>\<^sub>p ?S \<and>\<^sub>p ?I)"
    apply (rule_tac HoareP_IterP)
    apply (force intro:closure unrest simp add:erasure typing)
    apply (force intro:closure unrest simp add:erasure typing)
    apply (rule closure)
    apply (force intro:closure unrest simp add:erasure typing defined)+
    apply (rule HoareP_CondR)
    apply (rule HoareP_AssignR)
    apply (force intro:closure unrest simp add:erasure typing defined)
    apply (simp add:usubst typing defined)
    apply (utp_pred_auto_tac)
    apply (smt gcd_add1_int)
    apply (smt gcd_add1_int)
    apply (simp add:closure)
    apply (simp add:closure unrest typing)
    apply (simp add:closure typing defined)
    apply (rule HoareP_AssignR)
    apply (force intro:closure unrest simp add:erasure typing defined)+
    apply (simp add:usubst typing defined)
    apply (utp_pred_auto_tac)
    apply (smt gcd_add2_int)
    apply (smt gcd_add2_int)
    apply (simp add:closure)
    apply (simp add:unrest closure typing defined)
    apply (simp add:unrest closure typing defined)
  done

  moreover from assms 
  have "`$X = $Y \<and> $X = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>)` \<sqsubseteq> ?I \<and>\<^sub>p `$X = $Y` "
    by (utp_pred_auto_tac)

  ultimately show ?thesis
    apply (rule_tac HoareP_post_refine)
    apply (simp)
    apply (rule HoareP_pre_refine)
    apply (rule GCD_pre_sat_GCD_INV)
    apply (simp_all add:assms)
    apply (metis AndP_comm)
  done
qed

value "gcd (33::int) 12"

end