theory utp_basic_model
imports 
  Derive
  "../utp_base"
begin

default_sort type

datatype btyp = Int\<^isub>t | Bool\<^isub>t | List\<^isub>t btyp
datatype bval = Bot\<^isub>v btyp | Int\<^isub>v int | Bool\<^isub>v bool | List\<^isub>v btyp "(bval list)"

inductive bval_type_rel :: "bval \<Rightarrow> btyp \<Rightarrow> bool" (infix ":\<^sub>b" 50) where
Bot\<^isub>v_type [intro]: "Bot\<^isub>v(t) :\<^sub>b t" |
Bool\<^isub>v_type [intro]: "Bool\<^isub>v(x) :\<^sub>b Bool\<^isub>t"  |  
Int\<^isub>v_type [intro]: "Int\<^isub>v(n) :\<^sub>b Int\<^isub>t"  | 
List\<^isub>v_type [intro]: "\<forall> x\<in>set(xs). x :\<^sub>b t \<Longrightarrow> List\<^isub>v(t)(xs) :\<^sub>b List\<^isub>t(t)"

derive countable btyp
derive linorder btyp
derive linorder bval

type_synonym 'a bexp   = "('a, bval) WF_PEXPRESSION"
type_synonym bpred     = "bval WF_PREDICATE" 
type_synonym 'a bvar   = "('a, bval) PVAR"

translations
  (type) "'a bexp" <= (type) "('a, bval) WF_PEXPRESSION"
  (type) "bpred" <= (type) "bval WF_PREDICATE"
  (type) "'a bvar" <= (type) "('a, bval) PVAR"

inductive_cases
  Bot\<^isub>v_cases [elim]: "Bot\<^isub>v a :\<^sub>b t" and
  Bot\<^isub>t_cases [elim!]: "x :\<^sub>b Bot\<^isub>t" and
  Bool\<^isub>v_cases [elim]: "Bool\<^isub>v x :\<^sub>b t" and
  Bool\<^isub>t_cases [elim!]: "x :\<^sub>b Boot\<^isub>t" and
  Int\<^isub>v_cases [elim]: "Int\<^isub>v x :\<^sub>b t" and
  Int\<^isub>t_cases [elim!]: "x :\<^sub>b Int\<^isub>t" and
  List\<^isub>v_cases [elim]: "List\<^isub>v a xs :\<^sub>b t" and
  List\<^isub>t_cases [elim!]: "x :\<^sub>b List\<^isub>t a"

instantiation bval :: DEFINED
begin

fun Defined_bval :: "bval \<Rightarrow> bool" where
"\<D>(Bot\<^isub>v a) = False" |  "\<D>(Bool\<^isub>v x) = True" | "\<D>(Int\<^isub>v x) = True" |
"\<D>(List\<^isub>v a xs) = (\<forall> x \<in> set(xs). \<D>(x))"

instance ..
end

instantiation bval :: VALUE
begin

definition utype_rel_bval :: "bval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_bval x t \<longleftrightarrow> (\<exists> a. t = to_nat a \<and> x :\<^sub>b a)"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_bval_def)
  apply (rule_tac x="to_nat(Int\<^isub>t)" in exI)
  apply (rule_tac x="Int\<^isub>v 0" in exI)
  apply (auto)
done
end

lemma prjTYPE_inv_bty [simp]
  : "embTYPE ((prjTYPE t) :: btyp) = (t :: bval UTYPE)"
  by (metis Rep_UTYPE_elim Rep_UTYPE_inverse embTYPE_def from_nat_to_nat prjTYPE_def utype_rel_bval_def)

lemma embTYPE_inv_bty [simp]:
  "prjTYPE (embTYPE (t :: btyp) :: bval UTYPE) = t"
  apply (induct t)
  apply (rule embTYPE_inv[of "Int\<^isub>v 0"])
  apply (auto simp add: utype_rel_bval_def)
  apply (rule embTYPE_inv[of "Bool\<^isub>v False"])
  apply (auto simp add: utype_rel_bval_def)
  apply (rule_tac v="List\<^isub>v t []" in embTYPE_inv)
  apply (auto simp add: utype_rel_bval_def)
done

lemma type_rel_btyp [simp]: 
  "x : t \<longleftrightarrow> x :\<^sub>b prjTYPE t"
  by (metis (full_types) Rep_UTYPE_elim empty_Collect_eq from_nat_to_nat prjTYPE_def type_rel_def utype_rel_bval_def)

instantiation bval :: BOOL_SORT
begin

definition MkBool_bval :: "bool \<Rightarrow> bval" where
"MkBool_bval x = Bool\<^isub>v x"

primrec DestBool_bval :: "bval \<Rightarrow> bool" where
"DestBool_bval (Bool\<^isub>v x) = x" 

definition BoolType_bval :: "bval UTYPE" where
"BoolType_bval = embTYPE Bool\<^isub>t"

instance
  apply (intro_classes)
  apply (simp add:MkBool_bval_def DestBool_bval_def BoolType_bval_def dcarrier_def monotype_def type_rel_def)
  apply (auto simp add:MkBool_bval_def DestBool_bval_def BoolType_bval_def dcarrier_def monotype_def)
  apply (metis prjTYPE_inv_bty)
done
end

instantiation bval :: INT_SORT
begin

definition MkInt_bval :: "int \<Rightarrow> bval" where
"MkInt_bval x = Int\<^isub>v x"

primrec DestInt_bval :: "bval \<Rightarrow> int" where
"DestInt_bval (Int\<^isub>v x) = x" 

definition IntType_bval :: "bval UTYPE" where
"IntType_bval = embTYPE Int\<^isub>t"

instance
  apply (intro_classes)
  apply (simp add:MkInt_bval_def DestInt_bval_def IntType_bval_def dcarrier_def monotype_def type_rel_def)
  apply (auto simp add:MkInt_bval_def DestInt_bval_def IntType_bval_def dcarrier_def monotype_def)
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
  by (utp_poly_auto_tac)

lemma GCD_post_sat_GCD_INV:
  "\<lbrakk> x > 0; y > 0 \<rbrakk> \<Longrightarrow> `($X > \<guillemotleft>0\<guillemotright>) \<and> ($Y > \<guillemotleft>0\<guillemotright>) \<and> (gcd($X,$Y) = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>))` \<sqsubseteq> `$X = $Y \<and> $X = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>)`"
  apply (utp_poly_auto_tac)
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
    apply (utp_poly_auto_tac)
    apply (smt gcd_add1_int)
    apply (smt gcd_add1_int)
    apply (simp add:closure)
    apply (simp add:closure unrest typing)
    apply (simp add:closure typing defined)
    apply (rule HoareP_AssignR)
    apply (force intro:closure unrest simp add:erasure typing defined)+
    apply (simp add:usubst typing defined)
    apply (utp_poly_auto_tac)
    apply (smt gcd_add2_int)
    apply (smt gcd_add2_int)
    apply (simp add:closure)
    apply (simp add:unrest closure typing defined)
    apply (simp add:unrest closure typing defined)
  done

  moreover from assms 
  have "`$X = $Y \<and> $X = gcd(\<guillemotleft>x\<guillemotright>,\<guillemotleft>y\<guillemotright>)` \<sqsubseteq> ?I \<and>\<^sub>p `$X = $Y` "
    by (utp_poly_auto_tac)

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