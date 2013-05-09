theory utp_vdm_expr
imports 
  "../../core/utp_expr"
  "../../parser/utp_pred_parser"
  "../../laws/utp_rel_laws"
  utp_vdm_sorts 
begin

default_sort vbasic

typedef 'a vdme = "UNIV :: (vdmv WF_BINDING \<Rightarrow> 'a::vbasic) set" ..

declare Rep_vdme [simp]
declare Rep_vdme_inverse [simp]
declare Abs_vdme_inverse [simp]

lemma Rep_vdme_intro [intro]:
  "Rep_vdme x = Rep_vdme y \<Longrightarrow> x = y"
  by (simp add:Rep_vdme_inject)

lemma Rep_vdme_elim [elim]:
  "\<lbrakk> x = y; Rep_vdme x = Rep_vdme y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

notation Rep_vdme ("\<langle>_\<rangle>\<^sub>v")

definition UNREST_VDME :: "(vdmv VAR) set \<Rightarrow> 'a vdme \<Rightarrow> bool" where
"UNREST_VDME vs e \<equiv> (\<forall> b1 b2. \<langle>e\<rangle>\<^sub>v(b1 \<oplus>\<^sub>b b2 on vs) = \<langle>e\<rangle>\<^sub>v b1)" 

abbreviation MkVVar :: "char list \<Rightarrow> 'a::vbasic itself \<Rightarrow> vdmv VAR" where
"MkVVar n t \<equiv> (MkPlain n (embTYPE (Type t)) False)"

definition VarE :: "string \<Rightarrow> 'a::vbasic vdme" ("$_") where
"VarE n = Abs_vdme (\<lambda> b. the (Project (ProjBasicV (\<langle>b\<rangle>\<^sub>b (MkVVar n TYPE('a))))))"

lemma UNREST_VDME_VarE [unrest]: "UNREST_VDME (VAR - {MkVVar n TYPE('a)}) ($n :: 'a vdme) "
  by (simp add: UNREST_VDME_def VarE_def)

declare [[coercion VarE]]

definition LitE :: "'a::vbasic \<Rightarrow> 'a vdme" ("<_>") where
"LitE x = Abs_vdme (\<lambda> b. x)"

lemma UNREST_VDME_LitE [unrest]: "UNREST_VDME vs <x>"
  by (simp add:UNREST_VDME_def LitE_def)

definition UOpE :: "('a::vbasic \<Rightarrow> 'b::vbasic) \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme" where
"UOpE f v = Abs_vdme (\<lambda> b. f (Rep_vdme v b))"

lemma UNREST_VDME_UOpE [unrest]: "UNREST_VDME vs v \<Longrightarrow> UNREST_VDME vs (UOpE f v)"
  by (simp add:UNREST_VDME_def UOpE_def)

definition BOpE :: "('a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic) 
                   \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme \<Rightarrow> 'c vdme" where
"BOpE f v1 v2 = Abs_vdme (\<lambda> b. f (Rep_vdme v1 b) (Rep_vdme v2 b))"

lemma UNREST_VDME_BOpE [unrest]: "\<lbrakk> UNREST_VDME vs v1; UNREST_VDME vs v2 \<rbrakk> \<Longrightarrow> UNREST_VDME vs (BOpE f v1 v2)"
  by (simp add:UNREST_VDME_def BOpE_def)

definition ListE :: "'a::vbasic vdme list \<Rightarrow> 'a list vdme" where
"ListE xs = Abs_vdme (\<lambda> b. map (\<lambda> v. Rep_vdme v b) xs )"

declare [[coercion ListE]]

lemma UNREST_VDME_ListE [unrest]: "\<lbrakk> \<forall> x \<in> set xs. UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (ListE xs)"
  by (auto simp add:UNREST_VDME_def ListE_def)

definition FSetE :: "'a::vbasic vdme fset \<Rightarrow> 'a fset vdme" where
"FSetE xs = Abs_vdme (\<lambda> b. (\<lambda> v. Rep_vdme v b) `\<^sub>f xs )"

declare [[coercion FSetE]]

lemma UNREST_VDME_FSetE [unrest]: "\<lbrakk> \<forall> x \<in>\<^sub>f xs. UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (FSetE xs)"
  apply (simp add:UNREST_VDME_def FSetE_def)
  apply (clarify)
  apply (simp add:fimage.rep_eq)
  apply (safe)
  apply (metis imageI)+
done

definition SemE :: "'a::vbasic vdme \<Rightarrow> vdmv WF_EXPRESSION" where 
"SemE f = Abs_WF_EXPRESSION (\<lambda> b. BasicV (Inject (Rep_vdme f b)))"

lemma SemE_rep_eq: "\<langle>SemE f\<rangle>\<^sub>e = (\<lambda> b. BasicV (Inject (Rep_vdme f b)))"
  apply (subgoal_tac "(\<lambda> b. BasicV (Inject (Rep_vdme f b))) \<in> WF_EXPRESSION")
  apply (simp add:SemE_def)
  apply (simp add:WF_EXPRESSION_def)
  apply (rule_tac x="embTYPE (Type TYPE('a))" in exI)
  apply (rule)
  apply (simp add:type_rel_vdmt)
  apply (metis Abs_UTYPE_inverse BasicV_type Defined_vdmv_def InjVB_def InjVB_nbot Inject_type embTYPE_def from_nat_to_nat prjTYPE_def vdmt_UTYPE)
done

lemma UNREST_EXPR_SemE [unrest]:
  "UNREST_VDME vs e \<Longrightarrow> UNREST_EXPR vs (SemE e)"
  by (simp add:UNREST_EXPR_def UNREST_VDME_def SemE_rep_eq)

lemma SemE_type_nat [simp]: "expr_type (SemE (v::nat vdme)) = embTYPE NatT"
  apply (simp add:expr_type_def etype_rel_def SemE_rep_eq)
  apply (rule the_equality)
  apply (metis Abs_UTYPE_type BasicV_type Defined_vdmv_def InjVB_def InjVB_nbot Inject_nat_def NatI_type embTYPE_def utype_rel_vdmv_def)
  apply (metis BasicV_type_cases Inject_nat_def NatI_type_cases prjTYPE_inv_vdm type_rel_vdmt)
done

lemma SemE_type_int [simp]: "expr_type (SemE (v::int vdme)) = embTYPE IntT"
  apply (simp add:expr_type_def etype_rel_def SemE_rep_eq)
  apply (rule the_equality)
  apply (metis Abs_UTYPE_type BasicV_type Defined_vdmv_def InjVB_def InjVB_nbot Inject_int_def IntI_type embTYPE_def utype_rel_vdmv_def)
  apply (metis BasicV_type_cases Inject_int_def IntI_type_cases prjTYPE_inv_vdm type_rel_vdmt)
done

(* FIXME: The following two proofs can't be completed as the current representation of
          values is, perhaps, too polymorphic. I think we probably want to store
          type data in values which can possess multiple types, e.g. empty list, empty set
*)

lemma SemE_type_string [simp]: "expr_type (SemE (v::string vdme)) = embTYPE StringT"
  apply (simp add:expr_type_def etype_rel_def SemE_rep_eq)
  apply (rule the_equality)
  apply (simp add:type_rel_vdmt)
  apply (force simp add:Inject_list_def Inject_char_def)
oops


lemma SemE_type: "expr_type (SemE (v::('a::vbasic) vdme)) = embTYPE (Type TYPE('a))"
  apply (simp add:expr_type_def etype_rel_def SemE_rep_eq)
  apply (rule the_equality)
  apply (metis Abs_UTYPE_type BasicV_type Defined_vdmv_def InjVB_def InjVB_nbot Inject_type embTYPE_def utype_rel_vdmv_def)
  apply (auto)
oops

instantiation vdme :: ("{one,vbasic}") one
begin

definition one_vdme :: "'a vdme" where
"one_vdme = LitE 1"

instance .. 
end

lemma UNREST_VDME_one [unrest]: "UNREST_VDME vs 1"
  by (simp add:one_vdme_def unrest)

instantiation vdme :: ("{zero,vbasic}") zero
begin

definition zero_vdme :: "'a vdme" where
"zero_vdme = LitE 0"

instance .. 
end

lemma UNREST_VDME_zero [unrest]: "UNREST_VDME vs 0"
  by (simp add:zero_vdme_def unrest)

instance vdme :: ("{zero_neq_one,vbasic}") zero_neq_one
  apply (intro_classes)
  apply (auto simp add:one_vdme_def zero_vdme_def LitE_def)
  apply (erule Rep_vdme_elim)
  apply (simp)
  apply (metis zero_neq_one)
done
  
instantiation vdme :: ("{plus,vbasic}") plus
begin

definition plus_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"plus_vdme = BOpE (op +)"

instance ..

end

lemma UNREST_VDME_plus [unrest]: 
  "\<lbrakk> UNREST_VDME vs x; UNREST_VDME vs y \<rbrakk> \<Longrightarrow> UNREST_VDME vs (x + y)"
  by (simp add:plus_vdme_def unrest)

instantiation vdme :: ("{minus,vbasic}") minus
begin

definition minus_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"minus_vdme = BOpE (op -)"

instance ..

end

lemma UNREST_VDME_minus [unrest]: 
  "\<lbrakk> UNREST_VDME vs x; UNREST_VDME vs y \<rbrakk> \<Longrightarrow> UNREST_VDME vs (x - y)"
  by (simp add:minus_vdme_def unrest)

instantiation vdme :: ("{uminus,vbasic}") uminus
begin

definition uminus_vdme :: "'a vdme \<Rightarrow> 'a vdme" where
"uminus_vdme = UOpE uminus"

instance ..

end

lemma UNREST_VDME_uminus [unrest]: 
  "\<lbrakk> UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (- x)"
  by (simp add:uminus_vdme_def unrest)

instantiation vdme :: ("{times, vbasic}") times
begin

definition times_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"times_vdme = BOpE (op *)"

instance ..
end

lemma UNREST_VDME_times [unrest]: 
  "\<lbrakk> UNREST_VDME vs x; UNREST_VDME vs y \<rbrakk> \<Longrightarrow> UNREST_VDME vs (x * y)"
  by (simp add:times_vdme_def unrest)

instantiation vdme :: ("{inverse,vbasic}") inverse
begin

definition inverse_vdme :: "'a vdme \<Rightarrow> 'a vdme" where
"inverse_vdme = UOpE inverse"

definition divide_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"divide_vdme = BOpE divide"

instance ..

end

instantiation vdme :: ("{ord,vbasic}") ord
begin

definition less_eq_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> bool" where
"x \<le> y \<longleftrightarrow> (\<forall>b. \<langle>x\<rangle>\<^sub>v b \<le> \<langle>y\<rangle>\<^sub>v b)"

definition less_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> bool" where
"x < y \<longleftrightarrow> (\<forall>b. \<langle>x\<rangle>\<^sub>v b < \<langle>y\<rangle>\<^sub>v b)"

instance ..
end

instance vdme :: ("{semigroup_add,vbasic}") semigroup_add
  by (intro_classes, auto simp add:plus_vdme_def BOpE_def add_assoc)

instance vdme :: ("{ab_semigroup_add,vbasic}") ab_semigroup_add
  apply (intro_classes)
  apply (auto simp add:plus_vdme_def BOpE_def add_commute)
done

instance vdme :: ("{semigroup_mult, vbasic}") semigroup_mult
  by (intro_classes, auto simp add:times_vdme_def BOpE_def mult_assoc)

instance vdme :: ("{ab_semigroup_mult,vbasic}") ab_semigroup_mult
  by (intro_classes, auto simp add:times_vdme_def BOpE_def mult_commute)

(*
instance vdme :: ("{comm_monoid_mult,vbasic}") comm_monoid_mult
  by (intro_classes, auto simp add:times_vdme_def one_vdme_def BOpE_def LitE_def mult_1)
*)  

instance vdme :: ("{semiring,vbasic}") semiring
  by (intro_classes, auto simp add:plus_vdme_def times_vdme_def BOpE_def distrib_right distrib_left)

instance vdme :: ("{comm_semiring,vbasic}") comm_semiring
  by (intro_classes, auto simp add:plus_vdme_def times_vdme_def BOpE_def distrib)

instance vdme :: ("{semiring_0,vbasic}") semiring_0
  by (intro_classes, auto simp add:plus_vdme_def times_vdme_def zero_vdme_def BOpE_def LitE_def ab_left_minus ab_diff_minus)

instance vdme :: ("{semiring_1,vbasic}") semiring_1
  by (intro_classes, auto simp add:times_vdme_def one_vdme_def BOpE_def LitE_def)

instance vdme :: ("{ring,vbasic}") ring
  by (intro_classes, auto simp add:plus_vdme_def zero_vdme_def minus_vdme_def uminus_vdme_def BOpE_def UOpE_def LitE_def ab_left_minus ab_diff_minus)

instance vdme :: ("{comm_ring,vbasic}") comm_ring ..
instance vdme :: ("{ring_1,vbasic}") ring_1 ..
instance vdme :: ("{comm_ring_1,vbasic}") comm_ring_1 
  by (intro_classes, auto simp add:times_vdme_def one_vdme_def BOpE_def LitE_def mult_1)

instance vdme :: ("{numeral,vbasic}") numeral ..
instance vdme :: ("{numeral,semiring_1,vbasic}") semiring_numeral ..

(*
abbreviation const_numerals :: "('a::{zero,ord,vbasic}) vdme set" where
"const_numerals \<equiv> {0..}" 

lemma "num_of_nat 4 = undefined"
  apply (simp add:num_of_nat.simps)


lemma "2 \<in> const_numerals"
  apply (simp add: less_eq_vdme_def zero_vdme_def plus_vdme_def num_of_nat_def)
*)

declare is_num_numeral [simp]

lemma UNREST_VDME_ring1 [unrest]: "is_num x \<Longrightarrow> UNREST_VDME vs x"
  apply (induct rule:is_num.induct)
  apply (simp_all add:unrest) 
done

definition dom :: "('a::{linorder,vbasic},'b::{linorder,vbasic}) fmap vdme \<Rightarrow> 'a fset vdme" where
"dom \<equiv> UOpE fdom"

definition ran :: "('a::{linorder,vbasic},'b::{linorder,vbasic}) fmap vdme \<Rightarrow> 'b fset vdme" where
"ran \<equiv> UOpE fran"

definition card :: "('a::{linorder,vbasic}) fset vdme \<Rightarrow> nat vdme" where
"card = UOpE fcard"

syntax
  "_uexpr_vdme" :: "'a vdme \<Rightarrow> uexpr" ("_")

translations
  "_uexpr_vdme e" == "CONST SemE e"

lemma SemE_defined [defined]: "\<D> (SemE v)"
  apply (simp add:Defined_WF_EXPRESSION_def SemE_rep_eq)
  apply (metis Defined_vdmv_def InjVB_def InjVB_nbot)
done

lemma SemE_type [typing]: 
  "SemE (v :: 'a vdme) :\<^sub>e embTYPE (Type TYPE('a))"
  apply (simp add:etype_rel_def SemE_rep_eq)
  apply (metis Abs_UTYPE_type BasicV_type Defined_vdmv_def InjVB_def InjVB_nbot Inject_type embTYPE_def utype_rel_vdmv_def)
done


lemma SemE_EvalE_compat [typing]:
  "vtype x = embTYPE (Type TYPE('a::vbasic)) \<Longrightarrow> \<lbrakk>SemE (v :: 'a vdme)\<rbrakk>\<epsilon>b \<rhd> x"
  apply (rule) back back
  apply (force intro:typing defined)
  apply (force intro:defined)
done

lemma SemE_expr_compat [typing]:
  "vtype x = embTYPE (Type TYPE('a::vbasic)) \<Longrightarrow> SemE (v :: 'a vdme) \<rhd>\<^sub>e x"
  apply (rule) back
  apply (force intro:typing defined)
  apply (force intro:defined)
done

definition EvalV :: "'a vdme \<Rightarrow> vdmv WF_BINDING \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>\<^sub>v_") where
"\<lbrakk>v\<rbrakk>\<^sub>vb = \<langle>v\<rangle>\<^sub>v b"

lemma EvalE_SemE [evale]:
  "\<lbrakk>SemE v\<rbrakk>\<epsilon>b = BasicV (Inject (\<lbrakk>v\<rbrakk>\<^sub>vb))"
  by (simp add:EvalE_def SemE_rep_eq EvalV_def)

lemma Inject_simp [simp]: "Inject x = Inject y \<longleftrightarrow> x = y"
  by (metis InjVB_def InjVB_inv)

lemma [simp]: "\<lbrakk> v1 \<rhd> x; v2 \<rhd> x \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v1) = b(x :=\<^sub>b v2) \<longleftrightarrow> v1 = v2"
by (metis binding_upd_apply)

term "1.1"

term "2"

lemma EvalV_zero [evale]: "\<lbrakk>0\<rbrakk>\<^sub>v b = 0"
  by (simp add:EvalV_def zero_vdme_def LitE_def)

lemma EvalV_one [evale]: "\<lbrakk>1\<rbrakk>\<^sub>v b = 1"
  by (simp add:EvalV_def one_vdme_def LitE_def)

lemma EvalV_plus [evale]: "\<lbrakk>x + y\<rbrakk>\<^sub>vb = \<lbrakk>x\<rbrakk>\<^sub>vb + \<lbrakk>y\<rbrakk>\<^sub>vb"
  by (simp add:EvalV_def plus_vdme_def BOpE_def)

lemma EvalV_numeral [evale]: "\<lbrakk>numeral x\<rbrakk>\<^sub>v b = numeral x"
  apply (simp add:EvalV_def)
  apply (induct x)
  apply (simp add:one_vdme_def LitE_def)
  apply (simp add:numeral.simps plus_vdme_def BOpE_def)
  apply (simp add:numeral.simps plus_vdme_def one_vdme_def BOpE_def LitE_def)
done

abbreviation "x \<equiv> MkPlain ''x'' (embTYPE IntT) False"

lemma "`''x'' := 7::int vdme \<and> ''x'' := 1::int vdme` = false"
  apply (auto simp add:evalr typing defined unrest binding_upd_apply)
  apply (simp add:evale)
done

lemma "`''x'' := 7::int vdme ; ''x'' := $''x'' + 1::int vdme` = `''x'' := 8::int vdme`"
  apply (simp)
  apply (rule trans)
  apply (rule AssignR_SemiR_left)
  apply (simp)
  apply (simp add:typing)
  apply (simp add:unrest)
  apply (simp add:evalr typing defined unrest closure)
  apply (simp add:usubst closure typing defined)
  thm AssignR_SemiP_left
  apply (simp add:AssignR_SemiP_left)

  apply (simp add:evalr typing defined unrest)
  thm EvalR_AssignR



end