theory utp_vdm_expr
imports 
  "~~/src/HOL/Library/Option_ord"
  utp_vdm_sorts 
begin

default_sort vbasic

typedef 'a vdme = "UNIV :: (vdmv WF_BINDING \<rightharpoonup> 'a::vbasic) set" ..

declare Rep_vdme [simp]
declare Rep_vdme_inverse [simp]
declare Abs_vdme_inverse [simp]

lemma Rep_vdme_intro [intro]:
  "Rep_vdme x = Rep_vdme y \<Longrightarrow> x = y"
  by (simp add:Rep_vdme_inject)

lemma Rep_vdme_elim [elim]:
  "\<lbrakk> x = y; Rep_vdme x = Rep_vdme y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_vdme

notation Rep_vdme ("\<langle>_\<rangle>\<^sub>v")

definition UNREST_VDME :: "(vdmv VAR) set \<Rightarrow> 'a vdme \<Rightarrow> bool" where
"UNREST_VDME vs e \<equiv> (\<forall> b1 b2. \<langle>e\<rangle>\<^sub>v(b1 \<oplus>\<^sub>b b2 on vs) = \<langle>e\<rangle>\<^sub>v b1)" 

abbreviation MkVDVar :: "char list \<Rightarrow> 'a::vbasic itself \<Rightarrow> vdmv VAR" where
"MkVDVar n t \<equiv> (MkPlain n (embTYPE (Type t)) False)"

definition VarE :: "string \<Rightarrow> 'a::vbasic vdme" ("$_") where
"VarE n = Abs_vdme (\<lambda> b. Project (ProjBasicD (\<langle>b\<rangle>\<^sub>b (MkVDVar n TYPE('a)))))"

lemma UNREST_VDME_VarE [unrest]: "UNREST_VDME (VAR - {MkVDVar n TYPE('a)}) ($n :: 'a vdme)"
  by (simp add: UNREST_VDME_def VarE_def)

declare [[coercion VarE]]

definition LitE :: "'a::vbasic \<Rightarrow> 'a vdme" ("<_>") where
"LitE x = Abs_vdme (\<lambda> b. Some x)"

lemma UNREST_VDME_LitE [unrest]: "UNREST_VDME vs <x>"
  by (simp add:UNREST_VDME_def LitE_def)

definition UOpE :: "('a::vbasic \<rightharpoonup> 'b::vbasic) \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme" where
"UOpE f v = Abs_vdme (\<lambda> b. (Rep_vdme v b) >>= f)"

abbreviation UOpE' :: "('a::vbasic \<Rightarrow> 'b::vbasic)
                      \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme" where
"UOpE' f \<equiv> UOpE (\<lambda> v. Some (f v))"

lemma UNREST_VDME_UOpE [unrest]: "UNREST_VDME vs v \<Longrightarrow> UNREST_VDME vs (UOpE f v)"
  by (simp add:UNREST_VDME_def UOpE_def)

definition BOpE :: "('a::vbasic \<rightharpoonup> 'b::vbasic \<rightharpoonup> 'c::vbasic) 
                   \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme \<Rightarrow> 'c vdme" where
"BOpE f v1 v2 = Abs_vdme (\<lambda> b. do { x <- \<langle>v1\<rangle>\<^sub>v b; y <- \<langle>v2\<rangle>\<^sub>v b; g <- f x; g y })"

abbreviation BOpE' :: "('a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic)
                      \<Rightarrow> 'a vdme \<Rightarrow> 'b vdme \<Rightarrow> 'c vdme" where
"BOpE' f \<equiv> BOpE (\<lambda> v1. Some (\<lambda> v2. Some (f v1 v2)))"

lemma UNREST_VDME_BOpE [unrest]: "\<lbrakk> UNREST_VDME vs v1; UNREST_VDME vs v2 \<rbrakk> \<Longrightarrow> UNREST_VDME vs (BOpE f v1 v2)"
  by (simp add:UNREST_VDME_def BOpE_def)

fun sequence :: "'a option list \<Rightarrow> 'a list option" where
"sequence [] = Some []" |
"sequence (f # fs) = do { x \<leftarrow> f; xs \<leftarrow> sequence fs; Some (x # xs) }"

abbreviation "mapM f \<equiv> sequence \<circ> map f"

definition fset_option :: "'a option fset \<Rightarrow> 'a fset option" where
"fset_option xs = (if (None \<in>\<^sub>f xs) then None else Some (the `\<^sub>f xs))"

lemma fset_option_empty: 
  "fset_option \<lbrace>\<rbrace> = Some \<lbrace>\<rbrace>"
  by (simp add:fset_option_def)

definition ListE :: "'a::vbasic vdme list \<Rightarrow> 'a list vdme" where
"ListE xs = Abs_vdme (\<lambda> b. mapM (\<lambda> v. \<langle>v\<rangle>\<^sub>v b) xs)"

declare [[coercion ListE]]

lemma UNREST_VDME_ListE [unrest]: 
  "\<lbrakk> \<forall> x \<in> set xs. UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (ListE xs)"
  apply (induct xs)
  apply (auto simp add:UNREST_VDME_def ListE_def)
done

definition FSetE :: "'a::vbasic vdme fset \<Rightarrow> 'a fset vdme" where
"FSetE xs = Abs_vdme (\<lambda> b. fset_option ((\<lambda> v. \<langle>v\<rangle>\<^sub>v b) `\<^sub>f xs))"

declare [[coercion FSetE]]

lemma UNREST_VDME_FSetE [unrest]: 
  "\<lbrakk> \<forall> x \<in>\<^sub>f xs. UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (FSetE xs)"
  apply (simp add:UNREST_VDME_def FSetE_def)
  apply (clarify)
  apply (simp add:fimage.rep_eq fset_option_def)
  apply (safe)
oops

lemma embTYPE_inv_vdm [simp]: 
  "prjTYPE (embTYPE VTYPE('a) :: vdmv UTYPE) = VTYPE('a)"
  apply (rule_tac embTYPE_inv[of "BasicD (Inject undefined)"])
  apply (auto simp add:utype_rel_vdmv_def Defined_vdmv_def)
  apply (rule)
  apply (rule Inject_type)
done

lift_definition SemE :: "'a::vbasic vdme \<Rightarrow> vdmv WF_EXPRESSION" is
"\<lambda> f. (\<lambda> b. case \<langle>f\<rangle>\<^sub>v b of Some v \<Rightarrow> BasicD (Inject v) | None \<Rightarrow> \<bottom>\<^bsub>VTYPE('a)\<^esub>)"
  apply (simp add:WF_EXPRESSION_def)
  apply (rule_tac x="embTYPE VTYPE('a)" in exI)
  apply (rule)
  apply (simp add:type_rel_vdmt)
  apply (case_tac "\<langle>vdme\<rangle>\<^sub>v b")
  apply (auto)
done

lemma UNREST_EXPR_SemE [unrest]:
  "UNREST_VDME vs e \<Longrightarrow> UNREST_EXPR vs (SemE e)"
  by (simp add:UNREST_EXPR_def UNREST_VDME_def SemE.rep_eq)

lemma SemE_expr_type [simp]: 
  "expr_type (SemE (v::'a vdme)) = embTYPE VTYPE('a)"
  apply (simp add:expr_type_def etype_rel_def SemE.rep_eq type_rel_vdmt)
  apply (rule the_equality, rule)
  apply (case_tac "\<langle>v\<rangle>\<^sub>v b")
  apply (auto)
  apply (drule_tac x="\<B>" in spec)
  apply (case_tac "\<langle>v\<rangle>\<^sub>v \<B>")
  apply (auto)
  apply (metis BasicD_type_cases BotI_type_cases prjTYPE_inv_vdm)
  apply (metis BasicD_type_cases Inject_type prjTYPE_inv_vdm vbasic_type_rel_uniq)
done

instantiation vdme :: (vbasic) DEFINED
begin

definition Defined_vdme :: "'a vdme \<Rightarrow> bool" where
"\<D>(e) \<longleftrightarrow> (\<forall> b. (\<langle>e\<rangle>\<^sub>v b \<noteq> None))"

instance ..

end


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
  apply (metis option.inject zero_neq_one)
done
  
instantiation vdme :: ("{plus,vbasic}") plus
begin

definition plus_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"plus_vdme = BOpE' (op +)"

instance ..

end

lemma UNREST_VDME_plus [unrest]: 
  "\<lbrakk> UNREST_VDME vs x; UNREST_VDME vs y \<rbrakk> \<Longrightarrow> UNREST_VDME vs (x + y)"
  by (simp add:plus_vdme_def unrest)

instantiation vdme :: ("{minus,vbasic}") minus
begin

definition minus_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"minus_vdme = BOpE' (op -)"

instance ..

end

lemma UNREST_VDME_minus [unrest]: 
  "\<lbrakk> UNREST_VDME vs x; UNREST_VDME vs y \<rbrakk> \<Longrightarrow> UNREST_VDME vs (x - y)"
  by (simp add:minus_vdme_def unrest)

instantiation vdme :: ("{uminus,vbasic}") uminus
begin

definition uminus_vdme :: "'a vdme \<Rightarrow> 'a vdme" where
"uminus_vdme = UOpE' uminus"

instance ..

end

lemma UNREST_VDME_uminus [unrest]: 
  "\<lbrakk> UNREST_VDME vs x \<rbrakk> \<Longrightarrow> UNREST_VDME vs (- x)"
  by (simp add:uminus_vdme_def unrest)

instantiation vdme :: ("{times, vbasic}") times
begin

definition times_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"times_vdme = BOpE' (op *)"

instance ..
end

lemma UNREST_VDME_times [unrest]: 
  "\<lbrakk> UNREST_VDME vs x; UNREST_VDME vs y \<rbrakk> \<Longrightarrow> UNREST_VDME vs (x * y)"
  by (simp add:times_vdme_def unrest)

instantiation vdme :: ("{inverse,vbasic}") inverse
begin

definition inverse_vdme :: "'a vdme \<Rightarrow> 'a vdme" where
"inverse_vdme = UOpE' inverse"

definition divide_vdme :: "'a vdme \<Rightarrow> 'a vdme \<Rightarrow> 'a vdme" where
"divide_vdme = BOpE' divide"

instance ..

end

instantiation vdme :: ("{preorder,vbasic}") ord
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
  apply (auto simp add:plus_vdme_def BOpE_def)
  apply (rule, rule ext, auto)
  apply (case_tac "\<langle>a\<rangle>\<^sub>v x", auto, case_tac "\<langle>b\<rangle>\<^sub>v x", auto simp add:add_commute)
done

instance vdme :: ("{semigroup_mult, vbasic}") semigroup_mult
  by (intro_classes, auto simp add:times_vdme_def BOpE_def mult_assoc)

instance vdme :: ("{ab_semigroup_mult,vbasic}") ab_semigroup_mult
  apply (intro_classes, auto simp add:times_vdme_def BOpE_def)
  apply (rule, rule ext, auto)
  apply (case_tac "\<langle>a\<rangle>\<^sub>v x", auto, case_tac "\<langle>b\<rangle>\<^sub>v x", auto simp add:mult_commute)
done

(*
instance vdme :: ("{comm_monoid_mult,vbasic}") comm_monoid_mult
  by (intro_classes, auto simp add:times_vdme_def one_vdme_def BOpE_def LitE_def mult_1)
*)  

instance vdme :: ("{semiring,vbasic}") semiring
  apply (intro_classes, auto simp add:plus_vdme_def times_vdme_def BOpE_def distrib_right distrib_left)
  apply (rule, rule ext, auto)
  apply (case_tac "\<langle>a\<rangle>\<^sub>v x", auto, case_tac "\<langle>b\<rangle>\<^sub>v x", auto, case_tac "\<langle>c\<rangle>\<^sub>v x", auto simp add:distrib_right)
  apply (rule, rule ext, auto)
  apply (case_tac "\<langle>a\<rangle>\<^sub>v x", auto)
done

instance vdme :: ("{comm_semiring,vbasic}") comm_semiring
  apply (intro_classes, auto simp add:plus_vdme_def times_vdme_def BOpE_def distrib)
  apply (rule, rule ext, auto)
  apply (case_tac "\<langle>a\<rangle>\<^sub>v x", auto, case_tac "\<langle>b\<rangle>\<^sub>v x", auto, case_tac "\<langle>c\<rangle>\<^sub>v x", auto simp add:distrib)
done

(*
instance vdme :: ("{semiring_0,vbasic}") semiring_0
  apply (intro_classes, auto simp add:plus_vdme_def times_vdme_def zero_vdme_def BOpE_def LitE_def ab_left_minus ab_diff_minus)
  apply (rule, rule ext, auto, case_tac "\<langle>a\<rangle>\<^sub>v x", auto)


instance vdme :: ("{semiring_1,vbasic}") semiring_1
  apply (intro_classes, auto simp add:times_vdme_def one_vdme_def BOpE_def LitE_def)

instance vdme :: ("{ring,vbasic}") ring
  by (intro_classes, auto simp add:plus_vdme_def zero_vdme_def minus_vdme_def uminus_vdme_def BOpE_def UOpE_def LitE_def ab_left_minus ab_diff_minus)

instance vdme :: ("{comm_ring,vbasic}") comm_ring ..
instance vdme :: ("{ring_1,vbasic}") ring_1 ..
instance vdme :: ("{comm_ring_1,vbasic}") comm_ring_1 
  by (intro_classes, auto simp add:times_vdme_def one_vdme_def BOpE_def LitE_def mult_1)


instance vdme :: ("{numeral,vbasic}") numeral ..
(*
instance vdme :: ("{numeral,semiring_1,vbasic}") semiring_numeral ..
*)

declare is_num_numeral [simp]

lemma UNREST_VDME_ring1 [unrest]: "is_num x \<Longrightarrow> UNREST_VDME vs x"
  apply (induct rule:is_num.induct)
  apply (simp_all add:unrest) 
done

lemma UNREST_VDME_numeral [unrest]:
  "UNREST_VDME vs (numeral x)"
  apply (induct x)
  apply (simp_all add:unrest numeral.simps)
  apply (simp only:numeral_plus_numeral[symmetric] unrest)
  apply (simp only:numeral_plus_numeral[symmetric] numeral_One unrest)
done
*)

definition dom :: "('a::{linorder,vbasic},'b::{linorder,vbasic}) fmap vdme \<Rightarrow> 'a fset vdme" where
"dom \<equiv> UOpE' fdom"

definition ran :: "('a::{linorder,vbasic},'b::{linorder,vbasic}) fmap vdme \<Rightarrow> 'b fset vdme" where
"ran \<equiv> UOpE' fran"

definition card :: "('a::{linorder,vbasic}) fset vdme \<Rightarrow> nat vdme" where
"card = UOpE' fcard"

syntax
  "_uexpr_vdme" :: "'a vdme \<Rightarrow> uexpr" ("_")

translations
  "_uexpr_vdme e" == "CONST SemE e"

lemma SemE_defined [defined]: "\<D> v \<Longrightarrow> \<D> (SemE v)"
  apply (auto simp add:Defined_WF_EXPRESSION_def Defined_vdme_def SemE.rep_eq)
  apply (metis Defined_vdmv_def InjVB_def InjVB_nbot option.simps(5))
done

lemma SemE_type [typing]: 
  "SemE (v :: 'a vdme) :\<^sub>e embTYPE VTYPE('a)"
  apply (auto simp add:etype_rel_def SemE.rep_eq)
  apply (case_tac "\<langle>v\<rangle>\<^sub>v b")
  apply (auto simp add:type_rel_vdmt)
done

lemma SemE_EvalE_compat [typing]:
  "\<lbrakk> \<D> v; vtype x = embTYPE VTYPE('a) \<rbrakk> \<Longrightarrow> \<lbrakk>SemE (v :: 'a vdme)\<rbrakk>\<epsilon>b \<rhd> x"
  apply (rule) back back
  apply (force intro:typing defined)
  apply (force intro:defined)
done

lemma SemE_expr_compat [typing]:
  "\<lbrakk> \<D> v; vtype x = embTYPE VTYPE('a) \<rbrakk> \<Longrightarrow> SemE (v :: 'a vdme) \<rhd>\<^sub>e x"
  apply (rule) back
  apply (force intro:typing defined)
  apply (force intro:defined)
done

definition EvalD :: "'a vdme \<Rightarrow> vdmv WF_BINDING \<Rightarrow> 'a option" ("\<lbrakk>_\<rbrakk>\<^sub>v_") where
"\<lbrakk>v\<rbrakk>\<^sub>vb = \<langle>v\<rangle>\<^sub>v b"

lemma EvalE_SemE [evale]:
  "\<lbrakk>SemE v\<rbrakk>\<epsilon>b = BasicD (Inject (\<lbrakk>v\<rbrakk>\<^sub>vb))"
  by (simp add:EvalE_def SemE_rep_eq EvalD_def)

lemma Inject_simp [simp]: "Inject x = Inject y \<longleftrightarrow> x = y"
  by (metis InjVB_def InjVB_inv)

lemma [simp]: "\<lbrakk> v1 \<rhd> x; v2 \<rhd> x \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v1) = b(x :=\<^sub>b v2) \<longleftrightarrow> v1 = v2"
by (metis binding_upd_apply)

lemma EvalD_zero [evale]: "\<lbrakk>0\<rbrakk>\<^sub>v b = 0"
  by (simp add:EvalD_def zero_vdme_def LitE_def)

lemma EvalD_one [evale]: "\<lbrakk>1\<rbrakk>\<^sub>v b = 1"
  by (simp add:EvalD_def one_vdme_def LitE_def)

lemma EvalD_plus [evale]: "\<lbrakk>x + y\<rbrakk>\<^sub>vb = \<lbrakk>x\<rbrakk>\<^sub>vb + \<lbrakk>y\<rbrakk>\<^sub>vb"
  by (simp add:EvalD_def plus_vdme_def BOpE_def)

lemma EvalD_numeral [evale]: "\<lbrakk>numeral x\<rbrakk>\<^sub>v b = numeral x"
  apply (simp add:EvalD_def)
  apply (induct x)
  apply (simp add:one_vdme_def LitE_def)
  apply (simp add:numeral.simps plus_vdme_def BOpE_def)
  apply (simp add:numeral.simps plus_vdme_def one_vdme_def BOpE_def LitE_def)
done

lemma EvalD_LitE [evale]:
  "\<lbrakk><x>\<rbrakk>\<^sub>vb = x"
  by (simp add:LitE_def EvalD_def)

abbreviation "x \<equiv> MkPlain ''x'' (embTYPE IntT) False"

(*
lemma "\<lbrakk> v1 \<rhd>\<^sub>e x; v2 \<rhd>\<^sub>e x; UNREST_EXPR DASHED v1; UNREST_EXPR DASHED v2; UNREST_EXPR {x} v2 \<rbrakk> \<Longrightarrow> `x := v1; x := v2` = `x := v2`"
  apply (utp_rel_auto_tac)
  apply (simp add:evale typing defined)
  apply (simp add:evale typing defined)
  apply (simp add:evale typing defined)
  apply (utp_expr_tac)
*)

lemma "`''x'' := 6::nat vdme ; ''x'' := 7::nat vdme` = `''x'' := 7::nat vdme`"
  apply (simp add:evalr typing defined unrest binding_upd_apply relcomp_unfold)
  apply (simp add:evale relcomp_unfold typing defined)

  apply (auto)
done


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