(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_num.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Support for VDM numbers *}

theory utp_vdm_num
imports 
  utp_vdm_expr
begin

section {* Numbers in VDM *}

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

end