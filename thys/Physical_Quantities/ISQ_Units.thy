section \<open> Units \<close>

theory ISQ_Units
  imports ISQ_Proof
begin

text \<open> Parallel to the base quantities, there are base units. In the implementation of
  the SI unit system, we fix these to be precisely those quantities that have a base dimension
  and a magnitude of \<^term>\<open>1\<close>. Consequently, a base unit corresponds to a unit in the algebraic
  sense. \<close>

lift_definition is_base_unit :: "'a::one['d::dim_type, 's::unit_system] \<Rightarrow> bool" 
  is "\<lambda> x. mag x = 1 \<and> is_BaseDim (dim x)" . 

definition mk_base_unit :: "'u itself \<Rightarrow> 's itself \<Rightarrow> ('a::one)['u::basedim_type, 's::unit_system]" 
  where "mk_base_unit t s = 1"

syntax "_mk_base_unit" :: "type \<Rightarrow> type \<Rightarrow> logic" ("BUNIT'(_, _')")
translations "BUNIT('a, 's)" == "CONST mk_base_unit TYPE('a) TYPE('s)"

lemma mk_base_unit: "is_base_unit (mk_base_unit a s)"
  by (simp add: mk_base_unit_def si_eq, transfer, simp add: is_BaseDim)

lemma magQ_mk [si_eq]: "\<lbrakk>BUNIT('u::basedim_type, 's::unit_system)\<rbrakk>\<^sub>Q = 1"
  by (simp add: mk_base_unit_def magQ_def si_eq, transfer, simp)

end