(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_laws.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Extra laws for CML *}

theory utp_cml_laws
imports utp_cml_expr
begin

lemma Nats_elim [elim!]:
  "\<lbrakk> (x::real) \<in> Nats; \<lbrakk> x \<in> Ints; x \<ge> 0 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:Nats_def)

lemma Nats_floor [intro]: 
  "\<lbrakk> x \<ge> 0 \<rbrakk> \<Longrightarrow> real (floor (x :: real)) \<in> Nats"
  apply (auto simp add:Reals_def Nats_def)
  apply (metis of_nat_nat rangeI real_eq_of_int zero_le_floor)
done

lemma Nats_Ints_intro [intro]: 
  "\<lbrakk> (x::real) \<in> Ints; x \<ge> 0 \<rbrakk> \<Longrightarrow> x \<in> Nats"
  apply (auto simp add:Ints_def Nats_def)
  apply (metis Nats_def of_nat_in_Nats of_nat_nat)
done

lemma Ints_floor [intro]: 
  "floor (x :: real) \<in> Ints"
  by (metis Ints_diff Ints_of_nat int_diff_cases)

end

