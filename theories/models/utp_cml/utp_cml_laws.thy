(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_laws.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Extra laws for CML *}

theory utp_cml_laws
imports
  utp_cml_expr
  utp_cml_functions
begin

lemma Nats_elim [elim!]:
  "\<lbrakk> (x::real) \<in> Nats; \<lbrakk> x \<in> Ints; x \<ge> 0 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:Nats_def)

lemma Nats_floor [intro]: 
  "\<lbrakk> x \<ge> 0 \<rbrakk> \<Longrightarrow> real (hol_floor (x :: real)) \<in> Nats"
  apply (auto simp add: Nats_def)
  apply (metis of_nat_nat rangeI real_eq_of_int zero_le_floor)
done

lemma Nats_Ints_intro [intro]: 
  "\<lbrakk> (x::real) \<in> Ints; x \<ge> 0 \<rbrakk> \<Longrightarrow> x \<in> Nats"
  apply (auto simp add:Ints_def Nats_def)
  apply (metis Nats_def of_nat_in_Nats of_nat_nat)
done

lemma Ints_floor [intro]: 
  "hol_floor (x :: real) \<in> Ints"
  by (metis Ints_diff Ints_of_nat int_diff_cases)

(* This law allows integers in CML (elements of Ints) to
   be converted to HOL typed integers. This has the 
   advantage that HOL laws can be applied. *)

lemma Ints_elim [elim]:
  "\<lbrakk> x \<in> \<int>; \<And> (y :: int). \<lbrakk> x = real y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis Ints_cases real_eq_of_int)

(* The following laws are present in the default simplier
   but in reverse. However for CML we will often need to
   convert a real to an integer/nat so we can take advantage
   of HOL laws. Need to decide the best strategy for
   dealing with this. Do we always want to convert VDM
   types to HOL types through these abstractions? Need to
   experiment... *)

lemma Ints_abstract:
  "(0::real) = real (0 :: int)"
  "(numeral n) = real ((numeral n) :: int)"
  "(plus (real (x :: int)) (real y)) = real (plus x y)"
  "(minus (real (x :: int)) (real y)) = real (minus x y)"
  "real (x::int) \<le> real y \<longleftrightarrow> x \<le> y"
  "real (x::int) = real y \<longleftrightarrow> x = y"
  "real (x::int) \<in> Nats \<longleftrightarrow> x \<ge> 0"
  by (auto)

lemma vallI [intro!]: "\<lbrakk> \<And> x. x \<in> A \<Longrightarrow> TautDE (F(x)) \<rbrakk> \<Longrightarrow> ForallD A F"
  by (utp_poly_tac)

lemma vexI [intro]: "\<lbrakk> x \<in> A; TautDE (F(x)) \<rbrakk> \<Longrightarrow> ExistsD A F"
  by (utp_poly_auto_tac)

lemma vinvI [intro!]: "\<lbrakk> x \<in> A; TautDE (F(x)) \<rbrakk> \<Longrightarrow> x \<in> InvS A F"
  by (utp_poly_tac)

lemma ApplyD_fun_taut [intro!]: "TautDE (f(v)) \<Longrightarrow> TautDE (ApplyD_fun f (LitD v))"
  by (simp add:TautDE_def evalp)

lemma HasType_bool_taut [simp]: "|@P : @bool| = |@P|"
  by (auto simp add:evalp)

lemma vin_set_rangeI [intro!]:
  "\<lbrakk> x \<in> Ints; |&x >= &m|; |&x <= &n| \<rbrakk> \<Longrightarrow> |&x in @set {&m,...,&n}|"
  apply (auto elim!:Ints_elim simp add:evalp fatLeastAtMost.rep_eq)
  apply (rule imageI)
  apply (auto)
  apply (metis eq_iff floor_real_of_int linear real_le_floor)
  apply (metis le_floor)
done

lemma vleqI [intro]: "x \<le> y \<Longrightarrow> |&x <= &y|"
  by (utp_poly_tac)

lemma vinset_range [simp]:
  "|&i in @set {&m,...,&n}| = |&i hasType @int and &i >= floor(&m) and &i <= floor(&n)|"
  by (auto simp add:evalp fatLeastAtMost.rep_eq)

(* This causes problems so I've disabled it from the tactic for now *)

declare EvalD_vexpr_set_range [evalp del]

end

