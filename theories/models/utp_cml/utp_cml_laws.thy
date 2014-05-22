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
  apply (auto simp add: Nats_def)
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

(* This law allows integers in CML (elements of Ints) to
   be converted to HOL typed integers. This has the 
   advantage that HOL laws can be applied. *)

lemma Ints_elim:
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

end

