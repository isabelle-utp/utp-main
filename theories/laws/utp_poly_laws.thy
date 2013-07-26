(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_laws.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Laws for polymorphic predicates *}

theory utp_poly_laws
imports 
  "../poly/utp_poly_expr"
  "../parser/utp_pred_parser"
  utp_pred_laws
  utp_rename_laws
  utp_subst_laws
begin

lemma BoolType_pvaux_cases [ucases]:
  assumes "pvaux x" 
  shows "p = q \<longleftrightarrow> `p[false/x]` = `q[false/x]` \<and> `p[true/x]` = `q[true/x]`"
  using assms
  apply (rule_tac iffI)
  apply (utp_pred_tac)
  apply (rule BoolType_aux_var_split_eq_intro[of "x\<down>"])
  apply (simp_all add:typing defined erasure pvaux_aux)
done

end