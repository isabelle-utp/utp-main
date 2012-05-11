(******************************************************************************)
(* Title: utp/generic/utp_gen_laws.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Generic Laws *}

theory utp_gen_laws
imports utp_eval_tactic
begin

context GEN_PRED
begin
theorem AndP_intro :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 (\<alpha> p1) = (\<alpha> p2);
 taut (p1 \<Rightarrow>p p2)\<rbrakk> \<Longrightarrow> p1 = (p1 \<and>p p2)"
apply (utp_pred_taut_tac)
apply (auto)
done
end
end