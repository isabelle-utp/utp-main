(******************************************************************************)
(* Title: utp/generic/utp_gen_laws.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Generic Laws *}

theory utp_gen_laws
imports utp_eval_tactic "../algebra/alpha_boolean_algebra2"
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

theorem OrP_assoc:
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p (p2 \<or>p p3) = (p1 \<or>p p2) \<or>p p3"
by (utp_pred_eq_tac) (auto)

theorem OrP_comm:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p \<or>p q = q \<or>p p"
 by (utp_pred_eq_tac) (auto)

theorem OrP_identity:
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE;
   a \<subseteq> \<alpha> p\<rbrakk> \<Longrightarrow>
 p \<or>p false a = p"
  apply(frule WF_ALPHA_PREDICATE_subset)
  apply(auto)
  apply(utp_pred_eq_tac)
  apply(auto)
done

theorem OrP_AndP_dist:
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p (p2 \<and>p p3) = (p1 \<or>p p2) \<and>p (p1 \<or>p p3)"
apply (utp_pred_eq_tac)
apply (auto)
done

theorem huntington:
 "\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
   q \<in> WF_ALPHA_PREDICATE;
   \<alpha> q \<subseteq> \<alpha> p \<rbrakk> \<Longrightarrow>
  \<not>p (\<not>p p \<or>p \<not>p q) \<or>p \<not>p (\<not>p p \<or>p q) = p"
  by (utp_pred_eq_tac) (auto)


abbreviation "GEN_PRED_algebra \<equiv> \<lparr> alpha_boolean_algebra.carrier = WF_ALPHA_PREDICATE, wfalpha = WF_ALPHABET, alpha = alphabet, conj = AndP, disj = OrP, compl = NotP, top = TrueP, bot = FalseP, ble = (\<lambda> x y. Refinement y x) \<rparr>"

end

sublocale GEN_PRED \<subseteq> alpha_boolean_algebra "GEN_PRED_algebra" where
"alpha_boolean_algebra.carrier GEN_PRED_algebra = WF_ALPHA_PREDICATE" and
"wfalpha GEN_PRED_algebra = WF_ALPHABET" and
"alpha   GEN_PRED_algebra = alphabet" and
"conj    GEN_PRED_algebra = AndP" and
"disj    GEN_PRED_algebra = OrP" and
"compl   GEN_PRED_algebra = NotP"  and
"top     GEN_PRED_algebra = TrueP" and
"bot     GEN_PRED_algebra = FalseP" and
"ble     GEN_PRED_algebra = (\<lambda> x y. Refinement y x)"
apply(unfold_locales)
apply(simp_all)
apply(utp_pred_eq_tac)+
apply(utp_pred_taut_tac)
apply(auto)
apply(erule_tac ballE)+
apply(auto)
apply(smt OrP_assoc)
apply(smt OrP_comm)
apply(metis OrP_identity set_eq_subset)
apply(smt OrP_AndP_dist)
done


end