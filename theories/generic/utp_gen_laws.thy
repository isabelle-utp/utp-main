(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_gen_laws.thy                                         *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Generic Laws *}

theory utp_gen_laws
imports utp_eval_tactic (* "../algebra/alpha_boolean_algebra2" *)
begin


context GEN_PRED
begin
theorem AndP_intro :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 \<alpha> p2 \<subseteq> \<alpha> p1;
 taut (p1 \<Rightarrow>p p2)\<rbrakk> \<Longrightarrow> p1 = (p1 \<and>p p2)"
  by (utp_pred_eq_tac2)

subsection {* Simons Theorems *}

theorem OrP_assoc:
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p (p2 \<or>p p3) = (p1 \<or>p p2) \<or>p p3"
  by (utp_pred_eq_tac2)


theorem OrP_comm:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p \<or>p q = q \<or>p p"
  by (utp_pred_eq_tac2)

theorem OrP_identity:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<subseteq> \<alpha> p\<rbrakk> \<Longrightarrow>
 p \<or>p false a = p"
apply(frule_tac a="a" in WF_ALPHA_PREDICATE_subset)
apply(auto simp add:closure alphabet alpha_closure eval)+
done

theorem OrP_AndP_dist:
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p (p2 \<and>p p3) = (p1 \<or>p p2) \<and>p (p1 \<or>p p3)"
 by (utp_pred_eq_tac2)


theorem Huntington:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE;
 \<alpha> q \<subseteq> \<alpha> p\<rbrakk> \<Longrightarrow>
 \<not>p (\<not>p p \<or>p \<not>p q) \<or>p \<not>p (\<not>p p \<or>p q) = p"
 by (utp_pred_eq_tac2)

theorem OrP_RefP1:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE;
 \<alpha> q = \<alpha> p; p \<or>p q = q \<rbrakk> \<Longrightarrow>
 q \<sqsubseteq> p"
  by (utp_pred_eq_tac2)

theorem OrP_RefP2:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE;
 \<alpha> p = \<alpha> q; q \<sqsubseteq> p \<rbrakk> \<Longrightarrow>
 p \<or>p q = q"
  by (utp_pred_eq_tac2)

theorem OrP_RefP:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow>
(\<alpha> p = \<alpha> q \<and> p \<or>p q = p) = (\<alpha> p = \<alpha> q \<and> p \<sqsubseteq> q)"
  by (metis OrP_RefP1 OrP_RefP2 OrP_comm)

theorem ResP_extrude:
assumes "p \<in> WF_ALPHA_PREDICATE" "q \<in> WF_ALPHA_PREDICATE"
        "a \<in> WF_ALPHABET" "a \<inter> \<alpha> p = {}"
shows   "p \<and>p (q \<ominus>p a) = (p \<and>p q) \<ominus>p a"
  by (insert assms, utp_pred_eq_tac2)

theorem ExistsResP_extrude:
assumes "p \<in> WF_ALPHA_PREDICATE" "q \<in> WF_ALPHA_PREDICATE"
        "a \<in> WF_ALPHABET" "a \<inter> \<alpha> p = {}"
shows   "p \<and>p (\<exists>-p a . q) = (\<exists>-p a . (p \<and>p q))"
  by (insert assms, utp_pred_eq_tac2)

theorem ExistsResP_merge:
assumes "p \<in> WF_ALPHA_PREDICATE" "a \<in> WF_ALPHABET" "b \<in> WF_ALPHABET"
shows "(\<exists>-p a . \<exists>-p b. p) = (\<exists>-p (a \<union> b) . p)"
  apply (insert assms)
  apply (utp_pred_eq_tac2)
  apply (auto simp add:override_on_assoc)
  apply (metis override_on_idem)
done

theorem ResP_vacuous:
assumes "p \<in> WF_ALPHA_PREDICATE"
        "a \<in> WF_ALPHABET" "a \<inter> \<alpha> p = {}"
shows "p = p \<ominus>p a"
  by (insert assms, utp_pred_eq_tac2)

theorem ExistsResP_vacuous:
assumes "p \<in> WF_ALPHA_PREDICATE"
        "a \<in> WF_ALPHABET" "a \<inter> \<alpha> p = {}"
shows "p = (\<exists>-p a. p)"
  by (insert assms, utp_pred_eq_tac2)

(* The commented code is instantiation of the boolean algebra *)

(*
abbreviation "GEN_PRED_algebra \<equiv>
 \<lparr> alpha_boolean_algebra.carrier = WF_ALPHA_PREDICATE,
   wfalpha = WF_ALPHABET,
   alpha = alphabet,
   conj = AndP,
   disj = OrP,
   compl = NotP,
   top = TrueP,
   bot = FalseP,
   ble = (\<lambda> x y. (\<alpha> x = \<alpha> y \<and> y \<sqsubseteq> x)) \<rparr>"
end

subsection {* Sublocale @{term alpha_boolean_algebra} *}

sublocale GEN_PRED \<subseteq> alpha_boolean_algebra "GEN_PRED_algebra" where
"alpha_boolean_algebra.carrier GEN_PRED_algebra = WF_ALPHA_PREDICATE" and
"wfalpha GEN_PRED_algebra = WF_ALPHABET" and
"alpha GEN_PRED_algebra = alphabet" and
"conj GEN_PRED_algebra = AndP" and
"disj GEN_PRED_algebra = OrP" and
"compl GEN_PRED_algebra = NotP"  and
"top GEN_PRED_algebra = TrueP" and
"bot GEN_PRED_algebra = FalseP" and
"ble GEN_PRED_algebra = (\<lambda> x y. (\<alpha> x = \<alpha> y \<and> y \<sqsubseteq> x))"
apply(unfold_locales)
apply(simp_all)
apply(utp_pred_eq_tac)
apply(utp_pred_eq_tac)
apply(utp_pred_eq_tac)
apply(utp_pred_eq_tac)
apply (metis OrP_RefP OrP_comm)
apply(smt OrP_assoc)
apply(smt OrP_comm)
apply(metis OrP_identity set_eq_subset)
apply(smt OrP_AndP_dist)
done

context GEN_PRED
begin

thm Upper_mem_cong


end
*)

end
end
