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
apply (utp_pred_taut_tac)
apply (auto)
done

subsection {* Simons Theorems *}

theorem OrP_assoc:
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE;
 p3 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p (p2 \<or>p p3) = (p1 \<or>p p2) \<or>p p3"
apply (utp_pred_taut_tac)
apply (auto)
done

theorem OrP_comm:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p \<or>p q = q \<or>p p"
apply (utp_pred_taut_tac)
apply (auto)
done

theorem OrP_identity:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
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

theorem Huntington:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE;
 \<alpha> q \<subseteq> \<alpha> p\<rbrakk> \<Longrightarrow>
 \<not>p (\<not>p p \<or>p \<not>p q) \<or>p \<not>p (\<not>p p \<or>p q) = p"
apply (utp_pred_eq_tac)
apply (auto)
done


theorem OrP_RefP1:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE;
 \<alpha> p = \<alpha> q; p \<or>p q = q \<rbrakk> \<Longrightarrow>
 q \<sqsubseteq> p"
apply (utp_pred_taut_tac)
apply(auto)
done

theorem OrP_RefP2:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE;
 \<alpha> p = \<alpha> q; q \<sqsubseteq> p \<rbrakk> \<Longrightarrow>
 p \<or>p q = q"
apply (utp_pred_taut_tac)
apply(rule ballI)
apply(erule ballE)
apply(auto)
done

theorem OrP_RefP:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow>
(\<alpha> p = \<alpha> q \<and> p \<or>p q = p) = (\<alpha> p = \<alpha> q \<and> p \<sqsubseteq> q)"
  by (metis OrP_RefP1 OrP_RefP2 OrP_comm)

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
