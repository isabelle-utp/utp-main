theory utp_alpha_wp
  imports utp_alpha_laws
begin

ML {*
  structure wp =
    Named_Thms (val name = @{binding wp} val description = "weakest precondition theorems")
*}

setup wp.setup

definition WeakPrecondA :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" (infixr "wp" 150) where
"Q wp r \<equiv> \<not>\<alpha> (Q ;\<alpha> (\<not>\<alpha> r))"

declare WeakPrecondA_def [evala]

lemma WeakPrecondA_alphabet [alphabet]:
  "\<lbrakk> Q \<in> WF_RELATION; r \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
  \<alpha> (Q wp r) = in\<^sub>\<alpha> (\<alpha> Q) \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> r)"
  by (simp add:WeakPrecondA_def alphabet closure)

syntax
  "_uapred_wp" :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "wp" 55)

translations
  "_uapred_wp p q"     => "CONST WeakPrecondA p q"

lemma wp_conj [wp]:
  "\<lbrakk> P \<in> WF_RELATION; q \<in> WF_RELATION; r \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
   `P wp (q \<and> r)` = `P wp q \<and> P wp r`"
  by (smt NotA_WF_RELATION SemiA_OrA_distl WeakPrecondA_def demorgan1 demorgan2)

lemma SemiA_wp [wp]: 
  "\<lbrakk> P \<in> WF_RELATION; Q \<in> WF_RELATION; r \<in> WF_RELATION \<rbrakk> 
   \<Longrightarrow> `(P ; Q) wp r` = `P wp (Q wp r)`"
  apply (simp add: WeakPrecondA_def)
  apply (smt NotA_WF_RELATION SemiA_assoc)
done

lemma CondA_wp [wp]:
  "\<lbrakk> P \<in> WF_RELATION; Q \<in> WF_RELATION; b \<in> WF_CONDITION; r \<in> WF_RELATION
   ; \<alpha> P = \<alpha> Q; \<alpha> Q = \<alpha> r; \<alpha> b \<subseteq>\<^sub>f \<alpha> P \<rbrakk> \<Longrightarrow>
   `(P \<triangleleft> b \<triangleright> Q) wp r` = `(P wp r) \<triangleleft> b \<triangleright> (Q wp r)`"
  apply (simp add: WeakPrecondA_def SemiA_CondA_distr alphabet closure)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

lemma OrA_wp [wp]:
  "\<lbrakk> P \<in> WF_RELATION; Q \<in> WF_RELATION; r \<in> WF_RELATION \<rbrakk>
   \<Longrightarrow> `(P \<or> Q) wp r` = `(P wp r) \<and> (Q wp r)`"
  by (smt NotA_WF_RELATION SemiA_OrA_distr WeakPrecondA_def demorgan1)

end