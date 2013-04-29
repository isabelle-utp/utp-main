theory utp_wp
  imports utp_laws utp_lattice utp_recursion
begin

ML {*
  structure wp =
    Named_Thms (val name = @{binding wp} val description = "weakest precondition theorems")
*}

setup wp.setup

definition WeakPrecondP :: 
  "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE" (infixr "wp" 150) where
"Q wp r \<equiv> \<not>p (Q ; (\<not>p r))"

declare WeakPrecondP_def [eval,evalr]

lemma ConjP_wp [wp]:
  "P wp (q \<and>p r) = (P wp q) \<and>p (P wp r)"
  by (metis (no_types) SemiP_OrP_distl WeakPrecondP_def demorgan1 demorgan2)

lemma SemiR_wp [wp]: 
  "(P ; Q) wp r = P wp (Q wp r)"
  apply (simp add: WeakPrecondP_def)
  apply (metis NotP_NotP SemiP_assoc)
done

lemma CondP_wp [wp]:
  "\<lbrakk> UNREST DASHED_TWICE P; UNREST DASHED b;  UNREST DASHED_TWICE b;
     UNREST DASHED_TWICE Q; UNREST DASHED_TWICE r \<rbrakk> \<Longrightarrow>
  (P \<triangleleft> b \<triangleright> Q) wp r = (P wp r) \<triangleleft> b \<triangleright> (Q wp r)"
  apply (subgoal_tac "UNREST DASHED_TWICE (\<not>p r)")
  apply (simp add: WeakPrecondP_def SemiR_CondR_distr)
  apply (utp_pred_auto_tac)
  apply (blast intro:unrest)
done

lemma OrP_wp [wp]:
  "(P \<or>p Q) wp r = (P wp r) \<and>p (Q wp r)"
  by (metis (no_types) SemiP_OrP_distr WeakPrecondP_def demorgan1)

lemma ChoiceP_wp [wp]:
  "(P \<sqinter> Q) wp r = (P wp r) \<and>p (Q wp r)"
  by (simp add:sup_WF_PREDICATE_def wp)

lemma ImpliesP_precond_wp: "[r \<Rightarrow>p s]p \<Longrightarrow> [(Q wp r) \<Rightarrow>p (Q wp s)]p"
  by (metis ConjP_wp RefP_AndP RefP_def less_eq_WF_PREDICATE_def)

lemma ImpliesP_pred_wp: "[Q \<Rightarrow>p S]p \<Longrightarrow> [(S wp r) \<Rightarrow>p (Q wp r)]p"
  by (metis OrP_comm OrP_wp RefP_def inf_WF_PREDICATE_def le_iff_inf le_iff_sup less_eq_WF_PREDICATE_def sup_WF_PREDICATE_def)

lemma RefineP_precond_wp: "[r \<Rightarrow>p s]p \<Longrightarrow> Q wp s \<sqsubseteq> Q wp r"
  by (metis ImpliesP_precond_wp RefP_def less_eq_WF_PREDICATE_def)

lemma RefineP_pred_wp: "S \<sqsubseteq> Q \<Longrightarrow> Q wp r \<sqsubseteq> S wp r"
  by (metis OrP_wp RefP_AndP le_iff_sup sup_WF_PREDICATE_def)

lemma FalseP_wp: "Q ; true = true \<Longrightarrow> Q wp false = false"
  by (simp add:WeakPrecondP_def)

lemma weakest_prespec:
  "(P ; Q) \<Rightarrow>p S = P \<Rightarrow>p (Q wp S)"
  apply (simp add:WeakPrecondP_def)
oops

end