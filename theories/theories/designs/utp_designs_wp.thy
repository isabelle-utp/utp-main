(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs_wp.thy                                                   *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Designs WP calculus *}

theory utp_designs_wp
imports utp_designs_hoare
begin

definition WeakPrecondD :: 
  "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infixr "wp\<^sub>D" 150) where
"Q wp\<^sub>D r = `\<not> Q\<^bsup>tf\<^esup> \<and> Q\<^bsup>tt\<^esup> wp r`"

lemma ImpliesP_wp:
  assumes "`r` \<noteq> `true`" "p \<in> COND" "r \<in> COND"
  shows "`(p \<Rightarrow> q) wp r` = `p \<and> q wp r`"
proof -
  from assms have "`(\<not> p) wp r` = `p`"
    apply (simp add: WeakPrecondP_def)
    apply (subst SemiR_TrueP_precond[of "`\<not> p`", THEN sym])
    apply (simp add:closure assms)
    apply (subst SemiR_assoc[THEN sym])
    apply (subst SemiR_precond_left_zero)
    apply (simp add:closure assms)
    apply (metis NotP_not_false(1) assms(1))
    apply (metis SemiR_condition_comp assms(2))
  done

  thus ?thesis
    by (simp add:OrP_wp ImpliesP_def)
qed

theorem WeakPrecondD_form:
  assumes
    "OKAY \<sharp> p" "OKAY \<sharp> Q" 
    "r \<noteq> `true`" "p \<in> COND" "r \<in> COND"
  shows "(p \<turnstile> Q) wp\<^sub>D r = `p \<and> Q wp r`"
  using assms
  apply (subst WeakPrecondD_def)
  apply (subst DesignD_assumption_alt)
  apply (simp add:unrest)
  apply (subst DesignD_commitment_alt)
  apply (simp_all add: ImpliesP_wp closure assms)
  apply (utp_poly_auto_tac)
done

end

