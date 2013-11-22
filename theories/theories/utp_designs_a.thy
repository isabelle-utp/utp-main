theory utp_designs_a
imports utp_designs
begin

lift_definition DesignA :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE" (infixr "\<turnstile>\<^sub>\<alpha>" 60)
is "\<lambda> P Q. (\<alpha> P \<union>\<^sub>f \<alpha> Q \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, (\<pi> P) \<turnstile> (\<pi> Q))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest)
done

lemma REL_ALPHABET_in_alpha [closure]: "in\<^sub>\<alpha>a \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def var_defs)


lemma REL_ALPHABET_out_alpha [closure]: "out\<^sub>\<alpha>a \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def var_defs)


lemma DesignA_alphabet [alphabet]:
  "\<alpha> (P \<turnstile>\<^sub>\<alpha> Q) = \<alpha> P \<union>\<^sub>f \<alpha> Q \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:DesignA.rep_eq pred_alphabet_def)

lemma DesignA_evala [evala]:
  "\<lbrakk>P \<turnstile>\<^sub>\<alpha> Q\<rbrakk>\<pi> = \<lbrakk>P\<rbrakk>\<pi> \<turnstile> \<lbrakk>Q\<rbrakk>\<pi>"
  by (simp add:EvalA_def DesignA.rep_eq)

lemma DesignA_rel_closure [closure]:
  "\<lbrakk> P \<in> WF_ALPHA_REL; Q \<in> WF_ALPHA_REL \<rbrakk> \<Longrightarrow> P \<turnstile>\<^sub>\<alpha> Q \<in> WF_ALPHA_REL"
  apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def alphabet)
  apply (simp add:closure)
done

lemma WF_ALPHA_REL_EvalA_WF_RELATION [closure]:
  "P \<in> WF_ALPHA_REL \<Longrightarrow> \<lbrakk>P\<rbrakk>\<pi> \<in> WF_RELATION"
  apply (simp add:WF_ALPHA_REL_def WF_RELATION_def REL_ALPHABET_def)
  apply (rule UNREST_subset)
  apply (rule unrest) back back back
  apply (auto)
done

lemma UNREST_OKAY_alpha [unrest]: "\<lbrakk> okay\<down> \<notin>\<^sub>f \<alpha> P; okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P \<rbrakk> \<Longrightarrow> OKAY \<sharp> \<lbrakk>P\<rbrakk>\<pi>"
  apply (rule UNREST_subset)
  apply (rule EvalA_UNREST)
  apply (auto)
done

theorem DesignA_composition:
  assumes 
  "P1 \<in> WF_ALPHA_REL" "P2 \<in> WF_ALPHA_REL"
  "Q1 \<in> WF_ALPHA_REL" "Q2 \<in> WF_ALPHA_REL"
  "okay\<down> \<notin>\<^sub>f \<alpha> P1" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P1"
  "okay\<down> \<notin>\<^sub>f \<alpha> P2" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P2"
  "okay\<down> \<notin>\<^sub>f \<alpha> Q1" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q1"
  "okay\<down> \<notin>\<^sub>f \<alpha> Q2" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q2"
  shows "(P1 \<turnstile>\<^sub>\<alpha> Q1) ;\<^sub>\<alpha> (P2 \<turnstile>\<^sub>\<alpha> Q2) = ((\<not>\<^sub>\<alpha> ((\<not>\<^sub>\<alpha> P1) ;\<^sub>\<alpha> true\<^bsub>in\<^sub>\<alpha> (\<alpha> P1)\<^esub>)) \<and>\<^sub>\<alpha> \<not>\<^sub>\<alpha> (Q1 ;\<^sub>\<alpha> (\<not>\<^sub>\<alpha> P2))) \<turnstile>\<^sub>\<alpha> (Q1 ;\<^sub>\<alpha> Q2)"
  using assms
  apply (utp_alpha_tac)
  apply (rule conjI)
  apply (simp add:alphabet_dist closure)
  defer
  apply (subst DesignD_composition)
  apply (simp_all add:closure unrest)
  apply (auto)[1]
done

end