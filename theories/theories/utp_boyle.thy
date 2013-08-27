header {* UTP Theory for Boyle's Law *}

theory utp_boyle
imports utp_base
begin

text {* Observational Variables *}

default_sort REAL_SORT

abbreviation "k \<equiv> MkRealV ''k'' True"

abbreviation "p \<equiv> MkRealV ''p'' True"

abbreviation "V \<equiv> MkRealV ''V'' True"

text {* Healthiness condition *}

definition "BH(\<phi>) = `(\<exists> k. \<phi>) \<and> ($k = $p * $V)`"

declare BH_def [eval]

lemma BH_idem: "BH(BH(\<phi>)) = BH(\<phi>)"
proof -
  have "BH(BH(\<phi>)) = `(\<exists> k. BH(\<phi>)) \<and> ($k = $p * $V)`"
    by (simp add:BH_def)

  also have "... = `(\<exists> k. ((\<exists> k. \<phi>) \<and> ($k = $p * $V))) \<and> ($k = $p * $V)`"
    by (simp add:BH_def)

  also have "... = `(\<exists> k. \<phi>) \<and> ($k = $p * $V)`"
    by (utp_pred_auto_tac)

  also have "... = BH(\<phi>)"
    by (simp add:BH_def)

  finally show ?thesis ..
qed

lemma BH_idem_alt: "BH(BH(\<phi>)) = BH(\<phi>)"
  by (utp_pred_auto_tac)

lift_definition BOYLE :: "'a WF_THEORY" 
is "({vs. {k\<down>, p\<down>, V\<down>} \<subseteq> vs}, {BH})"
  apply (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def)
  apply (simp add:BH_idem)
done

abbreviation "WF_BOYLE \<equiv> THEORY_PRED BOYLE"

text {* Observations *}

lemma BH_example_1:
  "`($p = \<guillemotleft>10\<guillemotright>) \<and> ($V = \<guillemotleft>5\<guillemotright>) \<and> ($k = \<guillemotleft>50\<guillemotright>)` is BH"
  by (utp_pred_auto_tac)

lemma BH_example_2:
  "`($p = \<guillemotleft>7\<guillemotright>) \<and> ($V = \<guillemotleft>3\<guillemotright>) \<and> ($k = \<guillemotleft>21\<guillemotright>)` is BH"
  by (utp_pred_auto_tac)

end

(*
lemma DestReal_binding: 
  "vtype x = RealType \<Longrightarrow>
   DestReal (\<langle>b(x :=\<^sub>b MkReal n)\<rangle>\<^sub>b x) = n"
  by (metis MkReal_type REAL_SORT_class.Defined REAL_SORT_class.Inverse binding_upd_apply var_compat_intros(1))
  
lemma BH_example_2:
  "BH(`($p = \<guillemotleft>10\<guillemotright>) \<and> ($V = \<guillemotleft>5\<guillemotright>) \<and> ($k = \<guillemotleft>100\<guillemotright>)`) = 
      `($p = \<guillemotleft>10\<guillemotright>) \<and> ($V = \<guillemotleft>5\<guillemotright>) \<and> ($k = \<guillemotleft>50\<guillemotright>)`"
  apply (utp_pred_auto_tac)
  apply (rule)
  apply (rule DestReal_binding)
  apply (metis PVAR_VAR_vtype TypeU_real)
done
*)  
