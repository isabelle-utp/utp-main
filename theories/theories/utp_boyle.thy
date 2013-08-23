theory utp_boyle
imports utp_base
begin

abbreviation "k \<equiv> MkPlainP ''k'' True TYPE(real) TYPE('m :: REAL_SORT)"
abbreviation "p \<equiv> MkPlainP ''p'' True TYPE(real) TYPE('m :: REAL_SORT)"
abbreviation "V \<equiv> MkPlainP ''V'' True TYPE(real) TYPE('m :: REAL_SORT)"

definition "BH(\<phi>) = `(\<exists> k. \<phi>) \<and> ($k = $p * $V)`"

declare BH_def [eval]

lemma BH_idem: "BH(BH(\<phi>)) = BH(\<phi>)"
  apply (simp add:BH_def)
  apply (utp_pred_auto_tac)
done

lemma BH_example_1:
  "`($p = \<guillemotleft>10\<guillemotright>) \<and> ($V = \<guillemotleft>5\<guillemotright>) \<and> ($k = \<guillemotleft>50\<guillemotright>)` is BH"
  by (utp_pred_auto_tac)

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
  
end