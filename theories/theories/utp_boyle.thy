header {* UTP Theory for Boyle's Law *}

theory utp_boyle
imports utp_base
begin

text {* Observational Variables *}

default_sort REAL_SORT

abbreviation "k \<equiv> MkRealV ''k'' True"

abbreviation "p \<equiv> MkRealV ''p'' True"

abbreviation "V \<equiv> MkRealV ''V'' True"

text {* Signature *}

definition Init :: "real \<Rightarrow> real \<Rightarrow> 'a WF_PREDICATE" where
"Init ki Vi = `($k = \<guillemotleft>ki\<guillemotright>) \<and> ($k\<acute> = \<guillemotleft>ki\<guillemotright>) 
            \<and> ($V = \<guillemotleft>Vi\<guillemotright>) \<and> ($V\<acute> = \<guillemotleft>Vi\<guillemotright>)
            \<and> ($p = \<guillemotleft>ki / Vi\<guillemotright> \<and> $p\<acute> = \<guillemotleft>ki / Vi\<guillemotright>)`"

definition ChangePressure :: "real \<Rightarrow> 'a WF_PREDICATE" where
"ChangePressure dp = `p := $p + \<guillemotleft>dp\<guillemotright> ; V := (($k * $V) / ($k + ($V * \<guillemotleft>dp\<guillemotright>)))`"

definition ChangeVolume :: "real \<Rightarrow> 'a WF_PREDICATE" where
"ChangeVolume dV = `V := $V + \<guillemotleft>dV\<guillemotright> ; p := (($k * $p) / ($k + ($p * \<guillemotleft>dV\<guillemotright>)))`"

declare Init_def [eval,evalr,evalpp]
declare ChangePressure_def [eval,evalr,evalpp]
declare ChangeVolume_def [eval,evalr,evalpp]

text {* Healthiness condition *}

definition "BH1(\<phi>) = `(\<exists> k. \<phi>) \<and> ($k = $p * $V)`"

definition "BH2(\<phi>) = `(\<exists> k\<acute>. \<phi>) \<and> ($k\<acute> = $p\<acute> * $V\<acute>)`"

definition "BH3(\<phi>) = `\<phi> \<and> $k\<acute> = $k`"

declare BH1_def [eval,evalr,evalpp]
declare BH2_def [eval,evalr,evalpp]
declare BH3_def [eval,evalr,evalpp]

lemma BH1_idem: "BH1(BH1(\<phi>)) = BH1(\<phi>)"
proof -
  have "BH1(BH1(\<phi>)) = `(\<exists> k. BH1(\<phi>)) \<and> ($k = $p * $V)`"
    by (simp add:BH1_def)

  also have "... = `(\<exists> k. ((\<exists> k. \<phi>) \<and> ($k = $p * $V))) \<and> ($k = $p * $V)`"
    by (simp add:BH1_def)

  also have "... = `(\<exists> k. \<phi>) \<and> ($k = $p * $V)`"
    by (utp_poly_tac)

  also have "... = BH1(\<phi>)"
    by (simp add:BH1_def)

  finally show ?thesis ..
qed

lemma BH1_idem_alt: "BH1(BH1(\<phi>)) = BH1(\<phi>)"
  by (utp_poly_auto_tac)

lemma BH2_idem: "BH2(BH2(\<phi>)) = BH2(\<phi>)"
  by (utp_poly_auto_tac)

lemma BH3_idem: "BH3(BH3(\<phi>)) = BH3(\<phi>)"
  by (utp_poly_auto_tac)

lemma Init_BH1:
  "Vi > 0 \<Longrightarrow> (Init ki Vi) is BH1"
  by (utp_poly_auto_tac)

text {* Observations *}

lemma BH1_example_1:
  "`($p = \<guillemotleft>10\<guillemotright>) \<and> ($V = \<guillemotleft>5\<guillemotright>) \<and> ($k = \<guillemotleft>50\<guillemotright>)` is BH1"
  by (utp_poly_auto_tac)

lemma BH1_example_2:
  "`($p = \<guillemotleft>7\<guillemotright>) \<and> ($V = \<guillemotleft>3\<guillemotright>) \<and> ($k = \<guillemotleft>21\<guillemotright>)` is BH1"
  by (utp_poly_auto_tac)

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
