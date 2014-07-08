header {* UTP Theory for Boyle's Law *}

theory utp_boyle
imports "utp_theory" utp_context
begin

text {* Observational Variables *}

default_sort REAL_SORT

abbreviation "k \<equiv> MkRealV ''k'' True"

abbreviation "p \<equiv> MkRealV ''p'' True"

abbreviation "V \<equiv> MkRealV ''V'' True"

text {* Healthiness condition *}

definition "BH1(\<phi>) = ``(\<exists> k. \<phi>) \<and> ($k = $p * $V)``"

definition "BH2(\<phi>) = ``(\<exists> k\<acute>. \<phi>) \<and> ($k\<acute> = $p\<acute> * $V\<acute>)``"

definition "BH3(\<phi>) = ``\<phi> \<and> $k\<acute> = $k``"

declare BH1_def [evala]
declare BH2_def [evala]
declare BH3_def [evala]

lemma BH1_idem: "BH1(BH1(\<phi>)) = BH1(\<phi>)"
proof -
  have "BH1(BH1(\<phi>)) = ``(\<exists> k. BH1(\<phi>)) \<and> ($k = $p * $V)``"
    by (simp add:BH1_def)

  also have "... = ``(\<exists> k. ((\<exists> k. \<phi>) \<and> ($k = $p * $V))) \<and> ($k = $p * $V)``"
    by (simp add:BH1_def)

  also have "... = ``(\<exists> k. \<phi>) \<and> ($k = $p * $V)``"
    by (utp_alpha_tac, utp_poly_auto_tac)

  also have "... = BH1(\<phi>)"
    by (simp add:BH1_def)

  finally show ?thesis ..
qed

lemma BH1_idem_alt: "BH1(BH1(\<phi>)) = BH1(\<phi>)"
  by (utp_alpha_tac, utp_poly_auto_tac)

lemma BH2_idem: "BH2(BH2(\<phi>)) = BH2(\<phi>)"
  by (utp_alpha_tac, utp_poly_auto_tac)

lemma BH3_idem: "BH3(BH3(\<phi>)) = BH3(\<phi>)"
  by (utp_alpha_tac, utp_poly_auto_tac)

theorem BH1_BH2_comm: "BH1(BH2(P)) = BH2(BH1(P))"
  apply (utp_alpha_tac)
  apply (utp_poly_auto_tac)
  apply (metis PVAR_VAR_inj binding_upd_ty_twist)+
done

definition "BOYLE = \<lparr> alphas = {\<lbrace>k\<down>,k\<down>\<acute>,p\<down>,p\<down>\<acute>,V\<down>,V\<down>\<acute>\<rbrace>}, health = BH1 \<circ> BH2 \<rparr>"

interpretation boyle_thy: UTP_THEORY BOYLE
  apply (unfold_locales)
  apply (simp add:BOYLE_def IDEMPOTENT_OVER_def)
  apply (metis BH1_BH2_comm BH1_idem_alt BH2_idem)
done

locale BOYLE_CTX = UTP_THY_CTX  +
  assumes BOYLE_thy [simp]: "\<T> = BOYLE"
begin

text {* Signature *}

definition Init :: "real \<Rightarrow> real \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"Init ki Vi = ``($k = \<guillemotleft>ki\<guillemotright>) \<and> ($k\<acute> = \<guillemotleft>ki\<guillemotright>) 
            \<and> ($V = \<guillemotleft>Vi\<guillemotright>) \<and> ($V\<acute> = \<guillemotleft>Vi\<guillemotright>)
            \<and> ($p = \<guillemotleft>ki / Vi\<guillemotright> \<and> $p\<acute> = \<guillemotleft>ki / Vi\<guillemotright>)``"

definition ChangePressure :: "real \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"ChangePressure dp = ``p := $p + \<guillemotleft>dp\<guillemotright> ; V := (($k * $V) / ($k + ($V * \<guillemotleft>dp\<guillemotright>)))``"

definition ChangeVolume :: "real \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"ChangeVolume dV = ``V := $V + \<guillemotleft>dV\<guillemotright> ; p := (($k * $p) / ($k + ($p * \<guillemotleft>dV\<guillemotright>)))``"

declare Init_def [evala]
declare ChangePressure_def [evala]
declare ChangeVolume_def [evala]

lemma Init_BH1:
  "Vi > 0 \<Longrightarrow> (Init ki Vi) is BH1"
  by (utp_alpha_tac, utp_poly_auto_tac)

text {* Observations *}

lemma BH1_example_1:
  "``($p = \<guillemotleft>10\<guillemotright>) \<and> ($V = \<guillemotleft>5\<guillemotright>) \<and> ($k = \<guillemotleft>50\<guillemotright>)`` is BH1"
  by (utp_alpha_tac, utp_poly_auto_tac)

lemma BH1_example_2:
  "``($p = \<guillemotleft>7\<guillemotright>) \<and> ($V = \<guillemotleft>3\<guillemotright>) \<and> ($k = \<guillemotleft>21\<guillemotright>)`` is BH1"
  by (utp_alpha_tac, utp_poly_auto_tac)

(*
lemma BH_1_counterexample_1:
  "`($p = \<guillemotleft>9\<guillemotright>) \<and> ($V = \<guillemotleft>2\<guillemotright>) \<and> ($k = \<guillemotleft>18\<guillemotright>)` is BH1"
  by (utp_poly_auto_tac)
*)

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

end
