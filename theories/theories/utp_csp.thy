(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp
imports 
  utp_reactive
begin

lemma tr_prefix_as_a: 
  "`\<langle>a\<rangle> = ($tr \<acute>-$tr) \<and> ($tr \<le> $tr \<acute>)` = `$tr^\<langle>a\<rangle> = $tr \<acute>`"
apply(utp_poly_auto_tac)
apply (metis prefixeq_drop)
apply (metis append_eq_conv_conj)
apply (metis prefixeqI)
done

lemma a_notin_ref_closure[closure]:
  assumes "NON_REL_VAR \<sharp> a"
  shows "`a \<notin> $ref\<acute>` \<in> WF_RELATION"
apply(simp add:WF_RELATION_def)
apply(simp add:closure unrest assms typing defined)
done

lemma tr_prefix_a_closure[closure]:
  assumes "NON_REL_VAR \<sharp> a"
  shows "`$tr^\<langle>a\<rangle> = $tr\<acute>` \<in> WF_RELATION"
apply(simp add:WF_RELATION_def)
apply(simp add:closure unrest assms typing defined)
done

definition CSP1 :: "'a upred \<Rightarrow> 'a upred" where
"CSP1 P = `P \<or> (\<not> $ok \<and> ($tr \<le> $tr\<acute>))`"

abbreviation "CSP2 \<equiv> H2"

definition R3c :: "'a upred \<Rightarrow> 'a upred" where
"R3c P = `CSP1(II) \<lhd> $wait \<rhd> P`"

definition RHc :: "'a upred \<Rightarrow> 'a upred" where
"RHc P = (R1 \<circ> R2 \<circ> R3c) P"

definition CSP :: "'a upred \<Rightarrow> 'a upred" where
"CSP P = (CSP1 \<circ> CSP2 \<circ> RHc) P"

definition StopCSP :: "'a upred" ("STOP") where
"STOP = `CSP1( $ok\<acute> \<and> R3c($tr\<acute> = $tr \<and> $wait\<acute>))`"

definition PrefixSkipCSP :: "('m EVENT, 'm) pexpr \<Rightarrow> 'm upred" ("@_") where
"@a = `CSP1($ok\<acute> \<and> R3c((a \<notin> $ref\<acute> \<and> $tr\<acute>=$tr)\<lhd> $wait\<acute> \<rhd> ($tr^\<langle>a\<rangle> =$tr\<acute>)))`"

definition SkipCSP :: "'a upred" ("SKIP") where 
"SKIP = `RHc(\<exists> ref . CSP1(II))`"

syntax
  "_upred_StopCSP" :: "n_upred" ("STOP")
  "_upred_PrefixSkipCSP" :: "n_pexpr \<Rightarrow> n_upred" ("@_")
  "_upred_SkipCSP" :: "n_upred" ("SKIP")
  
translations
  "_upred_StopCSP" == "CONST StopCSP"
  "_upred_PrefixSkipCSP a" == "CONST PrefixSkipCSP a"
  "_upred_SkipCSP" == "CONST SkipCSP"

definition ChaosCSP :: "'a upred" ("CHAOS") where
"CHAOS = `CSP(true)`"

definition PrefixCSP :: 
  "('a EVENT, 'a) pexpr \<Rightarrow> 'a upred \<Rightarrow> 'a upred" ("_\<rightarrow>_") where
"a\<rightarrow>P = `@a ; P`"

definition InputCSP :: "'b::type CHAN \<Rightarrow> ('b \<Rightarrow> 'a upred) \<Rightarrow> 'a upred" where
"InputCSP n P = ExistsShP (\<lambda> v. PrefixCSP (LitPE (PEV n v)) (P v))"

definition OutputCSP :: 
  "'b::type CHAN \<Rightarrow> ('b, 'a) pexpr \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"OutputCSP n v P = PrefixCSP (EventPE n v) P"

definition ExternalChoiceCSP :: 
  "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" (infixl "\<box>" 65) where
"P \<box> Q = `CSP2((P \<and> Q)\<lhd> STOP \<rhd>(P \<or> Q))`"

definition MergeCSP :: 
  "('a EVENT USET, 'a) pexpr \<Rightarrow> 
   ('a uvar set * 'a upred)" where
  "MergeCSP A = ( { wait\<down>, ref\<down>, tr\<down>}
              , `R1(
                  (\<not>$ok \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>A \<^esub>($tr\<^bsub>1 \<^esub>- $tr))) \<or>
                  ($ok \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)) \<and> 
                 (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>A \<^esub>($tr\<^bsub>1 \<^esub>- $tr))
                 \<and> (($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)\<lhd> $wait\<acute> \<rhd>(\<not>$wait\<^bsub>0\<^esub>\<and>\<not>$wait\<^bsub>1\<^esub>) )
                 \<and> $ok\<acute>)
                 ) ; SKIP`)"

definition HideCSP ::
  "'m upred \<Rightarrow>
   ('m EVENT USET, 'm) pexpr \<Rightarrow>
   'm upred" where
"HideCSP P A = `RHc(\<exists> tr\<acute>\<acute>. P[$tr\<acute>\<acute>/tr\<acute>][($ref\<acute> \<union> A)/ref\<acute>] 
                   \<and> $tr\<acute> = $tr ^ (($tr\<acute>\<acute> - $tr)\<upharpoonright>A)) ; SKIP`"

definition GuardCSP ::
  "'a upred \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" where
"GuardCSP g P = P \<lhd> g \<rhd> STOP"

definition ParallelCSP :: 
  "'a upred \<Rightarrow> 
   ('a EVENT USET, 'a) pexpr \<Rightarrow> 
   'a upred \<Rightarrow> 
   'a upred" (infix "\<parallel>\<^bsub>CSP'(_')\<^esub>" 100) where
"P \<parallel>\<^bsub>CSP(A)\<^esub> Q = P \<parallel>\<^bsub>MergeCSP A\<^esub> Q"

definition InterleaveCSP 
  :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" (infix "|||\<^bsub>CSP\<^esub>" 100) where
"P |||\<^bsub>CSP\<^esub> Q = ParallelCSP P |{}| Q"

syntax
  "_upred_ChaosCSP" :: "n_upred" ("CHAOS")
  "_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ -> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_?_ -> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_!_ -> _")
  "_upred_extchoice" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "[]" 65)
  "_upred_guardcsp"  :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("[_] & _" [0, 100] 100)
  "_upred_parallel"  :: "n_upred \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "||\<^bsub>_\<^esub>" 100)

syntax (xsymbols)
  "_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ \<rightarrow> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_?_ \<rightarrow> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_!_ \<rightarrow> _")
  "_upred_extchoice" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "\<box>" 65)
  "_upred_parallel"  :: "n_upred \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<parallel>\<^bsub>_\<^esub>" 100)
  "_upred_interleave" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infix "|||" 100)

translations
  "_upred_ChaosCSP" == "CONST ChaosCSP"
  "_upred_prefixed a P"   == "CONST PrefixCSP a P"
  "_upred_input n v p"    == "CONST InputCSP n (\<lambda> v. p)"
  "_upred_output n v p"   == "CONST OutputCSP n v p"
  "_upred_extchoice P Q"  == "CONST ExternalChoiceCSP P Q"
  "_upred_guardcsp b P"   == "CONST GuardCSP b P"
  "_upred_parallel P A Q" == "CONST ParallelCSP P A Q"
  "_upred_interleave P Q" == "CONST InterleaveCSP P Q"

definition CSP_Pre
  :: "'a upred \<Rightarrow> 'a upred " where
"CSP_Pre P = `\<not>P\<^sup>f[true/ok]\<^sub>f`"

definition CSP_Post
  :: "'a upred \<Rightarrow> 'a upred " where
"CSP_Post P = `P\<^sup>t[true/ok]\<^sub>f`"


declare R3c_def [eval, evalr, evalrr, evalrx, evalp]
declare RHc_def [eval, evalr, evalrr, evalrx, evalp]
declare CSP1_def [eval, evalr, evalrr, evalrx, evalp]
declare CSP_def [eval, evalr, evalrr, evalrx, evalp]
declare StopCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare PrefixSkipCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare SkipCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ChaosCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare PrefixCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ExternalChoiceCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare MergeCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ParallelCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare InterleaveCSP_def [eval, evalr, evalrr, evalrx, evalp]

lemma CSP1_rel_closure[closure]:
  "P \<in> WF_RELATION \<Longrightarrow> CSP1(P) \<in> WF_RELATION"
by (metis CSP1_def DesignD_extreme_point_nok(2) OrP_rel_closure R1_def R1_rel_closure TopD_rel_closure)

lemma CSP2_rel_closure[closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> CSP2(P) \<in> WF_RELATION"
by (metis H2_def J_closure SemiR_closure)

lemma R3c_rel_closure[closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> R3c(P) \<in> WF_RELATION"
by (simp add:R3c_def closure)

subsection {* CSP1 laws *}

lemma CSP1_idempotent: "`CSP1(CSP1(P))` = `CSP1(P)`" 
  by (utp_pred_auto_tac)

lemma CSP1_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> CSP1(P) \<sqsubseteq> CSP1(Q)"
  by (utp_pred_tac)

lemma CSP1_R1_commute: "CSP1 (R1 P) = R1 (CSP1 (P))"by utp_pred_auto_tac
lemma CSP1_R2_commute: "CSP1 (R2 P) = R2 (CSP1 (P))"by(simp add:CSP1_def R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
lemma CSP1_R3c_commute: "CSP1 (R3c P) = R3c (CSP1 (P))"by(simp add:CSP1_def R3c_def, utp_poly_auto_tac)


lemma R1_R3c_commute: "`R1(R3c(P))` =`R3c(R1(P))`"
  apply(simp add:R3c_def SkipR_as_SkipRA)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing) back
  apply(simp add:R1_CondR CSP1_R1_commute[THEN sym] R1_extend_AndP[THEN sym])
  apply(simp add:R1_def tr_eq_is_R1)
done

lemma R2_R3c_commute: "`R2(R3c(P))` =`R3c(R2(P))`"
  apply(simp add:R3c_def SkipR_as_SkipRA)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing) back
  apply(simp add:R2_CondR CSP1_R2_commute[THEN sym])
  apply(simp add: R2_def R2s_AndP R1_extend_AndP[THEN sym])
  apply(simp add:R2s_def usubst typing closure defined R1_def tr_prefix_as_nil)
  done

lemma R3c_idempotent: "`R3c(R3c(P))`=`R3c(P)`"
  by(utp_poly_auto_tac)

lemma R3c_AndP: 
  "`R3c(P \<and> Q)` = `R3c(P) \<and> R3c(Q)`"
  by utp_pred_auto_tac

lemma R3c_OrP: 
  "`R3c(P \<or> Q)` = `R3c(P) \<or> R3c(Q)`"
  by utp_pred_auto_tac

lemma R3c_CondR: 
  "`R3c(P \<lhd> b \<rhd> Q)` = `R3c(P) \<lhd> b \<rhd> R3c(Q)`"
  by utp_pred_auto_tac

lemma CSP1_AndP: 
  "`CSP1(P \<and> Q)` = `CSP1(P) \<and> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_OrP: 
  "`CSP1(P \<or> Q)` = `CSP1(P) \<or> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_CondR: 
  "`CSP1(P \<lhd> b \<rhd> Q)` = `CSP1(P) \<lhd> b \<rhd> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_Extend_OrP: 
  "`CSP1(P) \<or> Q` = `CSP1(P \<or> Q)`"
  by utp_pred_auto_tac

lemma CSP1_R1_compose: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1($ok \<and> P)`"
proof -
  have "CSP1(P) = CSP1 (R1 P)" 
    by (metis Healthy_simp assms)
  thus ?thesis 
    by(utp_pred_auto_tac)
qed

lemma ok_AndP:
  "`$ok \<and> P` = `$ok \<and> P[true/ok]`"
apply(subst PVarPE_PSubstPE)
apply(simp_all add:typing closure)
done

lemma CSP1_R1_form: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1($ok \<and> P[true/ok])`"
by (metis CSP1_R1_compose assms ok_AndP)

lemma CSP1_R1_form_2: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1($ok \<and> P)`"
by (metis CSP1_R1_compose assms)


lemma R3c_form : "`R3c(P)` = `(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P \<^sub>f)`"
  apply (simp add:R3c_def)
  apply (utp_poly_auto_tac)
  apply (simp add:eval)
  apply (drule_tac x="tr\<down>" in bspec, simp add:closure)
  apply (simp add:Rep_binding_ty_def)
  apply (simp add:eval)
  apply (drule_tac x="tr\<down>" in bspec, simp add:closure)
  apply (simp add:Rep_binding_ty_def)
done

lemma R3c_form_2 : "`R3c(P)` = `(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P)`"
  apply (simp add:R3c_def)
  apply (subst CSP1_R1_form_2)
  apply (metis Healthy_intro R1_SkipR)
  apply (utp_poly_auto_tac)
done

lemma CSP1_R1_R3c_compose: 
  assumes "P is R1"
  shows "R3c(CSP1(P)) = `(\<not>$ok \<and> ($tr\<le>$tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> P[true/ok][false/wait])`"
  apply (subst CSP1_R1_form)
  apply (metis assms)
  apply (simp add:R3c_form CSP1_def)
  apply (utp_poly_auto_tac)
done

lemma CSP1_R1_R3c_compose_2: 
  assumes "P is R1"
  shows "R3c(CSP1(P)) = `(\<not>$ok \<and> ($tr\<le>$tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> P)`"
  apply (subst CSP1_R1_form_2)
  apply (metis assms)
  apply (simp add:R3c_form_2 CSP1_def)
  apply (utp_pred_auto_tac)
done

lemma CSP1_R3_ok': 
"`CSP1($ok\<acute> \<and> R3c(P))` = `CSP1(R3c($ok\<acute> \<and> P))`"
  apply (simp add:R3c_form CSP1_def SkipR_as_SkipRA)
  apply (subst SkipRA_unfold[of "ok\<down>"])
  apply (simp_all add:closure)
  apply (subst SkipRA_unfold[of "ok\<down>"]) back
  apply (simp_all add:closure)
  apply (utp_poly_auto_tac)
  apply (simp_all add:eval Rep_binding_ty_def)
done

subsection {* CSP2 laws *}

lemma CSP2_idempotent: "`CSP2(CSP2(P))` = `CSP2(P)`"
  by (metis H2_idempotent)

lemma CSP2_monotonic:
  "P \<sqsubseteq> Q \<Longrightarrow> CSP2(P) \<sqsubseteq> CSP2(Q)"
  by (metis H2_monotone)

lemma CSP1_CSP2_commute:
   "CSP1 (CSP2 P) = CSP2 (CSP1 P)" 
proof -
  have "(`(\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; J` :: 'a upred)
        = `(\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; (II\<^bsub>REL_VAR - OKAY\<^esub> \<or> ($ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>))`"
    apply (subst SemiR_extract_variable_id[of "ok\<down>"])
    apply (simp_all add:closure typing defined unrest usubst JA_pred_def)
    apply (subst BoolType_aux_var_split_exists, simp_all)
    apply (simp add:usubst typing closure UNREST_EXPR_TrueE UNREST_EXPR_FalseE)
    apply (simp add:usubst typing defined closure SubstP_VarP_single_UNREST unrest)
    apply (subst SemiR_OrP_distl[THEN sym])
    apply (simp)
  done

  also have "... = `(\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; II\<^bsub>REL_VAR - OKAY\<^esub>`"
    by (smt AndP_comm OrP_AndP_absorb)

  also have "... = `(\<not> $ok \<and> ($tr \<le> $tr\<acute>))`"
    by (simp add:SemiR_SkipRA_right closure var_dist unrest)

  finally show ?thesis
    by (simp add: H2_def CSP1_def SemiR_OrP_distr)
qed

lemma CSP2_R1_commute: 
   "CSP2 (R1 P) = R1 (CSP2 (P))"
apply(simp add:H2_split R1_def usubst typing defined closure)
apply(utp_pred_auto_tac)
done


lemma R1_ok'_true: 
  "(R1(P))\<^sup>t = R1(P\<^sup>t)"
by(simp add:R1_def, utp_poly_auto_tac)

lemma R1_ok_true: 
  "`(R1(P))[true/ok]` = `R1(P[true/ok])`"
by(simp add:R1_def, utp_poly_auto_tac)

lemma R1_ok'_false: 
  "(R1(P))\<^sup>f = R1(P\<^sup>f)"
by(simp add:R1_def, utp_poly_auto_tac)

lemma R2_ok'_true: "(R2(P))\<^sup>t = R2(P\<^sup>t)"
proof -
  have "(R2(P))\<^sup>t = R1((R2s(P))\<^sup>t)"
    by (metis R2_def PVAR_VAR_pvdash R1_ok'_true)
  also have "... = R2(P\<^sup>t)"
    apply(simp add:R2_def R2s_def)
    apply (subst SubstP_twice_3) back
    apply (simp_all add:unrest typing)
    apply (simp add:usubst typing defined closure)
    apply (subst SubstP_twice_3) back back
    apply (simp_all add:unrest typing defined closure)
    apply (simp add:usubst typing defined closure)
    done
  finally show ?thesis ..
qed

lemma R2_ok'_false: "(R2(P))\<^sup>f = R2(P\<^sup>f)"
proof -
  have "(R2(P))\<^sup>f = R1((R2s(P))\<^sup>f)"
    by (metis R2_def PVAR_VAR_pvdash R1_ok'_false)
  also have "... = R2(P\<^sup>f)"
    apply(simp add:R2_def R2s_def)
    apply (subst SubstP_twice_3) back
    apply (simp_all add:unrest typing)
    apply (simp add:usubst typing defined closure)
    apply (subst SubstP_twice_3) back back
    apply (simp_all add:unrest typing defined closure)
    apply (simp add:usubst typing defined closure)
    done
  finally show ?thesis ..
qed

lemma R2_ok_true: "`(R2(P))[true /ok]` =` R2(P[true/ok])`"
proof -
  have "`(R2(P))[true/ok]` = `R1((R2s(P))[true/ok])`"
    by (metis R2_def PVAR_VAR_pvdash R1_ok_true)
  also have "... =`R2(P[true/ok])`"
    apply(simp add:R2_def R2s_def)
    apply (subst SubstP_twice_3) back
    apply (simp_all add:unrest typing)
    apply (simp add:usubst typing defined closure)
    apply (subst SubstP_twice_3) back back
    apply (simp_all add:unrest typing defined closure)
    apply (simp add:usubst typing defined closure)
    done
  finally show ?thesis ..
qed

lemma CSP2_R2_commute:
  "CSP2 (R2 P) = R2 (CSP2 (P))"
apply(simp add:H2_split R2_OrP)
apply(subst R2_def) back back back
apply(simp add:R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2_def[THEN sym])
apply(simp add:R2s_def usubst typing defined closure)
apply (metis (hide_lams, no_types) PVAR_VAR_pvdash R2_ok'_false R2_ok'_true)
done

lemma CSP1_SkipR: "`CSP1(II)` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"
apply(subst CSP1_R1_form)
defer 
apply(simp add:SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:closure typing)
apply(simp add:usubst typing defined closure CSP1_def)
apply(utp_poly_auto_tac)
done

lemma CSP2_R3c_commute: 
  "CSP2 (R3c P) = R3c (CSP2 (P))"
apply(simp add:R3c_def H2_CondR assms closure)
apply(simp add:H2_split usubst typing closure defined CSP1_SkipR)
apply(utp_pred_auto_tac)
done

subsection {* CSP laws *}
  
lemma CSP_form: 
assumes "P is CSP" 
shows "P = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P))) \<or> ($ok \<and> \<not>$wait \<and>  $ok\<acute> \<and> R2(CSP_Post(P)))`"
proof-
  have "P = CSP P" 
    by(metis assms(1) is_healthy_def)
  also have "... = `R3c(CSP1(R1(CSP2(R2(P)))))`"
    by(simp add:CSP_def RHc_def R2_R3c_commute CSP2_R1_commute assms closure CSP2_R3c_commute R1_R3c_commute CSP1_R3c_commute) 
   also have "...  = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> R2s(P)\<^sup>f[true/ok]\<^sub>f) \<or> ($ok \<and> \<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> $ok\<acute> \<and> R2s(P)\<^sup>t[true/ok]\<^sub>f)`" 
    apply(subst CSP1_R1_R3c_compose)
    apply (metis Healthy_intro R1_idempotent)
    apply(subst H2_split)
    apply(simp add:R1_def usubst typing defined closure R2_def)
    apply(utp_pred_auto_tac)
    done
  also have "... =  `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and>  R2(P)\<^sup>f[true/ok]\<^sub>f) \<or> ($ok \<and> \<not>$wait \<and> $ok\<acute> \<and> R2(P)\<^sup>t[true/ok]\<^sub>f)`" 
    apply(simp add:R2_def R1_def usubst typing defined closure)
    apply(utp_pred_auto_tac)
    done
  finally show ?thesis 
  apply(simp add:CSP_Pre_def CSP_Post_def)
  apply(simp add: R2_wait_false[THEN sym] R2_ok_true[THEN sym])
  apply (smt PVAR_VAR_pvdash R2_ok'_false R2_ok'_true)
  done
qed

lemma CSP_is_CSP1:
  assumes "P is CSP"
  shows "P is CSP1"
proof-
from assms have 1: "P = CSP(P)" by(metis is_healthy_def)
show ?thesis 
  apply(subst 1)
  apply(simp add:is_healthy_def CSP_def CSP1_idempotent)
  done
qed

lemma CSP_is_CSP2:
  assumes "P is CSP"
  shows "P is CSP2"
proof-
from assms have 1: "P = CSP(P)" by(metis is_healthy_def)
show ?thesis 
  apply(subst 1)
  apply(simp add:is_healthy_def CSP_def CSP1_CSP2_commute CSP2_idempotent)
  done
qed

lemma CSP_is_RHc: 
assumes "P is CSP"
shows "P is RHc" 
proof -
  from assms have 1: "P = CSP(P)" 
    by (metis Healthy_simp)
  have 2: "CSP(P) is RHc"
    apply(simp add:is_healthy_def)
    apply(simp add:CSP_def RHc_def)
    apply(simp add:CSP2_R1_commute CSP2_R2_commute CSP2_R3c_commute assms closure)
    apply(simp add:CSP1_R1_commute CSP1_R2_commute CSP1_R3c_commute)
    apply(simp add:R1_R2_commute R1_R3c_commute R1_idempotent)
    apply(simp add:R2_R3c_commute R2_idempotent R3c_idempotent)
    done
  show ?thesis 
    by (metis "1" "2")
qed

lemma RHc_is_R1: 
  assumes "P is RHc"
  shows "P is R1"
proof-
from assms have 1: "P = RHc(P)" by(metis is_healthy_def)
show ?thesis 
  apply(subst 1)
  apply(simp add:is_healthy_def RHc_def R1_idempotent)
  done
qed

lemma RHc_is_R2: 
  assumes "P is RHc"
  shows "P is R2"
proof-
from assms have 1: "P = RHc(P)" by(metis is_healthy_def)
show ?thesis 
  apply(subst 1)
  apply(simp add:is_healthy_def RHc_def R1_R2_commute R2_idempotent)
  done
qed

lemma RHc_is_R3c: 
  assumes "P is RHc"
  shows "P is R3c"
proof-
from assms have 1: "P = RHc(P)" by(metis is_healthy_def)
show ?thesis 
  apply(subst 1)
  apply(simp add:is_healthy_def RHc_def R1_R3c_commute R2_R3c_commute R3c_idempotent)
  done
qed

lemma DesignD_form: "`(P \<turnstile> Q)` = `\<not>$ok \<or> ($ok \<and> \<not>P) \<or> ($ok \<and> P \<and> $ok\<acute> \<and> Q)`"
by(utp_pred_auto_tac)

lemma CSP_Design: 
assumes "P is CSP" 
shows "P = `RHc ( CSP_Pre(P) \<turnstile> CSP_Post(P))`"
apply(subst CSP_form, simp_all add: assms)
apply(simp add:DesignD_form RHc_def)
apply(simp add:R2_def R1_idempotent)
apply(simp add:R2_def[THEN sym] R2_R3c_commute demorgan2)
apply(simp add:R2_OrP R2_AndP)
apply(subst R2_def)back back
apply(subst R2_def)back back
apply(subst R2_def)back back back
apply(simp add:R2s_def usubst typing defined closure)
apply(simp add:R3c_form_2 R1_def AndP_OrP_distl AndP_assoc[THEN sym] R2_def)
apply(utp_pred_auto_tac)
done

subsection {* Stop laws *}

lemma Stop_R1 : "STOP is R1"
apply(simp add:StopCSP_def is_healthy_def CSP1_R1_commute[THEN sym])
apply(subst AndP_comm, simp add:R1_extend_AndP[THEN sym] R1_R3c_commute)
apply(simp add:R1_def tr_eq_is_R1, subst AndP_comm) back
apply(simp)
done

lemma Stop_R2 : "STOP is R2"
apply(simp add:StopCSP_def is_healthy_def CSP1_R2_commute[THEN sym])
apply(subst AndP_comm, simp add:R2_def R2s_AndP R1_extend_AndP[THEN sym], simp add:R2_def[THEN sym] R2_R3c_commute)
apply(simp add:R2_def R2s_def usubst typing defined closure R1_extend_AndP[THEN sym], subst AndP_comm) back
apply(simp add:R1_def tr_prefix_as_nil)
done

lemma Stop_R3c : "STOP is R3c"
apply(simp add:StopCSP_def is_healthy_def CSP1_R3c_commute[THEN sym] R3c_def CSP1_SkipR)
apply(utp_pred_auto_tac)
done

lemma Stop_CSP1 : "STOP is CSP1"
by(simp add:StopCSP_def is_healthy_def CSP1_idempotent)

lemma Stop_CSP2: "STOP is CSP2"
apply(simp add:StopCSP_def is_healthy_def)
apply(simp add:R3c_def CSP1_SkipR)
apply(simp add:CSP1_def H2_split usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma Stop_CSP : "STOP is CSP"
proof -
  have 1: "CSP2 STOP = STOP"
    by(metis is_healthy_def Stop_CSP2)
  have 2: "CSP1 STOP = STOP"
    by(metis is_healthy_def Stop_CSP1)
  have 3: "R3c STOP = STOP" 
    by(metis is_healthy_def Stop_R3c)
  have 4: "R2 STOP = STOP" 
    by(metis is_healthy_def Stop_R2)
  have 5: "R1 STOP = STOP" 
    by(metis is_healthy_def Stop_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Stop_rel_closure[closure] : "STOP \<in> WF_RELATION"
by(simp add:StopCSP_def closure)

lemma Stop_pre: "`CSP_Pre(STOP)` = `true`"
apply(simp add:StopCSP_def CSP_Pre_def R3c_def CSP1_SkipR)
apply(simp add:CSP1_def usubst typing defined closure)
done

lemma Stop_post: "`CSP_Post(STOP)` = `($tr \<acute>=$tr) \<and> $wait \<acute>`"
apply(simp add:StopCSP_def CSP_Post_def R3c_def CSP1_SkipR)
apply(simp add:CSP1_def usubst typing defined closure)
done

lemma Stop_design : "`STOP` = `RHc ( true \<turnstile> ($tr\<acute>=$tr) \<and> $wait\<acute>)`"
by(subst CSP_Design, simp_all add:Stop_pre Stop_post Stop_CSP Stop_rel_closure)

subsection {* Skip laws *}

lemma Skip_R1 : "SKIP is R1"
by(simp add:SkipCSP_def is_healthy_def RHc_def R1_idempotent)

lemma Skip_R2 : "SKIP is R2"
by(simp add:SkipCSP_def is_healthy_def RHc_def R1_R2_commute R2_idempotent)

lemma Skip_R3c : "SKIP is R3c"
by(simp add:SkipCSP_def is_healthy_def RHc_def R2_R3c_commute R1_R3c_commute R3c_idempotent)

lemma Skip_form: "SKIP = `R3c ( CSP1 ( II\<^bsub> REL_VAR - {ref \<down>,ref \<down>\<acute>}\<^esub>))`"
proof -
  have "SKIP = `RHc (CSP1 ( II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>}\<^esub>))`"
apply(simp add:SkipCSP_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "ref "])
apply(simp_all add:closure typing CSP1_def ExistsP_OrP_dist)
apply(subst ExistsP_ident,simp add:unrest)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(subst UNREST_subset[of "- (REL_VAR - {ref \<down>,ref \<down>\<acute>})"])
apply(subst UNREST_SkipRA)
apply(simp_all add:closure CSP1_def[THEN sym])
  apply(subst PEqualP_sym)
  apply(simp add:erasure closure typing defined)
  apply(subst ExistsP_has_value[of _ "ref \<down>"])
  apply(simp_all add:typing defined unrest)
done
also have "... = `R3c (CSP1 (II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>}\<^esub>))`"
apply(simp add: RHc_def R2_def R1_idempotent)
apply(simp add:R2_def[THEN sym] R2_R3c_commute CSP1_R2_commute[THEN sym])
apply(subst SkipRA_unfold[of "tr \<down>"], simp_all add:closure)
apply(simp add:R2_def R2s_def usubst typing closure defined R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil)
apply(subst SkipRA_unfold_aux_ty[of "tr "],simp_all add:typing closure defined) back
apply(subst tr_prefix_as_nil[THEN sym])
apply(utp_poly_tac)
done
finally show ?thesis ..
qed

lemma Skip_CSP1 : "SKIP is CSP1"
by(simp add:Skip_form is_healthy_def CSP1_R3c_commute CSP1_idempotent)

lemma Skip_CSP2: "SKIP is CSP2"
apply(simp add:Skip_form is_healthy_def)
apply(simp add: CSP2_R3c_commute closure)
apply(subst CSP1_R1_form_2) defer
apply(simp add: CSP1_CSP2_commute[THEN sym] closure)
apply(subst SkipRA_unfold_aux_ty[of "ok "], simp_all add:closure typing)
apply(simp add:H2_split usubst typing defined closure)
apply(subst CSP1_R1_form_2) back defer
apply(subst SkipRA_unfold_aux_ty[of "ok "], simp_all add:closure typing) back back
apply(utp_poly_auto_tac)
apply(simp add:is_healthy_def R1_def)
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:closure typing)
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:closure typing AndP_assoc[THEN sym]) back
apply(subst AndP_comm, simp add:AndP_assoc tr_eq_is_R1)
done

lemma Skip_CSP : "SKIP is CSP"
proof -
  have 1: "CSP2 SKIP = SKIP"
    by(metis is_healthy_def Skip_CSP2)
  have 2: "CSP1 SKIP = SKIP"
    by(metis is_healthy_def Skip_CSP1)
  have 3: "R3c SKIP = SKIP" 
    by(metis is_healthy_def Skip_R3c)
  have 4: "R2 SKIP = SKIP" 
    by(metis is_healthy_def Skip_R2)
  have 5: "R1 SKIP = SKIP" 
    by(metis is_healthy_def Skip_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Skip_rel_closure[closure] : "SKIP \<in> WF_RELATION"
by(simp add:Skip_form closure)

lemma Skip_expansion: "SKIP =   `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute> \<and> $tr \<acute>=$tr \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR -REA - OKAY\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $tr \<acute>=$tr\<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
proof-
have "SKIP =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> II\<^bsub>REL_VAR\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>}\<^esub>)`"
apply(simp add:Skip_form)
apply(subst CSP1_R1_form_2) 
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure is_healthy_def R1_def)
apply(subst AndP_comm,simp_all add: AndP_assoc[THEN sym] tr_eq_is_R1)
apply(metis AndP_comm)
apply(simp add: R3c_form_2 SkipR_as_SkipRA CSP1_def)
apply(utp_poly_auto_tac)
done
also have "... =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute>=$wait \<and> $tr \<acute>=$tr \<and> $ok \<acute>=$ok \<and> II\<^bsub>REL_VAR -{ref \<down>,ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> $wait \<acute>=$wait \<and> $tr \<acute>=$tr\<and> $ok \<acute>=$ok \<and> II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>)`"
  apply(subst SkipRA_unfold_aux_ty[of "ref"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:typing closure) back
  apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure) back
  apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure) back
  done
also have "... =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute> \<and> $tr \<acute>=$tr \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR -{ref \<down>,ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $tr \<acute>=$tr\<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>)`"
by(utp_poly_auto_tac)
also have "... =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute> \<and> $tr \<acute>=$tr \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR -REA - OKAY\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $tr \<acute>=$tr\<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
proof -
  have 1: "`II\<^bsub>REL_VAR -{ref \<down>,ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>` = `II\<^bsub>REL_VAR -REA - OKAY\<^esub>`" 
    by (smt Diff_insert2 insert_commute)
  show ?thesis
    by(metis 1)
qed
finally show ?thesis ..
qed

lemma Skip_pre: "`CSP_Pre(SKIP)` = `true`"
apply(simp add:Skip_expansion CSP_Pre_def)
apply(simp add:usubst typing defined closure)
done

lemma Skip_post: "`CSP_Post(SKIP)` = `($tr \<acute>=$tr) \<and> \<not>$wait\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub> `"
apply(simp add:Skip_expansion CSP_Post_def)
apply(simp add:usubst typing defined closure)
by (smt AndP_assoc AndP_comm ParallelD_assoc ParallelD_comm SemiR_assoc SkipRA.rep_eq Un_def inf_sup_aci(5) insert_commute insert_compr set_diff_eq sup_assoc utp_pred_simps(15))

lemma Skip_design : "`SKIP` = `RHc ( true \<turnstile> ($tr\<acute>=$tr) \<and> \<not>$wait\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
by(subst CSP_Design, simp_all add:Skip_pre Skip_post Skip_CSP Skip_rel_closure)

subsection {* Chaos laws *}

lemma Chaos_form : "`CHAOS`= `CSP1(R3c(R1(true)))`"
  apply(simp add:ChaosCSP_def CSP_def RHc_def R2_R3c_commute R1_R3c_commute)
  apply(simp add:R2_def R2s_def R1_idempotent usubst typing closure defined)  
  apply(simp add:CSP2_R1_commute CSP2_R3c_commute closure)
  apply(simp add:H2_split usubst typing defined closure)
  done

lemma Chaos_expansion : "`CHAOS`= `(\<not> $ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> $ok \<and> II) \<or> ($ok \<and> \<not> $wait \<and> ($tr \<le> $tr\<acute>))`"
apply(simp add:Chaos_form CSP1_R3c_commute)
apply(simp add:R1_def)
apply(subst CSP1_R1_R3c_compose)
apply (metis R1_by_refinement order_refl)
apply(simp add:usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma Chaos_R1: 
  "CHAOS is R1"
by(simp add:ChaosCSP_def is_healthy_def CSP_def RHc_def CSP1_R1_commute[THEN sym] CSP2_R1_commute[THEN sym] closure R1_idempotent)

lemma Chaos_R2: 
  "CHAOS is R2"
by(simp add:ChaosCSP_def is_healthy_def CSP_def RHc_def CSP1_R2_commute[THEN sym] CSP2_R2_commute[THEN sym] closure R1_R2_commute R2_idempotent)

lemma Chaos_R3c: 
  "CHAOS is R3c"
by(simp add:Chaos_form CSP1_R3c_commute R3c_idempotent is_healthy_def)

lemma Chaos_CSP1: 
  "CHAOS is CSP1"
by(simp add:Chaos_form is_healthy_def CSP1_idempotent)

lemma Chaos_CSP2: 
  "CHAOS is CSP2"
by(simp add:ChaosCSP_def CSP_def is_healthy_def CSP1_CSP2_commute[THEN sym] closure RHc_def CSP2_idempotent)

lemma Chaos_CSP: 
  "CHAOS is CSP"
proof -
  have 1: "CSP2 CHAOS = CHAOS"
    by(metis is_healthy_def Chaos_CSP2)
  have 2: "CSP1 CHAOS = CHAOS"
    by(metis is_healthy_def Chaos_CSP1)
  have 3: "R3c CHAOS = CHAOS" 
    by(metis is_healthy_def Chaos_R3c)
  have 4: "R2 CHAOS = CHAOS" 
    by(metis is_healthy_def Chaos_R2)
  have 5: "R1 CHAOS = CHAOS" 
    by(metis is_healthy_def Chaos_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Chaos_rel_closure[closure]: 
  "CHAOS \<in> WF_RELATION"
by(simp add:ChaosCSP_def CSP_def RHc_def closure)

lemma Chaos_pre: 
  "CSP_Pre(CHAOS) = `\<not> R1(true)`"
by(simp add:CSP_Pre_def Chaos_expansion usubst typing defined closure R1_def)

lemma Chaos_post: 
  "CSP_Post(CHAOS) = R1 true"
by(simp add:CSP_Post_def Chaos_expansion usubst typing defined closure R1_def) 

lemma Chaos_design: 
  "CHAOS = `RHc ( false \<turnstile> true )`"
apply(subst CSP_Design, simp_all add: Chaos_rel_closure Chaos_pre Chaos_post Chaos_CSP) 
apply(simp add:DesignD_form RHc_def R1_R2_commute R1_R3c_commute)
apply(utp_poly_auto_tac)
done

subsection {*Prefix laws *}

lemma Prefix_form: 
  "@a = `CSP1 (R3c ($ok\<acute> \<and> ((a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))))`"
apply(simp add:PrefixSkipCSP_def R3c_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure) back
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure) back
apply(utp_poly_auto_tac)
done

lemma Prefix_R1: 
  "@a is R1"
    apply(simp add:PrefixSkipCSP_def is_healthy_def CSP1_R1_commute[THEN sym])
    apply(subst AndP_comm)
    apply(simp add:R1_extend_AndP[THEN sym] R1_R3c_commute CondR_def)
    apply(simp add:R1_OrP)
    apply(simp add:R1_def AndP_assoc[THEN sym] tr_eq_is_R1 tr_prefix_app)
    apply(subst AndP_comm,simp) back
  done

lemma Prefix_R2:
  assumes "{tr \<down>} \<sharp> a" "{tr \<down>\<acute>} \<sharp> a" 
  shows "@a is R2"
apply(simp add:is_healthy_def Prefix_form CSP1_R2_commute[THEN sym] R2_R3c_commute)
apply(subst AndP_comm)
apply(simp add:R2_def R2s_AndP R1_extend_AndP[THEN sym] SubstP_AndP)
apply(simp add:R2_def R2s_def usubst typing closure defined assms PSubstPE_VarP_single_UNREST)
apply(simp add:R1_CondR)
apply(simp add:R1_def AndP_assoc[THEN sym] tr_prefix_as_nil tr_prefix_as_a)
apply(metis AndP_comm)
done

lemma Prefix_R3c: 
  "@a is R3c"
by(simp add:Prefix_form is_healthy_def CSP1_R3c_commute R3c_idempotent)

lemma Prefix_CSP1: 
  "@a is CSP1"
by(simp add:PrefixSkipCSP_def is_healthy_def CSP1_idempotent)

lemma Prefix_CSP2: 
  assumes "{ok \<down>\<acute>} \<sharp> a" 
  shows "@a is CSP2"
apply(simp add:is_healthy_def Prefix_form)
apply(subst CSP1_CSP2_commute[THEN sym])
apply(subst CSP2_R3c_commute)
apply(simp add:H2_split usubst typing defined closure assms PSubstPE_VarP_single_UNREST)
apply(metis AndP_comm)
done

lemma Prefix_rel_closure[closure]: 
  assumes "NON_REL_VAR \<sharp> a"
  shows "@a \<in> WF_RELATION"
by(simp_all add:closure typing defined PrefixSkipCSP_def assms tr_eq_rel_closure a_notin_ref_closure tr_prefix_a_closure)

lemma Prefix_CSP: 
  assumes "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a"
  shows "@a is CSP" 
proof -
  have 0: "{tr \<down>} \<sharp> a" "{tr \<down> \<acute>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
  have 1: "CSP2 `@a` = `@a`"
  by(metis is_healthy_def Prefix_CSP2 0)
  have 2: "CSP1 `@a` = `@a`"
    by(metis is_healthy_def Prefix_CSP1)
  have 3: "R3c `@a` = `@a`" 
    by(metis is_healthy_def Prefix_R3c)
  have 4: "R2 `@a` = `@a`" 
    by(metis is_healthy_def Prefix_R2 0)
  have 5: "R1 `@a` = `@a`" 
    by(metis is_healthy_def Prefix_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Prefix_pre: 
"`CSP_Pre(@a)` = `true`"
by(simp add:Prefix_form CSP_Pre_def CSP1_def R3c_def usubst typing defined closure)

lemma Prefix_post: 
  assumes "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" 
  shows "CSP_Post `@a` = `(a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
proof -
  have 0: "{ok \<down>} \<sharp> a" "{wait \<down>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
by(simp add:Prefix_form CSP_Post_def CSP1_def R3c_def usubst typing defined closure 0  PSubstPE_VarP_single_UNREST)
qed 

lemma Prefix_design: 
  assumes "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>} \<sharp> a"
  shows "`@a` = `RHc ( true \<turnstile> ((a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
proof -
have  0: "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
by(subst CSP_Design, simp_all add: Prefix_rel_closure Prefix_pre Prefix_post Prefix_CSP assms 0) 
qed

subsection {* Sequential composition *}

lemma left_form_P:
  assumes "P is CSP" "P \<in> WF_RELATION"
  shows "P = `
  (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> 
  ($ok \<and> $wait \<and> II) \<or> 
  ($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P))) \<or> 
  ($ok \<and> \<not>$wait \<and> R2(CSP_Post(P)) \<and> $ok\<acute>)`"
  apply(subst CSP_Design,simp_all add: assms)
  apply(simp_all add: DesignD_form)
  apply(simp add:RHc_def R1_R3c_commute R2_R3c_commute)
  apply(simp add:R2_def R2s_def R1_idempotent)
  apply(simp add:usubst typing defined closure)
  apply(simp add:R1_def R3c_form_2 AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym])
  apply(utp_poly_auto_tac)
done

lemma Idle:"`$ok \<and> $wait \<and> II\<^bsub>REL_VAR\<^esub>` = `$ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY\<^esub> \<and> $ok\<acute>`"
  apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)
  apply(utp_poly_auto_tac)
  done

lemma CSP_Post_rel_closure[closure]: 
  assumes "P \<in> WF_RELATION"
  shows "CSP_Post P \<in> WF_RELATION"
by(simp add:CSP_Post_def closure typing defined unrest assms)

lemma CSP_Pre_rel_closure[closure]: 
  assumes "P \<in> WF_RELATION"
  shows "CSP_Pre P \<in> WF_RELATION"
by(simp add:CSP_Pre_def closure typing defined unrest assms)
  
lemma Seq_comp_1: 
  assumes "Q is CSP" "Q \<in> WF_RELATION"
  shows "`(\<not>$ok \<and> ($tr \<le> $tr\<acute>));Q` = `\<not>$ok \<and> ($tr \<le> $tr\<acute>)`"
proof -
  have "`(\<not>$ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>));CSP1(R1(Q))`"
    by(metis assms is_healthy_def CSP_is_CSP1 CSP_is_RHc RHc_is_R1)
  also have "... = `\<not>$ok \<and> ($tr \<le> $tr\<acute>)`"
    apply(subst SemiR_AndP_left_precond,simp_all add:closure typing defined assms)
    apply(subst CSP1_R1_form, simp add:is_healthy_def R1_idempotent)
    apply(simp add:CSP1_def SemiR_OrP_distl)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined assms unrest)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined unrest)
    apply(simp add:R1_def usubst typing defined closure SemiR_OrP_distl[THEN sym])
    apply(subst tr_leq_trans[THEN sym]) back back back
    apply(utp_poly_auto_tac)
    done
  finally show ?thesis
    ..
qed

lemma Seq_comp_2: 
  assumes "Q is CSP"
  shows "`($ok \<and> $wait \<and> II);Q` = `$ok \<and> $wait \<and> II`"
proof -
  have "`($ok \<and> $wait \<and> II);Q` =`($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> Q)`"
    apply(simp add:SkipR_as_SkipRA SemiR_AndP_right_precond typing closure urename assms AndP_assoc[THEN sym])
    apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:closure typing)
    apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:closure typing)
    apply(utp_poly_auto_tac)
    done
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> R3c(Q))`"
    proof -
      have 1: "Q = `R3c(Q)`"
        by(metis is_healthy_def assms CSP_is_RHc RHc_is_R3c)
      show ?thesis
        by(subst 1,simp)
    qed
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> II)`"
    apply(simp add:R3c_def CSP1_def)
    apply(utp_poly_auto_tac)
    done
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub> \<and> $ok\<acute> \<and> $wait\<acute>)`"
    by(simp add:SemiR_AndP_right_precond assms closure typing urename AndP_assoc[THEN sym])
  also have "... = `$ok \<and> $wait \<and> II`"
    apply(simp add:SkipR_as_SkipRA)
    apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:closure typing) back
    apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:closure typing) back
    apply(utp_poly_auto_tac)
    done
  finally show ?thesis
    ..
qed

lemma Seq_comp_3: 
  assumes "Q is CSP" "Q\<in> WF_RELATION" "P\<in> WF_RELATION"
  shows "`($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `$ok \<and> \<not>$wait \<and> (R2(\<not>CSP_Pre(P));($tr\<le>$tr\<acute>))`"
proof -
  have "`($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));CSP1(R1(Q))`"
    by(metis assms is_healthy_def CSP_is_CSP1 CSP_is_RHc RHc_is_R1)
  also have "... = `$ok \<and> \<not>$wait \<and> (R2(\<not>CSP_Pre(P));($tr\<le>$tr\<acute>))`"
    apply(subst SemiR_AndP_left_precond,simp_all add:closure typing defined assms)
    apply(subst SemiR_AndP_left_precond,simp_all add:closure typing defined assms)
    apply(subst CSP1_R1_form, simp add:is_healthy_def R1_idempotent)
    apply(simp add:CSP1_def SemiR_OrP_distl)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined assms unrest)
    apply(simp add:typing closure defined assms unrest CSP_Pre_def R2_def R2s_def R1_def)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined unrest assms)
    apply(simp add:typing closure defined assms unrest CSP_Pre_def R2_def R2s_def R1_def)
    apply(simp add:R1_def usubst typing defined closure SemiR_OrP_distl[THEN sym] AndP_assoc[THEN sym])
    apply(utp_poly_auto_tac)
    done
  finally show ?thesis
    ..
qed

lemma DesignREA_form: 
  "`RHc( P \<turnstile> Q)` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(\<not>P)) \<or> ($ok \<and> \<not>$wait \<and> R2(Q) \<and> $ok\<acute>)`"
apply(simp add:DesignD_form RHc_def R3c_form_2 SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:closure typing)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:closure typing)back
apply(simp add:R2_def R1_idempotent R2s_def usubst typing defined closure)
apply(simp add:R1_OrP)
apply(simp add:R1_def AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(subst AndP_comm) back back back back
apply(simp add:AndP_assoc[THEN sym] tr_prefix_as_nil)
apply(utp_poly_auto_tac)
done

lemma Seq_comp_form: 
assumes "P is CSP" "Q is CSP" "P \<in> WF_RELATION" "Q\<in> WF_RELATION"
shows "`P ; Q` = 
`RHc (
          \<not>(\<not> CSP_Pre(P) ; ($tr \<le> $tr\<acute>)) \<and> \<not>(CSP_Post(P) ; (\<not> $wait \<and> R2(\<not> CSP_Pre(Q))))
                                                \<turnstile>
                  CSP_Post(P) ; (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> R2(CSP_Post(Q)))
                                                                                                       )`"
proof - have "`P ; Q` = `
  (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
  ($ok \<and> $wait \<and> II) \<or>
  ($ok \<and> \<not> $wait \<and> (R2(\<not> CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))) \<or>
  ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P));($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<and> $ok\<acute>) \<or>
  ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) ; ($ok \<and> \<not>$wait \<and> R2 (\<not> CSP_Pre(Q)))) \<or> 
  ($ok \<and> \<not> $wait \<and> (R2 (CSP_Post(P)) ; ($ok \<and> \<not>$wait \<and> R2 (CSP_Post(Q)))) \<and> $ok\<acute>)
`"
apply(subst left_form_P, simp_all add:assms SemiR_OrP_distr)
apply(simp add: Seq_comp_1 Seq_comp_2 assms Seq_comp_3 DesignREA_form AndP_assoc[THEN sym])
apply(subst left_form_P[of "Q"], simp_all add:assms SemiR_OrP_distl SkipR_as_SkipRA)
apply(subst Idle) back
apply(simp add: SemiR_AndP_right_precond typing closure defined urename)
apply(simp add:AndP_assoc[THEN sym] AndP_contra)
apply(simp add: SemiR_AndP_left_precond typing closure defined assms)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add: typing closure defined assms)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add: typing closure defined assms)
done
also have "... = `
     (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> ((R2 (\<not> CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<or> (R2 (CSP_Post(P)) ; (\<not> $wait \<and> R2 (\<not> CSP_Pre(Q)))))) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) ; (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> R2(CSP_Post(Q))) \<and> $ok\<acute>)
`"
apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"])
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:typing closure defined unrest assms CSP_Pre_def CSP_Post_def)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"]) back
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:typing closure defined unrest assms CSP_Pre_def CSP_Post_def)
apply(simp add:typing closure defined unrest assms CSP_Pre_def CSP_Post_def)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"]) back back
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:typing closure defined unrest assms CSP_Pre_def CSP_Post_def)
apply(simp add:typing closure defined unrest assms CSP_Pre_def CSP_Post_def)
apply(simp add:CondR_def AndP_OrP_distl SemiR_OrP_distl AndP_OrP_distr OrP_assoc[THEN sym])
apply(subst OrP_comm) back back back 
apply(simp add:OrP_assoc[THEN sym])
apply(subst OrP_comm) back back back back
apply(simp)
done
also have "... = `
     (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> ((R2 (\<not> CSP_Pre(P)) ; R2($tr \<le> $tr\<acute>)) \<or> (R2 (CSP_Post(P)) ; R2(\<not> $wait \<and> \<not> CSP_Pre(Q))))) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) ; R2(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q)) \<and> $ok\<acute>)
`"
apply(simp add:R2_CondR)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure) back
apply(simp add:R2_def R1_def R2s_def usubst typing defined closure AndP_assoc[THEN sym])
apply(subst AndP_comm) back back back back back back back back back back back back back back back back back back back back back back back back back back back back
apply(simp add:AndP_assoc tr_prefix_as_nil)
done
also have "... = `
     (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2(\<not> CSP_Pre(P) ; R2($tr \<le> $tr\<acute>)) \<or> R2(CSP_Post(P) ; R2(\<not> $wait \<and> \<not> CSP_Pre(Q)))) \<or>
     ($ok \<and> \<not> $wait \<and> R2(CSP_Post(P) ; R2(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q))) \<and> $ok\<acute>)
`"
by(simp add:R2_OrP R2_sequential_composition closure assms)
also have "... = `
     (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2(\<not>( \<not>(\<not> CSP_Pre(P) ; ($tr \<le> $tr\<acute>)) \<and> \<not>(CSP_Post(P) ; (\<not> $wait \<and> R2(\<not> CSP_Pre(Q))))))) \<or>
     ($ok \<and> \<not> $wait \<and> R2(CSP_Post(P) ; (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> R2(CSP_Post(Q)))) \<and> $ok\<acute>)
`"
apply(simp add:R2_OrP[THEN sym] R2_CondR demorgan2)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure)
apply(subst AndP_comm) back back back back back back back back
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure)back
apply(subst AndP_comm) back back back back back back back back back  back back back back back back back back back
apply(simp add:R2_def R2s_def R1_def usubst typing defined closure AndP_assoc[THEN sym] tr_prefix_as_nil)
done
finally show ?thesis
  by(metis DesignREA_form)
qed

subsection {*CSP laws*}
lemma L1 : 
  assumes "P is CSP" "P \<in> WF_RELATION"
  shows "`CHAOS ; P` = `CHAOS`"
apply(subst Seq_comp_form, simp_all add:assms closure Chaos_CSP Chaos_pre Chaos_post)
apply(simp add: R1_def usubst typing defined closure)
apply(simp add:DesignD_form demorgan2 tr_leq_trans AndP_OrP_distl Chaos_design RHc_def R1_R2_commute R1_R3c_commute AndP_OrP_distr)
apply(simp add:R1_def AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym])
apply(utp_poly_auto_tac)
done

lemma L2 : 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "`STOP ; P` = `STOP`"
apply(subst Seq_comp_form, simp_all add:assms closure Stop_CSP Stop_pre Stop_post)
apply(simp add:R1_def usubst typing defined closure CondR_def SemiR_OrP_distl)
apply(subst SemiR_AndP_right_precond, simp_all add:typing closure defined urename AndP_assoc[THEN sym] AndP_contra)
apply(subst SemiR_AndP_right_precond, simp_all add:typing closure defined urename AndP_assoc[THEN sym])
apply(subst SemiR_SkipRA_right, simp_all add:typing closure defined unrest)
apply(subst SemiR_AndP_right_precond, simp_all add:typing closure defined urename AndP_assoc[THEN sym] AndP_contra)
apply(simp add:Stop_design)
done

lemma External_R1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R1" "Q is R1"
shows "P \<box> Q is R1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R1_commute[THEN sym])
apply(simp add:R1_CondR R1_AndP R1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_R2: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R2" "Q is R2"
shows "P \<box> Q is R2"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R2_commute[THEN sym])
apply(simp add:R2_CondR_alt R2_AndP R2_OrP)
apply(metis assms Stop_R2 is_healthy_def)
done

lemma External_R3c: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R3c" "Q is R3c"
shows "P \<box> Q is R3c"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R3c_commute[THEN sym])
apply(simp add: R3c_CondR R3c_AndP R3c_OrP)
apply(metis assms is_healthy_def)
done

lemma External_CSP1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP1" "Q is CSP1"
shows "P \<box> Q is CSP1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP1_CSP2_commute)
apply(simp add:CSP1_CondR CSP1_AndP CSP1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_CSP2: 
  "P \<box> Q is CSP2"
by(simp add:ExternalChoiceCSP_def is_healthy_def CSP2_idempotent)

lemma External_closure[closure]: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "P \<box> Q \<in> WF_RELATION"
by(simp add:ExternalChoiceCSP_def closure assms)

lemma External_CSP:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP" 
shows  "P \<box> Q is CSP"
proof -
  have 1: "CSP2 (P \<box> Q) = (P \<box> Q)"
    by(metis is_healthy_def External_CSP2 assms)
  have 2: "CSP1 (P \<box> Q) = (P \<box> Q)"
    by(metis is_healthy_def External_CSP1 assms CSP_is_CSP1)
  have 3: "R3c (P \<box> Q) = (P \<box> Q)" 
    by(metis is_healthy_def External_R3c assms CSP_is_RHc RHc_is_R3c)
  have 4: "R2 (P \<box> Q) = (P \<box> Q)" 
    by(metis is_healthy_def External_R2 assms CSP_is_RHc RHc_is_R2)
  have 5: "R1 (P \<box> Q) = (P \<box> Q)" 
    by(metis is_healthy_def External_R1 assms CSP_is_RHc RHc_is_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma External_pre: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows"`CSP_Pre(P \<box> Q)` = `CSP_Pre(P) \<and> CSP_Pre(Q)`"
apply(simp add:ExternalChoiceCSP_def H2_split Stop_design DesignREA_form SkipR_as_SkipRA R2_def R1_def R2s_def)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)back
apply(simp add:usubst typing defined closure CSP_Pre_def)
apply (metis demorgan1)
done

lemma External_post:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "`CSP_Post(P \<box> Q)` = `\<not>CSP_Pre(P) \<or> \<not>CSP_Pre(Q) \<or> ((CSP_Post(P) \<and> CSP_Post(Q)) \<lhd> ($tr\<acute>=$tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q)))`"

apply(simp add:ExternalChoiceCSP_def H2_split Stop_design DesignREA_form SkipR_as_SkipRA R2_def R1_def R2s_def)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)back
apply(simp add:usubst typing defined closure CSP_Post_def CSP_Pre_def)
apply(subst AndP_comm) back
apply(simp add:AndP_assoc[THEN sym] tr_prefix_as_nil CondR_def)
apply(utp_poly_auto_tac)
done

lemma External_design: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP"
shows "P \<box> Q = `RHc((CSP_Pre(P) \<and> CSP_Pre(Q)) \<turnstile> ((CSP_Post(P) \<and> CSP_Post(Q)) \<lhd> ($tr\<acute>=$tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q))))`"
apply(subst CSP_Design[of "P \<box> Q"],simp_all add: External_CSP closure assms)
apply(simp add:External_pre External_post assms)
apply(simp add:DesignD_form AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym] CondR_def)
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_comm) back back back back back
apply(subst AndP_comm) back back back back back back back back back
apply(subst AndP_assoc) back back back back back
apply(simp add:AndP_contra)
done

lemma SemiR_Skip_right:
  assumes "P is CSP" "P \<in> WF_RELATION" "`\<not>((\<not>CSP_Pre(P));($tr\<le>$tr\<acute>))` = CSP_Pre(P)" "`(CSP_Post(P) \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>\<acute> . CSP_Post(P)[($ref\<acute>\<acute>)/ref\<acute>]))` = CSP_Post(P)"
  shows "`P ; SKIP` = P"
proof-
have 1: " `II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>` =  `II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {wait \<down>,wait \<down>\<acute>}\<^esub>`"
by (smt Diff_insert2 insert_commute)
have "`P ; SKIP` = `RHc (CSP_Pre(P) \<turnstile>  (CSP_Post(P) ; ($wait \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub>)) \<or>
         (CSP_Post(P) ; (\<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - OKAY\<^esub>)))`"
apply(subst Seq_comp_form, simp_all add:assms(1) assms(2) closure Skip_CSP)
apply(simp add:Skip_pre Skip_post R2_def R2s_def usubst typing closure defined R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil CondR_def SemiR_OrP_distl SemiR_OrP_distr assms(3))
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure)back back back
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing closure)back back back
apply(subst 1)
apply(utp_poly_auto_tac)
done
also have "... = `RHc (CSP_Pre(P) \<turnstile> CSP_Post(P))`"
apply(simp add:SemiR_AndP_right_precond closure typing assms urename)
apply(subst SemiR_SkipRA_right,simp_all add:typing closure defined assms unrest)
apply(rule unrest, simp add:CSP_Post_def typing closure defined assms unrest)
apply(rule unrest, simp_all add: typing closure defined assms unrest)
apply(rule unrest, simp_all add: typing closure defined assms unrest)
apply(rule unrest, simp_all add: typing closure defined assms unrest) defer
apply(subst SemiR_extract_variable_id_ty[of "ref "])
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:usubst typing defined closure)
apply(subst SemiR_SkipRA_right,simp_all add:typing closure defined assms unrest)
apply(rule unrest)
apply(rule unrest, simp add:CSP_Post_def typing closure defined assms unrest)
apply(simp add:CSP_Post_def)
apply(rule unrest, simp add: typing closure defined assms unrest)
apply(rule unrest, simp add: typing closure defined assms unrest)
apply(rule unrest, simp add: typing closure defined assms unrest) defer 
apply(rule unrest, simp add: typing closure defined assms unrest)
apply(subst ExistsP_AndP_expand1[THEN sym], simp add:typing closure defined unrest)
apply(subst assms(4)[THEN sym]) back back
apply(simp add:CondR_def,utp_poly_auto_tac)
apply(subst UNREST_subset[of "{}"],simp_all add:typing closure defined unrest)
apply(utp_poly_auto_tac)
apply(subst UNREST_subset[of "{}"],simp_all add:typing closure defined unrest)
apply(utp_poly_auto_tac)
done
also have "... = P"
apply(subst CSP_Design[of "P"]) back back
apply(simp_all add:assms)
done
finally show ?thesis ..
qed

lemma 
  assumes "{ok \<down>,ok\<down>\<acute>,tr \<down>,tr \<down>\<acute>,wait \<down>,wait \<down>\<acute>,ref \<down>\<acute>} \<sharp> a" "NON_REL_VAR \<sharp> a"
  shows "a \<rightarrow> SKIP = @a"
proof -
have 0:  "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{ref \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
apply(simp add:PrefixCSP_def)
apply(subst SemiR_Skip_right, simp_all add: Prefix_CSP assms closure Prefix_pre Prefix_post 0)
apply(simp add:usubst typing defined closure PSubstPE_VarP_single_UNREST assms CondR_def ExistsP_OrP_dist 0)
apply(subst ExistsP_AndP_expand2[THEN sym], simp add:closure typing defined unrest)
apply(subst ExistsP_ident[of "{ref \<down>\<acute>\<acute>}"]) back
apply(simp add:closure typing defined unrest assms 0)
apply(utp_poly_auto_tac)
done
qed

lemma CSP_Pre_R2: 
  assumes "P is R2"
  shows "`\<not>CSP_Pre(P)` is R2"
proof-
from assms have "`\<not>CSP_Pre(P)` = `\<not>CSP_Pre(R2(P))`"
by(metis is_healthy_def)
also have "... = `R2(\<not>CSP_Pre(P))`"
apply(subst CSP_Pre_def)
apply(subst R2_ok'_false)
apply(subst R2_ok_true)
apply(subst R2_wait_false)
apply(subst NotP_NotP[THEN sym]) back back back back back back
apply(subst CSP_Pre_def[THEN sym])
apply(simp add: NotP_NotP)
done
finally show ?thesis by(metis is_healthy_def)
qed

lemma Prefixed_pre: 
  assumes "P \<in> WF_RELATION" "P is CSP" "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
  shows "CSP_Pre(a \<rightarrow> P) = `\<not>(($tr^\<langle>a\<rangle>=$tr\<acute>);\<not>CSP_Pre(P))`" 
proof - 
have 0:  "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{wait \<down>} \<sharp> a" "{wait \<down>\<acute>} \<sharp> a" "{ok \<down>} \<sharp> a" "{tr \<down>} \<sharp> a""{tr \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
have "CSP_Pre(a \<rightarrow> P) = `CSP_Pre(R2(((a \<notin> $ref\<acute> \<and> $tr\<acute>= $tr) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)) ; (\<not>$wait \<and> R2(\<not>CSP_Pre(P)))))`"
apply(simp add:PrefixCSP_def)
apply(subst Seq_comp_form, simp_all add: closure assms Prefix_CSP 0)
apply(simp add:Prefix_pre Prefix_post assms DesignREA_form 0)
apply(simp add:CSP_Pre_def usubst typing defined closure)
done
also have "... = `CSP_Pre (R2 (($tr ^ \<langle>a\<rangle> = $tr\<acute>) ;(\<not>$wait \<and> R2 (\<not> CSP_Pre(P)))))`"
apply(subst SemiR_AndP_right_precond,simp_all add:closure typing defined urename CondR_def AndP_OrP_distr)
apply(subst AndP_comm)
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym] AndP_contra)
apply(subst SemiR_AndP_right_precond,simp_all add:closure typing defined urename)
done
also have "... = `\<not>(R2 ($tr ^ \<langle>a\<rangle> = $tr\<acute>) ; R2 (\<not>CSP_Pre(P)))`"
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait \<down>}"],simp_all add:typing closure defined unrest assms tr_prefix_a_closure 0)
apply(simp add:CSP_Pre_def closure typing defined unrest)
apply(subst CSP_Pre_def)
apply(subst R2_ok'_false)
apply(subst SubstP_SemiR_right)
apply(simp add:closure defined typing unrest)
apply(simp add:closure defined typing unrest)
apply(subst R2_ok'_false)
apply(simp add: R2_ok_true R2_wait_false)
apply(subst SubstP_SemiR_left,simp_all add:closure defined typing unrest)
apply(subst SubstP_SemiR_left,simp_all add:closure defined typing unrest)
apply(simp add:usubst typing defined closure assms PSubstPE_VarP_single_UNREST 0)
apply(subst SubstP_VarP_single_UNREST)
apply(simp add:CSP_Pre_def unrest typing defined closure)
apply(subst R2_SemiR_distribute[THEN sym],simp_all add:assms typing closure defined tr_prefix_a_closure)
apply(subst R2_SemiR_distribute',simp_all add:assms typing closure defined tr_prefix_a_closure)
done
also have "... = `\<not>(($tr^\<langle>a\<rangle>=$tr\<acute>);R2(\<not>CSP_Pre(P)))`"
by(simp add:R2_def R2s_def usubst typing defined closure assms PSubstPE_VarP_single_UNREST R1_def tr_prefix_as_a 0)
also have "... = `\<not>(($tr^\<langle>a\<rangle>=$tr\<acute>);(\<not>CSP_Pre(P)))`"
proof-
have "`\<not>CSP_Pre(P)` is R2" 
by(simp add:CSP_Pre_R2 assms CSP_is_RHc RHc_is_R2)
thus ?thesis by (metis Healthy_simp)
qed
finally show ?thesis 
..
qed

lemma CSP_Post_R2: 
  assumes "P is R2"
  shows "`CSP_Post(P)` is R2"
proof -
from assms have "`CSP_Post(P)` = `CSP_Post(R2(P))`" by (metis assms is_healthy_def)
also have "... = `R2(CSP_Post(P))`"
apply(subst CSP_Post_def)
apply(subst R2_ok'_true)
apply(subst R2_ok_true)
apply(subst R2_wait_false)
apply(subst CSP_Post_def[THEN sym])
apply(simp)
done
finally show ?thesis by(metis is_healthy_def)
qed

lemma Prefixed_post: 
  assumes "P \<in> WF_RELATION" "P is CSP" "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
  shows "CSP_Post(a \<rightarrow> P) = `(($tr ^ \<langle>a\<rangle> = $tr\<acute>) ;\<not> CSP_Pre(P)) \<or>
     ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> 
     (($tr ^ \<langle>a\<rangle> = $tr\<acute>) ; CSP_Post(P))`" 
proof -
have 0:  "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{wait \<down>} \<sharp> a" "{wait \<down>\<acute>} \<sharp> a" "{ok \<down>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a" "{tr \<down>} \<sharp> a""{tr \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
have" CSP_Post(a \<rightarrow> P) = `CSP_Post(R2((\<not> $wait\<acute> \<and> $tr ^ \<langle>a\<rangle> = $tr\<acute>) ; R2 (\<not> CSP_Pre(P)))) \<or> 
                      ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or>
                      CSP_Post(R2((\<not> $wait\<acute> \<and> $tr ^ \<langle>a\<rangle> = $tr\<acute>) ; R2 (CSP_Post(P))))`"
apply(simp add:PrefixCSP_def)
apply(subst Seq_comp_form,simp_all add:assms closure Prefix_CSP Prefix_pre Prefix_post DesignREA_form 0)
apply(subst CSP_Post_def,simp add:usubst typing defined closure CondR_def SemiR_OrP_distl 0)
apply(simp add: SemiR_AndP_right_precond typing closure defined urename)
apply(subst SemiR_SkipRA_right,simp_all add:typing closure defined)
apply(subst UNREST_subset[of "{ok \<down>\<acute>}"],simp_all add:typing defined closure unrest assms 0)
apply(utp_poly_auto_tac)
apply(simp add:CSP_Post_def R2_OrP)
apply(subst R2_def) back back
apply(simp add:R1_def R2s_def usubst typing defined closure assms PSubstPE_VarP_single_UNREST 0)
apply(simp add: AndP_OrP_distl AndP_OrP_distr)
apply(subst AndP_comm)
apply(subst AndP_assoc[THEN sym]) back
apply(simp add:AndP_contra)
apply(subst AndP_comm) back
apply(subst AndP_assoc,simp)
apply(subst AndP_comm) back
apply(subst AndP_assoc[THEN sym]) back
apply(simp)
apply(subst AndP_comm) back back
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc[THEN sym])
apply(subst tr_prefix_as_nil)
apply(subst AndP_comm) back back back back
apply(subst AndP_assoc)  back
apply(simp add:AndP_contra)
apply(subst AndP_comm) back back back back back
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back
apply(simp add:AndP_contra)
apply(subst AndP_comm) back back back back
apply(subst AndP_assoc) back
apply(simp)
done
also have "... = `(($tr ^ \<langle>a\<rangle> = $tr\<acute> \<and> \<not> $wait\<acute>) ; R2(\<not> CSP_Pre(P))) \<or>
     ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> 
     (($tr ^ \<langle>a\<rangle> = $tr\<acute> \<and> \<not> $wait\<acute>) ; R2(CSP_Post(P)))`"
apply(subst CSP_Post_def)apply(subst CSP_Post_def)
apply(subst R2_ok'_true)
apply(subst SubstP_SemiR_right)
apply(simp add:defined typing closure)
apply(simp add:defined typing closure unrest)
apply(subst R2_ok'_true)
apply(subst R2_ok'_true)
apply(subst SubstP_SemiR_right)
apply(simp add:defined typing closure)
apply(simp add:defined typing closure unrest)
apply(subst R2_ok'_true)
apply(subst SubstP_VarP_single_UNREST)
apply(simp add:CSP_Pre_def unrest typing closure defined)
apply(subst SubstP_VarP_single_UNREST) back back
apply(simp add:CSP_Post_def unrest typing closure defined)
apply(simp add:SubstP_SemiR_left defined typing closure unrest assms R2_ok_true R2_wait_false)
apply(simp add:usubst typing defined closure assms PSubstPE_VarP_single_UNREST 0)
apply(subst R2_SemiR_distribute'[THEN sym],simp_all add:typing closure defined unrest assms tr_prefix_a_closure)
apply(subst R2_SemiR_distribute,simp_all add:typing closure defined unrest assms tr_prefix_a_closure)
apply(subst R2_SemiR_distribute'[THEN sym],simp_all add:typing closure defined unrest assms tr_prefix_a_closure)
apply(subst R2_SemiR_distribute,simp_all add:typing closure defined unrest assms tr_prefix_a_closure)
apply(simp add:R2_def R2s_def usubst typing defined closure assms PSubstPE_VarP_single_UNREST 0)
apply(subst AndP_comm)
apply(subst AndP_comm) back back back
apply(simp add:R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_a)
done
also have "... = `(($tr ^ \<langle>a\<rangle> = $tr\<acute> \<and> \<not> $wait\<acute>) ; \<not> CSP_Pre(P)) \<or>
     ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> 
     (($tr ^ \<langle>a\<rangle> = $tr\<acute> \<and> \<not> $wait\<acute>) ; CSP_Post(P))`"
proof-
  from assms have 1: "`\<not>CSP_Pre(P)` is R2" by(simp add:CSP_Pre_R2 CSP_is_RHc RHc_is_R2)
  from assms have 2: "`CSP_Post(P)` is R2" by(simp add:CSP_Post_R2 CSP_is_RHc RHc_is_R2)
  show ?thesis by(metis 1 2 is_healthy_def)
qed
also have "... =  `(($tr ^ \<langle>a\<rangle> = $tr\<acute>) ;(\<not>$wait \<and> \<not> CSP_Pre(P))) \<or>
     ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> 
     (($tr ^ \<langle>a\<rangle> = $tr\<acute>) ; (\<not>$wait \<and> CSP_Post(P)))`"
by(simp add:SemiR_AndP_right_precond closure typing defined assms urename)
also have "... = `(($tr ^ \<langle>a\<rangle> = $tr\<acute>) ;\<not> CSP_Pre(P)) \<or>
     ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> 
     (($tr ^ \<langle>a\<rangle> = $tr\<acute>) ; CSP_Post(P))`"
by(simp add: SemiR_remove_middle_unrest1[of _ _ "{wait \<down>}"] typing closure defined unrest assms tr_prefix_a_closure CSP_Pre_def CSP_Post_def 0)
finally show ?thesis ..
qed 

lemma R3c_seq_comp_1: 
  assumes "Q is R3c" "Q is R1" "Q \<in> WF_RELATION"
  shows "`(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q` = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)`"
proof -
  have "`(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));R1(R3c(Q))`"
    by(metis assms is_healthy_def)
  also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; (\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; ($ok \<and> $wait \<and> ($ok\<acute>=$ok) \<and> ($wait\<acute>=$wait) \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (\<not> $wait \<and> Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    apply(simp add: SemiR_AndP_left_precond closure typing defined assms)
    apply(simp add:R1_def R3c_form SemiR_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym] SkipR_as_SkipRA)
    apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)
    apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing closure)
    apply(simp add:AndP_assoc[THEN sym])
    done
  also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; (\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (($ok \<and> $wait \<and> $ok\<acute> \<and> $wait\<acute>) \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (\<not> $wait \<and> Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    proof -
      have 0: "`$ok \<and> $wait \<and> ($ok\<acute>=$ok) \<and> ($wait\<acute>=$wait)`= `$ok \<and> $wait \<and> $ok\<acute> \<and> $wait\<acute>`"
        by(utp_poly_auto_tac)
      show ?thesis 
        by(subst 0[THEN sym],simp add:AndP_assoc[THEN sym])
   qed
 also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; ($tr \<le> $tr\<acute>) \<or>
                       ($tr \<le> $tr\<acute>) ; ($ok\<acute> \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    apply(simp add:AndP_assoc[THEN sym])
    apply(simp add: SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"] typing closure defined unrest assms)
    apply(simp add: SemiR_remove_middle_unrest1[of _ _ "{wait \<down>}"] typing closure defined unrest assms)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add: typing closure defined unrest)
defer 
apply(utp_poly_auto_tac)
apply(rule unrest) back back
apply(simp_all add:unrest closure typing)
apply(rule unrest) back back
apply(simp_all add:unrest closure typing)
apply(rule unrest) back back
apply(simp_all add:unrest closure typing)
apply(rule unrest) back back
apply(subst UNREST_subset)
apply(subst UNREST_SkipRA)
apply(simp_all add:typing closure defined unrest) 
done
also have "... = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>);((true \<or> ($ok\<acute> \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {ok \<down>,ok \<down>\<acute>} - {wait \<down>,wait \<down>\<acute>}\<^esub>) \<or> Q[false/wait]) \<and> ($tr \<le> $tr\<acute>))`"
apply(subst AndP_OrP_distr)
apply(simp add:AndP_OrP_distr SemiR_OrP_distl AndP_assoc[THEN sym])
done
also have "... = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)`"
  by(simp add:utp_pred_simps(8) tr_leq_trans)
  finally show ?thesis
    ..
qed

lemma R3c_seq_comp_2: 
  assumes "Q is R3c"
  shows "`($ok \<and> $wait \<and> II);Q` = `$ok \<and> $wait \<and> II`"
proof -
  have "`($ok \<and> $wait \<and> II);Q` =`($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> Q)`"
    apply(simp add:SkipR_as_SkipRA SemiR_AndP_right_precond typing closure urename assms AndP_assoc[THEN sym])
    apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:closure typing)
    apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:closure typing)
    apply(utp_poly_auto_tac)
    done
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> R3c(Q))`"
    proof -
      have 1: "Q = `R3c(Q)`"
        by(metis is_healthy_def assms)
      show ?thesis
        by(subst 1,simp)
    qed
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> II)`"
    apply(simp add:R3c_def CSP1_def)
    apply(utp_poly_auto_tac)
    done
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub> \<and> $ok\<acute> \<and> $wait\<acute>)`"
    by(simp add:SemiR_AndP_right_precond assms closure typing urename AndP_assoc[THEN sym])
  also have "... = `$ok \<and> $wait \<and> II`"
    apply(simp add:SkipR_as_SkipRA)
    apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:closure typing) back
    apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:closure typing) back
    apply(utp_poly_auto_tac)
    done
  finally show ?thesis
    ..
qed

lemma R3c_SemiR_closure:
  assumes "P is R3c" "Q is R3c" "P \<in> WF_RELATION" "Q\<in> WF_RELATION" "Q is R1"
  shows " `P ; Q` is R3c"
proof -
have "`P;Q` = `R3c(P);Q`"by(metis assms is_healthy_def)
also have "... = `R3c(P;Q)`"
   apply(simp add:R3c_form_2 SemiR_OrP_distr R3c_seq_comp_1 assms R3c_seq_comp_2 assms)
   apply(simp add: assms SemiR_AndP_left_precond typing closure)
   done
finally show ?thesis by (metis is_healthy_def)
qed

lemma CSP1_SemiR_closure:
  assumes "P is CSP1" "Q is CSP1" "Q is R1"
  shows " `P ; Q` is CSP1"
proof -
have "`P ; Q` = `CSP1(P);Q`" by (metis assms is_healthy_def)
also have "... = `(P;Q) \<or> (\<not>$ok \<and> ($tr \<le> $tr\<acute>));R1(CSP1(Q))`" 
apply(subst CSP1_def, simp add: SemiR_OrP_distr)
apply(metis assms is_healthy_def)
done
also have "... = ` (P ; Q) \<or> (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; ((Q \<or> true) \<and> ($tr \<le> $tr\<acute>))`"
apply(subst AndP_OrP_distr)
apply(simp add:R1_def CSP1_def AndP_OrP_distr AndP_assoc[THEN sym] SemiR_OrP_distl)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure unrest) back
done
also have "... = `CSP1(P ; Q)`"
by(simp add:SemiR_AndP_left_precond typing closure defined tr_leq_trans CSP1_def)
finally show ?thesis by (metis is_healthy_def)
qed

lemma CSP2_SemiR_closure:
  assumes "Q is CSP2"
  shows " `P ; Q` is CSP2"
apply(simp add:is_healthy_def H2_def SemiR_assoc[THEN sym])
apply(simp add:H2_def[THEN sym])
apply(metis assms is_healthy_def)
done

lemma CSP_SemiR_closure: 
  assumes "P is CSP" "Q is CSP" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows " `P ; Q` is CSP"
proof -
have 0: 
  "P is R1" "P is R2" "P is R3c" "P is CSP1"
  "Q is R1" "Q is R2" "Q is R3c" "Q is CSP1" "Q is CSP2"
  apply(metis assms CSP_is_RHc RHc_is_R1)
  apply(metis assms CSP_is_RHc RHc_is_R2)
  apply(metis assms CSP_is_RHc RHc_is_R3c)
  apply(metis assms CSP_is_CSP1)
  apply(metis assms CSP_is_RHc RHc_is_R1)
  apply(metis assms CSP_is_RHc RHc_is_R2)
  apply(metis assms CSP_is_RHc RHc_is_R3c)
  apply(metis assms CSP_is_CSP1)
  apply(metis assms CSP_is_CSP2)
done
have 1: "`P;Q` is R1" 
  by(simp add: 0 R1_SemiR_closure assms)
have 2: "`P;Q` is R2" 
  by(simp add: 0 R2_SemiR_closure assms)
have 3: "`P;Q` is R3c" 
  by(simp add: 0 R3c_SemiR_closure assms)
have 4: "`P;Q` is CSP1" 
  by(simp add: 0 CSP1_SemiR_closure assms)
have 5: "`P;Q` is CSP2" 
  by(simp add: 0 CSP2_SemiR_closure assms)
show ?thesis
apply(simp add: is_healthy_def CSP_def RHc_def)
apply(metis 1 2 3 4 5 is_healthy_def)
done
qed

lemma Prefixed_CSP: 
  assumes "P is CSP" "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "NON_REL_VAR \<sharp> a" "P \<in> WF_RELATION"
  shows "a \<rightarrow> P is CSP" 
apply(simp add:PrefixCSP_def)
apply(subst CSP_SemiR_closure,simp_all add:closure assms Prefix_CSP)
done

lemma Prefixed_design: 
  assumes "P \<in> WF_RELATION" "P is CSP" "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
  shows "a \<rightarrow> P = 
    `RHc (
                                     \<not>(($tr^\<langle>a\<rangle>=$tr\<acute>);\<not>CSP_Pre(P)) 
                                                 \<turnstile> 
              ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) ; CSP_Post(P)
                                                                                     )`"
proof -
have 0:  "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{wait \<down>} \<sharp> a" "{wait \<down>\<acute>} \<sharp> a" "{ok \<down>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a" "{tr \<down>} \<sharp> a""{tr \<down>\<acute>} \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
apply(subst CSP_Design)
apply(simp add: Prefixed_CSP 0 assms)  
apply(simp add:Prefixed_pre Prefixed_post assms 0 DesignD_form)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back
apply(simp add:AndP_assoc[THEN sym])
apply(simp add:AndP_OrP_distl AndP_OrP_distr)
apply(subst AndP_comm) back back back
apply(simp add:AndP_contra)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm) back back back back back back back
apply(simp add:AndP_assoc[THEN sym])
done
qed

lemma Skipform2: "`SKIP` = `(\<not>$ok \<and> ($tr\<le>$tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref\<down>,ref\<down>\<acute>}\<^esub>)`"
proof - 
have a: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} 
        =REL_VAR - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}"
by(utp_poly_auto_tac)
have b:  "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} 
         =REL_VAR - {ref\<down>, ref\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}"
by(utp_poly_auto_tac)
show ?thesis
apply(simp add:Skip_expansion SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "ref"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure) back back back
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) back back back
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing defined closure) back back back
apply(subst a)
apply(subst b)
apply(utp_poly_auto_tac)
done
qed

lemma Skip_right: 
  assumes "P \<in> WF_RELATION" "P \<in> REL"
  shows "`P ; SKIP` = `(P\<^sup>f ; ($tr \<le> $tr\<acute>)) \<or> (P\<^sup>t[true/wait \<acute>] \<and> $ok\<acute> \<and> $wait\<acute> ) \<or> ((\<exists> ref \<acute>. (P\<^sup>t[false/wait \<acute>])) \<and> $ok\<acute> \<and> \<not>$wait\<acute>)`"
proof-
have 0:  "D\<^sub>1 - out (REL_VAR - {ref\<down>, ref\<down>\<acute>}) - {ref\<down>\<acute>} = {}" by(utp_poly_auto_tac)
have "`P ; SKIP` = `
     (P \<and> \<not>$ok\<acute>) ; ($tr \<le> $tr\<acute>) \<or>
     (P \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (P \<and> $ok\<acute> \<and> \<not> $wait\<acute>) ; II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>`"
apply(simp add:Skipform2 SemiR_OrP_distl OrP_excluded_middle)
apply(simp add: SemiR_AndP_right_precond typing closure defined unrest urename AndP_assoc[THEN sym])
done
also have "... = `
     (P\<^sup>f \<and> \<not>$ok\<acute>) ; ($tr \<le> $tr\<acute>) \<or>
     (P\<^sup>t[true/wait\<acute>] \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (P\<^sup>t[false/wait\<acute>] \<and> $ok\<acute> \<and> \<not> $wait\<acute>) ; II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>`"
proof -
have a: "`P \<and> \<not>$ok\<acute>` = `P\<^sup>f \<and> \<not>$ok\<acute>`" by(utp_poly_auto_tac)
have b: "`P \<and> $ok\<acute> \<and> $wait\<acute>`=`P\<^sup>t[true/wait\<acute>] \<and> $ok\<acute> \<and> $wait\<acute>`" by(utp_poly_auto_tac)
have c: "`P \<and> $ok\<acute> \<and> \<not> $wait\<acute>` = `P\<^sup>t[false/wait\<acute>] \<and> $ok\<acute> \<and> \<not> $wait\<acute>`" by(utp_poly_auto_tac)
show ?thesis
apply(subst a)
apply(subst b)
apply(subst c)
apply(simp)
done
qed
also have "... = `
     P\<^sup>f ;(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (P\<^sup>t[true/wait\<acute>] \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (\<exists>ref\<acute>\<acute> . (P\<^sup>t[false/wait\<acute>] \<and> $ok\<acute> \<and> \<not> $wait\<acute>)[$ref\<acute>\<acute>/ref\<acute>])`"
apply(simp add:SemiR_AndP_right_precond closure typing defined urename)
apply(subst SemiR_extract_variable_id[of "ref\<down>"]) back
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:usubst typing defined closure)
apply(subst ExistsP_SemiR_NON_REL_VAR_expand2[THEN sym])
apply(simp_all add:typing closure defined unrest)
apply(subst SemiR_SkipRA_right)
apply(simp add:typing closure defined unrest)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(simp_all add:typing closure defined unrest)
apply(subst 0)
apply(simp_all add:typing closure defined unrest)
apply(simp add:typing closure defined erasure)
done
also have" ... = `
     (P\<^sup>f ; ($tr \<le> $tr\<acute>)) \<or>
     (P\<^sup>t[true/wait\<acute>] \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (\<exists>ref\<acute> . (P\<^sup>t[false/wait\<acute>] \<and> $ok\<acute> \<and> \<not> $wait\<acute>))`"
proof -
have a: " (\<exists>\<^sub>p {ref\<down>\<acute>\<acute>} . `(P[true/ok\<acute>][false/wait\<acute>] \<and> $ok\<acute> \<and> \<not> $wait\<acute>)[$ref\<acute>\<acute>/ref\<acute>]`) =
     (\<exists>\<^sub>p {ref\<down>\<acute>} . `P[true/ok\<acute>][false/wait\<acute>] \<and> $ok\<acute> \<and> \<not> $wait\<acute>`)"
apply(simp add:usubst typing defined closure)
apply(simp add:unrest typing defined closure ExistsP_AndP_expand1[THEN sym])
apply(subst ExistsP_SubstP_rename[of "ref\<down>\<acute>\<acute>"],simp_all add:typing defined closure assms unrest) back
apply(simp add:erasure typing closure defined)
done
show ?thesis
apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok\<down>}"],simp_all add:closure typing defined unrest assms)
apply (smt PVAR_VAR_pvdash a)
done
qed
finally show ?thesis 
by(subst ExistsP_AndP_expand1,simp_all add:closure typing defined unrest)
qed

lemma DesignREA_form2:  "`RHc( P \<turnstile> Q)` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(\<not>P)) \<or> ($ok \<and> \<not>$wait \<and> \<not>R2(\<not>P) \<and> R2(Q) \<and> $ok\<acute>)`"
apply(simp add:DesignREA_form)
apply(utp_poly_auto_tac)
done

lemma DesignREA_refine:
assumes 
    "`\<not>A` \<sqsubseteq> `\<not>C`"
    "`A \<Rightarrow> B` \<sqsubseteq> `D`"
shows"`RHc (A \<turnstile> B)` \<sqsubseteq> `RHc (C \<turnstile> D)`"
proof -
have 1: " `(\<not> A \<or> (B \<and> $ok\<acute>))` \<sqsubseteq> `(D \<and> $ok\<acute>)`"
proof -
  have "`(\<not> A \<or> (B \<and> $ok\<acute>))` = `((\<not> A \<and> ($ok\<acute> \<or> \<not>$ok\<acute>)) \<or> (B \<and> $ok\<acute>))`"
    by(simp add: OrP_excluded_middle)
  hence 1: "`(\<not> A \<or> (B \<and> $ok\<acute>))` = `((\<not> A \<or> B) \<and> $ok\<acute>) \<or> (\<not> A \<and> \<not>$ok\<acute>)`"
    apply(simp add:AndP_OrP_distl)
    apply(subst OrP_comm)
    apply(simp add:OrP_assoc[THEN sym])
    apply(subst AndP_OrP_distr[THEN sym])
    apply(subst OrP_comm)
    apply(simp)
    done
  have 2: "`(\<not> A \<or> (B \<and> $ok\<acute>))` \<sqsubseteq>`((\<not> A \<or> B) \<and> $ok\<acute>)`" "`((\<not> A \<or> B) \<and> $ok\<acute>)` \<sqsubseteq> `D \<and> $ok\<acute>`"
  apply(subst 1)
  apply (metis OrP_ref)
  apply(subst AndP_mono_refine)
  apply (metis ImpliesP_def assms(2))
  apply(simp_all add:eq_iff)
  done
  from 2 show ?thesis
  by (smt dual_order.trans)
qed
from 1 have 0: 
  "`R2(B) \<and> $ok\<acute>` = `R2(B \<and> $ok\<acute>)`"
  "`R2(D) \<and> $ok\<acute>` = `R2(D \<and> $ok\<acute>)`" 
  "`(\<not> A \<or> (B \<and> $ok\<acute>))` \<sqsubseteq> `(\<not> C \<or> (D \<and> $ok\<acute>))`" 
apply(simp_all add:R2_def R2s_def usubst typing defined closure R1_extend_AndP)
apply(subst OrP_refine)
apply (metis AndP_OrP_absorb RefineP_seperation assms(1))
apply(simp)
apply(simp)
done
from 0 show ?thesis
apply(simp add:DesignREA_form)
apply(subst OrP_mono_refine)
apply (metis AndP_idem RefP_AndP)
apply(subst OrP_mono_refine)
apply (metis eq_iff)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_mono_refine)
apply(metis eq_iff)
apply(subst AndP_mono_refine)
apply(metis eq_iff)
apply(simp add:R2_OrP[THEN sym])
apply(subst R2_monotonic)
apply(simp)
apply(simp)
done
qed

lemma aid2:
assumes 
  "NON_REL_VAR\<sharp> a" 
  "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>} \<sharp> a"
  "`P \<Rightarrow> Q` \<sqsubseteq> `((a \<notin> $ref\<acute>) \<and> ($tr\<acute> = $tr)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
shows "`RHc(P \<turnstile> Q)` \<sqsubseteq> `@a`"
apply(simp add:assms Prefix_design)
apply(subst DesignREA_refine)
apply(simp add:R2s_def usubst typing defined closure)
apply (metis RefineP_FalseP_refine)
apply (metis PVAR_VAR_pvdash assms(3))
apply(simp)
done

lemma aid3:
  assumes "`a \<Rightarrow> b` \<sqsubseteq> `c`"
  shows "`c \<Rightarrow> b` \<sqsubseteq> `a`"
proof -
  have "`(a \<Rightarrow> b) \<and> a` \<sqsubseteq> `c \<and> a`"
    by (metis AndP_mono_refine assms eq_iff)
  hence "`b \<and> a` \<sqsubseteq> `c \<and> a`"
    by (metis AndP_comm ImpliesP_AndP_pre utp_pred_simps(13) utp_pred_simps(7))  
  hence "`b` \<sqsubseteq> `c \<and> a`"
    by (metis RefineP_seperation)
  hence 1: "`b` \<sqsubseteq> `a \<and> c`"
    by (metis AndP_comm)
  hence "`b \<and> c` \<sqsubseteq> `a \<and> c`"
    by (metis AndP_refines_2 RefineP_seperation_refine dual_order.refl)
  hence "`(c \<Rightarrow> b) \<and> c` \<sqsubseteq> `a \<and> c`"
    by (metis "1" AndP_assoc AndP_comm AndP_idem RefineP_seperation RefineP_seperation_refine SemiR_spec_refine)
  hence "`(c \<Rightarrow> b)` \<sqsubseteq> `a`"
    by (metis "1" AndP_comm SemiR_spec_refine)
  thus ?thesis .
qed

lemma aid4:
assumes 
  "NON_REL_VAR\<sharp> a" 
  "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>} \<sharp> a"
  "`(((a \<notin> $ref\<acute>) \<and> ($tr\<acute> = $tr)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)) \<Rightarrow> Q` \<sqsubseteq> `P`"
shows "`RHc(P \<turnstile> Q)` \<sqsubseteq> `@a`"
apply(subst aid2)
apply(simp_all add:assms)
apply(subst aid3)
apply (metis (hide_lams, no_types) PVAR_VAR_pvdash assms(3))
apply(simp)
done

lemma aid5:
assumes 
  "NON_REL_VAR\<sharp> a" 
  "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>} \<sharp> a"
  "D\<^sub>2 \<sharp> Q"
shows "`RHc((CSP_Post(@a) \<Rightarrow> Q) \<turnstile> Q)` \<sqsubseteq> `@a`"
proof - 
have 0: "{ok\<down>, wait\<down>, ok\<down>\<acute>} \<sharp> a"
proof - have 1: "{ok\<down>, wait\<down>, ok\<down>\<acute>} \<subseteq> {tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>}" 
by (metis doubleton_eq_iff subset_insertI subset_insertI2)
show ?thesis
by (smt "1" UNREST_PEXPR_subset assms(2))
qed
show ?thesis
apply(subst aid4)
apply(simp_all add:assms)
apply(subst Prefix_post)
apply(simp add:0)
apply (metis (lifting, no_types) AndP_idem PVAR_VAR_pvdash RefP_AndP)
done
qed

definition CSP4:: "'a upred \<Rightarrow> 'a upred" where
"CSP4 P = `P;SKIP`"

lemma CSP_Pre_DesignREA:
  assumes "{ok\<down>}\<sharp>A" "{ok\<down>\<acute>}\<sharp>A" "{wait\<down>}\<sharp>A" "`\<not>A` is R2"
  shows "`CSP_Pre(RHc( A \<turnstile> B))` = `A`"
proof -
have "`CSP_Pre(RHc( A \<turnstile> B))` = `\<not>(R2(\<not>A))`"
apply(simp add:DesignREA_form CSP_Pre_def usubst typing defined closure R2_def R1_def R2s_def)
apply(subst SubstP_twice_3) back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back back back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3)
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back back
apply(simp_all add:unrest typing defined closure)
apply(simp add:usubst typing defined closure)
apply(simp add:SubstP_VarP_single_UNREST assms demorgan2 ImpliesP_def)
done
also have "... = A"
by (metis NotP_NotP assms(4) is_healthy_def)
finally show ?thesis .
qed

lemma CSP_Post_DesignREA:
  assumes "{ok\<down>}\<sharp>`A\<Rightarrow>B`" "{ok\<down>\<acute>}\<sharp>`A\<Rightarrow>B`" "{wait\<down>}\<sharp>`A\<Rightarrow>B`" "`A \<Rightarrow> B` is R2"
  shows"`CSP_Post(RHc( A \<turnstile> B))` = `A \<Rightarrow> B`"
proof -
have "`CSP_Post(RHc( A \<turnstile> B))` = `R1(CSP_Post(R2s(A \<Rightarrow> B)))`"
by(simp add:DesignREA_form CSP_Post_def usubst typing defined closure R2_def R1_def R2s_def AndP_OrP_distr[THEN sym] ImpliesP_def)
also have "... = `R2(CSP_Post(A \<Rightarrow> B))`"
apply(simp add:CSP_Post_def R2s_def)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3)
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(simp add:usubst typing defined closure R2_def R2s_def)
done
also have "... = `R2(A \<Rightarrow> B)`"
by(simp add:CSP_Post_def SubstP_VarP_single_UNREST assms)
finally show ?thesis
by (metis Healthy_simp assms(4))
qed

lemma R2_CondR_closure:
  assumes "P is R2" "Q is R2" "b is R2s"
  shows "`P \<lhd> b \<rhd> Q` is R2"
by(metis assms is_healthy_def R2_CondR)

lemma "`A \<and> $wait\<acute> ` = `A[true/wait\<acute>] \<and> $wait\<acute> `"
by (metis AndP_comm PVarPE_PSubstPE pvaux_MkPVAR pvaux_pvdash)


lemma CSP4_form:
assumes "P is CSP" "P is CSP4" "P \<in> REL"
shows 
  "`CSP_Pre(P)` = `\<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))`"
  "`CSP_Post(P)` = `\<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<Rightarrow> (CSP_Post(P)[true/wait\<acute>]  \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]))`"
proof -
have 1: "`P` = `P;SKIP`" 
  by(metis assms(2) is_healthy_def CSP4_def)
have "`P` = `(
     (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2 ((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))) \<or>
     ($ok \<and> \<not> $wait \<and> R2 ((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<and>  $ok\<acute>) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)[true/wait\<acute>]) \<and> $wait\<acute> \<and> $ok\<acute>) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]) \<and> \<not> $wait\<acute> \<and> $ok\<acute>)
     )`"
apply(subst CSP_Design, simp_all add:assms(1) DesignREA_form)
apply(subst 1, simp add:Skip_right assms(3) CSP_Pre_def usubst typing defined closure)
apply(subst 1, simp add:Skip_right assms(3) CSP_Post_def usubst typing defined closure) back
apply(simp add:SubstP_SemiR_right SubstP_SemiR_left SubstP_ExistsP typing defined closure unrest)
apply(simp add:usubst typing defined closure R2_OrP)
apply(simp add:AndP_OrP_distl AndP_OrP_distr)
apply(simp add:R2_def R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2_def[THEN sym] AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(simp add:R2s_def usubst typing defined closure)
apply(subst SubstP_twice_3) back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_1)
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3) back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3) back back back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_1)
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3) back back back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back back back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(simp add:usubst typing defined closure)
done
also have "... =  `(
     (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2 ((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)[true/wait\<acute>]) \<and> $wait\<acute> \<and> $ok\<acute>) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]) \<and> \<not> $wait\<acute> \<and> $ok\<acute>)
     )`"
by(utp_poly_auto_tac)
also have  "... =  `(
     (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2 ((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)[true/wait\<acute>]  \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]))\<and> $ok\<acute>)
     )`"
apply(simp add:R2_CondR R2s_def usubst typing defined closure)
apply(simp add:CondR_def AndP_OrP_distl AndP_OrP_distr)
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm) back back back back back back back
apply(subst AndP_assoc) back back back back back back
apply(subst AndP_comm) back back back back back back back back back back back
apply(simp)
done
also have "... = `RHc(\<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<turnstile> (CSP_Post(P)[true/wait\<acute>]  \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>])))`"
by(simp add: DesignREA_form)
finally have 2: "P = `RHc(\<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<turnstile> (CSP_Post(P)[true/wait\<acute>]  \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>])))`" .
have 3: "P is R2"
by (metis CSP_is_RHc RHc_is_R2 assms(1))
have a: "`\<not> CSP_Pre(P)` is R2"
by(metis 3 CSP_Pre_R2)
have 4: "`CSP_Post(P)` = `R2(CSP_Post(P))`"
by (metis is_healthy_def 3 CSP_Post_R2)
have b: "`CSP_Post(P)[true/wait\<acute>]` is R2"
apply(simp add: is_healthy_def R2_def R2s_def)
apply(subst 4) back
apply(subst SubstP_twice_3, simp_all add:closure typing defined unrest)
apply(subst SubstP_twice_3, simp_all add:closure typing defined unrest)back
apply(simp add:usubst typing closure defined R2_def R2s_def R1_def)
done
have c: "`\<exists> ref\<acute> . CSP_Post(P)[false/wait\<acute>]` is R2"
apply(simp add: is_healthy_def R2_def R2s_def)
apply(subst 4) back
apply(simp add:closure typing defined unrest SubstP_ExistsP)
apply(subst SubstP_twice_3, simp_all add:closure typing defined unrest)
apply(subst SubstP_twice_3, simp_all add:closure typing defined unrest)back
apply(simp add:usubst typing closure defined R2_def R2s_def R1_def)
apply(simp add:unrest typing closure defined ExistsP_AndP_expand1)
done
show "CSP_Pre(P) = `\<not> ((\<not> CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))`"
apply(subst 2)
apply(subst CSP_Pre_DesignREA)
apply(simp add:typing defined closure unrest CSP_Pre_def)
apply(simp add:typing defined closure unrest CSP_Pre_def)
apply(simp add:typing defined closure unrest CSP_Pre_def)
apply(simp add:typing defined closure unrest)
apply(subst R2_SemiR_closure)
apply(simp_all add:typing closure defined assms a)
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure)
done
show  "`CSP_Post(P)` = `\<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<Rightarrow> (CSP_Post(P)[true/wait\<acute>]  \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]))`"
apply(subst 2)
apply(subst CSP_Post_DesignREA)
apply(simp add:typing closure defined unrest CSP_Post_def CSP_Pre_def)
apply(simp add:typing closure defined unrest CSP_Post_def CSP_Pre_def)
apply(simp add:typing closure defined unrest CSP_Post_def CSP_Pre_def)
apply(simp_all add:typing closure defined unrest ImpliesP_def)
apply(subst R2_OrP_closure)
apply(subst R2_SemiR_closure)
apply(simp_all add:a usubst typing defined closure assms)
apply(simp add:a is_healthy_def R2_def R2s_def R1_def usubst typing defined closure assms)
apply(subst R2_CondR_closure)
apply (metis PVAR_VAR_pvdash b)
apply (metis PVAR_VAR_pvdash c)
apply(simp_all add:is_healthy_def R2s_def usubst typing defined closure)
done
qed

lemma CondR_form: "`P \<lhd> $wait\<acute> \<rhd> Q` = `P[true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (Q[false/wait\<acute>])`"
by(utp_poly_auto_tac)


lemma CSP4_form2:
assumes "P is CSP"  "P \<in> REL"
  "`CSP_Pre(P)` = `\<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))`"
  "`CSP_Post(P)` = `\<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<Rightarrow> (CSP_Post(P)[true/wait\<acute>]  \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]))`"
shows 
"P is CSP4"
proof -
  have 0: "D\<^sub>1 - out (REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}) = {ref\<down>\<acute>,ok\<down>\<acute>,wait\<down>\<acute>}"
    apply(utp_poly_auto_tac)
    apply(simp_all add:out_vars_diff)
    apply(simp_all add:typing defined closure unrest)
    done
  have 1:" `$wait \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub>` = `II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and> $wait\<acute>`"
  apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure)
  apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure)back
  apply(utp_poly_auto_tac)
  done
  have 2:"` (\<not> $wait \<and> \<not> $wait\<acute> \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and> ($tr\<acute>=$tr))` =
          ` II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and> \<not> $wait\<acute>`"
  proof -
    have a: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} = REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}"
    by(utp_poly_auto_tac)
    show ?thesis
    apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing closure defined) back
    apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure defined) back
    apply(subst a)
    apply(utp_poly_auto_tac)
    done
  qed
  have 3: "{ref\<down>\<acute>, ok\<down>\<acute>, wait\<down>\<acute>} \<sharp> `P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>]`"
    proof-
      have " `P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>]` = `CSP_Post(P)[false/wait\<acute>]`"
      by(simp add:CSP_Post_def)
      hence a: "`P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>]` = `(\<not> (\<not> CSP_Pre(P) ; ($tr \<le> $tr\<acute>)) \<Rightarrow> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]))`"
        apply(simp)        
        apply(subst assms(4))
        apply(simp_all add:typing defined closure usubst)
        apply(subst SubstP_ExistsP,simp_all add:typing defined closure unrest)
        apply(subst SubstP_twice_1,simp_all add:typing defined closure usubst)
        apply(subst SubstP_SemiR_right,simp_all add:typing defined closure unrest)
        apply(simp add:typing defined closure usubst)
        done
      show ?thesis
        apply(subst a)
        apply(rule unrest)
        apply(simp_all add:typing defined closure unrest)
        apply(rule unrest)
        apply(rule unrest,simp_all add:typing defined closure unrest)
        apply(simp add:CSP_Post_def)
        apply(rule unrest,simp_all add:typing defined closure unrest)
        apply(rule unrest,simp_all add:typing defined closure unrest)
        apply(rule unrest,simp_all add:typing defined closure unrest)
        apply (metis Diff_cancel Diff_insert UNREST_empty)
        done
qed
have "`P ; SKIP` = `RHc (CSP_Pre (P) \<turnstile>
         ((CSP_Post(P) ; II\<^bsub>REL_VAR - OKAY\<^esub>) \<and> $wait\<acute>) \<or>
         (CSP_Post(P) ; (II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and> \<not>$wait\<acute>)))`"
apply(subst Seq_comp_form)
apply(simp add:assms closure Skip_CSP)
apply(simp add:assms closure Skip_CSP)
apply(simp add:assms closure Skip_CSP)
apply(simp add:assms closure Skip_CSP)
apply(simp add:Skip_pre Skip_post)
apply(simp add:R2_def R1_def R2s_def usubst typing defined closure)
apply(subst assms(3)[THEN sym])
apply(simp add:CondR_def SemiR_OrP_distl)
apply(subst AndP_comm) back back
apply(simp add:AndP_assoc[THEN sym] tr_prefix_as_nil 1)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add:typing closure defined)
apply (smt "2" PVAR_VAR_pvdash)
done
also have "... = ` RHc (CSP_Pre(P) \<turnstile>
         ((CSP_Post(P) ; II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub>) \<lhd> $wait\<acute> \<rhd>
         (CSP_Post(P) ; II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>)))`"
apply(subst AndP_comm)
apply(subst SemiR_AndP_right_postcond)
apply(simp add:closure)
apply(subst AndP_comm)back
apply(simp add:CondR_def)
done
also have "... =`RHc (CSP_Pre (P) \<turnstile>
         ((P[true/ok\<acute>][true/ok][false/wait][true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> 
         (P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>] ;
         (\<not>$wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub>)))))`"
proof-
have a: " D\<^sub>1 - out (REL_VAR - {ok\<down>, ok\<down>\<acute>}) - {wait\<down>} - {ok\<down>} - {ok\<down>\<acute>} = {}"
by(utp_poly_auto_tac)
have b: "`false = $wait` = `\<not>$wait`" 
by(utp_poly_auto_tac)
have c: "`P[true/ok\<acute>][true/ok][false/wait] \<and> \<not> $wait\<acute>` = 
        `P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>] \<and> \<not> $wait\<acute>`"
by(utp_poly_auto_tac)
show ?thesis
apply(subst CondR_form)
apply(subst SemiR_SkipRA_right)
apply(simp_all add:typing defined closure CSP_Post_def unrest)
apply(rule unrest) defer 
apply(rule unrest) defer 
apply(rule unrest) defer 
apply(subst a)
apply(simp_all add:unrest typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure)
apply(subst SubstP_SemiR_right, simp_all add:typing defined closure unrest)
apply(simp add:typing closure defined usubst)
apply(subst b)
apply(simp add: SemiR_AndP_right_precond typing defined closure urename)
apply (smt PVAR_VAR_pvdash c)
done
qed
also have "... = `RHc (CSP_Pre (P) \<turnstile> (P[true/ok\<acute>][true/ok][false/wait][true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>])))`"
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait\<down>}"])
apply(simp_all add:typing defined closure unrest)
apply(rule closure)apply(rule closure)apply(rule closure)apply(rule closure)defer 
apply(simp_all add:typing defined closure unrest) defer 
apply(subst SemiR_SkipRA_right)
apply(simp_all add:typing defined closure)
apply(subst 0)
apply (metis (hide_lams, no_types) "3" PVAR_VAR_pvdash)
apply(metis assms(2))
apply(subst UNREST_subset[of "-(REL_VAR -{ref\<down>,ref\<down>\<acute>}-{ok\<down>,ok\<down>\<acute>}-{wait\<down>,wait\<down>\<acute>})"])
apply(subst UNREST_SkipRA, simp)
apply(utp_poly_auto_tac)
done
also have "... = `RHc (CSP_Pre (P) \<turnstile> (P[true/ok\<acute>][true/ok][false/wait] \<lhd> $wait\<acute> \<rhd> (P[true/ok\<acute>][true/ok][false/wait])))`"
proof - have a: "`P[true/ok\<acute>][true/ok][false/wait][true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>])` = `P[true/ok\<acute>][true/ok][false/wait] \<lhd> $wait\<acute> \<rhd> (P[true/ok\<acute>][true/ok][false/wait])`"
  apply(subst CondR_def)
  apply(subst CondR_def)
  apply(utp_poly_auto_tac)
  done
  show ?thesis
    by(subst a,simp)
qed
also have "... = `RHc (CSP_Pre (P) \<turnstile> CSP_Post(P))`"
by (metis CSP_Post_def CondR_idem)
also have "... = `P`"
by (metis CSP_Design assms(1))
finally show ?thesis
by(simp add:is_healthy_def CSP4_def)
qed


lemma CSP4_Design_form:
  assumes "P is CSP" "P is CSP4" "P \<in> REL"
  shows "P = `RHc(
  \<not>((\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>))
  \<turnstile>
  (CSP_Post(P)[true/wait\<acute>]  \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>. CSP_Post(P)[false/wait\<acute>]))
  )`"
apply(subst CSP_Design)
apply(simp add:assms(1))
apply(subst CSP4_form,simp_all add:assms)
apply(subst CSP4_form(2),simp_all add:assms)
apply(simp add:DesignD_form ImpliesP_def)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back
apply(simp add:AndP_assoc[THEN sym] AndP_OrP_distl)
apply(subst AndP_comm) back back back
apply(simp add:AndP_contra)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back
apply(simp add:AndP_assoc[THEN sym])
done

lemma hand:
  assumes "`P` \<sqsubseteq> `a \<and> R`"
  shows"`P \<or> (\<not>a \<and> Q)` \<sqsubseteq> `a \<and> R`"
by (metis AndP_OrP_absorb RefineP_seperation assms)

lemma hand2:
  assumes "`P \<or> Q` \<sqsubseteq> `R`"
  shows "`P \<or> (a \<and> Q)` \<sqsubseteq> `a \<and> R`"
by (metis AndP_OrP_distl OrP_AndP_distl OrP_assoc RefP_OrP assms)

lemma hand3:
  assumes "`P` \<sqsubseteq> `\<not>a \<and> R`"
  shows"`P \<or> (a \<and> Q)` \<sqsubseteq> `\<not>a \<and> R`"
by (metis AndP_OrP_absorb RefineP_seperation assms)

lemma CSP4_Design_refine:
assumes 
  "P is CSP" "Q is CSP" "P is CSP4" "Q is CSP4" "P \<in> REL" "Q \<in> REL" 
  "A = CSP_Pre(P)" "B = CSP_Post(P)" "C= CSP_Pre(Q)" "D = CSP_Post(Q)"
  "`((\<not> A) ; ($tr \<le> $tr\<acute>))` \<sqsubseteq> `((\<not> C) ; ($tr \<le> $tr\<acute>))`"
  "`(((\<not> A) ; ($tr \<le> $tr\<acute>)) \<or> B[true/wait\<acute>])` \<sqsubseteq> `D[true/wait\<acute>]`"
  "`(((\<not> A) ; ($tr \<le> $tr\<acute>)) \<or> (\<exists> ref\<acute> . B[false/wait\<acute>]))` \<sqsubseteq> `(\<exists> ref\<acute> . D[false/wait\<acute>])`"
shows
 "P \<sqsubseteq> Q"
apply(subst CSP4_Design_form,simp_all add:assms)
apply(subst CSP4_Design_form,simp_all add:assms) back back back back back back back back back back back back back back back back back
apply(subst DesignREA_refine)
apply(simp_all add:CondR_def ImpliesP_def OrP_assoc[THEN sym])
apply (metis assms(11) assms(7) assms(9))
apply(simp_all add: assms(7)[THEN sym] assms(8)[THEN sym] assms(9)[THEN sym] assms(10)[THEN sym]) 
apply(subst OrP_refine)
apply(subst OrP_assoc)
apply(subst hand)
apply(subst hand2)
apply (metis PVAR_VAR_pvdash assms(12))
apply(simp_all)
apply(subst OrP_comm) back
apply(subst OrP_assoc)
apply(subst hand3)
apply(subst hand2)
apply (metis (hide_lams, no_types) PVAR_VAR_pvdash assms(13)) 
apply(simp)
done

lemma Prefix_CSP4:
  assumes 
    "NON_REL_VAR \<sharp> a"
    "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>,wait\<down>\<acute>,ref\<down>\<acute>} \<sharp> a" 
  shows "`@a` is CSP4"
proof -
have 1:" {tr\<down>, tr\<down>\<acute>, ok\<down>\<acute>} \<sharp> a" 
    by(auto intro: assms UNREST_PEXPR_subset)
have 2:" {ok\<down>, wait\<down>, ok\<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
have 3: "{wait\<down>\<acute>}\<sharp>a"
    by(auto intro: assms UNREST_PEXPR_subset)
have 4: "{ref \<down>\<acute>}\<sharp>a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
apply(subst CSP4_form2)
apply(subst Prefix_CSP)
apply(simp_all add:1 typing defined closure assms)
apply(simp_all add:Prefix_pre)
apply(subst Prefix_post)
apply(simp add:2) 
apply(subst Prefix_post)
apply(simp add:2) 
apply(subst Prefix_post)
apply(simp add:2) 
apply(simp add:usubst typing defined closure 3 PSubstPE_VarP_single_UNREST PVAR_VAR_pvdash)
apply(subst ExistsP_ident)
apply(simp_all add:typing defined closure unrest 4)
done
qed


lemma Skip_post2: 
  "`\<not>$wait \<and> R2(CSP_Post(SKIP))` = `\<not> $wait \<and>     II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>`"
proof-
have 0: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} = REL_VAR - {ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}"
by(utp_poly_auto_tac)
show ?thesis
apply(subst Skip_post)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure defined)back
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing closure defined)back
apply(subst 0)
apply(simp add:R2_def R2s_def usubst typing defined closure R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil)
apply(utp_poly_auto_tac)
done
qed

lemma External_CSP4:
  assumes "P is CSP4" "Q is CSP4" "P is CSP" "Q is CSP" "P \<in> REL" "Q \<in> REL"
  shows "`P \<box> Q` is CSP4"
apply(simp add:is_healthy_def CSP4_def)
apply(subst Seq_comp_form)
apply(simp_all add:assms External_CSP Skip_CSP closure)
apply(simp add:External_pre assms External_post Skip_pre)
apply(subst CondR_def) back back
apply(simp add:SemiR_OrP_distl)
apply(subst Skip_post2)
apply(simp add:R2_def R2s_def R1_def usubst typing defined closure)
apply(simp add:SemiR_AndP_right_precond typing closure defined urename)
apply(subst SemiR_SkipRA_right) defer defer 
apply(subst SemiR_SkipRA_right) defer defer 
apply(subst AndP_OrP_distl[THEN sym])
apply(subst OrP_excluded_middle)
apply(simp)
apply(subst CSP_Design[of "`P\<box>Q`"])
apply(simp add:assms External_CSP)
apply(simp add:External_pre External_post assms)
apply(simp add:demorgan2 demorgan1 SemiR_OrP_distr)
apply(subst CSP4_form(1)[THEN sym],simp_all add:assms)
apply(subst CSP4_form(1)[THEN sym],simp_all add:assms)
apply(simp_all add:typing closure defined unrest)
apply(subst UNREST_subset[of "{ok\<down>\<acute>}"])
apply(simp add:CSP_Pre_def CSP_Post_def typing closure defined unrest)defer
apply(simp)
apply(subst UNREST_subset[of "{ok\<down>\<acute>,ref\<down>\<acute>}"])
apply(subst CSP4_form(1),simp_all add:assms)
apply(subst CSP4_form(1),simp_all add:assms) back
apply(simp add:CondR_def)
apply(subst AndP_comm) back back back back back
apply(simp add:demorgan1 demorgan2 AndP_OrP_distl AndP_OrP_distr AndP_assoc OrP_assoc)
apply(simp add:AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc)
apply(subst AndP_comm) back back
apply(simp add:AndP_contra)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst OrP_comm) back back back back
apply(subst AndP_comm) back back
apply(subst OrP_AndP_absorb)
apply(subst OrP_assoc) back back
apply(subst OrP_comm) back back 
apply(subst AndP_comm) back
apply(subst OrP_AndP_absorb)
apply(simp add:AndP_OrP_distl)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest)
apply(subst CSP4_form(2))
apply(simp_all add:assms ImpliesP_def CondR_def OrP_assoc[THEN sym] AndP_OrP_distl)
apply(simp add:AndP_assoc)
apply(subst AndP_comm) back
apply(simp add:AndP_contra)
apply(rule unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(simp add:CSP_Post_def)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(subst UNREST_subset[of "{}"])
apply(simp_all add:typing closure defined unrest)
apply(utp_poly_auto_tac) 
apply(subst CSP4_form(2))
apply(simp_all add:assms ImpliesP_def CondR_def OrP_assoc[THEN sym] AndP_OrP_distl)
apply(simp add:AndP_assoc)
apply(subst AndP_comm) back
apply(simp add:AndP_contra)
apply(rule unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(simp add:CSP_Post_def)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest,simp_all add:typing defined closure unrest)
apply(rule unrest,simp_all add:typing defined closure unrest) 
apply(subst UNREST_subset[of "{}"])
apply(simp_all add:typing closure defined unrest)
apply(utp_poly_auto_tac)
apply(utp_poly_auto_tac)
apply(utp_poly_auto_tac)
done

lemma 
  assumes   "NON_REL_VAR \<sharp> a"
    "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>,wait\<down>\<acute>,ref\<down>\<acute>} \<sharp> a" 
  shows "`@a \<box> SKIP` \<sqsubseteq> `SKIP`"
proof-
have 1:" {tr\<down>, tr\<down>\<acute>, ok\<down>\<acute>} \<sharp> a" 
    by(auto intro: assms UNREST_PEXPR_subset)
have 3:" {ok\<down>, wait\<down>, ok\<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
have 5: "{wait\<down>\<acute>}\<sharp>a"
    by(auto intro: assms UNREST_PEXPR_subset)
have a: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} =
    REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}"
by(utp_poly_auto_tac)
have 4: "`($tr\<acute> =$tr) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>` = `II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>}\<^esub>`"
apply(subst SkipRA_unfold_aux_ty[of "tr"]) back
apply(simp_all add:typing closure defined)
apply(metis a)
done
have 6: "in(REL_VAR) = D\<^sub>0"
by (metis in_out_UNDASHED_DASHED(1) in_out_UNDASHED_DASHED(3) in_vars_union sup_bot_right)

have 2: "`SKIP;SKIP` = `SKIP`"
proof -
have "`SKIP;SKIP` = `
 RHc (true \<turnstile>
         (($tr\<acute>=$tr) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and> \<not> $wait\<acute>) ;
         (($tr\<acute> = $tr) \<and>
          II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and>  \<not> $wait\<acute>))`"
apply(subst Seq_comp_form,simp_all add:closure typing defined Skip_CSP)
apply(simp add:Skip_pre Skip_post)
apply(simp add:R2s_def R2_def R1_def usubst typing defined closure)
apply(simp add:CondR_def AndP_assoc[THEN sym] OrP_assoc[THEN sym] SemiR_OrP_distl)
apply(simp add: SemiR_AndP_right_precond typing defined closure urename)
apply(subst AndP_comm) back back
apply(subst AndP_comm) back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc)
apply(simp add:AndP_contra)
apply(subst AndP_comm) back
apply(simp add:AndP_assoc[THEN sym])
 apply(subst AndP_comm) back back back back
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(simp add:tr_prefix_as_nil)
done
also have "... = `RHc(true \<turnstile> (II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>,ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>) ;
         (\<not> $wait \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub> \<and>  \<not> $wait\<acute>))`"
apply(simp add:AndP_assoc 4)
apply(simp add:AndP_assoc[THEN sym])
apply(subst SemiR_AndP_right_precond) back
apply(simp_all add:typing closure defined urename) 
done
also have "... = `RHc(true \<turnstile> (II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>,ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub> ;
         II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>) \<and>  \<not> $wait\<acute>)`"
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait \<down>}"])
apply(simp_all add:typing closure defined unrest)
apply(subst UNREST_subset[of "-(REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>})"])
apply(subst UNREST_SkipRA,simp)
defer 
apply(rule unrest) back
apply(subst UNREST_subset[of "-(REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>})"])
apply(subst UNREST_SkipRA,simp) defer 
apply(simp add:typing closure defined unrest)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add:typing closure defined)
done
also have "... = `SKIP`"
apply(subst SemiR_SkipRA_left)
apply(simp_all add:typing closure defined unrest)
apply(subst UNREST_subset[of "-(REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>})"])
apply(subst UNREST_SkipRA,simp) defer 
apply(subst Skip_design)
apply(subst 4[THEN sym])
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst in_vars_diff)
apply(subst 6)
apply(simp add:typing closure defined)
apply (smt in_vars_def inf.orderI inf_bot_left inf_sup_aci(1) inf_sup_aci(2) insert_inter_insert)
done
finally show ?thesis . qed
show ?thesis
apply(subst CSP4_Design_refine)
apply(subst External_CSP)
apply(simp_all add:closure typing defined assms Skip_CSP)
apply(subst Prefix_CSP, simp_all add:1)
defer 
apply(simp add:CSP4_def is_healthy_def)
apply(simp add:2)
apply(subst External_pre,simp_all add:closure typing defined assms)
apply(simp add:Prefix_pre)
apply(subst External_pre,simp_all add:closure typing defined assms)
apply(subst External_post,simp_all add:closure typing defined assms)
apply(simp_all add:Prefix_pre Prefix_post 3 4 Skip_pre Skip_post)
apply(simp_all add:usubst typing defined closure 5 6 PSubstPE_VarP_single_UNREST PVAR_VAR_pvdash)
apply(simp add:RefineP_FalseP_refine)
apply(subst External_pre,simp_all add:closure typing defined assms)
apply(subst External_post,simp_all add:closure typing defined assms)
apply(simp_all add:Prefix_pre Prefix_post 3 4 Skip_pre Skip_post)
apply(simp_all add:usubst typing defined closure 5 6 PSubstPE_VarP_single_UNREST PVAR_VAR_pvdash)
apply(subst 4)
apply(simp add:ExistsP_OrP_dist)
apply(subst OrP_comm)
apply(simp add: OrP_ref)
apply(subst External_CSP4)
apply(simp_all add:assms Skip_CSP closure Prefix_CSP 1 Prefix_CSP4)
apply(simp add:is_healthy_def CSP4_def 2)
done
qed

lemma CSP_Pre_UNREST: 
  assumes "{ok\<down>,wait\<down>,ok\<down>\<acute>} \<sharp> `P`"
  shows "`CSP_Pre(P)` = `\<not>P`"
apply(simp add:CSP_Pre_def)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
done

lemma CSP_Post_UNREST: 
  assumes "{ok\<down>,wait\<down>,ok\<down>\<acute>} \<sharp> `P`"
  shows "`CSP_Post(P)` = `P`"
apply(simp add:CSP_Post_def)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
done

(* sorries from here *)

lemma R2_wait_false: "`R2(P[false/wait])` = `R2(P)[false/wait]`"
apply(simp add:R2_def R1_def usubst typing defined closure R2s_def)
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest)back
apply(simp add:usubst typing defined closure)
done

lemma foot6: "`R1(\<not>R1(P))` = `R1(\<not>P)`"by(utp_poly_auto_tac)
lemma foot7: "`\<not>R2s(P)` = `R2s(\<not>P)`"by(simp add:R2s_def usubst typing defined closure)

lemma CSP_Pre_R2_commute:
  "`\<not>CSP_Pre(R2(P))` = `R2(\<not>CSP_Pre(P))`"
apply(simp add:CSP_Pre_def R2_def foot7[THEN sym])
apply(simp add:R2_def[THEN sym] R2_wait_false R2_ok_true[THEN sym])
apply (metis PVAR_VAR_pvdash R2_ok'_false)
done

lemma CSP_Post_R1_commute:
  "`CSP_Post(R1(P))` = `R1(CSP_Post(P))`"
by(simp add:CSP_Post_def R1_def usubst typing defined closure)

lemma CSP_Post_R2_commute:
  "`CSP_Post(R2(P))` = `R2(CSP_Post(P))`"
apply(simp add:CSP_Post_def)
apply(simp add: R2_wait_false R2_ok_true[THEN sym])
apply (metis PVAR_VAR_pvdash R2_ok'_true)
done

lemma foot1: assumes "`P \<and> B` \<sqsubseteq> `A \<and> B`"
  shows "`P` \<sqsubseteq> `A \<and> B`"
by (metis RefineP_seperation assms)

lemma foot2:
  assumes"`P` \<sqsubseteq> `b \<and> Q`" "`P` \<sqsubseteq> `\<not>b \<and> R`" 
  shows "`P` \<sqsubseteq> `Q  \<lhd> b \<rhd> R`" 
  apply(simp add:CondR_def)
  apply(metis OrP_refine PVAR_VAR_pvdash assms(1) assms(2))
done

lemma foot3: assumes "`P` \<sqsubseteq> `A \<and> B`"
  shows "`P \<and> B` \<sqsubseteq> `A \<and> B`"
by (metis RefineP_seperation assms dual_order.refl)

lemma foot4: "`(x;($tr\<le>$tr\<acute>)) \<or> x` = `x;($tr\<le>$tr\<acute>)`"
proof-
have 0: "`x` = `x;II`" by simp
show ?thesis
apply(subst 0) back
apply(subst SemiR_OrP_distl[THEN sym])
apply (metis R1_SkipR_closure R1_by_refinement RefP_OrP)
done
qed

(*sorries from here *)

lemma foot5: 
assumes "x \<in> REL"
shows "`R1(x;($tr\<le>$tr\<acute>))` = `R1(x);($tr\<le>$tr\<acute>)`"
proof -
have 0: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr]` = `($tr\<acute>\<acute> \<le> $tr\<acute>)`"
sorry
show?thesis
apply(subst SemiR_extract_variable_ty[of "tr" "tr\<acute>\<acute>"],simp_all add:typing defined closure unrest  assms)
apply(subst SemiR_extract_variable_ty[of "tr" "tr\<acute>\<acute>"],simp_all add:typing defined closure unrest assms) back
apply(simp add:R1_def usubst typing defined closure 0)
apply(subst ExistsP_AndP_expand1,simp add:typing defined closure unrest)
(* false *)

sorry
qed
lemma
  assumes "P is CSP" "P is CSP4" "P \<in> REL"
          "A \<in> REL" "B \<in> REL" "{ok\<down>,wait\<down>,ok\<down>\<acute>}\<sharp>`A`" "{ok\<down>,wait\<down>,ok\<down>\<acute>}\<sharp>`B`" "`\<not>A` is R2" "`B` is R2"
          "`(\<not>A) ;($tr \<le> $tr\<acute>)` \<sqsubseteq> `(\<not>CSP_Pre(P)); ($tr \<le> $tr\<acute>)`" 
          "`(((\<not> A); ($tr \<le> $tr\<acute>)) \<or> B) \<sqsubseteq> (CSP_Post(P) \<and> $wait\<acute>)`"
          "`(((\<not> A); ($tr \<le> $tr\<acute>)) \<or> (\<exists> ref\<acute> .B))` \<sqsubseteq> `(\<exists> ref\<acute> . CSP_Post(P)) \<and> \<not> $wait\<acute>`"
  shows "`CSP4(RHc(A \<turnstile> B))` \<sqsubseteq> `P`" 
proof - 
have 1: "`((\<not> A[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][false/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) ;
     ($tr \<le> $tr\<acute>))` \<sqsubseteq>
    `(P[false/ok\<acute>][true/ok][false/wait] ; ($tr \<le> $tr\<acute>))`"
proof -
have a: "`P` = `R1(P)`" by (metis assms CSP_is_RHc RHc_is_R1 is_healthy_def)
  have "`(\<not>CSP_Pre(R2(\<not> A))) ;($tr \<le> $tr\<acute>)` \<sqsubseteq>
    `(\<not>CSP_Pre(P)); ($tr \<le> $tr\<acute>)`" 

apply(simp add: CSP_Pre_R2_commute)
apply(subst CSP_Pre_UNREST) back
apply(rule unrest)
apply(simp_all add:assms)
apply(metis assms is_healthy_def)
done
  thus ?thesis 
  apply(simp add:R2_def R2s_def R1_def CSP_Pre_def)
  apply(simp add:usubst typing defined closure)
  done
qed
have 2:"`(false = true)` = `false`" by(utp_poly_auto_tac)
have 3:"`(true = true)` = `true`" by(utp_poly_auto_tac)
have 6:"D\<^sub>1 - out (REL_VAR - {ok\<down>, ok\<down>\<acute>}) = {ok\<down>\<acute>}" 
apply(utp_poly_auto_tac)
apply(simp add:out_vars_diff typing closure defined)
done
have 8:  "`\<not> (\<not> R2(A) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((R2 (A \<Rightarrow> B) \<and> $wait\<acute>) \<or>
     (R2 (A \<Rightarrow> B) ;
     (\<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>)))` \<sqsubseteq>
    `CSP_Post(P)[true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute> . CSP_Post(P)[false/wait\<acute>])`"
proof-
have a: "`P` = `R1(P)`" by (metis assms CSP_is_RHc RHc_is_R1 is_healthy_def)
have b: "`$tr\<le>$tr\<acute>`=`R2($tr\<le>$tr\<acute>)`"
by(simp add:R2_def R2s_def usubst typing closure defined R1_def)
have c: "`((\<not> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>)) \<and> ($tr \<le> $tr\<acute>)` = `false`"

sorry
have d: "` R1 (CSP_Post(P)[true/wait\<acute>])` = `CSP_Post(P)[true/wait\<acute>]`"
apply(subst a) back
apply(subst CSP_Post_R1_commute)
apply(simp add:R1_def usubst typing defined closure)
done
from assms(11) have e: "`(((\<not> A); ($tr \<le> $tr\<acute>)) \<or> B) \<sqsubseteq> (CSP_Post(P)[true/wait\<acute>] \<and> $wait\<acute>)`"
by(utp_poly_auto_tac)
have f: "`R2(\<not>A)` = `\<not>A`" by(metis assms is_healthy_def)
have g: "`R2(B)` = `B`" by(metis assms is_healthy_def)
have h: "D\<^sub>1 - out (REL_VAR - {ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>}) = {ref\<down>\<acute>,ok\<down>\<acute>}" 
proof -
have x: "D\<^sub>1 = out(REL_VAR)"
by (metis Un_empty_left in_out_UNDASHED_DASHED(2) in_out_UNDASHED_DASHED(4) out_vars_union)
have y: "out({ref\<down>,ref\<down>\<acute>,ok\<down>,ok\<down>\<acute>}) = {ref\<down>\<acute>,ok\<down>\<acute>}" sorry
show ?thesis
by(simp add:out_vars_diff typing defined closure x[THEN sym] y)
qed
show ?thesis
apply(subst SemiR_AndP_right_precond,simp_all add:typing closure urename f)
apply(subst SemiR_extract_variable_id[of "ref\<down>"],simp_all add:typing defined unrest assms closure)back
apply(simp add:usubst typing defined closure)
apply(subst ExistsP_SemiR_NON_REL_VAR_expand2[THEN sym])
apply(simp_all add:typing closure defined unrest)
apply(subst SemiR_SkipRA_right)
apply(simp add:typing closure defined unrest) defer 
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst AndP_comm)
apply(subst AndP_comm) back
apply(subst CondR_def[THEN sym])
apply(subst foot2)
apply(subst AndP_comm)
apply(subst foot1) defer
apply(simp)
apply(subst AndP_comm)
apply(subst foot1) defer
apply(simp) defer 
apply(subst AndP_comm) back
apply(simp add:CondR_def ImpliesP_def AndP_OrP_distl AndP_assoc AndP_contra R2_OrP)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_comm) back
apply(subst foot3,simp_all)
apply(subst a)
apply(subst CSP_Post_R1_commute)
apply(simp add:g R2_def)
apply(subst foot7[THEN sym])
apply(subst foot6[THEN sym])
apply(simp add:R2_def[THEN sym] f)
apply(simp add:R1_def usubst typing defined closure AndP_assoc[THEN sym]g)
apply(subst AndP_comm) back
apply(subst AndP_assoc)
apply(subst foot1)
apply(simp add:R1_def[THEN sym] R1_OrP R1_idempotent)
apply(simp add:R1_OrP[THEN sym])
apply(subst OrP_assoc)
apply(subst foot4,simp add:R1_def)
apply(subst foot3,simp add:R1_def[THEN sym] R1_extend_AndP[THEN sym])

sorry
qed
have a: "REL_VAR - {ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} = REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}"
by(utp_poly_auto_tac)
have b: "`\<not>$wait \<and> ($wait\<acute>=$wait)`=`\<not>$wait \<and> \<not>$wait\<acute>`"
by(utp_poly_auto_tac)
have 7: "`\<not> (\<not> R2(A) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((R2 (A \<Rightarrow> B) \<and> $wait\<acute>) \<or>
     (R2 (A \<Rightarrow> B) ;
     (\<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>)))`
        = `\<not> (\<not> R2(A) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((R2 (A \<Rightarrow> B) \<and> $wait\<acute>) \<or>
     (R2 (A \<Rightarrow> B) ;
     (\<not> $wait \<and> \<not> $wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>)))`"
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)
apply(subst a)
apply(subst AndP_assoc)
apply(subst b)
apply(simp add:AndP_assoc[THEN sym])
done
have 5: "`(\<not> (\<not>CSP_Pre(R2(\<not>A)) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     (CSP_Post(R2(\<not> A)) \<or> CSP_Post(R2(B))) ;
     (II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub> \<lhd> $wait \<rhd> 
      ((($tr\<acute> - $tr = \<langle>\<rangle>) \<and> \<not> $wait\<acute> \<and>
      II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>) \<and> ($tr \<le> $tr\<acute>))))` 
      \<sqsubseteq>
    `CSP_Post(P)[true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute> . CSP_Post(P)[false/wait\<acute>])`"
apply(simp add:CSP_Pre_R2_commute CSP_Post_R2_commute)
apply(simp add: CSP_Pre_UNREST CSP_Post_UNREST unrest assms R2_OrP[THEN sym] ImpliesP_def[THEN sym])
apply(simp add:CondR_def SemiR_OrP_distl)
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename)
apply(subst SemiR_SkipRA_right,simp_all add:6 typing defined closure)
apply(rule unrest) back back
apply(rule unrest)
apply(rule unrest) back back
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms unrest)
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back back
apply(subst AndP_comm) back back back back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst tr_prefix_as_nil)
sorry
have 4: "`(\<not> ((\<not> A[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][false/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) ;
         ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((\<not> A[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][true/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) \<or>
      B[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][true/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) ;
     (II\<^bsub>REL_VAR -
        {ok\<down>, ok\<down>\<acute>}\<^esub> \<lhd> $wait \<rhd> ((($tr\<acute> - $tr = \<langle>\<rangle>) \<and>
                                 \<not> $wait\<acute> \<and>
                                 II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>) \<and>
                                ($tr \<le> $tr\<acute>))))` \<sqsubseteq>
    `P[true/ok\<acute>][true/ok][false/wait][true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute> .
                        P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>])`"
proof -
from 5 show ?thesis
by(simp add:R2_def CSP_Pre_def R1_def R2s_def usubst typing defined closure CSP_Post_def)
have "`CSP4(RHc(A \<turnstile> B))` \<sqsubseteq> `P`"
apply(subst CSP4_Design_form)
apply(simp_all add:assms)
apply(simp add:CSP4_def)
apply(subst DesignREA_form) back
apply(subst Seq_comp_form[of _ "SKIP"])
apply(simp_all add:closure typing defined assms Skip_CSP)
apply(simp add:is_healthy_def CSP_def RHc_def)
apply(simp add: R1_R3c_commute R2_R3c_commute)
apply(simp add:R2_def R1_idempotent SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)
apply(simp add:R2s_def R1_def usubst typing defined closure AndP_OrP_distr)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym] tr_prefix_as_nil)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back
apply(subst AndP_assoc) back
apply(subst SkipRA_unfold_aux_ty[of "tr" "REL_VAR",THEN sym],simp_all add:typing defined closure)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_comm) back back
apply(simp add:CondR_def[THEN sym])
apply(simp add:CSP1_CSP2_commute CSP1_R3c_commute)
apply(simp add:CSP1_def)
apply(subst OrP_comm) back back
apply(simp add:OrP_assoc)
apply(simp add:R3c_def)
apply(subst CSP1_R1_form)
apply (metis R1_SkipR_closure) 
apply(simp add:CSP1_def SkipR_as_SkipRA CondR_def AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure defined)
apply(simp add:usubst typing defined closure)
apply(subst OrP_assoc) back
apply(simp add:AndP_OrP_distr[THEN sym])
apply(simp add: OrP_excluded_middle)
apply(subst AndP_assoc) back back
apply(subst AndP_comm) back back back back
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(subst AndP_comm) back back back back back
apply(simp add:AndP_contra)
apply(subst AndP_assoc)
apply(subst AndP_comm)
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_comm) back back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(simp add:AndP_idem)
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm) back back back back back back back
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back back back
apply(simp add:AndP_idem)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing defined closure usubst)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing defined closure usubst)
apply(subst AndP_comm) back back back back back back back back back back
apply(subst OrP_assoc)
apply(subst OrP_comm)
apply(simp add:OrP_assoc[THEN sym])
apply(simp add:H2_split usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest)
apply(simp add:usubst typing defined closure)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(simp add: 2 3 OrP_assoc[THEN sym] AndP_OrP_distr)
apply(subst OrP_assoc) back
apply(subst OrP_comm) back
apply(subst OrP_assoc[THEN sym])
apply(subst OrP_assoc)
apply(subst OrP_AndP_absorb)
apply(subst OrP_assoc) back
apply(subst OrP_comm) back
apply(subst OrP_assoc[THEN sym])
apply(subst OrP_assoc) back back
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst SubstP_VarP_single_UNREST)back back
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst OrP_AndP_absorb)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst SubstP_VarP_single_UNREST) back back
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(simp add:AndP_assoc[THEN sym])
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing defined closure) back
apply(utp_poly_auto_tac) 
apply(simp add:Skip_pre Skip_post)
apply(subst DesignREA_refine)
apply(simp_all)
apply(simp add:CSP_Pre_def CSP_Post_def usubst typing defined closure)
apply(simp add:R2_def R2s_def R1_def usubst typing defined closure)
apply (metis (lifting, mono_tags) "1" AndP_comm PVAR_VAR_pvdash)
sorry
qed
show ?thesis sorry
qed

(*
lemma DesignREA_refine2:
assumes"`RHc (A \<turnstile> B)` \<sqsubseteq> `RHc (C \<turnstile> D)`"
shows 
    "`\<not>A` \<sqsubseteq> `\<not>C`"
    "`A \<Rightarrow> B` \<sqsubseteq> `D`"

P = \<not> (\<not> P ; tr\<le>tr\<acute>)
(CSP_Post(@a) \<Rightarrow> Q) \<sqsubseteq> P

P = \<not> (CSP_Post(@a) \<and> \<not>Q ; tr\<le>tr\<acute>)

P = \<not> (((a \<notin> $ref\<acute>) \<and> ($tr\<acute> = $tr) \<and> $wait\<acute> \<and> \<not>Q);tr\<le>tr\<acute>) \<and> \<not> ((\<not>$wait\<acute> \<and> $tr ^\<langle>a\<rangle>=$tr\<acute> \<and> \<not>Q);tr\<le>tr\<acute>)

P = \<not> (\<exists> ref\<^sub>0 @ a \<notin> ref\<^sub>0 \<and> \<not>Q[\<langle>\<rangle>,true,ref\<^sub>0/tr\<acute>,wait\<acute>,ref\<acute>]) \<and> \<not> (\<exists> ref\<^sub>0 @ \<not>Q[\<langle>a\<rangle>,false,ref\<^sub>0/tr\<acute>,wait\<acute>,ref\<acute>] \<and> $tr^\<langle>a\<rangle>\<le>$tr\<acute>)

P =  (\<forall> ref\<^sub>0,ref\<^sub>1 | a \<notin> ref\<^sub>1 @ Q[\<langle>\<rangle>,true,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>]) \<and> 
     ($tr^\<langle>a\<rangle>\<le>$tr\<acute> \<Rightarrow> \<forall> ref\<^sub>0,ref\<^sub>1 @ Q[\<langle>a\<rangle>,false,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>])

Claim:
@a \<sqsubseteq> R(((\<forall> ref\<^sub>0,ref\<^sub>1 | a \<notin> ref\<^sub>1 @ Q\<^sup>t[tr,true,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>]) \<and> ($tr^\<langle>a\<rangle>\<le>$tr\<acute> \<Rightarrow> \<forall> ref\<^sub>0,ref\<^sub>1 @ Q\<^sup>t[\<langle>a\<rangle>,false,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>])) \<turnstile> Q) 


@a \<sqsubseteq> R(true \<turnstile> wait\<acute> \<or> #(tr\<acute>-tr) = 1)
@a \<sqsubseteq> R(false \<turnstile> b \<notin> ref\<acute>)
@a \<sqsubseteq> R(\<not>($tr^\<langle>a\<rangle>\<le>$tr\<acute>) \<turnstile> a \<notin> ref\<acute>) 
  

{P}(a \<rightarrow> CHAOS \<sqinter> STOP){Q}

{false}CHAOS{Q}

{\<forall> ref\<^sub>0,ref\<^sub>1 | a \<notin> ref\<^sub>1 @ Q\<^sup>t[tr,true,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>] \<and> \<not>($tr^\<langle>a\<rangle>\<le>$tr\<acute>)}a \<rightarrow> CHAOS{Q}
{\<forall> ref\<^sub>0,ref\<^sub>1 @ Q\<^sup>t[tr,true,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>]}STOP{Q}
{\<forall> ref\<^sub>0,ref\<^sub>1 @ Q\<^sup>t[tr,true,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>] \<and> \<not>($tr^\<langle>a\<rangle>\<le>$tr\<acute>)}a \<rightarrow> CHAOS\<sqinter>STOP{Q}
{}a \<rightarrow> CHAOS\<sqinter>STOP{a \<in> ref\<acute> \<or> tr\<acute>\<noteq>tr}
@a \<sqsubseteq> R(((\<forall> ref\<^sub>0,ref\<^sub>1 | a \<notin> ref\<^sub>1 @ Q\<^sup>t[tr,true,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>]) \<and> ($tr^\<langle>a\<rangle>\<le>$tr\<acute> \<Rightarrow> \<forall> ref\<^sub>0,ref\<^sub>1 @ Q\<^sup>t[\<langle>a\<rangle>,false,ref\<^sub>0,ref\<^sub>1/tr\<acute>,wait\<acute>,ref,ref\<acute>])) \<turnstile> Q) 

P \<sqsubseteq> \<mu>X.R( true \<turnstile> (a \<notin> ref\<acute> \<and> wait\<acute>) \<Rightarrow> \<exists> wait\<acute>,ref\<acute>,$ok\<acute>.X[tr\<acute>^\<langle>a\<rangle>/tr\<acute>])

F(X) = (\<not>$ok \<and> tr\<le>tr\<acute>) \<or> ($ok \<and> wait \<and> $ok\<acute> \<and> wait\<acute> \<and> tr\<acute>=tr \<and> ref\<acute>=ref) \<or> ($ok \<and> \<not>wait \<and> $ok\<acute> \<and> wait\<acute> \<and> tr\<le>tr\<acute> \<and> a \<in> ref\<acute>) \<or> ($ok \<and> \<not>wait \<and> $ok\<acute> \<and> wait\<acute> \<and> tr\<le>tr\<acute> \<and> a \<notin> ref\<acute> \<and> \<exists> wait\<acute>,ref\<acute>,$ok\<acute>.X[tr\<acute>^\<langle>a\<rangle>/tr\<acute>]) \<or> ($ok \<and> \<not>wait \<and> $ok\<acute> \<and> \<not>wait\<acute> \<and> tr\<le>tr\<acute>)

F(false) = (\<not>$ok \<and> tr\<le>tr\<acute>) \<or> ($ok \<and> wait \<and> $ok\<acute> \<and> wait\<acute> \<and> tr\<acute>=tr \<and> ref\<acute>=ref) \<or> ($ok \<and> \<not>wait \<and> $ok\<acute> \<and> wait\<acute> \<and> tr\<le>tr\<acute> \<and> a \<in> ref\<acute>) \<or> ($ok \<and> \<not>wait \<and> $ok\<acute> \<and> \<not>wait\<acute> \<and> tr\<le>tr\<acute>)
F\<^sup>2(false) = (\<not>$ok \<and> tr\<le>tr\<acute>) \<or> ($ok \<and> wait \<and> $ok\<acute> \<and> wait\<acute> \<and> tr\<acute>=tr \<and> ref\<acute>=ref) \<or> ($ok \<and> \<not>wait \<and> $ok\<acute> \<and> tr\<le>tr\<acute>)
F\<^sup>2(false) = R1($ok\<Rightarrow>R3($ok\<acute>))

P \<Rightarrow> \<forall>a | \<forall>wait\<acute>,ref\<acute>,$ok\<acute>.\<not>P[tr\<acute>^\<langle>a\<rangle>/tr\<acute>].  P[ref\<acute>\<union>{a}/ref\<acute>]



definition ParallelMergeD2 :: 
  "'a upred =>  'a upred => 'a upred \<Rightarrow> 'a upred" (infix "\<parallel>2\<^bsub>_\<^esub>" 100) where
"P \<parallel>2\<^bsub>M\<^esub> Q =  ((add_sub 0 on {tr \<down>\<acute>,wait \<down>\<acute>,ref \<down>\<acute>,$ok \<down>\<acute>} \<bullet> P) \<and>\<^sub>p (add_sub 1 on {tr \<down>\<acute>,wait \<down>\<acute>,ref \<down>\<acute>,$ok \<down>\<acute>} \<bullet> Q) \<and>\<^sub>p II\<^bsub>REA \<union> OKAY\<^esub>) ;\<^sub>R M"

lemma ParallelMerge_form:
"P \<parallel>2\<^bsub>M\<^esub> Q =  `(P[$tr\<^bsub>0\<^esub>\<acute>/tr\<acute>][$wait\<^bsub>0\<^esub>\<acute>/wait\<acute>][$ref\<^bsub>0\<^esub>\<acute>/ref\<acute>][$$ok\<^bsub>0\<^esub>\<acute>/ok\<acute>] \<and>
         Q[$tr\<^bsub>1\<^esub>\<acute>/tr\<acute>][$wait\<^bsub>1\<^esub>\<acute>/wait\<acute>][$ref\<^bsub>1\<^esub>\<acute>/ref\<acute>][$$ok\<^bsub>1\<^esub>\<acute>/ok\<acute>] \<and> II\<^bsub>REA \<union> OKAY\<^esub>) ; M`"


definition MergeCSP2 :: 
"'a upred" where
"MergeCSP2 = `($$ok\<acute> \<Leftrightarrow> ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub>)) \<and> 
              ($wait\<acute> \<Leftrightarrow> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)) \<and> 
              (($tr\<acute>-$tr)  \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> 
              ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)`"

definition InterleaveCSP2 ::
  "'a upred =>   'a upred \<Rightarrow> 'a upred" (infix "\<parallel>CSP" 100) where
"P \<parallel>CSP Q = P \<parallel>2\<^bsub>MergeCSP2 ;\<^sub>R SKIP\<^esub> Q"

lemma MergeCSP2_rel_closure: 
  "MergeCSP2 \<in> WF_RELATION"
apply(simp add:WF_RELATION_def MergeCSP2_def)
apply(rule unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(simp_all)


lemma aid:   "`($tr\<acute> - $tr \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> $tr\<^bsub>Suc 0\<^esub> - $tr)` \<in> WF_RELATION" 
apply(simp add:WF_RELATION_def)
apply(rule unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer


lemma pvaux_sub[simp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR" 
  assumes "TYPEUSOUND('a,'m)"
  shows "pvaux (x\<^bsub>n\<^esub>) = pvaux x "
by (metis MkPVAR_def pvaux_MkPVAR pvchsub_def)

lemma aid2:   "|$ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>Suc 0\<^esub>| \<rhd>\<^sub>* ref"
by(simp add:typing defined closure)

lemma MergeCSP2_form: 
"MergeCSP2 ;\<^sub>R SKIP = `((\<not>$$ok\<^bsub>0\<^esub> \<or> \<not>$$ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or>  
                  ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
                  ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> \<not>$wait\<^bsub>0\<^esub> \<and> \<not>$wait\<^bsub>1\<^esub> \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
proof - 
have "MergeCSP2 ;\<^sub>R SKIP = `
     (\<not> ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub>) \<and> ($wait\<acute> \<Leftrightarrow> $wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)) ; ($tr \<le> $tr\<acute>) \<or>
     ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> \<not> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> (\<exists> ref\<acute> . ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
apply(simp add: Skip_right MergeCSP2_rel_closure)
apply(simp add:MergeCSP2_def usubst typing defined closure)
apply(simp add:AndP_assoc)
apply(subst ExistsP_AndP_expand2[THEN sym])
apply(simp add:typing closure defined unrest)
apply(simp add:AndP_assoc[THEN sym])
done
also have "... = `(\<not> ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub>) \<and> (\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute> \<Leftrightarrow> $wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (\<exists> ref\<acute>\<acute> . ($ref\<acute>\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> 
                      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or>  
                      ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
                      ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> \<not> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
apply(subst ExistsP_has_ty_value,simp_all add:typing closure defined unrest aid2)  
apply(subst SemiR_extract_variable_id[of "ref \<down>"],simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst erasure) 
apply(subst SemiR_extract_variable_id[of "wait \<down>"],simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc)
apply(simp add:SubstP_VarP_single_UNREST SubstE_VarE_single_UNREST typing closure defined unrest)
apply(subst SemiR_AndP_left_DASHED)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand2[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand2[THEN sym])
apply(simp add:typing closure defined unrest)
apply(simp add:AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym] OrP_assoc[THEN sym])
done
also have "... = `((\<not>$$ok\<^bsub>0\<^esub> \<or> \<not>$$ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or>  
                  ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
                  ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> \<not>$wait\<^bsub>0\<^esub> \<and> \<not>$wait\<^bsub>1\<^esub> \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
proof -
  have 0 : "`\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute> \<Leftrightarrow> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)` = `true`" 
  proof -
    have "`\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute> \<Leftrightarrow> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)` = `(\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute>=true \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)) \<or> (\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute>=false \<and> \<not> $wait\<^bsub>0\<^esub> \<and> \<not> $wait\<^bsub>1\<^esub>) `" 
    apply(simp add:IffP_def ImpliesP_def demorgan1 AndP_OrP_distr AndP_OrP_distl AndP_assoc AndP_contra)
    apply(subst AndP_comm) back back
    apply(subst AndP_comm) back back back back
    apply(simp add:AndP_contra AndP_assoc[THEN sym] AndP_OrP_distr[THEN sym])
    apply(subst AndP_comm) back back
    apply(subst OrP_comm)
    apply(simp add:ExistsP_OrP_dist AndP_OrP_distr AndP_OrP_distl)
      done
      also have "... = `true`"
      apply(subst ExistsP_AndP_expand1[THEN sym])
      apply(simp add:typing closure defined unrest)
      apply(subst ExistsP_has_ty_value) defer defer defer defer 
      apply(subst ExistsP_AndP_expand1[THEN sym])
      apply(simp add:typing closure defined unrest)
      apply(subst ExistsP_has_ty_value)
      apply(simp_all add:typing closure defined unrest)
      apply(simp add:demorgan1[THEN sym] OrP_excluded_middle)
      done
      finally show ?thesis ..
      qed
  show ?thesis
  apply(subst 0)
  apply(subst ExistsP_has_ty_value)
  apply(simp_all add:typing closure defined unrest aid2 demorgan1 demorgan2 AndP_assoc[THEN sym])
  done
qed
finally show ?thesis ..
qed

lemma InterleaveCSP_pre: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "CSP_Pre( P \<parallel>CSP Q )= \<not>\<^sub>p (((
        ((add_sub 0 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> \<not>\<^sub>p CSP_Pre P ) \<and>\<^sub>p (add_sub 1 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> CSP_Post Q)) \<or>\<^sub>p 
        ((add_sub 0 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> CSP_Post P ) \<and>\<^sub>p (add_sub 1 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> \<not>\<^sub>p CSP_Pre Q))
) \<and>\<^sub>p `(($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))` 
);\<^sub>R `($tr \<le> $tr\<acute>)`
)"
proof -
have "CSP_Pre( P \<parallel>CSP Q) = `\<not> (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref)) ;
       ($ok \<and> \<not>$wait \<and> (\<not> $$ok\<^bsub>0\<^esub> \<or> \<not> $$ok\<^bsub>1\<^esub>) \<and> ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>)))`"
apply(simp add:InterleaveCSP2_def CSP_Pre_def ParallelMerge_form)
apply(subst SubstP_SemiR_right)
apply(simp add:closure)
apply(simp add:unrest closure typing)
apply(subst MergeCSP2_form)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add: typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add: typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add: typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ref"],simp_all add: typing defined closure)
apply(simp add:SubstP_SemiR_left closure unrest typing)
apply(simp add:usubst typing defined closure)
apply(simp add:SubstP_SemiR_right closure unrest typing)
apply(simp add:usubst typing defined closure)
apply(simp add:SkipRA_empty)
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename) back
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename) back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
done
also have "... = `\<not> (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $($ok\<^bsub>0\<^esub>\<acute>) \<or> \<not> $($ok\<^bsub>1\<^esub>\<acute>))) ;
       (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>))`"
apply(subst AndP_assoc) back back
apply(subst SemiR_remove_middle_unrest1[of _ _ "{$ok \<down>,wait \<down>}"])
apply(simp_all add:typing defined closure unrest)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp add:assms)
apply(simp_all add:typing closure defined unrest) defer defer defer defer 
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp add:assms)
apply(simp_all add:typing closure defined unrest) defer defer defer defer
apply(rule closure)

apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp add:UNDASHED_def)
apply(rule closure)
apply(rule closure)
apply(simp add:UNDASHED_def)
apply(rule closure)
apply(simp add:aid)
apply(simp add:closure) defer
apply(subst SemiR_AndP_right_precond)
apply(simp add:WF_CONDITION_def)
apply(rule conjI)
apply(simp add:WF_RELATION_def)
apply(rule unrest)
apply(rule unrest) defer
apply(rule unrest) defer 
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(simp add:DASHED_def)
apply(rule unrest)
apply(rule unrest)
apply(simp add:DASHED_def)
apply(simp add:AndP_assoc[THEN sym] urename typing defined)
apply(subst ConvR_VarP_1)
apply(simp add:UNDASHED_def)
apply(subst ConvR_VarP_1)
apply(simp add:UNDASHED_def)
apply(simp)
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer defer 
apply(rule unrest) defer
apply(rule unrest)

also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $$ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $$ok\<^bsub>1\<^esub>\<acute>)) ;
       ((($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> true) ; ($tr\<acute>\<acute> \<le> $tr\<acute>)))`"
proof -
have 0: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr]` = `($tr\<acute>\<acute> \<le> $tr\<acute>)`"
by(simp add:usubst typing defined closure)
have 1: "`(($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub> - $tr))[$tr\<acute>\<acute>/tr\<acute>]` = `(($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub> - $tr))`"
by(simp add:usubst typing defined closure)
show ?thesis
apply(subst SemiR_extract_variable_id[of "tr \<down>"]) back
apply(simp_all add:typing defined closure unrest)
apply(subst ExistsP_SemiR_NON_REL_VAR_expand1)
apply(simp_all add:typing defined closure unrest assms)
apply(subst 0[THEN sym])
apply(subst 1[THEN sym])
apply(simp add:erasure typing closure defined)
done
qed
also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $$ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $$ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute>\<acute> - $tr\<acute>) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr\<acute>) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr\<acute>))) ;
        true ; (true \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>))))`"
proof -
have 0: "`(($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub> - $tr))\<acute>` = `(($tr\<acute>\<acute> - $tr\<acute>) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr\<acute>) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub>\<acute> - $tr\<acute>))`" 

show ?thesis
apply(subst SemiR_assoc)
apply(subst SemiR_AndP_right_DASHED)
apply(rule unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)
apply(simp_all add:typing closure defined unrest)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(simp add:typing closure defined unrest)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(simp add:typing closure defined unrest)
apply(simp add:AndP_assoc[THEN sym] SemiR_assoc[THEN sym])
apply(simp add: 0)
done
qed
also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $$ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $$ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute>\<acute> - $tr\<acute>) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr\<acute>) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr\<acute>))) ;
        ($tr\<acute>\<acute> \<le> $tr\<acute>))))`"
apply(subst SemiR_AndP_right_UNDASHED)
apply(simp_all add:closure typing defined unrest)
done
also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        (\<not> $$ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $$ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr\<acute>\<acute> \<le> $tr\<acute>))))`"




also have " ... = `\<not>  (
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        (\<not> $$ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $$ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"
proof -
have 0: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr]` = `($tr\<acute>\<acute> \<le> $tr\<acute>)`"
by(simp add:usubst typing defined closure)
have 1: "`(($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub>\<acute> - $tr))[$tr\<acute>\<acute>/tr\<acute>]` = `(($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub>\<acute> - $tr))`"
by(simp add:usubst typing defined closure)
show ?thesis
apply(subst SemiR_extract_variable_id[of "tr \<down>"]) back
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing closure defined unrest SubstE_VarE_single_UNREST)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back 
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing closure defined unrest SubstE_VarE_single_UNREST)
apply(subst 0[THEN sym])
apply(subst 1[THEN sym])
apply(simp add:typing defined closure erasure)
done
qed
also have " ... = `\<not>  (((
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait]) \<or>
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"

also have " ... = `\<not>  (((
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>][true/ok][false/wait]) \<or>
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"

also have " ... = `\<not>  (((
        ((\<not>CSP_Pre(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> CSP_Post(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>]) \<or>
        (CSP_Post(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> \<not>CSP_Pre(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"

also have " ... = `\<not>  (((
        ((\<not>CSP_Pre(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> CSP_Post(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>]) \<or>
        (CSP_Post(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> \<not>CSP_Pre(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"

finally show ?thesis 


qed

lemma Inter_form: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP"
  shows "P \<parallel>CSP Q = `RHc(
  \<not>(
    (P \<^sub>f[($tr\<^bsub>0\<^esub>)/tr\<acute>][($wait\<^bsub>0\<^esub>)/wait\<acute>][($ref\<^bsub>0\<^esub>)/ref\<acute>][($$ok\<^bsub>0\<^esub>)/ok\<acute>] \<and>
      Q \<^sub>f[($tr\<^bsub>1\<^esub>)/tr\<acute>][($wait\<^bsub>1\<^esub>)/wait\<acute>][($ref\<^bsub>1\<^esub>)/ref\<acute>][($$ok\<^bsub>1\<^esub>)/ok\<acute>] \<and>
     (\<not> $$ok\<^bsub>0\<^esub> \<or> \<not> $$ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)))
     ; ($tr \<le> $tr\<acute>))
                                    \<turnstile>
      ((P \<^sub>f[($tr\<^bsub>0\<^esub>)/tr\<acute>][($wait\<^bsub>0\<^esub>)/wait\<acute>][($ref\<^bsub>0\<^esub>)/ref\<acute>][true/ok\<acute>] \<and>
     Q \<^sub>f[($tr\<^bsub>1\<^esub>)/tr\<acute>][($wait\<^bsub>1\<^esub>)/wait\<acute>][($ref\<^bsub>1\<^esub>)/ref\<acute>][true/ok\<acute>]
     \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and>
     ((($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)))
      \<lhd> $wait\<acute> \<rhd>
        (\<not>$wait\<^bsub>0\<^esub> \<and> \<not>$wait\<^bsub>1\<^esub> )))   ; II\<^bsub>REA \<union> OKAY\<^esub>
                                                                                            )`"
proof - 
have 1: "`(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
      II\<^bsub>{$ok\<down>, $ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) ;
     ((\<not> $$ok\<^bsub>0\<^esub> \<or> \<not> $$ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>))`=
     `(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
     (\<not> $$ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $$ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ; ($tr \<le> $tr\<acute>)`"

have 2:
"`(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      II\<^bsub>{$ok\<down>, $ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) ;
     ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and>
      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)) \<and> $$ok\<acute> \<and> $wait\<acute>)` = 
      `(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     ($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and>
      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<union> $ref\<^bsub>1\<^esub>\<acute>)) 
      \<and> $$ok\<acute> \<and> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>`"

have 3: "`(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
      II\<^bsub>{$ok\<down>, $ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) ;
     ($$ok\<^bsub>0\<^esub> \<and> $$ok\<^bsub>1\<^esub> \<and> \<not> $wait\<^bsub>0\<^esub> \<and> \<not> $wait\<^bsub>1\<^esub> \<and> 
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $$ok\<acute> \<and> \<not> $wait\<acute>)` = 
     `(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute>  - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))
     \<and> $$ok\<acute> \<and> \<not> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>`"

have "P \<parallel>CSP Q = `
((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
     (\<not> $$ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $$ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ; ($tr \<le> $tr\<acute>)
   ) \<or>((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     ($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and>
      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<union> $ref\<^bsub>1\<^esub>\<acute>)) 
      \<and> $$ok\<acute> \<and> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>
    )\<or>((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute>  - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))
     \<and> $$ok\<acute> \<and> \<not> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>
    )`"
apply(simp add: InterleaveCSP2_def)
apply(simp add: ParallelMerge_form)
apply(simp add: MergeCSP2_form)
apply(simp add:SemiR_OrP_distl)

show ?thesis 
qed

lemma CSP5: 
  assumes "P \<in> WF_RELATION" "P is CSP"
  shows "P \<parallel>CSP SKIP = undefined"
proof -
have 1: "P \<parallel>CSP SKIP = `RHc ((\<not> ((
             P \<^sub>f[$tr\<^bsub>0\<^esub>/tr\<acute>][$wait\<^bsub>0\<^esub>/wait\<acute>][$ref\<^bsub>0\<^esub>/ref\<acute>][false/ok\<acute>] \<and>
             II\<^bsub>REL_VAR - REA - OKAY\<^esub> \<and> 
             (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> \<langle>\<rangle>) 
             ) ; ($tr \<le> $tr\<acute>))) \<turnstile>
         ((P \<^sub>f[$tr\<^bsub>0\<^esub>/tr\<acute>][$wait\<^bsub>0\<^esub>/wait\<acute>][$ref\<^bsub>0\<^esub>/ref\<acute>][true/ok\<acute>] \<and>
            II\<^bsub>REL_VAR - REA - OKAY\<^esub> \<and>
           (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> \<langle>\<rangle>) \<and>
          ($wait\<acute> = wait\<down>\<^bsub>0\<^esub>) \<and>
          ((\<not>$wait\<acute>) \<or> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)))
          ); II\<^bsub>REA \<union> OKAY\<^esub>))`"
apply(subst Inter_form)
apply(simp_all add:closure assms Skip_CSP)
apply(simp add:Skip_expansion)

end


lemma hand: "P ;\<^sub>R MergeCSP2 ;\<^sub>R SKIP =  `(
      (((P[false/($ok\<^bsub>0\<^esub>)\<acute>]) \<or> (P[false/($ok\<^bsub>1\<^esub>)\<acute>])) ; 
              (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or> 
     (((P[true/($ok\<^bsub>0\<^esub>)\<acute>][true/($ok\<^bsub>1\<^esub>)\<acute>][true/(wait\<^bsub>0\<^esub>)\<acute>] \<or> (P[true/($ok\<^bsub>0\<^esub>)\<acute>][true/($ok\<^bsub>1\<^esub>)\<acute>][true/(wait\<^bsub>1\<^esub>)\<acute>])) ; 
              ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
      ((P[true/($ok\<^bsub>0\<^esub>)\<acute>][true/($ok\<^bsub>1\<^esub>)\<acute>][false/(wait\<^bsub>0\<^esub>)\<acute>][false/(wait\<^bsub>1\<^esub>)\<acute>] ; 
              (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and> $$ok\<acute> \<and> \<not> $wait\<acute>))`"

proof -
have "P ;\<^sub>R MergeCSP2 ;\<^sub>R SKIP = `(
      (P \<and> \<not> ($$ok\<^bsub>0\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or> 
      (P \<and> \<not> ($$ok\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or>
     ((P \<and> ($$ok\<^bsub>0\<^esub>)\<acute> \<and> ($$ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>0\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     ((P \<and> ($$ok\<^bsub>0\<^esub>)\<acute> \<and> ($$ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>1\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     ((P \<and> ($$ok\<^bsub>0\<^esub>)\<acute> \<and> ($$ok\<^bsub>1\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>0\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $$ok\<acute> \<and> \<not> $wait\<acute>))`"
apply(simp add:MergeCSP2_form SemiR_OrP_distl)
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer defer 
apply(simp_all add:typing defined closure unrest DASHED_def)
apply(simp add:typing defined closure urename AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst SemiR_AndP_right_UNDASHED) defer 
apply(subst SemiR_AndP_right_UNDASHED) back defer 
apply(simp_all add:typing defined closure unrest UNDASHED_def) 
apply(simp add:AndP_OrP_distl SemiR_OrP_distr AndP_OrP_distr AndP_assoc[THEN sym] OrP_assoc[THEN sym])
done
also have "... = `(
      (P[false/ok\<^bsub>0\<^esub>\<acute>] \<and> \<not> ($$ok\<^bsub>0\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or> 
      (P[false/ok\<^bsub>1\<^esub>\<acute>] \<and> \<not> ($$ok\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or>
     ((P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>0\<^esub>\<acute>] \<and> ($$ok\<^bsub>0\<^esub>)\<acute> \<and> ($$ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>0\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     ((P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>1\<^esub>\<acute>] \<and> ($$ok\<^bsub>0\<^esub>)\<acute> \<and> ($$ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>1\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     ((P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][false/wait\<^bsub>0\<^esub>\<acute>][false/wait\<^bsub>1\<^esub>\<acute>] \<and> ($$ok\<^bsub>0\<^esub>)\<acute> \<and> ($$ok\<^bsub>1\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>0\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $$ok\<acute> \<and> \<not> $wait\<acute>))`"

also have "... = `(
      P[false/ok\<^bsub>0\<^esub>\<acute>] ; (\<not> ($$ok\<^bsub>0\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>) \<or> 
      P[false/ok\<^bsub>1\<^esub>\<acute>] ; (\<not> ($$ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>0\<^esub>\<acute>] ; (($$ok\<^bsub>0\<^esub>) \<and> ($$ok\<^bsub>1\<^esub>) \<and> ($wait\<^bsub>0\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>1\<^esub>\<acute>] ; (($$ok\<^bsub>0\<^esub>) \<and> ($$ok\<^bsub>1\<^esub>) \<and> ($wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][false/wait\<^bsub>0\<^esub>\<acute>][false/wait\<^bsub>1\<^esub>\<acute>] ; (($$ok\<^bsub>0\<^esub>) \<and> ($$ok\<^bsub>1\<^esub>) \<and> \<not> ($wait\<^bsub>0\<^esub>) \<and> \<not> ($wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and> $$ok\<acute> \<and> \<not> $wait\<acute>))`"

also have "... = `(
      P[false/ok\<^bsub>0\<^esub>\<acute>] ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or> 
      P[false/ok\<^bsub>1\<^esub>\<acute>] ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>0\<^esub>\<acute>] ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>1\<^esub>\<acute>] ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $$ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][false/wait\<^bsub>0\<^esub>\<acute>][false/wait\<^bsub>1\<^esub>\<acute>] ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $$ok\<acute> \<and> \<not> $wait\<acute>))`"

finally show ?thesis ..
qed


lemma Interleave_R1: 
  assumes "P is R1" "Q is R1"
  shows "P \<parallel>CSP Q is R1"
proof -
have " P \<parallel>CSP Q =`
((
    ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>]) \<or>
     (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>]))
 \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>)) \<or>
(((((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][true/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>]) \<or> 
    (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][true/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>])) \<and> ($tr\<acute>=$tr)) ;
      ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)))) \<and>
      $ok\<acute> \<and> $wait\<acute>) \<or>
(((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>1\<^esub>)\<acute>/ref\<acute>][true/ok\<acute>] \<and> ($tr\<acute>=$tr)) ;
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and>
     $ok\<acute> \<and> \<not> $wait\<acute>)`"
apply(simp add:is_healthy_def R1_def InterleaveCSP2_def ParallelMerge_form hand)
apply(simp add:usubst typing defined closure)

thm SubstP_twice_2


thm SubstP_SkipRA
lemma Interleave_R2: 
  assumes "P is R2" "Q is R2" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "P \<parallel>CSP Q is R2"


lemma Interleave_R3c: 
  assumes "P is R3c" "Q is R3c"
  shows "P \<parallel>CSP Q is R3c"
proof-
from assms have "P \<parallel>CSP Q = (R3c P) \<parallel>CSP (R3c Q)" 
also have "... = ` ((
      (\<not> $$ok \<and> $wait \<and> ($tr \<le> $tr\<^bsub>0\<^esub>\<acute>) \<and> ($tr \<le> $tr\<^bsub>1\<^esub>\<acute>)) \<or>
      ($$ok \<and> $wait \<and> ($wait\<^bsub>0\<^esub>\<acute>=$wait) \<and> ($ref\<^bsub>0\<^esub>\<acute>=$ref) \<and> ($tr\<^bsub>0\<^esub>\<acute>=$tr) \<and> ($$ok\<^bsub>0\<^esub>\<acute>=$$ok) \<and> ($wait\<^bsub>Suc 0\<^esub>\<acute>=$wait) \<and> ($ref\<^bsub>Suc 0\<^esub>\<acute>=$ref) \<and> ($tr\<^bsub>Suc 0\<^esub>\<acute>=$tr) \<and> ($$ok\<^bsub>Suc 0\<^esub>\<acute>=$$ok) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>} - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {$ok\<down>, $ok\<down>\<acute>}\<^esub>) \<or>
      (\<not> $wait \<and> P[false/wait][($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and> Q[false/wait][($tr\<^bsub>Suc 0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>Suc 0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>Suc 0\<^esub>\<acute>)/ref\<acute>][($$ok\<^bsub>Suc 0\<^esub>\<acute>)/ok\<acute>]) 
     ) \<and> II\<^bsub>REA \<union> OKAY\<^esub>) ;
    MergeCSP2 ; SKIP`" 
apply(simp add:InterleaveCSP2_def ParallelMerge_form)
apply(simp add:R3c_form SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "wait"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ref"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "wait"]) back
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ref"]) back
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"]) back
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"]) back
apply(simp_all add:typing defined closure)
apply(simp add:usubst typing defined closure)

also have "... = undefined"
apply(simp add:MergeCSP2_form SemiR_OrP_distl)
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer defer 
apply(simp_all add:typing defined closure unrest DASHED_def)
apply(simp add:typing defined closure urename)




lemma Interleave_CSP1: 
  assumes "P is CSP1" "Q is CSP1"
shows "P \<parallel>CSP Q is CSP1"


lemma Interleave_CSP2: 
  assumes "P is CSP2" "Q is CSP2"
  shows "P \<parallel>CSP Q is CSP2"
apply(simp add:is_healthy_def H2_def InterleaveCSP2_def ParallelMerge_form SemiR_assoc[THEN sym])
apply(simp add:H2_def[THEN sym])
apply(metis Skip_CSP2 is_healthy_def)
done

lemma Interleave_CSP: 
  assumes "P is CSP" "Q is CSP"
  shows "`P ||| Q` is CSP"


lemma Interleave_closure[closure]: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`P ||| Q` \<in> WF_RELATION"



lemma Interleave_pre: 
  assumes "WITHSUB(0) \<sharp> P" "WITHSUB(1) \<sharp> Q"
  shows  "`CSP_Pre(P ||| Q)` = undefined"
proof -
  have 0: "{ref\<down>\<acute>, tr\<down>\<acute>, wait\<down>, ref\<down>, tr\<down>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {ref\<down>, ref\<down>\<acute>} = {}"
  have "`CSP_Pre(P ||| Q)` = ` 
      \<not> ( (((add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> P)[false/ok\<acute>][true/ok][false/wait] \<and> \<not> $wait\<acute> \<and> ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> \<not>$ok\<acute>) \<or>
        ((add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> Q)[false/ok\<acute>][true/ok][false/wait] \<and> \<not> $wait\<acute> \<and> ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> \<not>$ok\<acute>)) 
       ; (((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))) 
`"
    apply(simp add:InterleaveCSP_def ParallelMergeD_def ParallelCSP_def MergeCSP_form CSP_Pre_def)
    apply(subst SubstP_SemiR_right)
    apply(simp_all add:typing closure defined unrest)
    apply(simp add:typing defined closure usubst)
    apply(subst SubstP_SemiR_right)
    apply(simp_all add:typing closure defined unrest)
    apply(simp add:typing defined closure usubst)
    apply(subst SubstP_SemiR_left)
    apply(simp_all add:typing closure defined unrest)
    apply(subst SubstP_SemiR_left)
    apply(simp_all add:typing closure defined unrest)
    apply(simp add:typing defined closure usubst)
    apply(simp add:SemiR_AndP_right_precond typing closure defined urename)
    apply(simp add:DesignD_def ParallelD_def ImpliesP_def)
    apply(simp add:MergeCSP_def)
    apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure) defer 
    apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) defer 
    apply(subst SkipRA_unfold_aux_ty[of "ref"],simp_all add:typing defined closure) defer 
    apply(simp add:0 SkipRA_empty usubst typing defined closure demorgan1 demorgan2 AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym] OrP_assoc[THEN sym])
    apply(subst AndP_comm) back back back back back back back back
    apply(simp add:AndP_assoc[THEN sym])
    apply(subst AndP_comm) back back back back back back back back back back back back back
    apply(simp add:AndP_contra)
    
    also have "... = `\<not>(
(\<not>(CSP_Pre(add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> P) \<and> CSP_Pre(add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> Q)) \<and>
        \<not> $wait\<acute> \<and> ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> \<not>$ok\<acute>) ;
       (((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))
)`"
    by(simp add:AndP_OrP_distr[THEN sym] CSP_Pre_def CSP_Post_def demorgan1 demorgan2)
    also have "... = `\<not>(
(\<not>(CSP_Pre(add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> P) \<and> CSP_Pre(add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> Q)) \<and>
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref)) ;
       (\<not>$wait \<and> \<not>$ok \<and> ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))
)`"
  
also have "... =  `\<not> (\<exists> ref \<acute>\<acute>. (
(\<not>(CSP_Pre(add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> P) \<and> CSP_Pre(add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> Q)) \<and>
         ($tr\<acute> = $tr) \<and> ($ref\<acute>\<acute> = $ref)) ;
       (((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))
))`"

also have "... =  `\<not> (\<exists> ref \<acute>\<acute>. ($ref\<acute>\<acute> = $ref) \<and> (
(\<not>(CSP_Pre(add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> P) \<and> CSP_Pre(add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> Q)) \<and>
         ($tr\<acute> = $tr)) ;
       (((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))
))`"


also have "... =  `\<not> ((\<exists> ref \<acute>\<acute>. ($ref\<acute>\<acute> = $ref)) \<and> (
(\<not>(CSP_Pre(add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> P) \<and> CSP_Pre(add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> Q)) \<and>
         ($tr\<acute> = $tr)) ;
       (((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))
))`"

also have "... =  `\<not> (
(\<not>(CSP_Pre(add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> P) \<and> CSP_Pre(add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet> Q)) \<and>
         ($tr\<acute> = $tr)) ;
       (((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))
)`"

also have "... =  `\<not> (
(\<not>(add_sub 0 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet>CSP_Pre( P) \<and> add_sub 1 on {wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>} \<bullet>CSP_Pre( Q)) \<and> ($tr\<acute> = $tr)) ;
       (((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))
)`"


  have 0: "{wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>, wait\<down>, ref\<down>, tr\<down>} - {tr\<down>, tr\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {ref\<down>, ref\<down>\<acute>} = {}"
  have "`CSP_Pre(P ||| Q)` =  `\<not>((\<not>CSP_Pre(add_sub 0 on {tr \<down>\<acute>,wait \<down>\<acute>,ref \<down>\<acute>} \<bullet> P) \<or> \<not>CSP_Pre(add_sub 1 on {tr \<down>\<acute>,wait \<down>\<acute>,ref \<down>\<acute>} \<bullet> Q) \<and> ($tr \<le> $tr \<acute>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>))`"
    apply(simp add:InterleaveCSP_def ParallelCSP_def ParallelMergeD_def ParallelD_def DesignD_def ImpliesP_def)
    apply(subst CSP_Pre_def)
    apply(subst Merge_right) defer    
    apply(subst SubstP_OrP)    
    apply(subst SubstP_OrP)    
    apply(subst SubstP_OrP)
  apply(subst SubstP_SemiR_right, simp add:closure, simp add:unrest closure typing)
  apply(simp add:usubst typing defined closure)
  apply(subst SubstP_SemiR_left, simp add:closure, simp add:unrest closure typing)
  apply(subst SubstP_SemiR_left, simp add:closure, simp add:unrest closure typing)
  apply(subst SubstP_SemiR_left, simp add:closure, simp add:unrest closure typing)
  apply(subst SubstP_SemiR_left, simp add:closure, simp add:unrest closure typing)
  apply(simp add:MergeCSP_form)
  apply(simp add:usubst typing defined closure)
  apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure defined) defer 
  apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing closure defined) defer 
  apply(subst SkipRA_unfold_aux_ty[of "ref"],simp_all add:typing closure defined) defer 
  apply(subst 0)
  apply(simp add:usubst typing defined closure SkipRA_empty)
*)


end